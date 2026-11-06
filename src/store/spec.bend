import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared

# The store keeps sequences of items, each item some bytes, as prolly trees:
# the items are cut into chunks by their content, each chunk is a node, the
# references to those nodes are cut the same way, and so on up to one root.
# A node's address is the BLAKE3 hash of its encoding, so equal content is
# kept once, and a tree's shape depends only on its items. Raw content is a
# sequence of one-byte items; a view's content is a sequence of its items.

# Nodes
# -----

# A reference to a node: the hash of its encoding, and how many items lie
# below it.
type Ref is Data:
  Ref{hash: Shared.Bytes(), count: Nat}

# A node: a chunk of items, or a chunk of references one level down.
type Node is Data:
  Leaf{items: List<&2, Shared.Bytes()>}
  Branch{kids: List<&2, Ref>}

# the bytes of n, as LEB128: seven bits per byte, low bits first, the top
# bit set on every byte but the last; fuel counts the bytes left to write
def Leb.go(fuel: Nat, +n: Nat) -> Shared.Bytes():
  match fuel:
    case 0n:
      []
    case 1n+f:
      +low = U32.from_nat(Nat.mod(n, 128n))
      rest = Nat.div(n, 128n)
      Shared.Bool.when(
        Shared.Bytes(),
        Nat.is_lt(n, 128n),
        u => [low],
        u => (low + 128: U32) <> Leb.go(f, rest)
      )

# the LEB128 bytes of n; n itself bounds the bytes it needs
def Leb.of(+n: Nat) -> Shared.Bytes():
  Leb.go(1n+n, n)

# the bytes of b, after its length
def Bytes.framed(+b: Shared.Bytes()) -> Shared.Bytes():
  List.append(&2, U32, Leb.of(List.length(&2, U32, b)), b)

# the bytes of r: its hash, then its count
def Ref.encode(r: Ref) -> Shared.Bytes():
  match r:
    case Ref{h, c}:
      List.append(&2, U32, Bytes.framed(h), Leb.of(c))

# the bytes of each of xs, one after another
def Bytes.concat(xs: List<&2, Shared.Bytes()>) -> Shared.Bytes():
  match xs:
    case Nil{}:
      []
    case Con{x, t}:
      List.append(&2, U32, x, Bytes.concat(t))

# the framed encodings of refs, one after another
def Ref.encode_all(refs: List<&2, Ref>) -> Shared.Bytes():
  match refs:
    case Nil{}:
      []
    case Con{r, t}:
      List.append(&2, U32, Bytes.framed(Ref.encode(r)), Ref.encode_all(t))

# the framed items, one after another
def Bytes.frame_all(items: List<&2, Shared.Bytes()>) -> Shared.Bytes():
  match items:
    case Nil{}:
      []
    case Con{x, t}:
      List.append(&2, U32, Bytes.framed(x), Bytes.frame_all(t))

# the bytes that n's address hashes: a tag (0 leaf, 1 branch), then each
# item or reference with its length in front, so no two nodes share bytes
def Node.encode(n: Node) -> Shared.Bytes():
  match n:
    case Leaf{items}:
      0 <> Bytes.frame_all(items)
    case Branch{kids}:
      1 <> Ref.encode_all(kids)

# the items below the references
def Ref.total(refs: List<&2, Ref>) -> Nat:
  match refs:
    case Nil{}:
      0n
    case Con{Ref{h, c}, t}:
      Nat.add(c, Ref.total(t))

# the items below n
def Node.count(n: Node) -> Nat:
  match n:
    case Leaf{items}:
      List.length(&2, Shared.Bytes(), items)
    case Branch{kids}:
      Ref.total(kids)

# the reference to n
def Node.ref(+n: Node) -> Ref:
  Ref{Hash.Hash.blake3(Node.encode(n)), Node.count(n)}

# Chunking
# --------
# A cut depends only on the items, so equal content gives equal nodes, and
# an edit moves only the cuts near it. The rule aims at about 4 KiB of item
# bytes per node, whatever the item size: an item of len bytes ends its
# chunk with a chance of len / 4096.

# a cheap 32-bit digest of b, for cuts only: FNV-1a
def Chunk.digest.go(b: Shared.Bytes(), h: U32) -> U32:
  match b:
    case Nil{}:
      h
    case Con{x, t}:
      Chunk.digest.go(t, (U32.xor(h, x) * 16777619: U32))

# the FNV-1a digest of b
def Chunk.digest(b: Shared.Bytes()) -> U32:
  Chunk.digest.go(b, 2166136261)

# the rolling state after an item with digest d: the last 32 items decide it
def Chunk.roll(h: U32, d: U32) -> U32:
  ((h << 1n) + d: U32)

# the chunk ends after an item of len bytes, with rolling state h, when it
# then holds k items and size bytes: never below 2 items, always from 16 KiB
def Chunk.cuts(h: U32, len: Nat, k: Nat, size: Nat) -> Bool:
  luck = Nat.is_lt(U32.to_nat(h), Nat.mul(len, 1048576n))
  Bool.and(Nat.is_lt(1n, k), Bool.or(Nat.is_lt(16383n, size), luck))

# the chunks of items, given the rolling state h and the current chunk, last
# first, with its k items and size bytes
def Chunk.split.go(
  ~T: Data,
  ~bytes: T -> Shared.Bytes(),
  items: List<&2, T>,
  h: U32,
  +cur: List<&2, T>,
  +k: Nat,
  +size: Nat
) -> List<&2, List<&2, T>>:
  match items:
    case Nil{}:
      match cur:
        case Nil{}:
          Nil{}
        case Con{c, r}:
          [List.reverse(&2, T, Con{c, r})]
    case Con{+x, +t}:
      +b = bytes(x)
      +h2 = Chunk.roll(h, Chunk.digest(b))
      +len = List.length(&2, U32, b)
      Shared.Bool.when(
        List<&2, List<&2, T>>,
        Chunk.cuts(h2, len, 1n+k, Nat.add(size, len)),
        u => List.reverse(&2, T, Con{x, cur}) <> Chunk.split.go(~T, ~bytes, t, h2, Nil{}, 0n, 0n),
        u => Chunk.split.go(~T, ~bytes, t, h2, Con{x, cur}, 1n+k, Nat.add(size, len))
      )

# the chunks of items, cut by their bytes
def Chunk.split(~T: Data, ~bytes: T -> Shared.Bytes(), items: List<&2, T>) -> List<&2, List<&2, T>>:
  Chunk.split.go(~T, ~bytes, items, 0, Nil{}, 0n, 0n)

# an item is its own bytes
def Bytes.id(b: Shared.Bytes()) -> Shared.Bytes():
  b

# Trees
# -----

# a leaf per chunk
def Tree.leaves.map(chunks: List<&2, List<&2, Shared.Bytes()>>) -> List<&2, Node>:
  match chunks:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Leaf{c} <> Tree.leaves.map(t)

# a leaf per chunk, or one empty leaf for no chunks
def Tree.leaves.of(chunks: List<&2, List<&2, Shared.Bytes()>>) -> List<&2, Node>:
  match chunks:
    case Nil{}:
      [Leaf{Nil{}}]
    case Con{c, t}:
      Tree.leaves.map(Con{c, t})

# the leaves of items: one per chunk, and one empty leaf for no items
def Tree.leaves(items: List<&2, Shared.Bytes()>) -> List<&2, Node>:
  Tree.leaves.of(Chunk.split(~Shared.Bytes(), ~Bytes.id, items))

# the references to nodes
def Node.refs(ns: List<&2, Node>) -> List<&2, Ref>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Node.ref(n) <> Node.refs(t)

# a branch per chunk of references
def Tree.branches(chunks: List<&2, List<&2, Ref>>) -> List<&2, Node>:
  match chunks:
    case Nil{}:
      Nil{}
    case Con{c, t}:
      Branch{c} <> Tree.branches(t)

# the nodes of one level up from refs
def Tree.up.level(refs: List<&2, Ref>) -> List<&2, Node>:
  Tree.branches(Chunk.split(~Ref, ~Ref.encode, refs))

# the root over refs: one level up at a time, until one reference is left;
# fuel bounds the levels (each level at least halves), and at its end one
# branch holds every reference
def Tree.up(fuel: Nat, refs: List<&2, Ref>) -> Ref:
  match fuel refs:
    case _ Con{r, Nil{}}:
      r
    case 0n rs:
      Node.ref(Branch{rs})
    case 1n+f rs:
      Tree.up(f, Node.refs(Tree.up.level(rs)))

# the root of items: the reference that a store finds them under
def Tree.root(items: List<&2, Shared.Bytes()>) -> Ref:
  Tree.up(64n, Node.refs(Tree.leaves(items)))

# Stores
# ------

# The nodes, by the hex of their hash.
type Store is Data:
  Store{nodes: Shared.Table<Node>}

# a store with no nodes
def Store.new() -> Store:
  Store{Shared.Table.new(Node)}

# the node at hash h, or None
def Store.get(s: Store, h: Shared.Bytes()) -> Maybe<&2, Node>:
  match s:
    case Store{m}:
      Shared.Table.get(Node, m, Hash.Hash.hex(h))

# a then b, or None when either is None
def Items.both(
  a: Maybe<&2, List<&2, Shared.Bytes()>>,
  b: Maybe<&2, List<&2, Shared.Bytes()>>
) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  match a b:
    case Some{x} Some{y}:
      Some{List.append(&2, Shared.Bytes(), x, y)}
    case _ _:
      None{}

# the items of the node n, then rest(); below reads the kids of a branch
def Tree.read.node(
  n: Maybe<&2, Node>,
  below: List<&2, Ref> -> Maybe<&2, List<&2, Shared.Bytes()>>,
  rest: Unit -> Maybe<&2, List<&2, Shared.Bytes()>>
) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  match n:
    case None{}:
      None{}
    case Some{Leaf{items}}:
      Items.both(Some{items}, rest(Unit{}))
    case Some{Branch{kids}}:
      Items.both(below(kids), rest(Unit{}))

# the items below refs in s, in order, or None when a node is missing; fuel
# bounds the depth
def Tree.read.go(+fuel: Nat, +s: Store, refs: List<&2, Ref>) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  match fuel:
    case 0n:
      None{}
    case 1n+f:
      match refs:
        case Nil{}:
          Some{Nil{}}
        case Con{Ref{h, c}, t}:
          Tree.read.node(
            Store.get(s, h),
            kids => Tree.read.go(f, s, kids),
            u => Tree.read.go(fuel, s, t)
          )

# the items that r stands for in s, or None when s lacks a node below r
def Tree.read(s: Store, r: Ref) -> Maybe<&2, List<&2, Shared.Bytes()>>:
  Tree.read.go(64n, s, [r])

# Writing
# -------

# Why a write or an edit stopped. Collides: two different nodes with one
# hash; a store never keeps both, so it names them. Missing: the store lacks
# a node below the reference that an edit starts from.
type Problem is Data:
  Collides{a: Node, b: Node}
  Missing{}

# A finished write: the store with the new nodes, and the root.
type Wrote is Data:
  Wrote{store: Store, root: Ref}

# a and b are the same node
law Node.is_eq:
  for a: Node
  for b: Node
  Bool

# s with every node of items, and the root of items; or the collision that
# stopped it
law Tree.write:
  for s: Store
  for items: List<&2, Shared.Bytes()>
  Result<&2, &2, Problem, Wrote>

# items with del items at pos replaced by ins
def Items.splice(
  items: List<&2, Shared.Bytes()>,
  +pos: Nat,
  del: Nat,
  ins: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  +items = items
  rest = List.drop(&2, Shared.Bytes(), items, Nat.add(pos, del))
  List.append(
    &2,
    Shared.Bytes(),
    List.take(&2, Shared.Bytes(), items, pos),
    List.append(&2, Shared.Bytes(), ins, rest)
  )

# s with the nodes of the items under r after replacing del items at pos
# with ins, and their root; or the problem that stopped it
law Tree.edit:
  for s: Store
  for r: Ref
  for pos: Nat
  for del: Nat
  for ins: List<&2, Shared.Bytes()>
  Result<&2, &2, Problem, Wrote>

# One step of a diff: replace del items at pos with ins.
type Splice is Data:
  Splice{pos: Nat, del: Nat, ins: List<&2, Shared.Bytes()>}

# items after each splice, in order; each pos counts in the items as the
# splices before it left them
def Items.apply(
  edits: List<&2, Splice>,
  items: List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  match edits:
    case Nil{}:
      items
    case Con{Splice{pos, del, ins}, t}:
      Items.apply(t, Items.splice(items, pos, del, ins))

# the splices that turn the items under a into the items under b, or None
# when s lacks a node
law Tree.diff:
  for s: Store
  for a: Ref
  for b: Ref
  Maybe<&2, List<&2, Splice>>

# Laws
# ----

# Node.is_eq answers True exactly for equal nodes
law node_is_eq:
  for a: Node
  for b: Node
  {Node.is_eq(a, b) == True{}: Bool} -> {a == b: Node}

# a written sequence reads back
law read_after_write:
  for s: Store
  for items: List<&2, Shared.Bytes()>
  for t: Store
  for r: Ref
  for h: {Tree.write(s, items) == Done{Wrote{t, r}}: Result<&2, &2, Problem, Wrote>}
  {Tree.read(t, r) == Some{items}: Maybe<&2, List<&2, Shared.Bytes()>>}

# the root of a write is the root of its items, whatever the store held
law write_root:
  for s: Store
  for items: List<&2, Shared.Bytes()>
  for t: Store
  for r: Ref
  for h: {Tree.write(s, items) == Done{Wrote{t, r}}: Result<&2, &2, Problem, Wrote>}
  {r == Tree.root(items): Ref}

# a write keeps every sequence the store held
law write_keeps:
  for s: Store
  for items: List<&2, Shared.Bytes()>
  for t: Store
  for r: Ref
  for old: Ref
  for xs: List<&2, Shared.Bytes()>
  for h: {Tree.write(s, items) == Done{Wrote{t, r}}: Result<&2, &2, Problem, Wrote>}
  for o: {Tree.read(s, old) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  {Tree.read(t, old) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}

# an edit gives the same root as writing the edited items from scratch
law edit_root:
  for s: Store
  for r: Ref
  for xs: List<&2, Shared.Bytes()>
  for pos: Nat
  for del: Nat
  for ins: List<&2, Shared.Bytes()>
  for t: Store
  for r2: Ref
  for o: {Tree.read(s, r) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for h: {Tree.edit(s, r, pos, del, ins) == Done{Wrote{t, r2}}: Result<&2, &2, Problem, Wrote>}
  {r2 == Tree.root(Items.splice(xs, pos, del, ins)): Ref}

# an edited sequence reads back
law read_after_edit:
  for s: Store
  for r: Ref
  for xs: List<&2, Shared.Bytes()>
  for pos: Nat
  for del: Nat
  for ins: List<&2, Shared.Bytes()>
  for t: Store
  for r2: Ref
  for o: {Tree.read(s, r) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for h: {Tree.edit(s, r, pos, del, ins) == Done{Wrote{t, r2}}: Result<&2, &2, Problem, Wrote>}
  {Tree.read(t, r2) == Some{Items.splice(xs, pos, del, ins)}: Maybe<&2, List<&2, Shared.Bytes()>>}

# an edit keeps every sequence the store held
law edit_keeps:
  for s: Store
  for r: Ref
  for pos: Nat
  for del: Nat
  for ins: List<&2, Shared.Bytes()>
  for t: Store
  for r2: Ref
  for old: Ref
  for xs: List<&2, Shared.Bytes()>
  for h: {Tree.edit(s, r, pos, del, ins) == Done{Wrote{t, r2}}: Result<&2, &2, Problem, Wrote>}
  for o: {Tree.read(s, old) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  {Tree.read(t, old) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}

# a write fails only on a real collision: two different nodes, one hash
law write_collides:
  for s: Store
  for items: List<&2, Shared.Bytes()>
  for a: Node
  for b: Node
  for h: {Tree.write(s, items) == Fail{Collides{a, b}}: Result<&2, &2, Problem, Wrote>}
  {Node.is_eq(a, b) == False{}: Bool} &
    {Hash.Hash.blake3(Node.encode(a)) == Hash.Hash.blake3(Node.encode(b)): Shared.Bytes()}

# an edit fails only on a real collision
law edit_collides:
  for s: Store
  for r: Ref
  for pos: Nat
  for del: Nat
  for ins: List<&2, Shared.Bytes()>
  for a: Node
  for b: Node
  for h: {Tree.edit(s, r, pos, del, ins) == Fail{Collides{a, b}}: Result<&2, &2, Problem, Wrote>}
  {Node.is_eq(a, b) == False{}: Bool} &
    {Hash.Hash.blake3(Node.encode(a)) == Hash.Hash.blake3(Node.encode(b)): Shared.Bytes()}

# a diff turns the items under a into the items under b
law diff_applies:
  for s: Store
  for a: Ref
  for b: Ref
  for xs: List<&2, Shared.Bytes()>
  for ys: List<&2, Shared.Bytes()>
  for e: List<&2, Splice>
  for ha: {Tree.read(s, a) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for hb: {Tree.read(s, b) == Some{ys}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for h: {Tree.diff(s, a, b) == Some{e}: Maybe<&2, List<&2, Splice>>}
  {Items.apply(e, xs) == ys: List<&2, Shared.Bytes()>}

# a diff of two readable roots always answers
law diff_answers:
  for s: Store
  for a: Ref
  for b: Ref
  for xs: List<&2, Shared.Bytes()>
  for ys: List<&2, Shared.Bytes()>
  for ha: {Tree.read(s, a) == Some{xs}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for hb: {Tree.read(s, b) == Some{ys}: Maybe<&2, List<&2, Shared.Bytes()>>}
  {Maybe.is_some(&2, List<&2, Splice>, Tree.diff(s, a, b)) == True{}: Bool}
