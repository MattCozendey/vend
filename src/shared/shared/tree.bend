import Base
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/shared.bend as Shared
import ./shared/store.bend as Stores

# Trees
# =====
# A tree maps keys to values (both lists of words), and is held as nodes in a
# store of data by hash: a version of a line is the hash of its tree's root.
# A tree goes 16 ways by the nibbles of its key's hash, highest first, and
# ends in a leaf as soon as a subtree holds one key, so a read or a write
# visits about log16 of its size nodes. A tree is named by the hash of its root
# (none: the empty tree), and two versions share every subtree that neither
# changed.

# a node: empty (what an empty part reads as; never stored), a leaf, which
# holds one key and its value, or a branch, which holds the root of each of
# its 16 parts (none: empty)
type Node is Data:
  Node.Empty{}
  Node.Leaf{key: List<&2, U32>, value: List<&2, U32>}
  Node.Branch{parts: List<&2, Maybe<&2, Hashes.Hash>>}

# Codes
# -----

# the parts ks of a branch, then r
def Parts.code(ks: List<&2, Maybe<&2, Hashes.Hash>>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(
    ~Maybe<&2, Hashes.Hash>,
    ~(m => r2 => Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, m, r2)),
    ks,
    r
  )

# the parts of a branch
def Parts.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Maybe<&2, Hashes.Hash>>>>:
  Codes.Code.list.read(
    ~Maybe<&2, Hashes.Hash>,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    ts
  )

# the parts ps end with a part that is not empty: the one code of a branch
def Parts.ok(ps: List<&2, Maybe<&2, Hashes.Hash>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{None{}, Nil{}}:
      False{}
    case Con{Some{h}, Nil{}}:
      True{}
    case Con{x, Con{y, r}}:
      Parts.ok(Con{y, r})

# the node n is in its one code: a branch's parts are (Parts.ok)
def Node.ok(n: Node) -> Bool:
  match n:
    case Node.Branch{ps}:
      Parts.ok(ps)
    case _:
      True{}

# a branch of the parts ps, when they are its one code
def Node.branch.of(
  +ps: List<&2, Maybe<&2, Hashes.Hash>>,
  r: List<&2, U32>
) -> Maybe<&2, Codes.Read<Node>>:
  Shared.Maybe.when(Codes.Read<Node>, Parts.ok(ps), u => Some{Codes.Read{Node.Branch{ps}, r}})

# the node n, then r
def Node.code(n: Node, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Node.Empty{}:
      0 <> r
    case Node.Leaf{k, v}:
      1 <> Codes.Code.words(k, Codes.Code.words(v, r))
    case Node.Branch{ks}:
      2 <> Parts.code(ks, r)

# a node whose tag is x: empty (0), a leaf (1) or a branch (2)
def Node.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    U32.is_eq(x, 0),
    u => Some{Codes.Read{Node.Empty{}, r}},
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Node>>,
      U32.is_eq(x, 1),
      u => Codes.Code.two.read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.read,
        ~Codes.Code.words.read,
        k => v => Node.Leaf{k, v},
        r
      ),
      u => Shared.Bool.when(
        Maybe<&2, Codes.Read<Node>>,
        U32.is_eq(x, 2),
        u => Codes.Read.then(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Node,
          Parts.code.read(r),
          ps => r2 => Node.branch.of(ps, r2)
        ),
        u => None{}
      )
    )
  )

# a node
def Node.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Node.code.read.of(x, r)

# the words of the node n
def Node.words(n: Node) -> List<&2, U32>:
  Node.code(n, [])

# the hash of the node n
def Node.hash(n: Node) -> Hashes.Hash:
  Hashes.Sha.hash(Node.words(n))

# the node of a read, when nothing follows it
def Node.of.read(r: Codes.Read<Node>) -> Maybe<&2, Node>:
  match r:
    case Codes.Read{n, Nil{}}:
      Some{n}
    case Codes.Read{n, Con{x, xs}}:
      None{}

# the node of the words ws, when they hold one exactly
def Node.of(ws: List<&2, U32>) -> Maybe<&2, Node>:
  Maybe.bind(&2, Codes.Read<Node>, Node, Node.code.read(ws), Node.of.read)

# Paths
# -----

# the lowest 4 bits of x, as a number
def Nibble.of(+x: U32) -> Nat:
  Shared.Bool.when(
    Nat,
    U32.is_eq(U32.and(x, 8), 0),
    u => Shared.Bool.when(
      Nat,
      U32.is_eq(U32.and(x, 4), 0),
      u => Shared.Bool.when(
        Nat,
        U32.is_eq(U32.and(x, 2), 0),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 0n, u => 1n),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 2n, u => 3n)
      ),
      u => Shared.Bool.when(
        Nat,
        U32.is_eq(U32.and(x, 2), 0),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 4n, u => 5n),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 6n, u => 7n)
      )
    ),
    u => Shared.Bool.when(
      Nat,
      U32.is_eq(U32.and(x, 4), 0),
      u => Shared.Bool.when(
        Nat,
        U32.is_eq(U32.and(x, 2), 0),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 8n, u => 9n),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 10n, u => 11n)
      ),
      u => Shared.Bool.when(
        Nat,
        U32.is_eq(U32.and(x, 2), 0),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 12n, u => 13n),
        u => Shared.Bool.when(Nat, U32.is_eq(U32.and(x, 1), 0), u => 14n, u => 15n)
      )
    )
  )

# the 8 nibbles of x, highest first, then r
def Nibbles.word(+x: U32, r: List<&2, Nat>) -> List<&2, Nat>:
  Nibble.of(
    U32.shrn(x, 28n)
  )
    <> Nibble.of(U32.shrn(x, 24n))
    <> Nibble.of(U32.shrn(x, 20n))
    <> Nibble.of(U32.shrn(x, 16n))
    <> Nibble.of(U32.shrn(x, 12n))
    <> Nibble.of(U32.shrn(x, 8n))
    <> Nibble.of(U32.shrn(x, 4n))
    <> Nibble.of(x)
    <> r

# the 64 nibbles of the hash h, highest first
def Nibbles.of(h: Hashes.Hash) -> List<&2, Nat>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      Nibbles.word(
        a,
        Nibbles.word(
          b,
          Nibbles.word(
            c,
            Nibbles.word(d, Nibbles.word(e, Nibbles.word(f, Nibbles.word(g, Nibbles.word(i, [])))))
          )
        )
      )

# the path of the key k: the nibbles of its hash
def Tree.path(k: List<&2, U32>) -> List<&2, Nat>:
  Nibbles.of(Hashes.Sha.hash(k))

# the part n of the parts ks
def Parts.at(ks: List<&2, Maybe<&2, Hashes.Hash>>, n: Nat) -> Maybe<&2, Hashes.Hash>:
  match ks n:
    case Nil{} m:
      None{}
    case Con{x, r} 0n:
      x
    case Con{x, r} 1n+p:
      Parts.at(r, p)

# the parts ks with the part n set to x (empty parts fill a gap)
def Parts.set(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  x: Maybe<&2, Hashes.Hash>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match ks n:
    case Nil{} 0n:
      [x]
    case Nil{} 1n+p:
      None{} <> Parts.set([], p, x)
    case Con{y, r} 0n:
      x <> r
    case Con{y, r} 1n+p:
      y <> Parts.set(r, p, x)

# the part x, then the parts r, without empty parts at the end
def Parts.trim.of(
  x: Maybe<&2, Hashes.Hash>,
  r: List<&2, Maybe<&2, Hashes.Hash>>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match x r:
    case None{} Nil{}:
      []
    case y q:
      y <> q

# the parts ks without empty parts at the end
def Parts.trim(ks: List<&2, Maybe<&2, Hashes.Hash>>) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match ks:
    case Nil{}:
      []
    case Con{x, r}:
      Parts.trim.of(x, Parts.trim(r))

# the parts ks with the part n set to x, in their one code (Parts.ok)
def Parts.put(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  x: Maybe<&2, Hashes.Hash>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  Parts.trim(Parts.set(ks, n, x))

# the parts of a branch, empty
def Parts.none() -> List<&2, Maybe<&2, Hashes.Hash>>:
  []

# Reads
# -----

# the node of the hash h, in the store s
def Tree.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Maybe.bind(&2, List<&2, U32>, Node, fetch(s)(h), Node.of)

# the node of the part x of a branch (none: empty), in the store s
def Tree.part(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  x: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Node>:
  match x:
    case None{}:
      Some{Node.Empty{}}
    case Some{h}:
      Tree.node(~S, ~fetch, s, h)

# the value of the key k in the node m (none: not in the store), whose path
# below it is p
def Tree.get.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Maybe<&2, List<&2, U32>>:
  match p m:
    case q None{}:
      None{}
    case q Some{Node.Empty{}}:
      None{}
    case q Some{Node.Leaf{k2, v}}:
      Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), u => Some{v})
    case Nil{} Some{Node.Branch{ks}}:
      None{}
    case Con{x, r} Some{Node.Branch{ks}}:
      Tree.get.go(~S, ~fetch, s, r, k, Tree.part(~S, ~fetch, s, Parts.at(ks, x)))

# the value of the key k in the tree whose root is h, in the store s
def Tree.get.plain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Tree.get.go(~S, ~fetch, s, Tree.path(k), k, Tree.part(~S, ~fetch, s, h))

# what a read of a key finds: its value; that the tree does not hold the key;
# or that the store lacks the node of a hash, so the read cannot tell yet.
# Found and Absent are final (Tree.look_found_kept, Tree.look_absent_kept):
# only Missing changes when the store gets more nodes
type Look is Data:
  Look.Found{value: List<&2, U32>}
  Look.Absent{}
  Look.Missing{hash: Hashes.Hash}

# the value that a read found, if it found one
def Look.value(l: Look) -> Maybe<&2, List<&2, U32>>:
  match l:
    case Look.Found{v}:
      Some{v}
    case Look.Absent{}:
      None{}
    case Look.Missing{h}:
      None{}

# a read that lacks the node of the part o (an empty part lacks none)
def Look.missing(o: Maybe<&2, Hashes.Hash>) -> Look:
  match o:
    case None{}:
      Look.Absent{}
    case Some{h}:
      Look.Missing{h}

# what a read of the key k finds at the part o, whose node is m (none: not in
# the store) and whose path below it is p
def Tree.look.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>
) -> Look:
  match p m:
    case q None{}:
      Look.missing(o)
    case q Some{Node.Empty{}}:
      Look.Absent{}
    case q Some{Node.Leaf{k2, v}}:
      Shared.Bool.when(
        Look,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Look.Found{v},
        u => Look.Absent{}
      )
    case Nil{} Some{Node.Branch{ks}}:
      Look.Absent{}
    case Con{+x, r} Some{Node.Branch{+ks}}:
      Tree.look.go(~S, ~fetch, s, r, k, Parts.at(ks, x), Tree.part(~S, ~fetch, s, Parts.at(ks, x)))

# what a read of the key k finds in the tree whose root is h, in the store s
def Tree.look.plain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Look:
  Tree.look.go(~S, ~fetch, s, Tree.path(k), k, h, Tree.part(~S, ~fetch, s, h))

# Listings
# --------
# A listing walks every node of a tree, and lists a leaf only where its key's
# path leads, so that a key is listed exactly when it reads.

# a key and its value, as a tree lists them
type Binding is Data:
  Binding{key: List<&2, U32>, value: List<&2, U32>}

# the path of the key k starts with the nibbles pre
def Tree.leads(k: List<&2, U32>, +pre: List<&2, Nat>) -> Bool:
  Shared.List.is_eq(
    ~Nat,
    ~Nat.is_eq,
    List.take(&2, Nat, Tree.path(k), List.length(&2, Nat, pre)),
    pre
  )

# the node of the first part of ps, in the store s (none: no part)
def Tree.first(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  ps: List<&2, Maybe<&2, Hashes.Hash>>
) -> Maybe<&2, Node>:
  match ps:
    case Nil{}:
      None{}
    case Con{x, r}:
      Tree.part(~S, ~fetch, s, x)

# bend-lint: expect-begin bend-lint-rules/language/decreasing_call@warning -- g is f itself, bound by the match; the checker accepts these calls
# the bindings under the parts ps of a branch whose path is pre, from its part
# x, whose node is m; f levels deep at most
def Tree.list.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  m: Maybe<&2, Node>
) -> List<&2, Binding>:
  match f ps m:
    case g Nil{} w:
      []
    case g Con{y, +r} Some{Node.Leaf{+k, v}}:
      +rest = Tree.list.go(~S, ~fetch, g, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
      Shared.Bool.when(
        List<&2, Binding>,
        Tree.leads(k, List.append(&2, Nat, pre, [x])),
        u => Binding{k, v} <> rest,
        u => rest
      )
    case 1n+(+p) Con{y, r} Some{Node.Branch{+qs}}:
      here = List.append(&2, Nat, pre, [x])
      below rest = Tree.list.go(
        ~S,
        ~fetch,
        p,
        s,
        qs,
        here,
        0n,
        Tree.first(~S, ~fetch, s, qs)
      ) Tree.list.go(~S, ~fetch, 1n+p, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
      List.append(&2, Binding, below, rest)
    case g Con{y, r} w:
      Tree.list.go(~S, ~fetch, g, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
# bend-lint: expect-end bend-lint-rules/language/decreasing_call@warning

# the bindings of a tree whose root node is m
def Tree.list.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  m: Maybe<&2, Node>
) -> List<&2, Binding>:
  match m:
    case Some{Node.Leaf{k, v}}:
      [Binding{k, v}]
    case Some{Node.Branch{+qs}}:
      Tree.list.go(~S, ~fetch, 63n, s, qs, [], 0n, Tree.first(~S, ~fetch, s, qs))
    case w:
      []

# the bindings of the tree whose root is h, in the store s
def Tree.list(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>
) -> List<&2, Binding>:
  Tree.list.root(~S, ~fetch, s, Tree.part(~S, ~fetch, s, h))

# bend-lint: expect-begin bend-lint-rules/language/decreasing_call@warning -- g is f itself, bound by the match; the checker accepts these calls
# the store holds each node under the parts ps of a branch, whose first node
# is m; f levels deep at most (deeper: it cannot tell, so no)
def Tree.whole.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  m: Maybe<&2, Node>
) -> Bool:
  match f ps m:
    case g Nil{} w:
      True{}
    case g Con{y, r} None{}:
      False{}
    case g Con{y, +r} Some{Node.Empty{}}:
      Tree.whole.go(~S, ~fetch, g, s, r, Tree.first(~S, ~fetch, s, r))
    case g Con{y, +r} Some{Node.Leaf{k, v}}:
      Tree.whole.go(~S, ~fetch, g, s, r, Tree.first(~S, ~fetch, s, r))
    case 0n Con{y, r} Some{Node.Branch{qs}}:
      False{}
    case 1n+(+p) Con{y, +r} Some{Node.Branch{+qs}}:
      List.all.if(
        u => Tree.whole.go(~S, ~fetch, 1n+p, s, r, Tree.first(~S, ~fetch, s, r)),
        Tree.whole.go(~S, ~fetch, p, s, qs, Tree.first(~S, ~fetch, s, qs))
      )
# bend-lint: expect-end bend-lint-rules/language/decreasing_call@warning

# Tree.whole once the root node m is known
def Tree.whole.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  m: Maybe<&2, Node>
) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Node.Branch{+qs}}:
      Tree.whole.go(~S, ~fetch, 63n, s, qs, Tree.first(~S, ~fetch, s, qs))
    case Some{w}:
      True{}

# the store s holds each node of the tree whose root is h: a walk of the tree
# (Tree.list, Tree.diff) then sees all of it, not a part
def Tree.whole(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>
) -> Bool:
  Tree.whole.root(~S, ~fetch, s, Tree.part(~S, ~fetch, s, h))

# Differences
# -----------
# Two trees with the same root hold the same, so a walk of both skips each
# pair of parts with the same hash: it costs what differs, not what the trees
# hold.

# the parts a and b hold the same root
def Parts.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the node m is a branch
def Node.is_branch(m: Maybe<&2, Node>) -> Bool:
  match m:
    case Some{Node.Branch{qs}}:
      True{}
    case w:
      False{}

# the parts of the node m, when it is a branch (else none)
def Node.kids(m: Maybe<&2, Node>) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match m:
    case Some{Node.Branch{qs}}:
      qs
    case w:
      []

# the bindings below the parts ya and yb, at the place x of branches whose
# path is pre, whose nodes are ma and mb; f levels deep at most
def Tree.diff.sides(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ya: Maybe<&2, Hashes.Hash>,
  yb: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Nat>,
  +x: Nat,
  ma: Maybe<&2, Node>,
  mb: Maybe<&2, Node>
) -> List<&2, Binding>:
  List.append(
    &2,
    Binding,
    Tree.list.go(~S, ~fetch, f, s, [ya], pre, x, ma),
    Tree.list.go(~S, ~fetch, f, s, [yb], pre, x, mb)
  )

# the bindings of the parts ka and kb, from the part x of branches whose path
# is pre, whose nodes are ma and mb, where the parts differ: f levels deep at
# most
def Tree.diff.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ka: List<&2, Maybe<&2, Hashes.Hash>>,
  kb: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  +ma: Maybe<&2, Node>,
  +mb: Maybe<&2, Node>
) -> List<&2, Binding>:
  match f ka kb:
    case g Nil{} Nil{}:
      []
    case g Con{ya, ra} Nil{}:
      Tree.list.go(~S, ~fetch, g, s, ya <> ra, pre, x, ma)
    case g Nil{} Con{yb, rb}:
      Tree.list.go(~S, ~fetch, g, s, yb <> rb, pre, x, mb)
    case 0n Con{+ya, +ra} Con{+yb, +rb}:
      +rest = Tree.diff.go(
        ~S,
        ~fetch,
        0n,
        s,
        ra,
        rb,
        pre,
        1n+x,
        Tree.first(~S, ~fetch, s, ra),
        Tree.first(~S, ~fetch, s, rb)
      )
      Shared.Bool.when(
        List<&2, Binding>,
        Parts.same(ya, yb),
        u => rest,
        u => List.append(
          &2,
          Binding,
          Tree.diff.sides(~S, ~fetch, 0n, s, ya, yb, pre, x, ma, mb),
          rest
        )
      )
    case 1n+(+p) Con{+ya, +ra} Con{+yb, +rb}:
      here = List.append(&2, Nat, pre, [x])
      +rest = Tree.diff.go(
        ~S,
        ~fetch,
        1n+p,
        s,
        ra,
        rb,
        pre,
        1n+x,
        Tree.first(~S, ~fetch, s, ra),
        Tree.first(~S, ~fetch, s, rb)
      )
      Shared.Bool.when(
        List<&2, Binding>,
        Parts.same(ya, yb),
        u => rest,
        u => List.append(
          &2,
          Binding,
          Shared.Bool.when(
            List<&2, Binding>,
            Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
            u => Tree.diff.go(
              ~S,
              ~fetch,
              p,
              s,
              Node.kids(ma),
              Node.kids(mb),
              here,
              0n,
              Tree.first(~S, ~fetch, s, Node.kids(ma)),
              Tree.first(~S, ~fetch, s, Node.kids(mb))
            ),
            u => Tree.diff.sides(~S, ~fetch, 1n+p, s, ya, yb, pre, x, ma, mb)
          ),
          rest
        )
      )

# the bindings of the trees whose root nodes are ma and mb, where they may
# differ: every key that the two read differently is listed
def Tree.diff.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ma: Maybe<&2, Node>,
  +mb: Maybe<&2, Node>
) -> List<&2, Binding>:
  Shared.Bool.when(
    List<&2, Binding>,
    Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
    u => Tree.diff.go(
      ~S,
      ~fetch,
      63n,
      s,
      Node.kids(ma),
      Node.kids(mb),
      [],
      0n,
      Tree.first(~S, ~fetch, s, Node.kids(ma)),
      Tree.first(~S, ~fetch, s, Node.kids(mb))
    ),
    u => List.append(
      &2,
      Binding,
      Tree.list.root(~S, ~fetch, s, ma),
      Tree.list.root(~S, ~fetch, s, mb)
    )
  )

# the bindings of the trees whose roots are a and b, where they may differ
def Tree.diff(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +a: Maybe<&2, Hashes.Hash>,
  +b: Maybe<&2, Hashes.Hash>
) -> List<&2, Binding>:
  Shared.Bool.when(
    List<&2, Binding>,
    Parts.same(a, b),
    u => [],
    u => Tree.diff.root(~S, ~fetch, s, Tree.part(~S, ~fetch, s, a), Tree.part(~S, ~fetch, s, b))
  )

# Writes
# ------
# A write fails (none) when the store does not hold a node on its path, or
# when the key's path is the whole path of another key in the tree.

# a new subtree: its root, and the words of the nodes that it adds
type Put is Data:
  Put{root: Hashes.Hash, nodes: List<&2, List<&2, U32>>}

# the root of the subtree p
def Put.root(p: Put) -> Hashes.Hash:
  match p:
    case Put{h, ns}:
      h

# the nodes that the subtree p adds
def Put.nodes(p: Put) -> List<&2, List<&2, U32>>:
  match p:
    case Put{h, ns}:
      ns

# the subtree that is the node n, after the nodes ns
def Put.node(n: Node, ns: List<&2, List<&2, U32>>) -> Put:
  +ws = Node.words(n)
  Put{Hashes.Sha.hash(ws), ws <> ns}

# the subtree of a branch of parts ks whose part n is the new subtree p
def Put.into(ks: List<&2, Maybe<&2, Hashes.Hash>>, n: Nat, +p: Put) -> Put:
  Put.node(Node.Branch{Parts.put(ks, n, Some{Put.root(p)})}, Put.nodes(p))

# the subtree that holds the new leaf l, whose path below here is p1, and the
# part o already there, whose path below here is p2: branches down to where
# the paths differ
def Tree.split(
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +l: Put,
  +o: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Put>:
  match p1 p2:
    case Con{+a, r1} Con{+b, r2}:
      Shared.Bool.when(
        Maybe<&2, Put>,
        Nat.is_eq(a, b),
        u => Maybe.bind(
          &2,
          Put,
          Put,
          Tree.split(r1, r2, l, o),
          p => Some{Put.into(Parts.none(), a, p)}
        ),
        u => Some{
          Put.node(
            Node.Branch{Parts.put(Parts.put(Parts.none(), a, Some{Put.root(l)}), b, o)},
            Put.nodes(l)
          )
        }
      )
    case q w:
      None{}

# the part o (none: empty), whose node is m (none: not in the store), at depth
# d, whose path below is p, with the key k set to the value v
def Tree.set.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  d: Nat,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>
) -> Maybe<&2, Put>:
  match p m:
    case q None{}:
      None{}
    case q Some{Node.Empty{}}:
      Some{Put.node(Node.Leaf{k, v}, [])}
    case q Some{Node.Leaf{+k2, v2}}:
      +l = Put.node(Node.Leaf{k, v}, [])
      Shared.Bool.when(
        Maybe<&2, Put>,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Some{l},
        w => Tree.split(q, List.drop(&2, Nat, Tree.path(k2), d), l, o)
      )
    case Con{+x, r} Some{Node.Branch{+ks}}:
      +kid = Parts.at(ks, x)
      Maybe.bind(
        &2,
        Put,
        Put,
        Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
        p2 => Some{Put.into(ks, x, p2)}
      )
    case Nil{} Some{Node.Branch{ks}}:
      None{}

# the tree whose root is h, in the store s, with the key k set to the value
# v: its new root, and the nodes that it adds
def Tree.set.plain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> Maybe<&2, Put>:
  Tree.set.go(~S, ~fetch, s, Tree.path(k), 0n, k, v, h, Tree.part(~S, ~fetch, s, h))

# Tree.get once the root node m of the tree is known. The node comes before
# the path of the key (a hash): a tree with no node costs no hash, and a proof
# about a tree that is not known makes none
def Tree.get.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +k: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{Node.Empty{}}:
      None{}
    case Some{+n}:
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, Some{n})

# the value of the key k in the tree whose root is h, in the store s
def Tree.get(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Tree.get.at(~S, ~fetch, s, k, Tree.part(~S, ~fetch, s, h))

# Tree.set once the root node m of the tree is known (see Tree.get.at)
def Tree.set.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Maybe<&2, Put>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Tree.set.go(~S, ~fetch, s, Tree.path(k), 0n, k, x, h, Some{n})

# the tree whose root is h, in the store s, with the key k set to the value
# x: its new root, and the nodes that it adds
def Tree.set(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Put>:
  Tree.set.at(~S, ~fetch, s, h, k, x, Tree.part(~S, ~fetch, s, h))

# Tree.look once the root node m of the tree is known (see Tree.get.at)
def Tree.look.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Look:
  match m:
    case None{}:
      Look.missing(h)
    case Some{Node.Empty{}}:
      Look.Absent{}
    case Some{+n}:
      Tree.look.go(~S, ~fetch, s, Tree.path(k), k, h, Some{n})

# what a read of the key k finds in the tree whose root is h, in the store s
def Tree.look(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Look:
  Tree.look.at(~S, ~fetch, s, h, k, Tree.part(~S, ~fetch, s, h))

# The entry points look at the root node first; the laws below are stated of
# the plain ones (Tree.get.plain, Tree.set.plain, Tree.look.plain), which make
# the path first. They are equal: Tree.get_plain, Tree.set_plain,
# Tree.look_plain.

# a read below no node gives nothing
def Tree.get.go_none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {Tree.get.go(~S, ~fetch, s, p, k, None{}) == None{}: Maybe<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a read below an empty node gives nothing
def Tree.get.go_empty(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}) == None{}: Maybe<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# Tree.get_plain once the root node m is known
def Tree.get_plain.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +k: List<&2, U32>,
  m: Maybe<&2, Node>
) -> {
  Tree.get.at(
    ~S,
    ~fetch,
    s,
    k,
    m
  )
    == Tree.get.go(~S, ~fetch, s, Tree.path(k), k, m): Maybe<&2, List<&2, U32>>
}:
  match m:
    case None{}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.get.go(~S, ~fetch, s, Tree.path(k), k, None{}),
        None{},
        Tree.get.go_none(~S, ~fetch, s, Tree.path(k), k)
      )
    case Some{Node.Empty{}}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.get.go(~S, ~fetch, s, Tree.path(k), k, Some{Node.Empty{}}),
        None{},
        Tree.get.go_empty(~S, ~fetch, s, Tree.path(k), k)
      )
    case Some{Node.Leaf{a, b}}:
      {==}
    case Some{Node.Branch{ks}}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the read that looks at the root first is the plain read
def Tree.get_plain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> {
  Tree.get(~S, ~fetch, s, h, k) == Tree.get.plain(~S, ~fetch, s, h, k): Maybe<&2, List<&2, U32>>
}:
  Tree.get_plain.at(~S, ~fetch, s, k, Tree.part(~S, ~fetch, s, h))

# a write below no node gives nothing
def Tree.set.go_none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  x: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {Tree.set.go(~S, ~fetch, s, p, d, k, x, h, None{}) == None{}: Maybe<&2, Put>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, r}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# Tree.set_plain once the root node m is known
def Tree.set_plain.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Node>
) -> {
  Tree.set.at(
    ~S,
    ~fetch,
    s,
    h,
    k,
    x,
    m
  )
    == Tree.set.go(~S, ~fetch, s, Tree.path(k), 0n, k, x, h, m): Maybe<&2, Put>
}:
  match m:
    case None{}:
      Equal.sym(
        Maybe<&2, Put>,
        Tree.set.go(~S, ~fetch, s, Tree.path(k), 0n, k, x, h, None{}),
        None{},
        Tree.set.go_none(~S, ~fetch, s, Tree.path(k), 0n, k, x, h)
      )
    case Some{n}:
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the write that looks at the root first is the plain write
def Tree.set_plain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Tree.set(~S, ~fetch, s, h, k, x) == Tree.set.plain(~S, ~fetch, s, h, k, x): Maybe<&2, Put>}:
  Tree.set_plain.at(~S, ~fetch, s, h, k, x, Tree.part(~S, ~fetch, s, h))

# Laws
# ----

# the paths p1 and p2 differ before either ends
def Tree.split.ok(p1: List<&2, Nat>, p2: List<&2, Nat>) -> Bool:
  match p1 p2:
    case Con{a, r1} Con{b, r2}:
      Shared.Bool.when(Bool, Nat.is_eq(a, b), u => Tree.split.ok(r1, r2), u => True{})
    case q w:
      False{}

# the store s holds every node on the path p from the node m (none: not in the
# store) at depth d, and the leaf at its end, if any, is the key k's, or its
# path parts from p
def Tree.set.ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Bool:
  match p m:
    case q None{}:
      False{}
    case q Some{Node.Empty{}}:
      True{}
    case q Some{Node.Leaf{+k2, v2}}:
      Shared.Bool.when(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => True{},
        u => Tree.split.ok(q, List.drop(&2, Nat, Tree.path(k2), d))
      )
    case Con{x, r} Some{Node.Branch{ks}}:
      Tree.set.ok(~S, ~fetch, s, r, 1n+d, k, Tree.part(~S, ~fetch, s, Parts.at(ks, x)))
    case Nil{} Some{Node.Branch{ks}}:
      False{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# a read m, made a subtree by f, gives a subtree when m does
def Tree.some_then(
  m: Maybe<&2, Put>,
  -f: Put -> Put
) -> {
  Maybe.is_some(
    &2,
    Put,
    Maybe.bind(&2, Put, Put, m, p => Some{f(p)})
  )
    == Maybe.is_some(&2, Put, m): Bool
}:
  match m:
    case None{}:
      {==}
    case Some{q}:
      {==}

# the part c of a split of paths that part gives a subtree
def Tree.split_some.when(
  a: Nat,
  r1: List<&2, Nat>,
  b: Nat,
  r2: List<&2, Nat>,
  l: Put,
  o: Maybe<&2, Hashes.Hash>,
  c: Bool,
  ih: {
    Tree.split.ok(r1, r2) == True{}: Bool
  } -> {Maybe.is_some(&2, Put, Tree.split(r1, r2, l, o)) == True{}: Bool}
) -> {
  Shared.Bool.when(Bool, c, u => Tree.split.ok(r1, r2), u => True{}) == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Put,
    Shared.Bool.when(
      Maybe<&2, Put>,
      c,
      u => Maybe.bind(
        &2,
        Put,
        Put,
        Tree.split(r1, r2, l, o),
        p => Some{Put.into(Parts.none(), a, p)}
      ),
      u => Some{
        Put.node(
          Node.Branch{Parts.put(Parts.put(Parts.none(), a, Some{Put.root(l)}), b, o)},
          Put.nodes(l)
        )
      }
    )
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      e =>
        %Equal.sym(
          Bool,
          Maybe.is_some(
            &2,
            Put,
            Maybe.bind(
              &2,
              Put,
              Put,
              Tree.split(r1, r2, l, o),
              p => Some{Put.into(Parts.none(), a, p)}
            )
          ),
          Maybe.is_some(&2, Put, Tree.split(r1, r2, l, o)),
          Tree.some_then(Tree.split(r1, r2, l, o), p => Put.into(Parts.none(), a, p))
        ): {_ == True{}: Bool}
        ih(e)
    case False{}:
      e => {==}

# a split of paths that part gives a subtree
def Tree.split_some(
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +l: Put,
  +o: Maybe<&2, Hashes.Hash>
) -> {
  Tree.split.ok(p1, p2) == True{}: Bool
} -> {Maybe.is_some(&2, Put, Tree.split(p1, p2, l, o)) == True{}: Bool}:
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      Tree.split_some.when(a, r1, b, r2, l, o, Nat.is_eq(a, b), Tree.split_some(r1, r2, l, o))
    case Con{a, r1} Nil{}:
      e => Empty.absurd(
        {Maybe.is_some(&2, Put, Tree.split(a <> r1, [], l, o)) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case Nil{} w:
      e => Empty.absurd(
        {Maybe.is_some(&2, Put, Tree.split([], w, l, o)) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )

# a write along a path that the store holds, with no other key at its end,
# gives a subtree
# the part c of a write at a leaf of k2 gives a subtree, when the paths part
def Tree.set_some.leaf(
  q: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  c: Bool
) -> {
  Shared.Bool.when(
    Bool,
    c,
    u => True{},
    u => Tree.split.ok(q, List.drop(&2, Nat, Tree.path(k2), d))
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Put,
    Shared.Bool.when(
      Maybe<&2, Put>,
      c,
      u => Some{Put.node(Node.Leaf{k, v}, [])},
      w => Tree.split(q, List.drop(&2, Nat, Tree.path(k2), d), Put.node(Node.Leaf{k, v}, []), o)
    )
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      e => {==}
    case False{}:
      Tree.split_some(q, List.drop(&2, Nat, Tree.path(k2), d), Put.node(Node.Leaf{k, v}, []), o)

def Tree.set_some.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>
) -> {
  Tree.set.ok(~S, ~fetch, s, p, d, k, m) == True{}: Bool
} -> {Maybe.is_some(&2, Put, Tree.set.go(~S, ~fetch, s, p, d, k, v, o, m)) == True{}: Bool}:
  match p m:
    case q None{}:
      e => Empty.absurd(
        {Maybe.is_some(&2, Put, Tree.set.go(~S, ~fetch, s, q, d, k, v, o, None{})) == True{}: Bool},
        Shared.Bool.false_ne_true(e)
      )
    case q Some{Node.Empty{}}:
      e => {==}
    case q Some{Node.Leaf{+k2, v2}}:
      Tree.set_some.leaf(q, d, k, v, o, k2, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k))
    case Con{+x, +r} Some{Node.Branch{+ks}}:
      e =>
        %Equal.sym(
          Bool,
          Maybe.is_some(
            &2,
            Put,
            Maybe.bind(
              &2,
              Put,
              Put,
              Tree.set.go(
                ~S,
                ~fetch,
                s,
                r,
                1n+d,
                k,
                v,
                Parts.at(ks, x),
                Tree.part(~S, ~fetch, s, Parts.at(ks, x))
              ),
              p2 => Some{Put.into(ks, x, p2)}
            )
          ),
          Maybe.is_some(
            &2,
            Put,
            Tree.set.go(
              ~S,
              ~fetch,
              s,
              r,
              1n+d,
              k,
              v,
              Parts.at(ks, x),
              Tree.part(~S, ~fetch, s, Parts.at(ks, x))
            )
          ),
          Tree.some_then(
            Tree.set.go(
              ~S,
              ~fetch,
              s,
              r,
              1n+d,
              k,
              v,
              Parts.at(ks, x),
              Tree.part(~S, ~fetch, s, Parts.at(ks, x))
            ),
            p2 => Put.into(ks, x, p2)
          )
        ): {_ == True{}: Bool}
        Tree.set_some.go(
          ~S,
          ~fetch,
          s,
          r,
          1n+d,
          k,
          v,
          Parts.at(ks, x),
          Tree.part(~S, ~fetch, s, Parts.at(ks, x))
        )(e)
    case Nil{} Some{Node.Branch{ks}}:
      e => Empty.absurd(
        {
          Maybe.is_some(
            &2,
            Put,
            Tree.set.go(~S, ~fetch, s, [], d, k, v, o, Some{Node.Branch{ks}})
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(e)
      )

# a write gives a subtree when the store holds every node on the key's path,
# and no other key has the key's whole path
law Tree.set_some:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for v: List<&2, U32>
  {Tree.set.ok(~S, ~fetch, s, Tree.path(k), 0n, k, Tree.part(~S, ~fetch, s, h)) == True{}: Bool}
    -> {Maybe.is_some(&2, Put, Tree.set.plain(~S, ~fetch, s, h, k, v)) == True{}: Bool}

def Tree.set_some(ty, fetch, s, h, k, v):
  Tree.set_some.go(~ty, ~fetch, s, Tree.path(k), 0n, k, v, h, Tree.part(~ty, ~fetch, s, h))

# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the code of the parts of a branch
def Parts.codec() -> Codes.Codec(List<&2, Maybe<&2, Hashes.Hash>>):
  Codes.Code.list.codec(
    ~Maybe<&2, Hashes.Hash>,
    ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
  )

# a node reads back
def Node.code_read(
  n: Node,
  r: List<&2, U32>
) -> {
  Node.ok(n) == True{}: Bool
} -> {Node.code.read(Node.code(n, r)) == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>}:
  match n:
    case Node.Empty{}:
      ok => {==}
    case Node.Leaf{k, v}:
      ok => Codes.Code.two_read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        a => b => Node.Leaf{a, b},
        k,
        v,
        r
      )
    case Node.Branch{ks}:
      ok =>
        %Codes.Read.then_some(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Node,
          Codes.Codec.dec(
            List<&2, Maybe<&2, Hashes.Hash>>,
            Parts.codec()
          )(Codes.Codec.enc(List<&2, Maybe<&2, Hashes.Hash>>, Parts.codec())(ks)(r)),
          ps => r2 => Node.branch.of(ps, r2),
          ks,
          r,
          Codes.Codec.laws(List<&2, Maybe<&2, Hashes.Hash>>, Parts.codec())(ks)(r)
        ): {_ == Some{Codes.Read{Node.Branch{ks}, r}}: Maybe<&2, Codes.Read<Node>>}
        %Equal.sym(
          Bool,
          Parts.ok(ks),
          True{},
          ok
        ): {
          Shared.Maybe.when(
            Codes.Read<Node>,
            _,
            u => Some{Codes.Read{Node.Branch{ks}, r}}
          )
            == Some{Codes.Read{Node.Branch{ks}, r}}: Maybe<&2, Codes.Read<Node>>
        }
        {==}

# a node in its one code is the node of its words
law Node.of_words:
  for +n: Node
  {Node.ok(n) == True{}: Bool} -> {Node.of(Node.words(n)) == Some{n}: Maybe<&2, Node>}

def Node.of_words(n):
  ok =>
    %Equal.sym(
      Maybe<&2, Codes.Read<Node>>,
      Node.code.read(Node.words(n)),
      Some{Codes.Read{n, []}},
      Node.code_read(n, [])(ok)
    ): {Maybe.bind(&2, Codes.Read<Node>, Node, _, Node.of.read) == Some{n}: Maybe<&2, Node>}
    {==}

# a hash reads from its code only
def Hash.code_back(
  ts: List<&2, U32>,
  -h: Hashes.Hash,
  -r: List<&2, U32>
) -> {
  Hashes.Hash.code.read(ts) == Some{Codes.Read{h, r}}: Maybe<&2, Codes.Read<Hashes.Hash>>
} -> {Hashes.Hash.code(h, r) == ts: List<&2, U32>}:
  match ts:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{i, q}}}}}}}}:
      +k =>
        %Codes.Read.value_eq(
          Hashes.Hash,
          Hashes.Hash{a, b, c, d, e, f, g, i},
          h,
          q,
          r,
          k
        ): {Hashes.Hash.code(_, r) == a <> b <> c <> d <> e <> f <> g <> i <> q: List<&2, U32>}
        %Codes.Read.rest_eq(
          Hashes.Hash,
          Hashes.Hash{a, b, c, d, e, f, g, i},
          h,
          q,
          r,
          k
        ): {
          Hashes.Hash.code(
            Hashes.Hash{a, b, c, d, e, f, g, i},
            _
          )
            == a
            <> b
            <> c
            <> d
            <> e
            <> f
            <> g
            <> i
            <> q: List<&2, U32>
        }
        {==}
    case Nil{}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Nil{}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Nil{}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Con{c, Nil{}}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> c <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Con{c, Con{d, Nil{}}}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> c <> d <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Con{c, Con{d, Con{e, Nil{}}}}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> c <> d <> e <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Nil{}}}}}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> c <> d <> e <> f <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Nil{}}}}}}}}:
      k => Empty.absurd(
        {Hashes.Hash.code(h, r) == a <> b <> c <> d <> e <> f <> g <> []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Hashes.Hash>, Codes.Read{h, r}, k)
      )

# the parts of a branch read from their code only
def Parts.code_back() -> Codes.Code.Back(
  List<&2, Maybe<&2, Hashes.Hash>>,
  Parts.code,
  Parts.code.read
):
  Codes.Code.list_back(
    ~Maybe<&2, Hashes.Hash>,
    ~(m => r2 => Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, m, r2)),
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    ~Codes.Code.maybe_back(
      ~Hashes.Hash,
      ~Hashes.Hash.code,
      ~Hashes.Hash.code.read,
      ~(ts => h => r => Hash.code_back(ts, h, r))
    )
  )

# a branch of the parts ps that reads, reads as itself
def Node.branch.of_back(
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  r1: List<&2, U32>,
  -n: Node,
  -r: List<&2, U32>,
  c: Bool,
  ec: {Parts.ok(ps) == c: Bool}
) -> {
  Shared.Maybe.when(
    Codes.Read<Node>,
    c,
    u => Some{Codes.Read{Node.Branch{ps}, r1}}
  )
    == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
} -> {Some{Codes.Read{Node.Branch{ps}, r1}} == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>}:
  match c:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {
          Some{
            Codes.Read{Node.Branch{ps}, r1}
          }
            == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
        },
        Shared.Maybe.none_ne_some(Codes.Read<Node>, Codes.Read{n, r}, e)
      )

# a node whose tag is x, other than 0 and 1, reads from its code only
def Node.code_back.branch(
  x: U32,
  +q: List<&2, U32>,
  -n: Node,
  -r: List<&2, U32>,
  c: Bool,
  ec: {U32.is_eq(x, 2) == c: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    c,
    u => Codes.Read.then(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Node,
      Parts.code.read(q),
      ps => r2 => Node.branch.of(ps, r2)
    ),
    u => None{}
  )
    == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
} -> {Node.code(n, r) == x <> q: List<&2, U32>}:
  match c:
    case True{}:
      Codes.Read.then_back(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Node,
        Parts.code.read(q),
        ps => r2 => Node.branch.of(ps, r2),
        Codes.Read{n, r},
        {Node.code(n, r) == x <> q: List<&2, U32>},
        +ps => +r1 => em => ek =>
          +k2 = Node.branch.of_back(ps, r1, n, r, Parts.ok(ps), {==})(ek)
          %Codes.Read.value_eq(Node, Node.Branch{ps}, n, r1, r, k2): {Node.code(_, r) == x <> q: List<&2, U32>}
          %Codes.Read.rest_eq(Node, Node.Branch{ps}, n, r1, r, k2): {Node.code(Node.Branch{ps}, _) == x <> q: List<&2, U32>}
          %Equal.sym(U32, x, 2, Shared.U32.is_eq_sound(x, 2)(ec)): {Node.code(Node.Branch{ps}, r1) == _ <> q: List<&2, U32>}
          %Equal.sym(List<&2, U32>, Parts.code(ps, r1), q, Parts.code_back()(q)(ps)(r1)(em)): {2 <> _ == 2 <> q: List<&2, U32>}
          {==})
    case False{}:
      e => Empty.absurd(
        {Node.code(n, r) == x <> q: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Node>, Codes.Read{n, r}, e)
      )

# a node whose tag is x, other than 0, reads from its code only
def Node.code_back.leaf(
  +x: U32,
  +q: List<&2, U32>,
  -n: Node,
  -r: List<&2, U32>,
  c: Bool,
  ec: {U32.is_eq(x, 1) == c: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    c,
    u => Codes.Code.two.read(
      ~List<&2, U32>,
      ~List<&2, U32>,
      ~Node,
      ~Codes.Code.words.read,
      ~Codes.Code.words.read,
      k => v => Node.Leaf{k, v},
      q
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Node>>,
      U32.is_eq(x, 2),
      u => Codes.Read.then(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Node,
        Parts.code.read(q),
        ps => r2 => Node.branch.of(ps, r2)
      ),
      u => None{}
    )
  )
    == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
} -> {Node.code(n, r) == x <> q: List<&2, U32>}:
  match c:
    case True{}:
      Codes.Read.then_back(
        List<&2, U32>,
        Node,
        Codes.Code.words.read(q),
        k => r1 => Codes.Code.one.read(
          ~List<&2, U32>,
          ~Node,
          ~Codes.Code.words.read,
          v => Node.Leaf{k, v},
          r1
        ),
        Codes.Read{n, r},
        {Node.code(n, r) == x <> q: List<&2, U32>},
        k => +r1 => em1 => Codes.Read.then_back(
          List<&2, U32>,
          Node,
          Codes.Code.words.read(r1),
          v => r2 => Some{Codes.Read{Node.Leaf{k, v}, r2}},
          Codes.Read{n, r},
          {Node.code(n, r) == x <> q: List<&2, U32>},
          v => r2 => em2 => +ek =>
            %Codes.Read.value_eq(Node, Node.Leaf{k, v}, n, r2, r, ek): {Node.code(_, r) == x <> q: List<&2, U32>}
            %Codes.Read.rest_eq(Node, Node.Leaf{k, v}, n, r2, r, ek): {Node.code(Node.Leaf{k, v}, _) == x <> q: List<&2, U32>}
            %Equal.sym(U32, x, 1, Shared.U32.is_eq_sound(x, 1)(ec)): {Node.code(Node.Leaf{k, v}, r2) == _ <> q: List<&2, U32>}
            %Equal.sym(List<&2, U32>, Codes.Code.words(v, r2), r1, Codes.Code.words_back()(r1)(v)(r2)(em2)): {1 <> Codes.Code.words(k, _) == 1 <> q: List<&2, U32>}
            %Equal.sym(List<&2, U32>, Codes.Code.words(k, r1), q, Codes.Code.words_back()(q)(k)(r1)(em1)): {1 <> _ == 1 <> q: List<&2, U32>}
            {==})
      )
    case False{}:
      Node.code_back.branch(x, q, n, r, U32.is_eq(x, 2), {==})

# a node whose tag is x reads from its code only
def Node.code_back.of(
  +x: U32,
  q: List<&2, U32>,
  -n: Node,
  -r: List<&2, U32>,
  c: Bool,
  ec: {U32.is_eq(x, 0) == c: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    c,
    u => Some{Codes.Read{Node.Empty{}, q}},
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Node>>,
      U32.is_eq(x, 1),
      u => Codes.Code.two.read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.read,
        ~Codes.Code.words.read,
        k => v => Node.Leaf{k, v},
        q
      ),
      u => Shared.Bool.when(
        Maybe<&2, Codes.Read<Node>>,
        U32.is_eq(x, 2),
        u => Codes.Read.then(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Node,
          Parts.code.read(q),
          ps => r2 => Node.branch.of(ps, r2)
        ),
        u => None{}
      )
    )
  )
    == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
} -> {Node.code(n, r) == x <> q: List<&2, U32>}:
  match c:
    case True{}:
      +e =>
        %Codes.Read.value_eq(
          Node,
          Node.Empty{},
          n,
          q,
          r,
          e
        ): {Node.code(_, r) == x <> q: List<&2, U32>}
        %Codes.Read.rest_eq(
          Node,
          Node.Empty{},
          n,
          q,
          r,
          e
        ): {Node.code(Node.Empty{}, _) == x <> q: List<&2, U32>}
        %Equal.sym(U32, x, 0, Shared.U32.is_eq_sound(x, 0)(ec)): {0 <> q == _ <> q: List<&2, U32>}
        {==}
    case False{}:
      Node.code_back.leaf(x, q, n, r, U32.is_eq(x, 1), {==})

# a node reads from its code only
def Node.code_back(
  ts: List<&2, U32>,
  -n: Node,
  -r: List<&2, U32>
) -> {
  Node.code.read(ts) == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
} -> {Node.code(n, r) == ts: List<&2, U32>}:
  match ts:
    case Nil{}:
      e => Empty.absurd(
        {Node.code(n, r) == []: List<&2, U32>},
        Shared.Maybe.none_ne_some(Codes.Read<Node>, Codes.Read{n, r}, e)
      )
    case Con{+x, q}:
      Node.code_back.of(x, q, n, r, U32.is_eq(x, 0), {==})

# a read m that gives the node n, with nothing after it, reads n
def Node.of_back.at(
  m: Maybe<&2, Codes.Read<Node>>,
  -n: Node
) -> {
  Maybe.bind(&2, Codes.Read<Node>, Node, m, Node.of.read) == Some{n}: Maybe<&2, Node>
} -> {m == Some{Codes.Read{n, []}}: Maybe<&2, Codes.Read<Node>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {None{} == Some{Codes.Read{n, []}}: Maybe<&2, Codes.Read<Node>>},
        Shared.Maybe.none_ne_some(Node, n, e)
      )
    case Some{Codes.Read{n2, Nil{}}}:
      e =>
        %Shared.Maybe.some_inj(
          Node,
          n2,
          n,
          e
        ): {Some{Codes.Read{n2, []}} == Some{Codes.Read{_, []}}: Maybe<&2, Codes.Read<Node>>}
        {==}
    case Some{Codes.Read{n2, Con{y, ys}}}:
      e => Empty.absurd(
        {Some{Codes.Read{n2, y <> ys}} == Some{Codes.Read{n, []}}: Maybe<&2, Codes.Read<Node>>},
        Shared.Maybe.none_ne_some(Node, n, e)
      )

# the node of some words has those words: a node has one code
law Node.words_of:
  for +ws: List<&2, U32>
  for n: Node
  {Node.of(ws) == Some{n}: Maybe<&2, Node>} -> {Node.words(n) == ws: List<&2, U32>}

def Node.words_of(ws, n):
  e => Node.code_back(ws, n, [])(Node.of_back.at(Node.code.read(ws), n)(e))

# a part, then parts in their one code, are in their one code once trimmed
def Parts.ok_of(
  x: Maybe<&2, Hashes.Hash>,
  l: List<&2, Maybe<&2, Hashes.Hash>>
) -> {Parts.ok(l) == True{}: Bool} -> {Parts.ok(Parts.trim.of(x, l)) == True{}: Bool}:
  match x l:
    case None{} Nil{}:
      e => {==}
    case None{} Con{h, q}:
      e => e
    case Some{y} Nil{}:
      e => {==}
    case Some{y} Con{h, q}:
      e => e

# trimmed parts are in their one code
def Parts.ok_trim(
  ks: List<&2, Maybe<&2, Hashes.Hash>>
) -> {Parts.ok(Parts.trim(ks)) == True{}: Bool}:
  match ks:
    case Nil{}:
      {==}
    case Con{x, +r}:
      Parts.ok_of(x, Parts.trim(r))(Parts.ok_trim(r))

# trimming the part x before the parts l keeps each part
def Parts.at_of(
  x: Maybe<&2, Hashes.Hash>,
  l: List<&2, Maybe<&2, Hashes.Hash>>,
  z: Nat
) -> {Parts.at(Parts.trim.of(x, l), z) == Parts.at(x <> l, z): Maybe<&2, Hashes.Hash>}:
  match x l z:
    case None{} Nil{} 0n:
      {==}
    case None{} Nil{} 1n+p:
      {==}
    case None{} Con{h, q} w:
      {==}
    case Some{y} q w:
      {==}

# trimming keeps each part
def Parts.at_trim(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  z: Nat
) -> {Parts.at(Parts.trim(ks), z) == Parts.at(ks, z): Maybe<&2, Hashes.Hash>}:
  match ks z:
    case Nil{} w:
      {==}
    case Con{x, +r} 0n:
      Parts.at_of(x, Parts.trim(r), 0n)
    case Con{+x, +r} 1n+(+p):
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Parts.at(Parts.trim.of(x, Parts.trim(r)), 1n+p),
        Parts.at(x <> Parts.trim(r), 1n+p),
        Parts.at_of(x, Parts.trim(r), 1n+p)
      ): {_ == Parts.at(r, p): Maybe<&2, Hashes.Hash>}
      Parts.at_trim(r, p)

# the part n of parts whose part n was set to y is y
def Parts.at_set(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {Parts.at(Parts.set(ks, n, y), n) == y: Maybe<&2, Hashes.Hash>}:
  match ks n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Parts.at_set([], p, y)
    case Con{x, r} 0n:
      {==}
    case Con{x, r} 1n+p:
      Parts.at_set(r, p, y)

# the part z of parts whose part n was set to y: y if z is n, else as before
def Parts.at_set_pick(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  z: Nat,
  n: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.at(
    Parts.set(ks, n, y),
    z
  )
    == Bool.pick(
      Maybe<&2, Hashes.Hash>,
      Nat.is_eq(z, n),
      y,
      Parts.at(ks, z)
    ): Maybe<&2, Hashes.Hash>
}:
  match ks z n:
    case Nil{} 0n 0n:
      {==}
    case Nil{} 0n 1n+q:
      {==}
    case Nil{} 1n+p 0n:
      {==}
    case Nil{} 1n+p 1n+q:
      Parts.at_set_pick([], p, q, y)
    case Con{x, r} 0n 0n:
      {==}
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      Parts.at_set_pick(r, p, q, y)

# setting the part b does not change the part a, another part
def Parts.at_other(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  b: Nat,
  y: Maybe<&2, Hashes.Hash>,
  e: {Nat.is_eq(a, b) == False{}: Bool}
) -> {Parts.at(Parts.set(ks, b, y), a) == Parts.at(ks, a): Maybe<&2, Hashes.Hash>}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(Parts.set(ks, b, y), a),
    Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(a, b), y, Parts.at(ks, a)),
    Parts.at_set_pick(ks, a, b, y)
  ): {_ == Parts.at(ks, a): Maybe<&2, Hashes.Hash>}
  %Equal.sym(
    Bool,
    Nat.is_eq(a, b),
    False{},
    e
  ): {
    Bool.pick(
      Maybe<&2, Hashes.Hash>,
      _,
      y,
      Parts.at(ks, a)
    )
      == Parts.at(ks, a): Maybe<&2, Hashes.Hash>
  }
  {==}

# the part n of parts whose part n was put to y is y
def Parts.at_put(
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  +y: Maybe<&2, Hashes.Hash>
) -> {Parts.at(Parts.put(ks, n, y), n) == y: Maybe<&2, Hashes.Hash>}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(Parts.put(ks, n, y), n),
    Parts.at(Parts.set(ks, n, y), n),
    Parts.at_trim(Parts.set(ks, n, y), n)
  ): {_ == y: Maybe<&2, Hashes.Hash>}
  Parts.at_set(ks, n, y)

# the part z of parts whose part n was put to y: y if z is n, else as before
def Parts.at_put_pick(
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +z: Nat,
  +n: Nat,
  +y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.at(
    Parts.put(ks, n, y),
    z
  )
    == Bool.pick(
      Maybe<&2, Hashes.Hash>,
      Nat.is_eq(z, n),
      y,
      Parts.at(ks, z)
    ): Maybe<&2, Hashes.Hash>
}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(Parts.put(ks, n, y), z),
    Parts.at(Parts.set(ks, n, y), z),
    Parts.at_trim(Parts.set(ks, n, y), z)
  ): {
    _
      == Bool.pick(
        Maybe<&2, Hashes.Hash>,
        Nat.is_eq(z, n),
        y,
        Parts.at(ks, z)
      ): Maybe<&2, Hashes.Hash>
  }
  Parts.at_set_pick(ks, z, n, y)

# putting the part b does not change the part a, another part
def Parts.at_put_other(
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +a: Nat,
  +b: Nat,
  +y: Maybe<&2, Hashes.Hash>,
  e: {Nat.is_eq(a, b) == False{}: Bool}
) -> {Parts.at(Parts.put(ks, b, y), a) == Parts.at(ks, a): Maybe<&2, Hashes.Hash>}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(Parts.put(ks, b, y), a),
    Parts.at(Parts.set(ks, b, y), a),
    Parts.at_trim(Parts.set(ks, b, y), a)
  ): {_ == Parts.at(ks, a): Maybe<&2, Hashes.Hash>}
  Parts.at_other(ks, a, b, y, e)

# a branch of put parts is in its one code
def Node.ok_put(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {Node.ok(Node.Branch{Parts.put(ks, n, y)}) == True{}: Bool}:
  Parts.ok_trim(Parts.set(ks, n, y))

# a store that holds the words of the node n gives n for its hash
def Tree.has_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +n: Node,
  ok: {Node.ok(n) == True{}: Bool},
  e: {Stores.Store.has(~S, ~fetch, s, Node.words(n)) == True{}: Bool}
) -> {Tree.node(~S, ~fetch, s, Node.hash(n)) == Some{n}: Maybe<&2, Node>}:
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    fetch(s)(Node.hash(n)),
    Some{Node.words(n)},
    Shared.Maybe.is_eq_sound(
      ~List<&2, U32>,
      ~Shared.List.is_eq(~U32, ~U32.is_eq),
      x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
      fetch(s)(Node.hash(n)),
      Some{Node.words(n)}
    )(e)
  ): {Maybe.bind(&2, List<&2, U32>, Node, _, Node.of) == Some{n}: Maybe<&2, Node>}
  Node.of_words(n)(ok)

# a read of the key k at the leaf of k1 and v1 gives v1 if k1 is k
def Tree.get.go_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  k1: List<&2, U32>,
  v1: List<&2, U32>
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    p,
    k,
    Some{Node.Leaf{k1, v1}}
  )
    == Shared.Maybe.when(
      List<&2, U32>,
      Shared.List.is_eq(~U32, ~U32.is_eq, k1, k),
      u => Some{v1}
    ): Maybe<&2, List<&2, U32>>
}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a read of the key k at the leaf of k and v gives v
def Tree.read_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> {Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Leaf{k, v}}) == Some{v}: Maybe<&2, List<&2, U32>>}:
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Leaf{k, v}}),
    Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k, k), u => Some{v}),
    Tree.get.go_leaf(~S, ~fetch, s, p, k, k, v)
  ): {_ == Some{v}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
  ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == Some{v}: Maybe<&2, List<&2, U32>>}
  {==}

# what a read of the key k along p gives at the root of the new subtree r
# (none: a write that failed), in any store s2 that holds its nodes: w
def Tree.Reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  w: Maybe<&2, List<&2, U32>>,
  r: Maybe<&2, Put>
) -> Type:
  match r:
    case None{}:
      Unit
    case Some{q}:
      {
        Stores.Store.holds(~S, ~fetch, s2, Put.nodes(q)) == True{}: Bool
      } -> {
        Tree.get.go(
          ~S,
          ~fetch,
          s2,
          p,
          k,
          Tree.node(~S, ~fetch, s2, Put.root(q))
        )
          == w: Maybe<&2, List<&2, U32>>
      }

# a part m that reads as wi along pi, then f, reads as wo along po, when each
# part q that reads as wi along pi gives a part f(q) that reads as wo along po
def Tree.reads_then(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s2: S,
  -pi: List<&2, Nat>,
  -po: List<&2, Nat>,
  -k: List<&2, U32>,
  -wi: Maybe<&2, List<&2, U32>>,
  -wo: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Put>,
  -f: Put -> Maybe<&2, Put>,
  g: @q: Put -> Tree.Reads(
    ~S,
    ~fetch,
    s2,
    pi,
    k,
    wi,
    Some{q}
  ) -> Tree.Reads(~S, ~fetch, s2, po, k, wo, f(q)),
  i: Tree.Reads(~S, ~fetch, s2, pi, k, wi, m)
) -> Tree.Reads(~S, ~fetch, s2, po, k, wo, Maybe.bind(&2, Put, Put, m, f)):
  match m:
    case None{}:
      Unit{}
    case Some{q}:
      g(q)(i)

# the new leaf of k and v reads as v along any path
def Tree.read_new_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  p: List<&2, Nat>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> Tree.Reads(~S, ~fetch, s2, p, k, Some{v}, Some{Put.node(Node.Leaf{k, v}, [])}):
  e =>
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(Node.Leaf{k, v})),
      Some{Node.Leaf{k, v}},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        Node.Leaf{k, v},
        {==},
        Shared.List.all.if_hit(
          Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k, v})),
          u => True{}
        )(e)
      )
    ): {Tree.get.go(~S, ~fetch, s2, p, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
    Tree.read_leaf(~S, ~fetch, s2, p, k, v)

# a new branch of parts ks whose part n is the new subtree q reads along x then
# r as q reads along r, when x is n
def Tree.read_into(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  x: Nat,
  r: List<&2, Nat>,
  k: List<&2, U32>,
  -w: Maybe<&2, List<&2, U32>>,
  +q: Put,
  ez: {x == n: Nat},
  ih: Tree.Reads(~S, ~fetch, s2, r, k, w, Some{q})
) -> Tree.Reads(~S, ~fetch, s2, Con{x, r}, k, w, Some{Put.into(ks, n, q)}):
  +e =>
    +b = {Node.Branch{Parts.put(ks, n, Some{Put.root(q)})}: Node}
    +rest = Stores.Store.holds(~S, ~fetch, s2, Put.nodes(q))
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(b)),
      Some{b},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        b,
        Node.ok_put(ks, n, Some{Put.root(q)}),
        Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(b)), u => rest)(e)
      )
    ): {Tree.get.go(~S, ~fetch, s2, Con{x, r}, k, _) == w: Maybe<&2, List<&2, U32>>}
    %Equal.sym(
      Nat,
      x,
      n,
      ez
    ): {
      Tree.get.go(
        ~S,
        ~fetch,
        s2,
        r,
        k,
        Tree.part(~S, ~fetch, s2, Parts.at(Parts.put(ks, n, Some{Put.root(q)}), _))
      )
        == w: Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Parts.at(Parts.put(ks, n, Some{Put.root(q)}), n),
      Some{Put.root(q)},
      Parts.at_put(ks, n, Some{Put.root(q)})
    ): {
      Tree.get.go(~S, ~fetch, s2, r, k, Tree.part(~S, ~fetch, s2, _)) == w: Maybe<&2, List<&2, U32>>
    }
    ih(Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(b)), u => rest)(e))

# the subtree c of Tree.split, with the new leaf of k and v, reads as v along a
# then r1
def Tree.read_split.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +a: Nat,
  +r1: List<&2, Nat>,
  +b: Nat,
  r2: List<&2, Nat>,
  +o: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  c: Bool,
  ec: {Nat.is_eq(a, b) == c: Bool},
  ih: Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r1,
    k,
    Some{v},
    Tree.split(r1, r2, Put.node(Node.Leaf{k, v}, []), o)
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{a, r1},
  k,
  Some{v},
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(r1, r2, Put.node(Node.Leaf{k, v}, []), o),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{Parts.put(Parts.put(Parts.none(), a, Some{Node.hash(Node.Leaf{k, v})}), b, o)},
        [Node.words(Node.Leaf{k, v})]
      )
    }
  )
):
  match c:
    case True{}:
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r1,
        Con{a, r1},
        k,
        Some{v},
        Some{v},
        Tree.split(r1, r2, Put.node(Node.Leaf{k, v}, []), o),
        p => Some{Put.into(Parts.none(), a, p)},
        q => iq => Tree.read_into(~S, ~fetch, s2, Parts.none(), a, a, r1, k, Some{v}, q, {==}, iq),
        ih
      )
    case False{}:
      +e =>
        +l = {Node.Leaf{k, v}: Node}
        +ka = Parts.put(Parts.none(), a, Some{Node.hash(l)})
        +n = {Node.Branch{Parts.put(ka, b, o)}: Node}
        +rest = Stores.Store.holds(~S, ~fetch, s2, [Node.words(l)])
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Node.ok_put(ka, b, o),
            Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
          )
        ): {Tree.get.go(~S, ~fetch, s2, Con{a, r1}, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Parts.at(Parts.put(ka, b, o), a),
          Parts.at(ka, a),
          Parts.at_put_other(ka, a, b, o, ec)
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r1,
            k,
            Tree.part(~S, ~fetch, s2, _)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Parts.at(ka, a),
          Some{Node.hash(l)},
          Parts.at_put(Parts.none(), a, Some{Node.hash(l)})
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r1,
            k,
            Tree.part(~S, ~fetch, s2, _)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(l)),
          Some{l},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            l,
            {==},
            Shared.List.all.if_hit(
              Stores.Store.has(~S, ~fetch, s2, Node.words(l)),
              u => True{}
            )(
              Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
            )
          )
        ): {Tree.get.go(~S, ~fetch, s2, r1, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        Tree.read_leaf(~S, ~fetch, s2, r1, k, v)

# Tree.split, with the new leaf of k and v, reads as v along p1
def Tree.read_split(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +o: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p1,
  k,
  Some{v},
  Tree.split(p1, p2, Put.node(Node.Leaf{k, v}, []), o)
):
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      Tree.read_split.when(
        ~S,
        ~fetch,
        s2,
        a,
        r1,
        b,
        r2,
        o,
        k,
        v,
        Nat.is_eq(a, b),
        {==},
        Tree.read_split(~S, ~fetch, s2, r1, r2, o, k, v)
      )
    case Con{a, r1} Nil{}:
      Unit{}
    case Nil{} w:
      Unit{}

# the subtree c of Tree.set.go, at a leaf of k2, reads as v along q
def Tree.set_reads.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  q: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  k2: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  c: Bool
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  q,
  k,
  Some{v},
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Some{Put.node(Node.Leaf{k, v}, [])},
    w => Tree.split(q, List.drop(&2, Nat, Tree.path(k2), d), Put.node(Node.Leaf{k, v}, []), o)
  )
):
  match c:
    case True{}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v)
    case False{}:
      Tree.read_split(~S, ~fetch, s2, q, List.drop(&2, Nat, Tree.path(k2), d), o, k, v)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# Tree.set.go from the part o, whose node is m in the store s, with k set to v,
# reads as v along p, in any store s2 that holds its nodes
def Tree.set_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +s2: S,
  p: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>
) -> Tree.Reads(~S, ~fetch, s2, p, k, Some{v}, Tree.set.go(~S, ~fetch, s, p, d, k, v, o, m)):
  match p m:
    case q None{}:
      Unit{}
    case q Some{Node.Empty{}}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v)
    case q Some{Node.Leaf{+k2, v2}}:
      Tree.set_reads.when(
        ~S,
        ~fetch,
        s2,
        q,
        d,
        k,
        v,
        k2,
        o,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k)
      )
    case Con{+x, +r} Some{Node.Branch{+ks}}:
      +kid = Parts.at(ks, x)
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r,
        Con{x, r},
        k,
        Some{v},
        Some{v},
        Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
        p2 => Some{Put.into(ks, x, p2)},
        q => iq => Tree.read_into(~S, ~fetch, s2, ks, x, x, r, k, Some{v}, q, {==}, iq),
        Tree.set_reads(~S, ~fetch, s, s2, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid))
      )
    case Nil{} Some{Node.Branch{ks}}:
      Unit{}

# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# after the key k is set to v in the tree whose root is h in the store s, a
# read of k at the new root gives v, in any store s2 that holds the new nodes
law Tree.get_set:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for s2: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for v: List<&2, U32>
  for t: Put
  {Tree.set.plain(~S, ~fetch, s, h, k, v) == Some{t}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {Tree.get.plain(~S, ~fetch, s2, Some{Put.root(t)}, k) == Some{v}: Maybe<&2, List<&2, U32>>}

def Tree.get_set(ty, fetch, s, s2, h, k, v, t):
  e =>
    %e: Tree.Reads(~ty, ~fetch, s2, Tree.path(k), k, Some{v}, _)
    Tree.set_reads(~ty, ~fetch, s, s2, Tree.path(k), 0n, k, v, h, Tree.part(~ty, ~fetch, s, h))

# a store b that grows from a gives each node that a gives
def Tree.node_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +a: S,
  b: S,
  +h: Hashes.Hash,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.node(~S, ~fetch, a, h) == Some{n}: Maybe<&2, Node>
} -> {Tree.node(~S, ~fetch, b, h) == Some{n}: Maybe<&2, Node>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Node,
    fetch(a)(h),
    fetch(b)(h),
    Node.of,
    Node.of,
    n,
    w => kept(a)(b)(h)(w)(gr),
    w => e => e
  )

# a store b that grows from a gives each node of a part that a gives
def Tree.part_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  a: S,
  b: S,
  x: Maybe<&2, Hashes.Hash>,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.part(~S, ~fetch, a, x) == Some{n}: Maybe<&2, Node>
} -> {Tree.part(~S, ~fetch, b, x) == Some{n}: Maybe<&2, Node>}:
  match x:
    case None{}:
      e => e
    case Some{h}:
      Tree.node_kept(~S, ~fetch, ~grows, ~kept, a, b, h, n, gr)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# a read of the key k at the node m in a store a gives the same in a store b
# that grows from a, at a node m2 that b gives where a gives m
def Tree.get.go_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +a: S,
  +b: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  m: Maybe<&2, Node>,
  -m2: Maybe<&2, Node>,
  -x: List<&2, U32>,
  hm: @n: Node -> {m == Some{n}: Maybe<&2, Node>} -> {m2 == Some{n}: Maybe<&2, Node>},
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.get.go(~S, ~fetch, a, p, k, m) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Tree.get.go(~S, ~fetch, b, p, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match p m:
    case q None{}:
      e => Empty.absurd(
        {Tree.get.go(~S, ~fetch, b, q, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case q Some{Node.Empty{}}:
      e => Empty.absurd(
        {Tree.get.go(~S, ~fetch, b, q, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case q Some{Node.Leaf{k2, v}}:
      e =>
        %Equal.sym(
          Maybe<&2, Node>,
          m2,
          Some{Node.Leaf{k2, v}},
          hm(Node.Leaf{k2, v})({==})
        ): {Tree.get.go(~S, ~fetch, b, q, k, _) == Some{x}: Maybe<&2, List<&2, U32>>}
        e
    case Nil{} Some{Node.Branch{ks}}:
      e => Empty.absurd(
        {Tree.get.go(~S, ~fetch, b, [], k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case Con{+y, r} Some{Node.Branch{+ks}}:
      e =>
        %Equal.sym(
          Maybe<&2, Node>,
          m2,
          Some{Node.Branch{ks}},
          hm(Node.Branch{ks})({==})
        ): {Tree.get.go(~S, ~fetch, b, Con{y, r}, k, _) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tree.get.go_kept(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          a,
          b,
          r,
          k,
          Tree.part(~S, ~fetch, a, Parts.at(ks, y)),
          Tree.part(~S, ~fetch, b, Parts.at(ks, y)),
          x,
          n => Tree.part_kept(~S, ~fetch, ~grows, ~kept, a, b, Parts.at(ks, y), n, gr),
          gr
        )(e)

# a read that a store gives, a store that grows from it gives too
law Tree.get_grows:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +a: S
  for +b: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for x: List<&2, U32>
  {grows(a, b) == True{}: Bool}
    -> {Tree.get.plain(~S, ~fetch, a, h, k) == Some{x}: Maybe<&2, List<&2, U32>>}
    -> {Tree.get.plain(~S, ~fetch, b, h, k) == Some{x}: Maybe<&2, List<&2, U32>>}

def Tree.get_grows(ty, fetch, grows, kept, a, b, h, k, x):
  +gr => Tree.get.go_kept(
    ~ty,
    ~fetch,
    ~grows,
    ~kept,
    a,
    b,
    Tree.path(k),
    k,
    Tree.part(~ty, ~fetch, a, h),
    Tree.part(~ty, ~fetch, b, h),
    x,
    n => Tree.part_kept(~ty, ~fetch, ~grows, ~kept, a, b, h, n, gr),
    gr
  )

# a new branch of parts ks, whose part n is a new subtree, reads as nothing at
# its end
def Tree.read_into_nil(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  k: List<&2, U32>,
  m: Maybe<&2, Put>
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  [],
  k,
  None{},
  Maybe.bind(&2, Put, Put, m, p => Some{Put.into(ks, n, p)})
):
  match m:
    case None{}:
      Unit{}
    case Some{+q}:
      +e =>
        +b = {Node.Branch{Parts.put(ks, n, Some{Put.root(q)})}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(b)),
          Some{b},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            b,
            Node.ok_put(ks, n, Some{Put.root(q)}),
            Shared.List.all.if_hit(
              Stores.Store.has(~S, ~fetch, s2, Node.words(b)),
              u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(q))
            )(e)
          )
        ): {Tree.get.go(~S, ~fetch, s2, [], k, _) == None{}: Maybe<&2, List<&2, U32>>}
        {==}

# a new branch of parts ks whose part n is the new subtree q reads along z then r
# as the part z of ks, when z is not n
def Tree.read_into_off(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  z: Nat,
  r: List<&2, Nat>,
  k: List<&2, U32>,
  +q: Put,
  ec: {Nat.is_eq(z, n) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{z, r},
  k,
  Tree.get.go(~S, ~fetch, s2, r, k, Tree.part(~S, ~fetch, s2, Parts.at(ks, z))),
  Some{Put.into(ks, n, q)}
):
  +e =>
    +b = {Node.Branch{Parts.put(ks, n, Some{Put.root(q)})}: Node}
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(b)),
      Some{b},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        b,
        Node.ok_put(ks, n, Some{Put.root(q)}),
        Shared.List.all.if_hit(
          Stores.Store.has(~S, ~fetch, s2, Node.words(b)),
          u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(q))
        )(e)
      )
    ): {
      Tree.get.go(
        ~S,
        ~fetch,
        s2,
        Con{z, r},
        k,
        _
      )
        == Tree.get.go(
          ~S,
          ~fetch,
          s2,
          r,
          k,
          Tree.part(~S, ~fetch, s2, Parts.at(ks, z))
        ): Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Parts.at(Parts.put(ks, n, Some{Put.root(q)}), z),
      Parts.at(ks, z),
      Parts.at_put_other(ks, z, n, Some{Put.root(q)}, ec)
    ): {
      Tree.get.go(
        ~S,
        ~fetch,
        s2,
        r,
        k,
        Tree.part(~S, ~fetch, s2, _)
      )
        == Tree.get.go(
          ~S,
          ~fetch,
          s2,
          r,
          k,
          Tree.part(~S, ~fetch, s2, Parts.at(ks, z))
        ): Maybe<&2, List<&2, U32>>
    }
    {==}

# a read of the key k2 at the leaf of another key k gives nothing
def Tree.get.go_leaf_off(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k2: List<&2, U32>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> {Tree.get.go(~S, ~fetch, s, p, k2, Some{Node.Leaf{k, v}}) == None{}: Maybe<&2, List<&2, U32>>}:
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Tree.get.go(~S, ~fetch, s, p, k2, Some{Node.Leaf{k, v}}),
    Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k, k2), u => Some{v}),
    Tree.get.go_leaf(~S, ~fetch, s, p, k2, k, v)
  ): {_ == None{}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
    False{},
    ne
  ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == None{}: Maybe<&2, List<&2, U32>>}
  {==}

# a read at an empty part of a new branch gives nothing
def Tree.get.go_none_part(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  r: List<&2, Nat>,
  k: List<&2, U32>,
  z: Nat
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    r,
    k,
    Tree.part(~S, ~fetch, s, Parts.at(Parts.none(), z))
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
  Tree.get.go_empty(~S, ~fetch, s, r, k)

# the new leaf of k and v reads as nothing for another key k2
def Tree.read_new_leaf_off(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  p: List<&2, Nat>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  k2: List<&2, U32>,
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(~S, ~fetch, s2, p, k2, None{}, Some{Put.node(Node.Leaf{k, v}, [])}):
  e =>
    +l = {Node.Leaf{k, v}: Node}
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(l)),
      Some{l},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        l,
        {==},
        Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(l)), u => True{})(e)
      )
    ): {Tree.get.go(~S, ~fetch, s2, p, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
    Tree.get.go_leaf_off(~S, ~fetch, s2, p, k2, k, v, ne)

# the subtree c of Tree.split reads along b then r2, the path of the part o
# already there, as o's leaf of k1 and v1 reads
def Tree.other_split_old.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +a: Nat,
  r1: List<&2, Nat>,
  +b: Nat,
  +r2: List<&2, Nat>,
  +l: Put,
  +o: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  k1: List<&2, U32>,
  v1: List<&2, U32>,
  c: Bool,
  ec: {Nat.is_eq(a, b) == c: Bool},
  eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  ih: Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r2,
    k2,
    Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
    Tree.split(r1, r2, l, o)
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{b, r2},
  k2,
  Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(r1, r2, l, o),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{Parts.put(Parts.put(Parts.none(), a, Some{Put.root(l)}), b, o)},
        Put.nodes(l)
      )
    }
  )
):
  match c:
    case True{}:
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{b, r2},
        k2,
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Tree.split(r1, r2, l, o),
        p => Some{Put.into(Parts.none(), a, p)},
        q => iq => Tree.read_into(
          ~S,
          ~fetch,
          s2,
          Parts.none(),
          a,
          b,
          r2,
          k2,
          Shared.Maybe.when(
            List<&2, U32>,
            Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
            u => Some{v1}
          ),
          q,
          Equal.sym(Nat, a, b, Shared.Nat.is_eq_sound(a, b)(ec)),
          iq
        ),
        ih
      )
    case False{}:
      +e =>
        +ka = Parts.put(Parts.none(), a, Some{Put.root(l)})
        +n = {Node.Branch{Parts.put(ka, b, o)}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Node.ok_put(ka, b, o),
            Shared.List.all.if_hit(
              Stores.Store.has(~S, ~fetch, s2, Node.words(n)),
              u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(l))
            )(e)
          )
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            Con{b, r2},
            k2,
            _
          )
            == Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
              u => Some{v1}
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Parts.at(Parts.put(ka, b, o), b),
          o,
          Parts.at_put(ka, b, o)
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.part(~S, ~fetch, s2, _)
          )
            == Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
              u => Some{v1}
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.part(~S, ~fetch, s2, o),
          Some{Node.Leaf{k1, v1}},
          eo
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            _
          )
            == Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
              u => Some{v1}
            ): Maybe<&2, List<&2, U32>>
        }
        Tree.get.go_leaf(~S, ~fetch, s2, r2, k2, k1, v1)

# Tree.split reads along p2, the path of the part o already there, as o's
# leaf of k1 and v1 reads
def Tree.other_split_old(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +l: Put,
  +o: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
  Tree.split(p1, p2, l, o)
):
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      Tree.other_split_old.when(
        ~S,
        ~fetch,
        s2,
        a,
        r1,
        b,
        r2,
        l,
        o,
        k2,
        k1,
        v1,
        Nat.is_eq(a, b),
        {==},
        eo,
        Tree.other_split_old(~S, ~fetch, s2, r1, r2, l, o, k2, k1, v1, eo)
      )
    case Con{a, r1} Nil{}:
      Unit{}
    case Nil{} w:
      Unit{}

# a read of k2 at a part picked from the old part o (a leaf of k1 and v1), the
# new leaf of hash h (of k and v) and an empty part gives nothing
def Tree.other_pick(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  r: List<&2, Nat>,
  k2: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  h: Hashes.Hash,
  z: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  k1: List<&2, U32>,
  v1: List<&2, U32>,
  c1: Bool,
  c2: Bool,
  eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  eh: {Tree.node(~S, ~fetch, s2, h) == Some{Node.Leaf{k, v}}: Maybe<&2, Node>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool}
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s2,
    r,
    k2,
    Tree.part(
      ~S,
      ~fetch,
      s2,
      Bool.pick(
        Maybe<&2, Hashes.Hash>,
        c1,
        o,
        Bool.pick(Maybe<&2, Hashes.Hash>, c2, Some{h}, Parts.at(Parts.none(), z))
      )
    )
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
  match c1 c2:
    case True{} w:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.part(~S, ~fetch, s2, o),
        Some{Node.Leaf{k1, v1}},
        eo
      ): {Tree.get.go(~S, ~fetch, s2, r, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
      Tree.get.go_leaf_off(~S, ~fetch, s2, r, k2, k1, v1, n1)
    case False{} True{}:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.node(~S, ~fetch, s2, h),
        Some{Node.Leaf{k, v}},
        eh
      ): {Tree.get.go(~S, ~fetch, s2, r, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
      Tree.get.go_leaf_off(~S, ~fetch, s2, r, k2, k, v, ne)
    case False{} False{}:
      Tree.get.go_none_part(~S, ~fetch, s2, r, k2, z)

# a new branch made by Tree.split along a and the new subtree m reads as nothing
# for k2 along z then r2, when m reads as nothing along r2
def Tree.other_split_new.into(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +n: Nat,
  +z: Nat,
  +r2: List<&2, Nat>,
  +k2: List<&2, U32>,
  m: Maybe<&2, Put>,
  c: Bool,
  ec: {Nat.is_eq(z, n) == c: Bool},
  ih: Tree.Reads(~S, ~fetch, s2, r2, k2, None{}, m)
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{z, r2},
  k2,
  None{},
  Maybe.bind(&2, Put, Put, m, p => Some{Put.into(Parts.none(), n, p)})
):
  match c:
    case True{}:
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        None{},
        None{},
        m,
        p => Some{Put.into(Parts.none(), n, p)},
        q => iq => Tree.read_into(
          ~S,
          ~fetch,
          s2,
          Parts.none(),
          n,
          z,
          r2,
          k2,
          None{},
          q,
          Shared.Nat.is_eq_sound(z, n)(ec),
          iq
        ),
        ih
      )
    case False{}:
      %Tree.get.go_none_part(
        ~S,
        ~fetch,
        s2,
        r2,
        k2,
        z
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        Con{z, r2},
        k2,
        _,
        Maybe.bind(&2, Put, Put, m, p => Some{Put.into(Parts.none(), n, p)})
      )
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        None{},
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(Parts.none(), z))),
        m,
        p => Some{Put.into(Parts.none(), n, p)},
        q => iq => Tree.read_into_off(~S, ~fetch, s2, Parts.none(), n, z, r2, k2, q, ec),
        ih
      )

# the subtree c of Tree.split, with the new leaf of k and v, reads as nothing
# at its end
def Tree.other_split_new.nil(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +a: Nat,
  r1: List<&2, Nat>,
  +b: Nat,
  r1o: List<&2, Nat>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  c: Bool
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  [],
  k2,
  None{},
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(r1, r1o, Put.node(Node.Leaf{k, v}, []), o),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{
          Parts.put(
            Parts.put(Parts.none(), a, Some{Hashes.Sha.hash(Node.words(Node.Leaf{k, v}))}),
            b,
            o
          )
        },
        [Node.words(Node.Leaf{k, v})]
      )
    }
  )
):
  match c:
    case True{}:
      Tree.read_into_nil(
        ~S,
        ~fetch,
        s2,
        Parts.none(),
        a,
        k2,
        Tree.split(r1, r1o, Put.node(Node.Leaf{k, v}, []), o)
      )
    case False{}:
      +e =>
        +l = {Node.Leaf{k, v}: Node}
        +n = {Node.Branch{Parts.put(Parts.put(Parts.none(), a, Some{Node.hash(l)}), b, o)}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Node.ok_put(Parts.put(Parts.none(), a, Some{Node.hash(l)}), b, o),
            Shared.List.all.if_hit(
              Stores.Store.has(~S, ~fetch, s2, Node.words(n)),
              u => Stores.Store.holds(~S, ~fetch, s2, [Node.words(l)])
            )(e)
          )
        ): {Tree.get.go(~S, ~fetch, s2, [], k2, _) == None{}: Maybe<&2, List<&2, U32>>}
        {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement; a proof does not run
# the subtree c of Tree.split, with the new leaf of k and v, reads as nothing for
# another key k2 along z then r2, when o is a leaf of another key k1
def Tree.other_split_new.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +a: Nat,
  r1: List<&2, Nat>,
  +b: Nat,
  r1o: List<&2, Nat>,
  +z: Nat,
  r2: List<&2, Nat>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  k1: List<&2, U32>,
  v1: List<&2, U32>,
  c: Bool,
  ec: {Nat.is_eq(a, b) == c: Bool},
  eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool},
  ih: Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r2,
    k2,
    None{},
    Tree.split(r1, r1o, Put.node(Node.Leaf{k, v}, []), o)
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{z, r2},
  k2,
  None{},
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(r1, r1o, Put.node(Node.Leaf{k, v}, []), o),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{
          Parts.put(
            Parts.put(Parts.none(), a, Some{Hashes.Sha.hash(Node.words(Node.Leaf{k, v}))}),
            b,
            o
          )
        },
        [Node.words(Node.Leaf{k, v})]
      )
    }
  )
):
  match c:
    case True{}:
      Tree.other_split_new.into(
        ~S,
        ~fetch,
        s2,
        a,
        z,
        r2,
        k2,
        Tree.split(r1, r1o, Put.node(Node.Leaf{k, v}, []), o),
        Nat.is_eq(z, a),
        {==},
        ih
      )
    case False{}:
      +e =>
        +l = {Node.Leaf{k, v}: Node}
        +ka = Parts.put(Parts.none(), a, Some{Node.hash(l)})
        +n = {Node.Branch{Parts.put(ka, b, o)}: Node}
        +rest = Stores.Store.holds(~S, ~fetch, s2, [Node.words(l)])
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Node.ok_put(ka, b, o),
            Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
          )
        ): {Tree.get.go(~S, ~fetch, s2, Con{z, r2}, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Parts.at(Parts.put(ka, b, o), z),
          Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(z, b), o, Parts.at(ka, z)),
          Parts.at_put_pick(ka, z, b, o)
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.part(~S, ~fetch, s2, _)
          )
            == None{}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Parts.at(ka, z),
          Bool.pick(
            Maybe<&2, Hashes.Hash>,
            Nat.is_eq(z, a),
            Some{Node.hash(l)},
            Parts.at(Parts.none(), z)
          ),
          Parts.at_put_pick(Parts.none(), z, a, Some{Node.hash(l)})
        ): {
          Tree.get.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.part(~S, ~fetch, s2, Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(z, b), o, _))
          )
            == None{}: Maybe<&2, List<&2, U32>>
        }
        Tree.other_pick(
          ~S,
          ~fetch,
          s2,
          r2,
          k2,
          o,
          Node.hash(l),
          z,
          k,
          v,
          k1,
          v1,
          Nat.is_eq(z, b),
          Nat.is_eq(z, a),
          eo,
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            l,
            {==},
            Shared.List.all.if_hit(
              Stores.Store.has(~S, ~fetch, s2, Node.words(l)),
              u => True{}
            )(
              Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
            )
          ),
          ne,
          n1
        )

# Tree.split, with the new leaf of k and v and the old part o, a leaf of k1,
# reads as nothing for a key k2 that is neither, along any path p2
def Tree.other_split_new(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  p1: List<&2, Nat>,
  p1o: List<&2, Nat>,
  p2: List<&2, Nat>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  +ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  +n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  None{},
  Tree.split(p1, p1o, Put.node(Node.Leaf{k, v}, []), o)
):
  match p1 p1o p2:
    case Con{+a, +r1} Con{+b, +r1o} Nil{}:
      Tree.other_split_new.nil(~S, ~fetch, s2, a, r1, b, r1o, k, v, o, k2, Nat.is_eq(a, b))
    case Con{+a, +r1} Con{+b, +r1o} Con{z, +r2}:
      Tree.other_split_new.con(
        ~S,
        ~fetch,
        s2,
        a,
        r1,
        b,
        r1o,
        z,
        r2,
        k,
        v,
        o,
        k2,
        k1,
        v1,
        Nat.is_eq(a, b),
        {==},
        eo,
        ne,
        n1,
        Tree.other_split_new(~S, ~fetch, s2, r1, r1o, r2, k, v, o, k2, k1, v1, eo, ne, n1)
      )
    case Con{a, r1} Nil{} w:
      Unit{}
    case Nil{} w x:
      Unit{}

# the part Tree.split, after the leaf of k1 and v1 already there, reads for
# another key k2 along its path p2 as that leaf reads
def Tree.set_keeps.split(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  q: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  +k1: List<&2, U32>,
  v1: List<&2, U32>,
  +k2: List<&2, U32>,
  p2: List<&2, Nat>,
  c: Bool,
  +ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == c: Bool},
  eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
  Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.Leaf{k, v}, []), o)
):
  match c:
    case True{}:
      %hp: Tree.Reads(
        ~S,
        ~fetch,
        s2,
        _,
        k2,
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.Leaf{k, v}, []), o)
      )
      %Shared.List.is_eq_sound(
        ~U32,
        ~U32.is_eq,
        ~Shared.U32.laws(),
        k1,
        k2
      )(
        ec
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        List.drop(&2, Nat, Tree.path(_), d),
        k2,
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.Leaf{k, v}, []), o)
      )
      Tree.other_split_old(
        ~S,
        ~fetch,
        s2,
        q,
        List.drop(&2, Nat, Tree.path(k1), d),
        Put.node(Node.Leaf{k, v}, []),
        o,
        k2,
        k1,
        v1,
        eo
      )
    case False{}:
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
        False{},
        ec
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Shared.Maybe.when(List<&2, U32>, _, u => Some{v1}),
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.Leaf{k, v}, []), o)
      )
      Tree.other_split_new(
        ~S,
        ~fetch,
        s2,
        q,
        List.drop(&2, Nat, Tree.path(k1), d),
        p2,
        k,
        v,
        o,
        k2,
        k1,
        v1,
        eo,
        ne,
        ec
      )

# the subtree c of Tree.set.go at the leaf of k1 and v1 reads for another key k2
# along its path p2 as that leaf reads
def Tree.set_keeps.leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  q: List<&2, Nat>,
  d: Nat,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  +k1: List<&2, U32>,
  v1: List<&2, U32>,
  +k2: List<&2, U32>,
  p2: List<&2, Nat>,
  c: Bool,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k) == c: Bool},
  eo: {Tree.part(~S, ~fetch, s2, o) == Some{Node.Leaf{k1, v1}}: Maybe<&2, Node>},
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  +ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Some{Put.node(Node.Leaf{k, v}, [])},
    w => Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.Leaf{k, v}, []), o)
  )
):
  match c:
    case True{}:
      %Equal.sym(
        List<&2, U32>,
        k1,
        k,
        Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k1, k)(ec)
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, _, k2), u => Some{v1}),
        Some{Put.node(Node.Leaf{k, v}, [])}
      )
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
        False{},
        ne
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Shared.Maybe.when(List<&2, U32>, _, u => Some{v1}),
        Some{Put.node(Node.Leaf{k, v}, [])}
      )
      Tree.read_new_leaf_off(~S, ~fetch, s2, p2, k, v, k2, ne)
    case False{}:
      Tree.set_keeps.split(
        ~S,
        ~fetch,
        s2,
        q,
        d,
        k,
        v,
        o,
        k1,
        v1,
        k2,
        p2,
        Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
        {==},
        eo,
        hp,
        ne
      )

# a new branch of parts ks whose part n is the new subtree m reads for k2 along
# z then r2 as ks does, when m reads along r2 as the part n of ks
def Tree.set_keeps.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  +z: Nat,
  r2: List<&2, Nat>,
  k2: List<&2, U32>,
  m: Maybe<&2, Put>,
  c: Bool,
  ec: {Nat.is_eq(z, n) == c: Bool},
  ih: Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r2,
    k2,
    Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
    m
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{z, r2},
  k2,
  Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, z))),
  Maybe.bind(&2, Put, Put, m, p => Some{Put.into(ks, n, p)})
):
  match c:
    case True{}:
      +ez = Shared.Nat.is_eq_sound(z, n)(ec)
      %Equal.sym(
        Nat,
        z,
        n,
        ez
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        Con{z, r2},
        k2,
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, _))),
        Maybe.bind(&2, Put, Put, m, p => Some{Put.into(ks, n, p)})
      )
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
        m,
        p => Some{Put.into(ks, n, p)},
        q => iq => Tree.read_into(
          ~S,
          ~fetch,
          s2,
          ks,
          n,
          z,
          r2,
          k2,
          Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
          q,
          ez,
          iq
        ),
        ih
      )
    case False{}:
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
        Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, z))),
        m,
        p => Some{Put.into(ks, n, p)},
        q => iq => Tree.read_into_off(~S, ~fetch, s2, ks, n, z, r2, k2, q, ec),
        ih
      )

# a new branch of parts ks whose part n is the new subtree m reads for k2 along
# p2 as ks does, when m reads along the rest of p2 as the part n of ks
def Tree.set_keeps.branch(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +n: Nat,
  +k2: List<&2, U32>,
  p2: List<&2, Nat>,
  d: Nat,
  m: Maybe<&2, Put>,
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  ih: @r2: List<
    &2,
    Nat> -> {
    List.drop(&2, Nat, Tree.path(k2), 1n+d) == r2: List<&2, Nat>
  } -> Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r2,
    k2,
    Tree.get.go(~S, ~fetch, s2, r2, k2, Tree.part(~S, ~fetch, s2, Parts.at(ks, n))),
    m
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Tree.get.go(~S, ~fetch, s2, p2, k2, Some{Node.Branch{ks}}),
  Maybe.bind(&2, Put, Put, m, p => Some{Put.into(ks, n, p)})
):
  match p2:
    case Nil{}:
      Tree.read_into_nil(~S, ~fetch, s2, ks, n, k2, m)
    case Con{+z, +r2}:
      Tree.set_keeps.con(
        ~S,
        ~fetch,
        s2,
        ks,
        n,
        z,
        r2,
        k2,
        m,
        Nat.is_eq(z, n),
        {==},
        ih(r2)(Shared.List.drop_step(&2, Nat, Tree.path(k2), d, z, r2)(hp))
      )

# Tree.set.go from the part o, whose node is m in the store s, with k set to v,
# reads for another key k2 along its path p2 as o does, in a store s2 that
# grows from s
def Tree.set_keeps(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +s: S,
  +s2: S,
  p: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>,
  +k2: List<&2, U32>,
  +p2: List<&2, Nat>,
  +gr: {grows(s, s2) == True{}: Bool},
  hm: @n: Node -> {
    m == Some{n}: Maybe<&2, Node>
  } -> {Tree.part(~S, ~fetch, s2, o) == Some{n}: Maybe<&2, Node>},
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Tree.get.go(~S, ~fetch, s2, p2, k2, Tree.part(~S, ~fetch, s2, o)),
  Tree.set.go(~S, ~fetch, s, p, d, k, v, o, m)
):
  match p m:
    case q None{}:
      Unit{}
    case q Some{Node.Empty{}}:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.part(~S, ~fetch, s2, o),
        Some{Node.Empty{}},
        hm(Node.Empty{})({==})
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.get.go(~S, ~fetch, s2, p2, k2, _),
        Some{Put.node(Node.Leaf{k, v}, [])}
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.get.go(~S, ~fetch, s2, p2, k2, Some{Node.Empty{}}),
        None{},
        Tree.get.go_empty(~S, ~fetch, s2, p2, k2)
      ): Tree.Reads(~S, ~fetch, s2, p2, k2, _, Some{Put.node(Node.Leaf{k, v}, [])})
      Tree.read_new_leaf_off(~S, ~fetch, s2, p2, k, v, k2, ne)
    case q Some{Node.Leaf{+k1, +v1}}:
      +eo = hm(Node.Leaf{k1, v1})({==})
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.part(~S, ~fetch, s2, o),
        Some{Node.Leaf{k1, v1}},
        eo
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.get.go(~S, ~fetch, s2, p2, k2, _),
        Tree.set.go(~S, ~fetch, s, q, d, k, v, o, Some{Node.Leaf{k1, v1}})
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.get.go(~S, ~fetch, s2, p2, k2, Some{Node.Leaf{k1, v1}}),
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Tree.get.go_leaf(~S, ~fetch, s2, p2, k2, k1, v1)
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        _,
        Tree.set.go(~S, ~fetch, s, q, d, k, v, o, Some{Node.Leaf{k1, v1}})
      )
      Tree.set_keeps.leaf(
        ~S,
        ~fetch,
        s2,
        q,
        d,
        k,
        v,
        o,
        k1,
        v1,
        k2,
        p2,
        Shared.List.is_eq(~U32, ~U32.is_eq, k1, k),
        {==},
        eo,
        hp,
        ne
      )
    case Con{+x, +r} Some{Node.Branch{+ks}}:
      +kid = Parts.at(ks, x)
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.part(~S, ~fetch, s2, o),
        Some{Node.Branch{ks}},
        hm(Node.Branch{ks})({==})
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.get.go(~S, ~fetch, s2, p2, k2, _),
        Tree.set.go(~S, ~fetch, s, Con{x, r}, d, k, v, o, Some{Node.Branch{ks}})
      )
      Tree.set_keeps.branch(
        ~S,
        ~fetch,
        s2,
        ks,
        x,
        k2,
        p2,
        d,
        Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
        hp,
        r2 => h2 => Tree.set_keeps(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          s,
          s2,
          r,
          1n+d,
          k,
          v,
          kid,
          Tree.part(~S, ~fetch, s, kid),
          k2,
          r2,
          gr,
          n2 => Tree.part_kept(~S, ~fetch, ~grows, ~kept, s, s2, kid, n2, gr),
          h2,
          ne
        )
      )
    case Nil{} Some{Node.Branch{ks}}:
      Unit{}

# after the key k is set to v in the tree whose root is h in the store s, a
# read of another key k2 at the new root gives what it gives at h, in any
# store s2 that grows from s and holds the new nodes
law Tree.get_other:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +s: S
  for +s2: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for v: List<&2, U32>
  for t: Put
  for +k2: List<&2, U32>
  {grows(s, s2) == True{}: Bool}
    -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, h, k, v) == Some{t}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {
      Tree.get.plain(
        ~S,
        ~fetch,
        s2,
        Some{Put.root(t)},
        k2
      )
        == Tree.get.plain(~S, ~fetch, s2, h, k2): Maybe<&2, List<&2, U32>>
    }

def Tree.get_other(ty, fetch, grows, kept, s, s2, h, k, v, t, k2):
  +gr => ne => e =>
    %e: Tree.Reads(~ty, ~fetch, s2, Tree.path(k2), k2, Tree.get.plain(~ty, ~fetch, s2, h, k2), _)
    Tree.set_keeps(
      ~ty,
      ~fetch,
      ~grows,
      ~kept,
      s,
      s2,
      Tree.path(k),
      0n,
      k,
      v,
      h,
      Tree.part(~ty, ~fetch, s, h),
      k2,
      Tree.path(k2),
      gr,
      n => Tree.part_kept(~ty, ~fetch, ~grows, ~kept, s, s2, h, n, gr),
      Shared.List.drop_zero(&2, Nat, Tree.path(k2)),
      ne
    )

# a and b are the same binding
def Binding.is_eq(a: Binding, b: Binding) -> Bool:
  match a b:
    case Binding{k1, v1} Binding{k2, v2}:
      Shared.Bool.when(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
        u => Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2),
        u => False{}
      )

# Binding.is_eq is True for a binding and itself
def Binding.is_eq_refl(a: Binding) -> {Binding.is_eq(a, a) == True{}: Bool}:
  match a:
    case Binding{k, v}:
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
        True{},
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
      ): {
        Shared.Bool.when(
          Bool,
          _,
          u => Shared.List.is_eq(~U32, ~U32.is_eq, v, v),
          u => False{}
        )
          == True{}: Bool
      }
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), v)

# the listing of parts whose first is a leaf of k2 holds whatever the listing
# of the parts after it holds, when the leaf is listed (c) or not
def Tree.list_skip.leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  y: Maybe<&2, Hashes.Hash>,
  +r: List<&2, Maybe<&2, Hashes.Hash>>,
  pre: List<&2, Nat>,
  x: Nat,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  b: Binding,
  c: Bool
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
    b
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(
      List<&2, Binding>,
      c,
      u => Binding{
        k2,
        v2
      }
        <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
      u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
    ),
    b
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      Shared.List.contains_cons(
        ~Binding,
        ~Binding.is_eq,
        Binding{k2, v2},
        Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
        b
      )
    case False{}:
      h => h

# a binding of keys that Binding.is_eq compares as c (the keys are equal
# when it is True) is the other one, when Binding.is_eq says so
def Binding.is_eq_sound.at(
  k1: List<&2, U32>,
  v1: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  c: Bool,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == c: Bool}
) -> {
  Shared.Bool.when(
    Bool,
    c,
    u => Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2),
    u => False{}
  )
    == True{}: Bool
} -> {Binding{k1, v1} == Binding{k2, v2}: Binding}:
  match c:
    case True{}:
      e =>
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          k1,
          k2
        )(ec): {Binding{k1, v1} == Binding{_, v2}: Binding}
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          v1,
          v2
        )(e): {Binding{k1, v1} == Binding{k1, _}: Binding}
        {==}
    case False{}:
      e => Empty.absurd({Binding{k1, v1} == Binding{k2, v2}: Binding}, Shared.Bool.false_ne_true(e))

# Binding.is_eq is True only for equal bindings
def Binding.is_eq_sound(
  a: Binding,
  b: Binding
) -> {Binding.is_eq(a, b) == True{}: Bool} -> {a == b: Binding}:
  match a b:
    case Binding{+k1, v1} Binding{+k2, v2}:
      Binding.is_eq_sound.at(k1, v1, k2, v2, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), {==})

# the leaf of a binding
def Binding.leaf(b: Binding) -> Maybe<&2, Node>:
  match b:
    case Binding{k, v}:
      Some{Node.Leaf{k, v}}

# the path of a key has 64 nibbles
def Nibbles.of_length(h: Hashes.Hash) -> {List.length(&2, Nat, Nibbles.of(h)) == 64n: Nat}:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      {==}

# the nibbles after q, then z, are what follows z
def Tree.drop_next(
  ks: List<&2, Nat>,
  +q: List<&2, Nat>,
  -z: Nat,
  r: List<&2, Nat>,
  hd: {List.drop(&2, Nat, ks, List.length(&2, Nat, q)) == z <> r: List<&2, Nat>}
) -> {
  List.drop(&2, Nat, ks, List.length(&2, Nat, List.append(&2, Nat, q, [z]))) == r: List<&2, Nat>
}:
  %Equal.sym(
    Nat,
    List.length(&2, Nat, List.append(&2, Nat, q, [z])),
    1n+List.length(&2, Nat, q),
    Shared.List.length_snoc(Nat, q, z)
  ): {List.drop(&2, Nat, ks, _) == r: List<&2, Nat>}
  Shared.List.drop_step(&2, Nat, ks, List.length(&2, Nat, q), z, r)(hd)

# the listing of parts holds whatever the listing of the parts after the first
# holds
def Tree.list_skip(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  y: Maybe<&2, Hashes.Hash>,
  +r: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  m: Maybe<&2, Node>,
  +b: Binding
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
    b
  )
    == True{}: Bool
} -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.go(~S, ~fetch, f, s, Con{y, r}, pre, x, m),
    b
  )
    == True{}: Bool
}:
  match f m:
    case g Some{Node.Leaf{+k2, v2}}:
      Tree.list_skip.leaf(
        ~S,
        ~fetch,
        g,
        s,
        y,
        r,
        pre,
        x,
        k2,
        v2,
        b,
        Tree.leads(k2, List.append(&2, Nat, pre, [x]))
      )
    case 1n+(+p) Some{Node.Branch{+qs}}:
      +below = Tree.list.go(
        ~S,
        ~fetch,
        p,
        s,
        qs,
        List.append(&2, Nat, pre, [x]),
        0n,
        Tree.first(~S, ~fetch, s, qs)
      )
      rest = Tree.list.go(~S, ~fetch, 1n+p, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
      h =>
        %Equal.sym(
          Bool,
          List.contains(~Binding, ~Binding.is_eq, List.append(&2, Binding, below, rest), b),
          Bool.or(
            List.contains(~Binding, ~Binding.is_eq, below, b),
            List.contains(~Binding, ~Binding.is_eq, rest, b)
          ),
          Shared.List.contains_append(~Binding, ~Binding.is_eq, below, rest, b)
        ): {_ == True{}: Bool}
        %Equal.sym(
          Bool,
          List.contains(~Binding, ~Binding.is_eq, rest, b),
          True{},
          h
        ): {Bool.or(List.contains(~Binding, ~Binding.is_eq, below, b), _) == True{}: Bool}
        Shared.Bool.or_true_right(List.contains(~Binding, ~Binding.is_eq, below, b))
    case 0n Some{Node.Branch{qs}}:
      h => h
    case g Some{Node.Empty{}}:
      h => h
    case g None{}:
      h => h

# a key whose path starts with q is led to where q ends
def Tree.leads_at(
  k: List<&2, U32>,
  q: List<&2, Nat>,
  hq: {List.take(&2, Nat, Tree.path(k), List.length(&2, Nat, q)) == q: List<&2, Nat>}
) -> {Tree.leads(k, q) == True{}: Bool}:
  %Equal.sym(
    List<&2, Nat>,
    List.take(&2, Nat, Tree.path(k), List.length(&2, Nat, q)),
    q,
    hq
  ): {Shared.List.is_eq(~Nat, ~Nat.is_eq, _, q) == True{}: Bool}
  Shared.List.is_eq_refl(~Nat, ~Nat.is_eq, ~Shared.Nat.laws(), q)

# the listing of parts whose first is a leaf of k2 and v2, where the path of k
# leads, holds the binding of k and v, when that leaf reads v for k
def Tree.list_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  y: Maybe<&2, Hashes.Hash>,
  +r: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +t: Nat,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  c: Bool,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k) == c: Bool},
  hq: {
    List.take(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == List.append(&2, Nat, pre, [t]): List<&2, Nat>
  },
  hg: {Shared.Maybe.when(List<&2, U32>, c, u => Some{v2}) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(
      List<&2, Binding>,
      Tree.leads(k2, List.append(&2, Nat, pre, [t])),
      u => Binding{
        k2,
        v2
      }
        <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r)),
      u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
    ),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match c:
    case False{}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Shared.Bool.when(
              List<&2, Binding>,
              Tree.leads(k2, List.append(&2, Nat, pre, [t])),
              u => Binding{
                k2,
                v2
              }
                <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r)),
              u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
            ),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(List<&2, U32>, v, hg)
      )
    case True{}:
      rest = Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
      %Equal.sym(
        List<&2, U32>,
        k2,
        k,
        Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k2, k)(ec)
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Shared.Bool.when(
            List<&2, Binding>,
            Tree.leads(_, List.append(&2, Nat, pre, [t])),
            u => Binding{
              _,
              v2
            }
              <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r)),
            u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
          ),
          Binding{k, v}
        )
          == True{}: Bool
      }
      %Equal.sym(
        List<&2, U32>,
        v2,
        v,
        Shared.Maybe.some_inj(List<&2, U32>, v2, v, hg)
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Shared.Bool.when(
            List<&2, Binding>,
            Tree.leads(k, List.append(&2, Nat, pre, [t])),
            u => Binding{
              k,
              _
            }
              <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r)),
            u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
          ),
          Binding{k, v}
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        Tree.leads(k, List.append(&2, Nat, pre, [t])),
        True{},
        Tree.leads_at(k, List.append(&2, Nat, pre, [t]), hq)
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Shared.Bool.when(List<&2, Binding>, _, u => Binding{k, v} <> rest, u => rest),
          Binding{k, v}
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        Binding.is_eq(Binding{k, v}, Binding{k, v}),
        True{},
        Binding.is_eq_refl(Binding{k, v})
      ): {
        List.any.if(
          u => List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v}),
          _
        )
          == True{}: Bool
      }
      {==}

# bend-lint: expect-begin bend-lint-rules/language/decreasing_call@warning -- g is f itself, bound by the match; the checker accepts these calls
# the listing of the parts ps, from the place x, whose first node is m, holds
# the binding of k and v, when the part j of ps, at the place t, reads v for k
# along P, the rest of k's path, and f levels are enough for P
def Tree.list_part(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  m: Maybe<&2, Node>,
  j: Nat,
  +t: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  pth: List<&2, Nat>,
  em: {Tree.first(~S, ~fetch, s, ps) == m: Maybe<&2, Node>},
  ht: {Nat.add(j, x) == t: Nat},
  hq: {
    List.take(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == List.append(&2, Nat, pre, [t]): List<&2, Nat>
  },
  +hd: {
    List.drop(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == pth: List<&2, Nat>
  },
  hf: {Nat.is_le(List.length(&2, Nat, pth), f) == True{}: Bool},
  hg: {
    Tree.get.go(
      ~S,
      ~fetch,
      s,
      pth,
      k,
      Tree.part(~S, ~fetch, s, Parts.at(ps, j))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.go(~S, ~fetch, f, s, ps, pre, x, m),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match f ps m j pth:
    case g Nil{} w i pth2:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, g, s, [], pre, x, w),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
              None{},
              Tree.get.go_empty(~S, ~fetch, s, pth2, k)
            ),
            hg
          )
        )
      )
    case g Con{y, +r} w 1n+(+i) pth2:
      Tree.list_skip(
        ~S,
        ~fetch,
        g,
        s,
        y,
        r,
        pre,
        x,
        w,
        Binding{k, v}
      )(
        Tree.list_part(
          ~S,
          ~fetch,
          g,
          s,
          r,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, r),
          i,
          t,
          k,
          v,
          pth2,
          {==},
          Equal.trans(Nat, Nat.add(i, 1n+x), 1n+Nat.add(i, x), t, Shared.Nat.add_succ(i, x), ht),
          hq,
          hd,
          hf,
          hg
        )
      )
    case g Con{y, +r} Some{Node.Leaf{+k2, +v2}} 0n pth2:
      %Equal.sym(
        Nat,
        x,
        t,
        ht
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Tree.list.go(~S, ~fetch, g, s, Con{y, r}, pre, _, Some{Node.Leaf{k2, v2}}),
          Binding{k, v}
        )
          == True{}: Bool
      }
      Tree.list_leaf(
        ~S,
        ~fetch,
        g,
        s,
        y,
        r,
        pre,
        t,
        k,
        v,
        k2,
        v2,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        {==},
        hq,
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Shared.Maybe.when(
            List<&2, U32>,
            Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
            u => Some{v2}
          ),
          Tree.get.go(~S, ~fetch, s, pth2, k, Tree.part(~S, ~fetch, s, y)),
          Some{v},
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
              u => Some{v2}
            ),
            Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Leaf{k2, v2}}),
            Tree.get.go(~S, ~fetch, s, pth2, k, Tree.part(~S, ~fetch, s, y)),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Leaf{k2, v2}}),
              Shared.Maybe.when(
                List<&2, U32>,
                Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
                u => Some{v2}
              ),
              Tree.get.go_leaf(~S, ~fetch, s, pth2, k, k2, v2)
            ),
            Equal.cong(
              Maybe<&2, Node>,
              Maybe<&2, List<&2, U32>>,
              mm => Tree.get.go(~S, ~fetch, s, pth2, k, mm),
              Some{Node.Leaf{k2, v2}},
              Tree.part(~S, ~fetch, s, y),
              Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), Some{Node.Leaf{k2, v2}}, em)
            )
          ),
          hg
        )
      )
    case 1n+p Con{y, r} Some{Node.Branch{+qs}} 0n Nil{}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, 1n+p, s, Con{y, r}, pre, x, Some{Node.Branch{qs}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Tree.get.go(~S, ~fetch, s, [], k, Some{Node.Branch{qs}}),
            Tree.get.go(~S, ~fetch, s, [], k, Tree.part(~S, ~fetch, s, y)),
            Some{v},
            Equal.cong(
              Maybe<&2, Node>,
              Maybe<&2, List<&2, U32>>,
              mm => Tree.get.go(~S, ~fetch, s, [], k, mm),
              Some{Node.Branch{qs}},
              Tree.part(~S, ~fetch, s, y),
              Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), Some{Node.Branch{qs}}, em)
            ),
            hg
          )
        )
      )
    case 0n Con{y, r} Some{Node.Branch{qs}} 0n Nil{}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, 0n, s, Con{y, r}, pre, x, Some{Node.Branch{qs}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Tree.get.go(~S, ~fetch, s, [], k, Some{Node.Branch{qs}}),
            Tree.get.go(~S, ~fetch, s, [], k, Tree.part(~S, ~fetch, s, y)),
            Some{v},
            Equal.cong(
              Maybe<&2, Node>,
              Maybe<&2, List<&2, U32>>,
              mm => Tree.get.go(~S, ~fetch, s, [], k, mm),
              Some{Node.Branch{qs}},
              Tree.part(~S, ~fetch, s, y),
              Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), Some{Node.Branch{qs}}, em)
            ),
            hg
          )
        )
      )
    case 0n Con{y, r} Some{Node.Branch{qs}} 0n Con{z, rp}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, 0n, s, Con{y, r}, pre, x, Some{Node.Branch{qs}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(hf)
      )
    case g Con{y, r} None{} 0n +pth2:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, g, s, Con{y, r}, pre, x, None{}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, pth2, k, None{}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, None{}),
              None{},
              Tree.get.go_none(~S, ~fetch, s, pth2, k)
            ),
            Equal.trans(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, None{}),
              Tree.get.go(~S, ~fetch, s, pth2, k, Tree.part(~S, ~fetch, s, y)),
              Some{v},
              Equal.cong(
                Maybe<&2, Node>,
                Maybe<&2, List<&2, U32>>,
                mm => Tree.get.go(~S, ~fetch, s, pth2, k, mm),
                None{},
                Tree.part(~S, ~fetch, s, y),
                Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), None{}, em)
              ),
              hg
            )
          )
        )
      )
    case g Con{y, r} Some{Node.Empty{}} 0n +pth2:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.go(~S, ~fetch, g, s, Con{y, r}, pre, x, Some{Node.Empty{}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
              None{},
              Tree.get.go_empty(~S, ~fetch, s, pth2, k)
            ),
            Equal.trans(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
              Tree.get.go(~S, ~fetch, s, pth2, k, Tree.part(~S, ~fetch, s, y)),
              Some{v},
              Equal.cong(
                Maybe<&2, Node>,
                Maybe<&2, List<&2, U32>>,
                mm => Tree.get.go(~S, ~fetch, s, pth2, k, mm),
                Some{Node.Empty{}},
                Tree.part(~S, ~fetch, s, y),
                Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), Some{Node.Empty{}}, em)
              ),
              hg
            )
          )
        )
      )
    case 1n+(+p) Con{y, +r} Some{Node.Branch{+qs}} 0n Con{+z, +rp}:
      +here = List.append(&2, Nat, pre, [t])
      %Equal.sym(
        Nat,
        x,
        t,
        ht
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Tree.list.go(~S, ~fetch, 1n+p, s, Con{y, r}, pre, _, Some{Node.Branch{qs}}),
          Binding{k, v}
        )
          == True{}: Bool
      }
      +below = Tree.list.go(~S, ~fetch, p, s, qs, here, 0n, Tree.first(~S, ~fetch, s, qs))
      +rest = Tree.list.go(~S, ~fetch, 1n+p, s, r, pre, 1n+t, Tree.first(~S, ~fetch, s, r))
      %Equal.sym(
        Bool,
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          List.append(&2, Binding, below, rest),
          Binding{k, v}
        ),
        Bool.or(
          List.contains(~Binding, ~Binding.is_eq, below, Binding{k, v}),
          List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v})
        ),
        Shared.List.contains_append(~Binding, ~Binding.is_eq, below, rest, Binding{k, v})
      ): {_ == True{}: Bool}
      %Equal.sym(
        Bool,
        List.contains(~Binding, ~Binding.is_eq, below, Binding{k, v}),
        True{},
        Tree.list_part(
          ~S,
          ~fetch,
          p,
          s,
          qs,
          here,
          0n,
          Tree.first(~S, ~fetch, s, qs),
          z,
          z,
          k,
          v,
          rp,
          {==},
          Shared.Nat.add_zero(z),
          Shared.List.take_snoc(Nat, Tree.path(k), here, z, rp, hq, hd),
          Tree.drop_next(Tree.path(k), here, z, rp, hd),
          hf,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(qs, z))),
            Tree.get.go(~S, ~fetch, s, Con{z, rp}, k, Tree.part(~S, ~fetch, s, y)),
            Some{v},
            Equal.cong(
              Maybe<&2, Node>,
              Maybe<&2, List<&2, U32>>,
              mm => Tree.get.go(~S, ~fetch, s, Con{z, rp}, k, mm),
              Some{Node.Branch{qs}},
              Tree.part(~S, ~fetch, s, y),
              Equal.sym(Maybe<&2, Node>, Tree.part(~S, ~fetch, s, y), Some{Node.Branch{qs}}, em)
            ),
            hg
          )
        )
      ): {Bool.or(_, List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v})) == True{}: Bool}
      {==}
# bend-lint: expect-end bend-lint-rules/language/decreasing_call@warning

# the listing of one leaf of k2 and v2 holds the binding of k and v, when the
# leaf reads v for k
def Tree.list_root_leaf(
  +k: List<&2, U32>,
  v: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  c: Bool,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k) == c: Bool},
  hg: {Shared.Maybe.when(List<&2, U32>, c, u => Some{v2}) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {List.contains(~Binding, ~Binding.is_eq, [Binding{k2, v2}], Binding{k, v}) == True{}: Bool}:
  match c:
    case False{}:
      Empty.absurd(
        {List.contains(~Binding, ~Binding.is_eq, [Binding{k2, v2}], Binding{k, v}) == True{}: Bool},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, hg)
      )
    case True{}:
      %Equal.sym(
        List<&2, U32>,
        k2,
        k,
        Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k2, k)(ec)
      ): {List.contains(~Binding, ~Binding.is_eq, [Binding{_, v2}], Binding{k, v}) == True{}: Bool}
      %Equal.sym(
        List<&2, U32>,
        v2,
        v,
        Shared.Maybe.some_inj(List<&2, U32>, v2, v, hg)
      ): {List.contains(~Binding, ~Binding.is_eq, [Binding{k, _}], Binding{k, v}) == True{}: Bool}
      %Equal.sym(
        Bool,
        Binding.is_eq(Binding{k, v}, Binding{k, v}),
        True{},
        Binding.is_eq_refl(Binding{k, v})
      ): {
        List.any.if(
          u => List.contains(~Binding, ~Binding.is_eq, [], Binding{k, v}),
          _
        )
          == True{}: Bool
      }
      {==}

# the path of k, when it is z then rp, starts with z
def Tree.list_root.take(
  k: List<&2, U32>,
  z: Nat,
  rp: List<&2, Nat>,
  hpath: {Tree.path(k) == z <> rp: List<&2, Nat>}
) -> {
  List.take(
    &2,
    Nat,
    Tree.path(k),
    List.length(&2, Nat, List.append(&2, Nat, [], [z]))
  )
    == List.append(&2, Nat, [], [z]): List<&2, Nat>
}:
  %Equal.sym(
    List<&2, Nat>,
    Tree.path(k),
    z <> rp,
    hpath
  ): {List.take(&2, Nat, _, 1n) == [z]: List<&2, Nat>}
  %Equal.sym(
    List<&2, Nat>,
    List.take(&2, Nat, rp, 0n),
    [],
    Shared.List.take_zero(Nat, rp)
  ): {z <> _ == [z]: List<&2, Nat>}
  {==}

# the path of k, when it is z then rp, is rp after z
def Tree.list_root.drop(
  k: List<&2, U32>,
  z: Nat,
  rp: List<&2, Nat>,
  hpath: {Tree.path(k) == z <> rp: List<&2, Nat>}
) -> {
  List.drop(
    &2,
    Nat,
    Tree.path(k),
    List.length(&2, Nat, List.append(&2, Nat, [], [z]))
  )
    == rp: List<&2, Nat>
}:
  %Equal.sym(
    List<&2, Nat>,
    Tree.path(k),
    z <> rp,
    hpath
  ): {List.drop(&2, Nat, _, 1n) == rp: List<&2, Nat>}
  Shared.List.drop_zero(&2, Nat, rp)

# the path of k, when it is z then rp, leaves 63 nibbles after z
def Tree.list_root.deep(
  k: List<&2, U32>,
  z: Nat,
  rp: List<&2, Nat>,
  hpath: {Tree.path(k) == z <> rp: List<&2, Nat>}
) -> {Nat.is_le(List.length(&2, Nat, rp), 63n) == True{}: Bool}:
  %hpath: {Nat.is_le(List.length(&2, Nat, _), 64n) == True{}: Bool}
  %Equal.sym(
    Nat,
    List.length(&2, Nat, Tree.path(k)),
    64n,
    Nibbles.of_length(Hashes.Sha.hash(k))
  ): {Nat.is_le(_, 64n) == True{}: Bool}
  {==}

# the listing of a tree whose root node is m holds the binding of k and v,
# when m reads v for k along P, the path of k
def Tree.list_root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  pth: List<&2, Nat>,
  m: Maybe<&2, Node>,
  +hpath: {Tree.path(k) == pth: List<&2, Nat>},
  hg: {Tree.get.go(~S, ~fetch, s, pth, k, m) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.root(~S, ~fetch, s, m),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match pth m:
    case +pth2 Some{Node.Leaf{+k2, +v2}}:
      Tree.list_root_leaf(
        k,
        v,
        k2,
        v2,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        {==},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Shared.Maybe.when(
            List<&2, U32>,
            Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
            u => Some{v2}
          ),
          Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Leaf{k2, v2}}),
          Some{v},
          Equal.sym(
            Maybe<&2, List<&2, U32>>,
            Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Leaf{k2, v2}}),
            Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
              u => Some{v2}
            ),
            Tree.get.go_leaf(~S, ~fetch, s, pth2, k, k2, v2)
          ),
          hg
        )
      )
    case Con{+z, +rp} Some{Node.Branch{+qs}}:
      Tree.list_part(
        ~S,
        ~fetch,
        63n,
        s,
        qs,
        [],
        0n,
        Tree.first(~S, ~fetch, s, qs),
        z,
        z,
        k,
        v,
        rp,
        {==},
        Shared.Nat.add_zero(z),
        Tree.list_root.take(k, z, rp, hpath),
        Tree.list_root.drop(k, z, rp, hpath),
        Tree.list_root.deep(k, z, rp, hpath),
        hg
      )
    case Nil{} Some{Node.Branch{qs}}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.root(~S, ~fetch, s, Some{Node.Branch{qs}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(List<&2, U32>, v, hg)
      )
    case +pth2 None{}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.root(~S, ~fetch, s, None{}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, pth2, k, None{}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, None{}),
              None{},
              Tree.get.go_none(~S, ~fetch, s, pth2, k)
            ),
            hg
          )
        )
      )
    case +pth2 Some{Node.Empty{}}:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.list.root(~S, ~fetch, s, Some{Node.Empty{}}),
            Binding{k, v}
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, pth2, k, Some{Node.Empty{}}),
              None{},
              Tree.get.go_empty(~S, ~fetch, s, pth2, k)
            ),
            hg
          )
        )
      )

# a binding that reads is listed: a listing misses no key of a tree
law Tree.list_complete:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  {Tree.get.plain(~S, ~fetch, s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
    -> {
      List.contains(
        ~Binding,
        ~Binding.is_eq,
        Tree.list(~S, ~fetch, s, h),
        Binding{k, v}
      )
        == True{}: Bool
    }

def Tree.list_complete(ty, fetch, s, h, k, v):
  e => Tree.list_root(~ty, ~fetch, s, k, v, Tree.path(k), Tree.part(~ty, ~fetch, s, h), {==}, e)

# a node that is a branch is the branch of its parts
def Node.kids_of(
  m: Maybe<&2, Node>
) -> {Node.is_branch(m) == True{}: Bool} -> {m == Some{Node.Branch{Node.kids(m)}}: Maybe<&2, Node>}:
  match m:
    case Some{Node.Branch{qs}}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {None{} == Some{Node.Branch{[]}}: Maybe<&2, Node>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Node.Empty{}}:
      h => Empty.absurd(
        {Some{Node.Empty{}} == Some{Node.Branch{[]}}: Maybe<&2, Node>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Node.Leaf{k, v}}:
      h => Empty.absurd(
        {Some{Node.Leaf{k, v}} == Some{Node.Branch{[]}}: Maybe<&2, Node>},
        Shared.Bool.false_ne_true(h)
      )

# the reads of k along p at the nodes ma and mb, side c, are those at the
# nodes ma2 and mb2 that they equal
def Tree.pick_at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  c: Bool,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  ma: Maybe<&2, Node>,
  ma2: Maybe<&2, Node>,
  mb: Maybe<&2, Node>,
  mb2: Maybe<&2, Node>,
  ea: {ma == ma2: Maybe<&2, Node>},
  eb: {mb == mb2: Maybe<&2, Node>}
) -> {
  Bool.pick(
    Maybe<&2, List<&2, U32>>,
    c,
    Tree.get.go(~S, ~fetch, s, p, k, ma),
    Tree.get.go(~S, ~fetch, s, p, k, mb)
  )
    == Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, ma2),
      Tree.get.go(~S, ~fetch, s, p, k, mb2)
    ): Maybe<&2, List<&2, U32>>
}:
  %ea: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, ma),
      Tree.get.go(~S, ~fetch, s, p, k, mb)
    )
      == Bool.pick(
        Maybe<&2, List<&2, U32>>,
        c,
        Tree.get.go(~S, ~fetch, s, p, k, _),
        Tree.get.go(~S, ~fetch, s, p, k, mb2)
      ): Maybe<&2, List<&2, U32>>
  }
  %eb: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, ma),
      Tree.get.go(~S, ~fetch, s, p, k, mb)
    )
      == Bool.pick(
        Maybe<&2, List<&2, U32>>,
        c,
        Tree.get.go(~S, ~fetch, s, p, k, ma),
        Tree.get.go(~S, ~fetch, s, p, k, _)
      ): Maybe<&2, List<&2, U32>>
  }
  {==}

# the read a reads v, when the side c of a and an empty part's read (a on the
# side d) reads v
def Tree.pick_one(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  c: Bool,
  d: Bool,
  a: Maybe<&2, List<&2, U32>>,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  h: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        d,
        a,
        Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}})
      ),
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        d,
        Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}),
        a
      )
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> {a == Some{v}: Maybe<&2, List<&2, U32>>}:
  match c d:
    case True{} True{}:
      h
    case False{} False{}:
      h
    case True{} False{}:
      Empty.absurd(
        {a == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}),
              None{},
              Tree.get.go_empty(~S, ~fetch, s, p, k)
            ),
            h
          )
        )
      )
    case False{} True{}:
      Empty.absurd(
        {a == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}),
            Some{v},
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Empty{}}),
              None{},
              Tree.get.go_empty(~S, ~fetch, s, p, k)
            ),
            h
          )
        )
      )

# a pick of d between xs and ys holds the binding of k and v, when ys holds it
# and the side c of the parts ya and yb reads v for k along p while the other
# does not (so d, whether they hold the same root, is False)
def Tree.diff_here(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ya: Maybe<&2, Hashes.Hash>,
  +yb: Maybe<&2, Hashes.Hash>,
  c: Bool,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  d: Bool,
  ed: {Parts.same(ya, yb) == d: Bool},
  xs: List<&2, Binding>,
  ys: List<&2, Binding>,
  hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, ya)),
      Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, yb))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  hn: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, yb)),
      Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, ya))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Empty,
  hy: (
    {
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        c,
        Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, yb)),
        Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, ya))
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    } -> Empty
  ) -> {List.contains(~Binding, ~Binding.is_eq, ys, Binding{k, v}) == True{}: Bool}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(List<&2, Binding>, d, u => xs, u => ys),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match d:
    case True{}:
      +e = Shared.Maybe.is_eq_sound(
        ~Hashes.Hash,
        ~Hashes.Hash.is_eq,
        x => y => Hashes.Hash.is_eq_sound(x, y),
        ya,
        yb
      )(ed)
      Empty.absurd(
        {List.contains(~Binding, ~Binding.is_eq, xs, Binding{k, v}) == True{}: Bool},
        hn(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, yb)),
              Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, ya))
            ),
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, ya)),
              Tree.get.go(~S, ~fetch, s, p, k, Tree.part(~S, ~fetch, s, yb))
            ),
            Some{v},
            Tree.pick_at(
              ~S,
              ~fetch,
              s,
              c,
              p,
              k,
              Tree.part(~S, ~fetch, s, yb),
              Tree.part(~S, ~fetch, s, ya),
              Tree.part(~S, ~fetch, s, ya),
              Tree.part(~S, ~fetch, s, yb),
              Equal.cong(
                Maybe<&2, Hashes.Hash>,
                Maybe<&2, Node>,
                y => Tree.part(~S, ~fetch, s, y),
                yb,
                ya,
                Equal.sym(Maybe<&2, Hashes.Hash>, ya, yb, e)
              ),
              Equal.cong(
                Maybe<&2, Hashes.Hash>,
                Maybe<&2, Node>,
                y => Tree.part(~S, ~fetch, s, y),
                ya,
                yb,
                e
              )
            ),
            hg
          )
        )
      )
    case False{}:
      hy(hn)

# the listings of the parts ya and yb, at the place x of branches whose path
# is pre, hold the binding of k and v, when the side c of them, at the place
# t, reads v for k along P, the rest of k's path, and f levels are enough for P
def Tree.diff_side(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +ya: Maybe<&2, Hashes.Hash>,
  +yb: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Nat>,
  +x: Nat,
  t: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  pth: List<&2, Nat>,
  c: Bool,
  ht: {Nat.add(0n, x) == t: Nat},
  hq: {
    List.take(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == List.append(&2, Nat, pre, [t]): List<&2, Nat>
  },
  hd: {
    List.drop(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == pth: List<&2, Nat>
  },
  hf: {Nat.is_le(List.length(&2, Nat, pth), f) == True{}: Bool},
  hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, ya)),
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, yb))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.diff.sides(
      ~S,
      ~fetch,
      f,
      s,
      ya,
      yb,
      pre,
      x,
      Tree.part(~S, ~fetch, s, ya),
      Tree.part(~S, ~fetch, s, yb)
    ),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      Shared.List.contains_left(
        ~Binding,
        ~Binding.is_eq,
        Tree.list.go(~S, ~fetch, f, s, [ya], pre, x, Tree.part(~S, ~fetch, s, ya)),
        Tree.list.go(~S, ~fetch, f, s, [yb], pre, x, Tree.part(~S, ~fetch, s, yb)),
        Binding{k, v},
        Tree.list_part(
          ~S,
          ~fetch,
          f,
          s,
          [ya],
          pre,
          x,
          Tree.part(~S, ~fetch, s, ya),
          0n,
          t,
          k,
          v,
          pth,
          {==},
          ht,
          hq,
          hd,
          hf,
          hg
        )
      )
    case False{}:
      Shared.List.contains_right(
        ~Binding,
        ~Binding.is_eq,
        Tree.list.go(~S, ~fetch, f, s, [ya], pre, x, Tree.part(~S, ~fetch, s, ya)),
        Tree.list.go(~S, ~fetch, f, s, [yb], pre, x, Tree.part(~S, ~fetch, s, yb)),
        Binding{k, v},
        Tree.list_part(
          ~S,
          ~fetch,
          f,
          s,
          [yb],
          pre,
          x,
          Tree.part(~S, ~fetch, s, yb),
          0n,
          t,
          k,
          v,
          pth,
          {==},
          ht,
          hq,
          hd,
          hf,
          hg
        )
      )

# the listings of the trees whose root nodes are ma and mb hold the binding of
# k and v, when the side c of them reads v for k
def Tree.diff_roots(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ma: Maybe<&2, Node>,
  +mb: Maybe<&2, Node>,
  c: Bool,
  hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, ma),
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, mb)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    List.append(&2, Binding, Tree.list.root(~S, ~fetch, s, ma), Tree.list.root(~S, ~fetch, s, mb)),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      Shared.List.contains_left(
        ~Binding,
        ~Binding.is_eq,
        Tree.list.root(~S, ~fetch, s, ma),
        Tree.list.root(~S, ~fetch, s, mb),
        Binding{k, v},
        Tree.list_root(~S, ~fetch, s, k, v, Tree.path(k), ma, {==}, hg)
      )
    case False{}:
      Shared.List.contains_right(
        ~Binding,
        ~Binding.is_eq,
        Tree.list.root(~S, ~fetch, s, ma),
        Tree.list.root(~S, ~fetch, s, mb),
        Binding{k, v},
        Tree.list_root(~S, ~fetch, s, k, v, Tree.path(k), mb, {==}, hg)
      )

# ds holds the binding of k and v, when the side c of two branches of the
# parts qa and qb reads v for k along p while the other does not, and ds
# holds it whenever that holds one level down (along rp, at their parts z)
def Tree.diff_down(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  qa: List<&2, Maybe<&2, Hashes.Hash>>,
  qb: List<&2, Maybe<&2, Hashes.Hash>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  p: List<&2, Nat>,
  c: Bool,
  ds: List<&2, Binding>,
  hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{qa}}),
      Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{qb}})
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  hn: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{qb}}),
      Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{qa}})
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Empty,
  ih: @z: Nat -> @rp: List<
    &2,
    Nat> -> {
    p == z <> rp: List<&2, Nat>
  } -> {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(qa, z))),
      Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(qb, z)))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> (
    {
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        c,
        Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(qb, z))),
        Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(qa, z)))
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    } -> Empty
  ) -> {List.contains(~Binding, ~Binding.is_eq, ds, Binding{k, v}) == True{}: Bool}
) -> {List.contains(~Binding, ~Binding.is_eq, ds, Binding{k, v}) == True{}: Bool}:
  match p:
    case Nil{}:
      Empty.absurd(
        {List.contains(~Binding, ~Binding.is_eq, ds, Binding{k, v}) == True{}: Bool},
        hn(hg)
      )
    case Con{z, rp}:
      ih(z, rp, {==}, hg, hn)

# a pick of d between ds and fs holds the binding of k and v, when fs holds
# it, the side c of the nodes ma and mb reads v for k along p while the other
# does not, and ds holds it whenever that holds one level down (d: both are
# branches)
def Tree.diff_deep(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ma: Maybe<&2, Node>,
  +mb: Maybe<&2, Node>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  +p: List<&2, Nat>,
  +c: Bool,
  d: Bool,
  +ed: {Bool.and(Node.is_branch(ma), Node.is_branch(mb)) == d: Bool},
  ds: List<&2, Binding>,
  fs: List<&2, Binding>,
  flat: {List.contains(~Binding, ~Binding.is_eq, fs, Binding{k, v}) == True{}: Bool},
  hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, ma),
      Tree.get.go(~S, ~fetch, s, p, k, mb)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  hn: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, p, k, mb),
      Tree.get.go(~S, ~fetch, s, p, k, ma)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Empty,
  ih: @z: Nat -> @rp: List<
    &2,
    Nat> -> {
    p == z <> rp: List<&2, Nat>
  } -> {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(Node.kids(ma), z))),
      Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(Node.kids(mb), z)))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> (
    {
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        c,
        Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(Node.kids(mb), z))),
        Tree.get.go(~S, ~fetch, s, rp, k, Tree.part(~S, ~fetch, s, Parts.at(Node.kids(ma), z)))
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    } -> Empty
  ) -> {List.contains(~Binding, ~Binding.is_eq, ds, Binding{k, v}) == True{}: Bool}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(List<&2, Binding>, d, u => ds, u => fs),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match d:
    case False{}:
      flat
    case True{}:
      +ea = Node.kids_of(ma)(Shared.Bool.and_true_left(Node.is_branch(ma), Node.is_branch(mb))(ed))
      +eb = Node.kids_of(mb)(Shared.Bool.and_true_right(Node.is_branch(ma), Node.is_branch(mb))(ed))
      Tree.diff_down(
        ~S,
        ~fetch,
        s,
        Node.kids(ma),
        Node.kids(mb),
        k,
        v,
        p,
        c,
        ds,
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Bool.pick(
            Maybe<&2, List<&2, U32>>,
            c,
            Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(ma)}}),
            Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(mb)}})
          ),
          Bool.pick(
            Maybe<&2, List<&2, U32>>,
            c,
            Tree.get.go(~S, ~fetch, s, p, k, ma),
            Tree.get.go(~S, ~fetch, s, p, k, mb)
          ),
          Some{v},
          Equal.sym(
            Maybe<&2, List<&2, U32>>,
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, ma),
              Tree.get.go(~S, ~fetch, s, p, k, mb)
            ),
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(ma)}}),
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(mb)}})
            ),
            Tree.pick_at(
              ~S,
              ~fetch,
              s,
              c,
              p,
              k,
              ma,
              Some{Node.Branch{Node.kids(ma)}},
              mb,
              Some{Node.Branch{Node.kids(mb)}},
              ea,
              eb
            )
          ),
          hg
        ),
        e => hn(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, mb),
              Tree.get.go(~S, ~fetch, s, p, k, ma)
            ),
            Bool.pick(
              Maybe<&2, List<&2, U32>>,
              c,
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(mb)}}),
              Tree.get.go(~S, ~fetch, s, p, k, Some{Node.Branch{Node.kids(ma)}})
            ),
            Some{v},
            Tree.pick_at(
              ~S,
              ~fetch,
              s,
              c,
              p,
              k,
              mb,
              Some{Node.Branch{Node.kids(mb)}},
              ma,
              Some{Node.Branch{Node.kids(ma)}},
              eb,
              ea
            ),
            e
          )
        ),
        ih
      )

# a pick of d between rest and xs then rest holds what rest holds
def Tree.diff_skip.when(
  d: Bool,
  xs: List<&2, Binding>,
  rest: List<&2, Binding>,
  b: Binding,
  h: {List.contains(~Binding, ~Binding.is_eq, rest, b) == True{}: Bool}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(List<&2, Binding>, d, u => rest, u => List.append(&2, Binding, xs, rest)),
    b
  )
    == True{}: Bool
}:
  match d:
    case True{}:
      h
    case False{}:
      Shared.List.contains_right(~Binding, ~Binding.is_eq, xs, rest, b, h)

# the difference of the parts ya <> ra and yb <> rb holds what the difference
# of ra and rb holds
def Tree.diff_skip(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +ya: Maybe<&2, Hashes.Hash>,
  +ra: List<&2, Maybe<&2, Hashes.Hash>>,
  +yb: Maybe<&2, Hashes.Hash>,
  +rb: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  b: Binding,
  h: {
    List.contains(
      ~Binding,
      ~Binding.is_eq,
      Tree.diff.go(
        ~S,
        ~fetch,
        f,
        s,
        ra,
        rb,
        pre,
        1n+x,
        Tree.first(~S, ~fetch, s, ra),
        Tree.first(~S, ~fetch, s, rb)
      ),
      b
    )
      == True{}: Bool
  }
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.diff.go(
      ~S,
      ~fetch,
      f,
      s,
      ya <> ra,
      yb <> rb,
      pre,
      x,
      Tree.part(~S, ~fetch, s, ya),
      Tree.part(~S, ~fetch, s, yb)
    ),
    b
  )
    == True{}: Bool
}:
  match f:
    case 0n:
      Tree.diff_skip.when(
        Parts.same(ya, yb),
        Tree.diff.sides(
          ~S,
          ~fetch,
          0n,
          s,
          ya,
          yb,
          pre,
          x,
          Tree.part(~S, ~fetch, s, ya),
          Tree.part(~S, ~fetch, s, yb)
        ),
        Tree.diff.go(
          ~S,
          ~fetch,
          0n,
          s,
          ra,
          rb,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, ra),
          Tree.first(~S, ~fetch, s, rb)
        ),
        b,
        h
      )
    case 1n+(+p):
      +ma = Tree.part(~S, ~fetch, s, ya)
      +mb = Tree.part(~S, ~fetch, s, yb)
      Tree.diff_skip.when(
        Parts.same(ya, yb),
        Shared.Bool.when(
          List<&2, Binding>,
          Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
          u => Tree.diff.go(
            ~S,
            ~fetch,
            p,
            s,
            Node.kids(ma),
            Node.kids(mb),
            List.append(&2, Nat, pre, [x]),
            0n,
            Tree.first(~S, ~fetch, s, Node.kids(ma)),
            Tree.first(~S, ~fetch, s, Node.kids(mb))
          ),
          u => Tree.diff.sides(~S, ~fetch, 1n+p, s, ya, yb, pre, x, ma, mb)
        ),
        Tree.diff.go(
          ~S,
          ~fetch,
          1n+p,
          s,
          ra,
          rb,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, ra),
          Tree.first(~S, ~fetch, s, rb)
        ),
        b,
        h
      )

# bend-lint: expect-begin bend-lint-rules/language/decreasing_call@warning -- g is f itself, bound by the match; the checker accepts these calls
# the difference of the parts ka and kb, from the place x of branches whose
# path is pre, holds the binding of k and v, when the side c of their parts j,
# at the place t, reads v for k along P, the rest of k's path, while the other
# does not, and f levels are enough for P
def Tree.diff_part(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ka: List<&2, Maybe<&2, Hashes.Hash>>,
  kb: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  +j: Nat,
  +t: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +pth: List<&2, Nat>,
  +c: Bool,
  ht: {Nat.add(j, x) == t: Nat},
  +hq: {
    List.take(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == List.append(&2, Nat, pre, [t]): List<&2, Nat>
  },
  +hd: {
    List.drop(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
    )
      == pth: List<&2, Nat>
  },
  +hf: {Nat.is_le(List.length(&2, Nat, pth), f) == True{}: Bool},
  +hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(ka, j))),
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(kb, j)))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  hn: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(kb, j))),
      Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(ka, j)))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Empty
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.diff.go(
      ~S,
      ~fetch,
      f,
      s,
      ka,
      kb,
      pre,
      x,
      Tree.first(~S, ~fetch, s, ka),
      Tree.first(~S, ~fetch, s, kb)
    ),
    Binding{k, v}
  )
    == True{}: Bool
}:
  match f ka kb j:
    case g Nil{} Nil{} i:
      Empty.absurd(
        {
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            Tree.diff.go(
              ~S,
              ~fetch,
              g,
              s,
              [],
              [],
              pre,
              x,
              Tree.first(~S, ~fetch, s, []),
              Tree.first(~S, ~fetch, s, [])
            ),
            Binding{k, v}
          )
            == True{}: Bool
        },
        hn(hg)
      )
    case g Con{ya, +ra} Con{yb, +rb} 1n+(+i):
      Tree.diff_skip(
        ~S,
        ~fetch,
        g,
        s,
        ya,
        ra,
        yb,
        rb,
        pre,
        x,
        Binding{k, v},
        Tree.diff_part(
          ~S,
          ~fetch,
          g,
          s,
          ra,
          rb,
          pre,
          1n+x,
          i,
          t,
          k,
          v,
          pth,
          c,
          Equal.trans(Nat, Nat.add(i, 1n+x), 1n+Nat.add(i, x), t, Shared.Nat.add_succ(i, x), ht),
          hq,
          hd,
          hf,
          hg,
          hn
        )
      )
    case 0n Con{+ya, +ra} Con{+yb, +rb} 0n:
      +rest = Tree.diff.go(
        ~S,
        ~fetch,
        0n,
        s,
        ra,
        rb,
        pre,
        1n+x,
        Tree.first(~S, ~fetch, s, ra),
        Tree.first(~S, ~fetch, s, rb)
      )
      +flat = Tree.diff.sides(
        ~S,
        ~fetch,
        0n,
        s,
        ya,
        yb,
        pre,
        x,
        Tree.part(~S, ~fetch, s, ya),
        Tree.part(~S, ~fetch, s, yb)
      )
      Tree.diff_here(
        ~S,
        ~fetch,
        s,
        ya,
        yb,
        c,
        pth,
        k,
        v,
        Parts.same(ya, yb),
        {==},
        rest,
        List.append(&2, Binding, flat, rest),
        hg,
        hn,
        h => Shared.List.contains_left(
          ~Binding,
          ~Binding.is_eq,
          flat,
          rest,
          Binding{k, v},
          Tree.diff_side(~S, ~fetch, 0n, s, ya, yb, pre, x, t, k, v, pth, c, ht, hq, hd, hf, hg)
        )
      )
    case 1n+(+p) Con{+ya, +ra} Con{+yb, +rb} 0n:
      %Equal.sym(
        Nat,
        x,
        t,
        ht
      ): {
        List.contains(
          ~Binding,
          ~Binding.is_eq,
          Tree.diff.go(
            ~S,
            ~fetch,
            1n+p,
            s,
            Con{ya, ra},
            Con{yb, rb},
            pre,
            _,
            Tree.part(~S, ~fetch, s, ya),
            Tree.part(~S, ~fetch, s, yb)
          ),
          Binding{k, v}
        )
          == True{}: Bool
      }
      +ma = Tree.part(~S, ~fetch, s, ya)
      +mb = Tree.part(~S, ~fetch, s, yb)
      +here = List.append(&2, Nat, pre, [t])
      +rest = Tree.diff.go(
        ~S,
        ~fetch,
        1n+p,
        s,
        ra,
        rb,
        pre,
        1n+t,
        Tree.first(~S, ~fetch, s, ra),
        Tree.first(~S, ~fetch, s, rb)
      )
      +down = Tree.diff.go(
        ~S,
        ~fetch,
        p,
        s,
        Node.kids(ma),
        Node.kids(mb),
        here,
        0n,
        Tree.first(~S, ~fetch, s, Node.kids(ma)),
        Tree.first(~S, ~fetch, s, Node.kids(mb))
      )
      +flat = Tree.diff.sides(~S, ~fetch, 1n+p, s, ya, yb, pre, t, ma, mb)
      +w = Shared.Bool.when(
        List<&2, Binding>,
        Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
        u => down,
        u => flat
      )
      Tree.diff_here(
        ~S,
        ~fetch,
        s,
        ya,
        yb,
        c,
        pth,
        k,
        v,
        Parts.same(ya, yb),
        {==},
        rest,
        List.append(&2, Binding, w, rest),
        hg,
        hn,
        h => Shared.List.contains_left(
          ~Binding,
          ~Binding.is_eq,
          w,
          rest,
          Binding{k, v},
          Tree.diff_deep(
            ~S,
            ~fetch,
            s,
            ma,
            mb,
            k,
            v,
            pth,
            c,
            Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
            {==},
            down,
            flat,
            Tree.diff_side(~S, ~fetch, 1n+p, s, ya, yb, pre, t, t, k, v, pth, c, {==}, hq, hd, hf, hg),
            hg,
            h,
            +z => +rp => +e => a => b =>
              +hd2 = Equal.trans(List<&2, Nat>, List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, here)), pth, z <> rp, hd, e)
              Tree.diff_part(~S, ~fetch, p, s, Node.kids(ma), Node.kids(mb), here, 0n, z, z, k, v, rp, c, Shared.Nat.add_zero(z), Shared.List.take_snoc(Nat, Tree.path(k), here, z, rp, hq, hd2), Tree.drop_next(Tree.path(k), here, z, rp, hd2), Equal.trans(Bool, Nat.is_le(List.length(&2, Nat, z <> rp), 1n+p), Nat.is_le(List.length(&2, Nat, pth), 1n+p), True{}, Equal.cong(List<&2, Nat>, Bool, q => Nat.is_le(List.length(&2, Nat, q), 1n+p), z <> rp, pth, Equal.sym(List<&2, Nat>, pth, z <> rp, e)), hf), a, b))
        )
      )
    case g Con{+ya, +ra} Nil{} i:
      Tree.list_part(
        ~S,
        ~fetch,
        g,
        s,
        ya <> ra,
        pre,
        x,
        Tree.part(~S, ~fetch, s, ya),
        i,
        t,
        k,
        v,
        pth,
        {==},
        ht,
        hq,
        hd,
        hf,
        Tree.pick_one(
          ~S,
          ~fetch,
          s,
          c,
          True{},
          Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(ya <> ra, i))),
          pth,
          k,
          v,
          hg
        )
      )
    case g Nil{} Con{+yb, +rb} i:
      Tree.list_part(
        ~S,
        ~fetch,
        g,
        s,
        yb <> rb,
        pre,
        x,
        Tree.part(~S, ~fetch, s, yb),
        i,
        t,
        k,
        v,
        pth,
        {==},
        ht,
        hq,
        hd,
        hf,
        Tree.pick_one(
          ~S,
          ~fetch,
          s,
          c,
          False{},
          Tree.get.go(~S, ~fetch, s, pth, k, Tree.part(~S, ~fetch, s, Parts.at(yb <> rb, i))),
          pth,
          k,
          v,
          hg
        )
      )
# bend-lint: expect-end bend-lint-rules/language/decreasing_call@warning

# the difference of the trees whose root nodes are ma and mb holds the binding
# of k and v, when the side c of them reads v for k while the other does not
def Tree.diff_root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ma: Maybe<&2, Node>,
  +mb: Maybe<&2, Node>,
  +c: Bool,
  +hg: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, ma),
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, mb)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  hn: {
    Bool.pick(
      Maybe<&2, List<&2, U32>>,
      c,
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, mb),
      Tree.get.go(~S, ~fetch, s, Tree.path(k), k, ma)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Empty
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.diff.root(~S, ~fetch, s, ma, mb),
    Binding{k, v}
  )
    == True{}: Bool
}:
  Tree.diff_deep(
    ~S,
    ~fetch,
    s,
    ma,
    mb,
    k,
    v,
    Tree.path(k),
    c,
    Bool.and(Node.is_branch(ma), Node.is_branch(mb)),
    {==},
    Tree.diff.go(
      ~S,
      ~fetch,
      63n,
      s,
      Node.kids(ma),
      Node.kids(mb),
      [],
      0n,
      Tree.first(~S, ~fetch, s, Node.kids(ma)),
      Tree.first(~S, ~fetch, s, Node.kids(mb))
    ),
    List.append(&2, Binding, Tree.list.root(~S, ~fetch, s, ma), Tree.list.root(~S, ~fetch, s, mb)),
    Tree.diff_roots(~S, ~fetch, s, k, v, ma, mb, c, hg),
    hg,
    hn,
    +z => +rp => +e => a => b => Tree.diff_part(
      ~S,
      ~fetch,
      63n,
      s,
      Node.kids(ma),
      Node.kids(mb),
      [],
      0n,
      z,
      z,
      k,
      v,
      rp,
      c,
      Shared.Nat.add_zero(z),
      Tree.list_root.take(k, z, rp, e),
      Tree.list_root.drop(k, z, rp, e),
      Tree.list_root.deep(k, z, rp, e),
      a,
      b
    )
  )

# a key that the tree a reads as v, and the tree b does not, is listed in
# their difference (and so for b against a)
law Tree.diff_complete:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +a: Maybe<&2, Hashes.Hash>
  for +b: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  {Tree.get.plain(~S, ~fetch, s, a, k) == Some{v}: Maybe<&2, List<&2, U32>>}
    -> ({Tree.get.plain(~S, ~fetch, s, b, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> Empty)
    -> {
      List.contains(
        ~Binding,
        ~Binding.is_eq,
        Tree.diff(~S, ~fetch, s, a, b),
        Binding{k, v}
      )
        == True{}: Bool
    }

def Tree.diff_complete(ty, fetch, s, a, b, k, v):
  +hg => hn =>
    Tree.diff_here(
      ~ty,
      ~fetch,
      s,
      a,
      b,
      True{},
      Tree.path(k),
      k,
      v,
      Parts.same(a, b),
      {==},
      [],
      Tree.diff.root(~ty, ~fetch, s, Tree.part(~ty, ~fetch, s, a), Tree.part(~ty, ~fetch, s, b)),
      hg,
      hn,
      h => Tree.diff_root(
        ~ty,
        ~fetch,
        s,
        k,
        v,
        Tree.part(~ty, ~fetch, s, a),
        Tree.part(~ty, ~fetch, s, b),
        True{},
        hg,
        h
      )
    )

# a key that the tree b reads as v, and the tree a does not, is listed in
# their difference
law Tree.diff_complete_right:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +a: Maybe<&2, Hashes.Hash>
  for +b: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  {Tree.get.plain(~S, ~fetch, s, b, k) == Some{v}: Maybe<&2, List<&2, U32>>}
    -> ({Tree.get.plain(~S, ~fetch, s, a, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> Empty)
    -> {
      List.contains(
        ~Binding,
        ~Binding.is_eq,
        Tree.diff(~S, ~fetch, s, a, b),
        Binding{k, v}
      )
        == True{}: Bool
    }

def Tree.diff_complete_right(ty, fetch, s, a, b, k, v):
  +hg => hn =>
    Tree.diff_here(
      ~ty,
      ~fetch,
      s,
      a,
      b,
      False{},
      Tree.path(k),
      k,
      v,
      Parts.same(a, b),
      {==},
      [],
      Tree.diff.root(~ty, ~fetch, s, Tree.part(~ty, ~fetch, s, a), Tree.part(~ty, ~fetch, s, b)),
      hg,
      hn,
      h => Tree.diff_root(
        ~ty,
        ~fetch,
        s,
        k,
        v,
        Tree.part(~ty, ~fetch, s, a),
        Tree.part(~ty, ~fetch, s, b),
        False{},
        hg,
        h
      )
    )

# the key of a binding
def Binding.key(b: Binding) -> List<&2, U32>:
  match b:
    case Binding{k, v}:
      k

# a binding of k and v, found under the parts ps of a branch whose path is pre,
# from the place x: the part j there, at the place t, reads v for k
def Tree.Found(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  k: List<&2, U32>,
  v: List<&2, U32>,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  pre: List<&2, Nat>,
  x: Nat
) -> Type:
  Sigma<
    &1,
    &1,
    Nat,
    j => Sigma<
      &1,
      &1,
      Nat,
      t => {
        Nat.add(j, x) == t: Nat
      }
        & (
          {
            List.take(
              &2,
              Nat,
              Tree.path(k),
              List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
            )
              == List.append(&2, Nat, pre, [t]): List<&2, Nat>
          }
            & {
              Tree.get.go(
                ~S,
                ~fetch,
                s,
                List.drop(
                  &2,
                  Nat,
                  Tree.path(k),
                  List.length(&2, Nat, List.append(&2, Nat, pre, [t]))
                ),
                k,
                Tree.part(~S, ~fetch, s, Parts.at(ps, j))
              )
                == Some{v}: Maybe<&2, List<&2, U32>>
            }
        )>>

# a binding found under the parts after the first is found under them all
def Tree.Found.next(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  k: List<&2, U32>,
  v: List<&2, U32>,
  y: Maybe<&2, Hashes.Hash>,
  r: List<&2, Maybe<&2, Hashes.Hash>>,
  pre: List<&2, Nat>,
  x: Nat,
  fd: Tree.Found(~S, ~fetch, s, k, v, r, pre, 1n+x)
) -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x):
  match fd:
    case Tuple{+j, Tuple{t, Tuple{ht, Tuple{hq, hg}}}}:
      (
        1n+j,
        (
          t,
          (
            Equal.trans(
              Nat,
              1n+Nat.add(j, x),
              Nat.add(j, 1n+x),
              t,
              Equal.sym(Nat, Nat.add(j, 1n+x), 1n+Nat.add(j, x), Shared.Nat.add_succ(j, x)),
              ht
            ),
            (hq, hg)
          )
        )
      )

# a key whose path starts with q, then t, read along what follows in a branch
# of parts qs, reads in the branch m along what follows q
def Tree.list_found.up(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  k: List<&2, U32>,
  -v: List<&2, U32>,
  q: List<&2, Nat>,
  -m: Maybe<&2, Node>,
  qs: List<&2, Maybe<&2, Hashes.Hash>>,
  -j: Nat,
  t: Nat,
  jt: {j == t: Nat},
  em: {m == Some{Node.Branch{qs}}: Maybe<&2, Node>},
  hq: {
    List.take(
      &2,
      Nat,
      Tree.path(k),
      List.length(&2, Nat, List.append(&2, Nat, q, [t]))
    )
      == List.append(&2, Nat, q, [t]): List<&2, Nat>
  },
  hg: {
    Tree.get.go(
      ~S,
      ~fetch,
      s,
      List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, List.append(&2, Nat, q, [t]))),
      k,
      Tree.part(~S, ~fetch, s, Parts.at(qs, j))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, q)),
    k,
    m
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Node>,
    m,
    Some{Node.Branch{qs}},
    em
  ): {
    Tree.get.go(
      ~S,
      ~fetch,
      s,
      List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, q)),
      k,
      _
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  %Equal.sym(
    List<&2, Nat>,
    List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, q)),
    t <> List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, List.append(&2, Nat, q, [t]))),
    Shared.List.drop_at(Nat, Tree.path(k), q, t, hq)
  ): {Tree.get.go(~S, ~fetch, s, _, k, Some{Node.Branch{qs}}) == Some{v}: Maybe<&2, List<&2, U32>>}
  %jt: {
    Tree.get.go(
      ~S,
      ~fetch,
      s,
      List.drop(&2, Nat, Tree.path(k), List.length(&2, Nat, List.append(&2, Nat, q, [t]))),
      k,
      Tree.part(~S, ~fetch, s, Parts.at(qs, _))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  hg

# a binding found under a branch that is the first part is found under the parts
def Tree.Found.up(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  y: Maybe<&2, Hashes.Hash>,
  r: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  qs: List<&2, Maybe<&2, Hashes.Hash>>,
  em: {Tree.part(~S, ~fetch, s, y) == Some{Node.Branch{qs}}: Maybe<&2, Node>},
  fd: Tree.Found(~S, ~fetch, s, k, v, qs, List.append(&2, Nat, pre, [x]), 0n)
) -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x):
  match fd:
    case Tuple{j, Tuple{+t, Tuple{ht, Tuple{+hq, hg}}}}:
      (
        0n,
        (
          x,
          (
            {==},
            (
              Shared.List.take_shorten(Nat, Tree.path(k), List.append(&2, Nat, pre, [x]), t, hq),
              Tree.list_found.up(
                ~S,
                ~fetch,
                s,
                k,
                v,
                List.append(&2, Nat, pre, [x]),
                Tree.part(~S, ~fetch, s, y),
                qs,
                j,
                t,
                Equal.trans(
                  Nat,
                  j,
                  Nat.add(j, 0n),
                  t,
                  Equal.sym(Nat, Nat.add(j, 0n), j, Shared.Nat.add_zero(j)),
                  ht
                ),
                em,
                hq,
                hg
              )
            )
          )
        )
      )

# the leaf of k2 and v2, the binding of k and v, reads v for k along any path
def Tree.list_found.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  k: List<&2, U32>,
  v: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  y: Maybe<&2, Hashes.Hash>,
  pth: List<&2, Nat>,
  em: {Tree.part(~S, ~fetch, s, y) == Some{Node.Leaf{k2, v2}}: Maybe<&2, Node>},
  eb: {Binding{k2, v2} == Binding{k, v}: Binding}
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    pth,
    k,
    Tree.part(~S, ~fetch, s, y)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Node>,
    Tree.part(~S, ~fetch, s, y),
    Some{Node.Leaf{k2, v2}},
    em
  ): {Tree.get.go(~S, ~fetch, s, pth, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Maybe<&2, Node>,
    Some{Node.Leaf{k2, v2}},
    Some{Node.Leaf{k, v}},
    Equal.cong(Binding, Maybe<&2, Node>, b => Binding.leaf(b), Binding{k2, v2}, Binding{k, v}, eb)
  ): {Tree.get.go(~S, ~fetch, s, pth, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
  Tree.read_leaf(~S, ~fetch, s, pth, k, v)

# a key that leads as k2 does, when k2 is k
def Tree.leads_of(
  -k: List<&2, U32>,
  -k2: List<&2, U32>,
  -q: List<&2, Nat>,
  ek: {k2 == k: List<&2, U32>},
  ec: {Tree.leads(k2, q) == True{}: Bool}
) -> {Tree.leads(k, q) == True{}: Bool}:
  %ek: {Tree.leads(_, q) == True{}: Bool}
  ec

# a or b holds, so G holds when each gives it
def Tree.or_cases(
  -G: Type,
  a: Bool,
  -b: Bool,
  ga: {a == True{}: Bool} -> G,
  gb: {b == True{}: Bool} -> G
) -> {Bool.or(a, b) == True{}: Bool} -> G:
  match a:
    case True{}:
      e => ga({==})
    case False{}:
      e => gb(e)

# the binding of k and v, in the listing of parts whose first is a leaf of k2
# and v2 that is listed (c: the leaf is the binding of k and v), is found there
def Tree.list_found.hit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  s: S,
  y: Maybe<&2, Hashes.Hash>,
  r: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  d: Bool,
  ed: {Binding.is_eq(Binding{k2, v2}, Binding{k, v}) == d: Bool},
  ec: {Tree.leads(k2, List.append(&2, Nat, pre, [x])) == True{}: Bool},
  em: {Tree.part(~S, ~fetch, s, y) == Some{Node.Leaf{k2, v2}}: Maybe<&2, Node>},
  ih: {
    List.contains(
      ~Binding,
      ~Binding.is_eq,
      Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
      Binding{k, v}
    )
      == True{}: Bool
  } -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x)
) -> {
  List.any.if(
    u => List.contains(
      ~Binding,
      ~Binding.is_eq,
      Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
      Binding{k, v}
    ),
    d
  )
    == True{}: Bool
} -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x):
  match d:
    case True{}:
      e =>
        +eb = Binding.is_eq_sound(Binding{k2, v2}, Binding{k, v})(ed)
        (
          0n,
          (
            x,
            (
              {==},
              (
                Shared.List.is_eq_sound(
                  ~Nat,
                  ~Nat.is_eq,
                  ~Shared.Nat.laws(),
                  List.take(
                    &2,
                    Nat,
                    Tree.path(k),
                    List.length(&2, Nat, List.append(&2, Nat, pre, [x]))
                  ),
                  List.append(&2, Nat, pre, [x])
                )(
                  Tree.leads_of(
                    k,
                    k2,
                    List.append(&2, Nat, pre, [x]),
                    Equal.cong(
                      Binding,
                      List<&2, U32>,
                      b => Binding.key(b),
                      Binding{k2, v2},
                      Binding{k, v},
                      eb
                    ),
                    ec
                  )
                ),
                Tree.list_found.read(
                  ~S,
                  ~fetch,
                  s,
                  k,
                  v,
                  k2,
                  v2,
                  y,
                  List.drop(
                    &2,
                    Nat,
                    Tree.path(k),
                    List.length(&2, Nat, List.append(&2, Nat, pre, [x]))
                  ),
                  em,
                  eb
                )
              )
            )
          )
        )
    case False{}:
      e => ih(e)

# the binding of k and v, in the listing of parts whose first is a leaf of k2
# and v2, listed as c says, is found there
def Tree.list_found.leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  s: S,
  y: Maybe<&2, Hashes.Hash>,
  r: List<&2, Maybe<&2, Hashes.Hash>>,
  pre: List<&2, Nat>,
  x: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  c: Bool,
  ec: {Tree.leads(k2, List.append(&2, Nat, pre, [x])) == c: Bool},
  em: {Tree.part(~S, ~fetch, s, y) == Some{Node.Leaf{k2, v2}}: Maybe<&2, Node>},
  ih: {
    List.contains(
      ~Binding,
      ~Binding.is_eq,
      Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
      Binding{k, v}
    )
      == True{}: Bool
  } -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x)
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Shared.Bool.when(
      List<&2, Binding>,
      c,
      u => Binding{
        k2,
        v2
      }
        <> Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r)),
      u => Tree.list.go(~S, ~fetch, f, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
    ),
    Binding{k, v}
  )
    == True{}: Bool
} -> Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x):
  match c:
    case True{}:
      Tree.list_found.hit(
        ~S,
        ~fetch,
        f,
        s,
        y,
        r,
        pre,
        x,
        k,
        v,
        k2,
        v2,
        Binding.is_eq(Binding{k2, v2}, Binding{k, v}),
        {==},
        ec,
        em,
        ih
      )
    case False{}:
      ih

# bend-lint: expect-begin bend-lint-rules/language/decreasing_call@warning -- g is f itself, bound by the match; the checker accepts these calls
# bend-lint: expect-begin bend-lint-rules/performance/append_in_loop@warning -- a proof does not run
# a binding in the listing of the parts ps of a branch whose path is pre, from
# the place x, whose first node is m, is found there; f levels deep at most
def Tree.list_found.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  +pre: List<&2, Nat>,
  +x: Nat,
  m: Maybe<&2, Node>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Tree.first(~S, ~fetch, s, ps) == m: Maybe<&2, Node>}
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.go(~S, ~fetch, f, s, ps, pre, x, m),
    Binding{k, v}
  )
    == True{}: Bool
} -> Tree.Found(~S, ~fetch, s, k, v, ps, pre, x):
  match f ps m:
    case g Nil{} w:
      e => Empty.absurd(Tree.Found(~S, ~fetch, s, k, v, [], pre, x), Shared.Bool.false_ne_true(e))
    case g Con{+y, +r} Some{Node.Leaf{+k2, v2}}:
      Tree.list_found.leaf(
        ~S,
        ~fetch,
        g,
        s,
        y,
        r,
        pre,
        x,
        k,
        v,
        k2,
        v2,
        Tree.leads(k2, List.append(&2, Nat, pre, [x])),
        {==},
        em,
        e2 => Tree.Found.next(
          ~S,
          ~fetch,
          s,
          k,
          v,
          y,
          r,
          pre,
          x,
          Tree.list_found.go(
            ~S,
            ~fetch,
            g,
            s,
            r,
            pre,
            1n+x,
            Tree.first(~S, ~fetch, s, r),
            k,
            v,
            {==}
          )(e2)
        )
      )
    case 1n+(+p) Con{+y, +r} Some{Node.Branch{+qs}}:
      +below = Tree.list.go(
        ~S,
        ~fetch,
        p,
        s,
        qs,
        List.append(&2, Nat, pre, [x]),
        0n,
        Tree.first(~S, ~fetch, s, qs)
      )
      rest = Tree.list.go(~S, ~fetch, 1n+p, s, r, pre, 1n+x, Tree.first(~S, ~fetch, s, r))
      e => Tree.or_cases(
        Tree.Found(~S, ~fetch, s, k, v, Con{y, r}, pre, x),
        List.contains(~Binding, ~Binding.is_eq, below, Binding{k, v}),
        List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v}),
        e1 => Tree.Found.up(
          ~S,
          ~fetch,
          s,
          k,
          v,
          y,
          r,
          pre,
          x,
          qs,
          em,
          Tree.list_found.go(
            ~S,
            ~fetch,
            p,
            s,
            qs,
            List.append(&2, Nat, pre, [x]),
            0n,
            Tree.first(~S, ~fetch, s, qs),
            k,
            v,
            {==}
          )(e1)
        ),
        e2 => Tree.Found.next(
          ~S,
          ~fetch,
          s,
          k,
          v,
          y,
          r,
          pre,
          x,
          Tree.list_found.go(
            ~S,
            ~fetch,
            1n+p,
            s,
            r,
            pre,
            1n+x,
            Tree.first(~S, ~fetch, s, r),
            k,
            v,
            {==}
          )(e2)
        )
      )(
        Equal.trans(
          Bool,
          Bool.or(
            List.contains(~Binding, ~Binding.is_eq, below, Binding{k, v}),
            List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v})
          ),
          List.contains(
            ~Binding,
            ~Binding.is_eq,
            List.append(&2, Binding, below, rest),
            Binding{k, v}
          ),
          True{},
          Equal.sym(
            Bool,
            List.contains(
              ~Binding,
              ~Binding.is_eq,
              List.append(&2, Binding, below, rest),
              Binding{k, v}
            ),
            Bool.or(
              List.contains(~Binding, ~Binding.is_eq, below, Binding{k, v}),
              List.contains(~Binding, ~Binding.is_eq, rest, Binding{k, v})
            ),
            Shared.List.contains_append(~Binding, ~Binding.is_eq, below, rest, Binding{k, v})
          ),
          e
        )
      )
    case 0n Con{+y, +r} Some{Node.Branch{qs}}:
      e2 => Tree.Found.next(
        ~S,
        ~fetch,
        s,
        k,
        v,
        y,
        r,
        pre,
        x,
        Tree.list_found.go(
          ~S,
          ~fetch,
          0n,
          s,
          r,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, r),
          k,
          v,
          {==}
        )(e2)
      )
    case g Con{+y, +r} Some{Node.Empty{}}:
      e2 => Tree.Found.next(
        ~S,
        ~fetch,
        s,
        k,
        v,
        y,
        r,
        pre,
        x,
        Tree.list_found.go(
          ~S,
          ~fetch,
          g,
          s,
          r,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, r),
          k,
          v,
          {==}
        )(e2)
      )
    case g Con{+y, +r} None{}:
      e2 => Tree.Found.next(
        ~S,
        ~fetch,
        s,
        k,
        v,
        y,
        r,
        pre,
        x,
        Tree.list_found.go(
          ~S,
          ~fetch,
          g,
          s,
          r,
          pre,
          1n+x,
          Tree.first(~S, ~fetch, s, r),
          k,
          v,
          {==}
        )(e2)
      )
# bend-lint: expect-end bend-lint-rules/language/decreasing_call@warning
# bend-lint: expect-end bend-lint-rules/performance/append_in_loop@warning

# a binding found under the parts qs of the root reads at the root branch
def Tree.Found.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  qs: List<&2, Maybe<&2, Hashes.Hash>>,
  fd: Tree.Found(~S, ~fetch, s, k, v, qs, [], 0n)
) -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    Tree.path(k),
    k,
    Some{Node.Branch{qs}}
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match fd:
    case Tuple{j, Tuple{t, Tuple{ht, Tuple{hq, hg}}}}:
      %Shared.List.drop_zero(
        &2,
        Nat,
        Tree.path(k)
      ): {
        Tree.get.go(~S, ~fetch, s, _, k, Some{Node.Branch{qs}}) == Some{v}: Maybe<&2, List<&2, U32>>
      }
      Tree.list_found.up(
        ~S,
        ~fetch,
        s,
        k,
        v,
        [],
        Some{Node.Branch{qs}},
        qs,
        j,
        t,
        Equal.trans(
          Nat,
          j,
          Nat.add(j, 0n),
          t,
          Equal.sym(Nat, Nat.add(j, 0n), j, Shared.Nat.add_zero(j)),
          ht
        ),
        {==},
        hq,
        hg
      )

# the binding of k and v, when the leaf of k2 and v2 is it, reads v for k
def Tree.list_found.root.hit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>,
  d: Bool,
  ed: {Binding.is_eq(Binding{k2, v2}, Binding{k, v}) == d: Bool}
) -> {
  List.any.if(u => List.contains(~Binding, ~Binding.is_eq, [], Binding{k, v}), d) == True{}: Bool
} -> {
  Tree.get.go(
    ~S,
    ~fetch,
    s,
    Tree.path(k),
    k,
    Some{Node.Leaf{k2, v2}}
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match d:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Some{Node.Leaf{k2, v2}},
          Some{Node.Leaf{k, v}},
          Equal.cong(
            Binding,
            Maybe<&2, Node>,
            b => Binding.leaf(b),
            Binding{k2, v2},
            Binding{k, v},
            Binding.is_eq_sound(Binding{k2, v2}, Binding{k, v})(ed)
          )
        ): {Tree.get.go(~S, ~fetch, s, Tree.path(k), k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        Tree.read_leaf(~S, ~fetch, s, Tree.path(k), k, v)
    case False{}:
      e => Empty.absurd(
        {
          Tree.get.go(
            ~S,
            ~fetch,
            s,
            Tree.path(k),
            k,
            Some{Node.Leaf{k2, v2}}
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(e)
      )

# a binding in the listing of a tree whose root node is m reads in it
def Tree.list_found.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, Node>
) -> {
  List.contains(
    ~Binding,
    ~Binding.is_eq,
    Tree.list.root(~S, ~fetch, s, m),
    Binding{k, v}
  )
    == True{}: Bool
} -> {Tree.get.go(~S, ~fetch, s, Tree.path(k), k, m) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match m:
    case Some{Node.Leaf{+k2, +v2}}:
      Tree.list_found.root.hit(
        ~S,
        ~fetch,
        s,
        k,
        v,
        k2,
        v2,
        Binding.is_eq(Binding{k2, v2}, Binding{k, v}),
        {==}
      )
    case Some{Node.Branch{+qs}}:
      e => Tree.Found.root(
        ~S,
        ~fetch,
        s,
        k,
        v,
        qs,
        Tree.list_found.go(
          ~S,
          ~fetch,
          63n,
          s,
          qs,
          [],
          0n,
          Tree.first(~S, ~fetch, s, qs),
          k,
          v,
          {==}
        )(e)
      )
    case Some{Node.Empty{}}:
      e => Empty.absurd(
        {
          Tree.get.go(
            ~S,
            ~fetch,
            s,
            Tree.path(k),
            k,
            Some{Node.Empty{}}
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(e)
      )
    case None{}:
      e => Empty.absurd(
        {Tree.get.go(~S, ~fetch, s, Tree.path(k), k, None{}) == Some{v}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(e)
      )

# a listed binding reads: a listing lists only what a tree holds
law Tree.list_sound:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  {
    List.contains(
      ~Binding,
      ~Binding.is_eq,
      Tree.list(~S, ~fetch, s, h),
      Binding{k, v}
    )
      == True{}: Bool
  }
    -> {Tree.get.plain(~S, ~fetch, s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}

def Tree.list_sound(ty, fetch, s, h, k, v):
  Tree.list_found.root(~ty, ~fetch, s, k, v, Tree.part(~ty, ~fetch, s, h))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Canonical trees
# ---------------
# The root of a tree is a function of its bindings alone: Canon.root builds
# it from a list of bindings with distinct keys. A write gives the Canon.root
# of the bindings with its own (Tree.set_canon), and the store then holds the
# canonical tree (Tree.set_canon_holds). So writes of different keys commute
# (Tree.set_comm), and a second write of a key replaces the first
# (Tree.set_twice).

# the nibble at depth d of the path of the key k
def Key.nibble(k: List<&2, U32>, d: Nat) -> Nat:
  Shared.List.head_or(Nat, List.drop(&2, Nat, Tree.path(k), d), 0n)

# the binding b before the bindings r when c holds, else r
def Binds.keep(c: Bool, b: Binding, r: List<&2, Binding>) -> List<&2, Binding>:
  match c:
    case True{}:
      b <> r
    case False{}:
      r

# the bindings of bs whose key's nibble at depth d is x
def Binds.at(bs: List<&2, Binding>, +d: Nat, +x: Nat) -> List<&2, Binding>:
  match bs:
    case Nil{}:
      []
    case Con{+b, r}:
      Binds.keep(Nat.is_eq(x, Key.nibble(Binding.key(b), d)), b, Binds.at(r, d, x))

# the key k is not the key j
def Key.other(k: List<&2, U32>, j: List<&2, U32>) -> Bool:
  Bool.not(Shared.List.is_eq(~U32, ~U32.is_eq, k, j))

# the bindings of bs whose key is not k
def Binds.drop(bs: List<&2, Binding>, +k: List<&2, U32>) -> List<&2, Binding>:
  match bs:
    case Nil{}:
      []
    case Con{+b, r}:
      Binds.keep(Key.other(Binding.key(b), k), b, Binds.drop(r, k))

# the bindings bs with the key k bound to the value v
def Binds.put(bs: List<&2, Binding>, +k: List<&2, U32>, v: List<&2, U32>) -> List<&2, Binding>:
  Binding{k, v} <> Binds.drop(bs, k)

# some binding of bs has the key k
def Binds.has(bs: List<&2, Binding>, +k: List<&2, U32>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, r}:
      Shared.Bool.when(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), k),
        u => True{},
        u => Binds.has(r, k)
      )

# no two bindings of bs have the same key
def Binds.distinct(bs: List<&2, Binding>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, +r}:
      List.all.if(u => Binds.distinct(r), Bool.not(Binds.has(r, Binding.key(b))))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of a premise of a proof; a proof does not run
# the keys a and b are the same, when one is not other than the other
def Key.same(
  +a: List<&2, U32>,
  +b: List<&2, U32>
) -> {Key.other(a, b) == False{}: Bool} -> {a == b: List<&2, U32>}:
  e => Shared.List.is_eq_sound(
    ~U32,
    ~U32.is_eq,
    ~Shared.U32.laws(),
    a,
    b
  )(Shared.Bool.not_false(Shared.List.is_eq(~U32, ~U32.is_eq, a, b))(e))

# the same keys are equal
def Key.eq_of(
  a: List<&2, U32>,
  b: List<&2, U32>
) -> {a == b: List<&2, U32>} -> {Shared.List.is_eq(~U32, ~U32.is_eq, a, b) == True{}: Bool}:
  e =>
    %e: {Shared.List.is_eq(~U32, ~U32.is_eq, a, _) == True{}: Bool}
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), a)

# a drop of the key k from the binding b, kept when c, before r, which has no k
def Binds.drop_twice.at(
  c: Bool,
  b: Binding,
  r: List<&2, Binding>,
  k: List<&2, U32>,
  e: {Key.other(Binding.key(b), k) == c: Bool},
  ih: {Binds.drop(r, k) == r: List<&2, Binding>}
) -> {Binds.drop(Binds.keep(c, b, r), k) == Binds.keep(c, b, r): List<&2, Binding>}:
  match c:
    case True{}:
      %Equal.sym(Bool, Key.other(Binding.key(b), k), True{}, e):
        {Binds.keep(_, b, Binds.drop(r, k)) == b <> r: List<&2, Binding>}
      %Equal.sym(List<&2, Binding>, Binds.drop(r, k), r, ih): {b <> _ == b <> r: List<&2, Binding>}
      {==}
    case False{}:
      ih

# dropping a key twice drops it once
def Binds.drop_twice(
  bs: List<&2, Binding>,
  +k: List<&2, U32>
) -> {Binds.drop(Binds.drop(bs, k), k) == Binds.drop(bs, k): List<&2, Binding>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      Binds.drop_twice.at(
        Key.other(Binding.key(b), k),
        b,
        Binds.drop(r, k),
        k,
        {==},
        Binds.drop_twice(r, k)
      )

# dropping k1 and k2 after the binding b, kept when c1 or c2, in either order
def Binds.drop_comm.at(
  c1: Bool,
  c2: Bool,
  b: Binding,
  r: List<&2, Binding>,
  k1: List<&2, U32>,
  k2: List<&2, U32>,
  e1: {Key.other(Binding.key(b), k1) == c1: Bool},
  e2: {Key.other(Binding.key(b), k2) == c2: Bool},
  ih: {Binds.drop(Binds.drop(r, k1), k2) == Binds.drop(Binds.drop(r, k2), k1): List<&2, Binding>}
) -> {
  Binds.drop(
    Binds.keep(c1, b, Binds.drop(r, k1)),
    k2
  )
    == Binds.drop(Binds.keep(c2, b, Binds.drop(r, k2)), k1): List<&2, Binding>
}:
  match c1 c2:
    case True{} True{}:
      %Equal.sym(Bool, Key.other(Binding.key(b), k2), True{}, e2):
        {
          Binds.keep(
            _,
            b,
            Binds.drop(Binds.drop(r, k1), k2)
          )
            == Binds.keep(
              Key.other(Binding.key(b), k1),
              b,
              Binds.drop(Binds.drop(r, k2), k1)
            ): List<&2, Binding>
        }
      %Equal.sym(Bool, Key.other(Binding.key(b), k1), True{}, e1):
        {
          b
            <> Binds.drop(Binds.drop(r, k1), k2)
            == Binds.keep(_, b, Binds.drop(Binds.drop(r, k2), k1)): List<&2, Binding>
        }
      %ih:
        {b <> Binds.drop(Binds.drop(r, k1), k2) == b <> _: List<&2, Binding>}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Key.other(Binding.key(b), k2), False{}, e2):
        {
          Binds.keep(
            _,
            b,
            Binds.drop(Binds.drop(r, k1), k2)
          )
            == Binds.drop(Binds.drop(r, k2), k1): List<&2, Binding>
        }
      ih
    case False{} True{}:
      %Equal.sym(Bool, Key.other(Binding.key(b), k1), False{}, e1):
        {
          Binds.drop(
            Binds.drop(r, k1),
            k2
          )
            == Binds.keep(_, b, Binds.drop(Binds.drop(r, k2), k1)): List<&2, Binding>
        }
      ih
    case False{} False{}:
      ih

# dropping two keys does not depend on their order
def Binds.drop_comm(
  bs: List<&2, Binding>,
  +k1: List<&2, U32>,
  +k2: List<&2, U32>
) -> {Binds.drop(Binds.drop(bs, k1), k2) == Binds.drop(Binds.drop(bs, k2), k1): List<&2, Binding>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      Binds.drop_comm.at(
        Key.other(Binding.key(b), k1),
        Key.other(Binding.key(b), k2),
        b,
        r,
        k1,
        k2,
        {==},
        {==},
        Binds.drop_comm(r, k1, k2)
      )

# the bindings under the nibble x, without the key k, after the binding b, kept
# when cd (by the key) and ca (by the nibble)
def Binds.at_drop.at(
  cd: Bool,
  ca: Bool,
  b: Binding,
  r: List<&2, Binding>,
  d: Nat,
  x: Nat,
  k: List<&2, U32>,
  ed: {Key.other(Binding.key(b), k) == cd: Bool},
  ea: {Nat.is_eq(x, Key.nibble(Binding.key(b), d)) == ca: Bool},
  ih: {Binds.at(Binds.drop(r, k), d, x) == Binds.drop(Binds.at(r, d, x), k): List<&2, Binding>}
) -> {
  Binds.at(
    Binds.keep(cd, b, Binds.drop(r, k)),
    d,
    x
  )
    == Binds.drop(Binds.keep(ca, b, Binds.at(r, d, x)), k): List<&2, Binding>
}:
  match cd ca:
    case True{} True{}:
      %Equal.sym(Bool, Nat.is_eq(x, Key.nibble(Binding.key(b), d)), True{}, ea):
        {
          Binds.keep(
            _,
            b,
            Binds.at(Binds.drop(r, k), d, x)
          )
            == Binds.keep(
              Key.other(Binding.key(b), k),
              b,
              Binds.drop(Binds.at(r, d, x), k)
            ): List<&2, Binding>
        }
      %Equal.sym(Bool, Key.other(Binding.key(b), k), True{}, ed):
        {
          b
            <> Binds.at(Binds.drop(r, k), d, x)
            == Binds.keep(_, b, Binds.drop(Binds.at(r, d, x), k)): List<&2, Binding>
        }
      %ih:
        {b <> Binds.at(Binds.drop(r, k), d, x) == b <> _: List<&2, Binding>}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(x, Key.nibble(Binding.key(b), d)), False{}, ea):
        {
          Binds.keep(
            _,
            b,
            Binds.at(Binds.drop(r, k), d, x)
          )
            == Binds.drop(Binds.at(r, d, x), k): List<&2, Binding>
        }
      ih
    case False{} True{}:
      %Equal.sym(Bool, Key.other(Binding.key(b), k), False{}, ed):
        {
          Binds.at(
            Binds.drop(r, k),
            d,
            x
          )
            == Binds.keep(_, b, Binds.drop(Binds.at(r, d, x), k)): List<&2, Binding>
        }
      ih
    case False{} False{}:
      ih

# the bindings under a nibble, without a key, are those without the key, under
# the nibble
def Binds.at_drop(
  bs: List<&2, Binding>,
  +d: Nat,
  +x: Nat,
  +k: List<&2, U32>
) -> {Binds.at(Binds.drop(bs, k), d, x) == Binds.drop(Binds.at(bs, d, x), k): List<&2, Binding>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      Binds.at_drop.at(
        Key.other(Binding.key(b), k),
        Nat.is_eq(x, Key.nibble(Binding.key(b), d)),
        b,
        r,
        d,
        x,
        k,
        {==},
        {==},
        Binds.at_drop(r, d, x, k)
      )

# the bindings under the nibble z, without the key k, whose nibble is not z,
# after the binding b, kept when cd
def Binds.at_drop_other.at(
  cd: Bool,
  b: Binding,
  r: List<&2, Binding>,
  d: Nat,
  z: Nat,
  k: List<&2, U32>,
  ed: {Key.other(Binding.key(b), k) == cd: Bool},
  hz: {Nat.is_eq(z, Key.nibble(k, d)) == False{}: Bool},
  ih: {Binds.at(Binds.drop(r, k), d, z) == Binds.at(r, d, z): List<&2, Binding>}
) -> {
  Binds.at(
    Binds.keep(cd, b, Binds.drop(r, k)),
    d,
    z
  )
    == Binds.keep(
      Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
      b,
      Binds.at(r, d, z)
    ): List<&2, Binding>
}:
  match cd:
    case True{}:
      %Equal.sym(List<&2, Binding>, Binds.at(Binds.drop(r, k), d, z), Binds.at(r, d, z), ih):
        {
          Binds.keep(
            Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
            b,
            _
          )
            == Binds.keep(
              Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
              b,
              Binds.at(r, d, z)
            ): List<&2, Binding>
        }
      {==}
    case False{}:
      %Equal.sym(List<&2, U32>, Binding.key(b), k, Key.same(Binding.key(b), k)(ed)):
        {
          Binds.at(
            Binds.drop(r, k),
            d,
            z
          )
            == Binds.keep(Nat.is_eq(z, Key.nibble(_, d)), b, Binds.at(r, d, z)): List<&2, Binding>
        }
      %Equal.sym(Bool, Nat.is_eq(z, Key.nibble(k, d)), False{}, hz):
        {Binds.at(Binds.drop(r, k), d, z) == Binds.keep(_, b, Binds.at(r, d, z)): List<&2, Binding>}
      ih

# the bindings under a nibble that the key k is not under are the same
# without k
def Binds.at_drop_other(
  bs: List<&2, Binding>,
  +d: Nat,
  +z: Nat,
  +k: List<&2, U32>
) -> {
  Nat.is_eq(z, Key.nibble(k, d)) == False{}: Bool
} -> {Binds.at(Binds.drop(bs, k), d, z) == Binds.at(bs, d, z): List<&2, Binding>}:
  match bs:
    case Nil{}:
      hz => {==}
    case Con{+b, +r}:
      +hz => Binds.at_drop_other.at(
        Key.other(Binding.key(b), k),
        b,
        r,
        d,
        z,
        k,
        {==},
        hz,
        Binds.at_drop_other(r, d, z, k)(hz)
      )

# the binding b, kept when c before r, which has no key j, has no j when b's
# key is not j
def Binds.has_keep(
  c: Bool,
  b: Binding,
  r: List<&2, Binding>,
  j: List<&2, U32>,
  e: {Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j) == False{}: Bool},
  h: {Binds.has(r, j) == False{}: Bool}
) -> {Binds.has(Binds.keep(c, b, r), j) == False{}: Bool}:
  match c:
    case True{}:
      %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j), False{}, e):
        {Shared.Bool.when(Bool, _, u => True{}, u => Binds.has(r, j)) == False{}: Bool}
      h
    case False{}:
      h

# the first key of a list without the key j is not j, when that is c
def Binds.has_head.at(
  c: Bool,
  b: Binding,
  r: List<&2, Binding>,
  j: List<&2, U32>,
  e: {Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j) == c: Bool}
) -> {
  Shared.Bool.when(Bool, c, u => True{}, u => Binds.has(r, j)) == False{}: Bool
} -> {c == False{}: Bool}:
  match c:
    case True{}:
      h => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => {==}

# the first key of a list without the key j is not j
def Binds.has_head(
  +b: Binding,
  r: List<&2, Binding>,
  +j: List<&2, U32>
) -> {
  Binds.has(b <> r, j) == False{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j) == False{}: Bool}:
  Binds.has_head.at(Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j), b, r, j, {==})

# the rest of a list without the key j has no j, when the first key is c
def Binds.has_tail.at(
  c: Bool,
  r: List<&2, Binding>,
  j: List<&2, U32>
) -> {
  Shared.Bool.when(Bool, c, u => True{}, u => Binds.has(r, j)) == False{}: Bool
} -> {Binds.has(r, j) == False{}: Bool}:
  match c:
    case True{}:
      h => Empty.absurd(
        {Binds.has(r, j) == False{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      h => h

# the rest of a list without the key j has no j
def Binds.has_tail(
  b: Binding,
  r: List<&2, Binding>,
  +j: List<&2, U32>
) -> {Binds.has(b <> r, j) == False{}: Bool} -> {Binds.has(r, j) == False{}: Bool}:
  Binds.has_tail.at(Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), j), r, j)

# a list without the key k has no k
def Binds.has_drop.at(
  c: Bool,
  +b: Binding,
  r: List<&2, Binding>,
  +k: List<&2, U32>,
  e: {Key.other(Binding.key(b), k) == c: Bool},
  ih: {Binds.has(r, k) == False{}: Bool}
) -> {Binds.has(Binds.keep(c, b, r), k) == False{}: Bool}:
  match c:
    case True{}:
      Binds.has_keep(
        True{},
        b,
        r,
        k,
        Shared.Bool.not_true(Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b), k))(e),
        ih
      )
    case False{}:
      ih

# the bindings without the key k have no k
def Binds.has_drop(
  bs: List<&2, Binding>,
  +k: List<&2, U32>
) -> {Binds.has(Binds.drop(bs, k), k) == False{}: Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +r}:
      Binds.has_drop.at(
        Key.other(Binding.key(b), k),
        b,
        Binds.drop(r, k),
        k,
        {==},
        Binds.has_drop(r, k)
      )

# the bindings bs without a key k have no key j that bs has not
def Binds.has_drop_other(
  bs: List<&2, Binding>,
  +j: List<&2, U32>,
  +k: List<&2, U32>
) -> {Binds.has(bs, j) == False{}: Bool} -> {Binds.has(Binds.drop(bs, k), j) == False{}: Bool}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +r}:
      +h => Binds.has_keep(
        Key.other(Binding.key(b), k),
        b,
        Binds.drop(r, k),
        j,
        Binds.has_head(b, r, j)(h),
        Binds.has_drop_other(r, j, k)(Binds.has_tail(b, r, j)(h))
      )

# the bindings of bs under a nibble have no key j that bs has not
def Binds.has_at(
  bs: List<&2, Binding>,
  +j: List<&2, U32>,
  +d: Nat,
  +x: Nat
) -> {Binds.has(bs, j) == False{}: Bool} -> {Binds.has(Binds.at(bs, d, x), j) == False{}: Bool}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +r}:
      +h => Binds.has_keep(
        Nat.is_eq(x, Key.nibble(Binding.key(b), d)),
        b,
        Binds.at(r, d, x),
        j,
        Binds.has_head(b, r, j)(h),
        Binds.has_at(r, j, d, x)(Binds.has_tail(b, r, j)(h))
      )

# the rest of distinct bindings has no first key
def Binds.distinct_has(
  +b: Binding,
  +r: List<&2, Binding>
) -> {Binds.distinct(b <> r) == True{}: Bool} -> {Binds.has(r, Binding.key(b)) == False{}: Bool}:
  h => Shared.Bool.not_true(
    Binds.has(r, Binding.key(b))
  )(Shared.List.all.if_hit(Bool.not(Binds.has(r, Binding.key(b))), u => Binds.distinct(r))(h))

# the rest of distinct bindings is distinct
def Binds.distinct_rest(
  b: Binding,
  +r: List<&2, Binding>
) -> {Binds.distinct(b <> r) == True{}: Bool} -> {Binds.distinct(r) == True{}: Bool}:
  h => Shared.List.all.if_rest(Bool.not(Binds.has(r, Binding.key(b))), u => Binds.distinct(r))(h)

# the binding b, kept when c before distinct bindings without its key, gives
# distinct bindings
def Binds.distinct_keep(
  c: Bool,
  b: Binding,
  r: List<&2, Binding>
) -> {
  Binds.has(r, Binding.key(b)) == False{}: Bool
} -> {Binds.distinct(r) == True{}: Bool} -> {Binds.distinct(Binds.keep(c, b, r)) == True{}: Bool}:
  match c:
    case True{}:
      h1 => h2 =>
        %Equal.sym(Bool, Binds.has(r, Binding.key(b)), False{}, h1):
          {List.all.if(u => Binds.distinct(r), Bool.not(_)) == True{}: Bool}
        h2
    case False{}:
      h1 => h2 => h2

# distinct bindings without a key are distinct
def Binds.distinct_drop(
  bs: List<&2, Binding>,
  +k: List<&2, U32>
) -> {Binds.distinct(bs) == True{}: Bool} -> {Binds.distinct(Binds.drop(bs, k)) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +r}:
      +h => Binds.distinct_keep(
        Key.other(Binding.key(b), k),
        b,
        Binds.drop(r, k)
      )(
        Binds.has_drop_other(r, Binding.key(b), k)(Binds.distinct_has(b, r)(h))
      )(Binds.distinct_drop(r, k)(Binds.distinct_rest(b, r)(h)))

# distinct bindings under a nibble are distinct
def Binds.distinct_at(
  bs: List<&2, Binding>,
  +d: Nat,
  +x: Nat
) -> {Binds.distinct(bs) == True{}: Bool} -> {Binds.distinct(Binds.at(bs, d, x)) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => {==}
    case Con{+b, +r}:
      +h => Binds.distinct_keep(
        Nat.is_eq(x, Key.nibble(Binding.key(b), d)),
        b,
        Binds.at(r, d, x)
      )(
        Binds.has_at(r, Binding.key(b), d, x)(Binds.distinct_has(b, r)(h))
      )(Binds.distinct_at(r, d, x)(Binds.distinct_rest(b, r)(h)))

# distinct bindings with a key bound are distinct
def Binds.distinct_put(
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> {Binds.distinct(bs) == True{}: Bool} -> {Binds.distinct(Binds.put(bs, k, v)) == True{}: Bool}:
  h =>
    %Equal.sym(Bool, Binds.has(Binds.drop(bs, k), k), False{}, Binds.has_drop(bs, k)):
      {List.all.if(u => Binds.distinct(Binds.drop(bs, k)), Bool.not(_)) == True{}: Bool}
    Binds.distinct_drop(bs, k)(h)

# two distinct bindings, kept when c1 and c2, without the key k, leave one
def Binds.drop_many.at(
  c1: Bool,
  c2: Bool,
  +b1: Binding,
  +b2: Binding,
  +r: List<&2, Binding>,
  +k: List<&2, U32>,
  e1: {Key.other(Binding.key(b1), k) == c1: Bool},
  e2: {Key.other(Binding.key(b2), k) == c2: Bool},
  h: {Binds.distinct(b1 <> b2 <> r) == True{}: Bool}
) -> {
  List.is_empty(
    &2,
    Binding,
    Binds.keep(c1, b1, Binds.keep(c2, b2, Binds.drop(r, k)))
  )
    == False{}: Bool
}:
  match c1 c2:
    case True{} c:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Empty.absurd(
        {List.is_empty(&2, Binding, Binds.drop(r, k)) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b2), Binding.key(b1)),
            True{},
            Equal.sym(
              Bool,
              Shared.List.is_eq(~U32, ~U32.is_eq, Binding.key(b2), Binding.key(b1)),
              False{},
              Binds.has_head(b2, r, Binding.key(b1))(Binds.distinct_has(b1, b2 <> r)(h))
            ),
            Key.eq_of(
              Binding.key(b2),
              Binding.key(b1)
            )(
              Equal.trans(
                List<&2, U32>,
                Binding.key(b2),
                k,
                Binding.key(b1),
                Key.same(Binding.key(b2), k)(e2),
                Equal.sym(List<&2, U32>, Binding.key(b1), k, Key.same(Binding.key(b1), k)(e1))
              )
            )
          )
        )
      )

# distinct bindings, two or more, without a key, leave one
def Binds.drop_many(
  +b1: Binding,
  +b2: Binding,
  r: List<&2, Binding>,
  +k: List<&2, U32>
) -> {
  Binds.distinct(b1 <> b2 <> r) == True{}: Bool
} -> {List.is_empty(&2, Binding, Binds.drop(b1 <> b2 <> r, k)) == False{}: Bool}:
  h => Binds.drop_many.at(
    Key.other(Binding.key(b1), k),
    Key.other(Binding.key(b2), k),
    b1,
    b2,
    r,
    k,
    {==},
    {==},
    h
  )

# the part x, then the parts l, trimmed twice, are trimmed once, when l is
def Parts.trim_of_twice(
  x: Maybe<&2, Hashes.Hash>,
  l: List<&2, Maybe<&2, Hashes.Hash>>
) -> {
  Parts.trim(l) == l: List<&2, Maybe<&2, Hashes.Hash>>
} -> {Parts.trim(Parts.trim.of(x, l)) == Parts.trim.of(x, l): List<&2, Maybe<&2, Hashes.Hash>>}:
  match x l:
    case None{} Nil{}:
      h => {==}
    case None{} Con{h1, q}:
      h =>
        %Equal.sym(List<&2, Maybe<&2, Hashes.Hash>>, Parts.trim(h1 <> q), h1 <> q, h):
          {Parts.trim.of(None{}, _) == None{} <> h1 <> q: List<&2, Maybe<&2, Hashes.Hash>>}
        {==}
    case Some{z} q:
      h =>
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Parts.trim(q),
          q,
          h
        ): {Parts.trim.of(Some{z}, _) == Some{z} <> q: List<&2, Maybe<&2, Hashes.Hash>>}
        {==}

# trimming twice trims once
def Parts.trim_twice(
  ks: List<&2, Maybe<&2, Hashes.Hash>>
) -> {Parts.trim(Parts.trim(ks)) == Parts.trim(ks): List<&2, Maybe<&2, Hashes.Hash>>}:
  match ks:
    case Nil{}:
      {==}
    case Con{x, +r}:
      Parts.trim_of_twice(x, Parts.trim(r))(Parts.trim_twice(r))

# setting the first of the part x then the trimmed parts t, trimmed
def Parts.trim_set.zero(
  x: Maybe<&2, Hashes.Hash>,
  t: List<&2, Maybe<&2, Hashes.Hash>>,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.trim(t) == t: List<&2, Maybe<&2, Hashes.Hash>>
} -> {
  Parts.trim(
    Parts.set(Parts.trim.of(x, t), 0n, y)
  )
    == Parts.trim.of(y, t): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match x t:
    case None{} Nil{}:
      h => {==}
    case None{} Con{h1, q}:
      h =>
        %Equal.sym(List<&2, Maybe<&2, Hashes.Hash>>, Parts.trim(h1 <> q), h1 <> q, h):
          {Parts.trim.of(y, _) == Parts.trim.of(y, h1 <> q): List<&2, Maybe<&2, Hashes.Hash>>}
        {==}
    case Some{z} q:
      h =>
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Parts.trim(q),
          q,
          h
        ): {Parts.trim.of(y, _) == Parts.trim.of(y, q): List<&2, Maybe<&2, Hashes.Hash>>}
        {==}

# setting a later part of the part x then the parts t, trimmed
def Parts.trim_set.succ(
  x: Maybe<&2, Hashes.Hash>,
  t: List<&2, Maybe<&2, Hashes.Hash>>,
  p: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.trim(
    Parts.set(Parts.trim.of(x, t), 1n+p, y)
  )
    == Parts.trim.of(x, Parts.trim(Parts.set(t, p, y))): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match x t:
    case None{} Nil{}:
      {==}
    case None{} Con{h1, q}:
      {==}
    case Some{z} q:
      {==}

# a set part of trimmed parts, trimmed, is the set part of the parts, trimmed
def Parts.trim_set(
  l: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  +y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.trim(
    Parts.set(Parts.trim(l), n, y)
  )
    == Parts.trim(Parts.set(l, n, y)): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match l n:
    case Nil{} m:
      {==}
    case Con{x, r} 0n:
      Parts.trim_set.zero(x, Parts.trim(r), y)(Parts.trim_twice(r))
    case Con{x, +r} 1n+(+p):
      %Parts.trim_set(r, p, y):
        {
          Parts.trim(
            Parts.set(Parts.trim.of(x, Parts.trim(r)), 1n+p, y)
          )
            == Parts.trim.of(x, _): List<&2, Maybe<&2, Hashes.Hash>>
        }
      Parts.trim_set.succ(x, Parts.trim(r), p, y)

# setting two other parts does not depend on their order
def Parts.set_comm(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  b: Nat,
  x: Maybe<&2, Hashes.Hash>,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Nat.is_eq(a, b) == False{}: Bool
} -> {
  Parts.set(
    Parts.set(ks, a, x),
    b,
    y
  )
    == Parts.set(Parts.set(ks, b, y), a, x): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match ks a b:
    case Nil{} 0n 0n:
      e => Empty.absurd(
        {
          Parts.set(
            Parts.set([], 0n, x),
            0n,
            y
          )
            == Parts.set(Parts.set([], 0n, y), 0n, x): List<&2, Maybe<&2, Hashes.Hash>>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Nil{} 0n 1n+q:
      e => {==}
    case Nil{} 1n+p 0n:
      e => {==}
    case Nil{} 1n+p 1n+q:
      e =>
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Parts.set(Parts.set([], p, x), q, y),
          Parts.set(Parts.set([], q, y), p, x),
          Parts.set_comm([], p, q, x, y)(e)
        ):
          {
            None{}
              <> _
              == None{}
              <> Parts.set(Parts.set([], q, y), p, x): List<&2, Maybe<&2, Hashes.Hash>>
          }
        {==}
    case Con{h, t} 0n 0n:
      e => Empty.absurd(
        {
          Parts.set(
            Parts.set(h <> t, 0n, x),
            0n,
            y
          )
            == Parts.set(Parts.set(h <> t, 0n, y), 0n, x): List<&2, Maybe<&2, Hashes.Hash>>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Con{h, t} 0n 1n+q:
      e => {==}
    case Con{h, t} 1n+p 0n:
      e => {==}
    case Con{h, t} 1n+p 1n+q:
      e =>
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Parts.set(Parts.set(t, p, x), q, y),
          Parts.set(Parts.set(t, q, y), p, x),
          Parts.set_comm(t, p, q, x, y)(e)
        ):
          {h <> _ == h <> Parts.set(Parts.set(t, q, y), p, x): List<&2, Maybe<&2, Hashes.Hash>>}
        {==}

# setting a part twice sets it once
def Parts.set_twice(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  x: Maybe<&2, Hashes.Hash>,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.set(Parts.set(ks, a, x), a, y) == Parts.set(ks, a, y): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match ks a:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.set(Parts.set([], p, x), p, y),
        Parts.set([], p, y),
        Parts.set_twice([], p, x, y)
      ):
        {None{} <> _ == None{} <> Parts.set([], p, y): List<&2, Maybe<&2, Hashes.Hash>>}
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+p:
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.set(Parts.set(t, p, x), p, y),
        Parts.set(t, p, y),
        Parts.set_twice(t, p, x, y)
      ):
        {h <> _ == h <> Parts.set(t, p, y): List<&2, Maybe<&2, Hashes.Hash>>}
      {==}

# putting two other parts does not depend on their order
def Parts.put_comm(
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +a: Nat,
  +b: Nat,
  +x: Maybe<&2, Hashes.Hash>,
  +y: Maybe<&2, Hashes.Hash>
) -> {
  Nat.is_eq(a, b) == False{}: Bool
} -> {
  Parts.put(
    Parts.put(ks, a, x),
    b,
    y
  )
    == Parts.put(Parts.put(ks, b, y), a, x): List<&2, Maybe<&2, Hashes.Hash>>
}:
  e =>
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Parts.trim(Parts.set(Parts.trim(Parts.set(ks, a, x)), b, y)),
      Parts.trim(Parts.set(Parts.set(ks, a, x), b, y)),
      Parts.trim_set(Parts.set(ks, a, x), b, y)
    ): {_ == Parts.put(Parts.put(ks, b, y), a, x): List<&2, Maybe<&2, Hashes.Hash>>}
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Parts.trim(Parts.set(Parts.trim(Parts.set(ks, b, y)), a, x)),
      Parts.trim(Parts.set(Parts.set(ks, b, y), a, x)),
      Parts.trim_set(Parts.set(ks, b, y), a, x)
    ): {Parts.trim(Parts.set(Parts.set(ks, a, x), b, y)) == _: List<&2, Maybe<&2, Hashes.Hash>>}
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Parts.set(Parts.set(ks, a, x), b, y),
      Parts.set(Parts.set(ks, b, y), a, x),
      Parts.set_comm(ks, a, b, x, y)(e)
    ): {
      Parts.trim(
        _
      )
        == Parts.trim(Parts.set(Parts.set(ks, b, y), a, x)): List<&2, Maybe<&2, Hashes.Hash>>
    }
    {==}

# putting a part twice puts it once
def Parts.put_twice(
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +a: Nat,
  +x: Maybe<&2, Hashes.Hash>,
  +y: Maybe<&2, Hashes.Hash>
) -> {
  Parts.put(Parts.put(ks, a, x), a, y) == Parts.put(ks, a, y): List<&2, Maybe<&2, Hashes.Hash>>
}:
  %Equal.sym(
    List<&2, Maybe<&2, Hashes.Hash>>,
    Parts.trim(Parts.set(Parts.trim(Parts.set(ks, a, x)), a, y)),
    Parts.trim(Parts.set(Parts.set(ks, a, x), a, y)),
    Parts.trim_set(Parts.set(ks, a, x), a, y)
  ): {_ == Parts.put(ks, a, y): List<&2, Maybe<&2, Hashes.Hash>>}
  %Equal.sym(
    List<&2, Maybe<&2, Hashes.Hash>>,
    Parts.set(Parts.set(ks, a, x), a, y),
    Parts.set(ks, a, y),
    Parts.set_twice(ks, a, x, y)
  ):
    {Parts.trim(_) == Parts.put(ks, a, y): List<&2, Maybe<&2, Hashes.Hash>>}
  {==}

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
# the leaf of the binding b
def Binding.node(b: Binding) -> Node:
  match b:
    case Binding{k, v}:
      Node.Leaf{k, v}

# the root of the canonical tree of the bindings bs whose branch, if any, has
# the parts ps: none (no binding), a leaf (one binding) or a branch
def Canon.node(
  bs: List<&2, Binding>,
  ps: List<&2, Maybe<&2, Hashes.Hash>>
) -> Maybe<&2, Hashes.Hash>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, Nil{}}:
      Some{Node.hash(Binding.node(b))}
    case Con{b, Con{c, r}}:
      Some{Node.hash(Node.Branch{ps})}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- a law's measure of a tree, run by no node
# the parts of the canonical branch of the bindings all at depth d, n nibbles
# above the end of a path: for the nibble of each binding of bs, the canonical
# root of the bindings of all under it
def Canon.parts(
  n: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  bs: List<&2, Binding>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match n bs:
    case m Nil{}:
      []
    case 0n Con{b, r}:
      +x = Key.nibble(Binding.key(b), d)
      Parts.put(Canon.parts(0n, d, all, r), x, Canon.node(Binds.at(all, d, x), []))
    case 1n+(+m) Con{b, r}:
      +x = Key.nibble(Binding.key(b), d)
      +sub = Binds.at(all, d, x)
      Parts.put(Canon.parts(1n+m, d, all, r), x, Canon.node(sub, Canon.parts(m, 1n+d, sub, sub)))

# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint
# the canonical root of the bindings bs at depth d, n nibbles above the end of
# a path
def Canon.root(n: Nat, d: Nat, +bs: List<&2, Binding>) -> Maybe<&2, Hashes.Hash>:
  Canon.node(bs, Canon.parts(n, d, bs, bs))

# the canonical root of the bindings sub under a nibble of a branch at depth d,
# n nibbles above the end of a path
def Canon.sub(n: Nat, d: Nat, sub: List<&2, Binding>) -> Maybe<&2, Hashes.Hash>:
  match n:
    case 0n:
      Canon.node(sub, [])
    case 1n+m:
      Canon.root(m, 1n+d, sub)

# the canonical root of the bindings bs of a whole tree
def Canon.of(bs: List<&2, Binding>) -> Maybe<&2, Hashes.Hash>:
  Canon.root(64n, 0n, bs)

# the store s holds the node of the canonical root of bs, whose branch, if any,
# has the parts ps, and holds what is below it when below
def Canon.holds.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  bs: List<&2, Binding>,
  ps: List<&2, Maybe<&2, Hashes.Hash>>,
  below: Bool
) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, Nil{}}:
      Stores.Store.has(~S, ~fetch, s, Node.words(Binding.node(b)))
    case Con{b, Con{c, r}}:
      List.all.if(u => below, Stores.Store.has(~S, ~fetch, s, Node.words(Node.Branch{ps})))

# the store s holds the canonical tree under the nibble of each binding of bs,
# below a branch of the bindings all at depth d, n nibbles above the end of a
# path
def Canon.holds.parts(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  n: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  bs: List<&2, Binding>
) -> Bool:
  match n bs:
    case m Nil{}:
      True{}
    case 0n Con{b, r}:
      True{}
    case 1n+(+m) Con{b, r}:
      +sub = Binds.at(all, d, Key.nibble(Binding.key(b), d))
      List.all.if(
        u => Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, r),
        Canon.holds.node(
          ~S,
          ~fetch,
          s,
          sub,
          Canon.parts(m, 1n+d, sub, sub),
          Canon.holds.parts(~S, ~fetch, s, m, 1n+d, sub, sub)
        )
      )

# the store s holds the canonical tree of the bindings bs at depth d, n nibbles
# above the end of a path
def Canon.holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +n: Nat,
  +d: Nat,
  +bs: List<&2, Binding>
) -> Bool:
  Canon.holds.node(
    ~S,
    ~fetch,
    s,
    bs,
    Canon.parts(n, d, bs, bs),
    Canon.holds.parts(~S, ~fetch, s, n, d, bs, bs)
  )

# the store s holds the canonical tree of the bindings bs of a whole tree
def Canon.holds.of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  bs: List<&2, Binding>
) -> Bool:
  Canon.holds(~S, ~fetch, s, 64n, 0n, bs)

# canonical parts are in their one code
def Canon.parts_ok(
  n: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  bs: List<&2, Binding>
) -> {Parts.ok(Canon.parts(n, d, all, bs)) == True{}: Bool}:
  match n bs:
    case m Nil{}:
      {==}
    case 0n Con{+b, r}:
      Parts.ok_trim(
        Parts.set(
          Canon.parts(0n, d, all, r),
          Key.nibble(Binding.key(b), d),
          Canon.node(Binds.at(all, d, Key.nibble(Binding.key(b), d)), [])
        )
      )
    case 1n+(+m) Con{+b, r}:
      Parts.ok_trim(
        Parts.set(
          Canon.parts(1n+m, d, all, r),
          Key.nibble(Binding.key(b), d),
          Canon.sub(1n+m, d, Binds.at(all, d, Key.nibble(Binding.key(b), d)))
        )
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the picks are terms of proofs, which do not run
# the part z of canonical parts, put at the nibble x to v before the parts a,
# when c tells whether z is x
def Canon.at_parts.at(
  c: Bool,
  b: Binding,
  e: List<&2, Binding>,
  v: Maybe<&2, Hashes.Hash>,
  a: Maybe<&2, Hashes.Hash>,
  w: Maybe<&2, Hashes.Hash>,
  hv: {c == True{}: Bool} -> {v == w: Maybe<&2, Hashes.Hash>},
  ih: {
    a
      == Bool.pick(
        Maybe<&2, Hashes.Hash>,
        List.is_empty(&2, Binding, e),
        None{},
        w
      ): Maybe<&2, Hashes.Hash>
  }
) -> {
  Bool.pick(
    Maybe<&2, Hashes.Hash>,
    c,
    v,
    a
  )
    == Bool.pick(
      Maybe<&2, Hashes.Hash>,
      List.is_empty(&2, Binding, Binds.keep(c, b, e)),
      None{},
      w
    ): Maybe<&2, Hashes.Hash>
}:
  match c:
    case True{}:
      hv({==})
    case False{}:
      ih

# the part z of canonical parts for the nibbles of bs: the canonical root of
# the bindings of all under z, when a binding of bs is under z, else empty
def Canon.at_parts(
  n: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  bs: List<&2, Binding>,
  +z: Nat
) -> {
  Parts.at(
    Canon.parts(n, d, all, bs),
    z
  )
    == Bool.pick(
      Maybe<&2, Hashes.Hash>,
      List.is_empty(&2, Binding, Binds.at(bs, d, z)),
      None{},
      Canon.sub(n, d, Binds.at(all, d, z))
    ): Maybe<&2, Hashes.Hash>
}:
  match n bs:
    case m Nil{}:
      {==}
    case 0n Con{+b, +r}:
      +x = Key.nibble(Binding.key(b), d)
      +v = Canon.node(Binds.at(all, d, x), [])
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Parts.at(Parts.put(Canon.parts(0n, d, all, r), x, v), z),
        Bool.pick(
          Maybe<&2, Hashes.Hash>,
          Nat.is_eq(z, x),
          v,
          Parts.at(Canon.parts(0n, d, all, r), z)
        ),
        Parts.at_put_pick(Canon.parts(0n, d, all, r), z, x, v)
      ): {
        _
          == Bool.pick(
            Maybe<&2, Hashes.Hash>,
            List.is_empty(&2, Binding, Binds.at(b <> r, d, z)),
            None{},
            Canon.sub(0n, d, Binds.at(all, d, z))
          ): Maybe<&2, Hashes.Hash>
      }
      Canon.at_parts.at(
        Nat.is_eq(z, x),
        b,
        Binds.at(r, d, z),
        v,
        Parts.at(Canon.parts(0n, d, all, r), z),
        Canon.sub(0n, d, Binds.at(all, d, z)),
        e =>
          %Equal.sym(Nat, z, x, Shared.Nat.is_eq_sound(z, x)(e)): {v == Canon.node(Binds.at(all, d, _), []): Maybe<&2, Hashes.Hash>}
          {==},
        Canon.at_parts(0n, d, all, r, z))
    case 1n+(+m) Con{+b, +r}:
      +x = Key.nibble(Binding.key(b), d)
      +v = Canon.sub(1n+m, d, Binds.at(all, d, x))
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Parts.at(Parts.put(Canon.parts(1n+m, d, all, r), x, v), z),
        Bool.pick(
          Maybe<&2, Hashes.Hash>,
          Nat.is_eq(z, x),
          v,
          Parts.at(Canon.parts(1n+m, d, all, r), z)
        ),
        Parts.at_put_pick(Canon.parts(1n+m, d, all, r), z, x, v)
      ): {
        _
          == Bool.pick(
            Maybe<&2, Hashes.Hash>,
            List.is_empty(&2, Binding, Binds.at(b <> r, d, z)),
            None{},
            Canon.sub(1n+m, d, Binds.at(all, d, z))
          ): Maybe<&2, Hashes.Hash>
      }
      Canon.at_parts.at(
        Nat.is_eq(z, x),
        b,
        Binds.at(r, d, z),
        v,
        Parts.at(Canon.parts(1n+m, d, all, r), z),
        Canon.sub(1n+m, d, Binds.at(all, d, z)),
        e =>
          %Equal.sym(Nat, z, x, Shared.Nat.is_eq_sound(z, x)(e)): {v == Canon.sub(1n+m, d, Binds.at(all, d, _)): Maybe<&2, Hashes.Hash>}
          {==},
        Canon.at_parts(1n+m, d, all, r, z))

# the canonical root of the bindings e, or none when there are none
def Canon.pick_sub(
  n: Nat,
  d: Nat,
  e: List<&2, Binding>
) -> {
  Bool.pick(
    Maybe<&2, Hashes.Hash>,
    List.is_empty(&2, Binding, e),
    None{},
    Canon.sub(n, d, e)
  )
    == Canon.sub(n, d, e): Maybe<&2, Hashes.Hash>
}:
  match n e:
    case 0n Nil{}:
      {==}
    case 1n+m Nil{}:
      {==}
    case m Con{b, r}:
      {==}

# the part z of the canonical parts of the bindings all is the canonical root
# of those under z
def Canon.at_parts_all(
  +n: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  +z: Nat
) -> {
  Parts.at(
    Canon.parts(n, d, all, all),
    z
  )
    == Canon.sub(n, d, Binds.at(all, d, z)): Maybe<&2, Hashes.Hash>
}:
  Equal.trans(
    Maybe<&2, Hashes.Hash>,
    Parts.at(Canon.parts(n, d, all, all), z),
    Bool.pick(
      Maybe<&2, Hashes.Hash>,
      List.is_empty(&2, Binding, Binds.at(all, d, z)),
      None{},
      Canon.sub(n, d, Binds.at(all, d, z))
    ),
    Canon.sub(n, d, Binds.at(all, d, z)),
    Canon.at_parts(n, d, all, all, z),
    Canon.pick_sub(n, d, Binds.at(all, d, z))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of a premise of a proof; a proof does not run
# the nibble at depth d of the key k is the first of its path from there
def Key.nibble_of(
  k: List<&2, U32>,
  d: Nat,
  a: Nat,
  r: List<&2, Nat>
) -> {a <> r == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>} -> {Key.nibble(k, d) == a: Nat}:
  e =>
    %e: {Shared.List.head_or(Nat, _, 0n) == a: Nat}
    {==}

# the path of the key k from depth d, after its first nibble, is its path from
# the next depth
def Key.drop_next(
  k: List<&2, U32>,
  d: Nat,
  a: Nat,
  r: List<&2, Nat>
) -> {
  a <> r == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>
} -> {r == List.drop(&2, Nat, Tree.path(k), 1n+d): List<&2, Nat>}:
  e => Equal.sym(
    List<&2, Nat>,
    List.drop(&2, Nat, Tree.path(k), 1n+d),
    r,
    Shared.List.drop_step(
      &2,
      Nat,
      Tree.path(k),
      d,
      a,
      r
    )(Equal.sym(List<&2, Nat>, a <> r, List.drop(&2, Nat, Tree.path(k), d), e))
  )

# two bindings under the nibble a both
def Binds.at_same(
  b1: Binding,
  b2: Binding,
  d: Nat,
  +a: Nat
) -> {
  Key.nibble(Binding.key(b1), d) == a: Nat
} -> {
  Key.nibble(Binding.key(b2), d) == a: Nat
} -> {Binds.at([b1, b2], d, a) == [b1, b2]: List<&2, Binding>}:
  e1 => e2 =>
    %Equal.sym(Nat, Key.nibble(Binding.key(b1), d), a, e1):
      {
        Binds.keep(
          Nat.is_eq(a, _),
          b1,
          Binds.keep(Nat.is_eq(a, Key.nibble(Binding.key(b2), d)), b2, [])
        )
          == [b1, b2]: List<&2, Binding>
      }
    %Equal.sym(Nat, Key.nibble(Binding.key(b2), d), a, e2):
      {
        Binds.keep(
          Nat.is_eq(a, a),
          b1,
          Binds.keep(Nat.is_eq(a, _), b2, [])
        )
          == [b1, b2]: List<&2, Binding>
      }
    %Equal.sym(Bool, Nat.is_eq(a, a), True{}, Shared.Nat.is_eq_refl(a)):
      {Binds.keep(_, b1, Binds.keep(Nat.is_eq(a, a), b2, [])) == [b1, b2]: List<&2, Binding>}
    %Equal.sym(Bool, Nat.is_eq(a, a), True{}, Shared.Nat.is_eq_refl(a)):
      {b1 <> Binds.keep(_, b2, []) == [b1, b2]: List<&2, Binding>}
    {==}

# of two bindings under the nibbles a and b, another, the first is under a
def Binds.at_first(
  b1: Binding,
  b2: Binding,
  d: Nat,
  a: Nat,
  b: Nat
) -> {
  Key.nibble(Binding.key(b1), d) == a: Nat
} -> {
  Key.nibble(Binding.key(b2), d) == b: Nat
} -> {Nat.is_eq(a, b) == False{}: Bool} -> {Binds.at([b1, b2], d, a) == [b1]: List<&2, Binding>}:
  e1 => e2 => ne =>
    %Equal.sym(Nat, Key.nibble(Binding.key(b1), d), a, e1):
      {
        Binds.keep(
          Nat.is_eq(a, _),
          b1,
          Binds.keep(Nat.is_eq(a, Key.nibble(Binding.key(b2), d)), b2, [])
        )
          == [b1]: List<&2, Binding>
      }
    %Equal.sym(Nat, Key.nibble(Binding.key(b2), d), b, e2):
      {
        Binds.keep(
          Nat.is_eq(a, a),
          b1,
          Binds.keep(Nat.is_eq(a, _), b2, [])
        )
          == [b1]: List<&2, Binding>
      }
    %Equal.sym(Bool, Nat.is_eq(a, a), True{}, Shared.Nat.is_eq_refl(a)):
      {Binds.keep(_, b1, Binds.keep(Nat.is_eq(a, b), b2, [])) == [b1]: List<&2, Binding>}
    %Equal.sym(Bool, Nat.is_eq(a, b), False{}, ne):
      {b1 <> Binds.keep(_, b2, []) == [b1]: List<&2, Binding>}
    {==}

# of two bindings under the nibbles a and b, another, the second is under b
def Binds.at_second(
  b1: Binding,
  b2: Binding,
  d: Nat,
  a: Nat,
  b: Nat
) -> {
  Key.nibble(Binding.key(b1), d) == a: Nat
} -> {
  Key.nibble(Binding.key(b2), d) == b: Nat
} -> {Nat.is_eq(b, a) == False{}: Bool} -> {Binds.at([b1, b2], d, b) == [b2]: List<&2, Binding>}:
  e1 => e2 => ne =>
    %Equal.sym(Nat, Key.nibble(Binding.key(b1), d), a, e1):
      {
        Binds.keep(
          Nat.is_eq(b, _),
          b1,
          Binds.keep(Nat.is_eq(b, Key.nibble(Binding.key(b2), d)), b2, [])
        )
          == [b2]: List<&2, Binding>
      }
    %Equal.sym(Nat, Key.nibble(Binding.key(b2), d), b, e2):
      {
        Binds.keep(
          Nat.is_eq(b, a),
          b1,
          Binds.keep(Nat.is_eq(b, _), b2, [])
        )
          == [b2]: List<&2, Binding>
      }
    %Equal.sym(Bool, Nat.is_eq(b, a), False{}, ne):
      {Binds.keep(_, b1, Binds.keep(Nat.is_eq(b, b), b2, [])) == [b2]: List<&2, Binding>}
    %Equal.sym(Bool, Nat.is_eq(b, b), True{}, Shared.Nat.is_eq_refl(b)):
      {Binds.keep(_, b2, []) == [b2]: List<&2, Binding>}
    {==}

# the canonical parts of two bindings under the nibbles x1 and x2
def Canon.two(
  +m: Nat,
  +d: Nat,
  +l: List<&2, Binding>,
  +x1: Nat,
  +x2: Nat
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  Parts.put(
    Parts.put([], x2, Canon.sub(1n+m, d, Binds.at(l, d, x2))),
    x1,
    Canon.sub(1n+m, d, Binds.at(l, d, x1))
  )

# the canonical parts of two bindings under one nibble a: the part a only
def Canon.two_same(
  +m: Nat,
  +d: Nat,
  +b1: Binding,
  +b2: Binding,
  +a: Nat
) -> {
  Key.nibble(Binding.key(b1), d) == a: Nat
} -> {
  Key.nibble(Binding.key(b2), d) == a: Nat
} -> {
  Canon.parts(
    1n+m,
    d,
    [b1, b2],
    [b1, b2]
  )
    == Parts.put([], a, Canon.root(m, 1n+d, [b1, b2])): List<&2, Maybe<&2, Hashes.Hash>>
}:
  +e1 => +e2 =>
    %Equal.sym(Nat, Key.nibble(Binding.key(b1), d), a, e1):
      {
        Canon.two(
          m,
          d,
          [b1, b2],
          _,
          Key.nibble(Binding.key(b2), d)
        )
          == Parts.put([], a, Canon.root(m, 1n+d, [b1, b2])): List<&2, Maybe<&2, Hashes.Hash>>
      }
    %Equal.sym(Nat, Key.nibble(Binding.key(b2), d), a, e2):
      {
        Canon.two(
          m,
          d,
          [b1, b2],
          a,
          _
        )
          == Parts.put([], a, Canon.root(m, 1n+d, [b1, b2])): List<&2, Maybe<&2, Hashes.Hash>>
      }
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Parts.put(
        Parts.put([], a, Canon.sub(1n+m, d, Binds.at([b1, b2], d, a))),
        a,
        Canon.sub(1n+m, d, Binds.at([b1, b2], d, a))
      ),
      Parts.put([], a, Canon.sub(1n+m, d, Binds.at([b1, b2], d, a))),
      Parts.put_twice(
        [],
        a,
        Canon.sub(1n+m, d, Binds.at([b1, b2], d, a)),
        Canon.sub(1n+m, d, Binds.at([b1, b2], d, a))
      )
    ):
      {_ == Parts.put([], a, Canon.root(m, 1n+d, [b1, b2])): List<&2, Maybe<&2, Hashes.Hash>>}
    %Equal.sym(
      List<&2, Binding>,
      Binds.at([b1, b2], d, a),
      [b1, b2],
      Binds.at_same(b1, b2, d, a)(e1)(e2)
    ):
      {
        Parts.put(
          [],
          a,
          Canon.sub(1n+m, d, _)
        )
          == Parts.put([], a, Canon.root(m, 1n+d, [b1, b2])): List<&2, Maybe<&2, Hashes.Hash>>
      }
    {==}

# the canonical parts of two bindings under the nibbles a and b, another: the
# leaf of each at its nibble
def Canon.two_other(
  m: Nat,
  +d: Nat,
  +b1: Binding,
  +b2: Binding,
  +a: Nat,
  +b: Nat
) -> {
  Key.nibble(Binding.key(b1), d) == a: Nat
} -> {
  Key.nibble(Binding.key(b2), d) == b: Nat
} -> {
  Nat.is_eq(a, b) == False{}: Bool
} -> {
  Canon.parts(
    1n+m,
    d,
    [b1, b2],
    [b1, b2]
  )
    == Parts.put(
      Parts.put([], a, Some{Node.hash(Binding.node(b1))}),
      b,
      Some{Node.hash(Binding.node(b2))}
    ): List<&2, Maybe<&2, Hashes.Hash>>
}:
  +e1 => +e2 => +ne =>
    +nb = Equal.trans(
      Bool,
      Nat.is_eq(b, a),
      Nat.is_eq(a, b),
      False{},
      Shared.Nat.is_eq_comm(b, a),
      ne
    )
    +goal = Parts.put(
      Parts.put([], a, Some{Node.hash(Binding.node(b1))}),
      b,
      Some{Node.hash(Binding.node(b2))}
    )
    %Equal.sym(Nat, Key.nibble(Binding.key(b1), d), a, e1):
      {
        Canon.two(
          m,
          d,
          [b1, b2],
          _,
          Key.nibble(Binding.key(b2), d)
        )
          == goal: List<&2, Maybe<&2, Hashes.Hash>>
      }
    %Equal.sym(Nat, Key.nibble(Binding.key(b2), d), b, e2):
      {Canon.two(m, d, [b1, b2], a, _) == goal: List<&2, Maybe<&2, Hashes.Hash>>}
    %Equal.sym(
      List<&2, Binding>,
      Binds.at([b1, b2], d, b),
      [b2],
      Binds.at_second(b1, b2, d, a, b)(e1)(e2)(nb)
    ):
      {
        Parts.put(
          Parts.put([], b, Canon.sub(1n+m, d, _)),
          a,
          Canon.sub(1n+m, d, Binds.at([b1, b2], d, a))
        )
          == goal: List<&2, Maybe<&2, Hashes.Hash>>
      }
    %Equal.sym(
      List<&2, Binding>,
      Binds.at([b1, b2], d, a),
      [b1],
      Binds.at_first(b1, b2, d, a, b)(e1)(e2)(ne)
    ):
      {
        Parts.put(
          Parts.put([], b, Canon.sub(1n+m, d, [b2])),
          a,
          Canon.sub(1n+m, d, _)
        )
          == goal: List<&2, Maybe<&2, Hashes.Hash>>
      }
    Parts.put_comm(
      [],
      b,
      a,
      Some{Node.hash(Binding.node(b2))},
      Some{Node.hash(Binding.node(b1))}
    )(nb)

# the root of a branch whose part a is the new subtree that m gives, when m
# gives one whose root is w
def Canon.into(
  m: Maybe<&2, Put>,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  t: Put,
  w: Maybe<&2, Hashes.Hash>,
  ih: @t2: Put -> {
    m == Some{t2}: Maybe<&2, Put>
  } -> {Some{Put.root(t2)} == w: Maybe<&2, Hashes.Hash>}
) -> {
  Maybe.bind(&2, Put, Put, m, p => Some{Put.into(ks, a, p)}) == Some{t}: Maybe<&2, Put>
} -> {
  Some{Put.root(t)} == Some{Node.hash(Node.Branch{Parts.put(ks, a, w)})}: Maybe<&2, Hashes.Hash>
}:
  match m:
    case None{}:
      h => Empty.absurd(
        {
          Some{
            Put.root(t)
          }
            == Some{Node.hash(Node.Branch{Parts.put(ks, a, w)})}: Maybe<&2, Hashes.Hash>
        },
        Shared.Maybe.none_ne_some(Put, t, h)
      )
    case Some{t2}:
      h =>
        %Shared.Maybe.some_inj(Put, Put.into(ks, a, t2), t, h):
          {
            Some{
              Put.root(_)
            }
              == Some{Node.hash(Node.Branch{Parts.put(ks, a, w)})}: Maybe<&2, Hashes.Hash>
          }
        %ih(
          t2
        )(
          {==}
        ): {
          Some{
            Put.root(Put.into(ks, a, t2))
          }
            == Some{Node.hash(Node.Branch{Parts.put(ks, a, _)})}: Maybe<&2, Hashes.Hash>
        }
        {==}

# a split of two leaves under the nibbles a and b of their paths, when c tells
# whether a is b: the canonical root of the two
def Canon.split.at(
  c: Bool,
  +a: Nat,
  b: Nat,
  +r1: List<&2, Nat>,
  r2: List<&2, Nat>,
  +d: Nat,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  ns: List<&2, List<&2, U32>>,
  t: Put,
  ec: {Nat.is_eq(a, b) == c: Bool},
  e1: {Key.nibble(k1, d) == a: Nat},
  e2: {Key.nibble(k2, d) == b: Nat},
  ih: @t2: Put -> {
    Tree.split(
      r1,
      r2,
      Put{Node.hash(Node.Leaf{k1, v1}), ns},
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Some{
      Put.root(t2)
    }
      == Canon.root(
        List.length(&2, Nat, r1),
        1n+d,
        [Binding{k1, v1}, Binding{k2, v2}]
      ): Maybe<&2, Hashes.Hash>
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(r1, r2, Put{Node.hash(Node.Leaf{k1, v1}), ns}, Some{Node.hash(Node.Leaf{k2, v2})}),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{
          Parts.put(
            Parts.put(Parts.none(), a, Some{Node.hash(Node.Leaf{k1, v1})}),
            b,
            Some{Node.hash(Node.Leaf{k2, v2})}
          )
        },
        ns
      )
    }
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Some{
    Put.root(t)
  }
    == Canon.root(
      1n+List.length(&2, Nat, r1),
      d,
      [Binding{k1, v1}, Binding{k2, v2}]
    ): Maybe<&2, Hashes.Hash>
}:
  match c:
    case True{}:
      h =>
        +l = {[Binding{k1, v1}, Binding{k2, v2}]: List<&2, Binding>}
        +m = List.length(&2, Nat, r1)
        +ba = Shared.Nat.is_eq_sound(a, b)(ec)
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Canon.parts(1n+m, d, l, l),
          Parts.put([], a, Canon.root(m, 1n+d, l)),
          Canon.two_same(
            m,
            d,
            Binding{k1, v1},
            Binding{k2, v2},
            a
          )(e1)(Equal.trans(Nat, Key.nibble(k2, d), b, a, e2, Equal.sym(Nat, a, b, ba)))
        ): {Some{Put.root(t)} == Some{Node.hash(Node.Branch{_})}: Maybe<&2, Hashes.Hash>}
        Canon.into(
          Tree.split(
            r1,
            r2,
            Put{Node.hash(Node.Leaf{k1, v1}), ns},
            Some{Node.hash(Node.Leaf{k2, v2})}
          ),
          [],
          a,
          t,
          Canon.root(m, 1n+d, l),
          ih
        )(h)
    case False{}:
      h =>
        +l = {[Binding{k1, v1}, Binding{k2, v2}]: List<&2, Binding>}
        +m = List.length(&2, Nat, r1)
        %Equal.sym(
          List<&2, Maybe<&2, Hashes.Hash>>,
          Canon.parts(1n+m, d, l, l),
          Parts.put(
            Parts.put([], a, Some{Node.hash(Node.Leaf{k1, v1})}),
            b,
            Some{Node.hash(Node.Leaf{k2, v2})}
          ),
          Canon.two_other(m, d, Binding{k1, v1}, Binding{k2, v2}, a, b)(e1)(e2)(ec)
        ): {Some{Put.root(t)} == Some{Node.hash(Node.Branch{_})}: Maybe<&2, Hashes.Hash>}
        %Shared.Maybe.some_inj(
          Put,
          Put.node(
            Node.Branch{
              Parts.put(
                Parts.put([], a, Some{Node.hash(Node.Leaf{k1, v1})}),
                b,
                Some{Node.hash(Node.Leaf{k2, v2})}
              )
            },
            ns
          ),
          t,
          h
        ): {
          Some{
            Put.root(_)
          }
            == Some{
              Node.hash(
                Node.Branch{
                  Parts.put(
                    Parts.put([], a, Some{Node.hash(Node.Leaf{k1, v1})}),
                    b,
                    Some{Node.hash(Node.Leaf{k2, v2})}
                  )
                }
              )
            }: Maybe<&2, Hashes.Hash>
        }
        {==}

# a split of a new leaf and a leaf already there, whose paths from depth d are
# p1 and p2, gives the canonical root of the two
def Canon.split(
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +d: Nat,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  +ns: List<&2, List<&2, U32>>,
  t: Put
) -> {
  p1 == List.drop(&2, Nat, Tree.path(k1), d): List<&2, Nat>
} -> {
  p2 == List.drop(&2, Nat, Tree.path(k2), d): List<&2, Nat>
} -> {
  Tree.split(
    p1,
    p2,
    Put{Node.hash(Node.Leaf{k1, v1}), ns},
    Some{Node.hash(Node.Leaf{k2, v2})}
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Some{
    Put.root(t)
  }
    == Canon.root(
      List.length(&2, Nat, p1),
      d,
      [Binding{k1, v1}, Binding{k2, v2}]
    ): Maybe<&2, Hashes.Hash>
}:
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      +h1 => +h2 => hs => Canon.split.at(
        Nat.is_eq(a, b),
        a,
        b,
        r1,
        r2,
        d,
        k1,
        v1,
        k2,
        v2,
        ns,
        t,
        {==},
        Key.nibble_of(k1, d, a, r1)(h1),
        Key.nibble_of(k2, d, b, r2)(h2),
        t2 => Canon.split(
          r1,
          r2,
          1n+d,
          k1,
          v1,
          k2,
          v2,
          ns,
          t2
        )(Key.drop_next(k1, d, a, r1)(h1))(Key.drop_next(k2, d, b, r2)(h2))
      )(hs)
    case Nil{} q:
      h1 => h2 => hs => Empty.absurd(
        {
          Some{
            Put.root(t)
          }
            == Canon.root(0n, d, [Binding{k1, v1}, Binding{k2, v2}]): Maybe<&2, Hashes.Hash>
        },
        Shared.Maybe.none_ne_some(Put, t, hs)
      )
    case Con{a, r1} Nil{}:
      h1 => h2 => hs => Empty.absurd(
        {
          Some{
            Put.root(t)
          }
            == Canon.root(
              1n+List.length(&2, Nat, r1),
              d,
              [Binding{k1, v1}, Binding{k2, v2}]
            ): Maybe<&2, Hashes.Hash>
        },
        Shared.Maybe.none_ne_some(Put, t, hs)
      )

# a list that is empty is no list
def List.empty_nil(
  e: List<&2, Binding>
) -> {List.is_empty(&2, Binding, e) == True{}: Bool} -> {e == []: List<&2, Binding>}:
  match e:
    case Nil{}:
      h => {==}
    case Con{b, r}:
      h => Empty.absurd({b <> r == []: List<&2, Binding>}, Shared.Bool.false_ne_true(h))

# the store holds the canonical tree under the nibble z, when the binding b,
# kept when c (it is under z) before the bindings r, is under z
def Canon.holds_at.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Bool,
  +s: S,
  +m: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  +b: Binding,
  r: List<&2, Binding>,
  z: Nat,
  ec: {Nat.is_eq(z, Key.nibble(Binding.key(b), d)) == c: Bool},
  ih: {
    List.is_empty(&2, Binding, Binds.at(r, d, z)) == False{}: Bool
  } -> {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool}
) -> {
  Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, b <> r) == True{}: Bool
} -> {
  List.is_empty(&2, Binding, Binds.keep(c, b, Binds.at(r, d, z))) == False{}: Bool
} -> {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool}:
  match c:
    case True{}:
      h => he =>
        %Equal.sym(
          Nat,
          z,
          Key.nibble(Binding.key(b), d),
          Shared.Nat.is_eq_sound(z, Key.nibble(Binding.key(b), d))(ec)
        ):
          {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, _)) == True{}: Bool}
        Shared.List.all.if_hit(
          Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, Key.nibble(Binding.key(b), d))),
          u => Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, r)
        )(h)
    case False{}:
      h => he => ih(he)

# the store holds the canonical tree under a nibble z that a binding of l is
# under, when it holds the trees under the nibbles of l
def Canon.holds_at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +m: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  l: List<&2, Binding>,
  +z: Nat
) -> {
  Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, l) == True{}: Bool
} -> {
  List.is_empty(&2, Binding, Binds.at(l, d, z)) == False{}: Bool
} -> {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool}:
  match l:
    case Nil{}:
      h => he => Empty.absurd(
        {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, he))
      )
    case Con{+b, +r}:
      +h => Canon.holds_at.at(
        ~S,
        ~fetch,
        Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
        s,
        m,
        d,
        all,
        b,
        r,
        z,
        {==},
        Canon.holds_at(
          ~S,
          ~fetch,
          s,
          m,
          d,
          all,
          r,
          z
        )(
          Shared.List.all.if_rest(
            Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, Key.nibble(Binding.key(b), d))),
            u => Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, r)
          )(h)
        )
      )(h)

# the store holds the canonical tree under the nibble z, whether its bindings
# are empty (c) or not
def Canon.holds_all.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Bool,
  s: S,
  m: Nat,
  d: Nat,
  +all: List<&2, Binding>,
  z: Nat,
  ec: {List.is_empty(&2, Binding, Binds.at(all, d, z)) == c: Bool}
) -> {
  Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, all) == True{}: Bool
} -> {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool}:
  match c:
    case True{}:
      h =>
        %Equal.sym(
          List<&2, Binding>,
          Binds.at(all, d, z),
          [],
          List.empty_nil(Binds.at(all, d, z))(ec)
        ):
          {Canon.holds(~S, ~fetch, s, m, 1n+d, _) == True{}: Bool}
        {==}
    case False{}:
      h => Canon.holds_at(~S, ~fetch, s, m, d, all, all, z)(h)(ec)

# the store holds the canonical tree under each nibble z of a branch whose
# canonical subtrees it holds
def Canon.holds_all(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  m: Nat,
  +d: Nat,
  +all: List<&2, Binding>,
  +z: Nat
) -> {
  Canon.holds.parts(~S, ~fetch, s, 1n+m, d, all, all) == True{}: Bool
} -> {Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at(all, d, z)) == True{}: Bool}:
  Canon.holds_all.at(
    ~S,
    ~fetch,
    List.is_empty(&2, Binding, Binds.at(all, d, z)),
    s,
    m,
    d,
    all,
    z,
    {==}
  )

# the canonical root of a binding before others is a branch
def Canon.root_many(
  n: Nat,
  d: Nat,
  b: Binding,
  x: List<&2, Binding>
) -> {
  List.is_empty(&2, Binding, x) == False{}: Bool
} -> {
  Canon.root(
    n,
    d,
    b <> x
  )
    == Some{Node.hash(Node.Branch{Canon.parts(n, d, b <> x, b <> x)})}: Maybe<&2, Hashes.Hash>
}:
  match x:
    case Nil{}:
      e => Empty.absurd(
        {
          Canon.root(
            n,
            d,
            [b]
          )
            == Some{Node.hash(Node.Branch{Canon.parts(n, d, [b], [b])})}: Maybe<&2, Hashes.Hash>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Con{c, r}:
      e => {==}

# a put of the part x, under which the key k is, at the end of the canonical
# parts of bs, for the bindings of l, is the same for the bindings bs with k
# bound (when c1 tells whether the binding b is under x, and c2 whether its
# key is not k)
def Canon.parts_put.at(
  ca: Bool,
  cd: Bool,
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +x: Nat,
  +y: Maybe<&2, Hashes.Hash>,
  +b: Binding,
  +r: List<&2, Binding>,
  +ea: {Nat.is_eq(x, Key.nibble(Binding.key(b), d)) == ca: Bool},
  ed: {Key.other(Binding.key(b), k) == cd: Bool},
  +hx: {Key.nibble(k, d) == x: Nat},
  ih: {
    Parts.put(
      Canon.parts(1n+m, d, bs, r),
      x,
      y
    )
      == Parts.put(
        Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(r, k)),
        x,
        y
      ): List<&2, Maybe<&2, Hashes.Hash>>
  }
) -> {
  Parts.put(
    Parts.put(
      Canon.parts(1n+m, d, bs, r),
      Key.nibble(Binding.key(b), d),
      Canon.sub(1n+m, d, Binds.at(bs, d, Key.nibble(Binding.key(b), d)))
    ),
    x,
    y
  )
    == Parts.put(
      Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.keep(cd, b, Binds.drop(r, k))),
      x,
      y
    ): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match ca cd:
    case True{} True{}:
      +nb = Key.nibble(Binding.key(b), d)
      q = Canon.parts(1n+m, d, bs, r)
      q2 = Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(r, k))
      vb = Canon.sub(1n+m, d, Binds.at(bs, d, nb))
      vb2 = Canon.sub(1n+m, d, Binds.at(Binds.put(bs, k, v), d, nb))
      +xn = Shared.Nat.is_eq_sound(x, nb)(ea)
      %xn: {
        Parts.put(
          Parts.put(q, _, vb),
          x,
          y
        )
          == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(Parts.put(q, x, vb), x, y),
        Parts.put(q, x, y),
        Parts.put_twice(q, x, vb, y)
      ):
        {_ == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>}
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(q, x, y),
        Parts.put(q2, x, y),
        ih
      ): {_ == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>}
      %xn: {
        Parts.put(
          q2,
          x,
          y
        )
          == Parts.put(Parts.put(q2, _, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(Parts.put(q2, x, vb2), x, y),
        Parts.put(q2, x, y),
        Parts.put_twice(q2, x, vb2, y)
      ):
        {Parts.put(q2, x, y) == _: List<&2, Maybe<&2, Hashes.Hash>>}
      {==}
    case True{} False{}:
      +nb = Key.nibble(Binding.key(b), d)
      q = Canon.parts(1n+m, d, bs, r)
      q2 = Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(r, k))
      vb = Canon.sub(1n+m, d, Binds.at(bs, d, nb))
      vb2 = Canon.sub(1n+m, d, Binds.at(Binds.put(bs, k, v), d, nb))
      xn = Shared.Nat.is_eq_sound(x, nb)(ea)
      %xn: {
        Parts.put(
          Parts.put(q, _, vb),
          x,
          y
        )
          == Parts.put(q2, x, y): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(Parts.put(q, x, vb), x, y),
        Parts.put(q, x, y),
        Parts.put_twice(q, x, vb, y)
      ):
        {_ == Parts.put(q2, x, y): List<&2, Maybe<&2, Hashes.Hash>>}
      ih
    case False{} True{}:
      +nb = Key.nibble(Binding.key(b), d)
      q = Canon.parts(1n+m, d, bs, r)
      q2 = Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(r, k))
      +vb = Canon.sub(1n+m, d, Binds.at(bs, d, nb))
      vb2 = Canon.sub(1n+m, d, Binds.at(Binds.put(bs, k, v), d, nb))
      +nx = Equal.trans(
        Bool,
        Nat.is_eq(nb, x),
        Nat.is_eq(x, nb),
        False{},
        Shared.Nat.is_eq_comm(nb, x),
        ea
      )
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(Parts.put(q, nb, vb), x, y),
        Parts.put(Parts.put(q, x, y), nb, vb),
        Parts.put_comm(q, nb, x, vb, y)(nx)
      ):
        {_ == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>}
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(q, x, y),
        Parts.put(q2, x, y),
        ih
      ): {
        Parts.put(
          _,
          nb,
          vb
        )
          == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Parts.put(Parts.put(q2, x, y), nb, vb),
        Parts.put(Parts.put(q2, nb, vb), x, y),
        Parts.put_comm(q2, x, nb, y, vb)(ea)
      ):
        {_ == Parts.put(Parts.put(q2, nb, vb2), x, y): List<&2, Maybe<&2, Hashes.Hash>>}
      %Equal.sym(
        Nat,
        Key.nibble(k, d),
        x,
        hx
      ): {
        Parts.put(
          Parts.put(q2, nb, vb),
          x,
          y
        )
          == Parts.put(
            Parts.put(
              q2,
              nb,
              Canon.sub(
                1n+m,
                d,
                Binds.keep(Nat.is_eq(nb, _), Binding{k, v}, Binds.at(Binds.drop(bs, k), d, nb))
              )
            ),
            x,
            y
          ): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        Bool,
        Nat.is_eq(nb, x),
        False{},
        nx
      ): {
        Parts.put(
          Parts.put(q2, nb, vb),
          x,
          y
        )
          == Parts.put(
            Parts.put(
              q2,
              nb,
              Canon.sub(1n+m, d, Binds.keep(_, Binding{k, v}, Binds.at(Binds.drop(bs, k), d, nb)))
            ),
            x,
            y
          ): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        List<&2, Binding>,
        Binds.at(Binds.drop(bs, k), d, nb),
        Binds.at(bs, d, nb),
        Binds.at_drop_other(
          bs,
          d,
          nb,
          k
        )(
          Equal.trans(
            Bool,
            Nat.is_eq(nb, Key.nibble(k, d)),
            Nat.is_eq(nb, x),
            False{},
            Equal.cong(Nat, Bool, w => Nat.is_eq(nb, w), Key.nibble(k, d), x, hx),
            nx
          )
        )
      ): {
        Parts.put(
          Parts.put(q2, nb, vb),
          x,
          y
        )
          == Parts.put(
            Parts.put(q2, nb, Canon.sub(1n+m, d, _)),
            x,
            y
          ): List<&2, Maybe<&2, Hashes.Hash>>
      }
      {==}
    case False{} False{}:
      +nb = Key.nibble(Binding.key(b), d)
      q = Canon.parts(1n+m, d, bs, r)
      q2 = Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(r, k))
      vb = Canon.sub(1n+m, d, Binds.at(bs, d, nb))
      vb2 = Canon.sub(1n+m, d, Binds.at(Binds.put(bs, k, v), d, nb))
      bx = Equal.trans(
        Nat,
        nb,
        Key.nibble(k, d),
        x,
        Equal.cong(
          List<&2, U32>,
          Nat,
          w => Key.nibble(w, d),
          Binding.key(b),
          k,
          Key.same(Binding.key(b), k)(ed)
        ),
        hx
      )
      Empty.absurd(
        {
          Parts.put(
            Parts.put(q, nb, vb),
            x,
            y
          )
            == Parts.put(q2, x, y): List<&2, Maybe<&2, Hashes.Hash>>
        },
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_eq(x, nb),
            True{},
            Equal.sym(Bool, Nat.is_eq(x, nb), False{}, ea),
            Equal.trans(
              Bool,
              Nat.is_eq(x, nb),
              Nat.is_eq(x, x),
              True{},
              Equal.cong(Nat, Bool, w => Nat.is_eq(x, w), nb, x, bx),
              Shared.Nat.is_eq_refl(x)
            )
          )
        )
      )

# a put of the part x, under which the key k is, at the end of the canonical
# parts of bs, for the bindings of l, is the same for the bindings bs with k
# bound, for the bindings of l other than k
def Canon.parts_put(
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +x: Nat,
  +y: Maybe<&2, Hashes.Hash>,
  l: List<&2, Binding>
) -> {
  Key.nibble(k, d) == x: Nat
} -> {
  Parts.put(
    Canon.parts(1n+m, d, bs, l),
    x,
    y
  )
    == Parts.put(
      Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.drop(l, k)),
      x,
      y
    ): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match l:
    case Nil{}:
      hx => {==}
    case Con{+b, +r}:
      +hx => Canon.parts_put.at(
        Nat.is_eq(x, Key.nibble(Binding.key(b), d)),
        Key.other(Binding.key(b), k),
        m,
        d,
        bs,
        k,
        v,
        x,
        y,
        b,
        r,
        {==},
        {==},
        hx,
        Canon.parts_put(m, d, bs, k, v, x, y, r)(hx)
      )

# the canonical parts of the bindings bs with the binding b last, put at the
# nibble z
def Canon.last(
  m: Nat,
  +d: Nat,
  bs: List<&2, Binding>,
  q: List<&2, Maybe<&2, Hashes.Hash>>,
  +z: Nat
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  Parts.put(q, z, Canon.sub(1n+m, d, Binds.at(bs, d, z)))

# the bindings of bs with the key k bound, under the nibble x of k, are those
# of bs under x with k bound
def Binds.at_put(
  bs: List<&2, Binding>,
  d: Nat,
  +x: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Key.nibble(k, d) == x: Nat
} -> {
  Binds.at(Binds.put(bs, k, v), d, x) == Binds.put(Binds.at(bs, d, x), k, v): List<&2, Binding>
}:
  hx =>
    %Equal.sym(
      Nat,
      Key.nibble(k, d),
      x,
      hx
    ): {
      Binds.keep(
        Nat.is_eq(x, _),
        Binding{k, v},
        Binds.at(Binds.drop(bs, k), d, x)
      )
        == Binds.put(Binds.at(bs, d, x), k, v): List<&2, Binding>
    }
    %Equal.sym(
      Bool,
      Nat.is_eq(x, x),
      True{},
      Shared.Nat.is_eq_refl(x)
    ): {
      Binds.keep(
        _,
        Binding{k, v},
        Binds.at(Binds.drop(bs, k), d, x)
      )
        == Binds.put(Binds.at(bs, d, x), k, v): List<&2, Binding>
    }
    %Equal.sym(
      List<&2, Binding>,
      Binds.at(Binds.drop(bs, k), d, x),
      Binds.drop(Binds.at(bs, d, x), k),
      Binds.at_drop(bs, d, x, k)
    ): {Binding{k, v} <> _ == Binds.put(Binds.at(bs, d, x), k, v): List<&2, Binding>}
    {==}

# the canonical parts of the bindings bs with the key k bound: those of bs,
# with the part x of k put to the root of the bindings under x with k bound
def Canon.parts_of_put(
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +x: Nat
) -> {
  Key.nibble(k, d) == x: Nat
} -> {
  Canon.parts(
    1n+m,
    d,
    Binds.put(bs, k, v),
    Binds.put(bs, k, v)
  )
    == Parts.put(
      Canon.parts(1n+m, d, bs, bs),
      x,
      Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
    ): List<&2, Maybe<&2, Hashes.Hash>>
}:
  +hx =>
    +b2 = Binds.put(bs, k, v)
    +q2 = Canon.parts(1n+m, d, b2, Binds.drop(bs, k))
    +w = Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
    %Equal.sym(
      Nat,
      Key.nibble(k, d),
      x,
      hx
    ): {
      Canon.last(
        m,
        d,
        b2,
        q2,
        _
      )
        == Parts.put(Canon.parts(1n+m, d, bs, bs), x, w): List<&2, Maybe<&2, Hashes.Hash>>
    }
    %Equal.sym(
      List<&2, Binding>,
      Binds.at(b2, d, x),
      Binds.put(Binds.at(bs, d, x), k, v),
      Binds.at_put(bs, d, x, k, v)(hx)
    ): {
      Parts.put(
        q2,
        x,
        Canon.sub(1n+m, d, _)
      )
        == Parts.put(Canon.parts(1n+m, d, bs, bs), x, w): List<&2, Maybe<&2, Hashes.Hash>>
    }
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Parts.put(Canon.parts(1n+m, d, bs, bs), x, w),
      Parts.put(q2, x, w),
      Canon.parts_put(m, d, bs, k, v, x, w, bs)(hx)
    ): {Parts.put(q2, x, w) == _: List<&2, Maybe<&2, Hashes.Hash>>}
    {==}

# the canonical root of distinct bindings bs, two or more, with the key k
# bound, under whose nibble x the bindings with k bound have their root
def Canon.root_put(
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +x: Nat
) -> {
  Key.nibble(k, d) == x: Nat
} -> {
  List.is_empty(&2, Binding, Binds.drop(bs, k)) == False{}: Bool
} -> {
  Canon.root(
    1n+m,
    d,
    Binds.put(bs, k, v)
  )
    == Some{
      Node.hash(
        Node.Branch{
          Parts.put(
            Canon.parts(1n+m, d, bs, bs),
            x,
            Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
          )
        }
      )
    }: Maybe<&2, Hashes.Hash>
}:
  hx => hne =>
    +b2 = Binds.put(bs, k, v)
    +goal = {
      Some{
        Node.hash(
          Node.Branch{
            Parts.put(
              Canon.parts(1n+m, d, bs, bs),
              x,
              Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
            )
          }
        )
      }: Maybe<&2, Hashes.Hash>
    }
    %Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Canon.root(1n+m, d, b2),
      Some{Node.hash(Node.Branch{Canon.parts(1n+m, d, b2, b2)})},
      Canon.root_many(1n+m, d, Binding{k, v}, Binds.drop(bs, k))(hne)
    ):
      {_ == goal: Maybe<&2, Hashes.Hash>}
    %Equal.sym(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Canon.parts(1n+m, d, b2, b2),
      Parts.put(
        Canon.parts(1n+m, d, bs, bs),
        x,
        Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
      ),
      Canon.parts_of_put(m, d, bs, k, v, x)(hx)
    ):
      {Some{Node.hash(Node.Branch{_})} == goal: Maybe<&2, Hashes.Hash>}
    {==}

# a step of a write down a branch of the parts ks, at its part x, whose root
# is kid
def Canon.step(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  r: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  x: Nat,
  +kid: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Put>:
  Maybe.bind(
    &2,
    Put,
    Put,
    Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
    p2 => Some{Put.into(ks, x, p2)}
  )

# a new leaf: its root
def Canon.set_root.empty(
  t: Put,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Some{Put.node(Node.Leaf{k, v}, [])} == Some{t}: Maybe<&2, Put>
} -> {Some{Put.root(t)} == Some{Node.hash(Node.Leaf{k, v})}: Maybe<&2, Hashes.Hash>}:
  h =>
    %Shared.Maybe.some_inj(
      Put,
      Put.node(Node.Leaf{k, v}, []),
      t,
      h
    ): {Some{Put.root(_)} == Some{Node.hash(Node.Leaf{k, v})}: Maybe<&2, Hashes.Hash>}
    {==}

# a write of the key k at the leaf of the key k2, when c tells whether k2 is k
def Canon.set_root.leaf(
  c: Bool,
  q: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +k2: List<&2, U32>,
  v2: List<&2, U32>,
  t: Put,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k) == c: Bool},
  hq: {q == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>}
) -> {
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Some{Put.node(Node.Leaf{k, v}, [])},
    w => Tree.split(
      q,
      List.drop(&2, Nat, Tree.path(k2), d),
      Put.node(Node.Leaf{k, v}, []),
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Some{
    Put.root(t)
  }
    == Canon.root(
      List.length(&2, Nat, q),
      d,
      Binding{k, v} <> Binds.keep(Bool.not(c), Binding{k2, v2}, [])
    ): Maybe<&2, Hashes.Hash>
}:
  match c:
    case True{}:
      hs => Canon.set_root.empty(t, k, v)(hs)
    case False{}:
      hs => Canon.split(
        q,
        List.drop(&2, Nat, Tree.path(k2), d),
        d,
        k,
        v,
        k2,
        v2,
        [Node.words(Node.Leaf{k, v})],
        t
      )(hq)({==})(hs)

# a write down a branch, two or more distinct bindings, at the part x of its
# path, gives the canonical root of the bindings with the new one, when the
# write below gives that of the bindings under x
def Canon.set_root.branch(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +x: Nat,
  +r: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +bs: List<&2, Binding>,
  t: Put,
  hx: {Key.nibble(k, d) == x: Nat},
  hne: {List.is_empty(&2, Binding, Binds.drop(bs, k)) == False{}: Bool},
  ih: @t2: Put -> {
    Tree.set.go(
      ~S,
      ~fetch,
      s,
      r,
      1n+d,
      k,
      v,
      Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)),
      Tree.part(~S, ~fetch, s, Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)))
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Some{
      Put.root(t2)
    }
      == Canon.root(
        List.length(&2, Nat, r),
        1n+d,
        Binds.put(Binds.at(bs, d, x), k, v)
      ): Maybe<&2, Hashes.Hash>
  }
) -> {
  Canon.step(
    ~S,
    ~fetch,
    s,
    r,
    d,
    k,
    v,
    Canon.parts(1n+List.length(&2, Nat, r), d, bs, bs),
    x,
    Parts.at(Canon.parts(1n+List.length(&2, Nat, r), d, bs, bs), x)
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Some{
    Put.root(t)
  }
    == Canon.root(1n+List.length(&2, Nat, r), d, Binds.put(bs, k, v)): Maybe<&2, Hashes.Hash>
}:
  +m = List.length(&2, Nat, r)
  ps = Canon.parts(1n+m, d, bs, bs)
  w = Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))
  +kid = Canon.root(m, 1n+d, Binds.at(bs, d, x))
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(ps, x),
    kid,
    Canon.at_parts_all(1n+m, d, bs, x)
  ): {
    Canon.step(~S, ~fetch, s, r, d, k, v, ps, x, _) == Some{t}: Maybe<&2, Put>
  } -> {Some{Put.root(t)} == Canon.root(1n+m, d, Binds.put(bs, k, v)): Maybe<&2, Hashes.Hash>}
  hs => Equal.trans(
    Maybe<&2, Hashes.Hash>,
    Some{Put.root(t)},
    Some{Node.hash(Node.Branch{Parts.put(ps, x, w)})},
    Canon.root(1n+m, d, Binds.put(bs, k, v)),
    Canon.into(
      Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
      ps,
      x,
      t,
      w,
      ih
    )(hs),
    Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Canon.root(1n+m, d, Binds.put(bs, k, v)),
      Some{Node.hash(Node.Branch{Parts.put(ps, x, w)})},
      Canon.root_put(m, d, bs, k, v, x)(hx)(hne)
    )
  )

# a write of the key k into the canonical tree of distinct bindings bs, at
# depth d, whose path from there is p, in a store that holds that tree, gives
# the canonical root of bs with k bound
def Canon.set_root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  p: List<&2, Nat>,
  +s: S,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  bs: List<&2, Binding>,
  t: Put
) -> {
  p == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>
} -> {
  Binds.distinct(bs) == True{}: Bool
} -> {
  Canon.holds(~S, ~fetch, s, List.length(&2, Nat, p), d, bs) == True{}: Bool
} -> {
  Tree.set.go(
    ~S,
    ~fetch,
    s,
    p,
    d,
    k,
    v,
    Canon.root(List.length(&2, Nat, p), d, bs),
    Tree.part(~S, ~fetch, s, Canon.root(List.length(&2, Nat, p), d, bs))
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Some{
    Put.root(t)
  }
    == Canon.root(List.length(&2, Nat, p), d, Binds.put(bs, k, v)): Maybe<&2, Hashes.Hash>
}:
  match p bs:
    case Nil{} Nil{}:
      hp => hd => hh => hs => Canon.set_root.empty(t, k, v)(hs)
    case Con{+x, +r} Nil{}:
      hp => hd => hh => hs => Canon.set_root.empty(t, k, v)(hs)
    case Nil{} Con{Binding{+k2, +v2}, Nil{}}:
      hp => hd => hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, Node.hash(Node.Leaf{k2, v2})),
          Some{Node.Leaf{k2, v2}},
          Tree.has_node(~S, ~fetch, s, Node.Leaf{k2, v2}, {==}, hh)
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Nil{},
            d,
            k,
            v,
            Some{Node.hash(Node.Leaf{k2, v2})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Some{
            Put.root(t)
          }
            == Canon.root(0n, d, Binds.put([Binding{k2, v2}], k, v)): Maybe<&2, Hashes.Hash>
        }
        hs => Canon.set_root.leaf(
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          Nil{},
          d,
          k,
          v,
          k2,
          v2,
          t,
          {==},
          hp
        )(hs)
    case Con{x, r} Con{Binding{+k2, +v2}, Nil{}}:
      hp => hd => hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, Node.hash(Node.Leaf{k2, v2})),
          Some{Node.Leaf{k2, v2}},
          Tree.has_node(~S, ~fetch, s, Node.Leaf{k2, v2}, {==}, hh)
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Con{x, r},
            d,
            k,
            v,
            Some{Node.hash(Node.Leaf{k2, v2})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Some{
            Put.root(t)
          }
            == Canon.root(
              1n+List.length(&2, Nat, r),
              d,
              Binds.put([Binding{k2, v2}], k, v)
            ): Maybe<&2, Hashes.Hash>
        }
        hs => Canon.set_root.leaf(
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          Con{x, r},
          d,
          k,
          v,
          k2,
          v2,
          t,
          {==},
          hp
        )(hs)
    case Nil{} Con{b1, Con{+b2, +rest}}:
      hp => hd => hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(
            ~S,
            ~fetch,
            s,
            Node.hash(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})
          ),
          Some{Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)}},
          Tree.has_node(
            ~S,
            ~fetch,
            s,
            Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)},
            Canon.parts_ok(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest),
            Shared.List.all.if_hit(
              Stores.Store.has(
                ~S,
                ~fetch,
                s,
                Node.words(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})
              ),
              u => Canon.holds.parts(~S, ~fetch, s, 0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            )(hh)
          )
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Nil{},
            d,
            k,
            v,
            Some{Node.hash(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Some{
            Put.root(t)
          }
            == Canon.root(0n, d, Binds.put(b1 <> b2 <> rest, k, v)): Maybe<&2, Hashes.Hash>
        }
        hs => Empty.absurd(
          {
            Some{
              Put.root(t)
            }
              == Canon.root(0n, d, Binds.put(b1 <> b2 <> rest, k, v)): Maybe<&2, Hashes.Hash>
          },
          Shared.Maybe.none_ne_some(Put, t, hs)
        )
    case Con{x, r} Con{b1, Con{+b2, +rest}}:
      +hp => +hd => +hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(
            ~S,
            ~fetch,
            s,
            Node.hash(
              Node.Branch{
                Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
              }
            )
          ),
          Some{
            Node.Branch{
              Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            }
          },
          Tree.has_node(
            ~S,
            ~fetch,
            s,
            Node.Branch{
              Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            },
            Canon.parts_ok(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest),
            Shared.List.all.if_hit(
              Stores.Store.has(
                ~S,
                ~fetch,
                s,
                Node.words(
                  Node.Branch{
                    Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
                  }
                )
              ),
              u => Canon.holds.parts(
                ~S,
                ~fetch,
                s,
                1n+List.length(&2, Nat, r),
                d,
                b1 <> b2 <> rest,
                b1 <> b2 <> rest
              )
            )(hh)
          )
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Con{x, r},
            d,
            k,
            v,
            Some{
              Node.hash(
                Node.Branch{
                  Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
                }
              )
            },
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Some{
            Put.root(t)
          }
            == Canon.root(
              1n+List.length(&2, Nat, r),
              d,
              Binds.put(b1 <> b2 <> rest, k, v)
            ): Maybe<&2, Hashes.Hash>
        }
        hs => Canon.set_root.branch(
          ~S,
          ~fetch,
          s,
          x,
          r,
          d,
          k,
          v,
          b1 <> b2 <> rest,
          t,
          Key.nibble_of(k, d, x, r)(hp),
          Binds.drop_many(b1, b2, rest, k)(hd),
          t2 => Canon.set_root(
            ~S,
            ~fetch,
            r,
            s,
            1n+d,
            k,
            v,
            Binds.at(b1 <> b2 <> rest, d, x),
            t2
          )(
            Key.drop_next(k, d, x, r)(hp)
          )(
            Binds.distinct_at(b1 <> b2 <> rest, d, x)(hd)
          )(
            Canon.holds_all(
              ~S,
              ~fetch,
              s,
              List.length(&2, Nat, r),
              d,
              b1 <> b2 <> rest,
              x
            )(
              Shared.List.all.if_rest(
                Stores.Store.has(
                  ~S,
                  ~fetch,
                  s,
                  Node.words(
                    Node.Branch{
                      Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
                    }
                  )
                ),
                u => Canon.holds.parts(
                  ~S,
                  ~fetch,
                  s,
                  1n+List.length(&2, Nat, r),
                  d,
                  b1 <> b2 <> rest,
                  b1 <> b2 <> rest
                )
              )(hh)
            )
          )
        )(hs)

# a store that grows from a holds the words that a holds
def Tree.has_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +a: S,
  b: S,
  +ws: List<&2, U32>,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Stores.Store.has(~S, ~fetch, a, ws) == True{}: Bool
} -> {Stores.Store.has(~S, ~fetch, b, ws) == True{}: Bool}:
  h =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      fetch(b)(Hashes.Sha.hash(ws)),
      Some{ws},
      kept(
        a
      )(
        b
      )(
        Hashes.Sha.hash(ws)
      )(
        ws
      )(
        gr
      )(
        Shared.Maybe.is_eq_sound(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
          fetch(a)(Hashes.Sha.hash(ws)),
          Some{ws}
        )(h)
      )
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        _,
        Some{ws}
      )
        == True{}: Bool
    }
    Shared.Maybe.is_eq_refl(
      ~List<&2, U32>,
      ~Shared.List.is_eq(~U32, ~U32.is_eq),
      ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
      Some{ws}
    )

# a store that grows from a holds the canonical node of bs that a holds, when
# it holds what is below it
def Canon.holds.node_grows(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +a: S,
  +b: S,
  bs: List<&2, Binding>,
  +ps: List<&2, Maybe<&2, Hashes.Hash>>,
  +ba: Bool,
  bb: Bool,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Canon.holds.node(~S, ~fetch, a, bs, ps, ba) == True{}: Bool
} -> (
  {ba == True{}: Bool} -> {bb == True{}: Bool}
) -> {Canon.holds.node(~S, ~fetch, b, bs, ps, bb) == True{}: Bool}:
  match bs:
    case Nil{}:
      h => hb => {==}
    case Con{c, Nil{}}:
      h => hb => Tree.has_kept(~S, ~fetch, ~grows, ~kept, a, b, Node.words(Binding.node(c)), gr)(h)
    case Con{c, Con{c2, r}}:
      +h => hb => Shared.List.all.if_both(
        Stores.Store.has(~S, ~fetch, b, Node.words(Node.Branch{ps})),
        u => bb
      )(
        Tree.has_kept(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          a,
          b,
          Node.words(Node.Branch{ps}),
          gr
        )(
          Shared.List.all.if_hit(
            Stores.Store.has(~S, ~fetch, a, Node.words(Node.Branch{ps})),
            u => ba
          )(h)
        )
      )(
        hb(
          Shared.List.all.if_rest(
            Stores.Store.has(~S, ~fetch, a, Node.words(Node.Branch{ps})),
            u => ba
          )(h)
        )
      )

# a store that grows from a holds the canonical subtrees that a holds
def Canon.holds_grows(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  n: Nat,
  l: List<&2, Binding>,
  +a: S,
  +b: S,
  +d: Nat,
  +all: List<&2, Binding>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Canon.holds.parts(~S, ~fetch, a, n, d, all, l) == True{}: Bool
} -> {Canon.holds.parts(~S, ~fetch, b, n, d, all, l) == True{}: Bool}:
  match n l:
    case m Nil{}:
      h => {==}
    case 0n Con{c, r}:
      h => {==}
    case 1n+(+m) Con{c, +r}:
      +h =>
        +sub = Binds.at(all, d, Key.nibble(Binding.key(c), d))
        Shared.List.all.if_both(
          Canon.holds(~S, ~fetch, b, m, 1n+d, sub),
          u => Canon.holds.parts(~S, ~fetch, b, 1n+m, d, all, r)
        )(
          Canon.holds.node_grows(
            ~S,
            ~fetch,
            ~grows,
            ~kept,
            a,
            b,
            sub,
            Canon.parts(m, 1n+d, sub, sub),
            Canon.holds.parts(~S, ~fetch, a, m, 1n+d, sub, sub),
            Canon.holds.parts(~S, ~fetch, b, m, 1n+d, sub, sub),
            gr
          )(
            Shared.List.all.if_hit(
              Canon.holds(~S, ~fetch, a, m, 1n+d, sub),
              u => Canon.holds.parts(~S, ~fetch, a, 1n+m, d, all, r)
            )(h)
          )(hb => Canon.holds_grows(~S, ~fetch, ~grows, ~kept, m, sub, a, b, 1n+d, sub, gr)(hb))
        )(
          Canon.holds_grows(
            ~S,
            ~fetch,
            ~grows,
            ~kept,
            1n+m,
            r,
            a,
            b,
            d,
            all,
            gr
          )(
            Shared.List.all.if_rest(
              Canon.holds(~S, ~fetch, a, m, 1n+d, sub),
              u => Canon.holds.parts(~S, ~fetch, a, 1n+m, d, all, r)
            )(h)
          )
        )

# a store that grows from a holds the canonical trees that a holds
def Canon.holds_grows.root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +n: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +a: S,
  +b: S,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Canon.holds(~S, ~fetch, a, n, d, bs) == True{}: Bool
} -> {Canon.holds(~S, ~fetch, b, n, d, bs) == True{}: Bool}:
  h => Canon.holds.node_grows(
    ~S,
    ~fetch,
    ~grows,
    ~kept,
    a,
    b,
    bs,
    Canon.parts(n, d, bs, bs),
    Canon.holds.parts(~S, ~fetch, a, n, d, bs, bs),
    Canon.holds.parts(~S, ~fetch, b, n, d, bs, bs),
    gr
  )(h)(hb => Canon.holds_grows(~S, ~fetch, ~grows, ~kept, n, bs, a, b, d, bs, gr)(hb))

# a store holds the canonical subtrees of two bindings when it holds the
# canonical tree under the nibble of each
def Canon.holds_pair(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +m: Nat,
  +d: Nat,
  +b1: Binding,
  +b2: Binding
) -> {
  Canon.holds(
    ~S,
    ~fetch,
    s,
    m,
    1n+d,
    Binds.at([b1, b2], d, Key.nibble(Binding.key(b1), d))
  )
    == True{}: Bool
} -> {
  Canon.holds(
    ~S,
    ~fetch,
    s,
    m,
    1n+d,
    Binds.at([b1, b2], d, Key.nibble(Binding.key(b2), d))
  )
    == True{}: Bool
} -> {Canon.holds.parts(~S, ~fetch, s, 1n+m, d, [b1, b2], [b1, b2]) == True{}: Bool}:
  h1 => h2 => Shared.List.all.if_both(
    Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at([b1, b2], d, Key.nibble(Binding.key(b1), d))),
    u => Canon.holds.parts(~S, ~fetch, s, 1n+m, d, [b1, b2], [b2])
  )(
    h1
  )(
    Shared.List.all.if_both(
      Canon.holds(~S, ~fetch, s, m, 1n+d, Binds.at([b1, b2], d, Key.nibble(Binding.key(b2), d))),
      u => Canon.holds.parts(~S, ~fetch, s, 1n+m, d, [b1, b2], [])
    )(h2)({==})
  )

# a store holds the canonical tree of a binding before others when it holds its
# branch and the canonical subtrees
def Canon.holds_make(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +n: Nat,
  +d: Nat,
  +b: Binding,
  x: List<&2, Binding>
) -> {
  List.is_empty(&2, Binding, x) == False{}: Bool
} -> {
  Stores.Store.has(
    ~S,
    ~fetch,
    s,
    Node.words(Node.Branch{Canon.parts(n, d, b <> x, b <> x)})
  )
    == True{}: Bool
} -> {
  Canon.holds.parts(~S, ~fetch, s, n, d, b <> x, b <> x) == True{}: Bool
} -> {Canon.holds(~S, ~fetch, s, n, d, b <> x) == True{}: Bool}:
  match x:
    case Nil{}:
      e => h1 => h2 => Empty.absurd(
        {Canon.holds(~S, ~fetch, s, n, d, [b]) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Con{+c, +r}:
      e => h1 => h2 => Shared.List.all.if_both(
        Stores.Store.has(
          ~S,
          ~fetch,
          s,
          Node.words(Node.Branch{Canon.parts(n, d, b <> c <> r, b <> c <> r)})
        ),
        u => Canon.holds.parts(~S, ~fetch, s, n, d, b <> c <> r, b <> c <> r)
      )(h1)(h2)

# what a write of the subtree p as the part a of the parts ks gives, when the
# write gives p
def Canon.into_elim(
  mm: Maybe<&2, Put>,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  t: Put,
  -G: Put -> Type,
  k: @t2: Put -> {mm == Some{t2}: Maybe<&2, Put>} -> G(Put.into(ks, a, t2))
) -> {
  Maybe.bind(&2, Put, Put, mm, p => Some{Put.into(ks, a, p)}) == Some{t}: Maybe<&2, Put>
} -> G(t):
  match mm:
    case None{}:
      h => Empty.absurd(G(t), Shared.Maybe.none_ne_some(Put, t, h))
    case Some{t2}:
      h =>
        %Shared.Maybe.some_inj(Put, Put.into(ks, a, t2), t, h): G(_)
        k(t2)({==})

# a store that holds the nodes of a split of two leaves under the nibbles a and
# b of their paths, when c tells whether a is b, holds the canonical tree of
# the two
def Canon.split_holds.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Bool,
  +a: Nat,
  +b: Nat,
  +r1: List<&2, Nat>,
  r2: List<&2, Nat>,
  +d: Nat,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  t: Put,
  +s2: S,
  +ec: {Nat.is_eq(a, b) == c: Bool},
  +e1: {Key.nibble(k1, d) == a: Nat},
  +e2: {Key.nibble(k2, d) == b: Nat},
  ihr: @t2: Put -> {
    Tree.split(
      r1,
      r2,
      Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Some{
      Put.root(t2)
    }
      == Canon.root(
        List.length(&2, Nat, r1),
        1n+d,
        [Binding{k1, v1}, Binding{k2, v2}]
      ): Maybe<&2, Hashes.Hash>
  },
  ihh1: @t2: Put -> {
    Tree.split(
      r1,
      r2,
      Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)) == True{}: Bool
  } -> {
    Canon.holds(
      ~S,
      ~fetch,
      s2,
      List.length(&2, Nat, r1),
      1n+d,
      [Binding{k1, v1}, Binding{k2, v2}]
    )
      == True{}: Bool
  },
  ihh2: @t2: Put -> {
    Tree.split(
      r1,
      r2,
      Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)) == True{}: Bool
  } -> {
    Canon.holds(
      ~S,
      ~fetch,
      s2,
      List.length(&2, Nat, r1),
      1n+d,
      [Binding{k1, v1}, Binding{k2, v2}]
    )
      == True{}: Bool
  },
  hl2: {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k2, v2})) == True{}: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Maybe.bind(
      &2,
      Put,
      Put,
      Tree.split(
        r1,
        r2,
        Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
        Some{Node.hash(Node.Leaf{k2, v2})}
      ),
      p => Some{Put.into(Parts.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.Branch{
          Parts.put(
            Parts.put(Parts.none(), a, Some{Node.hash(Node.Leaf{k1, v1})}),
            b,
            Some{Node.hash(Node.Leaf{k2, v2})}
          )
        },
        [Node.words(Node.Leaf{k1, v1})]
      )
    }
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {
  Canon.holds(
    ~S,
    ~fetch,
    s2,
    1n+List.length(&2, Nat, r1),
    d,
    [Binding{k1, v1}, Binding{k2, v2}]
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      hs =>
        +l = {[Binding{k1, v1}, Binding{k2, v2}]: List<&2, Binding>}
        +m = List.length(&2, Nat, r1)
        +ba = Shared.Nat.is_eq_sound(a, b)(ec)
        +e2a = Equal.trans(Nat, Key.nibble(k2, d), b, a, e2, Equal.sym(Nat, a, b, ba))
        Canon.into_elim(
          Tree.split(
            r1,
            r2,
            Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
            Some{Node.hash(Node.Leaf{k2, v2})}
          ),
          [],
          a,
          t,
          t3 => {
            Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t3)) == True{}: Bool
          } -> {Canon.holds(~S, ~fetch, s2, 1n+m, d, l) == True{}: Bool},
          +t2 => +e => +hn => Canon.holds_make(
            ~S,
            ~fetch,
            s2,
            1n+m,
            d,
            Binding{k1, v1},
            [Binding{k2, v2}]
          )({==})(
            %Equal.sym(List<&2, Maybe<&2, Hashes.Hash>>, Canon.parts(1n+m, d, l, l), Parts.put([], a, Canon.root(m, 1n+d, l)), Canon.two_same(m, d, Binding{k1, v1}, Binding{k2, v2}, a)(e1)(e2a)):
              {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{_})) == True{}: Bool}
            %ihr(t2)(e): {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put([], a, _)})) == True{}: Bool}
            Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put([], a, Some{Put.root(t2)})})), u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)))(hn))(
            Canon.holds_pair(~S, ~fetch, s2, m, d, Binding{k1, v1}, Binding{k2, v2})(
              %Equal.sym(Nat, Key.nibble(k1, d), a, e1): {Canon.holds(~S, ~fetch, s2, m, 1n+d, Binds.at(l, d, _)) == True{}: Bool}
              %Equal.sym(List<&2, Binding>, Binds.at(l, d, a), l, Binds.at_same(Binding{k1, v1}, Binding{k2, v2}, d, a)(e1)(e2a)):
                {Canon.holds(~S, ~fetch, s2, m, 1n+d, _) == True{}: Bool}
              ihh1(t2)(e)(Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put([], a, Some{Put.root(t2)})})), u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)))(hn)))(
              %Equal.sym(Nat, Key.nibble(k2, d), a, e2a): {Canon.holds(~S, ~fetch, s2, m, 1n+d, Binds.at(l, d, _)) == True{}: Bool}
              %Equal.sym(List<&2, Binding>, Binds.at(l, d, a), l, Binds.at_same(Binding{k1, v1}, Binding{k2, v2}, d, a)(e1)(e2a)):
                {Canon.holds(~S, ~fetch, s2, m, 1n+d, _) == True{}: Bool}
              ihh2(t2)(e)(Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put([], a, Some{Put.root(t2)})})), u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)))(hn)))
          )
        )(hs)
    case False{}:
      hs =>
        +l = {[Binding{k1, v1}, Binding{k2, v2}]: List<&2, Binding>}
        +m = List.length(&2, Nat, r1)
        +pp = Parts.put(
          Parts.put([], a, Some{Node.hash(Node.Leaf{k1, v1})}),
          b,
          Some{Node.hash(Node.Leaf{k2, v2})}
        )
        +nb = Equal.trans(
          Bool,
          Nat.is_eq(b, a),
          Nat.is_eq(a, b),
          False{},
          Shared.Nat.is_eq_comm(b, a),
          ec
        )
        %Shared.Maybe.some_inj(
          Put,
          Put.node(Node.Branch{pp}, [Node.words(Node.Leaf{k1, v1})]),
          t,
          hs
        ):
          {
            Stores.Store.holds(~S, ~fetch, s2, Put.nodes(_)) == True{}: Bool
          } -> {Canon.holds(~S, ~fetch, s2, 1n+m, d, l) == True{}: Bool}
        +hn => Canon.holds_make(~S, ~fetch, s2, 1n+m, d, Binding{k1, v1}, [Binding{k2, v2}])({==})(
          %Equal.sym(List<&2, Maybe<&2, Hashes.Hash>>, Canon.parts(1n+m, d, l, l), pp, Canon.two_other(m, d, Binding{k1, v1}, Binding{k2, v2}, a, b)(e1)(e2)(ec)):
            {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{_})) == True{}: Bool}
          Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{pp})), u => Stores.Store.holds(~S, ~fetch, s2, [Node.words(Node.Leaf{k1, v1})]))(hn))(Canon.holds_pair(~S, ~fetch, s2, m, d, Binding{k1, v1}, Binding{k2, v2})(
            %Equal.sym(Nat, Key.nibble(k1, d), a, e1): {Canon.holds(~S, ~fetch, s2, m, 1n+d, Binds.at(l, d, _)) == True{}: Bool}
            %Equal.sym(List<&2, Binding>, Binds.at(l, d, a), [Binding{k1, v1}], Binds.at_first(Binding{k1, v1}, Binding{k2, v2}, d, a, b)(e1)(e2)(ec)):
              {Canon.holds(~S, ~fetch, s2, m, 1n+d, _) == True{}: Bool}
            Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k1, v1})), u => Stores.Store.holds(~S, ~fetch, s2, []))(Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{pp})), u => Stores.Store.holds(~S, ~fetch, s2, [Node.words(Node.Leaf{k1, v1})]))(hn)))(
            %Equal.sym(Nat, Key.nibble(k2, d), b, e2): {Canon.holds(~S, ~fetch, s2, m, 1n+d, Binds.at(l, d, _)) == True{}: Bool}
            %Equal.sym(List<&2, Binding>, Binds.at(l, d, b), [Binding{k2, v2}], Binds.at_second(Binding{k1, v1}, Binding{k2, v2}, d, a, b)(e1)(e2)(nb)):
              {Canon.holds(~S, ~fetch, s2, m, 1n+d, _) == True{}: Bool}
            hl2))

# a store that holds the nodes of a split of a new leaf and a leaf already
# there, and the old leaf, holds the canonical tree of the two
def Canon.split_holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  p1: List<&2, Nat>,
  p2: List<&2, Nat>,
  +d: Nat,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  t: Put,
  +s2: S
) -> {
  p1 == List.drop(&2, Nat, Tree.path(k1), d): List<&2, Nat>
} -> {
  p2 == List.drop(&2, Nat, Tree.path(k2), d): List<&2, Nat>
} -> {
  Tree.split(
    p1,
    p2,
    Put{Node.hash(Node.Leaf{k1, v1}), [Node.words(Node.Leaf{k1, v1})]},
    Some{Node.hash(Node.Leaf{k2, v2})}
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {
  Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k2, v2})) == True{}: Bool
} -> {
  Canon.holds(
    ~S,
    ~fetch,
    s2,
    List.length(&2, Nat, p1),
    d,
    [Binding{k1, v1}, Binding{k2, v2}]
  )
    == True{}: Bool
}:
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      +h1 => +h2 => hs => hn => +hl2 =>
        +n1 = Key.drop_next(k1, d, a, r1)(h1)
        +n2 = Key.drop_next(k2, d, b, r2)(h2)
        Canon.split_holds.at(
          ~S,
          ~fetch,
          Nat.is_eq(a, b),
          a,
          b,
          r1,
          r2,
          d,
          k1,
          v1,
          k2,
          v2,
          t,
          s2,
          {==},
          Key.nibble_of(k1, d, a, r1)(h1),
          Key.nibble_of(k2, d, b, r2)(h2),
          t2 => Canon.split(
            r1,
            r2,
            1n+d,
            k1,
            v1,
            k2,
            v2,
            [Node.words(Node.Leaf{k1, v1})],
            t2
          )(n1)(n2),
          t2 => e => hn2 => Canon.split_holds(
            ~S,
            ~fetch,
            r1,
            r2,
            1n+d,
            k1,
            v1,
            k2,
            v2,
            t2,
            s2
          )(n1)(n2)(e)(hn2)(hl2),
          t2 => e => hn2 => Canon.split_holds(
            ~S,
            ~fetch,
            r1,
            r2,
            1n+d,
            k1,
            v1,
            k2,
            v2,
            t2,
            s2
          )(n1)(n2)(e)(hn2)(hl2),
          hl2
        )(hs)(hn)
    case Nil{} q:
      h1 => h2 => hs => hn => hl2 => Empty.absurd(
        {Canon.holds(~S, ~fetch, s2, 0n, d, [Binding{k1, v1}, Binding{k2, v2}]) == True{}: Bool},
        Shared.Maybe.none_ne_some(Put, t, hs)
      )
    case Con{a, r1} Nil{}:
      h1 => h2 => hs => hn => hl2 => Empty.absurd(
        {
          Canon.holds(
            ~S,
            ~fetch,
            s2,
            1n+List.length(&2, Nat, r1),
            d,
            [Binding{k1, v1}, Binding{k2, v2}]
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(Put, t, hs)
      )

# the bindings of bs with the key k bound, under a nibble z other than that of
# k, are those of bs
def Binds.at_put_other(
  bs: List<&2, Binding>,
  d: Nat,
  z: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  x: Nat
) -> {
  Key.nibble(k, d) == x: Nat
} -> {
  Nat.is_eq(z, x) == False{}: Bool
} -> {Binds.at(Binds.put(bs, k, v), d, z) == Binds.at(bs, d, z): List<&2, Binding>}:
  +hx => +nz =>
    %Equal.sym(
      Nat,
      Key.nibble(k, d),
      x,
      hx
    ): {
      Binds.keep(
        Nat.is_eq(z, _),
        Binding{k, v},
        Binds.at(Binds.drop(bs, k), d, z)
      )
        == Binds.at(bs, d, z): List<&2, Binding>
    }
    %Equal.sym(
      Bool,
      Nat.is_eq(z, x),
      False{},
      nz
    ): {
      Binds.keep(
        _,
        Binding{k, v},
        Binds.at(Binds.drop(bs, k), d, z)
      )
        == Binds.at(bs, d, z): List<&2, Binding>
    }
    Binds.at_drop_other(
      bs,
      d,
      z,
      k
    )(
      Equal.trans(
        Bool,
        Nat.is_eq(z, Key.nibble(k, d)),
        Nat.is_eq(z, x),
        False{},
        Equal.cong(Nat, Bool, w => Nat.is_eq(z, w), Key.nibble(k, d), x, hx),
        nz
      )
    )

# a store b that holds the canonical tree of the bindings under the nibble x
# of k, with k bound, and grows from a store a that holds the canonical
# subtrees of bs, holds the canonical tree under the nibble z of bs with k
# bound, when c tells whether z is x
def Canon.holds_put.one(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  c: Bool,
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +x: Nat,
  +z: Nat,
  +a: S,
  b: S,
  gr: {grows(a, b) == True{}: Bool},
  ec: {Nat.is_eq(z, x) == c: Bool},
  hx: {Key.nibble(k, d) == x: Nat},
  fx: {Canon.holds(~S, ~fetch, b, m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v)) == True{}: Bool},
  fo: {Canon.holds.parts(~S, ~fetch, a, 1n+m, d, bs, bs) == True{}: Bool}
) -> {Canon.holds(~S, ~fetch, b, m, 1n+d, Binds.at(Binds.put(bs, k, v), d, z)) == True{}: Bool}:
  match c:
    case True{}:
      %Equal.sym(
        Nat,
        z,
        x,
        Shared.Nat.is_eq_sound(z, x)(ec)
      ): {Canon.holds(~S, ~fetch, b, m, 1n+d, Binds.at(Binds.put(bs, k, v), d, _)) == True{}: Bool}
      %Equal.sym(
        List<&2, Binding>,
        Binds.at(Binds.put(bs, k, v), d, x),
        Binds.put(Binds.at(bs, d, x), k, v),
        Binds.at_put(bs, d, x, k, v)(hx)
      ):
        {Canon.holds(~S, ~fetch, b, m, 1n+d, _) == True{}: Bool}
      fx
    case False{}:
      %Equal.sym(
        List<&2, Binding>,
        Binds.at(Binds.put(bs, k, v), d, z),
        Binds.at(bs, d, z),
        Binds.at_put_other(bs, d, z, k, v, x)(hx)(ec)
      ):
        {Canon.holds(~S, ~fetch, b, m, 1n+d, _) == True{}: Bool}
      Canon.holds_grows.root(
        ~S,
        ~fetch,
        ~grows,
        ~kept,
        m,
        1n+d,
        Binds.at(bs, d, z),
        a,
        b,
        gr
      )(Canon.holds_all(~S, ~fetch, a, m, d, bs, z)(fo))

# such a store b holds the canonical subtrees of bs with k bound, under the
# nibbles of the bindings l
def Canon.holds_put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  l: List<&2, Binding>,
  +m: Nat,
  +d: Nat,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +x: Nat,
  +a: S,
  +b: S,
  +gr: {grows(a, b) == True{}: Bool},
  +hx: {Key.nibble(k, d) == x: Nat},
  +fx: {Canon.holds(~S, ~fetch, b, m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v)) == True{}: Bool},
  +fo: {Canon.holds.parts(~S, ~fetch, a, 1n+m, d, bs, bs) == True{}: Bool}
) -> {Canon.holds.parts(~S, ~fetch, b, 1n+m, d, Binds.put(bs, k, v), l) == True{}: Bool}:
  match l:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      Shared.List.all.if_both(
        Canon.holds(
          ~S,
          ~fetch,
          b,
          m,
          1n+d,
          Binds.at(Binds.put(bs, k, v), d, Key.nibble(Binding.key(c), d))
        ),
        u => Canon.holds.parts(~S, ~fetch, b, 1n+m, d, Binds.put(bs, k, v), r)
      )(
        Canon.holds_put.one(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          Nat.is_eq(Key.nibble(Binding.key(c), d), x),
          m,
          d,
          bs,
          k,
          v,
          x,
          Key.nibble(Binding.key(c), d),
          a,
          b,
          gr,
          {==},
          hx,
          fx,
          fo
        )
      )(Canon.holds_put(~S, ~fetch, ~grows, ~kept, r, m, d, bs, k, v, x, a, b, gr, hx, fx, fo))

# a store that holds the nodes of a new leaf holds the leaf
def Canon.set_holds.empty(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  t: Put,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Some{Put.node(Node.Leaf{k, v}, [])} == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k, v})) == True{}: Bool}:
  h =>
    %Shared.Maybe.some_inj(Put, Put.node(Node.Leaf{k, v}, []), t, h):
      {
        Stores.Store.holds(~S, ~fetch, s2, Put.nodes(_)) == True{}: Bool
      } -> {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k, v})) == True{}: Bool}
    hn => Shared.List.all.if_hit(
      Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k, v})),
      u => Stores.Store.holds(~S, ~fetch, s2, [])
    )(hn)

# a store that holds the nodes of a write of the key k at the leaf of the key
# k2, when c tells whether k2 is k, and the old leaf, holds the canonical tree
# of the bindings after the write
def Canon.set_holds.leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Bool,
  q: List<&2, Nat>,
  +d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +k2: List<&2, U32>,
  v2: List<&2, U32>,
  t: Put,
  s2: S,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k) == c: Bool},
  hq: {q == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>},
  hl2: {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Leaf{k2, v2})) == True{}: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, Put>,
    c,
    u => Some{Put.node(Node.Leaf{k, v}, [])},
    w => Tree.split(
      q,
      List.drop(&2, Nat, Tree.path(k2), d),
      Put.node(Node.Leaf{k, v}, []),
      Some{Node.hash(Node.Leaf{k2, v2})}
    )
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {
  Canon.holds(
    ~S,
    ~fetch,
    s2,
    List.length(&2, Nat, q),
    d,
    Binding{k, v} <> Binds.keep(Bool.not(c), Binding{k2, v2}, [])
  )
    == True{}: Bool
}:
  match c:
    case True{}:
      Canon.set_holds.empty(~S, ~fetch, s2, t, k, v)
    case False{}:
      hs => hn => Canon.split_holds(
        ~S,
        ~fetch,
        q,
        List.drop(&2, Nat, Tree.path(k2), d),
        d,
        k,
        v,
        k2,
        v2,
        t,
        s2
      )(hq)({==})(hs)(hn)(hl2)

# a store b that grows from a store a and holds the nodes of a write down a
# branch, two or more distinct bindings, at the part x of its path, holds the
# canonical tree of the bindings with the new one, when it holds that of the
# bindings under x with it
def Canon.set_holds.branch(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +s: S,
  +s2: S,
  +x: Nat,
  +r: List<&2, Nat>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +bs: List<&2, Binding>,
  t: Put,
  gr: {grows(s, s2) == True{}: Bool},
  +hx: {Key.nibble(k, d) == x: Nat},
  hne: {List.is_empty(&2, Binding, Binds.drop(bs, k)) == False{}: Bool},
  hold: {Canon.holds.parts(~S, ~fetch, s, 1n+List.length(&2, Nat, r), d, bs, bs) == True{}: Bool},
  ihr: @t2: Put -> {
    Tree.set.go(
      ~S,
      ~fetch,
      s,
      r,
      1n+d,
      k,
      v,
      Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)),
      Tree.part(~S, ~fetch, s, Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)))
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Some{
      Put.root(t2)
    }
      == Canon.root(
        List.length(&2, Nat, r),
        1n+d,
        Binds.put(Binds.at(bs, d, x), k, v)
      ): Maybe<&2, Hashes.Hash>
  },
  ihh: @t2: Put -> {
    Tree.set.go(
      ~S,
      ~fetch,
      s,
      r,
      1n+d,
      k,
      v,
      Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)),
      Tree.part(~S, ~fetch, s, Canon.root(List.length(&2, Nat, r), 1n+d, Binds.at(bs, d, x)))
    )
      == Some{t2}: Maybe<&2, Put>
  } -> {
    Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)) == True{}: Bool
  } -> {
    Canon.holds(
      ~S,
      ~fetch,
      s2,
      List.length(&2, Nat, r),
      1n+d,
      Binds.put(Binds.at(bs, d, x), k, v)
    )
      == True{}: Bool
  }
) -> {
  Canon.step(
    ~S,
    ~fetch,
    s,
    r,
    d,
    k,
    v,
    Canon.parts(1n+List.length(&2, Nat, r), d, bs, bs),
    x,
    Parts.at(Canon.parts(1n+List.length(&2, Nat, r), d, bs, bs), x)
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {
  Canon.holds(~S, ~fetch, s2, 1n+List.length(&2, Nat, r), d, Binds.put(bs, k, v)) == True{}: Bool
}:
  +m = List.length(&2, Nat, r)
  +ps = Canon.parts(1n+m, d, bs, bs)
  +kid = Canon.root(m, 1n+d, Binds.at(bs, d, x))
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Parts.at(ps, x),
    kid,
    Canon.at_parts_all(1n+m, d, bs, x)
  ): {
    Canon.step(~S, ~fetch, s, r, d, k, v, ps, x, _) == Some{t}: Maybe<&2, Put>
  } -> {
    Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
  } -> {Canon.holds(~S, ~fetch, s2, 1n+m, d, Binds.put(bs, k, v)) == True{}: Bool}
  hs => Canon.into_elim(
    Tree.set.go(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.part(~S, ~fetch, s, kid)),
    ps,
    x,
    t,
    t3 => {Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t3)) == True{}: Bool} -> {Canon.holds(~S, ~fetch, s2, 1n+m, d, Binds.put(bs, k, v)) == True{}: Bool},
    +t2 => +e => +hn =>
      +rest = Shared.List.all.if_rest(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put(ps, x, Some{Put.root(t2)})})), u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)))(hn)
      Canon.holds_make(~S, ~fetch, s2, 1n+m, d, Binding{k, v}, Binds.drop(bs, k))(hne)(
    %Equal.sym(List<&2, Maybe<&2, Hashes.Hash>>, Canon.parts(1n+m, d, Binds.put(bs, k, v), Binds.put(bs, k, v)), Parts.put(ps, x, Canon.root(m, 1n+d, Binds.put(Binds.at(bs, d, x), k, v))), Canon.parts_of_put(m, d, bs, k, v, x)(hx)):
      {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{_})) == True{}: Bool}
    %ihr(t2)(e): {Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put(ps, x, _)})) == True{}: Bool}
    Shared.List.all.if_hit(Stores.Store.has(~S, ~fetch, s2, Node.words(Node.Branch{Parts.put(ps, x, Some{Put.root(t2)})})), u => Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t2)))(hn))(Canon.holds_put(~S, ~fetch, ~grows, ~kept, Binds.put(bs, k, v), m, d, bs, k, v, x, s, s2, gr, hx, ihh(t2)(e)(rest), hold)))(hs)

# a store s2 that grows from a store s that holds the canonical tree of
# distinct bindings bs at depth d, whose path from there is p, and holds the
# nodes that a write of the key k there adds, holds the canonical tree of bs
# with k bound
def Canon.set_holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  p: List<&2, Nat>,
  +s: S,
  +s2: S,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  bs: List<&2, Binding>,
  t: Put,
  +gr: {grows(s, s2) == True{}: Bool}
) -> {
  p == List.drop(&2, Nat, Tree.path(k), d): List<&2, Nat>
} -> {
  Binds.distinct(bs) == True{}: Bool
} -> {
  Canon.holds(~S, ~fetch, s, List.length(&2, Nat, p), d, bs) == True{}: Bool
} -> {
  Tree.set.go(
    ~S,
    ~fetch,
    s,
    p,
    d,
    k,
    v,
    Canon.root(List.length(&2, Nat, p), d, bs),
    Tree.part(~S, ~fetch, s, Canon.root(List.length(&2, Nat, p), d, bs))
  )
    == Some{t}: Maybe<&2, Put>
} -> {
  Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
} -> {Canon.holds(~S, ~fetch, s2, List.length(&2, Nat, p), d, Binds.put(bs, k, v)) == True{}: Bool}:
  match p bs:
    case Nil{} Nil{}:
      hp => hd => hh => Canon.set_holds.empty(~S, ~fetch, s2, t, k, v)
    case Con{+x, +r} Nil{}:
      hp => hd => hh => Canon.set_holds.empty(~S, ~fetch, s2, t, k, v)
    case Nil{} Con{Binding{+k2, +v2}, Nil{}}:
      +hp => hd => +hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, Node.hash(Node.Leaf{k2, v2})),
          Some{Node.Leaf{k2, v2}},
          Tree.has_node(~S, ~fetch, s, Node.Leaf{k2, v2}, {==}, hh)
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Nil{},
            d,
            k,
            v,
            Some{Node.hash(Node.Leaf{k2, v2})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
        } -> {
          Canon.holds(~S, ~fetch, s2, 0n, d, Binds.put([Binding{k2, v2}], k, v)) == True{}: Bool
        }
        Canon.set_holds.leaf(
          ~S,
          ~fetch,
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          Nil{},
          d,
          k,
          v,
          k2,
          v2,
          t,
          s2,
          {==},
          hp,
          Tree.has_kept(~S, ~fetch, ~grows, ~kept, s, s2, Node.words(Node.Leaf{k2, v2}), gr)(hh)
        )
    case Con{x, r} Con{Binding{+k2, +v2}, Nil{}}:
      +hp => hd => +hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, Node.hash(Node.Leaf{k2, v2})),
          Some{Node.Leaf{k2, v2}},
          Tree.has_node(~S, ~fetch, s, Node.Leaf{k2, v2}, {==}, hh)
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Con{x, r},
            d,
            k,
            v,
            Some{Node.hash(Node.Leaf{k2, v2})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
        } -> {
          Canon.holds(
            ~S,
            ~fetch,
            s2,
            1n+List.length(&2, Nat, r),
            d,
            Binds.put([Binding{k2, v2}], k, v)
          )
            == True{}: Bool
        }
        Canon.set_holds.leaf(
          ~S,
          ~fetch,
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          Con{x, r},
          d,
          k,
          v,
          k2,
          v2,
          t,
          s2,
          {==},
          hp,
          Tree.has_kept(~S, ~fetch, ~grows, ~kept, s, s2, Node.words(Node.Leaf{k2, v2}), gr)(hh)
        )
    case Nil{} Con{b1, Con{+b2, +rest}}:
      hp => hd => +hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(
            ~S,
            ~fetch,
            s,
            Node.hash(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})
          ),
          Some{Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)}},
          Tree.has_node(
            ~S,
            ~fetch,
            s,
            Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)},
            Canon.parts_ok(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest),
            Shared.List.all.if_hit(
              Stores.Store.has(
                ~S,
                ~fetch,
                s,
                Node.words(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})
              ),
              u => Canon.holds.parts(~S, ~fetch, s, 0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            )(hh)
          )
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Nil{},
            d,
            k,
            v,
            Some{Node.hash(Node.Branch{Canon.parts(0n, d, b1 <> b2 <> rest, b1 <> b2 <> rest)})},
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
        } -> {Canon.holds(~S, ~fetch, s2, 0n, d, Binds.put(b1 <> b2 <> rest, k, v)) == True{}: Bool}
        hs => hn => Empty.absurd(
          {Canon.holds(~S, ~fetch, s2, 0n, d, Binds.put(b1 <> b2 <> rest, k, v)) == True{}: Bool},
          Shared.Maybe.none_ne_some(Put, t, hs)
        )
    case Con{x, r} Con{b1, Con{+b2, +rest}}:
      +hp => +hd => +hh =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(
            ~S,
            ~fetch,
            s,
            Node.hash(
              Node.Branch{
                Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
              }
            )
          ),
          Some{
            Node.Branch{
              Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            }
          },
          Tree.has_node(
            ~S,
            ~fetch,
            s,
            Node.Branch{
              Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
            },
            Canon.parts_ok(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest),
            Shared.List.all.if_hit(
              Stores.Store.has(
                ~S,
                ~fetch,
                s,
                Node.words(
                  Node.Branch{
                    Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
                  }
                )
              ),
              u => Canon.holds.parts(
                ~S,
                ~fetch,
                s,
                1n+List.length(&2, Nat, r),
                d,
                b1 <> b2 <> rest,
                b1 <> b2 <> rest
              )
            )(hh)
          )
        ): {
          Tree.set.go(
            ~S,
            ~fetch,
            s,
            Con{x, r},
            d,
            k,
            v,
            Some{
              Node.hash(
                Node.Branch{
                  Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
                }
              )
            },
            _
          )
            == Some{t}: Maybe<&2, Put>
        } -> {
          Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
        } -> {
          Canon.holds(
            ~S,
            ~fetch,
            s2,
            1n+List.length(&2, Nat, r),
            d,
            Binds.put(b1 <> b2 <> rest, k, v)
          )
            == True{}: Bool
        }
        +hold = Shared.List.all.if_rest(
          Stores.Store.has(
            ~S,
            ~fetch,
            s,
            Node.words(
              Node.Branch{
                Canon.parts(1n+List.length(&2, Nat, r), d, b1 <> b2 <> rest, b1 <> b2 <> rest)
              }
            )
          ),
          u => Canon.holds.parts(
            ~S,
            ~fetch,
            s,
            1n+List.length(&2, Nat, r),
            d,
            b1 <> b2 <> rest,
            b1 <> b2 <> rest
          )
        )(hh)
        +bx = Binds.at(b1 <> b2 <> rest, d, x)
        +np = Key.drop_next(k, d, x, r)(hp)
        +nd = Binds.distinct_at(b1 <> b2 <> rest, d, x)(hd)
        +nh = Canon.holds_all(~S, ~fetch, s, List.length(&2, Nat, r), d, b1 <> b2 <> rest, x)(hold)
        Canon.set_holds.branch(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          s,
          s2,
          x,
          r,
          d,
          k,
          v,
          b1 <> b2 <> rest,
          t,
          gr,
          Key.nibble_of(k, d, x, r)(hp),
          Binds.drop_many(b1, b2, rest, k)(hd),
          hold,
          t2 => Canon.set_root(~S, ~fetch, r, s, 1n+d, k, v, bx, t2)(np)(nd)(nh),
          t2 => e => hn2 => Canon.set_holds(
            ~S,
            ~fetch,
            ~grows,
            ~kept,
            r,
            s,
            s2,
            1n+d,
            k,
            v,
            bx,
            t2,
            gr
          )(np)(nd)(nh)(e)(hn2)
        )

# the canonical parts of the bindings l for the nibbles i and then j
def Canon.pair(
  +n: Nat,
  +d: Nat,
  +l: List<&2, Binding>,
  q: List<&2, Maybe<&2, Hashes.Hash>>,
  +i: Nat,
  +j: Nat
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  Parts.put(
    Parts.put(q, j, Canon.sub(n, d, Binds.at(l, d, j))),
    i,
    Canon.sub(n, d, Binds.at(l, d, i))
  )

# the canonical parts for the nibbles i then j are those for j then i, when c
# tells whether j is i
def Canon.reorder.at(
  c: Bool,
  +n: Nat,
  +d: Nat,
  +l: List<&2, Binding>,
  q: List<&2, Maybe<&2, Hashes.Hash>>,
  +i: Nat,
  +j: Nat,
  ec: {Nat.is_eq(j, i) == c: Bool}
) -> {
  Canon.pair(n, d, l, q, i, j) == Canon.pair(n, d, l, q, j, i): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match c:
    case True{}:
      +e = Shared.Nat.is_eq_sound(j, i)(ec)
      %Equal.sym(
        Nat,
        j,
        i,
        e
      ): {
        Canon.pair(
          n,
          d,
          l,
          q,
          i,
          _
        )
          == Canon.pair(n, d, l, q, j, i): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        Nat,
        j,
        i,
        e
      ): {
        Canon.pair(
          n,
          d,
          l,
          q,
          i,
          i
        )
          == Canon.pair(n, d, l, q, _, i): List<&2, Maybe<&2, Hashes.Hash>>
      }
      {==}
    case False{}:
      Parts.put_comm(
        q,
        j,
        i,
        Canon.sub(n, d, Binds.at(l, d, j)),
        Canon.sub(n, d, Binds.at(l, d, i))
      )(ec)

# the canonical parts of the bindings l for the nibbles of a, b, then x are
# those for b, a, then x
def Canon.reorder(
  n: Nat,
  +d: Nat,
  +l: List<&2, Binding>,
  +a: Binding,
  +b: Binding,
  x: List<&2, Binding>
) -> {
  Canon.parts(
    n,
    d,
    l,
    a <> b <> x
  )
    == Canon.parts(n, d, l, b <> a <> x): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match n:
    case 0n:
      Canon.reorder.at(
        Nat.is_eq(Key.nibble(Binding.key(b), d), Key.nibble(Binding.key(a), d)),
        0n,
        d,
        l,
        Canon.parts(0n, d, l, x),
        Key.nibble(Binding.key(a), d),
        Key.nibble(Binding.key(b), d),
        {==}
      )
    case 1n+(+m):
      Canon.reorder.at(
        Nat.is_eq(Key.nibble(Binding.key(b), d), Key.nibble(Binding.key(a), d)),
        1n+m,
        d,
        l,
        Canon.parts(1n+m, d, l, x),
        Key.nibble(Binding.key(a), d),
        Key.nibble(Binding.key(b), d),
        {==}
      )

# the canonical tree, at the end of a path, of the bindings a and b, each kept
# when ca and cb, before y, is the same in either order
def Canon.swap.leaf(
  ca: Bool,
  cb: Bool,
  a: Binding,
  b: Binding,
  y: List<&2, Binding>,
  ps: List<&2, Maybe<&2, Hashes.Hash>>
) -> {
  Canon.node(
    Binds.keep(ca, a, Binds.keep(cb, b, y)),
    ps
  )
    == Canon.node(Binds.keep(cb, b, Binds.keep(ca, a, y)), ps): Maybe<&2, Hashes.Hash>
}:
  match ca cb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the canonical root of the bindings a and b, each kept when ca and cb, before
# y, is the same in either order, when that of a, b, y and of b, a, y are
def Canon.swap.entry(
  ca: Bool,
  cb: Bool,
  m: Nat,
  d: Nat,
  a: Binding,
  b: Binding,
  y: List<&2, Binding>,
  ih: {
    Canon.parts(
      m,
      1n+d,
      a <> b <> y,
      a <> b <> y
    )
      == Canon.parts(m, 1n+d, b <> a <> y, b <> a <> y): List<&2, Maybe<&2, Hashes.Hash>>
  }
) -> {
  Canon.root(
    m,
    1n+d,
    Binds.keep(ca, a, Binds.keep(cb, b, y))
  )
    == Canon.root(m, 1n+d, Binds.keep(cb, b, Binds.keep(ca, a, y))): Maybe<&2, Hashes.Hash>
}:
  match ca cb:
    case True{} True{}:
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Canon.parts(m, 1n+d, a <> b <> y, a <> b <> y),
        Canon.parts(m, 1n+d, b <> a <> y, b <> a <> y),
        ih
      ): {
        Some{
          Node.hash(Node.Branch{_})
        }
          == Some{
            Node.hash(Node.Branch{Canon.parts(m, 1n+d, b <> a <> y, b <> a <> y)})
          }: Maybe<&2, Hashes.Hash>
      }
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the canonical parts, for the nibbles of the bindings l, of a, b, then x are
# those of b, a, then x
def Canon.swap.go(
  n: Nat,
  l: List<&2, Binding>,
  +d: Nat,
  +a: Binding,
  +b: Binding,
  +x: List<&2, Binding>
) -> {
  Canon.parts(
    n,
    d,
    a <> b <> x,
    l
  )
    == Canon.parts(n, d, b <> a <> x, l): List<&2, Maybe<&2, Hashes.Hash>>
}:
  match n l:
    case m Nil{}:
      {==}
    case 0n Con{c, r}:
      +z = Key.nibble(Binding.key(c), d)
      y = Binds.at(x, d, z)
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Canon.parts(0n, d, a <> b <> x, r),
        Canon.parts(0n, d, b <> a <> x, r),
        Canon.swap.go(0n, r, d, a, b, x)
      ): {
        Parts.put(
          _,
          z,
          Canon.node(Binds.at(a <> b <> x, d, z), [])
        )
          == Canon.parts(0n, d, b <> a <> x, c <> r): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Canon.node(Binds.at(a <> b <> x, d, z), []),
        Canon.node(Binds.at(b <> a <> x, d, z), []),
        Canon.swap.leaf(
          Nat.is_eq(z, Key.nibble(Binding.key(a), d)),
          Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
          a,
          b,
          y,
          []
        )
      ): {
        Parts.put(
          Canon.parts(0n, d, b <> a <> x, r),
          z,
          _
        )
          == Canon.parts(0n, d, b <> a <> x, c <> r): List<&2, Maybe<&2, Hashes.Hash>>
      }
      {==}
    case 1n+(+m) Con{c, r}:
      +z = Key.nibble(Binding.key(c), d)
      +y = Binds.at(x, d, z)
      %Equal.sym(
        List<&2, Maybe<&2, Hashes.Hash>>,
        Canon.parts(1n+m, d, a <> b <> x, r),
        Canon.parts(1n+m, d, b <> a <> x, r),
        Canon.swap.go(1n+m, r, d, a, b, x)
      ): {
        Parts.put(
          _,
          z,
          Canon.sub(1n+m, d, Binds.at(a <> b <> x, d, z))
        )
          == Canon.parts(1n+m, d, b <> a <> x, c <> r): List<&2, Maybe<&2, Hashes.Hash>>
      }
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Canon.sub(1n+m, d, Binds.at(a <> b <> x, d, z)),
        Canon.sub(1n+m, d, Binds.at(b <> a <> x, d, z)),
        Canon.swap.entry(
          Nat.is_eq(z, Key.nibble(Binding.key(a), d)),
          Nat.is_eq(z, Key.nibble(Binding.key(b), d)),
          m,
          d,
          a,
          b,
          y,
          Equal.trans(
            List<&2, Maybe<&2, Hashes.Hash>>,
            Canon.parts(m, 1n+d, a <> b <> y, a <> b <> y),
            Canon.parts(m, 1n+d, b <> a <> y, a <> b <> y),
            Canon.parts(m, 1n+d, b <> a <> y, b <> a <> y),
            Canon.swap.go(m, a <> b <> y, 1n+d, a, b, y),
            Canon.reorder(m, 1n+d, b <> a <> y, a, b, y)
          )
        )
      ): {
        Parts.put(
          Canon.parts(1n+m, d, b <> a <> x, r),
          z,
          _
        )
          == Canon.parts(1n+m, d, b <> a <> x, c <> r): List<&2, Maybe<&2, Hashes.Hash>>
      }
      {==}

# the canonical root of a, b, then x is that of b, a, then x
def Canon.root_swap(
  +n: Nat,
  +d: Nat,
  +a: Binding,
  +b: Binding,
  +x: List<&2, Binding>
) -> {Canon.root(n, d, a <> b <> x) == Canon.root(n, d, b <> a <> x): Maybe<&2, Hashes.Hash>}:
  %Equal.sym(
    List<&2, Maybe<&2, Hashes.Hash>>,
    Canon.parts(n, d, a <> b <> x, a <> b <> x),
    Canon.parts(n, d, b <> a <> x, b <> a <> x),
    Equal.trans(
      List<&2, Maybe<&2, Hashes.Hash>>,
      Canon.parts(n, d, a <> b <> x, a <> b <> x),
      Canon.parts(n, d, b <> a <> x, a <> b <> x),
      Canon.parts(n, d, b <> a <> x, b <> a <> x),
      Canon.swap.go(n, a <> b <> x, d, a, b, x),
      Canon.reorder(n, d, b <> a <> x, a, b, x)
    )
  ): {Some{Node.hash(Node.Branch{_})} == Canon.root(n, d, b <> a <> x): Maybe<&2, Hashes.Hash>}
  {==}

# the key k1 is not k2 exactly when k2 is not k1, when c tells whether k2 is k1
def Key.ne_sym.at(
  c: Bool,
  +k1: List<&2, U32>,
  +k2: List<&2, U32>,
  ec: {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k1) == c: Bool}
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k1) == False{}: Bool}:
  match c:
    case True{}:
      ne => Empty.absurd(
        {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k1) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
            True{},
            Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), False{}, ne),
            Key.eq_of(
              k1,
              k2
            )(
              Equal.sym(
                List<&2, U32>,
                k2,
                k1,
                Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k2, k1)(ec)
              )
            )
          )
        )
      )
    case False{}:
      ne => ec

# the key k1 is not k2 exactly when k2 is not k1
def Key.ne_sym(
  +k1: List<&2, U32>,
  +k2: List<&2, U32>
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, k2, k1) == False{}: Bool}:
  Key.ne_sym.at(Shared.List.is_eq(~U32, ~U32.is_eq, k2, k1), k1, k2, {==})

# a binding put after the binding of another key: both, the new first
def Binds.put_put(
  bs: List<&2, Binding>,
  k1: List<&2, U32>,
  v1: List<&2, U32>,
  k2: List<&2, U32>,
  v2: List<&2, U32>
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool
} -> {
  Binds.put(
    Binds.put(bs, k1, v1),
    k2,
    v2
  )
    == Binding{k2, v2}
    <> Binding{k1, v1}
    <> Binds.drop(Binds.drop(bs, k1), k2): List<&2, Binding>
}:
  ne =>
    %Equal.sym(
      Bool,
      Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
      False{},
      ne
    ): {
      Binding{
        k2,
        v2
      }
        <> Binds.keep(Bool.not(_), Binding{k1, v1}, Binds.drop(Binds.drop(bs, k1), k2))
        == Binding{k2, v2}
        <> Binding{k1, v1}
        <> Binds.drop(Binds.drop(bs, k1), k2): List<&2, Binding>
    }
    {==}

# puts of two other keys give the same canonical root in either order
def Canon.put_comm(
  n: Nat,
  d: Nat,
  +bs: List<&2, Binding>,
  +k1: List<&2, U32>,
  +v1: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool
} -> {
  Canon.root(
    n,
    d,
    Binds.put(Binds.put(bs, k1, v1), k2, v2)
  )
    == Canon.root(n, d, Binds.put(Binds.put(bs, k2, v2), k1, v1)): Maybe<&2, Hashes.Hash>
}:
  +ne =>
    %Equal.sym(
      List<&2, Binding>,
      Binds.put(Binds.put(bs, k1, v1), k2, v2),
      Binding{k2, v2} <> Binding{k1, v1} <> Binds.drop(Binds.drop(bs, k1), k2),
      Binds.put_put(bs, k1, v1, k2, v2)(ne)
    ): {
      Canon.root(
        n,
        d,
        _
      )
        == Canon.root(n, d, Binds.put(Binds.put(bs, k2, v2), k1, v1)): Maybe<&2, Hashes.Hash>
    }
    %Equal.sym(
      List<&2, Binding>,
      Binds.put(Binds.put(bs, k2, v2), k1, v1),
      Binding{k1, v1} <> Binding{k2, v2} <> Binds.drop(Binds.drop(bs, k2), k1),
      Binds.put_put(bs, k2, v2, k1, v1)(Key.ne_sym(k1, k2)(ne))
    ): {
      Canon.root(
        n,
        d,
        Binding{k2, v2} <> Binding{k1, v1} <> Binds.drop(Binds.drop(bs, k1), k2)
      )
        == Canon.root(n, d, _): Maybe<&2, Hashes.Hash>
    }
    %Binds.drop_comm(
      bs,
      k1,
      k2
    ): {
      Canon.root(
        n,
        d,
        Binding{k2, v2} <> Binding{k1, v1} <> Binds.drop(Binds.drop(bs, k1), k2)
      )
        == Canon.root(n, d, Binding{k1, v1} <> Binding{k2, v2} <> _): Maybe<&2, Hashes.Hash>
    }
    Canon.root_swap(n, d, Binding{k2, v2}, Binding{k1, v1}, Binds.drop(Binds.drop(bs, k1), k2))

# a second put of a key replaces the first
def Binds.put_twice(
  bs: List<&2, Binding>,
  +k: List<&2, U32>,
  v1: List<&2, U32>,
  v2: List<&2, U32>
) -> {Binds.put(Binds.put(bs, k, v1), k, v2) == Binds.put(bs, k, v2): List<&2, Binding>}:
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
  ): {
    Binding{
      k,
      v2
    }
      <> Binds.keep(Bool.not(_), Binding{k, v1}, Binds.drop(Binds.drop(bs, k), k))
      == Binds.put(bs, k, v2): List<&2, Binding>
  }
  %Equal.sym(
    List<&2, Binding>,
    Binds.drop(Binds.drop(bs, k), k),
    Binds.drop(bs, k),
    Binds.drop_twice(bs, k)
  ): {Binding{k, v2} <> _ == Binds.put(bs, k, v2): List<&2, Binding>}
  {==}
# Laws of canonical trees
# ------------------------

# Tree.set_canon at n nibbles above the end of a path
def Canon.SetRoot(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  bs: List<&2, Binding>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  t: Put,
  n: Nat
) -> Type:
  {
    Binds.distinct(bs) == True{}: Bool
  } -> {
    Canon.holds(~S, ~fetch, s, n, 0n, bs) == True{}: Bool
  } -> {
    Tree.set.go(
      ~S,
      ~fetch,
      s,
      Tree.path(k),
      0n,
      k,
      v,
      Canon.root(n, 0n, bs),
      Tree.part(~S, ~fetch, s, Canon.root(n, 0n, bs))
    )
      == Some{t}: Maybe<&2, Put>
  } -> {Some{Put.root(t)} == Canon.root(n, 0n, Binds.put(bs, k, v)): Maybe<&2, Hashes.Hash>}

# Tree.set_canon_holds at n nibbles above the end of a path
def Canon.SetHolds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  s2: S,
  bs: List<&2, Binding>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  t: Put,
  n: Nat
) -> Type:
  {
    Binds.distinct(bs) == True{}: Bool
  } -> {
    Canon.holds(~S, ~fetch, s, n, 0n, bs) == True{}: Bool
  } -> {
    Tree.set.go(
      ~S,
      ~fetch,
      s,
      Tree.path(k),
      0n,
      k,
      v,
      Canon.root(n, 0n, bs),
      Tree.part(~S, ~fetch, s, Canon.root(n, 0n, bs))
    )
      == Some{t}: Maybe<&2, Put>
  } -> {
    Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool
  } -> {Canon.holds(~S, ~fetch, s2, n, 0n, Binds.put(bs, k, v)) == True{}: Bool}

# a write of the key k into the tree of distinct bindings bs, in a store that
# holds that tree, gives the tree of bs with k bound: a tree's root is a
# function of its bindings alone, not of the order of its writes
law Tree.set_canon:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +bs: List<&2, Binding>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  for t: Put
  {Binds.distinct(bs) == True{}: Bool}
    -> {Canon.holds.of(~S, ~fetch, s, bs) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k, v) == Some{t}: Maybe<&2, Put>}
    -> {Some{Put.root(t)} == Canon.of(Binds.put(bs, k, v)): Maybe<&2, Hashes.Hash>}

def Tree.set_canon(ty, fetch, s, bs, k, v, t):
  %Nibbles.of_length(Hashes.Sha.hash(k)): Canon.SetRoot(~ty, ~fetch, s, bs, k, v, t, _)
  hd => hh => hs => Canon.set_root(
    ~ty,
    ~fetch,
    Tree.path(k),
    s,
    0n,
    k,
    v,
    bs,
    t
  )(
    Equal.sym(
      List<&2, Nat>,
      List.drop(&2, Nat, Tree.path(k), 0n),
      Tree.path(k),
      Shared.List.drop_zero(&2, Nat, Tree.path(k))
    )
  )(hd)(hh)(hs)

# a store that grows from one holding the tree of distinct bindings bs, and
# holds the nodes that a write of the key k adds, holds the tree of bs with k
# bound: the next write's premise
law Tree.set_canon_holds:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +s: S
  for +s2: S
  for +bs: List<&2, Binding>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  for t: Put
  {grows(s, s2) == True{}: Bool}
    -> {Binds.distinct(bs) == True{}: Bool}
    -> {Canon.holds.of(~S, ~fetch, s, bs) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k, v) == Some{t}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {Canon.holds.of(~S, ~fetch, s2, Binds.put(bs, k, v)) == True{}: Bool}

def Tree.set_canon_holds(ty, fetch, grows, kept, s, s2, bs, k, v, t):
  +gr =>
    %Nibbles.of_length(Hashes.Sha.hash(k)): Canon.SetHolds(~ty, ~fetch, s, s2, bs, k, v, t, _)
    hd => hh => hs => hn => Canon.set_holds(
      ~ty,
      ~fetch,
      ~grows,
      ~kept,
      Tree.path(k),
      s,
      s2,
      0n,
      k,
      v,
      bs,
      t,
      gr
    )(
      Equal.sym(
        List<&2, Nat>,
        List.drop(&2, Nat, Tree.path(k), 0n),
        Tree.path(k),
        Shared.List.drop_zero(&2, Nat, Tree.path(k))
      )
    )(hd)(hh)(hs)(hn)

# writes of two other keys to a tree, in either order, give the same root
law Tree.set_comm:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +s: S
  for +a: S
  for +b: S
  for +bs: List<&2, Binding>
  for +k1: List<&2, U32>
  for +v1: List<&2, U32>
  for +k2: List<&2, U32>
  for +v2: List<&2, U32>
  for +t1: Put
  for +t12: Put
  for +t2: Put
  for +t21: Put
  {Binds.distinct(bs) == True{}: Bool}
    -> {Canon.holds.of(~S, ~fetch, s, bs) == True{}: Bool}
    -> {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool}
    -> {grows(s, a) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k1, v1) == Some{t1}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, a, Put.nodes(t1)) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, a, Some{Put.root(t1)}, k2, v2) == Some{t12}: Maybe<&2, Put>}
    -> {grows(s, b) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k2, v2) == Some{t2}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, b, Put.nodes(t2)) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, b, Some{Put.root(t2)}, k1, v1) == Some{t21}: Maybe<&2, Put>}
    -> {Put.root(t12) == Put.root(t21): Hashes.Hash}

def Tree.set_comm(ty, fetch, grows, kept, s, a, b, bs, k1, v1, k2, v2, t1, t12, t2, t21):
  +hd => +hh => ne => ga => +hs1 => hn1 =>
    +r1 = Tree.set_canon(~ty, ~fetch, s, bs, k1, v1, t1)(hd)(hh)(hs1)
    +ha = Tree.set_canon_holds(
      ~ty,
      ~fetch,
      ~grows,
      ~kept,
      s,
      a,
      bs,
      k1,
      v1,
      t1
    )(ga)(hd)(hh)(hs1)(hn1)
    %Equal.sym(Maybe<&2, Hashes.Hash>, Some{Put.root(t1)}, Canon.of(Binds.put(bs, k1, v1)), r1):
      {Tree.set.plain(~ty, ~fetch, a, _, k2, v2) == Some{t12}: Maybe<&2, Put>}
        -> {grows(s, b) == True{}: Bool}
        -> {Tree.set.plain(~ty, ~fetch, s, Canon.of(bs), k2, v2) == Some{t2}: Maybe<&2, Put>}
        -> {Stores.Store.holds(~ty, ~fetch, b, Put.nodes(t2)) == True{}: Bool}
        -> {Tree.set.plain(~ty, ~fetch, b, Some{Put.root(t2)}, k1, v1) == Some{t21}: Maybe<&2, Put>}
        -> {Put.root(t12) == Put.root(t21): Hashes.Hash}
    hs12 => gb => +hs2 => hn2 =>
      +r2 = Tree.set_canon(~ty, ~fetch, s, bs, k2, v2, t2)(hd)(hh)(hs2)
      +hb = Tree.set_canon_holds(
        ~ty,
        ~fetch,
        ~grows,
        ~kept,
        s,
        b,
        bs,
        k2,
        v2,
        t2
      )(gb)(hd)(hh)(hs2)(hn2)
      %Equal.sym(Maybe<&2, Hashes.Hash>, Some{Put.root(t2)}, Canon.of(Binds.put(bs, k2, v2)), r2):
        {
          Tree.set.plain(~ty, ~fetch, b, _, k1, v1) == Some{t21}: Maybe<&2, Put>
        } -> {Put.root(t12) == Put.root(t21): Hashes.Hash}
      hs21 =>
        +r12 = Tree.set_canon(
          ~ty,
          ~fetch,
          a,
          Binds.put(bs, k1, v1),
          k2,
          v2,
          t12
        )(Binds.distinct_put(bs, k1, v1)(hd))(ha)(hs12)
        +r21 = Tree.set_canon(
          ~ty,
          ~fetch,
          b,
          Binds.put(bs, k2, v2),
          k1,
          v1,
          t21
        )(Binds.distinct_put(bs, k2, v2)(hd))(hb)(hs21)
        Shared.Maybe.some_inj(
          Hashes.Hash,
          Put.root(t12),
          Put.root(t21),
          Equal.trans(
            Maybe<&2, Hashes.Hash>,
            Some{Put.root(t12)},
            Canon.of(Binds.put(Binds.put(bs, k2, v2), k1, v1)),
            Some{Put.root(t21)},
            Equal.trans(
              Maybe<&2, Hashes.Hash>,
              Some{Put.root(t12)},
              Canon.of(Binds.put(Binds.put(bs, k1, v1), k2, v2)),
              Canon.of(Binds.put(Binds.put(bs, k2, v2), k1, v1)),
              r12,
              Canon.put_comm(64n, 0n, bs, k1, v1, k2, v2)(ne)
            ),
            Equal.sym(
              Maybe<&2, Hashes.Hash>,
              Some{Put.root(t21)},
              Canon.of(Binds.put(Binds.put(bs, k2, v2), k1, v1)),
              r21
            )
          )
        )

# a second write of a key replaces the first: its root is that of the second
# write alone
law Tree.set_twice:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +s: S
  for +a: S
  for +bs: List<&2, Binding>
  for +k: List<&2, U32>
  for +v1: List<&2, U32>
  for +v2: List<&2, U32>
  for +t1: Put
  for +t12: Put
  for +t2: Put
  {Binds.distinct(bs) == True{}: Bool}
    -> {Canon.holds.of(~S, ~fetch, s, bs) == True{}: Bool}
    -> {grows(s, a) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k, v1) == Some{t1}: Maybe<&2, Put>}
    -> {Stores.Store.holds(~S, ~fetch, a, Put.nodes(t1)) == True{}: Bool}
    -> {Tree.set.plain(~S, ~fetch, a, Some{Put.root(t1)}, k, v2) == Some{t12}: Maybe<&2, Put>}
    -> {Tree.set.plain(~S, ~fetch, s, Canon.of(bs), k, v2) == Some{t2}: Maybe<&2, Put>}
    -> {Put.root(t12) == Put.root(t2): Hashes.Hash}

def Tree.set_twice(ty, fetch, grows, kept, s, a, bs, k, v1, v2, t1, t12, t2):
  +hd => +hh => ga => +hs1 => hn1 =>
    +r1 = Tree.set_canon(~ty, ~fetch, s, bs, k, v1, t1)(hd)(hh)(hs1)
    +ha = Tree.set_canon_holds(
      ~ty,
      ~fetch,
      ~grows,
      ~kept,
      s,
      a,
      bs,
      k,
      v1,
      t1
    )(ga)(hd)(hh)(hs1)(hn1)
    %Equal.sym(Maybe<&2, Hashes.Hash>, Some{Put.root(t1)}, Canon.of(Binds.put(bs, k, v1)), r1):
      {Tree.set.plain(~ty, ~fetch, a, _, k, v2) == Some{t12}: Maybe<&2, Put>}
        -> {Tree.set.plain(~ty, ~fetch, s, Canon.of(bs), k, v2) == Some{t2}: Maybe<&2, Put>}
        -> {Put.root(t12) == Put.root(t2): Hashes.Hash}
    hs12 => hs2 =>
      +r12 = Tree.set_canon(
        ~ty,
        ~fetch,
        a,
        Binds.put(bs, k, v1),
        k,
        v2,
        t12
      )(Binds.distinct_put(bs, k, v1)(hd))(ha)(hs12)
      +r2 = Tree.set_canon(~ty, ~fetch, s, bs, k, v2, t2)(hd)(hh)(hs2)
      Shared.Maybe.some_inj(
        Hashes.Hash,
        Put.root(t12),
        Put.root(t2),
        Equal.trans(
          Maybe<&2, Hashes.Hash>,
          Some{Put.root(t12)},
          Canon.of(Binds.put(bs, k, v2)),
          Some{Put.root(t2)},
          Equal.trans(
            Maybe<&2, Hashes.Hash>,
            Some{Put.root(t12)},
            Canon.of(Binds.put(Binds.put(bs, k, v1), k, v2)),
            Canon.of(Binds.put(bs, k, v2)),
            r12,
            Equal.cong(
              List<&2, Binding>,
              Maybe<&2, Hashes.Hash>,
              l => Canon.of(l),
              Binds.put(Binds.put(bs, k, v1), k, v2),
              Binds.put(bs, k, v2),
              Binds.put_twice(bs, k, v1, v2)
            )
          ),
          Equal.sym(Maybe<&2, Hashes.Hash>, Some{Put.root(t2)}, Canon.of(Binds.put(bs, k, v2)), r2)
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Looks
# -----

# Tree.look.go_value at a leaf, once whether its key is k is known (b)
def Tree.look.leaf_value(
  b: Bool,
  -v: List<&2, U32>
) -> {
  Look.value(
    Shared.Bool.when(Look, b, u => Look.Found{v}, u => Look.Absent{})
  )
    == Shared.Maybe.when(List<&2, U32>, b, u => Some{v}): Maybe<&2, List<&2, U32>>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the value that a look finds at a part is what the read gives there
def Tree.look.go_value(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  m: Maybe<&2, Node>,
  o: Maybe<&2, Hashes.Hash>
) -> {
  Look.value(
    Tree.look.go(~S, ~fetch, s, p, k, o, m)
  )
    == Tree.get.go(~S, ~fetch, s, p, k, m): Maybe<&2, List<&2, U32>>
}:
  match p m o:
    case q None{} None{}:
      {==}
    case q None{} Some{h}:
      {==}
    case q Some{Node.Empty{}} w:
      {==}
    case q Some{Node.Leaf{k2, v}} w:
      Tree.look.leaf_value(Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), v)
    case Nil{} Some{Node.Branch{ks}} w:
      {==}
    case Con{+x, r} Some{Node.Branch{+ks}} w:
      Tree.look.go_value(
        ~S,
        ~fetch,
        s,
        r,
        k,
        Tree.part(~S, ~fetch, s, Parts.at(ks, x)),
        Parts.at(ks, x)
      )

# the value that a look finds is what the read gives
law Tree.look_value:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  {
    Look.value(
      Tree.look.plain(~S, ~fetch, s, h, k)
    )
      == Tree.get.plain(~S, ~fetch, s, h, k): Maybe<&2, List<&2, U32>>
  }

def Tree.look_value(ty, fetch, s, h, k):
  Tree.look.go_value(~ty, ~fetch, s, Tree.path(k), k, Tree.part(~ty, ~fetch, s, h), h)

# a look is Absent
def Look.is_absent(l: Look) -> Bool:
  match l:
    case Look.Absent{}:
      True{}
    case Look.Found{v}:
      False{}
    case Look.Missing{h}:
      False{}

# a look that gives the value v is Found v
def Look.found_of(
  l: Look,
  -v: List<&2, U32>
) -> {Look.value(l) == Some{v}: Maybe<&2, List<&2, U32>>} -> {l == Look.Found{v}: Look}:
  match l:
    case Look.Found{x}:
      e => Equal.cong(
        List<&2, U32>,
        Look,
        y => Look.Found{y},
        x,
        v,
        Shared.Maybe.some_inj(List<&2, U32>, x, v, e)
      )
    case Look.Absent{}:
      e => Empty.absurd(
        {Look.Absent{} == Look.Found{v}: Look},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, e)
      )
    case Look.Missing{h}:
      e => Empty.absurd(
        {Look.Missing{h} == Look.Found{v}: Look},
        Shared.Maybe.none_ne_some(List<&2, U32>, v, e)
      )

# a value that a look found, it finds in any store that grows: Found is final
law Tree.look_found_kept:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +a: S
  for +b: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for +v: List<&2, U32>
  {grows(a, b) == True{}: Bool}
    -> {Tree.look.plain(~S, ~fetch, a, h, k) == Look.Found{v}: Look}
    -> {Tree.look.plain(~S, ~fetch, b, h, k) == Look.Found{v}: Look}

def Tree.look_found_kept(ty, fetch, grows, kept, a, b, h, k, v):
  gr => e => Look.found_of(
    Tree.look.plain(~ty, ~fetch, b, h, k),
    v
  )(
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Look.value(Tree.look.plain(~ty, ~fetch, b, h, k)),
      Tree.get.plain(~ty, ~fetch, b, h, k),
      Some{v},
      Tree.look_value(~ty, ~fetch, b, h, k),
      Tree.get_grows(
        ~ty,
        ~fetch,
        ~grows,
        ~kept,
        a,
        b,
        h,
        k,
        v
      )(
        gr
      )(
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Tree.get.plain(~ty, ~fetch, a, h, k),
          Look.value(Tree.look.plain(~ty, ~fetch, a, h, k)),
          Some{v},
          Equal.sym(
            Maybe<&2, List<&2, U32>>,
            Look.value(Tree.look.plain(~ty, ~fetch, a, h, k)),
            Tree.get.plain(~ty, ~fetch, a, h, k),
            Tree.look_value(~ty, ~fetch, a, h, k)
          ),
          Equal.cong(
            Look,
            Maybe<&2, List<&2, U32>>,
            l => Look.value(l),
            Tree.look.plain(~ty, ~fetch, a, h, k),
            Look.Found{v},
            e
          )
        )
      )
    )
  )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a key that a look found absent at a part is absent in any store that grows
def Tree.look.go_absent(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Stores.Store.Keeps(S, fetch, grows),
  +a: S,
  +b: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  m: Maybe<&2, Node>,
  o: Maybe<&2, Hashes.Hash>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.part(~S, ~fetch, a, o) == m: Maybe<&2, Node>
} -> {
  Tree.look.go(~S, ~fetch, a, p, k, o, m) == Look.Absent{}: Look
} -> {Tree.look.go(~S, ~fetch, b, p, k, o, Tree.part(~S, ~fetch, b, o)) == Look.Absent{}: Look}:
  match p m o:
    case q None{} None{}:
      em => e => Empty.absurd(
        {
          Tree.look.go(
            ~S,
            ~fetch,
            b,
            q,
            k,
            None{},
            Tree.part(~S, ~fetch, b, None{})
          )
            == Look.Absent{}: Look
        },
        Shared.Maybe.none_ne_some(
          Node,
          Node.Empty{},
          Equal.sym(Maybe<&2, Node>, Some{Node.Empty{}}, None{}, em)
        )
      )
    case q None{} Some{h}:
      em => e => Empty.absurd(
        {
          Tree.look.go(
            ~S,
            ~fetch,
            b,
            q,
            k,
            Some{h},
            Tree.part(~S, ~fetch, b, Some{h})
          )
            == Look.Absent{}: Look
        },
        Shared.Bool.false_ne_true(
          Equal.cong(Look, Bool, l => Look.is_absent(l), Look.Missing{h}, Look.Absent{}, e)
        )
      )
    case q Some{Node.Empty{}} w:
      em => e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.part(~S, ~fetch, b, w),
          Some{Node.Empty{}},
          Tree.part_kept(~S, ~fetch, ~grows, ~kept, a, b, w, Node.Empty{}, gr)(em)
        ): {Tree.look.go(~S, ~fetch, b, q, k, w, _) == Look.Absent{}: Look}
        e
    case q Some{Node.Leaf{k2, v}} w:
      em => e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.part(~S, ~fetch, b, w),
          Some{Node.Leaf{k2, v}},
          Tree.part_kept(~S, ~fetch, ~grows, ~kept, a, b, w, Node.Leaf{k2, v}, gr)(em)
        ): {Tree.look.go(~S, ~fetch, b, q, k, w, _) == Look.Absent{}: Look}
        e
    case Nil{} Some{Node.Branch{ks}} w:
      em => e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.part(~S, ~fetch, b, w),
          Some{Node.Branch{ks}},
          Tree.part_kept(~S, ~fetch, ~grows, ~kept, a, b, w, Node.Branch{ks}, gr)(em)
        ): {Tree.look.go(~S, ~fetch, b, [], k, w, _) == Look.Absent{}: Look}
        e
    case Con{+x, r} Some{Node.Branch{+ks}} w:
      em => e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.part(~S, ~fetch, b, w),
          Some{Node.Branch{ks}},
          Tree.part_kept(~S, ~fetch, ~grows, ~kept, a, b, w, Node.Branch{ks}, gr)(em)
        ): {Tree.look.go(~S, ~fetch, b, Con{x, r}, k, w, _) == Look.Absent{}: Look}
        Tree.look.go_absent(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          a,
          b,
          r,
          k,
          Tree.part(~S, ~fetch, a, Parts.at(ks, x)),
          Parts.at(ks, x),
          gr
        )({==})(e)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a key that a look found absent is absent in any store that grows: Absent is
# final
law Tree.look_absent_kept:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Stores.Store.Keeps(S, fetch, grows)
  for +a: S
  for +b: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  {grows(a, b) == True{}: Bool}
    -> {Tree.look.plain(~S, ~fetch, a, h, k) == Look.Absent{}: Look}
    -> {Tree.look.plain(~S, ~fetch, b, h, k) == Look.Absent{}: Look}

def Tree.look_absent_kept(ty, fetch, grows, kept, a, b, h, k):
  gr => Tree.look.go_absent(
    ~ty,
    ~fetch,
    ~grows,
    ~kept,
    a,
    b,
    Tree.path(k),
    k,
    Tree.part(~ty, ~fetch, a, h),
    h,
    gr
  )({==})
