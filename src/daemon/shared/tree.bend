import Base
import ../../shared.bend as Shared
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes

# Trees
# =====
# A tree maps keys to values (both lists of words), and is held as nodes in a
# store of data by hash: a version of a line is the hash of its tree's root.
# A tree goes 16 ways by the nibbles of its key's hash, highest first, and
# ends in a leaf as soon as a part of it holds one key, so a read or a write
# visits about log16 of its size nodes. A tree is named by the hash of its root
# (none: the empty tree), and two versions share every part that neither
# changed.

# a node: empty (what an empty part reads as; never stored), a leaf, which
# holds one key and its value, or a branch, which holds the root of each of
# its 16 parts (none: empty)
type Node is Data:
  Node.empty{}
  Node.leaf{key: List<&2, U32>, value: List<&2, U32>}
  Node.branch{kids: List<&2, Maybe<&2, Hashes.Hash>>}

# Codes
# -----

# the hash h, then r
def Hash.code(h: Hashes.Hash, r: List<&2, U32>) -> List<&2, U32>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      a <> b <> c <> d <> e <> f <> g <> i <> r

# a hash
def Hash.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Hashes.Hash>>:
  match ts:
    case Con{a, Con{b, Con{c, Con{d, Con{e, Con{f, Con{g, Con{i, r}}}}}}}}:
      Some{Codes.Read{Hashes.Hash{a, b, c, d, e, f, g, i}, r}}
    case _:
      None{}

# the parts ks of a branch, then r
def Kids.code(ks: List<&2, Maybe<&2, Hashes.Hash>>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(
    ~Maybe<&2, Hashes.Hash>,
    ~(m => r2 => Codes.Code.maybe(~Hashes.Hash, ~Hash.code, m, r2)),
    ks,
    r
  )

# the parts of a branch
def Kids.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Maybe<&2, Hashes.Hash>>>>:
  Codes.Code.list.read(
    ~Maybe<&2, Hashes.Hash>,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hash.code.read, m)),
    ts
  )

# the node n, then r
def Node.code(n: Node, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Node.empty{}:
      0 <> r
    case Node.leaf{k, v}:
      1 <> Codes.Code.words(k, Codes.Code.words(v, r))
    case Node.branch{ks}:
      2 <> Kids.code(ks, r)

# a node whose tag is x: empty (0), a leaf (1) or a branch (other tags)
def Node.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    U32.is_eq(x, 0),
    u => Some{Codes.Read{Node.empty{}, r}},
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Node>>,
      U32.is_eq(x, 1),
      u => Codes.Code.two.read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.read,
        ~Codes.Code.words.read,
        k => v => Node.leaf{k, v},
        r
      ),
      u => Codes.Code.one.read(
        ~List<&2, Maybe<&2, Hashes.Hash>>,
        ~Node,
        ~Kids.code.read,
        ks => Node.branch{ks},
        r
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
  Shared.Maybe.then(Codes.Read<Node>, Node, Node.code.read(ws), Node.of.read)

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
def Kids.at(ks: List<&2, Maybe<&2, Hashes.Hash>>, n: Nat) -> Maybe<&2, Hashes.Hash>:
  match ks n:
    case Nil{} m:
      None{}
    case Con{x, r} 0n:
      x
    case Con{x, r} 1n+p:
      Kids.at(r, p)

# the parts ks with the part n set to x (empty parts fill a gap)
def Kids.set(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  x: Maybe<&2, Hashes.Hash>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match ks n:
    case Nil{} 0n:
      [x]
    case Nil{} 1n+p:
      None{} <> Kids.set([], p, x)
    case Con{y, r} 0n:
      x <> r
    case Con{y, r} 1n+p:
      y <> Kids.set(r, p, x)

# n empty parts
def Kids.empty(n: Nat) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match n:
    case 0n:
      []
    case 1n+p:
      None{} <> Kids.empty(p)

# the 16 parts of a branch, empty
def Kids.none() -> List<&2, Maybe<&2, Hashes.Hash>>:
  Kids.empty(16n)

# Reads
# -----

# the node of the hash h, in the store s
def Tree.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Shared.Maybe.then(List<&2, U32>, Node, fetch(s)(h), Node.of)

# the node of the part x of a branch (none: empty), in the store s
def Tree.kid(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  x: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Node>:
  match x:
    case None{}:
      Some{Node.empty{}}
    case Some{h}:
      Tree.node(~S, ~fetch, s, h)

# the value of the key k in the node m (none: not in the store), whose path
# below it is p
def Tree.go(
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
    case q Some{Node.empty{}}:
      None{}
    case q Some{Node.leaf{k2, v}}:
      Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), u => Some{v})
    case Nil{} Some{Node.branch{ks}}:
      None{}
    case Con{x, r} Some{Node.branch{ks}}:
      Tree.go(~S, ~fetch, s, r, k, Tree.kid(~S, ~fetch, s, Kids.at(ks, x)))

# the value of the key k in the tree whose root is h, in the store s
def Tree.get(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Tree.go(~S, ~fetch, s, Tree.path(k), k, Tree.kid(~S, ~fetch, s, h))

# Writes
# ------
# A write fails (none) when the store does not hold a node on its path, or
# when the key's path is the whole path of another key in the tree.

# a new part of a tree: its root, and the words of the nodes that it adds
type Put is Data:
  Put{root: Hashes.Hash, nodes: List<&2, List<&2, U32>>}

# the root of the part p
def Put.root(p: Put) -> Hashes.Hash:
  match p:
    case Put{h, ns}:
      h

# the nodes that the part p adds
def Put.nodes(p: Put) -> List<&2, List<&2, U32>>:
  match p:
    case Put{h, ns}:
      ns

# the part that is the node n, after the nodes ns
def Put.node(n: Node, ns: List<&2, List<&2, U32>>) -> Put:
  +ws = Node.words(n)
  Put{Hashes.Sha.hash(ws), ws <> ns}

# the part of a branch of parts ks whose part n is the new part p
def Put.into(ks: List<&2, Maybe<&2, Hashes.Hash>>, n: Nat, +p: Put) -> Put:
  Put.node(Node.branch{Kids.set(ks, n, Some{Put.root(p)})}, Put.nodes(p))

# the part that holds the new leaf l, whose path below here is p1,
# and the part o already there, whose path below here is p2: branches down to
# where the paths part
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
        u => Shared.Maybe.then(
          Put,
          Put,
          Tree.split(r1, r2, l, o),
          p => Some{Put.into(Kids.none(), a, p)}
        ),
        u => Some{
          Put.node(
            Node.branch{Kids.set(Kids.set(Kids.none(), a, Some{Put.root(l)}), b, o)},
            Put.nodes(l)
          )
        }
      )
    case q w:
      None{}

# the part o (none: empty), whose node is m (none: not in the store), at depth
# d, whose path below is p, with the key k set to the value v
def Tree.put(
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
    case q Some{Node.empty{}}:
      Some{Put.node(Node.leaf{k, v}, [])}
    case q Some{Node.leaf{+k2, v2}}:
      +l = Put.node(Node.leaf{k, v}, [])
      Shared.Bool.when(
        Maybe<&2, Put>,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Some{l},
        w => Tree.split(q, List.drop(&2, Nat, Tree.path(k2), d), l, o)
      )
    case Con{+x, r} Some{Node.branch{+ks}}:
      +kid = Kids.at(ks, x)
      Shared.Maybe.then(
        Put,
        Put,
        Tree.put(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.kid(~S, ~fetch, s, kid)),
        p2 => Some{Put.into(ks, x, p2)}
      )
    case Nil{} Some{Node.branch{ks}}:
      None{}

# the tree whose root is h, in the store s, with the key k set to the value
# v: its new root, and the nodes that it adds
def Tree.set(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> Maybe<&2, Put>:
  Tree.put(~S, ~fetch, s, Tree.path(k), 0n, k, v, h, Tree.kid(~S, ~fetch, s, h))

# Laws
# ----

# a hash reads back
def Hash.code_read(
  h: Hashes.Hash,
  r: List<&2, U32>
) -> {
  Hash.code.read(Hash.code(h, r)) == Some{Codes.Read{h, r}}: Maybe<&2, Codes.Read<Hashes.Hash>>
}:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      {==}

# the code of hashes
def Hash.codec() -> Codes.Codec(Hashes.Hash):
  (Hash.code, (Hash.code.read, h => r => Hash.code_read(h, r)))

# the code of the parts of a branch
def Kids.codec() -> Codes.Codec(List<&2, Maybe<&2, Hashes.Hash>>):
  Codes.Code.list.codec(
    ~Maybe<&2, Hashes.Hash>,
    ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hash.codec())
  )

# a node reads back
def Node.code_read(
  n: Node,
  r: List<&2, U32>
) -> {Node.code.read(Node.code(n, r)) == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>}:
  match n:
    case Node.empty{}:
      {==}
    case Node.leaf{k, v}:
      Codes.Code.two_read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        a => b => Node.leaf{a, b},
        k,
        v,
        r
      )
    case Node.branch{ks}:
      Codes.Code.one_read(
        ~List<&2, Maybe<&2, Hashes.Hash>>,
        ~Node,
        ~Kids.codec(),
        a => Node.branch{a},
        ks,
        r
      )

# a node is the node of its words
law Node.of_words:
  for n: Node
  {Node.of(Node.words(n)) == Some{n}: Maybe<&2, Node>}

def Node.of_words(n):
  %Equal.sym(
    Maybe<&2, Codes.Read<Node>>,
    Node.code.read(Node.words(n)),
    Some{Codes.Read{n, []}},
    Node.code_read(n, [])
  ): {Shared.Maybe.then(Codes.Read<Node>, Node, _, Node.of.read) == Some{n}: Maybe<&2, Node>}
  {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the part n of parts whose part n was set to y is y
def Kids.at_set(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {Kids.at(Kids.set(ks, n, y), n) == y: Maybe<&2, Hashes.Hash>}:
  match ks n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      Kids.at_set([], p, y)
    case Con{x, r} 0n:
      {==}
    case Con{x, r} 1n+p:
      Kids.at_set(r, p, y)

# the part z of parts whose part n was set to y: y if z is n, else as before
def Kids.at_set_pick(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  z: Nat,
  n: Nat,
  y: Maybe<&2, Hashes.Hash>
) -> {
  Kids.at(
    Kids.set(ks, n, y),
    z
  )
    == Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(z, n), y, Kids.at(ks, z)): Maybe<&2, Hashes.Hash>
}:
  match ks z n:
    case Nil{} 0n 0n:
      {==}
    case Nil{} 0n 1n+q:
      {==}
    case Nil{} 1n+p 0n:
      {==}
    case Nil{} 1n+p 1n+q:
      Kids.at_set_pick([], p, q, y)
    case Con{x, r} 0n 0n:
      {==}
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      Kids.at_set_pick(r, p, q, y)

# setting the part b does not change the part a, another part
def Kids.at_other(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  b: Nat,
  y: Maybe<&2, Hashes.Hash>,
  e: {Nat.is_eq(a, b) == False{}: Bool}
) -> {Kids.at(Kids.set(ks, b, y), a) == Kids.at(ks, a): Maybe<&2, Hashes.Hash>}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Kids.at(Kids.set(ks, b, y), a),
    Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(a, b), y, Kids.at(ks, a)),
    Kids.at_set_pick(ks, a, b, y)
  ): {_ == Kids.at(ks, a): Maybe<&2, Hashes.Hash>}
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
      Kids.at(ks, a)
    )
      == Kids.at(ks, a): Maybe<&2, Hashes.Hash>
  }
  {==}

# the store s holds the words ws, under their hash
def Tree.has(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +ws: List<&2, U32>
) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    fetch(s)(Hashes.Sha.hash(ws)),
    Some{ws}
  )

# the store s holds each of the words ns, under their hashes
def Tree.holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ns: List<&2, List<&2, U32>>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{ws, r}:
      List.all.if(u => Tree.holds(~S, ~fetch, s, r), Tree.has(~S, ~fetch, s, ws))

# a store that holds the words of the node n gives n for its hash
def Tree.has_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +n: Node,
  e: {Tree.has(~S, ~fetch, s, Node.words(n)) == True{}: Bool}
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
  ): {Shared.Maybe.then(List<&2, U32>, Node, _, Node.of) == Some{n}: Maybe<&2, Node>}
  Node.of_words(n)

# a read of the key k at the leaf of k1 and v1 gives v1 if k1 is k
def Tree.go_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  k1: List<&2, U32>,
  v1: List<&2, U32>
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    p,
    k,
    Some{Node.leaf{k1, v1}}
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
) -> {Tree.go(~S, ~fetch, s, p, k, Some{Node.leaf{k, v}}) == Some{v}: Maybe<&2, List<&2, U32>>}:
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Tree.go(~S, ~fetch, s, p, k, Some{Node.leaf{k, v}}),
    Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k, k), u => Some{v}),
    Tree.go_leaf(~S, ~fetch, s, p, k, k, v)
  ): {_ == Some{v}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
  ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == Some{v}: Maybe<&2, List<&2, U32>>}
  {==}

# what a read of the key k along p gives at the root of the new part r
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
        Tree.holds(~S, ~fetch, s2, Put.nodes(q)) == True{}: Bool
      } -> {
        Tree.go(
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
) -> Tree.Reads(~S, ~fetch, s2, po, k, wo, Shared.Maybe.then(Put, Put, m, f)):
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
) -> Tree.Reads(~S, ~fetch, s2, p, k, Some{v}, Some{Put.node(Node.leaf{k, v}, [])}):
  e =>
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(Node.leaf{k, v})),
      Some{Node.leaf{k, v}},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        Node.leaf{k, v},
        Shared.List.all.if_hit(
          Tree.has(~S, ~fetch, s2, Node.words(Node.leaf{k, v})),
          u => True{}
        )(e)
      )
    ): {Tree.go(~S, ~fetch, s2, p, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
    Tree.read_leaf(~S, ~fetch, s2, p, k, v)

# a new branch of parts ks whose part n is the new part q reads along x then
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
    +b = {Node.branch{Kids.set(ks, n, Some{Put.root(q)})}: Node}
    +rest = Tree.holds(~S, ~fetch, s2, Put.nodes(q))
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(b)),
      Some{b},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        b,
        Shared.List.all.if_hit(Tree.has(~S, ~fetch, s2, Node.words(b)), u => rest)(e)
      )
    ): {Tree.go(~S, ~fetch, s2, Con{x, r}, k, _) == w: Maybe<&2, List<&2, U32>>}
    %Equal.sym(
      Nat,
      x,
      n,
      ez
    ): {
      Tree.go(
        ~S,
        ~fetch,
        s2,
        r,
        k,
        Tree.kid(~S, ~fetch, s2, Kids.at(Kids.set(ks, n, Some{Put.root(q)}), _))
      )
        == w: Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Kids.at(Kids.set(ks, n, Some{Put.root(q)}), n),
      Some{Put.root(q)},
      Kids.at_set(ks, n, Some{Put.root(q)})
    ): {Tree.go(~S, ~fetch, s2, r, k, Tree.kid(~S, ~fetch, s2, _)) == w: Maybe<&2, List<&2, U32>>}
    ih(Shared.List.all.if_rest(Tree.has(~S, ~fetch, s2, Node.words(b)), u => rest)(e))

# the part c of Tree.split, with the new leaf of k and v, reads as v along a
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
    Tree.split(r1, r2, Put.node(Node.leaf{k, v}, []), o)
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
    u => Shared.Maybe.then(
      Put,
      Put,
      Tree.split(r1, r2, Put.node(Node.leaf{k, v}, []), o),
      p => Some{Put.into(Kids.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.branch{Kids.set(Kids.set(Kids.none(), a, Some{Node.hash(Node.leaf{k, v})}), b, o)},
        [Node.words(Node.leaf{k, v})]
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
        Tree.split(r1, r2, Put.node(Node.leaf{k, v}, []), o),
        p => Some{Put.into(Kids.none(), a, p)},
        q => iq => Tree.read_into(~S, ~fetch, s2, Kids.none(), a, a, r1, k, Some{v}, q, {==}, iq),
        ih
      )
    case False{}:
      +e =>
        +l = {Node.leaf{k, v}: Node}
        +ka = Kids.set(Kids.none(), a, Some{Node.hash(l)})
        +n = {Node.branch{Kids.set(ka, b, o)}: Node}
        +rest = Tree.holds(~S, ~fetch, s2, [Node.words(l)])
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Shared.List.all.if_hit(Tree.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
          )
        ): {Tree.go(~S, ~fetch, s2, Con{a, r1}, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(Kids.set(ka, b, o), a),
          Kids.at(ka, a),
          Kids.at_other(ka, a, b, o, ec)
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s2,
            r1,
            k,
            Tree.kid(~S, ~fetch, s2, _)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(ka, a),
          Some{Node.hash(l)},
          Kids.at_set(Kids.none(), a, Some{Node.hash(l)})
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s2,
            r1,
            k,
            Tree.kid(~S, ~fetch, s2, _)
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
            Shared.List.all.if_hit(
              Tree.has(~S, ~fetch, s2, Node.words(l)),
              u => True{}
            )(Shared.List.all.if_rest(Tree.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e))
          )
        ): {Tree.go(~S, ~fetch, s2, r1, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
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
  Tree.split(p1, p2, Put.node(Node.leaf{k, v}, []), o)
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

# the part c of Tree.put, at a leaf of k2, reads as v along q
def Tree.read_put.when(
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
    u => Some{Put.node(Node.leaf{k, v}, [])},
    w => Tree.split(q, List.drop(&2, Nat, Tree.path(k2), d), Put.node(Node.leaf{k, v}, []), o)
  )
):
  match c:
    case True{}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v)
    case False{}:
      Tree.read_split(~S, ~fetch, s2, q, List.drop(&2, Nat, Tree.path(k2), d), o, k, v)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# Tree.put from the part m of the store s, with k set to v, reads as v along
# p, in any store s2 that holds its nodes
def Tree.read_put(
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
) -> Tree.Reads(~S, ~fetch, s2, p, k, Some{v}, Tree.put(~S, ~fetch, s, p, d, k, v, o, m)):
  match p m:
    case q None{}:
      Unit{}
    case q Some{Node.empty{}}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v)
    case q Some{Node.leaf{+k2, v2}}:
      Tree.read_put.when(
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
    case Con{+x, +r} Some{Node.branch{+ks}}:
      +kid = Kids.at(ks, x)
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r,
        Con{x, r},
        k,
        Some{v},
        Some{v},
        Tree.put(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.kid(~S, ~fetch, s, kid)),
        p2 => Some{Put.into(ks, x, p2)},
        q => iq => Tree.read_into(~S, ~fetch, s2, ks, x, x, r, k, Some{v}, q, {==}, iq),
        Tree.read_put(~S, ~fetch, s, s2, r, 1n+d, k, v, kid, Tree.kid(~S, ~fetch, s, kid))
      )
    case Nil{} Some{Node.branch{ks}}:
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
  {Tree.set(~S, ~fetch, s, h, k, v) == Some{t}: Maybe<&2, Put>}
    -> {Tree.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {Tree.get(~S, ~fetch, s2, Some{Put.root(t)}, k) == Some{v}: Maybe<&2, List<&2, U32>>}

def Tree.get_set(ty, fetch, s, s2, h, k, v, t):
  e =>
    %e: Tree.Reads(~ty, ~fetch, s2, Tree.path(k), k, Some{v}, _)
    Tree.read_put(~ty, ~fetch, s, s2, Tree.path(k), 0n, k, v, h, Tree.kid(~ty, ~fetch, s, h))

# that a store b, which grows from a store a (grows), gives the words that a
# gives
def Tree.Keeps(
  -S: Data,
  fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  grows: S -> S -> Bool
) -> Type:
  @a: S -> @b: S -> @h: Hashes.Hash -> @w: List<
    &2,
    U32> -> {
    grows(a, b) == True{}: Bool
  } -> {
    fetch(a)(h) == Some{w}: Maybe<&2, List<&2, U32>>
  } -> {fetch(b)(h) == Some{w}: Maybe<&2, List<&2, U32>>}

# a store b that grows from a gives each node that a gives
def Tree.node_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Tree.Keeps(S, fetch, grows),
  +a: S,
  b: S,
  +h: Hashes.Hash,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.node(~S, ~fetch, a, h) == Some{n}: Maybe<&2, Node>
} -> {Tree.node(~S, ~fetch, b, h) == Some{n}: Maybe<&2, Node>}:
  Shared.Maybe.then_kept(
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
def Tree.kid_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Tree.Keeps(S, fetch, grows),
  a: S,
  b: S,
  x: Maybe<&2, Hashes.Hash>,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Tree.kid(~S, ~fetch, a, x) == Some{n}: Maybe<&2, Node>
} -> {Tree.kid(~S, ~fetch, b, x) == Some{n}: Maybe<&2, Node>}:
  match x:
    case None{}:
      e => e
    case Some{h}:
      Tree.node_kept(~S, ~fetch, ~grows, ~kept, a, b, h, n, gr)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# a read of the key k at the node m in a store a gives the same in a store b
# that grows from a, at a node m2 that b gives where a gives m
def Tree.go_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Tree.Keeps(S, fetch, grows),
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
  Tree.go(~S, ~fetch, a, p, k, m) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Tree.go(~S, ~fetch, b, p, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match p m:
    case q None{}:
      e => Empty.absurd(
        {Tree.go(~S, ~fetch, b, q, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case q Some{Node.empty{}}:
      e => Empty.absurd(
        {Tree.go(~S, ~fetch, b, q, k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case q Some{Node.leaf{k2, v}}:
      e =>
        %Equal.sym(
          Maybe<&2, Node>,
          m2,
          Some{Node.leaf{k2, v}},
          hm(Node.leaf{k2, v})({==})
        ): {Tree.go(~S, ~fetch, b, q, k, _) == Some{x}: Maybe<&2, List<&2, U32>>}
        e
    case Nil{} Some{Node.branch{ks}}:
      e => Empty.absurd(
        {Tree.go(~S, ~fetch, b, [], k, m2) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, e)
      )
    case Con{+y, r} Some{Node.branch{+ks}}:
      e =>
        %Equal.sym(
          Maybe<&2, Node>,
          m2,
          Some{Node.branch{ks}},
          hm(Node.branch{ks})({==})
        ): {Tree.go(~S, ~fetch, b, Con{y, r}, k, _) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tree.go_kept(
          ~S,
          ~fetch,
          ~grows,
          ~kept,
          a,
          b,
          r,
          k,
          Tree.kid(~S, ~fetch, a, Kids.at(ks, y)),
          Tree.kid(~S, ~fetch, b, Kids.at(ks, y)),
          x,
          n => Tree.kid_kept(~S, ~fetch, ~grows, ~kept, a, b, Kids.at(ks, y), n, gr),
          gr
        )(e)

# a read that a store gives, a store that grows from it gives too
law Tree.get_grows:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Tree.Keeps(S, fetch, grows)
  for +a: S
  for +b: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for x: List<&2, U32>
  {grows(a, b) == True{}: Bool}
    -> {Tree.get(~S, ~fetch, a, h, k) == Some{x}: Maybe<&2, List<&2, U32>>}
    -> {Tree.get(~S, ~fetch, b, h, k) == Some{x}: Maybe<&2, List<&2, U32>>}

def Tree.get_grows(ty, fetch, grows, kept, a, b, h, k, x):
  +gr => Tree.go_kept(
    ~ty,
    ~fetch,
    ~grows,
    ~kept,
    a,
    b,
    Tree.path(k),
    k,
    Tree.kid(~ty, ~fetch, a, h),
    Tree.kid(~ty, ~fetch, b, h),
    x,
    n => Tree.kid_kept(~ty, ~fetch, ~grows, ~kept, a, b, h, n, gr),
    gr
  )

# each part of empty parts is empty
def Kids.at_empty(n: Nat, z: Nat) -> {Kids.at(Kids.empty(n), z) == None{}: Maybe<&2, Hashes.Hash>}:
  match n z:
    case 0n w:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Kids.at_empty(p, q)

# a read at the empty node gives nothing
def Tree.go_empty(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {Tree.go(~S, ~fetch, s, p, k, Some{Node.empty{}}) == None{}: Maybe<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a new branch of parts ks, whose part n is a new part, reads as nothing at
# its end
def Tree.read_into_nil(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  k: List<&2, U32>,
  m: Maybe<&2, Put>
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  [],
  k,
  None{},
  Shared.Maybe.then(Put, Put, m, p => Some{Put.into(ks, n, p)})
):
  match m:
    case None{}:
      Unit{}
    case Some{+q}:
      +e =>
        +b = {Node.branch{Kids.set(ks, n, Some{Put.root(q)})}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(b)),
          Some{b},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            b,
            Shared.List.all.if_hit(
              Tree.has(~S, ~fetch, s2, Node.words(b)),
              u => Tree.holds(~S, ~fetch, s2, Put.nodes(q))
            )(e)
          )
        ): {Tree.go(~S, ~fetch, s2, [], k, _) == None{}: Maybe<&2, List<&2, U32>>}
        {==}

# a new branch of parts ks whose part n is the new part q reads along z then r
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
  Tree.go(~S, ~fetch, s2, r, k, Tree.kid(~S, ~fetch, s2, Kids.at(ks, z))),
  Some{Put.into(ks, n, q)}
):
  +e =>
    +b = {Node.branch{Kids.set(ks, n, Some{Put.root(q)})}: Node}
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(b)),
      Some{b},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        b,
        Shared.List.all.if_hit(
          Tree.has(~S, ~fetch, s2, Node.words(b)),
          u => Tree.holds(~S, ~fetch, s2, Put.nodes(q))
        )(e)
      )
    ): {
      Tree.go(
        ~S,
        ~fetch,
        s2,
        Con{z, r},
        k,
        _
      )
        == Tree.go(
          ~S,
          ~fetch,
          s2,
          r,
          k,
          Tree.kid(~S, ~fetch, s2, Kids.at(ks, z))
        ): Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Maybe<&2, Hashes.Hash>,
      Kids.at(Kids.set(ks, n, Some{Put.root(q)}), z),
      Kids.at(ks, z),
      Kids.at_other(ks, z, n, Some{Put.root(q)}, ec)
    ): {
      Tree.go(
        ~S,
        ~fetch,
        s2,
        r,
        k,
        Tree.kid(~S, ~fetch, s2, _)
      )
        == Tree.go(
          ~S,
          ~fetch,
          s2,
          r,
          k,
          Tree.kid(~S, ~fetch, s2, Kids.at(ks, z))
        ): Maybe<&2, List<&2, U32>>
    }
    {==}

# a read of the key k2 at the leaf of another key k gives nothing
def Tree.go_leaf_off(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, Nat>,
  k2: List<&2, U32>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> {Tree.go(~S, ~fetch, s, p, k2, Some{Node.leaf{k, v}}) == None{}: Maybe<&2, List<&2, U32>>}:
  %Equal.sym(
    Maybe<&2, List<&2, U32>>,
    Tree.go(~S, ~fetch, s, p, k2, Some{Node.leaf{k, v}}),
    Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k, k2), u => Some{v}),
    Tree.go_leaf(~S, ~fetch, s, p, k2, k, v)
  ): {_ == None{}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
    False{},
    ne
  ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == None{}: Maybe<&2, List<&2, U32>>}
  {==}

# a read at an empty part of a new branch gives nothing
def Tree.go_none_part(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  r: List<&2, Nat>,
  k: List<&2, U32>,
  z: Nat
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    r,
    k,
    Tree.kid(~S, ~fetch, s, Kids.at(Kids.none(), z))
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Kids.at(Kids.none(), z),
    None{},
    Kids.at_empty(16n, z)
  ): {Tree.go(~S, ~fetch, s, r, k, Tree.kid(~S, ~fetch, s, _)) == None{}: Maybe<&2, List<&2, U32>>}
  Tree.go_empty(~S, ~fetch, s, r, k)

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
) -> Tree.Reads(~S, ~fetch, s2, p, k2, None{}, Some{Put.node(Node.leaf{k, v}, [])}):
  e =>
    +l = {Node.leaf{k, v}: Node}
    %Equal.sym(
      Maybe<&2, Node>,
      Tree.node(~S, ~fetch, s2, Node.hash(l)),
      Some{l},
      Tree.has_node(
        ~S,
        ~fetch,
        s2,
        l,
        Shared.List.all.if_hit(Tree.has(~S, ~fetch, s2, Node.words(l)), u => True{})(e)
      )
    ): {Tree.go(~S, ~fetch, s2, p, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
    Tree.go_leaf_off(~S, ~fetch, s2, p, k2, k, v, ne)

# the part c of Tree.split reads along b then r2, the path of the part o
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
  eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
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
    u => Shared.Maybe.then(
      Put,
      Put,
      Tree.split(r1, r2, l, o),
      p => Some{Put.into(Kids.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.branch{Kids.set(Kids.set(Kids.none(), a, Some{Put.root(l)}), b, o)},
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
        p => Some{Put.into(Kids.none(), a, p)},
        q => iq => Tree.read_into(
          ~S,
          ~fetch,
          s2,
          Kids.none(),
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
        +ka = Kids.set(Kids.none(), a, Some{Put.root(l)})
        +n = {Node.branch{Kids.set(ka, b, o)}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Shared.List.all.if_hit(
              Tree.has(~S, ~fetch, s2, Node.words(n)),
              u => Tree.holds(~S, ~fetch, s2, Put.nodes(l))
            )(e)
          )
        ): {
          Tree.go(
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
          Kids.at(Kids.set(ka, b, o), b),
          o,
          Kids.at_set(ka, b, o)
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.kid(~S, ~fetch, s2, _)
          )
            == Shared.Maybe.when(
              List<&2, U32>,
              Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
              u => Some{v1}
            ): Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.kid(~S, ~fetch, s2, o),
          Some{Node.leaf{k1, v1}},
          eo
        ): {
          Tree.go(
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
        Tree.go_leaf(~S, ~fetch, s2, r2, k2, k1, v1)

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
  +eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>}
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
  eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
  eh: {Tree.node(~S, ~fetch, s2, h) == Some{Node.leaf{k, v}}: Maybe<&2, Node>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool}
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s2,
    r,
    k2,
    Tree.kid(
      ~S,
      ~fetch,
      s2,
      Bool.pick(
        Maybe<&2, Hashes.Hash>,
        c1,
        o,
        Bool.pick(Maybe<&2, Hashes.Hash>, c2, Some{h}, Kids.at(Kids.none(), z))
      )
    )
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
  match c1 c2:
    case True{} w:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.kid(~S, ~fetch, s2, o),
        Some{Node.leaf{k1, v1}},
        eo
      ): {Tree.go(~S, ~fetch, s2, r, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
      Tree.go_leaf_off(~S, ~fetch, s2, r, k2, k1, v1, n1)
    case False{} True{}:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.node(~S, ~fetch, s2, h),
        Some{Node.leaf{k, v}},
        eh
      ): {Tree.go(~S, ~fetch, s2, r, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
      Tree.go_leaf_off(~S, ~fetch, s2, r, k2, k, v, ne)
    case False{} False{}:
      Tree.go_none_part(~S, ~fetch, s2, r, k2, z)

# a new branch made by Tree.split along a and the new part m reads as nothing
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
  Shared.Maybe.then(Put, Put, m, p => Some{Put.into(Kids.none(), n, p)})
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
        p => Some{Put.into(Kids.none(), n, p)},
        q => iq => Tree.read_into(
          ~S,
          ~fetch,
          s2,
          Kids.none(),
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
      %Tree.go_none_part(
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
        Shared.Maybe.then(Put, Put, m, p => Some{Put.into(Kids.none(), n, p)})
      )
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        None{},
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(Kids.none(), z))),
        m,
        p => Some{Put.into(Kids.none(), n, p)},
        q => iq => Tree.read_into_off(~S, ~fetch, s2, Kids.none(), n, z, r2, k2, q, ec),
        ih
      )

# the part c of Tree.split, with the new leaf of k and v, reads as nothing
# at its end
def Tree.other_split_new.nil(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  a: Nat,
  r1: List<&2, Nat>,
  b: Nat,
  r1o: List<&2, Nat>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
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
    u => Shared.Maybe.then(
      Put,
      Put,
      Tree.split(r1, r1o, Put.node(Node.leaf{k, v}, []), o),
      p => Some{Put.into(Kids.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.branch{
          Kids.set(
            Kids.set(Kids.none(), a, Some{Hashes.Sha.hash(Node.words(Node.leaf{k, v}))}),
            b,
            o
          )
        },
        [Node.words(Node.leaf{k, v})]
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
        Kids.none(),
        a,
        k2,
        Tree.split(r1, r1o, Put.node(Node.leaf{k, v}, []), o)
      )
    case False{}:
      +e =>
        +l = {Node.leaf{k, v}: Node}
        +n = {Node.branch{Kids.set(Kids.set(Kids.none(), a, Some{Node.hash(l)}), b, o)}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Shared.List.all.if_hit(
              Tree.has(~S, ~fetch, s2, Node.words(n)),
              u => Tree.holds(~S, ~fetch, s2, [Node.words(l)])
            )(e)
          )
        ): {Tree.go(~S, ~fetch, s2, [], k2, _) == None{}: Maybe<&2, List<&2, U32>>}
        {==}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement; a proof does not run
# the part c of Tree.split, with the new leaf of k and v, reads as nothing for
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
  eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool},
  ih: Tree.Reads(
    ~S,
    ~fetch,
    s2,
    r2,
    k2,
    None{},
    Tree.split(r1, r1o, Put.node(Node.leaf{k, v}, []), o)
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
    u => Shared.Maybe.then(
      Put,
      Put,
      Tree.split(r1, r1o, Put.node(Node.leaf{k, v}, []), o),
      p => Some{Put.into(Kids.none(), a, p)}
    ),
    u => Some{
      Put.node(
        Node.branch{
          Kids.set(
            Kids.set(Kids.none(), a, Some{Hashes.Sha.hash(Node.words(Node.leaf{k, v}))}),
            b,
            o
          )
        },
        [Node.words(Node.leaf{k, v})]
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
        Tree.split(r1, r1o, Put.node(Node.leaf{k, v}, []), o),
        Nat.is_eq(z, a),
        {==},
        ih
      )
    case False{}:
      +e =>
        +l = {Node.leaf{k, v}: Node}
        +ka = Kids.set(Kids.none(), a, Some{Node.hash(l)})
        +n = {Node.branch{Kids.set(ka, b, o)}: Node}
        +rest = Tree.holds(~S, ~fetch, s2, [Node.words(l)])
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s2, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s2,
            n,
            Shared.List.all.if_hit(Tree.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e)
          )
        ): {Tree.go(~S, ~fetch, s2, Con{z, r2}, k2, _) == None{}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(Kids.set(ka, b, o), z),
          Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(z, b), o, Kids.at(ka, z)),
          Kids.at_set_pick(ka, z, b, o)
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.kid(~S, ~fetch, s2, _)
          )
            == None{}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(ka, z),
          Bool.pick(
            Maybe<&2, Hashes.Hash>,
            Nat.is_eq(z, a),
            Some{Node.hash(l)},
            Kids.at(Kids.none(), z)
          ),
          Kids.at_set_pick(Kids.none(), z, a, Some{Node.hash(l)})
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s2,
            r2,
            k2,
            Tree.kid(~S, ~fetch, s2, Bool.pick(Maybe<&2, Hashes.Hash>, Nat.is_eq(z, b), o, _))
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
            Shared.List.all.if_hit(
              Tree.has(~S, ~fetch, s2, Node.words(l)),
              u => True{}
            )(Shared.List.all.if_rest(Tree.has(~S, ~fetch, s2, Node.words(n)), u => rest)(e))
          ),
          ne,
          n1
        )

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
  +eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
  +ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  +n1: {Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  None{},
  Tree.split(p1, p1o, Put.node(Node.leaf{k, v}, []), o)
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
def Tree.other_put.split(
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
  eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), u => Some{v1}),
  Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.leaf{k, v}, []), o)
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
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.leaf{k, v}, []), o)
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
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.leaf{k, v}, []), o)
      )
      Tree.other_split_old(
        ~S,
        ~fetch,
        s2,
        q,
        List.drop(&2, Nat, Tree.path(k1), d),
        Put.node(Node.leaf{k, v}, []),
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
        Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.leaf{k, v}, []), o)
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

# the part c of Tree.put at the leaf of k1 and v1 reads for another key k2
# along its path p2 as that leaf reads
def Tree.other_put.leaf(
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
  eo: {Tree.kid(~S, ~fetch, s2, o) == Some{Node.leaf{k1, v1}}: Maybe<&2, Node>},
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
    u => Some{Put.node(Node.leaf{k, v}, [])},
    w => Tree.split(q, List.drop(&2, Nat, Tree.path(k1), d), Put.node(Node.leaf{k, v}, []), o)
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
        Some{Put.node(Node.leaf{k, v}, [])}
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
        Some{Put.node(Node.leaf{k, v}, [])}
      )
      Tree.read_new_leaf_off(~S, ~fetch, s2, p2, k, v, k2, ne)
    case False{}:
      Tree.other_put.split(
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

# a new branch of parts ks whose part n is the new part m reads for k2 along
# z then r2 as ks does, when m reads along r2 as the part n of ks
def Tree.other_put.con(
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
    Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
    m
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  Con{z, r2},
  k2,
  Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, z))),
  Shared.Maybe.then(Put, Put, m, p => Some{Put.into(ks, n, p)})
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
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, _))),
        Shared.Maybe.then(Put, Put, m, p => Some{Put.into(ks, n, p)})
      )
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r2,
        Con{z, r2},
        k2,
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
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
          Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
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
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
        Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, z))),
        m,
        p => Some{Put.into(ks, n, p)},
        q => iq => Tree.read_into_off(~S, ~fetch, s2, ks, n, z, r2, k2, q, ec),
        ih
      )

# a new branch of parts ks whose part n is the new part m reads for k2 along
# p2 as ks does, when m reads along the rest of p2 as the part n of ks
def Tree.other_put.branch(
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
    Tree.go(~S, ~fetch, s2, r2, k2, Tree.kid(~S, ~fetch, s2, Kids.at(ks, n))),
    m
  )
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Tree.go(~S, ~fetch, s2, p2, k2, Some{Node.branch{ks}}),
  Shared.Maybe.then(Put, Put, m, p => Some{Put.into(ks, n, p)})
):
  match p2:
    case Nil{}:
      Tree.read_into_nil(~S, ~fetch, s2, ks, n, k2, m)
    case Con{+z, +r2}:
      Tree.other_put.con(
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

# Tree.put from the part o, whose node is m in the store s, with k set to v,
# reads for another key k2 along its path p2 as o does, in a store s2 that
# grows from s
def Tree.other_put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Tree.Keeps(S, fetch, grows),
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
  } -> {Tree.kid(~S, ~fetch, s2, o) == Some{n}: Maybe<&2, Node>},
  hp: {List.drop(&2, Nat, Tree.path(k2), d) == p2: List<&2, Nat>},
  ne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Tree.Reads(
  ~S,
  ~fetch,
  s2,
  p2,
  k2,
  Tree.go(~S, ~fetch, s2, p2, k2, Tree.kid(~S, ~fetch, s2, o)),
  Tree.put(~S, ~fetch, s, p, d, k, v, o, m)
):
  match p m:
    case q None{}:
      Unit{}
    case q Some{Node.empty{}}:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.kid(~S, ~fetch, s2, o),
        Some{Node.empty{}},
        hm(Node.empty{})({==})
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.go(~S, ~fetch, s2, p2, k2, _),
        Some{Put.node(Node.leaf{k, v}, [])}
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.go(~S, ~fetch, s2, p2, k2, Some{Node.empty{}}),
        None{},
        Tree.go_empty(~S, ~fetch, s2, p2, k2)
      ): Tree.Reads(~S, ~fetch, s2, p2, k2, _, Some{Put.node(Node.leaf{k, v}, [])})
      Tree.read_new_leaf_off(~S, ~fetch, s2, p2, k, v, k2, ne)
    case q Some{Node.leaf{+k1, +v1}}:
      +eo = hm(Node.leaf{k1, v1})({==})
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.kid(~S, ~fetch, s2, o),
        Some{Node.leaf{k1, v1}},
        eo
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.go(~S, ~fetch, s2, p2, k2, _),
        Tree.put(~S, ~fetch, s, q, d, k, v, o, Some{Node.leaf{k1, v1}})
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Tree.go(~S, ~fetch, s2, p2, k2, Some{Node.leaf{k1, v1}}),
        Shared.Maybe.when(
          List<&2, U32>,
          Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2),
          u => Some{v1}
        ),
        Tree.go_leaf(~S, ~fetch, s2, p2, k2, k1, v1)
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        _,
        Tree.put(~S, ~fetch, s, q, d, k, v, o, Some{Node.leaf{k1, v1}})
      )
      Tree.other_put.leaf(
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
    case Con{+x, +r} Some{Node.branch{+ks}}:
      +kid = Kids.at(ks, x)
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.kid(~S, ~fetch, s2, o),
        Some{Node.branch{ks}},
        hm(Node.branch{ks})({==})
      ): Tree.Reads(
        ~S,
        ~fetch,
        s2,
        p2,
        k2,
        Tree.go(~S, ~fetch, s2, p2, k2, _),
        Tree.put(~S, ~fetch, s, Con{x, r}, d, k, v, o, Some{Node.branch{ks}})
      )
      Tree.other_put.branch(
        ~S,
        ~fetch,
        s2,
        ks,
        x,
        k2,
        p2,
        d,
        Tree.put(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.kid(~S, ~fetch, s, kid)),
        hp,
        r2 => h2 => Tree.other_put(
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
          Tree.kid(~S, ~fetch, s, kid),
          k2,
          r2,
          gr,
          n2 => Tree.kid_kept(~S, ~fetch, ~grows, ~kept, s, s2, kid, n2, gr),
          h2,
          ne
        )
      )
    case Nil{} Some{Node.branch{ks}}:
      Unit{}

# after the key k is set to v in the tree whose root is h in the store s, a
# read of another key k2 at the new root gives what it gives at h, in any
# store s2 that grows from s and holds the new nodes
law Tree.get_other:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Tree.Keeps(S, fetch, grows)
  for +s: S
  for +s2: S
  for +h: Maybe<&2, Hashes.Hash>
  for +k: List<&2, U32>
  for v: List<&2, U32>
  for t: Put
  for +k2: List<&2, U32>
  {grows(s, s2) == True{}: Bool}
    -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
    -> {Tree.set(~S, ~fetch, s, h, k, v) == Some{t}: Maybe<&2, Put>}
    -> {Tree.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {
      Tree.get(
        ~S,
        ~fetch,
        s2,
        Some{Put.root(t)},
        k2
      )
        == Tree.get(~S, ~fetch, s2, h, k2): Maybe<&2, List<&2, U32>>
    }

def Tree.get_other(ty, fetch, grows, kept, s, s2, h, k, v, t, k2):
  +gr => ne => e =>
    %e: Tree.Reads(~ty, ~fetch, s2, Tree.path(k2), k2, Tree.get(~ty, ~fetch, s2, h, k2), _)
    Tree.other_put(
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
      Tree.kid(~ty, ~fetch, s, h),
      k2,
      Tree.path(k2),
      gr,
      n => Tree.kid_kept(~ty, ~fetch, ~grows, ~kept, s, s2, h, n, gr),
      Shared.List.drop_zero(&2, Nat, Tree.path(k2)),
      ne
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
