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
# visits about log16 of its size nodes. Every node is read through its hash,
# so a node that does not match its hash is never believed, and two versions
# share every part that neither changed.

# a node: a leaf, which holds one key and its value, or a branch, which holds
# the root of each of its 16 parts (none: empty)
type Node is Data:
  Node.leaf{key: List<&2, U32>, value: List<&2, U32>}
  Node.branch{kids: List<&2, Maybe<&2, Hashes.Hash>>}

# the hash of the empty tree
def Tree.none() -> Hashes.Hash:
  Hashes.Hash{0, 0, 0, 0, 0, 0, 0, 0}

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

# the words ws, then r
def Words.code(ws: List<&2, U32>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~U32, ~Codes.Code.token, ws, r)

# words
def Words.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, U32>>>:
  Codes.Code.list.read(~U32, ~Codes.Code.token.read, ts)

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
    case Node.leaf{k, v}:
      1 <> Words.code(k, Words.code(v, r))
    case Node.branch{ks}:
      2 <> Kids.code(ks, r)

# a node
def Node.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Node>>,
        U32.is_eq(x, 1),
        u => Codes.Code.two.read(
          ~List<&2, U32>,
          ~List<&2, U32>,
          ~Node,
          ~Words.code.read,
          ~Words.code.read,
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

# Paths
# -----

# the node of the words ws, when they hold one exactly
def Node.of(ws: List<&2, U32>) -> Maybe<&2, Node>:
  Shared.Maybe.then(Codes.Read<Node>, Node, Node.code.read(ws), Node.of.read)

# the 8 nibbles of x, highest first, then r
def Nibbles.word(+x: U32, r: List<&2, U32>) -> List<&2, U32>:
  U32.and(
    U32.shrn(x, 28n),
    15
  )
    <> U32.and(U32.shrn(x, 24n), 15)
    <> U32.and(U32.shrn(x, 20n), 15)
    <> U32.and(U32.shrn(x, 16n), 15)
    <> U32.and(U32.shrn(x, 12n), 15)
    <> U32.and(U32.shrn(x, 8n), 15)
    <> U32.and(U32.shrn(x, 4n), 15)
    <> U32.and(x, 15)
    <> r

# the 64 nibbles of the hash h, highest first
def Nibbles.of(h: Hashes.Hash) -> List<&2, U32>:
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
def Tree.path(k: List<&2, U32>) -> List<&2, U32>:
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

# the parts ks with the part n set to x
def Kids.set(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  n: Nat,
  x: Maybe<&2, Hashes.Hash>
) -> List<&2, Maybe<&2, Hashes.Hash>>:
  match ks n:
    case Nil{} m:
      []
    case Con{y, r} 0n:
      x <> r
    case Con{y, r} 1n+p:
      y <> Kids.set(r, p, x)

# 16 empty parts
def Kids.none() -> List<&2, Maybe<&2, Hashes.Hash>>:
  [
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{},
    None{}
  ]

# Reads
# -----

# the value of the key k in the node m, whose path below it is p
def Tree.go.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, U32>,
  k: List<&2, U32>,
  n: Node
) -> Maybe<&2, List<&2, U32>>:
  match p n:
    case q Node.leaf{k2, v}:
      Shared.Maybe.when(List<&2, U32>, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), u => Some{v})
    case Nil{} Node.branch{ks}:
      None{}
    case Con{x, r} Node.branch{ks}:
      Shared.Maybe.then(
        Hashes.Hash,
        List<&2, U32>,
        Kids.at(ks, U32.to_nat(x)),
        h => Shared.Maybe.then(
          Node,
          List<&2, U32>,
          Shared.Maybe.then(List<&2, U32>, Node, fetch(s)(h), Node.of),
          m => Tree.go.node(~S, ~fetch, s, r, k, m)
        )
      )

# the value of the key k in the tree whose root is h, in the store s
def Tree.get(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Shared.Maybe.when(
    List<&2, U32>,
    Bool.not(Hashes.Hash.is_eq(h, Tree.none())),
    u => Shared.Maybe.then(
      Node,
      List<&2, U32>,
      Shared.Maybe.then(List<&2, U32>, Node, fetch(s)(h), Node.of),
      n => Tree.go.node(~S, ~fetch, s, Tree.path(k), k, n)
    )
  )

# Writes
# ------

# a new part of a tree: its root, and the words of the nodes that it adds
type Put is Data:
  Put{root: Hashes.Hash, nodes: List<&2, List<&2, U32>>}

# the part that is the node n, after the nodes ns
def Put.node(n: Node, ns: List<&2, List<&2, U32>>) -> Put:
  +ws = Node.words(n)
  Put{Hashes.Sha.hash(ws), ws <> ns}

# a branch whose part x is the part p
def Put.under(x: U32, p: Put) -> Put:
  match p:
    case Put{h, ns}:
      Put.node(Node.branch{Kids.set(Kids.none(), U32.to_nat(x), Some{h})}, ns)

# the part that holds two leaves, of hashes h1 and h2, whose paths below here
# are p1 and p2: branches down to where the paths part, after the nodes ns
def Tree.split(
  p1: List<&2, U32>,
  p2: List<&2, U32>,
  +h1: Hashes.Hash,
  +h2: Hashes.Hash,
  +ns: List<&2, List<&2, U32>>
) -> Put:
  match p1 p2:
    case Con{+a, r1} Con{+b, r2}:
      Shared.Bool.when(
        Put,
        U32.is_eq(a, b),
        u => Put.under(a, Tree.split(r1, r2, h1, h2, ns)),
        u => Put.node(
          Node.branch{
            Kids.set(Kids.set(Kids.none(), U32.to_nat(a), Some{h1}), U32.to_nat(b), Some{h2})
          },
          ns
        )
      )
    case q w:
      Put{h1, ns}

# the node of the hash h, in the store s
def Tree.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Shared.Maybe.then(List<&2, U32>, Node, fetch(s)(h), Node.of)

# the part of a branch's part x, once its new part p is known
def Put.into(ks: List<&2, Maybe<&2, Hashes.Hash>>, x: U32, p: Put) -> Put:
  match p:
    case Put{h, ns}:
      Put.node(Node.branch{Kids.set(ks, U32.to_nat(x), Some{h})}, ns)

# the part that holds the leaf of k and v, whose path below here is p, and the
# leaf of k2 and v2 already there, at depth d
def Tree.put.split(
  p: List<&2, U32>,
  d: Nat,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +k2: List<&2, U32>,
  v2: List<&2, U32>
) -> Put:
  +ws = Node.words(Node.leaf{k, v})
  Tree.split(
    p,
    List.drop(&2, U32, Tree.path(k2), d),
    Hashes.Sha.hash(ws),
    Node.hash(Node.leaf{k2, v2}),
    [ws]
  )

# the part m (none: empty) at depth d, whose path below is p, with the key k
# set to the value v
def Tree.put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, U32>,
  d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, Node>
) -> Put:
  match p m:
    case q None{}:
      Put.node(Node.leaf{k, v}, [])
    case q Some{Node.leaf{+k2, v2}}:
      Shared.Bool.when(
        Put,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Put.node(Node.leaf{k, v}, []),
        w => Tree.put.split(q, d, k, v, k2, v2)
      )
    case Con{+x, r} Some{Node.branch{+ks}}:
      Put.into(
        ks,
        x,
        Tree.put(
          ~S,
          ~fetch,
          s,
          r,
          1n+d,
          k,
          v,
          Shared.Maybe.then(
            Hashes.Hash,
            Node,
            Kids.at(ks, U32.to_nat(x)),
            h => Tree.node(~S, ~fetch, s, h)
          )
        )
      )
    case Nil{} Some{Node.branch{ks}}:
      Put.node(Node.branch{ks}, [])

# the tree whose root is h, in the store s, with the key k set to the value
# v: its new root, and the nodes that it adds
def Tree.set(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> Put:
  Tree.put(
    ~S,
    ~fetch,
    s,
    Tree.path(k),
    0n,
    k,
    v,
    Shared.Bool.when(
      Maybe<&2, Node>,
      Hashes.Hash.is_eq(h, Tree.none()),
      u => None{},
      u => Tree.node(~S, ~fetch, s, h)
    )
  )
