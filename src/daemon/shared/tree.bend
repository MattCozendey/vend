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

# a node: the empty tree, a leaf, which holds one key and its value, or a
# branch, which holds the root of each of its 16 parts (none: empty)
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
    case Node.empty{}:
      0 <> r
    case Node.leaf{k, v}:
      1 <> Words.code(k, Words.code(v, r))
    case Node.branch{ks}:
      2 <> Kids.code(ks, r)

# a leaf (tag 1) or a branch (other tags), whose tag is x
def Node.code.read.full(x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
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

# a node
def Node.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Node>>,
        U32.is_eq(x, 0),
        u => Some{Codes.Read{Node.empty{}, r}},
        u => Node.code.read.full(x, r)
      )

# the words of the node n
def Node.words(n: Node) -> List<&2, U32>:
  Node.code(n, [])

# the hash of the node n
def Node.hash(n: Node) -> Hashes.Hash:
  Hashes.Sha.hash(Node.words(n))

# the hash of the empty tree
def Tree.none() -> Hashes.Hash:
  Node.hash(Node.empty{})

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

# the node of the hash h, in the store s
def Tree.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Shared.Maybe.then(List<&2, U32>, Node, fetch(s)(h), Node.of)

# the value of the key k in the node m (none: not in the store), whose path
# below it is p
def Tree.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, U32>,
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
      Tree.go(
        ~S,
        ~fetch,
        s,
        r,
        k,
        Shared.Maybe.then(
          Hashes.Hash,
          Node,
          Kids.at(ks, U32.to_nat(x)),
          h => Tree.node(~S, ~fetch, s, h)
        )
      )

# the value of the key k in the tree whose root is h, in the store s
def Tree.get(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Hashes.Hash,
  +k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Tree.go(~S, ~fetch, s, Tree.path(k), k, Tree.node(~S, ~fetch, s, h))

# Writes
# ------

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

# the part that holds two leaves, of hashes h1 and h2, whose paths below here
# are p1 and p2: branches down to where the paths part
def Tree.split(p1: List<&2, U32>, p2: List<&2, U32>, +h1: Hashes.Hash, +h2: Hashes.Hash) -> Put:
  match p1 p2:
    case Con{a, r1} Con{b, r2}:
      +x = U32.to_nat(a)
      +y = U32.to_nat(b)
      Shared.Bool.when(
        Put,
        Nat.is_eq(x, y),
        u => Put.into(Kids.none(), x, Tree.split(r1, r2, h1, h2)),
        u => Put.node(Node.branch{Kids.set(Kids.set(Kids.none(), x, Some{h1}), y, Some{h2})}, [])
      )
    case q w:
      Put{h1, []}

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
  +sp = Tree.split(
    p,
    List.drop(&2, U32, Tree.path(k2), d),
    Hashes.Sha.hash(ws),
    Node.hash(Node.leaf{k2, v2})
  )
  Put{Put.root(sp), ws <> Put.nodes(sp)}

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
    case q Some{Node.empty{}}:
      Put.node(Node.leaf{k, v}, [])
    case q Some{Node.leaf{+k2, v2}}:
      Shared.Bool.when(
        Put,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Put.node(Node.leaf{k, v}, []),
        w => Tree.put.split(q, d, k, v, k2, v2)
      )
    case Con{x, r} Some{Node.branch{+ks}}:
      +n = U32.to_nat(x)
      Put.into(
        ks,
        n,
        Tree.put(
          ~S,
          ~fetch,
          s,
          r,
          1n+d,
          k,
          v,
          Shared.Maybe.then(Hashes.Hash, Node, Kids.at(ks, n), h => Tree.node(~S, ~fetch, s, h))
        )
      )
    case Nil{} Some{Node.branch{ks}}:
      Put.node(Node.leaf{k, v}, [])

# the tree whose root is h, in the store s, with the key k set to the value
# v: its new root, and the nodes that it adds
def Tree.set(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Hashes.Hash,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> Put:
  Tree.put(~S, ~fetch, s, Tree.path(k), 0n, k, v, Tree.node(~S, ~fetch, s, h))

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

# the code of words
def Words.codec() -> Codes.Codec(List<&2, U32>):
  Codes.Code.list.codec(~U32, ~Codes.Code.token.codec())

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
        ~Words.codec(),
        ~Words.codec(),
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

# setting the part b does not change the part a, another part
def Kids.at_other(
  ks: List<&2, Maybe<&2, Hashes.Hash>>,
  a: Nat,
  b: Nat,
  y: Maybe<&2, Hashes.Hash>,
  e: {Nat.is_eq(a, b) == False{}: Bool}
) -> {Kids.at(Kids.set(ks, b, y), a) == Kids.at(ks, a): Maybe<&2, Hashes.Hash>}:
  match ks a b:
    case Nil{} 0n 0n:
      Empty.absurd(
        {Kids.at(Kids.set([], 0n, y), 0n) == None{}: Maybe<&2, Hashes.Hash>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Nil{} 0n 1n+q:
      {==}
    case Nil{} 1n+p 0n:
      {==}
    case Nil{} 1n+p 1n+q:
      Kids.at_other([], p, q, y, e)
    case Con{x, r} 0n 0n:
      Empty.absurd(
        {Kids.at(Kids.set(Con{x, r}, 0n, y), 0n) == x: Maybe<&2, Hashes.Hash>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Con{x, r} 0n 1n+q:
      {==}
    case Con{x, r} 1n+p 0n:
      {==}
    case Con{x, r} 1n+p 1n+q:
      Kids.at_other(r, p, q, y, e)

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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
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

# a read of the key k at the leaf of k and v gives v
def Tree.read_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  p: List<&2, U32>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {Tree.go(~S, ~fetch, s, p, k, Some{Node.leaf{k, v}}) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
        True{},
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
      ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == Some{v}: Maybe<&2, List<&2, U32>>}
      {==}
    case Con{x, r}:
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
        True{},
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k)
      ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{v}) == Some{v}: Maybe<&2, List<&2, U32>>}
      {==}

# a read of the key k at the new leaf of k and v gives v, when the store
# holds it
def Tree.read_new_leaf(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: List<&2, U32>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  e: {Tree.holds(~S, ~fetch, s, Put.nodes(Put.node(Node.leaf{k, v}, []))) == True{}: Bool}
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    p,
    k,
    Tree.node(~S, ~fetch, s, Put.root(Put.node(Node.leaf{k, v}, [])))
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Node>,
    Tree.node(~S, ~fetch, s, Node.hash(Node.leaf{k, v})),
    Some{Node.leaf{k, v}},
    Tree.has_node(
      ~S,
      ~fetch,
      s,
      Node.leaf{k, v},
      Shared.List.all.if_hit(Tree.has(~S, ~fetch, s, Node.words(Node.leaf{k, v})), u => True{})(e)
    )
  ): {Tree.go(~S, ~fetch, s, p, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
  Tree.read_leaf(~S, ~fetch, s, p, k, v)

# a read of the key k along x then r, at a new branch of parts ks whose part
# x is the new part p, is a read along r at p, when the store holds them
def Tree.read_into(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +x: U32,
  r: List<&2, U32>,
  k: List<&2, U32>,
  -v: List<&2, U32>,
  +p: Put,
  ih: {
    Tree.holds(~S, ~fetch, s, Put.nodes(p)) == True{}: Bool
  } -> {
    Tree.go(
      ~S,
      ~fetch,
      s,
      r,
      k,
      Tree.node(~S, ~fetch, s, Put.root(p))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  +e: {Tree.holds(~S, ~fetch, s, Put.nodes(Put.into(ks, U32.to_nat(x), p))) == True{}: Bool}
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    Con{x, r},
    k,
    Tree.node(~S, ~fetch, s, Put.root(Put.into(ks, U32.to_nat(x), p)))
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  +b = {Node.branch{Kids.set(ks, U32.to_nat(x), Some{Put.root(p)})}: Node}
  +rest = Tree.holds(~S, ~fetch, s, Put.nodes(p))
  %Equal.sym(
    Maybe<&2, Node>,
    Tree.node(~S, ~fetch, s, Node.hash(b)),
    Some{b},
    Tree.has_node(
      ~S,
      ~fetch,
      s,
      b,
      Shared.List.all.if_hit(Tree.has(~S, ~fetch, s, Node.words(b)), u => rest)(e)
    )
  ): {Tree.go(~S, ~fetch, s, Con{x, r}, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Kids.at(Kids.set(ks, U32.to_nat(x), Some{Put.root(p)}), U32.to_nat(x)),
    Some{Put.root(p)},
    Kids.at_set(ks, U32.to_nat(x), Some{Put.root(p)})
  ): {
    Tree.go(
      ~S,
      ~fetch,
      s,
      r,
      k,
      Shared.Maybe.then(Hashes.Hash, Node, _, h => Tree.node(~S, ~fetch, s, h))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  ih(Shared.List.all.if_rest(Tree.has(~S, ~fetch, s, Node.words(b)), u => rest)(e))

# a read along a then r1 at the part c of Tree.split that holds the new leaf
# of k and v, of hash h1, gives v, when the store holds them
def Tree.read_split.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +a: U32,
  +r1: List<&2, U32>,
  +b: U32,
  r2: List<&2, U32>,
  +h1: Hashes.Hash,
  +h2: Hashes.Hash,
  k: List<&2, U32>,
  v: List<&2, U32>,
  c: Bool,
  ec: {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == c: Bool},
  ih: {
    Tree.holds(~S, ~fetch, s, Put.nodes(Tree.split(r1, r2, h1, h2))) == True{}: Bool
  } -> {
    Tree.go(
      ~S,
      ~fetch,
      s,
      r1,
      k,
      Tree.node(~S, ~fetch, s, Put.root(Tree.split(r1, r2, h1, h2)))
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  },
  e1: {Tree.node(~S, ~fetch, s, h1) == Some{Node.leaf{k, v}}: Maybe<&2, Node>}
) -> {
  Tree.holds(
    ~S,
    ~fetch,
    s,
    Put.nodes(
      Shared.Bool.when(
        Put,
        c,
        u => Put.into(Kids.none(), U32.to_nat(a), Tree.split(r1, r2, h1, h2)),
        u => Put.node(
          Node.branch{
            Kids.set(Kids.set(Kids.none(), U32.to_nat(a), Some{h1}), U32.to_nat(b), Some{h2})
          },
          []
        )
      )
    )
  )
    == True{}: Bool
} -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    Con{a, r1},
    k,
    Tree.node(
      ~S,
      ~fetch,
      s,
      Put.root(
        Shared.Bool.when(
          Put,
          c,
          u => Put.into(Kids.none(), U32.to_nat(a), Tree.split(r1, r2, h1, h2)),
          u => Put.node(
            Node.branch{
              Kids.set(Kids.set(Kids.none(), U32.to_nat(a), Some{h1}), U32.to_nat(b), Some{h2})
            },
            []
          )
        )
      )
    )
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match c:
    case True{}:
      e => Tree.read_into(
        ~S,
        ~fetch,
        s,
        Kids.none(),
        a,
        r1,
        k,
        v,
        Tree.split(r1, r2, h1, h2),
        ih,
        e
      )
    case False{}:
      e =>
        +ka = Kids.set(Kids.none(), U32.to_nat(a), Some{h1})
        +n = {Node.branch{Kids.set(ka, U32.to_nat(b), Some{h2})}: Node}
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, Node.hash(n)),
          Some{n},
          Tree.has_node(
            ~S,
            ~fetch,
            s,
            n,
            Shared.List.all.if_hit(Tree.has(~S, ~fetch, s, Node.words(n)), u => True{})(e)
          )
        ): {Tree.go(~S, ~fetch, s, Con{a, r1}, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(Kids.set(ka, U32.to_nat(b), Some{h2}), U32.to_nat(a)),
          Kids.at(ka, U32.to_nat(a)),
          Kids.at_other(ka, U32.to_nat(a), U32.to_nat(b), Some{h2}, ec)
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s,
            r1,
            k,
            Shared.Maybe.then(Hashes.Hash, Node, _, h => Tree.node(~S, ~fetch, s, h))
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Hashes.Hash>,
          Kids.at(ka, U32.to_nat(a)),
          Some{h1},
          Kids.at_set(Kids.none(), U32.to_nat(a), Some{h1})
        ): {
          Tree.go(
            ~S,
            ~fetch,
            s,
            r1,
            k,
            Shared.Maybe.then(Hashes.Hash, Node, _, h => Tree.node(~S, ~fetch, s, h))
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Maybe<&2, Node>,
          Tree.node(~S, ~fetch, s, h1),
          Some{Node.leaf{k, v}},
          e1
        ): {Tree.go(~S, ~fetch, s, r1, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
        Tree.read_leaf(~S, ~fetch, s, r1, k, v)

# a read along p1 at Tree.split that holds the new leaf of k and v, of hash
# h1, gives v, when the store holds them
def Tree.read_split(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p1: List<&2, U32>,
  p2: List<&2, U32>,
  +h1: Hashes.Hash,
  +h2: Hashes.Hash,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +e1: {Tree.node(~S, ~fetch, s, h1) == Some{Node.leaf{k, v}}: Maybe<&2, Node>},
  e: {Tree.holds(~S, ~fetch, s, Put.nodes(Tree.split(p1, p2, h1, h2))) == True{}: Bool}
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s,
    p1,
    k,
    Tree.node(~S, ~fetch, s, Put.root(Tree.split(p1, p2, h1, h2)))
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match p1 p2:
    case Con{+a, +r1} Con{+b, +r2}:
      Tree.read_split.when(
        ~S,
        ~fetch,
        s,
        a,
        r1,
        b,
        r2,
        h1,
        h2,
        k,
        v,
        Nat.is_eq(U32.to_nat(a), U32.to_nat(b)),
        {==},
        h => Tree.read_split(~S, ~fetch, s, r1, r2, h1, h2, k, v, e1, h),
        e1
      )(e)
    case Con{a, r1} Nil{}:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.node(~S, ~fetch, s, h1),
        Some{Node.leaf{k, v}},
        e1
      ): {Tree.go(~S, ~fetch, s, Con{a, r1}, k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
      Tree.read_leaf(~S, ~fetch, s, Con{a, r1}, k, v)
    case Nil{} w:
      %Equal.sym(
        Maybe<&2, Node>,
        Tree.node(~S, ~fetch, s, h1),
        Some{Node.leaf{k, v}},
        e1
      ): {Tree.go(~S, ~fetch, s, [], k, _) == Some{v}: Maybe<&2, List<&2, U32>>}
      Tree.read_leaf(~S, ~fetch, s, [], k, v)

# a read of the key k along q at the part c of Tree.put, at a leaf of k2 and
# v2, gives v, when the store s2 holds the new nodes
def Tree.read_put.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +q: List<&2, U32>,
  d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +k2: List<&2, U32>,
  v2: List<&2, U32>,
  c: Bool,
  +e: {
    Tree.holds(
      ~S,
      ~fetch,
      s2,
      Put.nodes(
        Shared.Bool.when(
          Put,
          c,
          u => Put.node(Node.leaf{k, v}, []),
          w => Tree.put.split(q, d, k, v, k2, v2)
        )
      )
    )
      == True{}: Bool
  }
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s2,
    q,
    k,
    Tree.node(
      ~S,
      ~fetch,
      s2,
      Put.root(
        Shared.Bool.when(
          Put,
          c,
          u => Put.node(Node.leaf{k, v}, []),
          w => Tree.put.split(q, d, k, v, k2, v2)
        )
      )
    )
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match c:
    case True{}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v, e)
    case False{}:
      +l = {Node.leaf{k, v}: Node}
      +p2 = List.drop(&2, U32, Tree.path(k2), d)
      +h2 = Node.hash(Node.leaf{k2, v2})
      +ns = Tree.holds(~S, ~fetch, s2, Put.nodes(Tree.split(q, p2, Node.hash(l), h2)))
      Tree.read_split(
        ~S,
        ~fetch,
        s2,
        q,
        p2,
        Node.hash(l),
        h2,
        k,
        v,
        Tree.has_node(
          ~S,
          ~fetch,
          s2,
          l,
          Shared.List.all.if_hit(Tree.has(~S, ~fetch, s2, Node.words(l)), u => ns)(e)
        ),
        Shared.List.all.if_rest(Tree.has(~S, ~fetch, s2, Node.words(l)), u => ns)(e)
      )

# a read of the key k along p at the part that Tree.put makes from the part m
# of the store s, with k set to v, gives v, when the store s2 holds the new
# nodes
def Tree.read_put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +s2: S,
  p: List<&2, U32>,
  +d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, Node>,
  e: {Tree.holds(~S, ~fetch, s2, Put.nodes(Tree.put(~S, ~fetch, s, p, d, k, v, m))) == True{}: Bool}
) -> {
  Tree.go(
    ~S,
    ~fetch,
    s2,
    p,
    k,
    Tree.node(~S, ~fetch, s2, Put.root(Tree.put(~S, ~fetch, s, p, d, k, v, m)))
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  match p m:
    case q None{}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v, e)
    case q Some{Node.empty{}}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v, e)
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
        v2,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        e
      )
    case Con{+x, +r} Some{Node.branch{+ks}}:
      Tree.read_into(
        ~S,
        ~fetch,
        s2,
        ks,
        x,
        r,
        k,
        v,
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
        ),
        h => Tree.read_put(
          ~S,
          ~fetch,
          s,
          s2,
          r,
          1n+d,
          k,
          v,
          Shared.Maybe.then(
            Hashes.Hash,
            Node,
            Kids.at(ks, U32.to_nat(x)),
            h => Tree.node(~S, ~fetch, s, h)
          ),
          h
        ),
        e
      )
    case Nil{} Some{Node.branch{ks}}:
      Tree.read_new_leaf(~S, ~fetch, s2, [], k, v, e)

# after the key k is set to v in the tree whose root is h in the store s, a
# read of k at the new root gives v, in any store s2 that holds the new nodes
law Tree.get_set:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for s2: S
  for h: Hashes.Hash
  for +k: List<&2, U32>
  for v: List<&2, U32>
  for e: {Tree.holds(~S, ~fetch, s2, Put.nodes(Tree.set(~S, ~fetch, s, h, k, v))) == True{}: Bool}
  {
    Tree.get(
      ~S,
      ~fetch,
      s2,
      Put.root(Tree.set(~S, ~fetch, s, h, k, v)),
      k
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }

def Tree.get_set(ty, fetch, s, s2, h, k, v, e):
  Tree.read_put(~ty, ~fetch, s, s2, Tree.path(k), 0n, k, v, Tree.node(~ty, ~fetch, s, h), e)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
