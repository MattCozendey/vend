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
      Tree.go(~S, ~fetch, s, r, k, Tree.kid(~S, ~fetch, s, Kids.at(ks, U32.to_nat(x))))

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

# the part that holds the new leaf of words ws, whose path below here is p1,
# and the part o already there, whose path below here is p2: branches down to
# where the paths part
def Tree.split(
  p1: List<&2, U32>,
  p2: List<&2, U32>,
  +ws: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Put>:
  match p1 p2:
    case Con{a, r1} Con{b, r2}:
      +x = U32.to_nat(a)
      +y = U32.to_nat(b)
      Shared.Bool.when(
        Maybe<&2, Put>,
        Nat.is_eq(x, y),
        u => Shared.Maybe.then(
          Put,
          Put,
          Tree.split(r1, r2, ws, o),
          p => Some{Put.into(Kids.none(), x, p)}
        ),
        u => Some{
          Put.node(
            Node.branch{Kids.set(Kids.set(Kids.none(), x, Some{Hashes.Sha.hash(ws)}), y, o)},
            [ws]
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
  p: List<&2, U32>,
  d: Nat,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  o: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Node>
) -> Maybe<&2, Put>:
  match p m:
    case q None{}:
      None{}
    case q Some{Node.empty{}}:
      Some{Put.node(Node.leaf{k, v}, [])}
    case q Some{Node.leaf{+k2, v2}}:
      Shared.Bool.when(
        Maybe<&2, Put>,
        Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
        u => Some{Put.node(Node.leaf{k, v}, [])},
        w => Tree.split(q, List.drop(&2, U32, Tree.path(k2), d), Node.words(Node.leaf{k, v}), o)
      )
    case Con{x, r} Some{Node.branch{+ks}}:
      +n = U32.to_nat(x)
      +kid = Kids.at(ks, n)
      Shared.Maybe.then(
        Put,
        Put,
        Tree.put(~S, ~fetch, s, r, 1n+d, k, v, kid, Tree.kid(~S, ~fetch, s, kid)),
        p2 => Some{Put.into(ks, n, p2)}
      )
    case Nil{} Some{Node.branch{ks}}:
      None{}

# the tree whose root is h, in the store s, with the key k set to the value
# v: its new root, and the nodes that it adds
def Tree.set(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  v: List<&2, U32>
) -> Maybe<&2, Put>:
  Tree.put(~S, ~fetch, s, Tree.path(k), 0n, k, v, Some{h}, Tree.node(~S, ~fetch, s, h))

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

# what a read of the key k along p gives at the root of the new part r
# (none: a write that failed), in any store s2 that holds its nodes: w
def Tree.Reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s2: S,
  p: List<&2, U32>,
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
  -pi: List<&2, U32>,
  -po: List<&2, U32>,
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
  p: List<&2, U32>,
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

# a new branch of parts ks whose part x is the new part q reads along x then
# r as q reads along r
def Tree.read_into(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +ks: List<&2, Maybe<&2, Hashes.Hash>>,
  +x: U32,
  r: List<&2, U32>,
  k: List<&2, U32>,
  -w: Maybe<&2, List<&2, U32>>,
  +q: Put,
  ih: Tree.Reads(~S, ~fetch, s2, r, k, w, Some{q})
) -> Tree.Reads(~S, ~fetch, s2, Con{x, r}, k, w, Some{Put.into(ks, U32.to_nat(x), q)}):
  +e =>
    +b = {Node.branch{Kids.set(ks, U32.to_nat(x), Some{Put.root(q)})}: Node}
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
      Maybe<&2, Hashes.Hash>,
      Kids.at(Kids.set(ks, U32.to_nat(x), Some{Put.root(q)}), U32.to_nat(x)),
      Some{Put.root(q)},
      Kids.at_set(ks, U32.to_nat(x), Some{Put.root(q)})
    ): {Tree.go(~S, ~fetch, s2, r, k, Tree.kid(~S, ~fetch, s2, _)) == w: Maybe<&2, List<&2, U32>>}
    ih(Shared.List.all.if_rest(Tree.has(~S, ~fetch, s2, Node.words(b)), u => rest)(e))

# the part c of Tree.split, with the new leaf of k and v, reads as v along a
# then r1
def Tree.read_split.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s2: S,
  +a: U32,
  +r1: List<&2, U32>,
  +b: U32,
  r2: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  c: Bool,
  ec: {Nat.is_eq(U32.to_nat(a), U32.to_nat(b)) == c: Bool},
  ih: Tree.Reads(~S, ~fetch, s2, r1, k, Some{v}, Tree.split(r1, r2, Node.words(Node.leaf{k, v}), o))
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
      Tree.split(r1, r2, Node.words(Node.leaf{k, v}), o),
      p => Some{Put.into(Kids.none(), U32.to_nat(a), p)}
    ),
    u => Some{
      Put.node(
        Node.branch{
          Kids.set(
            Kids.set(Kids.none(), U32.to_nat(a), Some{Node.hash(Node.leaf{k, v})}),
            U32.to_nat(b),
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
      Tree.reads_then(
        ~S,
        ~fetch,
        s2,
        r1,
        Con{a, r1},
        k,
        Some{v},
        Some{v},
        Tree.split(r1, r2, Node.words(Node.leaf{k, v}), o),
        p => Some{Put.into(Kids.none(), U32.to_nat(a), p)},
        q => iq => Tree.read_into(~S, ~fetch, s2, Kids.none(), a, r1, k, Some{v}, q, iq),
        ih
      )
    case False{}:
      +e =>
        +l = {Node.leaf{k, v}: Node}
        +ka = Kids.set(Kids.none(), U32.to_nat(a), Some{Node.hash(l)})
        +n = {Node.branch{Kids.set(ka, U32.to_nat(b), o)}: Node}
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
          Kids.at(Kids.set(ka, U32.to_nat(b), o), U32.to_nat(a)),
          Kids.at(ka, U32.to_nat(a)),
          Kids.at_other(ka, U32.to_nat(a), U32.to_nat(b), o, ec)
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
          Kids.at(ka, U32.to_nat(a)),
          Some{Node.hash(l)},
          Kids.at_set(Kids.none(), U32.to_nat(a), Some{Node.hash(l)})
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
  p1: List<&2, U32>,
  p2: List<&2, U32>,
  +o: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> Tree.Reads(~S, ~fetch, s2, p1, k, Some{v}, Tree.split(p1, p2, Node.words(Node.leaf{k, v}), o)):
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
        Nat.is_eq(U32.to_nat(a), U32.to_nat(b)),
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
  q: List<&2, U32>,
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
    w => Tree.split(q, List.drop(&2, U32, Tree.path(k2), d), Node.words(Node.leaf{k, v}), o)
  )
):
  match c:
    case True{}:
      Tree.read_new_leaf(~S, ~fetch, s2, q, k, v)
    case False{}:
      Tree.read_split(~S, ~fetch, s2, q, List.drop(&2, U32, Tree.path(k2), d), o, k, v)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- a binder of an erased argument of a proof; a proof does not run
# Tree.put from the part m of the store s, with k set to v, reads as v along
# p, in any store s2 that holds its nodes
def Tree.read_put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +s2: S,
  p: List<&2, U32>,
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
      +kid = Kids.at(ks, U32.to_nat(x))
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
        p2 => Some{Put.into(ks, U32.to_nat(x), p2)},
        q => iq => Tree.read_into(~S, ~fetch, s2, ks, x, r, k, Some{v}, q, iq),
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
  for +h: Hashes.Hash
  for +k: List<&2, U32>
  for v: List<&2, U32>
  for t: Put
  {Tree.set(~S, ~fetch, s, h, k, v) == Some{t}: Maybe<&2, Put>}
    -> {Tree.holds(~S, ~fetch, s2, Put.nodes(t)) == True{}: Bool}
    -> {Tree.get(~S, ~fetch, s2, Put.root(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}

def Tree.get_set(ty, fetch, s, s2, h, k, v, t):
  e =>
    %e: Tree.Reads(~ty, ~fetch, s2, Tree.path(k), k, Some{v}, _)
    Tree.read_put(~ty, ~fetch, s, s2, Tree.path(k), 0n, k, v, Some{h}, Tree.node(~ty, ~fetch, s, h))

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
  p: List<&2, U32>,
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
          Tree.kid(~S, ~fetch, a, Kids.at(ks, U32.to_nat(y))),
          Tree.kid(~S, ~fetch, b, Kids.at(ks, U32.to_nat(y))),
          x,
          n => Tree.kid_kept(~S, ~fetch, ~grows, ~kept, a, b, Kids.at(ks, U32.to_nat(y)), n, gr),
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
  for +h: Hashes.Hash
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
    Tree.node(~ty, ~fetch, a, h),
    Tree.node(~ty, ~fetch, b, h),
    x,
    n => Tree.node_kept(~ty, ~fetch, ~grows, ~kept, a, b, h, n, gr),
    gr
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
