import Base
import ../../shared.bend as Shared
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes

# Ropes
# =====
# A rope holds the content of a resource (a list of words) as a tree of nodes
# in a store of data by hash. The content is cut into leaves, and each level
# of hashes into branches, by a test of the items themselves, so that two
# versions of a big resource share every node that an edit did not touch.

# a node: a leaf holds words of the content; a branch holds the hashes of its
# kids, in order
type Node is Data:
  Node.Leaf{words: List<&2, U32>}
  Node.Branch{kids: List<&2, Hashes.Hash>}

# the root of a rope: how many branch levels are above its leaves, and the
# hash of its top node
type Root is Data:
  Root{depth: Nat, hash: Hashes.Hash}

# a new rope: its root, and the nodes (each as words) that a store must hold
# to read it
type Put is Data:
  Put{root: Root, nodes: List<&2, List<&2, U32>>}

# the root of a new rope
def Put.root(p: Put) -> Root:
  match p:
    case Put{r, ns}:
      r

# the nodes of a new rope
def Put.nodes(p: Put) -> List<&2, List<&2, U32>>:
  match p:
    case Put{r, ns}:
      ns

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

# the code of the kids of a branch
def Kids.codec() -> Codes.Codec(List<&2, Hashes.Hash>):
  Codes.Code.list.codec(~Hashes.Hash, ~Hash.codec())

# the node n, then r: its tag (1: a leaf, 2: a branch), then what it holds
def Node.code(n: Node, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Node.Leaf{ws}:
      1 <> Codes.Codec.enc(List<&2, U32>, Codes.Code.words.codec())(ws)(r)
    case Node.Branch{ks}:
      2 <> Codes.Codec.enc(List<&2, Hashes.Hash>, Kids.codec())(ks)(r)

# a node whose tag is x: a leaf (1) or a branch (2)
def Node.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Node>>,
    U32.is_eq(x, 1),
    u => Codes.Code.one.read(
      ~List<&2, U32>,
      ~Node,
      ~Codes.Codec.dec(List<&2, U32>, Codes.Code.words.codec()),
      ws => Node.Leaf{ws},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Node>>,
      U32.is_eq(x, 2),
      u => Codes.Code.one.read(
        ~List<&2, Hashes.Hash>,
        ~Node,
        ~Codes.Codec.dec(List<&2, Hashes.Hash>, Kids.codec()),
        ks => Node.Branch{ks},
        r
      ),
      u => None{}
    )
  )

# a node
def Node.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Node.code.read.of(x, r)

# the words of the node n: its one code
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

# a node reads back
def Node.code_read(
  n: Node,
  r: List<&2, U32>
) -> {Node.code.read(Node.code(n, r)) == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>}:
  match n:
    case Node.Leaf{ws}:
      Codes.Code.one_read(
        ~List<&2, U32>,
        ~Node,
        ~Codes.Code.words.codec(),
        a => Node.Leaf{a},
        ws,
        r
      )
    case Node.Branch{ks}:
      Codes.Code.one_read(
        ~List<&2, Hashes.Hash>,
        ~Node,
        ~Kids.codec(),
        a => Node.Branch{a},
        ks,
        r
      )

# a node is the node of its words
law Node.of_words:
  for +n: Node
  {Node.of(Node.words(n)) == Some{n}: Maybe<&2, Node>}

def Node.of_words(n):
  %Equal.sym(
    Maybe<&2, Codes.Read<Node>>,
    Node.code.read(Node.words(n)),
    Some{Codes.Read{n, []}},
    Node.code_read(n, [])
  ): {Maybe.bind(&2, Codes.Read<Node>, Node, _, Node.of.read) == Some{n}: Maybe<&2, Node>}
  {==}

# the code of counts
def Count.codec() -> Codes.Codec(Nat):
  (Codes.Code.count, (Codes.Code.count.read, n => r => Codes.Code.count_read(n, r)))

# the root r, then rest: its depth, then its hash
def Root.code(r: Root, rest: List<&2, U32>) -> List<&2, U32>:
  match r:
    case Root{d, h}:
      Codes.Code.count(d, Hash.code(h, rest))

# a root
def Root.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Root>>:
  Codes.Code.two.read(
    ~Nat,
    ~Hashes.Hash,
    ~Root,
    ~Codes.Code.count.read,
    ~Hash.code.read,
    d => h => Root{d, h},
    ts
  )

# a root reads back
def Root.code_read(
  r: Root,
  rest: List<&2, U32>
) -> {Root.code.read(Root.code(r, rest)) == Some{Codes.Read{r, rest}}: Maybe<&2, Codes.Read<Root>>}:
  match r:
    case Root{d, h}:
      Codes.Code.two_read(
        ~Nat,
        ~Hashes.Hash,
        ~Root,
        ~Count.codec(),
        ~Hash.codec(),
        a => b => Root{a, b},
        d,
        h,
        rest
      )

# the code of roots
def Root.codec() -> Codes.Codec(Root):
  (Root.code, (Root.code.read, r => rest => Root.code_read(r, rest)))

# a and b are the same root
def Root.is_eq(a: Root, b: Root) -> Bool:
  match a b:
    case Root{d1, h1} Root{d2, h2}:
      Bool.and(Nat.is_eq(d1, d2), Hashes.Hash.is_eq(h1, h2))

# a root is the same as itself
def Root.is_eq_refl(a: Root) -> {Root.is_eq(a, a) == True{}: Bool}:
  match a:
    case Root{+d, +h}:
      Shared.Bool.and_both(
        Nat.is_eq(d, d),
        Hashes.Hash.is_eq(h, h)
      )(Shared.Nat.is_eq_refl(d))(Hashes.Hash.is_eq_refl(h))

# two roots that are the same are equal
def Root.is_eq_sound(a: Root, b: Root) -> {Root.is_eq(a, b) == True{}: Bool} -> {a == b: Root}:
  match a b:
    case Root{+d1, +h1} Root{+d2, +h2}:
      +e =>
        %Shared.Nat.is_eq_sound(d1, d2)(
          Shared.Bool.and_true_left(Nat.is_eq(d1, d2), Hashes.Hash.is_eq(h1, h2))(e)
        ): {Root{d1, h1} == Root{_, h2}: Root}
        %Hashes.Hash.is_eq_sound(h1, h2)(
          Shared.Bool.and_true_right(Nat.is_eq(d1, d2), Hashes.Hash.is_eq(h1, h2))(e)
        ): {Root{d1, h1} == Root{d1, _}: Root}
        {==}

# Root.is_eq is an equality
def Root.laws() -> Shared.Eq.Laws(Root, Root.is_eq):
  (a => Root.is_eq_refl(a), a => b => Root.is_eq_sound(a, b))

# Cuts
# ----

# x in front of the pieces gs: a new piece if x ends one (e), else the head
# of the first
def Rope.cut.at(-A: Data, e: Bool, x: A, gs: List<&2, List<&2, A>>) -> List<&2, List<&2, A>>:
  match e gs:
    case True{} gs:
      [x] <> gs
    case False{} Nil{}:
      [[x]]
    case False{} Con{g, t}:
      (x <> g) <> t

# xs cut after each element that edge holds of (the last piece may end
# without one)
def Rope.cut(~A: Data, ~edge: A -> Bool, xs: List<&2, A>) -> List<&2, List<&2, A>>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Rope.cut.at(A, edge(x), x, Rope.cut(~A, ~edge, r))

# the pieces of a cut with one more element, one after the other, are the
# element, then the pieces
def Rope.cut.at_flat(
  -A: Data,
  e: Bool,
  x: A,
  gs: List<&2, List<&2, A>>
) -> {List.concat(&2, A, Rope.cut.at(A, e, x, gs)) == x <> List.concat(&2, A, gs): List<&2, A>}:
  match e gs:
    case True{} gs:
      {==}
    case False{} Nil{}:
      {==}
    case False{} Con{g, t}:
      {==}

# the pieces of a cut, one after the other, are what was cut
law Rope.cut_flat:
  for ~A: Data
  for ~edge: A -> Bool
  for xs: List<&2, A>
  {List.concat(&2, A, Rope.cut(~A, ~edge, xs)) == xs: List<&2, A>}

def Rope.cut_flat(ty, edge, xs):
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(
        List<&2, ty>,
        List.concat(&2, ty, Rope.cut.at(ty, edge(x), x, Rope.cut(~ty, ~edge, r))),
        x <> List.concat(&2, ty, Rope.cut(~ty, ~edge, r)),
        Rope.cut.at_flat(ty, edge(x), x, Rope.cut(~ty, ~edge, r))
      ): {_ == x <> r: List<&2, ty>}
      %Rope.cut_flat(~ty, ~edge, r): {x <> List.concat(&2, ty, Rope.cut(~ty, ~edge, r)) == x <> _: List<&2, ty>}
      {==}
