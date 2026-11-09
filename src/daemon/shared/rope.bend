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

# Stores
# ------

# the store s holds the words ws, under their hash
def Rope.has(
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
def Rope.holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ns: List<&2, List<&2, U32>>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{ws, r}:
      List.all.if(u => Rope.holds(~S, ~fetch, s, r), Rope.has(~S, ~fetch, s, ws))

# that a store b, which grows from a store a (grows), gives the words that a
# gives
def Rope.Keeps(
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

# the node that the store s holds under the hash h
def Rope.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Maybe.bind(&2, List<&2, U32>, Node, fetch(s)(h), Node.of)

# Reads
# -----

# the words of a leaf
def Node.leaf(n: Node) -> Maybe<&2, List<&2, U32>>:
  match n:
    case Node.Leaf{ws}:
      Some{ws}
    case Node.Branch{ks}:
      None{}

# the kids of a branch
def Node.kids(n: Node) -> Maybe<&2, List<&2, Hashes.Hash>>:
  match n:
    case Node.Leaf{ws}:
      None{}
    case Node.Branch{ks}:
      Some{ks}

# what the nodes under the hashes hs hold (the part of each), one after the
# other
def Rope.level(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~A: Data,
  ~part: Node -> Maybe<&2, List<&2, A>>,
  +s: S,
  hs: List<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, A>>:
  match hs:
    case Nil{}:
      Some{[]}
    case Con{h, r}:
      Maybe.bind(
        &2,
        List<&2, A>,
        List<&2, A>,
        Maybe.bind(&2, Node, List<&2, A>, Rope.node(~S, ~fetch, s, h), part),
        x => Maybe.bind(
          &2,
          List<&2, A>,
          List<&2, A>,
          Rope.level(~S, ~fetch, ~A, ~part, s, r),
          y => Some{List.append(&2, A, x, y)}
        )
      )

# the content below the nodes under the hashes hs, which have d branch levels
# above their leaves
def Rope.read.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  d: Nat,
  +s: S,
  hs: List<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, U32>>:
  match d:
    case 0n:
      Rope.level(~S, ~fetch, ~U32, ~Node.leaf, s, hs)
    case 1n+p:
      Maybe.bind(
        &2,
        List<&2, Hashes.Hash>,
        List<&2, U32>,
        Rope.level(~S, ~fetch, ~Hashes.Hash, ~Node.kids, s, hs),
        ks => Rope.read.go(~S, ~fetch, p, s, ks)
      )

# the content of the rope whose root is r, in the store s (none: s lacks a
# node, or a node is not in its one code)
def Rope.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  r: Root
) -> Maybe<&2, List<&2, U32>>:
  match r:
    case Root{d, h}:
      Rope.read.go(~S, ~fetch, d, s, [h])

# Puts
# ----

# the chunk c ends a leaf, by its words mixed into x: the top 5 bits of the
# mix are 0
def Chunk.is_edge.go(c: List<&2, U32>, x: U32) -> Bool:
  match c:
    case Nil{}:
      U32.is_eq(U32.and(x, 4160749568), 0)
    case Con{w, r}:
      Chunk.is_edge.go(r, U32.mul(U32.xor(x, w), 2654435761))

# the chunk c ends a leaf: one chunk in about 32 does
def Chunk.is_edge(c: List<&2, U32>) -> Bool:
  Chunk.is_edge.go(c, 0)

# the hash h ends a branch: one hash in about 32 does
def Hash.is_edge(h: Hashes.Hash) -> Bool:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      U32.is_eq(U32.and(a, 31), 0)

# each of the pieces gs, as one list
def Rope.joins(gs: List<&2, List<&2, List<&2, U32>>>) -> List<&2, List<&2, U32>>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      List.concat(&2, U32, g) <> Rope.joins(r)

# the words of each leaf of the chunks cs: the chunks cut at their edges (no
# chunks: one leaf with no words)
def Rope.leaves(cs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      [[]]
    case Con{c, r}:
      Rope.joins(Rope.cut(~List<&2, U32>, ~Chunk.is_edge, Con{c, r}))

# the hashes of the nodes that mk makes of each of gs
def Rope.hashes(
  ~A: Data,
  ~mk: List<&2, A> -> Node,
  gs: List<&2, List<&2, A>>
) -> List<&2, Hashes.Hash>:
  match gs:
    case Nil{}:
      []
    case Con{g, r}:
      Node.hash(mk(g)) <> Rope.hashes(~A, ~mk, r)

# the words of the nodes that mk makes of each of gs, then acc
def Rope.codes(
  ~A: Data,
  ~mk: List<&2, A> -> Node,
  gs: List<&2, List<&2, A>>,
  acc: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match gs:
    case Nil{}:
      acc
    case Con{g, r}:
      Node.words(mk(g)) <> Rope.codes(~A, ~mk, r, acc)

# a leaf of the words ws
def Node.leaf.of(ws: List<&2, U32>) -> Node:
  Node.Leaf{ws}

# a branch of the kids ks
def Node.branch.of(ks: List<&2, Hashes.Hash>) -> Node:
  Node.Branch{ks}

# the rope whose top is one branch of the nodes under hs, which have d branch
# levels above their leaves, with the nodes acc
def Rope.put.top(d: Nat, +hs: List<&2, Hashes.Hash>, acc: List<&2, List<&2, U32>>) -> Put:
  Put{
    Root{1n+d, Node.hash(Node.Branch{hs})},
    Rope.codes(~Hashes.Hash, ~Node.branch.of, [hs], acc)
  }

# the rope above the nodes under hs, which have d branch levels above their
# leaves, with the nodes acc: one node is the top; more are cut into the
# branches of the next level, while a level has fewer nodes than the one
# below it and f lasts
def Rope.put.go(
  f: Nat,
  +d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>
) -> Put:
  match f hs:
    case 0n hs:
      Rope.put.top(d, hs, acc)
    case 1n+p Con{h, Nil{}}:
      Put{Root{d, h}, acc}
    case 1n+p hs:
      +gs = Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)
      Shared.Bool.when(
        Put,
        Nat.is_lt(List.length(&2, List<&2, Hashes.Hash>, gs), List.length(&2, Hashes.Hash, hs)),
        u => Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, gs),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, gs, acc)
        ),
        u => Rope.put.top(d, hs, acc)
      )

# the rope of the leaves ls, each the words of one
def Rope.put.of(+ls: List<&2, List<&2, U32>>) -> Put:
  +hs = Rope.hashes(~U32, ~Node.leaf.of, ls)
  Rope.put.go(List.length(&2, Hashes.Hash, hs), 0n, hs, Rope.codes(~U32, ~Node.leaf.of, ls, []))

# the rope of the chunks cs, whose words one after the other are the content
def Rope.put(cs: List<&2, List<&2, U32>>) -> Put:
  Rope.put.of(Rope.leaves(cs))

# Laws
# ----

# a store that holds the words of the node n gives n for its hash
def Rope.has_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +n: Node,
  e: {Rope.has(~S, ~fetch, s, Node.words(n)) == True{}: Bool}
) -> {Rope.node(~S, ~fetch, s, Node.hash(n)) == Some{n}: Maybe<&2, Node>}:
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
  Node.of_words(n)

# a store that holds the nodes of gs, then acc, holds acc
def Rope.holds_acc(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~A: Data,
  ~mk: List<&2, A> -> Node,
  +s: S,
  gs: List<&2, List<&2, A>>,
  +acc: List<&2, List<&2, U32>>
) -> {
  Rope.holds(~S, ~fetch, s, Rope.codes(~A, ~mk, gs, acc)) == True{}: Bool
} -> {Rope.holds(~S, ~fetch, s, acc) == True{}: Bool}:
  match gs:
    case Nil{}:
      e => e
    case Con{+g, +r}:
      e => Rope.holds_acc(~S, ~fetch, ~A, ~mk, s, r, acc)(
        Shared.List.all.if_rest(
          Rope.has(~S, ~fetch, s, Node.words(mk(g))),
          u => Rope.holds(~S, ~fetch, s, Rope.codes(~A, ~mk, r, acc))
        )(e)
      )

# a store that holds the nodes that mk makes of each of gs gives, for their
# hashes, the parts gs one after the other, when the part of a node of mk is
# what it was made of
def Rope.level_put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~A: Data,
  ~part: Node -> Maybe<&2, List<&2, A>>,
  ~mk: List<&2, A> -> Node,
  ~back: @g: List<&2, A> -> {part(mk(g)) == Some{g}: Maybe<&2, List<&2, A>>},
  +s: S,
  gs: List<&2, List<&2, A>>,
  +acc: List<&2, List<&2, U32>>
) -> {
  Rope.holds(~S, ~fetch, s, Rope.codes(~A, ~mk, gs, acc)) == True{}: Bool
} -> {
  Rope.level(~S, ~fetch, ~A, ~part, s, Rope.hashes(~A, ~mk, gs))
    == Some{List.concat(&2, A, gs)}: Maybe<&2, List<&2, A>>
}:
  match gs:
    case Nil{}:
      e => {==}
    case Con{+g, +r}:
      +e =>
        %Equal.sym(
          Maybe<&2, Node>,
          Rope.node(~S, ~fetch, s, Node.hash(mk(g))),
          Some{mk(g)},
          Rope.has_node(
            ~S,
            ~fetch,
            s,
            mk(g),
            Shared.List.all.if_hit(
              Rope.has(~S, ~fetch, s, Node.words(mk(g))),
              u => Rope.holds(~S, ~fetch, s, Rope.codes(~A, ~mk, r, acc))
            )(e)
          )
        ): {
          Maybe.bind(
            &2,
            List<&2, A>,
            List<&2, A>,
            Maybe.bind(&2, Node, List<&2, A>, _, part),
            x => Maybe.bind(
              &2,
              List<&2, A>,
              List<&2, A>,
              Rope.level(~S, ~fetch, ~A, ~part, s, Rope.hashes(~A, ~mk, r)),
              y => Some{List.append(&2, A, x, y)}
            )
          )
            == Some{List.append(&2, A, g, List.concat(&2, A, r))}: Maybe<&2, List<&2, A>>
        }
        %Equal.sym(
          Maybe<&2, List<&2, A>>,
          part(mk(g)),
          Some{g},
          back(g)
        ): {
          Maybe.bind(
            &2,
            List<&2, A>,
            List<&2, A>,
            _,
            x => Maybe.bind(
              &2,
              List<&2, A>,
              List<&2, A>,
              Rope.level(~S, ~fetch, ~A, ~part, s, Rope.hashes(~A, ~mk, r)),
              y => Some{List.append(&2, A, x, y)}
            )
          )
            == Some{List.append(&2, A, g, List.concat(&2, A, r))}: Maybe<&2, List<&2, A>>
        }
        %Equal.sym(
          Maybe<&2, List<&2, A>>,
          Rope.level(~S, ~fetch, ~A, ~part, s, Rope.hashes(~A, ~mk, r)),
          Some{List.concat(&2, A, r)},
          Rope.level_put(~S, ~fetch, ~A, ~part, ~mk, ~back, s, r, acc)(
            Shared.List.all.if_rest(
              Rope.has(~S, ~fetch, s, Node.words(mk(g))),
              u => Rope.holds(~S, ~fetch, s, Rope.codes(~A, ~mk, r, acc))
            )(e)
          )
        ): {
          Maybe.bind(&2, List<&2, A>, List<&2, A>, _, y => Some{List.append(&2, A, g, y)})
            == Some{List.append(&2, A, g, List.concat(&2, A, r))}: Maybe<&2, List<&2, A>>
        }
        {==}

# lists one after the other can be put together in any order
def Rope.append_assoc(
  -A: Data,
  xs: List<&2, A>,
  ys: List<&2, A>,
  zs: List<&2, A>
) -> {
  List.append(&2, A, List.append(&2, A, xs, ys), zs)
    == List.append(&2, A, xs, List.append(&2, A, ys, zs)): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      %Rope.append_assoc(A, r, ys, zs): {
        x <> List.append(&2, A, List.append(&2, A, r, ys), zs) == x <> _: List<&2, A>
      }
      {==}

# the lists of xs then ys, one after the other, are those of xs, then those
# of ys
def Rope.concat_append(
  -A: Data,
  xs: List<&2, List<&2, A>>,
  +ys: List<&2, List<&2, A>>
) -> {
  List.concat(&2, A, List.append(&2, List<&2, A>, xs, ys))
    == List.append(&2, A, List.concat(&2, A, xs), List.concat(&2, A, ys)): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(
        List<&2, A>,
        List.concat(&2, A, List.append(&2, List<&2, A>, r, ys)),
        List.append(&2, A, List.concat(&2, A, r), List.concat(&2, A, ys)),
        Rope.concat_append(A, r, ys)
      ): {
        List.append(&2, A, x, _)
          == List.append(&2, A, List.append(&2, A, x, List.concat(&2, A, r)), List.concat(&2, A, ys)): List<&2, A>
      }
      Equal.sym(
        List<&2, A>,
        List.append(&2, A, List.append(&2, A, x, List.concat(&2, A, r)), List.concat(&2, A, ys)),
        List.append(&2, A, x, List.append(&2, A, List.concat(&2, A, r), List.concat(&2, A, ys))),
        Rope.append_assoc(A, x, List.concat(&2, A, r), List.concat(&2, A, ys))
      )

# the joined pieces gs, one after the other, are the chunks of gs, one after
# the other
def Rope.joins_flat(
  gs: List<&2, List<&2, List<&2, U32>>>
) -> {
  List.concat(&2, U32, Rope.joins(gs))
    == List.concat(&2, U32, List.concat(&2, List<&2, U32>, gs)): List<&2, U32>
}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +r}:
      %Equal.sym(
        List<&2, U32>,
        List.concat(&2, U32, List.append(&2, List<&2, U32>, g, List.concat(&2, List<&2, U32>, r))),
        List.append(&2, U32, List.concat(&2, U32, g), List.concat(&2, U32, List.concat(&2, List<&2, U32>, r))),
        Rope.concat_append(U32, g, List.concat(&2, List<&2, U32>, r))
      ): {List.append(&2, U32, List.concat(&2, U32, g), List.concat(&2, U32, Rope.joins(r))) == _: List<&2, U32>}
      %Rope.joins_flat(r): {
        List.append(&2, U32, List.concat(&2, U32, g), List.concat(&2, U32, Rope.joins(r)))
          == List.append(&2, U32, List.concat(&2, U32, g), _): List<&2, U32>
      }
      {==}

# the leaves of the chunks cs, one after the other, are the content of cs
def Rope.leaves_flat(
  cs: List<&2, List<&2, U32>>
) -> {List.concat(&2, U32, Rope.leaves(cs)) == List.concat(&2, U32, cs): List<&2, U32>}:
  match cs:
    case Nil{}:
      {==}
    case Con{+c, +r}:
      %Rope.cut_flat(~List<&2, U32>, ~Chunk.is_edge, Con{c, r}): {
        List.concat(&2, U32, Rope.joins(Rope.cut(~List<&2, U32>, ~Chunk.is_edge, Con{c, r})))
          == List.concat(&2, U32, _): List<&2, U32>
      }
      Rope.joins_flat(Rope.cut(~List<&2, U32>, ~Chunk.is_edge, Con{c, r}))

# a branch gives back the kids it was made of
def Node.kids_of(
  ks: List<&2, Hashes.Hash>
) -> {Node.kids(Node.branch.of(ks)) == Some{ks}: Maybe<&2, List<&2, Hashes.Hash>>}:
  {==}

# a leaf gives back the words it was made of
def Node.leaf_of(
  ws: List<&2, U32>
) -> {Node.leaf(Node.leaf.of(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}:
  {==}

# a store that holds the branches of the pieces gs of hs reads, a level up,
# under their hashes what it reads under hs
def Rope.up_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -d: Nat,
  +gs: List<&2, List<&2, Hashes.Hash>>,
  -hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S,
  -x: List<&2, U32>,
  flat: {List.concat(&2, Hashes.Hash, gs) == hs: List<&2, Hashes.Hash>},
  pre: {Rope.read.go(~S, ~fetch, d, s, hs) == Some{x}: Maybe<&2, List<&2, U32>>},
  e: {
    Rope.holds(~S, ~fetch, s, Rope.codes(~Hashes.Hash, ~Node.branch.of, gs, acc)) == True{}: Bool
  }
) -> {
  Rope.read.go(~S, ~fetch, 1n+d, s, Rope.hashes(~Hashes.Hash, ~Node.branch.of, gs))
    == Some{x}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, List<&2, Hashes.Hash>>,
    Rope.level(~S, ~fetch, ~Hashes.Hash, ~Node.kids, s, Rope.hashes(~Hashes.Hash, ~Node.branch.of, gs)),
    Some{List.concat(&2, Hashes.Hash, gs)},
    Rope.level_put(
      ~S,
      ~fetch,
      ~Hashes.Hash,
      ~Node.kids,
      ~Node.branch.of,
      ~Node.kids_of,
      s,
      gs,
      acc
    )(e)
  ): {
    Maybe.bind(
      &2,
      List<&2, Hashes.Hash>,
      List<&2, U32>,
      _,
      ks => Rope.read.go(~S, ~fetch, d, s, ks)
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }
  %Equal.sym(
    List<&2, Hashes.Hash>,
    List.concat(&2, Hashes.Hash, gs),
    hs,
    flat
  ): {Rope.read.go(~S, ~fetch, d, s, _) == Some{x}: Maybe<&2, List<&2, U32>>}
  pre

# p holds of a choice between two ropes when it holds of both
def Rope.put.when(
  -p: Put -> Type,
  b: Bool,
  -x: Unit -> Put,
  -y: Unit -> Put,
  px: p(x(Unit{})),
  py: p(y(Unit{}))
) -> p(Shared.Bool.when(Put, b, x, y)):
  match b:
    case True{}:
      px
    case False{}:
      py

# a store that holds the nodes of a rope with a top branch holds the nodes
# it was given
def Rope.put.top_holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S
) -> {
  Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put.top(d, hs, acc))) == True{}: Bool
} -> {Rope.holds(~S, ~fetch, s, acc) == True{}: Bool}:
  e => Rope.holds_acc(~S, ~fetch, ~Hashes.Hash, ~Node.branch.of, s, [hs], acc)(e)

# a store that holds the nodes of a rope with a top branch reads, at its
# root, what it reads under the kids of the top
def Rope.put.top_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S,
  -x: List<&2, U32>,
  pre: {Rope.read.go(~S, ~fetch, d, s, hs) == Some{x}: Maybe<&2, List<&2, U32>>}
) -> {
  Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put.top(d, hs, acc))) == True{}: Bool
} -> {Rope.read(~S, ~fetch, s, Put.root(Rope.put.top(d, hs, acc))) == Some{x}: Maybe<&2, List<&2, U32>>}:
  e => Rope.up_reads(
    ~S,
    ~fetch,
    d,
    [hs],
    hs,
    acc,
    s,
    x,
    Shared.List.append_nil(Hashes.Hash, hs),
    pre,
    e
  )

# a store that holds the nodes of the rope of one more level, or of a top
# branch, holds the nodes it was given, when one that holds the nodes of the
# rope above the next level holds the nodes of that level
def Rope.put.step_holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -p: Nat,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S,
  ih: {
    Rope.holds(
      ~S,
      ~fetch,
      s,
      Put.nodes(
        Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        )
      )
    )
      == True{}: Bool
  } -> {
    Rope.holds(
      ~S,
      ~fetch,
      s,
      Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
    )
      == True{}: Bool
  }
) -> {
  Rope.holds(
    ~S,
    ~fetch,
    s,
    Put.nodes(
      Shared.Bool.when(
        Put,
        Nat.is_lt(
          List.length(&2, List<&2, Hashes.Hash>, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          List.length(&2, Hashes.Hash, hs)
        ),
        u => Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        ),
        u => Rope.put.top(d, hs, acc)
      )
    )
  )
    == True{}: Bool
} -> {Rope.holds(~S, ~fetch, s, acc) == True{}: Bool}:
  Rope.put.when(
    q => {
      Rope.holds(~S, ~fetch, s, Put.nodes(q)) == True{}: Bool
    } -> {Rope.holds(~S, ~fetch, s, acc) == True{}: Bool},
    Nat.is_lt(
      List.length(&2, List<&2, Hashes.Hash>, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
      List.length(&2, Hashes.Hash, hs)
    ),
    u => Rope.put.go(
      p,
      1n+d,
      Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
      Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
    ),
    u => Rope.put.top(d, hs, acc),
    e => Rope.holds_acc(
      ~S,
      ~fetch,
      ~Hashes.Hash,
      ~Node.branch.of,
      s,
      Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs),
      acc
    )(ih(e)),
    Rope.put.top_holds(~S, ~fetch, d, hs, acc, s)
  )

# a store that holds the nodes of a rope holds the nodes it was given
def Rope.put.go_holds(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S
) -> {
  Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put.go(f, d, hs, acc))) == True{}: Bool
} -> {Rope.holds(~S, ~fetch, s, acc) == True{}: Bool}:
  match f hs:
    case 0n hs:
      Rope.put.top_holds(~S, ~fetch, d, hs, acc, s)
    case 1n+p Con{h, Nil{}}:
      e => e
    case 1n+p Nil{}:
      Rope.put.step_holds(
        ~S,
        ~fetch,
        p,
        d,
        [],
        acc,
        s,
        Rope.put.go_holds(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, [])),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, []), acc),
          s
        )
      )
    case 1n+p Con{h, Con{h2, t}}:
      Rope.put.step_holds(
        ~S,
        ~fetch,
        p,
        d,
        Con{h, Con{h2, t}},
        acc,
        s,
        Rope.put.go_holds(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}})),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}}), acc),
          s
        )
      )

# a store that holds the nodes of the rope of one more level, or of a top
# branch, reads at its root what it reads under hs, when one that holds the
# nodes of the rope above the next level holds the nodes of that level, and
# reads at its root what it reads under the hashes of that level
def Rope.put.step_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -p: Nat,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S,
  -x: List<&2, U32>,
  +pre: {Rope.read.go(~S, ~fetch, d, s, hs) == Some{x}: Maybe<&2, List<&2, U32>>},
  hd: {
    Rope.holds(
      ~S,
      ~fetch,
      s,
      Put.nodes(
        Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        )
      )
    )
      == True{}: Bool
  } -> {
    Rope.holds(
      ~S,
      ~fetch,
      s,
      Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
    )
      == True{}: Bool
  },
  ih: {
    Rope.read.go(
      ~S,
      ~fetch,
      1n+d,
      s,
      Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs))
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {
    Rope.holds(
      ~S,
      ~fetch,
      s,
      Put.nodes(
        Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        )
      )
    )
      == True{}: Bool
  } -> {
    Rope.read(
      ~S,
      ~fetch,
      s,
      Put.root(
        Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        )
      )
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }
) -> {
  Rope.holds(
    ~S,
    ~fetch,
    s,
    Put.nodes(
      Shared.Bool.when(
        Put,
        Nat.is_lt(
          List.length(&2, List<&2, Hashes.Hash>, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          List.length(&2, Hashes.Hash, hs)
        ),
        u => Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        ),
        u => Rope.put.top(d, hs, acc)
      )
    )
  )
    == True{}: Bool
} -> {
  Rope.read(
    ~S,
    ~fetch,
    s,
    Put.root(
      Shared.Bool.when(
        Put,
        Nat.is_lt(
          List.length(&2, List<&2, Hashes.Hash>, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          List.length(&2, Hashes.Hash, hs)
        ),
        u => Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        ),
        u => Rope.put.top(d, hs, acc)
      )
    )
  )
    == Some{x}: Maybe<&2, List<&2, U32>>
}:
  Rope.put.when(
    q => {
      Rope.holds(~S, ~fetch, s, Put.nodes(q)) == True{}: Bool
    } -> {Rope.read(~S, ~fetch, s, Put.root(q)) == Some{x}: Maybe<&2, List<&2, U32>>},
    Nat.is_lt(
          List.length(&2, List<&2, Hashes.Hash>, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          List.length(&2, Hashes.Hash, hs)
        ),
    u => Rope.put.go(
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs)),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs), acc)
        ),
    u => Rope.put.top(d, hs, acc),
    +e => ih(
      Rope.up_reads(
        ~S,
        ~fetch,
        d,
        Rope.cut(~Hashes.Hash, ~Hash.is_edge, hs),
        hs,
        acc,
        s,
        x,
        Rope.cut_flat(~Hashes.Hash, ~Hash.is_edge, hs),
        pre,
        hd(e)
      )
    )(e),
    Rope.put.top_reads(~S, ~fetch, d, hs, acc, s, x, pre)
  )

# a store that holds the nodes of a rope reads, at its root, what it reads
# under the hashes the rope was put above
def Rope.put.go_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  -d: Nat,
  +hs: List<&2, Hashes.Hash>,
  +acc: List<&2, List<&2, U32>>,
  +s: S,
  -x: List<&2, U32>,
  pre: {Rope.read.go(~S, ~fetch, d, s, hs) == Some{x}: Maybe<&2, List<&2, U32>>}
) -> {
  Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put.go(f, d, hs, acc))) == True{}: Bool
} -> {
  Rope.read(~S, ~fetch, s, Put.root(Rope.put.go(f, d, hs, acc)))
    == Some{x}: Maybe<&2, List<&2, U32>>
}:
  match f hs:
    case 0n hs:
      Rope.put.top_reads(~S, ~fetch, d, hs, acc, s, x, pre)
    case 1n+p Con{h, Nil{}}:
      e => pre
    case 1n+p Nil{}:
      Rope.put.step_reads(
        ~S,
        ~fetch,
        p,
        d,
        [],
        acc,
        s,
        x,
        pre,
        Rope.put.go_holds(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, [])),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, []), acc),
          s
        ),
        pre2 => Rope.put.go_reads(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, [])),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, []), acc),
          s,
          x,
          pre2
        )
      )
    case 1n+p Con{h, Con{h2, t}}:
      Rope.put.step_reads(
        ~S,
        ~fetch,
        p,
        d,
        Con{h, Con{h2, t}},
        acc,
        s,
        x,
        pre,
        Rope.put.go_holds(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}})),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}}), acc),
          s
        ),
        pre2 => Rope.put.go_reads(
          ~S,
          ~fetch,
          p,
          1n+d,
          Rope.hashes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}})),
          Rope.codes(~Hashes.Hash, ~Node.branch.of, Rope.cut(~Hashes.Hash, ~Hash.is_edge, Con{h, Con{h2, t}}), acc),
          s,
          x,
          pre2
        )
      )

# a store that holds the nodes of the rope of the leaves ls reads it as the
# leaves, one after the other
def Rope.put.of_reads(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ls: List<&2, List<&2, U32>>
) -> {
  Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put.of(ls))) == True{}: Bool
} -> {
  Rope.read(~S, ~fetch, s, Put.root(Rope.put.of(ls)))
    == Some{List.concat(&2, U32, ls)}: Maybe<&2, List<&2, U32>>
}:
  +e => Rope.put.go_reads(
    ~S,
    ~fetch,
    List.length(&2, Hashes.Hash, Rope.hashes(~U32, ~Node.leaf.of, ls)),
    0n,
    Rope.hashes(~U32, ~Node.leaf.of, ls),
    Rope.codes(~U32, ~Node.leaf.of, ls, []),
    s,
    List.concat(&2, U32, ls),
    Rope.level_put(
      ~S,
      ~fetch,
      ~U32,
      ~Node.leaf,
      ~Node.leaf.of,
      ~Node.leaf_of,
      s,
      ls,
      []
    )(
      Rope.put.go_holds(
        ~S,
        ~fetch,
        List.length(&2, Hashes.Hash, Rope.hashes(~U32, ~Node.leaf.of, ls)),
        0n,
        Rope.hashes(~U32, ~Node.leaf.of, ls),
        Rope.codes(~U32, ~Node.leaf.of, ls, []),
        s
      )(e)
    )
  )(e)

# a rope reads back as its content, in any store that holds its nodes
law Rope.read_put:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for +s: S
  for +cs: List<&2, List<&2, U32>>
  {Rope.holds(~S, ~fetch, s, Put.nodes(Rope.put(cs))) == True{}: Bool}
    -> {
      Rope.read(~S, ~fetch, s, Put.root(Rope.put(cs)))
        == Some{List.concat(&2, U32, cs)}: Maybe<&2, List<&2, U32>>
    }

def Rope.read_put(ty, fetch, s, cs):
  e =>
    %Rope.leaves_flat(cs): {
      Rope.read(~ty, ~fetch, s, Put.root(Rope.put(cs))) == Some{_}: Maybe<&2, List<&2, U32>>
    }
    Rope.put.of_reads(~ty, ~fetch, s, Rope.leaves(cs))(e)

# a node that a store gives, a store that grows from it gives too
def Rope.node_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Rope.Keeps(S, fetch, grows),
  +a: S,
  +b: S,
  +h: Hashes.Hash,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Rope.node(~S, ~fetch, a, h) == Some{n}: Maybe<&2, Node>
} -> {Rope.node(~S, ~fetch, b, h) == Some{n}: Maybe<&2, Node>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Node,
    fetch(a)(h),
    fetch(b)(h),
    Node.of,
    Node.of,
    n,
    w => e => kept(a)(b)(h)(w)(gr)(e),
    w => e => e
  )

# what a store gives for a level, a store that grows from it gives too
def Rope.level_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Rope.Keeps(S, fetch, grows),
  ~A: Data,
  ~part: Node -> Maybe<&2, List<&2, A>>,
  +a: S,
  +b: S,
  hs: List<&2, Hashes.Hash>,
  -x: List<&2, A>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Rope.level(~S, ~fetch, ~A, ~part, a, hs) == Some{x}: Maybe<&2, List<&2, A>>
} -> {Rope.level(~S, ~fetch, ~A, ~part, b, hs) == Some{x}: Maybe<&2, List<&2, A>>}:
  match hs:
    case Nil{}:
      e => e
    case Con{+h, +r}:
      Shared.Maybe.bind_kept(
        List<&2, A>,
        List<&2, A>,
        Maybe.bind(&2, Node, List<&2, A>, Rope.node(~S, ~fetch, a, h), part),
        Maybe.bind(&2, Node, List<&2, A>, Rope.node(~S, ~fetch, b, h), part),
        v => Maybe.bind(
          &2,
          List<&2, A>,
          List<&2, A>,
          Rope.level(~S, ~fetch, ~A, ~part, a, r),
          y => Some{List.append(&2, A, v, y)}
        ),
        v => Maybe.bind(
          &2,
          List<&2, A>,
          List<&2, A>,
          Rope.level(~S, ~fetch, ~A, ~part, b, r),
          y => Some{List.append(&2, A, v, y)}
        ),
        x,
        v => Shared.Maybe.bind_kept(
          Node,
          List<&2, A>,
          Rope.node(~S, ~fetch, a, h),
          Rope.node(~S, ~fetch, b, h),
          part,
          part,
          v,
          n => Rope.node_kept(~S, ~fetch, ~grows, ~kept, a, b, h, n, gr),
          n => e => e
        ),
        v => Shared.Maybe.bind_kept(
          List<&2, A>,
          List<&2, A>,
          Rope.level(~S, ~fetch, ~A, ~part, a, r),
          Rope.level(~S, ~fetch, ~A, ~part, b, r),
          y => Some{List.append(&2, A, v, y)},
          y => Some{List.append(&2, A, v, y)},
          x,
          y => Rope.level_kept(~S, ~fetch, ~grows, ~kept, ~A, ~part, a, b, r, y, gr),
          y => e => e
        )
      )

# the content that a store gives below some nodes, a store that grows from it
# gives too
def Rope.read.go_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Rope.Keeps(S, fetch, grows),
  d: Nat,
  +a: S,
  +b: S,
  +hs: List<&2, Hashes.Hash>,
  -x: List<&2, U32>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Rope.read.go(~S, ~fetch, d, a, hs) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Rope.read.go(~S, ~fetch, d, b, hs) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match d:
    case 0n:
      Rope.level_kept(~S, ~fetch, ~grows, ~kept, ~U32, ~Node.leaf, a, b, hs, x, gr)
    case 1n+p:
      Shared.Maybe.bind_kept(
        List<&2, Hashes.Hash>,
        List<&2, U32>,
        Rope.level(~S, ~fetch, ~Hashes.Hash, ~Node.kids, a, hs),
        Rope.level(~S, ~fetch, ~Hashes.Hash, ~Node.kids, b, hs),
        ks => Rope.read.go(~S, ~fetch, p, a, ks),
        ks => Rope.read.go(~S, ~fetch, p, b, ks),
        x,
        v => Rope.level_kept(~S, ~fetch, ~grows, ~kept, ~Hashes.Hash, ~Node.kids, a, b, hs, v, gr),
        ks => Rope.read.go_kept(~S, ~fetch, ~grows, ~kept, p, a, b, ks, x, gr)
      )

# a read that a store gives, a store that grows from it gives too
law Rope.read_grows:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Rope.Keeps(S, fetch, grows)
  for +a: S
  for +b: S
  for r: Root
  for x: List<&2, U32>
  {grows(a, b) == True{}: Bool}
    -> {Rope.read(~S, ~fetch, a, r) == Some{x}: Maybe<&2, List<&2, U32>>}
    -> {Rope.read(~S, ~fetch, b, r) == Some{x}: Maybe<&2, List<&2, U32>>}

def Rope.read_grows(ty, fetch, grows, kept, a, b, r, x):
  match r:
    case Root{d, h}:
      gr => Rope.read.go_kept(~ty, ~fetch, ~grows, ~kept, d, a, b, [h], x, gr)
