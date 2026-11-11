import Base
import ./shared/shared/code.bend as Codes
import ./shared/depot.bend as Depots
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/shared.bend as Shared

# Trees
# =====
# A tree maps keys to values (both lists of words). It is held as nodes in a
# depot of data by hash, and named by the hash of its root (none: the empty
# tree), so two versions share every node that neither changed. This file
# states what a tree must do (Tree.Laws): any structure that obeys the laws is
# a tree. Its root is a function of its bindings alone, so nodes that hold the
# same bindings hold the same root, whatever the order of their writes.
#
# The tree of this file is a Merkle search tree (Mst): each key has a level,
# from the hash of the key, so about one key in 32 is a level up. A node holds
# the keys of one level in its range, in order, and between them the subtrees
# of the keys of lower levels. So the shape is a function of the keys, a read
# or a write visits about log n nodes, a write adds only the nodes on its
# path, and two trees share each subtree whose keys and values they share, so
# a difference costs the nodes that differ.

# what a read of a key finds: its value; that the tree does not hold the key;
# or that the depot lacks the node of a hash, so the read cannot tell yet.
# Found and Absent are final: only Missing changes when the depot gets more
# nodes
type Look is Data:
  Look.Found{value: List<&2, U32>}
  Look.Absent{}
  Look.Missing{hash: Hashes.Hash}

# the value that a read found, if it found one
def Look.value(l: Look) -> Maybe<&2, List<&2, U32>>:
  match l:
    case Look.Found{v}:
      Some{v}
    case _:
      None{}

# what a read found, when it could tell: a value, or that there is none
def Look.known(l: Look) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match l:
    case Look.Found{v}:
      Some{Some{v}}
    case Look.Absent{}:
      Some{None{}}
    case Look.Missing{h}:
      None{}

# the read l is final: it found a value or that there is none
def Look.is_final(l: Look) -> Bool:
  Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, Look.known(l))

# what a read of a key gives after a write of the value m there (none: a
# delete)
def Look.of(m: Maybe<&2, List<&2, U32>>) -> Look:
  match m:
    case None{}:
      Look.Absent{}
    case Some{v}:
      Look.Found{v}

# a key and its value, as a tree lists them
type Binding is Data:
  Binding{key: List<&2, U32>, value: List<&2, U32>}

# a and b are the same binding
def Binding.is_eq(a: Binding, b: Binding) -> Bool:
  match a b:
    case Binding{k1, v1} Binding{k2, v2}:
      List.all.if(
        u => Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2),
        Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2)
      )

# the key of a binding
def Binding.key(b: Binding) -> List<&2, U32>:
  match b:
    case Binding{k, v}:
      k

# what a write gives: the root of the new tree (none: the empty tree), and the
# nodes that it adds, each as words
type Edit is Data:
  Edit{root: Maybe<&2, Hashes.Hash>, nodes: List<&2, List<&2, U32>>}

# the root of the new tree of e
def Edit.root(e: Edit) -> Maybe<&2, Hashes.Hash>:
  match e:
    case Edit{r, ns}:
      r

# the nodes that e adds
def Edit.nodes(e: Edit) -> List<&2, List<&2, U32>>:
  match e:
    case Edit{r, ns}:
      ns

# the key k starts with the words p
def Key.leads(p: List<&2, U32>, k: List<&2, U32>) -> Bool:
  match p k:
    case Nil{} y:
      True{}
    case Con{x, rp} Nil{}:
      False{}
    case Con{+x, rp} Con{+y, rk}:
      List.all.if(u => Key.leads(rp, rk), U32.is_eq(x, y))

# the key a comes before the key b: word by word, and a key before each key
# that it starts
def Key.is_lt(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  match a b:
    case x Nil{}:
      False{}
    case Nil{} Con{y, rb}:
      True{}
    case Con{+x, ra} Con{+y, rb}:
      Bool.or(U32.is_lt(x, y), Bool.and(U32.is_eq(x, y), Key.is_lt(ra, rb)))

# the bindings bs are in the order of their keys, each key once
def Bindings.sorted(bs: List<&2, Binding>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{a, Nil{}}:
      True{}
    case Con{+a, Con{+b, rest}}:
      List.all.if(u => Bindings.sorted(b <> rest), Key.is_lt(Binding.key(a), Binding.key(b)))

# The operations of a tree
# ------------------------

# the operations of a tree in a depot kept as S: what a read of a key finds;
# a write of a key (some value: set it; none: delete it), none when the depot
# lacks a node on the key's path; the bindings whose keys start with a
# prefix, in the order of their keys (none: the depot lacks a node); and the
# keys that two trees read differently (none: the depot lacks a node)
def Tree.Ops(-S: Data) -> Type:
  (S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Look)
    & (
      (S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Maybe<&2, List<&2, U32>> -> Maybe<&2, Edit>)
        & (
          (S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Maybe<&2, List<&2, Binding>>)
            & (S -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, List<&2, List<&2, U32>>>)
        )
    )

# what a read finds, by the operations o
def Ops.look(-S: Data, o: Tree.Ops(S)) -> S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Look:
  match o:
    case Tuple{lk, rest}:
      lk

# a write, by the operations o
def Ops.put(
  -S: Data,
  o: Tree.Ops(S)
) -> S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Maybe<&2, List<&2, U32>> -> Maybe<&2, Edit>:
  match o:
    case Tuple{lk, Tuple{pt, rest}}:
      pt

# the bindings under a prefix, by the operations o
def Ops.range(
  -S: Data,
  o: Tree.Ops(S)
) -> S -> Maybe<&2, Hashes.Hash> -> List<&2, U32> -> Maybe<&2, List<&2, Binding>>:
  match o:
    case Tuple{lk, Tuple{pt, Tuple{rg, df}}}:
      rg

# the keys that two trees read differently, by the operations o
def Ops.diff(
  -S: Data,
  o: Tree.Ops(S)
) -> S -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, List<&2, List<&2, U32>>>:
  match o:
    case Tuple{lk, Tuple{pt, Tuple{rg, df}}}:
      df

# The laws of a tree
# ------------------
# Each is a proposition about the operations o in a depot kept as S, whose
# data is fetch, and where grows says that a depot keeps all that another
# holds (a test, so that a proof may use it many times).

# the depot s holds each node of the edit e, under its hash
def Edit.Held(-S: Data, -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, -s: S, -e: Edit) -> Type:
  @w: List<&2, U32> -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Edit.nodes(e), w) == True{}: Bool
  } -> {fetch(s)(Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}

# what a read could tell, it tells in any depot that grows: only Missing
# changes
def Laws.Final(-S: Data, -grows: S -> S -> Bool, -o: Tree.Ops(S)) -> Type:
  @h: Maybe<&2, Hashes.Hash> -> @k: List<&2, U32> -> Shared.Read.Stable(
    S,
    a => b => {grows(a, b) == True{}: Bool},
    Maybe<&2, List<&2, U32>>,
    s => Look.known(Ops.look(S, o)(s)(h)(k))
  )

# a write stays as the depot grows: it reads only nodes on its key's path,
# and what a read could tell stays
def Laws.PutFinal(-S: Data, -grows: S -> S -> Bool, -o: Tree.Ops(S)) -> Type:
  @s: S -> @s2: S -> @h: Maybe<&2, Hashes.Hash> -> @k: List<&2, U32> -> @m: Maybe<
    &2,
    List<&2, U32>> -> @e: Edit -> {
    Ops.put(S, o)(s)(h)(k)(m) == Some{e}: Maybe<&2, Edit>
  } -> {grows(s, s2) == True{}: Bool} -> {Ops.put(S, o)(s2)(h)(k)(m) == Some{e}: Maybe<&2, Edit>}

# a write changes its key and no other: in a depot that grows and holds the
# new nodes, the new root reads the key as written, and every other key as
# the old root does
def Laws.Write(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  -o: Tree.Ops(S)
) -> Type:
  @s: S -> @s2: S -> @h: Maybe<&2, Hashes.Hash> -> @k: List<&2, U32> -> @m: Maybe<
    &2,
    List<&2, U32>> -> @e: Edit -> {
    Ops.put(S, o)(s)(h)(k)(m) == Some{e}: Maybe<&2, Edit>
  } -> {grows(s, s2) == True{}: Bool} -> Edit.Held(S, fetch, s2, e) -> {
    Ops.look(S, o)(s2)(Edit.root(e))(k) == Look.of(m): Look
  }
    & (
      @k2: List<&2, U32> -> {
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
      } -> {Ops.look(S, o)(s2)(Edit.root(e))(k2) == Ops.look(S, o)(s2)(h)(k2): Look}
    )

# a root is a function of the bindings alone: two trees that list the same
# bindings have the same root, whatever the order of their writes
def Laws.Canon(-S: Data, -o: Tree.Ops(S)) -> Type:
  @s: S -> @h1: Maybe<&2, Hashes.Hash> -> @h2: Maybe<&2, Hashes.Hash> -> @bs: List<&2, Binding> -> {
    Ops.range(S, o)(s)(h1)([]) == Some{bs}: Maybe<&2, List<&2, Binding>>
  } -> {
    Ops.range(S, o)(s)(h2)([]) == Some{bs}: Maybe<&2, List<&2, Binding>>
  } -> {h1 == h2: Maybe<&2, Hashes.Hash>}

# a listing under a prefix is in the order of its keys, and holds a binding
# exactly when its key starts with the prefix and the tree reads it so
def Laws.Range(-S: Data, -o: Tree.Ops(S)) -> Type:
  @s: S -> @h: Maybe<&2, Hashes.Hash> -> @p: List<&2, U32> -> @bs: List<&2, Binding> -> {
    Ops.range(S, o)(s)(h)(p) == Some{bs}: Maybe<&2, List<&2, Binding>>
  } -> {
    Bindings.sorted(bs) == True{}: Bool
  }
    & (
      @k: List<&2, U32> -> @v: List<&2, U32> -> {
        List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
          == Bool.and(
            Key.leads(p, k),
            Shared.Maybe.is_eq(
              ~List<&2, U32>,
              ~Shared.List.is_eq(~U32, ~U32.is_eq),
              Look.value(Ops.look(S, o)(s)(h)(k)),
              Some{v}
            )
          ): Bool
      }
    )

# a difference lists exactly the keys that the two trees read differently
def Laws.Diff(-S: Data, -o: Tree.Ops(S)) -> Type:
  @s: S -> @a: Maybe<&2, Hashes.Hash> -> @b: Maybe<&2, Hashes.Hash> -> @ks: List<
    &2,
    List<&2, U32>> -> {
    Ops.diff(S, o)(s)(a)(b) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>
  } -> @k: List<&2, U32> -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, k)
      == Bool.not(
        Shared.Maybe.is_eq(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          Look.value(Ops.look(S, o)(s)(a)(k)),
          Look.value(Ops.look(S, o)(s)(b)(k))
        )
      ): Bool
  }

# a tree that the depot holds whole answers: the empty tree lists nothing; a
# whole tree reads each key finally, writes each key, lists each prefix, and
# differs from each whole tree
def Laws.Whole(-S: Data, -o: Tree.Ops(S)) -> Type:
  (
    @s: S -> @p: List<&2, U32> -> {
      Ops.range(S, o)(s)(None{})(p) == Some{[]}: Maybe<&2, List<&2, Binding>>
    }
  )
    & (
      @s: S -> @h: Maybe<&2, Hashes.Hash> -> @bs: List<&2, Binding> -> {
        Ops.range(S, o)(s)(h)([]) == Some{bs}: Maybe<&2, List<&2, Binding>>
      } -> (
        @k: List<&2, U32> -> @m: Maybe<&2, List<&2, U32>> -> @p: List<&2, U32> -> {
          Look.is_final(Ops.look(S, o)(s)(h)(k)) == True{}: Bool
        }
          & (
            {
              Maybe.is_some(&2, Edit, Ops.put(S, o)(s)(h)(k)(m)) == True{}: Bool
            }
              & {Maybe.is_some(&2, List<&2, Binding>, Ops.range(S, o)(s)(h)(p)) == True{}: Bool}
          )
      )
        & (
          @h2: Maybe<&2, Hashes.Hash> -> @bs2: List<&2, Binding> -> {
            Ops.range(S, o)(s)(h2)([]) == Some{bs2}: Maybe<&2, List<&2, Binding>>
          } -> {
            Maybe.is_some(&2, List<&2, List<&2, U32>>, Ops.diff(S, o)(s)(h)(h2)) == True{}: Bool
          }
        )
    )

# a write keeps a tree whole: in a depot that grows and holds the new nodes,
# a write to a tree that lists whole gives a tree that lists whole
def Laws.Kept(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  -o: Tree.Ops(S)
) -> Type:
  @s: S -> @s2: S -> @h: Maybe<&2, Hashes.Hash> -> @bs: List<&2, Binding> -> @k: List<&2, U32> -> @m: Maybe<
    &2,
    List<&2, U32>> -> @e: Edit -> {
    Ops.range(S, o)(s)(h)([]) == Some{bs}: Maybe<&2, List<&2, Binding>>
  } -> {
    Ops.put(S, o)(s)(h)(k)(m) == Some{e}: Maybe<&2, Edit>
  } -> {grows(s, s2) == True{}: Bool} -> Edit.Held(S, fetch, s2, e) -> {
    Maybe.is_some(&2, List<&2, Binding>, Ops.range(S, o)(s2)(Edit.root(e))([])) == True{}: Bool
  }

# the laws of a tree with the operations o
def Tree.Laws(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  -o: Tree.Ops(S)
) -> Type:
  Laws.Final(S, grows, o)
    & (
      Laws.PutFinal(S, grows, o)
    )
    & (
      Laws.Write(S, fetch, grows, o)
        & (Laws.Canon(S, o) & (Laws.Range(S, o) & (Laws.Diff(S, o) & (Laws.Whole(S, o) & Laws.Kept(S, fetch, grows, o)))))
    )

# a tree in a depot kept as S, whose data is fetch and which grows as grows
# says: its operations, and the proof that they obey the laws
def Tree(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool
) -> Type:
  &o: Tree.Ops(S) -> Tree.Laws(S, fetch, grows, o)

# the operations of the tree t
def Tree.ops(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Tree(S, fetch, grows)
) -> Tree.Ops(S):
  match t:
    case Tuple{o, laws}:
      o

# Merkle search trees
# -------------------

# how the key a compares to the key b: word by word, a key before each key
# that it starts
def Key.cmp(a: List<&2, U32>, b: List<&2, U32>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, rb}:
      LT{}
    case Con{x, ra} Nil{}:
      GT{}
    case Con{x, ra} Con{y, rb}:
      +c = U32.cmp(x, y)
      Shared.Bool.when(Cmp, Cmp.is_eq(c), u => Key.cmp(ra, rb), u => c)

# the number of zero groups of 5 bits at the top of x, f groups at most
def Level.zeros(f: Nat, +x: U32) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+p:
      Shared.Bool.when(
        Nat,
        U32.is_eq(U32.and(x, 4160749568), 0),
        u => 1n+Level.zeros(p, U32.mul(x, 32)),
        u => 0n
      )

# the level of a key of the hash h: its zero groups of 5 bits at the top, so
# about one key in 32 is a level up
def Level.of(h: Hashes.Hash) -> Nat:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      +za = Level.zeros(6n, a)
      Shared.Bool.when(Nat, Nat.is_eq(za, 6n), u => Nat.add(6n, Level.zeros(6n, b)), u => za)

# the level of the key k: by its hash, so no writer can choose it
def Key.level(k: List<&2, U32>) -> Nat:
  Level.of(Hashes.Sha.hash(k))

# a binding of a node, and the subtree of the keys between it and the next
type Item is Data:
  Item{key: List<&2, U32>, value: List<&2, U32>, right: Maybe<&2, Hashes.Hash>}

# a node of a tree: its level, the subtree of the keys before its first item,
# and its items, in the order of their keys
type Node is Data:
  Node{level: Nat, left: Maybe<&2, Hashes.Hash>, items: List<&2, Item>}

# the item x, then r
def Item.code(x: Item, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Item{k, v, h}:
      Codes.Code.words(k, Codes.Code.words(v, Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, h, r)))

# an item
def Item.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Item>>:
  Codes.Code.three.read(
    ~List<&2, U32>,
    ~List<&2, U32>,
    ~Maybe<&2, Hashes.Hash>,
    ~Item,
    ~Codes.Code.words.read,
    ~Codes.Code.words.read,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    k => v => h => Item{k, v, h},
    ts
  )

# an item reads back
def Item.code_read(x: Item, r: List<&2, U32>) -> {
  Item.code.read(Item.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Item>>
}:
  match x:
    case Item{k, v, h}:
      Codes.Code.three_read(
        ~List<&2, U32>,
        ~List<&2, U32>,
        ~Maybe<&2, Hashes.Hash>,
        ~Item,
        ~Codes.Code.words.codec(),
        ~Codes.Code.words.codec(),
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        a => b => c => Item{a, b, c},
        k,
        v,
        h,
        r
      )

# the code of items
def Item.codec() -> Codes.Codec(Item):
  (Item.code, (Item.code.read, x => r => Item.code_read(x, r)))

# the code of counts
def Count.codec() -> Codes.Codec(Nat):
  (Codes.Code.count, (Codes.Code.count.read, x => r => Codes.Code.count_read(x, r)))

# the node n, then r
def Node.code(n: Node, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Node{l, h, xs}:
      Codes.Code.count(
        l,
        Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, h, Codes.Code.list(~Item, ~Item.code, xs, r))
      )

# a node
def Node.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Node>>:
  Codes.Code.three.read(
    ~Nat,
    ~Maybe<&2, Hashes.Hash>,
    ~List<&2, Item>,
    ~Node,
    ~Codes.Code.count.read,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    ~(m => Codes.Code.list.read(~Item, ~Item.code.read, m)),
    l => h => xs => Node{l, h, xs},
    ts
  )

# a node reads back
def Node.code_read(n: Node, r: List<&2, U32>) -> {
  Node.code.read(Node.code(n, r)) == Some{Codes.Read{n, r}}: Maybe<&2, Codes.Read<Node>>
}:
  match n:
    case Node{l, h, xs}:
      Codes.Code.three_read(
        ~Nat,
        ~Maybe<&2, Hashes.Hash>,
        ~List<&2, Item>,
        ~Node,
        ~Count.codec(),
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        ~Codes.Code.list.codec(~Item, ~Item.codec()),
        a => b => c => Node{a, b, c},
        l,
        h,
        xs,
        r
      )

# the node n, when it may sit below a node of the level up: its level is below
# up, and it has an item
def Node.below(n: Node, up: Nat) -> Maybe<&2, Node>:
  match n:
    case Node{+l, left, +xs}:
      Shared.Maybe.when(
        Node,
        Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))),
        u => Some{Node{l, left, xs}}
      )

# the node that the depot s holds under the hash h (none: s lacks it, or it
# is not the code of one node)
def Mst.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash
) -> Maybe<&2, Node>:
  Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, fetch(s)(h))

# the node that the depot s holds under the hash h, when it may sit below a
# node of the level up: its level is below up, and it has an item. So the
# levels fall along each path, and no path is longer than up nodes (none: s
# lacks it, or it is not so)
def Mst.node.below(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash,
  up: Nat
) -> Maybe<&2, Node>:
  Maybe.bind(&2, Node, Node, Mst.node(~S, ~fetch, s, h), n => Node.below(n, up))

# what a read of a node finds: the value of the key, or the subtree to go on in
type Pick is Data:
  Pick.Hit{value: List<&2, U32>}
  Pick.Down{sub: Maybe<&2, Hashes.Hash>}

# the pick of the key k among the items xs, whose subtree before is prev
def Mst.pick(xs: List<&2, Item>, prev: Maybe<&2, Hashes.Hash>, +k: List<&2, U32>) -> Pick:
  match xs:
    case Nil{}:
      Pick.Down{prev}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +c = Key.cmp(k, ik)
      Shared.Bool.when(
        Pick,
        Cmp.is_lt(c),
        u => Pick.Down{prev},
        u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, k))
      )

# the read that a pick gives: a value, or the read of its subtree (go)
def Mst.look.pick(p: Pick, go: Maybe<&2, Hashes.Hash> -> Look) -> Look:
  match p:
    case Pick.Hit{v}:
      Look.Found{v}
    case Pick.Down{m}:
      go(m)

# the read of the key k in the node m of the hash h, with go reading a
# subtree below the node's level
def Mst.look.at(
  h: Hashes.Hash,
  m: Maybe<&2, Node>,
  +k: List<&2, U32>,
  go: Nat -> Maybe<&2, Hashes.Hash> -> Look
) -> Look:
  match m:
    case None{}:
      Look.Missing{h}
    case Some{Node{l, left, xs}}:
      Mst.look.pick(Mst.pick(xs, left, k), go(l))

# the read of the key k in the tree of the root m, below the level up, at
# most f levels down
def Mst.look.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  up: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Look:
  match f m:
    case x None{}:
      Look.Absent{}
    case 0n Some{h}:
      Look.Missing{h}
    case 1n+p Some{+h}:
      Mst.look.at(h, Mst.node.below(~S, ~fetch, s, h, up), k, u2 => m2 => Mst.look.go(~S, ~fetch, p, s, u2, m2, k))

# no tree is deeper than this many levels, and no level of a node reaches
# it: levels fall along each path (Mst.node.below)
def Mst.depth() -> Nat:
  64n

# the read of the key k in the tree of the root m
def Mst.look(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  m: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Look:
  Mst.look.go(~S, ~fetch, Mst.depth(), s, Mst.depth(), m, k)

# Writes
# ------
# A write changes only the nodes on the path to its key: an insert splits the
# subtree where the key goes, a delete merges the two subtrees beside it, and
# every node it rebuilds is new; all others stay shared.

# the node n stored: its hash, and its words in front of the new nodes acc
def Mst.store(n: Node, acc: List<&2, List<&2, U32>>) -> Edit:
  +ws = Node.code(n, [])
  Edit{Some{Hashes.Sha.hash(ws)}, ws <> acc}

# a node of the level l in its one shape: with no item it is its left subtree
def Mst.make(+l: Nat, left: Maybe<&2, Hashes.Hash>, xs: List<&2, Item>, acc: List<&2, List<&2, U32>>) -> Edit:
  match xs:
    case Nil{}:
      Edit{left, acc}
    case Con{x, r}:
      Mst.store(Node{l, left, x <> r}, acc)

# the items of a node split at the key k: those before it, last first; the
# subtree where k goes; and those from k on
type Part is Data:
  Part{before: List<&2, Item>, gap: Maybe<&2, Hashes.Hash>, after: List<&2, Item>}

# the items xs split at the key k, the subtree before them prev, after the
# items acc, last first
def Mst.part(xs: List<&2, Item>, prev: Maybe<&2, Hashes.Hash>, +k: List<&2, U32>, +acc: List<&2, Item>) -> Part:
  match xs:
    case Nil{}:
      Part{acc, prev, []}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Shared.Bool.when(
        Part,
        Cmp.is_lt(Key.cmp(ik, k)),
        u => Mst.part(rest, r, k, Item{ik, iv, r} <> acc),
        u => Part{acc, prev, Item{ik, iv, r} <> rest}
      )

# the subtree of a part
def Part.gap(p: Part) -> Maybe<&2, Hashes.Hash>:
  match p:
    case Part{b, g, a}:
      g

# a node's items before a place, last first, with the subtree there set to
# m, in order, then the items after
def Mst.rejoin(before: List<&2, Item>, m: Maybe<&2, Hashes.Hash>, after: List<&2, Item>) -> List<&2, Item>:
  match before:
    case Nil{}:
      after
    case Con{Item{k, v, r}, rest}:
      List.append(&2, Item, List.reverse(&2, Item, rest), Item{k, v, m} <> after)

# the left subtree of a node whose items before a place are before (last
# first), when the subtree there becomes m
def Mst.left(before: List<&2, Item>, left: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Hashes.Hash>:
  match before:
    case Nil{}:
      m
    case Con{x, r}:
      left

# a tree split at a key: the subtree of the keys before it, of those after
# it, and the new nodes
type Halves is Data:
  Halves{lo: Maybe<&2, Hashes.Hash>, hi: Maybe<&2, Hashes.Hash>, nodes: List<&2, List<&2, U32>>}

# the node of the level l and the left subtree left, split at k by its part
# p, once its gap is split (m)
def Mst.split.done(+l: Nat, +left: Maybe<&2, Hashes.Hash>, p: Part, m: Maybe<&2, Halves>) -> Maybe<&2, Halves>:
  match p m:
    case x None{}:
      None{}
    case Part{+b, g, a} Some{Halves{+clo, chi, ns}}:
      +lo = Mst.make(l, Mst.left(b, left, clo), Mst.rejoin(b, clo, []), ns)
      +hi = Mst.make(l, chi, a, Edit.nodes(lo))
      Some{Halves{Edit.root(lo), Edit.root(hi), Edit.nodes(hi)}}

# the node m split at the key k, with go splitting a subtree below the node's
# level
def Mst.split.at(
  m: Maybe<&2, Node>,
  +k: List<&2, U32>,
  go: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>
) -> Maybe<&2, Halves>:
  match m:
    case None{}:
      None{}
    case Some{Node{+l, +left, xs}}:
      +p = Mst.part(xs, left, k, [])
      Mst.split.done(l, left, p, go(l)(Part.gap(p)))

# the tree of the root m, below the level up, split at the key k, which it
# lacks, at most f levels down
def Mst.split(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  up: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Maybe<&2, Halves>:
  match f m:
    case x None{}:
      Some{Halves{None{}, None{}, []}}
    case 0n Some{h}:
      None{}
    case 1n+p Some{h}:
      Mst.split.at(Mst.node.below(~S, ~fetch, s, h, up), k, u2 => c => Mst.split(~S, ~fetch, p, s, u2, c, k))

# the subtree at the end of a node: the right of its last item, else its left
def Mst.last(xs: List<&2, Item>, left: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Hashes.Hash>:
  match xs:
    case Nil{}:
      left
    case Con{Item{k, v, r}, rest}:
      Mst.last(rest, r)

# the items xs with the subtree after the last one set to m
def Mst.set_last(xs: List<&2, Item>, m: Maybe<&2, Hashes.Hash>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{Item{k, v, r}, Nil{}}:
      [Item{k, v, m}]
    case Con{x, rest}:
      x <> Mst.set_last(rest, m)

# a node with no item has m as its left subtree, else it keeps left
def Mst.end_left(xs: List<&2, Item>, left: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Hashes.Hash>:
  match xs:
    case Nil{}:
      m
    case Con{x, r}:
      left

# the node of the level l, left subtree left and items xs, with its last
# subtree replaced by the merge e
def Mst.with_last(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  e: Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match e:
    case None{}:
      None{}
    case Some{Edit{+mc, ns}}:
      Some{Mst.make(l, Mst.end_left(xs, left, mc), Mst.set_last(xs, mc), ns)}

# the node of the level l and items xs, with its left subtree replaced by the
# merge e
def Mst.with_first(+l: Nat, xs: List<&2, Item>, e: Maybe<&2, Edit>) -> Maybe<&2, Edit>:
  match e:
    case None{}:
      None{}
    case Some{Edit{mc, ns}}:
      Some{Mst.make(l, mc, xs, ns)}

# two nodes of one level as one: the items of a, then of b, the subtrees
# between them merged (e)
def Mst.with_both(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  xb: List<&2, Item>,
  e: Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match e:
    case None{}:
      None{}
    case Some{Edit{+mc, ns}}:
      Some{Mst.make(l, Mst.end_left(xa, left, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), ns)}

# the merge of the node a of the level la, below the level ua, and the node b
# of the level lb, below the level ub, by how la compares to lb (c), with go
# merging two subtrees, each below its level
def Mst.merge.nodes(
  c: Cmp,
  +ha: Hashes.Hash,
  +ua: Nat,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +hb: Hashes.Hash,
  +ub: Nat,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  go: Nat -> Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match c:
    case GT{}:
      Mst.with_last(la, lefta, xa, go(la)(ub)(Mst.last(xa, lefta))(Some{hb}))
    case LT{}:
      Mst.with_first(lb, xb, go(ua)(lb)(Some{ha})(leftb))
    case EQ{}:
      Mst.with_both(la, lefta, xa, xb, go(la)(lb)(Mst.last(xa, lefta))(leftb))

# the merge of the nodes na, below the level ua, and nb, below the level ub,
# of the hashes ha and hb
def Mst.merge.at(
  na: Maybe<&2, Node>,
  nb: Maybe<&2, Node>,
  +ha: Hashes.Hash,
  +ua: Nat,
  +hb: Hashes.Hash,
  +ub: Nat,
  go: Nat -> Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match na nb:
    case Some{Node{+la, lefta, xa}} Some{Node{+lb, leftb, xb}}:
      Mst.merge.nodes(Nat.cmp(la, lb), ha, ua, la, lefta, xa, hb, ub, lb, leftb, xb, go)
    case x y:
      None{}

# the tree of the keys of a, below the level ua, then of b, below the level
# ub, when each key of a is before each of b, at most f levels down
def Mst.merge(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +ua: Nat,
  +ub: Nat,
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Edit>:
  match f a b:
    case x None{} y:
      Some{Edit{y, []}}
    case x y None{}:
      Some{Edit{y, []}}
    case 0n y z:
      None{}
    case 1n+p Some{+ha} Some{+hb}:
      Mst.merge.at(
        Mst.node.below(~S, ~fetch, s, ha, ua),
        Mst.node.below(~S, ~fetch, s, hb, ub),
        ha,
        ua,
        hb,
        ub,
        u1 => u2 => x => y => Mst.merge(~S, ~fetch, p, s, u1, u2, x, y)
      )

# the tree of the level L with only the key k, over the halves of a tree split
# at k
def Mst.insert.top(+L: Nat, +k: List<&2, U32>, +v: List<&2, U32>, m: Maybe<&2, Halves>) -> Maybe<&2, Edit>:
  match m:
    case None{}:
      None{}
    case Some{Halves{lo, hi, ns}}:
      Some{Mst.store(Node{L, lo, [Item{k, v, hi}]}, ns)}

# a node of the level l that gets the key k, which it lacks, in the gap of its
# part p, once that gap is split (m)
def Mst.insert.gap(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  p: Part,
  m: Maybe<&2, Halves>
) -> Maybe<&2, Edit>:
  match p m:
    case x None{}:
      None{}
    case Part{+b, g, a} Some{Halves{+clo, chi, ns}}:
      Some{Mst.store(Node{l, Mst.left(b, left, clo), Mst.rejoin(b, clo, Item{k, v, chi} <> a)}, ns)}

# a node of the level l, split at k by its part p, that gets the key k: a new
# value when it holds k, else k in its gap (sp splits the gap)
def Mst.insert.here(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  p: Part,
  sp: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>
) -> Maybe<&2, Edit>:
  match p:
    case Part{+b, +g, Con{Item{+ik, iv, +r}, +rest}}:
      Shared.Bool.when(
        Maybe<&2, Edit>,
        Cmp.is_eq(Key.cmp(ik, k)),
        u => Some{Mst.store(Node{l, left, Mst.rejoin(b, g, Item{k, v, r} <> rest)}, [])},
        u => Mst.insert.gap(l, left, k, v, Part{b, g, Item{ik, iv, r} <> rest}, sp(g))
      )
    case Part{+b, +g, Nil{}}:
      Mst.insert.gap(l, left, k, v, Part{b, g, []}, sp(g))

# a node of the level l whose gap of its part p got the edit e
def Mst.with_gap(+l: Nat, +left: Maybe<&2, Hashes.Hash>, p: Part, e: Maybe<&2, Edit>) -> Maybe<&2, Edit>:
  match p e:
    case x None{}:
      None{}
    case Part{+b, g, a} Some{Edit{+nc, ns}}:
      Some{Mst.make(l, Mst.left(b, left, nc), Mst.rejoin(b, nc, a), ns)}

# the node of the hash h, of the level l, that gets the key k of the level L,
# by how l compares to L (c): above it a new node splits the tree (sp); at
# it, it takes the key (spg splits its gap); below it, the key goes into the
# gap of its part (ins)
def Mst.insert.node(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  xs: List<&2, Item>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  sp: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spg: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  ins: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match c:
    case LT{}:
      Mst.insert.top(L, k, v, sp(Some{h}))
    case EQ{}:
      Mst.insert.here(l, left, k, v, Mst.part(xs, left, k, []), spg(l))
    case GT{}:
      +p = Mst.part(xs, left, k, [])
      Mst.with_gap(l, left, p, ins(l)(Part.gap(p)))

# the node m of the hash h with the key k of the level L bound to v
def Mst.insert.at(
  m: Maybe<&2, Node>,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  sp: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spg: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  ins: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match m:
    case None{}:
      None{}
    case Some{Node{+l, left, xs}}:
      Mst.insert.node(Nat.cmp(l, L), h, l, left, xs, k, v, L, sp, spg, ins)

# the tree of the root m, below the level up, with the key k, of the level L,
# bound to v, at most f levels down
def Mst.insert(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +up: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat
) -> Maybe<&2, Edit>:
  match f m:
    case x None{}:
      Some{Mst.store(Node{L, None{}, [Item{k, v, None{}}]}, [])}
    case 0n Some{h}:
      None{}
    case 1n+(+p) Some{+h}:
      Mst.insert.at(
        Mst.node.below(~S, ~fetch, s, h, up),
        h,
        k,
        v,
        L,
        c => Mst.split(~S, ~fetch, p, s, up, c, k),
        u2 => c => Mst.split(~S, ~fetch, p, s, u2, c, k),
        u2 => c => Mst.insert(~S, ~fetch, p, s, u2, c, k, v, L)
      )

# a node of the level l, split at k by its part p, without the key k: the two
# subtrees beside k merge (mg); a node that lacks k stays (h)
def Mst.delete.here(
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  p: Part,
  mg: Nat -> Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match p:
    case Part{+b, +g, Con{Item{+ik, iv, +r}, +rest}}:
      Shared.Bool.when(
        Maybe<&2, Edit>,
        Cmp.is_eq(Key.cmp(ik, k)),
        u => Mst.with_gap(l, left, Part{b, g, rest}, mg(l)(l)(g)(r)),
        u => Some{Edit{Some{h}, []}}
      )
    case Part{b, g, Nil{}}:
      Some{Edit{Some{h}, []}}

# the node of the hash h, of the level l, without the key k of the level L,
# by how l compares to L (c)
def Mst.delete.node(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  xs: List<&2, Item>,
  +k: List<&2, U32>,
  mg: Nat -> Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  del: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match c:
    case LT{}:
      Some{Edit{Some{h}, []}}
    case EQ{}:
      Mst.delete.here(h, l, left, k, Mst.part(xs, left, k, []), mg)
    case GT{}:
      +p = Mst.part(xs, left, k, [])
      Mst.with_gap(l, left, p, del(l)(Part.gap(p)))

# the node m of the hash h without the key k of the level L
def Mst.delete.at(
  m: Maybe<&2, Node>,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  +L: Nat,
  mg: Nat -> Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  del: Nat -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match m:
    case None{}:
      None{}
    case Some{Node{+l, left, xs}}:
      Mst.delete.node(Nat.cmp(l, L), h, l, left, xs, k, mg, del)

# the tree of the root m, below the level up, without the key k, of the level
# L, at most f levels down
def Mst.delete(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  up: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +L: Nat
) -> Maybe<&2, Edit>:
  match f m:
    case x None{}:
      Some{Edit{None{}, []}}
    case 0n Some{h}:
      None{}
    case 1n+(+p) Some{+h}:
      Mst.delete.at(
        Mst.node.below(~S, ~fetch, s, h, up),
        h,
        k,
        L,
        u1 => u2 => x => y => Mst.merge(~S, ~fetch, p, s, u1, u2, x, y),
        u2 => c => Mst.delete(~S, ~fetch, p, s, u2, c, k, L)
      )

# the tree of the root m with the key k set to the value of m2 (none: deleted)
def Mst.put(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  m2: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, Edit>:
  match m2:
    case Some{v}:
      Mst.insert(~S, ~fetch, Mst.depth(), s, Mst.depth(), m, k, v, Key.level(k))
    case None{}:
      Mst.delete(~S, ~fetch, Mst.depth(), s, Mst.depth(), m, k, Key.level(k))

# Reads of many keys
# ------------------
# A listing and a difference read a tree as pieces, and check each node that
# they open (Mst.open): its hash, its code, its level, and its keys in their
# bounds. So they answer only of a tree in its one shape, whoever made its
# root, and two roots that list the same bindings are the same root.

# a piece of a tree, as a walk reads it: a binding, or the subtree of the hash
# h, whose node must have a level below up and keys after lo and before hi
type Piece is Data:
  Piece.Bind{key: List<&2, U32>, value: List<&2, U32>}
  Piece.Sub{hash: Hashes.Hash, up: Nat, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>}

# the key k comes after the bound lo (none: no bound)
def Bound.after(lo: Maybe<&2, List<&2, U32>>, k: List<&2, U32>) -> Bool:
  match lo:
    case None{}:
      True{}
    case Some{a}:
      Key.is_lt(a, k)

# the key k comes before the bound hi (none: no bound)
def Bound.before(k: List<&2, U32>, hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match hi:
    case None{}:
      True{}
    case Some{b}:
      Key.is_lt(k, b)

# the piece of the subtree m of a node of the level l, between lo and hi,
# before the pieces rest (none: no piece)
def Piece.sub(
  m: Maybe<&2, Hashes.Hash>,
  l: Nat,
  lo: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>,
  rest: List<&2, Piece>
) -> List<&2, Piece>:
  match m:
    case None{}:
      rest
    case Some{h}:
      Piece.Sub{h, l, lo, hi} <> rest

# the pieces of the items xs of a node of the level l, after the subtree
# prev, between lo and hi (none: a key is not of the level l, or not in order
# between the bounds, or a subtree sits before the empty key, where no key
# can be)
def Mst.pieces(
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, Piece>>:
  match xs:
    case Nil{}:
      Some{Piece.sub(prev, l, lo, hi, [])}
    case Con{Item{+k, v, r}, rest}:
      Shared.Maybe.when(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(k), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, k)))),
          Bool.and(Bound.after(lo, k), Bound.before(k, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps => Piece.sub(prev, l, lo, Some{k}, Piece.Bind{k, v} <> ps),
          Mst.pieces(rest, l, r, Some{k}, hi)
        )
      )

# the pieces of the node n, below the level up and between lo and hi (none:
# it has no item, its level is not below up, or its items are not so)
def Mst.open.node(
  n: Node,
  up: Nat,
  lo: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, Piece>>:
  match n:
    case Node{+l, left, +xs}:
      Shared.Maybe.when(
        List<&2, Piece>,
        Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))),
        u => Mst.pieces(xs, l, left, lo, hi)
      )

# the pieces of the node of the hash h, checked (none: the depot s lacks it,
# its words do not have the hash h or are not the code of one node, or the
# node is not in its one shape below up and between lo and hi)
def Mst.open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  +h: Hashes.Hash,
  up: Nat,
  lo: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, Piece>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Piece>,
    fetch(s)(h),
    +ws => Shared.Maybe.when(
      List<&2, Piece>,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
      u => Maybe.bind(
        &2,
        Node,
        List<&2, Piece>,
        Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws),
        n => Mst.open.node(n, up, lo, hi)
      )
    )
  )

# the pieces of the tree of the root m
def Mst.root(m: Maybe<&2, Hashes.Hash>) -> List<&2, Piece>:
  Piece.sub(m, Mst.depth(), None{}, None{}, [])

# Listings

# a key that starts with p may come after the bound lo
def Bound.meets_lo(+p: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>) -> Bool:
  match lo:
    case None{}:
      True{}
    case Some{+a}:
      Bool.or(Key.is_lt(a, p), Key.leads(p, a))

# a key that starts with p may come before the bound hi
def Bound.meets_hi(p: List<&2, U32>, hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match hi:
    case None{}:
      True{}
    case Some{b}:
      Key.is_lt(p, b)

# the bindings under the prefix p among the pieces ps, at most f levels down:
# a subtree whose bounds hold no key that starts with p is not read
def Mst.range.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +p: List<&2, U32>,
  ps: List<&2, Piece>
) -> Maybe<&2, List<&2, Binding>>:
  match f ps:
    case x Nil{}:
      Some{[]}
    case 0n Con{x, rest}:
      None{}
    case 1n+(+q) Con{Piece.Bind{+k, +v}, rest}:
      Maybe.map(
        &2,
        List<&2, Binding>,
        List<&2, Binding>,
        +bs => Shared.Bool.when(List<&2, Binding>, Key.leads(p, k), u => Binding{k, v} <> bs, u => bs),
        Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
      )
    case 1n+(+q) Con{Piece.Sub{h, up, +lo, +hi}, +rest}:
      Shared.Bool.when(
        Maybe<&2, List<&2, Binding>>,
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        u => Maybe.bind(
          &2,
          List<&2, Piece>,
          List<&2, Binding>,
          Mst.open(~S, ~fetch, s, h, up, lo, hi),
          ks => Maybe.bind(
            &2,
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, q, s, p, ks),
            a => Maybe.map(
              &2,
              List<&2, Binding>,
              List<&2, Binding>,
              b => List.append(&2, Binding, a, b),
              Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
            )
          )
        ),
        u => Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
      )

# the bindings whose keys start with p, in the tree of the root m, in the
# order of their keys (none: the depot lacks a node, or a node is not in its
# one shape)
def Mst.range(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  m: Maybe<&2, Hashes.Hash>,
  p: List<&2, U32>
) -> Maybe<&2, List<&2, Binding>>:
  Mst.range.go(~S, ~fetch, Mst.depth(), s, p, Mst.root(m))

# Differences
# -----------
# A difference walks both trees in rounds, one level of nodes a round. A round
# cuts the pieces of both at each key that both hold as a binding; of each run
# between two cuts, it drops the pieces at its ends that both trees share (a
# subtree of one hash, in the same bounds, reads the same in both), and opens
# each subtree that is left. So a difference opens only the nodes on the paths
# to the keys that differ.

# the pieces a and b are the same: one binding, or one subtree in the same
# bounds
def Piece.same(a: Piece, b: Piece) -> Bool:
  match a b:
    case Piece.Bind{k1, v1} Piece.Bind{k2, v2}:
      Bool.and(Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2))
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Sub{h2, u2, lo2, hi2}:
      Bool.and(
        Hashes.Hash.is_eq(h1, h2),
        Bool.and(
          Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), lo1, lo2),
          Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), hi1, hi2)
        )
      )
    case x y:
      False{}

# two runs of pieces over the same keys, one of each tree
type Runs is Data:
  Runs{a: List<&2, Piece>, b: List<&2, Piece>}

# what a round gives: keys that differ, and the runs to read on
type Round is Data:
  Round{keys: List<&2, List<&2, U32>>, pairs: List<&2, Runs>}

# the keys of a round
def Round.keys(r: Round) -> List<&2, List<&2, U32>>:
  match r:
    case Round{ks, ps}:
      ks

# the runs of a round
def Round.pairs(r: Round) -> List<&2, Runs>:
  match r:
    case Round{ks, ps}:
      ps

# the round r with the run p first
def Round.cons(p: Runs, r: Round) -> Round:
  match r:
    case Round{ks, ps}:
      Round{ks, p <> ps}

# the round r with the key k, when the values v1 and v2 of it differ
def Round.differs(+k: List<&2, U32>, v1: List<&2, U32>, v2: List<&2, U32>, r: Round) -> Round:
  match r:
    case Round{+ks, ps}:
      Round{Shared.Bool.when(List<&2, List<&2, U32>>, Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2), u => ks, u => k <> ks), ps}

# the rounds a and b, one after the other
def Round.append(a: Round, b: Round) -> Round:
  match a b:
    case Round{k1, p1} Round{k2, p2}:
      Round{List.append(&2, List<&2, U32>, k1, k2), List.append(&2, Runs, p1, p2)}

# the pieces as and bs cut at each key that both hold as a binding, after the
# pieces sa and sb of the run so far, last first
def Mst.cut(as: List<&2, Piece>, bs: List<&2, Piece>, +sa: List<&2, Piece>, +sb: List<&2, Piece>) -> Round:
  match as bs:
    case Nil{} Nil{}:
      Round{[], [Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)}]}
    case Nil{} Con{y, rb}:
      Mst.cut([], rb, sa, y <> sb)
    case Con{x, ra} Nil{}:
      Mst.cut(ra, [], x <> sa, sb)
    case Con{Piece.Sub{h, u, lo, hi}, ra} ys:
      Mst.cut(ra, ys, Piece.Sub{h, u, lo, hi} <> sa, sb)
    case Con{Piece.Bind{k1, v1}, ra} Con{Piece.Sub{h, u, lo, hi}, rb}:
      Mst.cut(Con{Piece.Bind{k1, v1}, ra}, rb, sa, Piece.Sub{h, u, lo, hi} <> sb)
    case Con{Piece.Bind{+k1, +v1}, +ra} Con{Piece.Bind{+k2, +v2}, +rb}:
      +c = Key.cmp(k1, k2)
      Shared.Bool.when(
        Round,
        Cmp.is_lt(c),
        w => Mst.cut(ra, Con{Piece.Bind{k2, v2}, rb}, Piece.Bind{k1, v1} <> sa, sb),
        w => Shared.Bool.when(
          Round,
          Cmp.is_eq(c),
          w2 => Round.cons(
            Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)},
            Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], []))
          ),
          w2 => Mst.cut(Con{Piece.Bind{k1, v1}, ra}, rb, sa, Piece.Bind{k2, v2} <> sb)
        )
      )

# the runs as and bs without the pieces at their fronts that both share
def Mst.trim(as: List<&2, Piece>, bs: List<&2, Piece>) -> Runs:
  match as bs:
    case Con{+x, +ra} Con{+y, +rb}:
      Shared.Bool.when(Runs, Piece.same(x, y), u => Mst.trim(ra, rb), u => Runs{x <> ra, y <> rb})
    case xs ys:
      Runs{xs, ys}

# the runs r, read back to front
def Runs.reverse(r: Runs) -> Runs:
  match r:
    case Runs{a, b}:
      Runs{List.reverse(&2, Piece, a), List.reverse(&2, Piece, b)}

# the runs r without their front pieces that both share
def Runs.trim_front(r: Runs) -> Runs:
  match r:
    case Runs{a, b}:
      Mst.trim(a, b)

# the run p without the pieces at either end that both runs share
def Runs.trim(p: Runs) -> Runs:
  Runs.reverse(Runs.trim_front(Runs.reverse(Runs.trim_front(p))))

# the run ps holds a subtree
def Pieces.has_sub(ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Piece.Sub{h, u, lo, hi}, rest}:
      True{}
    case Con{Piece.Bind{k, v}, rest}:
      Pieces.has_sub(rest)

# the keys of the bindings of the run ps, before ks
def Pieces.keys(ps: List<&2, Piece>, ks: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      ks
    case Con{Piece.Bind{k, v}, rest}:
      k <> Pieces.keys(rest, ks)
    case Con{Piece.Sub{h, u, lo, hi}, rest}:
      Pieces.keys(rest, ks)

# the run ps with each subtree opened one level (none: a node does not read)
def Mst.open.all(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ps: List<&2, Piece>
) -> Maybe<&2, List<&2, Piece>>:
  match ps:
    case Nil{}:
      Some{[]}
    case Con{Piece.Bind{k, v}, rest}:
      Maybe.map(
        &2,
        List<&2, Piece>,
        List<&2, Piece>,
        r => Piece.Bind{k, v} <> r,
        Mst.open.all(~S, ~fetch, s, rest)
      )
    case Con{Piece.Sub{h, u, lo, hi}, rest}:
      Maybe.bind(
        &2,
        List<&2, Piece>,
        List<&2, Piece>,
        Mst.open(~S, ~fetch, s, h, u, lo, hi),
        a => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          b => List.append(&2, Piece, a, b),
          Mst.open.all(~S, ~fetch, s, rest)
        )
      )

# a run between two cuts, trimmed (Runs.trim): the keys of its bindings, when
# neither side holds a subtree (no key there is in both trees); else the run
# with each subtree opened, to read on
def Mst.step.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  p: Runs
) -> Maybe<&2, Round>:
  match p:
    case Runs{+a, +b}:
      Shared.Bool.when(
        Maybe<&2, Round>,
        Bool.or(Pieces.has_sub(a), Pieces.has_sub(b)),
        u => Maybe.bind(
          &2,
          List<&2, Piece>,
          Round,
          Mst.open.all(~S, ~fetch, s, a),
          a2 => Maybe.map(
            &2,
            List<&2, Piece>,
            Round,
            b2 => Round{[], [Runs{a2, b2}]},
            Mst.open.all(~S, ~fetch, s, b)
          )
        ),
        u => Some{Round{Pieces.keys(a, Pieces.keys(b, [])), []}}
      )

# the round of each of the runs ps between two cuts
def Mst.step(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ps: List<&2, Runs>
) -> Maybe<&2, Round>:
  match ps:
    case Nil{}:
      Some{Round{[], []}}
    case Con{p, rest}:
      Maybe.bind(
        &2,
        Round,
        Round,
        Mst.step.at(~S, ~fetch, s, Runs.trim(p)),
        a => Maybe.map(&2, Round, Round, b => Round.append(a, b), Mst.step(~S, ~fetch, s, rest))
      )

# the keys that differ in each of the runs ps, at most f rounds on
def Mst.diff.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Runs>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match f ps:
    case x Nil{}:
      Some{[]}
    case 0n Con{p, rest}:
      None{}
    case 1n+(+q) Con{Runs{a, b}, rest}:
      +c = Mst.cut(a, b, [], [])
      Maybe.bind(
        &2,
        Round,
        List<&2, List<&2, U32>>,
        Mst.step(~S, ~fetch, s, Round.pairs(c)),
        +r => Maybe.bind(
          &2,
          List<&2, List<&2, U32>>,
          List<&2, List<&2, U32>>,
          Mst.diff.go(~S, ~fetch, q, s, Round.pairs(r)),
          k3 => Maybe.map(
            &2,
            List<&2, List<&2, U32>>,
            List<&2, List<&2, U32>>,
            k4 => List.append(
              &2,
              List<&2, U32>,
              Round.keys(c),
              List.append(&2, List<&2, U32>, Round.keys(r), List.append(&2, List<&2, U32>, k3, k4))
            ),
            Mst.diff.go(~S, ~fetch, 1n+q, s, rest)
          )
        )
      )

# the keys that the trees of the roots a and b read differently (none: the
# depot lacks a node on a path where they differ, or a node there is not in
# its one shape)
def Mst.diff(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  Mst.diff.go(~S, ~fetch, Mst.depth(), s, [Runs{Mst.root(a), Mst.root(b)}])

# The tree
# --------

# the operations of a Merkle search tree in a depot kept as S, whose data is
# fetch
def Mst.ops(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>) -> Tree.Ops(S):
  (
    s => m => k => Mst.look(~S, ~fetch, s, m, k),
    (
      s => m => k => v => Mst.put(~S, ~fetch, s, m, k, v),
      (s => m => p => Mst.range(~S, ~fetch, s, m, p), s => a => b => Mst.diff(~S, ~fetch, s, a, b))
    )
  )

# what a read tells stays, in a depot that keeps what it holds
law Mst.reads_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Final(S, grows, Mst.ops(~S, ~fetch))

# a write stays, in a depot that keeps what it holds
law Mst.puts_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.PutFinal(S, grows, Mst.ops(~S, ~fetch))

# a write changes its key and no other
law Mst.writes:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Write(S, fetch, grows, Mst.ops(~S, ~fetch))

# a root is a function of its bindings, over any root
law Mst.canon:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Canon(S, Mst.ops(~S, ~fetch))

# a listing holds exactly the bindings under its prefix, in order
law Mst.lists:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Range(S, Mst.ops(~S, ~fetch))

# a difference lists exactly the keys that read differently
law Mst.differs:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Diff(S, Mst.ops(~S, ~fetch))

# a whole tree answers every read, write, listing and difference
law Mst.whole:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Whole(S, Mst.ops(~S, ~fetch))

# a write keeps a whole tree whole
law Mst.keeps_whole:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Kept(S, fetch, grows, Mst.ops(~S, ~fetch))
