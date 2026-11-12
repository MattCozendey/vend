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

# the read l found that the tree does not hold the key
def Look.is_absent(l: Look) -> Bool:
  match l:
    case Look.Absent{}:
      True{}
    case _:
      False{}

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
# new nodes, the new root reads the key as written, and tells of every other
# key what the old root tells (a read that could not tell may tell after)
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
      @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> {
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
      } -> {
        Look.known(Ops.look(S, o)(s2)(h)(k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {Look.known(Ops.look(S, o)(s2)(Edit.root(e))(k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
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

# Rooms
# -----
# A read or a write opens a node only where it may sit: below the level of its
# parent, with an item, and with its keys in order between the keys beside it
# in its parent. So in any tree that a read or a write walks, the levels fall
# along each path, no path outruns Mst.depth, and a key is where the order of
# keys puts it.

# where a subtree sits: its node has a level below up, and keys after lo and
# before hi (none: no bound)
type Room is Data:
  Room{up: Nat, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>}

# no tree is deeper than this many levels, and no level of a node reaches
# it: levels fall along each path
def Mst.depth() -> Nat:
  64n

# the room of a root
def Room.top() -> Room:
  Room{Mst.depth(), None{}, None{}}

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

# the keys of the items xs come in order, after lo and before hi
def Items.fit(xs: List<&2, Item>, lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Item{+k, v, r}, rest}:
      Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Items.fit(rest, Some{k}, hi))

# the key of the first of the items xs, else m
def Items.head_key(xs: List<&2, Item>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      m
    case Con{Item{k, v, r}, rest}:
      Some{k}

# the key of the last of the items xs, else m
def Items.last_key(xs: List<&2, Item>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      m
    case Con{Item{k, v, r}, rest}:
      Items.last_key(rest, Some{k})

# the node n, when it may sit in the room r
def Node.in(n: Node, r: Room) -> Maybe<&2, Node>:
  match n r:
    case Node{+l, left, +xs} Room{up, lo, hi}:
      Shared.Maybe.when(
        Node,
        Bool.and(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi)),
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

# the node of the hash h, when it may sit in the room r (none: the depot s
# lacks it, or it may not sit there)
def Mst.node.in(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  h: Hashes.Hash,
  r: Room
) -> Maybe<&2, Node>:
  Maybe.bind(&2, Node, Node, Mst.node(~S, ~fetch, s, h), n => Node.in(n, r))

# the room of a subtree of a node of the level l, after the key lo and
# before hi
def Room.of(+l: Nat, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> Room:
  Room{l, lo, hi}

# Reads
# -----

# what a read of a node finds: the value of the key, or the subtree to go on
# in and its room
type Pick is Data:
  Pick.Hit{value: List<&2, U32>}
  Pick.Down{sub: Maybe<&2, Hashes.Hash>, room: Room}

# the pick of the key k among the items xs of a node of the level l, whose
# subtree before them is prev, after the key lo, and before hi
def Mst.pick(xs: List<&2, Item>, prev: Maybe<&2, Hashes.Hash>, +l: Nat, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> Pick:
  match xs:
    case Nil{}:
      Pick.Down{prev, Room.of(l, lo, hi)}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +c = Key.cmp(k, ik)
      Shared.Bool.when(
        Pick,
        Cmp.is_lt(c),
        u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
        u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k))
      )

# the read that a pick in the node of the hash h, of the level l, gives for
# the key k: its value, when the node is of the level of k (else the tree is
# not in its one shape, and the read cannot tell); or the read of its subtree
# (go)
def Mst.look.pick(p: Pick, h: Hashes.Hash, l: Nat, k: List<&2, U32>, go: Maybe<&2, Hashes.Hash> -> Room -> Look) -> Look:
  match p:
    case Pick.Hit{v}:
      Shared.Bool.when(Look, Nat.is_eq(Key.level(k), l), u => Look.Found{v}, u => Look.Missing{h})
    case Pick.Down{m, r}:
      go(m)(r)

# the read of the key k in the node m of the hash h, in the room r, with go
# reading a subtree
def Mst.look.at(h: Hashes.Hash, m: Maybe<&2, Node>, r: Room, +k: List<&2, U32>, go: Maybe<&2, Hashes.Hash> -> Room -> Look) -> Look:
  match m r:
    case None{} x:
      Look.Missing{h}
    case Some{Node{+l, left, xs}} Room{up, lo, hi}:
      Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k), h, l, k, go)

# the read of the key k in the tree of the root m, in the room r, at most f
# levels down
def Mst.look.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +r: Room,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Look:
  match f m:
    case x None{}:
      Look.Absent{}
    case 0n Some{h}:
      Look.Missing{h}
    case 1n+p Some{+h}:
      Mst.look.at(h, Mst.node.in(~S, ~fetch, s, h, r), r, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k))

# the read of the key k in the tree of the root m
def Mst.look(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  s: S,
  m: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Look:
  Mst.look.go(~S, ~fetch, Mst.depth(), s, Room.top(), m, k)

# Writes
# ------
# A write changes only the nodes on the path to its key: an insert splits the
# subtree where the key goes, a delete merges the two subtrees beside it, and
# every node it rebuilds is new; all others stay shared. It opens each node
# in its room, so what it builds from them is in order; a subtree that a
# merge lifts into a wider room has its inner edge read in its old room.

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

# the room of the gap of the part p of a node of the level l, after the key
# lo and before hi
def Part.room(p: Part, +l: Nat, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> Room:
  match p:
    case Part{b, g, a}:
      Room.of(l, Items.head_key(b, lo), Items.head_key(a, hi))

# the part p cuts its node at a key k that the node holds
def Part.hits(p: Part, k: List<&2, U32>) -> Bool:
  match p:
    case Part{b, g, Con{Item{ik, iv, r}, rest}}:
      Cmp.is_eq(Key.cmp(ik, k))
    case Part{b, g, Nil{}}:
      False{}

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

# the node m, in the room r, split at the key k, with go splitting a subtree
def Mst.split.at(
  m: Maybe<&2, Node>,
  r: Room,
  +k: List<&2, U32>,
  go: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>
) -> Maybe<&2, Halves>:
  match m r:
    case None{} x:
      None{}
    case Some{Node{+l, +left, xs}} Room{up, lo, hi}:
      +p = Mst.part(xs, left, k, [])
      Shared.Bool.when(
        Maybe<&2, Halves>,
        Part.hits(p, k),
        u => None{},
        u => Mst.split.done(l, left, p, go(Part.room(p, l, lo, hi))(Part.gap(p)))
      )

# the tree of the root m, in the room r, split at the key k, which it lacks,
# at most f levels down (none: a node holds k, so the tree is not in its one
# shape)
def Mst.split(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +r: Room,
  m: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Maybe<&2, Halves>:
  match f m:
    case x None{}:
      Some{Halves{None{}, None{}, []}}
    case 0n Some{h}:
      None{}
    case 1n+p Some{h}:
      Mst.split.at(Mst.node.in(~S, ~fetch, s, h, r), r, k, r2 => c => Mst.split(~S, ~fetch, p, s, r2, c, k))

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

# the subtree m, in the room r, with each node of its left edge in its room
# (go reads the next one): no key of it comes before the lower bound of r,
# even once that bound widens
def Mst.edge.left.at(m: Maybe<&2, Node>, r: Room, go: Room -> Maybe<&2, Hashes.Hash> -> Bool) -> Bool:
  match m r:
    case None{} x:
      False{}
    case Some{Node{+l, left, xs}} Room{up, lo, hi}:
      go(Room.of(l, lo, Items.head_key(xs, hi)))(left)

# the subtree m, in the room r, with each node of its right edge in its room
# (go reads the next one): no key of it comes after the upper bound of r,
# even once that bound widens
def Mst.edge.right.at(m: Maybe<&2, Node>, r: Room, go: Room -> Maybe<&2, Hashes.Hash> -> Bool) -> Bool:
  match m r:
    case None{} x:
      False{}
    case Some{Node{+l, left, +xs}} Room{up, lo, hi}:
      go(Room.of(l, Items.last_key(xs, lo), hi))(Mst.last(xs, left))

# the nodes of the left (left: True) or right edge of the tree of the root
# m, in the room r, each sit in their rooms, at most f levels down
def Mst.edge(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +left: Bool,
  +r: Room,
  m: Maybe<&2, Hashes.Hash>
) -> Bool:
  match f m:
    case x None{}:
      True{}
    case 0n Some{h}:
      False{}
    case 1n+(+p) Some{h}:
      +n = Mst.node.in(~S, ~fetch, s, h, r)
      Shared.Bool.when(
        Bool,
        left,
        u => Mst.edge.left.at(n, r, r2 => c => Mst.edge(~S, ~fetch, p, s, left, r2, c)),
        u => Mst.edge.right.at(n, r, r2 => c => Mst.edge(~S, ~fetch, p, s, left, r2, c))
      )

# the merge of the node a of the level la, in the room ra, and the node b of
# the level lb, in the room rb, by how la compares to lb (c), with go merging
# two subtrees, each in its room
def Mst.merge.nodes(
  c: Cmp,
  +ha: Hashes.Hash,
  +ra: Room,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +hb: Hashes.Hash,
  +rb: Room,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  go: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match c ra rb:
    case GT{} Room{ua, loa, hia} y:
      Mst.with_last(la, lefta, xa, go(Room.of(la, Items.last_key(xa, loa), hia))(rb)(Mst.last(xa, lefta))(Some{hb}))
    case LT{} x Room{ub, lob, hib}:
      Mst.with_first(lb, xb, go(ra)(Room.of(lb, lob, Items.head_key(xb, hib)))(Some{ha})(leftb))
    case EQ{} Room{ua, loa, hia} Room{ub, lob, hib}:
      Mst.with_both(
        la,
        lefta,
        xa,
        xb,
        go(Room.of(la, Items.last_key(xa, loa), hia))(Room.of(lb, lob, Items.head_key(xb, hib)))(Mst.last(xa, lefta))(leftb)
      )

# the merge of the nodes na, in the room ra, and nb, in the room rb, of the
# hashes ha and hb
def Mst.merge.at(
  na: Maybe<&2, Node>,
  nb: Maybe<&2, Node>,
  +ha: Hashes.Hash,
  +ra: Room,
  +hb: Hashes.Hash,
  +rb: Room,
  go: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match na nb:
    case Some{Node{+la, lefta, xa}} Some{Node{+lb, leftb, xb}}:
      Mst.merge.nodes(Nat.cmp(la, lb), ha, ra, la, lefta, xa, hb, rb, lb, leftb, xb, go)
    case x y:
      None{}

# the tree of the keys of a, in the room ra, then of b, in the room rb, when
# each key of a is before each of b, at most f levels down. A side that stands
# alone rises into the room of both, so the edge that faces the other side
# is read in its old room
def Mst.merge(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +ra: Room,
  +rb: Room,
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Edit>:
  match f a b:
    case x None{} None{}:
      Some{Edit{None{}, []}}
    case x None{} Some{+hb}:
      Shared.Maybe.when(Edit, Mst.edge(~S, ~fetch, Mst.depth(), s, True{}, rb, Some{hb}), u => Some{Edit{Some{hb}, []}})
    case x Some{+ha} None{}:
      Shared.Maybe.when(Edit, Mst.edge(~S, ~fetch, Mst.depth(), s, False{}, ra, Some{ha}), u => Some{Edit{Some{ha}, []}})
    case 0n y z:
      None{}
    case 1n+p Some{+ha} Some{+hb}:
      Mst.merge.at(
        Mst.node.in(~S, ~fetch, s, ha, ra),
        Mst.node.in(~S, ~fetch, s, hb, rb),
        ha,
        ra,
        hb,
        rb,
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y)
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

# the node of the hash h, of the level l, after the key lo and before hi,
# that gets the key k of the level L, by how l compares to L (c): above it a
# new node splits the tree (sp); at it, it takes the key (spg splits its gap);
# below it, the key goes into the gap of its part (ins). A node of another
# level that holds k is not in its one shape: none
def Mst.insert.node(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  xs: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  sp: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spg: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  ins: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match c:
    case LT{}:
      Mst.insert.top(L, k, v, sp(Some{h}))
    case EQ{}:
      +p = Mst.part(xs, left, k, [])
      Mst.insert.here(l, left, k, v, p, spg(Part.room(p, l, lo, hi)))
    case GT{}:
      +p = Mst.part(xs, left, k, [])
      Shared.Bool.when(
        Maybe<&2, Edit>,
        Part.hits(p, k),
        u => None{},
        u => Mst.with_gap(l, left, p, ins(Part.room(p, l, lo, hi))(Part.gap(p)))
      )

# the node m of the hash h, in the room r, with the key k of the level L
# bound to v
def Mst.insert.at(
  m: Maybe<&2, Node>,
  +h: Hashes.Hash,
  r: Room,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  sp: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spg: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  ins: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>
) -> Maybe<&2, Edit>:
  match m r:
    case None{} x:
      None{}
    case Some{Node{+l, left, xs}} Room{up, lo, hi}:
      Mst.insert.node(Nat.cmp(l, L), h, l, left, xs, lo, hi, k, v, L, sp, spg, ins)

# the tree of the root m, in the room r, with the key k, of the level L,
# bound to v, at most f levels down
def Mst.insert(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +r: Room,
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
        Mst.node.in(~S, ~fetch, s, h, r),
        h,
        r,
        k,
        v,
        L,
        c => Mst.split(~S, ~fetch, p, s, r, c, k),
        r2 => c => Mst.split(~S, ~fetch, p, s, r2, c, k),
        r2 => c => Mst.insert(~S, ~fetch, p, s, r2, c, k, v, L)
      )

# the tree of the hash h, unchanged, once a read (lk) finds k absent from its
# subtree m in the room r; else none: the tree holds k where it does not
# belong, or the read cannot tell
def Mst.delete.none(+h: Hashes.Hash, r: Room, m: Maybe<&2, Hashes.Hash>, lk: Room -> Maybe<&2, Hashes.Hash> -> Look) -> Maybe<&2, Edit>:
  Shared.Maybe.when(Edit, Look.is_absent(lk(r)(m)), u => Some{Edit{Some{h}, []}})

# a node of the level l, after the key lo and before hi, split at k by its
# part p, without the key k: the two subtrees beside k merge (mg); a node
# that lacks k stays (h), once its gap lacks k too (lk)
def Mst.delete.here(
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  p: Part,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  mg: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lk: Room -> Maybe<&2, Hashes.Hash> -> Look
) -> Maybe<&2, Edit>:
  match p:
    case Part{+b, +g, Con{Item{+ik, iv, +r}, +rest}}:
      Shared.Bool.when(
        Maybe<&2, Edit>,
        Cmp.is_eq(Key.cmp(ik, k)),
        u => Mst.with_gap(
          l,
          left,
          Part{b, g, rest},
          mg(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r)
        ),
        u => Mst.delete.none(h, Room.of(l, Items.head_key(b, lo), Some{ik}), g, lk)
      )
    case Part{b, g, Nil{}}:
      Mst.delete.none(h, Room.of(l, Items.head_key(b, lo), hi), g, lk)

# the pick p of k in a node lacks k, and so does the subtree it goes on in
# (lk reads)
def Mst.delete.lacks(p: Pick, lk: Room -> Maybe<&2, Hashes.Hash> -> Look) -> Bool:
  match p:
    case Pick.Hit{v}:
      False{}
    case Pick.Down{m, r}:
      Look.is_absent(lk(r)(m))

# the node of the hash h, of the level l, after the key lo and before hi,
# without the key k of the level L, by how l compares to L (c). Below it, k is
# not there, once a read (lk) finds it absent; a node of another level that
# holds k is not in its one shape: none
def Mst.delete.node(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  xs: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  mg: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  del: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lk: Room -> Maybe<&2, Hashes.Hash> -> Look
) -> Maybe<&2, Edit>:
  match c:
    case LT{}:
      Shared.Maybe.when(Edit, Mst.delete.lacks(Mst.pick(xs, left, l, lo, hi, k), lk), u => Some{Edit{Some{h}, []}})
    case EQ{}:
      Mst.delete.here(h, l, left, k, Mst.part(xs, left, k, []), lo, hi, mg, lk)
    case GT{}:
      +p = Mst.part(xs, left, k, [])
      Shared.Bool.when(
        Maybe<&2, Edit>,
        Part.hits(p, k),
        u => None{},
        u => Mst.with_gap(l, left, p, del(Part.room(p, l, lo, hi))(Part.gap(p)))
      )

# the node m of the hash h, in the room r, without the key k of the level L
def Mst.delete.at(
  m: Maybe<&2, Node>,
  +h: Hashes.Hash,
  r: Room,
  +k: List<&2, U32>,
  +L: Nat,
  mg: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  del: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lk: Room -> Maybe<&2, Hashes.Hash> -> Look
) -> Maybe<&2, Edit>:
  match m r:
    case None{} x:
      None{}
    case Some{Node{+l, left, xs}} Room{up, lo, hi}:
      Mst.delete.node(Nat.cmp(l, L), h, l, left, xs, lo, hi, k, mg, del, lk)

# the tree of the root m, in the room r, without the key k, of the level L,
# at most f levels down
def Mst.delete(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +r: Room,
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
        Mst.node.in(~S, ~fetch, s, h, r),
        h,
        r,
        k,
        L,
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y),
        r2 => c => Mst.delete(~S, ~fetch, p, s, r2, c, k, L),
        r2 => c => Mst.look.go(~S, ~fetch, p, s, r2, c, k)
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
      Mst.insert(~S, ~fetch, Mst.depth(), s, Room.top(), m, k, v, Key.level(k))
    case None{}:
      Mst.delete(~S, ~fetch, Mst.depth(), s, Room.top(), m, k, Key.level(k))

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

# Proofs of reads and writes
# --------------------------

# the value whose code m1 holds, m2 holds too, when m2 holds the words of m1
def Mst.whole_kept(
  m1: Maybe<&2, List<&2, U32>>,
  -m2: Maybe<&2, List<&2, U32>>,
  -n: Node,
  hm: @w: List<&2, U32> -> {m1 == Some{w}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {
  Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, m1) == Some{n}: Maybe<&2, Node>
} -> {Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, m2) == Some{n}: Maybe<&2, Node>}:
  match m1:
    case None{}:
      e => Empty.absurd(
        {Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, m2) == Some{n}: Maybe<&2, Node>},
        Shared.Maybe.none_ne_some(Node, n, e)
      )
    case Some{w}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, m2, Some{w}, hm(w)({==})): (
        {Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, Some{w}) == Some{n}: Maybe<&2, Node>}
          -> {Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, _) == Some{n}: Maybe<&2, Node>}
      )
      e => e

# a node that a depot gives, a depot that grows from it gives too
def Mst.node_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  +a: S,
  b: S,
  +h: Hashes.Hash,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {Mst.node(~S, ~fetch, a, h) == Some{n}: Maybe<&2, Node>} -> {Mst.node(~S, ~fetch, b, h) == Some{n}: Maybe<&2, Node>}:
  Mst.whole_kept(fetch(a)(h), fetch(b)(h), n, w => e => kept(a)(b)(h)(w)(gr)(e))

# a node that a depot gives in a room, a depot that grows from it gives too
def Mst.node_in_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  +a: S,
  +b: S,
  +h: Hashes.Hash,
  +r: Room,
  -n: Node,
  gr: {grows(a, b) == True{}: Bool}
) -> {
  Mst.node.in(~S, ~fetch, a, h, r) == Some{n}: Maybe<&2, Node>
} -> {Mst.node.in(~S, ~fetch, b, h, r) == Some{n}: Maybe<&2, Node>}:
  Shared.Maybe.bind_kept(
    Node,
    Node,
    Mst.node(~S, ~fetch, a, h),
    Mst.node(~S, ~fetch, b, h),
    m => Node.in(m, r),
    m => Node.in(m, r),
    n,
    m => Mst.node_kept(~S, ~fetch, ~grows, ~kept, a, b, h, m, gr),
    m => e => e
  )

# what a pick tells, it tells with any reader of subtrees that tells the same
def Mst.look.pick_kept(
  p: Pick,
  -h: Hashes.Hash,
  -l: Nat,
  -k: List<&2, U32>,
  -goa: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -gob: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -x: Maybe<&2, List<&2, U32>>,
  hg: @m: Maybe<&2, Hashes.Hash> -> @r: Room -> {
    Look.known(goa(m)(r)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Look.known(gob(m)(r)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Look.known(Mst.look.pick(p, h, l, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.pick(p, h, l, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match p:
    case Pick.Hit{v}:
      e => e
    case Pick.Down{m, r}:
      hg(m)(r)

# what a read of a node tells, it tells of the same node, with a reader of
# subtrees that tells the same
def Mst.look.at_kept(
  -h: Hashes.Hash,
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  k: List<&2, U32>,
  -goa: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -gob: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -x: Maybe<&2, List<&2, U32>>,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hg: @m: Maybe<&2, Hashes.Hash> -> @r2: Room -> {
    Look.known(goa(m)(r2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Look.known(gob(m)(r2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Look.known(Mst.look.at(h, na, r, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.at(h, nb, r, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match na r:
    case None{} r0:
      e => Empty.absurd(
        {Look.known(Mst.look.at(h, nb, r0, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): (
        {Look.known(Mst.look.at(h, Some{Node{l, left, xs}}, Room{up, lo, hi}, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.at(h, _, Room{up, lo, hi}, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.look.pick_kept(Mst.pick(xs, left, l, lo, hi, k), h, l, k, goa, gob, x, hg)

# what a read tells, a depot that grows from it tells too
def Mst.look.go_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +r: Room,
  +k: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Look.known(Mst.look.go(~S, ~fetch, f, a, r, m, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.go(~S, ~fetch, f, b, r, m, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match f m:
    case f0 None{}:
      e => e
    case 0n Some{h}:
      e => e
    case 1n+p Some{+h}:
      Mst.look.at_kept(
        h,
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        k,
        m2 => r2 => Mst.look.go(~S, ~fetch, p, a, r2, m2, k),
        m2 => r2 => Mst.look.go(~S, ~fetch, p, b, r2, m2, k),
        x,
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        m2 => r2 => Mst.look.go_kept(~S, ~fetch, ~grows, ~kept, p, m2, a, b, r2, k, x, gr)
      )

# a read ma that gives a value, mb gives too
def Mst.Kept(-A: Data, -ma: Maybe<&2, A>, -mb: Maybe<&2, A>) -> Type:
  @x: A -> {ma == Some{x}: Maybe<&2, A>} -> {mb == Some{x}: Maybe<&2, A>}

# a step F that gives nothing of nothing keeps what it reads kept
def Mst.kept.app(
  -A: Data,
  -B: Data,
  -F: Maybe<&2, A> -> Maybe<&2, B>,
  ma: Maybe<&2, A>,
  -mb: Maybe<&2, A>,
  hn: {F(None{}) == None{}: Maybe<&2, B>},
  hm: Mst.Kept(A, ma, mb)
) -> Mst.Kept(B, F(ma), F(mb)):
  match ma:
    case None{}:
      x => e => Empty.absurd(
        {F(mb) == Some{x}: Maybe<&2, B>},
        Shared.Maybe.none_ne_some(
          B,
          x,
          Equal.trans(Maybe<&2, B>, None{}, F(None{}), Some{x}, Equal.sym(Maybe<&2, B>, F(None{}), None{}, hn), e)
        )
      )
    case Some{+y}:
      %Equal.sym(Maybe<&2, A>, mb, Some{y}, hm(y)({==})): Mst.Kept(B, F(Some{y}), F(_))
      x => e => e

# a choice keeps what each of its branches keeps
def Mst.kept.when(
  -A: Data,
  b: Bool,
  -ka: Unit -> Maybe<&2, A>,
  -kb: Unit -> Maybe<&2, A>,
  -ea: Unit -> Maybe<&2, A>,
  -eb: Unit -> Maybe<&2, A>,
  hk: Mst.Kept(A, ka(Unit{}), kb(Unit{})),
  he: Mst.Kept(A, ea(Unit{}), eb(Unit{}))
) -> Mst.Kept(A, Shared.Bool.when(Maybe<&2, A>, b, ka, ea), Shared.Bool.when(Maybe<&2, A>, b, kb, eb)):
  match b:
    case True{}:
      hk
    case False{}:
      he

# a test that stays true keeps what its branch keeps
def Mst.kept.mwhen(
  -A: Data,
  ba: Bool,
  -bb: Bool,
  -ka: Unit -> Maybe<&2, A>,
  -kb: Unit -> Maybe<&2, A>,
  hb: {ba == True{}: Bool} -> {bb == True{}: Bool},
  hk: Mst.Kept(A, ka(Unit{}), kb(Unit{}))
) -> Mst.Kept(A, Shared.Maybe.when(A, ba, ka), Shared.Maybe.when(A, bb, kb)):
  match ba:
    case True{}:
      %Equal.sym(Bool, bb, True{}, hb({==})): Mst.Kept(A, ka(Unit{}), Shared.Maybe.when(A, _, kb))
      hk
    case False{}:
      x => e => Empty.absurd(
        {Shared.Maybe.when(A, bb, kb) == Some{x}: Maybe<&2, A>},
        Shared.Maybe.none_ne_some(A, x, e)
      )

# a read that finds a key absent tells that it is absent
def Look.absent_known(l: Look) -> {Look.is_absent(l) == True{}: Bool} -> {
  Look.known(l) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match l:
    case Look.Found{v}:
      e => Empty.absurd(
        {Look.known(Look.Found{v}) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Bool.false_ne_true(e)
      )
    case Look.Absent{}:
      e => {==}
    case Look.Missing{h}:
      e => Empty.absurd(
        {Look.known(Look.Missing{h}) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Bool.false_ne_true(e)
      )

# a read that tells that a key is absent finds it absent
def Look.known_absent(l: Look) -> {
  Look.known(l) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.is_absent(l) == True{}: Bool}:
  match l:
    case Look.Found{v}:
      e => Empty.absurd(
        {Look.is_absent(Look.Found{v}) == True{}: Bool},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.sym(
            Maybe<&2, List<&2, U32>>,
            Some{v},
            None{},
            Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{v}, None{}, e)
          )
        )
      )
    case Look.Absent{}:
      e => {==}
    case Look.Missing{h}:
      e => Empty.absurd(
        {Look.is_absent(Look.Missing{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, None{}, e)
      )

# a read that finds a key absent, a depot that grows from it finds so too
def Mst.look.absent_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  +f: Nat,
  +m: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +r: Room,
  +k: List<&2, U32>,
  +gr: {grows(a, b) == True{}: Bool}
) -> {
  Look.is_absent(Mst.look.go(~S, ~fetch, f, a, r, m, k)) == True{}: Bool
} -> {Look.is_absent(Mst.look.go(~S, ~fetch, f, b, r, m, k)) == True{}: Bool}:
  e => Look.known_absent(Mst.look.go(~S, ~fetch, f, b, r, m, k))(
    Mst.look.go_kept(~S, ~fetch, ~grows, ~kept, f, m, a, b, r, k, None{}, gr)(
      Look.absent_known(Mst.look.go(~S, ~fetch, f, a, r, m, k))(e)
    )
  )

# Mst.split.done keeps what the split of its gap keeps
def Mst.split.done_kept(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  p: Part,
  ma: Maybe<&2, Halves>,
  -mb: Maybe<&2, Halves>,
  hm: Mst.Kept(Halves, ma, mb)
) -> Mst.Kept(Halves, Mst.split.done(l, left, p, ma), Mst.split.done(l, left, p, mb)):
  match p:
    case Part{+b, +g, +a}:
      Mst.kept.app(Halves, Halves, m => Mst.split.done(l, left, Part{b, g, a}, m), ma, mb, {==}, hm)

# Mst.split.at keeps what its node and the splits below it keep
def Mst.split.at_kept(
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  +k: List<&2, U32>,
  goa: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -gob: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hg: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, goa(r2)(c), gob(r2)(c))
) -> Mst.Kept(Halves, Mst.split.at(na, r, k, goa), Mst.split.at(nb, r, k, gob)):
  match na r:
    case None{} r0:
      x => e => Empty.absurd(
        {Mst.split.at(nb, r0, k, gob) == Some{x}: Maybe<&2, Halves>},
        Shared.Maybe.none_ne_some(Halves, x, e)
      )
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): Mst.Kept(
        Halves,
        Mst.split.at(Some{Node{l, left, xs}}, Room{up, lo, hi}, k, goa),
        Mst.split.at(_, Room{up, lo, hi}, k, gob)
      )
      Mst.kept.when(
        Halves,
        Part.hits(Mst.part(xs, left, k, []), k),
        u => None{},
        u => None{},
        u => Mst.split.done(
          l,
          left,
          Mst.part(xs, left, k, []),
          goa(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        u => Mst.split.done(
          l,
          left,
          Mst.part(xs, left, k, []),
          gob(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        x => e => e,
        Mst.split.done_kept(
          l,
          left,
          Mst.part(xs, left, k, []),
          goa(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          gob(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          hg(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        )
      )

# a split that a depot gives, a depot that grows from it gives too
def Mst.split_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +r: Room,
  +k: List<&2, U32>,
  +gr: {grows(a, b) == True{}: Bool}
) -> Mst.Kept(Halves, Mst.split(~S, ~fetch, f, a, r, m, k), Mst.split(~S, ~fetch, f, b, r, m, k)):
  match f m:
    case f0 None{}:
      x => e => e
    case 0n Some{h}:
      x => e => e
    case 1n+(+p) Some{+h}:
      Mst.split.at_kept(
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        k,
        r2 => c => Mst.split(~S, ~fetch, p, a, r2, c, k),
        r2 => c => Mst.split(~S, ~fetch, p, b, r2, c, k),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        r2 => c => Mst.split_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r2, k, gr)
      )

# an edge walk of a node that a depot gives keeps what the walk below keeps
def Mst.edge.left.at_kept(
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  -goa: Room -> Maybe<&2, Hashes.Hash> -> Bool,
  -gob: Room -> Maybe<&2, Hashes.Hash> -> Bool,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hg: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> {goa(r2)(c) == True{}: Bool} -> {gob(r2)(c) == True{}: Bool}
) -> {Mst.edge.left.at(na, r, goa) == True{}: Bool} -> {Mst.edge.left.at(nb, r, gob) == True{}: Bool}:
  match na r:
    case None{} r0:
      e => Empty.absurd({Mst.edge.left.at(nb, r0, gob) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): (
        {Mst.edge.left.at(Some{Node{l, left, xs}}, Room{up, lo, hi}, goa) == True{}: Bool}
          -> {Mst.edge.left.at(_, Room{up, lo, hi}, gob) == True{}: Bool}
      )
      hg(Room.of(l, lo, Items.head_key(xs, hi)))(left)

# Mst.edge.left.at_kept, on the right edge
def Mst.edge.right.at_kept(
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  -goa: Room -> Maybe<&2, Hashes.Hash> -> Bool,
  -gob: Room -> Maybe<&2, Hashes.Hash> -> Bool,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hg: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> {goa(r2)(c) == True{}: Bool} -> {gob(r2)(c) == True{}: Bool}
) -> {Mst.edge.right.at(na, r, goa) == True{}: Bool} -> {Mst.edge.right.at(nb, r, gob) == True{}: Bool}:
  match na r:
    case None{} r0:
      e => Empty.absurd({Mst.edge.right.at(nb, r0, gob) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): (
        {Mst.edge.right.at(Some{Node{l, left, xs}}, Room{up, lo, hi}, goa) == True{}: Bool}
          -> {Mst.edge.right.at(_, Room{up, lo, hi}, gob) == True{}: Bool}
      )
      hg(Room.of(l, Items.last_key(xs, lo), hi))(Mst.last(xs, left))

# an edge that a depot gives in its rooms, a depot that grows from it gives too
def Mst.edge_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  left: Bool,
  +a: S,
  +b: S,
  +r: Room,
  +gr: {grows(a, b) == True{}: Bool}
) -> {Mst.edge(~S, ~fetch, f, a, left, r, m) == True{}: Bool} -> {Mst.edge(~S, ~fetch, f, b, left, r, m) == True{}: Bool}:
  match f m left:
    case f0 None{} l0:
      e => e
    case 0n Some{h} l0:
      e => e
    case 1n+(+p) Some{+h} True{}:
      Mst.edge.left.at_kept(
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        r2 => c => Mst.edge(~S, ~fetch, p, a, True{}, r2, c),
        r2 => c => Mst.edge(~S, ~fetch, p, b, True{}, r2, c),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        r2 => c => Mst.edge_kept(~S, ~fetch, ~grows, ~kept, p, c, True{}, a, b, r2, gr)
      )
    case 1n+(+p) Some{+h} False{}:
      Mst.edge.right.at_kept(
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        r2 => c => Mst.edge(~S, ~fetch, p, a, False{}, r2, c),
        r2 => c => Mst.edge(~S, ~fetch, p, b, False{}, r2, c),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        r2 => c => Mst.edge_kept(~S, ~fetch, ~grows, ~kept, p, c, False{}, a, b, r2, gr)
      )

# Mst.merge.nodes keeps what the merge below it keeps
def Mst.merge.nodes_kept(
  c: Cmp,
  +ha: Hashes.Hash,
  ra: Room,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +hb: Hashes.Hash,
  rb: Room,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  goa: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -gob: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  hg: @r1: Room -> @r2: Room -> @x: Maybe<&2, Hashes.Hash> -> @y: Maybe<&2, Hashes.Hash> -> Mst.Kept(
    Edit,
    goa(r1)(r2)(x)(y),
    gob(r1)(r2)(x)(y)
  )
) -> Mst.Kept(
  Edit,
  Mst.merge.nodes(c, ha, ra, la, lefta, xa, hb, rb, lb, leftb, xb, goa),
  Mst.merge.nodes(c, ha, ra, la, lefta, xa, hb, rb, lb, leftb, xb, gob)
):
  match c ra rb:
    case GT{} Room{+ua, +loa, +hia} Room{+ub, +lob, +hib}:
      Mst.kept.app(
        Edit,
        Edit,
        e => Mst.with_last(la, lefta, xa, e),
        goa(Room.of(la, Items.last_key(xa, loa), hia))(Room{ub, lob, hib})(Mst.last(xa, lefta))(Some{hb}),
        gob(Room.of(la, Items.last_key(xa, loa), hia))(Room{ub, lob, hib})(Mst.last(xa, lefta))(Some{hb}),
        {==},
        hg(Room.of(la, Items.last_key(xa, loa), hia))(Room{ub, lob, hib})(Mst.last(xa, lefta))(Some{hb})
      )
    case LT{} Room{+ua, +loa, +hia} Room{+ub, +lob, +hib}:
      Mst.kept.app(
        Edit,
        Edit,
        e => Mst.with_first(lb, xb, e),
        goa(Room{ua, loa, hia})(Room.of(lb, lob, Items.head_key(xb, hib)))(Some{ha})(leftb),
        gob(Room{ua, loa, hia})(Room.of(lb, lob, Items.head_key(xb, hib)))(Some{ha})(leftb),
        {==},
        hg(Room{ua, loa, hia})(Room.of(lb, lob, Items.head_key(xb, hib)))(Some{ha})(leftb)
      )
    case EQ{} Room{+ua, +loa, +hia} Room{+ub, +lob, +hib}:
      Mst.kept.app(
        Edit,
        Edit,
        e => Mst.with_both(la, lefta, xa, xb, e),
        goa(Room.of(la, Items.last_key(xa, loa), hia))(Room.of(lb, lob, Items.head_key(xb, hib)))(Mst.last(xa, lefta))(leftb),
        gob(Room.of(la, Items.last_key(xa, loa), hia))(Room.of(lb, lob, Items.head_key(xb, hib)))(Mst.last(xa, lefta))(leftb),
        {==},
        hg(Room.of(la, Items.last_key(xa, loa), hia))(Room.of(lb, lob, Items.head_key(xb, hib)))(Mst.last(xa, lefta))(leftb)
      )

# Mst.merge.at keeps what its nodes and the merge below them keep
def Mst.merge.at_kept(
  na: Maybe<&2, Node>,
  nb: Maybe<&2, Node>,
  -na2: Maybe<&2, Node>,
  -nb2: Maybe<&2, Node>,
  +ha: Hashes.Hash,
  +ra: Room,
  +hb: Hashes.Hash,
  +rb: Room,
  goa: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -gob: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  hna: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {na2 == Some{n}: Maybe<&2, Node>},
  hnb: @n: Node -> {nb == Some{n}: Maybe<&2, Node>} -> {nb2 == Some{n}: Maybe<&2, Node>},
  hg: @r1: Room -> @r2: Room -> @x: Maybe<&2, Hashes.Hash> -> @y: Maybe<&2, Hashes.Hash> -> Mst.Kept(
    Edit,
    goa(r1)(r2)(x)(y),
    gob(r1)(r2)(x)(y)
  )
) -> Mst.Kept(Edit, Mst.merge.at(na, nb, ha, ra, hb, rb, goa), Mst.merge.at(na2, nb2, ha, ra, hb, rb, gob)):
  match na nb:
    case Some{Node{+la, +lefta, +xa}} Some{Node{+lb, +leftb, +xb}}:
      %Equal.sym(Maybe<&2, Node>, na2, Some{Node{la, lefta, xa}}, hna(Node{la, lefta, xa})({==})): Mst.Kept(
        Edit,
        Mst.merge.at(Some{Node{la, lefta, xa}}, Some{Node{lb, leftb, xb}}, ha, ra, hb, rb, goa),
        Mst.merge.at(_, nb2, ha, ra, hb, rb, gob)
      )
      %Equal.sym(Maybe<&2, Node>, nb2, Some{Node{lb, leftb, xb}}, hnb(Node{lb, leftb, xb})({==})): Mst.Kept(
        Edit,
        Mst.merge.at(Some{Node{la, lefta, xa}}, Some{Node{lb, leftb, xb}}, ha, ra, hb, rb, goa),
        Mst.merge.at(Some{Node{la, lefta, xa}}, _, ha, ra, hb, rb, gob)
      )
      Mst.merge.nodes_kept(Nat.cmp(la, lb), ha, ra, la, lefta, xa, hb, rb, lb, leftb, xb, goa, gob, hg)
    case Some{Node{la, lefta, xa}} None{}:
      x => e => Empty.absurd(
        {Mst.merge.at(na2, nb2, ha, ra, hb, rb, gob) == Some{x}: Maybe<&2, Edit>},
        Shared.Maybe.none_ne_some(Edit, x, e)
      )
    case None{} y0:
      x => e => Empty.absurd(
        {Mst.merge.at(na2, nb2, ha, ra, hb, rb, gob) == Some{x}: Maybe<&2, Edit>},
        Shared.Maybe.none_ne_some(Edit, x, e)
      )

# a merge that a depot gives, a depot that grows from it gives too
def Mst.merge_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  ma: Maybe<&2, Hashes.Hash>,
  mb: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +ra: Room,
  +rb: Room,
  +gr: {grows(a, b) == True{}: Bool}
) -> Mst.Kept(Edit, Mst.merge(~S, ~fetch, f, a, ra, rb, ma, mb), Mst.merge(~S, ~fetch, f, b, ra, rb, ma, mb)):
  match f ma mb:
    case f0 None{} None{}:
      x => e => e
    case f0 None{} Some{+hb}:
      Mst.kept.mwhen(
        Edit,
        Mst.edge(~S, ~fetch, Mst.depth(), a, True{}, rb, Some{hb}),
        Mst.edge(~S, ~fetch, Mst.depth(), b, True{}, rb, Some{hb}),
        u => Some{Edit{Some{hb}, []}},
        u => Some{Edit{Some{hb}, []}},
        Mst.edge_kept(~S, ~fetch, ~grows, ~kept, Mst.depth(), Some{hb}, True{}, a, b, rb, gr),
        x => e => e
      )
    case f0 Some{+ha} None{}:
      Mst.kept.mwhen(
        Edit,
        Mst.edge(~S, ~fetch, Mst.depth(), a, False{}, ra, Some{ha}),
        Mst.edge(~S, ~fetch, Mst.depth(), b, False{}, ra, Some{ha}),
        u => Some{Edit{Some{ha}, []}},
        u => Some{Edit{Some{ha}, []}},
        Mst.edge_kept(~S, ~fetch, ~grows, ~kept, Mst.depth(), Some{ha}, False{}, a, b, ra, gr),
        x => e => e
      )
    case 0n Some{ha} Some{hb}:
      x => e => e
    case 1n+(+p) Some{+ha} Some{+hb}:
      Mst.merge.at_kept(
        Mst.node.in(~S, ~fetch, a, ha, ra),
        Mst.node.in(~S, ~fetch, a, hb, rb),
        Mst.node.in(~S, ~fetch, b, ha, ra),
        Mst.node.in(~S, ~fetch, b, hb, rb),
        ha,
        ra,
        hb,
        rb,
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, a, r1, r2, x, y),
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, b, r1, r2, x, y),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, ha, ra, n, gr),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, hb, rb, n, gr),
        r1 => r2 => x => y => Mst.merge_kept(~S, ~fetch, ~grows, ~kept, p, x, y, a, b, r1, r2, gr)
      )

# Mst.with_gap keeps what the edit of its gap keeps
def Mst.with_gap_kept(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  p: Part,
  ea: Maybe<&2, Edit>,
  -eb: Maybe<&2, Edit>,
  he: Mst.Kept(Edit, ea, eb)
) -> Mst.Kept(Edit, Mst.with_gap(l, left, p, ea), Mst.with_gap(l, left, p, eb)):
  match p:
    case Part{+b, +g, +a}:
      Mst.kept.app(Edit, Edit, e => Mst.with_gap(l, left, Part{b, g, a}, e), ea, eb, {==}, he)

# Mst.insert.gap keeps what the split of its gap keeps
def Mst.insert.gap_kept(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  p: Part,
  ma: Maybe<&2, Halves>,
  -mb: Maybe<&2, Halves>,
  hm: Mst.Kept(Halves, ma, mb)
) -> Mst.Kept(Edit, Mst.insert.gap(l, left, k, v, p, ma), Mst.insert.gap(l, left, k, v, p, mb)):
  match p:
    case Part{+b, +g, +a}:
      Mst.kept.app(Halves, Edit, m => Mst.insert.gap(l, left, k, v, Part{b, g, a}, m), ma, mb, {==}, hm)

# Mst.insert.here keeps what the split of its gap keeps
def Mst.insert.here_kept(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  p: Part,
  spa: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -spb: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  hs: @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, spa(c), spb(c))
) -> Mst.Kept(Edit, Mst.insert.here(l, left, k, v, p, spa), Mst.insert.here(l, left, k, v, p, spb)):
  match p:
    case Part{+b, +g, Con{Item{+ik, +iv, +r}, +rest}}:
      Mst.kept.when(
        Edit,
        Cmp.is_eq(Key.cmp(ik, k)),
        u => Some{Mst.store(Node{l, left, Mst.rejoin(b, g, Item{k, v, r} <> rest)}, [])},
        u => Some{Mst.store(Node{l, left, Mst.rejoin(b, g, Item{k, v, r} <> rest)}, [])},
        u => Mst.insert.gap(l, left, k, v, Part{b, g, Item{ik, iv, r} <> rest}, spa(g)),
        u => Mst.insert.gap(l, left, k, v, Part{b, g, Item{ik, iv, r} <> rest}, spb(g)),
        x => e => e,
        Mst.insert.gap_kept(l, left, k, v, Part{b, g, Item{ik, iv, r} <> rest}, spa(g), spb(g), hs(g))
      )
    case Part{+b, +g, Nil{}}:
      Mst.insert.gap_kept(l, left, k, v, Part{b, g, []}, spa(g), spb(g), hs(g))

# Mst.insert.node keeps what the splits and inserts below it keep
def Mst.insert.node_kept(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  spa: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -spb: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spga: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -spgb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  insa: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -insb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  hs: @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, spa(c), spb(c)),
  hsg: @r: Room -> @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, spga(r)(c), spgb(r)(c)),
  hins: @r: Room -> @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Edit, insa(r)(c), insb(r)(c))
) -> Mst.Kept(
  Edit,
  Mst.insert.node(c, h, l, left, xs, lo, hi, k, v, L, spa, spga, insa),
  Mst.insert.node(c, h, l, left, xs, lo, hi, k, v, L, spb, spgb, insb)
):
  match c:
    case LT{}:
      Mst.kept.app(Halves, Edit, m => Mst.insert.top(L, k, v, m), spa(Some{h}), spb(Some{h}), {==}, hs(Some{h}))
    case EQ{}:
      Mst.insert.here_kept(
        l,
        left,
        k,
        v,
        Mst.part(xs, left, k, []),
        spga(Part.room(Mst.part(xs, left, k, []), l, lo, hi)),
        spgb(Part.room(Mst.part(xs, left, k, []), l, lo, hi)),
        hsg(Part.room(Mst.part(xs, left, k, []), l, lo, hi))
      )
    case GT{}:
      Mst.kept.when(
        Edit,
        Part.hits(Mst.part(xs, left, k, []), k),
        u => None{},
        u => None{},
        u => Mst.with_gap(
          l,
          left,
          Mst.part(xs, left, k, []),
          insa(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        u => Mst.with_gap(
          l,
          left,
          Mst.part(xs, left, k, []),
          insb(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        x => e => e,
        Mst.with_gap_kept(
          l,
          left,
          Mst.part(xs, left, k, []),
          insa(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          insb(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          hins(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        )
      )

# Mst.insert.at keeps what its node and the writes below it keep
def Mst.insert.at_kept(
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  spa: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -spb: Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  spga: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  -spgb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Halves>,
  insa: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -insb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hs: @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, spa(c), spb(c)),
  hsg: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Halves, spga(r2)(c), spgb(r2)(c)),
  hins: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> Mst.Kept(Edit, insa(r2)(c), insb(r2)(c))
) -> Mst.Kept(
  Edit,
  Mst.insert.at(na, h, r, k, v, L, spa, spga, insa),
  Mst.insert.at(nb, h, r, k, v, L, spb, spgb, insb)
):
  match na r:
    case None{} r0:
      x => e => Empty.absurd(
        {Mst.insert.at(nb, h, r0, k, v, L, spb, spgb, insb) == Some{x}: Maybe<&2, Edit>},
        Shared.Maybe.none_ne_some(Edit, x, e)
      )
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): Mst.Kept(
        Edit,
        Mst.insert.at(Some{Node{l, left, xs}}, h, Room{up, lo, hi}, k, v, L, spa, spga, insa),
        Mst.insert.at(_, h, Room{up, lo, hi}, k, v, L, spb, spgb, insb)
      )
      Mst.insert.node_kept(Nat.cmp(l, L), h, l, left, xs, lo, hi, k, v, L, spa, spb, spga, spgb, insa, insb, hs, hsg, hins)

# an insert that a depot gives, a depot that grows from it gives too
def Mst.insert_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +r: Room,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +L: Nat,
  +gr: {grows(a, b) == True{}: Bool}
) -> Mst.Kept(Edit, Mst.insert(~S, ~fetch, f, a, r, m, k, v, L), Mst.insert(~S, ~fetch, f, b, r, m, k, v, L)):
  match f m:
    case f0 None{}:
      x => e => e
    case 0n Some{h}:
      x => e => e
    case 1n+(+p) Some{+h}:
      Mst.insert.at_kept(
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        h,
        k,
        v,
        L,
        c => Mst.split(~S, ~fetch, p, a, r, c, k),
        c => Mst.split(~S, ~fetch, p, b, r, c, k),
        r2 => c => Mst.split(~S, ~fetch, p, a, r2, c, k),
        r2 => c => Mst.split(~S, ~fetch, p, b, r2, c, k),
        r2 => c => Mst.insert(~S, ~fetch, p, a, r2, c, k, v, L),
        r2 => c => Mst.insert(~S, ~fetch, p, b, r2, c, k, v, L),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        c => Mst.split_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r, k, gr),
        r2 => c => Mst.split_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r2, k, gr),
        r2 => c => Mst.insert_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r2, k, v, L, gr)
      )

# Mst.delete.none keeps what the read of its subtree keeps
def Mst.delete.none_kept(
  +h: Hashes.Hash,
  +r: Room,
  +m: Maybe<&2, Hashes.Hash>,
  lka: Room -> Maybe<&2, Hashes.Hash> -> Look,
  -lkb: Room -> Maybe<&2, Hashes.Hash> -> Look,
  hl: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> {Look.is_absent(lka(r2)(c)) == True{}: Bool} -> {
    Look.is_absent(lkb(r2)(c)) == True{}: Bool
  }
) -> Mst.Kept(Edit, Mst.delete.none(h, r, m, lka), Mst.delete.none(h, r, m, lkb)):
  Mst.kept.mwhen(
    Edit,
    Look.is_absent(lka(r)(m)),
    Look.is_absent(lkb(r)(m)),
    u => Some{Edit{Some{h}, []}},
    u => Some{Edit{Some{h}, []}},
    hl(r)(m),
    x => e => e
  )

# Mst.delete.lacks stays true with a read that keeps what it finds absent
def Mst.delete.lacks_kept(
  p: Pick,
  -lka: Room -> Maybe<&2, Hashes.Hash> -> Look,
  -lkb: Room -> Maybe<&2, Hashes.Hash> -> Look,
  hl: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> {Look.is_absent(lka(r2)(c)) == True{}: Bool} -> {
    Look.is_absent(lkb(r2)(c)) == True{}: Bool
  }
) -> {Mst.delete.lacks(p, lka) == True{}: Bool} -> {Mst.delete.lacks(p, lkb) == True{}: Bool}:
  match p:
    case Pick.Hit{v}:
      e => e
    case Pick.Down{m, r}:
      hl(r)(m)

# Mst.delete.here keeps what the merge and the read below it keep
def Mst.delete.here_kept(
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  p: Part,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  mga: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -mgb: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lka: Room -> Maybe<&2, Hashes.Hash> -> Look,
  -lkb: Room -> Maybe<&2, Hashes.Hash> -> Look,
  hm: @r1: Room -> @r2: Room -> @x: Maybe<&2, Hashes.Hash> -> @y: Maybe<&2, Hashes.Hash> -> Mst.Kept(
    Edit,
    mga(r1)(r2)(x)(y),
    mgb(r1)(r2)(x)(y)
  ),
  hl: @r2: Room -> @c: Maybe<&2, Hashes.Hash> -> {Look.is_absent(lka(r2)(c)) == True{}: Bool} -> {
    Look.is_absent(lkb(r2)(c)) == True{}: Bool
  }
) -> Mst.Kept(
  Edit,
  Mst.delete.here(h, l, left, k, p, lo, hi, mga, lka),
  Mst.delete.here(h, l, left, k, p, lo, hi, mgb, lkb)
):
  match p:
    case Part{+b, +g, Con{Item{+ik, +iv, +r}, +rest}}:
      Mst.kept.when(
        Edit,
        Cmp.is_eq(Key.cmp(ik, k)),
        u => Mst.with_gap(
          l,
          left,
          Part{b, g, rest},
          mga(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r)
        ),
        u => Mst.with_gap(
          l,
          left,
          Part{b, g, rest},
          mgb(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r)
        ),
        u => Mst.delete.none(h, Room.of(l, Items.head_key(b, lo), Some{ik}), g, lka),
        u => Mst.delete.none(h, Room.of(l, Items.head_key(b, lo), Some{ik}), g, lkb),
        Mst.with_gap_kept(
          l,
          left,
          Part{b, g, rest},
          mga(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r),
          mgb(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r),
          hm(Room.of(l, Items.head_key(b, lo), Some{ik}))(Room.of(l, Some{ik}, Items.head_key(rest, hi)))(g)(r)
        ),
        Mst.delete.none_kept(h, Room.of(l, Items.head_key(b, lo), Some{ik}), g, lka, lkb, hl)
      )
    case Part{+b, +g, Nil{}}:
      Mst.delete.none_kept(h, Room.of(l, Items.head_key(b, lo), hi), g, lka, lkb, hl)

# Mst.delete.node keeps what the merges, deletes and reads below it keep
def Mst.delete.node_kept(
  c: Cmp,
  +h: Hashes.Hash,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  mga: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -mgb: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  dela: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -delb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lka: Room -> Maybe<&2, Hashes.Hash> -> Look,
  -lkb: Room -> Maybe<&2, Hashes.Hash> -> Look,
  hm: @r1: Room -> @r2: Room -> @x: Maybe<&2, Hashes.Hash> -> @y: Maybe<&2, Hashes.Hash> -> Mst.Kept(
    Edit,
    mga(r1)(r2)(x)(y),
    mgb(r1)(r2)(x)(y)
  ),
  hd: @r2: Room -> @c2: Maybe<&2, Hashes.Hash> -> Mst.Kept(Edit, dela(r2)(c2), delb(r2)(c2)),
  hl: @r2: Room -> @c2: Maybe<&2, Hashes.Hash> -> {Look.is_absent(lka(r2)(c2)) == True{}: Bool} -> {
    Look.is_absent(lkb(r2)(c2)) == True{}: Bool
  }
) -> Mst.Kept(
  Edit,
  Mst.delete.node(c, h, l, left, xs, lo, hi, k, mga, dela, lka),
  Mst.delete.node(c, h, l, left, xs, lo, hi, k, mgb, delb, lkb)
):
  match c:
    case LT{}:
      Mst.kept.mwhen(
        Edit,
        Mst.delete.lacks(Mst.pick(xs, left, l, lo, hi, k), lka),
        Mst.delete.lacks(Mst.pick(xs, left, l, lo, hi, k), lkb),
        u => Some{Edit{Some{h}, []}},
        u => Some{Edit{Some{h}, []}},
        Mst.delete.lacks_kept(Mst.pick(xs, left, l, lo, hi, k), lka, lkb, hl),
        x => e => e
      )
    case EQ{}:
      Mst.delete.here_kept(h, l, left, k, Mst.part(xs, left, k, []), lo, hi, mga, mgb, lka, lkb, hm, hl)
    case GT{}:
      Mst.kept.when(
        Edit,
        Part.hits(Mst.part(xs, left, k, []), k),
        u => None{},
        u => None{},
        u => Mst.with_gap(
          l,
          left,
          Mst.part(xs, left, k, []),
          dela(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        u => Mst.with_gap(
          l,
          left,
          Mst.part(xs, left, k, []),
          delb(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        ),
        x => e => e,
        Mst.with_gap_kept(
          l,
          left,
          Mst.part(xs, left, k, []),
          dela(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          delb(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, []))),
          hd(Part.room(Mst.part(xs, left, k, []), l, lo, hi))(Part.gap(Mst.part(xs, left, k, [])))
        )
      )

# Mst.delete.at keeps what its node and the steps below it keep
def Mst.delete.at_kept(
  na: Maybe<&2, Node>,
  r: Room,
  -nb: Maybe<&2, Node>,
  +h: Hashes.Hash,
  +k: List<&2, U32>,
  +L: Nat,
  mga: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -mgb: Room -> Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  dela: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  -delb: Room -> Maybe<&2, Hashes.Hash> -> Maybe<&2, Edit>,
  lka: Room -> Maybe<&2, Hashes.Hash> -> Look,
  -lkb: Room -> Maybe<&2, Hashes.Hash> -> Look,
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hm: @r1: Room -> @r2: Room -> @x: Maybe<&2, Hashes.Hash> -> @y: Maybe<&2, Hashes.Hash> -> Mst.Kept(
    Edit,
    mga(r1)(r2)(x)(y),
    mgb(r1)(r2)(x)(y)
  ),
  hd: @r2: Room -> @c2: Maybe<&2, Hashes.Hash> -> Mst.Kept(Edit, dela(r2)(c2), delb(r2)(c2)),
  hl: @r2: Room -> @c2: Maybe<&2, Hashes.Hash> -> {Look.is_absent(lka(r2)(c2)) == True{}: Bool} -> {
    Look.is_absent(lkb(r2)(c2)) == True{}: Bool
  }
) -> Mst.Kept(
  Edit,
  Mst.delete.at(na, h, r, k, L, mga, dela, lka),
  Mst.delete.at(nb, h, r, k, L, mgb, delb, lkb)
):
  match na r:
    case None{} r0:
      x => e => Empty.absurd(
        {Mst.delete.at(nb, h, r0, k, L, mgb, delb, lkb) == Some{x}: Maybe<&2, Edit>},
        Shared.Maybe.none_ne_some(Edit, x, e)
      )
    case Some{Node{+l, +left, +xs}} Room{+up, +lo, +hi}:
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, hn(Node{l, left, xs})({==})): Mst.Kept(
        Edit,
        Mst.delete.at(Some{Node{l, left, xs}}, h, Room{up, lo, hi}, k, L, mga, dela, lka),
        Mst.delete.at(_, h, Room{up, lo, hi}, k, L, mgb, delb, lkb)
      )
      Mst.delete.node_kept(Nat.cmp(l, L), h, l, left, xs, lo, hi, k, mga, mgb, dela, delb, lka, lkb, hm, hd, hl)

# a delete that a depot gives, a depot that grows from it gives too
def Mst.delete_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +a: S,
  +b: S,
  +r: Room,
  +k: List<&2, U32>,
  +L: Nat,
  +gr: {grows(a, b) == True{}: Bool}
) -> Mst.Kept(Edit, Mst.delete(~S, ~fetch, f, a, r, m, k, L), Mst.delete(~S, ~fetch, f, b, r, m, k, L)):
  match f m:
    case f0 None{}:
      x => e => e
    case 0n Some{h}:
      x => e => e
    case 1n+(+p) Some{+h}:
      Mst.delete.at_kept(
        Mst.node.in(~S, ~fetch, a, h, r),
        r,
        Mst.node.in(~S, ~fetch, b, h, r),
        h,
        k,
        L,
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, a, r1, r2, x, y),
        r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, b, r1, r2, x, y),
        r2 => c => Mst.delete(~S, ~fetch, p, a, r2, c, k, L),
        r2 => c => Mst.delete(~S, ~fetch, p, b, r2, c, k, L),
        r2 => c => Mst.look.go(~S, ~fetch, p, a, r2, c, k),
        r2 => c => Mst.look.go(~S, ~fetch, p, b, r2, c, k),
        n => Mst.node_in_kept(~S, ~fetch, ~grows, ~kept, a, b, h, r, n, gr),
        r1 => r2 => x => y => Mst.merge_kept(~S, ~fetch, ~grows, ~kept, p, x, y, a, b, r1, r2, gr),
        r2 => c => Mst.delete_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r2, k, L, gr),
        r2 => c => Mst.look.absent_kept(~S, ~fetch, ~grows, ~kept, p, c, a, b, r2, k, gr)
      )

# a write that a depot gives, a depot that grows from it gives too
def Mst.put_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ~grows: S -> S -> Bool,
  ~kept: Depots.Depot.Keeps(S, fetch, grows),
  m2: Maybe<&2, List<&2, U32>>,
  +a: S,
  +b: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +gr: {grows(a, b) == True{}: Bool}
) -> Mst.Kept(Edit, Mst.put(~S, ~fetch, a, h, k, m2), Mst.put(~S, ~fetch, b, h, k, m2)):
  match m2:
    case Some{v}:
      Mst.insert_kept(~S, ~fetch, ~grows, ~kept, Mst.depth(), h, a, b, Room.top(), k, v, Key.level(k), gr)
    case None{}:
      Mst.delete_kept(~S, ~fetch, ~grows, ~kept, Mst.depth(), h, a, b, Room.top(), k, Key.level(k), gr)

# Proofs of writes
# ----------------

# the comparison c the other way round
def Mst.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# a comparison that is LT is LT
def Mst.lt_sound(c: Cmp) -> {Cmp.is_lt(c) == True{}: Bool} -> {c == LT{}: Cmp}:
  match c:
    case LT{}:
      e => {==}
    case EQ{}:
      e => Empty.absurd({EQ{} == LT{}: Cmp}, Shared.Bool.false_ne_true(e))
    case GT{}:
      e => Empty.absurd({GT{} == LT{}: Cmp}, Shared.Bool.false_ne_true(e))

# no comparison is two of LT, EQ and GT
def Mst.cmp_disc(c: Cmp) -> Type:
  match c:
    case LT{}:
      Unit
    case EQ{}:
      Empty
    case GT{}:
      Empty

# LT is not EQ
def Mst.lt_ne_eq(e: {LT{} == EQ{}: Cmp}) -> Empty:
  %e: Mst.cmp_disc(_)
  Unit{}

# LT is not GT
def Mst.lt_ne_gt(e: {LT{} == GT{}: Cmp}) -> Empty:
  %e: Mst.cmp_disc(_)
  Unit{}

# EQ is not GT
def Mst.eq_ne_gt(e: {EQ{} == GT{}: Cmp}) -> Empty:
  %Equal.sym(Cmp, EQ{}, GT{}, e): Mst.cmp_disc(Mst.flip(_))
  Unit{}

# a comparison of numbers the other way round is flipped
def Mst.nat_flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == Mst.flip(Nat.cmp(a, b)): Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Mst.nat_flip(p, q)

# numbers that compare EQ are equal
def Mst.nat_eq(a: Nat, b: Nat) -> {Nat.cmp(a, b) == EQ{}: Cmp} -> {a == b: Nat}:
  match a b:
    case 0n 0n:
      e => {==}
    case 0n 1n+q:
      e => Empty.absurd({0n == 1n+q: Nat}, Mst.lt_ne_eq(e))
    case 1n+p 0n:
      e => Empty.absurd({1n+p == 0n: Nat}, Mst.eq_ne_gt(Equal.sym(Cmp, GT{}, EQ{}, e)))
    case 1n+p 1n+q:
      e => Equal.cong(Nat, Nat, n => 1n+n, p, q, Mst.nat_eq(p, q)(e))

# LT on numbers is transitive
def Mst.nat_trans(a: Nat, b: Nat, c: Nat) -> {Nat.cmp(a, b) == LT{}: Cmp} -> {Nat.cmp(b, c) == LT{}: Cmp} -> {
  Nat.cmp(a, c) == LT{}: Cmp
}:
  match a b c:
    case 0n 0n z:
      e1 => e2 => Empty.absurd({Nat.cmp(0n, z) == LT{}: Cmp}, Mst.lt_ne_eq(Equal.sym(Cmp, EQ{}, LT{}, e1)))
    case 0n 1n+q 0n:
      e1 => e2 => Empty.absurd({Nat.cmp(0n, 0n) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2)))
    case 0n 1n+q 1n+r:
      e1 => e2 => {==}
    case 1n+p 0n z:
      e1 => e2 => Empty.absurd({Nat.cmp(1n+p, z) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e1)))
    case 1n+p 1n+q 0n:
      e1 => e2 => Empty.absurd({Nat.cmp(1n+p, 0n) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2)))
    case 1n+p 1n+q 1n+r:
      Mst.nat_trans(p, q, r)

# a comparison of words the other way round is flipped
def Mst.u32_flip(+x: U32, +y: U32) -> {U32.cmp(y, x) == Mst.flip(U32.cmp(x, y)): Cmp}:
  %Equal.sym(Cmp, U32.cmp(y, x), Nat.cmp(U32.to_nat(y), U32.to_nat(x)), Shared.U32.cmp_to_nat(y, x)): {
    _ == Mst.flip(U32.cmp(x, y)): Cmp
  }
  %Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Shared.U32.cmp_to_nat(x, y)): {
    Nat.cmp(U32.to_nat(y), U32.to_nat(x)) == Mst.flip(_): Cmp
  }
  Mst.nat_flip(U32.to_nat(x), U32.to_nat(y))

# words that compare EQ are equal
def Mst.u32_eq(+x: U32, +y: U32) -> {U32.cmp(x, y) == EQ{}: Cmp} -> {x == y: U32}:
  e => Shared.U32.is_eq_sound(x, y)(Equal.cong(Cmp, Bool, Cmp.is_eq, U32.cmp(x, y), EQ{}, e))

# LT on words is transitive
def Mst.u32_trans(+x: U32, +y: U32, +z: U32) -> {U32.cmp(x, y) == LT{}: Cmp} -> {U32.cmp(y, z) == LT{}: Cmp} -> {
  U32.cmp(x, z) == LT{}: Cmp
}:
  e1 => e2 => Equal.trans(
    Cmp,
    U32.cmp(x, z),
    Nat.cmp(U32.to_nat(x), U32.to_nat(z)),
    LT{},
    Shared.U32.cmp_to_nat(x, z),
    Mst.nat_trans(U32.to_nat(x), U32.to_nat(y), U32.to_nat(z))(
      Equal.trans(
        Cmp,
        Nat.cmp(U32.to_nat(x), U32.to_nat(y)),
        U32.cmp(x, y),
        LT{},
        Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Shared.U32.cmp_to_nat(x, y)),
        e1
      )
    )(
      Equal.trans(
        Cmp,
        Nat.cmp(U32.to_nat(y), U32.to_nat(z)),
        U32.cmp(y, z),
        LT{},
        Equal.sym(Cmp, U32.cmp(y, z), Nat.cmp(U32.to_nat(y), U32.to_nat(z)), Shared.U32.cmp_to_nat(y, z)),
        e2
      )
    )
  )

# a word compares EQ to itself
def Mst.u32_refl(x: U32) -> {U32.cmp(x, x) == EQ{}: Cmp}:
  Shared.U32.cmp_refl(x)

# Key.cmp of two lists that start with x and y, once x compares to y as c
def Mst.key_step(+c: Cmp, ra: List<&2, U32>, rb: List<&2, U32>) -> Cmp:
  Shared.Bool.when(Cmp, Cmp.is_eq(c), u => Key.cmp(ra, rb), u => c)

# a key step flips with its parts
def Mst.key_flip.step(c: Cmp, k: Cmp, -kf: Cmp, e: {kf == Mst.flip(k): Cmp}) -> {
  Shared.Bool.when(Cmp, Cmp.is_eq(Mst.flip(c)), u => kf, u => Mst.flip(c))
    == Mst.flip(Shared.Bool.when(Cmp, Cmp.is_eq(c), u => k, u => c)): Cmp
}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      e
    case GT{}:
      {==}

# a comparison of keys the other way round is flipped
def Mst.key_flip(a: List<&2, U32>, b: List<&2, U32>) -> {Key.cmp(b, a) == Mst.flip(Key.cmp(a, b)): Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, rb}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
    case Con{+x, +ra} Con{+y, +rb}:
      %Equal.sym(Cmp, U32.cmp(y, x), Mst.flip(U32.cmp(x, y)), Mst.u32_flip(x, y)): {
        Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(rb, ra), u => _)
          == Mst.flip(Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, y)), u => Key.cmp(ra, rb), u => U32.cmp(x, y))): Cmp
      }
      Mst.key_flip.step(U32.cmp(x, y), Key.cmp(ra, rb), Key.cmp(rb, ra), Mst.key_flip(ra, rb))

# Mst.key_eq once x compares to y as c
def Mst.key_eq.step(
  c: Cmp,
  +x: U32,
  +y: U32,
  -ra: List<&2, U32>,
  -rb: List<&2, U32>,
  ec: {U32.cmp(x, y) == c: Cmp},
  ih: {Key.cmp(ra, rb) == EQ{}: Cmp} -> {ra == rb: List<&2, U32>}
) -> {Shared.Bool.when(Cmp, Cmp.is_eq(c), u => Key.cmp(ra, rb), u => c) == EQ{}: Cmp} -> {
  x <> ra == y <> rb: List<&2, U32>
}:
  match c:
    case LT{}:
      e => Empty.absurd({x <> ra == y <> rb: List<&2, U32>}, Mst.lt_ne_eq(e))
    case EQ{}:
      e =>
        %Mst.u32_eq(x, y)(ec): {x <> ra == _ <> rb: List<&2, U32>}
        %ih(e): {x <> ra == x <> _: List<&2, U32>}
        {==}
    case GT{}:
      e => Empty.absurd({x <> ra == y <> rb: List<&2, U32>}, Mst.eq_ne_gt(Equal.sym(Cmp, GT{}, EQ{}, e)))

# keys that compare EQ are equal
def Mst.key_eq(a: List<&2, U32>, b: List<&2, U32>) -> {Key.cmp(a, b) == EQ{}: Cmp} -> {a == b: List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      e => {==}
    case Nil{} Con{y, rb}:
      e => Empty.absurd({Nil{} == y <> rb: List<&2, U32>}, Mst.lt_ne_eq(e))
    case Con{x, ra} Nil{}:
      e => Empty.absurd({x <> ra == Nil{}: List<&2, U32>}, Mst.eq_ne_gt(Equal.sym(Cmp, GT{}, EQ{}, e)))
    case Con{+x, +ra} Con{+y, +rb}:
      Mst.key_eq.step(U32.cmp(x, y), x, y, ra, rb, {==}, Mst.key_eq(ra, rb))

# a key compares EQ to itself
def Mst.key_refl(a: List<&2, U32>) -> {Key.cmp(a, a) == EQ{}: Cmp}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +ra}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, Mst.u32_refl(x)): {
        Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(ra, ra), u => _) == EQ{}: Cmp
      }
      Mst.key_refl(ra)

# Mst.key_trans once the heads compare as cxy, cyz and cxz
def Mst.key_trans.step(
  cxy: Cmp,
  cyz: Cmp,
  +x: U32,
  +y: U32,
  +z: U32,
  -ra: List<&2, U32>,
  -rb: List<&2, U32>,
  -rc: List<&2, U32>,
  exy: {U32.cmp(x, y) == cxy: Cmp},
  eyz: {U32.cmp(y, z) == cyz: Cmp},
  ih: {Key.cmp(ra, rb) == LT{}: Cmp} -> {Key.cmp(rb, rc) == LT{}: Cmp} -> {Key.cmp(ra, rc) == LT{}: Cmp}
) -> {Mst.key_step(cxy, ra, rb) == LT{}: Cmp} -> {Mst.key_step(cyz, rb, rc) == LT{}: Cmp} -> {
  Mst.key_step(U32.cmp(x, z), ra, rc) == LT{}: Cmp
}:
  match cxy cyz:
    case LT{} LT{}:
      e1 => e2 =>
        %Equal.sym(Cmp, U32.cmp(x, z), LT{}, Mst.u32_trans(x, y, z)(exy)(eyz)): {Mst.key_step(_, ra, rc) == LT{}: Cmp}
        {==}
    case LT{} EQ{}:
      e1 => e2 =>
        %Mst.u32_eq(y, z)(eyz): {Mst.key_step(U32.cmp(x, _), ra, rc) == LT{}: Cmp}
        %Equal.sym(Cmp, U32.cmp(x, y), LT{}, exy): {Mst.key_step(_, ra, rc) == LT{}: Cmp}
        {==}
    case EQ{} LT{}:
      e1 => e2 =>
        %Equal.sym(U32, x, y, Mst.u32_eq(x, y)(exy)): {Mst.key_step(U32.cmp(_, z), ra, rc) == LT{}: Cmp}
        %Equal.sym(Cmp, U32.cmp(y, z), LT{}, eyz): {Mst.key_step(_, ra, rc) == LT{}: Cmp}
        {==}
    case EQ{} EQ{}:
      e1 => e2 =>
        %Equal.sym(U32, x, y, Mst.u32_eq(x, y)(exy)): {Mst.key_step(U32.cmp(_, z), ra, rc) == LT{}: Cmp}
        %Equal.sym(U32, y, z, Mst.u32_eq(y, z)(eyz)): {Mst.key_step(U32.cmp(_, z), ra, rc) == LT{}: Cmp}
        %Equal.sym(Cmp, U32.cmp(z, z), EQ{}, Mst.u32_refl(z)): {Mst.key_step(_, ra, rc) == LT{}: Cmp}
        ih(e1)(e2)
    case GT{} c2:
      e1 => e2 => Empty.absurd(
        {Mst.key_step(U32.cmp(x, z), ra, rc) == LT{}: Cmp},
        Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e1))
      )
    case LT{} GT{}:
      e1 => e2 => Empty.absurd(
        {Mst.key_step(U32.cmp(x, z), ra, rc) == LT{}: Cmp},
        Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2))
      )
    case EQ{} GT{}:
      e1 => e2 => Empty.absurd(
        {Mst.key_step(U32.cmp(x, z), ra, rc) == LT{}: Cmp},
        Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2))
      )

# LT on keys is transitive
def Mst.key_trans(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> {Key.cmp(a, b) == LT{}: Cmp} -> {
  Key.cmp(b, c) == LT{}: Cmp
} -> {Key.cmp(a, c) == LT{}: Cmp}:
  match a b c:
    case Nil{} Nil{} z:
      e1 => e2 => Empty.absurd({Key.cmp(Nil{}, z) == LT{}: Cmp}, Mst.lt_ne_eq(Equal.sym(Cmp, EQ{}, LT{}, e1)))
    case Nil{} Con{y, rb} Nil{}:
      e1 => e2 => Empty.absurd({Key.cmp(Nil{}, Nil{}) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2)))
    case Nil{} Con{y, rb} Con{z, rc}:
      e1 => e2 => {==}
    case Con{x, ra} Nil{} z:
      e1 => e2 => Empty.absurd({Key.cmp(x <> ra, z) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e1)))
    case Con{x, ra} Con{y, rb} Nil{}:
      e1 => e2 => Empty.absurd({Key.cmp(x <> ra, Nil{}) == LT{}: Cmp}, Mst.lt_ne_gt(Equal.sym(Cmp, GT{}, LT{}, e2)))
    case Con{+x, +ra} Con{+y, +rb} Con{+z, +rc}:
      Mst.key_trans.step(U32.cmp(x, y), U32.cmp(y, z), x, y, z, ra, rb, rc, {==}, {==}, Mst.key_trans(ra, rb, rc))

# Key.is_lt is the LT of Key.cmp, once x compares to y as c
def Mst.key_lt.step(c: Cmp, -k: Cmp, -b: Bool, e: {Cmp.is_lt(k) == b: Bool}) -> {
  Cmp.is_lt(Shared.Bool.when(Cmp, Cmp.is_eq(c), u => k, u => c)) == Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), b)): Bool
}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      e
    case GT{}:
      {==}

# Key.is_lt is the LT of Key.cmp
def Mst.key_lt(a: List<&2, U32>, b: List<&2, U32>) -> {Cmp.is_lt(Key.cmp(a, b)) == Key.is_lt(a, b): Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, rb}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
    case Con{+x, +ra} Con{+y, +rb}:
      Mst.key_lt.step(U32.cmp(x, y), Key.cmp(ra, rb), Key.is_lt(ra, rb), Mst.key_lt(ra, rb))

# a key before another compares LT
def Mst.key_lt_of(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {Key.cmp(a, b) == LT{}: Cmp}:
  e => Mst.lt_sound(Key.cmp(a, b))(Equal.trans(Bool, Cmp.is_lt(Key.cmp(a, b)), Key.is_lt(a, b), True{}, Mst.key_lt(a, b), e))

# a key that compares LT is before
def Mst.key_is_lt(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.cmp(a, b) == LT{}: Cmp} -> {Key.is_lt(a, b) == True{}: Bool}:
  e =>
    %Mst.key_lt(a, b): {_ == True{}: Bool}
    %Equal.sym(Cmp, Key.cmp(a, b), LT{}, e): {Cmp.is_lt(_) == True{}: Bool}
    {==}

# a key that compares GT to another is after it
def Mst.key_gt_lt(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.cmp(a, b) == GT{}: Cmp} -> {Key.cmp(b, a) == LT{}: Cmp}:
  e =>
    %Equal.sym(Cmp, Key.cmp(b, a), Mst.flip(Key.cmp(a, b)), Mst.key_flip(a, b)): {_ == LT{}: Cmp}
    %Equal.sym(Cmp, Key.cmp(a, b), GT{}, e): {Mst.flip(_) == LT{}: Cmp}
    {==}

# a key that compares LT to another, the other compares GT to it
def Mst.key_lt_gt(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.cmp(a, b) == LT{}: Cmp} -> {Key.cmp(b, a) == GT{}: Cmp}:
  e =>
    %Equal.sym(Cmp, Key.cmp(b, a), Mst.flip(Key.cmp(a, b)), Mst.key_flip(a, b)): {_ == GT{}: Cmp}
    %Equal.sym(Cmp, Key.cmp(a, b), LT{}, e): {Mst.flip(_) == GT{}: Cmp}
    {==}

# Key.is_lt is transitive
def Mst.key_lt_trans(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {
  Key.is_lt(b, c) == True{}: Bool
} -> {Key.is_lt(a, c) == True{}: Bool}:
  e1 => e2 => Mst.key_is_lt(a, c)(Mst.key_trans(a, b, c)(Mst.key_lt_of(a, b)(e1))(Mst.key_lt_of(b, c)(e2)))

# Shared.List.is_eq calls a key the same as one equal to it
def Mst.key_ne.of(+k: List<&2, U32>, -k2: List<&2, U32>, e: {k2 == k: List<&2, U32>}) -> {
  True{} == Shared.List.is_eq(~U32, ~U32.is_eq, k, k2): Bool
}:
  %Equal.sym(List<&2, U32>, k2, k, e): {True{} == Shared.List.is_eq(~U32, ~U32.is_eq, k, _): Bool}
  Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, k, k), True{}, Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k))

# two keys that Shared.List.is_eq calls different do not compare EQ
def Mst.key_ne(+k: List<&2, U32>, +k2: List<&2, U32>) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool
} -> {Key.cmp(k2, k) == EQ{}: Cmp} -> Empty:
  ne => e =>
    Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
        False{},
        Mst.key_ne.of(k, k2, Mst.key_eq(k2, k)(e)),
        ne
      )
    )

# what holds of each value of a bit holds of the bit
def Mst.case_bool(
  -P: Bool -> Type,
  b: Bool,
  pt: {b == True{}: Bool} -> P(True{}),
  pf: {b == False{}: Bool} -> P(False{})
) -> P(b):
  match b:
    case True{}:
      pt({==})
    case False{}:
      pf({==})

# what holds of each value of a comparison holds of the comparison
def Mst.case_cmp(
  -P: Cmp -> Type,
  c: Cmp,
  plt: {c == LT{}: Cmp} -> P(LT{}),
  peq: {c == EQ{}: Cmp} -> P(EQ{}),
  pgt: {c == GT{}: Cmp} -> P(GT{})
) -> P(c):
  match c:
    case LT{}:
      plt({==})
    case EQ{}:
      peq({==})
    case GT{}:
      pgt({==})

# a comparison that is GT is GT
def Mst.gt_sound(c: Cmp) -> {Cmp.is_gt(c) == True{}: Bool} -> {c == GT{}: Cmp}:
  match c:
    case LT{}:
      e => Empty.absurd({LT{} == GT{}: Cmp}, Shared.Bool.false_ne_true(e))
    case EQ{}:
      e => Empty.absurd({EQ{} == GT{}: Cmp}, Shared.Bool.false_ne_true(e))
    case GT{}:
      e => {==}

# every key of the items xs compares LT to k
def Mst.all_lt(xs: List<&2, Item>, +k: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Item{ik, iv, r}, rest}:
      Bool.and(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k))

# k2 compares GT to every key of the items xs: a pick of k2 passes them
def Mst.passes(xs: List<&2, Item>, +k2: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Item{ik, iv, r}, rest}:
      Bool.and(Cmp.is_gt(Key.cmp(k2, ik)), Mst.passes(rest, k2))

# a pick of k2 among the items ys stops at once: there is none, or k2 comes
# before the first
def Mst.stops_first(ys: List<&2, Item>, k2: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{Item{ik, iv, r}, rest}:
      Cmp.is_lt(Key.cmp(k2, ik))

# the lower bound lo2 is at or below lo1 (none: no bound)
def Mst.lo_le(+lo2: Maybe<&2, List<&2, U32>>, +lo1: Maybe<&2, List<&2, U32>>) -> Bool:
  match lo2 lo1:
    case None{} y:
      True{}
    case Some{a2} None{}:
      False{}
    case Some{a2} Some{a1}:
      Cmp.is_le(Key.cmp(a2, a1))

# the upper bound hi2 is at or above hi1 (none: no bound)
def Mst.hi_le(+hi1: Maybe<&2, List<&2, U32>>, +hi2: Maybe<&2, List<&2, U32>>) -> Bool:
  match hi1 hi2:
    case x None{}:
      True{}
    case None{} Some{b2}:
      False{}
    case Some{b1} Some{b2}:
      Cmp.is_le(Key.cmp(b1, b2))

# a at or below b, and b before c: a before c
def Mst.key_le_lt(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {
  Cmp.is_le(Key.cmp(a, b)) == True{}: Bool
} -> {Key.cmp(b, c) == LT{}: Cmp} -> {Key.cmp(a, c) == LT{}: Cmp}:
  Mst.case_cmp(
    t => {Key.cmp(a, b) == t: Cmp} -> {Cmp.is_le(t) == True{}: Bool} -> {Key.cmp(b, c) == LT{}: Cmp} -> {
      Key.cmp(a, c) == LT{}: Cmp
    },
    Key.cmp(a, b),
    q => e => l => e1 => Mst.key_trans(a, b, c)(e)(e1),
    q => e => l => e1 =>
      %Equal.sym(List<&2, U32>, a, b, Mst.key_eq(a, b)(e)): {Key.cmp(_, c) == LT{}: Cmp}
      e1,
    q => e => l => e1 => Empty.absurd({Key.cmp(a, c) == LT{}: Cmp}, Shared.Bool.false_ne_true(l))
  )({==})

# a before b, and b at or below c: a before c
def Mst.key_lt_le(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.cmp(a, b) == LT{}: Cmp} -> {
  Cmp.is_le(Key.cmp(b, c)) == True{}: Bool
} -> {Key.cmp(a, c) == LT{}: Cmp}:
  Mst.case_cmp(
    t => {Key.cmp(b, c) == t: Cmp} -> {Key.cmp(a, b) == LT{}: Cmp} -> {Cmp.is_le(t) == True{}: Bool} -> {
      Key.cmp(a, c) == LT{}: Cmp
    },
    Key.cmp(b, c),
    q => e => e1 => l => Mst.key_trans(a, b, c)(e1)(e),
    q => e => e1 => l =>
      %Mst.key_eq(b, c)(e): {Key.cmp(a, _) == LT{}: Cmp}
      e1,
    q => e => e1 => l => Empty.absurd({Key.cmp(a, c) == LT{}: Cmp}, Shared.Bool.false_ne_true(l))
  )({==})

# a key after lo1 is after a lower bound at or below it
def Mst.after_wide(+lo2: Maybe<&2, List<&2, U32>>, +lo1: Maybe<&2, List<&2, U32>>, +x: List<&2, U32>) -> {
  Mst.lo_le(lo2, lo1) == True{}: Bool
} -> {Bound.after(lo1, x) == True{}: Bool} -> {Bound.after(lo2, x) == True{}: Bool}:
  match lo2 lo1:
    case None{} y:
      w => e => {==}
    case Some{a2} None{}:
      w => e => Empty.absurd({Bound.after(Some{a2}, x) == True{}: Bool}, Shared.Bool.false_ne_true(w))
    case Some{+a2} Some{+a1}:
      w => e => Mst.key_is_lt(a2, x)(Mst.key_le_lt(a2, a1, x)(w)(Mst.key_lt_of(a1, x)(e)))

# a key before hi1 is before an upper bound at or above it
def Mst.before_wide(+x: List<&2, U32>, +hi1: Maybe<&2, List<&2, U32>>, +hi2: Maybe<&2, List<&2, U32>>) -> {
  Mst.hi_le(hi1, hi2) == True{}: Bool
} -> {Bound.before(x, hi1) == True{}: Bool} -> {Bound.before(x, hi2) == True{}: Bool}:
  match hi1 hi2:
    case y None{}:
      w => e => {==}
    case None{} Some{b2}:
      w => e => Empty.absurd({Bound.before(x, Some{b2}) == True{}: Bool}, Shared.Bool.false_ne_true(w))
    case Some{+b1} Some{+b2}:
      w => e => Mst.key_is_lt(x, b2)(Mst.key_lt_le(x, b1, b2)(Mst.key_lt_of(x, b1)(e))(w))

# a bound is at or below itself
def Mst.lo_le_refl(+lo: Maybe<&2, List<&2, U32>>) -> {Mst.lo_le(lo, lo) == True{}: Bool}:
  match lo:
    case None{}:
      {==}
    case Some{+a}:
      %Equal.sym(Cmp, Key.cmp(a, a), EQ{}, Mst.key_refl(a)): {Cmp.is_le(_) == True{}: Bool}
      {==}

# a bound is at or above itself
def Mst.hi_le_refl(+hi: Maybe<&2, List<&2, U32>>) -> {Mst.hi_le(hi, hi) == True{}: Bool}:
  match hi:
    case None{}:
      {==}
    case Some{+b}:
      %Equal.sym(Cmp, Key.cmp(b, b), EQ{}, Mst.key_refl(b)): {Cmp.is_le(_) == True{}: Bool}
      {==}

# a lower bound before k is below the bound k
def Mst.lo_le_key(+lo: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> {Bound.after(lo, k) == True{}: Bool} -> {
  Mst.lo_le(lo, Some{k}) == True{}: Bool
}:
  match lo:
    case None{}:
      e => {==}
    case Some{+a}:
      e =>
        %Equal.sym(Cmp, Key.cmp(a, k), LT{}, Mst.key_lt_of(a, k)(e)): {Cmp.is_le(_) == True{}: Bool}
        {==}

# an upper bound after k is above the bound k
def Mst.hi_le_key(+k: List<&2, U32>, +hi: Maybe<&2, List<&2, U32>>) -> {Bound.before(k, hi) == True{}: Bool} -> {
  Mst.hi_le(Some{k}, hi) == True{}: Bool
}:
  match hi:
    case None{}:
      e => {==}
    case Some{+b}:
      e =>
        %Equal.sym(Cmp, Key.cmp(k, b), LT{}, Mst.key_lt_of(k, b)(e)): {Cmp.is_le(_) == True{}: Bool}
        {==}

# items that fit between two bounds fit between wider ones
def Mst.fit_wide(
  xs: List<&2, Item>,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool}
) -> {Items.fit(xs, lo1, hi1) == True{}: Bool} -> {Items.fit(xs, lo2, hi2) == True{}: Bool}:
  match xs:
    case Nil{}:
      +e => {==}
    case Con{Item{+k, v, r}, +rest}:
      +e => Shared.Bool.and_both(
        Bool.and(Bound.after(lo2, k), Bound.before(k, hi2)),
        Items.fit(rest, Some{k}, hi2),
        Shared.Bool.and_both(
          Bound.after(lo2, k),
          Bound.before(k, hi2),
          Mst.after_wide(lo2, lo1, k)(wl)(
            Shared.Bool.and_true_left(
              Bound.after(lo1, k),
              Bound.before(k, hi1),
              Shared.Bool.and_true_left(
                Bool.and(Bound.after(lo1, k), Bound.before(k, hi1)),
                Items.fit(rest, Some{k}, hi1),
                e
              )
            )
          ),
          Mst.before_wide(k, hi1, hi2)(wh)(
            Shared.Bool.and_true_right(
              Bound.after(lo1, k),
              Bound.before(k, hi1),
              Shared.Bool.and_true_left(
                Bool.and(Bound.after(lo1, k), Bound.before(k, hi1)),
                Items.fit(rest, Some{k}, hi1),
                e
              )
            )
          )
        ),
        Mst.fit_wide(rest, Some{k}, Some{k}, hi1, hi2, Mst.lo_le_refl(Some{k}), wh)(
          Shared.Bool.and_true_right(
            Bool.and(Bound.after(lo1, k), Bound.before(k, hi1)),
            Items.fit(rest, Some{k}, hi1),
            e
          )
        )
      )

# items fit in a row as the first fit, and the rest fit after the last of
# the first
def Mst.fit_append(xs: List<&2, Item>, +ys: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Items.fit(List.append(&2, Item, xs, ys), lo, hi)
    == Bool.and(Items.fit(xs, lo, hi), Items.fit(ys, Items.last_key(xs, lo), hi)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, +rest}:
      %Equal.sym(
        Bool,
        Items.fit(List.append(&2, Item, rest, ys), Some{k}, hi),
        Bool.and(Items.fit(rest, Some{k}, hi), Items.fit(ys, Items.last_key(rest, Some{k}), hi)),
        Mst.fit_append(rest, ys, Some{k}, hi)
      ): {
        Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), _)
          == Bool.and(
            Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Items.fit(rest, Some{k}, hi)),
            Items.fit(ys, Items.last_key(rest, Some{k}), hi)
          ): Bool
      }
      Shared.Bool.and_assoc(
        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
        Items.fit(rest, Some{k}, hi),
        Items.fit(ys, Items.last_key(rest, Some{k}), hi)
      )

# the items with their last subtree set fit as they did
def Mst.fit_set_last(xs: List<&2, Item>, -m: Maybe<&2, Hashes.Hash>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Items.fit(Mst.set_last(xs, m), lo, hi) == Items.fit(xs, lo, hi): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      %Equal.sym(
        Bool,
        Items.fit(Mst.set_last(y <> rest, m), Some{k}, hi),
        Items.fit(y <> rest, Some{k}, hi),
        Mst.fit_set_last(y <> rest, m, Some{k}, hi)
      ): {Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), _) == Items.fit(Item{k, v, r} <> y <> rest, lo, hi): Bool}
      {==}

# the last key of items with their last subtree set is their last key
def Mst.last_key_set_last(xs: List<&2, Item>, -m: Maybe<&2, Hashes.Hash>, +lo: Maybe<&2, List<&2, U32>>) -> {
  Items.last_key(Mst.set_last(xs, m), lo) == Items.last_key(xs, lo): Maybe<&2, List<&2, U32>>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      Mst.last_key_set_last(y <> rest, m, Some{k})

# a pick passes items with their last subtree set as it passes them
def Mst.passes_set_last(xs: List<&2, Item>, -m: Maybe<&2, Hashes.Hash>, +k2: List<&2, U32>) -> {
  Mst.passes(Mst.set_last(xs, m), k2) == Mst.passes(xs, k2): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      %Equal.sym(
        Bool,
        Mst.passes(Mst.set_last(y <> rest, m), k2),
        Mst.passes(y <> rest, k2),
        Mst.passes_set_last(y <> rest, m, k2)
      ): {Bool.and(Cmp.is_gt(Key.cmp(k2, k)), _) == Mst.passes(Item{k, v, r} <> y <> rest, k2): Bool}
      {==}

# the last subtree of items with it set to m is m
def Mst.last_set_last(xs: List<&2, Item>, -left: Maybe<&2, Hashes.Hash>, -m: Maybe<&2, Hashes.Hash>) -> {
  Mst.last(Mst.set_last(xs, m), Mst.end_left(xs, left, m)) == m: Maybe<&2, Hashes.Hash>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      Mst.last_set_last(y <> rest, r, m)

# the last key of items in a row is the last key of the second, after the
# first
def Mst.last_key_append(xs: List<&2, Item>, -ys: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>) -> {
  Items.last_key(List.append(&2, Item, xs, ys), lo) == Items.last_key(ys, Items.last_key(xs, lo)): Maybe<&2, List<&2, U32>>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, +rest}:
      Mst.last_key_append(rest, ys, Some{k})

# items that fit before hi and come before k fit before k
def Mst.fit_below(
  +xs: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> {Items.fit(xs, lo, hi) == True{}: Bool} -> {Mst.all_lt(xs, k) == True{}: Bool} -> {
  Items.fit(xs, lo, Some{k}) == True{}: Bool
}:
  match xs:
    case Nil{}:
      +e => +a => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +e => +a => Shared.Bool.and_both(
        Bool.and(Bound.after(lo, ik), Bound.before(ik, Some{k})),
        Items.fit(rest, Some{ik}, Some{k}),
        Shared.Bool.and_both(
          Bound.after(lo, ik),
          Bound.before(ik, Some{k}),
          Shared.Bool.and_true_left(
            Bound.after(lo, ik),
            Bound.before(ik, hi),
            Shared.Bool.and_true_left(Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)), Items.fit(rest, Some{ik}, hi), e)
          ),
          Mst.key_is_lt(ik, k)(
            Mst.lt_sound(Key.cmp(ik, k))(
              Shared.Bool.and_true_left(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a)
            )
          )
        ),
        Mst.fit_below(rest, Some{ik}, hi, k)(
          Shared.Bool.and_true_right(Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)), Items.fit(rest, Some{ik}, hi), e)
        )(Shared.Bool.and_true_right(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
      )

# items that all come before k end before k, once their lower bound does
def Mst.last_below(xs: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> {
  Mst.all_lt(xs, k) == True{}: Bool
} -> {Bound.after(lo, k) == True{}: Bool} -> {Bound.after(Items.last_key(xs, lo), k) == True{}: Bool}:
  match xs:
    case Nil{}:
      +a => +e => e
    case Con{Item{+ik, +iv, +r}, +rest}:
      +a => +e => Mst.last_below(rest, Some{ik}, k)(
        Shared.Bool.and_true_right(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a)
      )(
        Mst.key_is_lt(ik, k)(
          Mst.lt_sound(Key.cmp(ik, k))(Shared.Bool.and_true_left(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
        )
      )

# items that fit before k come before k
def Mst.fit_all_lt(xs: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> {
  Items.fit(xs, lo, Some{k}) == True{}: Bool
} -> {Mst.all_lt(xs, k) == True{}: Bool}:
  match xs:
    case Nil{}:
      +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +e => Shared.Bool.and_both(
        Cmp.is_lt(Key.cmp(ik, k)),
        Mst.all_lt(rest, k),
        Equal.trans(
          Bool,
          Cmp.is_lt(Key.cmp(ik, k)),
          Key.is_lt(ik, k),
          True{},
          Mst.key_lt(ik, k),
          Shared.Bool.and_true_right(
            Bound.after(lo, ik),
            Key.is_lt(ik, k),
            Shared.Bool.and_true_left(Bool.and(Bound.after(lo, ik), Key.is_lt(ik, k)), Items.fit(rest, Some{ik}, Some{k}), e)
          )
        ),
        Mst.fit_all_lt(rest, Some{ik}, k)(
          Shared.Bool.and_true_right(Bool.and(Bound.after(lo, ik), Key.is_lt(ik, k)), Items.fit(rest, Some{ik}, Some{k}), e)
        )
      )

# a key after k2 passes nothing it does not pass: if k2 is after every key of
# xs, so is a key after k2 (here: a key that compares GT to k2)
def Mst.passes_of_lt(xs: List<&2, Item>, +k: List<&2, U32>, +k2: List<&2, U32>) -> {Mst.all_lt(xs, k) == True{}: Bool} -> {
  Cmp.is_lt(Key.cmp(k, k2)) == True{}: Bool
} -> {Mst.passes(xs, k2) == True{}: Bool}:
  match xs:
    case Nil{}:
      +a => +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +a => +e => Shared.Bool.and_both(
        Cmp.is_gt(Key.cmp(k2, ik)),
        Mst.passes(rest, k2),
        Equal.cong(
          Cmp,
          Bool,
          Cmp.is_gt,
          Key.cmp(k2, ik),
          GT{},
          Mst.key_lt_gt(ik, k2)(
            Mst.key_trans(ik, k, k2)(
              Mst.lt_sound(Key.cmp(ik, k))(Shared.Bool.and_true_left(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
            )(Mst.lt_sound(Key.cmp(k, k2))(e))
          )
        ),
        Mst.passes_of_lt(rest, k, k2)(Shared.Bool.and_true_right(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))(e)
      )

# a pick of k passes the items before k (k itself here)
def Mst.passes_of_all_lt(xs: List<&2, Item>, +k: List<&2, U32>) -> {Mst.all_lt(xs, k) == True{}: Bool} -> {
  Mst.passes(xs, k) == True{}: Bool
}:
  match xs:
    case Nil{}:
      +a => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +a => Shared.Bool.and_both(
        Cmp.is_gt(Key.cmp(k, ik)),
        Mst.passes(rest, k),
        Equal.cong(
          Cmp,
          Bool,
          Cmp.is_gt,
          Key.cmp(k, ik),
          GT{},
          Mst.key_lt_gt(ik, k)(
            Mst.lt_sound(Key.cmp(ik, k))(Shared.Bool.and_true_left(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
          )
        ),
        Mst.passes_of_all_lt(rest, k)(Shared.Bool.and_true_right(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
      )

# the items xs before the first whose key is not before k (what a part of
# them at k puts before)
def Mst.pre(xs: List<&2, Item>, +k: List<&2, U32>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{Item{+ik, +iv, +r}, +rest}:
      Shared.Bool.when(List<&2, Item>, Cmp.is_lt(Key.cmp(ik, k)), u => Item{ik, iv, r} <> Mst.pre(rest, k), u => [])

# the items xs from the first whose key is not before k on
def Mst.post(xs: List<&2, Item>, +k: List<&2, U32>) -> List<&2, Item>:
  match xs:
    case Nil{}:
      []
    case Con{Item{+ik, +iv, +r}, +rest}:
      Shared.Bool.when(List<&2, Item>, Cmp.is_lt(Key.cmp(ik, k)), u => Mst.post(rest, k), u => Item{ik, iv, r} <> rest)

# the first of the items ys (if any) does not come before k
def Mst.head_not_lt(ys: List<&2, Item>, +k: List<&2, U32>) -> Bool:
  match ys:
    case Nil{}:
      True{}
    case Con{Item{ik, iv, r}, rest}:
      Bool.not(Cmp.is_lt(Key.cmp(ik, k)))

# the part of the items xs at k, by Mst.pre and Mst.post
def Mst.part_eq(+xs: List<&2, Item>, +prev: Maybe<&2, Hashes.Hash>, +k: List<&2, U32>, +acc: List<&2, Item>) -> {
  Mst.part(xs, prev, k, acc)
    == Part{List.reverse.go(&2, Item, Mst.pre(xs, k), acc), Mst.last(Mst.pre(xs, k), prev), Mst.post(xs, k)}: Part
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_bool(
        b => {
          Shared.Bool.when(
            Part,
            b,
            u => Mst.part(rest, r, k, Item{ik, iv, r} <> acc),
            u => Part{acc, prev, Item{ik, iv, r} <> rest}
          )
            == Part{
              List.reverse.go(
                &2,
                Item,
                Shared.Bool.when(List<&2, Item>, b, u => Item{ik, iv, r} <> Mst.pre(rest, k), u => []),
                acc
              ),
              Mst.last(Shared.Bool.when(List<&2, Item>, b, u => Item{ik, iv, r} <> Mst.pre(rest, k), u => []), prev),
              Shared.Bool.when(List<&2, Item>, b, u => Mst.post(rest, k), u => Item{ik, iv, r} <> rest)
            }: Part
        },
        Cmp.is_lt(Key.cmp(ik, k)),
        +q => Mst.part_eq(rest, r, k, Item{ik, iv, r} <> acc),
        +q => {==}
      )

# the items before k and from k on are the items
def Mst.pre_post(+xs: List<&2, Item>, +k: List<&2, U32>) -> {
  List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)) == xs: List<&2, Item>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_bool(
        b => {
          List.append(
            &2,
            Item,
            Shared.Bool.when(List<&2, Item>, b, u => Item{ik, iv, r} <> Mst.pre(rest, k), u => []),
            Shared.Bool.when(List<&2, Item>, b, u => Mst.post(rest, k), u => Item{ik, iv, r} <> rest)
          )
            == Item{ik, iv, r} <> rest: List<&2, Item>
        },
        Cmp.is_lt(Key.cmp(ik, k)),
        +q => Equal.cong(
          List<&2, Item>,
          List<&2, Item>,
          ys => Item{ik, iv, r} <> ys,
          List.append(&2, Item, Mst.pre(rest, k), Mst.post(rest, k)),
          rest,
          Mst.pre_post(rest, k)
        ),
        +q => {==}
      )

# the items before k all come before k
def Mst.pre_all_lt(+xs: List<&2, Item>, +k: List<&2, U32>) -> {Mst.all_lt(Mst.pre(xs, k), k) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_bool(
        b => {b == Cmp.is_lt(Key.cmp(ik, k)): Bool} -> {
          Mst.all_lt(Shared.Bool.when(List<&2, Item>, b, u => Item{ik, iv, r} <> Mst.pre(rest, k), u => []), k) == True{}: Bool
        },
        Cmp.is_lt(Key.cmp(ik, k)),
        +q => +e =>
          %e: {Bool.and(_, Mst.all_lt(Mst.pre(rest, k), k)) == True{}: Bool}
          Mst.pre_all_lt(rest, k),
        +q => +e => {==}
      )({==})

# the first item from k on does not come before k
def Mst.post_head(+xs: List<&2, Item>, +k: List<&2, U32>) -> {Mst.head_not_lt(Mst.post(xs, k), k) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_bool(
        b => {b == Cmp.is_lt(Key.cmp(ik, k)): Bool} -> {
          Mst.head_not_lt(Shared.Bool.when(List<&2, Item>, b, u => Mst.post(rest, k), u => Item{ik, iv, r} <> rest), k)
            == True{}: Bool
        },
        Cmp.is_lt(Key.cmp(ik, k)),
        +q => +e => Mst.post_head(rest, k),
        +q => +e =>
          %e: {Bool.not(_) == True{}: Bool}
          {==}
      )({==})

# a list reversed onto zs, then ys, is the list reversed onto zs then ys
def Mst.rev_append(+acc: List<&2, Item>, +zs: List<&2, Item>, +ys: List<&2, Item>) -> {
  List.append(&2, Item, List.reverse.go(&2, Item, acc, zs), ys) == List.reverse.go(&2, Item, acc, List.append(&2, Item, zs, ys)): List<&2, Item>
}:
  match acc:
    case Nil{}:
      {==}
    case Con{+a, +as}:
      Mst.rev_append(as, a <> zs, ys)

# Mst.rejoin of nonempty items reversed onto acc
def Mst.rejoin_rev.go(+xs: List<&2, Item>, +x: Item, +acc: List<&2, Item>, +m: Maybe<&2, Hashes.Hash>, +after: List<&2, Item>) -> {
  Mst.rejoin(List.reverse.go(&2, Item, x <> xs, acc), m, after)
    == List.reverse.go(&2, Item, acc, List.append(&2, Item, Mst.set_last(x <> xs, m), after)): List<&2, Item>
}:
  match xs x:
    case Nil{} Item{+k, +v, +r}:
      Mst.rev_append(acc, [], Item{k, v, m} <> after)
    case Con{+y, +ys} Item{+k, +v, +r}:
      Mst.rejoin_rev.go(ys, y, Item{k, v, r} <> acc, m, after)

# Mst.rejoin of the items before a place, as a part gives them, is the items
# with their last subtree set
def Mst.rejoin_rev(+xs: List<&2, Item>, +m: Maybe<&2, Hashes.Hash>, +after: List<&2, Item>) -> {
  Mst.rejoin(List.reverse.go(&2, Item, xs, []), m, after) == List.append(&2, Item, Mst.set_last(xs, m), after): List<&2, Item>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      Mst.rejoin_rev.go(rest, x, [], m, after)

# a node with no item before a place keeps left, else as Mst.end_left
def Mst.end_left_same(+xs: List<&2, Item>, +left: Maybe<&2, Hashes.Hash>) -> {
  Mst.end_left(xs, left, left) == left: Maybe<&2, Hashes.Hash>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# Mst.left of the items before a place reversed onto acc
def Mst.left_rev.go(+xs: List<&2, Item>, +acc: List<&2, Item>, +left: Maybe<&2, Hashes.Hash>, +m: Maybe<&2, Hashes.Hash>) -> {
  Mst.left(List.reverse.go(&2, Item, xs, acc), left, m) == Mst.end_left(xs, left, Mst.left(acc, left, m)): Maybe<&2, Hashes.Hash>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.left(List.reverse.go(&2, Item, rest, x <> acc), left, m),
        Mst.end_left(rest, left, left),
        Mst.left_rev.go(rest, x <> acc, left, m)
      ): {_ == left: Maybe<&2, Hashes.Hash>}
      Mst.end_left_same(rest, left)

# Mst.left of the items before a place, as a part gives them
def Mst.left_rev(+xs: List<&2, Item>, +left: Maybe<&2, Hashes.Hash>, +m: Maybe<&2, Hashes.Hash>) -> {
  Mst.left(List.reverse.go(&2, Item, xs, []), left, m) == Mst.end_left(xs, left, m): Maybe<&2, Hashes.Hash>
}:
  Mst.left_rev.go(xs, [], left, m)

# the head key of items reversed onto acc
def Mst.head_rev.go(+xs: List<&2, Item>, +acc: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>) -> {
  Items.head_key(List.reverse.go(&2, Item, xs, acc), lo) == Items.last_key(xs, Items.head_key(acc, lo)): Maybe<&2, List<&2, U32>>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, +rest}:
      Mst.head_rev.go(rest, Item{k, v, r} <> acc, lo)

# the head key of the items before a place, as a part gives them, is their
# last key
def Mst.head_rev(+xs: List<&2, Item>, +lo: Maybe<&2, List<&2, U32>>) -> {
  Items.head_key(List.reverse.go(&2, Item, xs, []), lo) == Items.last_key(xs, lo): Maybe<&2, List<&2, U32>>
}:
  Mst.head_rev.go(xs, [], lo)

# a pick passes the items that k2 is after
def Mst.pick_passes(
  +xs: List<&2, Item>,
  +ys: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.passes(xs, k2) == True{}: Bool} -> {
  Mst.pick(List.append(&2, Item, xs, ys), prev, l, lo, hi, k2)
    == Mst.pick(ys, Mst.last(xs, prev), l, Items.last_key(xs, lo), hi, k2): Pick
}:
  match xs:
    case Nil{}:
      +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +e =>
        %Equal.sym(
          Cmp,
          Key.cmp(k2, ik),
          GT{},
          Mst.gt_sound(Key.cmp(k2, ik))(Shared.Bool.and_true_left(Cmp.is_gt(Key.cmp(k2, ik)), Mst.passes(rest, k2), e))
        ): {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(_),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(
              Pick,
              Cmp.is_eq(_),
              w => Pick.Hit{iv},
              w => Mst.pick(List.append(&2, Item, rest, ys), r, l, Some{ik}, hi, k2)
            )
          )
            == Mst.pick(ys, Mst.last(rest, r), l, Items.last_key(rest, Some{ik}), hi, k2): Pick
        }
        Mst.pick_passes(rest, ys, r, l, Some{ik}, hi, k2)(
          Shared.Bool.and_true_right(Cmp.is_gt(Key.cmp(k2, ik)), Mst.passes(rest, k2), e)
        )

# a pick that stops within the items xs reads nothing after them
def Mst.pick_stops(
  +xs: List<&2, Item>,
  +ys1: List<&2, Item>,
  +ys2: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.passes(xs, k2) == False{}: Bool} -> {
  Mst.pick(List.append(&2, Item, xs, ys1), prev, l, lo, hi1, k2)
    == Mst.pick(List.append(&2, Item, xs, ys2), prev, l, lo, hi2, k2): Pick
}:
  match xs:
    case Nil{}:
      +e => Empty.absurd(
        {Mst.pick(ys1, prev, l, lo, hi1, k2) == Mst.pick(ys2, prev, l, lo, hi2, k2): Pick},
        Shared.Bool.true_ne_false(e)
      )
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_cmp(
        c => {Bool.and(Cmp.is_gt(c), Mst.passes(rest, k2)) == False{}: Bool} -> {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(
              Pick,
              Cmp.is_eq(c),
              w => Pick.Hit{iv},
              w => Mst.pick(List.append(&2, Item, rest, ys1), r, l, Some{ik}, hi1, k2)
            )
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
              u => Shared.Bool.when(
                Pick,
                Cmp.is_eq(c),
                w => Pick.Hit{iv},
                w => Mst.pick(List.append(&2, Item, rest, ys2), r, l, Some{ik}, hi2, k2)
              )
            ): Pick
        },
        Key.cmp(k2, ik),
        +q => +e => {==},
        +q => +e => {==},
        +q => +e => Mst.pick_stops(rest, ys1, ys2, r, l, Some{ik}, hi1, hi2, k2)(e)
      )

# Mst.pick_stops, with the last subtree of the items set on one side
def Mst.pick_stops_set(
  +xs: List<&2, Item>,
  +m: Maybe<&2, Hashes.Hash>,
  +ys1: List<&2, Item>,
  +ys2: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.passes(xs, k2) == False{}: Bool} -> {
  Mst.pick(List.append(&2, Item, Mst.set_last(xs, m), ys1), prev, l, lo, hi1, k2)
    == Mst.pick(List.append(&2, Item, xs, ys2), prev, l, lo, hi2, k2): Pick
}:
  match xs:
    case Nil{}:
      +e => Empty.absurd(
        {Mst.pick(ys1, prev, l, lo, hi1, k2) == Mst.pick(ys2, prev, l, lo, hi2, k2): Pick},
        Shared.Bool.true_ne_false(e)
      )
    case Con{Item{+ik, +iv, +r}, Nil{}}:
      Mst.case_cmp(
        c => {Bool.and(Cmp.is_gt(c), True{}) == False{}: Bool} -> {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(ys1, m, l, Some{ik}, hi1, k2))
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
              u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(ys2, r, l, Some{ik}, hi2, k2))
            ): Pick
        },
        Key.cmp(k2, ik),
        +q => +e => {==},
        +q => +e => {==},
        +q => +e => Empty.absurd(
          {Mst.pick(ys1, m, l, Some{ik}, hi1, k2) == Mst.pick(ys2, r, l, Some{ik}, hi2, k2): Pick},
          Shared.Bool.true_ne_false(e)
        )
      )
    case Con{Item{+ik, +iv, +r}, Con{+y, +rest}}:
      Mst.case_cmp(
        c => {Bool.and(Cmp.is_gt(c), Mst.passes(y <> rest, k2)) == False{}: Bool} -> {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(
              Pick,
              Cmp.is_eq(c),
              w => Pick.Hit{iv},
              w => Mst.pick(List.append(&2, Item, Mst.set_last(y <> rest, m), ys1), r, l, Some{ik}, hi1, k2)
            )
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
              u => Shared.Bool.when(
                Pick,
                Cmp.is_eq(c),
                w => Pick.Hit{iv},
                w => Mst.pick(List.append(&2, Item, y <> rest, ys2), r, l, Some{ik}, hi2, k2)
              )
            ): Pick
        },
        Key.cmp(k2, ik),
        +q => +e => {==},
        +q => +e => {==},
        +q => +e => Mst.pick_stops_set(y <> rest, m, ys1, ys2, r, l, Some{ik}, hi1, hi2, k2)(e)
      )

# a pick that stops at the first item goes down before it
def Mst.pick_first(
  +ys: List<&2, Item>,
  +m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.stops_first(ys, k2) == True{}: Bool} -> {
  Mst.pick(ys, m, l, lo, hi, k2) == Pick.Down{m, Room.of(l, lo, Items.head_key(ys, hi))}: Pick
}:
  match ys:
    case Nil{}:
      +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +e =>
        %Equal.sym(Cmp, Key.cmp(k2, ik), LT{}, Mst.lt_sound(Key.cmp(k2, ik))(e)): {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(_),
            u => Pick.Down{m, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k2))
          )
            == Pick.Down{m, Room.of(l, lo, Some{ik})}: Pick
        }
        {==}

# a pick that does not stop at the first item reads neither the subtree
# before it nor the bound before it
def Mst.pick_past(
  +ys: List<&2, Item>,
  +m1: Maybe<&2, Hashes.Hash>,
  +m2: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.stops_first(ys, k2) == False{}: Bool} -> {
  Mst.pick(ys, m1, l, lo1, hi, k2) == Mst.pick(ys, m2, l, lo2, hi, k2): Pick
}:
  match ys:
    case Nil{}:
      +e => Empty.absurd(
        {Pick.Down{m1, Room.of(l, lo1, hi)} == Pick.Down{m2, Room.of(l, lo2, hi)}: Pick},
        Shared.Bool.true_ne_false(e)
      )
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_cmp(
        c => {Cmp.is_lt(c) == False{}: Bool} -> {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{m1, Room.of(l, lo1, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k2))
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{m2, Room.of(l, lo2, Some{ik})},
              u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k2))
            ): Pick
        },
        Key.cmp(k2, ik),
        +q => +e => Empty.absurd(
          {Pick.Down{m1, Room.of(l, lo1, Some{ik})} == Pick.Down{m2, Room.of(l, lo2, Some{ik})}: Pick},
          Shared.Bool.true_ne_false(e)
        ),
        +q => +e => {==},
        +q => +e => {==}
      )

# the up of a room
def Mst.room_up(r: Room) -> Nat:
  match r:
    case Room{u, lo, hi}:
      u

# the room r2 is at least as wide as r1
def Mst.room_le(r1: Room, r2: Room) -> Bool:
  match r1 r2:
    case Room{u1, lo1, hi1} Room{u2, lo2, hi2}:
      Bool.and(Nat.is_le(u1, u2), Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)))

# the room r2 is at least as wide as r1, and of the up l
def Mst.down_ok(l: Nat, r1: Room, +r2: Room) -> Bool:
  Bool.and(Mst.room_le(r1, r2), Nat.is_eq(Mst.room_up(r2), l))

# two picks of one key among the same items of a node of the level l: the
# same hit, or the same subtree, in a room at least as wide and of the up l
def Mst.PickSub(l: Nat, p1: Pick, p2: Pick) -> Type:
  match p1 p2:
    case Pick.Hit{v1} Pick.Hit{v2}:
      {v1 == v2: List<&2, U32>}
    case Pick.Down{m1, r1} Pick.Down{m2, r2}:
      {m1 == m2: Maybe<&2, Hashes.Hash>} & {Mst.down_ok(l, r1, r2) == True{}: Bool}
    case Pick.Hit{v1} Pick.Down{m2, r2}:
      Empty
    case Pick.Down{m1, r1} Pick.Hit{v2}:
      Empty

# a room of the up l, between wider bounds, is wider
def Mst.room_le_of(
  +l: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool}
) -> {Mst.room_le(Room{l, lo1, hi1}, Room{l, lo2, hi2}) == True{}: Bool}:
  Shared.Bool.and_both(
    Nat.is_le(l, l),
    Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)),
    Shared.Nat.le_refl(l),
    Shared.Bool.and_both(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wl, wh)
  )

# a pick between wider bounds finds the same, in a wider room
def Mst.pick_wide(
  +xs: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool}
) -> Mst.PickSub(l, Mst.pick(xs, prev, l, lo1, hi1, k), Mst.pick(xs, prev, l, lo2, hi2, k)):
  match xs:
    case Nil{}:
      ({==}, Shared.Bool.and_both(Mst.room_le(Room{l, lo1, hi1}, Room{l, lo2, hi2}), Nat.is_eq(l, l), Mst.room_le_of(l, lo1, lo2, hi1, hi2, wl, wh), Shared.Nat.is_eq_refl(l)))
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_cmp(
        c => Mst.PickSub(
          l,
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo1, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi1, k))
          ),
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo2, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi2, k))
          )
        ),
        Key.cmp(k, ik),
        +q => (
          {==},
          Shared.Bool.and_both(
            Mst.room_le(Room{l, lo1, Some{ik}}, Room{l, lo2, Some{ik}}),
            Nat.is_eq(l, l),
            Mst.room_le_of(l, lo1, lo2, Some{ik}, Some{ik}, wl, Mst.hi_le_refl(Some{ik})),
            Shared.Nat.is_eq_refl(l)
          )
        ),
        +q => {==},
        +q => Mst.pick_wide(rest, r, l, Some{ik}, Some{ik}, hi1, hi2, k, Mst.lo_le_refl(Some{ik}), wh)
      )

# a list of words holds its first
def Mst.contains_head(+w: List<&2, U32>, rest: List<&2, List<&2, U32>>) -> {
  List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), w <> rest, w) == True{}: Bool
}:
  %Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, w, w),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), w)
  ): {List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, w), _) == True{}: Bool}
  {==}

# a depot that gives the words w under their hash has them
def Mst.has_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +w: List<&2, U32>,
  e: {fetch(s)(Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {True{} == Depots.Depot.has(~S, ~fetch, s, w): Bool}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, fetch(s)(Hashes.Sha.hash(w)), Some{w}, e): {
    True{}
      == Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), _, Some{w}): Bool
  }
  Equal.sym(
    Bool,
    Shared.List.is_eq(~U32, ~U32.is_eq, w, w),
    True{},
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), w)
  )

# the depot s has the first of the words ns (none: True)
def Mst.head_has(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +s: S, ns: List<&2, List<&2, U32>>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{w, rest}:
      Depots.Depot.has(~S, ~fetch, s, w)

# the depot s holds each of the words ns, once a proof says so of each (b:
# whether it has the first)
def Mst.holds_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>,
  b: Bool,
  +s: S,
  eb: {Mst.head_has(~S, ~fetch, s, ns) == b: Bool},
  held: @w: List<&2, U32> -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ns, w) == True{}: Bool
  } -> {fetch(s)(Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool}:
  match ns b:
    case Nil{} b0:
      {==}
    case Con{+w, +rest} True{}:
      %Equal.sym(Bool, Depots.Depot.has(~S, ~fetch, s, w), True{}, eb): {
        List.all.if(u => Depots.Depot.holds(~S, ~fetch, s, rest), _) == True{}: Bool
      }
      Mst.holds_of(
        ~S,
        ~fetch,
        rest,
        Mst.head_has(~S, ~fetch, s, rest),
        s,
        {==},
        +w2 => +c => held(w2)(Shared.List.contains_cons(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), w, rest, w2)(c))
      )
    case Con{+w, +rest} False{}:
      Empty.absurd(
        {Depots.Depot.holds(~S, ~fetch, s, w <> rest) == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Depots.Depot.has(~S, ~fetch, s, w),
            False{},
            Mst.has_of(~S, ~fetch, s, w, held(w)(Mst.contains_head(w, rest))),
            eb
          )
        )
      )

# a depot that holds the words ws first holds them under their hash
def Mst.holds_head(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ws: List<&2, U32>,
  +ns: List<&2, List<&2, U32>>,
  +e: {Depots.Depot.holds(~S, ~fetch, s, ws <> ns) == True{}: Bool}
) -> {fetch(s)(Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
    fetch(s)(Hashes.Sha.hash(ws)),
    Some{ws}
  )(Shared.List.all.if_hit(Depots.Depot.has(~S, ~fetch, s, ws), u => Depots.Depot.holds(~S, ~fetch, s, ns))(e))

# a depot that holds words holds the rest of them
def Mst.holds_tail(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ws: List<&2, U32>,
  +ns: List<&2, List<&2, U32>>,
  +e: {Depots.Depot.holds(~S, ~fetch, s, ws <> ns) == True{}: Bool}
) -> {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool}:
  Shared.List.all.if_rest(Depots.Depot.has(~S, ~fetch, s, ws), u => Depots.Depot.holds(~S, ~fetch, s, ns))(e)

# the node whose code a depot holds under its hash is the node of that hash
def Mst.node_code(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +n: Node,
  e: {fetch(s)(Hashes.Sha.hash(Node.code(n, []))) == Some{Node.code(n, [])}: Maybe<&2, List<&2, U32>>}
) -> {Mst.node(~S, ~fetch, s, Hashes.Sha.hash(Node.code(n, []))) == Some{n}: Maybe<&2, Node>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, fetch(s)(Hashes.Sha.hash(Node.code(n, []))), Some{Node.code(n, [])}, e): {
    Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, _) == Some{n}: Maybe<&2, Node>
  }
  Codes.Code.whole_read(~Node, ~Node.code, ~Node.code.read, ~(x => r => Node.code_read(x, r)), n)

# the node n may sit in the room r: its level is below the up of r, it has
# an item, and its items fit the bounds of r
def Mst.opens(n: Node, r: Room) -> Bool:
  match n r:
    case Node{+l, left, +xs} Room{up, lo, hi}:
      Bool.and(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi))

# a node that sits in a room is itself
def Mst.in_same(n: Node, r: Room, -m: Node) -> {Node.in(n, r) == Some{m}: Maybe<&2, Node>} -> {n == m: Node}:
  match n r:
    case Node{+l, +left, +xs} Room{+up, +lo, +hi}:
      Mst.case_bool(
        b => {Shared.Maybe.when(Node, b, u => Some{Node{l, left, xs}}) == Some{m}: Maybe<&2, Node>} -> {
          Node{l, left, xs} == m: Node
        },
        Bool.and(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi)),
        +q => +e => Shared.Maybe.some_inj(Node, Node{l, left, xs}, m, e),
        +q => +e => Empty.absurd({Node{l, left, xs} == m: Node}, Shared.Maybe.none_ne_some(Node, m, e))
      )

# a node that sits in a room opens there
def Mst.in_opens(n: Node, r: Room, -m: Node) -> {Node.in(n, r) == Some{m}: Maybe<&2, Node>} -> {Mst.opens(n, r) == True{}: Bool}:
  match n r:
    case Node{+l, +left, +xs} Room{+up, +lo, +hi}:
      Mst.case_bool(
        b => {Shared.Maybe.when(Node, b, u => Some{Node{l, left, xs}}) == Some{m}: Maybe<&2, Node>} -> {b == True{}: Bool},
        Bool.and(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi)),
        +q => +e => {==},
        +q => +e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Node, m, e))
      )

# a node that opens in a room sits there
def Mst.opens_in(n: Node, r: Room) -> {Mst.opens(n, r) == True{}: Bool} -> {Node.in(n, r) == Some{n}: Maybe<&2, Node>}:
  match n r:
    case Node{+l, +left, +xs} Room{+up, +lo, +hi}:
      +e =>
        %Equal.sym(
          Bool,
          Bool.and(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi)),
          True{},
          e
        ): {Shared.Maybe.when(Node, _, u => Some{Node{l, left, xs}}) == Some{Node{l, left, xs}}: Maybe<&2, Node>}
        {==}

# the node that a depot gives in a room is the node it gives
def Mst.bind_in(mn: Maybe<&2, Node>, +r: Room, -m: Node) -> {
  Maybe.bind(&2, Node, Node, mn, n => Node.in(n, r)) == Some{m}: Maybe<&2, Node>
} -> {mn == Some{m}: Maybe<&2, Node>}:
  match mn:
    case None{}:
      +e => e
    case Some{+n}:
      +e => Equal.cong(Node, Maybe<&2, Node>, x => Some{x}, n, m, Mst.in_same(n, r, m)(e))

# the node that a depot gives in a room opens there
def Mst.bind_opens(mn: Maybe<&2, Node>, +r: Room, -m: Node) -> {
  Maybe.bind(&2, Node, Node, mn, n => Node.in(n, r)) == Some{m}: Maybe<&2, Node>
} -> {Mst.opens(m, r) == True{}: Bool}:
  match mn:
    case None{}:
      +e => Empty.absurd({Mst.opens(m, r) == True{}: Bool}, Shared.Maybe.none_ne_some(Node, m, e))
    case Some{+n}:
      +e =>
        %Mst.in_same(n, r, m)(e): {Mst.opens(_, r) == True{}: Bool}
        Mst.in_opens(n, r, m)(e)

# the node of a hash in a room is the node of the hash
def Mst.in_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +r: Room,
  -m: Node
) -> {Mst.node.in(~S, ~fetch, s, h, r) == Some{m}: Maybe<&2, Node>} -> {Mst.node(~S, ~fetch, s, h) == Some{m}: Maybe<&2, Node>}:
  Mst.bind_in(Mst.node(~S, ~fetch, s, h), r, m)

# the node of a hash in a room opens there
def Mst.in_open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +r: Room,
  -m: Node
) -> {Mst.node.in(~S, ~fetch, s, h, r) == Some{m}: Maybe<&2, Node>} -> {Mst.opens(m, r) == True{}: Bool}:
  Mst.bind_opens(Mst.node(~S, ~fetch, s, h), r, m)

# the node of a hash, where it opens, is the node of the hash there
def Mst.node_in_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +r: Room,
  +m: Node
) -> {Mst.node(~S, ~fetch, s, h) == Some{m}: Maybe<&2, Node>} -> {Mst.opens(m, r) == True{}: Bool} -> {
  Mst.node.in(~S, ~fetch, s, h, r) == Some{m}: Maybe<&2, Node>
}:
  +e => +o =>
    %Equal.sym(Maybe<&2, Node>, Mst.node(~S, ~fetch, s, h), Some{m}, e): {
      Maybe.bind(&2, Node, Node, _, n => Node.in(n, r)) == Some{m}: Maybe<&2, Node>
    }
    Mst.opens_in(m, r)(o)

# the bounds of r2 are at least as wide as those of r1
def Mst.bounds_le(r1: Room, r2: Room) -> Bool:
  match r1 r2:
    case Room{u1, lo1, hi1} Room{u2, lo2, hi2}:
      Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2))

# a room at least as wide has bounds at least as wide
def Mst.room_bounds(r1: Room, r2: Room) -> {Mst.room_le(r1, r2) == True{}: Bool} -> {Mst.bounds_le(r1, r2) == True{}: Bool}:
  match r1 r2:
    case Room{+u1, +lo1, +hi1} Room{+u2, +lo2, +hi2}:
      +e => Shared.Bool.and_true_right(Nat.is_le(u1, u2), Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)), e)

# a node that opens in a room opens in a wider one
def Mst.opens_wide(n: Node, r1: Room, r2: Room) -> {Mst.opens(n, r1) == True{}: Bool} -> {Mst.room_le(r1, r2) == True{}: Bool} -> {
  Mst.opens(n, r2) == True{}: Bool
}:
  match n r1 r2:
    case Node{+l, +left, +xs} Room{+u1, +lo1, +hi1} Room{+u2, +lo2, +hi2}:
      +e => +w => Shared.Bool.and_both(
        Bool.and(Nat.is_lt(l, u2), Bool.not(List.is_empty(&2, Item, xs))),
        Items.fit(xs, lo2, hi2),
        Shared.Bool.and_both(
          Nat.is_lt(l, u2),
          Bool.not(List.is_empty(&2, Item, xs)),
          Shared.Nat.lt_le(l, u1, u2)(
            Shared.Bool.and_true_left(
              Nat.is_lt(l, u1),
              Bool.not(List.is_empty(&2, Item, xs)),
              Shared.Bool.and_true_left(
                Bool.and(Nat.is_lt(l, u1), Bool.not(List.is_empty(&2, Item, xs))),
                Items.fit(xs, lo1, hi1),
                e
              )
            )
          )(Shared.Bool.and_true_left(Nat.is_le(u1, u2), Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)), w)),
          Shared.Bool.and_true_right(
            Nat.is_lt(l, u1),
            Bool.not(List.is_empty(&2, Item, xs)),
            Shared.Bool.and_true_left(
              Bool.and(Nat.is_lt(l, u1), Bool.not(List.is_empty(&2, Item, xs))),
              Items.fit(xs, lo1, hi1),
              e
            )
          )
        ),
        Mst.fit_wide(
          xs,
          lo1,
          lo2,
          hi1,
          hi2,
          Shared.Bool.and_true_left(
            Mst.lo_le(lo2, lo1),
            Mst.hi_le(hi1, hi2),
            Shared.Bool.and_true_right(Nat.is_le(u1, u2), Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)), w)
          ),
          Shared.Bool.and_true_right(
            Mst.lo_le(lo2, lo1),
            Mst.hi_le(hi1, hi2),
            Shared.Bool.and_true_right(Nat.is_le(u1, u2), Bool.and(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2)), w)
          )
        )(Shared.Bool.and_true_right(Bool.and(Nat.is_lt(l, u1), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo1, hi1), e))
      )

# no number is below 0
def Mst.nat_lt_zero(l: Nat) -> {Nat.is_lt(l, 0n) == True{}: Bool} -> Empty:
  match l:
    case 0n:
      +e => Shared.Bool.false_ne_true(e)
    case 1n+p:
      +e => Shared.Bool.false_ne_true(e)

# the level of a node that opens in a room is below its up
def Mst.opens_lt(+l: Nat, -left: Maybe<&2, Hashes.Hash>, +xs: List<&2, Item>, r: Room) -> {
  Mst.opens(Node{l, left, xs}, r) == True{}: Bool
} -> {Nat.is_lt(l, Mst.room_up(r)) == True{}: Bool}:
  match r:
    case Room{+up, +lo, +hi}:
      +e => Shared.Bool.and_true_left(
        Nat.is_lt(l, up),
        Bool.not(List.is_empty(&2, Item, xs)),
        Shared.Bool.and_true_left(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi), e)
      )

# the nodes that a tree m may have at its root in r1 may sit there in r2
def Mst.Hop(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  m: Maybe<&2, Hashes.Hash>,
  -r1: Room,
  -r2: Room
) -> Type:
  match m:
    case None{}:
      Unit
    case Some{h}:
      @n: Node -> {Mst.node(~S, ~fetch, s, h) == Some{n}: Maybe<&2, Node>} -> {Mst.opens(n, r1) == True{}: Bool} -> {
        Mst.opens(n, r2) == True{}: Bool
      }

# a hit tells the same, whatever node it names when it cannot tell
def Mst.look.hit_kept(b: Bool, -v: List<&2, U32>, -h1: Hashes.Hash, -h2: Hashes.Hash, -x: Maybe<&2, List<&2, U32>>) -> {
  Look.known(Shared.Bool.when(Look, b, u => Look.Found{v}, u => Look.Missing{h1})) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Shared.Bool.when(Look, b, u => Look.Found{v}, u => Look.Missing{h2})) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {Look.known(Look.Missing{h2}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )

# a read of a pick tells as a read of a pick in a wider room
def Mst.look.wide.pick(
  +l: Nat,
  +p1: Pick,
  +p2: Pick,
  -h: Hashes.Hash,
  -h2: Hashes.Hash,
  +k: List<&2, U32>,
  -goa: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -gob: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -x: Maybe<&2, List<&2, U32>>,
  ps: Mst.PickSub(l, p1, p2),
  hg: @m: Maybe<&2, Hashes.Hash> -> @r1: Room -> @r2: Room -> {Mst.room_le(r1, r2) == True{}: Bool} -> {
    Mst.room_up(r2) == l: Nat
  } -> {Look.known(goa(m)(r1)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
    Look.known(gob(m)(r2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.pick(p1, h, l, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.pick(p2, h2, l, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match p1 p2:
    case Pick.Hit{+v1} Pick.Hit{+v2}:
      %ps: (
        {Look.known(Mst.look.pick(Pick.Hit{v1}, h, l, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.pick(Pick.Hit{_}, h2, l, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.look.hit_kept(Nat.is_eq(Key.level(k), l), v1, h, h2, x)
    case Pick.Down{+m1, +r1} Pick.Down{+m2, +r2}:
      match ps:
        case Tuple{+em, +eo}:
          %em: (
            {Look.known(goa(m1)(r1)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
              -> {Look.known(gob(_)(r2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          )
          hg(m1)(r1)(r2)(Shared.Bool.and_true_left(Mst.room_le(r1, r2), Nat.is_eq(Mst.room_up(r2), l), eo))(
            Shared.Nat.is_eq_sound(Mst.room_up(r2), l)(Shared.Bool.and_true_right(Mst.room_le(r1, r2), Nat.is_eq(Mst.room_up(r2), l), eo))
          )
    case Pick.Hit{+v1} Pick.Down{+m2, +r2}:
      +e => Empty.absurd(
        {Look.known(Mst.look.pick(Pick.Down{m2, r2}, h2, l, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        ps
      )
    case Pick.Down{+m1, +r1} Pick.Hit{+v2}:
      +e => Empty.absurd(
        {Look.known(Mst.look.pick(Pick.Hit{v2}, h2, l, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        ps
      )

# a read of a node tells as a read of it in a room with wider bounds
def Mst.look.wide.at(
  -h: Hashes.Hash,
  +na: Maybe<&2, Node>,
  +r1: Room,
  +r2: Room,
  -nb: Maybe<&2, Node>,
  +k: List<&2, U32>,
  -goa: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -gob: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -x: Maybe<&2, List<&2, U32>>,
  -p2: Nat,
  +wb: {Mst.bounds_le(r1, r2) == True{}: Bool},
  hn: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> {nb == Some{n}: Maybe<&2, Node>},
  hl: @l: Nat -> @left: Maybe<&2, Hashes.Hash> -> @xs: List<&2, Item> -> {
    nb == Some{Node{l, left, xs}}: Maybe<&2, Node>
  } -> {Nat.is_le(l, p2) == True{}: Bool},
  hg: @m: Maybe<&2, Hashes.Hash> -> @r3: Room -> @r4: Room -> {Mst.room_le(r3, r4) == True{}: Bool} -> {
    Nat.is_le(Mst.room_up(r4), p2) == True{}: Bool
  } -> {Look.known(goa(m)(r3)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
    Look.known(gob(m)(r4)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.at(h, na, r1, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.at(h, nb, r2, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match na r1 r2:
    case None{} +r5 +r6:
      +e => Empty.absurd(
        {Look.known(Mst.look.at(h, nb, r6, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case Some{Node{+l, +left, +xs}} Room{+u1, +lo1, +hi1} Room{+u2, +lo2, +hi2}:
      +enb = hn(Node{l, left, xs})({==})
      %Equal.sym(Maybe<&2, Node>, nb, Some{Node{l, left, xs}}, enb): (
        {Look.known(Mst.look.at(h, Some{Node{l, left, xs}}, Room{u1, lo1, hi1}, k, goa)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.at(h, _, Room{u2, lo2, hi2}, k, gob)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.look.wide.pick(
        l,
        Mst.pick(xs, left, l, lo1, hi1, k),
        Mst.pick(xs, left, l, lo2, hi2, k),
        h,
        h,
        k,
        goa,
        gob,
        x,
        Mst.pick_wide(
          xs,
          left,
          l,
          lo1,
          lo2,
          hi1,
          hi2,
          k,
          Shared.Bool.and_true_left(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wb),
          Shared.Bool.and_true_right(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wb)
        ),
        m => r3 => r4 => w => eu => hg(m)(r3)(r4)(w)(
          Equal.trans(
            Bool,
            Nat.is_le(Mst.room_up(r4), p2),
            Nat.is_le(l, p2),
            True{},
            Equal.cong(Nat, Bool, a => Nat.is_le(a, p2), Mst.room_up(r4), l, eu),
            hl(l)(left)(xs)(enb)
          )
        )
      )

# a read of a node that cannot open tells nothing
def Mst.look.at_none(
  -h: Hashes.Hash,
  +na: Maybe<&2, Node>,
  +r: Room,
  -k: List<&2, U32>,
  -go: Maybe<&2, Hashes.Hash> -> Room -> Look,
  -x: Maybe<&2, List<&2, U32>>,
  hz: @n: Node -> {na == Some{n}: Maybe<&2, Node>} -> Empty
) -> {Look.known(Mst.look.at(h, na, r, k, go)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> Empty:
  match na r:
    case None{} Room{+u, +lo, +hi}:
      +e => Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
    case Some{+n} Room{+u, +lo, +hi}:
      +e => hz(n)({==})

# no node opens in a room whose up is 0
def Mst.opens_zero(n: Node, r: Room, o: {Mst.opens(n, r) == True{}: Bool}, fu: {Nat.is_le(Mst.room_up(r), 0n) == True{}: Bool}) -> Empty:
  match n r:
    case Node{+l, +left, +xs} Room{+up, +lo, +hi}:
      Mst.nat_lt_zero(l)(
        Shared.Nat.lt_le(l, up, 0n)(
          Shared.Bool.and_true_left(
            Nat.is_lt(l, up),
            Bool.not(List.is_empty(&2, Item, xs)),
            Shared.Bool.and_true_left(Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi), o)
          )
        )(fu)
      )

# a root may sit in a wider room
def Mst.hop_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  +m: Maybe<&2, Hashes.Hash>,
  +r1: Room,
  +r2: Room,
  +w: {Mst.room_le(r1, r2) == True{}: Bool}
) -> Mst.Hop(~S, ~fetch, s, m, r1, r2):
  match m:
    case None{}:
      Unit{}
    case Some{+h}:
      n => +e => +o => Mst.opens_wide(n, r1, r2)(o)(w)

# what a read tells, a read in a room with wider bounds, where the root may
# sit too, tells: with any fuel that reaches the room
def Mst.look.wide(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g2: Nat,
  +g1: Nat,
  +m: Maybe<&2, Hashes.Hash>,
  +s: S,
  +r1: Room,
  +r2: Room,
  +k: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  hop: Mst.Hop(~S, ~fetch, s, m, r1, r2),
  +wb: {Mst.bounds_le(r1, r2) == True{}: Bool},
  +fu: {Nat.is_le(Mst.room_up(r2), g2) == True{}: Bool}
) -> {
  Look.known(Mst.look.go(~S, ~fetch, g1, s, r1, m, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, r2, m, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g2 g1 m:
    case +y +z None{}:
      +e => e
    case +y 0n Some{+h}:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, r2, Some{h}, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 0n 1n+p1 Some{+h}:
      +e => Empty.absurd(
        {Look.known(Look.Missing{h}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.look.at_none(
          h,
          Mst.node.in(~S, ~fetch, s, h, r1),
          r1,
          k,
          +m2 => +r3 => Mst.look.go(~S, ~fetch, p1, s, r3, m2, k),
          x,
          +n => +en => Mst.opens_zero(
            n,
            r2,
            hop(n)(Mst.in_node(~S, ~fetch, s, h, r1, n)(en))(Mst.in_open(~S, ~fetch, s, h, r1, n)(en)),
            fu
          )
        )(e)
      )
    case 1n+(+p2) 1n+p1 Some{+h}:
      Mst.look.wide.at(
        h,
        Mst.node.in(~S, ~fetch, s, h, r1),
        r1,
        r2,
        Mst.node.in(~S, ~fetch, s, h, r2),
        k,
        +m2 => +r3 => Mst.look.go(~S, ~fetch, p1, s, r3, m2, k),
        +m2 => +r3 => Mst.look.go(~S, ~fetch, p2, s, r3, m2, k),
        x,
        p2,
        wb,
        +n => +en => Mst.node_in_of(~S, ~fetch, s, h, r2, n)(Mst.in_node(~S, ~fetch, s, h, r1, n)(en))(
          hop(n)(Mst.in_node(~S, ~fetch, s, h, r1, n)(en))(Mst.in_open(~S, ~fetch, s, h, r1, n)(en))
        ),
        +l => +left => +xs => +en => Shared.Nat.lt_succ_le(l, p2)(
          Shared.Nat.lt_le(l, Mst.room_up(r2), 1n+p2)(
            Mst.opens_lt(l, left, xs, r2)(Mst.in_open(~S, ~fetch, s, h, r2, Node{l, left, xs})(en))
          )(fu)
        ),
        +m2 => +r3 => +r4 => +w => +f => Mst.look.wide(
          ~S,
          ~fetch,
          p2,
          p1,
          m2,
          s,
          r3,
          r4,
          k,
          x,
          Mst.hop_of(~S, ~fetch, s, m2, r3, r4, w),
          Mst.room_bounds(r3, r4)(w),
          f
        )
      )

# a read of a node that opens in its room is the read of its pick
def Mst.look_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +p: Nat,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +k: List<&2, U32>,
  +e: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +o: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool}
) -> {
  Mst.look.go(~S, ~fetch, 1n+p, s, Room{u, lo, hi}, Some{h}, k)
    == Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k)): Look
}:
  %Equal.sym(
    Maybe<&2, Node>,
    Mst.node.in(~S, ~fetch, s, h, Room{u, lo, hi}),
    Some{Node{l, left, xs}},
    Mst.node_in_of(~S, ~fetch, s, h, Room{u, lo, hi}, Node{l, left, xs})(e)(o)
  ): {
    Mst.look.at(h, _, Room{u, lo, hi}, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k))
      == Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k)): Look
  }
  {==}

# the level of the root of the node mn, if any, is below u
def Mst.lvl.at(mn: Maybe<&2, Node>, +u: Nat) -> Bool:
  match mn:
    case None{}:
      True{}
    case Some{Node{l, left, xs}}:
      Nat.is_lt(l, u)

# the level of the root of the tree m, if the depot gives it, is below u
def Mst.lvl(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +s: S, m: Maybe<&2, Hashes.Hash>, +u: Nat) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{h}:
      Mst.lvl.at(Mst.node(~S, ~fetch, s, h), u)

# the level of a root whose level is below u
def Mst.lvl_lt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  -xs: List<&2, Item>,
  +lv: {Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool},
  +e: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>}
) -> {Nat.is_lt(l, u) == True{}: Bool}:
  %e: {Mst.lvl.at(_, u) == True{}: Bool}
  lv

# a root whose level is below u
def Mst.lvl_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  -xs: List<&2, Item>,
  +e: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +lt: {Nat.is_lt(l, u) == True{}: Bool}
) -> {Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool}:
  %Equal.sym(Maybe<&2, Node>, Mst.node(~S, ~fetch, s, h), Some{Node{l, left, xs}}, e): {Mst.lvl.at(_, u) == True{}: Bool}
  lt

# a root whose level is below u2 and that opens in r1 opens in a room of the
# up u2 with wider bounds
def Mst.opens_lvl(
  n: Node,
  r1: Room,
  r2: Room,
  +lt: {Mst.lvl.at(Some{n}, Mst.room_up(r2)) == True{}: Bool},
  +wb: {Mst.bounds_le(r1, r2) == True{}: Bool}
) -> {Mst.opens(n, r1) == True{}: Bool} -> {Mst.opens(n, r2) == True{}: Bool}:
  match n r1 r2:
    case Node{+l, +left, +xs} Room{+u1, +lo1, +hi1} Room{+u2, +lo2, +hi2}:
      +o => Shared.Bool.and_both(
        Bool.and(Nat.is_lt(l, u2), Bool.not(List.is_empty(&2, Item, xs))),
        Items.fit(xs, lo2, hi2),
        Shared.Bool.and_both(
          Nat.is_lt(l, u2),
          Bool.not(List.is_empty(&2, Item, xs)),
          lt,
          Shared.Bool.and_true_right(
            Nat.is_lt(l, u1),
            Bool.not(List.is_empty(&2, Item, xs)),
            Shared.Bool.and_true_left(Bool.and(Nat.is_lt(l, u1), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo1, hi1), o)
          )
        ),
        Mst.fit_wide(
          xs,
          lo1,
          lo2,
          hi1,
          hi2,
          Shared.Bool.and_true_left(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wb),
          Shared.Bool.and_true_right(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wb)
        )(Shared.Bool.and_true_right(Bool.and(Nat.is_lt(l, u1), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo1, hi1), o))
      )

# a root whose level is below the up of r2 may sit in r2, of wider bounds
def Mst.hop_lvl(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +r1: Room,
  +r2: Room,
  +lv: {Mst.lvl(~S, ~fetch, s, m, Mst.room_up(r2)) == True{}: Bool},
  +wb: {Mst.bounds_le(r1, r2) == True{}: Bool}
) -> Mst.Hop(~S, ~fetch, s, m, r1, r2):
  match m:
    case None{}:
      Unit{}
    case Some{+h}:
      +n => +e => Mst.opens_lvl(
        n,
        r1,
        r2,
        Equal.trans(
          Bool,
          Mst.lvl.at(Some{n}, Mst.room_up(r2)),
          Mst.lvl.at(Mst.node(~S, ~fetch, s, h), Mst.room_up(r2)),
          True{},
          Equal.cong(
            Maybe<&2, Node>,
            Bool,
            a => Mst.lvl.at(a, Mst.room_up(r2)),
            Some{n},
            Mst.node(~S, ~fetch, s, h),
            Equal.sym(Maybe<&2, Node>, Mst.node(~S, ~fetch, s, h), Some{n}, e)
          ),
          lv
        ),
        wb
      )

# items with their last subtree set, then more, fit as before
def Mst.fit_set_last_append(
  +xs: List<&2, Item>,
  -m: Maybe<&2, Hashes.Hash>,
  -ys: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {
  Items.fit(List.append(&2, Item, Mst.set_last(xs, m), ys), lo, hi) == Items.fit(List.append(&2, Item, xs, ys), lo, hi): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      %Equal.sym(
        Bool,
        Items.fit(List.append(&2, Item, Mst.set_last(y <> rest, m), ys), Some{k}, hi),
        Items.fit(List.append(&2, Item, y <> rest, ys), Some{k}, hi),
        Mst.fit_set_last_append(y <> rest, m, ys, Some{k}, hi)
      ): {
        Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), _)
          == Items.fit(List.append(&2, Item, Item{k, v, r} <> y <> rest, ys), lo, hi): Bool
      }
      {==}

# items with their last subtree set, then more, are as empty as before
def Mst.empty_set_last_append(+xs: List<&2, Item>, -m: Maybe<&2, Hashes.Hash>, -ys: List<&2, Item>) -> {
  List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xs, m), ys)) == List.is_empty(&2, Item, List.append(&2, Item, xs, ys)): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      {==}

# a node with the last subtree of its first items set opens where it did
def Mst.opens_set_last(
  +l: Nat,
  -left1: Maybe<&2, Hashes.Hash>,
  -left2: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +m: Maybe<&2, Hashes.Hash>,
  +ys: List<&2, Item>,
  r: Room
) -> {Mst.opens(Node{l, left1, List.append(&2, Item, xs, ys)}, r) == True{}: Bool} -> {
  Mst.opens(Node{l, left2, List.append(&2, Item, Mst.set_last(xs, m), ys)}, r) == True{}: Bool
}:
  match r:
    case Room{+u, +lo, +hi}:
      %Equal.sym(
        Bool,
        List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xs, m), ys)),
        List.is_empty(&2, Item, List.append(&2, Item, xs, ys)),
        Mst.empty_set_last_append(xs, m, ys)
      ): (
        {Mst.opens(Node{l, left1, List.append(&2, Item, xs, ys)}, Room{u, lo, hi}) == True{}: Bool}
          -> {
            Bool.and(
              Bool.and(Nat.is_lt(l, u), Bool.not(_)),
              Items.fit(List.append(&2, Item, Mst.set_last(xs, m), ys), lo, hi)
            )
              == True{}: Bool
          }
      )
      %Equal.sym(
        Bool,
        Items.fit(List.append(&2, Item, Mst.set_last(xs, m), ys), lo, hi),
        Items.fit(List.append(&2, Item, xs, ys), lo, hi),
        Mst.fit_set_last_append(xs, m, ys, lo, hi)
      ): (
        {Mst.opens(Node{l, left1, List.append(&2, Item, xs, ys)}, Room{u, lo, hi}) == True{}: Bool}
          -> {
            Bool.and(Bool.and(Nat.is_lt(l, u), Bool.not(List.is_empty(&2, Item, List.append(&2, Item, xs, ys)))), _)
              == True{}: Bool
          }
      )
      +o => o

# a node of items that are not empty is stored
def Mst.make_full(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +ys: List<&2, Item>,
  +acc: List<&2, List<&2, U32>>
) -> {List.is_empty(&2, Item, ys) == False{}: Bool} -> {Mst.make(l, left, ys, acc) == Mst.store(Node{l, left, ys}, acc): Edit}:
  match ys:
    case Nil{}:
      +e => Empty.absurd({Edit{left, acc} == Mst.store(Node{l, left, []}, acc): Edit}, Shared.Bool.true_ne_false(e))
    case Con{+y, +rest}:
      +e => {==}

# items that a pick does not pass are not empty
def Mst.end_left_full(
  +xs: List<&2, Item>,
  -left: Maybe<&2, Hashes.Hash>,
  -m: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>
) -> {Mst.passes(xs, k2) == False{}: Bool} -> {Mst.end_left(xs, left, m) == left: Maybe<&2, Hashes.Hash>}:
  match xs:
    case Nil{}:
      +e => Empty.absurd({m == left: Maybe<&2, Hashes.Hash>}, Shared.Bool.true_ne_false(e))
    case Con{+x, +rest}:
      +e => {==}

# a pick that passes the first items, with their last subtree set to m, goes
# on from m
def Mst.pick_set_passes(
  +pre: List<&2, Item>,
  +m: Maybe<&2, Hashes.Hash>,
  +post: List<&2, Item>,
  +left: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  +e: {Mst.passes(pre, k2) == True{}: Bool}
) -> {
  Mst.pick(List.append(&2, Item, Mst.set_last(pre, m), post), Mst.end_left(pre, left, m), l, lo, hi, k2)
    == Mst.pick(post, m, l, Items.last_key(pre, lo), hi, k2): Pick
}:
  Equal.trans(
    Pick,
    Mst.pick(List.append(&2, Item, Mst.set_last(pre, m), post), Mst.end_left(pre, left, m), l, lo, hi, k2),
    Mst.pick(post, Mst.last(Mst.set_last(pre, m), Mst.end_left(pre, left, m)), l, Items.last_key(Mst.set_last(pre, m), lo), hi, k2),
    Mst.pick(post, m, l, Items.last_key(pre, lo), hi, k2),
    Mst.pick_passes(Mst.set_last(pre, m), post, Mst.end_left(pre, left, m), l, lo, hi, k2)(
      Equal.trans(Bool, Mst.passes(Mst.set_last(pre, m), k2), Mst.passes(pre, k2), True{}, Mst.passes_set_last(pre, m, k2), e)
    ),
    Equal.trans(
      Pick,
      Mst.pick(post, Mst.last(Mst.set_last(pre, m), Mst.end_left(pre, left, m)), l, Items.last_key(Mst.set_last(pre, m), lo), hi, k2),
      Mst.pick(post, m, l, Items.last_key(Mst.set_last(pre, m), lo), hi, k2),
      Mst.pick(post, m, l, Items.last_key(pre, lo), hi, k2),
      Equal.cong(
        Maybe<&2, Hashes.Hash>,
        Pick,
        a => Mst.pick(post, a, l, Items.last_key(Mst.set_last(pre, m), lo), hi, k2),
        Mst.last(Mst.set_last(pre, m), Mst.end_left(pre, left, m)),
        m,
        Mst.last_set_last(pre, left, m)
      ),
      Equal.cong(
        Maybe<&2, List<&2, U32>>,
        Pick,
        a => Mst.pick(post, m, l, a, hi, k2),
        Items.last_key(Mst.set_last(pre, m), lo),
        Items.last_key(pre, lo),
        Mst.last_key_set_last(pre, m, lo)
      )
    )
  )

# a read of a pick tells as a read of the same pick between wider bounds,
# in any fuel that reaches the level of the node
def Mst.look.same_pick(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +p1: Nat,
  +p2: Nat,
  +s: S,
  +xs: List<&2, Item>,
  +left: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  -h1: Hashes.Hash,
  -h2: Hashes.Hash,
  +k: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool},
  +fl: {Nat.is_le(l, p2) == True{}: Bool}
) -> {
  Look.known(Mst.look.pick(Mst.pick(xs, left, l, lo1, hi1, k), h1, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k)))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Look.known(Mst.look.pick(Mst.pick(xs, left, l, lo2, hi2, k), h2, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k)))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  Mst.look.wide.pick(
    l,
    Mst.pick(xs, left, l, lo1, hi1, k),
    Mst.pick(xs, left, l, lo2, hi2, k),
    h1,
    h2,
    k,
    m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k),
    m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k),
    x,
    Mst.pick_wide(xs, left, l, lo1, lo2, hi1, hi2, k, wl, wh),
    +m2 => +r3 => +r4 => +w => +eu => Mst.look.wide(
      ~S,
      ~fetch,
      p2,
      p1,
      m2,
      s,
      r3,
      r4,
      k,
      x,
      Mst.hop_of(~S, ~fetch, s, m2, r3, r4, w),
      Mst.room_bounds(r3, r4)(w),
      Equal.trans(
        Bool,
        Nat.is_le(Mst.room_up(r4), p2),
        Nat.is_le(l, p2),
        True{},
        Equal.cong(Nat, Bool, a => Nat.is_le(a, p2), Mst.room_up(r4), l, eu),
        fl
      )
    )
  )

# the last key of the first items, after wider bounds, is at or below
def Mst.lo_le_last(+pre: List<&2, Item>, +lo1: Maybe<&2, List<&2, U32>>, +lo2: Maybe<&2, List<&2, U32>>, +wl: {
  Mst.lo_le(lo2, lo1) == True{}: Bool
}) -> {Mst.lo_le(Items.last_key(pre, lo2), Items.last_key(pre, lo1)) == True{}: Bool}:
  match pre:
    case Nil{}:
      wl
    case Con{Item{+k, +v, +r}, +rest}:
      Mst.lo_le_refl(Items.last_key(rest, Some{k}))

# the head key of items, before wider bounds, is at or above
def Mst.hi_le_head(+post: List<&2, Item>, +hi1: Maybe<&2, List<&2, U32>>, +hi2: Maybe<&2, List<&2, U32>>, +wh: {
  Mst.hi_le(hi1, hi2) == True{}: Bool
}) -> {Mst.hi_le(Items.head_key(post, hi1), Items.head_key(post, hi2)) == True{}: Bool}:
  match post:
    case Nil{}:
      wh
    case Con{Item{+k, +v, +r}, +rest}:
      Mst.hi_le_refl(Some{k})

# Mst.gap_kept, once a pick passes the items before the gap (b2: whether the
# pick stops at the first item after it)
def Mst.gap_kept.first(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b2: Bool,
  +p1: Nat,
  +p2: Nat,
  +s: S,
  +post: List<&2, Item>,
  +g: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lk1: Maybe<&2, List<&2, U32>>,
  +lk2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  -h1: Hashes.Hash,
  -h2: Hashes.Hash,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eb: {Mst.stops_first(post, k2) == b2: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool},
  +fl: {Nat.is_le(l, p2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, lk1, Items.head_key(post, hi1)}, g, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, lk2, Items.head_key(post, hi2)}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Look.known(Mst.look.pick(Mst.pick(post, g, l, lk1, hi1, k2), h1, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Look.known(Mst.look.pick(Mst.pick(post, nc, l, lk2, hi2, k2), h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match b2:
    case True{}:
      %Equal.sym(
        Pick,
        Mst.pick(post, g, l, lk1, hi1, k2),
        Pick.Down{g, Room.of(l, lk1, Items.head_key(post, hi1))},
        Mst.pick_first(post, g, l, lk1, hi1, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(_, h1, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(Mst.pick(post, nc, l, lk2, hi2, k2), h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(post, nc, l, lk2, hi2, k2),
        Pick.Down{nc, Room.of(l, lk2, Items.head_key(post, hi2))},
        Mst.pick_first(post, nc, l, lk2, hi2, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(Pick.Down{g, Room.of(l, lk1, Items.head_key(post, hi1))}, h1, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      ih(p1)(p2)(fl)
    case False{}:
      %Mst.pick_past(post, g, nc, l, lk1, lk2, hi2, k2)(eb): (
        {
          Look.known(Mst.look.pick(Mst.pick(post, g, l, lk1, hi1, k2), h1, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.look.same_pick(~S, ~fetch, p1, p2, s, post, g, l, lk1, lk1, hi1, hi2, h1, h2, k2, x, Mst.lo_le_refl(lk1), wh, fl)

# Mst.gap_kept, by whether a pick passes the items before the gap (b)
def Mst.gap_kept.passes(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +p1: Nat,
  +p2: Nat,
  +s: S,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +left: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  -h1: Hashes.Hash,
  -h2: Hashes.Hash,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eb: {Mst.passes(pre, k2) == b: Bool},
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool},
  +fl: {Nat.is_le(l, p2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo1), Items.head_key(post, hi1)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo2), Items.head_key(post, hi2)}, nc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(
    Mst.look.pick(
      Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
      h1,
      l,
      k2,
      m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Look.known(
    Mst.look.pick(
      Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo2, hi2, k2),
      h2,
      l,
      k2,
      m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match b:
    case True{}:
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
        Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo1), hi1, k2),
        Mst.pick_passes(pre, post, left, l, lo1, hi1, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(_, h1, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo2, hi2, k2),
                h2,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo2, hi2, k2),
        Mst.pick(post, nc, l, Items.last_key(pre, lo2), hi2, k2),
        Mst.pick_set_passes(pre, nc, post, left, l, lo2, hi2, k2, eb)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo1), hi1, k2),
              h1,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.gap_kept.first(
        ~S,
        ~fetch,
        Mst.stops_first(post, k2),
        p1,
        p2,
        s,
        post,
        Mst.last(pre, left),
        nc,
        l,
        Items.last_key(pre, lo1),
        Items.last_key(pre, lo2),
        hi1,
        hi2,
        h1,
        h2,
        k2,
        x,
        {==},
        wh,
        fl,
        ih
      )
    case False{}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.end_left(pre, left, nc),
        left,
        Mst.end_left_full(pre, left, nc, k2)(eb)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
              h1,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), _, l, lo2, hi2, k2),
                h2,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), left, l, lo2, hi2, k2),
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo2, hi2, k2),
        Mst.pick_stops_set(pre, nc, post, post, left, l, lo2, hi2, hi2, k2)(eb)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
              h1,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.look.same_pick(~S, ~fetch, p1, p2, s, List.append(&2, Item, pre, post), left, l, lo1, lo2, hi1, hi2, h1, h2, k2, x, wl, wh, fl)

# no node opens below a fuel of 0
def Mst.opens_fuel(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +o: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, 0n) == True{}: Bool}
) -> Empty:
  Mst.nat_lt_zero(l)(Shared.Nat.lt_le(l, u, 0n)(Mst.opens_lt(l, left, xs, Room{u, lo, hi})(o))(fu))

# the level of a node that opens below a fuel of 1+p is at most p
def Mst.opens_fl(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +p: Nat,
  +o: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, 1n+p) == True{}: Bool}
) -> {Nat.is_le(l, p) == True{}: Bool}:
  Shared.Nat.lt_succ_le(l, p)(Shared.Nat.lt_le(l, u, 1n+p)(Mst.opens_lt(l, left, xs, Room{u, lo, hi})(o))(fu))

# a node with one gap replaced reads every key as before, but in the gap,
# where it reads as ih says
def Mst.gap_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +h2: Hashes.Hash,
  +u1: Nat,
  +u2: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{u1, lo1, hi1}) == True{}: Bool},
  +eN2: {
    Mst.node(~S, ~fetch, s, h2)
      == Some{Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}}: Maybe<&2, Node>
  },
  +oN2: {
    Mst.opens(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, Room{u2, lo2, hi2})
      == True{}: Bool
  },
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool},
  +fu: {Nat.is_le(u2, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo1), Items.head_key(post, hi1)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo2), Items.head_key(post, hi2)}, nc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, lo1, hi1}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, lo2, hi2}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u2, lo2, hi2}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{h2}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          u2,
          lo2,
          hi2,
          oN2,
          fu
        )
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{u1, lo1, hi1}, Some{h}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
          h,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
        ),
        Mst.look_node(~S, ~fetch, p1, s, h, u1, lo1, hi1, l, left, List.append(&2, Item, pre, post), k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, lo2, hi2}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, lo2, hi2}, Some{h2}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo2, hi2, k2),
          h2,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          h2,
          u2,
          lo2,
          hi2,
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          k2,
          eN2,
          oN2
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo1, hi1, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.gap_kept.passes(
        ~S,
        ~fetch,
        Mst.passes(pre, k2),
        p1,
        p2,
        s,
        pre,
        post,
        left,
        nc,
        l,
        lo1,
        lo2,
        hi1,
        hi2,
        h,
        h2,
        k2,
        x,
        {==},
        wl,
        wh,
        Mst.opens_fl(
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          u2,
          lo2,
          hi2,
          p2,
          oN2,
          fu
        ),
        ih
      )

# a node with one gap replaced tells of the key k what ih tells, when a
# pick of k passes the items before the gap and stops at the first after it
def Mst.gap_k(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g: Nat,
  +s: S,
  +h2: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN2: {
    Mst.node(~S, ~fetch, s, h2)
      == Some{Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}}: Maybe<&2, Node>
  },
  +oN2: {
    Mst.opens(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, Room{u, lo, hi})
      == True{}: Bool
  },
  +fu: {Nat.is_le(u, g) == True{}: Bool},
  +ep: {Mst.passes(pre, k) == True{}: Bool},
  +es: {Mst.stops_first(post, k) == True{}: Bool},
  ih: @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, nc, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hi}, Some{h2}, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g:
    case 0n:
      Empty.absurd(
        {Look.known(Look.Missing{h2}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          u,
          lo,
          hi,
          oN2,
          fu
        )
      )
    case 1n+(+p):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p, s, Room{u, lo, hi}, Some{h2}, k),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo, hi, k),
          h2,
          l,
          k,
          m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p,
          s,
          h2,
          u,
          lo,
          hi,
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          k,
          eN2,
          oN2
        )
      ): {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), post), Mst.end_left(pre, left, nc), l, lo, hi, k),
        Mst.pick(post, nc, l, Items.last_key(pre, lo), hi, k),
        Mst.pick_set_passes(pre, nc, post, left, l, lo, hi, k, ep)
      ): {Look.known(Mst.look.pick(_, h2, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k))) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      %Equal.sym(
        Pick,
        Mst.pick(post, nc, l, Items.last_key(pre, lo), hi, k),
        Pick.Down{nc, Room.of(l, Items.last_key(pre, lo), Items.head_key(post, hi))},
        Mst.pick_first(post, nc, l, Items.last_key(pre, lo), hi, k)(es)
      ): {Look.known(Mst.look.pick(_, h2, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k))) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      ih(p)(
        Mst.opens_fl(
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), post),
          u,
          lo,
          hi,
          p,
          oN2,
          fu
        )
      )

# what a read of a node in one room tells, a read of it in a room where it
# opens tells, with any fuel that reaches that room
def Mst.reroom(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g: Nat,
  +s: S,
  +h: Hashes.Hash,
  +r1: Room,
  +r2: Room,
  +n: Node,
  +k: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +en: {Mst.node.in(~S, ~fetch, s, h, r2) == Some{n}: Maybe<&2, Node>},
  +wb: {Mst.bounds_le(r1, r2) == True{}: Bool},
  +fu: {Nat.is_le(Mst.room_up(r2), g) == True{}: Bool}
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, r1, Some{h}, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g, s, r2, Some{h}, k)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  Mst.look.wide(
    ~S,
    ~fetch,
    g,
    g1,
    Some{h},
    s,
    r1,
    r2,
    k,
    x,
    +n2 => +e2 => +o =>
      %Shared.Maybe.some_inj(
        Node,
        n,
        n2,
        Equal.trans(
          Maybe<&2, Node>,
          Some{n},
          Mst.node(~S, ~fetch, s, h),
          Some{n2},
          Equal.sym(Maybe<&2, Node>, Mst.node(~S, ~fetch, s, h), Some{n}, Mst.in_node(~S, ~fetch, s, h, r2, n)(en)),
          e2
        )
      ): {Mst.opens(_, r2) == True{}: Bool}
      Mst.in_open(~S, ~fetch, s, h, r2, n)(en),
    wb,
    fu
  )

# a read of the empty tree finds the key absent
def Mst.look_none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g: Nat,
  -s: S,
  -r: Room,
  -k: List<&2, U32>
) -> {Mst.look.go(~S, ~fetch, g, s, r, None{}, k) == Look.Absent{}: Look}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a key after k passes every key before k
def Mst.passes_of_le(xs: List<&2, Item>, +k: List<&2, U32>, +k2: List<&2, U32>) -> {Mst.all_lt(xs, k) == True{}: Bool} -> {
  Cmp.is_le(Key.cmp(k, k2)) == True{}: Bool
} -> {Mst.passes(xs, k2) == True{}: Bool}:
  match xs:
    case Nil{}:
      +a => +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +a => +e => Shared.Bool.and_both(
        Cmp.is_gt(Key.cmp(k2, ik)),
        Mst.passes(rest, k2),
        Equal.cong(
          Cmp,
          Bool,
          Cmp.is_gt,
          Key.cmp(k2, ik),
          GT{},
          Mst.key_lt_gt(ik, k2)(
            Mst.key_lt_le(ik, k, k2)(
              Mst.lt_sound(Key.cmp(ik, k))(Shared.Bool.and_true_left(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))
            )(e)
          )
        ),
        Mst.passes_of_le(rest, k, k2)(Shared.Bool.and_true_right(Cmp.is_lt(Key.cmp(ik, k)), Mst.all_lt(rest, k), a))(e)
      )

# a pick that passes every item goes down after the last
def Mst.pick_all(
  +xs: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.passes(xs, k2) == True{}: Bool} -> {
  Mst.pick(xs, prev, l, lo, hi, k2) == Pick.Down{Mst.last(xs, prev), Room.of(l, Items.last_key(xs, lo), hi)}: Pick
}:
  match xs:
    case Nil{}:
      +e => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +e =>
        %Equal.sym(
          Cmp,
          Key.cmp(k2, ik),
          GT{},
          Mst.gt_sound(Key.cmp(k2, ik))(Shared.Bool.and_true_left(Cmp.is_gt(Key.cmp(k2, ik)), Mst.passes(rest, k2), e))
        ): {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(_),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k2))
          )
            == Pick.Down{Mst.last(rest, r), Room.of(l, Items.last_key(rest, Some{ik}), hi)}: Pick
        }
        Mst.pick_all(rest, r, l, Some{ik}, hi, k2)(Shared.Bool.and_true_right(Cmp.is_gt(Key.cmp(k2, ik)), Mst.passes(rest, k2), e))

# a pick of a key at or before k stops at once among items after k
def Mst.stops_first_of_fit(
  +xs: List<&2, Item>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Items.fit(xs, Some{k}, hi) == True{}: Bool} -> {List.is_empty(&2, Item, xs) == False{}: Bool} -> {
  Cmp.is_le(Key.cmp(k2, k)) == True{}: Bool
} -> {Mst.stops_first(xs, k2) == True{}: Bool}:
  match xs:
    case Nil{}:
      +f => +n => +c => Empty.absurd({True{} == True{}: Bool}, Shared.Bool.true_ne_false(n))
    case Con{Item{+x1, +v1, +r1}, +rest}:
      +f => +n => +c => Equal.cong(
        Cmp,
        Bool,
        Cmp.is_lt,
        Key.cmp(k2, x1),
        LT{},
        Mst.key_le_lt(k2, k, x1)(c)(
          Mst.key_lt_of(k, x1)(
            Shared.Bool.and_true_left(
              Key.is_lt(k, x1),
              Bound.before(x1, hi),
              Shared.Bool.and_true_left(Bool.and(Key.is_lt(k, x1), Bound.before(x1, hi)), Items.fit(rest, Some{x1}, hi), f)
            )
          )
        )
      )

# the items of a node that opens in a room fit its bounds
def Mst.opens_fit(
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +o: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool}
) -> {Items.fit(xs, lo, hi) == True{}: Bool}:
  Shared.Bool.and_true_right(Bool.and(Nat.is_lt(l, u), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi), o)

# a node that opens in a room has an item
def Mst.opens_full(
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +o: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool}
) -> {List.is_empty(&2, Item, xs) == False{}: Bool}:
  Shared.Bool.not_true(List.is_empty(&2, Item, xs))(
    Shared.Bool.and_true_right(
      Nat.is_lt(l, u),
      Bool.not(List.is_empty(&2, Item, xs)),
      Shared.Bool.and_true_left(Bool.and(Nat.is_lt(l, u), Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi), o)
    )
  )

# a node that opens in a room opens in a room of a higher up and wider
# bounds where its level is below the up
def Mst.opens_move(
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u1: Nat,
  +lo1: Maybe<&2, List<&2, U32>>,
  +hi1: Maybe<&2, List<&2, U32>>,
  +u2: Nat,
  +lo2: Maybe<&2, List<&2, U32>>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +lt: {Nat.is_lt(l, u2) == True{}: Bool},
  +wl: {Mst.lo_le(lo2, lo1) == True{}: Bool},
  +wh: {Mst.hi_le(hi1, hi2) == True{}: Bool},
  +o: {Mst.opens(Node{l, left, xs}, Room{u1, lo1, hi1}) == True{}: Bool}
) -> {Mst.opens(Node{l, left, xs}, Room{u2, lo2, hi2}) == True{}: Bool}:
  Mst.opens_lvl(
    Node{l, left, xs},
    Room{u1, lo1, hi1},
    Room{u2, lo2, hi2},
    lt,
    Shared.Bool.and_both(Mst.lo_le(lo2, lo1), Mst.hi_le(hi1, hi2), wl, wh)
  )(o)

# an edge that opens has a root that opens in its room
def Mst.edge_lvl.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  left: Bool,
  na: Maybe<&2, Node>,
  r: Room,
  -go: Room -> Maybe<&2, Hashes.Hash> -> Bool,
  +s: S,
  +h: Hashes.Hash,
  +en: {Mst.node.in(~S, ~fetch, s, h, r) == na: Maybe<&2, Node>}
) -> {Shared.Bool.when(Bool, left, u => Mst.edge.left.at(na, r, go), u => Mst.edge.right.at(na, r, go)) == True{}: Bool} -> {
  Mst.lvl(~S, ~fetch, s, Some{h}, Mst.room_up(r)) == True{}: Bool
}:
  match left na r:
    case True{} None{} Room{+u, +lo, +hi}:
      +e => Empty.absurd({Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} None{} Room{+u, +lo, +hi}:
      +e => Empty.absurd({Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case b Some{Node{+l, +lf, +xs}} Room{+u, +lo, +hi}:
      +e => Mst.lvl_of(
        ~S,
        ~fetch,
        s,
        h,
        u,
        l,
        lf,
        xs,
        Mst.in_node(~S, ~fetch, s, h, Room{u, lo, hi}, Node{l, lf, xs})(en),
        Mst.opens_lt(l, lf, xs, Room{u, lo, hi})(Mst.in_open(~S, ~fetch, s, h, Room{u, lo, hi}, Node{l, lf, xs})(en))
      )

# an edge that opens has a root whose level is below the up of its room
def Mst.edge_lvl(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +s: S,
  +left: Bool,
  +r: Room
) -> {Mst.edge(~S, ~fetch, f, s, left, r, m) == True{}: Bool} -> {Mst.lvl(~S, ~fetch, s, m, Mst.room_up(r)) == True{}: Bool}:
  match f m:
    case x None{}:
      +e => {==}
    case 0n Some{+h}:
      +e => Empty.absurd({Mst.lvl(~S, ~fetch, s, Some{h}, Mst.room_up(r)) == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case 1n+(+p) Some{+h}:
      Mst.edge_lvl.at(
        ~S,
        ~fetch,
        left,
        Mst.node.in(~S, ~fetch, s, h, r),
        r,
        r2 => c => Mst.edge(~S, ~fetch, p, s, left, r2, c),
        s,
        h,
        {==}
      )

# Mst.edge_left, at the node na of the root h
def Mst.edge_left.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  g: Nat,
  +p: Nat,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +k: List<&2, U32>,
  +hr: Maybe<&2, List<&2, U32>>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, Some{k}, hr}) == na: Maybe<&2, Node>},
  +lv: {Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +fu: {Nat.is_le(u, g) == True{}: Bool},
  +c: {Cmp.is_le(Key.cmp(k2, k)) == True{}: Bool},
  ih: @l: Nat -> @hr2: Maybe<&2, List<&2, U32>> -> @m: Maybe<&2, Hashes.Hash> -> @g2: Nat -> {
    Mst.edge(~S, ~fetch, p, s, True{}, Room{l, Some{k}, hr2}, m) == True{}: Bool
  } -> {Nat.is_le(l, g2) == True{}: Bool} -> {Mst.look.go(~S, ~fetch, g2, s, Room{l, lo, hr2}, m, k2) == Look.Absent{}: Look}
) -> {
  Mst.edge.left.at(na, Room{ur, Some{k}, hr}, r2 => c2 => Mst.edge(~S, ~fetch, p, s, True{}, r2, c2)) == True{}: Bool
} -> {Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hr}, Some{h}, k2) == Look.Absent{}: Look}:
  match na g:
    case None{} g0:
      +e => Empty.absurd({Mst.look.go(~S, ~fetch, g0, s, Room{u, lo, hr}, Some{h}, k2) == Look.Absent{}: Look}, Shared.Bool.false_ne_true(e))
    case Some{Node{+l, +lf, +xs}} 0n:
      +e => Empty.absurd(
        {Look.Missing{h} == Look.Absent{}: Look},
        Mst.nat_lt_zero(l)(
          Shared.Nat.lt_le(l, u, 0n)(
            Mst.lvl_lt(~S, ~fetch, s, h, u, l, lf, xs, lv, Mst.in_node(~S, ~fetch, s, h, Room{ur, Some{k}, hr}, Node{l, lf, xs})(en))
          )(fu)
        )
      )
    case Some{Node{+l, +lf, +xs}} 1n+(+q):
      +e =>
        +o = Mst.in_open(~S, ~fetch, s, h, Room{ur, Some{k}, hr}, Node{l, lf, xs})(en)
        +lt = Mst.lvl_lt(~S, ~fetch, s, h, u, l, lf, xs, lv, Mst.in_node(~S, ~fetch, s, h, Room{ur, Some{k}, hr}, Node{l, lf, xs})(en))
        +o2 = Mst.opens_move(l, lf, xs, ur, Some{k}, hr, u, lo, hr, lt, Mst.lo_le_key(lo, k)(a), Mst.hi_le_refl(hr), o)
        %Equal.sym(
          Look,
          Mst.look.go(~S, ~fetch, 1n+q, s, Room{u, lo, hr}, Some{h}, k2),
          Mst.look.pick(Mst.pick(xs, lf, l, lo, hr, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k2)),
          Mst.look_node(
            ~S,
            ~fetch,
            q,
            s,
            h,
            u,
            lo,
            hr,
            l,
            lf,
            xs,
            k2,
            Mst.in_node(~S, ~fetch, s, h, Room{ur, Some{k}, hr}, Node{l, lf, xs})(en),
            o2
          )
        ): {_ == Look.Absent{}: Look}
        %Equal.sym(
          Pick,
          Mst.pick(xs, lf, l, lo, hr, k2),
          Pick.Down{lf, Room.of(l, lo, Items.head_key(xs, hr))},
          Mst.pick_first(xs, lf, l, lo, hr, k2)(
            Mst.stops_first_of_fit(xs, k, hr, k2)(Mst.opens_fit(l, lf, xs, ur, Some{k}, hr, o))(
              Mst.opens_full(l, lf, xs, ur, Some{k}, hr, o)
            )(c)
          )
        ): {Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k2)) == Look.Absent{}: Look}
        ih(l)(Items.head_key(xs, hr))(lf)(q)(e)(Mst.opens_fl(l, lf, xs, u, lo, hr, q, o2, fu))

# a read of a key at or before k in a tree whose left edge opens in rooms
# after k, in a room of wider bounds, finds the key absent
def Mst.edge_left(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +g: Nat,
  +s: S,
  +ur: Nat,
  +k: List<&2, U32>,
  +hr: Maybe<&2, List<&2, U32>>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.edge(~S, ~fetch, f, s, True{}, Room{ur, Some{k}, hr}, m) == True{}: Bool} -> {
  Mst.lvl(~S, ~fetch, s, m, u) == True{}: Bool
} -> {Bound.after(lo, k) == True{}: Bool} -> {Nat.is_le(u, g) == True{}: Bool} -> {
  Cmp.is_le(Key.cmp(k2, k)) == True{}: Bool
} -> {Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hr}, m, k2) == Look.Absent{}: Look}:
  match f m:
    case x None{}:
      +e => +lv => +a => +fu => +c => Mst.look_none(~S, ~fetch, g, s, Room{u, lo, hr}, k2)
    case 0n Some{+h}:
      +e => +lv => +a => +fu => +c => Empty.absurd(
        {Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hr}, Some{h}, k2) == Look.Absent{}: Look},
        Shared.Bool.false_ne_true(e)
      )
    case 1n+(+p) Some{+h}:
      +e => +lv => +a => +fu => +c => Mst.edge_left.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, h, Room{ur, Some{k}, hr}),
        g,
        p,
        s,
        h,
        ur,
        k,
        hr,
        u,
        lo,
        k2,
        {==},
        lv,
        a,
        fu,
        c,
        +l => +hr2 => +m2 => +g2 => +e2 => +f2 => Mst.edge_left(~S, ~fetch, p, m2, g2, s, l, k, hr2, l, lo, k2)(e2)(
          Mst.edge_lvl(~S, ~fetch, p, m2, s, True{}, Room{l, Some{k}, hr2})(e2)
        )(a)(f2)(c)
      )(e)

# Mst.edge_right, at the node na of the root h
def Mst.edge_right.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  g: Nat,
  +p: Nat,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lr: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +u: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lr, Some{k}}) == na: Maybe<&2, Node>},
  +lv: {Mst.lvl(~S, ~fetch, s, Some{h}, u) == True{}: Bool},
  +b: {Bound.before(k, hi) == True{}: Bool},
  +fu: {Nat.is_le(u, g) == True{}: Bool},
  +c: {Cmp.is_le(Key.cmp(k, k2)) == True{}: Bool},
  ih: @l: Nat -> @lr2: Maybe<&2, List<&2, U32>> -> @m: Maybe<&2, Hashes.Hash> -> @g2: Nat -> {
    Mst.edge(~S, ~fetch, p, s, False{}, Room{l, lr2, Some{k}}, m) == True{}: Bool
  } -> {Nat.is_le(l, g2) == True{}: Bool} -> {Mst.look.go(~S, ~fetch, g2, s, Room{l, lr2, hi}, m, k2) == Look.Absent{}: Look}
) -> {
  Mst.edge.right.at(na, Room{ur, lr, Some{k}}, r2 => c2 => Mst.edge(~S, ~fetch, p, s, False{}, r2, c2)) == True{}: Bool
} -> {Mst.look.go(~S, ~fetch, g, s, Room{u, lr, hi}, Some{h}, k2) == Look.Absent{}: Look}:
  match na g:
    case None{} g0:
      +e => Empty.absurd({Mst.look.go(~S, ~fetch, g0, s, Room{u, lr, hi}, Some{h}, k2) == Look.Absent{}: Look}, Shared.Bool.false_ne_true(e))
    case Some{Node{+l, +lf, +xs}} 0n:
      +e => Empty.absurd(
        {Look.Missing{h} == Look.Absent{}: Look},
        Mst.nat_lt_zero(l)(
          Shared.Nat.lt_le(l, u, 0n)(
            Mst.lvl_lt(~S, ~fetch, s, h, u, l, lf, xs, lv, Mst.in_node(~S, ~fetch, s, h, Room{ur, lr, Some{k}}, Node{l, lf, xs})(en))
          )(fu)
        )
      )
    case Some{Node{+l, +lf, +xs}} 1n+(+q):
      +e =>
        +o = Mst.in_open(~S, ~fetch, s, h, Room{ur, lr, Some{k}}, Node{l, lf, xs})(en)
        +lt = Mst.lvl_lt(~S, ~fetch, s, h, u, l, lf, xs, lv, Mst.in_node(~S, ~fetch, s, h, Room{ur, lr, Some{k}}, Node{l, lf, xs})(en))
        +o2 = Mst.opens_move(l, lf, xs, ur, lr, Some{k}, u, lr, hi, lt, Mst.lo_le_refl(lr), Mst.hi_le_key(k, hi)(b), o)
        %Equal.sym(
          Look,
          Mst.look.go(~S, ~fetch, 1n+q, s, Room{u, lr, hi}, Some{h}, k2),
          Mst.look.pick(Mst.pick(xs, lf, l, lr, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k2)),
          Mst.look_node(
            ~S,
            ~fetch,
            q,
            s,
            h,
            u,
            lr,
            hi,
            l,
            lf,
            xs,
            k2,
            Mst.in_node(~S, ~fetch, s, h, Room{ur, lr, Some{k}}, Node{l, lf, xs})(en),
            o2
          )
        ): {_ == Look.Absent{}: Look}
        %Equal.sym(
          Pick,
          Mst.pick(xs, lf, l, lr, hi, k2),
          Pick.Down{Mst.last(xs, lf), Room.of(l, Items.last_key(xs, lr), hi)},
          Mst.pick_all(xs, lf, l, lr, hi, k2)(
            Mst.passes_of_le(xs, k, k2)(Mst.fit_all_lt(xs, lr, k)(Mst.opens_fit(l, lf, xs, ur, lr, Some{k}, o)))(c)
          )
        ): {Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k2)) == Look.Absent{}: Look}
        ih(l)(Items.last_key(xs, lr))(Mst.last(xs, lf))(q)(e)(Mst.opens_fl(l, lf, xs, u, lr, hi, q, o2, fu))

# a read of a key at or after k in a tree whose right edge opens in rooms
# before k, in a room of wider bounds, finds the key absent
def Mst.edge_right(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +g: Nat,
  +s: S,
  +ur: Nat,
  +lr: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +u: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Mst.edge(~S, ~fetch, f, s, False{}, Room{ur, lr, Some{k}}, m) == True{}: Bool} -> {
  Mst.lvl(~S, ~fetch, s, m, u) == True{}: Bool
} -> {Bound.before(k, hi) == True{}: Bool} -> {Nat.is_le(u, g) == True{}: Bool} -> {
  Cmp.is_le(Key.cmp(k, k2)) == True{}: Bool
} -> {Mst.look.go(~S, ~fetch, g, s, Room{u, lr, hi}, m, k2) == Look.Absent{}: Look}:
  match f m:
    case x None{}:
      +e => +lv => +b => +fu => +c => Mst.look_none(~S, ~fetch, g, s, Room{u, lr, hi}, k2)
    case 0n Some{+h}:
      +e => +lv => +b => +fu => +c => Empty.absurd(
        {Mst.look.go(~S, ~fetch, g, s, Room{u, lr, hi}, Some{h}, k2) == Look.Absent{}: Look},
        Shared.Bool.false_ne_true(e)
      )
    case 1n+(+p) Some{+h}:
      +e => +lv => +b => +fu => +c => Mst.edge_right.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, h, Room{ur, lr, Some{k}}),
        g,
        p,
        s,
        h,
        ur,
        lr,
        k,
        u,
        hi,
        k2,
        {==},
        lv,
        b,
        fu,
        c,
        +l => +lr2 => +m2 => +g2 => +e2 => +f2 => Mst.edge_right(~S, ~fetch, p, m2, g2, s, l, lr2, k, l, hi, k2)(e2)(
          Mst.edge_lvl(~S, ~fetch, p, m2, s, False{}, Room{l, lr2, Some{k}})(e2)
        )(b)(f2)(c)
      )(e)

# the empty tree, read with any fuel and in any room, tells the same
def Mst.none_kept(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  -s: S,
  -r1: Room,
  -r2: Room,
  -k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, r1, None{}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, r2, None{}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n 0n:
      +e => e
    case 0n 1n+q:
      +e => e
    case 1n+p 0n:
      +e => e
    case 1n+p 1n+q:
      +e => e

# a read that finds a key absent tells what a read of the empty tree tells
def Mst.absent_to(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +s: S,
  +r1: Room,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +t: Look,
  +et: {t == Look.Absent{}: Look}
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, r1, None{}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(t) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  +e =>
    %Equal.sym(Look, t, Look.Absent{}, et): {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    Equal.trans(
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      Look.known(Look.Absent{}),
      Look.known(Mst.look.go(~S, ~fetch, g1, s, r1, None{}, k2)),
      Some{x},
      Equal.cong(
        Look,
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Look.known,
        Look.Absent{},
        Mst.look.go(~S, ~fetch, g1, s, r1, None{}, k2),
        Equal.sym(Look, Mst.look.go(~S, ~fetch, g1, s, r1, None{}, k2), Look.Absent{}, Mst.look_none(~S, ~fetch, g1, s, r1, k2))
      ),
      e
    )

# a number above another is after it
def Mst.nat_gt_lt(+a: Nat, +b: Nat) -> {Nat.cmp(a, b) == GT{}: Cmp} -> {Nat.is_lt(b, a) == True{}: Bool}:
  +e => Equal.cong(
    Cmp,
    Bool,
    Cmp.is_lt,
    Nat.cmp(b, a),
    LT{},
    Equal.trans(Cmp, Nat.cmp(b, a), Mst.flip(Nat.cmp(a, b)), LT{}, Mst.nat_flip(a, b), Equal.cong(Cmp, Cmp, Mst.flip, Nat.cmp(a, b), GT{}, e))
  )

# a number below another is before it
def Mst.nat_lt_of(+a: Nat, +b: Nat) -> {Nat.cmp(a, b) == LT{}: Cmp} -> {Nat.is_lt(a, b) == True{}: Bool}:
  +e => Equal.cong(Cmp, Bool, Cmp.is_lt, Nat.cmp(a, b), LT{}, e)

# a comparison that is LT or EQ is at or below
def Mst.le_of_lt(+c: Cmp) -> {c == LT{}: Cmp} -> {Cmp.is_le(c) == True{}: Bool}:
  +e => Equal.cong(Cmp, Bool, Cmp.is_le, c, LT{}, e)

# a key is at or below itself
def Mst.le_refl_key(+k: List<&2, U32>) -> {Cmp.is_le(Key.cmp(k, k)) == True{}: Bool}:
  Equal.cong(Cmp, Bool, Cmp.is_le, Key.cmp(k, k), EQ{}, Mst.key_refl(k))

# items with their last subtree set are as empty as before
def Mst.empty_set_last(+xs: List<&2, Item>, -m: Maybe<&2, Hashes.Hash>) -> {
  List.is_empty(&2, Item, Mst.set_last(xs, m)) == List.is_empty(&2, Item, xs): Bool
}:
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+k, +v, +r}, Nil{}}:
      {==}
    case Con{Item{+k, +v, +r}, Con{+y, +rest}}:
      {==}

# items that are not empty, then more, are not empty
def Mst.empty_append(+xs: List<&2, Item>, -ys: List<&2, Item>) -> {List.is_empty(&2, Item, xs) == False{}: Bool} -> {
  List.is_empty(&2, Item, List.append(&2, Item, xs, ys)) == False{}: Bool
}:
  match xs:
    case Nil{}:
      +e => Empty.absurd({List.is_empty(&2, Item, ys) == False{}: Bool}, Shared.Bool.true_ne_false(e))
    case Con{+x, +rest}:
      +e => {==}

# k comes before the head key of items after k
def Mst.before_head(+xb: List<&2, Item>, +k: List<&2, U32>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Items.fit(xb, Some{k}, hi) == True{}: Bool
} -> {Bound.before(k, hi) == True{}: Bool} -> {Bound.before(k, Items.head_key(xb, hi)) == True{}: Bool}:
  match xb:
    case Nil{}:
      +f => +b => b
    case Con{Item{+x1, +v1, +r1}, +rest}:
      +f => +b => Shared.Bool.and_true_left(
        Key.is_lt(k, x1),
        Bound.before(x1, hi),
        Shared.Bool.and_true_left(Bool.and(Key.is_lt(k, x1), Bound.before(x1, hi)), Items.fit(rest, Some{x1}, hi), f)
      )

# what holds of items holds of them followed by nothing
def Mst.with_nil(-P: List<&2, Item> -> Type, +xs: List<&2, Item>, p: P(xs)) -> P(List.append(&2, Item, xs, [])):
  %Equal.sym(List<&2, Item>, List.append(&2, Item, xs, []), xs, Shared.List.append_nil(Item, xs)): P(_)
  p

# what holds of items followed by nothing holds of them
def Mst.without_nil(-P: List<&2, Item> -> Type, +xs: List<&2, Item>, p: P(List.append(&2, Item, xs, []))) -> P(xs):
  %Shared.List.append_nil(Item, xs): P(_)
  p

# what a merge reads: below k, as the tree ma in the room after lo; above k,
# as the tree mb in the room before hi; and k, absent; in the room of the up
# u, between lo and hi
def Mst.MergeRead(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -u: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -hi: Maybe<&2, List<&2, U32>>,
  -ma: Maybe<&2, Hashes.Hash>,
  -mb: Maybe<&2, Hashes.Hash>,
  -nc: Maybe<&2, Hashes.Hash>
) -> Type:
  (
    @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {Key.cmp(k2, k) == LT{}: Cmp} -> {
      Nat.is_le(u, g2) == True{}: Bool
    } -> {
      Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, lo, Some{k}}, ma, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
  )
    & (
      (
        @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {Key.cmp(k2, k) == GT{}: Cmp} -> {
          Nat.is_le(u, g2) == True{}: Bool
        } -> {
          Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, Some{k}, hi}, mb, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
        & (
          @g2: Nat -> {Nat.is_le(u, g2) == True{}: Bool} -> {
            Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, nc, k)) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
        )
    )

# what a merge reads, in any room whose up is above both roots, between
# bounds around k
def Mst.MergeMain(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -lo: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -hi: Maybe<&2, List<&2, U32>>,
  -ma: Maybe<&2, Hashes.Hash>,
  -mb: Maybe<&2, Hashes.Hash>,
  -nc: Maybe<&2, Hashes.Hash>
) -> Type:
  @u: Nat -> {Mst.lvl(~S, ~fetch, s, ma, u) == True{}: Bool} -> {Mst.lvl(~S, ~fetch, s, mb, u) == True{}: Bool} -> {
    Bound.after(lo, k) == True{}: Bool
  } -> {Bound.before(k, hi) == True{}: Bool} -> Mst.MergeRead(~S, ~fetch, s, u, lo, k, hi, ma, mb, nc)

# a merge res of the trees ma, in the room of the up ua after lo, and mb, in
# the room of the up ub before hi, around the key k: once the depot holds its
# new nodes, the roots sit in their rooms, and it reads as Mst.MergeMain says
def Mst.MergeOk(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -ua: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -ub: Nat,
  -hi: Maybe<&2, List<&2, U32>>,
  -ma: Maybe<&2, Hashes.Hash>,
  -mb: Maybe<&2, Hashes.Hash>,
  res: Maybe<&2, Edit>
) -> Type:
  match res:
    case None{}:
      Unit
    case Some{Edit{nc, ns}}:
      {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool} -> (
        ({Mst.lvl(~S, ~fetch, s, ma, ua) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, mb, ub) == True{}: Bool})
          & Mst.MergeMain(~S, ~fetch, s, lo, k, hi, ma, mb, nc)
      )

# a merge of two empty trees
def Mst.merge_ok.none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  -ua: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  -ub: Nat,
  -hi: Maybe<&2, List<&2, U32>>
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, None{}, None{}, Some{Edit{None{}, []}}):
  +hold => (
    ({==}, {==}),
    +u => +lva => +lvb => +a => +b => (
      +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.none_kept(~S, ~fetch, g1, g2, s, Room{u1, lo, Some{k}}, Room{u, lo, hi}, k2, x),
      (
        +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.none_kept(~S, ~fetch, g1, g2, s, Room{u1, Some{k}, hi}, Room{u, lo, hi}, k2, x),
        +g2 => +fu => Equal.cong(
          Look,
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Look.known,
          Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, None{}, k),
          Look.Absent{},
          Mst.look_none(~S, ~fetch, g2, s, Room{u, lo, hi}, k)
        )
      )
    )
  )

# a merge of an empty tree and the tree of hb, once its left edge opens (b)
def Mst.merge_ok.lone_b(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +s: S,
  -ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +hb: Hashes.Hash,
  +eb: {Mst.edge(~S, ~fetch, Mst.depth(), s, True{}, Room{ub, Some{k}, hi}, Some{hb}) == b: Bool}
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, None{}, Some{hb}, Shared.Maybe.when(Edit, b, u => Some{Edit{Some{hb}, []}})):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +hold => (
        ({==}, Mst.edge_lvl(~S, ~fetch, Mst.depth(), Some{hb}, s, True{}, Room{ub, Some{k}, hi})(eb)),
        +u => +lva => +lvb => +a => +bb => (
          +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.absent_to(
            ~S,
            ~fetch,
            g1,
            s,
            Room{u1, lo, Some{k}},
            k2,
            x,
            Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{hb}, k2),
            Mst.edge_left(~S, ~fetch, Mst.depth(), Some{hb}, g2, s, ub, k, hi, u, lo, k2)(eb)(lvb)(a)(fu)(
              Mst.le_of_lt(Key.cmp(k2, k))(c)
            )
          )(e),
          (
            +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.look.wide(
              ~S,
              ~fetch,
              g2,
              g1,
              Some{hb},
              s,
              Room{u1, Some{k}, hi},
              Room{u, lo, hi},
              k2,
              x,
              Mst.hop_lvl(
                ~S,
                ~fetch,
                s,
                Some{hb},
                Room{u1, Some{k}, hi},
                Room{u, lo, hi},
                lvb,
                Shared.Bool.and_both(Mst.lo_le(lo, Some{k}), Mst.hi_le(hi, hi), Mst.lo_le_key(lo, k)(a), Mst.hi_le_refl(hi))
              ),
              Shared.Bool.and_both(Mst.lo_le(lo, Some{k}), Mst.hi_le(hi, hi), Mst.lo_le_key(lo, k)(a), Mst.hi_le_refl(hi)),
              fu
            ),
            +g2 => +fu => Equal.cong(
              Look,
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              Look.known,
              Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{hb}, k),
              Look.Absent{},
              Mst.edge_left(~S, ~fetch, Mst.depth(), Some{hb}, g2, s, ub, k, hi, u, lo, k)(eb)(lvb)(a)(fu)(Mst.le_refl_key(k))
            )
          )
        )
      )

# a merge of the tree of ha and an empty tree, once its right edge opens (b)
def Mst.merge_ok.lone_a(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +s: S,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  -ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +ha: Hashes.Hash,
  +eb: {Mst.edge(~S, ~fetch, Mst.depth(), s, False{}, Room{ua, lo, Some{k}}, Some{ha}) == b: Bool}
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, None{}, Shared.Maybe.when(Edit, b, u => Some{Edit{Some{ha}, []}})):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +hold => (
        (Mst.edge_lvl(~S, ~fetch, Mst.depth(), Some{ha}, s, False{}, Room{ua, lo, Some{k}})(eb), {==}),
        +u => +lva => +lvb => +a => +bb => (
          +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.look.wide(
            ~S,
            ~fetch,
            g2,
            g1,
            Some{ha},
            s,
            Room{u1, lo, Some{k}},
            Room{u, lo, hi},
            k2,
            x,
            Mst.hop_lvl(
              ~S,
              ~fetch,
              s,
              Some{ha},
              Room{u1, lo, Some{k}},
              Room{u, lo, hi},
              lva,
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(Some{k}, hi), Mst.lo_le_refl(lo), Mst.hi_le_key(k, hi)(bb))
            ),
            Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(Some{k}, hi), Mst.lo_le_refl(lo), Mst.hi_le_key(k, hi)(bb)),
            fu
          ),
          (
            +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.absent_to(
              ~S,
              ~fetch,
              g1,
              s,
              Room{u1, Some{k}, hi},
              k2,
              x,
              Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{ha}, k2),
              Mst.edge_right(~S, ~fetch, Mst.depth(), Some{ha}, g2, s, ua, lo, k, u, hi, k2)(eb)(lva)(bb)(fu)(
                Mst.le_of_lt(Key.cmp(k, k2))(Mst.key_gt_lt(k2, k)(c))
              )
            )(e),
            +g2 => +fu => Equal.cong(
              Look,
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              Look.known,
              Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{ha}, k),
              Look.Absent{},
              Mst.edge_right(~S, ~fetch, Mst.depth(), Some{ha}, g2, s, ua, lo, k, u, hi, k)(eb)(lva)(bb)(fu)(Mst.le_refl_key(k))
            )
          )
        )
      )

# a node of the items of a, the subtree between them merged, then the items
# of b opens in a room of the up u around k
def Mst.opens_both(
  +la: Nat,
  -el: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +lt: {Nat.is_lt(la, u) == True{}: Bool},
  +na: {List.is_empty(&2, Item, xa) == False{}: Bool},
  +fa: {Items.fit(xa, lo, Some{k}) == True{}: Bool},
  +fb: {Items.fit(xb, Some{k}, hi) == True{}: Bool},
  +ak: {Bound.after(Items.last_key(xa, lo), k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool}
) -> {Mst.opens(Node{la, el, List.append(&2, Item, Mst.set_last(xa, mc), xb)}, Room{u, lo, hi}) == True{}: Bool}:
  Shared.Bool.and_both(
    Bool.and(Nat.is_lt(la, u), Bool.not(List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xa, mc), xb)))),
    Items.fit(List.append(&2, Item, Mst.set_last(xa, mc), xb), lo, hi),
    Shared.Bool.and_both(
      Nat.is_lt(la, u),
      Bool.not(List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xa, mc), xb))),
      lt,
      Equal.cong(
        Bool,
        Bool,
        Bool.not,
        List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xa, mc), xb)),
        False{},
        Equal.trans(
          Bool,
          List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xa, mc), xb)),
          List.is_empty(&2, Item, List.append(&2, Item, xa, xb)),
          False{},
          Mst.empty_set_last_append(xa, mc, xb),
          Mst.empty_append(xa, xb)(na)
        )
      )
    ),
    Equal.trans(
      Bool,
      Items.fit(List.append(&2, Item, Mst.set_last(xa, mc), xb), lo, hi),
      Items.fit(List.append(&2, Item, xa, xb), lo, hi),
      True{},
      Mst.fit_set_last_append(xa, mc, xb, lo, hi),
      Equal.trans(
        Bool,
        Items.fit(List.append(&2, Item, xa, xb), lo, hi),
        Bool.and(Items.fit(xa, lo, hi), Items.fit(xb, Items.last_key(xa, lo), hi)),
        True{},
        Mst.fit_append(xa, xb, lo, hi),
        Shared.Bool.and_both(
          Items.fit(xa, lo, hi),
          Items.fit(xb, Items.last_key(xa, lo), hi),
          Mst.fit_wide(xa, lo, lo, Some{k}, hi, Mst.lo_le_refl(lo), Mst.hi_le_key(k, hi)(bb))(fa),
          Mst.fit_wide(xb, Some{k}, Items.last_key(xa, lo), hi, hi, Mst.lo_le_key(Items.last_key(xa, lo), k)(ak), Mst.hi_le_refl(hi))(fb)
        )
      )
    )
  )

# what a merge whose a is of a higher level reads, from what the merge of the
# last subtree of a with b reads (tri)
def Mst.merge_ok.gt.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ha: Hashes.Hash,
  -hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +hold: {
    Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []) <> ns)
      == True{}: Bool
  },
  +u: Nat,
  +lva: {Mst.lvl(~S, ~fetch, s, Some{ha}, u) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  tri: Mst.MergeRead(~S, ~fetch, s, la, Items.last_key(xa, lo), k, hi, Mst.last(xa, lefta), Some{hb}, mc)
) -> Mst.MergeRead(
  ~S,
  ~fetch,
  s,
  u,
  lo,
  k,
  hi,
  Some{ha},
  Some{hb},
  Some{Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []))}
):
  (ilo, r3) = tri
  (ihi, ik) = r3
  +eA = Mst.in_node(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +oA = Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +lt = Mst.lvl_lt(~S, ~fetch, s, ha, u, la, lefta, xa, lva, eA)
  +all = Mst.fit_all_lt(xa, lo, k)(Mst.opens_fit(la, lefta, xa, ua, lo, Some{k}, oA))
  +eN = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)},
    Mst.holds_head(~S, ~fetch, s, Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []), ns, hold)
  )
  +oN = Mst.opens_set_last(la, lefta, Mst.end_left(xa, lefta, mc), xa, mc, [], Room{u, lo, hi})(
    Mst.with_nil(
      ys => {Mst.opens(Node{la, lefta, ys}, Room{u, lo, hi}) == True{}: Bool},
      xa,
      Mst.opens_move(la, lefta, xa, ua, lo, Some{k}, u, lo, hi, lt, Mst.lo_le_refl(lo), Mst.hi_le_key(k, hi)(bb), oA)
    )
  )
  +eN2 = Mst.with_nil(
    ys => {
      Mst.node(~S, ~fetch, s, Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, [])))
        == Some{Node{la, Mst.end_left(xa, lefta, mc), ys}}: Maybe<&2, Node>
    },
    Mst.set_last(xa, mc),
    eN
  )
  (
    +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_kept(
      ~S,
      ~fetch,
      ua,
      g2,
      s,
      ha,
      Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, [])),
      ua,
      u,
      lo,
      lo,
      Some{k},
      hi,
      la,
      lefta,
      xa,
      [],
      mc,
      k2,
      x,
      Mst.with_nil(ys => {Mst.node(~S, ~fetch, s, ha) == Some{Node{la, lefta, ys}}: Maybe<&2, Node>}, xa, eA),
      Mst.with_nil(ys => {Mst.opens(Node{la, lefta, ys}, Room{ua, lo, Some{k}}) == True{}: Bool}, xa, oA),
      eN2,
      oN,
      Mst.lo_le_refl(lo),
      Mst.hi_le_key(k, hi)(bb),
      fu,
      +g3 => +g4 => +fl => +e3 => ilo(k2)(x)(la)(g3)(g4)(c)(fl)(e3)
    )(
      Mst.reroom(
        ~S,
        ~fetch,
        g1,
        ua,
        s,
        ha,
        Room{u1, lo, Some{k}},
        Room{ua, lo, Some{k}},
        Node{la, lefta, xa},
        k2,
        x,
        ena,
        Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(Some{k}, Some{k}), Mst.lo_le_refl(lo), Mst.hi_le_refl(Some{k})),
        Shared.Nat.le_refl(ua)
      )(e)
    ),
    (
      +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_k(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, [])),
        u,
        lo,
        hi,
        la,
        lefta,
        xa,
        [],
        mc,
        k2,
        x,
        eN2,
        oN,
        fu,
        Mst.passes_of_le(xa, k, k2)(all)(Mst.le_of_lt(Key.cmp(k, k2))(Mst.key_gt_lt(k2, k)(c))),
        {==},
        +g4 => +fl => ihi(k2)(x)(u1)(g1)(g4)(c)(fl)(e)
      ),
      +g2 => +fu => Mst.gap_k(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, [])),
        u,
        lo,
        hi,
        la,
        lefta,
        xa,
        [],
        mc,
        k,
        None{},
        eN2,
        oN,
        fu,
        Mst.passes_of_all_lt(xa, k)(all),
        {==},
        +g4 => +fl => ik(g4)(fl)
      )
    )
  )

# the roots of a merge whose a is of a higher level, and what it reads, from
# those of the merge of the last subtree of a with b (bi)
def Mst.merge_ok.gt.body(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == GT{}: Cmp},
  +hold: {
    Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []) <> ns)
      == True{}: Bool
  },
  bi: ({Mst.lvl(~S, ~fetch, s, Mst.last(xa, lefta), la) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, Some{hb}, ub) == True{}: Bool})
    & Mst.MergeMain(~S, ~fetch, s, Items.last_key(xa, lo), k, hi, Mst.last(xa, lefta), Some{hb}, mc)
) -> ({Mst.lvl(~S, ~fetch, s, Some{ha}, ua) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, Some{hb}, ub) == True{}: Bool})
  & Mst.MergeMain(
    ~S,
    ~fetch,
    s,
    lo,
    k,
    hi,
    Some{ha},
    Some{hb},
    Some{Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []))}
  ):
  (lvs2, main2) = bi
  (lva2, lvb2) = lvs2
  +eA = Mst.in_node(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +oA = Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +eB = Mst.in_node(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +oB = Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  (
    (
      Mst.lvl_of(~S, ~fetch, s, ha, ua, la, lefta, xa, eA, Mst.opens_lt(la, lefta, xa, Room{ua, lo, Some{k}})(oA)),
      Mst.lvl_of(~S, ~fetch, s, hb, ub, lb, leftb, xb, eB, Mst.opens_lt(lb, leftb, xb, Room{ub, Some{k}, hi})(oB))
    ),
    +u => +lva => +lvb => +a => +bb => Mst.merge_ok.gt.read(
      ~S,
      ~fetch,
      s,
      ha,
      hb,
      ua,
      lo,
      k,
      hi,
      la,
      lefta,
      xa,
      mc,
      ns,
      ena,
      hold,
      u,
      lva,
      a,
      bb,
      main2(la)(lva2)(Mst.lvl_of(~S, ~fetch, s, hb, la, lb, leftb, xb, eB, Mst.nat_gt_lt(la, lb)(ec)))(
        Mst.last_below(xa, lo, k)(Mst.fit_all_lt(xa, lo, k)(Mst.opens_fit(la, lefta, xa, ua, lo, Some{k}, oA)))(a)
      )(bb)
    )
  )

# a merge whose a is of a higher level: a with its last subtree merged with b
def Mst.merge_ok.gt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  res: Maybe<&2, Edit>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == GT{}: Cmp},
  ih: Mst.MergeOk(~S, ~fetch, s, la, Items.last_key(xa, lo), k, ub, hi, Mst.last(xa, lefta), Some{hb}, res)
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Mst.with_last(la, lefta, xa, res)):
  match res:
    case None{}:
      Unit{}
    case Some{Edit{+mc, +ns}}:
      %Equal.sym(
        Edit,
        Mst.make(la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc), ns),
        Mst.store(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, ns),
        Mst.make_full(la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc), ns)(
          Equal.trans(
            Bool,
            List.is_empty(&2, Item, Mst.set_last(xa, mc)),
            List.is_empty(&2, Item, xa),
            False{},
            Mst.empty_set_last(xa, mc),
            Mst.opens_full(la, lefta, xa, ua, lo, Some{k}, Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena))
          )
        )
      ): Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Some{_})
      +hold => Mst.merge_ok.gt.body(
        ~S,
        ~fetch,
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        mc,
        ns,
        ena,
        enb,
        ec,
        hold,
        ih(Mst.holds_tail(~S, ~fetch, s, Node.code(Node{la, Mst.end_left(xa, lefta, mc), Mst.set_last(xa, mc)}, []), ns, hold))
      )

# what a merge whose b is of a higher level reads, from what the merge of a
# with the left subtree of b reads (tri)
def Mst.merge_ok.lt.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  -ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ub: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +hold: {Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{lb, mc, xb}, []) <> ns) == True{}: Bool},
  +u: Nat,
  +lvb: {Mst.lvl(~S, ~fetch, s, Some{hb}, u) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  tri: Mst.MergeRead(~S, ~fetch, s, lb, lo, k, Items.head_key(xb, hi), Some{ha}, leftb, mc)
) -> Mst.MergeRead(~S, ~fetch, s, u, lo, k, hi, Some{ha}, Some{hb}, Some{Hashes.Sha.hash(Node.code(Node{lb, mc, xb}, []))}):
  (ilo, r3) = tri
  (ihi, ik) = r3
  +eB = Mst.in_node(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +oB = Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +lt = Mst.lvl_lt(~S, ~fetch, s, hb, u, lb, leftb, xb, lvb, eB)
  +fb = Mst.opens_fit(lb, leftb, xb, ub, Some{k}, hi, oB)
  +nb = Mst.opens_full(lb, leftb, xb, ub, Some{k}, hi, oB)
  +eN = Mst.node_code(~S, ~fetch, s, Node{lb, mc, xb}, Mst.holds_head(~S, ~fetch, s, Node.code(Node{lb, mc, xb}, []), ns, hold))
  +oN = Mst.opens_move(lb, leftb, xb, ub, Some{k}, hi, u, lo, hi, lt, Mst.lo_le_key(lo, k)(a), Mst.hi_le_refl(hi), oB)
  (
    +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_k(
      ~S,
      ~fetch,
      g2,
      s,
      Hashes.Sha.hash(Node.code(Node{lb, mc, xb}, [])),
      u,
      lo,
      hi,
      lb,
      leftb,
      [],
      xb,
      mc,
      k2,
      x,
      eN,
      oN,
      fu,
      {==},
      Mst.stops_first_of_fit(xb, k, hi, k2)(fb)(nb)(Mst.le_of_lt(Key.cmp(k2, k))(c)),
      +g4 => +fl => ilo(k2)(x)(u1)(g1)(g4)(c)(fl)(e)
    ),
    (
      +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_kept(
        ~S,
        ~fetch,
        ub,
        g2,
        s,
        hb,
        Hashes.Sha.hash(Node.code(Node{lb, mc, xb}, [])),
        ub,
        u,
        Some{k},
        lo,
        hi,
        hi,
        lb,
        leftb,
        [],
        xb,
        mc,
        k2,
        x,
        eB,
        oB,
        eN,
        oN,
        Mst.lo_le_key(lo, k)(a),
        Mst.hi_le_refl(hi),
        fu,
        +g3 => +g4 => +fl => +e3 => ihi(k2)(x)(lb)(g3)(g4)(c)(fl)(e3)
      )(
        Mst.reroom(
          ~S,
          ~fetch,
          g1,
          ub,
          s,
          hb,
          Room{u1, Some{k}, hi},
          Room{ub, Some{k}, hi},
          Node{lb, leftb, xb},
          k2,
          x,
          enb,
          Shared.Bool.and_both(Mst.lo_le(Some{k}, Some{k}), Mst.hi_le(hi, hi), Mst.lo_le_refl(Some{k}), Mst.hi_le_refl(hi)),
          Shared.Nat.le_refl(ub)
        )(e)
      ),
      +g2 => +fu => Mst.gap_k(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{lb, mc, xb}, [])),
        u,
        lo,
        hi,
        lb,
        leftb,
        [],
        xb,
        mc,
        k,
        None{},
        eN,
        oN,
        fu,
        {==},
        Mst.stops_first_of_fit(xb, k, hi, k)(fb)(nb)(Mst.le_refl_key(k)),
        +g4 => +fl => ik(g4)(fl)
      )
    )
  )

# the roots of a merge whose b is of a higher level, and what it reads, from
# those of the merge of a with the left subtree of b (bi)
def Mst.merge_ok.lt.body(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == LT{}: Cmp},
  +hold: {Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{lb, mc, xb}, []) <> ns) == True{}: Bool},
  bi: ({Mst.lvl(~S, ~fetch, s, Some{ha}, ua) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, leftb, lb) == True{}: Bool})
    & Mst.MergeMain(~S, ~fetch, s, lo, k, Items.head_key(xb, hi), Some{ha}, leftb, mc)
) -> ({Mst.lvl(~S, ~fetch, s, Some{ha}, ua) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, Some{hb}, ub) == True{}: Bool})
  & Mst.MergeMain(~S, ~fetch, s, lo, k, hi, Some{ha}, Some{hb}, Some{Hashes.Sha.hash(Node.code(Node{lb, mc, xb}, []))}):
  (lvs2, main2) = bi
  (lva2, lvb2) = lvs2
  +eA = Mst.in_node(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +oA = Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +eB = Mst.in_node(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +oB = Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  (
    (
      Mst.lvl_of(~S, ~fetch, s, ha, ua, la, lefta, xa, eA, Mst.opens_lt(la, lefta, xa, Room{ua, lo, Some{k}})(oA)),
      Mst.lvl_of(~S, ~fetch, s, hb, ub, lb, leftb, xb, eB, Mst.opens_lt(lb, leftb, xb, Room{ub, Some{k}, hi})(oB))
    ),
    +u => +lva => +lvb => +a => +bb => Mst.merge_ok.lt.read(
      ~S,
      ~fetch,
      s,
      ha,
      hb,
      ub,
      lo,
      k,
      hi,
      lb,
      leftb,
      xb,
      mc,
      ns,
      enb,
      hold,
      u,
      lvb,
      a,
      main2(lb)(Mst.lvl_of(~S, ~fetch, s, ha, lb, la, lefta, xa, eA, Mst.nat_lt_of(la, lb)(ec)))(lvb2)(a)(
        Mst.before_head(xb, k, hi)(Mst.opens_fit(lb, leftb, xb, ub, Some{k}, hi, oB))(bb)
      )
    )
  )

# a merge whose b is of a higher level: b with its left subtree merged with a
def Mst.merge_ok.lt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  res: Maybe<&2, Edit>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == LT{}: Cmp},
  ih: Mst.MergeOk(~S, ~fetch, s, ua, lo, k, lb, Items.head_key(xb, hi), Some{ha}, leftb, res)
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Mst.with_first(lb, xb, res)):
  match res:
    case None{}:
      Unit{}
    case Some{Edit{+mc, +ns}}:
      %Equal.sym(
        Edit,
        Mst.make(lb, mc, xb, ns),
        Mst.store(Node{lb, mc, xb}, ns),
        Mst.make_full(lb, mc, xb, ns)(
          Mst.opens_full(lb, leftb, xb, ub, Some{k}, hi, Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb))
        )
      ): Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Some{_})
      +hold => Mst.merge_ok.lt.body(
        ~S,
        ~fetch,
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        mc,
        ns,
        ena,
        enb,
        ec,
        hold,
        ih(Mst.holds_tail(~S, ~fetch, s, Node.code(Node{lb, mc, xb}, []), ns, hold))
      )

# Mst.merge_eq_lo, by whether a pick passes the items of a (b)
def Mst.merge_eq_lo.passes(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +p1: Nat,
  +p2: Nat,
  +s: S,
  -ha: Hashes.Hash,
  -hn: Hashes.Hash,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eb: {Mst.passes(xa, k2) == b: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +c: {Key.cmp(k2, k) == LT{}: Cmp},
  +fb: {Items.fit(xb, Some{k}, hi) == True{}: Bool},
  +nb: {List.is_empty(&2, Item, xb) == False{}: Bool},
  +fl: {Nat.is_le(la, p2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(la, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{la, Items.last_key(xa, lo), Some{k}}, Mst.last(xa, lefta), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{la, Items.last_key(xa, lo), Items.head_key(xb, hi)}, mc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Look.known(
    Mst.look.pick(
      Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
      hn,
      la,
      k2,
      m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match b:
    case True{}:
      %Equal.sym(
        Pick,
        Mst.pick(xa, lefta, la, lo, Some{k}, k2),
        Pick.Down{Mst.last(xa, lefta), Room.of(la, Items.last_key(xa, lo), Some{k})},
        Mst.pick_all(xa, lefta, la, lo, Some{k}, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(_, ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
                hn,
                la,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
        Mst.pick(xb, mc, la, Items.last_key(xa, lo), hi, k2),
        Mst.pick_set_passes(xa, mc, xb, lefta, la, lo, hi, k2, eb)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Pick.Down{Mst.last(xa, lefta), Room.of(la, Items.last_key(xa, lo), Some{k})},
              ha,
              la,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(xb, mc, la, Items.last_key(xa, lo), hi, k2),
        Pick.Down{mc, Room.of(la, Items.last_key(xa, lo), Items.head_key(xb, hi))},
        Mst.pick_first(xb, mc, la, Items.last_key(xa, lo), hi, k2)(
          Mst.stops_first_of_fit(xb, k, hi, k2)(fb)(nb)(Mst.le_of_lt(Key.cmp(k2, k))(c))
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Pick.Down{Mst.last(xa, lefta), Room.of(la, Items.last_key(xa, lo), Some{k})},
              ha,
              la,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      ih(p1)(p2)(fl)
    case False{}:
      %Equal.sym(Maybe<&2, Hashes.Hash>, Mst.end_left(xa, lefta, mc), lefta, Mst.end_left_full(xa, lefta, mc, k2)(eb)): (
        {
          Look.known(Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), _, la, lo, hi, k2),
                hn,
                la,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), lefta, la, lo, hi, k2),
        Mst.pick(List.append(&2, Item, xa, []), lefta, la, lo, hi, k2),
        Mst.pick_stops_set(xa, mc, xb, [], lefta, la, lo, hi, hi, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(List<&2, Item>, List.append(&2, Item, xa, []), xa, Shared.List.append_nil(Item, xa)): (
        {
          Look.known(Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(Mst.pick(_, lefta, la, lo, hi, k2), hn, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.look.same_pick(~S, ~fetch, p1, p2, s, xa, lefta, la, lo, lo, Some{k}, hi, ha, hn, k2, x, Mst.lo_le_refl(lo), Mst.hi_le_key(k, hi)(bb), fl)

# a merge of two nodes of one level reads a key below k as a did
def Mst.merge_eq_lo(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +ha: Hashes.Hash,
  +hn: Hashes.Hash,
  +ua: Nat,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eA: {Mst.node(~S, ~fetch, s, ha) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +oA: {Mst.opens(Node{la, lefta, xa}, Room{ua, lo, Some{k}}) == True{}: Bool},
  +eN: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}}: Maybe<&2, Node>
  },
  +oN: {
    Mst.opens(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, Room{u, lo, hi})
      == True{}: Bool
  },
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +c: {Key.cmp(k2, k) == LT{}: Cmp},
  +fb: {Items.fit(xb, Some{k}, hi) == True{}: Bool},
  +nb: {List.is_empty(&2, Item, xb) == False{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(la, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{la, Items.last_key(xa, lo), Some{k}}, Mst.last(xa, lefta), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{la, Items.last_key(xa, lo), Items.head_key(xb, hi)}, mc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ua, lo, Some{k}}, Some{ha}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), u, lo, hi, oN, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ua, lo, Some{k}}, Some{ha}, k2),
        Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p1, s, ha, ua, lo, Some{k}, la, lefta, xa, k2, eA, oA)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{hn}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
          hn,
          la,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          hn,
          u,
          lo,
          hi,
          la,
          Mst.end_left(xa, lefta, mc),
          List.append(&2, Item, Mst.set_last(xa, mc), xb),
          k2,
          eN,
          oN
        )
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(xa, lefta, la, lo, Some{k}, k2), ha, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.merge_eq_lo.passes(
        ~S,
        ~fetch,
        Mst.passes(xa, k2),
        p1,
        p2,
        s,
        ha,
        hn,
        lo,
        k,
        hi,
        la,
        lefta,
        xa,
        mc,
        xb,
        k2,
        x,
        {==},
        bb,
        c,
        fb,
        nb,
        Mst.opens_fl(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), u, lo, hi, p2, oN, fu),
        ih
      )

# a merge of two nodes of one level reads a key above k as b did
def Mst.merge_eq_hi(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +hb: Hashes.Hash,
  +hn: Hashes.Hash,
  +ub: Nat,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eB: {Mst.node(~S, ~fetch, s, hb) == Some{Node{la, leftb, xb}}: Maybe<&2, Node>},
  +oB: {Mst.opens(Node{la, leftb, xb}, Room{ub, Some{k}, hi}) == True{}: Bool},
  +eN: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}}: Maybe<&2, Node>
  },
  +oN: {
    Mst.opens(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, Room{u, lo, hi})
      == True{}: Bool
  },
  +ps: {Mst.passes(xa, k2) == True{}: Bool},
  +ak: {Bound.after(Items.last_key(xa, lo), k) == True{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(la, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{la, Some{k}, Items.head_key(xb, hi)}, leftb, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{la, Items.last_key(xa, lo), Items.head_key(xb, hi)}, mc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ub, Some{k}, hi}, Some{hb}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), u, lo, hi, oN, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ub, Some{k}, hi}, Some{hb}, k2),
        Mst.look.pick(Mst.pick(xb, leftb, la, Some{k}, hi, k2), hb, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p1, s, hb, ub, Some{k}, hi, la, leftb, xb, k2, eB, oB)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{hn}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
          hn,
          la,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          hn,
          u,
          lo,
          hi,
          la,
          Mst.end_left(xa, lefta, mc),
          List.append(&2, Item, Mst.set_last(xa, mc), xb),
          k2,
          eN,
          oN
        )
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(xb, leftb, la, Some{k}, hi, k2), hb, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(xa, mc), xb), Mst.end_left(xa, lefta, mc), la, lo, hi, k2),
        Mst.pick(xb, mc, la, Items.last_key(xa, lo), hi, k2),
        Mst.pick_set_passes(xa, mc, xb, lefta, la, lo, hi, k2, ps)
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(xb, leftb, la, Some{k}, hi, k2), hb, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, la, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.gap_kept.first(
        ~S,
        ~fetch,
        Mst.stops_first(xb, k2),
        p1,
        p2,
        s,
        xb,
        leftb,
        mc,
        la,
        Some{k},
        Items.last_key(xa, lo),
        hi,
        hi,
        hb,
        hn,
        k2,
        x,
        {==},
        Mst.hi_le_refl(hi),
        Mst.opens_fl(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), u, lo, hi, p2, oN, fu),
        ih
      )

# what a merge of two nodes of one level reads, from what the merge of the
# subtrees between them reads (tri)
def Mst.merge_ok.eq.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +elab: {la == lb: Nat},
  +hold: {
    Depots.Depot.holds(
      ~S,
      ~fetch,
      s,
      Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []) <> ns
    )
      == True{}: Bool
  },
  +u: Nat,
  +lva: {Mst.lvl(~S, ~fetch, s, Some{ha}, u) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  tri: Mst.MergeRead(~S, ~fetch, s, la, Items.last_key(xa, lo), k, Items.head_key(xb, hi), Mst.last(xa, lefta), leftb, mc)
) -> Mst.MergeRead(
  ~S,
  ~fetch,
  s,
  u,
  lo,
  k,
  hi,
  Some{ha},
  Some{hb},
  Some{Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []))}
):
  (ilo, r3) = tri
  (ihi, ik) = r3
  +eA = Mst.in_node(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +oA = Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +eB = Mst.in_node(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +oB = Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +lt = Mst.lvl_lt(~S, ~fetch, s, ha, u, la, lefta, xa, lva, eA)
  +fa = Mst.opens_fit(la, lefta, xa, ua, lo, Some{k}, oA)
  +fb = Mst.opens_fit(lb, leftb, xb, ub, Some{k}, hi, oB)
  +nb = Mst.opens_full(lb, leftb, xb, ub, Some{k}, hi, oB)
  +all = Mst.fit_all_lt(xa, lo, k)(fa)
  +ak = Mst.last_below(xa, lo, k)(all)(a)
  +eN = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)},
    Mst.holds_head(
      ~S,
      ~fetch,
      s,
      Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []),
      ns,
      hold
    )
  )
  +oN = Mst.opens_both(la, Mst.end_left(xa, lefta, mc), xa, mc, xb, u, lo, k, hi, lt, Mst.opens_full(la, lefta, xa, ua, lo, Some{k}, oA), fa, fb, ak, bb)
  +eB2 = Equal.trans(
    Maybe<&2, Node>,
    Mst.node(~S, ~fetch, s, hb),
    Some{Node{lb, leftb, xb}},
    Some{Node{la, leftb, xb}},
    eB,
    Equal.cong(Nat, Maybe<&2, Node>, n => Some{Node{n, leftb, xb}}, lb, la, Equal.sym(Nat, la, lb, elab))
  )
  +oB2 = Equal.trans(
    Bool,
    Mst.opens(Node{la, leftb, xb}, Room{ub, Some{k}, hi}),
    Mst.opens(Node{lb, leftb, xb}, Room{ub, Some{k}, hi}),
    True{},
    Equal.cong(Nat, Bool, n => Mst.opens(Node{n, leftb, xb}, Room{ub, Some{k}, hi}), la, lb, elab),
    oB
  )
  (
    +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.merge_eq_lo(
      ~S,
      ~fetch,
      ua,
      g2,
      s,
      ha,
      Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, [])),
      ua,
      u,
      lo,
      k,
      hi,
      la,
      lefta,
      xa,
      mc,
      xb,
      k2,
      x,
      eA,
      oA,
      eN,
      oN,
      bb,
      c,
      fb,
      nb,
      fu,
      +g3 => +g4 => +fl => +e3 => ilo(k2)(x)(la)(g3)(g4)(c)(fl)(e3)
    )(
      Mst.reroom(
        ~S,
        ~fetch,
        g1,
        ua,
        s,
        ha,
        Room{u1, lo, Some{k}},
        Room{ua, lo, Some{k}},
        Node{la, lefta, xa},
        k2,
        x,
        ena,
        Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(Some{k}, Some{k}), Mst.lo_le_refl(lo), Mst.hi_le_refl(Some{k})),
        Shared.Nat.le_refl(ua)
      )(e)
    ),
    (
      +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.merge_eq_hi(
        ~S,
        ~fetch,
        ub,
        g2,
        s,
        hb,
        Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, [])),
        ub,
        u,
        lo,
        k,
        hi,
        la,
        lefta,
        xa,
        mc,
        leftb,
        xb,
        k2,
        x,
        eB2,
        oB2,
        eN,
        oN,
        Mst.passes_of_le(xa, k, k2)(all)(Mst.le_of_lt(Key.cmp(k, k2))(Mst.key_gt_lt(k2, k)(c))),
        ak,
        fu,
        +g3 => +g4 => +fl => +e3 => ihi(k2)(x)(la)(g3)(g4)(c)(fl)(e3)
      )(
        Mst.reroom(
          ~S,
          ~fetch,
          g1,
          ub,
          s,
          hb,
          Room{u1, Some{k}, hi},
          Room{ub, Some{k}, hi},
          Node{lb, leftb, xb},
          k2,
          x,
          enb,
          Shared.Bool.and_both(Mst.lo_le(Some{k}, Some{k}), Mst.hi_le(hi, hi), Mst.lo_le_refl(Some{k}), Mst.hi_le_refl(hi)),
          Shared.Nat.le_refl(ub)
        )(e)
      ),
      +g2 => +fu => Mst.gap_k(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, [])),
        u,
        lo,
        hi,
        la,
        lefta,
        xa,
        xb,
        mc,
        k,
        None{},
        eN,
        oN,
        fu,
        Mst.passes_of_all_lt(xa, k)(all),
        Mst.stops_first_of_fit(xb, k, hi, k)(fb)(nb)(Mst.le_refl_key(k)),
        +g4 => +fl => ik(g4)(fl)
      )
    )
  )

# the roots of a merge of two nodes of one level, and what it reads, from
# those of the merge of the subtrees between them (bi)
def Mst.merge_ok.eq.body(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +mc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +elab: {la == lb: Nat},
  +hold: {
    Depots.Depot.holds(
      ~S,
      ~fetch,
      s,
      Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []) <> ns
    )
      == True{}: Bool
  },
  bi: ({Mst.lvl(~S, ~fetch, s, Mst.last(xa, lefta), la) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, leftb, lb) == True{}: Bool})
    & Mst.MergeMain(~S, ~fetch, s, Items.last_key(xa, lo), k, Items.head_key(xb, hi), Mst.last(xa, lefta), leftb, mc)
) -> ({Mst.lvl(~S, ~fetch, s, Some{ha}, ua) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, Some{hb}, ub) == True{}: Bool})
  & Mst.MergeMain(
    ~S,
    ~fetch,
    s,
    lo,
    k,
    hi,
    Some{ha},
    Some{hb},
    Some{Hashes.Sha.hash(Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []))}
  ):
  (lvs2, main2) = bi
  (lva2, lvb2) = lvs2
  +eA = Mst.in_node(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +oA = Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena)
  +eB = Mst.in_node(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  +oB = Mst.in_open(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}, Node{lb, leftb, xb})(enb)
  (
    (
      Mst.lvl_of(~S, ~fetch, s, ha, ua, la, lefta, xa, eA, Mst.opens_lt(la, lefta, xa, Room{ua, lo, Some{k}})(oA)),
      Mst.lvl_of(~S, ~fetch, s, hb, ub, lb, leftb, xb, eB, Mst.opens_lt(lb, leftb, xb, Room{ub, Some{k}, hi})(oB))
    ),
    +u => +lva => +lvb => +a => +bb => Mst.merge_ok.eq.read(
      ~S,
      ~fetch,
      s,
      ha,
      hb,
      ua,
      lo,
      k,
      ub,
      hi,
      la,
      lefta,
      xa,
      lb,
      leftb,
      xb,
      mc,
      ns,
      ena,
      enb,
      elab,
      hold,
      u,
      lva,
      a,
      bb,
      main2(la)(lva2)(
        Equal.trans(
          Bool,
          Mst.lvl(~S, ~fetch, s, leftb, la),
          Mst.lvl(~S, ~fetch, s, leftb, lb),
          True{},
          Equal.cong(Nat, Bool, n => Mst.lvl(~S, ~fetch, s, leftb, n), la, lb, elab),
          lvb2
        )
      )(Mst.last_below(xa, lo, k)(Mst.fit_all_lt(xa, lo, k)(Mst.opens_fit(la, lefta, xa, ua, lo, Some{k}, oA)))(a))(
        Mst.before_head(xb, k, hi)(Mst.opens_fit(lb, leftb, xb, ub, Some{k}, hi, oB))(bb)
      )
    )
  )

# a merge of two nodes of one level: one node of the items of both, the
# subtrees between them merged
def Mst.merge_ok.eq(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  res: Maybe<&2, Edit>,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == EQ{}: Cmp},
  ih: Mst.MergeOk(~S, ~fetch, s, la, Items.last_key(xa, lo), k, lb, Items.head_key(xb, hi), Mst.last(xa, lefta), leftb, res)
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Mst.with_both(la, lefta, xa, xb, res)):
  match res:
    case None{}:
      Unit{}
    case Some{Edit{+mc, +ns}}:
      %Equal.sym(
        Edit,
        Mst.make(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), ns),
        Mst.store(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, ns),
        Mst.make_full(la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb), ns)(
          Equal.trans(
            Bool,
            List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(xa, mc), xb)),
            List.is_empty(&2, Item, List.append(&2, Item, xa, xb)),
            False{},
            Mst.empty_set_last_append(xa, mc, xb),
            Mst.empty_append(xa, xb)(
              Mst.opens_full(la, lefta, xa, ua, lo, Some{k}, Mst.in_open(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}, Node{la, lefta, xa})(ena))
            )
          )
        )
      ): Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, Some{ha}, Some{hb}, Some{_})
      +hold => Mst.merge_ok.eq.body(
        ~S,
        ~fetch,
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        mc,
        ns,
        ena,
        enb,
        Mst.nat_eq(la, lb)(ec),
        hold,
        ih(
          Mst.holds_tail(
            ~S,
            ~fetch,
            s,
            Node.code(Node{la, Mst.end_left(xa, lefta, mc), List.append(&2, Item, Mst.set_last(xa, mc), xb)}, []),
            ns,
            hold
          )
        )
      )

# the merge of two nodes, by how their levels compare (c)
def Mst.merge_ok.nodes(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +p: Nat,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +la: Nat,
  +lefta: Maybe<&2, Hashes.Hash>,
  +xa: List<&2, Item>,
  +lb: Nat,
  +leftb: Maybe<&2, Hashes.Hash>,
  +xb: List<&2, Item>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == Some{Node{la, lefta, xa}}: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == Some{Node{lb, leftb, xb}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(la, lb) == c: Cmp},
  ih: @ua2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @ub2: Nat -> @hi2: Maybe<&2, List<&2, U32>> -> @ma2: Maybe<&2, Hashes.Hash> -> @mb2: Maybe<
    &2,
    Hashes.Hash> -> Mst.MergeOk(
    ~S,
    ~fetch,
    s,
    ua2,
    lo2,
    k,
    ub2,
    hi2,
    ma2,
    mb2,
    Mst.merge(~S, ~fetch, p, s, Room{ua2, lo2, Some{k}}, Room{ub2, Some{k}, hi2}, ma2, mb2)
  )
) -> Mst.MergeOk(
  ~S,
  ~fetch,
  s,
  ua,
  lo,
  k,
  ub,
  hi,
  Some{ha},
  Some{hb},
  Mst.merge.nodes(
    c,
    ha,
    Room{ua, lo, Some{k}},
    la,
    lefta,
    xa,
    hb,
    Room{ub, Some{k}, hi},
    lb,
    leftb,
    xb,
    r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y)
  )
):
  match c:
    case GT{}:
      Mst.merge_ok.gt(
        ~S,
        ~fetch,
        Mst.merge(~S, ~fetch, p, s, Room{la, Items.last_key(xa, lo), Some{k}}, Room{ub, Some{k}, hi}, Mst.last(xa, lefta), Some{hb}),
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        ena,
        enb,
        ec,
        ih(la)(Items.last_key(xa, lo))(ub)(hi)(Mst.last(xa, lefta))(Some{hb})
      )
    case LT{}:
      Mst.merge_ok.lt(
        ~S,
        ~fetch,
        Mst.merge(~S, ~fetch, p, s, Room{ua, lo, Some{k}}, Room{lb, Some{k}, Items.head_key(xb, hi)}, Some{ha}, leftb),
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        ena,
        enb,
        ec,
        ih(ua)(lo)(lb)(Items.head_key(xb, hi))(Some{ha})(leftb)
      )
    case EQ{}:
      Mst.merge_ok.eq(
        ~S,
        ~fetch,
        Mst.merge(
          ~S,
          ~fetch,
          p,
          s,
          Room{la, Items.last_key(xa, lo), Some{k}},
          Room{lb, Some{k}, Items.head_key(xb, hi)},
          Mst.last(xa, lefta),
          leftb
        ),
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        ena,
        enb,
        ec,
        ih(la)(Items.last_key(xa, lo))(lb)(Items.head_key(xb, hi))(Mst.last(xa, lefta))(leftb)
      )

# the merge of the nodes na and nb that a depot gives
def Mst.merge_ok.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  nb: Maybe<&2, Node>,
  +p: Nat,
  +s: S,
  +ha: Hashes.Hash,
  +hb: Hashes.Hash,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>,
  +ena: {Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}) == na: Maybe<&2, Node>},
  +enb: {Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}) == nb: Maybe<&2, Node>},
  ih: @ua2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @ub2: Nat -> @hi2: Maybe<&2, List<&2, U32>> -> @ma2: Maybe<&2, Hashes.Hash> -> @mb2: Maybe<
    &2,
    Hashes.Hash> -> Mst.MergeOk(
    ~S,
    ~fetch,
    s,
    ua2,
    lo2,
    k,
    ub2,
    hi2,
    ma2,
    mb2,
    Mst.merge(~S, ~fetch, p, s, Room{ua2, lo2, Some{k}}, Room{ub2, Some{k}, hi2}, ma2, mb2)
  )
) -> Mst.MergeOk(
  ~S,
  ~fetch,
  s,
  ua,
  lo,
  k,
  ub,
  hi,
  Some{ha},
  Some{hb},
  Mst.merge.at(na, nb, ha, Room{ua, lo, Some{k}}, hb, Room{ub, Some{k}, hi}, r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y))
):
  match na nb:
    case Some{Node{+la, +lefta, +xa}} Some{Node{+lb, +leftb, +xb}}:
      Mst.merge_ok.nodes(
        ~S,
        ~fetch,
        Nat.cmp(la, lb),
        p,
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        la,
        lefta,
        xa,
        lb,
        leftb,
        xb,
        ena,
        enb,
        {==},
        ih
      )
    case Some{Node{+la, +lefta, +xa}} None{}:
      Unit{}
    case None{} y:
      Unit{}

# a merge of two trees around the key k, each in its room, reads as
# Mst.MergeOk says
def Mst.merge_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  ma: Maybe<&2, Hashes.Hash>,
  mb: Maybe<&2, Hashes.Hash>,
  +s: S,
  +ua: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ub: Nat,
  +hi: Maybe<&2, List<&2, U32>>
) -> Mst.MergeOk(~S, ~fetch, s, ua, lo, k, ub, hi, ma, mb, Mst.merge(~S, ~fetch, f, s, Room{ua, lo, Some{k}}, Room{ub, Some{k}, hi}, ma, mb)):
  match f ma mb:
    case 0n None{} None{}:
      Mst.merge_ok.none(~S, ~fetch, s, ua, lo, k, ub, hi)
    case 1n+p None{} None{}:
      Mst.merge_ok.none(~S, ~fetch, s, ua, lo, k, ub, hi)
    case 0n None{} Some{+hb}:
      Mst.merge_ok.lone_b(
        ~S,
        ~fetch,
        Mst.edge(~S, ~fetch, Mst.depth(), s, True{}, Room{ub, Some{k}, hi}, Some{hb}),
        s,
        ua,
        lo,
        k,
        ub,
        hi,
        hb,
        {==}
      )
    case 1n+p None{} Some{+hb}:
      Mst.merge_ok.lone_b(
        ~S,
        ~fetch,
        Mst.edge(~S, ~fetch, Mst.depth(), s, True{}, Room{ub, Some{k}, hi}, Some{hb}),
        s,
        ua,
        lo,
        k,
        ub,
        hi,
        hb,
        {==}
      )
    case 0n Some{+ha} None{}:
      Mst.merge_ok.lone_a(
        ~S,
        ~fetch,
        Mst.edge(~S, ~fetch, Mst.depth(), s, False{}, Room{ua, lo, Some{k}}, Some{ha}),
        s,
        ua,
        lo,
        k,
        ub,
        hi,
        ha,
        {==}
      )
    case 1n+p Some{+ha} None{}:
      Mst.merge_ok.lone_a(
        ~S,
        ~fetch,
        Mst.edge(~S, ~fetch, Mst.depth(), s, False{}, Room{ua, lo, Some{k}}, Some{ha}),
        s,
        ua,
        lo,
        k,
        ub,
        hi,
        ha,
        {==}
      )
    case 0n Some{ha} Some{hb}:
      Unit{}
    case 1n+(+p) Some{+ha} Some{+hb}:
      Mst.merge_ok.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, ha, Room{ua, lo, Some{k}}),
        Mst.node.in(~S, ~fetch, s, hb, Room{ub, Some{k}, hi}),
        p,
        s,
        ha,
        hb,
        ua,
        lo,
        k,
        ub,
        hi,
        {==},
        {==},
        +ua2 => +lo2 => +ub2 => +hi2 => +ma2 => +mb2 => Mst.merge_ok(~S, ~fetch, p, ma2, mb2, s, ua2, lo2, k, ub2, hi2)
      )

# a root below the level u is below a level at or above u
def Mst.lvl.at_mono(mn: Maybe<&2, Node>, +u: Nat, +u2: Nat) -> {Mst.lvl.at(mn, u) == True{}: Bool} -> {Nat.is_le(u, u2) == True{}: Bool} -> {
  Mst.lvl.at(mn, u2) == True{}: Bool
}:
  match mn:
    case None{}:
      +e => +w => {==}
    case Some{Node{+l, +left, +xs}}:
      +e => +w => Shared.Nat.lt_le(l, u, u2)(e)(w)

# Mst.lvl.at_mono, of the root of a tree
def Mst.lvl_mono(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +u: Nat,
  +u2: Nat
) -> {Mst.lvl(~S, ~fetch, s, m, u) == True{}: Bool} -> {Nat.is_le(u, u2) == True{}: Bool} -> {Mst.lvl(~S, ~fetch, s, m, u2) == True{}: Bool}:
  match m:
    case None{}:
      +e => +w => {==}
    case Some{+h}:
      Mst.lvl.at_mono(Mst.node(~S, ~fetch, s, h), u, u2)

# the new nodes of a node made from items, in front of acc, hold acc
def Mst.make_acc(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +acc: List<&2, List<&2, U32>>
) -> {Depots.Depot.holds(~S, ~fetch, s, Edit.nodes(Mst.make(l, left, xs, acc))) == True{}: Bool} -> {
  Depots.Depot.holds(~S, ~fetch, s, acc) == True{}: Bool
}:
  match xs:
    case Nil{}:
      +e => e
    case Con{+x, +rest}:
      +e => Mst.holds_tail(~S, ~fetch, s, Node.code(Node{l, left, x <> rest}, []), acc, e)

# a pick of a key at or before k among items after k stops at once
def Mst.stops_first_fit(
  +post: List<&2, Item>,
  +k: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>
) -> {Items.fit(post, Some{k}, hi) == True{}: Bool} -> {Cmp.is_le(Key.cmp(k2, k)) == True{}: Bool} -> {
  Mst.stops_first(post, k2) == True{}: Bool
}:
  match post:
    case Nil{}:
      +f => +c => {==}
    case Con{+y, +rest}:
      +f => +c => Mst.stops_first_of_fit(y <> rest, k, hi, k2)(f)({==})(c)

# a comparison neither LT nor EQ is GT
def Mst.gt_of(c: Cmp) -> {Cmp.is_lt(c) == False{}: Bool} -> {Cmp.is_eq(c) == False{}: Bool} -> {c == GT{}: Cmp}:
  match c:
    case LT{}:
      +a => +b => Empty.absurd({LT{} == GT{}: Cmp}, Shared.Bool.true_ne_false(a))
    case EQ{}:
      +a => +b => Empty.absurd({EQ{} == GT{}: Cmp}, Shared.Bool.true_ne_false(b))
    case GT{}:
      +a => +b => {==}

# the items from k on, when the first is not k, fit after k
def Mst.post_after(
  +post: List<&2, Item>,
  -b: List<&2, Item>,
  -g: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Mst.head_not_lt(post, k) == True{}: Bool} -> {Part.hits(Part{b, g, post}, k) == False{}: Bool} -> {
  Items.fit(post, lo, hi) == True{}: Bool
} -> {Items.fit(post, Some{k}, hi) == True{}: Bool}:
  match post:
    case Nil{}:
      +hn => +hh => +f => {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      +hn => +hh => +f => Shared.Bool.and_both(
        Bool.and(Key.is_lt(k, ik), Bound.before(ik, hi)),
        Items.fit(rest, Some{ik}, hi),
        Shared.Bool.and_both(
          Key.is_lt(k, ik),
          Bound.before(ik, hi),
          Mst.key_is_lt(k, ik)(
            Mst.key_gt_lt(ik, k)(Mst.gt_of(Key.cmp(ik, k))(Shared.Bool.not_true(Cmp.is_lt(Key.cmp(ik, k)))(hn))(hh))
          ),
          Shared.Bool.and_true_right(
            Bound.after(lo, ik),
            Bound.before(ik, hi),
            Shared.Bool.and_true_left(Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)), Items.fit(rest, Some{ik}, hi), f)
          )
        ),
        Shared.Bool.and_true_right(Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)), Items.fit(rest, Some{ik}, hi), f)
      )

# a read of a node whose pick goes down to m in r tells what a read of m in
# r tells, with less fuel (cont)
def Mst.old_down(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -G: Type,
  g1: Nat,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +m: Maybe<&2, Hashes.Hash>,
  +r: Room,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +ep: {Mst.pick(xs, left, l, lo, hi, k2) == Pick.Down{m, r}: Pick},
  cont: @g3: Nat -> {Look.known(Mst.look.go(~S, ~fetch, g3, s, r, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> G
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> G:
  match g1:
    case 0n:
      +e => Empty.absurd(G, Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e))
    case 1n+(+p):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p, s, Room{u, lo, hi}, Some{h}, k2),
        Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p, s, h, u, lo, hi, l, left, xs, k2, eN, oN)
      ): ({Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> G)
      %Equal.sym(Pick, Mst.pick(xs, left, l, lo, hi, k2), Pick.Down{m, r}, ep): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> G
      )
      cont(p)

# a read of a new node whose pick goes down to m in a room of its level tells
# what ih says a read of m there tells
def Mst.new_down(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +m: Maybe<&2, Hashes.Hash>,
  +a: Maybe<&2, List<&2, U32>>,
  +b: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  +ep: {Mst.pick(xs, left, l, lo, hi, k2) == Pick.Down{m, Room{l, a, b}}: Pick},
  ih: @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, a, b}, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g2:
    case 0n:
      Empty.absurd(
        {Look.known(Look.Missing{h}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, left, xs, u, lo, hi, oN, fu)
      )
    case 1n+(+p):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p, s, Room{u, lo, hi}, Some{h}, k2),
        Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p, s, h, u, lo, hi, l, left, xs, k2, eN, oN)
      ): {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      %Equal.sym(Pick, Mst.pick(xs, left, l, lo, hi, k2), Pick.Down{m, Room{l, a, b}}, ep): {
        Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k2)))
          == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      ih(p)(Mst.opens_fl(l, left, xs, u, lo, hi, p, oN, fu))

# a node of the level l with items opens in a room above its level whose
# bounds the items fit
def Mst.opens_of(
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +lt: {Nat.is_lt(l, u) == True{}: Bool},
  +ne: {List.is_empty(&2, Item, xs) == False{}: Bool},
  +f: {Items.fit(xs, lo, hi) == True{}: Bool}
) -> {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool}:
  %Equal.sym(Bool, List.is_empty(&2, Item, xs), False{}, ne) :
    {Bool.and(Bool.and(Cmp.is_lt(Nat.cmp(l, u)), Bool.not(_)), Items.fit(xs, lo, hi)) == True{} : Bool}
  %Equal.sym(Bool, Cmp.is_lt(Nat.cmp(l, u)), True{}, lt) :
    {Bool.and(Bool.and(_, True{}), Items.fit(xs, lo, hi)) == True{} : Bool}
  f

# the items before k of items that fit, then nothing, fit before k
def Mst.pre_fit(
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> {Items.fit(List.append(&2, Item, pre, post), lo, hi) == True{}: Bool} -> {Mst.all_lt(pre, k) == True{}: Bool} -> {
  Items.fit(List.append(&2, Item, pre, []), lo, Some{k}) == True{}: Bool
}:
  +f => +a => Mst.with_nil(
    ys => {Items.fit(ys, lo, Some{k}) == True{}: Bool},
    pre,
    Mst.fit_below(pre, lo, hi, k)(
      Shared.Bool.and_true_left(
        Items.fit(pre, lo, hi),
        Items.fit(post, Items.last_key(pre, lo), hi),
        Equal.trans(
          Bool,
          Bool.and(Items.fit(pre, lo, hi), Items.fit(post, Items.last_key(pre, lo), hi)),
          Items.fit(List.append(&2, Item, pre, post), lo, hi),
          True{},
          Equal.sym(
            Bool,
            Items.fit(List.append(&2, Item, pre, post), lo, hi),
            Bool.and(Items.fit(pre, lo, hi), Items.fit(post, Items.last_key(pre, lo), hi)),
            Mst.fit_append(pre, post, lo, hi)
          ),
          f
        )
      )
    )(a)
  )

# the items from k on of items that fit fit after the last before k
def Mst.post_fit(
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Items.fit(List.append(&2, Item, pre, post), lo, hi) == True{}: Bool} -> {
  Items.fit(post, Items.last_key(pre, lo), hi) == True{}: Bool
}:
  match pre:
    case Nil{}:
      x => x
    case Con{head, tail}:
      match head:
        case Item{key, value, right}:
          x => Mst.post_fit(tail, post, Some{key}, hi)(Shared.Bool.and_true_right(Bool.and(Bound.after(lo, key), Bound.before(key, hi)), Items.fit(List.append(&2, Item, tail, post), Some{key}, hi))(x))

# what a split reads: below k, the lower half as the tree; above k, the upper
# half as the tree; each half in a room above its root
def Mst.SplitRead(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -m: Maybe<&2, Hashes.Hash>,
  -hl: Maybe<&2, Hashes.Hash>,
  -hh: Maybe<&2, Hashes.Hash>
) -> Type:
  (
    @u2: Nat -> {Mst.lvl(~S, ~fetch, s, m, u2) == True{}: Bool} -> @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {
      Key.cmp(k2, k) == LT{}: Cmp
    } -> {Nat.is_le(u2, g2) == True{}: Bool} -> {
      Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, lo, hi}, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, lo, Some{k}}, hl, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
  )
    & (
      @u2: Nat -> {Mst.lvl(~S, ~fetch, s, m, u2) == True{}: Bool} -> @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {
        Key.cmp(k2, k) == GT{}: Cmp
      } -> {Nat.is_le(u2, g2) == True{}: Bool} -> {
        Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, lo, hi}, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, Some{k}, hi}, hh, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    )

# a split res of the tree m, in the room of the up ur between lo and hi, at
# k: once the depot holds its new nodes, the root sits in its room, and it
# reads as Mst.SplitRead says
def Mst.SplitOk(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -ur: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -m: Maybe<&2, Hashes.Hash>,
  res: Maybe<&2, Halves>
) -> Type:
  match res:
    case None{}:
      Unit
    case Some{Halves{hl, hh, ns}}:
      {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool} -> (
        {Mst.lvl(~S, ~fetch, s, m, ur) == True{}: Bool} & Mst.SplitRead(~S, ~fetch, s, lo, hi, k, m, hl, hh)
      )

# Mst.gap_lo, by whether a pick passes the items before the gap (b)
def Mst.gap_lo.passes(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +p1: Nat,
  +p2: Nat,
  +s: S,
  -h: Hashes.Hash,
  -hn: Hashes.Hash,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +post2: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eb: {Mst.passes(pre, k2) == b: Bool},
  +sf: {Mst.stops_first(post, k2) == True{}: Bool},
  +sf2: {Mst.stops_first(post2, k2) == True{}: Bool},
  +fl: {Nat.is_le(l, p2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo), Items.head_key(post2, hi2)}, clo, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {
  Look.known(
    Mst.look.pick(Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2))
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Look.known(
    Mst.look.pick(
      Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
      hn,
      l,
      k2,
      m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
    )
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match b:
    case True{}:
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
        Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
        Mst.pick_passes(pre, post, left, l, lo, hi, k2)(eb)
      ): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
                hn,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
        Pick.Down{Mst.last(pre, left), Room.of(l, Items.last_key(pre, lo), Items.head_key(post, hi))},
        Mst.pick_first(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2)(sf)
      ): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
                hn,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
        Pick.Down{clo, Room.of(l, Items.last_key(pre, lo), Items.head_key(post2, hi2))},
        Equal.trans(
          Pick,
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
          Mst.pick(post2, clo, l, Items.last_key(pre, lo), hi2, k2),
          Pick.Down{clo, Room.of(l, Items.last_key(pre, lo), Items.head_key(post2, hi2))},
          Mst.pick_set_passes(pre, clo, post2, left, l, lo, hi2, k2, eb),
          Mst.pick_first(post2, clo, l, Items.last_key(pre, lo), hi2, k2)(sf2)
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Pick.Down{Mst.last(pre, left), Room.of(l, Items.last_key(pre, lo), Items.head_key(post, hi))},
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      ih(p1)(p2)(fl)
    case False{}:
      %Equal.sym(Maybe<&2, Hashes.Hash>, Mst.end_left(pre, left, clo), left, Mst.end_left_full(pre, left, clo, k2)(eb)): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), _, l, lo, hi2, k2),
                hn,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), left, l, lo, hi2, k2),
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
        Mst.pick_stops_set(pre, clo, post2, post, left, l, lo, hi2, hi, k2)(eb)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.look.same_pick(
        ~S,
        ~fetch,
        p1,
        p2,
        s,
        List.append(&2, Item, pre, post),
        left,
        l,
        lo,
        lo,
        hi,
        hi,
        h,
        hn,
        k2,
        x,
        Mst.lo_le_refl(lo),
        Mst.hi_le_refl(hi),
        fl
      )

# a node whose gap is replaced by the subtree clo, then the items post2,
# reads a key that a pick of passes the items before the gap and stops at
# the first item after it, as the node did, but in the gap, as ih says
def Mst.gap_lo(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +u2: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +post2: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +hi2: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +eL: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), post2)}}: Maybe<&2, Node>
  },
  +oL: {
    Mst.opens(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), post2)}, Room{u2, lo, hi2})
      == True{}: Bool
  },
  +sf: {Mst.stops_first(post, k2) == True{}: Bool},
  +sf2: {Mst.stops_first(post2, k2) == True{}: Bool},
  +fu: {Nat.is_le(u2, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo), Items.head_key(post2, hi2)}, clo, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, lo, hi2}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u2, lo, hi2}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), post2), u2, lo, hi2, oL, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ur, lo, hi}, Some{h}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
          h,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
        ),
        Mst.look_node(~S, ~fetch, p1, s, h, ur, lo, hi, l, left, List.append(&2, Item, pre, post), k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, lo, hi2}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, lo, hi2}, Some{hn}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), post2), Mst.end_left(pre, left, clo), l, lo, hi2, k2),
          hn,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          hn,
          u2,
          lo,
          hi2,
          l,
          Mst.end_left(pre, left, clo),
          List.append(&2, Item, Mst.set_last(pre, clo), post2),
          k2,
          eL,
          oL
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      Mst.gap_lo.passes(
        ~S,
        ~fetch,
        Mst.passes(pre, k2),
        p1,
        p2,
        s,
        h,
        hn,
        lo,
        hi,
        k,
        l,
        left,
        pre,
        post,
        post2,
        clo,
        hi2,
        k2,
        x,
        {==},
        sf,
        sf2,
        Mst.opens_fl(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), post2), u2, lo, hi2, p2, oL, fu),
        ih
      )

# the upper half of a split node, of the items after k, reads a key above k
# as the node did
def Mst.split_hi_full(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +u2: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +chi: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +eH: {Mst.node(~S, ~fetch, s, hn) == Some{Node{l, chi, post}}: Maybe<&2, Node>},
  +oH: {Mst.opens(Node{l, chi, post}, Room{u2, Some{k}, hi}) == True{}: Bool},
  +ps: {Mst.passes(pre, k2) == True{}: Bool},
  +fu: {Nat.is_le(u2, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Some{k}, Items.head_key(post, hi)}, chi, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, Some{k}, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u2, Some{k}, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, chi, post, u2, Some{k}, hi, oH, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ur, lo, hi}, Some{h}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
          h,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
        ),
        Mst.look_node(~S, ~fetch, p1, s, h, ur, lo, hi, l, left, List.append(&2, Item, pre, post), k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, Some{k}, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u2, Some{k}, hi}, Some{hn}, k2),
        Mst.look.pick(Mst.pick(post, chi, l, Some{k}, hi, k2), hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p2, s, hn, u2, Some{k}, hi, l, chi, post, k2, eH, oH)
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
        Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
        Mst.pick_passes(pre, post, left, l, lo, hi, k2)(ps)
      ): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(Mst.pick(post, chi, l, Some{k}, hi, k2), hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.gap_kept.first(
        ~S,
        ~fetch,
        Mst.stops_first(post, k2),
        p1,
        p2,
        s,
        post,
        Mst.last(pre, left),
        chi,
        l,
        Items.last_key(pre, lo),
        Some{k},
        hi,
        hi,
        h,
        hn,
        k2,
        x,
        {==},
        Mst.hi_le_refl(hi),
        Mst.opens_fl(l, chi, post, u2, Some{k}, hi, p2, oH, fu),
        ih
      )


# the halves of a split node of the items pre, then post, once its gap is
# split into clo and chi (bi: what that split reads)
def Mst.split_ok.halves(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  pre: List<&2, Item>,
  post: List<&2, Item>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +clo: Maybe<&2, Hashes.Hash>,
  +chi: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  bi: {Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool}
    & Mst.SplitRead(~S, ~fetch, s, Items.last_key(pre, lo), Items.head_key(post, hi), k, Mst.last(pre, left), clo, chi)
) -> {
  Depots.Depot.holds(
    ~S,
    ~fetch,
    s,
    Edit.nodes(
      Mst.make(
        l,
        chi,
        post,
        Edit.nodes(Mst.make(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), []), ns))
      )
    )
  )
    == True{}: Bool
} -> {Mst.lvl(~S, ~fetch, s, Some{h}, ur) == True{}: Bool}
  & Mst.SplitRead(
    ~S,
    ~fetch,
    s,
    lo,
    hi,
    k,
    Some{h},
    Edit.root(Mst.make(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), []), ns)),
    Edit.root(
      Mst.make(
        l,
        chi,
        post,
        Edit.nodes(Mst.make(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), []), ns))
      )
    )
  ):
  match pre post:
    case Nil{} Nil{}:
      Empty.absurd(
        {
          Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool
        } -> {Mst.lvl(~S, ~fetch, s, Some{h}, ur) == True{}: Bool} & Mst.SplitRead(~S, ~fetch, s, lo, hi, k, Some{h}, clo, chi),
        Shared.Bool.true_ne_false(Mst.opens_full(l, left, [], ur, lo, hi, oN))
      )
    case Nil{} Con{+y, +ys}:
      (+lvg, sr) = bi
      (srlo, srhi) = sr
      +hold => (
        Mst.lvl_of(~S, ~fetch, s, h, ur, l, left, y <> ys, eN, Mst.opens_lt(l, left, y <> ys, Room{ur, lo, hi})(oN)),
        (
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.old_down(
            ~S,
            ~fetch,
            {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, lo, Some{k}}, clo, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
            ur,
            s,
            h,
            ur,
            lo,
            hi,
            l,
            left,
            y <> ys,
            k2,
            x,
            left,
            Room.of(l, lo, Items.head_key(y <> ys, hi)),
            eN,
            oN,
            Mst.pick_first(y <> ys, left, l, lo, hi, k2)(Mst.stops_first_fit(y <> ys, k, hi, k2)(pk)(Mst.le_of_lt(Key.cmp(k2, k))(c))),
            +g3 => +e3 => srlo(u2)(
              Mst.lvl_mono(~S, ~fetch, s, left, l, u2)(lvg)(
                Shared.Nat.lt_weak(l, u2)(Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, y <> ys, lvm, eN))
              )
            )(k2)(x)(l)(g3)(g2)(c)(fu)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, y <> ys},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, y <> ys})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          ),
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.split_hi_full(
            ~S,
            ~fetch,
            ur,
            g2,
            s,
            h,
            Hashes.Sha.hash(Node.code(Node{l, chi, y <> ys}, [])),
            ur,
            u2,
            lo,
            hi,
            k,
            l,
            left,
            [],
            y <> ys,
            chi,
            k2,
            x,
            eN,
            oN,
            Mst.node_code(~S, ~fetch, s, Node{l, chi, y <> ys}, Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, chi, y <> ys}, []), ns, hold)),
            Mst.opens_of(l, chi, y <> ys, u2, Some{k}, hi, Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, y <> ys, lvm, eN), {==}, pk),
            {==},
            fu,
            +g3 => +g4 => +fl => +e3 => srhi(l)(lvg)(k2)(x)(l)(g3)(g4)(c)(fl)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, y <> ys},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, y <> ys})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          )
        )
      )
    case Con{+x0, +r0} Nil{}:
      (+lvg, sr) = bi
      (srlo, srhi) = sr
      %Equal.sym(
        Edit,
        Mst.make(l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), []), ns),
        Mst.store(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, ns),
        Mst.make_full(l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), []), ns)(
          Equal.trans(
            Bool,
            List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])),
            List.is_empty(&2, Item, List.append(&2, Item, x0 <> r0, [])),
            False{},
            Mst.empty_set_last_append(x0 <> r0, clo, []),
            {==}
          )
        )
      ): (
        {Depots.Depot.holds(~S, ~fetch, s, Edit.nodes(Mst.make(l, chi, [], Edit.nodes(_)))) == True{}: Bool}
          -> {Mst.lvl(~S, ~fetch, s, Some{h}, ur) == True{}: Bool}
          & Mst.SplitRead(~S, ~fetch, s, lo, hi, k, Some{h}, Edit.root(_), Edit.root(Mst.make(l, chi, [], Edit.nodes(_))))
      )
      +hold => (
        Mst.lvl_of(~S, ~fetch, s, h, ur, l, left, List.append(&2, Item, x0 <> r0, []), eN, Mst.opens_lt(l, left, List.append(&2, Item, x0 <> r0, []), Room{ur, lo, hi})(oN)),
        (
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_lo(
            ~S,
            ~fetch,
            ur,
            g2,
            s,
            h,
            Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, [])),
            ur,
            u2,
            lo,
            hi,
            k,
            l,
            left,
            x0 <> r0,
            [],
            [],
            clo,
            Some{k},
            k2,
            x,
            eN,
            oN,
            Mst.node_code(~S, ~fetch, s, Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, []), ns, hold)),
            Mst.opens_set_last(l, left, Mst.end_left(x0 <> r0, left, clo), x0 <> r0, clo, [], Room{u2, lo, Some{k}})(
              Mst.opens_of(
                l,
                left,
                List.append(&2, Item, x0 <> r0, []),
                u2,
                lo,
                Some{k},
                Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, List.append(&2, Item, x0 <> r0, []), lvm, eN),
                {==},
                Mst.pre_fit(x0 <> r0, [], lo, hi, k)(Mst.opens_fit(l, left, List.append(&2, Item, x0 <> r0, []), ur, lo, hi, oN))(all)
              )
            ),
            {==},
            {==},
            fu,
            +g3 => +g4 => +fl => +e3 => srlo(l)(lvg)(k2)(x)(l)(g3)(g4)(c)(fl)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, List.append(&2, Item, x0 <> r0, [])},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, List.append(&2, Item, x0 <> r0, [])})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          ),
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.old_down(
            ~S,
            ~fetch,
            {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u2, Some{k}, hi}, chi, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
            ur,
            s,
            h,
            ur,
            lo,
            hi,
            l,
            left,
            List.append(&2, Item, x0 <> r0, []),
            k2,
            x,
            Mst.last(x0 <> r0, left),
            Room.of(l, Items.last_key(x0 <> r0, lo), hi),
            eN,
            oN,
            Mst.pick_passes(x0 <> r0, [], left, l, lo, hi, k2)(Mst.passes_of_lt(x0 <> r0, k, k2)(all)(Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k, k2), LT{}, Mst.key_gt_lt(k2, k)(c)))),
            +g3 => +e3 => srhi(u2)(Mst.lvl_mono(~S, ~fetch, s, Mst.last(x0 <> r0, left), l, u2)(lvg)(Shared.Nat.lt_weak(l, u2)(Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, List.append(&2, Item, x0 <> r0, []), lvm, eN))))(k2)(x)(l)(g3)(g2)(c)(fu)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, List.append(&2, Item, x0 <> r0, [])},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, List.append(&2, Item, x0 <> r0, [])})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          )
        )
      )
    case Con{+x0, +r0} Con{+y, +ys}:
      (+lvg, sr) = bi
      (srlo, srhi) = sr
      %Equal.sym(
        Edit,
        Mst.make(l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), []), ns),
        Mst.store(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, ns),
        Mst.make_full(l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), []), ns)(
          Equal.trans(
            Bool,
            List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])),
            List.is_empty(&2, Item, List.append(&2, Item, x0 <> r0, [])),
            False{},
            Mst.empty_set_last_append(x0 <> r0, clo, []),
            {==}
          )
        )
      ): (
        {Depots.Depot.holds(~S, ~fetch, s, Edit.nodes(Mst.make(l, chi, y <> ys, Edit.nodes(_)))) == True{}: Bool}
          -> {Mst.lvl(~S, ~fetch, s, Some{h}, ur) == True{}: Bool}
          & Mst.SplitRead(~S, ~fetch, s, lo, hi, k, Some{h}, Edit.root(_), Edit.root(Mst.make(l, chi, y <> ys, Edit.nodes(_))))
      )
      +hold => (
        Mst.lvl_of(~S, ~fetch, s, h, ur, l, left, List.append(&2, Item, x0 <> r0, y <> ys), eN, Mst.opens_lt(l, left, List.append(&2, Item, x0 <> r0, y <> ys), Room{ur, lo, hi})(oN)),
        (
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.gap_lo(
            ~S,
            ~fetch,
            ur,
            g2,
            s,
            h,
            Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, [])),
            ur,
            u2,
            lo,
            hi,
            k,
            l,
            left,
            x0 <> r0,
            y <> ys,
            [],
            clo,
            Some{k},
            k2,
            x,
            eN,
            oN,
            Mst.node_code(~S, ~fetch, s, Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, []), ns, Mst.holds_tail(~S, ~fetch, s, Node.code(Node{l, chi, y <> ys}, []), Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, []) <> ns, hold))),
            Mst.opens_set_last(l, left, Mst.end_left(x0 <> r0, left, clo), x0 <> r0, clo, [], Room{u2, lo, Some{k}})(
              Mst.opens_of(
                l,
                left,
                List.append(&2, Item, x0 <> r0, []),
                u2,
                lo,
                Some{k},
                Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, List.append(&2, Item, x0 <> r0, y <> ys), lvm, eN),
                {==},
                Mst.pre_fit(x0 <> r0, y <> ys, lo, hi, k)(Mst.opens_fit(l, left, List.append(&2, Item, x0 <> r0, y <> ys), ur, lo, hi, oN))(all)
              )
            ),
            Mst.stops_first_fit(y <> ys, k, hi, k2)(pk)(Mst.le_of_lt(Key.cmp(k2, k))(c)),
            {==},
            fu,
            +g3 => +g4 => +fl => +e3 => srlo(l)(lvg)(k2)(x)(l)(g3)(g4)(c)(fl)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, List.append(&2, Item, x0 <> r0, y <> ys)},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, List.append(&2, Item, x0 <> r0, y <> ys)})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          ),
          +u2 => +lvm => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => +e => Mst.split_hi_full(
            ~S,
            ~fetch,
            ur,
            g2,
            s,
            h,
            Hashes.Sha.hash(Node.code(Node{l, chi, y <> ys}, [])),
            ur,
            u2,
            lo,
            hi,
            k,
            l,
            left,
            x0 <> r0,
            y <> ys,
            chi,
            k2,
            x,
            eN,
            oN,
            Mst.node_code(~S, ~fetch, s, Node{l, chi, y <> ys}, Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, chi, y <> ys}, []), Node.code(Node{l, Mst.end_left(x0 <> r0, left, clo), List.append(&2, Item, Mst.set_last(x0 <> r0, clo), [])}, []) <> ns, hold)),
            Mst.opens_of(l, chi, y <> ys, u2, Some{k}, hi, Mst.lvl_lt(~S, ~fetch, s, h, u2, l, left, List.append(&2, Item, x0 <> r0, y <> ys), lvm, eN), {==}, pk),
            Mst.passes_of_lt(x0 <> r0, k, k2)(all)(Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k, k2), LT{}, Mst.key_gt_lt(k2, k)(c))),
            fu,
            +g3 => +g4 => +fl => +e3 => srhi(l)(lvg)(k2)(x)(l)(g3)(g4)(c)(fl)(e3)
          )(
            Mst.reroom(
              ~S,
              ~fetch,
              g1,
              ur,
              s,
              h,
              Room{u1, lo, hi},
              Room{ur, lo, hi},
              Node{l, left, List.append(&2, Item, x0 <> r0, y <> ys)},
              k2,
              x,
              Mst.node_in_of(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, List.append(&2, Item, x0 <> r0, y <> ys)})(eN)(oN),
              Shared.Bool.and_both(Mst.lo_le(lo, lo), Mst.hi_le(hi, hi), Mst.lo_le_refl(lo), Mst.hi_le_refl(hi)),
              Shared.Nat.le_refl(ur)
            )(e)
          )
        )
      )

# the split of a node of the items pre, then post, once its gap is split (ms)
def Mst.split_ok.done(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ms: Maybe<&2, Halves>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  ihs: Mst.SplitOk(~S, ~fetch, s, l, Items.last_key(pre, lo), Items.head_key(post, hi), k, Mst.last(pre, left), ms)
) -> Mst.SplitOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  k,
  Some{h},
  Mst.split.done(l, left, Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, ms)
):
  match ms:
    case None{}:
      Unit{}
    case Some{Halves{+clo, +chi, +ns}}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.left(List.reverse.go(&2, Item, pre, []), left, clo),
        Mst.end_left(pre, left, clo),
        Mst.left_rev(pre, left, clo)
      ): Mst.SplitOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        k,
        Some{h},
        Some{
          Halves{
            Edit.root(Mst.make(l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, []), ns)),
            Edit.root(Mst.make(l, chi, post, Edit.nodes(Mst.make(l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, []), ns)))),
            Edit.nodes(Mst.make(l, chi, post, Edit.nodes(Mst.make(l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, []), ns))))
          }
        }
      )
      %Equal.sym(
        List<&2, Item>,
        Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, []),
        List.append(&2, Item, Mst.set_last(pre, clo), []),
        Mst.rejoin_rev(pre, clo, [])
      ): Mst.SplitOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        k,
        Some{h},
        Some{
          Halves{
            Edit.root(Mst.make(l, Mst.end_left(pre, left, clo), _, ns)),
            Edit.root(Mst.make(l, chi, post, Edit.nodes(Mst.make(l, Mst.end_left(pre, left, clo), _, ns)))),
            Edit.nodes(Mst.make(l, chi, post, Edit.nodes(Mst.make(l, Mst.end_left(pre, left, clo), _, ns))))
          }
        }
      )
      +hold => Mst.split_ok.halves(
        ~S,
        ~fetch,
        pre,
        post,
        s,
        h,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        clo,
        chi,
        ns,
        eN,
        oN,
        all,
        pk,
        ihs(
          Mst.make_acc(~S, ~fetch, s, l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), []), ns)(
            Mst.make_acc(
              ~S,
              ~fetch,
              s,
              l,
              chi,
              post,
              Edit.nodes(Mst.make(l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), []), ns))
            )(hold)
          )
        )
      )(hold)

# the split of a node at k, by whether the node holds k (b0)
def Mst.split_ok.hit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b0: Bool,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(post, k) == True{}: Bool},
  +eb0: {Part.hits(Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, k) == b0: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> Mst.SplitOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    k,
    m2,
    Mst.split(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k)
  )
) -> Mst.SplitOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  k,
  Some{h},
  Shared.Bool.when(
    Maybe<&2, Halves>,
    b0,
    u => None{},
    u => Mst.split.done(
      l,
      left,
      Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
      Mst.split(
        ~S,
        ~fetch,
        p,
        s,
        Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Items.head_key(post, hi)},
        Mst.last(pre, left),
        k
      )
    )
  )
):
  match b0:
    case True{}:
      Unit{}
    case False{}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.SplitOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        k,
        Some{h},
        Mst.split.done(
          l,
          left,
          Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
          Mst.split(~S, ~fetch, p, s, Room{l, _, Items.head_key(post, hi)}, Mst.last(pre, left), k)
        )
      )
      Mst.split_ok.done(
        ~S,
        ~fetch,
        Mst.split(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        pre,
        post,
        eN,
        oN,
        all,
        Mst.post_after(post, List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), k, Items.last_key(pre, lo), hi)(hn)(eb0)(
          Mst.post_fit(pre, post, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, post), ur, lo, hi, oN))
        ),
        ih(l)(Items.last_key(pre, lo))(Items.head_key(post, hi))(Mst.last(pre, left))
      )

# the split of the node na of the hash h
def Mst.split_ok.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}) == na: Maybe<&2, Node>},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> Mst.SplitOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    k,
    m2,
    Mst.split(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k)
  )
) -> Mst.SplitOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  k,
  Some{h},
  Mst.split.at(na, Room{ur, lo, hi}, k, r2 => c => Mst.split(~S, ~fetch, p, s, r2, c, k))
):
  match na:
    case None{}:
      Unit{}
    case Some{Node{+l, +left, +xs}}:
      %Equal.sym(
        Part,
        Mst.part(xs, left, k, []),
        Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
        Mst.part_eq(xs, left, k, [])
      ): Mst.SplitOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        k,
        Some{h},
        Shared.Bool.when(
          Maybe<&2, Halves>,
          Part.hits(_, k),
          u => None{},
          u => Mst.split.done(l, left, _, Mst.split(~S, ~fetch, p, s, Part.room(_, l, lo, hi), Part.gap(_), k))
        )
      )
      Mst.split_ok.hit(
        ~S,
        ~fetch,
        Part.hits(Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)}, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        Mst.pre(xs, k),
        Mst.post(xs, k),
        Equal.trans(
          Maybe<&2, Node>,
          Mst.node(~S, ~fetch, s, h),
          Some{Node{l, left, xs}},
          Some{Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}},
          Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
          Equal.cong(
            List<&2, Item>,
            Maybe<&2, Node>,
            ys => Some{Node{l, left, ys}},
            xs,
            List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
            Equal.sym(List<&2, Item>, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)), xs, Mst.pre_post(xs, k))
          )
        ),
        Equal.trans(
          Bool,
          Mst.opens(Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}, Room{ur, lo, hi}),
          Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}),
          True{},
          Equal.cong(
            List<&2, Item>,
            Bool,
            ys => Mst.opens(Node{l, left, ys}, Room{ur, lo, hi}),
            List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
            xs,
            Mst.pre_post(xs, k)
          ),
          Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
        ),
        Mst.pre_all_lt(xs, k),
        Mst.post_head(xs, k),
        {==},
        ih
      )

# the split of an empty tree
def Mst.split_ok.none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  -ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> Mst.SplitOk(~S, ~fetch, s, ur, lo, hi, k, None{}, Some{Halves{None{}, None{}, []}}):
  +hold => (
    {==},
    (
      +u2 => +lv => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.none_kept(~S, ~fetch, g1, g2, s, Room{u1, lo, hi}, Room{u2, lo, Some{k}}, k2, x),
      +u2 => +lv => +k2 => +x => +u1 => +g1 => +g2 => +c => +fu => Mst.none_kept(~S, ~fetch, g1, g2, s, Room{u1, lo, hi}, Room{u2, Some{k}, hi}, k2, x)
    )
  )

# a split of a tree at k, in its room, reads as Mst.SplitOk says
def Mst.split_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +s: S,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> Mst.SplitOk(~S, ~fetch, s, ur, lo, hi, k, m, Mst.split(~S, ~fetch, f, s, Room{ur, lo, hi}, m, k)):
  match f m:
    case 0n None{}:
      Mst.split_ok.none(~S, ~fetch, s, ur, lo, hi, k)
    case 1n+q None{}:
      Mst.split_ok.none(~S, ~fetch, s, ur, lo, hi, k)
    case 0n Some{h}:
      Unit{}
    case 1n+(+p) Some{+h}:
      Mst.split_ok.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        {==},
        +ur2 => +lo2 => +hi2 => +m2 => Mst.split_ok(~S, ~fetch, p, m2, s, ur2, lo2, hi2, k)
      )

# a pick of k among items that start with k hits its value
def Mst.hit_first(
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +b: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +a: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Mst.pick(Item{k, v, b} <> rest, a, l, lo, hi, k) == Pick.Hit{v}: Pick}:
  %Equal.sym(Cmp, Key.cmp(k, k), EQ{}, Mst.key_refl(k)) :
    {Shared.Bool.when(Pick, Cmp.is_lt(_), u => Pick.Down{a, Room.of(l, lo, Some{k})}, u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{v}, w => Mst.pick(rest, b, l, Some{k}, hi, k))) == Pick.Hit{v} : Pick}
  {==}

# the level of k, checked against the level L of k
def Mst.level_ok(+k: List<&2, U32>, +l: Nat, +el: {Key.level(k) == l: Nat}) -> {Nat.is_eq(Key.level(k), l) == True{}: Bool}:
  %Equal.sym(Nat, Level.of(Hashes.Sha.go.of(List.length(&2, U32, k), Hashes.Hash{1779033703, 3144134277, 1013904242, 2773480762, 1359893119, 2600822924, 528734635, 1541459225}, k, 0, Hashes.Block.of(List.take(&2, U32, k, 16n)))), l, el) : {Cmp.is_eq(Nat.cmp(_, l)) == True{} : Bool}; Shared.Nat.is_eq_refl(l)

# a read of a node whose pick hits the value v, of a key of the level of the
# node, finds v
def Mst.new_hit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g: Nat,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g) == True{}: Bool},
  +ep: {Mst.pick(xs, left, l, lo, hi, k) == Pick.Hit{v}: Pick},
  +el: {Nat.is_eq(Key.level(k), l) == True{}: Bool}
) -> {Look.known(Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hi}, Some{h}, k)) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match g:
    case 0n:
      Empty.absurd(
        {Look.known(Look.Missing{h}) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, left, xs, u, lo, hi, oN, fu)
      )
    case 1n+(+p):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p, s, Room{u, lo, hi}, Some{h}, k),
        Mst.look.pick(Mst.pick(xs, left, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k)),
        Mst.look_node(~S, ~fetch, p, s, h, u, lo, hi, l, left, xs, k, eN, oN)
      ): {Look.known(_) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      %Equal.sym(Pick, Mst.pick(xs, left, l, lo, hi, k), Pick.Hit{v}, ep): {
        Look.known(Mst.look.pick(_, h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, p, s, r2, m2, k)))
          == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      %Equal.sym(Bool, Nat.is_eq(Key.level(k), l), True{}, el): {
        Look.known(Shared.Bool.when(Look, _, u2 => Look.Found{v}, u2 => Look.Missing{h}))
          == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      {==}

# items with their last subtree set to their own last subtree are the items
def Mst.set_last_last(+xs: List<&2, Item>, +left: Maybe<&2, Hashes.Hash>) -> {Mst.set_last(xs, Mst.last(xs, left)) == xs: List<&2, Item>}:
  match xs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Item{key, value, right}:
          match tail:
            case Nil{}:
              {==}
            case Con{head, tail1}:
              %Equal.sym(List<&2, Item>, Mst.set_last(head <> tail1, Mst.last(head <> tail1, right)), head <> tail1, Mst.set_last_last(head <> tail1, right)) : {Item{key, value, right} <> _ == Item{key, value, right} <> head <> tail1 : List<&2, Item>}; {==}

# a pick of another key than k reads no value of k
def Mst.pick_val(
  +pre: List<&2, Item>,
  +k: List<&2, U32>,
  +v1: List<&2, U32>,
  +v2: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool}
) -> {
  Mst.pick(List.append(&2, Item, pre, Item{k, v1, r} <> rest), prev, l, lo, hi, k2)
    == Mst.pick(List.append(&2, Item, pre, Item{k, v2, r} <> rest), prev, l, lo, hi, k2): Pick
}:
  match pre:
    case Nil{}:
      Mst.case_cmp(
        c => {Cmp.is_eq(c) == False{}: Bool} -> {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{k})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{v1}, w => Mst.pick(rest, r, l, Some{k}, hi, k2))
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{prev, Room.of(l, lo, Some{k})},
              u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{v2}, w => Mst.pick(rest, r, l, Some{k}, hi, k2))
            ): Pick
        },
        Key.cmp(k2, k),
        +q => +e => {==},
        +q => +e => Empty.absurd({Pick.Hit{v1} == Pick.Hit{v2}: Pick}, Shared.Bool.true_ne_false(e)),
        +q => +e => {==}
      )(ne)
    case Con{Item{+ik, +iv, +ir}, +tl}:
      Mst.case_cmp(
        c => {
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(
              Pick,
              Cmp.is_eq(c),
              w => Pick.Hit{iv},
              w => Mst.pick(List.append(&2, Item, tl, Item{k, v1, r} <> rest), ir, l, Some{ik}, hi, k2)
            )
          )
            == Shared.Bool.when(
              Pick,
              Cmp.is_lt(c),
              u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
              u => Shared.Bool.when(
                Pick,
                Cmp.is_eq(c),
                w => Pick.Hit{iv},
                w => Mst.pick(List.append(&2, Item, tl, Item{k, v2, r} <> rest), ir, l, Some{ik}, hi, k2)
              )
            ): Pick
        },
        Key.cmp(k2, ik),
        +q => {==},
        +q => {==},
        +q => Mst.pick_val(tl, k, v1, v2, r, rest, ir, l, Some{ik}, hi, k2, ne)
      )

# items of other values fit as the items
def Mst.fit_val(
  +pre: List<&2, Item>,
  +k: List<&2, U32>,
  -v1: List<&2, U32>,
  -v2: List<&2, U32>,
  -r: Maybe<&2, Hashes.Hash>,
  -rest: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {
  Items.fit(List.append(&2, Item, pre, Item{k, v1, r} <> rest), lo, hi)
    == Items.fit(List.append(&2, Item, pre, Item{k, v2, r} <> rest), lo, hi): Bool
}:
  match pre:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +ir}, +tl}:
      Equal.cong(
        Bool,
        Bool,
        b => Bool.and(Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)), b),
        Items.fit(List.append(&2, Item, tl, Item{k, v1, r} <> rest), Some{ik}, hi),
        Items.fit(List.append(&2, Item, tl, Item{k, v2, r} <> rest), Some{ik}, hi),
        Mst.fit_val(tl, k, v1, v2, r, rest, Some{ik}, hi)
      )

# items, then one more and more, are not empty
def Mst.empty_app_con(+pre: List<&2, Item>, -y: Item, -ys: List<&2, Item>) -> {
  List.is_empty(&2, Item, List.append(&2, Item, pre, y <> ys)) == False{}: Bool
}:
  match pre:
    case Nil{}:
      {==}
    case Con{head, tail}:
      {==}

# a node of items of other values opens where the node opens
def Mst.opens_val(
  +l: Nat,
  -left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +k: List<&2, U32>,
  +v1: List<&2, U32>,
  +v2: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +o: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, v1, r} <> rest)}, Room{u, lo, hi}) == True{}: Bool}
) -> {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, v2, r} <> rest)}, Room{u, lo, hi}) == True{}: Bool}:
  Mst.opens_of(l, left, List.append(&2, Item, pre, Item{k, v2, r} <> rest), u, lo, hi, Mst.opens_lt(l, left, List.append(&2, Item, pre, Item{k, v1, r} <> rest), Room{u, lo, hi})(o), Mst.empty_app_con(pre, Item{k, v2, r}, rest), (%Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{k, v1, r} <> rest), u, lo, hi, o) : {Items.fit(List.append(&2, Item, pre, Item{k, v2, r} <> rest), lo, hi) == _ : Bool}; Mst.fit_val(pre, k, v2, v1, r, rest, lo, hi)))

# two nodes in one room whose picks of k2 are the same read k2 the same
def Mst.same_read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +h2: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left1: Maybe<&2, Hashes.Hash>,
  +xs1: List<&2, Item>,
  +left2: Maybe<&2, Hashes.Hash>,
  +xs2: List<&2, Item>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left1, xs1}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left1, xs1}, Room{u, lo, hi}) == True{}: Bool},
  +eN2: {Mst.node(~S, ~fetch, s, h2) == Some{Node{l, left2, xs2}}: Maybe<&2, Node>},
  +oN2: {Mst.opens(Node{l, left2, xs2}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  +ep: {Mst.pick(xs2, left2, l, lo, hi, k2) == Mst.pick(xs1, left1, l, lo, hi, k2): Pick}
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{u, lo, hi}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{h2}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, left2, xs2, u, lo, hi, oN2, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{u, lo, hi}, Some{h}, k2),
        Mst.look.pick(Mst.pick(xs1, left1, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p1, s, h, u, lo, hi, l, left1, xs1, k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{h2}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{u, lo, hi}, Some{h2}, k2),
        Mst.look.pick(Mst.pick(xs2, left2, l, lo, hi, k2), h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)),
        Mst.look_node(~S, ~fetch, p2, s, h2, u, lo, hi, l, left2, xs2, k2, eN2, oN2)
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(xs1, left1, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(Pick, Mst.pick(xs2, left2, l, lo, hi, k2), Mst.pick(xs1, left1, l, lo, hi, k2), ep): (
        {
          Look.known(Mst.look.pick(Mst.pick(xs1, left1, l, lo, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, h2, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.look.same_pick(
        ~S,
        ~fetch,
        p1,
        p2,
        s,
        xs1,
        left1,
        l,
        lo,
        lo,
        hi,
        hi,
        h,
        h2,
        k2,
        x,
        Mst.lo_le_refl(lo),
        Mst.hi_le_refl(hi),
        Mst.opens_fl(l, left2, xs2, u, lo, hi, p2, oN2, fu)
      )

# a read of a node of one item k, of a key below k, reads the subtree before it
def Mst.single_lt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g2: Nat,
  +s: S,
  +ht: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +a: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +b: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eT: {Mst.node(~S, ~fetch, s, ht) == Some{Node{l, a, [Item{k, v, b}]}}: Maybe<&2, Node>},
  +oT: {Mst.opens(Node{l, a, [Item{k, v, b}]}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  +c: {Key.cmp(k2, k) == LT{}: Cmp},
  ih: @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, lo, Some{k}}, a, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{ht}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  Mst.new_down(~S, ~fetch, g2, s, ht, u, lo, hi, l, a, [Item{k, v, b}], k2, x, a, lo, Some{k}, eT, oT, fu, (%Equal.sym(Cmp, Key.cmp(k2, k), LT{}, c) : {Shared.Bool.when(Pick, Cmp.is_lt(_), u => Pick.Down{a, Room.of(l, lo, Some{k})}, u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{v}, w => Mst.pick([], b, l, Some{k}, hi, k2))) == Pick.Down{a, Room{l, lo, Some{k}}} : Pick}; {==}), ih)

# a read of a node of one item k, of a key above k, reads the subtree after it
def Mst.single_gt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g2: Nat,
  +s: S,
  +ht: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +a: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +b: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eT: {Mst.node(~S, ~fetch, s, ht) == Some{Node{l, a, [Item{k, v, b}]}}: Maybe<&2, Node>},
  +oT: {Mst.opens(Node{l, a, [Item{k, v, b}]}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g2) == True{}: Bool},
  +c: {Key.cmp(k2, k) == GT{}: Cmp},
  ih: @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Some{k}, hi}, b, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, Some{ht}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  Mst.new_down(~S, ~fetch, g2, s, ht, u, lo, hi, l, a, [Item{k, v, b}], k2, x, b, Some{k}, hi, eT, oT, fu, (%Equal.sym(Cmp, Key.cmp(k2, k), GT{}, c) : {Shared.Bool.when(Pick, Cmp.is_lt(_), u => Pick.Down{a, Room.of(l, lo, Some{k})}, u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{v}, w => Mst.pick([], b, l, Some{k}, hi, k2))) == Pick.Down{b, Room{l, Some{k}, hi}} : Pick}; {==}), ih)

# what a write of k as v reads: k, as v; any other key, as the tree m did
def Mst.InsRead(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -ur: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  -m: Maybe<&2, Hashes.Hash>,
  -k: List<&2, U32>,
  -v: Maybe<&2, List<&2, U32>>,
  -nr: Maybe<&2, Hashes.Hash>
) -> Type:
  (
    @g: Nat -> {Nat.is_le(ur, g) == True{}: Bool} -> {
      Look.known(Mst.look.go(~S, ~fetch, g, s, Room{ur, lo, hi}, nr, k)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
  )
    & (
      @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @g1: Nat -> @g2: Nat -> {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool} -> {
        Nat.is_le(ur, g2) == True{}: Bool
      } -> {
        Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, nr, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    )

# a write res of k as v (none: a delete) to the tree m in the room of the up
# ur between lo and hi: once the depot holds its new nodes, it reads as
# Mst.InsRead says
def Mst.InsOk(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -ur: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  -m: Maybe<&2, Hashes.Hash>,
  -k: List<&2, U32>,
  -v: Maybe<&2, List<&2, U32>>,
  res: Maybe<&2, Edit>
) -> Type:
  match res:
    case None{}:
      Unit
    case Some{Edit{nr, ns}}:
      {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool} -> Mst.InsRead(~S, ~fetch, s, ur, lo, hi, m, k, v, nr)


# a key that is not k does not compare EQ to it
def Mst.ne_eq(+k2: List<&2, U32>, +k: List<&2, U32>, +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool}, +c: {Key.cmp(k2, k) == EQ{}: Cmp}) -> Empty:
  Shared.Bool.true_ne_false(
    Equal.trans(
      Bool,
      True{},
      Cmp.is_eq(Key.cmp(k2, k)),
      False{},
      Equal.sym(Bool, Cmp.is_eq(Key.cmp(k2, k)), True{}, Equal.cong(Cmp, Bool, Cmp.is_eq, Key.cmp(k2, k), EQ{}, c)),
      ne
    )
  )

# items with k put between those before it and those after it fit
def Mst.fit_ins(
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +chi: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Items.fit(List.append(&2, Item, pre, post), lo, hi) == True{}: Bool} -> {Mst.all_lt(pre, k) == True{}: Bool} -> {
  Bound.after(lo, k) == True{}: Bool
} -> {Bound.before(k, hi) == True{}: Bool} -> {Items.fit(post, Some{k}, hi) == True{}: Bool} -> {
  Items.fit(List.append(&2, Item, pre, Item{k, v, chi} <> post), lo, hi) == True{}: Bool
}:
  +f => +al => +a => +b => +fp => Equal.trans(
    Bool,
    Items.fit(List.append(&2, Item, pre, Item{k, v, chi} <> post), lo, hi),
    Bool.and(Items.fit(pre, lo, hi), Items.fit(Item{k, v, chi} <> post, Items.last_key(pre, lo), hi)),
    True{},
    Mst.fit_append(pre, Item{k, v, chi} <> post, lo, hi),
    Shared.Bool.and_both(
      Items.fit(pre, lo, hi),
      Items.fit(Item{k, v, chi} <> post, Items.last_key(pre, lo), hi),
      Shared.Bool.and_true_left(
        Items.fit(pre, lo, hi),
        Items.fit(post, Items.last_key(pre, lo), hi),
        Equal.trans(
          Bool,
          Bool.and(Items.fit(pre, lo, hi), Items.fit(post, Items.last_key(pre, lo), hi)),
          Items.fit(List.append(&2, Item, pre, post), lo, hi),
          True{},
          Equal.sym(
            Bool,
            Items.fit(List.append(&2, Item, pre, post), lo, hi),
            Bool.and(Items.fit(pre, lo, hi), Items.fit(post, Items.last_key(pre, lo), hi)),
            Mst.fit_append(pre, post, lo, hi)
          ),
          f
        )
      ),
      Shared.Bool.and_both(
        Bool.and(Bound.after(Items.last_key(pre, lo), k), Bound.before(k, hi)),
        Items.fit(post, Some{k}, hi),
        Shared.Bool.and_both(Bound.after(Items.last_key(pre, lo), k), Bound.before(k, hi), Mst.last_below(pre, lo, k)(al)(a), b),
        fp
      )
    )
  )

# a pick of a key after k among k and more steps past k
def Mst.pick_past_k(
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +chi: Maybe<&2, Hashes.Hash>,
  +post: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lk: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k2: List<&2, U32>,
  +c: {Key.cmp(k2, k) == GT{}: Cmp}
) -> {Mst.pick(Item{k, v, chi} <> post, clo, l, lk, hi, k2) == Mst.pick(post, chi, l, Some{k}, hi, k2): Pick}:
  %Equal.sym(Cmp, Key.cmp(k2, k), GT{}, c): {
    Shared.Bool.when(
      Pick,
      Cmp.is_lt(_),
      u => Pick.Down{clo, Room.of(l, lk, Some{k})},
      u => Shared.Bool.when(Pick, Cmp.is_eq(_), w => Pick.Hit{v}, w => Mst.pick(post, chi, l, Some{k}, hi, k2))
    )
      == Mst.pick(post, chi, l, Some{k}, hi, k2): Pick
  }
  {==}

# a node with k put into its gap, between its halves, reads a key above k as
# the node did, but in the upper half, as ih says
def Mst.ins_hi(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +chi: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +eG: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}}: Maybe<&2, Node>
  },
  +oG: {
    Mst.opens(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, Room{ur, lo, hi})
      == True{}: Bool
  },
  +ps: {Mst.passes(pre, k2) == True{}: Bool},
  +c: {Key.cmp(k2, k) == GT{}: Cmp},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Some{k}, Items.head_key(post, hi)}, chi, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(
          l,
          Mst.end_left(pre, left, clo),
          List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post),
          ur,
          lo,
          hi,
          oG,
          fu
        )
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ur, lo, hi}, Some{h}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
          h,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
        ),
        Mst.look_node(~S, ~fetch, p1, s, h, ur, lo, hi, l, left, List.append(&2, Item, pre, post), k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{ur, lo, hi}, Some{hn}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post), Mst.end_left(pre, left, clo), l, lo, hi, k2),
          hn,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          hn,
          ur,
          lo,
          hi,
          l,
          Mst.end_left(pre, left, clo),
          List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post),
          k2,
          eG,
          oG
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, pre, post), left, l, lo, hi, k2),
        Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
        Mst.pick_passes(pre, post, left, l, lo, hi, k2)(ps)
      ): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post), Mst.end_left(pre, left, clo), l, lo, hi, k2),
                hn,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post), Mst.end_left(pre, left, clo), l, lo, hi, k2),
        Mst.pick(post, chi, l, Some{k}, hi, k2),
        Equal.trans(
          Pick,
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post), Mst.end_left(pre, left, clo), l, lo, hi, k2),
          Mst.pick(Item{k, v, chi} <> post, clo, l, Items.last_key(pre, lo), hi, k2),
          Mst.pick(post, chi, l, Some{k}, hi, k2),
          Mst.pick_set_passes(pre, clo, Item{k, v, chi} <> post, left, l, lo, hi, k2, ps),
          Mst.pick_past_k(k, v, chi, post, clo, l, Items.last_key(pre, lo), hi, k2, c)
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(post, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.gap_kept.first(
        ~S,
        ~fetch,
        Mst.stops_first(post, k2),
        p1,
        p2,
        s,
        post,
        Mst.last(pre, left),
        chi,
        l,
        Items.last_key(pre, lo),
        Some{k},
        hi,
        hi,
        h,
        hn,
        k2,
        x,
        {==},
        Mst.hi_le_refl(hi),
        Mst.opens_fl(
          l,
          Mst.end_left(pre, left, clo),
          List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post),
          ur,
          lo,
          hi,
          p2,
          oG,
          fu
        ),
        ih
      )

# a write of k into an empty tree
def Mst.ins_ok.none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +el: {Key.level(k) == ll: Nat},
  +lt: {Nat.is_lt(ll, ur) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool}
) -> Mst.InsOk(~S, ~fetch, s, ur, lo, hi, None{}, k, Some{v}, Some{Mst.store(Node{ll, None{}, [Item{k, v, None{}}]}, [])}):
  +hold =>
    +eT = Mst.node_code(
      ~S,
      ~fetch,
      s,
      Node{ll, None{}, [Item{k, v, None{}}]},
      Mst.holds_head(~S, ~fetch, s, Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, []), [], hold)
    )
    +oT = Mst.opens_of(
      ll,
      None{},
      [Item{k, v, None{}}],
      ur,
      lo,
      hi,
      lt,
      {==},
      Shared.Bool.and_both(
        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
        True{},
        Shared.Bool.and_both(Bound.after(lo, k), Bound.before(k, hi), a, bb),
        {==}
      )
    )
    (
      +g => +fu => Mst.new_hit(
        ~S,
        ~fetch,
        g,
        s,
        Hashes.Sha.hash(Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, [])),
        ur,
        lo,
        hi,
        ll,
        None{},
        [Item{k, v, None{}}],
        k,
        v,
        eT,
        oT,
        fu,
        Mst.hit_first(k, v, None{}, [], None{}, ll, lo, hi),
        Mst.level_ok(k, ll, el)
      ),
      +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.case_cmp(
        t => {Key.cmp(k2, k) == t: Cmp} -> {
          Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{Hashes.Sha.hash(Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, []))}, k2))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Key.cmp(k2, k),
        +q => +c => Mst.single_lt(
          ~S,
          ~fetch,
          g2,
          s,
          Hashes.Sha.hash(Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, [])),
          ur,
          lo,
          hi,
          ll,
          None{},
          k,
          v,
          None{},
          k2,
          x,
          eT,
          oT,
          fu,
          c,
          +g4 => +fl => Mst.none_kept(~S, ~fetch, g1, g4, s, Room{ur, lo, hi}, Room{ll, lo, Some{k}}, k2, x)(e)
        ),
        +q => +c => Empty.absurd(
          {
            Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{Hashes.Sha.hash(Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, []))}, k2))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          },
          Mst.ne_eq(k2, k, ne, c)
        ),
        +q => +c => Mst.single_gt(
          ~S,
          ~fetch,
          g2,
          s,
          Hashes.Sha.hash(Node.code(Node{ll, None{}, [Item{k, v, None{}}]}, [])),
          ur,
          lo,
          hi,
          ll,
          None{},
          k,
          v,
          None{},
          k2,
          x,
          eT,
          oT,
          fu,
          c,
          +g4 => +fl => Mst.none_kept(~S, ~fetch, g1, g4, s, Room{ur, lo, hi}, Room{ll, Some{k}, hi}, k2, x)(e)
        )
      )({==})
    )

# Mst.ins_ok.top.read, for a key other than k, by how it compares to k (c)
def Mst.ins_ok.top.k2(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +hl: Maybe<&2, Hashes.Hash>,
  +hh: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +x: Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g2: Nat,
  +ec: {Key.cmp(k2, k) == c: Cmp},
  +eT: {Mst.node(~S, ~fetch, s, Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, []))) == Some{Node{ll, hl, [Item{k, v, hh}]}}: Maybe<&2, Node>},
  +oT: {Mst.opens(Node{ll, hl, [Item{k, v, hh}]}, Room{ur, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool},
  +lv: {Mst.lvl(~S, ~fetch, s, Some{h}, ll) == True{}: Bool},
  +e: {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sr: Mst.SplitRead(~S, ~fetch, s, lo, hi, k, Some{h}, hl, hh)
) -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, []))}, k2))
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match c:
    case LT{}:
      (slo, shi) = sr
      Mst.single_lt(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, [])),
        ur,
        lo,
        hi,
        ll,
        hl,
        k,
        v,
        hh,
        k2,
        x,
        eT,
        oT,
        fu,
        ec,
        +g4 => +fl => slo(ll)(lv)(k2)(x)(ur)(g1)(g4)(ec)(fl)(e)
      )
    case GT{}:
      (slo, shi) = sr
      Mst.single_gt(
        ~S,
        ~fetch,
        g2,
        s,
        Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, [])),
        ur,
        lo,
        hi,
        ll,
        hl,
        k,
        v,
        hh,
        k2,
        x,
        eT,
        oT,
        fu,
        ec,
        +g4 => +fl => shi(ll)(lv)(k2)(x)(ur)(g1)(g4)(ec)(fl)(e)
      )
    case EQ{}:
      Empty.absurd(
        {
          Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, []))}, k2))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Mst.ne_eq(k2, k, ne, ec)
      )

# what a write of k as a new root reads, from what the split of the old root
# reads (bi)
def Mst.ins_ok.top.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +hl: Maybe<&2, Hashes.Hash>,
  +hh: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(l, ll) == LT{}: Cmp},
  +el: {Key.level(k) == ll: Nat},
  +lt: {Nat.is_lt(ll, ur) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +hold: {Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{ll, hl, [Item{k, v, hh}]}, []) <> ns) == True{}: Bool},
  bi: {Mst.lvl(~S, ~fetch, s, Some{h}, ur) == True{}: Bool} & Mst.SplitRead(~S, ~fetch, s, lo, hi, k, Some{h}, hl, hh)
) -> Mst.InsRead(~S, ~fetch, s, ur, lo, hi, Some{h}, k, Some{v}, Some{Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, []))}):
  (lvh, sr) = bi
  +eT = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{ll, hl, [Item{k, v, hh}]},
    Mst.holds_head(~S, ~fetch, s, Node.code(Node{ll, hl, [Item{k, v, hh}]}, []), ns, hold)
  )
  +oT = Mst.opens_of(
    ll,
    hl,
    [Item{k, v, hh}],
    ur,
    lo,
    hi,
    lt,
    {==},
    Shared.Bool.and_both(
      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
      True{},
      Shared.Bool.and_both(Bound.after(lo, k), Bound.before(k, hi), a, bb),
      {==}
    )
  )
  (
    +g => +fu => Mst.new_hit(
      ~S,
      ~fetch,
      g,
      s,
      Hashes.Sha.hash(Node.code(Node{ll, hl, [Item{k, v, hh}]}, [])),
      ur,
      lo,
      hi,
      ll,
      hl,
      [Item{k, v, hh}],
      k,
      v,
      eT,
      oT,
      fu,
      Mst.hit_first(k, v, hh, [], hl, ll, lo, hi),
      Mst.level_ok(k, ll, el)
    ),
    +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.ins_ok.top.k2(
      ~S,
      ~fetch,
      Key.cmp(k2, k),
      s,
      h,
      ur,
      lo,
      hi,
      k,
      v,
      ll,
      hl,
      hh,
      k2,
      x,
      g1,
      g2,
      {==},
      eT,
      oT,
      fu,
      ne,
      Mst.lvl_of(~S, ~fetch, s, h, ll, l, left, xs, eN, Mst.nat_lt_of(l, ll)(ec)),
      e,
      sr
    )
  )

# a write of k into a tree of a lower level: a new root over its split
def Mst.ins_ok.top(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ms: Maybe<&2, Halves>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +ec: {Nat.cmp(l, ll) == LT{}: Cmp},
  +el: {Key.level(k) == ll: Nat},
  +lt: {Nat.is_lt(ll, ur) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ihs: Mst.SplitOk(~S, ~fetch, s, ur, lo, hi, k, Some{h}, ms)
) -> Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, Some{v}, Mst.insert.top(ll, k, v, ms)):
  match ms:
    case None{}:
      Unit{}
    case Some{Halves{+hl, +hh, +ns}}:
      +hold => Mst.ins_ok.top.read(
        ~S,
        ~fetch,
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        ll,
        l,
        left,
        xs,
        hl,
        hh,
        ns,
        eN,
        ec,
        el,
        lt,
        a,
        bb,
        hold,
        ihs(Mst.holds_tail(~S, ~fetch, s, Node.code(Node{ll, hl, [Item{k, v, hh}]}, []), ns, hold))
      )

# a write of k as v to a node of its level that holds k: the value replaced
def Mst.ins_ok.replace(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +ell: {Nat.is_eq(Key.level(k), l) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Some{Mst.store(Node{l, left, Mst.rejoin(List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), Item{k, v, r} <> rest)}, [])}
):
  %Equal.sym(
    List<&2, Item>,
    Mst.rejoin(List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), Item{k, v, r} <> rest),
    List.append(&2, Item, Mst.set_last(pre, Mst.last(pre, left)), Item{k, v, r} <> rest),
    Mst.rejoin_rev(pre, Mst.last(pre, left), Item{k, v, r} <> rest)
  ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, Some{v}, Some{Mst.store(Node{l, left, _}, [])})
  %Equal.sym(List<&2, Item>, Mst.set_last(pre, Mst.last(pre, left)), pre, Mst.set_last_last(pre, left)): Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur,
    lo,
    hi,
    Some{h},
    k,
    Some{v},
    Some{Mst.store(Node{l, left, List.append(&2, Item, _, Item{k, v, r} <> rest)}, [])}
  )
  +hold =>
    +eR = Mst.node_code(
      ~S,
      ~fetch,
      s,
      Node{l, left, List.append(&2, Item, pre, Item{k, v, r} <> rest)},
      Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, left, List.append(&2, Item, pre, Item{k, v, r} <> rest)}, []), [], hold)
    )
    +oR = Mst.opens_val(l, left, pre, k, iv, v, r, rest, ur, lo, hi, oN)
    (
      +g => +fu => Mst.new_hit(
        ~S,
        ~fetch,
        g,
        s,
        Hashes.Sha.hash(Node.code(Node{l, left, List.append(&2, Item, pre, Item{k, v, r} <> rest)}, [])),
        ur,
        lo,
        hi,
        l,
        left,
        List.append(&2, Item, pre, Item{k, v, r} <> rest),
        k,
        v,
        eR,
        oR,
        fu,
        Equal.trans(
          Pick,
          Mst.pick(List.append(&2, Item, pre, Item{k, v, r} <> rest), left, l, lo, hi, k),
          Mst.pick(Item{k, v, r} <> rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k),
          Pick.Hit{v},
          Mst.pick_passes(pre, Item{k, v, r} <> rest, left, l, lo, hi, k)(Mst.passes_of_all_lt(pre, k)(all)),
          Mst.hit_first(k, v, r, rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi)
        ),
        ell
      ),
      +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.same_read(
        ~S,
        ~fetch,
        g1,
        g2,
        s,
        h,
        Hashes.Sha.hash(Node.code(Node{l, left, List.append(&2, Item, pre, Item{k, v, r} <> rest)}, [])),
        ur,
        lo,
        hi,
        l,
        left,
        List.append(&2, Item, pre, Item{k, iv, r} <> rest),
        left,
        List.append(&2, Item, pre, Item{k, v, r} <> rest),
        k2,
        x,
        eN,
        oN,
        eR,
        oR,
        fu,
        Mst.pick_val(pre, k, v, iv, r, rest, left, l, lo, hi, k2, ne)
      )(e)
    )

# Mst.ins_ok.gap.read, for a key other than k, by how it compares to k (c)
def Mst.ins_ok.gap.k2(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +chi: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +x: Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g2: Nat,
  +ec: {Key.cmp(k2, k) == c: Cmp},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +eG: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}}: Maybe<&2, Node>
  },
  +oG: {
    Mst.opens(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, Room{ur, lo, hi})
      == True{}: Bool
  },
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool},
  +lvg: {Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool},
  +e: {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sr: Mst.SplitRead(~S, ~fetch, s, Items.last_key(pre, lo), Items.head_key(post, hi), k, Mst.last(pre, left), clo, chi)
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match c:
    case LT{}:
      (slo, shi) = sr
      Mst.gap_lo(
        ~S,
        ~fetch,
        g1,
        g2,
        s,
        h,
        hn,
        ur,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        pre,
        post,
        Item{k, v, chi} <> post,
        clo,
        hi,
        k2,
        x,
        eN,
        oN,
        eG,
        oG,
        Mst.stops_first_fit(post, k, hi, k2)(pk)(Mst.le_of_lt(Key.cmp(k2, k))(ec)),
        Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k2, k), LT{}, ec),
        fu,
        +g3 => +g4 => +fl => +e3 => slo(l)(lvg)(k2)(x)(l)(g3)(g4)(ec)(fl)(e3)
      )(e)
    case GT{}:
      (slo, shi) = sr
      Mst.ins_hi(
        ~S,
        ~fetch,
        g1,
        g2,
        s,
        h,
        hn,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        post,
        clo,
        chi,
        k2,
        x,
        eN,
        oN,
        eG,
        oG,
        Mst.passes_of_lt(pre, k, k2)(all)(Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k, k2), LT{}, Mst.key_gt_lt(k2, k)(ec))),
        ec,
        fu,
        +g3 => +g4 => +fl => +e3 => shi(l)(lvg)(k2)(x)(l)(g3)(g4)(ec)(fl)(e3)
      )(e)
    case EQ{}:
      Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.ne_eq(k2, k, ne, ec)
      )

# what a write of k into the gap of a node of its level reads, from what the
# split of the gap reads (bi)
def Mst.ins_ok.gap.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +clo: Maybe<&2, Hashes.Hash>,
  +chi: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +ell: {Nat.is_eq(Key.level(k), l) == True{}: Bool},
  +hold: {
    Depots.Depot.holds(
      ~S,
      ~fetch,
      s,
      Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, []) <> ns
    )
      == True{}: Bool
  },
  bi: {Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool}
    & Mst.SplitRead(~S, ~fetch, s, Items.last_key(pre, lo), Items.head_key(post, hi), k, Mst.last(pre, left), clo, chi)
) -> Mst.InsRead(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Some{Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, []))}
):
  (+lvg, sr) = bi
  +eG = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)},
    Mst.holds_head(
      ~S,
      ~fetch,
      s,
      Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, []),
      ns,
      hold
    )
  )
  +oG = Mst.opens_set_last(l, left, Mst.end_left(pre, left, clo), pre, clo, Item{k, v, chi} <> post, Room{ur, lo, hi})(
    Mst.opens_of(
      l,
      left,
      List.append(&2, Item, pre, Item{k, v, chi} <> post),
      ur,
      lo,
      hi,
      Mst.opens_lt(l, left, List.append(&2, Item, pre, post), Room{ur, lo, hi})(oN),
      Mst.empty_app_con(pre, Item{k, v, chi}, post),
      Mst.fit_ins(pre, post, k, v, chi, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, post), ur, lo, hi, oN))(all)(a)(bb)(pk)
    )
  )
  (
    +g => +fu => Mst.new_hit(
      ~S,
      ~fetch,
      g,
      s,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, [])),
      ur,
      lo,
      hi,
      l,
      Mst.end_left(pre, left, clo),
      List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post),
      k,
      v,
      eG,
      oG,
      fu,
      Equal.trans(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post), Mst.end_left(pre, left, clo), l, lo, hi, k),
        Mst.pick(Item{k, v, chi} <> post, clo, l, Items.last_key(pre, lo), hi, k),
        Pick.Hit{v},
        Mst.pick_set_passes(pre, clo, Item{k, v, chi} <> post, left, l, lo, hi, k, Mst.passes_of_all_lt(pre, k)(all)),
        Mst.hit_first(k, v, chi, post, clo, l, Items.last_key(pre, lo), hi)
      ),
      ell
    ),
    +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.ins_ok.gap.k2(
      ~S,
      ~fetch,
      Key.cmp(k2, k),
      s,
      h,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, [])),
      ur,
      lo,
      hi,
      k,
      v,
      l,
      left,
      pre,
      post,
      clo,
      chi,
      k2,
      x,
      g1,
      g2,
      {==},
      eN,
      oN,
      eG,
      oG,
      all,
      pk,
      fu,
      ne,
      lvg,
      e,
      sr
    )
  )

# a write of k into the gap of a node of its level, once the gap is split (ms)
def Mst.ins_ok.gap(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ms: Maybe<&2, Halves>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +ell: {Nat.is_eq(Key.level(k), l) == True{}: Bool},
  ihs: Mst.SplitOk(~S, ~fetch, s, l, Items.last_key(pre, lo), Items.head_key(post, hi), k, Mst.last(pre, left), ms)
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Mst.insert.gap(l, left, k, v, Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, ms)
):
  match ms:
    case None{}:
      Unit{}
    case Some{Halves{+clo, +chi, +ns}}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.left(List.reverse.go(&2, Item, pre, []), left, clo),
        Mst.end_left(pre, left, clo),
        Mst.left_rev(pre, left, clo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        Some{v},
        Some{Mst.store(Node{l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, Item{k, v, chi} <> post)}, ns)}
      )
      %Equal.sym(
        List<&2, Item>,
        Mst.rejoin(List.reverse.go(&2, Item, pre, []), clo, Item{k, v, chi} <> post),
        List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post),
        Mst.rejoin_rev(pre, clo, Item{k, v, chi} <> post)
      ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, Some{v}, Some{Mst.store(Node{l, Mst.end_left(pre, left, clo), _}, ns)})
      +hold => Mst.ins_ok.gap.read(
        ~S,
        ~fetch,
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        post,
        clo,
        chi,
        ns,
        eN,
        oN,
        all,
        pk,
        a,
        bb,
        ell,
        hold,
        ihs(
          Mst.holds_tail(
            ~S,
            ~fetch,
            s,
            Node.code(Node{l, Mst.end_left(pre, left, clo), List.append(&2, Item, Mst.set_last(pre, clo), Item{k, v, chi} <> post)}, []),
            ns,
            hold
          )
        )
      )

# a write of k to a node of its level whose first item from k on is ik, by
# whether ik is k (b)
def Mst.ins_ok.here.b(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +eb: {Cmp.is_eq(Key.cmp(ik, k)) == b: Bool},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(Item{ik, iv, r} <> rest, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +ell: {Nat.is_eq(Key.level(k), l) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Shared.Bool.when(
    Maybe<&2, Edit>,
    b,
    u => Some{Mst.store(Node{l, left, Mst.rejoin(List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), Item{k, v, r} <> rest)}, [])},
    u => Mst.insert.gap(
      l,
      left,
      k,
      v,
      Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), Item{ik, iv, r} <> rest},
      Mst.split(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Some{ik}}, Mst.last(pre, left), k)
    )
  )
):
  match b:
    case True{}:
      +eik = Mst.key_eq(ik, k)(Shared.Cmp.is_eq_sound(Key.cmp(ik, k))(eb))
      Mst.ins_ok.replace(
        ~S,
        ~fetch,
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        iv,
        r,
        rest,
        Equal.trans(
          Maybe<&2, Node>,
          Mst.node(~S, ~fetch, s, h),
          Some{Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}},
          Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}},
          eN,
          Equal.cong(List<&2, U32>, Maybe<&2, Node>, z => Some{Node{l, left, List.append(&2, Item, pre, Item{z, iv, r} <> rest)}}, ik, k, eik)
        ),
        Equal.trans(
          Bool,
          Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}),
          Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}, Room{ur, lo, hi}),
          True{},
          Equal.cong(
            List<&2, U32>,
            Bool,
            z => Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{z, iv, r} <> rest)}, Room{ur, lo, hi}),
            k,
            ik,
            Equal.sym(List<&2, U32>, ik, k, eik)
          ),
          oN
        ),
        all,
        ell
      )
    case False{}:
      Mst.ins_ok.gap(
        ~S,
        ~fetch,
        Mst.split(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Some{ik}}, Mst.last(pre, left), k),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        Item{ik, iv, r} <> rest,
        eN,
        oN,
        all,
        Mst.post_after(Item{ik, iv, r} <> rest, List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), k, Items.last_key(pre, lo), hi)(hn)(eb)(
          Mst.post_fit(pre, Item{ik, iv, r} <> rest, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest), ur, lo, hi, oN))
        ),
        a,
        bb,
        ell,
        Mst.split_ok(~S, ~fetch, p, Mst.last(pre, left), s, l, Items.last_key(pre, lo), Some{ik}, k)
      )

# a write of k to a node of its level, by the items from k on (post)
def Mst.ins_ok.here(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  post: List<&2, Item>,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(post, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +ell: {Nat.is_eq(Key.level(k), l) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Mst.insert.here(
    l,
    left,
    k,
    v,
    Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
    c => Mst.split(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, c, k)
  )
):
  match post:
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.ins_ok.here.b(
        ~S,
        ~fetch,
        Cmp.is_eq(Key.cmp(ik, k)),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        ik,
        iv,
        r,
        rest,
        {==},
        eN,
        oN,
        all,
        hn,
        a,
        bb,
        ell
      )
    case Nil{}:
      Mst.ins_ok.gap(
        ~S,
        ~fetch,
        Mst.split(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), hi}, Mst.last(pre, left), k),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        pre,
        [],
        eN,
        oN,
        all,
        {==},
        a,
        bb,
        ell,
        Mst.split_ok(~S, ~fetch, p, Mst.last(pre, left), s, l, Items.last_key(pre, lo), hi, k)
      )

# what a write of k (as m) below a node of a higher level reads, from what the
# write into its gap reads (bi)
def Mst.ins_ok.gtw.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  +hold: {
    Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, []) <> ns)
      == True{}: Bool
  },
  bi: Mst.InsRead(~S, ~fetch, s, l, Items.last_key(pre, lo), Items.head_key(post, hi), Mst.last(pre, left), k, m, nc)
) -> Mst.InsRead(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  m,
  Some{Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, []))}
):
  (i1, i2) = bi
  +eW = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)},
    Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, []), ns, hold)
  )
  +oW = Mst.opens_set_last(l, left, Mst.end_left(pre, left, nc), pre, nc, post, Room{ur, lo, hi})(oN)
  (
    +g => +fu => Mst.gap_k(
      ~S,
      ~fetch,
      g,
      s,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, [])),
      ur,
      lo,
      hi,
      l,
      left,
      pre,
      post,
      nc,
      k,
      m,
      eW,
      oW,
      fu,
      Mst.passes_of_all_lt(pre, k)(all),
      Mst.stops_first_fit(post, k, hi, k)(pk)(Mst.le_refl_key(k)),
      +g4 => +fl => i1(g4)(fl)
    ),
    +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.gap_kept(
      ~S,
      ~fetch,
      g1,
      g2,
      s,
      h,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, [])),
      ur,
      ur,
      lo,
      lo,
      hi,
      hi,
      l,
      left,
      pre,
      post,
      nc,
      k2,
      x,
      eN,
      oN,
      eW,
      oW,
      Mst.lo_le_refl(lo),
      Mst.hi_le_refl(hi),
      fu,
      +g3 => +g4 => +fl => +e3 => i2(k2)(x)(g3)(g4)(ne)(fl)(e3)
    )(e)
  )

# a write of k (as m) below a node of a higher level, once its gap is written
# (ein)
def Mst.ins_ok.gtw(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  ein: Maybe<&2, Edit>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +pk: {Items.fit(post, Some{k}, hi) == True{}: Bool},
  ihi: Mst.InsOk(~S, ~fetch, s, l, Items.last_key(pre, lo), Items.head_key(post, hi), Mst.last(pre, left), k, m, ein)
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  m,
  Mst.with_gap(l, left, Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, ein)
):
  match ein:
    case None{}:
      Unit{}
    case Some{Edit{+nc, +ns}}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.left(List.reverse.go(&2, Item, pre, []), left, nc),
        Mst.end_left(pre, left, nc),
        Mst.left_rev(pre, left, nc)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        m,
        Some{Mst.make(l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), nc, post), ns)}
      )
      %Equal.sym(
        List<&2, Item>,
        Mst.rejoin(List.reverse.go(&2, Item, pre, []), nc, post),
        List.append(&2, Item, Mst.set_last(pre, nc), post),
        Mst.rejoin_rev(pre, nc, post)
      ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, m, Some{Mst.make(l, Mst.end_left(pre, left, nc), _, ns)})
      %Equal.sym(
        Edit,
        Mst.make(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post), ns),
        Mst.store(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, ns),
        Mst.make_full(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post), ns)(
          Equal.trans(
            Bool,
            List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(pre, nc), post)),
            List.is_empty(&2, Item, List.append(&2, Item, pre, post)),
            False{},
            Mst.empty_set_last_append(pre, nc, post),
            Mst.opens_full(l, left, List.append(&2, Item, pre, post), ur, lo, hi, oN)
          )
        )
      ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, m, Some{_})
      +hold => Mst.ins_ok.gtw.read(
        ~S,
        ~fetch,
        s,
        h,
        ur,
        lo,
        hi,
        k,
        m,
        l,
        left,
        pre,
        post,
        nc,
        ns,
        eN,
        oN,
        all,
        pk,
        hold,
        ihi(
          Mst.holds_tail(
            ~S,
            ~fetch,
            s,
            Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), post)}, []),
            ns,
            hold
          )
        )
      )

# an insert of k below a node of a higher level, by whether the node holds k
# (b0)
def Mst.ins_ok.gt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b0: Bool,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eb0: {Part.hits(Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, k) == b0: Bool},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(post, k) == True{}: Bool},
  +el: {Key.level(k) == ll: Nat},
  +ec: {Nat.cmp(l, ll) == GT{}: Cmp},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Nat.is_lt(ll, ur2) == True{}: Bool
  } -> {Bound.after(lo2, k) == True{}: Bool} -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    Some{v},
    Mst.insert(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, v, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Shared.Bool.when(
    Maybe<&2, Edit>,
    b0,
    u => None{},
    u => Mst.with_gap(
      l,
      left,
      Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
      Mst.insert(
        ~S,
        ~fetch,
        p,
        s,
        Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Items.head_key(post, hi)},
        Mst.last(pre, left),
        k,
        v,
        ll
      )
    )
  )
):
  match b0:
    case True{}:
      Unit{}
    case False{}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        Some{v},
        Mst.with_gap(
          l,
          left,
          Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
          Mst.insert(~S, ~fetch, p, s, Room{l, _, Items.head_key(post, hi)}, Mst.last(pre, left), k, v, ll)
        )
      )
      +pk = Mst.post_after(post, List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), k, Items.last_key(pre, lo), hi)(hn)(eb0)(
        Mst.post_fit(pre, post, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, post), ur, lo, hi, oN))
      )
      Mst.ins_ok.gtw(
        ~S,
        ~fetch,
        Mst.insert(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k, v, ll),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        Some{v},
        l,
        left,
        pre,
        post,
        eN,
        oN,
        all,
        pk,
        ih(l)(Items.last_key(pre, lo))(Items.head_key(post, hi))(Mst.last(pre, left))(el)(Mst.nat_gt_lt(l, ll)(ec))(
          Mst.last_below(pre, lo, k)(all)(a)
        )(Mst.before_head(post, k, hi)(pk)(bb))
      )

# an insert of k at the node of the hash h, by how its level compares to the
# level of k (c)
def Mst.ins_ok.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +ec: {Nat.cmp(l, ll) == c: Cmp},
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +el: {Key.level(k) == ll: Nat},
  +lt: {Nat.is_lt(ll, ur) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Nat.is_lt(ll, ur2) == True{}: Bool
  } -> {Bound.after(lo2, k) == True{}: Bool} -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    Some{v},
    Mst.insert(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, v, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Mst.insert.node(
    c,
    h,
    l,
    left,
    xs,
    lo,
    hi,
    k,
    v,
    ll,
    c2 => Mst.split(~S, ~fetch, p, s, Room{ur, lo, hi}, c2, k),
    r2 => c2 => Mst.split(~S, ~fetch, p, s, r2, c2, k),
    r2 => c2 => Mst.insert(~S, ~fetch, p, s, r2, c2, k, v, ll)
  )
):
  match c:
    case LT{}:
      Mst.ins_ok.top(
        ~S,
        ~fetch,
        Mst.split(~S, ~fetch, p, s, Room{ur, lo, hi}, Some{h}, k),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        ll,
        l,
        left,
        xs,
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        ec,
        el,
        lt,
        a,
        bb,
        Mst.split_ok(~S, ~fetch, p, Some{h}, s, ur, lo, hi, k)
      )
    case EQ{}:
      %Equal.sym(
        Part,
        Mst.part(xs, left, k, []),
        Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
        Mst.part_eq(xs, left, k, [])
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        Some{v},
        Mst.insert.here(l, left, k, v, _, c2 => Mst.split(~S, ~fetch, p, s, Part.room(_, l, lo, hi), c2, k))
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, Mst.pre(xs, k), []), lo),
        Items.last_key(Mst.pre(xs, k), lo),
        Mst.head_rev(Mst.pre(xs, k), lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        Some{v},
        Mst.insert.here(
          l,
          left,
          k,
          v,
          Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
          c2 => Mst.split(~S, ~fetch, p, s, Room{l, _, Items.head_key(Mst.post(xs, k), hi)}, c2, k)
        )
      )
      +eN = Equal.trans(
        Maybe<&2, Node>,
        Mst.node(~S, ~fetch, s, h),
        Some{Node{l, left, xs}},
        Some{Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}},
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        Equal.cong(
          List<&2, Item>,
          Maybe<&2, Node>,
          ys => Some{Node{l, left, ys}},
          xs,
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          Equal.sym(List<&2, Item>, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)), xs, Mst.pre_post(xs, k))
        )
      )
      +oN = Equal.trans(
        Bool,
        Mst.opens(Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}, Room{ur, lo, hi}),
        Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}),
        True{},
        Equal.cong(
          List<&2, Item>,
          Bool,
          ys => Mst.opens(Node{l, left, ys}, Room{ur, lo, hi}),
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          xs,
          Mst.pre_post(xs, k)
        ),
        Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
      )
      Mst.ins_ok.here(
        ~S,
        ~fetch,
        Mst.post(xs, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        l,
        left,
        Mst.pre(xs, k),
        eN,
        oN,
        Mst.pre_all_lt(xs, k),
        Mst.post_head(xs, k),
        a,
        bb,
        Mst.level_ok(k, l, Equal.trans(Nat, Key.level(k), ll, l, el, Equal.sym(Nat, l, ll, Mst.nat_eq(l, ll)(ec))))
      )
    case GT{}:
      %Equal.sym(
        Part,
        Mst.part(xs, left, k, []),
        Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
        Mst.part_eq(xs, left, k, [])
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        Some{v},
        Shared.Bool.when(
          Maybe<&2, Edit>,
          Part.hits(_, k),
          u => None{},
          u => Mst.with_gap(l, left, _, Mst.insert(~S, ~fetch, p, s, Part.room(_, l, lo, hi), Part.gap(_), k, v, ll))
        )
      )
      +eN = Equal.trans(
        Maybe<&2, Node>,
        Mst.node(~S, ~fetch, s, h),
        Some{Node{l, left, xs}},
        Some{Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}},
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        Equal.cong(
          List<&2, Item>,
          Maybe<&2, Node>,
          ys => Some{Node{l, left, ys}},
          xs,
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          Equal.sym(List<&2, Item>, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)), xs, Mst.pre_post(xs, k))
        )
      )
      +oN = Equal.trans(
        Bool,
        Mst.opens(Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}, Room{ur, lo, hi}),
        Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}),
        True{},
        Equal.cong(
          List<&2, Item>,
          Bool,
          ys => Mst.opens(Node{l, left, ys}, Room{ur, lo, hi}),
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          xs,
          Mst.pre_post(xs, k)
        ),
        Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
      )
      Mst.ins_ok.gt(
        ~S,
        ~fetch,
        Part.hits(Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)}, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        ll,
        l,
        left,
        Mst.pre(xs, k),
        Mst.post(xs, k),
        {==},
        eN,
        oN,
        Mst.pre_all_lt(xs, k),
        Mst.post_head(xs, k),
        el,
        ec,
        a,
        bb,
        ih
      )

# an insert of k at the node na of the hash h
def Mst.ins_ok.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}) == na: Maybe<&2, Node>},
  +el: {Key.level(k) == ll: Nat},
  +lt: {Nat.is_lt(ll, ur) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Nat.is_lt(ll, ur2) == True{}: Bool
  } -> {Bound.after(lo2, k) == True{}: Bool} -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    Some{v},
    Mst.insert(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, v, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  Some{v},
  Mst.insert.at(
    na,
    h,
    Room{ur, lo, hi},
    k,
    v,
    ll,
    c2 => Mst.split(~S, ~fetch, p, s, Room{ur, lo, hi}, c2, k),
    r2 => c2 => Mst.split(~S, ~fetch, p, s, r2, c2, k),
    r2 => c2 => Mst.insert(~S, ~fetch, p, s, r2, c2, k, v, ll)
  )
):
  match na:
    case None{}:
      Unit{}
    case Some{Node{+l, +left, +xs}}:
      Mst.ins_ok.node(~S, ~fetch, Nat.cmp(l, ll), s, p, h, ur, lo, hi, k, v, ll, l, left, xs, {==}, en, el, lt, a, bb, ih)

# a write of k as v to a tree in its room, around k and above the level of
# k, reads as Mst.InsOk says
def Mst.ins_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +s: S,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ll: Nat
) -> {Key.level(k) == ll: Nat} -> {Nat.is_lt(ll, ur) == True{}: Bool} -> {Bound.after(lo, k) == True{}: Bool} -> {
  Bound.before(k, hi) == True{}: Bool
} -> Mst.InsOk(~S, ~fetch, s, ur, lo, hi, m, k, Some{v}, Mst.insert(~S, ~fetch, f, s, Room{ur, lo, hi}, m, k, v, ll)):
  match f m:
    case 0n None{}:
      +el => +lt => +a => +bb => Mst.ins_ok.none(~S, ~fetch, s, ur, lo, hi, k, v, ll, el, lt, a, bb)
    case 1n+q None{}:
      +el => +lt => +a => +bb => Mst.ins_ok.none(~S, ~fetch, s, ur, lo, hi, k, v, ll, el, lt, a, bb)
    case 0n Some{h}:
      +el => +lt => +a => +bb => Unit{}
    case 1n+(+p) Some{+h}:
      +el => +lt => +a => +bb => Mst.ins_ok.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        v,
        ll,
        {==},
        el,
        lt,
        a,
        bb,
        +ur2 => +lo2 => +hi2 => +m2 => Mst.ins_ok(~S, ~fetch, p, m2, s, ur2, lo2, hi2, k, v, ll)
      )

# a room is at least as wide as itself
def Mst.room_le_refl(r: Room) -> {Mst.room_le(r, r) == True{}: Bool}:
  match r:
    case Room{+u, +lo, +hi}:
      Mst.room_le_of(u, lo, lo, hi, hi, Mst.lo_le_refl(lo), Mst.hi_le_refl(hi))

# the room of a pick that goes down is of the level of the node
def Mst.PickUp(l: Nat, p: Pick) -> Data:
  match p:
    case Pick.Hit{v}:
      Unit
    case Pick.Down{m, r}:
      {Mst.room_up(r) == l: Nat}

# a pick goes down into a room of the level of the node
def Mst.pick_up(
  +xs: List<&2, Item>,
  +prev: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> Mst.PickUp(l, Mst.pick(xs, prev, l, lo, hi, k)):
  match xs:
    case Nil{}:
      {==}
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.case_cmp(
        c => Mst.PickUp(
          l,
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k))
          )
        ),
        Key.cmp(k, ik),
        +q => {==},
        +q => Unit{},
        +q => Mst.pick_up(rest, r, l, Some{ik}, hi, k)
      )

# a read of a node whose pick of k goes down to a subtree where k is absent
# finds k absent
def Mst.del_same(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g: Nat,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +k: List<&2, U32>,
  +p: Nat,
  +m: Maybe<&2, Hashes.Hash>,
  +a: Maybe<&2, List<&2, U32>>,
  +b: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, xs}, Room{u, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(u, g) == True{}: Bool},
  +ep: {Mst.pick(xs, left, l, lo, hi, k) == Pick.Down{m, Room{l, a, b}}: Pick},
  +ab: {Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{l, a, b}, m, k)) == True{}: Bool}
) -> {Look.known(Mst.look.go(~S, ~fetch, g, s, Room{u, lo, hi}, Some{h}, k)) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  Mst.new_down(
    ~S,
    ~fetch,
    g,
    s,
    h,
    u,
    lo,
    hi,
    l,
    left,
    xs,
    k,
    None{},
    m,
    a,
    b,
    eN,
    oN,
    fu,
    ep,
    +g4 => +fl => Mst.look.wide(
      ~S,
      ~fetch,
      g4,
      p,
      m,
      s,
      Room{l, a, b},
      Room{l, a, b},
      k,
      None{},
      Mst.hop_of(~S, ~fetch, s, m, Room{l, a, b}, Room{l, a, b}, Mst.room_le_refl(Room{l, a, b})),
      Mst.room_bounds(Room{l, a, b}, Room{l, a, b})(Mst.room_le_refl(Room{l, a, b})),
      fl
    )(Look.absent_known(Mst.look.go(~S, ~fetch, p, s, Room{l, a, b}, m, k))(ab))
  )

# a tree read with more fuel in the same room tells the same
def Mst.del_keep(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g2: Nat,
  +s: S,
  +m: Maybe<&2, Hashes.Hash>,
  +r: Room,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +fu: {Nat.is_le(Mst.room_up(r), g2) == True{}: Bool}
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, r, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, r, m, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  Mst.look.wide(
    ~S,
    ~fetch,
    g2,
    g1,
    m,
    s,
    r,
    r,
    k2,
    x,
    Mst.hop_of(~S, ~fetch, s, m, r, r, Mst.room_le_refl(r)),
    Mst.room_bounds(r, r)(Mst.room_le_refl(r)),
    fu
  )

# a delete that leaves the tree as it is, once a read finds k absent (bb)
def Mst.del_ok.when(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  bb: Bool,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  -t: Look,
  +ebb: {Look.is_absent(t) == bb: Bool},
  d1: {Look.is_absent(t) == True{}: Bool} -> @g: Nat -> {Nat.is_le(ur, g) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g, s, Room{ur, lo, hi}, Some{h}, k)) == Some{None{}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, None{}, Shared.Maybe.when(Edit, bb, u => Some{Edit{Some{h}, []}})):
  match bb:
    case False{}:
      Unit{}
    case True{}:
      +hold => (
        d1(ebb),
        +k2 => +x => +g1 => +g2 => +ne => +fu => Mst.del_keep(~S, ~fetch, g1, g2, s, Some{h}, Room{ur, lo, hi}, k2, x, fu)
      )

# a delete from an empty tree
def Mst.del_ok.none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> Mst.InsOk(~S, ~fetch, s, ur, lo, hi, None{}, k, None{}, Some{Edit{None{}, []}}):
  +hold => (
    +g => +fu => Equal.cong(
      Look,
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      Look.known,
      Mst.look.go(~S, ~fetch, g, s, Room{ur, lo, hi}, None{}, k),
      Look.Absent{},
      Mst.look_none(~S, ~fetch, g, s, Room{ur, lo, hi}, k)
    ),
    +k2 => +x => +g1 => +g2 => +ne => +fu => Mst.none_kept(~S, ~fetch, g1, g2, s, Room{ur, lo, hi}, Room{ur, lo, hi}, k2, x)
  )

# items with one item k taken out fit as before
def Mst.fit_del(
  +pre: List<&2, Item>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Items.fit(List.append(&2, Item, pre, Item{k, iv, r} <> rest), lo, hi) == True{}: Bool} -> {
  Items.fit(List.append(&2, Item, pre, rest), lo, hi) == True{}: Bool
}:
  +f =>
    +both = Equal.trans(
      Bool,
      Bool.and(Items.fit(pre, lo, hi), Items.fit(Item{k, iv, r} <> rest, Items.last_key(pre, lo), hi)),
      Items.fit(List.append(&2, Item, pre, Item{k, iv, r} <> rest), lo, hi),
      True{},
      Equal.sym(
        Bool,
        Items.fit(List.append(&2, Item, pre, Item{k, iv, r} <> rest), lo, hi),
        Bool.and(Items.fit(pre, lo, hi), Items.fit(Item{k, iv, r} <> rest, Items.last_key(pre, lo), hi)),
        Mst.fit_append(pre, Item{k, iv, r} <> rest, lo, hi)
      ),
      f
    )
    +fk = Shared.Bool.and_true_right(Items.fit(pre, lo, hi), Items.fit(Item{k, iv, r} <> rest, Items.last_key(pre, lo), hi), both)
    Equal.trans(
      Bool,
      Items.fit(List.append(&2, Item, pre, rest), lo, hi),
      Bool.and(Items.fit(pre, lo, hi), Items.fit(rest, Items.last_key(pre, lo), hi)),
      True{},
      Mst.fit_append(pre, rest, lo, hi),
      Shared.Bool.and_both(
        Items.fit(pre, lo, hi),
        Items.fit(rest, Items.last_key(pre, lo), hi),
        Shared.Bool.and_true_left(Items.fit(pre, lo, hi), Items.fit(Item{k, iv, r} <> rest, Items.last_key(pre, lo), hi), both),
        Mst.fit_wide(
          rest,
          Some{k},
          Items.last_key(pre, lo),
          hi,
          hi,
          Mst.lo_le_key(Items.last_key(pre, lo), k)(
            Shared.Bool.and_true_left(
              Bound.after(Items.last_key(pre, lo), k),
              Bound.before(k, hi),
              Shared.Bool.and_true_left(
                Bool.and(Bound.after(Items.last_key(pre, lo), k), Bound.before(k, hi)),
                Items.fit(rest, Some{k}, hi),
                fk
              )
            )
          ),
          Mst.hi_le_refl(hi)
        )(Shared.Bool.and_true_right(Bool.and(Bound.after(Items.last_key(pre, lo), k), Bound.before(k, hi)), Items.fit(rest, Some{k}, hi), fk))
      )
    )

# the items after k of items that fit, k among them, fit after k
def Mst.fit_rest(
  +pre: List<&2, Item>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Items.fit(List.append(&2, Item, pre, Item{k, iv, r} <> rest), lo, hi) == True{}: Bool} -> {Items.fit(rest, Some{k}, hi) == True{}: Bool}:
  +f => Shared.Bool.and_true_right(
    Bool.and(Bound.after(Items.last_key(pre, lo), k), Bound.before(k, hi)),
    Items.fit(rest, Some{k}, hi),
    Mst.post_fit(pre, Item{k, iv, r} <> rest, lo, hi)(f)
  )

# what a merge reads below k (the first part of Mst.MergeRead)
def Mst.MergeLo(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -u: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -hi: Maybe<&2, List<&2, U32>>,
  -ma: Maybe<&2, Hashes.Hash>,
  -nc: Maybe<&2, Hashes.Hash>
) -> Type:
  @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {Key.cmp(k2, k) == LT{}: Cmp} -> {
    Nat.is_le(u, g2) == True{}: Bool
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, lo, Some{k}}, ma, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# what a merge reads above k (the second part of Mst.MergeRead)
def Mst.MergeHi(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -s: S,
  -u: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -k: List<&2, U32>,
  -hi: Maybe<&2, List<&2, U32>>,
  -mb: Maybe<&2, Hashes.Hash>,
  -nc: Maybe<&2, Hashes.Hash>
) -> Type:
  @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> @u1: Nat -> @g1: Nat -> @g2: Nat -> {Key.cmp(k2, k) == GT{}: Cmp} -> {
    Nat.is_le(u, g2) == True{}: Bool
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{u1, Some{k}, hi}, mb, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{u, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# a node with the item k taken out and the subtrees beside it merged reads a
# key above k as the node did, but past k, as ih says
def Mst.del_hi(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  g1: Nat,
  g2: Nat,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  -x: Maybe<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +eD: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}}: Maybe<&2, Node>
  },
  +oD: {
    Mst.opens(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, Room{ur, lo, hi})
      == True{}: Bool
  },
  +ps: {Mst.passes(pre, k2) == True{}: Bool},
  +c: {Key.cmp(k2, k) == GT{}: Cmp},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  ih: @g3: Nat -> @g4: Nat -> {Nat.is_le(l, g4) == True{}: Bool} -> {
    Look.known(Mst.look.go(~S, ~fetch, g3, s, Room{l, Some{k}, Items.head_key(rest, hi)}, r, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {
    Look.known(Mst.look.go(~S, ~fetch, g4, s, Room{l, Items.last_key(pre, lo), Items.head_key(rest, hi)}, nc, k2))
      == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }
) -> {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match g1 g2:
    case 0n y:
      +e => Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, y, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, e)
      )
    case 1n+p1 0n:
      +e => Empty.absurd(
        {Look.known(Look.Missing{hn}) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.opens_fuel(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ur, lo, hi, oD, fu)
      )
    case 1n+(+p1) 1n+(+p2):
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p1, s, Room{ur, lo, hi}, Some{h}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, pre, Item{k, iv, r} <> rest), left, l, lo, hi, k2),
          h,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
        ),
        Mst.look_node(~S, ~fetch, p1, s, h, ur, lo, hi, l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest), k2, eN, oN)
      ): (
        {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
          -> {Look.known(Mst.look.go(~S, ~fetch, 1n+p2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Look,
        Mst.look.go(~S, ~fetch, 1n+p2, s, Room{ur, lo, hi}, Some{hn}, k2),
        Mst.look.pick(
          Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), rest), Mst.end_left(pre, left, nc), l, lo, hi, k2),
          hn,
          l,
          k2,
          m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
        ),
        Mst.look_node(
          ~S,
          ~fetch,
          p2,
          s,
          hn,
          ur,
          lo,
          hi,
          l,
          Mst.end_left(pre, left, nc),
          List.append(&2, Item, Mst.set_last(pre, nc), rest),
          k2,
          eD,
          oD
        )
      ): (
        {
          Look.known(
            Mst.look.pick(
              Mst.pick(List.append(&2, Item, pre, Item{k, iv, r} <> rest), left, l, lo, hi, k2),
              h,
              l,
              k2,
              m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)
            )
          )
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {Look.known(_) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, pre, Item{k, iv, r} <> rest), left, l, lo, hi, k2),
        Mst.pick(rest, r, l, Some{k}, hi, k2),
        Equal.trans(
          Pick,
          Mst.pick(List.append(&2, Item, pre, Item{k, iv, r} <> rest), left, l, lo, hi, k2),
          Mst.pick(Item{k, iv, r} <> rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2),
          Mst.pick(rest, r, l, Some{k}, hi, k2),
          Mst.pick_passes(pre, Item{k, iv, r} <> rest, left, l, lo, hi, k2)(ps),
          Mst.pick_past_k(k, iv, r, rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k2, c)
        )
      ): (
        {
          Look.known(Mst.look.pick(_, h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(
              Mst.look.pick(
                Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), rest), Mst.end_left(pre, left, nc), l, lo, hi, k2),
                hn,
                l,
                k2,
                m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)
              )
            )
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      %Equal.sym(
        Pick,
        Mst.pick(List.append(&2, Item, Mst.set_last(pre, nc), rest), Mst.end_left(pre, left, nc), l, lo, hi, k2),
        Mst.pick(rest, nc, l, Items.last_key(pre, lo), hi, k2),
        Mst.pick_set_passes(pre, nc, rest, left, l, lo, hi, k2, ps)
      ): (
        {
          Look.known(Mst.look.pick(Mst.pick(rest, r, l, Some{k}, hi, k2), h, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p1, s, r2, m2, k2)))
            == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          -> {
            Look.known(Mst.look.pick(_, hn, l, k2, m2 => r2 => Mst.look.go(~S, ~fetch, p2, s, r2, m2, k2)))
              == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
      )
      Mst.gap_kept.first(
        ~S,
        ~fetch,
        Mst.stops_first(rest, k2),
        p1,
        p2,
        s,
        rest,
        r,
        nc,
        l,
        Some{k},
        Items.last_key(pre, lo),
        hi,
        hi,
        h,
        hn,
        k2,
        x,
        {==},
        Mst.hi_le_refl(hi),
        Mst.opens_fl(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ur, lo, hi, p2, oD, fu),
        ih
      )

# a delete of the one item k of a node, whose merged subtrees rise in its
# place, for a key other than k, by how it compares to k (c)
def Mst.del_ok.rise.k2(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +x: Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g2: Nat,
  +ec: {Key.cmp(k2, k) == c: Cmp},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, [Item{k, iv, r}]}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, [Item{k, iv, r}]}, Room{ur, lo, hi}) == True{}: Bool},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool},
  +e: {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  mlo: Mst.MergeLo(~S, ~fetch, s, ur, lo, k, hi, left, nc),
  mhi: Mst.MergeHi(~S, ~fetch, s, ur, lo, k, hi, r, nc)
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match c:
    case LT{}:
      Mst.old_down(
        ~S,
        ~fetch,
        {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        g1,
        s,
        h,
        ur,
        lo,
        hi,
        l,
        left,
        [Item{k, iv, r}],
        k2,
        x,
        left,
        Room.of(l, lo, Some{k}),
        eN,
        oN,
        Mst.pick_first([Item{k, iv, r}], left, l, lo, hi, k2)(Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k2, k), LT{}, ec)),
        +g3 => +e3 => mlo(k2)(x)(l)(g3)(g2)(ec)(fu)(e3)
      )(e)
    case GT{}:
      Mst.old_down(
        ~S,
        ~fetch,
        {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        g1,
        s,
        h,
        ur,
        lo,
        hi,
        l,
        left,
        [Item{k, iv, r}],
        k2,
        x,
        r,
        Room.of(l, Some{k}, hi),
        eN,
        oN,
        Mst.pick_all([Item{k, iv, r}], left, l, lo, hi, k2)(
          Shared.Bool.and_both(Cmp.is_gt(Key.cmp(k2, k)), True{}, Equal.cong(Cmp, Bool, Cmp.is_gt, Key.cmp(k2, k), GT{}, ec), {==})
        ),
        +g3 => +e3 => mhi(k2)(x)(l)(g3)(g2)(ec)(fu)(e3)
      )(e)
    case EQ{}:
      Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, nc, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.ne_eq(k2, k, ne, ec)
      )

# what a delete of the one item k of a node reads, from what the merge of the
# subtrees beside k reads (tri)
def Mst.del_ok.rise.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, [Item{k, iv, r}]}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, [Item{k, iv, r}]}, Room{ur, lo, hi}) == True{}: Bool},
  tri: Mst.MergeRead(~S, ~fetch, s, ur, lo, k, hi, left, r, nc)
) -> Mst.InsRead(~S, ~fetch, s, ur, lo, hi, Some{h}, k, None{}, nc):
  (mlo, r3) = tri
  (mhi, mk) = r3
  (
    +g => +fu => mk(g)(fu),
    +k2 => +x => +g1 => +g2 => +ne => +fu => +e => Mst.del_ok.rise.k2(
      ~S,
      ~fetch,
      Key.cmp(k2, k),
      s,
      h,
      ur,
      lo,
      hi,
      k,
      iv,
      r,
      l,
      left,
      nc,
      k2,
      x,
      g1,
      g2,
      {==},
      eN,
      oN,
      fu,
      ne,
      e,
      mlo,
      mhi
    )
  )

# what a delete of the one item k of a node reads, from what its merge reads
# (bi)
def Mst.del_ok.rise.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, [Item{k, iv, r}]}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, [Item{k, iv, r}]}, Room{ur, lo, hi}) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  bi: ({Mst.lvl(~S, ~fetch, s, left, l) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, r, l) == True{}: Bool})
    & Mst.MergeMain(~S, ~fetch, s, lo, k, hi, left, r, nc)
) -> Mst.InsRead(~S, ~fetch, s, ur, lo, hi, Some{h}, k, None{}, nc):
  (lvs, main2) = bi
  (lva, lvb) = lvs
  +lt = Shared.Nat.lt_weak(l, ur)(Mst.opens_lt(l, left, [Item{k, iv, r}], Room{ur, lo, hi})(oN))
  Mst.del_ok.rise.go(
    ~S,
    ~fetch,
    s,
    h,
    ur,
    lo,
    hi,
    k,
    iv,
    r,
    l,
    left,
    nc,
    eN,
    oN,
    main2(ur)(Mst.lvl_mono(~S, ~fetch, s, left, l, ur)(lva)(lt))(Mst.lvl_mono(~S, ~fetch, s, r, l, ur)(lvb)(lt))(a)(bb)
  )

# a delete of k from a node of its level that holds more items, for a key
# other than k, by how it compares to k (c)
def Mst.del_ok.store.k2(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +h: Hashes.Hash,
  +hn: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +k2: List<&2, U32>,
  +x: Maybe<&2, List<&2, U32>>,
  +g1: Nat,
  +g2: Nat,
  +ec: {Key.cmp(k2, k) == c: Cmp},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +eD: {
    Mst.node(~S, ~fetch, s, hn)
      == Some{Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}}: Maybe<&2, Node>
  },
  +oD: {
    Mst.opens(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, Room{ur, lo, hi})
      == True{}: Bool
  },
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +fr: {Items.fit(rest, Some{k}, hi) == True{}: Bool},
  +fu: {Nat.is_le(ur, g2) == True{}: Bool},
  +ne: {Cmp.is_eq(Key.cmp(k2, k)) == False{}: Bool},
  +e: {Look.known(Mst.look.go(~S, ~fetch, g1, s, Room{ur, lo, hi}, Some{h}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  mlo: Mst.MergeLo(~S, ~fetch, s, l, Items.last_key(pre, lo), k, Items.head_key(rest, hi), Mst.last(pre, left), nc),
  mhi: Mst.MergeHi(~S, ~fetch, s, l, Items.last_key(pre, lo), k, Items.head_key(rest, hi), r, nc)
) -> {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match c:
    case LT{}:
      Mst.gap_lo(
        ~S,
        ~fetch,
        g1,
        g2,
        s,
        h,
        hn,
        ur,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        pre,
        Item{k, iv, r} <> rest,
        rest,
        nc,
        hi,
        k2,
        x,
        eN,
        oN,
        eD,
        oD,
        Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k2, k), LT{}, ec),
        Mst.stops_first_fit(rest, k, hi, k2)(fr)(Mst.le_of_lt(Key.cmp(k2, k))(ec)),
        fu,
        +g3 => +g4 => +fl => +e3 => mlo(k2)(x)(l)(g3)(g4)(ec)(fl)(e3)
      )(e)
    case GT{}:
      Mst.del_hi(
        ~S,
        ~fetch,
        g1,
        g2,
        s,
        h,
        hn,
        ur,
        lo,
        hi,
        k,
        iv,
        r,
        l,
        left,
        pre,
        rest,
        nc,
        k2,
        x,
        eN,
        oN,
        eD,
        oD,
        Mst.passes_of_lt(pre, k, k2)(all)(Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(k, k2), LT{}, Mst.key_gt_lt(k2, k)(ec))),
        ec,
        fu,
        +g3 => +g4 => +fl => +e3 => mhi(k2)(x)(l)(g3)(g4)(ec)(fl)(e3)
      )(e)
    case EQ{}:
      Empty.absurd(
        {Look.known(Mst.look.go(~S, ~fetch, g2, s, Room{ur, lo, hi}, Some{hn}, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
        Mst.ne_eq(k2, k, ne, ec)
      )

# what a delete of k from a node of its level that holds more items reads,
# from what the merge of the subtrees beside k reads (tri)
def Mst.del_ok.store.go(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +ne: {List.is_empty(&2, Item, List.append(&2, Item, pre, rest)) == False{}: Bool},
  +hold: {
    Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []) <> ns)
      == True{}: Bool
  },
  tri: Mst.MergeRead(~S, ~fetch, s, l, Items.last_key(pre, lo), k, Items.head_key(rest, hi), Mst.last(pre, left), r, nc)
) -> Mst.InsRead(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Some{Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []))}
):
  (mlo, r3) = tri
  (mhi, mk) = r3
  +fr = Mst.fit_rest(pre, k, iv, r, rest, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest), ur, lo, hi, oN))
  +eD = Mst.node_code(
    ~S,
    ~fetch,
    s,
    Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)},
    Mst.holds_head(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []), ns, hold)
  )
  +oD = Mst.opens_set_last(l, left, Mst.end_left(pre, left, nc), pre, nc, rest, Room{ur, lo, hi})(
    Mst.opens_of(
      l,
      left,
      List.append(&2, Item, pre, rest),
      ur,
      lo,
      hi,
      Mst.opens_lt(l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest), Room{ur, lo, hi})(oN),
      ne,
      Mst.fit_del(pre, k, iv, r, rest, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest), ur, lo, hi, oN))
    )
  )
  (
    +g => +fu => Mst.gap_k(
      ~S,
      ~fetch,
      g,
      s,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, [])),
      ur,
      lo,
      hi,
      l,
      left,
      pre,
      rest,
      nc,
      k,
      None{},
      eD,
      oD,
      fu,
      Mst.passes_of_all_lt(pre, k)(all),
      Mst.stops_first_fit(rest, k, hi, k)(fr)(Mst.le_refl_key(k)),
      +g4 => +fl => mk(g4)(fl)
    ),
    +k2 => +x => +g1 => +g2 => +ne2 => +fu => +e => Mst.del_ok.store.k2(
      ~S,
      ~fetch,
      Key.cmp(k2, k),
      s,
      h,
      Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, [])),
      ur,
      lo,
      hi,
      k,
      iv,
      r,
      l,
      left,
      pre,
      rest,
      nc,
      k2,
      x,
      g1,
      g2,
      {==},
      eN,
      oN,
      eD,
      oD,
      all,
      fr,
      fu,
      ne2,
      e,
      mlo,
      mhi
    )
  )

# what a delete of k from a node of its level that holds more items reads,
# from what its merge reads (bi)
def Mst.del_ok.store.read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +ne: {List.is_empty(&2, Item, List.append(&2, Item, pre, rest)) == False{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  +hold: {
    Depots.Depot.holds(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []) <> ns)
      == True{}: Bool
  },
  bi: ({Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, r, l) == True{}: Bool})
    & Mst.MergeMain(~S, ~fetch, s, Items.last_key(pre, lo), k, Items.head_key(rest, hi), Mst.last(pre, left), r, nc)
) -> Mst.InsRead(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Some{Hashes.Sha.hash(Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []))}
):
  (lvs, main2) = bi
  (lva, lvb) = lvs
  Mst.del_ok.store.go(
    ~S,
    ~fetch,
    s,
    h,
    ur,
    lo,
    hi,
    k,
    iv,
    r,
    l,
    left,
    pre,
    rest,
    nc,
    ns,
    eN,
    oN,
    all,
    ne,
    hold,
    main2(l)(lva)(lvb)(Mst.last_below(pre, lo, k)(all)(a))(
      Mst.before_head(rest, k, hi)(
        Mst.fit_rest(pre, k, iv, r, rest, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest), ur, lo, hi, oN))
      )(bb)
    )
  )

# a delete of k from a node of its level that holds more items, once the
# subtrees beside k are merged into nc
def Mst.del_ok.store(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +nc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +ne: {List.is_empty(&2, Item, List.append(&2, Item, pre, rest)) == False{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ihm: {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool} -> (
    ({Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, r, l) == True{}: Bool})
      & Mst.MergeMain(~S, ~fetch, s, Items.last_key(pre, lo), k, Items.head_key(rest, hi), Mst.last(pre, left), r, nc)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Some{Mst.make(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ns)}
):
  %Equal.sym(
    Edit,
    Mst.make(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ns),
    Mst.store(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, ns),
    Mst.make_full(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ns)(
      Equal.trans(
        Bool,
        List.is_empty(&2, Item, List.append(&2, Item, Mst.set_last(pre, nc), rest)),
        List.is_empty(&2, Item, List.append(&2, Item, pre, rest)),
        False{},
        Mst.empty_set_last_append(pre, nc, rest),
        ne
      )
    )
  ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, None{}, Some{_})
  +hold => Mst.del_ok.store.read(
    ~S,
    ~fetch,
    s,
    h,
    ur,
    lo,
    hi,
    k,
    iv,
    r,
    l,
    left,
    pre,
    rest,
    nc,
    ns,
    eN,
    oN,
    all,
    ne,
    a,
    bb,
    hold,
    ihm(Mst.holds_tail(~S, ~fetch, s, Node.code(Node{l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest)}, []), ns, hold))
  )

# a delete of k from a node of its level, by the items around k
def Mst.del_ok.hit.mk(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  pre: List<&2, Item>,
  rest: List<&2, Item>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +nc: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ihm: {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool} -> (
    ({Mst.lvl(~S, ~fetch, s, Mst.last(pre, left), l) == True{}: Bool} & {Mst.lvl(~S, ~fetch, s, r, l) == True{}: Bool})
      & Mst.MergeMain(~S, ~fetch, s, Items.last_key(pre, lo), k, Items.head_key(rest, hi), Mst.last(pre, left), r, nc)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Some{Mst.make(l, Mst.end_left(pre, left, nc), List.append(&2, Item, Mst.set_last(pre, nc), rest), ns)}
):
  match pre rest:
    case Nil{} Nil{}:
      +hold => Mst.del_ok.rise.read(~S, ~fetch, s, h, ur, lo, hi, k, iv, r, l, left, nc, eN, oN, a, bb, ihm(hold))
    case Nil{} Con{+y, +ys}:
      Mst.del_ok.store(~S, ~fetch, s, h, ur, lo, hi, k, iv, r, l, left, [], y <> ys, nc, ns, eN, oN, all, {==}, a, bb, ihm)
    case Con{+x0, +r0} q:
      Mst.del_ok.store(~S, ~fetch, s, h, ur, lo, hi, k, iv, r, l, left, x0 <> r0, q, nc, ns, eN, oN, all, {==}, a, bb, ihm)

# a delete of k from a node of its level that holds k, once the subtrees
# beside k are merged (res)
def Mst.del_ok.hit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  res: Maybe<&2, Edit>,
  +s: S,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +rest: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ihm: Mst.MergeOk(~S, ~fetch, s, l, Items.last_key(pre, lo), k, l, Items.head_key(rest, hi), Mst.last(pre, left), r, res)
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Mst.with_gap(l, left, Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), rest}, res)
):
  match res:
    case None{}:
      Unit{}
    case Some{Edit{+nc, +ns}}:
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Mst.left(List.reverse.go(&2, Item, pre, []), left, nc),
        Mst.end_left(pre, left, nc),
        Mst.left_rev(pre, left, nc)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Some{Mst.make(l, _, Mst.rejoin(List.reverse.go(&2, Item, pre, []), nc, rest), ns)}
      )
      %Equal.sym(
        List<&2, Item>,
        Mst.rejoin(List.reverse.go(&2, Item, pre, []), nc, rest),
        List.append(&2, Item, Mst.set_last(pre, nc), rest),
        Mst.rejoin_rev(pre, nc, rest)
      ): Mst.InsOk(~S, ~fetch, s, ur, lo, hi, Some{h}, k, None{}, Some{Mst.make(l, Mst.end_left(pre, left, nc), _, ns)})
      Mst.del_ok.hit.mk(~S, ~fetch, pre, rest, s, h, ur, lo, hi, k, iv, r, l, left, nc, ns, eN, oN, all, a, bb, ihm)

# a delete of k at a node of a lower level, by the pick of k there (pk)
def Mst.del_ok.lacks(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  pk: Pick,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +ep: {Mst.pick(xs, left, l, lo, hi, k) == pk: Pick},
  pu: Mst.PickUp(l, pk),
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Shared.Maybe.when(Edit, Mst.delete.lacks(pk, r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)), u => Some{Edit{Some{h}, []}})
):
  match pk:
    case Pick.Hit{v}:
      Unit{}
    case Pick.Down{+m, Room{+u2, +a, +b}}:
      +pe = pu
      Mst.del_ok.when(
        ~S,
        ~fetch,
        Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{u2, a, b}, m, k)),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        Mst.look.go(~S, ~fetch, p, s, Room{u2, a, b}, m, k),
        {==},
        +ab => +g => +fu => Mst.del_same(
          ~S,
          ~fetch,
          g,
          s,
          h,
          ur,
          lo,
          hi,
          l,
          left,
          xs,
          k,
          p,
          m,
          a,
          b,
          eN,
          oN,
          fu,
          Equal.trans(
            Pick,
            Mst.pick(xs, left, l, lo, hi, k),
            Pick.Down{m, Room{u2, a, b}},
            Pick.Down{m, Room{l, a, b}},
            ep,
            Equal.cong(Nat, Pick, n => Pick.Down{m, Room{n, a, b}}, u2, l, pe)
          ),
          Equal.trans(
            Bool,
            Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{l, a, b}, m, k)),
            Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{u2, a, b}, m, k)),
            True{},
            Equal.cong(Nat, Bool, n => Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{n, a, b}, m, k)), l, u2, Equal.sym(Nat, u2, l, pe)),
            ab
          )
        )
      )

# a delete of k from a node of its level whose first item from k on is ik, by
# whether ik is k (b)
def Mst.del_ok.here.b(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b: Bool,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +eb: {Cmp.is_eq(Key.cmp(ik, k)) == b: Bool},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(Item{ik, iv, r} <> rest, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Shared.Bool.when(
    Maybe<&2, Edit>,
    b,
    u => Mst.with_gap(
      l,
      left,
      Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), rest},
      Mst.merge(
        ~S,
        ~fetch,
        p,
        s,
        Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Some{ik}},
        Room{l, Some{ik}, Items.head_key(rest, hi)},
        Mst.last(pre, left),
        r
      )
    ),
    u => Mst.delete.none(
      h,
      Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Some{ik}},
      Mst.last(pre, left),
      r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)
    )
  )
):
  match b:
    case True{}:
      +eik = Mst.key_eq(ik, k)(Shared.Cmp.is_eq_sound(Key.cmp(ik, k))(eb))
      %Equal.sym(List<&2, U32>, ik, k, eik): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.with_gap(
          l,
          left,
          Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), rest},
          Mst.merge(
            ~S,
            ~fetch,
            p,
            s,
            Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Some{_}},
            Room{l, Some{_}, Items.head_key(rest, hi)},
            Mst.last(pre, left),
            r
          )
        )
      )
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.with_gap(
          l,
          left,
          Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), rest},
          Mst.merge(~S, ~fetch, p, s, Room{l, _, Some{k}}, Room{l, Some{k}, Items.head_key(rest, hi)}, Mst.last(pre, left), r)
        )
      )
      Mst.del_ok.hit(
        ~S,
        ~fetch,
        Mst.merge(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Some{k}}, Room{l, Some{k}, Items.head_key(rest, hi)}, Mst.last(pre, left), r),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        iv,
        r,
        l,
        left,
        pre,
        rest,
        Equal.trans(
          Maybe<&2, Node>,
          Mst.node(~S, ~fetch, s, h),
          Some{Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}},
          Some{Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}},
          eN,
          Equal.cong(List<&2, U32>, Maybe<&2, Node>, z => Some{Node{l, left, List.append(&2, Item, pre, Item{z, iv, r} <> rest)}}, ik, k, eik)
        ),
        Equal.trans(
          Bool,
          Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{k, iv, r} <> rest)}, Room{ur, lo, hi}),
          Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest)}, Room{ur, lo, hi}),
          True{},
          Equal.cong(
            List<&2, U32>,
            Bool,
            z => Mst.opens(Node{l, left, List.append(&2, Item, pre, Item{z, iv, r} <> rest)}, Room{ur, lo, hi}),
            k,
            ik,
            Equal.sym(List<&2, U32>, ik, k, eik)
          ),
          oN
        ),
        all,
        a,
        bb,
        Mst.merge_ok(~S, ~fetch, p, Mst.last(pre, left), r, s, l, Items.last_key(pre, lo), k, l, Items.head_key(rest, hi))
      )
    case False{}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.delete.none(h, Room{l, _, Some{ik}}, Mst.last(pre, left), r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k))
      )
      Mst.del_ok.when(
        ~S,
        ~fetch,
        Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Some{ik}}, Mst.last(pre, left), k)),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        Mst.look.go(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Some{ik}}, Mst.last(pre, left), k),
        {==},
        +ab => +g => +fu => Mst.del_same(
          ~S,
          ~fetch,
          g,
          s,
          h,
          ur,
          lo,
          hi,
          l,
          left,
          List.append(&2, Item, pre, Item{ik, iv, r} <> rest),
          k,
          p,
          Mst.last(pre, left),
          Items.last_key(pre, lo),
          Some{ik},
          eN,
          oN,
          fu,
          Equal.trans(
            Pick,
            Mst.pick(List.append(&2, Item, pre, Item{ik, iv, r} <> rest), left, l, lo, hi, k),
            Mst.pick(Item{ik, iv, r} <> rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k),
            Pick.Down{Mst.last(pre, left), Room{l, Items.last_key(pre, lo), Some{ik}}},
            Mst.pick_passes(pre, Item{ik, iv, r} <> rest, left, l, lo, hi, k)(Mst.passes_of_all_lt(pre, k)(all)),
            Mst.pick_first(Item{ik, iv, r} <> rest, Mst.last(pre, left), l, Items.last_key(pre, lo), hi, k)(
              Mst.stops_first_fit(Item{ik, iv, r} <> rest, k, hi, k)(
                Mst.post_after(Item{ik, iv, r} <> rest, List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), k, Items.last_key(pre, lo), hi)(hn)(eb)(
                  Mst.post_fit(pre, Item{ik, iv, r} <> rest, lo, hi)(
                    Mst.opens_fit(l, left, List.append(&2, Item, pre, Item{ik, iv, r} <> rest), ur, lo, hi, oN)
                  )
                )
              )(Mst.le_refl_key(k))
            )
          ),
          ab
        )
      )

# a delete of k from a node of its level, by the items from k on (post)
def Mst.del_ok.here(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  post: List<&2, Item>,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(post, k) == True{}: Bool},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool}
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Mst.delete.here(
    h,
    l,
    left,
    k,
    Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
    lo,
    hi,
    r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y),
    r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)
  )
):
  match post:
    case Con{Item{+ik, +iv, +r}, +rest}:
      Mst.del_ok.here.b(~S, ~fetch, Cmp.is_eq(Key.cmp(ik, k)), s, p, h, ur, lo, hi, k, l, left, pre, ik, iv, r, rest, {==}, eN, oN, all, hn, a, bb)
    case Nil{}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.delete.none(h, Room{l, _, hi}, Mst.last(pre, left), r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k))
      )
      Mst.del_ok.when(
        ~S,
        ~fetch,
        Look.is_absent(Mst.look.go(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), hi}, Mst.last(pre, left), k)),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        Mst.look.go(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), hi}, Mst.last(pre, left), k),
        {==},
        +ab => +g => +fu => Mst.del_same(
          ~S,
          ~fetch,
          g,
          s,
          h,
          ur,
          lo,
          hi,
          l,
          left,
          List.append(&2, Item, pre, []),
          k,
          p,
          Mst.last(pre, left),
          Items.last_key(pre, lo),
          hi,
          eN,
          oN,
          fu,
          Mst.pick_passes(pre, [], left, l, lo, hi, k)(Mst.passes_of_all_lt(pre, k)(all)),
          ab
        )
      )

# a delete of k below a node of a higher level, by whether the node holds k
# (b0)
def Mst.del_ok.gt(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  b0: Bool,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +pre: List<&2, Item>,
  +post: List<&2, Item>,
  +eb0: {Part.hits(Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post}, k) == b0: Bool},
  +eN: {Mst.node(~S, ~fetch, s, h) == Some{Node{l, left, List.append(&2, Item, pre, post)}}: Maybe<&2, Node>},
  +oN: {Mst.opens(Node{l, left, List.append(&2, Item, pre, post)}, Room{ur, lo, hi}) == True{}: Bool},
  +all: {Mst.all_lt(pre, k) == True{}: Bool},
  +hn: {Mst.head_not_lt(post, k) == True{}: Bool},
  +el: {Key.level(k) == ll: Nat},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Bound.after(lo2, k) == True{}: Bool
  } -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    None{},
    Mst.delete(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Shared.Bool.when(
    Maybe<&2, Edit>,
    b0,
    u => None{},
    u => Mst.with_gap(
      l,
      left,
      Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
      Mst.delete(
        ~S,
        ~fetch,
        p,
        s,
        Room{l, Items.head_key(List.reverse.go(&2, Item, pre, []), lo), Items.head_key(post, hi)},
        Mst.last(pre, left),
        k,
        ll
      )
    )
  )
):
  match b0:
    case True{}:
      Unit{}
    case False{}:
      %Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Items.head_key(List.reverse.go(&2, Item, pre, []), lo),
        Items.last_key(pre, lo),
        Mst.head_rev(pre, lo)
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.with_gap(
          l,
          left,
          Part{List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), post},
          Mst.delete(~S, ~fetch, p, s, Room{l, _, Items.head_key(post, hi)}, Mst.last(pre, left), k, ll)
        )
      )
      +pk = Mst.post_after(post, List.reverse.go(&2, Item, pre, []), Mst.last(pre, left), k, Items.last_key(pre, lo), hi)(hn)(eb0)(
        Mst.post_fit(pre, post, lo, hi)(Mst.opens_fit(l, left, List.append(&2, Item, pre, post), ur, lo, hi, oN))
      )
      Mst.ins_ok.gtw(
        ~S,
        ~fetch,
        Mst.delete(~S, ~fetch, p, s, Room{l, Items.last_key(pre, lo), Items.head_key(post, hi)}, Mst.last(pre, left), k, ll),
        s,
        h,
        ur,
        lo,
        hi,
        k,
        None{},
        l,
        left,
        pre,
        post,
        eN,
        oN,
        all,
        pk,
        ih(l)(Items.last_key(pre, lo))(Items.head_key(post, hi))(Mst.last(pre, left))(el)(Mst.last_below(pre, lo, k)(all)(a))(
          Mst.before_head(post, k, hi)(pk)(bb)
        )
      )

# a delete of k at the node of the hash h, by how its level compares to the
# level of k (c)
def Mst.del_ok.node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ll: Nat,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  +el: {Key.level(k) == ll: Nat},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Bound.after(lo2, k) == True{}: Bool
  } -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    None{},
    Mst.delete(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Mst.delete.node(
    c,
    h,
    l,
    left,
    xs,
    lo,
    hi,
    k,
    r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y),
    r2 => c2 => Mst.delete(~S, ~fetch, p, s, r2, c2, k, ll),
    r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)
  )
):
  match c:
    case LT{}:
      Mst.del_ok.lacks(
        ~S,
        ~fetch,
        Mst.pick(xs, left, l, lo, hi, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        xs,
        {==},
        Mst.pick_up(xs, left, l, lo, hi, k),
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
      )
    case EQ{}:
      %Equal.sym(
        Part,
        Mst.part(xs, left, k, []),
        Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
        Mst.part_eq(xs, left, k, [])
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Mst.delete.here(
          h,
          l,
          left,
          k,
          _,
          lo,
          hi,
          r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y),
          r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)
        )
      )
      +eN = Equal.trans(
        Maybe<&2, Node>,
        Mst.node(~S, ~fetch, s, h),
        Some{Node{l, left, xs}},
        Some{Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}},
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        Equal.cong(
          List<&2, Item>,
          Maybe<&2, Node>,
          ys => Some{Node{l, left, ys}},
          xs,
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          Equal.sym(List<&2, Item>, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)), xs, Mst.pre_post(xs, k))
        )
      )
      +oN = Equal.trans(
        Bool,
        Mst.opens(Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}, Room{ur, lo, hi}),
        Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}),
        True{},
        Equal.cong(
          List<&2, Item>,
          Bool,
          ys => Mst.opens(Node{l, left, ys}, Room{ur, lo, hi}),
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          xs,
          Mst.pre_post(xs, k)
        ),
        Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
      )
      Mst.del_ok.here(
        ~S,
        ~fetch,
        Mst.post(xs, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        l,
        left,
        Mst.pre(xs, k),
        eN,
        oN,
        Mst.pre_all_lt(xs, k),
        Mst.post_head(xs, k),
        a,
        bb
      )
    case GT{}:
      %Equal.sym(
        Part,
        Mst.part(xs, left, k, []),
        Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)},
        Mst.part_eq(xs, left, k, [])
      ): Mst.InsOk(
        ~S,
        ~fetch,
        s,
        ur,
        lo,
        hi,
        Some{h},
        k,
        None{},
        Shared.Bool.when(
          Maybe<&2, Edit>,
          Part.hits(_, k),
          u => None{},
          u => Mst.with_gap(l, left, _, Mst.delete(~S, ~fetch, p, s, Part.room(_, l, lo, hi), Part.gap(_), k, ll))
        )
      )
      +eN = Equal.trans(
        Maybe<&2, Node>,
        Mst.node(~S, ~fetch, s, h),
        Some{Node{l, left, xs}},
        Some{Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}},
        Mst.in_node(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en),
        Equal.cong(
          List<&2, Item>,
          Maybe<&2, Node>,
          ys => Some{Node{l, left, ys}},
          xs,
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          Equal.sym(List<&2, Item>, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)), xs, Mst.pre_post(xs, k))
        )
      )
      +oN = Equal.trans(
        Bool,
        Mst.opens(Node{l, left, List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k))}, Room{ur, lo, hi}),
        Mst.opens(Node{l, left, xs}, Room{ur, lo, hi}),
        True{},
        Equal.cong(
          List<&2, Item>,
          Bool,
          ys => Mst.opens(Node{l, left, ys}, Room{ur, lo, hi}),
          List.append(&2, Item, Mst.pre(xs, k), Mst.post(xs, k)),
          xs,
          Mst.pre_post(xs, k)
        ),
        Mst.in_open(~S, ~fetch, s, h, Room{ur, lo, hi}, Node{l, left, xs})(en)
      )
      Mst.del_ok.gt(
        ~S,
        ~fetch,
        Part.hits(Part{List.reverse.go(&2, Item, Mst.pre(xs, k), []), Mst.last(Mst.pre(xs, k), left), Mst.post(xs, k)}, k),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        ll,
        l,
        left,
        Mst.pre(xs, k),
        Mst.post(xs, k),
        {==},
        eN,
        oN,
        Mst.pre_all_lt(xs, k),
        Mst.post_head(xs, k),
        el,
        a,
        bb,
        ih
      )

# a delete of k at the node na of the hash h
def Mst.del_ok.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  na: Maybe<&2, Node>,
  +s: S,
  +p: Nat,
  +h: Hashes.Hash,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ll: Nat,
  +en: {Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}) == na: Maybe<&2, Node>},
  +el: {Key.level(k) == ll: Nat},
  +a: {Bound.after(lo, k) == True{}: Bool},
  +bb: {Bound.before(k, hi) == True{}: Bool},
  ih: @ur2: Nat -> @lo2: Maybe<&2, List<&2, U32>> -> @hi2: Maybe<&2, List<&2, U32>> -> @m2: Maybe<&2, Hashes.Hash> -> {Key.level(k) == ll: Nat} -> {
    Bound.after(lo2, k) == True{}: Bool
  } -> {Bound.before(k, hi2) == True{}: Bool} -> Mst.InsOk(
    ~S,
    ~fetch,
    s,
    ur2,
    lo2,
    hi2,
    m2,
    k,
    None{},
    Mst.delete(~S, ~fetch, p, s, Room{ur2, lo2, hi2}, m2, k, ll)
  )
) -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  Some{h},
  k,
  None{},
  Mst.delete.at(
    na,
    h,
    Room{ur, lo, hi},
    k,
    ll,
    r1 => r2 => x => y => Mst.merge(~S, ~fetch, p, s, r1, r2, x, y),
    r2 => c2 => Mst.delete(~S, ~fetch, p, s, r2, c2, k, ll),
    r2 => c2 => Mst.look.go(~S, ~fetch, p, s, r2, c2, k)
  )
):
  match na:
    case None{}:
      Unit{}
    case Some{Node{+l, +left, +xs}}:
      Mst.del_ok.node(~S, ~fetch, Nat.cmp(l, ll), s, p, h, ur, lo, hi, k, ll, l, left, xs, en, el, a, bb, ih)

# a delete of k from a tree in its room around k reads as Mst.InsOk says
def Mst.del_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  m: Maybe<&2, Hashes.Hash>,
  +s: S,
  +ur: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +ll: Nat
) -> {Key.level(k) == ll: Nat} -> {Bound.after(lo, k) == True{}: Bool} -> {Bound.before(k, hi) == True{}: Bool} -> Mst.InsOk(
  ~S,
  ~fetch,
  s,
  ur,
  lo,
  hi,
  m,
  k,
  None{},
  Mst.delete(~S, ~fetch, f, s, Room{ur, lo, hi}, m, k, ll)
):
  match f m:
    case 0n None{}:
      +el => +a => +bb => Mst.del_ok.none(~S, ~fetch, s, ur, lo, hi, k)
    case 1n+q None{}:
      +el => +a => +bb => Mst.del_ok.none(~S, ~fetch, s, ur, lo, hi, k)
    case 0n Some{h}:
      +el => +a => +bb => Unit{}
    case 1n+(+p) Some{+h}:
      +el => +a => +bb => Mst.del_ok.at(
        ~S,
        ~fetch,
        Mst.node.in(~S, ~fetch, s, h, Room{ur, lo, hi}),
        s,
        p,
        h,
        ur,
        lo,
        hi,
        k,
        ll,
        {==},
        el,
        a,
        bb,
        +ur2 => +lo2 => +hi2 => +m2 => Mst.del_ok(~S, ~fetch, p, m2, s, ur2, lo2, hi2, k, ll)
      )

# the number of zero groups of 5 bits at the top of x, f groups at most, is at
# most f
def Mst.zeros_le(+f: Nat, +x: U32) -> {Nat.is_le(Level.zeros(f, x), f) == True{}: Bool}:
  match f:
    case 0n:
      {==}
    case 1n+(+p):
      Mst.case_bool(
        b => {Nat.is_le(Shared.Bool.when(Nat, b, u => 1n+Level.zeros(p, U32.mul(x, 32)), u => 0n), 1n+p) == True{}: Bool},
        U32.is_eq(U32.and(x, 4160749568), 0),
        +q => Mst.zeros_le(p, U32.mul(x, 32)),
        +q => Shared.Nat.le_zero(1n+p)
      )

# the level of a key is at most 12
def Mst.level_le(+hh: Hashes.Hash) -> {Nat.is_le(Level.of(hh), 12n) == True{}: Bool}:
  match hh:
    case Hashes.Hash{+a, +b, +c, +d, +e, +f, +g, +i}:
      Mst.case_bool(
        t => {
          Nat.is_le(Shared.Bool.when(Nat, t, u => Nat.add(6n, Level.zeros(6n, b)), u => Level.zeros(6n, a)), 12n) == True{}: Bool
        },
        Nat.is_eq(Level.zeros(6n, a), 6n),
        +q => Mst.zeros_le(6n, b),
        +q => Shared.Nat.le_trans(Level.zeros(6n, a), 6n, 12n)(Mst.zeros_le(6n, a))({==})
      )

# the level of a key is below the depth of a tree
def Mst.level_lt(+k: List<&2, U32>) -> {Nat.is_lt(Key.level(k), Mst.depth()) == True{}: Bool}:
  Shared.Nat.le_lt(Key.level(k), 12n, 64n)(Mst.level_le(Hashes.Sha.hash(k)))({==})

# a read that tells m is the read Look.of(m)
def Mst.known_of(t: Look, -m: Maybe<&2, List<&2, U32>>) -> {Look.known(t) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {
  t == Look.of(m): Look
}:
  match t:
    case Look.Found{+v}:
      +e =>
        %Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{v}, m, e): {Look.Found{v} == Look.of(_): Look}
        {==}
    case Look.Absent{}:
      +e =>
        %Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, m, e): {Look.Absent{} == Look.of(_): Look}
        {==}
    case Look.Missing{h}:
      +e => Empty.absurd({Look.Missing{h} == Look.of(m): Look}, Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, m, e))

# a comparison that is not EQ
def Mst.is_eq_false(c: Cmp, f: {c == EQ{}: Cmp} -> Empty) -> {Cmp.is_eq(c) == False{}: Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      Empty.absurd({True{} == False{}: Bool}, f({==}))
    case GT{}:
      {==}

# a write of k as m to a tree reads as Mst.InsOk says
def Mst.put_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> Mst.InsOk(~S, ~fetch, s, Mst.depth(), None{}, None{}, h, k, m, Mst.put(~S, ~fetch, s, h, k, m)):
  match m:
    case Some{+v}:
      Mst.ins_ok(~S, ~fetch, Mst.depth(), h, s, Mst.depth(), None{}, None{}, k, v, Key.level(k))({==})(Mst.level_lt(k))({==})({==})
    case None{}:
      Mst.del_ok(~S, ~fetch, Mst.depth(), h, s, Mst.depth(), None{}, None{}, k, Key.level(k))({==})({==})({==})

# a write res that gave the edit e reads, once the depot holds its new nodes,
# as Mst.InsRead says
def Mst.put_read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  e: Edit,
  -res: Maybe<&2, Edit>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +er: {res == Some{e}: Maybe<&2, Edit>}
) -> Mst.InsOk(~S, ~fetch, s, Mst.depth(), None{}, None{}, h, k, m, res) -> {Depots.Depot.holds(~S, ~fetch, s, Edit.nodes(e)) == True{}: Bool} -> Mst.InsRead(
  ~S,
  ~fetch,
  s,
  Mst.depth(),
  None{},
  None{},
  h,
  k,
  m,
  Edit.root(e)
):
  match e:
    case Edit{+nr, +ns}:
      %Equal.sym(Maybe<&2, Edit>, res, Some{Edit{nr, ns}}, er): (
        Mst.InsOk(~S, ~fetch, s, Mst.depth(), None{}, None{}, h, k, m, _)
          -> {Depots.Depot.holds(~S, ~fetch, s, ns) == True{}: Bool}
          -> Mst.InsRead(~S, ~fetch, s, Mst.depth(), None{}, None{}, h, k, m, nr)
      )
      ok => +hold => ok(hold)

# the two parts of Laws.Write, from what the write reads (bi)
def Mst.writes.of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +nr: Maybe<&2, Hashes.Hash>,
  bi: Mst.InsRead(~S, ~fetch, s, Mst.depth(), None{}, None{}, h, k, m, nr)
) -> {Mst.look(~S, ~fetch, s, nr, k) == Look.of(m): Look}
  & (
    @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool} -> {
      Look.known(Mst.look(~S, ~fetch, s, h, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {Look.known(Mst.look(~S, ~fetch, s, nr, k2)) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
):
  (i1, i2) = bi
  (
    Mst.known_of(Mst.look(~S, ~fetch, s, nr, k), m)(i1(Mst.depth())(Shared.Nat.le_refl(Mst.depth()))),
    +k2 => +x => +ne => +e => i2(k2)(x)(Mst.depth())(Mst.depth())(Mst.is_eq_false(Key.cmp(k2, k), +c => Mst.key_ne(k, k2)(ne)(c)))(
      Shared.Nat.le_refl(Mst.depth())
    )(e)
  )

# what a read tells stays, in a depot that keeps what it holds
law Mst.reads_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Final(S, grows, Mst.ops(~S, ~fetch))

def Mst.reads_final(S, fetch, grows, kept):
  h => k => a => b => x => gr => Mst.look.go_kept(~S, ~fetch, ~grows, ~kept, Mst.depth(), h, a, b, Room.top(), k, x, gr)

# a write stays, in a depot that keeps what it holds
law Mst.puts_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.PutFinal(S, grows, Mst.ops(~S, ~fetch))

def Mst.puts_final(S, fetch, grows, kept):
  s => s2 => h => k => m => e => he => gr => Mst.put_kept(~S, ~fetch, ~grows, ~kept, m, s, s2, h, k, gr)(e)(he)

# a write changes its key and no other
law Mst.writes:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Write(S, fetch, grows, Mst.ops(~S, ~fetch))

def Mst.writes(S, fetch, grows, kept):
  s => +s2 => +h => +k => +m => +e => he => gr => held => Mst.writes.of(
    ~S,
    ~fetch,
    s2,
    h,
    k,
    m,
    Edit.root(e),
    Mst.put_read(
      ~S,
      ~fetch,
      e,
      Mst.put(~S, ~fetch, s2, h, k, m),
      s2,
      h,
      k,
      m,
      Mst.put_kept(~S, ~fetch, ~grows, ~kept, m, s, s2, h, k, gr)(e)(he)
    )(Mst.put_ok(~S, ~fetch, m, s2, h, k))(
      Mst.holds_of(~S, ~fetch, Edit.nodes(e), Mst.head_has(~S, ~fetch, s2, Edit.nodes(e)), s2, {==}, held)
    )
  )

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
