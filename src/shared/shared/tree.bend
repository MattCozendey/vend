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

# The order of keys
# -----------------

# the comparison c, seen from the other side
def Cmp.flip(c: Cmp) -> Cmp:
  match c:
    case LT{}:
      GT{}
    case EQ{}:
      EQ{}
    case GT{}:
      LT{}

# no LT is an EQ
def Cmp.lt_ne_eq(e: {LT{} == EQ{}: Cmp}) -> Empty:
  Shared.Bool.false_ne_true(Equal.cong(Cmp, Bool, Cmp.is_eq, LT{}, EQ{}, e))

# no GT is an EQ
def Cmp.gt_ne_eq(e: {GT{} == EQ{}: Cmp}) -> Empty:
  Shared.Bool.false_ne_true(Equal.cong(Cmp, Bool, Cmp.is_eq, GT{}, EQ{}, e))

# no GT is an LT
def Cmp.gt_ne_lt(e: {GT{} == LT{}: Cmp}) -> Empty:
  Shared.Bool.false_ne_true(Equal.cong(Cmp, Bool, Cmp.is_lt, GT{}, LT{}, e))

# no EQ is an LT
def Cmp.eq_ne_lt(e: {EQ{} == LT{}: Cmp}) -> Empty:
  Shared.Bool.false_ne_true(Equal.cong(Cmp, Bool, Cmp.is_lt, EQ{}, LT{}, e))

# two numbers compare the other way round from the other side
def Nat.cmp_flip(a: Nat, b: Nat) -> {Nat.cmp(b, a) == Cmp.flip(Nat.cmp(a, b)): Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.cmp_flip(p, q)

# a < b and b < c give a < c
def Nat.cmp_trans(a: Nat, b: Nat, c: Nat) -> {Nat.cmp(a, b) == LT{}: Cmp} -> {Nat.cmp(b, c) == LT{}: Cmp} -> {
  Nat.cmp(a, c) == LT{}: Cmp
}:
  match a b c:
    case 0n 0n z:
      h => k => Empty.absurd({Nat.cmp(0n, z) == LT{}: Cmp}, Cmp.eq_ne_lt(h))
    case 1n+p 0n z:
      h => k => Empty.absurd({Nat.cmp(1n+p, z) == LT{}: Cmp}, Cmp.gt_ne_lt(h))
    case 0n 1n+q 0n:
      h => k => Empty.absurd({Nat.cmp(0n, 0n) == LT{}: Cmp}, Cmp.gt_ne_lt(k))
    case 0n 1n+q 1n+w:
      h => k => {==}
    case 1n+p 1n+q 0n:
      h => k => Empty.absurd({Nat.cmp(1n+p, 0n) == LT{}: Cmp}, Cmp.gt_ne_lt(k))
    case 1n+p 1n+q 1n+w:
      Nat.cmp_trans(p, q, w)

# two words compare the other way round from the other side
def U32.cmp_flip(+x: U32, +y: U32) -> {U32.cmp(y, x) == Cmp.flip(U32.cmp(x, y)): Cmp}:
  %Equal.sym(Cmp, U32.cmp(y, x), Nat.cmp(U32.to_nat(y), U32.to_nat(x)), Shared.U32.cmp_to_nat(y, x)): {
    _ == Cmp.flip(U32.cmp(x, y)): Cmp
  }
  %Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Shared.U32.cmp_to_nat(x, y)): {
    Nat.cmp(U32.to_nat(y), U32.to_nat(x)) == Cmp.flip(_): Cmp
  }
  Nat.cmp_flip(U32.to_nat(x), U32.to_nat(y))

# x < y and y < z give x < z
def U32.cmp_trans(+x: U32, +y: U32, +z: U32) -> {U32.cmp(x, y) == LT{}: Cmp} -> {U32.cmp(y, z) == LT{}: Cmp} -> {
  U32.cmp(x, z) == LT{}: Cmp
}:
  h => k =>
    %Equal.sym(Cmp, U32.cmp(x, z), Nat.cmp(U32.to_nat(x), U32.to_nat(z)), Shared.U32.cmp_to_nat(x, z)): {
      _ == LT{}: Cmp
    }
    Nat.cmp_trans(
      U32.to_nat(x),
      U32.to_nat(y),
      U32.to_nat(z)
    )(
      Equal.trans(
        Cmp,
        Nat.cmp(U32.to_nat(x), U32.to_nat(y)),
        U32.cmp(x, y),
        LT{},
        Equal.sym(Cmp, U32.cmp(x, y), Nat.cmp(U32.to_nat(x), U32.to_nat(y)), Shared.U32.cmp_to_nat(x, y)),
        h
      )
    )(
      Equal.trans(
        Cmp,
        Nat.cmp(U32.to_nat(y), U32.to_nat(z)),
        U32.cmp(y, z),
        LT{},
        Equal.sym(Cmp, U32.cmp(y, z), Nat.cmp(U32.to_nat(y), U32.to_nat(z)), Shared.U32.cmp_to_nat(y, z)),
        k
      )
    )

# words that compare EQ are equal
def U32.cmp_eq(+x: U32, +y: U32) -> {U32.cmp(x, y) == EQ{}: Cmp} -> {x == y: U32}:
  h => Shared.U32.is_eq_sound(x, y)(Shared.Cmp.is_eq_of(U32.cmp(x, y), Equal.sym(Cmp, U32.cmp(x, y), EQ{}, h)))

# a key compares EQ to itself
def Key.cmp_refl(a: List<&2, U32>) -> {Key.cmp(a, a) == EQ{}: Cmp}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(Cmp, U32.cmp(x, x), EQ{}, Shared.U32.cmp_refl(x)): {
        Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(r, r), u => _) == EQ{}: Cmp
      }
      Key.cmp_refl(r)

# Key.cmp_eq for two keys of heads x and y, whose comparison is c
def Key.cmp_eq.con(
  c: Cmp,
  +x: U32,
  +y: U32,
  +ra: List<&2, U32>,
  +rb: List<&2, U32>,
  ec: {U32.cmp(x, y) == c: Cmp},
  ih: {Key.cmp(ra, rb) == EQ{}: Cmp} -> {ra == rb: List<&2, U32>}
) -> {Shared.Bool.when(Cmp, Cmp.is_eq(c), u => Key.cmp(ra, rb), u => c) == EQ{}: Cmp} -> {
  x <> ra == y <> rb: List<&2, U32>
}:
  match c:
    case EQ{}:
      h =>
        %U32.cmp_eq(x, y)(ec): {x <> ra == _ <> rb: List<&2, U32>}
        %ih(h): {x <> ra == x <> _: List<&2, U32>}
        {==}
    case LT{}:
      h => Empty.absurd({x <> ra == y <> rb: List<&2, U32>}, Cmp.lt_ne_eq(h))
    case GT{}:
      h => Empty.absurd({x <> ra == y <> rb: List<&2, U32>}, Cmp.gt_ne_eq(h))

# keys that compare EQ are equal
def Key.cmp_eq(a: List<&2, U32>, b: List<&2, U32>) -> {Key.cmp(a, b) == EQ{}: Cmp} -> {a == b: List<&2, U32>}:
  match a b:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, rb}:
      h => Empty.absurd({[] == y <> rb: List<&2, U32>}, Cmp.lt_ne_eq(h))
    case Con{x, ra} Nil{}:
      h => Empty.absurd({x <> ra == []: List<&2, U32>}, Cmp.gt_ne_eq(h))
    case Con{+x, +ra} Con{+y, +rb}:
      Key.cmp_eq.con(U32.cmp(x, y), x, y, ra, rb, {==}, Key.cmp_eq(ra, rb))

# Key.cmp_flip for two keys of heads that compare as c, and rests that compare
# as r
def Key.cmp_flip.con(c: Cmp, r: Cmp) -> {
  Shared.Bool.when(Cmp, Cmp.is_eq(Cmp.flip(c)), u => Cmp.flip(r), u => Cmp.flip(c))
    == Cmp.flip(Shared.Bool.when(Cmp, Cmp.is_eq(c), u => r, u => c)): Cmp
}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# two keys compare the other way round from the other side
def Key.cmp_flip(a: List<&2, U32>, b: List<&2, U32>) -> {Key.cmp(b, a) == Cmp.flip(Key.cmp(a, b)): Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, rb}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
    case Con{+x, +ra} Con{+y, +rb}:
      %Equal.sym(Cmp, U32.cmp(y, x), Cmp.flip(U32.cmp(x, y)), U32.cmp_flip(x, y)): {
        Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(rb, ra), u => _)
          == Cmp.flip(Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, y)), u => Key.cmp(ra, rb), u => U32.cmp(x, y))): Cmp
      }
      %Equal.sym(Cmp, Key.cmp(rb, ra), Cmp.flip(Key.cmp(ra, rb)), Key.cmp_flip(ra, rb)): {
        Shared.Bool.when(Cmp, Cmp.is_eq(Cmp.flip(U32.cmp(x, y))), u => _, u => Cmp.flip(U32.cmp(x, y)))
          == Cmp.flip(Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, y)), u => Key.cmp(ra, rb), u => U32.cmp(x, y))): Cmp
      }
      Key.cmp_flip.con(U32.cmp(x, y), Key.cmp(ra, rb))

# Key.cmp_trans for three keys of heads x, y and z, where x and y compare as
# c1, and y and z as c2
def Key.cmp_trans.con(
  c1: Cmp,
  c2: Cmp,
  +x: U32,
  +y: U32,
  +z: U32,
  +ra: List<&2, U32>,
  +rb: List<&2, U32>,
  +rc: List<&2, U32>,
  e1: {U32.cmp(x, y) == c1: Cmp},
  e2: {U32.cmp(y, z) == c2: Cmp},
  ih: {Key.cmp(ra, rb) == LT{}: Cmp} -> {Key.cmp(rb, rc) == LT{}: Cmp} -> {Key.cmp(ra, rc) == LT{}: Cmp}
) -> {Shared.Bool.when(Cmp, Cmp.is_eq(c1), u => Key.cmp(ra, rb), u => c1) == LT{}: Cmp} -> {
  Shared.Bool.when(Cmp, Cmp.is_eq(c2), u => Key.cmp(rb, rc), u => c2) == LT{}: Cmp
} -> {Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, z)), u => Key.cmp(ra, rc), u => U32.cmp(x, z)) == LT{}: Cmp}:
  match c1 c2:
    case LT{} LT{}:
      h => k =>
        %Equal.sym(Cmp, U32.cmp(x, z), LT{}, U32.cmp_trans(x, y, z)(e1)(e2)): {
          Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(ra, rc), u => _) == LT{}: Cmp
        }
        {==}
    case LT{} EQ{}:
      h => k =>
        %U32.cmp_eq(y, z)(e2): {
          Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, _)), u => Key.cmp(ra, rc), u => U32.cmp(x, _)) == LT{}: Cmp
        }
        %Equal.sym(Cmp, U32.cmp(x, y), LT{}, e1): {
          Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(ra, rc), u => _) == LT{}: Cmp
        }
        {==}
    case EQ{} LT{}:
      h => k =>
        %Equal.sym(U32, x, y, U32.cmp_eq(x, y)(e1)): {
          Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(_, z)), u => Key.cmp(ra, rc), u => U32.cmp(_, z)) == LT{}: Cmp
        }
        %Equal.sym(Cmp, U32.cmp(y, z), LT{}, e2): {
          Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(ra, rc), u => _) == LT{}: Cmp
        }
        {==}
    case EQ{} EQ{}:
      h => k =>
        %Equal.sym(U32, x, y, U32.cmp_eq(x, y)(e1)): {
          Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(_, z)), u => Key.cmp(ra, rc), u => U32.cmp(_, z)) == LT{}: Cmp
        }
        %U32.cmp_eq(y, z)(e2): {
          Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(y, _)), u => Key.cmp(ra, rc), u => U32.cmp(y, _)) == LT{}: Cmp
        }
        %Equal.sym(Cmp, U32.cmp(y, y), EQ{}, Shared.U32.cmp_refl(y)): {
          Shared.Bool.when(Cmp, Cmp.is_eq(_), u => Key.cmp(ra, rc), u => _) == LT{}: Cmp
        }
        ih(h)(k)
    case GT{} w:
      h => k => Empty.absurd(
        {Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, z)), u => Key.cmp(ra, rc), u => U32.cmp(x, z)) == LT{}: Cmp},
        Cmp.gt_ne_lt(h)
      )
    case w GT{}:
      h => k => Empty.absurd(
        {Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, z)), u => Key.cmp(ra, rc), u => U32.cmp(x, z)) == LT{}: Cmp},
        Cmp.gt_ne_lt(k)
      )

# a < b and b < c give a < c
def Key.cmp_trans(a: List<&2, U32>, b: List<&2, U32>, c: List<&2, U32>) -> {Key.cmp(a, b) == LT{}: Cmp} -> {
  Key.cmp(b, c) == LT{}: Cmp
} -> {Key.cmp(a, c) == LT{}: Cmp}:
  match a b c:
    case Nil{} Nil{} z:
      h => k => Empty.absurd({Key.cmp([], z) == LT{}: Cmp}, Cmp.eq_ne_lt(h))
    case Con{x, ra} Nil{} z:
      h => k => Empty.absurd({Key.cmp(x <> ra, z) == LT{}: Cmp}, Cmp.gt_ne_lt(h))
    case Nil{} Con{y, rb} Nil{}:
      h => k => Empty.absurd({Key.cmp([], []) == LT{}: Cmp}, Cmp.gt_ne_lt(k))
    case Nil{} Con{y, rb} Con{z, rc}:
      h => k => {==}
    case Con{x, ra} Con{y, rb} Nil{}:
      h => k => Empty.absurd({Key.cmp(x <> ra, []) == LT{}: Cmp}, Cmp.gt_ne_lt(k))
    case Con{+x, +ra} Con{+y, +rb} Con{+z, +rc}:
      Key.cmp_trans.con(U32.cmp(x, y), U32.cmp(y, z), x, y, z, ra, rb, rc, {==}, {==}, Key.cmp_trans(ra, rb, rc))

# Key.is_lt_cmp for two keys of heads that compare as c, and rests that
# compare as r
def Key.is_lt_cmp.con(c: Cmp, r: Cmp) -> {
  Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), Cmp.is_lt(r))) == Cmp.is_lt(Shared.Bool.when(Cmp, Cmp.is_eq(c), u => r, u => c)): Bool
}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Key.is_lt is the LT of Key.cmp
def Key.is_lt_cmp(a: List<&2, U32>, b: List<&2, U32>) -> {Key.is_lt(a, b) == Cmp.is_lt(Key.cmp(a, b)): Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
    case Nil{} Con{y, rb}:
      {==}
    case Con{+x, +ra} Con{+y, +rb}:
      %Equal.sym(Bool, Key.is_lt(ra, rb), Cmp.is_lt(Key.cmp(ra, rb)), Key.is_lt_cmp(ra, rb)): {
        Bool.or(U32.is_lt(x, y), Bool.and(U32.is_eq(x, y), _))
          == Cmp.is_lt(Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, y)), u => Key.cmp(ra, rb), u => U32.cmp(x, y))): Bool
      }
      Key.is_lt_cmp.con(U32.cmp(x, y), Key.cmp(ra, rb))

# Key.is_eq_cmp for two keys of heads that compare as c, and rests that
# compare as r
def Key.is_eq_cmp.con(c: Cmp, r: Cmp) -> {
  List.all.if(u => Cmp.is_eq(r), Cmp.is_eq(c)) == Cmp.is_eq(Shared.Bool.when(Cmp, Cmp.is_eq(c), u => r, u => c)): Bool
}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# the equality of words of keys is the EQ of Key.cmp
def Key.is_eq_cmp(a: List<&2, U32>, b: List<&2, U32>) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, a, b) == Cmp.is_eq(Key.cmp(a, b)): Bool
}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Con{x, ra} Nil{}:
      {==}
    case Nil{} Con{y, rb}:
      {==}
    case Con{+x, +ra} Con{+y, +rb}:
      %Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, ra, rb),
        Cmp.is_eq(Key.cmp(ra, rb)),
        Key.is_eq_cmp(ra, rb)
      ): {
        List.all.if(u => _, U32.is_eq(x, y))
          == Cmp.is_eq(Shared.Bool.when(Cmp, Cmp.is_eq(U32.cmp(x, y)), u => Key.cmp(ra, rb), u => U32.cmp(x, y))): Bool
      }
      Key.is_eq_cmp.con(U32.cmp(x, y), Key.cmp(ra, rb))

# Opened nodes
# ------------

# an is_lt that is True is of LT
def Cmp.lt_true(c: Cmp) -> {Cmp.is_lt(c) == True{}: Bool} -> {c == LT{}: Cmp}:
  match c:
    case LT{}:
      h => {==}
    case EQ{}:
      h => Empty.absurd({EQ{} == LT{}: Cmp}, Shared.Bool.false_ne_true(h))
    case GT{}:
      h => Empty.absurd({GT{} == LT{}: Cmp}, Shared.Bool.false_ne_true(h))

# a key before b compares as c, then Key.is_lt asks for LT
def Key.lt_of(+a: List<&2, U32>, +b: List<&2, U32>, -c: Cmp) -> {Key.cmp(a, b) == c: Cmp} -> {
  Key.is_lt(a, b) == Cmp.is_lt(c): Bool
}:
  e =>
    %Equal.sym(Bool, Key.is_lt(a, b), Cmp.is_lt(Key.cmp(a, b)), Key.is_lt_cmp(a, b)): {_ == Cmp.is_lt(c): Bool}
    Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(a, b), c, e)

# a key a that compares to b as c is after b as the flip of c is LT
def Key.gt_of(+a: List<&2, U32>, +b: List<&2, U32>, -c: Cmp) -> {Key.cmp(a, b) == c: Cmp} -> {
  Key.is_lt(b, a) == Cmp.is_lt(Cmp.flip(c)): Bool
}:
  e =>
    %Equal.sym(Bool, Key.is_lt(b, a), Cmp.is_lt(Key.cmp(b, a)), Key.is_lt_cmp(b, a)): {_ == Cmp.is_lt(Cmp.flip(c)): Bool}
    %Equal.sym(Cmp, Key.cmp(b, a), Cmp.flip(Key.cmp(a, b)), Key.cmp_flip(a, b)): {Cmp.is_lt(_) == Cmp.is_lt(Cmp.flip(c)): Bool}
    Equal.cong(Cmp, Bool, x => Cmp.is_lt(Cmp.flip(x)), Key.cmp(a, b), c, e)

# a key a that compares to b as c has the words of b as the flip of c is EQ
def Key.eq_of(+a: List<&2, U32>, +b: List<&2, U32>, -c: Cmp) -> {Key.cmp(a, b) == c: Cmp} -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, b, a) == Cmp.is_eq(Cmp.flip(c)): Bool
}:
  e =>
    %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, b, a), Cmp.is_eq(Key.cmp(b, a)), Key.is_eq_cmp(b, a)): {
      _ == Cmp.is_eq(Cmp.flip(c)): Bool
    }
    %Equal.sym(Cmp, Key.cmp(b, a), Cmp.flip(Key.cmp(a, b)), Key.cmp_flip(a, b)): {Cmp.is_eq(_) == Cmp.is_eq(Cmp.flip(c)): Bool}
    Equal.cong(Cmp, Bool, x => Cmp.is_eq(Cmp.flip(x)), Key.cmp(a, b), c, e)

# a < b and b < c give a < c
def Key.lt_trans(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {
  Key.is_lt(b, c) == True{}: Bool
} -> {Key.is_lt(a, c) == True{}: Bool}:
  h => k =>
    %Equal.sym(Bool, Key.is_lt(a, c), Cmp.is_lt(Key.cmp(a, c)), Key.is_lt_cmp(a, c)): {_ == True{}: Bool}
    %Equal.sym(
      Cmp,
      Key.cmp(a, c),
      LT{},
      Key.cmp_trans(
        a,
        b,
        c
      )(
        Cmp.lt_true(Key.cmp(a, b))(Equal.trans(Bool, Cmp.is_lt(Key.cmp(a, b)), Key.is_lt(a, b), True{}, Equal.sym(Bool, Key.is_lt(a, b), Cmp.is_lt(Key.cmp(a, b)), Key.is_lt_cmp(a, b)), h))
      )(
        Cmp.lt_true(Key.cmp(b, c))(Equal.trans(Bool, Cmp.is_lt(Key.cmp(b, c)), Key.is_lt(b, c), True{}, Equal.sym(Bool, Key.is_lt(b, c), Cmp.is_lt(Key.cmp(b, c)), Key.is_lt_cmp(b, c)), k))
      )
    ): {Cmp.is_lt(_) == True{}: Bool}
    {==}

# no key is before the empty key
def Key.lt_nil(k: List<&2, U32>) -> {Key.is_lt(k, []) == False{}: Bool}:
  match k:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a key after the bound lo is after it once it grows: lo < a < k
def Bound.after_trans(+lo: Maybe<&2, List<&2, U32>>, +a: List<&2, U32>, +k: List<&2, U32>) -> {
  Bound.after(lo, a) == True{}: Bool
} -> {Key.is_lt(a, k) == True{}: Bool} -> {Bound.after(lo, k) == True{}: Bool}:
  match lo:
    case None{}:
      h => g => {==}
    case Some{+b}:
      h => g => Key.lt_trans(b, a, k)(h)(g)

# a key before the bound hi is before it: k < a < hi
def Bound.before_trans(+k: List<&2, U32>, +a: List<&2, U32>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Key.is_lt(k, a) == True{}: Bool
} -> {Bound.before(a, hi) == True{}: Bool} -> {Bound.before(k, hi) == True{}: Bool}:
  match hi:
    case None{}:
      g => h => {==}
    case Some{+b}:
      g => h => Key.lt_trans(k, a, b)(g)(h)

# Key.leads_before for heads that compare as c, and rests r1 and r2
def Key.leads_before.con(c: Cmp, r1: Bool, r2: Bool, ih: {r1 == True{}: Bool} -> {r2 == True{}: Bool}) -> {
  Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), r1)) == True{}: Bool
} -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), r2)) == True{}: Bool}:
  match c:
    case LT{}:
      h => {==}
    case EQ{}:
      h => ih(h)
    case GT{}:
      h => h

# a key that starts with p and is before b has p before b
def Key.leads_before(p: List<&2, U32>, +k: List<&2, U32>, +b: List<&2, U32>) -> {Key.leads(p, k) == True{}: Bool} -> {
  Key.is_lt(k, b) == True{}: Bool
} -> {Key.is_lt(p, b) == True{}: Bool}:
  match p k b:
    case Nil{} k2 Nil{}:
      h1 => h2 => Empty.absurd(
        {Key.is_lt([], []) == True{}: Bool},
        Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, Key.is_lt(k2, []), True{}, Equal.sym(Bool, Key.is_lt(k2, []), False{}, Key.lt_nil(k2)), h2))
      )
    case Nil{} k2 Con{z, rb}:
      h1 => h2 => {==}
    case Con{x, rp} Nil{} b2:
      h1 => h2 => Empty.absurd({Key.is_lt(x <> rp, b2) == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case Con{x, rp} Con{y, rk} Nil{}:
      h1 => h2 => Empty.absurd({Key.is_lt(x <> rp, []) == True{}: Bool}, Shared.Bool.false_ne_true(h2))
    case Con{+x, +rp} Con{+y, +rk} Con{+z, +rb}:
      +h1 => h2 =>
        %Equal.sym(U32, x, y, Shared.U32.is_eq_sound(x, y)(Shared.List.all.if_hit(U32.is_eq(x, y), u => Key.leads(rp, rk))(h1))): {
          Bool.or(U32.is_lt(_, z), Bool.and(U32.is_eq(_, z), Key.is_lt(rp, rb))) == True{}: Bool
        }
        Key.leads_before.con(
          U32.cmp(y, z),
          Key.is_lt(rk, rb),
          Key.is_lt(rp, rb),
          Key.leads_before(rp, rk, rb)(Shared.List.all.if_rest(U32.is_eq(x, y), u => Key.leads(rp, rk))(h1))
        )(h2)

# Key.leads_after for heads that compare as c
def Key.leads_after.con(
  c: Cmp,
  r1: Bool,
  a1: Bool,
  b1: Bool,
  ih: {r1 == True{}: Bool} -> {Bool.or(a1, b1) == True{}: Bool}
) -> {Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), r1)) == True{}: Bool} -> {
  Bool.or(Bool.or(Cmp.is_lt(c), Bool.and(Cmp.is_eq(c), a1)), List.all.if(u => b1, Cmp.is_eq(Cmp.flip(c)))) == True{}: Bool
}:
  match c:
    case LT{}:
      h => {==}
    case EQ{}:
      h => ih(h)
    case GT{}:
      h => h

# a key that starts with p and is after a has a before p, or starts with p
def Key.leads_after(p: List<&2, U32>, +k: List<&2, U32>, +a: List<&2, U32>) -> {Key.leads(p, k) == True{}: Bool} -> {
  Key.is_lt(a, k) == True{}: Bool
} -> {Bool.or(Key.is_lt(a, p), Key.leads(p, a)) == True{}: Bool}:
  match p k a:
    case Nil{} k2 a2:
      h1 => h2 =>
        %Equal.sym(Bool, Key.is_lt(a2, []), False{}, Key.lt_nil(a2)): {Bool.or(_, Key.leads([], a2)) == True{}: Bool}
        {==}
    case Con{x, rp} Nil{} a2:
      h1 => h2 => Empty.absurd(
        {Bool.or(Key.is_lt(a2, x <> rp), Key.leads(x <> rp, a2)) == True{}: Bool},
        Shared.Bool.false_ne_true(h1)
      )
    case Con{x, rp} Con{y, rk} Nil{}:
      h1 => h2 => {==}
    case Con{+x, +rp} Con{+y, +rk} Con{+z, +ra}:
      +h1 => h2 =>
        %Equal.sym(U32, x, y, Shared.U32.is_eq_sound(x, y)(Shared.List.all.if_hit(U32.is_eq(x, y), u => Key.leads(rp, rk))(h1))): {
          Bool.or(Bool.or(U32.is_lt(z, _), Bool.and(U32.is_eq(z, _), Key.is_lt(ra, rp))), List.all.if(u => Key.leads(rp, ra), U32.is_eq(_, z)))
            == True{}: Bool
        }
        %Equal.sym(Cmp, U32.cmp(y, z), Cmp.flip(U32.cmp(z, y)), U32.cmp_flip(z, y)): {
          Bool.or(Bool.or(U32.is_lt(z, y), Bool.and(U32.is_eq(z, y), Key.is_lt(ra, rp))), List.all.if(u => Key.leads(rp, ra), Cmp.is_eq(_)))
            == True{}: Bool
        }
        Key.leads_after.con(
          U32.cmp(z, y),
          Key.is_lt(ra, rk),
          Key.is_lt(ra, rp),
          Key.leads(rp, ra),
          Key.leads_after(rp, rk, ra)(Shared.List.all.if_rest(U32.is_eq(x, y), u => Key.leads(rp, rk))(h1))
        )(h2)

# a key that starts with p, between lo and hi, makes p meet both bounds
def Bound.meets(+p: List<&2, U32>, +k: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> {
  Key.leads(p, k) == True{}: Bool
} -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {
  Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == True{}: Bool
}:
  match lo hi:
    case None{} None{}:
      h1 => h2 => {==}
    case None{} Some{+b}:
      h1 => h2 => Key.leads_before(p, k, b)(h1)(h2)
    case Some{+a} None{}:
      +h1 => h2 => Shared.Bool.and_both(
        Bool.or(Key.is_lt(a, p), Key.leads(p, a)),
        True{}
      )(Key.leads_after(p, k, a)(h1)(Shared.Bool.and_true_left(Key.is_lt(a, k), True{})(h2)))({==})
    case Some{+a} Some{+b}:
      +h1 => +h2 => Shared.Bool.and_both(
        Bool.or(Key.is_lt(a, p), Key.leads(p, a)),
        Key.is_lt(p, b)
      )(Key.leads_after(p, k, a)(h1)(Shared.Bool.and_true_left(Key.is_lt(a, k), Key.is_lt(k, b))(h2)))(
        Key.leads_before(p, k, b)(h1)(Shared.Bool.and_true_right(Key.is_lt(a, k), Key.is_lt(k, b))(h2))
      )

# a bind that gives x: m holds a value a, and f gives x of a
def Maybe.bind_cases(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -f: A -> Maybe<&2, B>,
  -x: B,
  -P: Type,
  k: @a: A -> {m == Some{a}: Maybe<&2, A>} -> {f(a) == Some{x}: Maybe<&2, B>} -> P
) -> {Maybe.bind(&2, A, B, m, f) == Some{x}: Maybe<&2, B>} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(B, x, e))
    case Some{+a}:
      e => k(a)({==})(e)

# a map that gives x: m holds a value a, and f gives x of a
def Maybe.map_cases(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -f: A -> B,
  -x: B,
  -P: Type,
  k: @a: A -> {m == Some{a}: Maybe<&2, A>} -> {f(a) == x: B} -> P
) -> {Maybe.map(&2, A, B, f, m) == Some{x}: Maybe<&2, B>} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(B, x, e))
    case Some{+a}:
      e => k(a)({==})(Shared.Maybe.some_inj(B, f(a), x, e))

# a Shared.Maybe.when that gives x: its test holds, and its body gives x
def Maybe.when_cases(
  -B: Data,
  b: Bool,
  -g: Unit -> Maybe<&2, B>,
  -x: B,
  -P: Type,
  k: {b == True{}: Bool} -> {g(Unit{}) == Some{x}: Maybe<&2, B>} -> P
) -> {Shared.Maybe.when(B, b, g) == Some{x}: Maybe<&2, B>} -> P:
  match b:
    case True{}:
      e => k({==})(e)
    case False{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(B, x, e))

# the pieces of an opened node: of a node below up with an item, by its items
def Mst.open.node_cases(
  n: Node,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ps: List<&2, Piece>,
  -P: Type,
  k: @l: Nat -> @left: Maybe<&2, Hashes.Hash> -> @xs: List<&2, Item> -> {n == Node{l, left, xs}: Node} -> {
    Nat.is_lt(l, up) == True{}: Bool
  } -> {List.is_empty(&2, Item, xs) == False{}: Bool} -> {
    Mst.pieces(xs, l, left, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>
  } -> P
) -> {Mst.open.node(n, up, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>} -> P:
  match n:
    case Node{+l, +left, +xs}:
      e => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs))),
        u => Mst.pieces(xs, l, left, lo, hi),
        ps,
        P,
        +c => ep => k(l)(left)(xs)({==})(
          Shared.Bool.and_true_left(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs)))(c)
        )(
          Shared.Bool.not_true(
            List.is_empty(&2, Item, xs)
          )(Shared.Bool.and_true_right(Nat.is_lt(l, up), Bool.not(List.is_empty(&2, Item, xs)))(c))
        )(ep)
      )(e)

# the keys of the items of a node that gives pieces fit its bounds
def Mst.pieces_fit(
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ps: List<&2, Piece>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>} -> {Items.fit(xs, lo, hi) == True{}: Bool}:
  match xs:
    case Nil{}:
      e => {==}
    case Con{Item{+k, +v, +r}, +rest}:
      e => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(k), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, k)))),
          Bool.and(Bound.after(lo, k), Bound.before(k, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{k}, Piece.Bind{k, v} <> ps2),
          Mst.pieces(rest, l, r, Some{k}, hi)
        ),
        ps,
        {Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Items.fit(rest, Some{k}, hi)) == True{}: Bool},
        c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{k}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{k}, Piece.Bind{k, v} <> ps2),
          ps,
          {Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Items.fit(rest, Some{k}, hi)) == True{}: Bool},
          ps2 => e3 => e4 => Shared.Bool.and_both(
            Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
            Items.fit(rest, Some{k}, hi)
          )(
            Shared.Bool.and_true_right(
              Bool.and(Nat.is_eq(Key.level(k), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, k)))),
              Bool.and(Bound.after(lo, k), Bound.before(k, hi))
            )(c)
          )(Mst.pieces_fit(rest, l, r, Some{k}, hi, ps2)(e3))
        )(e2)
      )(e)

# the node that a depot holds, once its words read whole as a node that may
# sit in the room of up, lo and hi
def Mst.node.in_of(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ws: List<&2, U32>,
  +l: Nat,
  +left: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Item>,
  ew: {fetch(s)(h) == Some{ws}: Maybe<&2, List<&2, U32>>},
  er: {Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws) == Some{Node{l, left, xs}}: Maybe<&2, Node>},
  elt: {Nat.is_lt(l, up) == True{}: Bool},
  ee: {List.is_empty(&2, Item, xs) == False{}: Bool},
  ef: {Items.fit(xs, lo, hi) == True{}: Bool}
) -> {Mst.node.in(~S, ~fetch, s, h, Room{up, lo, hi}) == Some{Node{l, left, xs}}: Maybe<&2, Node>}:
  %Equal.sym(Maybe<&2, List<&2, U32>>, fetch(s)(h), Some{ws}, ew): {
    Maybe.bind(&2, Node, Node, Codes.Code.whole.of(~Node, ~Node.code, ~Node.code.read, _), n => Node.in(n, Room{up, lo, hi}))
      == Some{Node{l, left, xs}}: Maybe<&2, Node>
  }
  %Equal.sym(Maybe<&2, Node>, Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws), Some{Node{l, left, xs}}, er): {
    Maybe.bind(&2, Node, Node, _, n => Node.in(n, Room{up, lo, hi})) == Some{Node{l, left, xs}}: Maybe<&2, Node>
  }
  %Equal.sym(Bool, Nat.is_lt(l, up), True{}, elt): {
    Shared.Maybe.when(
      Node,
      Bool.and(Bool.and(_, Bool.not(List.is_empty(&2, Item, xs))), Items.fit(xs, lo, hi)),
      u => Some{Node{l, left, xs}}
    ) == Some{Node{l, left, xs}}: Maybe<&2, Node>
  }
  %Equal.sym(Bool, List.is_empty(&2, Item, xs), False{}, ee): {
    Shared.Maybe.when(Node, Bool.and(Bool.and(True{}, Bool.not(_)), Items.fit(xs, lo, hi)), u => Some{Node{l, left, xs}})
      == Some{Node{l, left, xs}}: Maybe<&2, Node>
  }
  %Equal.sym(Bool, Items.fit(xs, lo, hi), True{}, ef): {
    Shared.Maybe.when(Node, Bool.and(Bool.and(True{}, Bool.not(False{})), _), u => Some{Node{l, left, xs}})
      == Some{Node{l, left, xs}}: Maybe<&2, Node>
  }
  {==}

# what an opened node is: the depot holds its code under its hash, a read
# finds it in its room, and its items give the pieces
def Mst.open_cases(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ps: List<&2, Piece>,
  -P: Type,
  k: @l: Nat -> @left: Maybe<&2, Hashes.Hash> -> @xs: List<&2, Item> -> {
    fetch(s)(h) == Some{Node.code(Node{l, left, xs}, [])}: Maybe<&2, List<&2, U32>>
  } -> {Hashes.Sha.hash(Node.code(Node{l, left, xs}, [])) == h: Hashes.Hash} -> {
    Mst.node.in(~S, ~fetch, s, h, Room{up, lo, hi}) == Some{Node{l, left, xs}}: Maybe<&2, Node>
  } -> {Mst.pieces(xs, l, left, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>} -> P
) -> {Mst.open(~S, ~fetch, s, h, up, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>} -> P:
  e => Maybe.bind_cases(
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
    ),
    ps,
    P,
    +ws => +ew => e1 => Maybe.when_cases(
      List<&2, Piece>,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h),
      u => Maybe.bind(
        &2,
        Node,
        List<&2, Piece>,
        Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws),
        n => Mst.open.node(n, up, lo, hi)
      ),
      ps,
      P,
      +eh => e2 => Maybe.bind_cases(
        Node,
        List<&2, Piece>,
        Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws),
        n => Mst.open.node(n, up, lo, hi),
        ps,
        P,
        +n => +er => e3 => Mst.open.node_cases(
          n,
          up,
          lo,
          hi,
          ps,
          P,
          +l => +left => +xs => +en => +elt => +ee => +ep =>
            +er2 = Equal.trans(
              Maybe<&2, Node>,
              Codes.Code.whole.read(~Node, ~Node.code, ~Node.code.read, ws),
              Some{n},
              Some{Node{l, left, xs}},
              er,
              Equal.cong(Node, Maybe<&2, Node>, x => Some{x}, n, Node{l, left, xs}, en)
            )
            +w = Equal.sym(
              List<&2, U32>,
              Node.code(Node{l, left, xs}, []),
              ws,
              Codes.Code.whole_back(~Node, ~Node.code, ~Node.code.read, ws, Node{l, left, xs})(er2)
            )
            k(l)(left)(xs)(
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                fetch(s)(h),
                Some{ws},
                Some{Node.code(Node{l, left, xs}, [])},
                ew,
                Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, x => Some{x}, ws, Node.code(Node{l, left, xs}, []), w)
              )
            )(
              Equal.trans(
                Hashes.Hash,
                Hashes.Sha.hash(Node.code(Node{l, left, xs}, [])),
                Hashes.Sha.hash(ws),
                h,
                Equal.cong(
                  List<&2, U32>,
                  Hashes.Hash,
                  x => Hashes.Sha.hash(x),
                  Node.code(Node{l, left, xs}, []),
                  ws,
                  Equal.sym(List<&2, U32>, ws, Node.code(Node{l, left, xs}, []), w)
                ),
                Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws), h)(eh)
              )
            )(Mst.node.in_of(~S, ~fetch, s, h, up, lo, hi, ws, l, left, xs, ew, er2, elt, ee, Mst.pieces_fit(xs, l, left, lo, hi, ps)(ep)))(ep)
        )(e3)
      )(e2)
    )(e1)
  )(e)

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
