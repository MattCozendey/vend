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
