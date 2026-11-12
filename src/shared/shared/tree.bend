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

# a listing stays as the depot grows: it reads only nodes by hash
def Laws.RangeFinal(-S: Data, -grows: S -> S -> Bool, -o: Tree.Ops(S)) -> Type:
  @s: S -> @s2: S -> @h: Maybe<&2, Hashes.Hash> -> @p: List<&2, U32> -> @bs: List<&2, Binding> -> {
    Ops.range(S, o)(s)(h)(p) == Some{bs}: Maybe<&2, List<&2, Binding>>
  } -> {grows(s, s2) == True{}: Bool} -> {Ops.range(S, o)(s2)(h)(p) == Some{bs}: Maybe<&2, List<&2, Binding>>}

# a difference stays as the depot grows: it reads only nodes by hash
def Laws.DiffFinal(-S: Data, -grows: S -> S -> Bool, -o: Tree.Ops(S)) -> Type:
  @s: S -> @s2: S -> @a: Maybe<&2, Hashes.Hash> -> @b: Maybe<&2, Hashes.Hash> -> @ks: List<
    &2,
    List<&2, U32>> -> {
    Ops.diff(S, o)(s)(a)(b) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>
  } -> {grows(s, s2) == True{}: Bool} -> {Ops.diff(S, o)(s2)(a)(b) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}

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
        & (Laws.Canon(S, o) & (Laws.Range(S, o) & (Laws.Diff(S, o) & (Laws.Whole(S, o) & (Laws.Kept(S, fetch, grows, o) & (Laws.RangeFinal(S, grows, o) & Laws.DiffFinal(S, grows, o)))))))
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
# room
def Piece.same(a: Piece, b: Piece) -> Bool:
  match a b:
    case Piece.Bind{k1, v1} Piece.Bind{k2, v2}:
      Bool.and(Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2))
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Sub{h2, u2, lo2, hi2}:
      Bool.and(
        Bool.and(Hashes.Hash.is_eq(h1, h2), Nat.is_eq(u1, u2)),
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
  } -> {Nat.is_lt(l, up) == True{}: Bool} -> {List.is_empty(&2, Item, xs) == False{}: Bool} -> {
    Mst.pieces(xs, l, left, lo, hi) == Some{ps}: Maybe<&2, List<&2, Piece>>
  } -> P
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
            )(Mst.node.in_of(~S, ~fetch, s, h, up, lo, hi, ws, l, left, xs, ew, er2, elt, ee, Mst.pieces_fit(xs, l, left, lo, hi, ps)(ep)))(elt)(ee)(ep)
        )(e3)
      )(e2)
    )(e1)
  )(e)

# Listings
# --------

# the read l found the value v
def Look.has(l: Look, v: List<&2, U32>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Look.value(l), Some{v})

# the pieces ps hold the key k bound to v, as reads f levels down find it: as
# a binding, or in a subtree whose bounds hold k
def Pieces.has(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{Piece.Bind{k2, v2}, rest}:
      Bool.or(Binding.is_eq(Binding{k2, v2}, Binding{k, v}), Pieces.has(~S, ~fetch, f, s, rest, k, v))
    case Con{Piece.Sub{h, up, +lo, +hi}, rest}:
      Bool.or(
        Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{up, lo, hi}, Some{h}, k), v)),
        Pieces.has(~S, ~fetch, f, s, rest, k, v)
      )

# a read of the empty tree finds that it lacks the key
def Mst.look_none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +r: Room,
  +k: List<&2, U32>
) -> {Mst.look.go(~S, ~fetch, f, s, r, None{}, k) == Look.Absent{}: Look}:
  match f:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the pieces of a subtree m hold k bound to v when its bounds hold k and a
# read of m finds v
def Pieces.has_at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Pieces.has(~S, ~fetch, f, s, Piece.sub(m, l, lo, hi, rest), k, v)
    == Bool.or(
      Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, m, k), v)),
      Pieces.has(~S, ~fetch, f, s, rest, k, v)
    ): Bool
}:
  match m:
    case None{}:
      %Equal.sym(Look, Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, None{}, k), Look.Absent{}, Mst.look_none(~S, ~fetch, f, s, Room{l, lo, hi}, k)): {
        Pieces.has(~S, ~fetch, f, s, rest, k, v)
          == Bool.or(Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(_, v)), Pieces.has(~S, ~fetch, f, s, rest, k, v)): Bool
      }
      %Equal.sym(
        Bool,
        Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), False{}),
        False{},
        Shared.Bool.and_false_right(Bool.and(Bound.after(lo, k), Bound.before(k, hi)))
      ): {Pieces.has(~S, ~fetch, f, s, rest, k, v) == Bool.or(_, Pieces.has(~S, ~fetch, f, s, rest, k, v)): Bool}
      {==}
    case Some{h}:
      {==}

# Mst.has_pick where k comes before the key of the item: the subtree before
# it decides
def Mst.has_pick.lt(
  b: Bool,
  l1: Bool,
  l2: Bool,
  e: Bool,
  a: Bool,
  -v: Bool,
  x: Bool,
  -y: Bool,
  eb: {b == True{}: Bool},
  el1: {l1 == True{}: Bool},
  el2: {l2 == False{}: Bool},
  ee: {e == False{}: Bool}
) -> {
  Bool.or(Bool.and(Bool.and(a, l1), x), Bool.or(List.all.if(u => v, e), Bool.and(Bool.and(l2, b), y)))
    == Bool.and(Bool.and(a, b), x): Bool
}:
  match b l1 l2 e:
    case True{} True{} False{} False{}:
      Equal.sym(Bool, Bool.and(Bool.and(a, True{}), x), Bool.or(Bool.and(Bool.and(a, True{}), x), False{}), Shared.Bool.or_false(Bool.and(Bool.and(a, True{}), x)))
    case False{} w1 w2 w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(a, w1), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(w2, False{}), y)))
            == Bool.and(Bool.and(a, False{}), x): Bool
        },
        Shared.Bool.false_ne_true(eb)
      )
    case True{} False{} w2 w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(a, False{}), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(w2, True{}), y)))
            == Bool.and(Bool.and(a, True{}), x): Bool
        },
        Shared.Bool.false_ne_true(el1)
      )
    case True{} True{} True{} w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(a, True{}), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(True{}, True{}), y)))
            == Bool.and(Bool.and(a, True{}), x): Bool
        },
        Shared.Bool.true_ne_false(el2)
      )
    case True{} True{} False{} True{}:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(a, True{}), x), Bool.or(List.all.if(u => v, True{}), Bool.and(Bool.and(False{}, True{}), y)))
            == Bool.and(Bool.and(a, True{}), x): Bool
        },
        Shared.Bool.true_ne_false(ee)
      )

# Mst.has_pick where k is the key of the item: its value decides
def Mst.has_pick.eq(
  a: Bool,
  b: Bool,
  l1: Bool,
  l2: Bool,
  e: Bool,
  w: Bool,
  -x: Bool,
  -y: Bool,
  +h: Hashes.Hash,
  +iv: List<&2, U32>,
  +v: List<&2, U32>,
  ea: {a == True{}: Bool},
  eb: {b == True{}: Bool},
  el1: {l1 == False{}: Bool},
  el2: {l2 == False{}: Bool},
  ee: {e == True{}: Bool},
  ew: {w == True{}: Bool}
) -> {
  Bool.or(
    Bool.and(Bool.and(a, l1), x),
    Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), e), Bool.and(Bool.and(l2, b), y))
  )
    == Bool.and(Bool.and(a, b), Look.has(Shared.Bool.when(Look, w, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
}:
  match a b l1 l2 e w:
    case True{} True{} False{} False{} True{} True{}:
      Equal.sym(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, iv, v),
        Bool.or(Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), False{}),
        Shared.Bool.or_false(Shared.List.is_eq(~U32, ~U32.is_eq, iv, v))
      )
    case False{} w1 w2 w3 w4 w5:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(False{}, w2), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), w4), Bool.and(Bool.and(w3, w1), y))
          )
            == Bool.and(Bool.and(False{}, w1), Look.has(Shared.Bool.when(Look, w5, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.false_ne_true(ea)
      )
    case True{} False{} w2 w3 w4 w5:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(True{}, w2), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), w4), Bool.and(Bool.and(w3, False{}), y))
          )
            == Bool.and(Bool.and(True{}, False{}), Look.has(Shared.Bool.when(Look, w5, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.false_ne_true(eb)
      )
    case True{} True{} True{} w3 w4 w5:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(True{}, True{}), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), w4), Bool.and(Bool.and(w3, True{}), y))
          )
            == Bool.and(Bool.and(True{}, True{}), Look.has(Shared.Bool.when(Look, w5, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.true_ne_false(el1)
      )
    case True{} True{} False{} True{} w4 w5:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(True{}, False{}), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), w4), Bool.and(Bool.and(True{}, True{}), y))
          )
            == Bool.and(Bool.and(True{}, True{}), Look.has(Shared.Bool.when(Look, w5, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.true_ne_false(el2)
      )
    case True{} True{} False{} False{} False{} w5:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(True{}, False{}), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), False{}), Bool.and(Bool.and(False{}, True{}), y))
          )
            == Bool.and(Bool.and(True{}, True{}), Look.has(Shared.Bool.when(Look, w5, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.false_ne_true(ee)
      )
    case True{} True{} False{} False{} True{} False{}:
      Empty.absurd(
        {
          Bool.or(
            Bool.and(Bool.and(True{}, False{}), x),
            Bool.or(List.all.if(u => Shared.List.is_eq(~U32, ~U32.is_eq, iv, v), True{}), Bool.and(Bool.and(False{}, True{}), y))
          )
            == Bool.and(Bool.and(True{}, True{}), Look.has(Shared.Bool.when(Look, False{}, u => Look.Found{iv}, u => Look.Missing{h}), v)): Bool
        },
        Shared.Bool.false_ne_true(ew)
      )

# Mst.has_pick where k comes after the key of the item: the items after it
# decide
def Mst.has_pick.gt(
  a: Bool,
  l1: Bool,
  l2: Bool,
  e: Bool,
  -b: Bool,
  -v: Bool,
  -x: Bool,
  -y: Bool,
  ea: {a == True{}: Bool},
  el1: {l1 == False{}: Bool},
  el2: {l2 == True{}: Bool},
  ee: {e == False{}: Bool}
) -> {
  Bool.or(Bool.and(Bool.and(a, l1), x), Bool.or(List.all.if(u => v, e), Bool.and(Bool.and(l2, b), y)))
    == Bool.and(Bool.and(a, b), y): Bool
}:
  match a l1 l2 e:
    case True{} False{} True{} False{}:
      {==}
    case False{} w1 w2 w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(False{}, w1), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(w2, b), y)))
            == Bool.and(Bool.and(False{}, b), y): Bool
        },
        Shared.Bool.false_ne_true(ea)
      )
    case True{} True{} w2 w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(True{}, True{}), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(w2, b), y)))
            == Bool.and(Bool.and(True{}, b), y): Bool
        },
        Shared.Bool.true_ne_false(el1)
      )
    case True{} False{} False{} w3:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(True{}, False{}), x), Bool.or(List.all.if(u => v, w3), Bool.and(Bool.and(False{}, b), y)))
            == Bool.and(Bool.and(True{}, b), y): Bool
        },
        Shared.Bool.false_ne_true(el2)
      )
    case True{} False{} True{} True{}:
      Empty.absurd(
        {
          Bool.or(Bool.and(Bool.and(True{}, False{}), x), Bool.or(List.all.if(u => v, True{}), Bool.and(Bool.and(True{}, b), y)))
            == Bool.and(Bool.and(True{}, b), y): Bool
        },
        Shared.Bool.true_ne_false(ee)
      )

# Mst.has_pick at an item of the key ik, whose comparison with k is c
def Mst.has_pick.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  +ec: {Key.cmp(k, ik) == c: Cmp},
  ea: {Bound.after(lo, ik) == True{}: Bool},
  eb: {Bound.before(ik, hi) == True{}: Bool},
  ew: {Nat.is_eq(Key.level(ik), l) == True{}: Bool}
) -> {
  Bool.or(
    Bool.and(Bool.and(Bound.after(lo, k), Key.is_lt(k, ik)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v)),
    Bool.or(
      Binding.is_eq(Binding{ik, iv}, Binding{k, v}),
      Bool.and(
        Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)),
        Look.has(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v)
      )
    )
  )
    == Bool.and(
      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
      Look.has(
        Mst.look.pick(
          Shared.Bool.when(
            Pick,
            Cmp.is_lt(c),
            u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
            u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k))
          ),
          h,
          l,
          k,
          m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)
        ),
        v
      )
    ): Bool
}:
  match c:
    case LT{}:
      +l1 = Key.lt_of(k, ik, LT{})(ec)
      Mst.has_pick.lt(
        Bound.before(k, hi),
        Key.is_lt(k, ik),
        Key.is_lt(ik, k),
        Shared.List.is_eq(~U32, ~U32.is_eq, ik, k),
        Bound.after(lo, k),
        Shared.List.is_eq(~U32, ~U32.is_eq, iv, v),
        Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v),
        Look.has(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v),
        Bound.before_trans(k, ik, hi)(l1)(eb),
        l1,
        Key.gt_of(k, ik, LT{})(ec),
        Key.eq_of(k, ik, LT{})(ec)
      )
    case EQ{}:
      +ke = Key.cmp_eq(k, ik)(ec)
      Mst.has_pick.eq(
        Bound.after(lo, k),
        Bound.before(k, hi),
        Key.is_lt(k, ik),
        Key.is_lt(ik, k),
        Shared.List.is_eq(~U32, ~U32.is_eq, ik, k),
        Nat.is_eq(Key.level(k), l),
        Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v),
        Look.has(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v),
        h,
        iv,
        v,
        Equal.trans(Bool, Bound.after(lo, k), Bound.after(lo, ik), True{}, Equal.cong(List<&2, U32>, Bool, x => Bound.after(lo, x), k, ik, ke), ea),
        Equal.trans(Bool, Bound.before(k, hi), Bound.before(ik, hi), True{}, Equal.cong(List<&2, U32>, Bool, x => Bound.before(x, hi), k, ik, ke), eb),
        Key.lt_of(k, ik, EQ{})(ec),
        Key.gt_of(k, ik, EQ{})(ec),
        Key.eq_of(k, ik, EQ{})(ec),
        Equal.trans(
          Bool,
          Nat.is_eq(Key.level(k), l),
          Nat.is_eq(Key.level(ik), l),
          True{},
          Equal.cong(List<&2, U32>, Bool, x => Nat.is_eq(Key.level(x), l), k, ik, ke),
          ew
        )
      )
    case GT{}:
      +l2 = Key.gt_of(k, ik, GT{})(ec)
      Mst.has_pick.gt(
        Bound.after(lo, k),
        Key.is_lt(k, ik),
        Key.is_lt(ik, k),
        Shared.List.is_eq(~U32, ~U32.is_eq, ik, k),
        Bound.before(k, hi),
        Shared.List.is_eq(~U32, ~U32.is_eq, iv, v),
        Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v),
        Look.has(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v),
        Bound.after_trans(lo, ik, k)(ea)(l2),
        Key.lt_of(k, ik, GT{})(ec),
        l2,
        Key.eq_of(k, ik, GT{})(ec)
      )

# the pieces of the items xs of the node of the hash h hold k bound to v
# exactly when k is in their bounds and a read of k in the node finds v
def Mst.has_pick(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ks: List<&2, Piece>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Pieces.has(~S, ~fetch, f, s, ks, k, v)
    == Bool.and(
      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
      Look.has(Mst.look.pick(Mst.pick(xs, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v)
    ): Bool
}:
  match xs:
    case Nil{}:
      e =>
        %Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, e): {
          Pieces.has(~S, ~fetch, f, s, _, k, v)
            == Bool.and(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v)
            ): Bool
        }
        %Equal.sym(
          Bool,
          Pieces.has(~S, ~fetch, f, s, Piece.sub(prev, l, lo, hi, []), k, v),
          Bool.or(
            Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v)),
            False{}
          ),
          Pieces.has_at(~S, ~fetch, f, s, prev, l, lo, hi, [], k, v)
        ): {
          _
            == Bool.and(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v)
            ): Bool
        }
        Equal.sym(
          Bool,
          Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v)),
          Bool.or(
            Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v)),
            False{}
          ),
          Shared.Bool.or_false(
            Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k), v))
          )
        )
    case Con{Item{+ik, +iv, +r}, +rest}:
      e => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {
          Pieces.has(~S, ~fetch, f, s, ks, k, v)
            == Bool.and(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Look.has(
                Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)),
                v
              )
            ): Bool
        },
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {
            Pieces.has(~S, ~fetch, f, s, ks, k, v)
              == Bool.and(
                Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                Look.has(
                  Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)),
                  v
                )
              ): Bool
          },
          +ks2 => e3 => e4 =>
            +c1 = Shared.Bool.and_true_left(
              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
            )(c)
            +c2 = Shared.Bool.and_true_right(
              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
            )(c)
            %e4: {
              Pieces.has(~S, ~fetch, f, s, _, k, v)
                == Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(
                    Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)),
                    v
                  )
                ): Bool
            }
            %Equal.sym(
              Bool,
              Pieces.has(~S, ~fetch, f, s, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), k, v),
              Bool.or(
                Bool.and(Bool.and(Bound.after(lo, k), Key.is_lt(k, ik)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v)),
                Pieces.has(~S, ~fetch, f, s, Piece.Bind{ik, iv} <> ks2, k, v)
              ),
              Pieces.has_at(~S, ~fetch, f, s, prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2, k, v)
            ): {
              _
                == Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(
                    Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)),
                    v
                  )
                ): Bool
            }
            %Equal.sym(
              Bool,
              Pieces.has(~S, ~fetch, f, s, ks2, k, v),
              Bool.and(
                Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)),
                Look.has(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)), v)
              ),
              Mst.has_pick(~S, ~fetch, f, s, h, rest, l, r, Some{ik}, hi, ks2, k, v)(e3)
            ): {
              Bool.or(
                Bool.and(Bool.and(Bound.after(lo, k), Key.is_lt(k, ik)), Look.has(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, Some{ik}}, prev, k), v)),
                Bool.or(Binding.is_eq(Binding{ik, iv}, Binding{k, v}), _)
              )
                == Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(
                    Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)),
                    v
                  )
                ): Bool
            }
            Mst.has_pick.con(
              ~S,
              ~fetch,
              Key.cmp(k, ik),
              f,
              s,
              h,
              ik,
              iv,
              r,
              rest,
              l,
              prev,
              lo,
              hi,
              k,
              v,
              {==},
              Shared.Bool.and_true_left(Bound.after(lo, ik), Bound.before(ik, hi))(c2),
              Shared.Bool.and_true_right(Bound.after(lo, ik), Bound.before(ik, hi))(c2),
              Shared.Bool.and_true_left(
                Nat.is_eq(Key.level(ik), l),
                Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
              )(c1)
            )
        )(e2)
      )(e)

# the pieces of an opened node hold k bound to v exactly when k is in its
# bounds and a read of its subtree finds v
def Mst.has_open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ks: List<&2, Piece>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {Mst.open(~S, ~fetch, s, h, up, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Pieces.has(~S, ~fetch, q, s, ks, k, v)
    == Bool.and(
      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
      Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
    ): Bool
}:
  e => Mst.open_cases(
    ~S,
    ~fetch,
    s,
    h,
    up,
    lo,
    hi,
    ks,
    {
      Pieces.has(~S, ~fetch, q, s, ks, k, v)
        == Bool.and(
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
        ): Bool
    },
    +l => +left => +xs => ef => eh => en => elt => ee0 => ep =>
      %Equal.sym(Maybe<&2, Node>, Mst.node.in(~S, ~fetch, s, h, Room{up, lo, hi}), Some{Node{l, left, xs}}, en): {
        Pieces.has(~S, ~fetch, q, s, ks, k, v)
          == Bool.and(
            Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
            Look.has(Mst.look.at(h, _, Room{up, lo, hi}, k, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k)), v)
          ): Bool
      }
      Mst.has_pick(~S, ~fetch, q, s, h, xs, l, left, lo, hi, ks, k, v)(ep)
  )(e)

# an or of two ands with one first side is the and of it with the or
def Bool.and_or_left(a: Bool, -b: Bool, -c: Bool) -> {Bool.or(Bool.and(a, b), Bool.and(a, c)) == Bool.and(a, Bool.or(b, c)): Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# an and whose first side is False is False
def Bool.and_false_left(a: Bool, -b: Bool) -> {a == False{}: Bool} -> {Bool.and(a, b) == False{}: Bool}:
  match a:
    case False{}:
      e => {==}
    case True{}:
      e => Empty.absurd({b == False{}: Bool}, Shared.Bool.true_ne_false(e))

# a listing of a binding of k2 then of bs2 holds k bound to v as its pieces
# do, when bs2 does (ih)
def Mst.lists_bind(
  +p: List<&2, U32>,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  -bs2: List<&2, Binding>,
  t: Bool,
  be: Bool,
  -hr: Bool,
  et: {Key.leads(p, k2) == t: Bool},
  +ebe: {Binding.is_eq(Binding{k2, v2}, Binding{k, v}) == be: Bool},
  ih: {List.contains(~Binding, ~Binding.is_eq, bs2, Binding{k, v}) == Bool.and(Key.leads(p, k), hr): Bool}
) -> {
  List.contains(~Binding, ~Binding.is_eq, Shared.Bool.when(List<&2, Binding>, t, u => Binding{k2, v2} <> bs2, u => bs2), Binding{k, v})
    == Bool.and(Key.leads(p, k), Bool.or(be, hr)): Bool
}:
  match t be:
    case True{} True{}:
      +keq = Shared.List.is_eq_sound(
        ~U32,
        ~U32.is_eq,
        ~Shared.U32.laws(),
        k2,
        k
      )(
        Shared.List.all.if_hit(
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          u => Shared.List.is_eq(~U32, ~U32.is_eq, v2, v)
        )(ebe)
      )
      %Equal.sym(Bool, Binding.is_eq(Binding{k2, v2}, Binding{k, v}), True{}, ebe): {
        List.any.if(u => List.contains(~Binding, ~Binding.is_eq, bs2, Binding{k, v}), _) == Bool.and(Key.leads(p, k), True{}): Bool
      }
      %Equal.sym(
        Bool,
        Key.leads(p, k),
        True{},
        Equal.trans(
          Bool,
          Key.leads(p, k),
          Key.leads(p, k2),
          True{},
          Equal.cong(List<&2, U32>, Bool, x => Key.leads(p, x), k, k2, Equal.sym(List<&2, U32>, k2, k, keq)),
          et
        )
      ): {True{} == Bool.and(_, True{}): Bool}
      {==}
    case True{} False{}:
      %Equal.sym(Bool, Binding.is_eq(Binding{k2, v2}, Binding{k, v}), False{}, ebe): {
        List.any.if(u => List.contains(~Binding, ~Binding.is_eq, bs2, Binding{k, v}), _) == Bool.and(Key.leads(p, k), hr): Bool
      }
      ih
    case False{} True{}:
      +keq = Shared.List.is_eq_sound(
        ~U32,
        ~U32.is_eq,
        ~Shared.U32.laws(),
        k2,
        k
      )(
        Shared.List.all.if_hit(
          Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
          u => Shared.List.is_eq(~U32, ~U32.is_eq, v2, v)
        )(ebe)
      )
      +lkf = Equal.trans(
        Bool,
        Key.leads(p, k),
        Key.leads(p, k2),
        False{},
        Equal.cong(List<&2, U32>, Bool, x => Key.leads(p, x), k, k2, Equal.sym(List<&2, U32>, k2, k, keq)),
        et
      )
      %Equal.sym(Bool, Key.leads(p, k), False{}, lkf): {
        List.contains(~Binding, ~Binding.is_eq, bs2, Binding{k, v}) == Bool.and(_, True{}): Bool
      }
      Equal.trans(
        Bool,
        List.contains(~Binding, ~Binding.is_eq, bs2, Binding{k, v}),
        Bool.and(Key.leads(p, k), hr),
        False{},
        ih,
        Bool.and_false_left(Key.leads(p, k), hr)(lkf)
      )
    case False{} False{}:
      ih

# a subtree that a listing skips holds no key under its prefix
def Mst.lists_skip(
  l: Bool,
  i: Bool,
  -z: Bool,
  -h: Bool,
  -m: Bool,
  em: {m == False{}: Bool},
  imp: {l == True{}: Bool} -> {i == True{}: Bool} -> {m == True{}: Bool}
) -> {Bool.and(l, h) == Bool.and(l, Bool.or(Bool.and(i, z), h)): Bool}:
  match l i:
    case False{} y:
      {==}
    case True{} False{}:
      {==}
    case True{} True{}:
      Empty.absurd(
        {Bool.and(True{}, h) == Bool.and(True{}, Bool.or(Bool.and(True{}, z), h)): Bool},
        Shared.Bool.true_ne_false(Equal.trans(Bool, True{}, m, False{}, Equal.sym(Bool, m, True{}, imp({==})({==})), em))
      )

# Mst.lists_has at a subtree, by whether the listing reads it (t)
def Mst.lists_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  t: Bool,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  -bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>,
  et: {Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == t: Bool},
  ihr: @-b: List<&2, Binding> -> {Mst.range.go(~S, ~fetch, 1n+q, s, p, rest) == Some{b}: Maybe<&2, List<&2, Binding>>} -> {
    List.contains(~Binding, ~Binding.is_eq, b, Binding{k, v}) == Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)): Bool
  },
  ihs: @ks: List<&2, Piece> -> @-a: List<&2, Binding> -> {
    Mst.range.go(~S, ~fetch, q, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>
  } -> {List.contains(~Binding, ~Binding.is_eq, a, Binding{k, v}) == Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, q, s, ks, k, v)): Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Binding>>,
    t,
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
    == Some{bs}: Maybe<&2, List<&2, Binding>>
} -> {
  List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
    == Bool.and(
      Key.leads(p, k),
      Bool.or(
        Bool.and(
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
        ),
        Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
      )
    ): Bool
}:
  match t:
    case True{}:
      e => Maybe.bind_cases(
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
        ),
        bs,
        {
          List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
            == Bool.and(
              Key.leads(p, k),
              Bool.or(
                Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                ),
                Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
              )
            ): Bool
        },
        +ks => +eo => e2 => Maybe.bind_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, p, ks),
          a => Maybe.map(
            &2,
            List<&2, Binding>,
            List<&2, Binding>,
            b => List.append(&2, Binding, a, b),
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
          ),
          bs,
          {
            List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
              == Bool.and(
                Key.leads(p, k),
                Bool.or(
                  Bool.and(
                    Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                    Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                  ),
                  Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                )
              ): Bool
          },
          +a => ea => e3 => Maybe.map_cases(
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest),
            b => List.append(&2, Binding, a, b),
            bs,
            {
              List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
                == Bool.and(
                  Key.leads(p, k),
                  Bool.or(
                    Bool.and(
                      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                      Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                    ),
                    Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                  )
                ): Bool
            },
            +b => eb => e4 =>
              %e4: {
                List.contains(~Binding, ~Binding.is_eq, _, Binding{k, v})
                  == Bool.and(
                    Key.leads(p, k),
                    Bool.or(
                      Bool.and(
                        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                        Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                      ),
                      Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                    )
                  ): Bool
              }
              %Equal.sym(
                Bool,
                List.contains(~Binding, ~Binding.is_eq, List.append(&2, Binding, a, b), Binding{k, v}),
                Bool.or(List.contains(~Binding, ~Binding.is_eq, a, Binding{k, v}), List.contains(~Binding, ~Binding.is_eq, b, Binding{k, v})),
                Shared.List.contains_append(~Binding, ~Binding.is_eq, a, b, Binding{k, v})
              ): {
                _
                  == Bool.and(
                    Key.leads(p, k),
                    Bool.or(
                      Bool.and(
                        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                        Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                      ),
                      Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                    )
                  ): Bool
              }
              %Equal.sym(
                Bool,
                List.contains(~Binding, ~Binding.is_eq, a, Binding{k, v}),
                Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, q, s, ks, k, v)),
                ihs(ks)(a)(ea)
              ): {
                Bool.or(_, List.contains(~Binding, ~Binding.is_eq, b, Binding{k, v}))
                  == Bool.and(
                    Key.leads(p, k),
                    Bool.or(
                      Bool.and(
                        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                        Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                      ),
                      Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                    )
                  ): Bool
              }
              %Equal.sym(
                Bool,
                Pieces.has(~S, ~fetch, q, s, ks, k, v),
                Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                ),
                Mst.has_open(~S, ~fetch, q, s, h, up, lo, hi, ks, k, v)(eo)
              ): {
                Bool.or(Bool.and(Key.leads(p, k), _), List.contains(~Binding, ~Binding.is_eq, b, Binding{k, v}))
                  == Bool.and(
                    Key.leads(p, k),
                    Bool.or(
                      Bool.and(
                        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                        Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                      ),
                      Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                    )
                  ): Bool
              }
              %Equal.sym(
                Bool,
                List.contains(~Binding, ~Binding.is_eq, b, Binding{k, v}),
                Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)),
                ihr(b)(eb)
              ): {
                Bool.or(
                  Bool.and(
                    Key.leads(p, k),
                    Bool.and(
                      Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                      Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                    )
                  ),
                  _
                )
                  == Bool.and(
                    Key.leads(p, k),
                    Bool.or(
                      Bool.and(
                        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                        Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                      ),
                      Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
                    )
                  ): Bool
              }
              Bool.and_or_left(
                Key.leads(p, k),
                Bool.and(
                  Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                  Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
                ),
                Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
              )
          )(e3)
        )(e2)
      )(e)
    case False{}:
      e => Equal.trans(
        Bool,
        List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v}),
        Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)),
        Bool.and(
          Key.leads(p, k),
          Bool.or(
            Bool.and(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v)
            ),
            Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v)
          )
        ),
        ihr(bs)(e),
        Mst.lists_skip(
          Key.leads(p, k),
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Look.has(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k), v),
          Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v),
          Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
          et,
          Bound.meets(p, k, lo, hi)
        )
      )

# a listing of the pieces ps holds k bound to v exactly when k starts with
# the prefix and the pieces hold it
def Mst.lists_has(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +p: List<&2, U32>,
  ps: List<&2, Piece>,
  -bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {Mst.range.go(~S, ~fetch, f, s, p, ps) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {
  List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v}) == Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, f, s, ps, k, v)): Bool
}:
  match f ps:
    case x Nil{}:
      e =>
        %Shared.Maybe.some_inj(List<&2, Binding>, [], bs, e): {
          List.contains(~Binding, ~Binding.is_eq, _, Binding{k, v}) == Bool.and(Key.leads(p, k), False{}): Bool
        }
        Equal.sym(Bool, Bool.and(Key.leads(p, k), False{}), False{}, Shared.Bool.and_false_right(Key.leads(p, k)))
    case 0n Con{x, rest}:
      e => Empty.absurd(
        {
          List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v}) == Bool.and(Key.leads(p, k), Pieces.has(~S, ~fetch, 0n, s, x <> rest, k, v)): Bool
        },
        Shared.Maybe.none_ne_some(List<&2, Binding>, bs, e)
      )
    case 1n+(+q) Con{Piece.Bind{+k2, +v2}, +rest}:
      e => Maybe.map_cases(
        List<&2, Binding>,
        List<&2, Binding>,
        Mst.range.go(~S, ~fetch, 1n+q, s, p, rest),
        +bs2 => Shared.Bool.when(List<&2, Binding>, Key.leads(p, k2), u => Binding{k2, v2} <> bs2, u => bs2),
        bs,
        {
          List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v})
            == Bool.and(
              Key.leads(p, k),
              Bool.or(Binding.is_eq(Binding{k2, v2}, Binding{k, v}), Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v))
            ): Bool
        },
        +bs2 => e1 => e2 =>
          %e2: {
            List.contains(~Binding, ~Binding.is_eq, _, Binding{k, v})
              == Bool.and(
                Key.leads(p, k),
                Bool.or(Binding.is_eq(Binding{k2, v2}, Binding{k, v}), Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v))
              ): Bool
          }
          Mst.lists_bind(
            p,
            k2,
            v2,
            k,
            v,
            bs2,
            Key.leads(p, k2),
            Binding.is_eq(Binding{k2, v2}, Binding{k, v}),
            Pieces.has(~S, ~fetch, 1n+q, s, rest, k, v),
            {==},
            {==},
            Mst.lists_has(~S, ~fetch, 1n+q, s, p, rest, bs2, k, v)(e1)
          )
      )(e)
    case 1n+(+q) Con{Piece.Sub{+h, +up, +lo, +hi}, +rest}:
      e => Mst.lists_sub(
        ~S,
        ~fetch,
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        q,
        s,
        p,
        h,
        up,
        lo,
        hi,
        rest,
        bs,
        k,
        v,
        {==},
        b => eb => Mst.lists_has(~S, ~fetch, 1n+q, s, p, rest, b, k, v)(eb),
        ks => a => ea => Mst.lists_has(~S, ~fetch, q, s, p, ks, a, k, v)(ea)
      )(e)

# the bindings bs come in the order of their keys, after lo and before hi
def Bindings.within(bs: List<&2, Binding>, lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{Binding{+k, v}, rest}:
      Bool.and(Bool.and(Bound.after(lo, k), Bound.before(k, hi)), Bindings.within(rest, Some{k}, hi))

# bindings in order between two bounds are in order
def Bindings.within_sorted(bs: List<&2, Binding>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Bindings.within(bs, lo, hi) == True{}: Bool
} -> {Bindings.sorted(bs) == True{}: Bool}:
  match bs:
    case Nil{}:
      e => {==}
    case Con{a, Nil{}}:
      e => {==}
    case Con{Binding{+ka, +va}, Con{Binding{+kb, +vb}, +rest}}:
      +e =>
        +w = Shared.Bool.and_true_right(
          Bool.and(Bound.after(lo, ka), Bound.before(ka, hi)),
          Bindings.within(Binding{kb, vb} <> rest, Some{ka}, hi)
        )(e)
        Shared.List.all.if_both(
          Key.is_lt(ka, kb),
          u => Bindings.sorted(Binding{kb, vb} <> rest)
        )(
          Shared.Bool.and_true_left(
            Key.is_lt(ka, kb),
            Bound.before(kb, hi)
          )(
            Shared.Bool.and_true_left(
              Bool.and(Key.is_lt(ka, kb), Bound.before(kb, hi)),
              Bindings.within(rest, Some{kb}, hi)
            )(w)
          )
        )(Bindings.within_sorted(Binding{kb, vb} <> rest, Some{ka}, hi)(w))

# bindings after a key a are after a bound below a
def Bindings.within_weak(
  bs: List<&2, Binding>,
  +a: List<&2, U32>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Bindings.within(bs, Some{a}, hi) == True{}: Bool} -> {Bound.after(lo, a) == True{}: Bool} -> {
  Bindings.within(bs, lo, hi) == True{}: Bool
}:
  match bs:
    case Nil{}:
      e => g => {==}
    case Con{Binding{+k, +v}, +rest}:
      +e => g =>
        +x = Shared.Bool.and_true_left(Bool.and(Key.is_lt(a, k), Bound.before(k, hi)), Bindings.within(rest, Some{k}, hi))(e)
        Shared.Bool.and_both(
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Bindings.within(rest, Some{k}, hi)
        )(
          Shared.Bool.and_both(
            Bound.after(lo, k),
            Bound.before(k, hi)
          )(Bound.after_trans(lo, a, k)(g)(Shared.Bool.and_true_left(Key.is_lt(a, k), Bound.before(k, hi))(x)))(
            Shared.Bool.and_true_right(Key.is_lt(a, k), Bound.before(k, hi))(x)
          )
        )(Shared.Bool.and_true_right(Bool.and(Key.is_lt(a, k), Bound.before(k, hi)), Bindings.within(rest, Some{k}, hi))(e))

# bindings before m, the binding of m, then bindings after it, are in order
def Bindings.within_cons(
  a: List<&2, Binding>,
  +m: List<&2, U32>,
  +w: List<&2, U32>,
  +b: List<&2, Binding>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Bindings.within(a, lo, Some{m}) == True{}: Bool} -> {Bool.and(Bound.after(lo, m), Bound.before(m, hi)) == True{}: Bool} -> {
  Bindings.within(b, Some{m}, hi) == True{}: Bool
} -> {Bindings.within(List.append(&2, Binding, a, Binding{m, w} <> b), lo, hi) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hm => hb => Shared.Bool.and_both(Bool.and(Bound.after(lo, m), Bound.before(m, hi)), Bindings.within(b, Some{m}, hi))(hm)(hb)
    case Con{Binding{+k, +v}, +rest}:
      +ha => +hm => hb =>
        +x = Shared.Bool.and_true_left(Bool.and(Bound.after(lo, k), Key.is_lt(k, m)), Bindings.within(rest, Some{k}, Some{m}))(ha)
        +km = Shared.Bool.and_true_right(Bound.after(lo, k), Key.is_lt(k, m))(x)
        +mh = Shared.Bool.and_true_right(Bound.after(lo, m), Bound.before(m, hi))(hm)
        Shared.Bool.and_both(
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Bindings.within(List.append(&2, Binding, rest, Binding{m, w} <> b), Some{k}, hi)
        )(
          Shared.Bool.and_both(
            Bound.after(lo, k),
            Bound.before(k, hi)
          )(Shared.Bool.and_true_left(Bound.after(lo, k), Key.is_lt(k, m))(x))(Bound.before_trans(k, m, hi)(km)(mh))
        )(
          Bindings.within_cons(
            rest,
            m,
            w,
            b,
            Some{k},
            hi
          )(Shared.Bool.and_true_right(Bool.and(Bound.after(lo, k), Key.is_lt(k, m)), Bindings.within(rest, Some{k}, Some{m}))(ha))(
            Shared.Bool.and_both(Key.is_lt(k, m), Bound.before(m, hi))(km)(mh)
          )(hb)
        )

# bindings before m, then bindings after it, are in order
def Bindings.within_cat(
  a: List<&2, Binding>,
  +m: List<&2, U32>,
  +b: List<&2, Binding>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Bindings.within(a, lo, Some{m}) == True{}: Bool} -> {Bool.and(Bound.after(lo, m), Bound.before(m, hi)) == True{}: Bool} -> {
  Bindings.within(b, Some{m}, hi) == True{}: Bool
} -> {Bindings.within(List.append(&2, Binding, a, b), lo, hi) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hm => hb => Bindings.within_weak(b, m, lo, hi)(hb)(Shared.Bool.and_true_left(Bound.after(lo, m), Bound.before(m, hi))(hm))
    case Con{Binding{+k, +v}, +rest}:
      +ha => +hm => hb =>
        +x = Shared.Bool.and_true_left(Bool.and(Bound.after(lo, k), Key.is_lt(k, m)), Bindings.within(rest, Some{k}, Some{m}))(ha)
        +km = Shared.Bool.and_true_right(Bound.after(lo, k), Key.is_lt(k, m))(x)
        +mh = Shared.Bool.and_true_right(Bound.after(lo, m), Bound.before(m, hi))(hm)
        Shared.Bool.and_both(
          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
          Bindings.within(List.append(&2, Binding, rest, b), Some{k}, hi)
        )(
          Shared.Bool.and_both(
            Bound.after(lo, k),
            Bound.before(k, hi)
          )(Shared.Bool.and_true_left(Bound.after(lo, k), Key.is_lt(k, m))(x))(Bound.before_trans(k, m, hi)(km)(mh))
        )(
          Bindings.within_cat(
            rest,
            m,
            b,
            Some{k},
            hi
          )(Shared.Bool.and_true_right(Bool.and(Bound.after(lo, k), Key.is_lt(k, m)), Bindings.within(rest, Some{k}, Some{m}))(ha))(
            Shared.Bool.and_both(Key.is_lt(k, m), Bound.before(m, hi))(km)(mh)
          )(hb)
        )

# a listing with no levels left lists nothing
def Mst.range_zero(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +p: List<&2, U32>,
  ps: List<&2, Piece>,
  -bs: List<&2, Binding>
) -> {Mst.range.go(~S, ~fetch, 0n, s, p, ps) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {bs == []: List<&2, Binding>}:
  match ps:
    case Nil{}:
      e => Equal.sym(List<&2, Binding>, [], bs, Shared.Maybe.some_inj(List<&2, Binding>, [], bs, e))
    case Con{x, rest}:
      e => Empty.absurd({bs == []: List<&2, Binding>}, Shared.Maybe.none_ne_some(List<&2, Binding>, bs, e))

# Mst.range_sub at a subtree, by whether the listing reads it (t)
def Mst.range_sub.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  t: Bool,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +bs: List<&2, Binding>,
  -P: Type,
  k: @a: List<&2, Binding> -> @b: List<&2, Binding> -> {List.append(&2, Binding, a, b) == bs: List<&2, Binding>} -> {
    Mst.range.go(~S, ~fetch, 1n+q, s, p, rest) == Some{b}: Maybe<&2, List<&2, Binding>>
  } -> {Bindings.within(a, lo, hi) == True{}: Bool} -> P,
  ihc: @ks: List<&2, Piece> -> @a: List<&2, Binding> -> {
    Mst.open(~S, ~fetch, s, h, l, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, q, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Bindings.within(a, lo, hi) == True{}: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Binding>>,
    t,
    u => Maybe.bind(
      &2,
      List<&2, Piece>,
      List<&2, Binding>,
      Mst.open(~S, ~fetch, s, h, l, lo, hi),
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
    == Some{bs}: Maybe<&2, List<&2, Binding>>
} -> P:
  match t:
    case True{}:
      e => Maybe.bind_cases(
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, l, lo, hi),
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
        ),
        bs,
        P,
        +ks => eo => e2 => Maybe.bind_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, p, ks),
          a => Maybe.map(
            &2,
            List<&2, Binding>,
            List<&2, Binding>,
            b => List.append(&2, Binding, a, b),
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
          ),
          bs,
          P,
          +a => ea => e3 => Maybe.map_cases(
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest),
            b => List.append(&2, Binding, a, b),
            bs,
            P,
            b => eb => e4 => k(a)(b)(e4)(eb)(ihc(ks)(a)(eo)(ea))
          )(e3)
        )(e2)
      )(e)
    case False{}:
      e => k([])(bs)({==})(e)({==})

# a listing of the subtree m, then of the pieces rest, is a listing of m
# (whose bindings are in its bounds, by ihc), then one of rest
def Mst.range_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Hashes.Hash>,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +bs: List<&2, Binding>,
  -P: Type,
  k: @a: List<&2, Binding> -> @b: List<&2, Binding> -> {List.append(&2, Binding, a, b) == bs: List<&2, Binding>} -> {
    Mst.range.go(~S, ~fetch, 1n+q, s, p, rest) == Some{b}: Maybe<&2, List<&2, Binding>>
  } -> {Bindings.within(a, lo, hi) == True{}: Bool} -> P,
  ihc: @h: Hashes.Hash -> @ks: List<&2, Piece> -> @a: List<&2, Binding> -> {
    Mst.open(~S, ~fetch, s, h, l, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, q, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Bindings.within(a, lo, hi) == True{}: Bool}
) -> {Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(m, l, lo, hi, rest)) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> P:
  match m:
    case None{}:
      e => k([])(bs)({==})(e)({==})
    case Some{+h}:
      e => Mst.range_sub.at(
        ~S,
        ~fetch,
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        q,
        s,
        p,
        h,
        l,
        lo,
        hi,
        rest,
        bs,
        P,
        k,
        ks => a => ihc(h)(ks)(a)
      )(e)

# Mst.lists_within at an item of the key ik, by whether the prefix leads it (t)
def Mst.lists_within.bind(
  t: Bool,
  a: List<&2, Binding>,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +b: List<&2, Binding>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  ha: {Bindings.within(a, lo, Some{ik}) == True{}: Bool},
  hm: {Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)) == True{}: Bool},
  hb: {Bindings.within(b, Some{ik}, hi) == True{}: Bool}
) -> {
  Bindings.within(List.append(&2, Binding, a, Shared.Bool.when(List<&2, Binding>, t, u => Binding{ik, iv} <> b, u => b)), lo, hi) == True{}: Bool
}:
  match t:
    case True{}:
      Bindings.within_cons(a, ik, iv, b, lo, hi)(ha)(hm)(hb)
    case False{}:
      Bindings.within_cat(a, ik, b, lo, hi)(ha)(hm)(hb)

# a listing of the pieces of the items xs comes in order, between their bounds
def Mst.lists_within(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +p: List<&2, U32>,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +bs: List<&2, Binding>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, f, s, p, ks) == Some{bs}: Maybe<&2, List<&2, Binding>>
} -> {Bindings.within(bs, lo, hi) == True{}: Bool}:
  match f:
    case 0n:
      ep => e =>
        %Equal.sym(List<&2, Binding>, bs, [], Mst.range_zero(~S, ~fetch, s, p, ks, bs)(e)): {Bindings.within(_, lo, hi) == True{}: Bool}
        {==}
    case 1n+(+q):
      match xs:
        case Nil{}:
          ep => e => Mst.range_sub(
              ~S,
              ~fetch,
              prev,
              q,
              s,
              p,
              l,
              lo,
              hi,
              [],
              bs,
              {Bindings.within(bs, lo, hi) == True{}: Bool},
              a => b => e4 => eb => wa =>
                %e4: {Bindings.within(_, lo, hi) == True{}: Bool}
                %Shared.Maybe.some_inj(List<&2, Binding>, [], b, eb): {Bindings.within(List.append(&2, Binding, a, _), lo, hi) == True{}: Bool}
                %Equal.sym(List<&2, Binding>, List.append(&2, Binding, a, []), a, Shared.List.append_nil(Binding, a)): {
                  Bindings.within(_, lo, hi) == True{}: Bool
                }
                wa,
              h => ks2 => a => eo => ea => Mst.open_cases(
                ~S,
                ~fetch,
                s,
                h,
                l,
                lo,
                hi,
                ks2,
                {Bindings.within(a, lo, hi) == True{}: Bool},
                +l2 => +left2 => +xs2 => ef => eh => en => elt => ee0 => ep2 => Mst.lists_within(~S, ~fetch, q, s, p, xs2, l2, left2, lo, hi, ks2, a)(ep2)(ea)
              )(eo)
            )(
              Equal.trans(
                Maybe<&2, List<&2, Binding>>,
                Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(prev, l, lo, hi, [])),
                Mst.range.go(~S, ~fetch, 1n+q, s, p, ks),
                Some{bs},
                Equal.cong(
                  List<&2, Piece>,
                  Maybe<&2, List<&2, Binding>>,
                  x => Mst.range.go(~S, ~fetch, 1n+q, s, p, x),
                  Piece.sub(prev, l, lo, hi, []),
                  ks,
                  Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep)
                ),
                e
              )
            )
        case Con{Item{+ik, +iv, +r}, +rest}:
          ep => e => Maybe.when_cases(
            List<&2, Piece>,
            Bool.and(
              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
            ),
            u => Maybe.map(
              &2,
              List<&2, Piece>,
              List<&2, Piece>,
              ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
              Mst.pieces(rest, l, r, Some{ik}, hi)
            ),
            ks,
            {Bindings.within(bs, lo, hi) == True{}: Bool},
            +c => e2 => Maybe.map_cases(
              List<&2, Piece>,
              List<&2, Piece>,
              Mst.pieces(rest, l, r, Some{ik}, hi),
              ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
              ks,
              {Bindings.within(bs, lo, hi) == True{}: Bool},
              +ks2 => e3 => e4 =>
                +hm = Shared.Bool.and_true_right(
                  Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                  Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
                )(c)
                Mst.range_sub(
                  ~S,
                  ~fetch,
                  prev,
                  q,
                  s,
                  p,
                  l,
                  lo,
                  Some{ik},
                  Piece.Bind{ik, iv} <> ks2,
                  bs,
                  {Bindings.within(bs, lo, hi) == True{}: Bool},
                  a => b => e5 => eb => wa => Maybe.map_cases(
                    List<&2, Binding>,
                    List<&2, Binding>,
                    Mst.range.go(~S, ~fetch, 1n+q, s, p, ks2),
                    +b2 => Shared.Bool.when(List<&2, Binding>, Key.leads(p, ik), u => Binding{ik, iv} <> b2, u => b2),
                    b,
                    {Bindings.within(bs, lo, hi) == True{}: Bool},
                    +b2 => eb2 => e6 =>
                      %e5: {Bindings.within(_, lo, hi) == True{}: Bool}
                      %e6: {Bindings.within(List.append(&2, Binding, a, _), lo, hi) == True{}: Bool}
                      Mst.lists_within.bind(
                        Key.leads(p, ik),
                        a,
                        ik,
                        iv,
                        b2,
                        lo,
                        hi,
                        wa,
                        hm,
                        Mst.lists_within(~S, ~fetch, 1n+q, s, p, rest, l, r, Some{ik}, hi, ks2, b2)(e3)(eb2)
                      )
                  )(eb),
                  h => ks3 => a => eo => ea => Mst.open_cases(
                    ~S,
                    ~fetch,
                    s,
                    h,
                    l,
                    lo,
                    Some{ik},
                    ks3,
                    {Bindings.within(a, lo, Some{ik}) == True{}: Bool},
                    +l2 => +left2 => +xs2 => ef => eh => en => elt => ee0 => ep2 => Mst.lists_within(~S, ~fetch, q, s, p, xs2, l2, left2, lo, Some{ik}, ks3, a)(ep2)(ea)
                  )(eo)
                )(Equal.trans(
                  Maybe<&2, List<&2, Binding>>,
                  Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)),
                  Mst.range.go(~S, ~fetch, 1n+q, s, p, ks),
                  Some{bs},
                  Equal.cong(List<&2, Piece>, Maybe<&2, List<&2, Binding>>, x => Mst.range.go(~S, ~fetch, 1n+q, s, p, x), Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), ks, e4),
                  e
                ))
            )(e2)
          )(ep)

# a listing of a tree comes in the order of its keys
def Mst.lists_sorted(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +p: List<&2, U32>,
  +bs: List<&2, Binding>
) -> {Mst.range(~S, ~fetch, s, h, p) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {Bindings.sorted(bs) == True{}: Bool}:
  match h:
    case None{}:
      e =>
        %Shared.Maybe.some_inj(List<&2, Binding>, [], bs, e): {Bindings.sorted(_) == True{}: Bool}
        {==}
    case Some{+h2}:
      e => Mst.range_sub(
        ~S,
        ~fetch,
        Some{h2},
        63n,
        s,
        p,
        Mst.depth(),
        None{},
        None{},
        [],
        bs,
        {Bindings.sorted(bs) == True{}: Bool},
        +a => b => e4 => eb => wa =>
          %e4: {Bindings.sorted(_) == True{}: Bool}
          %Shared.Maybe.some_inj(List<&2, Binding>, [], b, eb): {Bindings.sorted(List.append(&2, Binding, a, _)) == True{}: Bool}
          %Equal.sym(List<&2, Binding>, List.append(&2, Binding, a, []), a, Shared.List.append_nil(Binding, a)): {
            Bindings.sorted(_) == True{}: Bool
          }
          Bindings.within_sorted(a, None{}, None{})(wa),
        h3 => ks => a => eo => ea => Mst.open_cases(
          ~S,
          ~fetch,
          s,
          h3,
          Mst.depth(),
          None{},
          None{},
          ks,
          {Bindings.within(a, None{}, None{}) == True{}: Bool},
          +l2 => +left2 => +xs2 => ef => eh => en => elt => ee0 => ep => Mst.lists_within(~S, ~fetch, 63n, s, p, xs2, l2, left2, None{}, None{}, ks, a)(ep)(ea)
        )(eo)
      )(e)

# the pieces of a root hold k bound to v exactly when a read of the root
# finds v
def Mst.lists_root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +v: List<&2, U32>
) -> {Pieces.has(~S, ~fetch, Mst.depth(), s, Mst.root(h), k, v) == Look.has(Mst.look(~S, ~fetch, s, h, k), v): Bool}:
  match h:
    case None{}:
      {==}
    case Some{+h2}:
      Equal.sym(
        Bool,
        Look.has(Mst.look(~S, ~fetch, s, Some{h2}, k), v),
        Bool.or(Look.has(Mst.look(~S, ~fetch, s, Some{h2}, k), v), False{}),
        Shared.Bool.or_false(Look.has(Mst.look(~S, ~fetch, s, Some{h2}, k), v))
      )

# One shape
# ---------

# the bindings of the subtree m under the prefix p, in the room of the level
# l between lo and hi, read q levels down: none when a node does not read
def Mst.sub_list(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  q: Nat,
  +s: S,
  +p: List<&2, U32>,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, Binding>>:
  match m:
    case None{}:
      Some{[]}
    case Some{+h}:
      Shared.Bool.when(
        Maybe<&2, List<&2, Binding>>,
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        u => Maybe.bind(
          &2,
          List<&2, Piece>,
          List<&2, Binding>,
          Mst.open(~S, ~fetch, s, h, l, lo, hi),
          ks => Mst.range.go(~S, ~fetch, q, s, p, ks)
        ),
        u => Some{[]}
      )

# the bindings of a subtree that a listing reads: those of its node's pieces
def Mst.sub_list_read(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -ks: List<&2, Piece>,
  -a: List<&2, Binding>,
  et: {Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == True{}: Bool},
  eo: {Mst.open(~S, ~fetch, s, h, l, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>},
  ea: {Mst.range.go(~S, ~fetch, q, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>}
) -> {Mst.sub_list(~S, ~fetch, q, s, p, Some{h}, l, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>}:
  %Equal.sym(Bool, Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)), True{}, et): {
    Shared.Bool.when(
      Maybe<&2, List<&2, Binding>>,
      _,
      u => Maybe.bind(
        &2,
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, l, lo, hi),
        ks2 => Mst.range.go(~S, ~fetch, q, s, p, ks2)
      ),
      u => Some{[]}
    )
      == Some{a}: Maybe<&2, List<&2, Binding>>
  }
  %Equal.sym(Maybe<&2, List<&2, Piece>>, Mst.open(~S, ~fetch, s, h, l, lo, hi), Some{ks}, eo): {
    Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, _, ks2 => Mst.range.go(~S, ~fetch, q, s, p, ks2))
      == Some{a}: Maybe<&2, List<&2, Binding>>
  }
  ea

# a subtree that a listing skips lists nothing
def Mst.sub_list_skip(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  et: {Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == False{}: Bool}
) -> {Mst.sub_list(~S, ~fetch, q, s, p, Some{h}, l, lo, hi) == Some{[]}: Maybe<&2, List<&2, Binding>>}:
  %Equal.sym(Bool, Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)), False{}, et): {
    Shared.Bool.when(
      Maybe<&2, List<&2, Binding>>,
      _,
      u => Maybe.bind(
        &2,
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, l, lo, hi),
        ks2 => Mst.range.go(~S, ~fetch, q, s, p, ks2)
      ),
      u => Some{[]}
    )
      == Some{[]}: Maybe<&2, List<&2, Binding>>
  }
  {==}

# Mst.range_list at a subtree, by whether the listing reads it (t)
def Mst.range_list.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  t: Bool,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +bs: List<&2, Binding>,
  -P: Type,
  k: @a: List<&2, Binding> -> @b: List<&2, Binding> -> {List.append(&2, Binding, a, b) == bs: List<&2, Binding>} -> {
    Mst.range.go(~S, ~fetch, 1n+q, s, p, rest) == Some{b}: Maybe<&2, List<&2, Binding>>
  } -> {Mst.sub_list(~S, ~fetch, q, s, p, Some{h}, l, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> P,
  et: {Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == t: Bool}
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Binding>>,
    t,
    u => Maybe.bind(
      &2,
      List<&2, Piece>,
      List<&2, Binding>,
      Mst.open(~S, ~fetch, s, h, l, lo, hi),
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
    == Some{bs}: Maybe<&2, List<&2, Binding>>
} -> P:
  match t:
    case True{}:
      e => Maybe.bind_cases(
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, l, lo, hi),
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
        ),
        bs,
        P,
        +ks => eo => e2 => Maybe.bind_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, p, ks),
          a => Maybe.map(
            &2,
            List<&2, Binding>,
            List<&2, Binding>,
            b => List.append(&2, Binding, a, b),
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
          ),
          bs,
          P,
          +a => ea => e3 => Maybe.map_cases(
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, 1n+q, s, p, rest),
            b => List.append(&2, Binding, a, b),
            bs,
            P,
            b => eb => e4 => k(a)(b)(e4)(eb)(Mst.sub_list_read(~S, ~fetch, q, s, p, h, l, lo, hi, ks, a, et, eo, ea))
          )(e3)
        )(e2)
      )(e)
    case False{}:
      e => k([])(bs)({==})(e)(Mst.sub_list_skip(~S, ~fetch, q, s, p, h, l, lo, hi, et))

# a listing of the subtree m, then of the pieces rest, is the listing of m,
# then one of rest
def Mst.range_list(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Hashes.Hash>,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +bs: List<&2, Binding>,
  -P: Type,
  k: @a: List<&2, Binding> -> @b: List<&2, Binding> -> {List.append(&2, Binding, a, b) == bs: List<&2, Binding>} -> {
    Mst.range.go(~S, ~fetch, 1n+q, s, p, rest) == Some{b}: Maybe<&2, List<&2, Binding>>
  } -> {Mst.sub_list(~S, ~fetch, q, s, p, m, l, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> P
) -> {Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(m, l, lo, hi, rest)) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> P:
  match m:
    case None{}:
      e => k([])(bs)({==})(e)({==})
    case Some{+h}:
      e => Mst.range_list.at(
        ~S,
        ~fetch,
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        q,
        s,
        p,
        h,
        l,
        lo,
        hi,
        rest,
        bs,
        P,
        k,
        {==}
      )(e)

# a listing with no levels left has no pieces
def Mst.range_zero_nil(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +p: List<&2, U32>,
  ps: List<&2, Piece>,
  -bs: List<&2, Binding>
) -> {Mst.range.go(~S, ~fetch, 0n, s, p, ps) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {ps == []: List<&2, Piece>}:
  match ps:
    case Nil{}:
      e => {==}
    case Con{x, rest}:
      e => Empty.absurd({x <> rest == []: List<&2, Piece>}, Shared.Maybe.none_ne_some(List<&2, Binding>, bs, e))

# a subtree, then a piece, is no empty run
def Mst.sub_ne_nil(
  m: Maybe<&2, Hashes.Hash>,
  -l: Nat,
  -lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  -x: Piece,
  -r: List<&2, Piece>
) -> {Piece.sub(m, l, lo, hi, x <> r) == []: List<&2, Piece>} -> Empty:
  match m:
    case None{}:
      e => Shared.Bool.false_ne_true(Equal.cong(List<&2, Piece>, Bool, ys => List.is_empty(&2, Piece, ys), x <> r, [], e))
    case Some{h}:
      e => Shared.Bool.false_ne_true(
        Equal.cong(List<&2, Piece>, Bool, ys => List.is_empty(&2, Piece, ys), Piece.Sub{h, l, lo, hi} <> (x <> r), [], e)
      )

# the items that give no piece: none, and no subtree before them
def Mst.pieces_empty(
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{[]}: Maybe<&2, List<&2, Piece>>} -> {Node{l, prev, xs} == Node{l, None{}, []}: Node}:
  match xs:
    case Nil{}:
      match prev:
        case None{}:
          e => {==}
        case Some{h}:
          e => Empty.absurd(
            {Node{l, Some{h}, []} == Node{l, None{}, []}: Node},
            Shared.Bool.false_ne_true(
              Equal.cong(
                List<&2, Piece>,
                Bool,
                ys => List.is_empty(&2, Piece, ys),
                [Piece.Sub{h, l, lo, hi}],
                [],
                Shared.Maybe.some_inj(List<&2, Piece>, [Piece.Sub{h, l, lo, hi}], [], e)
              )
            )
          )
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
        [],
        {Node{l, prev, Item{k, v, r} <> rest} == Node{l, None{}, []}: Node},
        c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{k}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{k}, Piece.Bind{k, v} <> ps2),
          [],
          {Node{l, prev, Item{k, v, r} <> rest} == Node{l, None{}, []}: Node},
          ks2 => e3 => e4 => Empty.absurd(
            {Node{l, prev, Item{k, v, r} <> rest} == Node{l, None{}, []}: Node},
            Mst.sub_ne_nil(prev, l, lo, Some{k}, Piece.Bind{k, v}, ks2)(e4)
          )
        )(e2)
      )(e)

# the keys of the bindings bs have levels below n
def Bindings.below(bs: List<&2, Binding>, +n: Nat) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{Binding{k, v}, rest}:
      Bool.and(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))

# bindings below n, then bindings below n, are below n
def Bindings.below_append(a: List<&2, Binding>, +b: List<&2, Binding>, +n: Nat) -> {Bindings.below(a, n) == True{}: Bool} -> {
  Bindings.below(b, n) == True{}: Bool
} -> {Bindings.below(List.append(&2, Binding, a, b), n) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hb => hb
    case Con{Binding{+k, +v}, +rest}:
      +ha => hb => Shared.Bool.and_both(
        Nat.is_lt(Key.level(k), n),
        Bindings.below(List.append(&2, Binding, rest, b), n)
      )(Shared.Bool.and_true_left(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(ha))(
        Bindings.below_append(rest, b, n)(Shared.Bool.and_true_right(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(ha))(hb)
      )

# bindings below n are below any m from n on
def Bindings.below_mono(a: List<&2, Binding>, +n: Nat, +m: Nat) -> {Bindings.below(a, n) == True{}: Bool} -> {
  Nat.is_le(n, m) == True{}: Bool
} -> {Bindings.below(a, m) == True{}: Bool}:
  match a:
    case Nil{}:
      h => g => {==}
    case Con{Binding{+k, +v}, +rest}:
      +h => +g => Shared.Bool.and_both(
        Nat.is_lt(Key.level(k), m),
        Bindings.below(rest, m)
      )(Shared.Nat.lt_le(Key.level(k), n, m)(Shared.Bool.and_true_left(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(h))(g))(
        Bindings.below_mono(rest, n, m)(Shared.Bool.and_true_right(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(h))(g)
      )

# the bindings b, with the binding of k first when t holds, are below n
def Bindings.below_when(t: Bool, +k: List<&2, U32>, +v: List<&2, U32>, b: List<&2, Binding>, +n: Nat) -> {
  Nat.is_lt(Key.level(k), n) == True{}: Bool
} -> {Bindings.below(b, n) == True{}: Bool} -> {
  Bindings.below(Shared.Bool.when(List<&2, Binding>, t, u => Binding{k, v} <> b, u => b), n) == True{}: Bool
}:
  match t:
    case True{}:
      hk => hb => Shared.Bool.and_both(Nat.is_lt(Key.level(k), n), Bindings.below(b, n))(hk)(hb)
    case False{}:
      hk => hb => hb

# a key of the bindings bs has the level l
def Bindings.has_level(bs: List<&2, Binding>, +l: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Binding{k, v}, rest}:
      Bool.or(Nat.is_eq(Key.level(k), l), Bindings.has_level(rest, l))

# bindings that hold a key of the level l, after others, still do
def Bindings.has_level_right(a: List<&2, Binding>, +b: List<&2, Binding>, +l: Nat) -> {Bindings.has_level(b, l) == True{}: Bool} -> {
  Bindings.has_level(List.append(&2, Binding, a, b), l) == True{}: Bool
}:
  match a:
    case Nil{}:
      h => h
    case Con{Binding{+k, +v}, +rest}:
      h =>
        %Equal.sym(Bool, Bindings.has_level(List.append(&2, Binding, rest, b), l), True{}, Bindings.has_level_right(rest, b, l)(h)): {
          Bool.or(Nat.is_eq(Key.level(k), l), _) == True{}: Bool
        }
        Shared.Bool.or_true_right(Nat.is_eq(Key.level(k), l))

# Bindings.has_level_lt at a binding of k, by whether k has the level l (t)
def Bindings.has_level_lt.at(
  t: Bool,
  +k: List<&2, U32>,
  +l: Nat,
  +n: Nat,
  rest: List<&2, Binding>,
  et: {Nat.is_eq(Key.level(k), l) == t: Bool},
  ih: {Bindings.has_level(rest, l) == True{}: Bool} -> {Nat.is_lt(l, n) == True{}: Bool}
) -> {Bool.and(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n)) == True{}: Bool} -> {
  Bool.or(t, Bindings.has_level(rest, l)) == True{}: Bool
} -> {Nat.is_lt(l, n) == True{}: Bool}:
  match t:
    case True{}:
      hb => hh =>
        %Shared.Nat.is_eq_sound(Key.level(k), l)(et): {Nat.is_lt(_, n) == True{}: Bool}
        Shared.Bool.and_true_left(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(hb)
    case False{}:
      hb => hh => ih(hh)

# a key of the level l among bindings below n has l below n
def Bindings.has_level_lt(bs: List<&2, Binding>, +l: Nat, +n: Nat) -> {Bindings.below(bs, n) == True{}: Bool} -> {
  Bindings.has_level(bs, l) == True{}: Bool
} -> {Nat.is_lt(l, n) == True{}: Bool}:
  match bs:
    case Nil{}:
      hb => hh => Empty.absurd({Nat.is_lt(l, n) == True{}: Bool}, Shared.Bool.false_ne_true(hh))
    case Con{Binding{+k, +v}, +rest}:
      +hb => hh => Bindings.has_level_lt.at(
        Nat.is_eq(Key.level(k), l),
        k,
        l,
        n,
        rest,
        {==},
        Bindings.has_level_lt(rest, l, n)(Shared.Bool.and_true_right(Nat.is_lt(Key.level(k), n), Bindings.below(rest, n))(hb))
      )(hb)(hh)

# bindings a then the empty rest b are a
def Bindings.cat_nil(+a: List<&2, Binding>, -b: List<&2, Binding>, -c: List<&2, Binding>) -> {
  Some{[]} == Some{b}: Maybe<&2, List<&2, Binding>>
} -> {List.append(&2, Binding, a, b) == c: List<&2, Binding>} -> {a == c: List<&2, Binding>}:
  eb => e => Equal.trans(
    List<&2, Binding>,
    a,
    List.append(&2, Binding, a, b),
    c,
    Equal.trans(
      List<&2, Binding>,
      a,
      List.append(&2, Binding, a, []),
      List.append(&2, Binding, a, b),
      Equal.sym(List<&2, Binding>, List.append(&2, Binding, a, []), a, Shared.List.append_nil(Binding, a)),
      Equal.cong(
        List<&2, Binding>,
        List<&2, Binding>,
        y => List.append(&2, Binding, a, y),
        [],
        b,
        Shared.Maybe.some_inj(List<&2, Binding>, [], b, eb)
      )
    ),
    e
  )

# a < b gives a + 1 <= b
def Nat.lt_le_succ(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(1n+a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => Shared.Nat.le_zero(q)
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(2n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      h => Nat.lt_le_succ(p, q)(h)

# a <= b and b <= a give a == b
def Nat.lt_succ_eq(+a: Nat, +b: Nat) -> {Nat.is_lt(a, 1n+b) == True{}: Bool} -> {Nat.is_lt(b, 1n+a) == True{}: Bool} -> {a == b: Nat}:
  h => g => Shared.Nat.is_eq_sound(
    a,
    b
  )(
    Equal.trans(
      Bool,
      Nat.is_eq(a, b),
      Bool.and(Nat.is_le(a, b), Nat.is_le(b, a)),
      True{},
      Equal.sym(Bool, Bool.and(Nat.is_le(a, b), Nat.is_le(b, a)), Nat.is_eq(a, b), Shared.Nat.le_both(a, b)),
      Shared.Bool.and_both(Nat.is_le(a, b), Nat.is_le(b, a))(Shared.Nat.lt_succ_le(a, b)(h))(Shared.Nat.lt_succ_le(b, a)(g))
    )
  )

# a key of the level l has a level below l + 1
def Mst.level_lt(+k: List<&2, U32>, +l: Nat) -> {Nat.is_eq(Key.level(k), l) == True{}: Bool} -> {
  Nat.is_lt(Key.level(k), 1n+l) == True{}: Bool
}:
  e =>
    %Equal.sym(Nat, Key.level(k), l, Shared.Nat.is_eq_sound(Key.level(k), l)(e)): {Nat.is_lt(_, 1n+l) == True{}: Bool}
    Shared.Nat.lt_succ(l)

# an or whose first side is True is True
def Bool.or_true_left(a: Bool, -b: Bool) -> {a == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({b == True{}: Bool}, Shared.Bool.false_ne_true(e))

# an or whose second side is True is True
def Bool.or_true_of(a: Bool, -b: Bool) -> {b == True{}: Bool} -> {Bool.or(a, b) == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => e

# the bindings of a subtree in the room of the level l have levels below l
def Mst.sub_below(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  q: Nat,
  +s: S,
  +p: List<&2, U32>,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +a: List<&2, Binding>,
  ihn: @xs: List<&2, Item> -> @l2: Nat -> @left: Maybe<&2, Hashes.Hash> -> @ks: List<&2, Piece> -> {
    Mst.pieces(xs, l2, left, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, q, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Bindings.below(a, 1n+l2) == True{}: Bool}
) -> {Mst.sub_list(~S, ~fetch, q, s, p, m, l, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Bindings.below(a, l) == True{}: Bool}:
  match m:
    case None{}:
      e =>
        %Shared.Maybe.some_inj(List<&2, Binding>, [], a, e): {Bindings.below(_, l) == True{}: Bool}
        {==}
    case Some{+h}:
      e => Shared.Bool.when_cases(
        Maybe<&2, List<&2, Binding>>,
        x => {x == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Bindings.below(a, l) == True{}: Bool},
        Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
        u => Maybe.bind(
          &2,
          List<&2, Piece>,
          List<&2, Binding>,
          Mst.open(~S, ~fetch, s, h, l, lo, hi),
          ks => Mst.range.go(~S, ~fetch, q, s, p, ks)
        ),
        u => Some{[]},
        et => e2 => Maybe.bind_cases(
          List<&2, Piece>,
          List<&2, Binding>,
          Mst.open(~S, ~fetch, s, h, l, lo, hi),
          ks => Mst.range.go(~S, ~fetch, q, s, p, ks),
          a,
          {Bindings.below(a, l) == True{}: Bool},
          +ks => eo => ea => Mst.open_cases(
            ~S,
            ~fetch,
            s,
            h,
            l,
            lo,
            hi,
            ks,
            {Bindings.below(a, l) == True{}: Bool},
            +l2 => +left => +xs => ef => eh => en => elt => ee0 => ep => Bindings.below_mono(
              a,
              1n+l2,
              l
            )(ihn(xs)(l2)(left)(ks)(ep)(ea))(Nat.lt_le_succ(l2, l)(elt))
          )(eo)
        )(e2),
        et => e2 =>
          %Shared.Maybe.some_inj(List<&2, Binding>, [], a, e2): {Bindings.below(_, l) == True{}: Bool}
          {==}
      )(e)

# a listing of the pieces of a node of the level l has levels up to l
def Mst.lists_below(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +p: List<&2, U32>,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, f, s, p, ks) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Bindings.below(a, 1n+l) == True{}: Bool}:
  match f:
    case 0n:
      ep => e =>
        %Equal.sym(List<&2, Binding>, a, [], Mst.range_zero(~S, ~fetch, s, p, ks, a)(e)): {Bindings.below(_, 1n+l) == True{}: Bool}
        {==}
    case 1n+(+q):
      match xs:
        case Nil{}:
          ep => e => Mst.range_list(
            ~S,
            ~fetch,
            prev,
            q,
            s,
            p,
            l,
            lo,
            hi,
            [],
            a,
            {Bindings.below(a, 1n+l) == True{}: Bool},
            +a1 => b => e4 => eb => esl =>
              %Bindings.cat_nil(a1, b, a)(eb)(e4): {Bindings.below(_, 1n+l) == True{}: Bool}
              Bindings.below_mono(
                a1,
                l,
                1n+l
              )(
                Mst.sub_below(
                  ~S,
                  ~fetch,
                  q,
                  s,
                  p,
                  prev,
                  l,
                  lo,
                  hi,
                  a1,
                  xs2 => l2 => left2 => ks2 => ep2 => ea2 => Mst.lists_below(~S, ~fetch, q, s, p, xs2, l2, left2, lo, hi, ks2, a1)(ep2)(ea2)
                )(esl)
              )(Shared.Nat.le_succ(l, l)(Shared.Nat.le_refl(l)))
          )(
            Equal.trans(
              Maybe<&2, List<&2, Binding>>,
              Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(prev, l, lo, hi, [])),
              Mst.range.go(~S, ~fetch, 1n+q, s, p, ks),
              Some{a},
              Equal.cong(
                List<&2, Piece>,
                Maybe<&2, List<&2, Binding>>,
                x => Mst.range.go(~S, ~fetch, 1n+q, s, p, x),
                Piece.sub(prev, l, lo, hi, []),
                ks,
                Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep)
              ),
              e
            )
          )
        case Con{Item{+ik, +iv, +r}, +rest}:
          ep => e => Maybe.when_cases(
            List<&2, Piece>,
            Bool.and(
              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
            ),
            u => Maybe.map(
              &2,
              List<&2, Piece>,
              List<&2, Piece>,
              ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
              Mst.pieces(rest, l, r, Some{ik}, hi)
            ),
            ks,
            {Bindings.below(a, 1n+l) == True{}: Bool},
            +c => e2 => Maybe.map_cases(
              List<&2, Piece>,
              List<&2, Piece>,
              Mst.pieces(rest, l, r, Some{ik}, hi),
              ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
              ks,
              {Bindings.below(a, 1n+l) == True{}: Bool},
              +ks2 => e3 => e4 => Mst.range_list(
                ~S,
                ~fetch,
                prev,
                q,
                s,
                p,
                l,
                lo,
                Some{ik},
                Piece.Bind{ik, iv} <> ks2,
                a,
                {Bindings.below(a, 1n+l) == True{}: Bool},
                +c1 => b => e5 => eb => esl => Maybe.map_cases(
                  List<&2, Binding>,
                  List<&2, Binding>,
                  Mst.range.go(~S, ~fetch, 1n+q, s, p, ks2),
                  +b2 => Shared.Bool.when(List<&2, Binding>, Key.leads(p, ik), u => Binding{ik, iv} <> b2, u => b2),
                  b,
                  {Bindings.below(a, 1n+l) == True{}: Bool},
                  +b2 => eb2 => e6 =>
                    %e5: {Bindings.below(_, 1n+l) == True{}: Bool}
                    %e6: {Bindings.below(List.append(&2, Binding, c1, _), 1n+l) == True{}: Bool}
                    Bindings.below_append(
                      c1,
                      Shared.Bool.when(List<&2, Binding>, Key.leads(p, ik), u => Binding{ik, iv} <> b2, u => b2),
                      1n+l
                    )(
                      Bindings.below_mono(
                        c1,
                        l,
                        1n+l
                      )(
                        Mst.sub_below(
                          ~S,
                          ~fetch,
                          q,
                          s,
                          p,
                          prev,
                          l,
                          lo,
                          Some{ik},
                          c1,
                          xs2 => l2 => left2 => ks3 => ep2 => ea2 => Mst.lists_below(~S, ~fetch, q, s, p, xs2, l2, left2, lo, Some{ik}, ks3, c1)(ep2)(ea2)
                        )(esl)
                      )(Shared.Nat.le_succ(l, l)(Shared.Nat.le_refl(l)))
                    )(
                      Bindings.below_when(
                        Key.leads(p, ik),
                        ik,
                        iv,
                        b2,
                        1n+l
                      )(
                        Mst.level_lt(
                          ik,
                          l
                        )(
                          Shared.Bool.and_true_left(
                            Nat.is_eq(Key.level(ik), l),
                            Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
                          )(
                            Shared.Bool.and_true_left(
                              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
                            )(c)
                          )
                        )
                      )(Mst.lists_below(~S, ~fetch, 1n+q, s, p, rest, l, r, Some{ik}, hi, ks2, b2)(e3)(eb2))
                    )
                )(eb)
              )(
                Equal.trans(
                  Maybe<&2, List<&2, Binding>>,
                  Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)),
                  Mst.range.go(~S, ~fetch, 1n+q, s, p, ks),
                  Some{a},
                  Equal.cong(
                    List<&2, Piece>,
                    Maybe<&2, List<&2, Binding>>,
                    x => Mst.range.go(~S, ~fetch, 1n+q, s, p, x),
                    Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2),
                    ks,
                    e4
                  ),
                  e
                )
              )
            )(e2)
          )(ep)

# Mst.lists_level at the first item of the key ik, read f levels down
def Mst.lists_level.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +ks2: List<&2, Piece>,
  +a: List<&2, Binding>,
  lvl: {Nat.is_eq(Key.level(ik), l) == True{}: Bool}
) -> {
  Mst.range.go(~S, ~fetch, f, s, [], Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Bindings.has_level(a, l) == True{}: Bool}:
  match f:
    case 0n:
      e => Empty.absurd(
        {Bindings.has_level(a, l) == True{}: Bool},
        Mst.sub_ne_nil(
          prev,
          l,
          lo,
          Some{ik},
          Piece.Bind{ik, iv},
          ks2
        )(Mst.range_zero_nil(~S, ~fetch, s, [], Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), a)(e))
      )
    case 1n+(+q):
      e => Mst.range_list(
        ~S,
        ~fetch,
        prev,
        q,
        s,
        [],
        l,
        lo,
        Some{ik},
        Piece.Bind{ik, iv} <> ks2,
        a,
        {Bindings.has_level(a, l) == True{}: Bool},
        +c1 => b => e5 => eb => esl => Maybe.map_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2),
          +b2 => Shared.Bool.when(List<&2, Binding>, Key.leads([], ik), u => Binding{ik, iv} <> b2, u => b2),
          b,
          {Bindings.has_level(a, l) == True{}: Bool},
          +b2 => eb2 => e6 =>
            %e5: {Bindings.has_level(_, l) == True{}: Bool}
            %e6: {Bindings.has_level(List.append(&2, Binding, c1, _), l) == True{}: Bool}
            Bindings.has_level_right(
              c1,
              Binding{ik, iv} <> b2,
              l
            )(Bool.or_true_left(Nat.is_eq(Key.level(ik), l), Bindings.has_level(b2, l))(lvl))
        )(eb)
      )(e)

# a listing of the pieces of a node of the level l with an item, under no
# prefix, holds a key of the level l
def Mst.lists_level(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {List.is_empty(&2, Item, xs) == False{}: Bool} -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, f, s, [], ks) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Bindings.has_level(a, l) == True{}: Bool}:
  match xs:
    case Nil{}:
      ee => ep => e => Empty.absurd({Bindings.has_level(a, l) == True{}: Bool}, Shared.Bool.true_ne_false(ee))
    case Con{Item{+ik, +iv, +r}, +rest}:
      ee => ep => e => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {Bindings.has_level(a, l) == True{}: Bool},
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {Bindings.has_level(a, l) == True{}: Bool},
          +ks2 => e3 => e4 => Mst.lists_level.at(
            ~S,
            ~fetch,
            f,
            s,
            ik,
            iv,
            l,
            prev,
            lo,
            ks2,
            a,
            Shared.Bool.and_true_left(
              Nat.is_eq(Key.level(ik), l),
              Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
            )(
              Shared.Bool.and_true_left(
                Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
              )(c)
            )
          )(
            Equal.trans(
              Maybe<&2, List<&2, Binding>>,
              Mst.range.go(~S, ~fetch, f, s, [], Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)),
              Mst.range.go(~S, ~fetch, f, s, [], ks),
              Some{a},
              Equal.cong(
                List<&2, Piece>,
                Maybe<&2, List<&2, Binding>>,
                x => Mst.range.go(~S, ~fetch, f, s, [], x),
                Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2),
                ks,
                e4
              ),
              e
            )
          )
        )(e2)
      )(ep)

# a key of the level l has no level below l
def Mst.level_clash(+k: List<&2, U32>, +l: Nat) -> {Nat.is_eq(Key.level(k), l) == True{}: Bool} -> {
  Nat.is_lt(Key.level(k), l) == True{}: Bool
} -> Empty:
  e => g => Shared.Bool.true_ne_false(
    Equal.trans(
      Bool,
      True{},
      Nat.is_lt(Key.level(k), l),
      False{},
      Equal.sym(Bool, Nat.is_lt(Key.level(k), l), True{}, g),
      Equal.trans(
        Bool,
        Nat.is_lt(Key.level(k), l),
        Nat.is_lt(l, l),
        False{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(z, l), Key.level(k), l, Shared.Nat.is_eq_sound(Key.level(k), l)(e)),
        Shared.Nat.lt_irrefl(l)
      )
    )
  )

# bindings below the level l hold no key of the level l
def Bindings.level_clash(+a: List<&2, Binding>, +l: Nat) -> {Bindings.below(a, l) == True{}: Bool} -> {
  Bindings.has_level(a, l) == True{}: Bool
} -> Empty:
  hb => hh => Shared.Bool.true_ne_false(
    Equal.trans(Bool, True{}, Nat.is_lt(l, l), False{}, Equal.sym(Bool, Nat.is_lt(l, l), True{}, Bindings.has_level_lt(a, l, l)(hb)(hh)), Shared.Nat.lt_irrefl(l))
  )

# the value of a binding
def Binding.value(b: Binding) -> List<&2, U32>:
  match b:
    case Binding{k, v}:
      v

# a node of the level l, left subtree p, and the binding of k to v, with the
# left subtree and the items of n after it
def Node.under(n: Node, +l: Nat, +p: Maybe<&2, Hashes.Hash>, +k: List<&2, U32>, +v: List<&2, U32>) -> Node:
  match n:
    case Node{x, left, xs}:
      Node{l, p, Item{k, v, left} <> xs}

# two listings of a subtree below the level l, a binding of the level l, and
# more, that are equal, have equal parts
def Bindings.split_eq(
  c1: List<&2, Binding>,
  c2: List<&2, Binding>,
  +x1: Binding,
  +x2: Binding,
  +r1: List<&2, Binding>,
  +r2: List<&2, Binding>,
  +l: Nat,
  -P: Type,
  k: {c1 == c2: List<&2, Binding>} -> {x1 == x2: Binding} -> {r1 == r2: List<&2, Binding>} -> P
) -> {
  List.append(&2, Binding, c1, x1 <> r1) == List.append(&2, Binding, c2, x2 <> r2): List<&2, Binding>
} -> {Bindings.below(c1, l) == True{}: Bool} -> {Bindings.below(c2, l) == True{}: Bool} -> {
  Nat.is_eq(Key.level(Binding.key(x1)), l) == True{}: Bool
} -> {Nat.is_eq(Key.level(Binding.key(x2)), l) == True{}: Bool} -> P:
  match c1 c2:
    case Nil{} Nil{}:
      +e => h1 => h2 => g1 => g2 => k({==})(Shared.List.head_eq(Binding, x1, x2, r1, r2, e))(Shared.List.tail_eq(Binding, x1, x2, r1, r2, e))
    case Nil{} Con{Binding{+ky, +vy}, +cr}:
      e => h1 => h2 => g1 => g2 => Empty.absurd(
        P,
        Mst.level_clash(
          ky,
          l
        )(
          Equal.trans(
            Bool,
            Nat.is_eq(Key.level(ky), l),
            Nat.is_eq(Key.level(Binding.key(x1)), l),
            True{},
            Equal.cong(
              Binding,
              Bool,
              z => Nat.is_eq(Key.level(Binding.key(z)), l),
              Binding{ky, vy},
              x1,
              Equal.sym(
                Binding,
                x1,
                Binding{ky, vy},
                Shared.List.head_eq(Binding, x1, Binding{ky, vy}, r1, List.append(&2, Binding, cr, x2 <> r2), e)
              )
            ),
            g1
          )
        )(Shared.Bool.and_true_left(Nat.is_lt(Key.level(ky), l), Bindings.below(cr, l))(h2))
      )
    case Con{Binding{+ky, +vy}, +cr} Nil{}:
      e => h1 => h2 => g1 => g2 => Empty.absurd(
        P,
        Mst.level_clash(
          ky,
          l
        )(
          Equal.trans(
            Bool,
            Nat.is_eq(Key.level(ky), l),
            Nat.is_eq(Key.level(Binding.key(x2)), l),
            True{},
            Equal.cong(
              Binding,
              Bool,
              z => Nat.is_eq(Key.level(Binding.key(z)), l),
              Binding{ky, vy},
              x2,
              Shared.List.head_eq(Binding, Binding{ky, vy}, x2, List.append(&2, Binding, cr, x1 <> r1), r2, e)
            ),
            g2
          )
        )(Shared.Bool.and_true_left(Nat.is_lt(Key.level(ky), l), Bindings.below(cr, l))(h1))
      )
    case Con{Binding{+ky1, +vy1}, +cr1} Con{Binding{+ky2, +vy2}, +cr2}:
      +e => h1 => h2 => g1 => g2 => Bindings.split_eq(
        cr1,
        cr2,
        x1,
        x2,
        r1,
        r2,
        l,
        P,
        ec => k(
          Shared.List.cons_eq(
            Binding,
            Binding{ky1, vy1},
            Binding{ky2, vy2},
            cr1,
            cr2,
            Shared.List.head_eq(
              Binding,
              Binding{ky1, vy1},
              Binding{ky2, vy2},
              List.append(&2, Binding, cr1, x1 <> r1),
              List.append(&2, Binding, cr2, x2 <> r2),
              e
            ),
            ec
          )
        )
      )(
        Shared.List.tail_eq(
          Binding,
          Binding{ky1, vy1},
          Binding{ky2, vy2},
          List.append(&2, Binding, cr1, x1 <> r1),
          List.append(&2, Binding, cr2, x2 <> r2),
          e
        )
      )(Shared.Bool.and_true_right(Nat.is_lt(Key.level(ky1), l), Bindings.below(cr1, l))(h1))(
        Shared.Bool.and_true_right(Nat.is_lt(Key.level(ky2), l), Bindings.below(cr2, l))(h2)
      )(g1)(g2)

# a key before the empty bound hi of a node meets every listing
def Bound.meets_nil(lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> {Bound.before([], hi) == True{}: Bool} -> {
  Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)) == True{}: Bool
}:
  match lo hi:
    case None{} None{}:
      h => {==}
    case None{} Some{b}:
      h => h
    case Some{+a} None{}:
      h =>
        %Equal.sym(Bool, Key.is_lt(a, []), False{}, Key.lt_nil(a)): {Bool.and(Bool.or(_, Key.leads([], a)), True{}) == True{}: Bool}
        {==}
    case Some{+a} Some{b}:
      h =>
        %Equal.sym(Bool, Key.is_lt(a, []), False{}, Key.lt_nil(a)): {Bool.and(Bool.or(_, Key.leads([], a)), Key.is_lt([], b)) == True{}: Bool}
        h

# no key is before the empty key: before it is the key that has words
def Key.lt_nil_left(k: List<&2, U32>) -> {Key.is_lt([], k) == Bool.not(List.is_empty(&2, U32, k)): Bool}:
  match k:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a subtree whose bounds hold keys lists the bindings of its node
def Mst.sub_list_on(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  -a: List<&2, Binding>
) -> {Bound.before([], hi) == True{}: Bool} -> {Mst.sub_list(~S, ~fetch, f, s, [], Some{h}, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
  Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, up, lo, hi), ks => Mst.range.go(~S, ~fetch, f, s, [], ks))
    == Some{a}: Maybe<&2, List<&2, Binding>>
}:
  hb => e => Equal.trans(
    Maybe<&2, List<&2, Binding>>,
    Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, up, lo, hi), ks => Mst.range.go(~S, ~fetch, f, s, [], ks)),
    Mst.sub_list(~S, ~fetch, f, s, [], Some{h}, up, lo, hi),
    Some{a},
    Equal.cong(
      Bool,
      Maybe<&2, List<&2, Binding>>,
      t => Shared.Bool.when(
        Maybe<&2, List<&2, Binding>>,
        t,
        u => Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, up, lo, hi), ks => Mst.range.go(~S, ~fetch, f, s, [], ks)),
        u => Some{[]}
      ),
      True{},
      Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)),
      Equal.sym(Bool, Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)), True{}, Bound.meets_nil(lo, hi)(hb))
    ),
    e
  )

# a subtree whose bounds hold keys lists a binding
def Mst.canon_sub.one(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +a: List<&2, Binding>,
  hb: {Bound.before([], hi) == True{}: Bool}
) -> {Some{[]} == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
  Mst.sub_list(~S, ~fetch, f, s, [], Some{h}, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> Empty:
  e0 => e => Maybe.bind_cases(
    List<&2, Piece>,
    List<&2, Binding>,
    Mst.open(~S, ~fetch, s, h, up, lo, hi),
    ks => Mst.range.go(~S, ~fetch, f, s, [], ks),
    a,
    Empty,
    +ks => eo => ea => Mst.open_cases(
      ~S,
      ~fetch,
      s,
      h,
      up,
      lo,
      hi,
      ks,
      Empty,
      +l2 => +left2 => +xs2 => ef => eh => en => elt => ee => ep => Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Bindings.has_level(a, l2),
          True{},
          Equal.cong(List<&2, Binding>, Bool, x => Bindings.has_level(x, l2), [], a, Shared.Maybe.some_inj(List<&2, Binding>, [], a, e0)),
          Mst.lists_level(~S, ~fetch, f, s, xs2, l2, left2, lo, hi, ks, a)(ee)(ep)(ea)
        )
      )
    )(eo)
  )(Mst.sub_list_on(~S, ~fetch, f, s, h, up, lo, hi, a)(hb)(e))

# two subtrees whose bounds hold keys, with nodes whose listings are one
# (ihn: two such nodes of one level are one), are one subtree
def Mst.canon_sub.both(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h1: Hashes.Hash,
  +h2: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +a: List<&2, Binding>,
  +hb: {Bound.before([], hi) == True{}: Bool},
  ihn: @xs1: List<&2, Item> -> @xs2: List<&2, Item> -> @l: Nat -> @p1: Maybe<&2, Hashes.Hash> -> @p2: Maybe<&2, Hashes.Hash> -> @ks1: List<
    &2,
    Piece> -> @ks2: List<&2, Piece> -> {Bound.before([], hi) == True{}: Bool} -> {
    Mst.pieces(xs1, l, p1, lo, hi) == Some{ks1}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, f, s, [], ks1) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
    Mst.pieces(xs2, l, p2, lo, hi) == Some{ks2}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, f, s, [], ks2) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Node{l, p1, xs1} == Node{l, p2, xs2}: Node}
) -> {Mst.sub_list(~S, ~fetch, f, s, [], Some{h1}, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
  Mst.sub_list(~S, ~fetch, f, s, [], Some{h2}, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Some{h1} == Some{h2}: Maybe<&2, Hashes.Hash>}:
  e1 => e2 => Maybe.bind_cases(
    List<&2, Piece>,
    List<&2, Binding>,
    Mst.open(~S, ~fetch, s, h1, up, lo, hi),
    ks => Mst.range.go(~S, ~fetch, f, s, [], ks),
    a,
    {Some{h1} == Some{h2}: Maybe<&2, Hashes.Hash>},
    +ks1 => eo1 => +ea1 => Mst.open_cases(
      ~S,
      ~fetch,
      s,
      h1,
      up,
      lo,
      hi,
      ks1,
      {Some{h1} == Some{h2}: Maybe<&2, Hashes.Hash>},
      +l1 => +left1 => +xs1 => ef1 => +eh1 => en1 => elt1 => +ee1 => +ep1 => Maybe.bind_cases(
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h2, up, lo, hi),
        ks => Mst.range.go(~S, ~fetch, f, s, [], ks),
        a,
        {Some{h1} == Some{h2}: Maybe<&2, Hashes.Hash>},
        +ks2 => eo2 => +ea2 => Mst.open_cases(
          ~S,
          ~fetch,
          s,
          h2,
          up,
          lo,
          hi,
          ks2,
          {Some{h1} == Some{h2}: Maybe<&2, Hashes.Hash>},
          +l2 => +left2 => +xs2 => ef2 => +eh2 => en2 => elt2 => +ee2 => +ep2 =>
            +l12 = Nat.lt_succ_eq(
              l1,
              l2
            )(
              Bindings.has_level_lt(
                a,
                l1,
                1n+l2
              )(Mst.lists_below(~S, ~fetch, f, s, [], xs2, l2, left2, lo, hi, ks2, a)(ep2)(ea2))(
                Mst.lists_level(~S, ~fetch, f, s, xs1, l1, left1, lo, hi, ks1, a)(ee1)(ep1)(ea1)
              )
            )(
              Bindings.has_level_lt(
                a,
                l2,
                1n+l1
              )(Mst.lists_below(~S, ~fetch, f, s, [], xs1, l1, left1, lo, hi, ks1, a)(ep1)(ea1))(
                Mst.lists_level(~S, ~fetch, f, s, xs2, l2, left2, lo, hi, ks2, a)(ee2)(ep2)(ea2)
              )
            )
            +nodes = ihn(xs1)(xs2)(l1)(left1)(left2)(ks1)(ks2)(hb)(ep1)(ea1)(
              Equal.trans(
                Maybe<&2, List<&2, Piece>>,
                Mst.pieces(xs2, l1, left2, lo, hi),
                Mst.pieces(xs2, l2, left2, lo, hi),
                Some{ks2},
                Equal.cong(Nat, Maybe<&2, List<&2, Piece>>, x => Mst.pieces(xs2, x, left2, lo, hi), l1, l2, l12),
                ep2
              )
            )(ea2)
            +n12 = Equal.trans(
              Node,
              Node{l1, left1, xs1},
              Node{l1, left2, xs2},
              Node{l2, left2, xs2},
              nodes,
              Equal.cong(Nat, Node, x => Node{x, left2, xs2}, l1, l2, l12)
            )
            Equal.cong(
              Hashes.Hash,
              Maybe<&2, Hashes.Hash>,
              x => Some{x},
              h1,
              h2,
              Equal.trans(
                Hashes.Hash,
                h1,
                Hashes.Sha.hash(Node.code(Node{l1, left1, xs1}, [])),
                h2,
                Equal.sym(Hashes.Hash, Hashes.Sha.hash(Node.code(Node{l1, left1, xs1}, [])), h1, eh1),
                Equal.trans(
                  Hashes.Hash,
                  Hashes.Sha.hash(Node.code(Node{l1, left1, xs1}, [])),
                  Hashes.Sha.hash(Node.code(Node{l2, left2, xs2}, [])),
                  h2,
                  Equal.cong(Node, Hashes.Hash, x => Hashes.Sha.hash(Node.code(x, [])), Node{l1, left1, xs1}, Node{l2, left2, xs2}, n12),
                  eh2
                )
              )
            )
        )(eo2)
      )(Mst.sub_list_on(~S, ~fetch, f, s, h2, up, lo, hi, a)(hb)(e2))
    )(eo1)
  )(Mst.sub_list_on(~S, ~fetch, f, s, h1, up, lo, hi, a)(hb)(e1))

# two subtrees in one room that list the same bindings, under no prefix, are
# one subtree, when two such nodes of one level are one (ihn)
def Mst.canon_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m1: Maybe<&2, Hashes.Hash>,
  m2: Maybe<&2, Hashes.Hash>,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +a: List<&2, Binding>,
  hn1: {Bool.or(Maybe.is_none(&2, Hashes.Hash, m1), Bound.before([], hi)) == True{}: Bool},
  hn2: {Bool.or(Maybe.is_none(&2, Hashes.Hash, m2), Bound.before([], hi)) == True{}: Bool},
  ihn: @xs1: List<&2, Item> -> @xs2: List<&2, Item> -> @l: Nat -> @p1: Maybe<&2, Hashes.Hash> -> @p2: Maybe<&2, Hashes.Hash> -> @ks1: List<
    &2,
    Piece> -> @ks2: List<&2, Piece> -> {Bound.before([], hi) == True{}: Bool} -> {
    Mst.pieces(xs1, l, p1, lo, hi) == Some{ks1}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, f, s, [], ks1) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
    Mst.pieces(xs2, l, p2, lo, hi) == Some{ks2}: Maybe<&2, List<&2, Piece>>
  } -> {Mst.range.go(~S, ~fetch, f, s, [], ks2) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Node{l, p1, xs1} == Node{l, p2, xs2}: Node}
) -> {Mst.sub_list(~S, ~fetch, f, s, [], m1, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
  Mst.sub_list(~S, ~fetch, f, s, [], m2, up, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {m1 == m2: Maybe<&2, Hashes.Hash>}:
  match m1 m2:
    case None{} None{}:
      e1 => e2 => {==}
    case None{} Some{+h2}:
      e1 => e2 => Empty.absurd({None{} == Some{h2}: Maybe<&2, Hashes.Hash>}, Mst.canon_sub.one(~S, ~fetch, f, s, h2, up, lo, hi, a, hn2)(e1)(e2))
    case Some{+h1} None{}:
      e1 => e2 => Empty.absurd({Some{h1} == None{}: Maybe<&2, Hashes.Hash>}, Mst.canon_sub.one(~S, ~fetch, f, s, h1, up, lo, hi, a, hn1)(e2)(e1))
    case Some{+h1} Some{+h2}:
      e1 => e2 => Mst.canon_sub.both(~S, ~fetch, f, s, h1, h2, up, lo, hi, a, hn1, ihn)(e1)(e2)

# a node with no item and a node with an item, of one level and room, list
# different bindings: the second holds a key of its level, the first none
def Mst.canon_clash(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +a: List<&2, Binding>,
  hh: {Bindings.has_level(a, l) == True{}: Bool}
) -> {Mst.pieces([], l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, 1n+q, s, [], ks) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> Empty:
  ep => e => Mst.range_list(
    ~S,
    ~fetch,
    prev,
    q,
    s,
    [],
    l,
    lo,
    hi,
    [],
    a,
    Empty,
    +a1 => b => e4 => eb => esl => Bindings.level_clash(
      a,
      l
    )(
      Equal.trans(
        Bool,
        Bindings.below(a, l),
        Bindings.below(a1, l),
        True{},
        Equal.cong(List<&2, Binding>, Bool, x => Bindings.below(x, l), a, a1, Equal.sym(List<&2, Binding>, a1, a, Bindings.cat_nil(a1, b, a)(eb)(e4))),
        Mst.sub_below(
          ~S,
          ~fetch,
          q,
          s,
          [],
          prev,
          l,
          lo,
          hi,
          a1,
          xs2 => l2 => left2 => ks2 => ep2 => ea2 => Mst.lists_below(~S, ~fetch, q, s, [], xs2, l2, left2, lo, hi, ks2, a1)(ep2)(ea2)
        )(esl)
      )
    )(hh)
  )(
    Equal.trans(
      Maybe<&2, List<&2, Binding>>,
      Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev, l, lo, hi, [])),
      Mst.range.go(~S, ~fetch, 1n+q, s, [], ks),
      Some{a},
      Equal.cong(
        List<&2, Piece>,
        Maybe<&2, List<&2, Binding>>,
        x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
        Piece.sub(prev, l, lo, hi, []),
        ks,
        Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep)
      ),
      e
    )
  )

# two nodes of one level, in one room, whose pieces list the same bindings
# under no prefix, are one node
def Mst.canon_node(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  xs1: List<&2, Item>,
  +xs2: List<&2, Item>,
  +l: Nat,
  +prev1: Maybe<&2, Hashes.Hash>,
  +prev2: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks1: List<&2, Piece>,
  +ks2: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {Bound.before([], hi) == True{}: Bool} -> {Mst.pieces(xs1, l, prev1, lo, hi) == Some{ks1}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, f, s, [], ks1) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Mst.pieces(xs2, l, prev2, lo, hi) == Some{ks2}: Maybe<&2, List<&2, Piece>>} -> {
  Mst.range.go(~S, ~fetch, f, s, [], ks2) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Node{l, prev1, xs1} == Node{l, prev2, xs2}: Node}:
  match f:
    case 0n:
      hb => ep1 => e1 => ep2 => e2 => Equal.trans(
        Node,
        Node{l, prev1, xs1},
        Node{l, None{}, []},
        Node{l, prev2, xs2},
        Mst.pieces_empty(
          xs1,
          l,
          prev1,
          lo,
          hi
        )(
          Equal.trans(
            Maybe<&2, List<&2, Piece>>,
            Mst.pieces(xs1, l, prev1, lo, hi),
            Some{ks1},
            Some{[]},
            ep1,
            Equal.cong(List<&2, Piece>, Maybe<&2, List<&2, Piece>>, x => Some{x}, ks1, [], Mst.range_zero_nil(~S, ~fetch, s, [], ks1, a)(e1))
          )
        ),
        Equal.sym(
          Node,
          Node{l, prev2, xs2},
          Node{l, None{}, []},
          Mst.pieces_empty(
            xs2,
            l,
            prev2,
            lo,
            hi
          )(
            Equal.trans(
              Maybe<&2, List<&2, Piece>>,
              Mst.pieces(xs2, l, prev2, lo, hi),
              Some{ks2},
              Some{[]},
              ep2,
              Equal.cong(List<&2, Piece>, Maybe<&2, List<&2, Piece>>, x => Some{x}, ks2, [], Mst.range_zero_nil(~S, ~fetch, s, [], ks2, a)(e2))
            )
          )
        )
      )
    case 1n+(+q):
      match xs1 xs2:
        case Nil{} Nil{}:
          +hb => ep1 => e1 => ep2 => e2 => Mst.range_list(
            ~S,
            ~fetch,
            prev1,
            q,
            s,
            [],
            l,
            lo,
            hi,
            [],
            a,
            {Node{l, prev1, []} == Node{l, prev2, []}: Node},
            +a1 => b1 => e41 => eb1 => esl1 => Mst.range_list(
              ~S,
              ~fetch,
              prev2,
              q,
              s,
              [],
              l,
              lo,
              hi,
              [],
              a,
              {Node{l, prev1, []} == Node{l, prev2, []}: Node},
              +a2 => b2 => e42 => eb2 => esl2 => Equal.cong(
                Maybe<&2, Hashes.Hash>,
                Node,
                x => Node{l, x, []},
                prev1,
                prev2,
                Mst.canon_sub(
                  ~S,
                  ~fetch,
                  q,
                  s,
                  prev1,
                  prev2,
                  l,
                  lo,
                  hi,
                  a,
                  Bool.or_true_of(Maybe.is_none(&2, Hashes.Hash, prev1), Bound.before([], hi))(hb),
                  Bool.or_true_of(Maybe.is_none(&2, Hashes.Hash, prev2), Bound.before([], hi))(hb),
                  ys1 => ys2 => l3 => p1 => p2 => j1 => j2 => hb3 => f1 => g1 => f2 => g2 => Mst.canon_node(
                    ~S,
                    ~fetch,
                    q,
                    s,
                    ys1,
                    ys2,
                    l3,
                    p1,
                    p2,
                    lo,
                    hi,
                    j1,
                    j2,
                    a
                  )(hb3)(f1)(g1)(f2)(g2)
                )(
                  Equal.trans(
                    Maybe<&2, List<&2, Binding>>,
                    Mst.sub_list(~S, ~fetch, q, s, [], prev1, l, lo, hi),
                    Some{a1},
                    Some{a},
                    esl1,
                    Equal.cong(List<&2, Binding>, Maybe<&2, List<&2, Binding>>, x => Some{x}, a1, a, Bindings.cat_nil(a1, b1, a)(eb1)(e41))
                  )
                )(
                  Equal.trans(
                    Maybe<&2, List<&2, Binding>>,
                    Mst.sub_list(~S, ~fetch, q, s, [], prev2, l, lo, hi),
                    Some{a2},
                    Some{a},
                    esl2,
                    Equal.cong(List<&2, Binding>, Maybe<&2, List<&2, Binding>>, x => Some{x}, a2, a, Bindings.cat_nil(a2, b2, a)(eb2)(e42))
                  )
                )
              )
            )(
              Equal.trans(
                Maybe<&2, List<&2, Binding>>,
                Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev2, l, lo, hi, [])),
                Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2),
                Some{a},
                Equal.cong(
                  List<&2, Piece>,
                  Maybe<&2, List<&2, Binding>>,
                  x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
                  Piece.sub(prev2, l, lo, hi, []),
                  ks2,
                  Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev2, l, lo, hi, []), ks2, ep2)
                ),
                e2
              )
            )
          )(
            Equal.trans(
              Maybe<&2, List<&2, Binding>>,
              Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev1, l, lo, hi, [])),
              Mst.range.go(~S, ~fetch, 1n+q, s, [], ks1),
              Some{a},
              Equal.cong(
                List<&2, Piece>,
                Maybe<&2, List<&2, Binding>>,
                x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
                Piece.sub(prev1, l, lo, hi, []),
                ks1,
                Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev1, l, lo, hi, []), ks1, ep1)
              ),
              e1
            )
          )
        case Nil{} Con{Item{+k2, +v2, +r2}, +rest2}:
          hb => ep1 => e1 => ep2 => e2 => Empty.absurd(
            {Node{l, prev1, []} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
            Mst.canon_clash(
              ~S,
              ~fetch,
              q,
              s,
              l,
              prev1,
              lo,
              hi,
              ks1,
              a,
              Mst.lists_level(~S, ~fetch, 1n+q, s, Item{k2, v2, r2} <> rest2, l, prev2, lo, hi, ks2, a)({==})(ep2)(e2)
            )(ep1)(e1)
          )
        case Con{Item{+k1, +v1, +r1}, +rest1} Nil{}:
          hb => ep1 => e1 => ep2 => e2 => Empty.absurd(
            {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, []}: Node},
            Mst.canon_clash(
              ~S,
              ~fetch,
              q,
              s,
              l,
              prev2,
              lo,
              hi,
              ks2,
              a,
              Mst.lists_level(~S, ~fetch, 1n+q, s, Item{k1, v1, r1} <> rest1, l, prev1, lo, hi, ks1, a)({==})(ep1)(e1)
            )(ep2)(e2)
          )
        case Con{Item{+k1, +v1, +r1}, +rest1} Con{Item{+k2, +v2, +r2}, +rest2}:
          +hb => ep1 => e1 => ep2 => e2 => Maybe.when_cases(
            List<&2, Piece>,
            Bool.and(
              Bool.and(Nat.is_eq(Key.level(k1), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1)))),
              Bool.and(Bound.after(lo, k1), Bound.before(k1, hi))
            ),
            u => Maybe.map(
              &2,
              List<&2, Piece>,
              List<&2, Piece>,
              ps2 => Piece.sub(prev1, l, lo, Some{k1}, Piece.Bind{k1, v1} <> ps2),
              Mst.pieces(rest1, l, r1, Some{k1}, hi)
            ),
            ks1,
            {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
            +c1 => e21 => Maybe.map_cases(
              List<&2, Piece>,
              List<&2, Piece>,
              Mst.pieces(rest1, l, r1, Some{k1}, hi),
              ps2 => Piece.sub(prev1, l, lo, Some{k1}, Piece.Bind{k1, v1} <> ps2),
              ks1,
              {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
              +ks1b => +e31 => e41 => Maybe.when_cases(
                List<&2, Piece>,
                Bool.and(
                  Bool.and(Nat.is_eq(Key.level(k2), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2)))),
                  Bool.and(Bound.after(lo, k2), Bound.before(k2, hi))
                ),
                u => Maybe.map(
                  &2,
                  List<&2, Piece>,
                  List<&2, Piece>,
                  ps2 => Piece.sub(prev2, l, lo, Some{k2}, Piece.Bind{k2, v2} <> ps2),
                  Mst.pieces(rest2, l, r2, Some{k2}, hi)
                ),
                ks2,
                {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                +c2 => e22 => Maybe.map_cases(
                  List<&2, Piece>,
                  List<&2, Piece>,
                  Mst.pieces(rest2, l, r2, Some{k2}, hi),
                  ps2 => Piece.sub(prev2, l, lo, Some{k2}, Piece.Bind{k2, v2} <> ps2),
                  ks2,
                  {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                  +ks2b => +e32 => e42 => Mst.range_list(
                    ~S,
                    ~fetch,
                    prev1,
                    q,
                    s,
                    [],
                    l,
                    lo,
                    Some{k1},
                    Piece.Bind{k1, v1} <> ks1b,
                    a,
                    {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                    +ca => +ba => e51 => eb1 => +esl1 => Maybe.map_cases(
                      List<&2, Binding>,
                      List<&2, Binding>,
                      Mst.range.go(~S, ~fetch, 1n+q, s, [], ks1b),
                      +bb => Shared.Bool.when(List<&2, Binding>, Key.leads([], k1), u => Binding{k1, v1} <> bb, u => bb),
                      ba,
                      {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                      +ba2 => +eb12 => e61 => Mst.range_list(
                        ~S,
                        ~fetch,
                        prev2,
                        q,
                        s,
                        [],
                        l,
                        lo,
                        Some{k2},
                        Piece.Bind{k2, v2} <> ks2b,
                        a,
                        {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                        +cb => +bx => e52 => eb2 => +esl2 => Maybe.map_cases(
                          List<&2, Binding>,
                          List<&2, Binding>,
                          Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2b),
                          +bb => Shared.Bool.when(List<&2, Binding>, Key.leads([], k2), u => Binding{k2, v2} <> bb, u => bb),
                          bx,
                          {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                          +bb2 => +eb22 => e62 => Bindings.split_eq(
                            ca,
                            cb,
                            Binding{k1, v1},
                            Binding{k2, v2},
                            ba2,
                            bb2,
                            l,
                            {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev2, Item{k2, v2, r2} <> rest2}: Node},
                            +ec => +ex => +er =>
                              +kk = Equal.cong(Binding, List<&2, U32>, Binding.key, Binding{k1, v1}, Binding{k2, v2}, ex)
                              +vv = Equal.cong(Binding, List<&2, U32>, Binding.value, Binding{k1, v1}, Binding{k2, v2}, ex)
                              +pp = Mst.canon_sub(
                                ~S,
                                ~fetch,
                                q,
                                s,
                                prev1,
                                prev2,
                                l,
                                lo,
                                Some{k1},
                                ca,
                                Equal.trans(
                                  Bool,
                                  Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Key.is_lt([], k1)),
                                  Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1))),
                                  True{},
                                  Equal.cong(
                                    Bool,
                                    Bool,
                                    x => Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), x),
                                    Key.is_lt([], k1),
                                    Bool.not(List.is_empty(&2, U32, k1)),
                                    Key.lt_nil_left(k1)
                                  ),
                                  Shared.Bool.and_true_right(
                                    Nat.is_eq(Key.level(k1), l),
                                    Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1)))
                                  )(
                                    Shared.Bool.and_true_left(
                                      Bool.and(
                                        Nat.is_eq(Key.level(k1), l),
                                        Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1)))
                                      ),
                                      Bool.and(Bound.after(lo, k1), Bound.before(k1, hi))
                                    )(c1)
                                  )
                                ),
                                Equal.trans(
                                  Bool,
                                  Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Key.is_lt([], k1)),
                                  Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Key.is_lt([], k2)),
                                  True{},
                                  Equal.cong(List<&2, U32>, Bool, x => Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Key.is_lt([], x)), k1, k2, kk),
                                  Equal.trans(
                                    Bool,
                                    Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Key.is_lt([], k2)),
                                    Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2))),
                                    True{},
                                    Equal.cong(
                                      Bool,
                                      Bool,
                                      x => Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), x),
                                      Key.is_lt([], k2),
                                      Bool.not(List.is_empty(&2, U32, k2)),
                                      Key.lt_nil_left(k2)
                                    ),
                                    Shared.Bool.and_true_right(
                                      Nat.is_eq(Key.level(k2), l),
                                      Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2)))
                                    )(
                                      Shared.Bool.and_true_left(
                                        Bool.and(
                                          Nat.is_eq(Key.level(k2), l),
                                          Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2)))
                                        ),
                                        Bool.and(Bound.after(lo, k2), Bound.before(k2, hi))
                                      )(c2)
                                    )
                                  )
                                ),
                                ys1 => ys2 => l3 => p1 => p2 => j1 => j2 => hb3 => f1 => g1 => f2 => g2 => Mst.canon_node(
                                  ~S,
                                  ~fetch,
                                  q,
                                  s,
                                  ys1,
                                  ys2,
                                  l3,
                                  p1,
                                  p2,
                                  lo,
                                  Some{k1},
                                  j1,
                                  j2,
                                  ca
                                )(hb3)(f1)(g1)(f2)(g2)
                              )(esl1)(
                                Equal.trans(
                                  Maybe<&2, List<&2, Binding>>,
                                  Mst.sub_list(~S, ~fetch, q, s, [], prev2, l, lo, Some{k1}),
                                  Mst.sub_list(~S, ~fetch, q, s, [], prev2, l, lo, Some{k2}),
                                  Some{ca},
                                  Equal.cong(
                                    List<&2, U32>,
                                    Maybe<&2, List<&2, Binding>>,
                                    x => Mst.sub_list(~S, ~fetch, q, s, [], prev2, l, lo, Some{x}),
                                    k1,
                                    k2,
                                    kk
                                  ),
                                  Equal.trans(
                                    Maybe<&2, List<&2, Binding>>,
                                    Mst.sub_list(~S, ~fetch, q, s, [], prev2, l, lo, Some{k2}),
                                    Some{cb},
                                    Some{ca},
                                    esl2,
                                    Equal.cong(
                                      List<&2, Binding>,
                                      Maybe<&2, List<&2, Binding>>,
                                      x => Some{x},
                                      cb,
                                      ca,
                                      Equal.sym(List<&2, Binding>, ca, cb, ec)
                                    )
                                  )
                                )
                              )
                              +nr = Mst.canon_node(
                                ~S,
                                ~fetch,
                                1n+q,
                                s,
                                rest1,
                                rest2,
                                l,
                                r1,
                                r2,
                                Some{k1},
                                hi,
                                ks1b,
                                ks2b,
                                ba2
                              )(hb)(e31)(eb12)(
                                Equal.trans(
                                  Maybe<&2, List<&2, Piece>>,
                                  Mst.pieces(rest2, l, r2, Some{k1}, hi),
                                  Mst.pieces(rest2, l, r2, Some{k2}, hi),
                                  Some{ks2b},
                                  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, Piece>>, x => Mst.pieces(rest2, l, r2, Some{x}, hi), k1, k2, kk),
                                  e32
                                )
                              )(
                                Equal.trans(
                                  Maybe<&2, List<&2, Binding>>,
                                  Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2b),
                                  Some{bb2},
                                  Some{ba2},
                                  eb22,
                                  Equal.cong(
                                    List<&2, Binding>,
                                    Maybe<&2, List<&2, Binding>>,
                                    x => Some{x},
                                    bb2,
                                    ba2,
                                    Equal.sym(List<&2, Binding>, ba2, bb2, er)
                                  )
                                )
                              )
                              %pp: {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, _, Item{k2, v2, r2} <> rest2}: Node}
                              %kk: {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev1, Item{_, v2, r2} <> rest2}: Node}
                              %vv: {Node{l, prev1, Item{k1, v1, r1} <> rest1} == Node{l, prev1, Item{k1, _, r2} <> rest2}: Node}
                              Equal.cong(Node, Node, n => Node.under(n, l, prev1, k1, v1), Node{l, r1, rest1}, Node{l, r2, rest2}, nr)
                          )(
                            Equal.trans(
                              List<&2, Binding>,
                              List.append(&2, Binding, ca, Binding{k1, v1} <> ba2),
                              a,
                              List.append(&2, Binding, cb, Binding{k2, v2} <> bb2),
                              Equal.trans(
                                List<&2, Binding>,
                                List.append(&2, Binding, ca, Binding{k1, v1} <> ba2),
                                List.append(&2, Binding, ca, ba),
                                a,
                                Equal.cong(List<&2, Binding>, List<&2, Binding>, x => List.append(&2, Binding, ca, x), Binding{k1, v1} <> ba2, ba, e61),
                                e51
                              ),
                              Equal.sym(
                                List<&2, Binding>,
                                List.append(&2, Binding, cb, Binding{k2, v2} <> bb2),
                                a,
                                Equal.trans(
                                  List<&2, Binding>,
                                  List.append(&2, Binding, cb, Binding{k2, v2} <> bb2),
                                  List.append(&2, Binding, cb, bx),
                                  a,
                                  Equal.cong(List<&2, Binding>, List<&2, Binding>, x => List.append(&2, Binding, cb, x), Binding{k2, v2} <> bb2, bx, e62),
                                  e52
                                )
                              )
                            )
                          )(
                            Mst.sub_below(
                              ~S,
                              ~fetch,
                              q,
                              s,
                              [],
                              prev1,
                              l,
                              lo,
                              Some{k1},
                              ca,
                              xs3 => l3 => left3 => ks3 => ep3 => ea3 => Mst.lists_below(~S, ~fetch, q, s, [], xs3, l3, left3, lo, Some{k1}, ks3, ca)(ep3)(ea3)
                            )(esl1)
                          )(
                            Mst.sub_below(
                              ~S,
                              ~fetch,
                              q,
                              s,
                              [],
                              prev2,
                              l,
                              lo,
                              Some{k2},
                              cb,
                              xs3 => l3 => left3 => ks3 => ep3 => ea3 => Mst.lists_below(~S, ~fetch, q, s, [], xs3, l3, left3, lo, Some{k2}, ks3, cb)(ep3)(ea3)
                            )(esl2)
                          )(
                            Shared.Bool.and_true_left(
                              Nat.is_eq(Key.level(k1), l),
                              Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1)))
                            )(
                              Shared.Bool.and_true_left(
                                Bool.and(Nat.is_eq(Key.level(k1), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev1), Bool.not(List.is_empty(&2, U32, k1)))),
                                Bool.and(Bound.after(lo, k1), Bound.before(k1, hi))
                              )(c1)
                            )
                          )(
                            Shared.Bool.and_true_left(
                              Nat.is_eq(Key.level(k2), l),
                              Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2)))
                            )(
                              Shared.Bool.and_true_left(
                                Bool.and(Nat.is_eq(Key.level(k2), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev2), Bool.not(List.is_empty(&2, U32, k2)))),
                                Bool.and(Bound.after(lo, k2), Bound.before(k2, hi))
                              )(c2)
                            )
                          )
                        )(eb2)
                      )(
                        Equal.trans(
                          Maybe<&2, List<&2, Binding>>,
                          Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev2, l, lo, Some{k2}, Piece.Bind{k2, v2} <> ks2b)),
                          Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2),
                          Some{a},
                          Equal.cong(
                            List<&2, Piece>,
                            Maybe<&2, List<&2, Binding>>,
                            x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
                            Piece.sub(prev2, l, lo, Some{k2}, Piece.Bind{k2, v2} <> ks2b),
                            ks2,
                            e42
                          ),
                          e2
                        )
                      )
                    )(eb1)
                  )(
                    Equal.trans(
                      Maybe<&2, List<&2, Binding>>,
                      Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev1, l, lo, Some{k1}, Piece.Bind{k1, v1} <> ks1b)),
                      Mst.range.go(~S, ~fetch, 1n+q, s, [], ks1),
                      Some{a},
                      Equal.cong(
                        List<&2, Piece>,
                        Maybe<&2, List<&2, Binding>>,
                        x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
                        Piece.sub(prev1, l, lo, Some{k1}, Piece.Bind{k1, v1} <> ks1b),
                        ks1,
                        e41
                      ),
                      e1
                    )
                  )
                )(e22)
              )(ep2)
            )(e21)
          )(ep1)

# Whole trees
# -----------

# no key under no prefix is before the bound lo: every key may come after it
def Bound.meets_lo_nil(lo: Maybe<&2, List<&2, U32>>) -> {Bound.meets_lo([], lo) == True{}: Bool}:
  match lo:
    case None{}:
      {==}
    case Some{+a}:
      %Equal.sym(Bool, Key.is_lt(a, []), False{}, Key.lt_nil(a)): {Bool.or(_, Key.leads([], a)) == True{}: Bool}
      {==}

# a subtree that a listing under no prefix skips, a listing under any prefix
# skips
def Bound.meets_any(+p: List<&2, U32>, +lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> {
  Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)) == False{}: Bool
} -> {Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)) == False{}: Bool}:
  match hi:
    case None{}:
      e => Empty.absurd(
        {Bool.and(Bound.meets_lo(p, lo), True{}) == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Bool.and(Bound.meets_lo([], lo), True{}),
            False{},
            Equal.trans(Bool, True{}, Bound.meets_lo([], lo), Bool.and(Bound.meets_lo([], lo), True{}), Equal.sym(Bool, Bound.meets_lo([], lo), True{}, Bound.meets_lo_nil(lo)), Shared.Bool.and_true(Bound.meets_lo([], lo))),
            e
          )
        )
      )
    case Some{b}:
      match b:
        case Nil{}:
          e =>
            %Equal.sym(Bool, Key.is_lt(p, []), False{}, Key.lt_nil(p)): {Bool.and(Bound.meets_lo(p, lo), _) == False{}: Bool}
            Shared.Bool.and_false_right(Bound.meets_lo(p, lo))
        case Con{x, r}:
          e => Empty.absurd(
            {Bool.and(Bound.meets_lo(p, lo), Key.is_lt(p, x <> r)) == False{}: Bool},
            Shared.Bool.true_ne_false(
              Equal.trans(
                Bool,
                True{},
                Bool.and(Bound.meets_lo([], lo), True{}),
                False{},
                Equal.trans(Bool, True{}, Bound.meets_lo([], lo), Bool.and(Bound.meets_lo([], lo), True{}), Equal.sym(Bool, Bound.meets_lo([], lo), True{}, Bound.meets_lo_nil(lo)), Shared.Bool.and_true(Bound.meets_lo([], lo))),
                e
              )
            )
          )

# a map has a value exactly when what it maps has one
def Maybe.map_is_some(-A: Data, -B: Data, -f: A -> B, m: Maybe<&2, A>) -> {
  Maybe.is_some(&2, B, Maybe.map(&2, A, B, f, m)) == Maybe.is_some(&2, A, m): Bool
}:
  match m:
    case None{}:
      {==}
    case Some{a}:
      {==}

# a Maybe that has a value holds one
def Maybe.some_cases(-A: Data, m: Maybe<&2, A>, -P: Type, k: @a: A -> {m == Some{a}: Maybe<&2, A>} -> P) -> {
  Maybe.is_some(&2, A, m) == True{}: Bool
} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Bool.false_ne_true(e))
    case Some{+a}:
      e => k(a)({==})

# Mst.range_some at a subtree that the listing under no prefix reads (t)
def Mst.range_some.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  t: Bool,
  +q: Nat,
  +s: S,
  +p: List<&2, U32>,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +a: List<&2, Binding>,
  et: {Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)) == t: Bool},
  ihr: @b: List<&2, Binding> -> {Mst.range.go(~S, ~fetch, 1n+q, s, [], rest) == Some{b}: Maybe<&2, List<&2, Binding>>} -> {
    Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)) == True{}: Bool
  },
  ihs: @ks: List<&2, Piece> -> @b: List<&2, Binding> -> {Mst.range.go(~S, ~fetch, q, s, [], ks) == Some{b}: Maybe<&2, List<&2, Binding>>} -> {
    Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, q, s, p, ks)) == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Binding>>,
    t,
    u => Maybe.bind(
      &2,
      List<&2, Piece>,
      List<&2, Binding>,
      Mst.open(~S, ~fetch, s, h, up, lo, hi),
      ks => Maybe.bind(
        &2,
        List<&2, Binding>,
        List<&2, Binding>,
        Mst.range.go(~S, ~fetch, q, s, [], ks),
        a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest))
      )
    ),
    u => Mst.range.go(~S, ~fetch, 1n+q, s, [], rest)
  )
    == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.Sub{h, up, lo, hi} <> rest)) == True{}: Bool}:
  match t:
    case True{}:
      e => Maybe.bind_cases(
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, up, lo, hi),
        ks => Maybe.bind(
          &2,
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, [], ks),
          a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest))
        ),
        a,
        {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.Sub{h, up, lo, hi} <> rest)) == True{}: Bool},
        +ks => +eo => e2 => Maybe.bind_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, [], ks),
          a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest)),
          a,
          {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.Sub{h, up, lo, hi} <> rest)) == True{}: Bool},
          +a2 => ea => e3 => Maybe.map_cases(
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, 1n+q, s, [], rest),
            b => List.append(&2, Binding, a2, b),
            a,
            {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.Sub{h, up, lo, hi} <> rest)) == True{}: Bool},
            +b => +eb => e4 =>
              +ir = ihr(b)(eb)
              Shared.Bool.when_cases(
              Maybe<&2, List<&2, Binding>>,
              x => {Maybe.is_some(&2, List<&2, Binding>, x) == True{}: Bool},
              Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
              u => Maybe.bind(
                &2,
                List<&2, Piece>,
                List<&2, Binding>,
                Mst.open(~S, ~fetch, s, h, up, lo, hi),
                ks2 => Maybe.bind(
                  &2,
                  List<&2, Binding>,
                  List<&2, Binding>,
                  Mst.range.go(~S, ~fetch, q, s, p, ks2),
                  a3 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, a3, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                )
              ),
              u => Mst.range.go(~S, ~fetch, 1n+q, s, p, rest),
              et2 =>
                %Equal.sym(Maybe<&2, List<&2, Piece>>, Mst.open(~S, ~fetch, s, h, up, lo, hi), Some{ks}, eo): {
                  Maybe.is_some(
                    &2,
                    List<&2, Binding>,
                    Maybe.bind(
                      &2,
                      List<&2, Piece>,
                      List<&2, Binding>,
                      _,
                      ks2 => Maybe.bind(
                        &2,
                        List<&2, Binding>,
                        List<&2, Binding>,
                        Mst.range.go(~S, ~fetch, q, s, p, ks2),
                        a3 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, a3, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                      )
                    )
                  )
                    == True{}: Bool
                }
                Maybe.some_cases(
                  List<&2, Binding>,
                  Mst.range.go(~S, ~fetch, q, s, p, ks),
                  {
                    Maybe.is_some(
                      &2,
                      List<&2, Binding>,
                      Maybe.bind(
                        &2,
                        List<&2, Binding>,
                        List<&2, Binding>,
                        Mst.range.go(~S, ~fetch, q, s, p, ks),
                        a3 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, a3, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                      )
                    )
                      == True{}: Bool
                  },
                  +x => ex =>
                    %Equal.sym(Maybe<&2, List<&2, Binding>>, Mst.range.go(~S, ~fetch, q, s, p, ks), Some{x}, ex): {
                      Maybe.is_some(
                        &2,
                        List<&2, Binding>,
                        Maybe.bind(
                          &2,
                          List<&2, Binding>,
                          List<&2, Binding>,
                          _,
                          a3 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, a3, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                        )
                      )
                        == True{}: Bool
                    }
                    %Equal.sym(
                      Bool,
                      Maybe.is_some(
                        &2,
                        List<&2, Binding>,
                        Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, x, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                      ),
                      Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)),
                      Maybe.map_is_some(List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, x, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                    ): {_ == True{}: Bool}
                    ir
                )(ihs(ks)(a2)(ea)),
              ef2 => ir
            )
          )(e3)
        )(e2)
      )(e)
    case False{}:
      e =>
        %Equal.sym(
          Bool,
          Bool.and(Bound.meets_lo(p, lo), Bound.meets_hi(p, hi)),
          False{},
          Bound.meets_any(p, lo, hi)(et)
        ): {
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Shared.Bool.when(
              Maybe<&2, List<&2, Binding>>,
              _,
              u => Maybe.bind(
                &2,
                List<&2, Piece>,
                List<&2, Binding>,
                Mst.open(~S, ~fetch, s, h, up, lo, hi),
                ks2 => Maybe.bind(
                  &2,
                  List<&2, Binding>,
                  List<&2, Binding>,
                  Mst.range.go(~S, ~fetch, q, s, p, ks2),
                  a3 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b2 => List.append(&2, Binding, a3, b2), Mst.range.go(~S, ~fetch, 1n+q, s, p, rest))
                )
              ),
              u => Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
            )
          )
            == True{}: Bool
        }
        ihr(a)(e)

# a listing under no prefix that reads lets a listing under any prefix read
def Mst.range_some(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  +p: List<&2, U32>,
  ps: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {Mst.range.go(~S, ~fetch, f, s, [], ps) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {
  Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, f, s, p, ps)) == True{}: Bool
}:
  match f ps:
    case x Nil{}:
      e => {==}
    case 0n Con{x, rest}:
      e => Empty.absurd(
        {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 0n, s, p, x <> rest)) == True{}: Bool},
        Shared.Maybe.none_ne_some(List<&2, Binding>, a, e)
      )
    case 1n+(+q) Con{Piece.Bind{+k, +v}, +rest}:
      e => Maybe.map_cases(
        List<&2, Binding>,
        List<&2, Binding>,
        Mst.range.go(~S, ~fetch, 1n+q, s, [], rest),
        +bs => Shared.Bool.when(List<&2, Binding>, Key.leads([], k), u => Binding{k, v} <> bs, u => bs),
        a,
        {Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, Piece.Bind{k, v} <> rest)) == True{}: Bool},
        +b => eb => e2 =>
          %Equal.sym(
            Bool,
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.map(
                &2,
                List<&2, Binding>,
                List<&2, Binding>,
                +bs => Shared.Bool.when(List<&2, Binding>, Key.leads(p, k), u => Binding{k, v} <> bs, u => bs),
                Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
              )
            ),
            Maybe.is_some(&2, List<&2, Binding>, Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)),
            Maybe.map_is_some(
              List<&2, Binding>,
              List<&2, Binding>,
              +bs => Shared.Bool.when(List<&2, Binding>, Key.leads(p, k), u => Binding{k, v} <> bs, u => bs),
              Mst.range.go(~S, ~fetch, 1n+q, s, p, rest)
            )
          ): {_ == True{}: Bool}
          Mst.range_some(~S, ~fetch, 1n+q, s, p, rest, b)(eb)
      )(e)
    case 1n+(+q) Con{Piece.Sub{+h, +up, +lo, +hi}, +rest}:
      e => Mst.range_some.at(
        ~S,
        ~fetch,
        Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)),
        q,
        s,
        p,
        h,
        up,
        lo,
        hi,
        rest,
        a,
        {==},
        b => eb => Mst.range_some(~S, ~fetch, 1n+q, s, p, rest, b)(eb),
        ks => b => eb => Mst.range_some(~S, ~fetch, q, s, p, ks, b)(eb)
      )(e)

# the subtrees of the pieces ps whose bounds hold k read k finally, f levels
# down
def Pieces.final(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +k: List<&2, U32>
) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Piece.Bind{k2, v2}, rest}:
      Pieces.final(~S, ~fetch, f, s, rest, k)
    case Con{Piece.Sub{h, up, +lo, +hi}, rest}:
      Bool.and(
        Bool.or(
          Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))),
          Look.is_final(Mst.look.go(~S, ~fetch, f, s, Room{up, lo, hi}, Some{h}, k))
        ),
        Pieces.final(~S, ~fetch, f, s, rest, k)
      )

# a not-or whose test holds is its second side
def Bool.or_not_true(i: Bool, -x: Bool) -> {Bool.or(Bool.not(i), x) == True{}: Bool} -> {i == True{}: Bool} -> {x == True{}: Bool}:
  match i:
    case True{}:
      h => e => h
    case False{}:
      h => e => Empty.absurd({x == True{}: Bool}, Shared.Bool.false_ne_true(e))

# a not-or holds when its second side follows from its test
def Bool.or_not_of(i: Bool, -x: Bool) -> ({i == True{}: Bool} -> {x == True{}: Bool}) -> {Bool.or(Bool.not(i), x) == True{}: Bool}:
  match i:
    case True{}:
      g => g({==})
    case False{}:
      g => {==}

# a subtree whose bounds hold k, of pieces that read k finally, reads it
# finally
def Mst.final_at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Pieces.final(~S, ~fetch, f, s, Piece.sub(m, l, lo, hi, rest), k) == True{}: Bool} -> {
  Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool
} -> {Look.is_final(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, m, k)) == True{}: Bool}:
  match m:
    case None{}:
      h => i =>
        %Equal.sym(Look, Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, None{}, k), Look.Absent{}, Mst.look_none(~S, ~fetch, f, s, Room{l, lo, hi}, k)): {
          Look.is_final(_) == True{}: Bool
        }
        {==}
    case Some{+h2}:
      h => i => Bool.or_not_true(
        Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
        Look.is_final(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, Some{h2}, k))
      )(
        Shared.Bool.and_true_left(
          Bool.or(
            Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))),
            Look.is_final(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, Some{h2}, k))
          ),
          Pieces.final(~S, ~fetch, f, s, rest, k)
        )(h)
      )(i)

# the pieces after a subtree read k finally when all do
def Mst.final_rest(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Pieces.final(~S, ~fetch, f, s, Piece.sub(m, l, lo, hi, rest), k) == True{}: Bool} -> {
  Pieces.final(~S, ~fetch, f, s, rest, k) == True{}: Bool
}:
  match m:
    case None{}:
      h => h
    case Some{+h2}:
      h => Shared.Bool.and_true_right(
        Bool.or(
          Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))),
          Look.is_final(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, Some{h2}, k))
        ),
        Pieces.final(~S, ~fetch, f, s, rest, k)
      )(h)

# Mst.final_pick at an item of the key ik, whose comparison with k is c
def Mst.final_pick.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks2: List<&2, Piece>,
  +k: List<&2, U32>,
  +ec: {Key.cmp(k, ik) == c: Cmp},
  hf: {Pieces.final(~S, ~fetch, f, s, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), k) == True{}: Bool},
  +hin: {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool},
  ew: {Nat.is_eq(Key.level(ik), l) == True{}: Bool},
  ih: {Pieces.final(~S, ~fetch, f, s, ks2, k) == True{}: Bool} -> {Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)) == True{}: Bool} -> {
    Look.is_final(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))) == True{}: Bool
  }
) -> {
  Look.is_final(
    Mst.look.pick(
      Shared.Bool.when(
        Pick,
        Cmp.is_lt(c),
        u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
        u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k))
      ),
      h,
      l,
      k,
      m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)
    )
  )
    == True{}: Bool
}:
  match c:
    case LT{}:
      Mst.final_at(
        ~S,
        ~fetch,
        f,
        s,
        prev,
        l,
        lo,
        Some{ik},
        Piece.Bind{ik, iv} <> ks2,
        k
      )(hf)(
        Shared.Bool.and_both(Bound.after(lo, k), Key.is_lt(k, ik))(Shared.Bool.and_true_left(Bound.after(lo, k), Bound.before(k, hi))(hin))(
          Key.lt_of(k, ik, LT{})(ec)
        )
      )
    case EQ{}:
      %Equal.sym(
        Bool,
        Nat.is_eq(Key.level(k), l),
        True{},
        Equal.trans(
          Bool,
          Nat.is_eq(Key.level(k), l),
          Nat.is_eq(Key.level(ik), l),
          True{},
          Equal.cong(List<&2, U32>, Bool, x => Nat.is_eq(Key.level(x), l), k, ik, Key.cmp_eq(k, ik)(ec)),
          ew
        )
      ): {Look.is_final(Shared.Bool.when(Look, _, u => Look.Found{iv}, u => Look.Missing{h})) == True{}: Bool}
      {==}
    case GT{}:
      ih(Mst.final_rest(~S, ~fetch, f, s, prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2, k)(hf))(
        Shared.Bool.and_both(Key.is_lt(ik, k), Bound.before(k, hi))(Key.gt_of(k, ik, GT{})(ec))(
          Shared.Bool.and_true_right(Bound.after(lo, k), Bound.before(k, hi))(hin)
        )
      )

# a read of k in a node, between the bounds of its items, is final when its
# pieces read k finally
def Mst.final_pick(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {Pieces.final(~S, ~fetch, f, s, ks, k) == True{}: Bool} -> {
  Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool
} -> {
  Look.is_final(Mst.look.pick(Mst.pick(xs, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))) == True{}: Bool
}:
  match xs:
    case Nil{}:
      ep => hf => hin => Mst.final_at(
        ~S,
        ~fetch,
        f,
        s,
        prev,
        l,
        lo,
        hi,
        [],
        k
      )(
        Equal.trans(
          Bool,
          Pieces.final(~S, ~fetch, f, s, Piece.sub(prev, l, lo, hi, []), k),
          Pieces.final(~S, ~fetch, f, s, ks, k),
          True{},
          Equal.cong(
            List<&2, Piece>,
            Bool,
            x => Pieces.final(~S, ~fetch, f, s, x, k),
            Piece.sub(prev, l, lo, hi, []),
            ks,
            Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep)
          ),
          hf
        )
      )(hin)
    case Con{Item{+ik, +iv, +r}, +rest}:
      ep => hf => hin => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {
          Look.is_final(
            Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))
          )
            == True{}: Bool
        },
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {
            Look.is_final(
              Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))
            )
              == True{}: Bool
          },
          +ks2 => e3 => e4 => Mst.final_pick.con(
            ~S,
            ~fetch,
            Key.cmp(k, ik),
            f,
            s,
            h,
            ik,
            iv,
            r,
            rest,
            l,
            prev,
            lo,
            hi,
            ks2,
            k,
            {==},
            Equal.trans(
              Bool,
              Pieces.final(~S, ~fetch, f, s, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), k),
              Pieces.final(~S, ~fetch, f, s, ks, k),
              True{},
              Equal.cong(List<&2, Piece>, Bool, x => Pieces.final(~S, ~fetch, f, s, x, k), Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), ks, e4),
              hf
            ),
            hin,
            Shared.Bool.and_true_left(
              Nat.is_eq(Key.level(ik), l),
              Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
            )(
              Shared.Bool.and_true_left(
                Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
              )(c)
            ),
            hf3 => hin3 => Mst.final_pick(~S, ~fetch, f, s, h, rest, l, r, Some{ik}, hi, ks2, k)(e3)(hf3)(hin3)
          )
        )(e2)
      )(ep)

# a read of k in an opened node, between its bounds, is final when its pieces
# read k finally
def Mst.final_open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.open(~S, ~fetch, s, h, up, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {Pieces.final(~S, ~fetch, q, s, ks, k) == True{}: Bool} -> {
  Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool
} -> {Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k)) == True{}: Bool}:
  eo => hf => hin => Mst.open_cases(
    ~S,
    ~fetch,
    s,
    h,
    up,
    lo,
    hi,
    ks,
    {Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k)) == True{}: Bool},
    +l => +left => +xs => ef => eh => en => elt => ee => ep =>
      %Equal.sym(Maybe<&2, Node>, Mst.node.in(~S, ~fetch, s, h, Room{up, lo, hi}), Some{Node{l, left, xs}}, en): {
        Look.is_final(Mst.look.at(h, _, Room{up, lo, hi}, k, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k))) == True{}: Bool
      }
      Mst.final_pick(~S, ~fetch, q, s, h, xs, l, left, lo, hi, ks, k)(ep)(hf)(hin)
  )(eo)

# a subtree that a listing under no prefix skips holds no key
def Bound.not_in(+lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>, -x: Bool) -> {
  Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)) == False{}: Bool
} -> {Bool.or(Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))), x) == True{}: Bool}:
  match hi:
    case None{}:
      e => Empty.absurd(
        {Bool.or(Bool.not(Bool.and(Bound.after(lo, k), True{})), x) == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Bool.and(Bound.meets_lo([], lo), True{}),
            False{},
            Equal.trans(Bool, True{}, Bound.meets_lo([], lo), Bool.and(Bound.meets_lo([], lo), True{}), Equal.sym(Bool, Bound.meets_lo([], lo), True{}, Bound.meets_lo_nil(lo)), Shared.Bool.and_true(Bound.meets_lo([], lo))),
            e
          )
        )
      )
    case Some{b}:
      match b:
        case Nil{}:
          e =>
            %Equal.sym(Bool, Key.is_lt(k, []), False{}, Key.lt_nil(k)): {Bool.or(Bool.not(Bool.and(Bound.after(lo, k), _)), x) == True{}: Bool}
            %Equal.sym(Bool, Bool.and(Bound.after(lo, k), False{}), False{}, Shared.Bool.and_false_right(Bound.after(lo, k))): {
              Bool.or(Bool.not(_), x) == True{}: Bool
            }
            {==}
        case Con{y, r}:
          e => Empty.absurd(
            {Bool.or(Bool.not(Bool.and(Bound.after(lo, k), Key.is_lt(k, y <> r))), x) == True{}: Bool},
            Shared.Bool.true_ne_false(
              Equal.trans(
                Bool,
                True{},
                Bool.and(Bound.meets_lo([], lo), True{}),
                False{},
                Equal.trans(Bool, True{}, Bound.meets_lo([], lo), Bool.and(Bound.meets_lo([], lo), True{}), Equal.sym(Bool, Bound.meets_lo([], lo), True{}, Bound.meets_lo_nil(lo)), Shared.Bool.and_true(Bound.meets_lo([], lo))),
                e
              )
            )
          )

# Mst.final_list at a subtree, by whether the listing reads it (t)
def Mst.final_list.at(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  t: Bool,
  +q: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +a: List<&2, Binding>,
  +k: List<&2, U32>,
  et: {Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)) == t: Bool},
  ihr: @b: List<&2, Binding> -> {Mst.range.go(~S, ~fetch, 1n+q, s, [], rest) == Some{b}: Maybe<&2, List<&2, Binding>>} -> {
    Pieces.final(~S, ~fetch, 1n+q, s, rest, k) == True{}: Bool
  },
  ihs: @ks: List<&2, Piece> -> @b: List<&2, Binding> -> {Mst.range.go(~S, ~fetch, q, s, [], ks) == Some{b}: Maybe<&2, List<&2, Binding>>} -> {
    Pieces.final(~S, ~fetch, q, s, ks, k) == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, List<&2, Binding>>,
    t,
    u => Maybe.bind(
      &2,
      List<&2, Piece>,
      List<&2, Binding>,
      Mst.open(~S, ~fetch, s, h, up, lo, hi),
      ks => Maybe.bind(
        &2,
        List<&2, Binding>,
        List<&2, Binding>,
        Mst.range.go(~S, ~fetch, q, s, [], ks),
        a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest))
      )
    ),
    u => Mst.range.go(~S, ~fetch, 1n+q, s, [], rest)
  )
    == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Pieces.final(~S, ~fetch, 1n+q, s, Piece.Sub{h, up, lo, hi} <> rest, k) == True{}: Bool}:
  match t:
    case True{}:
      e => Maybe.bind_cases(
        List<&2, Piece>,
        List<&2, Binding>,
        Mst.open(~S, ~fetch, s, h, up, lo, hi),
        ks => Maybe.bind(
          &2,
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, [], ks),
          a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest))
        ),
        a,
        {Pieces.final(~S, ~fetch, 1n+q, s, Piece.Sub{h, up, lo, hi} <> rest, k) == True{}: Bool},
        +ks => eo => e2 => Maybe.bind_cases(
          List<&2, Binding>,
          List<&2, Binding>,
          Mst.range.go(~S, ~fetch, q, s, [], ks),
          a2 => Maybe.map(&2, List<&2, Binding>, List<&2, Binding>, b => List.append(&2, Binding, a2, b), Mst.range.go(~S, ~fetch, 1n+q, s, [], rest)),
          a,
          {Pieces.final(~S, ~fetch, 1n+q, s, Piece.Sub{h, up, lo, hi} <> rest, k) == True{}: Bool},
          +a2 => ea => e3 => Maybe.map_cases(
            List<&2, Binding>,
            List<&2, Binding>,
            Mst.range.go(~S, ~fetch, 1n+q, s, [], rest),
            b => List.append(&2, Binding, a2, b),
            a,
            {Pieces.final(~S, ~fetch, 1n+q, s, Piece.Sub{h, up, lo, hi} <> rest, k) == True{}: Bool},
            b => eb => e4 => Shared.Bool.and_both(
              Bool.or(
                Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))),
                Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k))
              ),
              Pieces.final(~S, ~fetch, 1n+q, s, rest, k)
            )(
              Bool.or_not_of(
                Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k))
              )(hin => Mst.final_open(~S, ~fetch, q, s, h, up, lo, hi, ks, k)(eo)(ihs(ks)(a2)(ea))(hin))
            )(ihr(b)(eb))
          )(e3)
        )(e2)
      )(e)
    case False{}:
      e => Shared.Bool.and_both(
        Bool.or(
          Bool.not(Bool.and(Bound.after(lo, k), Bound.before(k, hi))),
          Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k))
        ),
        Pieces.final(~S, ~fetch, 1n+q, s, rest, k)
      )(Bound.not_in(lo, hi, k, Look.is_final(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k)))(et))(ihr(a)(e))

# the pieces of a listing under no prefix that reads read every key finally
def Mst.final_list(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +a: List<&2, Binding>,
  +k: List<&2, U32>
) -> {Mst.range.go(~S, ~fetch, f, s, [], ps) == Some{a}: Maybe<&2, List<&2, Binding>>} -> {Pieces.final(~S, ~fetch, f, s, ps, k) == True{}: Bool}:
  match f ps:
    case x Nil{}:
      e => {==}
    case 0n Con{x, rest}:
      e => Empty.absurd({Pieces.final(~S, ~fetch, 0n, s, x <> rest, k) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, Binding>, a, e))
    case 1n+(+q) Con{Piece.Bind{+k2, +v2}, +rest}:
      e => Maybe.map_cases(
        List<&2, Binding>,
        List<&2, Binding>,
        Mst.range.go(~S, ~fetch, 1n+q, s, [], rest),
        +bs => Shared.Bool.when(List<&2, Binding>, Key.leads([], k2), u => Binding{k2, v2} <> bs, u => bs),
        a,
        {Pieces.final(~S, ~fetch, 1n+q, s, rest, k) == True{}: Bool},
        +b => eb => e2 => Mst.final_list(~S, ~fetch, 1n+q, s, rest, b, k)(eb)
      )(e)
    case 1n+(+q) Con{Piece.Sub{+h, +up, +lo, +hi}, +rest}:
      e => Mst.final_list.at(
        ~S,
        ~fetch,
        Bool.and(Bound.meets_lo([], lo), Bound.meets_hi([], hi)),
        q,
        s,
        h,
        up,
        lo,
        hi,
        rest,
        a,
        k,
        {==},
        b => eb => Mst.final_list(~S, ~fetch, 1n+q, s, rest, b, k)(eb),
        ks => b => eb => Mst.final_list(~S, ~fetch, q, s, ks, b, k)(eb)
      )(e)

# a read of a tree that lists whole is final
def Mst.final_root(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>
) -> {Pieces.final(~S, ~fetch, Mst.depth(), s, Mst.root(h), k) == True{}: Bool} -> {
  Look.is_final(Mst.look(~S, ~fetch, s, h, k)) == True{}: Bool
}:
  match h:
    case None{}:
      hf => {==}
    case Some{+h2}:
      hf => Shared.Bool.and_true_left(Look.is_final(Mst.look(~S, ~fetch, s, Some{h2}, k)), True{})(hf)

# Differences of whole trees
# --------------------------

# each subtree of the pieces ps has keys in its bounds and lists whole, q
# levels down
def Pieces.ok(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Piece.Bind{k, v}, rest}:
      Pieces.ok(~S, ~fetch, q, s, rest)
    case Con{Piece.Sub{h, up, +lo, +hi}, rest}:
      Bool.and(
        Bool.and(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        ),
        Pieces.ok(~S, ~fetch, q, s, rest)
      )

# both sides of each of the runs ps are ok
def Runs.ok(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, ps: List<&2, Runs>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{Runs{a, b}, rest}:
      Bool.and(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))

# the pieces ps, then the pieces acc, are ok when both are
def Pieces.ok_append(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +acc: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, ps) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, acc) == True{}: Bool} -> {
  Pieces.ok(~S, ~fetch, q, s, List.append(&2, Piece, ps, acc)) == True{}: Bool
}:
  match ps:
    case Nil{}:
      h => g => g
    case Con{Piece.Bind{k, v}, +rest}:
      h => g => Pieces.ok_append(~S, ~fetch, q, s, rest, acc)(h)(g)
    case Con{Piece.Sub{+h2, +up, +lo, +hi}, +rest}:
      +h => g => Shared.Bool.and_both(
        Bool.and(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        ),
        Pieces.ok(~S, ~fetch, q, s, List.append(&2, Piece, rest, acc))
      )(
        Shared.Bool.and_true_left(
          Bool.and(
            Bound.before([], hi),
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
            )
          ),
          Pieces.ok(~S, ~fetch, q, s, rest)
        )(h)
      )(
        Pieces.ok_append(
          ~S,
          ~fetch,
          q,
          s,
          rest,
          acc
        )(
          Shared.Bool.and_true_right(
            Bool.and(
              Bound.before([], hi),
              Maybe.is_some(
                &2,
                List<&2, Binding>,
                Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
              )
            ),
            Pieces.ok(~S, ~fetch, q, s, rest)
          )(h)
        )(g)
      )

# the piece x before ok pieces is ok when x before others is
def Pieces.ok_move(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  x: Piece,
  -r: List<&2, Piece>,
  +acc: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, x <> r) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, acc) == True{}: Bool} -> {
  Pieces.ok(~S, ~fetch, q, s, x <> acc) == True{}: Bool
}:
  match x:
    case Piece.Bind{k, v}:
      h => g => g
    case Piece.Sub{+h2, +up, +lo, +hi}:
      h => g => Shared.Bool.and_both(
        Bool.and(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        ),
        Pieces.ok(~S, ~fetch, q, s, acc)
      )(
        Shared.Bool.and_true_left(
          Bool.and(
            Bound.before([], hi),
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
            )
          ),
          Pieces.ok(~S, ~fetch, q, s, r)
        )(h)
      )(g)

# the pieces after an ok piece are ok
def Pieces.ok_tail(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  x: Piece,
  +r: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, x <> r) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, r) == True{}: Bool}:
  match x:
    case Piece.Bind{k, v}:
      h => h
    case Piece.Sub{+h2, +up, +lo, +hi}:
      h => Shared.Bool.and_true_right(
        Bool.and(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h2, up, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        ),
        Pieces.ok(~S, ~fetch, q, s, r)
      )(h)

# ok pieces read back to front, after ok pieces acc, are ok
def Pieces.ok_reverse(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +acc: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, ps) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, acc) == True{}: Bool} -> {
  Pieces.ok(~S, ~fetch, q, s, List.reverse.go(&2, Piece, ps, acc)) == True{}: Bool
}:
  match ps:
    case Nil{}:
      h => g => g
    case Con{+x, +rest}:
      +h => g => Pieces.ok_reverse(
        ~S,
        ~fetch,
        q,
        s,
        rest,
        x <> acc
      )(Pieces.ok_tail(~S, ~fetch, q, s, x, rest)(h))(Pieces.ok_move(~S, ~fetch, q, s, x, rest, acc)(h)(g))

# the runs of the round r with the run p first
def Round.pairs_cons(p: Runs, r: Round) -> {Round.pairs(Round.cons(p, r)) == p <> Round.pairs(r): List<&2, Runs>}:
  match r:
    case Round{ks, ps}:
      {==}

# the runs of a round with a differing key are its runs
def Round.pairs_differs(k: List<&2, U32>, v1: List<&2, U32>, v2: List<&2, U32>, r: Round) -> {
  Round.pairs(Round.differs(k, v1, v2, r)) == Round.pairs(r): List<&2, Runs>
}:
  match r:
    case Round{ks, ps}:
      {==}

# the runs of two rounds, one after the other
def Round.pairs_append(a: Round, b: Round) -> {
  Round.pairs(Round.append(a, b)) == List.append(&2, Runs, Round.pairs(a), Round.pairs(b)): List<&2, Runs>
}:
  match a b:
    case Round{k1, p1} Round{k2, p2}:
      {==}

# ok runs, then ok runs, are ok
def Runs.ok_append(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Runs>,
  +acc: List<&2, Runs>
) -> {Runs.ok(~S, ~fetch, q, s, ps) == True{}: Bool} -> {Runs.ok(~S, ~fetch, q, s, acc) == True{}: Bool} -> {
  Runs.ok(~S, ~fetch, q, s, List.append(&2, Runs, ps, acc)) == True{}: Bool
}:
  match ps:
    case Nil{}:
      h => g => g
    case Con{Runs{+a, +b}, +rest}:
      +h => g => Shared.Bool.and_both(
        Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)),
        Runs.ok(~S, ~fetch, q, s, List.append(&2, Runs, rest, acc))
      )(
        Shared.Bool.and_true_left(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h)
      )(
        Runs.ok_append(
          ~S,
          ~fetch,
          q,
          s,
          rest,
          acc
        )(Shared.Bool.and_true_right(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h))(g)
      )

# a run cut out of two ok sides, read back to front, is ok
def Runs.ok_emit(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +sa: List<&2, Piece>,
  +sb: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, sa) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, sb) == True{}: Bool} -> {
  Bool.and(Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sa)), Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sb))) == True{}: Bool
}:
  ha => hb => Shared.Bool.and_both(
    Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sa)),
    Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sb))
  )(Pieces.ok_reverse(~S, ~fetch, q, s, sa, [])(ha)({==}))(Pieces.ok_reverse(~S, ~fetch, q, s, sb, [])(hb)({==}))

# the runs that a cut of ok pieces gives are ok
def Mst.cut_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  as: List<&2, Piece>,
  bs: List<&2, Piece>,
  +sa: List<&2, Piece>,
  +sb: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, as) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, bs) == True{}: Bool} -> {
  Pieces.ok(~S, ~fetch, q, s, sa) == True{}: Bool
} -> {Pieces.ok(~S, ~fetch, q, s, sb) == True{}: Bool} -> {Runs.ok(~S, ~fetch, q, s, Round.pairs(Mst.cut(as, bs, sa, sb))) == True{}: Bool}:
  match as bs:
    case Nil{} Nil{}:
      ha => hb => hsa => hsb => Shared.Bool.and_both(
        Bool.and(Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sa)), Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sb))),
        True{}
      )(Runs.ok_emit(~S, ~fetch, q, s, sa, sb)(hsa)(hsb))({==})
    case Nil{} Con{+y, +rb}:
      ha => +hb => hsa => hsb => Mst.cut_ok(
        ~S,
        ~fetch,
        q,
        s,
        [],
        rb,
        sa,
        y <> sb
      )(ha)(Pieces.ok_tail(~S, ~fetch, q, s, y, rb)(hb))(hsa)(Pieces.ok_move(~S, ~fetch, q, s, y, rb, sb)(hb)(hsb))
    case Con{+x, +ra} Nil{}:
      +ha => hb => hsa => hsb => Mst.cut_ok(
        ~S,
        ~fetch,
        q,
        s,
        ra,
        [],
        x <> sa,
        sb
      )(Pieces.ok_tail(~S, ~fetch, q, s, x, ra)(ha))(hb)(Pieces.ok_move(~S, ~fetch, q, s, x, ra, sa)(ha)(hsa))(hsb)
    case Con{Piece.Sub{+h, +u, +lo, +hi}, +ra} Con{+y, +rb}:
      +ha => hb => hsa => hsb => Mst.cut_ok(
        ~S,
        ~fetch,
        q,
        s,
        ra,
        y <> rb,
        Piece.Sub{h, u, lo, hi} <> sa,
        sb
      )(Pieces.ok_tail(~S, ~fetch, q, s, Piece.Sub{h, u, lo, hi}, ra)(ha))(hb)(
        Pieces.ok_move(~S, ~fetch, q, s, Piece.Sub{h, u, lo, hi}, ra, sa)(ha)(hsa)
      )(hsb)
    case Con{Piece.Bind{+k1, +v1}, +ra} Con{Piece.Sub{+h, +u, +lo, +hi}, +rb}:
      ha => +hb => hsa => hsb => Mst.cut_ok(
        ~S,
        ~fetch,
        q,
        s,
        Piece.Bind{k1, v1} <> ra,
        rb,
        sa,
        Piece.Sub{h, u, lo, hi} <> sb
      )(ha)(Pieces.ok_tail(~S, ~fetch, q, s, Piece.Sub{h, u, lo, hi}, rb)(hb))(hsa)(
        Pieces.ok_move(~S, ~fetch, q, s, Piece.Sub{h, u, lo, hi}, rb, sb)(hb)(hsb)
      )
    case Con{Piece.Bind{+k1, +v1}, +ra} Con{Piece.Bind{+k2, +v2}, +rb}:
      +ha => +hb => +hsa => +hsb => Shared.Bool.when_cases(
        Round,
        x => {Runs.ok(~S, ~fetch, q, s, Round.pairs(x)) == True{}: Bool},
        Cmp.is_lt(Key.cmp(k1, k2)),
        w => Mst.cut(ra, Piece.Bind{k2, v2} <> rb, Piece.Bind{k1, v1} <> sa, sb),
        w => Shared.Bool.when(
          Round,
          Cmp.is_eq(Key.cmp(k1, k2)),
          w2 => Round.cons(Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)}, Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], []))),
          w2 => Mst.cut(Piece.Bind{k1, v1} <> ra, rb, sa, Piece.Bind{k2, v2} <> sb)
        ),
        e1 => Mst.cut_ok(~S, ~fetch, q, s, ra, Piece.Bind{k2, v2} <> rb, Piece.Bind{k1, v1} <> sa, sb)(ha)(hb)(hsa)(hsb),
        e1 => Shared.Bool.when_cases(
          Round,
          x => {Runs.ok(~S, ~fetch, q, s, Round.pairs(x)) == True{}: Bool},
          Cmp.is_eq(Key.cmp(k1, k2)),
          w2 => Round.cons(Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)}, Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], []))),
          w2 => Mst.cut(Piece.Bind{k1, v1} <> ra, rb, sa, Piece.Bind{k2, v2} <> sb),
          e2 =>
            %Equal.sym(
              List<&2, Runs>,
              Round.pairs(Round.cons(Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)}, Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], [])))),
              Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)} <> Round.pairs(Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], []))),
              Round.pairs_cons(Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)}, Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], [])))
            ): {Runs.ok(~S, ~fetch, q, s, _) == True{}: Bool}
            %Equal.sym(
              List<&2, Runs>,
              Round.pairs(Round.differs(k1, v1, v2, Mst.cut(ra, rb, [], []))),
              Round.pairs(Mst.cut(ra, rb, [], [])),
              Round.pairs_differs(k1, v1, v2, Mst.cut(ra, rb, [], []))
            ): {Runs.ok(~S, ~fetch, q, s, Runs{List.reverse(&2, Piece, sa), List.reverse(&2, Piece, sb)} <> _) == True{}: Bool}
            Shared.Bool.and_both(
              Bool.and(Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sa)), Pieces.ok(~S, ~fetch, q, s, List.reverse(&2, Piece, sb))),
              Runs.ok(~S, ~fetch, q, s, Round.pairs(Mst.cut(ra, rb, [], [])))
            )(Runs.ok_emit(~S, ~fetch, q, s, sa, sb)(hsa)(hsb))(Mst.cut_ok(~S, ~fetch, q, s, ra, rb, [], [])(ha)(hb)({==})({==})),
          e2 => Mst.cut_ok(~S, ~fetch, q, s, Piece.Bind{k1, v1} <> ra, rb, sa, Piece.Bind{k2, v2} <> sb)(ha)(hb)(hsa)(hsb)
        )
      )

# both sides of the run r are ok
def Runs.ok1(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, r: Runs) -> Bool:
  match r:
    case Runs{a, b}:
      Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b))

# a trim of ok pieces leaves ok pieces
def Mst.trim_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  as: List<&2, Piece>,
  bs: List<&2, Piece>
) -> {Pieces.ok(~S, ~fetch, q, s, as) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, bs) == True{}: Bool} -> {
  Runs.ok1(~S, ~fetch, q, s, Mst.trim(as, bs)) == True{}: Bool
}:
  match as bs:
    case Con{+x, +ra} Con{+y, +rb}:
      +ha => +hb => Shared.Bool.when_cases(
        Runs,
        r => {Runs.ok1(~S, ~fetch, q, s, r) == True{}: Bool},
        Piece.same(x, y),
        u => Mst.trim(ra, rb),
        u => Runs{x <> ra, y <> rb},
        e => Mst.trim_ok(~S, ~fetch, q, s, ra, rb)(Pieces.ok_tail(~S, ~fetch, q, s, x, ra)(ha))(Pieces.ok_tail(~S, ~fetch, q, s, y, rb)(hb)),
        e => Shared.Bool.and_both(Pieces.ok(~S, ~fetch, q, s, x <> ra), Pieces.ok(~S, ~fetch, q, s, y <> rb))(ha)(hb)
      )
    case Nil{} ys:
      ha => hb => Shared.Bool.and_both(True{}, Pieces.ok(~S, ~fetch, q, s, ys))({==})(hb)
    case Con{+x, +ra} Nil{}:
      ha => hb => Shared.Bool.and_both(Pieces.ok(~S, ~fetch, q, s, x <> ra), True{})(ha)({==})

# a trimmed run trims to ok sides
def Runs.trim_front_ok(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, r: Runs) -> {
  Runs.ok1(~S, ~fetch, q, s, r) == True{}: Bool
} -> {Runs.ok1(~S, ~fetch, q, s, Runs.trim_front(r)) == True{}: Bool}:
  match r:
    case Runs{+a, +b}:
      +h => Mst.trim_ok(
        ~S,
        ~fetch,
        q,
        s,
        a,
        b
      )(Shared.Bool.and_true_left(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b))(h))(
        Shared.Bool.and_true_right(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b))(h)
      )

# a run read back to front has ok sides
def Runs.reverse_ok(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, r: Runs) -> {
  Runs.ok1(~S, ~fetch, q, s, r) == True{}: Bool
} -> {Runs.ok1(~S, ~fetch, q, s, Runs.reverse(r)) == True{}: Bool}:
  match r:
    case Runs{+a, +b}:
      +h => Runs.ok_emit(
        ~S,
        ~fetch,
        q,
        s,
        a,
        b
      )(Shared.Bool.and_true_left(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b))(h))(
        Shared.Bool.and_true_right(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b))(h)
      )

# a run trimmed at both ends has ok sides
def Runs.trim_ok(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +q: Nat, +s: S, +r: Runs) -> {
  Runs.ok1(~S, ~fetch, q, s, r) == True{}: Bool
} -> {Runs.ok1(~S, ~fetch, q, s, Runs.trim(r)) == True{}: Bool}:
  h => Runs.reverse_ok(
    ~S,
    ~fetch,
    q,
    s,
    Runs.trim_front(Runs.reverse(Runs.trim_front(r)))
  )(
    Runs.trim_front_ok(
      ~S,
      ~fetch,
      q,
      s,
      Runs.reverse(Runs.trim_front(r))
    )(Runs.reverse_ok(~S, ~fetch, q, s, Runs.trim_front(r))(Runs.trim_front_ok(~S, ~fetch, q, s, r)(h)))
  )

# a subtree whose bounds hold keys and which lists whole, before ok pieces,
# gives ok pieces
def Pieces.ok_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {Bool.or(Maybe.is_none(&2, Hashes.Hash, m), Bound.before([], hi)) == True{}: Bool} -> {
  Mst.sub_list(~S, ~fetch, q, s, [], m, l, lo, hi) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Pieces.ok(~S, ~fetch, q, s, rest) == True{}: Bool} -> {Pieces.ok(~S, ~fetch, q, s, Piece.sub(m, l, lo, hi, rest)) == True{}: Bool}:
  match m:
    case None{}:
      hn => esl => hr => hr
    case Some{+h}:
      +hn => esl => hr => Shared.Bool.and_both(
        Bool.and(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, l, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        ),
        Pieces.ok(~S, ~fetch, q, s, rest)
      )(
        Shared.Bool.and_both(
          Bound.before([], hi),
          Maybe.is_some(
            &2,
            List<&2, Binding>,
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, l, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks))
          )
        )(hn)(
          Equal.cong(
            Maybe<&2, List<&2, Binding>>,
            Bool,
            x => Maybe.is_some(&2, List<&2, Binding>, x),
            Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, l, lo, hi), ks => Mst.range.go(~S, ~fetch, q, s, [], ks)),
            Some{a},
            Mst.sub_list_on(~S, ~fetch, q, s, h, l, lo, hi, a)(hn)(esl)
          )
        )
      )(hr)

# the pieces of a node whose upper bound holds keys, when a listing of them
# reads, are ok one level down
def Mst.pieces_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +a: List<&2, Binding>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {Bound.before([], hi) == True{}: Bool} -> {
  Mst.range.go(~S, ~fetch, 1n+q, s, [], ks) == Some{a}: Maybe<&2, List<&2, Binding>>
} -> {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool}:
  match xs:
    case Nil{}:
      +ep => +hb => e => Mst.range_list(
        ~S,
        ~fetch,
        prev,
        q,
        s,
        [],
        l,
        lo,
        hi,
        [],
        a,
        {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool},
        +a1 => b => e4 => eb => esl =>
          %Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep): {Pieces.ok(~S, ~fetch, q, s, _) == True{}: Bool}
          Pieces.ok_sub(~S, ~fetch, q, s, prev, l, lo, hi, [], a1)(Bool.or_true_of(Maybe.is_none(&2, Hashes.Hash, prev), Bound.before([], hi))(hb))(esl)({==})
      )(
        Equal.trans(
          Maybe<&2, List<&2, Binding>>,
          Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev, l, lo, hi, [])),
          Mst.range.go(~S, ~fetch, 1n+q, s, [], ks),
          Some{a},
          Equal.cong(
            List<&2, Piece>,
            Maybe<&2, List<&2, Binding>>,
            x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
            Piece.sub(prev, l, lo, hi, []),
            ks,
            Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep)
          ),
          e
        )
      )
    case Con{Item{+ik, +iv, +r}, +rest}:
      ep => +hb => e => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool},
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool},
          +ks2 => +e3 => +e4 => Mst.range_list(
            ~S,
            ~fetch,
            prev,
            q,
            s,
            [],
            l,
            lo,
            Some{ik},
            Piece.Bind{ik, iv} <> ks2,
            a,
            {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool},
            +c1 => b => e5 => eb => esl => Maybe.map_cases(
              List<&2, Binding>,
              List<&2, Binding>,
              Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2),
              +bb => Shared.Bool.when(List<&2, Binding>, Key.leads([], ik), u => Binding{ik, iv} <> bb, u => bb),
              b,
              {Pieces.ok(~S, ~fetch, q, s, ks) == True{}: Bool},
              +b2 => eb2 => e6 =>
                %e4: {Pieces.ok(~S, ~fetch, q, s, _) == True{}: Bool}
                Pieces.ok_sub(
                  ~S,
                  ~fetch,
                  q,
                  s,
                  prev,
                  l,
                  lo,
                  Some{ik},
                  Piece.Bind{ik, iv} <> ks2,
                  c1
                )(
                  Equal.trans(
                    Bool,
                    Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Key.is_lt([], ik)),
                    Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik))),
                    True{},
                    Equal.cong(Bool, Bool, x => Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), x), Key.is_lt([], ik), Bool.not(List.is_empty(&2, U32, ik)), Key.lt_nil_left(ik)),
                    Shared.Bool.and_true_right(
                      Nat.is_eq(Key.level(ik), l),
                      Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
                    )(
                      Shared.Bool.and_true_left(
                        Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                        Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
                      )(c)
                    )
                  )
                )(esl)(Mst.pieces_ok(~S, ~fetch, q, s, rest, l, r, Some{ik}, hi, ks2, b2)(e3)(hb)(eb2))
            )(eb)
          )(
            Equal.trans(
              Maybe<&2, List<&2, Binding>>,
              Mst.range.go(~S, ~fetch, 1n+q, s, [], Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)),
              Mst.range.go(~S, ~fetch, 1n+q, s, [], ks),
              Some{a},
              Equal.cong(
                List<&2, Piece>,
                Maybe<&2, List<&2, Binding>>,
                x => Mst.range.go(~S, ~fetch, 1n+q, s, [], x),
                Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2),
                ks,
                e4
              ),
              e
            )
          )
        )(e2)
      )(ep)

# ok pieces open, one level, to ok pieces
def Mst.open_all_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Piece>,
  -P: Type,
  k: @ps2: List<&2, Piece> -> {Mst.open.all(~S, ~fetch, s, ps) == Some{ps2}: Maybe<&2, List<&2, Piece>>} -> {
    Pieces.ok(~S, ~fetch, q, s, ps2) == True{}: Bool
  } -> P
) -> {Pieces.ok(~S, ~fetch, 1n+q, s, ps) == True{}: Bool} -> P:
  match ps:
    case Nil{}:
      h => k([])({==})({==})
    case Con{Piece.Bind{+k1, +v1}, +rest}:
      h => Mst.open_all_ok(
        ~S,
        ~fetch,
        q,
        s,
        rest,
        P,
        +r2 => er => gr => k(Piece.Bind{k1, v1} <> r2)(
          Equal.cong(
            Maybe<&2, List<&2, Piece>>,
            Maybe<&2, List<&2, Piece>>,
            x => Maybe.map(&2, List<&2, Piece>, List<&2, Piece>, r => Piece.Bind{k1, v1} <> r, x),
            Mst.open.all(~S, ~fetch, s, rest),
            Some{r2},
            er
          )
        )(gr)
      )(h)
    case Con{Piece.Sub{+h, +u, +lo, +hi}, +rest}:
      +hh =>
        +hc = Shared.Bool.and_true_left(
          Bool.and(
            Bound.before([], hi),
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks))
            )
          ),
          Pieces.ok(~S, ~fetch, 1n+q, s, rest)
        )(hh)
        Maybe.some_cases(
          List<&2, Binding>,
          Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks)),
          P,
          +x => ex => Maybe.bind_cases(
            List<&2, Piece>,
            List<&2, Binding>,
            Mst.open(~S, ~fetch, s, h, u, lo, hi),
            ks => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks),
            x,
            P,
            +ks => +eo => ea => Mst.open_cases(
              ~S,
              ~fetch,
              s,
              h,
              u,
              lo,
              hi,
              ks,
              P,
              +l2 => +left2 => +xs2 => ef => eh => en => elt => ee => ep =>
                +oks = Mst.pieces_ok(
                  ~S,
                  ~fetch,
                  q,
                  s,
                  xs2,
                  l2,
                  left2,
                  lo,
                  hi,
                  ks,
                  x
                )(ep)(Shared.Bool.and_true_left(Bound.before([], hi), Maybe.is_some(&2, List<&2, Binding>, Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks2 => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2))))(hc))(ea)
                Mst.open_all_ok(
                  ~S,
                  ~fetch,
                  q,
                  s,
                  rest,
                  P,
                  +r2 => er => gr => k(List.append(&2, Piece, ks, r2))(
                    Equal.trans(
                      Maybe<&2, List<&2, Piece>>,
                      Mst.open.all(~S, ~fetch, s, Piece.Sub{h, u, lo, hi} <> rest),
                      Maybe.map(&2, List<&2, Piece>, List<&2, Piece>, b => List.append(&2, Piece, ks, b), Mst.open.all(~S, ~fetch, s, rest)),
                      Some{List.append(&2, Piece, ks, r2)},
                      Equal.cong(
                        Maybe<&2, List<&2, Piece>>,
                        Maybe<&2, List<&2, Piece>>,
                        y => Maybe.bind(
                          &2,
                          List<&2, Piece>,
                          List<&2, Piece>,
                          y,
                          a => Maybe.map(&2, List<&2, Piece>, List<&2, Piece>, b => List.append(&2, Piece, a, b), Mst.open.all(~S, ~fetch, s, rest))
                        ),
                        Mst.open(~S, ~fetch, s, h, u, lo, hi),
                        Some{ks},
                        eo
                      ),
                      Equal.cong(
                        Maybe<&2, List<&2, Piece>>,
                        Maybe<&2, List<&2, Piece>>,
                        y => Maybe.map(&2, List<&2, Piece>, List<&2, Piece>, b => List.append(&2, Piece, ks, b), y),
                        Mst.open.all(~S, ~fetch, s, rest),
                        Some{r2},
                        er
                      )
                    )
                  )(Pieces.ok_append(~S, ~fetch, q, s, ks, r2)(oks)(gr))
                )(
                  Shared.Bool.and_true_right(
                    Bool.and(
                      Bound.before([], hi),
                      Maybe.is_some(
                        &2,
                        List<&2, Binding>,
                        Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks2 => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks2))
                      )
                    ),
                    Pieces.ok(~S, ~fetch, 1n+q, s, rest)
                  )(hh)
                )
            )(eo)
          )(ex)
        )(
          Shared.Bool.and_true_right(
            Bound.before([], hi),
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 1n+q, s, [], ks))
            )
          )(hc)
        )

# the items of a node
def Node.items(n: Node) -> List<&2, Item>:
  match n:
    case Node{l, left, xs}:
      xs

# an empty list is the empty list
def List.empty_nil(-A: Data, xs: List<&2, A>) -> {List.is_empty(&2, A, xs) == True{}: Bool} -> {xs == []: List<&2, A>}:
  match xs:
    case Nil{}:
      x => {==}
    case Con{head, tail}:
      x => Empty.absurd({head <> tail == [] : List<&2, A>}, {(%x : {\{False: Unit; \{True: Empty; \{}}} : Bool -> Type}(_); Unit{}) : Empty})

# what the runs of the next round must be, q levels down: none when no level
# is left, else ok
def Runs.next(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, q: Nat, +s: S, ps: List<&2, Runs>) -> Bool:
  match q:
    case 0n:
      List.is_empty(&2, Runs, ps)
    case 1n+p:
      Runs.ok(~S, ~fetch, p, s, ps)

# no run is a next round
def Runs.next_nil(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, q: Nat, +s: S) -> {
  Runs.next(~S, ~fetch, q, s, []) == True{}: Bool
}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

# two next rounds, one after the other, are a next round
def Runs.next_append(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  q: Nat,
  +s: S,
  ps: List<&2, Runs>,
  +acc: List<&2, Runs>
) -> {Runs.next(~S, ~fetch, q, s, ps) == True{}: Bool} -> {Runs.next(~S, ~fetch, q, s, acc) == True{}: Bool} -> {
  Runs.next(~S, ~fetch, q, s, List.append(&2, Runs, ps, acc)) == True{}: Bool
}:
  match q:
    case 0n:
      match ps:
        case Nil{}:
          h => g => g
        case Con{x, r}:
          h => g => Empty.absurd({List.is_empty(&2, Runs, x <> List.append(&2, Runs, r, acc)) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+(+p):
      h => g => Runs.ok_append(~S, ~fetch, p, s, ps, acc)(h)(g)

# a step that read and gave a next round
def Step.good(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, q: Nat, +s: S, m: Maybe<&2, Round>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      Runs.next(~S, ~fetch, q, s, Round.pairs(r))

# pieces ok with no level left hold no subtree: a node has an item, so its
# listing needs a level
def Mst.no_sub(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +s: S, ps: List<&2, Piece>) -> {
  Pieces.ok(~S, ~fetch, 0n, s, ps) == True{}: Bool
} -> {Pieces.has_sub(ps) == False{}: Bool}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{Piece.Bind{k, v}, rest}:
      h => Mst.no_sub(~S, ~fetch, s, rest)(h)
    case Con{Piece.Sub{+h, +u, +lo, +hi}, rest}:
      hh => Empty.absurd(
        {True{} == False{}: Bool},
        Maybe.some_cases(
          List<&2, Binding>,
          Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 0n, s, [], ks)),
          Empty,
          +x => ex => Maybe.bind_cases(
            List<&2, Piece>,
            List<&2, Binding>,
            Mst.open(~S, ~fetch, s, h, u, lo, hi),
            ks => Mst.range.go(~S, ~fetch, 0n, s, [], ks),
            x,
            Empty,
            +ks => eo => ea => Mst.open_cases(
              ~S,
              ~fetch,
              s,
              h,
              u,
              lo,
              hi,
              ks,
              Empty,
              +l2 => +left2 => +xs2 => ef => eh => en => elt => ee => ep => Shared.Bool.true_ne_false(
                Equal.trans(
                  Bool,
                  True{},
                  List.is_empty(&2, Item, xs2),
                  False{},
                  Equal.cong(
                    Node,
                    Bool,
                    n => List.is_empty(&2, Item, Node.items(n)),
                    Node{l2, None{}, []},
                    Node{l2, left2, xs2},
                    Equal.sym(
                      Node,
                      Node{l2, left2, xs2},
                      Node{l2, None{}, []},
                      Mst.pieces_empty(
                        xs2,
                        l2,
                        left2,
                        lo,
                        hi
                      )(
                        Equal.trans(
                          Maybe<&2, List<&2, Piece>>,
                          Mst.pieces(xs2, l2, left2, lo, hi),
                          Some{ks},
                          Some{[]},
                          ep,
                          Equal.cong(List<&2, Piece>, Maybe<&2, List<&2, Piece>>, y => Some{y}, ks, [], Mst.range_zero_nil(~S, ~fetch, s, [], ks, x)(ea))
                        )
                      )
                    )
                  ),
                  ee
                )
              )
            )(eo)
          )(ex)
        )(
          Shared.Bool.and_true_right(
            Bound.before([], hi),
            Maybe.is_some(
              &2,
              List<&2, Binding>,
              Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 0n, s, [], ks))
            )
          )(
            Shared.Bool.and_true_left(
              Bool.and(
                Bound.before([], hi),
                Maybe.is_some(
                  &2,
                  List<&2, Binding>,
                  Maybe.bind(&2, List<&2, Piece>, List<&2, Binding>, Mst.open(~S, ~fetch, s, h, u, lo, hi), ks => Mst.range.go(~S, ~fetch, 0n, s, [], ks))
                )
              ),
              Pieces.ok(~S, ~fetch, 0n, s, rest)
            )(hh)
          )
        )
      )

# an or of two False sides is not True
def Bool.or_false_both(a: Bool, -b: Bool) -> {a == False{}: Bool} -> {b == False{}: Bool} -> {Bool.or(a, b) == True{}: Bool} -> Empty:
  match a:
    case True{}:
      ea => eb => e => Shared.Bool.true_ne_false(ea)
    case False{}:
      ea => eb => e => Shared.Bool.true_ne_false(Equal.trans(Bool, True{}, b, False{}, Equal.sym(Bool, b, True{}, e), eb))

# a step of a run with ok sides reads and gives a next round
def Mst.step_at_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  q: Nat,
  +s: S,
  p: Runs
) -> {Runs.ok1(~S, ~fetch, q, s, p) == True{}: Bool} -> {Step.good(~S, ~fetch, q, s, Mst.step.at(~S, ~fetch, s, p)) == True{}: Bool}:
  match q:
    case 0n:
      match p:
        case Runs{+a, +b}:
          +h => Shared.Bool.when_cases(
            Maybe<&2, Round>,
            x => {Step.good(~S, ~fetch, 0n, s, x) == True{}: Bool},
            Bool.or(Pieces.has_sub(a), Pieces.has_sub(b)),
            u => Maybe.bind(
              &2,
              List<&2, Piece>,
              Round,
              Mst.open.all(~S, ~fetch, s, a),
              a2 => Maybe.map(&2, List<&2, Piece>, Round, b2 => Round{[], [Runs{a2, b2}]}, Mst.open.all(~S, ~fetch, s, b))
            ),
            u => Some{Round{Pieces.keys(a, Pieces.keys(b, [])), []}},
            e => Empty.absurd(
              {
                Step.good(
                  ~S,
                  ~fetch,
                  0n,
                  s,
                  Maybe.bind(
                    &2,
                    List<&2, Piece>,
                    Round,
                    Mst.open.all(~S, ~fetch, s, a),
                    a2 => Maybe.map(&2, List<&2, Piece>, Round, b2 => Round{[], [Runs{a2, b2}]}, Mst.open.all(~S, ~fetch, s, b))
                  )
                )
                  == True{}: Bool
              },
              Bool.or_false_both(
                Pieces.has_sub(a),
                Pieces.has_sub(b)
              )(Mst.no_sub(~S, ~fetch, s, a)(Shared.Bool.and_true_left(Pieces.ok(~S, ~fetch, 0n, s, a), Pieces.ok(~S, ~fetch, 0n, s, b))(h)))(
                Mst.no_sub(~S, ~fetch, s, b)(Shared.Bool.and_true_right(Pieces.ok(~S, ~fetch, 0n, s, a), Pieces.ok(~S, ~fetch, 0n, s, b))(h))
              )(e)
            ),
            e => {==}
          )
    case 1n+(+q2):
      match p:
        case Runs{+a, +b}:
          +h => Shared.Bool.when_cases(
            Maybe<&2, Round>,
            x => {Step.good(~S, ~fetch, 1n+q2, s, x) == True{}: Bool},
            Bool.or(Pieces.has_sub(a), Pieces.has_sub(b)),
            u => Maybe.bind(
              &2,
              List<&2, Piece>,
              Round,
              Mst.open.all(~S, ~fetch, s, a),
              a2 => Maybe.map(&2, List<&2, Piece>, Round, b2 => Round{[], [Runs{a2, b2}]}, Mst.open.all(~S, ~fetch, s, b))
            ),
            u => Some{Round{Pieces.keys(a, Pieces.keys(b, [])), []}},
            e => Mst.open_all_ok(
              ~S,
              ~fetch,
              q2,
              s,
              a,
              {
                Step.good(
                  ~S,
                  ~fetch,
                  1n+q2,
                  s,
                  Maybe.bind(
                    &2,
                    List<&2, Piece>,
                    Round,
                    Mst.open.all(~S, ~fetch, s, a),
                    a2 => Maybe.map(&2, List<&2, Piece>, Round, b2 => Round{[], [Runs{a2, b2}]}, Mst.open.all(~S, ~fetch, s, b))
                  )
                )
                  == True{}: Bool
              },
              +a2 => ea => ga => Mst.open_all_ok(
                ~S,
                ~fetch,
                q2,
                s,
                b,
                {
                  Step.good(
                    ~S,
                    ~fetch,
                    1n+q2,
                    s,
                    Maybe.bind(
                      &2,
                      List<&2, Piece>,
                      Round,
                      Mst.open.all(~S, ~fetch, s, a),
                      a3 => Maybe.map(&2, List<&2, Piece>, Round, b2 => Round{[], [Runs{a3, b2}]}, Mst.open.all(~S, ~fetch, s, b))
                    )
                  )
                    == True{}: Bool
                },
                +b2 => eb => gb =>
                  %Equal.sym(Maybe<&2, List<&2, Piece>>, Mst.open.all(~S, ~fetch, s, a), Some{a2}, ea): {
                    Step.good(
                      ~S,
                      ~fetch,
                      1n+q2,
                      s,
                      Maybe.bind(
                        &2,
                        List<&2, Piece>,
                        Round,
                        _,
                        a3 => Maybe.map(&2, List<&2, Piece>, Round, b3 => Round{[], [Runs{a3, b3}]}, Mst.open.all(~S, ~fetch, s, b))
                      )
                    )
                      == True{}: Bool
                  }
                  %Equal.sym(Maybe<&2, List<&2, Piece>>, Mst.open.all(~S, ~fetch, s, b), Some{b2}, eb): {
                    Step.good(~S, ~fetch, 1n+q2, s, Maybe.map(&2, List<&2, Piece>, Round, b3 => Round{[], [Runs{a2, b3}]}, _)) == True{}: Bool
                  }
                  Shared.Bool.and_both(
                    Bool.and(Pieces.ok(~S, ~fetch, q2, s, a2), Pieces.ok(~S, ~fetch, q2, s, b2)),
                    True{}
                  )(Shared.Bool.and_both(Pieces.ok(~S, ~fetch, q2, s, a2), Pieces.ok(~S, ~fetch, q2, s, b2))(ga)(gb))({==})
              )(Shared.Bool.and_true_right(Pieces.ok(~S, ~fetch, 1n+q2, s, a), Pieces.ok(~S, ~fetch, 1n+q2, s, b))(h))
            )(Shared.Bool.and_true_left(Pieces.ok(~S, ~fetch, 1n+q2, s, a), Pieces.ok(~S, ~fetch, 1n+q2, s, b))(h)),
            e => {==}
          )

# two good steps, one after the other, are a good step
def Step.good_bind(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  m1: Maybe<&2, Round>,
  m2: Maybe<&2, Round>
) -> {Step.good(~S, ~fetch, q, s, m1) == True{}: Bool} -> {Step.good(~S, ~fetch, q, s, m2) == True{}: Bool} -> {
  Step.good(~S, ~fetch, q, s, Maybe.bind(&2, Round, Round, m1, a => Maybe.map(&2, Round, Round, b => Round.append(a, b), m2))) == True{}: Bool
}:
  match m1 m2:
    case None{} y:
      h => g => Empty.absurd(
        {Step.good(~S, ~fetch, q, s, None{}) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{r1} None{}:
      h => g => Empty.absurd(
        {Step.good(~S, ~fetch, q, s, None{}) == True{}: Bool},
        Shared.Bool.false_ne_true(g)
      )
    case Some{+r1} Some{+r2}:
      h => g =>
        %Equal.sym(
          List<&2, Runs>,
          Round.pairs(Round.append(r1, r2)),
          List.append(&2, Runs, Round.pairs(r1), Round.pairs(r2)),
          Round.pairs_append(r1, r2)
        ): {Runs.next(~S, ~fetch, q, s, _) == True{}: Bool}
        Runs.next_append(~S, ~fetch, q, s, Round.pairs(r1), Round.pairs(r2))(h)(g)

# a step of ok runs reads and gives a next round
def Mst.step_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Runs>
) -> {Runs.ok(~S, ~fetch, q, s, ps) == True{}: Bool} -> {Step.good(~S, ~fetch, q, s, Mst.step(~S, ~fetch, s, ps)) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => Runs.next_nil(~S, ~fetch, q, s)
    case Con{Runs{+a, +b}, +rest}:
      +h => Step.good_bind(
        ~S,
        ~fetch,
        q,
        s,
        Mst.step.at(~S, ~fetch, s, Runs.trim(Runs{a, b})),
        Mst.step(~S, ~fetch, s, rest)
      )(
        Mst.step_at_ok(
          ~S,
          ~fetch,
          q,
          s,
          Runs.trim(Runs{a, b})
        )(
          Runs.trim_ok(
            ~S,
            ~fetch,
            q,
            s,
            Runs{a, b}
          )(Shared.Bool.and_true_left(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h))
        )
      )(
        Mst.step_ok(
          ~S,
          ~fetch,
          q,
          s,
          rest
        )(Shared.Bool.and_true_right(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h))
      )

# a bind of a good step whose next rounds read, reads
def Step.bind_good(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  q: Nat,
  +s: S,
  m: Maybe<&2, Round>,
  -f: Round -> Maybe<&2, List<&2, List<&2, U32>>>,
  hg: {Step.good(~S, ~fetch, q, s, m) == True{}: Bool},
  hf: @r: Round -> {Runs.next(~S, ~fetch, q, s, Round.pairs(r)) == True{}: Bool} -> {
    Maybe.is_some(&2, List<&2, List<&2, U32>>, f(r)) == True{}: Bool
  }
) -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Maybe.bind(&2, Round, List<&2, List<&2, U32>>, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hg))
    case Some{+r}:
      hf(r)(hg)

# a bind of a value whose every next reads, reads
def Maybe.bind_some(
  -A: Data,
  -B: Data,
  m: Maybe<&2, A>,
  -f: A -> Maybe<&2, B>,
  h1: {Maybe.is_some(&2, A, m) == True{}: Bool},
  h2: @x: A -> {Maybe.is_some(&2, B, f(x)) == True{}: Bool}
) -> {Maybe.is_some(&2, B, Maybe.bind(&2, A, B, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h1))
    case Some{+x}:
      h2(x)

# a difference of ok runs reads, when its next round (ihn) and its other runs
# (ihr) read
def Mst.diff_some.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +a: List<&2, Piece>,
  +b: List<&2, Piece>,
  +rest: List<&2, Runs>,
  +h: {Runs.ok(~S, ~fetch, q, s, Runs{a, b} <> rest) == True{}: Bool},
  ihr: {Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, 1n+q, s, rest)) == True{}: Bool},
  ihn: @ps: List<&2, Runs> -> {Runs.next(~S, ~fetch, q, s, ps) == True{}: Bool} -> {
    Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, q, s, ps)) == True{}: Bool
  }
) -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, 1n+q, s, Runs{a, b} <> rest)) == True{}: Bool}:
  Step.bind_good(
    ~S,
    ~fetch,
    q,
    s,
    Mst.step(~S, ~fetch, s, Round.pairs(Mst.cut(a, b, [], []))),
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
          Round.keys(Mst.cut(a, b, [], [])),
          List.append(&2, List<&2, U32>, Round.keys(r), List.append(&2, List<&2, U32>, k3, k4))
        ),
        Mst.diff.go(~S, ~fetch, 1n+q, s, rest)
      )
    ),
    Mst.step_ok(
      ~S,
      ~fetch,
      q,
      s,
      Round.pairs(Mst.cut(a, b, [], []))
    )(
      Mst.cut_ok(
        ~S,
        ~fetch,
        q,
        s,
        a,
        b,
        [],
        []
      )(
        Shared.Bool.and_true_left(
          Pieces.ok(~S, ~fetch, q, s, a),
          Pieces.ok(~S, ~fetch, q, s, b)
        )(
          Shared.Bool.and_true_left(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h)
        )
      )(
        Shared.Bool.and_true_right(
          Pieces.ok(~S, ~fetch, q, s, a),
          Pieces.ok(~S, ~fetch, q, s, b)
        )(
          Shared.Bool.and_true_left(Bool.and(Pieces.ok(~S, ~fetch, q, s, a), Pieces.ok(~S, ~fetch, q, s, b)), Runs.ok(~S, ~fetch, q, s, rest))(h)
        )
      )({==})({==})
    ),
    +r => hn => Maybe.bind_some(
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
          Round.keys(Mst.cut(a, b, [], [])),
          List.append(&2, List<&2, U32>, Round.keys(r), List.append(&2, List<&2, U32>, k3, k4))
        ),
        Mst.diff.go(~S, ~fetch, 1n+q, s, rest)
      ),
      ihn(Round.pairs(r))(hn),
      x => Equal.trans(
        Bool,
        Maybe.is_some(
          &2,
          List<&2, List<&2, U32>>,
          Maybe.map(
            &2,
            List<&2, List<&2, U32>>,
            List<&2, List<&2, U32>>,
            k4 => List.append(
              &2,
              List<&2, U32>,
              Round.keys(Mst.cut(a, b, [], [])),
              List.append(&2, List<&2, U32>, Round.keys(r), List.append(&2, List<&2, U32>, x, k4))
            ),
            Mst.diff.go(~S, ~fetch, 1n+q, s, rest)
          )
        ),
        Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, 1n+q, s, rest)),
        True{},
        Maybe.map_is_some(
          List<&2, List<&2, U32>>,
          List<&2, List<&2, U32>>,
          k4 => List.append(
            &2,
            List<&2, U32>,
            Round.keys(Mst.cut(a, b, [], [])),
            List.append(&2, List<&2, U32>, Round.keys(r), List.append(&2, List<&2, U32>, x, k4))
          ),
          Mst.diff.go(~S, ~fetch, 1n+q, s, rest)
        ),
        ihr
      )
    )
  )

# a difference of ok runs reads, while levels are left
def Mst.diff_some(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, q: Nat, +s: S, runs: List<&2, Runs>) -> {
  Runs.ok(~S, ~fetch, q, s, runs) == True{}: Bool
} -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, 1n+q, s, runs)) == True{}: Bool}:
  match q:
    case 0n:
      match runs:
        case Nil{}:
          h => {==}
        case Con{Runs{+a, +b}, +rest}:
          +h => Mst.diff_some.con(
            ~S,
            ~fetch,
            0n,
            s,
            a,
            b,
            rest,
            h,
            Mst.diff_some(
              ~S,
              ~fetch,
              0n,
              s,
              rest
            )(Shared.Bool.and_true_right(Bool.and(Pieces.ok(~S, ~fetch, 0n, s, a), Pieces.ok(~S, ~fetch, 0n, s, b)), Runs.ok(~S, ~fetch, 0n, s, rest))(h)),
            ps => hn =>
              %Equal.sym(List<&2, Runs>, ps, [], List.empty_nil(Runs, ps)(hn)): {
                Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff.go(~S, ~fetch, 0n, s, _)) == True{}: Bool
              }
              {==}
          )
    case 1n+(+q2):
      match runs:
        case Nil{}:
          h => {==}
        case Con{Runs{+a, +b}, +rest}:
          +h => Mst.diff_some.con(
            ~S,
            ~fetch,
            1n+q2,
            s,
            a,
            b,
            rest,
            h,
            Mst.diff_some(
              ~S,
              ~fetch,
              1n+q2,
              s,
              rest
            )(Shared.Bool.and_true_right(Bool.and(Pieces.ok(~S, ~fetch, 1n+q2, s, a), Pieces.ok(~S, ~fetch, 1n+q2, s, b)), Runs.ok(~S, ~fetch, 1n+q2, s, rest))(h)),
            ps => hn => Mst.diff_some(~S, ~fetch, q2, s, ps)(hn)
          )

# the root of a tree that lists whole is ok
def Mst.root_ok(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Binding>
) -> {Mst.range(~S, ~fetch, s, h, []) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {Pieces.ok(~S, ~fetch, 63n, s, Mst.root(h)) == True{}: Bool}:
  match h:
    case None{}:
      e => {==}
    case Some{+h1}:
      e => Mst.range_list(
        ~S,
        ~fetch,
        Some{h1},
        63n,
        s,
        [],
        Mst.depth(),
        None{},
        None{},
        [],
        bs,
        {Pieces.ok(~S, ~fetch, 63n, s, Mst.root(Some{h1})) == True{}: Bool},
        +a1 => b => e4 => eb => esl => Pieces.ok_sub(~S, ~fetch, 63n, s, Some{h1}, Mst.depth(), None{}, None{}, [], a1)({==})(esl)({==})
      )(e)

# a difference of two trees that list whole reads
def Mst.diff_whole(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Maybe<&2, Hashes.Hash>,
  +h2: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Binding>,
  +bs2: List<&2, Binding>
) -> {Mst.range(~S, ~fetch, s, h, []) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {
  Mst.range(~S, ~fetch, s, h2, []) == Some{bs2}: Maybe<&2, List<&2, Binding>>
} -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Mst.diff(~S, ~fetch, s, h, h2)) == True{}: Bool}:
  e1 => e2 => Mst.diff_some(
    ~S,
    ~fetch,
    63n,
    s,
    [Runs{Mst.root(h), Mst.root(h2)}]
  )(
    Shared.Bool.and_both(
      Bool.and(Pieces.ok(~S, ~fetch, 63n, s, Mst.root(h)), Pieces.ok(~S, ~fetch, 63n, s, Mst.root(h2))),
      True{}
    )(
      Shared.Bool.and_both(Pieces.ok(~S, ~fetch, 63n, s, Mst.root(h)), Pieces.ok(~S, ~fetch, 63n, s, Mst.root(h2)))(Mst.root_ok(~S, ~fetch, s, h, bs)(e1))(
        Mst.root_ok(~S, ~fetch, s, h2, bs2)(e2)
      )
    )({==})
  )

# Differences
# -----------

# the key a is not after the key b
def Key.le(a: List<&2, U32>, b: List<&2, U32>) -> Bool:
  Bool.not(Key.is_lt(b, a))

# Key.cmp, by its three cases
def Key.cases.at(
  c: Cmp,
  -a: List<&2, U32>,
  -b: List<&2, U32>,
  -P: Type,
  e: {Key.cmp(a, b) == c: Cmp},
  kl: {Key.cmp(a, b) == LT{}: Cmp} -> P,
  ke: {Key.cmp(a, b) == EQ{}: Cmp} -> P,
  kg: {Key.cmp(a, b) == GT{}: Cmp} -> P
) -> P:
  match c:
    case LT{}:
      kl(e)
    case EQ{}:
      ke(e)
    case GT{}:
      kg(e)

# a key is not before itself
def Key.lt_irrefl(+a: List<&2, U32>) -> {Key.is_lt(a, a) == False{}: Bool}:
  %Equal.sym(Bool, Key.is_lt(a, a), Cmp.is_lt(Key.cmp(a, a)), Key.is_lt_cmp(a, a)): {_ == False{}: Bool}
  %Equal.sym(Cmp, Key.cmp(a, a), EQ{}, Key.cmp_refl(a)): {Cmp.is_lt(_) == False{}: Bool}
  {==}

# a key before b is not after it
def Key.lt_asym(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {Key.is_lt(b, a) == False{}: Bool}:
  h =>
    %Equal.sym(Bool, Key.is_lt(b, a), Cmp.is_lt(Key.cmp(b, a)), Key.is_lt_cmp(b, a)): {_ == False{}: Bool}
    %Equal.sym(Cmp, Key.cmp(b, a), Cmp.flip(Key.cmp(a, b)), Key.cmp_flip(a, b)): {Cmp.is_lt(_) == False{}: Bool}
    %Equal.sym(
      Cmp,
      Key.cmp(a, b),
      LT{},
      Cmp.lt_true(Key.cmp(a, b))(Equal.trans(Bool, Cmp.is_lt(Key.cmp(a, b)), Key.is_lt(a, b), True{}, Equal.sym(Bool, Key.is_lt(a, b), Cmp.is_lt(Key.cmp(a, b)), Key.is_lt_cmp(a, b)), h))
    ): {Cmp.is_lt(Cmp.flip(_)) == False{}: Bool}
    {==}

# a key before b has other words than b
def Key.lt_ne(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, a, b) == False{}: Bool
}:
  h =>
    %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, a, b), Cmp.is_eq(Key.cmp(a, b)), Key.is_eq_cmp(a, b)): {_ == False{}: Bool}
    %Equal.sym(
      Cmp,
      Key.cmp(a, b),
      LT{},
      Cmp.lt_true(Key.cmp(a, b))(Equal.trans(Bool, Cmp.is_lt(Key.cmp(a, b)), Key.is_lt(a, b), True{}, Equal.sym(Bool, Key.is_lt(a, b), Cmp.is_lt(Key.cmp(a, b)), Key.is_lt_cmp(a, b)), h))
    ): {Cmp.is_eq(_) == False{}: Bool}
    {==}

# a <= b and b < c give a < c
def Key.le_lt(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.le(a, b) == True{}: Bool} -> {Key.is_lt(b, c) == True{}: Bool} -> {
  Key.is_lt(a, c) == True{}: Bool
}:
  +h => +g => Key.cases.at(
    Key.cmp(a, b),
    a,
    b,
    {Key.is_lt(a, c) == True{}: Bool},
    {==},
    el => Key.lt_trans(a, b, c)(Equal.trans(Bool, Key.is_lt(a, b), Cmp.is_lt(Key.cmp(a, b)), True{}, Key.is_lt_cmp(a, b), Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(a, b), LT{}, el)))(g),
    ee =>
      %Equal.sym(List<&2, U32>, a, b, Key.cmp_eq(a, b)(ee)): {Key.is_lt(_, c) == True{}: Bool}
      g,
    eg => Empty.absurd(
      {Key.is_lt(a, c) == True{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Bool.not(Key.is_lt(b, a)),
          False{},
          Equal.sym(Bool, Bool.not(Key.is_lt(b, a)), True{}, h),
          Equal.cong(
            Bool,
            Bool,
            Bool.not,
            Key.is_lt(b, a),
            True{},
            Equal.trans(
              Bool,
              Key.is_lt(b, a),
              Cmp.is_lt(Key.cmp(b, a)),
              True{},
              Key.is_lt_cmp(b, a),
              Equal.trans(
                Bool,
                Cmp.is_lt(Key.cmp(b, a)),
                Cmp.is_lt(Cmp.flip(Key.cmp(a, b))),
                True{},
                Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(b, a), Cmp.flip(Key.cmp(a, b)), Key.cmp_flip(a, b)),
                Equal.cong(Cmp, Bool, x => Cmp.is_lt(Cmp.flip(x)), Key.cmp(a, b), GT{}, eg)
              )
            )
          )
        )
      )
    )
  )

# a < b and b <= c give a < c
def Key.lt_le(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {Key.le(b, c) == True{}: Bool} -> {
  Key.is_lt(a, c) == True{}: Bool
}:
  +h => +g => Key.cases.at(
    Key.cmp(b, c),
    b,
    c,
    {Key.is_lt(a, c) == True{}: Bool},
    {==},
    el => Key.lt_trans(a, b, c)(h)(Equal.trans(Bool, Key.is_lt(b, c), Cmp.is_lt(Key.cmp(b, c)), True{}, Key.is_lt_cmp(b, c), Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(b, c), LT{}, el))),
    ee =>
      %Key.cmp_eq(b, c)(ee): {Key.is_lt(a, _) == True{}: Bool}
      h,
    eg => Empty.absurd(
      {Key.is_lt(a, c) == True{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Bool.not(Key.is_lt(c, b)),
          False{},
          Equal.sym(Bool, Bool.not(Key.is_lt(c, b)), True{}, g),
          Equal.cong(
            Bool,
            Bool,
            Bool.not,
            Key.is_lt(c, b),
            True{},
            Equal.trans(
              Bool,
              Key.is_lt(c, b),
              Cmp.is_lt(Key.cmp(c, b)),
              True{},
              Key.is_lt_cmp(c, b),
              Equal.trans(
                Bool,
                Cmp.is_lt(Key.cmp(c, b)),
                Cmp.is_lt(Cmp.flip(Key.cmp(b, c))),
                True{},
                Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(c, b), Cmp.flip(Key.cmp(b, c)), Key.cmp_flip(b, c)),
                Equal.cong(Cmp, Bool, x => Cmp.is_lt(Cmp.flip(x)), Key.cmp(b, c), GT{}, eg)
              )
            )
          )
        )
      )
    )
  )

# a key is not after itself
def Key.le_refl(+a: List<&2, U32>) -> {Key.le(a, a) == True{}: Bool}:
  %Equal.sym(Bool, Key.is_lt(a, a), False{}, Key.lt_irrefl(a)): {Bool.not(_) == True{}: Bool}
  {==}

# a key before b is not after b
def Key.lt_le_of(+a: List<&2, U32>, +b: List<&2, U32>) -> {Key.is_lt(a, b) == True{}: Bool} -> {Key.le(a, b) == True{}: Bool}:
  h =>
    %Equal.sym(Bool, Key.is_lt(b, a), False{}, Key.lt_asym(a, b)(h)): {Bool.not(_) == True{}: Bool}
    {==}

# a <= b and b <= c give a <= c
def Key.le_trans(+a: List<&2, U32>, +b: List<&2, U32>, +c: List<&2, U32>) -> {Key.le(a, b) == True{}: Bool} -> {Key.le(b, c) == True{}: Bool} -> {
  Key.le(a, c) == True{}: Bool
}:
  +h => +g => Key.cases.at(
    Key.cmp(c, a),
    c,
    a,
    {Key.le(a, c) == True{}: Bool},
    {==},
    el => Empty.absurd(
      {Key.le(a, c) == True{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Key.is_lt(c, b),
          False{},
          Equal.sym(
            Bool,
            Key.is_lt(c, b),
            True{},
            Key.lt_le(c, a, b)(Equal.trans(Bool, Key.is_lt(c, a), Cmp.is_lt(Key.cmp(c, a)), True{}, Key.is_lt_cmp(c, a), Equal.cong(Cmp, Bool, Cmp.is_lt, Key.cmp(c, a), LT{}, el)))(h)
          ),
          Shared.Bool.not_true(Key.is_lt(c, b))(g)
        )
      )
    ),
    ee =>
      %Equal.sym(Bool, Key.is_lt(c, a), Cmp.is_lt(Key.cmp(c, a)), Key.is_lt_cmp(c, a)): {Bool.not(_) == True{}: Bool}
      %Equal.sym(Cmp, Key.cmp(c, a), EQ{}, ee): {Bool.not(Cmp.is_lt(_)) == True{}: Bool}
      {==},
    eg =>
      %Equal.sym(Bool, Key.is_lt(c, a), Cmp.is_lt(Key.cmp(c, a)), Key.is_lt_cmp(c, a)): {Bool.not(_) == True{}: Bool}
      %Equal.sym(Cmp, Key.cmp(c, a), GT{}, eg): {Bool.not(Cmp.is_lt(_)) == True{}: Bool}
      {==}
  )

# the key k comes no later than the bound lo, which a subtree after k starts
# at (none: no bound, so no subtree is after k)
def Bound.at_most(k: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>) -> Bool:
  match lo:
    case None{}:
      False{}
    case Some{a}:
      Key.le(k, a)

# the bound hi, which a subtree before k ends at, comes no later than k
def Bound.at_least(hi: Maybe<&2, List<&2, U32>>, k: List<&2, U32>) -> Bool:
  match hi:
    case None{}:
      False{}
    case Some{b}:
      Key.le(b, k)

# a subtree that ends at hi is before one that starts at lo
def Bound.ends_before(hi: Maybe<&2, List<&2, U32>>, lo: Maybe<&2, List<&2, U32>>) -> Bool:
  match hi lo:
    case Some{b} Some{a}:
      Key.le(b, a)
    case x y:
      False{}

# each key of the piece x comes before each key of the piece y
def Piece.before(x: Piece, y: Piece) -> Bool:
  match x y:
    case Piece.Bind{k1, v1} Piece.Bind{k2, v2}:
      Key.is_lt(k1, k2)
    case Piece.Bind{k, v} Piece.Sub{h, u, lo, hi}:
      Bound.at_most(k, lo)
    case Piece.Sub{h, u, lo, hi} Piece.Bind{k, v}:
      Bound.at_least(hi, k)
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Sub{h2, u2, lo2, hi2}:
      Bound.ends_before(hi1, lo2)

# the piece x may hold the key k: a binding of k, or a subtree whose bounds
# hold k
def Piece.covers(x: Piece, +k: List<&2, U32>) -> Bool:
  match x:
    case Piece.Bind{k2, v}:
      Shared.List.is_eq(~U32, ~U32.is_eq, k2, k)
    case Piece.Sub{h, u, +lo, +hi}:
      Bool.and(Bound.after(lo, k), Bound.before(k, hi))

# a piece of the pieces ps may hold k
def Pieces.covers(ps: List<&2, Piece>, +k: List<&2, U32>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{+x, rest}:
      Bool.or(Piece.covers(x, k), Pieces.covers(rest, k))

# the value of k that the piece x gives, read f levels down
def Piece.value(~S: Data, ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>, +f: Nat, +s: S, x: Piece, +k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match x:
    case Piece.Bind{k2, v}:
      Some{v}
    case Piece.Sub{h, u, lo, hi}:
      Look.value(Mst.look.go(~S, ~fetch, f, s, Room{u, lo, hi}, Some{h}, k))

# the value of k that the first piece of ps that may hold it gives (none: no
# piece may hold it)
def Pieces.value(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +k: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  match ps:
    case Nil{}:
      None{}
    case Con{+x, rest}:
      Shared.Bool.when(
        Maybe<&2, List<&2, U32>>,
        Piece.covers(x, k),
        u => Piece.value(~S, ~fetch, f, s, x, k),
        u => Pieces.value(~S, ~fetch, f, s, rest, k)
      )

# each piece of ps comes after the piece x
def Pieces.after_all(+x: Piece, ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{y, rest}:
      Bool.and(Piece.before(x, y), Pieces.after_all(x, rest))

# the pieces ps come in the order of their keys, each after the ones before
def Pieces.sorted(ps: List<&2, Piece>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{+x, +rest}:
      Bool.and(Pieces.after_all(x, rest), Pieces.sorted(rest))

# the first side of a False or is False
def Bool.or_false_l(a: Bool, -b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {a == False{}: Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => {==}

# the second side of a False or is False
def Bool.or_false_r(a: Bool, -b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case True{}:
      h => Empty.absurd({b == False{}: Bool}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => h

# pieces that may not hold k give no value of it
def Pieces.value_none(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Pieces.covers(ps, k) == False{}: Bool} -> {Pieces.value(~S, ~fetch, f, s, ps, k) == None{}: Maybe<&2, List<&2, U32>>}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+x, +rest}:
      +h =>
        %Equal.sym(Bool, Piece.covers(x, k), False{}, Bool.or_false_l(Piece.covers(x, k), Pieces.covers(rest, k))(h)): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Piece.value(~S, ~fetch, f, s, x, k),
            u => Pieces.value(~S, ~fetch, f, s, rest, k)
          )
            == None{}: Maybe<&2, List<&2, U32>>
        }
        Pieces.value_none(~S, ~fetch, f, s, rest, k)(Bool.or_false_r(Piece.covers(x, k), Pieces.covers(rest, k))(h))

# pieces that may not hold k, then others: the others give its value
def Pieces.value_right(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +qs: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Pieces.covers(ps, k) == False{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, List.append(&2, Piece, ps, qs), k) == Pieces.value(~S, ~fetch, f, s, qs, k): Maybe<&2, List<&2, U32>>
}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+x, +rest}:
      +h =>
        %Equal.sym(Bool, Piece.covers(x, k), False{}, Bool.or_false_l(Piece.covers(x, k), Pieces.covers(rest, k))(h)): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Piece.value(~S, ~fetch, f, s, x, k),
            u => Pieces.value(~S, ~fetch, f, s, List.append(&2, Piece, rest, qs), k)
          )
            == Pieces.value(~S, ~fetch, f, s, qs, k): Maybe<&2, List<&2, U32>>
        }
        Pieces.value_right(~S, ~fetch, f, s, rest, qs, k)(Bool.or_false_r(Piece.covers(x, k), Pieces.covers(rest, k))(h))

# pieces, then others that may not hold k: the first give its value
def Pieces.value_left(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  ps: List<&2, Piece>,
  +qs: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Pieces.covers(qs, k) == False{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, List.append(&2, Piece, ps, qs), k) == Pieces.value(~S, ~fetch, f, s, ps, k): Maybe<&2, List<&2, U32>>
}:
  match ps:
    case Nil{}:
      h => Pieces.value_none(~S, ~fetch, f, s, qs, k)(h)
    case Con{+x, +rest}:
      h => Equal.cong(
        Maybe<&2, List<&2, U32>>,
        Maybe<&2, List<&2, U32>>,
        z => Shared.Bool.when(Maybe<&2, List<&2, U32>>, Piece.covers(x, k), u => Piece.value(~S, ~fetch, f, s, x, k), u => z),
        Pieces.value(~S, ~fetch, f, s, List.append(&2, Piece, rest, qs), k),
        Pieces.value(~S, ~fetch, f, s, rest, k),
        Pieces.value_left(~S, ~fetch, f, s, rest, qs, k)(h)
      )

# a Bool, by its two cases
def Bool.cases(b: Bool, -P: Type, kt: {b == True{}: Bool} -> P, kf: {b == False{}: Bool} -> P) -> P:
  match b:
    case True{}:
      kt({==})
    case False{}:
      kf({==})

# a Bool that is not True is False
def Bool.false_of(b: Bool, no: {b == True{}: Bool} -> Empty) -> {b == False{}: Bool}:
  match b:
    case True{}:
      Empty.absurd({True{} == False{}: Bool}, no({==}))
    case False{}:
      {==}

# Piece.disjoint for a binding x, by the lower bound lo of the subtree y
def Piece.disjoint.bs(+k: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>, -hi: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>) -> {
  Bound.at_most(k, lo) == True{}: Bool
} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool} -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, key) == False{}: Bool}:
  match lo:
    case None{}:
      hb => hc => Empty.absurd({Shared.List.is_eq(~U32, ~U32.is_eq, k, key) == False{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+a}:
      hb => hc => Key.lt_ne(k, key)(Key.le_lt(k, a, key)(hb)(Shared.Bool.and_true_left(Key.is_lt(a, key), Bound.before(key, hi))(hc)))

# Piece.disjoint for a subtree x before a binding, by the upper bound hi of x
def Piece.disjoint.sb(+lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>, +key: List<&2, U32>) -> {
  Bound.at_least(hi, k) == True{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, k, key) == True{}: Bool} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == False{}: Bool}:
  match hi:
    case None{}:
      hb => hc => Empty.absurd({Bool.and(Bound.after(lo, key), True{}) == False{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+b}:
      hb => hc =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, key)(hc): {Bool.and(Bound.after(lo, _), Key.is_lt(_, b)) == False{}: Bool}
        %Equal.sym(Bool, Key.is_lt(k, b), False{}, Shared.Bool.not_true(Key.is_lt(k, b))(hb)): {Bool.and(Bound.after(lo, k), _) == False{}: Bool}
        Shared.Bool.and_false_right(Bound.after(lo, k))

# Piece.disjoint for two subtrees, by the upper bound of x and the lower one
# of y
def Piece.disjoint.ss(
  +lo1: Maybe<&2, List<&2, U32>>,
  hi1: Maybe<&2, List<&2, U32>>,
  lo2: Maybe<&2, List<&2, U32>>,
  -hi2: Maybe<&2, List<&2, U32>>,
  +key: List<&2, U32>
) -> {Bound.ends_before(hi1, lo2) == True{}: Bool} -> {Bool.and(Bound.after(lo2, key), Bound.before(key, hi2)) == True{}: Bool} -> {
  Bool.and(Bound.after(lo1, key), Bound.before(key, hi1)) == False{}: Bool
}:
  match hi1 lo2:
    case Some{+b} Some{+a}:
      hb => hc =>
        %Equal.sym(
          Bool,
          Key.is_lt(key, b),
          False{},
          Key.lt_asym(b, key)(Key.le_lt(b, a, key)(hb)(Shared.Bool.and_true_left(Key.is_lt(a, key), Bound.before(key, hi2))(hc)))
        ): {Bool.and(Bound.after(lo1, key), _) == False{}: Bool}
        Shared.Bool.and_false_right(Bound.after(lo1, key))
    case None{} y:
      hb => hc => Empty.absurd({Bool.and(Bound.after(lo1, key), True{}) == False{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+b} None{}:
      hb => hc => Empty.absurd({Bool.and(Bound.after(lo1, key), Key.is_lt(key, b)) == False{}: Bool}, Shared.Bool.false_ne_true(hb))

# a key that a piece y may hold, the piece x before y may not hold
def Piece.disjoint(x: Piece, y: Piece, +key: List<&2, U32>) -> {Piece.before(x, y) == True{}: Bool} -> {Piece.covers(y, key) == True{}: Bool} -> {
  Piece.covers(x, key) == False{}: Bool
}:
  match x y:
    case Piece.Bind{+k1, v1} Piece.Bind{+k2, v2}:
      hb => hc =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k2, key)(hc): {Shared.List.is_eq(~U32, ~U32.is_eq, k1, _) == False{}: Bool}
        Key.lt_ne(k1, k2)(hb)
    case Piece.Bind{+k, v} Piece.Sub{h, u, lo, hi}:
      hb => hc => Piece.disjoint.bs(k, lo, hi, key)(hb)(hc)
    case Piece.Sub{h, u, lo, hi} Piece.Bind{+k, v}:
      hb => hc => Piece.disjoint.sb(lo, hi, k, key)(hb)(hc)
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Sub{h2, u2, lo2, hi2}:
      hb => hc => Piece.disjoint.ss(lo1, hi1, lo2, hi2, key)(hb)(hc)

# Piece.below_bind for a subtree, by its upper bound hi
def Piece.below_bind.s(+lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>, +k1: List<&2, U32>, +key: List<&2, U32>) -> {
  Bound.at_least(hi, k1) == True{}: Bool
} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool} -> {Key.is_lt(key, k1) == True{}: Bool}:
  match hi:
    case None{}:
      hb => hc => Empty.absurd({Key.is_lt(key, k1) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+b}:
      hb => hc => Key.lt_le(key, b, k1)(Shared.Bool.and_true_right(Bound.after(lo, key), Key.is_lt(key, b))(hc))(hb)

# a key that a piece before the binding of k1 may hold is before k1
def Piece.below_bind(x: Piece, +k1: List<&2, U32>, -v1: List<&2, U32>, +key: List<&2, U32>) -> {
  Piece.before(x, Piece.Bind{k1, v1}) == True{}: Bool
} -> {Piece.covers(x, key) == True{}: Bool} -> {Key.is_lt(key, k1) == True{}: Bool}:
  match x:
    case Piece.Bind{+k, v}:
      hb => hc =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, key)(hc): {Key.is_lt(_, k1) == True{}: Bool}
        hb
    case Piece.Sub{h, u, lo, hi}:
      hb => hc => Piece.below_bind.s(lo, hi, k1, key)(hb)(hc)

# Piece.above_bind for a subtree, by its lower bound lo
def Piece.above_bind.s(lo: Maybe<&2, List<&2, U32>>, -hi: Maybe<&2, List<&2, U32>>, +k1: List<&2, U32>, +key: List<&2, U32>) -> {
  Bound.at_most(k1, lo) == True{}: Bool
} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool} -> {Key.is_lt(k1, key) == True{}: Bool}:
  match lo:
    case None{}:
      hb => hc => Empty.absurd({Key.is_lt(k1, key) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+a}:
      hb => hc => Key.le_lt(k1, a, key)(hb)(Shared.Bool.and_true_left(Key.is_lt(a, key), Bound.before(key, hi))(hc))

# a key that a piece after the binding of k1 may hold is after k1
def Piece.above_bind(+k1: List<&2, U32>, -v1: List<&2, U32>, y: Piece, +key: List<&2, U32>) -> {
  Piece.before(Piece.Bind{k1, v1}, y) == True{}: Bool
} -> {Piece.covers(y, key) == True{}: Bool} -> {Key.is_lt(k1, key) == True{}: Bool}:
  match y:
    case Piece.Bind{+k, v}:
      hb => hc =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, key)(hc): {Key.is_lt(k1, _) == True{}: Bool}
        hb
    case Piece.Sub{h, u, lo, hi}:
      hb => hc => Piece.above_bind.s(lo, hi, k1, key)(hb)(hc)

# pieces after a piece that may hold k may not hold it
def Pieces.after_all_miss(+x: Piece, ps: List<&2, Piece>, +key: List<&2, U32>) -> {Piece.covers(x, key) == True{}: Bool} -> {
  Pieces.after_all(x, ps) == True{}: Bool
} -> {Pieces.covers(ps, key) == False{}: Bool}:
  match ps:
    case Nil{}:
      hx => ha => {==}
    case Con{+y, +rest}:
      +hx => +ha =>
        %Equal.sym(
          Bool,
          Piece.covers(y, key),
          False{},
          Bool.false_of(
            Piece.covers(y, key),
            cy => Shared.Bool.true_ne_false(
              Equal.trans(
                Bool,
                True{},
                Piece.covers(x, key),
                False{},
                Equal.sym(Bool, Piece.covers(x, key), True{}, hx),
                Piece.disjoint(x, y, key)(Shared.Bool.and_true_left(Piece.before(x, y), Pieces.after_all(x, rest))(ha))(cy)
              )
            )
          )
        ): {Bool.or(_, Pieces.covers(rest, key)) == False{}: Bool}
        Pieces.after_all_miss(x, rest, key)(hx)(Shared.Bool.and_true_right(Piece.before(x, y), Pieces.after_all(x, rest))(ha))

# each piece of xs comes before each piece of ys
def Pieces.before_all(xs: List<&2, Piece>, +ys: List<&2, Piece>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, rest}:
      Bool.and(Pieces.after_all(x, ys), Pieces.before_all(rest, ys))

# pieces after others may not hold a key that the others may hold
def Pieces.before_miss(xs: List<&2, Piece>, +ys: List<&2, Piece>, +key: List<&2, U32>) -> {Pieces.before_all(xs, ys) == True{}: Bool} -> {
  Pieces.covers(xs, key) == True{}: Bool
} -> {Pieces.covers(ys, key) == False{}: Bool}:
  match xs:
    case Nil{}:
      hb => hc => Empty.absurd({Pieces.covers(ys, key) == False{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{+x, +rest}:
      +hb => hc => Bool.cases(
        Piece.covers(x, key),
        {Pieces.covers(ys, key) == False{}: Bool},
        cx => Pieces.after_all_miss(x, ys, key)(cx)(Shared.Bool.and_true_left(Pieces.after_all(x, ys), Pieces.before_all(rest, ys))(hb)),
        cx => Pieces.before_miss(
          rest,
          ys,
          key
        )(Shared.Bool.and_true_right(Pieces.after_all(x, ys), Pieces.before_all(rest, ys))(hb))(
          Equal.trans(
            Bool,
            Pieces.covers(rest, key),
            Bool.or(Piece.covers(x, key), Pieces.covers(rest, key)),
            True{},
            Equal.cong(Bool, Bool, t => Bool.or(t, Pieces.covers(rest, key)), False{}, Piece.covers(x, key), Equal.sym(Bool, Piece.covers(x, key), False{}, cx)),
            hc
          )
        )
      )

# pieces before others may not hold a key that the others may hold
def Pieces.after_miss(+xs: List<&2, Piece>, +ys: List<&2, Piece>, +key: List<&2, U32>) -> {Pieces.before_all(xs, ys) == True{}: Bool} -> {
  Pieces.covers(ys, key) == True{}: Bool
} -> {Pieces.covers(xs, key) == False{}: Bool}:
  +hb => +hc => Bool.false_of(
    Pieces.covers(xs, key),
    cx => Shared.Bool.true_ne_false(
      Equal.trans(Bool, True{}, Pieces.covers(ys, key), False{}, Equal.sym(Bool, Pieces.covers(ys, key), True{}, hc), Pieces.before_miss(xs, ys, key)(hb)(cx))
    )
  )

# each piece after all of a, then all of b, is after all of a
def Pieces.after_all_left(+x: Piece, a: List<&2, Piece>, +b: List<&2, Piece>) -> {
  Pieces.after_all(x, List.append(&2, Piece, a, b)) == True{}: Bool
} -> {Pieces.after_all(x, a) == True{}: Bool}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+y, +rest}:
      +h => Shared.Bool.and_both(
        Piece.before(x, y),
        Pieces.after_all(x, rest)
      )(Shared.Bool.and_true_left(Piece.before(x, y), Pieces.after_all(x, List.append(&2, Piece, rest, b)))(h))(
        Pieces.after_all_left(x, rest, b)(Shared.Bool.and_true_right(Piece.before(x, y), Pieces.after_all(x, List.append(&2, Piece, rest, b)))(h))
      )

# each piece after all of a, then all of b, is after all of b
def Pieces.after_all_right(+x: Piece, a: List<&2, Piece>, +b: List<&2, Piece>) -> {
  Pieces.after_all(x, List.append(&2, Piece, a, b)) == True{}: Bool
} -> {Pieces.after_all(x, b) == True{}: Bool}:
  match a:
    case Nil{}:
      h => h
    case Con{+y, +rest}:
      h => Pieces.after_all_right(x, rest, b)(Shared.Bool.and_true_right(Piece.before(x, y), Pieces.after_all(x, List.append(&2, Piece, rest, b)))(h))

# a sorted run of a, then b: a is sorted
def Pieces.sorted_left(a: List<&2, Piece>, +b: List<&2, Piece>) -> {Pieces.sorted(List.append(&2, Piece, a, b)) == True{}: Bool} -> {
  Pieces.sorted(a) == True{}: Bool
}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+x, +rest}:
      +h => Shared.Bool.and_both(
        Pieces.after_all(x, rest),
        Pieces.sorted(rest)
      )(
        Pieces.after_all_left(
          x,
          rest,
          b
        )(Shared.Bool.and_true_left(Pieces.after_all(x, List.append(&2, Piece, rest, b)), Pieces.sorted(List.append(&2, Piece, rest, b)))(h))
      )(
        Pieces.sorted_left(
          rest,
          b
        )(Shared.Bool.and_true_right(Pieces.after_all(x, List.append(&2, Piece, rest, b)), Pieces.sorted(List.append(&2, Piece, rest, b)))(h))
      )

# a sorted run of a, then b: b is sorted
def Pieces.sorted_right(a: List<&2, Piece>, +b: List<&2, Piece>) -> {Pieces.sorted(List.append(&2, Piece, a, b)) == True{}: Bool} -> {
  Pieces.sorted(b) == True{}: Bool
}:
  match a:
    case Nil{}:
      h => h
    case Con{+x, +rest}:
      h => Pieces.sorted_right(
        rest,
        b
      )(Shared.Bool.and_true_right(Pieces.after_all(x, List.append(&2, Piece, rest, b)), Pieces.sorted(List.append(&2, Piece, rest, b)))(h))

# a sorted run of a, then b: a is before b
def Pieces.sorted_split(a: List<&2, Piece>, +b: List<&2, Piece>) -> {Pieces.sorted(List.append(&2, Piece, a, b)) == True{}: Bool} -> {
  Pieces.before_all(a, b) == True{}: Bool
}:
  match a:
    case Nil{}:
      h => {==}
    case Con{+x, +rest}:
      +h => Shared.Bool.and_both(
        Pieces.after_all(x, b),
        Pieces.before_all(rest, b)
      )(
        Pieces.after_all_right(
          x,
          rest,
          b
        )(Shared.Bool.and_true_left(Pieces.after_all(x, List.append(&2, Piece, rest, b)), Pieces.sorted(List.append(&2, Piece, rest, b)))(h))
      )(
        Pieces.sorted_split(
          rest,
          b
        )(Shared.Bool.and_true_right(Pieces.after_all(x, List.append(&2, Piece, rest, b)), Pieces.sorted(List.append(&2, Piece, rest, b)))(h))
      )

# a key that pieces before the binding of k1 may hold is before k1
def Pieces.below_all(xs: List<&2, Piece>, +k1: List<&2, U32>, +v1: List<&2, U32>, +ys: List<&2, Piece>, +key: List<&2, U32>) -> {
  Pieces.before_all(xs, Piece.Bind{k1, v1} <> ys) == True{}: Bool
} -> {Pieces.covers(xs, key) == True{}: Bool} -> {Key.is_lt(key, k1) == True{}: Bool}:
  match xs:
    case Nil{}:
      hb => hc => Empty.absurd({Key.is_lt(key, k1) == True{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{+x, +rest}:
      +hb => hc => Bool.cases(
        Piece.covers(x, key),
        {Key.is_lt(key, k1) == True{}: Bool},
        cx => Piece.below_bind(
          x,
          k1,
          v1,
          key
        )(
          Shared.Bool.and_true_left(
            Piece.before(x, Piece.Bind{k1, v1}),
            Pieces.after_all(x, ys)
          )(Shared.Bool.and_true_left(Pieces.after_all(x, Piece.Bind{k1, v1} <> ys), Pieces.before_all(rest, Piece.Bind{k1, v1} <> ys))(hb))
        )(cx),
        cx => Pieces.below_all(
          rest,
          k1,
          v1,
          ys,
          key
        )(Shared.Bool.and_true_right(Pieces.after_all(x, Piece.Bind{k1, v1} <> ys), Pieces.before_all(rest, Piece.Bind{k1, v1} <> ys))(hb))(
          Equal.trans(
            Bool,
            Pieces.covers(rest, key),
            Bool.or(Piece.covers(x, key), Pieces.covers(rest, key)),
            True{},
            Equal.cong(Bool, Bool, t => Bool.or(t, Pieces.covers(rest, key)), False{}, Piece.covers(x, key), Equal.sym(Bool, Piece.covers(x, key), False{}, cx)),
            hc
          )
        )
      )

# a key that pieces after the binding of k1 may hold is after k1
def Pieces.above_all(+k1: List<&2, U32>, +v1: List<&2, U32>, ys: List<&2, Piece>, +key: List<&2, U32>) -> {
  Pieces.after_all(Piece.Bind{k1, v1}, ys) == True{}: Bool
} -> {Pieces.covers(ys, key) == True{}: Bool} -> {Key.is_lt(k1, key) == True{}: Bool}:
  match ys:
    case Nil{}:
      hb => hc => Empty.absurd({Key.is_lt(k1, key) == True{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{+y, +rest}:
      +hb => hc => Bool.cases(
        Piece.covers(y, key),
        {Key.is_lt(k1, key) == True{}: Bool},
        cy => Piece.above_bind(k1, v1, y, key)(Shared.Bool.and_true_left(Piece.before(Piece.Bind{k1, v1}, y), Pieces.after_all(Piece.Bind{k1, v1}, rest))(hb))(cy),
        cy => Pieces.above_all(
          k1,
          v1,
          rest,
          key
        )(Shared.Bool.and_true_right(Piece.before(Piece.Bind{k1, v1}, y), Pieces.after_all(Piece.Bind{k1, v1}, rest))(hb))(
          Equal.trans(
            Bool,
            Pieces.covers(rest, key),
            Bool.or(Piece.covers(y, key), Pieces.covers(rest, key)),
            True{},
            Equal.cong(Bool, Bool, t => Bool.or(t, Pieces.covers(rest, key)), False{}, Piece.covers(y, key), Equal.sym(Bool, Piece.covers(y, key), False{}, cy)),
            hc
          )
        )
      )

# the lower bound lo is not after the lower bound lo2
def Bound.lo_le(lo: Maybe<&2, List<&2, U32>>, lo2: Maybe<&2, List<&2, U32>>) -> Bool:
  match lo lo2:
    case None{} y:
      True{}
    case Some{a} None{}:
      False{}
    case Some{a} Some{c}:
      Key.le(a, c)

# the upper bound hi2 is not after the upper bound hi
def Bound.hi_le(hi2: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match hi2 hi:
    case x None{}:
      True{}
    case None{} Some{b}:
      False{}
    case Some{c} Some{b}:
      Key.le(c, b)

# the piece x lies between lo and hi
def Piece.inside(x: Piece, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match x:
    case Piece.Bind{+k, v}:
      Bool.and(Bound.after(lo, k), Bound.before(k, hi))
    case Piece.Sub{h, u, lo2, hi2}:
      Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi))

# the pieces ps lie between lo and hi
def Pieces.inside(ps: List<&2, Piece>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{x, rest}:
      Bool.and(Piece.inside(x, lo, hi), Pieces.inside(rest, lo, hi))

# a lower bound is not after itself
def Bound.lo_le_refl(lo: Maybe<&2, List<&2, U32>>) -> {Bound.lo_le(lo, lo) == True{}: Bool}:
  match lo:
    case None{}:
      {==}
    case Some{+a}:
      Key.le_refl(a)

# Piece.refine_left for two bindings, by the upper bound hi
def Piece.refine_left.bb(+kw: List<&2, U32>, +k: List<&2, U32>, +lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>) -> {
  Bool.and(Bound.after(lo, kw), Bound.before(kw, hi)) == True{}: Bool
} -> {Bound.at_least(hi, k) == True{}: Bool} -> {Key.is_lt(kw, k) == True{}: Bool}:
  match hi:
    case None{}:
      hin => hb => Empty.absurd({Key.is_lt(kw, k) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+b}:
      hin => hb => Key.lt_le(kw, b, k)(Shared.Bool.and_true_right(Bound.after(lo, kw), Key.is_lt(kw, b))(hin))(hb)

# Piece.refine_left for a binding before a subtree, by the bounds
def Piece.refine_left.bs(+kw: List<&2, U32>, +lo: Maybe<&2, List<&2, U32>>, hi: Maybe<&2, List<&2, U32>>, lo3: Maybe<&2, List<&2, U32>>) -> {
  Bool.and(Bound.after(lo, kw), Bound.before(kw, hi)) == True{}: Bool
} -> {Bound.ends_before(hi, lo3) == True{}: Bool} -> {Bound.at_most(kw, lo3) == True{}: Bool}:
  match hi lo3:
    case Some{+b} Some{+a}:
      hin => hb => Key.lt_le_of(kw, a)(Key.lt_le(kw, b, a)(Shared.Bool.and_true_right(Bound.after(lo, kw), Key.is_lt(kw, b))(hin))(hb))
    case None{} z:
      hin => hb => Empty.absurd({Bound.at_most(kw, z) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{b} None{}:
      hin => hb => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hb))

# Piece.refine_left for a subtree before a binding, by the bounds
def Piece.refine_left.sb(
  +lo: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  hi2: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> {Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi)) == True{}: Bool} -> {Bound.at_least(hi, k) == True{}: Bool} -> {
  Bound.at_least(hi2, k) == True{}: Bool
}:
  match hi2 hi:
    case Some{+c} Some{+b}:
      hin => hb => Key.le_trans(c, b, k)(Shared.Bool.and_true_right(Bound.lo_le(lo, lo2), Key.le(c, b))(hin))(hb)
    case x None{}:
      hin => hb => Empty.absurd({Bound.at_least(x, k) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case None{} Some{b}:
      hin => hb => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Bound.lo_le(lo, lo2), False{})(hin)))

# Piece.refine_left for two subtrees, by the bounds
def Piece.refine_left.ss(
  +lo: Maybe<&2, List<&2, U32>>,
  +lo2: Maybe<&2, List<&2, U32>>,
  hi2: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>,
  lo3: Maybe<&2, List<&2, U32>>
) -> {Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi)) == True{}: Bool} -> {Bound.ends_before(hi, lo3) == True{}: Bool} -> {
  Bound.ends_before(hi2, lo3) == True{}: Bool
}:
  match hi2 hi lo3:
    case Some{+c} Some{+b} Some{+a}:
      hin => hb => Key.le_trans(c, b, a)(Shared.Bool.and_true_right(Bound.lo_le(lo, lo2), Key.le(c, b))(hin))(hb)
    case x None{} z:
      hin => hb => Empty.absurd({Bound.ends_before(x, z) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case x Some{b} None{}:
      hin => hb => Empty.absurd({Bound.ends_before(x, None{}) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case None{} Some{b} Some{a}:
      hin => hb => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Bound.lo_le(lo, lo2), False{})(hin)))

# a piece between lo and hi comes before what the subtree of lo and hi comes
# before
def Piece.refine_left(w: Piece, y: Piece, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, -h: Hashes.Hash, -u: Nat) -> {
  Piece.inside(w, lo, hi) == True{}: Bool
} -> {Piece.before(Piece.Sub{h, u, lo, hi}, y) == True{}: Bool} -> {Piece.before(w, y) == True{}: Bool}:
  match w y:
    case Piece.Bind{+kw, vw} Piece.Bind{+k, v}:
      Piece.refine_left.bb(kw, k, lo, hi)
    case Piece.Bind{+kw, vw} Piece.Sub{h3, u3, lo3, hi3}:
      Piece.refine_left.bs(kw, lo, hi, lo3)
    case Piece.Sub{h2, u2, lo2, hi2} Piece.Bind{+k, v}:
      Piece.refine_left.sb(lo, lo2, hi2, hi, k)
    case Piece.Sub{h2, u2, lo2, hi2} Piece.Sub{h3, u3, lo3, hi3}:
      Piece.refine_left.ss(lo, lo2, hi2, hi, lo3)

# Piece.refine_right for a binding before a subtree, by the bounds
def Piece.refine_right.bb(+kw: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>, -hi: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> {
  Bound.at_most(kw, lo) == True{}: Bool
} -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {Key.is_lt(kw, k) == True{}: Bool}:
  match lo:
    case None{}:
      hb => hin => Empty.absurd({Key.is_lt(kw, k) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{+a}:
      hb => hin => Key.le_lt(kw, a, k)(hb)(Shared.Bool.and_true_left(Key.is_lt(a, k), Bound.before(k, hi))(hin))

# Piece.refine_right for a binding before a subtree, then a subtree in it
def Piece.refine_right.bs(+kw: List<&2, U32>, lo: Maybe<&2, List<&2, U32>>, -hi: Maybe<&2, List<&2, U32>>, lo2: Maybe<&2, List<&2, U32>>, -hi2: Maybe<&2, List<&2, U32>>) -> {
  Bound.at_most(kw, lo) == True{}: Bool
} -> {Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi)) == True{}: Bool} -> {Bound.at_most(kw, lo2) == True{}: Bool}:
  match lo lo2:
    case Some{+a} Some{+c}:
      hb => hin => Key.le_trans(kw, a, c)(hb)(Shared.Bool.and_true_left(Key.le(a, c), Bound.hi_le(hi2, hi))(hin))
    case None{} z:
      hb => hin => Empty.absurd({Bound.at_most(kw, z) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{a} None{}:
      hb => hin => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_left(False{}, Bound.hi_le(hi2, hi))(hin)))

# Piece.refine_right for a subtree before a subtree, then a binding in it
def Piece.refine_right.sb(hi1: Maybe<&2, List<&2, U32>>, lo: Maybe<&2, List<&2, U32>>, -hi: Maybe<&2, List<&2, U32>>, +k: List<&2, U32>) -> {
  Bound.ends_before(hi1, lo) == True{}: Bool
} -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {Bound.at_least(hi1, k) == True{}: Bool}:
  match hi1 lo:
    case Some{+b} Some{+a}:
      hb => hin => Key.lt_le_of(b, k)(Key.le_lt(b, a, k)(hb)(Shared.Bool.and_true_left(Key.is_lt(a, k), Bound.before(k, hi))(hin)))
    case None{} z:
      hb => hin => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{b} None{}:
      hb => hin => Empty.absurd({Key.le(b, k) == True{}: Bool}, Shared.Bool.false_ne_true(hb))

# Piece.refine_right for a subtree before a subtree, then a subtree in it
def Piece.refine_right.ss(
  hi1: Maybe<&2, List<&2, U32>>,
  lo: Maybe<&2, List<&2, U32>>,
  -hi: Maybe<&2, List<&2, U32>>,
  lo2: Maybe<&2, List<&2, U32>>,
  -hi2: Maybe<&2, List<&2, U32>>
) -> {Bound.ends_before(hi1, lo) == True{}: Bool} -> {Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi)) == True{}: Bool} -> {
  Bound.ends_before(hi1, lo2) == True{}: Bool
}:
  match hi1 lo lo2:
    case Some{+b} Some{+a} Some{+c}:
      hb => hin => Key.le_trans(b, a, c)(hb)(Shared.Bool.and_true_left(Key.le(a, c), Bound.hi_le(hi2, hi))(hin))
    case None{} y z:
      hb => hin => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{b} None{} z:
      hb => hin => Empty.absurd({Bound.ends_before(Some{b}, z) == True{}: Bool}, Shared.Bool.false_ne_true(hb))
    case Some{b} Some{a} None{}:
      hb => hin => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_left(False{}, Bound.hi_le(hi2, hi))(hin)))

# a piece before the subtree of lo and hi comes before each piece between lo
# and hi
def Piece.refine_right(w: Piece, z: Piece, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, -h: Hashes.Hash, -u: Nat) -> {
  Piece.before(w, Piece.Sub{h, u, lo, hi}) == True{}: Bool
} -> {Piece.inside(z, lo, hi) == True{}: Bool} -> {Piece.before(w, z) == True{}: Bool}:
  match w z:
    case Piece.Bind{+kw, vw} Piece.Bind{+k, v}:
      Piece.refine_right.bb(kw, lo, hi, k)
    case Piece.Bind{+kw, vw} Piece.Sub{h2, u2, lo2, hi2}:
      Piece.refine_right.bs(kw, lo, hi, lo2, hi2)
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Bind{+k, v}:
      Piece.refine_right.sb(hi1, lo, hi, k)
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Sub{h2, u2, lo2, hi2}:
      Piece.refine_right.ss(hi1, lo, hi, lo2, hi2)

# pieces after x, then others after x, are all after x
def Pieces.after_all_append(+x: Piece, a: List<&2, Piece>, +b: List<&2, Piece>) -> {Pieces.after_all(x, a) == True{}: Bool} -> {
  Pieces.after_all(x, b) == True{}: Bool
} -> {Pieces.after_all(x, List.append(&2, Piece, a, b)) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hb => hb
    case Con{+y, +rest}:
      +ha => hb => Shared.Bool.and_both(
        Piece.before(x, y),
        Pieces.after_all(x, List.append(&2, Piece, rest, b))
      )(Shared.Bool.and_true_left(Piece.before(x, y), Pieces.after_all(x, rest))(ha))(
        Pieces.after_all_append(x, rest, b)(Shared.Bool.and_true_right(Piece.before(x, y), Pieces.after_all(x, rest))(ha))(hb)
      )

# sorted pieces, then sorted pieces after them, are sorted
def Pieces.sorted_append(a: List<&2, Piece>, +b: List<&2, Piece>) -> {Pieces.sorted(a) == True{}: Bool} -> {Pieces.sorted(b) == True{}: Bool} -> {
  Pieces.before_all(a, b) == True{}: Bool
} -> {Pieces.sorted(List.append(&2, Piece, a, b)) == True{}: Bool}:
  match a:
    case Nil{}:
      ha => hb => hab => hb
    case Con{+x, +rest}:
      +ha => hb => +hab => Shared.Bool.and_both(
        Pieces.after_all(x, List.append(&2, Piece, rest, b)),
        Pieces.sorted(List.append(&2, Piece, rest, b))
      )(
        Pieces.after_all_append(
          x,
          rest,
          b
        )(Shared.Bool.and_true_left(Pieces.after_all(x, rest), Pieces.sorted(rest))(ha))(
          Shared.Bool.and_true_left(Pieces.after_all(x, b), Pieces.before_all(rest, b))(hab)
        )
      )(
        Pieces.sorted_append(
          rest,
          b
        )(Shared.Bool.and_true_right(Pieces.after_all(x, rest), Pieces.sorted(rest))(ha))(hb)(
          Shared.Bool.and_true_right(Pieces.after_all(x, b), Pieces.before_all(rest, b))(hab)
        )
      )

# a piece between lo and hi comes before what the subtree of lo and hi
# comes before
def Pieces.refine_left_list(+w: Piece, ys: List<&2, Piece>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, +h: Hashes.Hash, +u: Nat) -> {
  Piece.inside(w, lo, hi) == True{}: Bool
} -> {Pieces.after_all(Piece.Sub{h, u, lo, hi}, ys) == True{}: Bool} -> {Pieces.after_all(w, ys) == True{}: Bool}:
  match ys:
    case Nil{}:
      hi2 => ha => {==}
    case Con{+y, +rest}:
      +hi2 => +ha => Shared.Bool.and_both(
        Piece.before(w, y),
        Pieces.after_all(w, rest)
      )(
        Piece.refine_left(
          w,
          y,
          lo,
          hi,
          h,
          u
        )(hi2)(Shared.Bool.and_true_left(Piece.before(Piece.Sub{h, u, lo, hi}, y), Pieces.after_all(Piece.Sub{h, u, lo, hi}, rest))(ha))
      )(
        Pieces.refine_left_list(
          w,
          rest,
          lo,
          hi,
          h,
          u
        )(hi2)(Shared.Bool.and_true_right(Piece.before(Piece.Sub{h, u, lo, hi}, y), Pieces.after_all(Piece.Sub{h, u, lo, hi}, rest))(ha))
      )

# pieces between lo and hi come before what the subtree of lo and hi comes
# before
def Pieces.refine_left_all(ws: List<&2, Piece>, +ys: List<&2, Piece>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, +h: Hashes.Hash, +u: Nat) -> {
  Pieces.inside(ws, lo, hi) == True{}: Bool
} -> {Pieces.after_all(Piece.Sub{h, u, lo, hi}, ys) == True{}: Bool} -> {Pieces.before_all(ws, ys) == True{}: Bool}:
  match ws:
    case Nil{}:
      hi2 => ha => {==}
    case Con{+w, +rest}:
      +hi2 => +ha => Shared.Bool.and_both(
        Pieces.after_all(w, ys),
        Pieces.before_all(rest, ys)
      )(Pieces.refine_left_list(w, ys, lo, hi, h, u)(Shared.Bool.and_true_left(Piece.inside(w, lo, hi), Pieces.inside(rest, lo, hi))(hi2))(ha))(
        Pieces.refine_left_all(rest, ys, lo, hi, h, u)(Shared.Bool.and_true_right(Piece.inside(w, lo, hi), Pieces.inside(rest, lo, hi))(hi2))(ha)
      )

# a piece before the subtree of lo and hi comes before each piece between
# lo and hi
def Pieces.refine_right_all(+w: Piece, zs: List<&2, Piece>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, +h: Hashes.Hash, +u: Nat) -> {
  Piece.before(w, Piece.Sub{h, u, lo, hi}) == True{}: Bool
} -> {Pieces.inside(zs, lo, hi) == True{}: Bool} -> {Pieces.after_all(w, zs) == True{}: Bool}:
  match zs:
    case Nil{}:
      hb => hi2 => {==}
    case Con{+z, +rest}:
      +hb => +hi2 => Shared.Bool.and_both(
        Piece.before(w, z),
        Pieces.after_all(w, rest)
      )(Piece.refine_right(w, z, lo, hi, h, u)(hb)(Shared.Bool.and_true_left(Piece.inside(z, lo, hi), Pieces.inside(rest, lo, hi))(hi2)))(
        Pieces.refine_right_all(w, rest, lo, hi, h, u)(hb)(Shared.Bool.and_true_right(Piece.inside(z, lo, hi), Pieces.inside(rest, lo, hi))(hi2))
      )

# Piece.inside_covers for a subtree, by the bounds
def Piece.inside_covers.s(
  lo: Maybe<&2, List<&2, U32>>,
  lo2: Maybe<&2, List<&2, U32>>,
  hi2: Maybe<&2, List<&2, U32>>,
  hi: Maybe<&2, List<&2, U32>>,
  +key: List<&2, U32>
) -> {Bool.and(Bound.lo_le(lo, lo2), Bound.hi_le(hi2, hi)) == True{}: Bool} -> {Bool.and(Bound.after(lo2, key), Bound.before(key, hi2)) == True{}: Bool} -> {
  Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool
}:
  match lo lo2 hi2 hi:
    case None{} x y None{}:
      hin => hc => {==}
    case None{} x Some{+c} Some{+b}:
      hin => hc => Key.lt_le(key, c, b)(Shared.Bool.and_true_right(Bound.after(x, key), Key.is_lt(key, c))(hc))(Shared.Bool.and_true_right(True{}, Key.le(c, b))(hin))
    case Some{+a} Some{+d} y None{}:
      hin => hc => Shared.Bool.and_both(Key.is_lt(a, key), True{})(
        Key.le_lt(a, d, key)(Shared.Bool.and_true_left(Key.le(a, d), True{})(hin))(Shared.Bool.and_true_left(Key.is_lt(d, key), Bound.before(key, y))(hc))
      )({==})
    case Some{+a} Some{+d} Some{+c} Some{+b}:
      +hin => +hc => Shared.Bool.and_both(
        Key.is_lt(a, key),
        Key.is_lt(key, b)
      )(Key.le_lt(a, d, key)(Shared.Bool.and_true_left(Key.le(a, d), Key.le(c, b))(hin))(Shared.Bool.and_true_left(Key.is_lt(d, key), Key.is_lt(key, c))(hc)))(
        Key.lt_le(key, c, b)(Shared.Bool.and_true_right(Key.is_lt(d, key), Key.is_lt(key, c))(hc))(Shared.Bool.and_true_right(Key.le(a, d), Key.le(c, b))(hin))
      )
    case x y None{} Some{b}:
      hin => hc => Empty.absurd(
        {Bool.and(Bound.after(x, key), Key.is_lt(key, b)) == True{}: Bool},
        Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Bound.lo_le(x, y), False{})(hin))
      )
    case Some{a} None{} y z:
      hin => hc => Empty.absurd(
        {Bool.and(Key.is_lt(a, key), Bound.before(key, z)) == True{}: Bool},
        Shared.Bool.false_ne_true(Shared.Bool.and_true_left(False{}, Bound.hi_le(y, z))(hin))
      )

# a key that a piece between lo and hi may hold is between lo and hi
def Piece.inside_covers(x: Piece, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>) -> {
  Piece.inside(x, lo, hi) == True{}: Bool
} -> {Piece.covers(x, key) == True{}: Bool} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool}:
  match x:
    case Piece.Bind{+k, v}:
      hin => hc =>
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, key)(hc): {Bool.and(Bound.after(lo, _), Bound.before(_, hi)) == True{}: Bool}
        hin
    case Piece.Sub{h, u, lo2, hi2}:
      hin => hc => Piece.inside_covers.s(lo, lo2, hi2, hi, key)(hin)(hc)

# a key that pieces between lo and hi may hold is between lo and hi
def Pieces.inside_covers(ps: List<&2, Piece>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>, +key: List<&2, U32>) -> {
  Pieces.inside(ps, lo, hi) == True{}: Bool
} -> {Pieces.covers(ps, key) == True{}: Bool} -> {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool}:
  match ps:
    case Nil{}:
      hin => hc => Empty.absurd({Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool}, Shared.Bool.false_ne_true(hc))
    case Con{+x, +rest}:
      +hin => hc => Bool.cases(
        Piece.covers(x, key),
        {Bool.and(Bound.after(lo, key), Bound.before(key, hi)) == True{}: Bool},
        cx => Piece.inside_covers(x, lo, hi, key)(Shared.Bool.and_true_left(Piece.inside(x, lo, hi), Pieces.inside(rest, lo, hi))(hin))(cx),
        cx => Pieces.inside_covers(
          rest,
          lo,
          hi,
          key
        )(Shared.Bool.and_true_right(Piece.inside(x, lo, hi), Pieces.inside(rest, lo, hi))(hin))(
          Equal.trans(
            Bool,
            Pieces.covers(rest, key),
            Bool.or(Piece.covers(x, key), Pieces.covers(rest, key)),
            True{},
            Equal.cong(Bool, Bool, t => Bool.or(t, Pieces.covers(rest, key)), False{}, Piece.covers(x, key), Equal.sym(Bool, Piece.covers(x, key), False{}, cx)),
            hc
          )
        )
      )

# an upper bound is not after itself
def Bound.hi_le_refl(hi: Maybe<&2, List<&2, U32>>) -> {Bound.hi_le(hi, hi) == True{}: Bool}:
  match hi:
    case None{}:
      {==}
    case Some{+b}:
      Key.le_refl(b)

# a key before hi, as an upper bound, is not after hi
def Bound.hi_le_of(+ik: List<&2, U32>, hi: Maybe<&2, List<&2, U32>>) -> {Bound.before(ik, hi) == True{}: Bool} -> {Bound.hi_le(Some{ik}, hi) == True{}: Bool}:
  match hi:
    case None{}:
      h => {==}
    case Some{+b}:
      h => Key.lt_le_of(ik, b)(h)

# a lower bound after ik is after any bound before ik
def Bound.lo_le_widen(lo: Maybe<&2, List<&2, U32>>, +ik: List<&2, U32>, lo2: Maybe<&2, List<&2, U32>>) -> {
  Bound.lo_le(Some{ik}, lo2) == True{}: Bool
} -> {Bound.after(lo, ik) == True{}: Bool} -> {Bound.lo_le(lo, lo2) == True{}: Bool}:
  match lo lo2:
    case None{} y:
      h => g => {==}
    case Some{a} None{}:
      h => g => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Some{+a} Some{+c}:
      h => g => Key.lt_le_of(a, c)(Key.lt_le(a, ik, c)(g)(h))

# a piece after ik and before hi lies between any bound before ik and hi
def Piece.inside_widen(x: Piece, +ik: List<&2, U32>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Piece.inside(x, Some{ik}, hi) == True{}: Bool
} -> {Bound.after(lo, ik) == True{}: Bool} -> {Piece.inside(x, lo, hi) == True{}: Bool}:
  match x:
    case Piece.Bind{+k, v}:
      +h => g => Shared.Bool.and_both(
        Bound.after(lo, k),
        Bound.before(k, hi)
      )(Bound.after_trans(lo, ik, k)(g)(Shared.Bool.and_true_left(Key.is_lt(ik, k), Bound.before(k, hi))(h)))(
        Shared.Bool.and_true_right(Key.is_lt(ik, k), Bound.before(k, hi))(h)
      )
    case Piece.Sub{h2, u, +lo2, +hi2}:
      +h => g => Shared.Bool.and_both(
        Bound.lo_le(lo, lo2),
        Bound.hi_le(hi2, hi)
      )(Bound.lo_le_widen(lo, ik, lo2)(Shared.Bool.and_true_left(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi))(h))(g))(
        Shared.Bool.and_true_right(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi))(h)
      )

# pieces after ik and before hi lie between any bound before ik and hi
def Pieces.inside_widen(ps: List<&2, Piece>, +ik: List<&2, U32>, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Pieces.inside(ps, Some{ik}, hi) == True{}: Bool
} -> {Bound.after(lo, ik) == True{}: Bool} -> {Pieces.inside(ps, lo, hi) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => g => {==}
    case Con{+x, +rest}:
      +h => +g => Shared.Bool.and_both(
        Piece.inside(x, lo, hi),
        Pieces.inside(rest, lo, hi)
      )(Piece.inside_widen(x, ik, lo, hi)(Shared.Bool.and_true_left(Piece.inside(x, Some{ik}, hi), Pieces.inside(rest, Some{ik}, hi))(h))(g))(
        Pieces.inside_widen(rest, ik, lo, hi)(Shared.Bool.and_true_right(Piece.inside(x, Some{ik}, hi), Pieces.inside(rest, Some{ik}, hi))(h))(g)
      )

# a lower bound after ik is what the binding of ik ends before
def Bound.at_most_of(+ik: List<&2, U32>, lo2: Maybe<&2, List<&2, U32>>) -> {Bound.lo_le(Some{ik}, lo2) == True{}: Bool} -> {
  Bound.at_most(ik, lo2) == True{}: Bool
}:
  match lo2:
    case None{}:
      h => h
    case Some{c}:
      h => h

# a lower bound after ik is what a subtree that ends at ik ends before
def Bound.ends_before_of(+ik: List<&2, U32>, lo2: Maybe<&2, List<&2, U32>>) -> {Bound.lo_le(Some{ik}, lo2) == True{}: Bool} -> {
  Bound.ends_before(Some{ik}, lo2) == True{}: Bool
}:
  match lo2:
    case None{}:
      h => h
    case Some{c}:
      h => h

# pieces after ik come after the binding of ik
def Pieces.after_inside_bind(+ik: List<&2, U32>, +iv: List<&2, U32>, ys: List<&2, Piece>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Pieces.inside(ys, Some{ik}, hi) == True{}: Bool
} -> {Pieces.after_all(Piece.Bind{ik, iv}, ys) == True{}: Bool}:
  match ys:
    case Nil{}:
      h => {==}
    case Con{Piece.Bind{+k, +v}, +rest}:
      +h => Shared.Bool.and_both(
        Key.is_lt(ik, k),
        Pieces.after_all(Piece.Bind{ik, iv}, rest)
      )(Shared.Bool.and_true_left(Key.is_lt(ik, k), Bound.before(k, hi))(Shared.Bool.and_true_left(Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)), Pieces.inside(rest, Some{ik}, hi))(h)))(
        Pieces.after_inside_bind(ik, iv, rest, hi)(Shared.Bool.and_true_right(Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)), Pieces.inside(rest, Some{ik}, hi))(h))
      )
    case Con{Piece.Sub{+h2, +u, +lo2, +hi2}, +rest}:
      +h => Shared.Bool.and_both(
        Bound.at_most(ik, lo2),
        Pieces.after_all(Piece.Bind{ik, iv}, rest)
      )(
        Bound.at_most_of(
          ik,
          lo2
        )(
          Shared.Bool.and_true_left(
            Bound.lo_le(Some{ik}, lo2),
            Bound.hi_le(hi2, hi)
          )(Shared.Bool.and_true_left(Bool.and(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi)), Pieces.inside(rest, Some{ik}, hi))(h))
        )
      )(
        Pieces.after_inside_bind(
          ik,
          iv,
          rest,
          hi
        )(Shared.Bool.and_true_right(Bool.and(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi)), Pieces.inside(rest, Some{ik}, hi))(h))
      )

# pieces after ik come after a subtree that ends at ik
def Pieces.after_inside_sub(
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +ik: List<&2, U32>,
  ys: List<&2, Piece>,
  +hi: Maybe<&2, List<&2, U32>>
) -> {Pieces.inside(ys, Some{ik}, hi) == True{}: Bool} -> {Pieces.after_all(Piece.Sub{h, u, lo, Some{ik}}, ys) == True{}: Bool}:
  match ys:
    case Nil{}:
      g => {==}
    case Con{Piece.Bind{+k, +v}, +rest}:
      +g => Shared.Bool.and_both(
        Key.le(ik, k),
        Pieces.after_all(Piece.Sub{h, u, lo, Some{ik}}, rest)
      )(
        Key.lt_le_of(
          ik,
          k
        )(Shared.Bool.and_true_left(Key.is_lt(ik, k), Bound.before(k, hi))(Shared.Bool.and_true_left(Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)), Pieces.inside(rest, Some{ik}, hi))(g)))
      )(
        Pieces.after_inside_sub(
          h,
          u,
          lo,
          ik,
          rest,
          hi
        )(Shared.Bool.and_true_right(Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)), Pieces.inside(rest, Some{ik}, hi))(g))
      )
    case Con{Piece.Sub{+h2, +u2, +lo2, +hi2}, +rest}:
      +g => Shared.Bool.and_both(
        Bound.ends_before(Some{ik}, lo2),
        Pieces.after_all(Piece.Sub{h, u, lo, Some{ik}}, rest)
      )(
        Bound.ends_before_of(
          ik,
          lo2
        )(
          Shared.Bool.and_true_left(
            Bound.lo_le(Some{ik}, lo2),
            Bound.hi_le(hi2, hi)
          )(Shared.Bool.and_true_left(Bool.and(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi)), Pieces.inside(rest, Some{ik}, hi))(g))
        )
      )(
        Pieces.after_inside_sub(
          h,
          u,
          lo,
          ik,
          rest,
          hi
        )(Shared.Bool.and_true_right(Bool.and(Bound.lo_le(Some{ik}, lo2), Bound.hi_le(hi2, hi)), Pieces.inside(rest, Some{ik}, hi))(g))
      )

# Mst.pieces_sorted at the subtree prev before the item of the key ik
def Mst.pieces_sorted.con(
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +ks2: List<&2, Piece>,
  hs: {Pieces.sorted(Piece.Bind{ik, iv} <> ks2) == True{}: Bool},
  hin: {Pieces.inside(Piece.Bind{ik, iv} <> ks2, lo, hi) == True{}: Bool},
  ins2: {Pieces.inside(ks2, Some{ik}, hi) == True{}: Bool},
  bh: {Bound.before(ik, hi) == True{}: Bool}
) -> {
  Bool.and(
    Pieces.sorted(Piece.sub(m, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2)),
    Pieces.inside(Piece.sub(m, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), lo, hi)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      Shared.Bool.and_both(Pieces.sorted(Piece.Bind{ik, iv} <> ks2), Pieces.inside(Piece.Bind{ik, iv} <> ks2, lo, hi))(hs)(hin)
    case Some{+h}:
      Shared.Bool.and_both(
        Pieces.sorted(Piece.Sub{h, l, lo, Some{ik}} <> (Piece.Bind{ik, iv} <> ks2)),
        Pieces.inside(Piece.Sub{h, l, lo, Some{ik}} <> (Piece.Bind{ik, iv} <> ks2), lo, hi)
      )(
        Shared.Bool.and_both(
          Pieces.after_all(Piece.Sub{h, l, lo, Some{ik}}, Piece.Bind{ik, iv} <> ks2),
          Pieces.sorted(Piece.Bind{ik, iv} <> ks2)
        )(Shared.Bool.and_both(Key.le(ik, ik), Pieces.after_all(Piece.Sub{h, l, lo, Some{ik}}, ks2))(Key.le_refl(ik))(Pieces.after_inside_sub(h, l, lo, ik, ks2, hi)(ins2)))(
          hs
        )
      )(
        Shared.Bool.and_both(
          Piece.inside(Piece.Sub{h, l, lo, Some{ik}}, lo, hi),
          Pieces.inside(Piece.Bind{ik, iv} <> ks2, lo, hi)
        )(Shared.Bool.and_both(Bound.lo_le(lo, lo), Bound.hi_le(Some{ik}, hi))(Bound.lo_le_refl(lo))(Bound.hi_le_of(ik, hi)(bh)))(hin)
      )

# Mst.pieces_sorted with no item: at most the subtree before
def Mst.pieces_sorted.nil(m: Maybe<&2, Hashes.Hash>, +l: Nat, +lo: Maybe<&2, List<&2, U32>>, +hi: Maybe<&2, List<&2, U32>>) -> {
  Bool.and(Pieces.sorted(Piece.sub(m, l, lo, hi, [])), Pieces.inside(Piece.sub(m, l, lo, hi, []), lo, hi)) == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Shared.Bool.and_both(
        Pieces.sorted([Piece.Sub{h, l, lo, hi}]),
        Pieces.inside([Piece.Sub{h, l, lo, hi}], lo, hi)
      )({==})(
        Shared.Bool.and_both(Piece.inside(Piece.Sub{h, l, lo, hi}, lo, hi), True{})(
          Shared.Bool.and_both(Bound.lo_le(lo, lo), Bound.hi_le(hi, hi))(Bound.lo_le_refl(lo))(Bound.hi_le_refl(hi))
        )({==})
      )

# the pieces of a node's items are sorted and lie in its bounds
def Mst.pieces_sorted(
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Bool.and(Pieces.sorted(ks), Pieces.inside(ks, lo, hi)) == True{}: Bool
}:
  match xs:
    case Nil{}:
      ep =>
        %Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep): {
          Bool.and(Pieces.sorted(_), Pieces.inside(_, lo, hi)) == True{}: Bool
        }
        Mst.pieces_sorted.nil(prev, l, lo, hi)
    case Con{Item{+ik, +iv, +r}, +rest}:
      ep => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {Bool.and(Pieces.sorted(ks), Pieces.inside(ks, lo, hi)) == True{}: Bool},
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {Bool.and(Pieces.sorted(ks), Pieces.inside(ks, lo, hi)) == True{}: Bool},
          +ks2 => e3 => e4 =>
            +ih = Mst.pieces_sorted(rest, l, r, Some{ik}, hi, ks2)(e3)
            +ins2 = Shared.Bool.and_true_right(Pieces.sorted(ks2), Pieces.inside(ks2, Some{ik}, hi))(ih)
            +cb = Shared.Bool.and_true_right(
              Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
              Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
            )(c)
            %e4: {Bool.and(Pieces.sorted(_), Pieces.inside(_, lo, hi)) == True{}: Bool}
            Mst.pieces_sorted.con(
              prev,
              l,
              lo,
              hi,
              ik,
              iv,
              ks2,
              Shared.Bool.and_both(
                Pieces.after_all(Piece.Bind{ik, iv}, ks2),
                Pieces.sorted(ks2)
              )(Pieces.after_inside_bind(ik, iv, ks2, hi)(ins2))(Shared.Bool.and_true_left(Pieces.sorted(ks2), Pieces.inside(ks2, Some{ik}, hi))(ih)),
              Shared.Bool.and_both(
                Bool.and(Bound.after(lo, ik), Bound.before(ik, hi)),
                Pieces.inside(ks2, lo, hi)
              )(cb)(Pieces.inside_widen(ks2, ik, lo, hi)(ins2)(Shared.Bool.and_true_left(Bound.after(lo, ik), Bound.before(ik, hi))(cb))),
              ins2,
              Shared.Bool.and_true_right(Bound.after(lo, ik), Bound.before(ik, hi))(cb)
            )
        )(e2)
      )(ep)

# pieces, then others, may hold k when either may
def Pieces.covers_append(a: List<&2, Piece>, +b: List<&2, Piece>, +k: List<&2, U32>) -> {
  Pieces.covers(List.append(&2, Piece, a, b), k) == Bool.or(Pieces.covers(a, k), Pieces.covers(b, k)): Bool
}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(
        Bool,
        Pieces.covers(List.append(&2, Piece, rest, b), k),
        Bool.or(Pieces.covers(rest, k), Pieces.covers(b, k)),
        Pieces.covers_append(rest, b, k)
      ): {Bool.or(Piece.covers(x, k), _) == Bool.or(Bool.or(Piece.covers(x, k), Pieces.covers(rest, k)), Pieces.covers(b, k)): Bool}
      Shared.Bool.or_assoc(Piece.covers(x, k), Pieces.covers(rest, k), Pieces.covers(b, k))

# the value from the subtree m, between lo and hi, before the pieces rest,
# when its bounds hold k and rest give none: a read of m
def Mst.value_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, rest, k) == None{}: Maybe<&2, List<&2, U32>>
} -> {
  Pieces.value(~S, ~fetch, f, s, Piece.sub(m, l, lo, hi, rest), k) == Look.value(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, m, k)): Maybe<&2, List<&2, U32>>
}:
  match m:
    case None{}:
      hin => hr =>
        %Equal.sym(Look, Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, None{}, k), Look.Absent{}, Mst.look_none(~S, ~fetch, f, s, Room{l, lo, hi}, k)): {
          Pieces.value(~S, ~fetch, f, s, rest, k) == Look.value(_): Maybe<&2, List<&2, U32>>
        }
        hr
    case Some{+h}:
      hin => hr =>
        %Equal.sym(Bool, Bool.and(Bound.after(lo, k), Bound.before(k, hi)), True{}, hin): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Piece.value(~S, ~fetch, f, s, Piece.Sub{h, l, lo, hi}, k),
            u => Pieces.value(~S, ~fetch, f, s, rest, k)
          )
            == Look.value(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, Some{h}, k)): Maybe<&2, List<&2, U32>>
        }
        {==}

# the value from the subtree m, whose bounds lo and hi do not hold k, before
# the pieces rest: the value from rest
def Mst.value_skip(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  m: Maybe<&2, Hashes.Hash>,
  +l: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == False{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, rest, k) == Pieces.value(~S, ~fetch, f, s, Piece.sub(m, l, lo, hi, rest), k): Maybe<&2, List<&2, U32>>
}:
  match m:
    case None{}:
      hin => {==}
    case Some{+h}:
      hin =>
        %Equal.sym(Bool, Bool.and(Bound.after(lo, k), Bound.before(k, hi)), False{}, hin): {
          Pieces.value(~S, ~fetch, f, s, rest, k) == Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Piece.value(~S, ~fetch, f, s, Piece.Sub{h, l, lo, hi}, k),
            u => Pieces.value(~S, ~fetch, f, s, rest, k)
          ): Maybe<&2, List<&2, U32>>
        }
        {==}

# pieces between ik and hi give no value of a key before ik
def Mst.value_before(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +ks: List<&2, Piece>,
  +ik: List<&2, U32>,
  +hi: Maybe<&2, List<&2, U32>>,
  +k: List<&2, U32>
) -> {Pieces.inside(ks, Some{ik}, hi) == True{}: Bool} -> {Key.is_lt(ik, k) == False{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, ks, k) == None{}: Maybe<&2, List<&2, U32>>
}:
  +hin => +hk => Pieces.value_none(
    ~S,
    ~fetch,
    f,
    s,
    ks,
    k
  )(
    Bool.false_of(
      Pieces.covers(ks, k),
      cv => Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          Key.is_lt(ik, k),
          False{},
          Equal.sym(
            Bool,
            Key.is_lt(ik, k),
            True{},
            Shared.Bool.and_true_left(Key.is_lt(ik, k), Bound.before(k, hi))(Pieces.inside_covers(ks, Some{ik}, hi, k)(hin)(cv))
          ),
          hk
        )
      )
    )
  )

# Mst.value_pick at an item of the key ik, whose comparison with k is c
def Mst.value_pick.con(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  c: Cmp,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  +ik: List<&2, U32>,
  +iv: List<&2, U32>,
  +r: Maybe<&2, Hashes.Hash>,
  +rest: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks2: List<&2, Piece>,
  +k: List<&2, U32>,
  +ec: {Key.cmp(k, ik) == c: Cmp},
  +hin: {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool},
  ew: {Nat.is_eq(Key.level(ik), l) == True{}: Bool},
  ins2: {Pieces.inside(ks2, Some{ik}, hi) == True{}: Bool},
  ih: {Bool.and(Key.is_lt(ik, k), Bound.before(k, hi)) == True{}: Bool} -> {
    Pieces.value(~S, ~fetch, f, s, ks2, k)
      == Look.value(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))): Maybe<
      &2,
      List<&2, U32>>
  }
) -> {
  Pieces.value(~S, ~fetch, f, s, Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ks2), k)
    == Look.value(
      Mst.look.pick(
        Shared.Bool.when(
          Pick,
          Cmp.is_lt(c),
          u => Pick.Down{prev, Room.of(l, lo, Some{ik})},
          u => Shared.Bool.when(Pick, Cmp.is_eq(c), w => Pick.Hit{iv}, w => Mst.pick(rest, r, l, Some{ik}, hi, k))
        ),
        h,
        l,
        k,
        m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k)
      )
    ): Maybe<&2, List<&2, U32>>
}:
  match c:
    case LT{}:
      Mst.value_sub(
        ~S,
        ~fetch,
        f,
        s,
        prev,
        l,
        lo,
        Some{ik},
        Piece.Bind{ik, iv} <> ks2,
        k
      )(Shared.Bool.and_both(Bound.after(lo, k), Key.is_lt(k, ik))(Shared.Bool.and_true_left(Bound.after(lo, k), Bound.before(k, hi))(hin))(Key.lt_of(k, ik, LT{})(ec)))(
        %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, ik, k), False{}, Key.eq_of(k, ik, LT{})(ec)): {
          Shared.Bool.when(
            Maybe<&2, List<&2, U32>>,
            _,
            u => Piece.value(~S, ~fetch, f, s, Piece.Bind{ik, iv}, k),
            u => Pieces.value(~S, ~fetch, f, s, ks2, k)
          )
            == None{}: Maybe<&2, List<&2, U32>>
        }
        Mst.value_before(~S, ~fetch, f, s, ks2, ik, hi, k)(ins2)(Key.gt_of(k, ik, LT{})(ec))
      )
    case EQ{}:
      +ke = Key.cmp_eq(k, ik)(ec)
      %Mst.value_skip(
        ~S,
        ~fetch,
        f,
        s,
        prev,
        l,
        lo,
        Some{ik},
        Piece.Bind{ik, iv} <> ks2,
        k
      )(
        %Equal.sym(Bool, Key.is_lt(k, ik), False{}, Key.lt_of(k, ik, EQ{})(ec)): {Bool.and(Bound.after(lo, k), _) == False{}: Bool}
        Shared.Bool.and_false_right(Bound.after(lo, k))
      ): {
        _
          == Look.value(Shared.Bool.when(Look, Nat.is_eq(Key.level(k), l), u => Look.Found{iv}, u => Look.Missing{h})): Maybe<&2, List<&2, U32>>
      }
      %Equal.sym(
        Bool,
        Nat.is_eq(Key.level(k), l),
        True{},
        Equal.trans(Bool, Nat.is_eq(Key.level(k), l), Nat.is_eq(Key.level(ik), l), True{}, Equal.cong(List<&2, U32>, Bool, x => Nat.is_eq(Key.level(x), l), k, ik, ke), ew)
      ): {
        Pieces.value(~S, ~fetch, f, s, Piece.Bind{ik, iv} <> ks2, k)
          == Look.value(Shared.Bool.when(Look, _, u => Look.Found{iv}, u => Look.Missing{h})): Maybe<&2, List<&2, U32>>
      }
      %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, ik, k), True{}, Key.eq_of(k, ik, EQ{})(ec)): {
        Shared.Bool.when(
          Maybe<&2, List<&2, U32>>,
          _,
          u => Piece.value(~S, ~fetch, f, s, Piece.Bind{ik, iv}, k),
          u => Pieces.value(~S, ~fetch, f, s, ks2, k)
        )
          == Some{iv}: Maybe<&2, List<&2, U32>>
      }
      {==}
    case GT{}:
      +l2 = Key.gt_of(k, ik, GT{})(ec)
      %Mst.value_skip(
        ~S,
        ~fetch,
        f,
        s,
        prev,
        l,
        lo,
        Some{ik},
        Piece.Bind{ik, iv} <> ks2,
        k
      )(
        %Equal.sym(Bool, Key.is_lt(k, ik), False{}, Key.lt_of(k, ik, GT{})(ec)): {Bool.and(Bound.after(lo, k), _) == False{}: Bool}
        Shared.Bool.and_false_right(Bound.after(lo, k))
      ): {
        _
          == Look.value(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))): Maybe<
          &2,
          List<&2, U32>>
      }
      %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, ik, k), False{}, Key.eq_of(k, ik, GT{})(ec)): {
        Shared.Bool.when(
          Maybe<&2, List<&2, U32>>,
          _,
          u => Piece.value(~S, ~fetch, f, s, Piece.Bind{ik, iv}, k),
          u => Pieces.value(~S, ~fetch, f, s, ks2, k)
        )
          == Look.value(Mst.look.pick(Mst.pick(rest, r, l, Some{ik}, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))): Maybe<
          &2,
          List<&2, U32>>
      }
      ih(Shared.Bool.and_both(Key.is_lt(ik, k), Bound.before(k, hi))(l2)(Shared.Bool.and_true_right(Bound.after(lo, k), Bound.before(k, hi))(hin)))

# the pieces of the items xs of the node of the hash h give, for a key in
# their bounds, what a read of the key in the node finds
def Mst.value_pick(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +f: Nat,
  +s: S,
  +h: Hashes.Hash,
  xs: List<&2, Item>,
  +l: Nat,
  +prev: Maybe<&2, Hashes.Hash>,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.pieces(xs, l, prev, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {
  Pieces.value(~S, ~fetch, f, s, ks, k)
    == Look.value(Mst.look.pick(Mst.pick(xs, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))): Maybe<&2, List<&2, U32>>
}:
  match xs:
    case Nil{}:
      ep => hin =>
        %Shared.Maybe.some_inj(List<&2, Piece>, Piece.sub(prev, l, lo, hi, []), ks, ep): {
          Pieces.value(~S, ~fetch, f, s, _, k) == Look.value(Mst.look.go(~S, ~fetch, f, s, Room{l, lo, hi}, prev, k)): Maybe<&2, List<&2, U32>>
        }
        Mst.value_sub(~S, ~fetch, f, s, prev, l, lo, hi, [], k)(hin)({==})
    case Con{Item{+ik, +iv, +r}, +rest}:
      ep => +hin => Maybe.when_cases(
        List<&2, Piece>,
        Bool.and(
          Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
          Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
        ),
        u => Maybe.map(
          &2,
          List<&2, Piece>,
          List<&2, Piece>,
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          Mst.pieces(rest, l, r, Some{ik}, hi)
        ),
        ks,
        {
          Pieces.value(~S, ~fetch, f, s, ks, k)
            == Look.value(
              Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))
            ): Maybe<&2, List<&2, U32>>
        },
        +c => e2 => Maybe.map_cases(
          List<&2, Piece>,
          List<&2, Piece>,
          Mst.pieces(rest, l, r, Some{ik}, hi),
          ps2 => Piece.sub(prev, l, lo, Some{ik}, Piece.Bind{ik, iv} <> ps2),
          ks,
          {
            Pieces.value(~S, ~fetch, f, s, ks, k)
              == Look.value(
                Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))
              ): Maybe<&2, List<&2, U32>>
          },
          +ks2 => +e3 => e4 =>
            %e4: {
              Pieces.value(~S, ~fetch, f, s, _, k)
                == Look.value(
                  Mst.look.pick(Mst.pick(Item{ik, iv, r} <> rest, prev, l, lo, hi, k), h, l, k, m2 => r2 => Mst.look.go(~S, ~fetch, f, s, r2, m2, k))
                ): Maybe<&2, List<&2, U32>>
            }
            Mst.value_pick.con(
              ~S,
              ~fetch,
              Key.cmp(k, ik),
              f,
              s,
              h,
              ik,
              iv,
              r,
              rest,
              l,
              prev,
              lo,
              hi,
              ks2,
              k,
              {==},
              hin,
              Shared.Bool.and_true_left(
                Nat.is_eq(Key.level(ik), l),
                Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))
              )(
                Shared.Bool.and_true_left(
                  Bool.and(Nat.is_eq(Key.level(ik), l), Bool.or(Maybe.is_none(&2, Hashes.Hash, prev), Bool.not(List.is_empty(&2, U32, ik)))),
                  Bool.and(Bound.after(lo, ik), Bound.before(ik, hi))
                )(c)
              ),
              Shared.Bool.and_true_right(Pieces.sorted(ks2), Pieces.inside(ks2, Some{ik}, hi))(Mst.pieces_sorted(rest, l, r, Some{ik}, hi, ks2)(e3)),
              hin2 => Mst.value_pick(~S, ~fetch, f, s, h, rest, l, r, Some{ik}, hi, ks2, k)(e3)(hin2)
            )
        )(e2)
      )(ep)

# the pieces of an opened node give, for a key in its bounds, what a read of
# its subtree finds
def Mst.value_open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.open(~S, ~fetch, s, h, up, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {Bool.and(Bound.after(lo, k), Bound.before(k, hi)) == True{}: Bool} -> {
  Pieces.value(~S, ~fetch, q, s, ks, k) == Look.value(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k)): Maybe<&2, List<&2, U32>>
}:
  e => hin => Mst.open_cases(
    ~S,
    ~fetch,
    s,
    h,
    up,
    lo,
    hi,
    ks,
    {Pieces.value(~S, ~fetch, q, s, ks, k) == Look.value(Mst.look.go(~S, ~fetch, 1n+q, s, Room{up, lo, hi}, Some{h}, k)): Maybe<&2, List<&2, U32>>},
    +l => +left => +xs => ef => eh => en => elt => ee0 => ep =>
      %Equal.sym(Maybe<&2, Node>, Mst.node.in(~S, ~fetch, s, h, Room{up, lo, hi}), Some{Node{l, left, xs}}, en): {
        Pieces.value(~S, ~fetch, q, s, ks, k)
          == Look.value(Mst.look.at(h, _, Room{up, lo, hi}, k, m2 => r2 => Mst.look.go(~S, ~fetch, q, s, r2, m2, k))): Maybe<&2, List<&2, U32>>
      }
      Mst.value_pick(~S, ~fetch, q, s, h, xs, l, left, lo, hi, ks, k)(ep)(hin)
  )(e)

# the pieces of an opened node are sorted and lie in its bounds
def Mst.open_sorted(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +up: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +ks: List<&2, Piece>
) -> {Mst.open(~S, ~fetch, s, h, up, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
  Bool.and(Pieces.sorted(ks), Pieces.inside(ks, lo, hi)) == True{}: Bool
}:
  e => Mst.open_cases(
    ~S,
    ~fetch,
    s,
    h,
    up,
    lo,
    hi,
    ks,
    {Bool.and(Pieces.sorted(ks), Pieces.inside(ks, lo, hi)) == True{}: Bool},
    +l => +left => +xs => ef => eh => en => elt => ee0 => ep => Mst.pieces_sorted(xs, l, left, lo, hi, ks)(ep)
  )(e)

# the opening of a binding, then pieces: the binding, then their opening
def Mst.open_all_bind(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +k2: List<&2, U32>,
  +v2: List<&2, U32>,
  +r: List<&2, Piece>,
  -a2: List<&2, Piece>,
  -P: Type,
  k: @r2: List<&2, Piece> -> {Mst.open.all(~S, ~fetch, s, r) == Some{r2}: Maybe<&2, List<&2, Piece>>} -> {
    Piece.Bind{k2, v2} <> r2 == a2: List<&2, Piece>
  } -> P
) -> {Mst.open.all(~S, ~fetch, s, Piece.Bind{k2, v2} <> r) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> P:
  e => Maybe.map_cases(
    List<&2, Piece>,
    List<&2, Piece>,
    Mst.open.all(~S, ~fetch, s, r),
    x => Piece.Bind{k2, v2} <> x,
    a2,
    P,
    r2 => er => ea => k(r2)(er)(ea)
  )(e)

# the opening of a subtree, then pieces: the pieces of its node, then their
# opening
def Mst.open_all_sub(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +h: Hashes.Hash,
  +u: Nat,
  +lo: Maybe<&2, List<&2, U32>>,
  +hi: Maybe<&2, List<&2, U32>>,
  +r: List<&2, Piece>,
  -a2: List<&2, Piece>,
  -P: Type,
  k: @ks: List<&2, Piece> -> @r2: List<&2, Piece> -> {Mst.open(~S, ~fetch, s, h, u, lo, hi) == Some{ks}: Maybe<&2, List<&2, Piece>>} -> {
    Mst.open.all(~S, ~fetch, s, r) == Some{r2}: Maybe<&2, List<&2, Piece>>
  } -> {List.append(&2, Piece, ks, r2) == a2: List<&2, Piece>} -> P
) -> {Mst.open.all(~S, ~fetch, s, Piece.Sub{h, u, lo, hi} <> r) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> P:
  e => Maybe.bind_cases(
    List<&2, Piece>,
    List<&2, Piece>,
    Mst.open(~S, ~fetch, s, h, u, lo, hi),
    a => Maybe.map(&2, List<&2, Piece>, List<&2, Piece>, b => List.append(&2, Piece, a, b), Mst.open.all(~S, ~fetch, s, r)),
    a2,
    P,
    +ks => eo => e2 => Maybe.map_cases(
      List<&2, Piece>,
      List<&2, Piece>,
      Mst.open.all(~S, ~fetch, s, r),
      b => List.append(&2, Piece, ks, b),
      a2,
      P,
      r2 => er => ea => k(ks)(r2)(eo)(er)(ea)
    )(e2)
  )(e)

# an opening may hold only keys that what it opens may hold
def Mst.open_all_covers(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ps: List<&2, Piece>,
  -a2: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.open.all(~S, ~fetch, s, ps) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> {Pieces.covers(a2, k) == True{}: Bool} -> {
  Pieces.covers(ps, k) == True{}: Bool
}:
  match ps:
    case Nil{}:
      e => hc => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Pieces.covers(a2, k),
            True{},
            Equal.cong(List<&2, Piece>, Bool, x => Pieces.covers(x, k), [], a2, Shared.Maybe.some_inj(List<&2, Piece>, [], a2, e)),
            hc
          )
        )
      )
    case Con{Piece.Bind{+k2, +v2}, +rest}:
      e => hc => Mst.open_all_bind(
        ~S,
        ~fetch,
        s,
        k2,
        v2,
        rest,
        a2,
        {Pieces.covers(Piece.Bind{k2, v2} <> rest, k) == True{}: Bool},
        +r2 => er => ea =>
          +hc2 = Equal.trans(
            Bool,
            Pieces.covers(Piece.Bind{k2, v2} <> r2, k),
            Pieces.covers(a2, k),
            True{},
            Equal.cong(List<&2, Piece>, Bool, x => Pieces.covers(x, k), Piece.Bind{k2, v2} <> r2, a2, ea),
            hc
          )
          Bool.cases(
            Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
            {Pieces.covers(Piece.Bind{k2, v2} <> rest, k) == True{}: Bool},
            ct => Bool.or_true_left(Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), Pieces.covers(rest, k))(ct),
            cf => Bool.or_true_of(
              Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
              Pieces.covers(rest, k)
            )(
              Mst.open_all_covers(
                ~S,
                ~fetch,
                s,
                rest,
                r2,
                k
              )(er)(
                Equal.trans(
                  Bool,
                  Pieces.covers(r2, k),
                  Bool.or(Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), Pieces.covers(r2, k)),
                  True{},
                  Equal.cong(
                    Bool,
                    Bool,
                    t => Bool.or(t, Pieces.covers(r2, k)),
                    False{},
                    Shared.List.is_eq(~U32, ~U32.is_eq, k2, k),
                    Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), False{}, cf)
                  ),
                  hc2
                )
              )
            )
          )
      )(e)
    case Con{Piece.Sub{+h, +u, +lo, +hi}, +rest}:
      e => hc => Mst.open_all_sub(
        ~S,
        ~fetch,
        s,
        h,
        u,
        lo,
        hi,
        rest,
        a2,
        {Pieces.covers(Piece.Sub{h, u, lo, hi} <> rest, k) == True{}: Bool},
        +ks => +r2 => eo => er => ea =>
          +hc2 = Equal.trans(
            Bool,
            Bool.or(Pieces.covers(ks, k), Pieces.covers(r2, k)),
            Pieces.covers(a2, k),
            True{},
            Equal.trans(
              Bool,
              Bool.or(Pieces.covers(ks, k), Pieces.covers(r2, k)),
              Pieces.covers(List.append(&2, Piece, ks, r2), k),
              Pieces.covers(a2, k),
              Equal.sym(Bool, Pieces.covers(List.append(&2, Piece, ks, r2), k), Bool.or(Pieces.covers(ks, k), Pieces.covers(r2, k)), Pieces.covers_append(ks, r2, k)),
              Equal.cong(List<&2, Piece>, Bool, x => Pieces.covers(x, k), List.append(&2, Piece, ks, r2), a2, ea)
            ),
            hc
          )
          Bool.cases(
            Pieces.covers(ks, k),
            {Pieces.covers(Piece.Sub{h, u, lo, hi} <> rest, k) == True{}: Bool},
            ct => Bool.or_true_left(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Pieces.covers(rest, k)
            )(
              Pieces.inside_covers(
                ks,
                lo,
                hi,
                k
              )(Shared.Bool.and_true_right(Pieces.sorted(ks), Pieces.inside(ks, lo, hi))(Mst.open_sorted(~S, ~fetch, s, h, u, lo, hi, ks)(eo)))(ct)
            ),
            cf => Bool.or_true_of(
              Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
              Pieces.covers(rest, k)
            )(
              Mst.open_all_covers(
                ~S,
                ~fetch,
                s,
                rest,
                r2,
                k
              )(er)(
                Equal.trans(
                  Bool,
                  Pieces.covers(r2, k),
                  Bool.or(Pieces.covers(ks, k), Pieces.covers(r2, k)),
                  True{},
                  Equal.cong(Bool, Bool, t => Bool.or(t, Pieces.covers(r2, k)), False{}, Pieces.covers(ks, k), Equal.sym(Bool, Pieces.covers(ks, k), False{}, cf)),
                  hc2
                )
              )
            )
          )
      )(e)

# a piece before pieces is before their opening
def Mst.open_all_after(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  +w: Piece,
  ps: List<&2, Piece>,
  -a2: List<&2, Piece>
) -> {Mst.open.all(~S, ~fetch, s, ps) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> {Pieces.after_all(w, ps) == True{}: Bool} -> {
  Pieces.after_all(w, a2) == True{}: Bool
}:
  match ps:
    case Nil{}:
      e => h =>
        %Shared.Maybe.some_inj(List<&2, Piece>, [], a2, e): {Pieces.after_all(w, _) == True{}: Bool}
        {==}
    case Con{Piece.Bind{+k2, +v2}, +rest}:
      e => +h => Mst.open_all_bind(
        ~S,
        ~fetch,
        s,
        k2,
        v2,
        rest,
        a2,
        {Pieces.after_all(w, a2) == True{}: Bool},
        +r2 => er => ea =>
          %ea: {Pieces.after_all(w, _) == True{}: Bool}
          Shared.Bool.and_both(
            Piece.before(w, Piece.Bind{k2, v2}),
            Pieces.after_all(w, r2)
          )(Shared.Bool.and_true_left(Piece.before(w, Piece.Bind{k2, v2}), Pieces.after_all(w, rest))(h))(
            Mst.open_all_after(~S, ~fetch, s, w, rest, r2)(er)(Shared.Bool.and_true_right(Piece.before(w, Piece.Bind{k2, v2}), Pieces.after_all(w, rest))(h))
          )
      )(e)
    case Con{Piece.Sub{+h2, +u, +lo, +hi}, +rest}:
      e => +h => Mst.open_all_sub(
        ~S,
        ~fetch,
        s,
        h2,
        u,
        lo,
        hi,
        rest,
        a2,
        {Pieces.after_all(w, a2) == True{}: Bool},
        +ks => +r2 => eo => er => ea =>
          %ea: {Pieces.after_all(w, _) == True{}: Bool}
          Pieces.after_all_append(
            w,
            ks,
            r2
          )(
            Pieces.refine_right_all(
              w,
              ks,
              lo,
              hi,
              h2,
              u
            )(Shared.Bool.and_true_left(Piece.before(w, Piece.Sub{h2, u, lo, hi}), Pieces.after_all(w, rest))(h))(
              Shared.Bool.and_true_right(Pieces.sorted(ks), Pieces.inside(ks, lo, hi))(Mst.open_sorted(~S, ~fetch, s, h2, u, lo, hi, ks)(eo))
            )
          )(Mst.open_all_after(~S, ~fetch, s, w, rest, r2)(er)(Shared.Bool.and_true_right(Piece.before(w, Piece.Sub{h2, u, lo, hi}), Pieces.after_all(w, rest))(h)))
      )(e)

# pieces before others are before their opening
def Mst.before_all_open(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ws: List<&2, Piece>,
  +ps: List<&2, Piece>,
  +a2: List<&2, Piece>
) -> {Mst.open.all(~S, ~fetch, s, ps) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> {Pieces.before_all(ws, ps) == True{}: Bool} -> {
  Pieces.before_all(ws, a2) == True{}: Bool
}:
  match ws:
    case Nil{}:
      e => h => {==}
    case Con{+w, +rest}:
      +e => +h => Shared.Bool.and_both(
        Pieces.after_all(w, a2),
        Pieces.before_all(rest, a2)
      )(Mst.open_all_after(~S, ~fetch, s, w, ps, a2)(e)(Shared.Bool.and_true_left(Pieces.after_all(w, ps), Pieces.before_all(rest, ps))(h)))(
        Mst.before_all_open(~S, ~fetch, s, rest, ps, a2)(e)(Shared.Bool.and_true_right(Pieces.after_all(w, ps), Pieces.before_all(rest, ps))(h))
      )

# the opening of sorted pieces is sorted
def Mst.open_all_sorted(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  ps: List<&2, Piece>,
  -a2: List<&2, Piece>
) -> {Mst.open.all(~S, ~fetch, s, ps) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> {Pieces.sorted(ps) == True{}: Bool} -> {
  Pieces.sorted(a2) == True{}: Bool
}:
  match ps:
    case Nil{}:
      e => h =>
        %Shared.Maybe.some_inj(List<&2, Piece>, [], a2, e): {Pieces.sorted(_) == True{}: Bool}
        {==}
    case Con{Piece.Bind{+k2, +v2}, +rest}:
      e => +h => Mst.open_all_bind(
        ~S,
        ~fetch,
        s,
        k2,
        v2,
        rest,
        a2,
        {Pieces.sorted(a2) == True{}: Bool},
        +r2 => +er => ea =>
          %ea: {Pieces.sorted(_) == True{}: Bool}
          Shared.Bool.and_both(
            Pieces.after_all(Piece.Bind{k2, v2}, r2),
            Pieces.sorted(r2)
          )(
            Mst.open_all_after(
              ~S,
              ~fetch,
              s,
              Piece.Bind{k2, v2},
              rest,
              r2
            )(er)(Shared.Bool.and_true_left(Pieces.after_all(Piece.Bind{k2, v2}, rest), Pieces.sorted(rest))(h))
          )(Mst.open_all_sorted(~S, ~fetch, s, rest, r2)(er)(Shared.Bool.and_true_right(Pieces.after_all(Piece.Bind{k2, v2}, rest), Pieces.sorted(rest))(h)))
      )(e)
    case Con{Piece.Sub{+h2, +u, +lo, +hi}, +rest}:
      e => +h => Mst.open_all_sub(
        ~S,
        ~fetch,
        s,
        h2,
        u,
        lo,
        hi,
        rest,
        a2,
        {Pieces.sorted(a2) == True{}: Bool},
        +ks => +r2 => eo => +er => ea =>
          +os = Mst.open_sorted(~S, ~fetch, s, h2, u, lo, hi, ks)(eo)
          %ea: {Pieces.sorted(_) == True{}: Bool}
          Pieces.sorted_append(
            ks,
            r2
          )(Shared.Bool.and_true_left(Pieces.sorted(ks), Pieces.inside(ks, lo, hi))(os))(
            Mst.open_all_sorted(~S, ~fetch, s, rest, r2)(er)(Shared.Bool.and_true_right(Pieces.after_all(Piece.Sub{h2, u, lo, hi}, rest), Pieces.sorted(rest))(h))
          )(
            Mst.before_all_open(
              ~S,
              ~fetch,
              s,
              ks,
              rest,
              r2
            )(er)(
              Pieces.refine_left_all(
                ks,
                rest,
                lo,
                hi,
                h2,
                u
              )(Shared.Bool.and_true_right(Pieces.sorted(ks), Pieces.inside(ks, lo, hi))(os))(
                Shared.Bool.and_true_left(Pieces.after_all(Piece.Sub{h2, u, lo, hi}, rest), Pieces.sorted(rest))(h)
              )
            )
          )
      )(e)

# the opening of sorted pieces gives, one level less down, the values that
# they give
def Mst.open_all_value(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +q: Nat,
  +s: S,
  ps: List<&2, Piece>,
  -a2: List<&2, Piece>,
  +k: List<&2, U32>
) -> {Mst.open.all(~S, ~fetch, s, ps) == Some{a2}: Maybe<&2, List<&2, Piece>>} -> {Pieces.sorted(ps) == True{}: Bool} -> {
  Pieces.value(~S, ~fetch, 1n+q, s, ps, k) == Pieces.value(~S, ~fetch, q, s, a2, k): Maybe<&2, List<&2, U32>>
}:
  match ps:
    case Nil{}:
      e => h =>
        %Shared.Maybe.some_inj(List<&2, Piece>, [], a2, e): {None{} == Pieces.value(~S, ~fetch, q, s, _, k): Maybe<&2, List<&2, U32>>}
        {==}
    case Con{Piece.Bind{+k2, +v2}, +rest}:
      e => +h => Mst.open_all_bind(
        ~S,
        ~fetch,
        s,
        k2,
        v2,
        rest,
        a2,
        {Pieces.value(~S, ~fetch, 1n+q, s, Piece.Bind{k2, v2} <> rest, k) == Pieces.value(~S, ~fetch, q, s, a2, k): Maybe<&2, List<&2, U32>>},
        +r2 => er => ea =>
          %ea: {Pieces.value(~S, ~fetch, 1n+q, s, Piece.Bind{k2, v2} <> rest, k) == Pieces.value(~S, ~fetch, q, s, _, k): Maybe<&2, List<&2, U32>>}
          Equal.cong(
            Maybe<&2, List<&2, U32>>,
            Maybe<&2, List<&2, U32>>,
            z => Shared.Bool.when(Maybe<&2, List<&2, U32>>, Shared.List.is_eq(~U32, ~U32.is_eq, k2, k), u => Some{v2}, u => z),
            Pieces.value(~S, ~fetch, 1n+q, s, rest, k),
            Pieces.value(~S, ~fetch, q, s, r2, k),
            Mst.open_all_value(~S, ~fetch, q, s, rest, r2, k)(er)(Shared.Bool.and_true_right(Pieces.after_all(Piece.Bind{k2, v2}, rest), Pieces.sorted(rest))(h))
          )
      )(e)
    case Con{Piece.Sub{+h2, +u, +lo, +hi}, +rest}:
      e => +h => Mst.open_all_sub(
        ~S,
        ~fetch,
        s,
        h2,
        u,
        lo,
        hi,
        rest,
        a2,
        {
          Pieces.value(~S, ~fetch, 1n+q, s, Piece.Sub{h2, u, lo, hi} <> rest, k) == Pieces.value(~S, ~fetch, q, s, a2, k): Maybe<&2, List<&2, U32>>
        },
        +ks => +r2 => +eo => +er => ea =>
          +os = Mst.open_sorted(~S, ~fetch, s, h2, u, lo, hi, ks)(eo)
          %ea: {
            Pieces.value(~S, ~fetch, 1n+q, s, Piece.Sub{h2, u, lo, hi} <> rest, k)
              == Pieces.value(~S, ~fetch, q, s, _, k): Maybe<&2, List<&2, U32>>
          }
          Bool.cases(
            Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
            {
              Pieces.value(~S, ~fetch, 1n+q, s, Piece.Sub{h2, u, lo, hi} <> rest, k)
                == Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k): Maybe<&2, List<&2, U32>>
            },
            +ct =>
              %Equal.sym(Bool, Bool.and(Bound.after(lo, k), Bound.before(k, hi)), True{}, ct): {
                Shared.Bool.when(
                  Maybe<&2, List<&2, U32>>,
                  _,
                  w => Piece.value(~S, ~fetch, 1n+q, s, Piece.Sub{h2, u, lo, hi}, k),
                  w => Pieces.value(~S, ~fetch, 1n+q, s, rest, k)
                )
                  == Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k): Maybe<&2, List<&2, U32>>
              }
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                Look.value(Mst.look.go(~S, ~fetch, 1n+q, s, Room{u, lo, hi}, Some{h2}, k)),
                Pieces.value(~S, ~fetch, q, s, ks, k),
                Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k),
                Equal.sym(
                  Maybe<&2, List<&2, U32>>,
                  Pieces.value(~S, ~fetch, q, s, ks, k),
                  Look.value(Mst.look.go(~S, ~fetch, 1n+q, s, Room{u, lo, hi}, Some{h2}, k)),
                  Mst.value_open(~S, ~fetch, q, s, h2, u, lo, hi, ks, k)(eo)(ct)
                ),
                Equal.sym(
                  Maybe<&2, List<&2, U32>>,
                  Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k),
                  Pieces.value(~S, ~fetch, q, s, ks, k),
                  Pieces.value_left(
                    ~S,
                    ~fetch,
                    q,
                    s,
                    ks,
                    r2,
                    k
                  )(
                    Bool.false_of(
                      Pieces.covers(r2, k),
                      c2 => Shared.Bool.true_ne_false(
                        Equal.trans(
                          Bool,
                          True{},
                          Pieces.covers(rest, k),
                          False{},
                          Equal.sym(Bool, Pieces.covers(rest, k), True{}, Mst.open_all_covers(~S, ~fetch, s, rest, r2, k)(er)(c2)),
                          Pieces.after_all_miss(
                            Piece.Sub{h2, u, lo, hi},
                            rest,
                            k
                          )(ct)(Shared.Bool.and_true_left(Pieces.after_all(Piece.Sub{h2, u, lo, hi}, rest), Pieces.sorted(rest))(h))
                        )
                      )
                    )
                  )
                )
              ),
            +cf =>
              %Equal.sym(Bool, Bool.and(Bound.after(lo, k), Bound.before(k, hi)), False{}, cf): {
                Shared.Bool.when(
                  Maybe<&2, List<&2, U32>>,
                  _,
                  w => Piece.value(~S, ~fetch, 1n+q, s, Piece.Sub{h2, u, lo, hi}, k),
                  w => Pieces.value(~S, ~fetch, 1n+q, s, rest, k)
                )
                  == Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k): Maybe<&2, List<&2, U32>>
              }
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                Pieces.value(~S, ~fetch, 1n+q, s, rest, k),
                Pieces.value(~S, ~fetch, q, s, r2, k),
                Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k),
                Mst.open_all_value(~S, ~fetch, q, s, rest, r2, k)(er)(Shared.Bool.and_true_right(Pieces.after_all(Piece.Sub{h2, u, lo, hi}, rest), Pieces.sorted(rest))(h)),
                Equal.sym(
                  Maybe<&2, List<&2, U32>>,
                  Pieces.value(~S, ~fetch, q, s, List.append(&2, Piece, ks, r2), k),
                  Pieces.value(~S, ~fetch, q, s, r2, k),
                  Pieces.value_right(
                    ~S,
                    ~fetch,
                    q,
                    s,
                    ks,
                    r2,
                    k
                  )(
                    Bool.false_of(
                      Pieces.covers(ks, k),
                      c2 => Shared.Bool.true_ne_false(
                        Equal.trans(
                          Bool,
                          True{},
                          Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                          False{},
                          Equal.sym(
                            Bool,
                            Bool.and(Bound.after(lo, k), Bound.before(k, hi)),
                            True{},
                            Pieces.inside_covers(ks, lo, hi, k)(Shared.Bool.and_true_right(Pieces.sorted(ks), Pieces.inside(ks, lo, hi))(os))(c2)
                          ),
                          cf
                        )
                      )
                    )
                  )
                )
              )
          )
      )(e)

# the values x and y differ
def Mst.differ(x: Maybe<&2, List<&2, U32>>, y: Maybe<&2, List<&2, U32>>) -> Bool:
  Bool.not(Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x, y))

# a value does not differ from itself
def Mst.differ_self(x: Maybe<&2, List<&2, U32>>) -> {Mst.differ(x, x) == False{}: Bool}:
  match x:
    case None{}:
      {==}
    case Some{value}:
      %Equal.sym(Bool, Shared.List.is_eq(U32, U32.is_eq, value, value), True{}, Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), value)) :
        {Bool.not(_) == False{} : Bool}
      {==}

# pieces that Piece.same calls the same are equal
def Piece.same_eq(x: Piece, y: Piece) -> {Piece.same(x, y) == True{}: Bool} -> {x == y: Piece}:
  match x y:
    case Piece.Bind{+k1, +v1} Piece.Bind{+k2, +v2}:
      +h =>
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          k1,
          k2
        )(Shared.Bool.and_true_left(Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2))(h)): {
          Piece.Bind{k1, v1} == Piece.Bind{_, v2}: Piece
        }
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          v1,
          v2
        )(Shared.Bool.and_true_right(Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2), Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2))(h)): {
          Piece.Bind{k1, v1} == Piece.Bind{k1, _}: Piece
        }
        {==}
    case Piece.Sub{+h1, +u1, +lo1, +hi1} Piece.Sub{+h2, +u2, +lo2, +hi2}:
      +h =>
        +a = Shared.Bool.and_true_left(
          Bool.and(Hashes.Hash.is_eq(h1, h2), Nat.is_eq(u1, u2)),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), lo1, lo2),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), hi1, hi2)
          )
        )(h)
        +b = Shared.Bool.and_true_right(
          Bool.and(Hashes.Hash.is_eq(h1, h2), Nat.is_eq(u1, u2)),
          Bool.and(
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), lo1, lo2),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), hi1, hi2)
          )
        )(h)
        %Hashes.Hash.is_eq_sound(h1, h2)(Shared.Bool.and_true_left(Hashes.Hash.is_eq(h1, h2), Nat.is_eq(u1, u2))(a)): {
          Piece.Sub{h1, u1, lo1, hi1} == Piece.Sub{_, u2, lo2, hi2}: Piece
        }
        %Shared.Nat.is_eq_sound(u1, u2)(Shared.Bool.and_true_right(Hashes.Hash.is_eq(h1, h2), Nat.is_eq(u1, u2))(a)): {
          Piece.Sub{h1, u1, lo1, hi1} == Piece.Sub{h1, _, lo2, hi2}: Piece
        }
        %Shared.Maybe.is_eq_sound(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          x2 => y2 => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x2, y2),
          lo1,
          lo2
        )(
          Shared.Bool.and_true_left(
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), lo1, lo2),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), hi1, hi2)
          )(b)
        ): {Piece.Sub{h1, u1, lo1, hi1} == Piece.Sub{h1, u1, _, hi2}: Piece}
        %Shared.Maybe.is_eq_sound(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          x2 => y2 => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x2, y2),
          hi1,
          hi2
        )(
          Shared.Bool.and_true_right(
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), lo1, lo2),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), hi1, hi2)
          )(b)
        ): {Piece.Sub{h1, u1, lo1, hi1} == Piece.Sub{h1, u1, lo1, _}: Piece}
        {==}
    case Piece.Bind{k1, v1} Piece.Sub{h2, u2, lo2, hi2}:
      h => Empty.absurd({Piece.Bind{k1, v1} == Piece.Sub{h2, u2, lo2, hi2}: Piece}, Shared.Bool.false_ne_true(h))
    case Piece.Sub{h1, u1, lo1, hi1} Piece.Bind{k2, v2}:
      h => Empty.absurd({Piece.Sub{h1, u1, lo1, hi1} == Piece.Bind{k2, v2}: Piece}, Shared.Bool.false_ne_true(h))

# a reversal onto acc is the reversal, then acc
def List.rev_acc(-A: Data, xs: List<&2, A>, acc: List<&2, A>) -> {
  List.reverse.go(&2, A, xs, acc) == List.append(&2, A, List.reverse(&2, A, xs), acc): List<&2, A>
}:
  match xs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      +head = head
      +tail = tail
      +acc = acc
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, tail, [head]), List.append(&2, A, List.reverse(&2, A, tail), [head]), List.rev_acc(A, tail, [head])) :
        {List.reverse.go(&2, A, tail, head <> acc) == List.append(&2, A, _, acc) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.append(&2, A, List.append(&2, A, List.reverse.go(&2, A, tail, []), [head]), acc), List.append(&2, A, List.reverse.go(&2, A, tail, []), List.append(&2, A, [head], acc)), Shared.List.append_assoc(A, List.reverse.go(&2, A, tail, []), [head], acc)) :
        {List.reverse.go(&2, A, tail, head <> acc) == _ : List<&2, A>}
      List.rev_acc(A, tail, head <> acc)

# the reversal of xs, then ys, is the reversal of ys, then of xs
def List.rev_append.g2(
  -A: Data,
  +xs: List<&2, A>,
  +ys: List<&2, A>,
  +x: List<&2, A>,
  hx: {x == List.reverse.go(&2, A, ys, []) : List<&2, A>}) ->
  {List.reverse.go(&2, A, List.append(&2, A, xs, ys), []) == List.append(&2, A, x, List.reverse.go(&2, A, xs, [])) : List<&2, A>}:
  match xs:
    case Nil{}:
      %Equal.sym(List<&2, A>, List.append(&2, A, x, []), x, Shared.List.append_nil(A, x)) :
        {List.reverse.go(&2, A, ys, []) == _ : List<&2, A>}
      Equal.sym(List<&2, A>, x, List.reverse.go(&2, A, ys, []), hx)
    case Con{head, tail}:
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, List.append(&2, A, tail, ys), [head]), List.append(&2, A, List.reverse(&2, A, List.append(&2, A, tail, ys)), [head]), List.rev_acc(A, List.append(&2, A, tail, ys), [head])) :
        {_ == List.append(&2, A, x, List.reverse.go(&2, A, tail, [head])) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, List.append(&2, A, tail, ys), []), List.append(&2, A, x, List.reverse.go(&2, A, tail, [])), List.rev_append.g2(A, tail, ys, x, hx)) :
        {List.append(&2, A, _, [head]) == List.append(&2, A, x, List.reverse.go(&2, A, tail, [head])) : List<&2, A>}
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, tail, [head]), List.append(&2, A, List.reverse(&2, A, tail), [head]), List.rev_acc(A, tail, [head])) :
        {List.append(&2, A, List.append(&2, A, x, List.reverse.go(&2, A, tail, [])), [head]) == List.append(&2, A, x, _) : List<&2, A>}
      Shared.List.append_assoc(A, x, List.reverse.go(&2, A, tail, []), [head])

def List.rev_append(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> {
  List.reverse(&2, A, List.append(&2, A, xs, ys)) == List.append(&2, A, List.reverse(&2, A, ys), List.reverse(&2, A, xs)): List<&2, A>
}:
  +ys = ys
  List.rev_append.g2(A, xs, ys, List.reverse.go(&2, A, ys, []), {==})

# a list reversed twice is itself
def List.rev_rev(-A: Data, xs: List<&2, A>) -> {List.reverse(&2, A, List.reverse(&2, A, xs)) == xs: List<&2, A>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      %Equal.sym(List<&2, A>, List.reverse.go(&2, A, r, [x]), List.append(&2, A, List.reverse(&2, A, r), [x]), List.rev_acc(A, r, [x])): {
        List.reverse(&2, A, _) == x <> r: List<&2, A>
      }
      %Equal.sym(
        List<&2, A>,
        List.reverse(&2, A, List.append(&2, A, List.reverse(&2, A, r), [x])),
        List.append(&2, A, List.reverse(&2, A, [x]), List.reverse(&2, A, List.reverse(&2, A, r))),
        List.rev_append(A, List.reverse(&2, A, r), [x])
      ): {_ == x <> r: List<&2, A>}
      %Equal.sym(List<&2, A>, List.reverse(&2, A, List.reverse(&2, A, r)), r, List.rev_rev(A, r)): {x <> _ == x <> r: List<&2, A>}
      {==}

# the pieces of the first tree of a run
def Runs.side_a(r: Runs) -> List<&2, Piece>:
  match r:
    case Runs{a, b}:
      a

# the pieces of the second tree of a run
def Runs.side_b(r: Runs) -> List<&2, Piece>:
  match r:
    case Runs{a, b}:
      b

# the pieces at the fronts of as and bs that a trim drops
def Mst.trim_pre(as: List<&2, Piece>, bs: List<&2, Piece>) -> List<&2, Piece>:
  match as bs:
    case Con{+x, ra} Con{y, rb}:
      Shared.Bool.when(List<&2, Piece>, Piece.same(x, y), u => x <> Mst.trim_pre(ra, rb), u => [])
    case xs ys:
      []

# Mst.trim_a at two first pieces x and y that Piece.same calls t
def Mst.trim_a.at(
  t: Bool,
  +x: Piece,
  -y: Piece,
  +ra: List<&2, Piece>,
  -rb: List<&2, Piece>,
  ih: {List.append(&2, Piece, Mst.trim_pre(ra, rb), Runs.side_a(Mst.trim(ra, rb))) == ra: List<&2, Piece>}
) -> {
  List.append(
    &2,
    Piece,
    Shared.Bool.when(List<&2, Piece>, t, u => x <> Mst.trim_pre(ra, rb), u => []),
    Runs.side_a(Shared.Bool.when(Runs, t, u => Mst.trim(ra, rb), u => Runs{x <> ra, y <> rb}))
  )
    == x <> ra: List<&2, Piece>
}:
  match t:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(List<&2, Piece>, List.append(&2, Piece, Mst.trim_pre(ra, rb), Runs.side_a(Mst.trim(ra, rb))), ra, ih) :
        {x <> _ == x <> ra : List<&2, Piece>}
      {==}

# a trim drops a front of as and keeps the rest
def Mst.trim_a(as: List<&2, Piece>, bs: List<&2, Piece>) -> {
  List.append(&2, Piece, Mst.trim_pre(as, bs), Runs.side_a(Mst.trim(as, bs))) == as: List<&2, Piece>
}:
  match as:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{head1, tail1}:
          +head = head
          +tail = tail
          Mst.trim_a.at(Piece.same(head, head1), head, head1, tail, tail1, Mst.trim_a(tail, tail1))

# Mst.trim_b at two first pieces x and y that Piece.same calls t
def Mst.trim_b.at(
  t: Bool,
  +x: Piece,
  +y: Piece,
  -ra: List<&2, Piece>,
  +rb: List<&2, Piece>,
  et: {Piece.same(x, y) == t: Bool},
  ih: {List.append(&2, Piece, Mst.trim_pre(ra, rb), Runs.side_b(Mst.trim(ra, rb))) == rb: List<&2, Piece>}
) -> {
  List.append(
    &2,
    Piece,
    Shared.Bool.when(List<&2, Piece>, t, u => x <> Mst.trim_pre(ra, rb), u => []),
    Runs.side_b(Shared.Bool.when(Runs, t, u => Mst.trim(ra, rb), u => Runs{x <> ra, y <> rb}))
  )
    == y <> rb: List<&2, Piece>
}:
  match t:
    case False{}:
      {==}
    case True{}:
      Shared.List.cons_eq(Piece, x, y, List.append(&2, Piece, Mst.trim_pre(ra, rb), Runs.side_b(Mst.trim(ra, rb))), rb, Piece.same_eq(x, y)(et), ih)

# a trim drops the same front of bs and keeps the rest
def Mst.trim_b(as: List<&2, Piece>, bs: List<&2, Piece>) -> {
  List.append(&2, Piece, Mst.trim_pre(as, bs), Runs.side_b(Mst.trim(as, bs))) == bs: List<&2, Piece>
}:
  match as:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match bs:
        case Nil{}:
          {==}
        case Con{head1, tail1}:
          +head = head
          +head1 = head1
          +tail1 = tail1
          Mst.trim_b.at(Piece.same(head, head1), head, head1, tail, tail1, {==}, Mst.trim_b(tail, tail1))

# a run is the run of its two sides
def Runs.eta(r: Runs) -> {r == Runs{Runs.side_a(r), Runs.side_b(r)}: Runs}:
  match r:
    case Runs{a, b}:
      {==}

# a write to a tree that lists whole reads every node it needs
def Mst.put_some(
  ~S: Data,
  ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  +s: S,
  h: Maybe<&2, Hashes.Hash>,
  +bs: List<&2, Binding>,
  +k: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>
) -> {Mst.range(~S, ~fetch, s, h, []) == Some{bs}: Maybe<&2, List<&2, Binding>>} -> {
  Maybe.is_some(&2, Edit, Mst.put(~S, ~fetch, s, h, k, m)) == True{}: Bool
}:
  ?TODO

# a root is a function of its bindings, over any root
law Mst.canon:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Canon(S, Mst.ops(~S, ~fetch))

def Mst.canon(ty, fetch):
  +s => +h1 => +h2 => +bs => e1 => e2 => Mst.range_list(
    ~ty,
    ~fetch,
    h1,
    63n,
    s,
    [],
    Mst.depth(),
    None{},
    None{},
    [],
    bs,
    {h1 == h2: Maybe<&2, Hashes.Hash>},
    +a1 => b1 => e41 => eb1 => esl1 => Mst.range_list(
      ~ty,
      ~fetch,
      h2,
      63n,
      s,
      [],
      Mst.depth(),
      None{},
      None{},
      [],
      bs,
      {h1 == h2: Maybe<&2, Hashes.Hash>},
      +a2 => b2 => e42 => eb2 => esl2 => Mst.canon_sub(
        ~ty,
        ~fetch,
        63n,
        s,
        h1,
        h2,
        Mst.depth(),
        None{},
        None{},
        bs,
        Shared.Bool.or_true_right(Maybe.is_none(&2, Hashes.Hash, h1)),
        Shared.Bool.or_true_right(Maybe.is_none(&2, Hashes.Hash, h2)),
        ys1 => ys2 => l3 => p1 => p2 => j1 => j2 => hb3 => f1 => g1 => f2 => g2 => Mst.canon_node(
          ~ty,
          ~fetch,
          63n,
          s,
          ys1,
          ys2,
          l3,
          p1,
          p2,
          None{},
          None{},
          j1,
          j2,
          bs
        )(hb3)(f1)(g1)(f2)(g2)
      )(
        Equal.trans(
          Maybe<&2, List<&2, Binding>>,
          Mst.sub_list(~ty, ~fetch, 63n, s, [], h1, Mst.depth(), None{}, None{}),
          Some{a1},
          Some{bs},
          esl1,
          Equal.cong(List<&2, Binding>, Maybe<&2, List<&2, Binding>>, x => Some{x}, a1, bs, Bindings.cat_nil(a1, b1, bs)(eb1)(e41))
        )
      )(
        Equal.trans(
          Maybe<&2, List<&2, Binding>>,
          Mst.sub_list(~ty, ~fetch, 63n, s, [], h2, Mst.depth(), None{}, None{}),
          Some{a2},
          Some{bs},
          esl2,
          Equal.cong(List<&2, Binding>, Maybe<&2, List<&2, Binding>>, x => Some{x}, a2, bs, Bindings.cat_nil(a2, b2, bs)(eb2)(e42))
        )
      )
    )(e2)
  )(e1)

# a listing holds exactly the bindings under its prefix, in order
law Mst.lists:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  Laws.Range(S, Mst.ops(~S, ~fetch))

def Mst.lists(ty, fetch):
  +s => +h => +p => +bs => +e => (
    Mst.lists_sorted(~ty, ~fetch, s, h, p, bs)(e),
    +k => +v => Equal.trans(
      Bool,
      List.contains(~Binding, ~Binding.is_eq, bs, Binding{k, v}),
      Bool.and(Key.leads(p, k), Pieces.has(~ty, ~fetch, Mst.depth(), s, Mst.root(h), k, v)),
      Bool.and(Key.leads(p, k), Look.has(Mst.look(~ty, ~fetch, s, h, k), v)),
      Mst.lists_has(~ty, ~fetch, Mst.depth(), s, p, Mst.root(h), bs, k, v)(e),
      Equal.cong(
        Bool,
        Bool,
        x => Bool.and(Key.leads(p, k), x),
        Pieces.has(~ty, ~fetch, Mst.depth(), s, Mst.root(h), k, v),
        Look.has(Mst.look(~ty, ~fetch, s, h, k), v),
        Mst.lists_root(~ty, ~fetch, s, h, k, v)
      )
    )
  )

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

def Mst.whole(ty, fetch):
  (
    s => p => {==},
    +s => +h => +bs => +e => (
      +k => +m => +p => (
        Mst.final_root(~ty, ~fetch, s, h, k)(Mst.final_list(~ty, ~fetch, Mst.depth(), s, Mst.root(h), bs, k)(e)),
        (Mst.put_some(~ty, ~fetch, s, h, bs, k, m)(e), Mst.range_some(~ty, ~fetch, Mst.depth(), s, p, Mst.root(h), bs)(e))
      ),
      +h2 => +bs2 => e2 => Mst.diff_whole(~ty, ~fetch, s, h, h2, bs, bs2)(e)(e2)
    )
  )

# a write keeps a whole tree whole
law Mst.keeps_whole:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.Kept(S, fetch, grows, Mst.ops(~S, ~fetch))

# a listing stays, in a depot that keeps what it holds
law Mst.ranges_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.RangeFinal(S, grows, Mst.ops(~S, ~fetch))

# a difference stays, in a depot that keeps what it holds
law Mst.diffs_final:
  for ~S: Data
  for ~fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>
  for ~grows: S -> S -> Bool
  for ~kept: Depots.Depot.Keeps(S, fetch, grows)
  Laws.DiffFinal(S, grows, Mst.ops(~S, ~fetch))
