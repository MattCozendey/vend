import Base
import ../shared.bend as Shared
import ./spec.bend as Spec

# Conditions as reduced ordered BDDs. Atoms are ordered by String.order of
# their names: a node tests an atom that comes before every atom below it.
# A node whose two children are equal is never made, and equal nodes share
# one id (hash-consing), so two conditions with the same meaning give the
# same BDD, and Cond.canon reads it back the same way. Cond.sat reads a
# path to Always off the BDD; a plain conjunction of literals skips the BDD.

# BDDs
# ----

# A node: test atom v; go to lo when it does not hold, to hi when it does.
# Ids 0 and 1 are the leaves Never and Always; a node's id is 2 or more.
type Node is Data:
  Node{v: String, lo: U32, hi: U32}

# The nodes of one build. nodes: each node by its id's text. ids: each
# node's id by its key (so equal nodes get one id). memo: the result of
# each operation already done, by the operation's key. next: the next
# free id. Tables are memo tables: an operation on the same ids is done
# once.
type Bdds is Data:
  Bdds{nodes: Shared.Table<Node>, ids: Shared.Table<U32>, memo: Shared.Table<U32>, next: U32}

# A build step: the nodes after it, and the id it made.
type Got is Data:
  Got{bdds: Bdds, id: U32}

# The two binary operations.
type Op is Data:
  OpAnd{}
  OpOr{}

# nodes with none made yet
def Bdds.new() -> Bdds:
  Bdds{Shared.Table.new(Node), Shared.Table.new(U32), Shared.Table.new(U32), 2}

# the node with id x (x is 2 or more)
def Bdds.node.of(m: Maybe<&2, Node>) -> Node:
  match m:
    case None{}:
      Node{"", 0, 0}
    case Some{n}:
      n

# the node with id x
def Bdds.node(b: Bdds, x: U32) -> Node:
  match b:
    case Bdds{ns, ids, ms, n}:
      Bdds.node.of(Shared.Table.get(Node, ns, U32.show(x)))

# the key of a node: its children, then its atom; the numbers hold no ','
# so the key names one node
def Node.key(v: String, lo: U32, hi: U32) -> String:
  String.concat([U32.show(lo), ",", U32.show(hi), ",", v])

# the id stored under key in the node keys of b
def Bdds.memo.ids(b: Bdds, key: String) -> Maybe<&2, U32>:
  match b:
    case Bdds{ns, ids, ms, n}:
      Shared.Table.get(U32, ids, key)

# the node that was found under key, or a new one with the next id
def Bdds.mk.found(m: Maybe<&2, U32>, b: Bdds, key: String, v: String, lo: U32, hi: U32) -> Got:
  match m b:
    case Some{x} _:
      Got{b, x}
    case None{} Bdds{ns, ids, ms, +n}:
      nodes = Shared.Table.set(Node, ns, U32.show(n), Node{v, lo, hi})
      Got{Bdds{nodes, Shared.Table.set(U32, ids, key, n), ms, (n + 1: U32)}, n}

# the id of the node testing v with children lo and hi: the child itself
# when both are equal, else the one node with that key
def Bdds.mk(+b: Bdds, +v: String, +lo: U32, +hi: U32) -> Got:
  +key = Node.key(v, lo, hi)
  Shared.Bool.when(
    Got,
    U32.is_eq(lo, hi),
    u => Got{b, lo},
    u => Bdds.mk.found(Bdds.memo.ids(b, key), b, key, v, lo, hi)
  )

# the result stored under key in the memo of b
def Bdds.memo.get(b: Bdds, key: String) -> Maybe<&2, U32>:
  match b:
    case Bdds{ns, ids, ms, n}:
      Shared.Table.get(U32, ms, key)

# b with the result x stored under key
def Bdds.memo.set(b: Bdds, key: String, +x: U32) -> Got:
  match b:
    case Bdds{ns, ids, ms, n}:
      Got{Bdds{ns, ids, Shared.Table.set(U32, ms, key, x), n}, x}

# k of the nodes and the id of g
def Got.then(g: Got, k: Bdds -> U32 -> Got) -> Got:
  match g:
    case Got{b, x}:
      k(b, x)

# the result of op on two leaves or a leaf and anything, or None when both
# are nodes
def Op.leaf(op: Op, +x: U32, +y: U32) -> Maybe<&2, U32>:
  match op:
    case OpAnd{}:
      Shared.Bool.when(
        Maybe<&2, U32>,
        Bool.or(U32.is_eq(x, 0), U32.is_eq(y, 0)),
        u => Some{0},
        u => Shared.Bool.when(
          Maybe<&2, U32>,
          U32.is_eq(x, 1),
          v => Some{y},
          v => Shared.Bool.when(
            Maybe<&2, U32>,
            Bool.or(U32.is_eq(y, 1), U32.is_eq(x, y)),
            w => Some{x},
            w => None{}
          )
        )
      )
    case OpOr{}:
      Shared.Bool.when(
        Maybe<&2, U32>,
        Bool.or(U32.is_eq(x, 1), U32.is_eq(y, 1)),
        u => Some{1},
        u => Shared.Bool.when(
          Maybe<&2, U32>,
          U32.is_eq(x, 0),
          v => Some{y},
          v => Shared.Bool.when(
            Maybe<&2, U32>,
            Bool.or(U32.is_eq(y, 0), U32.is_eq(x, y)),
            w => Some{x},
            w => None{}
          )
        )
      )

# the text of op in memo keys
def Op.tag(op: Op) -> String:
  match op:
    case OpAnd{}:
      "&"
    case OpOr{}:
      "|"

# the memo key of op on x and y; both operations commute, so the smaller
# id comes first
def Op.key(op: Op, +x: U32, +y: U32) -> String:
  lo = Bool.pick(U32, U32.is_le(x, y), x, y)
  hi = Bool.pick(U32, U32.is_le(x, y), y, x)
  String.concat([Op.tag(op), U32.show(lo), ",", U32.show(hi)])

# the atom that n tests
def Node.v(n: Node) -> String:
  match n:
    case Node{v, l, h}:
      v

# The atom of a split, and the children of x and y under it.
type Split is Data:
  Split{v: String, x0: U32, x1: U32, y0: U32, y1: U32}

# the split of nodes x and y by the atom that comes first: a node whose
# atom comes later stays whole on both sides
def Bdd.split.by(c: Cmp, nx: Node, ny: Node, +x: U32, +y: U32) -> Split:
  match c nx ny:
    case LT{} Node{vx, lx, hx} n:
      Split{vx, lx, hx, y, y}
    case GT{} n Node{vy, ly, hy}:
      Split{vy, x, x, ly, hy}
    case EQ{} Node{vx, lx, hx} Node{vy, ly, hy}:
      Split{vx, lx, hx, ly, hy}

# the split of the nodes x and y, whose nodes are nx and ny
def Bdd.split(+nx: Node, +ny: Node, x: U32, y: U32) -> Split:
  Bdd.split.by(String.order(Node.v(nx), Node.v(ny)), nx, ny, x, y)

# k of s
def Split.then(s: Split, k: String -> U32 -> U32 -> U32 -> U32 -> Got) -> Got:
  match s:
    case Split{v, x0, x1, y0, y1}:
      k(v, x0, x1, y0, y1)

# Got{b, x} when r is Some{x}, else k(b)
def Bdd.or_else(r: Maybe<&2, U32>, b: Bdds, k: Bdds -> Got) -> Got:
  match r:
    case Some{x}:
      Got{b, x}
    case None{}:
      k(b)

# the result stored under key in b, else k(b)
def Bdd.apply.memo(+b: Bdds, key: String, k: Bdds -> Got) -> Got:
  Bdd.or_else(Bdds.memo.get(b, key), b, k)

# op of the BDDs x and y in b; fuel bounds the depth (each level tests a
# later atom, so the number of distinct atoms is enough)
def Bdd.apply(fuel: Nat, +op: Op, b: Bdds, +x: U32, +y: U32) -> Got:
  match fuel:
    case 0n:
      Got{b, 0}
    case 1n+(+f):
      +key = Op.key(op, x, y)
      Bdd.or_else(
        Op.leaf(op, x, y),
        b,
        b0 => Bdd.apply.memo(
          b0,
          key,
          +b1 => Split.then(
            Bdd.split(Bdds.node(b1, x), Bdds.node(b1, y), x, y),
            v => x0 => x1 => y0 => y1 => Got.then(
              Bdd.apply(f, op, b1, x0, y0),
              b2 => r0 => Got.then(
                Bdd.apply(f, op, b2, x1, y1),
                b3 => r1 => Got.then(Bdds.mk(b3, v, r0, r1), b4 => r => Bdds.memo.set(b4, key, r))
              )
            )
          )
        )
      )

# k of the atom and children of node n, with the nodes b
def Bdd.not.node(n: Node, b: Bdds, k: String -> U32 -> U32 -> Got) -> Got:
  match n:
    case Node{v, lo, hi}:
      k(v, lo, hi)

# the negation of the BDD x in b; fuel bounds the depth
def Bdd.not(fuel: Nat, b: Bdds, +x: U32) -> Got:
  match fuel:
    case 0n:
      Got{b, 0}
    case 1n+(+f):
      +key = String.append("!", U32.show(x))
      leaf = Shared.Bool.when(
        Maybe<&2, U32>,
        U32.is_eq(x, 0),
        u => Some{1},
        u => Shared.Bool.when(Maybe<&2, U32>, U32.is_eq(x, 1), v => Some{0}, v => None{})
      )
      Bdd.or_else(
        leaf,
        b,
        b0 => Bdd.apply.memo(
          b0,
          key,
          +b1 => Bdd.not.node(
            Bdds.node(b1, x),
            b1,
            n => lo => hi => Got.then(
              Bdd.not(f, b1, lo),
              b2 => r0 => Got.then(
                Bdd.not(f, b2, hi),
                b3 => r1 => Got.then(Bdds.mk(b3, n, r0, r1), b4 => r => Bdds.memo.set(b4, key, r))
              )
            )
          )
        )
      )

# Building and reading
# --------------------

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- conditions and their BDDs are small (a few atoms per #if); a fork costs more than it saves
# the number of parts of c: enough fuel for any BDD operation on c, since
# a BDD of c is at most as deep as c names distinct atoms
def Cond.size(c: Spec.Cond) -> Nat:
  match c:
    case Spec.Always{}:
      1n
    case Spec.Never{}:
      1n
    case Spec.Atom{n}:
      1n
    case Spec.Not{x}:
      1n+Cond.size(x)
    case Spec.And{a, b}:
      1n+Nat.add(Cond.size(a), Cond.size(b))
    case Spec.Or{a, b}:
      1n+Nat.add(Cond.size(a), Cond.size(b))
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the BDD of c in b
def Bdd.build(c: Spec.Cond, +fuel: Nat, b: Bdds) -> Got:
  match c:
    case Spec.Always{}:
      Got{b, 1}
    case Spec.Never{}:
      Got{b, 0}
    case Spec.Atom{n}:
      Bdds.mk(b, n, 0, 1)
    case Spec.Not{x}:
      Got.then(Bdd.build(x, fuel, b), b1 => r => Bdd.not(fuel, b1, r))
    case Spec.And{x, y}:
      Got.then(
        Bdd.build(x, fuel, b),
        b1 => rx => Got.then(
          Bdd.build(y, fuel, b1),
          b2 => ry => Bdd.apply(fuel, OpAnd{}, b2, rx, ry)
        )
      )
    case Spec.Or{x, y}:
      Got.then(
        Bdd.build(x, fuel, b),
        b1 => rx => Got.then(
          Bdd.build(y, fuel, b1),
          b2 => ry => Bdd.apply(fuel, OpOr{}, b2, rx, ry)
        )
      )

# k of the hi child, lo child and atom of node n
def Bdd.read.node(n: Node, k: U32 -> U32 -> String -> Spec.Cond) -> Spec.Cond:
  match n:
    case Node{v, lo, hi}:
      k(hi, lo, v)

# k of the hi child, lo child and atom of node n
def Bdd.path.node(
  n: Node,
  k: U32 -> U32 -> String -> Maybe<&2, List<&2, String>>
) -> Maybe<&2, List<&2, String>>:
  match n:
    case Node{v, lo, hi}:
      k(hi, lo, v)

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- conditions and their BDDs are small (a few atoms per #if); a fork costs more than it saves
# the condition of the BDD x in b, as a chain of tests: a node testing v
# reads as (v and its hi part) or (not v and its lo part); fuel bounds the
# depth
def Bdd.read(fuel: Nat, +b: Bdds, +x: U32) -> Spec.Cond:
  match fuel:
    case 0n:
      Spec.Never{}
    case 1n+(+f):
      Shared.Bool.when(
        Spec.Cond,
        U32.is_eq(x, 0),
        u => Spec.Never{},
        u => Shared.Bool.when(
          Spec.Cond,
          U32.is_eq(x, 1),
          v => Spec.Always{},
          v => Bdd.read.node(
            Bdds.node(b, x),
            hi => lo => +n => Spec.Or{
              Spec.And{Spec.Atom{n}, Bdd.read(f, b, hi)},
              Spec.And{Spec.Not{Spec.Atom{n}}, Bdd.read(f, b, lo)}
            }
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# the atoms set true on a path from x to Always in b, or None when x is
# Never; at each node it takes hi unless hi is Never. In a reduced BDD
# every node other than Never reaches Always, so a path exists exactly
# when x is not Never.
def Bdd.path(fuel: Nat, +b: Bdds, +x: U32, +on: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match fuel:
    case 0n:
      None{}
    case 1n+(+f):
      Shared.Bool.when(
        Maybe<&2, List<&2, String>>,
        U32.is_eq(x, 0),
        u => None{},
        u => Shared.Bool.when(
          Maybe<&2, List<&2, String>>,
          U32.is_eq(x, 1),
          v => Some{on},
          v => Bdd.path.node(
            Bdds.node(b, x),
            +hi => lo => n => Shared.Bool.when(
              Maybe<&2, List<&2, String>>,
              U32.is_eq(hi, 0),
              w => Bdd.path(f, b, lo, on),
              w => Bdd.path(f, b, hi, n <> on)
            )
          )
        )
      )

# the condition read back from the BDD g
def Bdd.canon.of(g: Got, fuel: Nat) -> Spec.Cond:
  match g:
    case Got{b, x}:
      Bdd.read(fuel, b, x)

def Spec.Cond.canon(c):
  +c = c
  +fuel = {1n+Cond.size(c): Nat}
  Bdd.canon.of(Bdd.build(c, fuel, Bdds.new()), fuel)

# Satisfiability
# --------------

# The literals of a plain conjunction: the atoms that must hold, the atoms
# that must not, and whether a Never is among them.
type Lits is Data:
  Lits{pos: List<&2, String>, neg: List<&2, String>, never: Bool}

# the literals of both conjunctions, or None when either is not one
def Lits.both(a: Maybe<&2, Lits>, b: Maybe<&2, Lits>) -> Maybe<&2, Lits>:
  match a b:
    case Some{Lits{p1, n1, v1}} Some{Lits{p2, n2, v2}}:
      Some{Lits{List.append(&2, String, p1, p2), List.append(&2, String, n1, n2), Bool.or(v1, v2)}}
    case _ _:
      None{}

# bend-lint: expect-begin bend-lint-rules/performance/missed_fork@hint -- conditions and their BDDs are small (a few atoms per #if); a fork costs more than it saves
# the literals of c when c is a plain conjunction of atoms, negated atoms,
# Always and Never (in any And nesting); None for anything else
def Lits.of(c: Spec.Cond) -> Maybe<&2, Lits>:
  match c:
    case Spec.Always{}:
      Some{Lits{[], [], False{}}}
    case Spec.Never{}:
      Some{Lits{[], [], True{}}}
    case Spec.Atom{n}:
      Some{Lits{[n], [], False{}}}
    case Spec.Not{Spec.Atom{n}}:
      Some{Lits{[], [n], False{}}}
    case Spec.Not{x}:
      None{}
    case Spec.And{a, b}:
      Lits.both(Lits.of(a), Lits.of(b))
    case Spec.Or{a, b}:
      None{}
# bend-lint: expect-end bend-lint-rules/performance/missed_fork@hint

# some atom of xs is in ys
def Lits.meet(xs: List<&2, String>, +ys: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      List.any.if(u => Lits.meet(t, ys), List.contains(~String, ~String.eq, ys, x))

# the answer for a plain conjunction, in linear time per literal: Unsat
# when it holds a Never or an atom both ways, else Holds with exactly the
# atoms that must hold. It gives the same verdict as the BDD: a
# conjunction of literals is false everywhere exactly in those two cases.
def Lits.sat(l: Lits) -> Spec.Sat:
  match l:
    case Lits{+p, n, v}:
      Shared.Bool.when(
        Spec.Sat,
        List.any.if(u => Lits.meet(p, n), v),
        u => Spec.Unsat{},
        u => Spec.Holds{Spec.Config{p}}
      )

# Unsat for no path, else Holds with the path's atoms
def Bdd.sat.path(m: Maybe<&2, List<&2, String>>) -> Spec.Sat:
  match m:
    case None{}:
      Spec.Unsat{}
    case Some{on}:
      Spec.Holds{Spec.Config{on}}

# the answer read off the BDD g: Unsat for Never, else Holds with the atoms
# set true on a path to Always
def Bdd.sat.of(g: Got, fuel: Nat) -> Spec.Sat:
  match g:
    case Got{b, x}:
      Bdd.sat.path(Bdd.path(fuel, b, x, []))

# the fast answer for a conjunction, else the BDD's
def Cond.sat.of(m: Maybe<&2, Lits>, +c: Spec.Cond) -> Spec.Sat:
  match m:
    case Some{l}:
      Lits.sat(l)
    case None{}:
      +fuel = {1n+Cond.size(c): Nat}
      Bdd.sat.of(Bdd.build(c, fuel, Bdds.new()), fuel)

def Spec.Cond.sat(c):
  +c = c
  Cond.sat.of(Lits.of(c), c)
