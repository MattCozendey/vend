import Base
import ../hash/spec.bend as Hash
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/tables.bend as Tables
import ./spec.bend as Spec

# First versions: an edit reads, splices and writes everything again, and a
# diff trims the common prefix and suffix of the two item lists. The laws
# pin what both answer, so faster tree-aware versions can replace them.

# Equality
# --------

# xs and ys are the same items
def Items.is_eq(xs: List<&2, Octets.Bytes()>, ys: List<&2, Octets.Bytes()>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Items.is_eq(xt, yt), Octets.Bytes.is_eq(x, y))
    case _ _:
      False{}

# xs and ys are the same references
def Refs.is_eq(xs: List<&2, Spec.Ref>, ys: List<&2, Spec.Ref>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{Spec.Ref{xh, xc}, xt} Con{Spec.Ref{yh, yc}, yt}:
      same = Bool.and(Octets.Bytes.is_eq(xh, yh), Nat.is_eq(xc, yc))
      List.all.if(u => Refs.is_eq(xt, yt), same)
    case _ _:
      False{}

def Spec.Node.is_eq(a, b):
  match a b:
    case Spec.Leaf{xs} Spec.Leaf{ys}:
      Items.is_eq(xs, ys)
    case Spec.Branch{xs} Spec.Branch{ys}:
      Refs.is_eq(xs, ys)
    case _ _:
      False{}

# Writing
# -------

# A node with its reference, so its hash is computed once.
type Built is Data:
  Built{node: Spec.Node, ref: Spec.Ref}

# each node with its reference
def Built.of_all(ns: List<&2, Spec.Node>) -> List<&2, Built>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      Built{n, Spec.Node.ref(n)} <> Built.of_all(t)

# the references of built nodes
def Built.refs(bs: List<&2, Built>) -> List<&2, Spec.Ref>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{Built{n, r}, t}:
      r <> Built.refs(t)

# every node above refs, with the root; the same steps as Spec.Tree.up
def Built.up(
  fuel: Nat,
  refs: List<&2, Spec.Ref>,
  acc: List<&2, Built>
) -> List<&2, Built>
  & Spec.Ref:
  match fuel refs:
    case _ Con{r, Nil{}}:
      (acc, r)
    case 0n rs:
      +top = {Spec.Branch{rs}: Spec.Node}
      +r = Spec.Node.ref(top)
      (Built{top, r} <> acc, r)
    case 1n+f rs:
      +level = Built.of_all(Spec.Tree.up.level(rs))
      Built.up(f, Built.refs(level), List.append(&2, Built, level, acc))

# every node of items, with the root
def Built.tree(items: List<&2, Octets.Bytes()>) -> List<&2, Built> & Spec.Ref:
  +leaves = Built.of_all(Spec.Tree.leaves(items))
  Built.up(64n, Built.refs(leaves), leaves)

# s with n at its hash, or the collision with the node already there
def Store.put.at(
  s: Spec.Store,
  key: String,
  +n: Spec.Node,
  old: Maybe<&2, Spec.Node>
) -> Result<&2, &2, Spec.Problem, Spec.Store>:
  match s old:
    case Spec.Store{m} None{}:
      Done{Spec.Store{Tables.Table.set(Spec.Node, m, key, n)}}
    case st Some{+o}:
      Bools.Bool.when(
        Result<&2, &2, Spec.Problem, Spec.Store>,
        Spec.Node.is_eq(o, n),
        u => Done{st},
        u => Fail{Spec.Collides{o, n}}
      )

# s with the built node b
def Store.put(+s: Spec.Store, b: Built) -> Result<&2, &2, Spec.Problem, Spec.Store>:
  match b:
    case Built{n, Spec.Ref{+h, c}}:
      key = Hash.Hash.hex(h)
      Store.put.at(s, key, n, Spec.Store.get(s, h))

# the store after r, then the rest of the nodes
def Store.put_all.after(
  r: Result<&2, &2, Spec.Problem, Spec.Store>,
  k: Spec.Store -> Result<&2, &2, Spec.Problem, Spec.Store>
) -> Result<&2, &2, Spec.Problem, Spec.Store>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      k(s)

# s with every built node
def Store.put_all(bs: List<&2, Built>, s: Spec.Store) -> Result<&2, &2, Spec.Problem, Spec.Store>:
  match bs:
    case Nil{}:
      Done{s}
    case Con{b, t}:
      Store.put_all.after(Store.put(s, b), s2 => Store.put_all(t, s2))

# the write that put_all made, with its root
def Store.wrote(
  r: Result<&2, &2, Spec.Problem, Spec.Store>,
  root: Spec.Ref
) -> Result<&2, &2, Spec.Problem, Spec.Wrote>:
  match r:
    case Fail{e}:
      Fail{e}
    case Done{s}:
      Done{Spec.Wrote{s, root}}

# the write of the built tree
def Store.write.of(
  s: Spec.Store,
  t: List<&2, Built> & Spec.Ref
) -> Result<&2, &2, Spec.Problem, Spec.Wrote>:
  (bs, root) = t
  Store.wrote(Store.put_all(bs, s), root)

def Spec.Tree.write(s, items):
  Store.write.of(s, Built.tree(items))

# the write of the edited items, or Missing when they cannot be read
def Store.edit.of(
  s: Spec.Store,
  read: Maybe<&2, List<&2, Octets.Bytes()>>,
  pos: Nat,
  del: Nat,
  ins: List<&2, Octets.Bytes()>
) -> Result<&2, &2, Spec.Problem, Spec.Wrote>:
  match read:
    case None{}:
      Fail{Spec.Missing{}}
    case Some{xs}:
      Spec.Tree.write(s, Spec.Items.splice(xs, pos, del, ins))

def Spec.Tree.edit(s, r, pos, del, ins):
  +s = s
  Store.edit.of(s, Spec.Tree.read(s, r), pos, del, ins)

# Diff
# ----

# how many items xs and ys share at their start
def Items.common(xs: List<&2, Octets.Bytes()>, ys: List<&2, Octets.Bytes()>) -> Nat:
  match xs ys:
    case Con{x, xt} Con{y, yt}:
      Bools.Bool.when(Nat, Octets.Bytes.is_eq(x, y), u => 1n+Items.common(xt, yt), u => 0n)
    case _ _:
      0n

# the one splice that turns xs into ys: keep the common start and end
def Items.diff(
  +xs: List<&2, Octets.Bytes()>,
  +ys: List<&2, Octets.Bytes()>
) -> List<&2, Spec.Splice>:
  +nx = List.length(&2, Octets.Bytes(), xs)
  +ny = List.length(&2, Octets.Bytes(), ys)
  +pre = Items.common(xs, ys)
  +room = Nat.sub(Bool.pick(Nat, Nat.is_lt(nx, ny), nx, ny), pre)
  rx = List.reverse(&2, Octets.Bytes(), xs)
  ry = List.reverse(&2, Octets.Bytes(), ys)
  +c = Items.common(rx, ry)
  +suf = Bool.pick(Nat, Nat.is_lt(c, room), c, room)
  ins = List.take(
    &2,
    Octets.Bytes(),
    List.drop(&2, Octets.Bytes(), ys, pre),
    Nat.sub(Nat.sub(ny, pre), suf)
  )
  [Spec.Splice{pre, Nat.sub(Nat.sub(nx, pre), suf), ins}]

# the diff of two reads, or None when either failed
def Store.diff.of(
  a: Maybe<&2, List<&2, Octets.Bytes()>>,
  b: Maybe<&2, List<&2, Octets.Bytes()>>
) -> Maybe<&2, List<&2, Spec.Splice>>:
  match a b:
    case Some{xs} Some{ys}:
      Some{Items.diff(xs, ys)}
    case _ _:
      None{}

def Spec.Tree.diff(s, a, b):
  +s = s
  Store.diff.of(Spec.Tree.read(s, a), Spec.Tree.read(s, b))

def Spec.diff_answers(s, a, b, xs, ys, ha, hb):
  +s = s
  +b = b
  +xs = xs
  %Equal.sym(Maybe<&2, List<&2, Octets.Bytes()>>, Spec.Tree.read.go(64n, s, [a]), Some{xs}, ha) :
    {Maybe.is_some(&2, List<&2, Spec.Splice>, Store.diff.of(_, Spec.Tree.read.go(64n, s, [b]))) == True{} : Bool}
  %Equal.sym(Maybe<&2, List<&2, Octets.Bytes()>>, Spec.Tree.read.go(64n, s, [b]), Some{ys}, hb) :
    {Maybe.is_some(&2, List<&2, Spec.Splice>, Store.diff.of(Some{xs}, _)) == True{} : Bool}
  {==}
