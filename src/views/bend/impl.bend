import Base
import ../../graph/spec.bend as Graph
import ../../shared/bools.bend as Bools
import ../shared.bend as Views
import ../text/impl.bend as TextImpl
import ../text/spec.bend as Text
import ./spec.bend as Spec

# Diff, patch and merge item by item, through the views' shared sequence
# diff and merge. Two sides that change one keyed item differently merge
# its three texts line by line; two sides that insert at one place get one
# order whichever side is which.

# the document of the text of UTF-8 bytes, if they are UTF-8
def Bend.module_of(m: Maybe<&2, String>) -> Maybe<&2, Spec.Module>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Some{Spec.Module{Spec.Bend.split(s)}}

def Spec.Bend.decode(b):
  Bend.module_of(Text.Text.decode(b))

# the item edits of steps
def Bend.edits(hs: List<&2, Views.Hunk<Spec.Item>>) -> List<&2, Spec.ItemEdit>:
  match hs:
    case Nil{}:
      Nil{}
    case Con{Views.Hunk{s, d, i}, t}:
      Spec.ItemEdit{s, d, i} <> Bend.edits(t)

# the steps of item edits
def Bend.steps(es: List<&2, Spec.ItemEdit>) -> List<&2, Views.Hunk<Spec.Item>>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Spec.ItemEdit{s, d, i}, t}:
      Views.Hunk{s, d, i} <> Bend.steps(t)

# the document of items, if there are items
def Bend.of_items(m: Maybe<&2, List<&2, Spec.Item>>) -> Maybe<&2, Spec.Module>:
  match m:
    case None{}:
      None{}
    case Some{items}:
      Some{Spec.Module{items}}

def Spec.Bend.diff(a, b):
  hs = Views.Seq.diff(~Spec.Item, ~Spec.Item.is_eq, Spec.Module.items(a), Spec.Module.items(b))
  Bend.edits(Views.Seq.steps(~Spec.Item, hs, 0n, 0n))

def Spec.Bend.patch(d, es):
  Bend.of_items(Views.Seq.patch(~Spec.Item, Bend.steps(es), Some{Spec.Module.items(d)}))

# Settling a collision
# --------------------

# the hunk that keeps the item kind and name of the base with the merged
# text t, if the texts merged
def Bend.retext(
  k: Spec.ItemKind,
  n: String,
  s: Nat,
  m: Maybe<&2, String>
) -> Maybe<&2, Views.Hunk<Spec.Item>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Views.Hunk{s, 1n, [Spec.Keyed{k, n, t}]}}

# both sides replace the base item b with one item of its key: merge the
# three texts line by line
def Bend.one(
  b: Maybe<&2, Spec.Item>,
  xs: List<&2, Spec.Item>,
  ys: List<&2, Spec.Item>,
  s: Nat
) -> Maybe<&2, Views.Hunk<Spec.Item>>:
  match b xs ys:
    case Some{
      Spec.Keyed{+k, +n, bt}
    } Con{Spec.Keyed{k1, n1, xt}, Nil{}} Con{Spec.Keyed{k2, n2, yt}, Nil{}}:
      same = Bool.and(
        Bool.and(Spec.ItemKind.is_eq(k, k1), Spec.ItemKind.is_eq(k, k2)),
        Bool.and(String.eq(n, n1), String.eq(n, n2))
      )
      Bools.Bool.when(
        Maybe<&2, Views.Hunk<Spec.Item>>,
        same,
        u => Bend.retext(k, n, s, Text.Text.merge(bt, xt, yt)),
        u => None{}
      )
    case _ _ _:
      None{}

# some item of xs mentions a name that some item of ys defines
def Bend.uses(xs: List<&2, Spec.Item>, +ys: List<&2, Spec.Item>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      here = Graph.Keys.meet(Spec.Bend.runs(Spec.Item.text(x)), Spec.Items.names(ys))
      List.any.if(u => Bend.uses(t, ys), here)

# the first of names, or ""
def Bend.first(names: List<&2, String>) -> String:
  match names:
    case Nil{}:
      ""
    case Con{n, t}:
      n

# lt for LT, gt for GT, eq for EQ
def Bend.pick(
  c: Cmp,
  lt: Maybe<&2, Views.Hunk<Spec.Item>>,
  gt: Maybe<&2, Views.Hunk<Spec.Item>>,
  eq: Maybe<&2, Views.Hunk<Spec.Item>>
) -> Maybe<&2, Views.Hunk<Spec.Item>>:
  match c:
    case LT{}:
      lt
    case EQ{}:
      eq
    case GT{}:
      gt

# the hunk of two insertions xs and ys at s, in one order whichever side
# is which: a list that uses a name the other defines goes after it; else
# the list whose first name comes first, then the one whose text comes
# first; two different lists with the same first name and text clash
def Bend.order(
  +xs: List<&2, Spec.Item>,
  +ys: List<&2, Spec.Item>,
  +s: Nat
) -> Maybe<&2, Views.Hunk<Spec.Item>>:
  +xy = Bend.uses(xs, ys)
  +yx = Bend.uses(ys, xs)
  +xfirst = {
    Some{Views.Hunk{s, 0n, List.append(&2, Spec.Item, xs, ys)}}: Maybe<&2, Views.Hunk<Spec.Item>>
  }
  +yfirst = {
    Some{Views.Hunk{s, 0n, List.append(&2, Spec.Item, ys, xs)}}: Maybe<&2, Views.Hunk<Spec.Item>>
  }
  by_text = Bend.pick(
    String.order(Spec.Bend.join.go(xs), Spec.Bend.join.go(ys)),
    xfirst,
    yfirst,
    None{}
  )
  by_key = Bend.pick(
    String.order(Bend.first(Spec.Items.names(xs)), Bend.first(Spec.Items.names(ys))),
    xfirst,
    yfirst,
    by_text
  )
  Bools.Bool.when(
    Maybe<&2, Views.Hunk<Spec.Item>>,
    Bool.and(xy, Bool.not(yx)),
    u => yfirst,
    u => Bools.Bool.when(
      Maybe<&2, Views.Hunk<Spec.Item>>,
      Bool.and(yx, Bool.not(xy)),
      v => xfirst,
      v => by_key
    )
  )

# a collision of two different item changes from base: both sides
# replacing one keyed item with one of its key merge its texts; both
# sides inserting at one place get one order; anything else is a clash
def Bend.resolve(
  base: List<&2, Spec.Item>,
  a: Views.Hunk<Spec.Item>,
  b: Views.Hunk<Spec.Item>
) -> Maybe<&2, Views.Hunk<Spec.Item>>:
  match a b:
    case Views.Hunk{+s1, +d1, +i1} Views.Hunk{s2, +d2, +i2}:
      +here = Nat.is_eq(s1, s2)
      Bools.Bool.when(
        Maybe<&2, Views.Hunk<Spec.Item>>,
        Bool.and(here, Bool.and(Nat.is_eq(d1, 1n), Nat.is_eq(d2, 1n))),
        u => Bend.one(List.get(&2, Spec.Item, base, s1), i1, i2, s1),
        u => Bools.Bool.when(
          Maybe<&2, Views.Hunk<Spec.Item>>,
          Bool.and(here, Bool.and(Nat.is_eq(d1, 0n), Nat.is_eq(d2, 0n))),
          v => Bend.order(i1, i2, s1),
          v => None{}
        )
      )

def Spec.Bend.merge(base, x, y):
  items = Views.Seq.merge(
    ~Spec.Item,
    ~Spec.Item.is_eq,
    ~Bend.resolve,
    Spec.Module.items(base),
    Spec.Module.items(x),
    Spec.Module.items(y)
  )
  Bend.of_items(items)
