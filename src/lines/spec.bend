import Base
import ../history/spec.bend as History
import ../shared.bend as Shared

# A line: a named cursor over the history of one space, like a git branch
# but per resource. For each path it holds the heads that a working copy on
# this line follows. Writes on one line never block writes on another; the
# two simply fork the resource in the history. Moving a line forward is the
# compare-and-swap: the writer names the heads it saw, and the new node must
# descend from them. A merge is a node with several parents, advanced onto
# one line.

# A line of the space: its name, and the heads of each path by the path.
type Line is Data:
  Line{space: String, name: String, heads: Shared.Table<List<&2, Shared.Bytes()>>}

# a line with no heads yet
def Line.new(space: String, name: String) -> Line:
  Line{space, name, Shared.Table.new(List<&2, Shared.Bytes()>)}

# the heads that l follows for the resource n: none when l has not
# reached it yet; a resource of another space has none on l
def Line.heads(l: Line, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  match l n:
    case Line{sp, nm, hs} Shared.Name{s, p}:
      hs = hs
      Shared.Bool.when(
        List<&2, Shared.Bytes()>,
        String.eq(sp, s),
        u => Maybe.default(
          &2,
          List<&2, Shared.Bytes()>,
          Shared.Table.get(List<&2, Shared.Bytes()>, hs, p),
          []
        ),
        u => []
      )

# every id of xs is a parent of the node v
def Line.descends(xs: List<&2, Shared.Bytes()>, +v: History.Node) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      List.all.if(u => Line.descends(t, v), History.Ids.has(History.Node.parents(v), x))

# the found node may follow expect for n
def Line.fits.of(
  v: Maybe<&2, History.Node>,
  n: Shared.Name,
  expect: List<&2, Shared.Bytes()>
) -> Bool:
  match v:
    case None{}:
      False{}
    case Some{+w}:
      same = String.eq(Shared.Name.show(History.Node.name(w)), Shared.Name.show(n))
      List.all.if(u => Line.descends(expect, w), same)

# the node x of h may follow the heads expect of n: it is a node of n, and
# every id of expect is one of its parents
def Line.fits(
  h: History.History,
  n: Shared.Name,
  expect: List<&2, Shared.Bytes()>,
  x: Shared.Bytes()
) -> Bool:
  Line.fits.of(History.History.get(h, x), n, expect)

# Why a line refused to move: the heads it follows now for the resource.
type Refused is Data:
  Refused{now: List<&2, Shared.Bytes()>}

# l with the node x of h as the one head of n; refused unless expect is
# the heads that l follows for n and x is a node of n in h that descends
# from them
law Line.advance:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  Result<&2, &2, Refused, Line>

# Laws
# ----

# a line refuses exactly when the writer did not see its heads, or the node
# does not fit them
law advance_refused:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  {
    Result.is_fail(
      &2,
      &2,
      Refused,
      Line,
      Line.advance(l, h, n, expect, x)
    )
      == Bool.not(
        Bool.and(History.Ids.is_eq(expect, Line.heads(l, n)), Line.fits(h, n, expect, x))
      ): Bool
  }

# after a line moves, the node is the one head of its resource on it
law advance_head:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  for k: Line
  for a: {Line.advance(l, h, n, expect, x) == Done{k}: Result<&2, &2, Refused, Line>}
  {Line.heads(k, n) == [x]: List<&2, Shared.Bytes()>}

# moving a line touches only the heads of its own resource
law advance_frames:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  for k: Line
  for m: Shared.Name
  for a: {Line.advance(l, h, n, expect, x) == Done{k}: Result<&2, &2, Refused, Line>}
  for d: {String.eq(Shared.Name.show(m), Shared.Name.show(n)) == False{}: Bool}
  {Line.heads(k, m) == Line.heads(l, m): List<&2, Shared.Bytes()>}

# a line only moves forward: its new head has every old head as a parent
law advance_descends:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  for k: Line
  for p: Shared.Bytes()
  for v: History.Node
  for a: {Line.advance(l, h, n, expect, x) == Done{k}: Result<&2, &2, Refused, Line>}
  for o: {History.Ids.has(Line.heads(l, n), p) == True{}: Bool}
  for g: {History.History.get(h, x) == Some{v}: Maybe<&2, History.Node>}
  {History.Ids.has(History.Node.parents(v), p) == True{}: Bool}
