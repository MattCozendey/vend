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

# n is a resource of the space of l
def Line.owns(l: Line, n: Shared.Name) -> Bool:
  match l n:
    case Line{sp, nm, hs} Shared.Name{s, p}:
      String.eq(sp, s)

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

# l with the node x of h as the one head of n; refused unless n is a
# resource of the space of l, expect is the heads that l follows for n, and
# x is a node of n in h that descends from them
law Line.advance:
  for l: Line
  for h: History.History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  Result<&2, &2, Refused, Line>

# Laws
# ----

# a line refuses exactly when the resource is of another space, the writer
# did not see its heads, or the node does not fit them
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
        Bool.and(
          Line.owns(l, n),
          Bool.and(History.Ids.is_eq(expect, Line.heads(l, n)), Line.fits(h, n, expect, x))
        )
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

# Seen markers
# ------------
# What each agent last saw of each line, so "what changed since I looked"
# is exact and per agent. A marker moves only when its agent catches up.

# What an agent last saw of a line: for each path, the heads it saw then.
type Seen is Data:
  Seen{agent: String, line: String, heads: Shared.Table<List<&2, Shared.Bytes()>>}

# a marker of agent a on the line named ln that has seen nothing
def Seen.new(a: String, ln: String) -> Seen:
  Seen{a, ln, Shared.Table.new(List<&2, Shared.Bytes()>)}

# the name of the line of s
def Seen.line(s: Seen) -> String:
  match s:
    case Seen{a, ln, hs}:
      ln

# the name of l
def Line.name(l: Line) -> String:
  match l:
    case Line{sp, nm, hs}:
      nm

# s caught up with l: it has seen every head that l follows now; a marker
# of another line does not move
def Seen.update(s: Seen, l: Line) -> Seen:
  match s l:
    case Seen{+a, +ln, hs} Line{sp, nm, lh}:
      Shared.Bool.when(Seen, String.eq(ln, nm), u => Seen{a, ln, lh}, u => Seen{a, ln, hs})

# the heads in the table t for the path p: none when t has no row for it
def Heads.at(t: Shared.Table<List<&2, Shared.Bytes()>>, p: String) -> List<&2, Shared.Bytes()>:
  Maybe.default(&2, List<&2, Shared.Bytes()>, Shared.Table.get(List<&2, Shared.Bytes()>, t, p), [])

# the paths of ps whose heads in lh differ from those in seen
def Seen.unseen.go(
  ps: List<&2, String>,
  +lh: Shared.Table<List<&2, Shared.Bytes()>>,
  +seen: Shared.Table<List<&2, Shared.Bytes()>>
) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, +t}:
      same = History.Ids.is_eq(Heads.at(lh, p), Heads.at(seen, p))
      Shared.Bool.when(
        List<&2, String>,
        same,
        u => Seen.unseen.go(t, lh, seen),
        u => p <> Seen.unseen.go(t, lh, seen)
      )

# the names of the paths ps in the space sp
def Seen.names(+sp: String, ps: List<&2, String>) -> List<&2, Shared.Name>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Shared.Name{sp, p} <> Seen.names(sp, t)

# the resources of l whose heads changed since s saw them
def Seen.unseen(s: Seen, l: Line) -> List<&2, Shared.Name>:
  match s l:
    case Seen{a, ln, hs} Line{sp, nm, +lh}:
      Seen.names(sp, Seen.unseen.go(Shared.Table.keys(List<&2, Shared.Bytes()>, lh), lh, hs))

# The markers of every agent on every line.
type SeenBook is Data:
  SeenBook{rows: Shared.Table<Seen>}

# no markers yet
def SeenBook.new() -> SeenBook:
  SeenBook{Shared.Table.new(Seen)}

# the key of the marker of agent a on the line named ln: the length of a
# first, so no two pairs share a key
def SeenBook.key(a: String, ln: String) -> String:
  +a = a
  String.concat([Nat.show(String.length(a)), ":", a, ln])

# the marker of agent a on the line named ln
def SeenBook.get(m: SeenBook, +a: String, +ln: String) -> Seen:
  match m:
    case SeenBook{rs}:
      Maybe.default(&2, Seen, Shared.Table.get(Seen, rs, SeenBook.key(a, ln)), Seen.new(a, ln))

# m with the marker of agent a on l caught up with l
def SeenBook.update(m: SeenBook, +a: String, +l: Line) -> SeenBook:
  match m:
    case SeenBook{+rs}:
      +ln = Line.name(l)
      SeenBook{
        Shared.Table.set(
          Seen,
          rs,
          SeenBook.key(a, ln),
          Seen.update(SeenBook.get(SeenBook{rs}, a, ln), l)
        )
      }

# right after an agent catches up with a line, nothing of it is unseen
law seen_caught_up:
  for s: Seen
  for l: Line
  for h: {String.eq(Seen.line(s), Line.name(l)) == True{}: Bool}
  {Seen.unseen(Seen.update(s, l), l) == []: List<&2, Shared.Name>}

# catching up moves only that agent's marker on that line
law seen_frames:
  for m: SeenBook
  for a: String
  for l: Line
  for b: String
  for ln: String
  for d: {Bool.and(String.eq(b, a), String.eq(ln, Line.name(l))) == False{}: Bool}
  {SeenBook.get(SeenBook.update(m, a, l), b, ln) == SeenBook.get(m, b, ln): Seen}

# Marks
# -----
# A mark is a named snapshot of a line, with a message and an author: the
# heads the line followed for each resource when it was made. Merges and
# diffs may take a mark wherever they take a line's heads. A line moves on;
# its marks do not.

# A mark: the line it was made on, its name, why (message), who made it,
# and the line as it was then (its space and its heads).
type Mark is Data:
  Mark{line: String, name: String, message: String, author: History.Author, at: Line}

# the mark named name of l as it is now, made by author a with message msg
def Mark.of(+l: Line, name: String, msg: String, a: History.Author) -> Mark:
  Mark{Line.name(l), name, msg, a, l}

# the heads that the line of m followed for the resource n when m was made
def Mark.heads(m: Mark, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  match m:
    case Mark{ln, nm, msg, a, l}:
      Line.heads(l, n)

# a mark holds the heads its line followed for every resource when it was
# made
law mark_heads:
  for l: Line
  for nm: String
  for msg: String
  for a: History.Author
  for n: Shared.Name
  {Mark.heads(Mark.of(l, nm, msg, a), n) == Line.heads(l, n): List<&2, Shared.Bytes()>}

# moving a line does not move its marks: a mark made before an advance still
# gives the heads from before it, not the line's new ones
law mark_fixed:
  for l: Line
  for h: History.History
  for r: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for x: Shared.Bytes()
  for k: Line
  for nm: String
  for msg: String
  for a: History.Author
  for n: Shared.Name
  for d: {Line.advance(l, h, r, expect, x) == Done{k}: Result<&2, &2, Refused, Line>}
  {Mark.heads(Mark.of(l, nm, msg, a), n) == Line.heads(l, n): List<&2, Shared.Bytes()>}
