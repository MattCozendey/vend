import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/shared.bend as Shared
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./files.bend as Files
import ../shared/format.bend as Formats
import ../spec.bend as Spec
import ../types.bend as Types

# Content
# -------
# The content of a version is read from the versions of its line: what the
# version before held, changed by the request of the version. A move and a
# merge read a version of another line, so a read goes from line to line, at
# most as many times as the node holds facts (Facts.fuel).

# Parents
# -------

# the version that the request r takes from another line, with the pinned
# version from: where a move points, or what a merge merges
def Request.takes(r: Spec.Request, from: Nat) -> Maybe<&2, Spec.Point>:
  match r:
    case Spec.Request.Move{b, t, v}:
      Some{Spec.Point{t, v}}
    case Spec.Request.Merge{f, x}:
      Some{Spec.Point{f, from}}
    case _:
      None{}

# the version that the entry e takes from another line
def Entry.takes(e: Types.Entry) -> Maybe<&2, Spec.Point>:
  match e:
    case Types.Entry{Types.Pick{Types.Ask{i, n, r}, Types.Pins{era, from, base, ours, theirs}}, k}:
      Request.takes(r, from)

# the versions that version k of the line c, the entry e, comes from
def Entry.parents(c: Ledgers.Line, k: Nat, e: Types.Entry) -> List<&2, Spec.Point>:
  match k:
    case 0n:
      []
    case 1n+j:
      Spec.Point{c, j} <> Shared.Maybe.cons(Spec.Point, Entry.takes(e), [])

# the point m, or version 0 of the line c
def Point.or(c: Ledgers.Line, m: Maybe<&2, Spec.Point>) -> Spec.Point:
  match m:
    case None{}:
      Spec.Point{c, 0n}
    case Some{x}:
      x

# the request r is a merge
def Request.is_merge(r: Spec.Request) -> Bool:
  match r:
    case Spec.Request.Merge{f, x}:
      True{}
    case _:
      False{}

# the base that the entry e pins, when e is a merge
def Entry.base(e: Types.Entry) -> Maybe<&2, Spec.Point>:
  match e:
    case Types.Entry{Types.Pick{Types.Ask{i, n, r}, Types.Pins{era, from, base, ours, theirs}}, k}:
      Shared.Maybe.when(Spec.Point, Request.is_merge(r), u => base)

# Ways
# ----
# A merge pins its base, and a way back to it from each side: points, each
# reached from the one before by going down its line, or by the version that
# it takes from another line. A node checks the ways; it does not search.

# the point w is reached in one hop from version k of the line c, the entry m
# if the node holds it: w is that version or an older one of c, or the version
# that the entry takes
def Way.hop.of(c: Ledgers.Line, k: Nat, +w: Spec.Point, m: Maybe<&2, Types.Entry>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      Bool.or(
        Bool.and(Ledgers.Line.is_eq(Spec.Point.line(w), c), Nat.is_le(Spec.Point.n(w), k)),
        Shared.Maybe.is_eq(~Spec.Point, ~Spec.Point.is_eq, Entry.takes(e), Some{w})
      )

# the point w is reached in one hop from version k of the line c
def Way.hop(+s: Facts.Plain(), +c: Ledgers.Line, +k: Nat, w: Spec.Point) -> Bool:
  Way.hop.of(c, k, w, Lines.Line.at(s, c, k))

# ws is a way from version k of the line c back to the point a
def Way.ok(
  +s: Facts.Plain(),
  +a: Spec.Point,
  ws: List<&2, Spec.Point>,
  +c: Ledgers.Line,
  +k: Nat
) -> Bool:
  match ws:
    case Nil{}:
      Spec.Point.is_eq(a, Spec.Point{c, k})
    case Con{+w, rest}:
      Bool.and(Way.hop(s, c, k, w), Way.ok(s, a, rest, Spec.Point.line(w), Spec.Point.n(w)))

# the ways ours and theirs lead to the base m, if any, from version j of the
# line c and from the point t
def Merge.fits.of(
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Spec.Point>,
  ours: List<&2, Spec.Point>,
  theirs: List<&2, Spec.Point>,
  t: Spec.Point
) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+a}:
      +t = t
      Bool.and(Way.ok(s, a, ours, c, j), Way.ok(s, a, theirs, Spec.Point.line(t), Spec.Point.n(t)))

# the ways that the entry e pins to its base
def Entry.ours(e: Types.Entry) -> List<&2, Spec.Point>:
  match e:
    case Types.Entry{Types.Pick{a, Types.Pins{era, from, base, ours, theirs}}, k}:
      ours

# the ways that the entry e pins from the version that it takes to its base
def Entry.theirs(e: Types.Entry) -> List<&2, Spec.Point>:
  match e:
    case Types.Entry{Types.Pick{a, Types.Pins{era, from, base, ours, theirs}}, k}:
      theirs

# the entry e, version 1+j of the line c, pins a base that both merged
# versions come from, or none
def Merge.fits(+s: Facts.Plain(), +c: Ledgers.Line, +j: Nat, +e: Types.Entry) -> Bool:
  Merge.fits.of(s, c, j, Entry.base(e), Entry.ours(e), Entry.theirs(e), Point.or(c, Entry.takes(e)))

# Merges
# ------

# acc with the merge m of the path p, when it does not clash
def Merge.put(
  acc: Files.Files(),
  +p: String,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Files.Files():
  match m:
    case None{}:
      acc
    case Some{x}:
      Files.Files.set(acc, p, x)

# the merge of the path p, from the base b, ours o and theirs t
def Merge.at(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Formats.Format.merge(p, Files.Files.get(b, p), Files.Files.get(o, p), Files.Files.get(t, p))

# acc with the merge of each of the paths ps that does not clash
def Merge.fold(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>,
  acc: Files.Files()
) -> Files.Files():
  match ps:
    case Nil{}:
      acc
    case Con{+p, rest}:
      Merge.fold(b, o, t, rest, Merge.put(acc, p, Merge.at(b, o, t, p)))

# the paths that b, o or t hold
def Merge.paths(b: Files.Files(), o: Files.Files(), t: Files.Files()) -> List<&2, String>:
  List.append(
    &2,
    String,
    Files.Files.paths(b),
    List.append(&2, String, Files.Files.paths(o), Files.Files.paths(t))
  )

# the merge of ours o and theirs t, two changes of the base b: each path
# merged in its format; a path that clashes stays as ours
def Merge.files(+b: Files.Files(), +o: Files.Files(), +t: Files.Files()) -> Files.Files():
  Merge.fold(b, o, t, Merge.paths(b, o, t), o)

# the paths among ps that clash
def Merge.clashes.go(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ps: List<&2, String>
) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.filter.put(
        String,
        p,
        Merge.clashes.go(b, o, t, rest),
        Maybe.is_none(&2, Maybe<&2, List<&2, U32>>, Merge.at(b, o, t, p))
      )

# the paths that clash in the merge of o and t from b
def Merge.clashes(+b: Files.Files(), +o: Files.Files(), +t: Files.Files()) -> List<&2, String>:
  Merge.clashes.go(b, o, t, Merge.paths(b, o, t))

# The content of a version
# ------------------------

# the merge of ours and theirs from base, when the merge fits and the node
# holds the three
def Merge.of(
  fits: Bool,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match fits ours theirs base:
    case True{} Some{o} Some{t} Some{b}:
      Some{Merge.files(b, o, t)}
    case _ _ _ _:
      None{}

# the content t with the words w at the path p
def Content.write(
  +p: String,
  w: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Files.Files.set(t, p, w)}

# the content after the request r: prev is the content before, other the
# content that r takes from another line, base the content of the base of a
# merge, and fits says that the merge fits
def Content.apply(
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match r:
    case Spec.Request.Write{b, p, w}:
      Content.write(p, w, prev)
    case Spec.Request.Resolve{m, p, w}:
      Content.write(p, w, prev)
    case Spec.Request.Move{b, t, v}:
      other
    case Spec.Request.Merge{f, x}:
      Merge.of(fits, prev, other, base)
    case _:
      prev

# the content of a version, the entry m if the node holds it
def Content.next(
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Content.apply(Lines.Ask.request(Lines.Entry.ask(e)), fits, prev, other, base)

# the content of version 0, the entry m if the node holds it: nothing yet
def Content.first(m: Maybe<&2, Types.Entry>) -> Maybe<&2, Files.Files()>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{Files.Files.new()}

# the point that the entry m, if any, takes; else version 0 of the line c
def Entry.taken(c: Ledgers.Line, m: Maybe<&2, Types.Entry>) -> Spec.Point:
  match m:
    case None{}:
      Spec.Point{c, 0n}
    case Some{e}:
      Point.or(c, Entry.takes(e))

# the base that the entry m, if any, pins; else version 0 of the line c, which
# holds nothing
def Entry.based(c: Ledgers.Line, m: Maybe<&2, Types.Entry>) -> Spec.Point:
  match m:
    case None{}:
      Spec.Point{c, 0n}
    case Some{e}:
      Point.or(c, Entry.base(e))

# the merge that the entry m, if any, is fits
def Entry.fits(+s: Facts.Plain(), +c: Ledgers.Line, +j: Nat, m: Maybe<&2, Types.Entry>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      Merge.fits(s, c, j, e)

# the content of version k of the line c in the facts s, read through at most
# fuel versions (nothing while the node does not hold enough)
def Content.at(
  +fuel: Nat,
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Maybe<&2, Files.Files()>:
  match fuel k:
    case 0n _:
      None{}
    case 1n+f 0n:
      Content.first(Lines.Line.at(s, c, 0n))
    case 1n+f 1n+j:
      +e = Lines.Line.at(s, c, 1n+j)
      +t = Entry.taken(c, e)
      +a = Entry.based(c, e)
      Content.next(
        e,
        Entry.fits(s, c, j, e),
        Content.at(f, s, c, j),
        Content.at(f, s, Spec.Point.line(t), Spec.Point.n(t)),
        Content.at(f, s, Spec.Point.line(a), Spec.Point.n(a))
      )

# the content of version k of the line c in the facts s
def Content.of(+s: Facts.Plain(), +c: Ledgers.Line, +k: Nat) -> Maybe<&2, Files.Files()>:
  Content.at(Facts.Facts.fuel(s), s, c, k)

# the words at the path p of the content m
def Content.get(m: Maybe<&2, Files.Files()>, +p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Files.Files.get(t, p)}

# the words of the resource at the path p in version k of the line c
def Content.read(
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Content.get(Content.of(s, c, k), p)
