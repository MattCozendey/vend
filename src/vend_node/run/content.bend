import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/shared/crit_order.bend as Orders
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
import ../shared/format.bend as Formats
import ../spec.bend as Spec
import ../types.bend as Types
import ./facts.bend as Facts
import ./files.bend as Files
import ./known.bend as Knowns
import ./lines.bend as Lines

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
def Way.hop(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  w: Spec.Point
) -> Bool:
  Way.hop.of(c, k, w, Knowns.Known.at(kn, s, c, k))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for a way that does not hold, which then costs no more than a way that holds, where both sides run
# ws is a way from version k of the line c back to the point a
def Way.ok(
  +kn: Knowns.Known(),
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
      Bool.and(Way.hop(kn, s, c, k, w), Way.ok(kn, s, a, rest, Spec.Point.line(w), Spec.Point.n(w)))

# the ways ours and theirs lead to the base m, if any, from version j of the
# line c and from the point t
def Merge.fits.of(
  +kn: Knowns.Known(),
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
      Bool.and(
        Way.ok(kn, s, a, ours, c, j),
        Way.ok(kn, s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
def Merge.fits(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +e: Types.Entry
) -> Bool:
  Merge.fits.of(
    kn,
    s,
    c,
    j,
    Entry.base(e),
    Entry.ours(e),
    Entry.theirs(e),
    Point.or(c, Entry.takes(e))
  )

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

# Merges of a few writes
# ----------------------
# When what a merge takes is its base with a few writes, the merge changes
# ours at most at the paths of those writes: a path that theirs left as the
# base stays as ours. A node that holds the state of the line that the merge
# takes from reads the writes from its versions, and merges only their paths.
# merges.bend proves that this is the merge of every path (Merge.files).

# a write: the words at a path (none: no resource)
type Write is Data:
  Write{path: String, words: Maybe<&2, List<&2, U32>>}

# the writes m, if any, after the write of w at the path p
def Write.put(
  p: String,
  w: Maybe<&2, List<&2, U32>>,
  m: Maybe<&2, List<&2, Write>>
) -> Maybe<&2, List<&2, Write>>:
  match m:
    case None{}:
      None{}
    case Some{ws}:
      Some{Write{p, w} <> ws}

# the write of the request r, then the writes that rest gives: none when r
# may change more than one path
def Request.wrote(
  r: Spec.Request,
  rest: Unit -> Maybe<&2, List<&2, Write>>
) -> Maybe<&2, List<&2, Write>>:
  match r:
    case Spec.Request.Start{os}:
      rest(Unit{})
    case Spec.Request.Write{b, p, w}:
      Write.put(p, w, rest(Unit{}))
    case Spec.Request.Merge{f, x}:
      None{}
    case Spec.Request.Resolve{m, p, w}:
      Write.put(p, w, rest(Unit{}))
    case Spec.Request.Mark{b, m, v}:
      rest(Unit{})
    case Spec.Request.Move{b, t, v}:
      None{}
    case Spec.Request.Group{h, g, ms}:
      rest(Unit{})
    case Spec.Request.Own{c, g}:
      rest(Unit{})

# the writes of the first n of the entries es, the oldest first: none when
# one of them may change more than one path, or es has less than n entries
def Writes.of(n: Nat, es: List<&2, Types.Entry>) -> Maybe<&2, List<&2, Write>>:
  match n es:
    case 0n es:
      Some{[]}
    case 1n+d Nil{}:
      None{}
    case 1n+d Con{e, rest}:
      Request.wrote(Lines.Ask.request(Lines.Entry.ask(e)), u => Writes.of(d, rest))

# the writes that make the content of the point t from the content of the
# point a, when both are versions of one line, a is not after t, and the
# table holds the state m of the line
def Merge.hint(
  m: Maybe<&2, Lines.State>,
  t: Spec.Point,
  a: Spec.Point
) -> Maybe<&2, List<&2, Write>>:
  match m t a:
    case None{} t a:
      None{}
    case Some{Lines.State{vs, k}} Spec.Point{tl, +tn} Spec.Point{al, +an}:
      Shared.Maybe.when(
        List<&2, Write>,
        List.all.if(u => Nat.is_le(an, tn), Ledgers.Line.is_eq(al, tl)),
        u => Writes.of(Nat.sub(tn, an), List.drop(&2, Types.Entry, vs, 1n+an))
      )

# the paths of the writes ws
def Writes.paths(ws: List<&2, Write>) -> List<&2, String>:
  match ws:
    case Nil{}:
      []
    case Con{Write{p, w}, rest}:
      p <> Writes.paths(rest)

# the merge of ours o and theirs t from the base b, when t is b with the
# writes ws: only the paths of ws are merged
def Merge.few(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ws: List<&2, Write>
) -> Files.Files():
  Merge.fold(b, o, t, Writes.paths(ws), o)

# the paths among ps that are among cs
def Paths.among(ps: List<&2, String>, +cs: List<&2, String>) -> List<&2, String>:
  match ps:
    case Nil{}:
      []
    case Con{+p, rest}:
      List.filter.put(String, p, Paths.among(rest, cs), List.contains(~String, ~String.eq, cs, p))

# the paths among those that ps gives that are among cs: none when cs is
# empty, and then ps is not read
def Merge.clashes.few.of(cs: List<&2, String>, ps: Unit -> List<&2, String>) -> List<&2, String>:
  match cs:
    case Nil{}:
      []
    case Con{p, rest}:
      Paths.among(ps(Unit{}), p <> rest)

# the paths that clash in the merge of o and t from b, as Merge.clashes
# gives them, when t is b with the writes ws: only the paths of ws are
# merged, and the paths of the three are walked only when one of those
# clashes
def Merge.clashes.few(
  +b: Files.Files(),
  +o: Files.Files(),
  +t: Files.Files(),
  ws: List<&2, Write>
) -> List<&2, String>:
  Merge.clashes.few.of(Merge.clashes.go(b, o, t, Writes.paths(ws)), u => Merge.paths(b, o, t))

# the merge of ours and theirs from base, as Merge.of gives it, when theirs
# is base with the writes ws
def Merge.of.few(
  ws: List<&2, Write>,
  fits: Bool,
  ours: Maybe<&2, Files.Files()>,
  theirs: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match fits ours theirs base:
    case True{} Some{o} Some{t} Some{b}:
      Some{Merge.few(b, o, t, ws)}
    case _ _ _ _:
      None{}

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

# the content after the request r, as Content.apply gives it, when other is
# base with the writes ws
def Content.apply.few(
  ws: List<&2, Write>,
  r: Spec.Request,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match r:
    case Spec.Request.Merge{f, x}:
      Merge.of.few(ws, fits, prev, other, base)
    case Spec.Request.Start{os}:
      prev
    case Spec.Request.Write{b, p, w}:
      Content.write(p, w, prev)
    case Spec.Request.Resolve{m, p, w}:
      Content.write(p, w, prev)
    case Spec.Request.Mark{b, m, v}:
      prev
    case Spec.Request.Move{b, t, v}:
      other
    case Spec.Request.Group{h, g, ms}:
      prev
    case Spec.Request.Own{c, g}:
      prev

# the content of a version, as Content.next gives it: when the writes h that
# make other from base are known, a merge reads only their paths
def Content.quick(
  h: Maybe<&2, List<&2, Write>>,
  m: Maybe<&2, Types.Entry>,
  fits: Bool,
  prev: Maybe<&2, Files.Files()>,
  other: Maybe<&2, Files.Files()>,
  base: Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match h m:
    case None{} m:
      Content.next(m, fits, prev, other, base)
    case Some{ws} None{}:
      None{}
    case Some{ws} Some{e}:
      Content.apply.few(ws, Lines.Ask.request(Lines.Entry.ask(e)), fits, prev, other, base)

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
def Entry.fits(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Types.Entry>
) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      Merge.fits(kn, s, c, j, e)

# the content m, or else the one that rest gives
def Content.or(
  m: Maybe<&2, Files.Files()>,
  rest: Unit -> Maybe<&2, Files.Files()>
) -> Maybe<&2, Files.Files()>:
  match m:
    case Some{x}:
      Some{x}
    case None{}:
      rest(Unit{})

# the content of version k of the line c in the facts s, read through at most
# fuel versions (nothing while the node does not hold enough); a content that
# the table kn holds is not read again, and a merge reads only the paths
# that what it takes changed from its base, when the table holds the state
# of the line that it takes from
def Content.at(
  +fuel: Nat,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Maybe<&2, Files.Files()>:
  match fuel k:
    case 0n _:
      None{}
    case 1n+f 0n:
      Content.first(Knowns.Known.at(kn, s, c, 0n))
    case 1n+f 1n+j:
      +e = Knowns.Known.at(kn, s, c, 1n+j)
      +t = Entry.taken(c, e)
      +a = Entry.based(c, e)
      Content.quick(
        Merge.hint(Knowns.Known.find(kn, Spec.Point.line(t)), t, a),
        e,
        Entry.fits(kn, s, c, j, e),
        Content.or(Knowns.Known.files(kn, c, j, f), u => Content.at(f, kn, s, c, j)),
        Content.or(
          Knowns.Known.files(kn, Spec.Point.line(t), Spec.Point.n(t), f),
          u => Content.at(f, kn, s, Spec.Point.line(t), Spec.Point.n(t))
        ),
        Content.or(
          Knowns.Known.files(kn, Spec.Point.line(a), Spec.Point.n(a), f),
          u => Content.at(f, kn, s, Spec.Point.line(a), Spec.Point.n(a))
        )
      )

# the content of version k of the line c in the facts s, read with the fuel g
# unless the table kn holds it
def Content.from(
  +g: Nat,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Maybe<&2, Files.Files()>:
  Content.or(Knowns.Known.files(kn, c, k, g), u => Content.at(g, kn, s, c, k))

# the content of version k of the line c in the facts s: as the table kn
# holds it, when a read with at most as much fuel as the node holds facts
# gives it (Known.low); else read with the fuel of the facts
def Content.of(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Maybe<&2, Files.Files()>:
  Content.or(
    Knowns.Known.files(kn, c, k, Knowns.Known.low(kn)),
    u => Content.from(Facts.Facts.fuel(s), kn, s, c, k)
  )

# the words at the path p of the content m
def Content.get(m: Maybe<&2, Files.Files()>, +p: String) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Some{Files.Files.get(t, p)}

# the words of the resource at the path p in version k of the line c
def Content.read(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Content.get(Content.of(kn, s, c, k), p)

# A table that is right
# ---------------------

# the content e is right: it is what a read of the facts s with its fuel
# gives
def Held.ok(s: Facts.Plain(), e: Knowns.Held) -> Bool:
  match e:
    case Knowns.Held{c, k, d, x}:
      Files.Files.fits(Content.at(d, Knowns.Known.none(), s, c, k), x)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for an entry that is wrong, which then costs no more than a right entry, where both sides run
# the entry e is right: its state is the state that the facts s give its
# line, or each of its contents is right, or its rule and its era are those
# of the next version of its line in the facts s, or its ids are those of the
# versions of its line in the facts s; the facts that a work may act on are
# checked apart (Known.fit), since only the first counts
def Kept.ok(+s: Facts.Plain(), e: Knowns.Kept) -> Bool:
  match e:
    case Knowns.Kept{c, st}:
      Knowns.State.fits(Lines.Line.state(s, c), st)
    case Knowns.Stock{m, q}:
      Bool.and(
        Orders.Crit.every(~Knowns.Held, ~Facts.Plain(), ~Held.ok, m, s),
        Nat.is_le(q, Facts.Facts.fuel(s))
      )
    case Knowns.Ruled{+c, m, u}:
      Bool.and(
        Knowns.Rule.fits(
          Knowns.Known.rule.next(Knowns.Known.none(), s, c, Lines.Line.state(s, c)),
          u
        ),
        Knowns.Era.fits(Lines.Line.state(s, c), c, m)
      )
    case Knowns.Made{c, x}:
      Knowns.Made.fits(Lines.Line.state(s, c), x)
    case Knowns.Open{fs, n, tx, mx}:
      True{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the state m of the line c, if any, is the state that the facts s give
def State.ok(+s: Facts.Plain(), c: Ledgers.Line, m: Maybe<&2, Lines.State>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{st}:
      Kept.ok(s, Knowns.Kept{c, st})

# the era and the rule m of the next version of the line c, if any, are
# those that the facts s give
def Mark.ok(+s: Facts.Plain(), c: Ledgers.Line, m: Maybe<&2, Knowns.Mark>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Knowns.Mark{n, u}}:
      Kept.ok(s, Knowns.Ruled{c, n, u})

# the ids m of the versions of the line c, if any, are those that the facts
# s give
def Made.ok(+s: Facts.Plain(), c: Ledgers.Line, m: Maybe<&2, Knowns.Ids>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      Kept.ok(s, Knowns.Made{c, x})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for a table that is wrong, which then costs no more than a right table, where both sides run
# the count that m keeps, if any, is the count of its versions
def Seen.counted(m: Maybe<&2, Knowns.Seen>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Knowns.Seen{rev, n, k}}:
      Nat.is_eq(n, List.length(&2, Types.Entry, rev))

# what i holds of its line is what the facts s give, and the count of its
# versions is right
def Info.ok(s: Facts.Plain(), i: Knowns.Info) -> Bool:
  match i:
    case Knowns.Info{+c, +m, r, x}:
      +s = s
      Bool.and(
        State.ok(s, c, Knowns.Seen.state.of(m)),
        Bool.and(Mark.ok(s, c, r), Bool.and(Made.ok(s, c, x), Seen.counted(m)))
      )

# the lines l are right for the facts s: what each holds of its line is what
# s gives, and each sits under the key of its line
def Infos.ok(+l: Crits.Crit<Knowns.Info>, s: Facts.Plain()) -> Bool:
  Bool.and(
    Orders.Crit.every(~Knowns.Info, ~Facts.Plain(), ~Info.ok, l, s),
    Orders.Binds.keyed(~Knowns.Info, ~Knowns.Info.key, Crits.Crit.entries(Knowns.Info, l))
  )

# the table kn is right for the facts s: each state and each content that it
# holds is what s gives
def Known.ok(+kn: Knowns.Known(), +s: Facts.Plain()) -> Bool:
  Bool.and(
    Infos.ok(Knowns.Known.lines(kn), s),
    Kept.ok(s, Knowns.Stock{Knowns.Known.stock(kn), Knowns.Known.low(kn)})
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the lines of merges that the entry m holds, if it holds them, are those of
# the facts s
def Shelf.led(m: Maybe<&2, Knowns.Kept>, s: Facts.Plain()) -> Bool:
  match m:
    case Some{Knowns.Open{fs, n, tx, mx}}:
      Knowns.Mergers.same(mx, Knowns.Mergers.of(Facts.Facts.list(s)))
    case _:
      True{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the left side fails only for a table that is wrong, which then costs no more than a right table, where both sides run
# what the entry m holds for a work, if it does, is right: the facts that a
# work may still act on in the facts s, the greatest number of an ask in s,
# the newest writes of s, and the lines of the merges of s
def Shelf.fits(m: Maybe<&2, Knowns.Kept>, +s: Facts.Plain()) -> Bool:
  match m:
    case Some{Knowns.Open{fs, n, tx, mx}}:
      Bool.and(
        Bool.and(
          Bool.and(
            Shared.List.is_eq(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              fs,
              Knowns.Open.of(Facts.Facts.list(s), Knowns.Scene{Knowns.Known.none(), s})
            ),
            Nat.is_eq(n, Facts.Seq.peak(Facts.Facts.list(s)))
          ),
          Knowns.Tops.same(tx, Knowns.Tops.of(Facts.Facts.list(s)))
        ),
        Knowns.Mergers.same(mx, Knowns.Mergers.of(Facts.Facts.list(s)))
      )
    case _:
      True{}

# the table kn fits the facts s: it is right, and what it holds for a work
# is right
def Known.fit(+kn: Knowns.Known(), +s: Facts.Plain()) -> Bool:
  Bool.and(Known.ok(kn, s), Shelf.fits(Knowns.Known.shelf(kn), s))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# What a node learns of the contents
# ----------------------------------

# one more than the fuels a, b and c of three contents, if the table holds
# them; else the fuel that g gives
def Fill.fuel.of(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, c: Maybe<&2, Nat>, g: Unit -> Nat) -> Nat:
  match a b c:
    case Some{x} Some{y} Some{z}:
      1n+Nat.max(x, Nat.max(y, z))
    case _ _ _:
      g(Unit{})

# a fuel that reads the content of version k of the line c, the entry e if the
# node holds it, through the table kn: one more than the fuels of the contents
# that the version reads, when the table holds them; else the fuel that g
# gives, which is then read
def Fill.fuel(
  k: Nat,
  +kn: Knowns.Known(),
  +c: Ledgers.Line,
  +e: Maybe<&2, Types.Entry>,
  g: Unit -> Nat
) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+j:
      +t = Entry.taken(c, e)
      +a = Entry.based(c, e)
      Fill.fuel.of(
        Knowns.Known.depth(kn, c, j),
        Knowns.Known.depth(kn, Spec.Point.line(t), Spec.Point.n(t)),
        Knowns.Known.depth(kn, Spec.Point.line(a), Spec.Point.n(a)),
        g
      )

# the table kn with the content m, if any, of version k of the line c, that a
# read with the fuel d gives
def Known.fill.of(
  kn: Knowns.Known(),
  c: Ledgers.Line,
  k: Nat,
  d: Nat,
  m: Maybe<&2, Files.Files()>
) -> Knowns.Known():
  match m:
    case None{}:
      kn
    case Some{x}:
      Knowns.Known.hold(kn, Knowns.Held{c, k, d, x})

# the table kn with the content of version k of the line c in the facts s,
# read with the fuel d
def Known.fill.at(
  +d: Nat,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Knowns.Known():
  Known.fill.of(kn, c, k, d, Content.at(d, kn, s, c, k))

# the table kn with the content of version k of the line c in the facts s,
# read from the facts with a fuel that reaches it
def Known.fill.slow(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Knowns.Known():
  +d = Fill.fuel(k, kn, c, Knowns.Known.at(kn, s, c, k), u => Facts.Facts.fuel(s))
  Known.fill.at(d, kn, s, c, k)

# the table kn with the content of the version after j of the line c, made
# by the request r, when the table holds the content x of version j, read
# with the fuel d: a write is one change of x, and reads no other content
def Known.fill.write(
  r: Spec.Request,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +d: Nat,
  x: Files.Files()
) -> Knowns.Known():
  match r:
    case Spec.Request.Write{b, p, w}:
      Known.fill.of(kn, c, 1n+j, 1n+d, Some{Files.Files.set(x, p, w)})
    case Spec.Request.Resolve{m, p, w}:
      Known.fill.of(kn, c, 1n+j, 1n+d, Some{Files.Files.set(x, p, w)})
    case _:
      Known.fill.slow(kn, s, c, 1n+j)

# the table kn with the content of the version after j of the line c, the
# entry e if the node holds it, when prev is what the table holds of the
# content of version j
def Known.fill.next(
  prev: Maybe<&2, Knowns.Held>,
  e: Maybe<&2, Types.Entry>,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> Knowns.Known():
  match prev e:
    case Some{
      Knowns.Held{c2, k2, d, x}
    } Some{Types.Entry{Types.Pick{Types.Ask{i, n, r}, pins}, slot}}:
      Known.fill.write(r, kn, s, c, j, d, x)
    case _ _:
      Known.fill.slow(kn, s, c, 1n+j)

# the table kn with the content of version k of the line c in the facts s
def Known.fill.new(
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> Knowns.Known():
  match k:
    case 0n:
      Known.fill.slow(kn, s, c, 0n)
    case 1n+j:
      +j = j
      Known.fill.next(Knowns.Known.held(kn, c, j), Knowns.Known.at(kn, s, c, 1n+j), kn, s, c, j)

# the table kn with the content of version k of the line c in the facts s,
# unless the table holds it (old)
def Known.fill.if(
  old: Bool,
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> Knowns.Known():
  match old:
    case True{}:
      kn
    case False{}:
      Known.fill.new(kn, s, c, k)

# the table kn with the content of version k of the line c in the facts s
def Known.fill(+kn: Knowns.Known(), +s: Facts.Plain(), +c: Ledgers.Line, +k: Nat) -> Knowns.Known():
  Known.fill.if(Maybe.is_some(&2, Nat, Knowns.Known.depth(kn, c, k)), kn, s, c, k)

# the table kn with the contents of the n versions of the line c from the
# version k on, the oldest first: each is read from the one before
def Known.warm.go(
  n: Nat,
  +k: Nat,
  kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Knowns.Known():
  match n:
    case 0n:
      kn
    case 1n+p:
      Known.warm.go(p, 1n+k, Known.fill(kn, s, c, k), s, c)

# the number of the versions m
def Versions.count(m: Maybe<&2, List<&2, Types.Entry>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{vs}:
      List.length(&2, Types.Entry, vs)

# the table kn with the content of each version of the line c in the facts s
def Known.warm(+kn: Knowns.Known(), +s: Facts.Plain(), +c: Ledgers.Line) -> Knowns.Known():
  Known.warm.go(
    Versions.count(Knowns.Known.versions(kn, s, c)),
    0n,
    Knowns.Known.sync(kn, Facts.Facts.fuel(s)),
    s,
    c
  )

# the number of the versions of the state m, if any
def State.count(m: Maybe<&2, Lines.State>) -> Nat:
  Versions.count(Maybe.map(&2, Lines.State, List<&2, Types.Entry>, Lines.State.versions, m))

# the number of the versions that the table kn holds for the line c: as the
# versions x of c by id hold it, if known; else counted
def Tally.by(x: Maybe<&2, Knowns.Ids>, kn: Knowns.Known(), c: Ledgers.Line) -> Nat:
  match x:
    case None{}:
      State.count(Knowns.Known.find(kn, c))
    case Some{ids}:
      Knowns.Ids.count(ids)

# the number of the versions that the table kn holds for the line c
def Known.tally(+kn: Knowns.Known(), +c: Ledgers.Line) -> Nat:
  Tally.by(Knowns.Known.ids(kn, c), kn, c)

# the table kn with the contents of the versions of the line c in the facts
# s from the version a on, up to b versions, when it holds the one before
# (near); else with the content of each of the b versions
def Known.grow.if(
  near: Bool,
  +a: Nat,
  +b: Nat,
  kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Knowns.Known():
  match near:
    case True{}:
      Known.warm.go(Nat.sub(b, a), a, kn, s, c)
    case False{}:
      Known.warm.go(b, 0n, Knowns.Known.sync(kn, Facts.Facts.fuel(s)), s, c)

# the table kn with the content of each version of the line c in the facts s
# that the table old did not know: those after the versions of the state that
# old holds for c, if kn holds the content of the last of them; else all the
# versions of the state that kn holds for c
def Known.grow(
  +old: Knowns.Known(),
  +kn: Knowns.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line
) -> Knowns.Known():
  +a = Known.tally(old, c)
  Known.grow.if(
    Maybe.is_some(&2, Nat, Knowns.Known.depth(kn, c, Nat.sub(a, 1n))),
    a,
    Known.tally(kn, c),
    kn,
    s,
    c
  )
