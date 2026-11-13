import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./mirror.bend as Mirror
import ./shared/files.bend as Files
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./stays.bend as Stays
import ./types.bend as Types
import ./versions.bend as Versions

# What the content of a version is
# --------------------------------
# The laws of the spec about the content of a version, each in its core form:
# said of the facts s of a node.

# Small helpers
# -------------

# what holds of a holds of b, equal to it
def Eq.to(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b: A}, p: P(a)) -> P(b):
  %e: P(_)
  p

# what holds of b holds of a, equal to it
def Eq.back(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b: A}, p: P(b)) -> P(a):
  Eq.to(A, P, b, a, Equal.sym(A, a, b, e), p)

# m2 holds what m holds
def Maybe.Le(-A: Data, m: Maybe<&2, A>, m2: Maybe<&2, A>) -> Type:
  @-x: A -> {m == Some{x}: Maybe<&2, A>} -> {m2 == Some{x}: Maybe<&2, A>}

# the hash of the reply m, or d
def Reply.to_hash(m: Maybe<&2, Spec.Reply>, d: Hashes.Hash) -> Hashes.Hash:
  match m:
    case Some{Spec.Reply.Hash{h}}:
      h
    case _:
      d

# the id of the reply m, or d
def Reply.to_id(m: Maybe<&2, Spec.Reply>, d: Ledgers.Id) -> Ledgers.Id:
  match m:
    case Some{Spec.Reply.Id{i}}:
      i
    case _:
      d

# the request of the reply m, or d
def Reply.to_ask(m: Maybe<&2, Spec.Reply>, d: Spec.Request) -> Spec.Request:
  match m:
    case Some{Spec.Reply.Ask{r}}:
      r
    case _:
      d

# the names of the reply m, or d
def Reply.to_names(m: Maybe<&2, Spec.Reply>, d: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{Spec.Reply.Names{ns}}:
      ns
    case _:
      d

# the points of the reply m, or d
def Reply.to_points(m: Maybe<&2, Spec.Reply>, d: List<&2, Spec.Point>) -> List<&2, Spec.Point>:
  match m:
    case Some{Spec.Reply.Points{ps}}:
      ps
    case _:
      d

# the point of the reply m, or d
def Reply.to_point(m: Maybe<&2, Spec.Reply>, d: Spec.Point) -> Spec.Point:
  match m:
    case Some{Spec.Reply.Point{x}}:
      x
    case _:
      d

# a content that answers words at a path is held, and holds them there
def Content.get_some(m: Maybe<&2, Files.Files()>, +p: String, -x: Maybe<&2, List<&2, U32>>) -> {
  Contents.Content.get(m, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> Exists(Files.Files(), t => {m == Some{t}: Maybe<&2, Files.Files()>} & {Files.Files.get(t, p) == x: Maybe<&2, List<&2, U32>>}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Files.Files(), t => {None{} == Some{t}: Maybe<&2, Files.Files()>} & {Files.Files.get(t, p) == x: Maybe<&2, List<&2, U32>>}),
        Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, x, h)
      )
    case Some{t}:
      h => (t, ({==}, Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Files.Files.get(t, p), x, h)))

# a write that gives a content was made on a held content
def Content.write_some(+p: String, +w: Maybe<&2, List<&2, U32>>, m: Maybe<&2, Files.Files()>, -t: Files.Files()) -> {
  Contents.Content.write(p, w, m) == Some{t}: Maybe<&2, Files.Files()>
} -> Exists(Files.Files(), prev => {m == Some{prev}: Maybe<&2, Files.Files()>} & {Files.Files.set(prev, p, w) == t: Files.Files()}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Files.Files(), prev => {None{} == Some{prev}: Maybe<&2, Files.Files()>} & {Files.Files.set(prev, p, w) == t: Files.Files()}),
        Shared.Maybe.none_ne_some(Files.Files(), t, h)
      )
    case Some{prev}:
      h => (prev, ({==}, Shared.Maybe.some_inj(Files.Files(), Files.Files.set(prev, p, w), t, h)))

# More fuel, same content
# -----------------------

# a write on a content that holds more gives the same
def Content.write_le(+p: String, +w: Maybe<&2, List<&2, U32>>, m: Maybe<&2, Files.Files()>, -m2: Maybe<&2, Files.Files()>, -t: Files.Files()) -> Maybe.Le(Files.Files(), m, m2) -> {
  Contents.Content.write(p, w, m) == Some{t}: Maybe<&2, Files.Files()>
} -> {Contents.Content.write(p, w, m2) == Some{t}: Maybe<&2, Files.Files()>}:
  match m:
    case None{}:
      le => h => Empty.absurd({Contents.Content.write(p, w, m2) == Some{t}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), t, h))
    case Some{x}:
      le => h => Eq.back(Maybe<&2, Files.Files()>, y => {Contents.Content.write(p, w, y) == Some{t}: Maybe<&2, Files.Files()>}, m2, Some{x}, le(x)({==}), h)

# a merge of contents that hold more, that fits if the first does, gives the same
def Merge.of_le(fits: Bool, o: Maybe<&2, Files.Files()>, t: Maybe<&2, Files.Files()>, b: Maybe<&2, Files.Files()>, -fits2: Bool, -o2: Maybe<&2, Files.Files()>, -t2: Maybe<&2, Files.Files()>, -b2: Maybe<&2, Files.Files()>, -x: Files.Files()) -> (
  {fits == True{}: Bool} -> {fits2 == True{}: Bool}
) -> Maybe.Le(Files.Files(), o, o2) -> Maybe.Le(Files.Files(), t, t2) -> Maybe.Le(Files.Files(), b, b2) -> {
  Contents.Merge.of(fits, o, t, b) == Some{x}: Maybe<&2, Files.Files()>
} -> {Contents.Merge.of(fits2, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>}:
  match fits o t b:
    case True{} Some{ov} Some{tv} Some{bv}:
      lf => lo => lt => lb => h => Eq.back(
        Bool,
        y => {Contents.Merge.of(y, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>},
        fits2,
        True{},
        lf({==}),
        Eq.back(
          Maybe<&2, Files.Files()>,
          y => {Contents.Merge.of(True{}, y, t2, b2) == Some{x}: Maybe<&2, Files.Files()>},
          o2,
          Some{ov},
          lo(ov)({==}),
          Eq.back(
            Maybe<&2, Files.Files()>,
            y => {Contents.Merge.of(True{}, Some{ov}, y, b2) == Some{x}: Maybe<&2, Files.Files()>},
            t2,
            Some{tv},
            lt(tv)({==}),
            Eq.back(
              Maybe<&2, Files.Files()>,
              y => {Contents.Merge.of(True{}, Some{ov}, Some{tv}, y) == Some{x}: Maybe<&2, Files.Files()>},
              b2,
              Some{bv},
              lb(bv)({==}),
              h
            )
          )
        )
      )
    case True{} Some{ov} Some{tv} None{}:
      lf => lo => lt => lb => h => Empty.absurd({Contents.Merge.of(fits2, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), x, h))
    case True{} Some{ov} None{} b:
      lf => lo => lt => lb => h => Empty.absurd({Contents.Merge.of(fits2, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), x, h))
    case True{} None{} t b:
      lf => lo => lt => lb => h => Empty.absurd({Contents.Merge.of(fits2, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), x, h))
    case False{} o t b:
      lf => lo => lt => lb => h => Empty.absurd({Contents.Merge.of(fits2, o2, t2, b2) == Some{x}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), x, h))

# a request applied to contents that hold more, with a merge that fits if the
# first does, gives the same
def Content.apply_le(r: Spec.Request, +fits: Bool, +prev: Maybe<&2, Files.Files()>, +other: Maybe<&2, Files.Files()>, +base: Maybe<&2, Files.Files()>, -fits2: Bool, -prev2: Maybe<&2, Files.Files()>, -other2: Maybe<&2, Files.Files()>, -base2: Maybe<&2, Files.Files()>, -x: Files.Files()) -> (
  {fits == True{}: Bool} -> {fits2 == True{}: Bool}
) -> Maybe.Le(Files.Files(), prev, prev2) -> Maybe.Le(Files.Files(), other, other2) -> Maybe.Le(Files.Files(), base, base2) -> {
  Contents.Content.apply(r, fits, prev, other, base) == Some{x}: Maybe<&2, Files.Files()>
} -> {Contents.Content.apply(r, fits2, prev2, other2, base2) == Some{x}: Maybe<&2, Files.Files()>}:
  match r:
    case Spec.Request.Write{b, +p, +w}:
      lf => lp => lo => lb => h => Content.write_le(p, w, prev, prev2, x)(lp)(h)
    case Spec.Request.Resolve{m, +p, +w}:
      lf => lp => lo => lb => h => Content.write_le(p, w, prev, prev2, x)(lp)(h)
    case Spec.Request.Move{b, t, v}:
      lf => lp => lo => lb => h => lo(x)(h)
    case Spec.Request.Merge{f, y}:
      lf => lp => lo => lb => h => Merge.of_le(fits, prev, other, base, fits2, prev2, other2, base2, x)(lf)(lp)(lo)(lb)(h)
    case Spec.Request.Start{os}:
      lf => lp => lo => lb => h => lp(x)(h)
    case Spec.Request.Mark{b, m, v}:
      lf => lp => lo => lb => h => lp(x)(h)
    case Spec.Request.Group{g, m, ms}:
      lf => lp => lo => lb => h => lp(x)(h)
    case Spec.Request.Own{c, g}:
      lf => lp => lo => lb => h => lp(x)(h)

# the content of an entry, if any, from contents that hold more, gives the same
def Content.next_le(m: Maybe<&2, Types.Entry>, +fits: Bool, +prev: Maybe<&2, Files.Files()>, +other: Maybe<&2, Files.Files()>, +base: Maybe<&2, Files.Files()>, -fits2: Bool, -prev2: Maybe<&2, Files.Files()>, -other2: Maybe<&2, Files.Files()>, -base2: Maybe<&2, Files.Files()>, -x: Files.Files()) -> (
  {fits == True{}: Bool} -> {fits2 == True{}: Bool}
) -> Maybe.Le(Files.Files(), prev, prev2) -> Maybe.Le(Files.Files(), other, other2) -> Maybe.Le(Files.Files(), base, base2) -> {
  Contents.Content.next(m, fits, prev, other, base) == Some{x}: Maybe<&2, Files.Files()>
} -> {Contents.Content.next(m, fits2, prev2, other2, base2) == Some{x}: Maybe<&2, Files.Files()>}:
  match m:
    case None{}:
      lf => lp => lo => lb => h => Empty.absurd({None{} == Some{x}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), x, h))
    case Some{e}:
      Content.apply_le(Lines.Ask.request(Lines.Entry.ask(e)), fits, prev, other, base, fits2, prev2, other2, base2, x)

# the content, read with the fuel f, of the version that the entry m of the
# line c takes
def Sub.taken(+f: Nat, +s: Facts.Facts(), +c: Ledgers.Line, +m: Maybe<&2, Types.Entry>) -> Maybe<&2, Files.Files()>:
  Contents.Content.at(f, s, Spec.Point.line(Contents.Entry.taken(c, m)), Spec.Point.n(Contents.Entry.taken(c, m)))

# the content, read with the fuel f, of the base of the entry m of the line c
def Sub.based(+f: Nat, +s: Facts.Facts(), +c: Ledgers.Line, +m: Maybe<&2, Types.Entry>) -> Maybe<&2, Files.Files()>:
  Contents.Content.at(f, s, Spec.Point.line(Contents.Entry.based(c, m)), Spec.Point.n(Contents.Entry.based(c, m)))

# a content read with some fuel is read with one more
def Content.at_more(f: Nat, +s: Facts.Facts(), +c: Ledgers.Line, k: Nat, -t: Files.Files()) -> {
  Contents.Content.at(f, s, c, k) == Some{t}: Maybe<&2, Files.Files()>
} -> {Contents.Content.at(1n+f, s, c, k) == Some{t}: Maybe<&2, Files.Files()>}:
  match f k:
    case 0n k:
      h => Empty.absurd({Contents.Content.at(1n, s, c, k) == Some{t}: Maybe<&2, Files.Files()>}, Shared.Maybe.none_ne_some(Files.Files(), t, h))
    case 1n+g 0n:
      h => h
    case 1n+(+g) 1n+(+j):
      h => Content.next_le(
        Lines.Line.at(s, c, 1n+j),
        Contents.Entry.fits(s, c, j, Lines.Line.at(s, c, 1n+j)),
        Contents.Content.at(g, s, c, j),
        Sub.taken(g, s, c, Lines.Line.at(s, c, 1n+j)),
        Sub.based(g, s, c, Lines.Line.at(s, c, 1n+j)),
        Contents.Entry.fits(s, c, j, Lines.Line.at(s, c, 1n+j)),
        Contents.Content.at(1n+g, s, c, j),
        Sub.taken(1n+g, s, c, Lines.Line.at(s, c, 1n+j)),
        Sub.based(1n+g, s, c, Lines.Line.at(s, c, 1n+j)),
        t
      )(e => e)(
        Content.at_more(g, s, c, j)
      )(
        Content.at_more(
          g,
          s,
          Spec.Point.line(Contents.Entry.taken(c, Lines.Line.at(s, c, 1n+j))),
          Spec.Point.n(Contents.Entry.taken(c, Lines.Line.at(s, c, 1n+j)))
        )
      )(
        Content.at_more(
          g,
          s,
          Spec.Point.line(Contents.Entry.based(c, Lines.Line.at(s, c, 1n+j))),
          Spec.Point.n(Contents.Entry.based(c, Lines.Line.at(s, c, 1n+j)))
        )
      )(h)
