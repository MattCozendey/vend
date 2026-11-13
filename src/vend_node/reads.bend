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

# what follows from a witness and what holds of it follows from r
def Ex.by(-A: Type, -B: @-x: A -> Type, -Q: Type, r: Exists(A, B), k: @x: A -> B(x) -> Q) -> Q:
  (x, w) = r
  k(x)(w)

# what follows from both sides follows from r
def And.by(-A: Type, -B: Type, -Q: Type, r: A & B, k: A -> B -> Q) -> Q:
  (a, b) = r
  k(a)(b)

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

# Versions made by a request
# --------------------------

# a reply of an id comes from an entry of that id
def Reply.id_some(m: Maybe<&2, Types.Entry>, -i: Ledgers.Id) -> {
  Answers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> Exists(Types.Entry, e => {m == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(Types.Entry, e => {None{} == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h)
      )
    case Some{e}:
      h => (
        e,
        (
          {==},
          Equal.cong(
            Maybe<&2, Spec.Reply>,
            Ledgers.Id,
            x => Reply.to_id(x, i),
            Some{Spec.Reply.Id{Lines.Entry.id(e)}},
            Some{Spec.Reply.Id{i}},
            h
          )
        )
      )

# a version that a line holds is among its versions
def Line.at.of_some(m: Maybe<&2, List<&2, Types.Entry>>, -k: Nat, -e: Types.Entry) -> {
  Lines.Line.at.of(m, k) == Some{e}: Maybe<&2, Types.Entry>
} -> Exists(
  List<&2, Types.Entry>,
  vs => {m == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} & {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
):
  match m:
    case None{}:
      h => Empty.absurd(
        Exists(
          List<&2, Types.Entry>,
          vs => {None{} == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} & {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
        ),
        Shared.Maybe.none_ne_some(Types.Entry, e, h)
      )
    case Some{vs}:
      h => (vs, ({==}, h))

# version k of a line is version k of its versions
def Line.at_some(+s: Facts.Facts(), +c: Ledgers.Line, -k: Nat, -e: Types.Entry) -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> Exists(
  List<&2, Types.Entry>,
  vs => {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} & {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
):
  h => Line.at.of_some(Lines.Line.versions(s, c), k, e)(h)

# version k of the versions of a line is version k of the line
def Line.at_of(+s: Facts.Facts(), +c: Ledgers.Line, -vs: List<&2, Types.Entry>, -k: Nat, -e: Types.Entry) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
}:
  hv => hg => Eq.back(Maybe<&2, List<&2, Types.Entry>>, y => {Lines.Line.at.of(y, k) == Some{e}: Maybe<&2, Types.Entry>}, Lines.Line.versions(s, c), Some{vs}, hv, hg)

# the entry found for the id of version k of a line is version k
def Line.find_at(+s: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +k: Nat, +e: Types.Entry) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>} -> {
  Answers.Line.find(s, c, Lines.Entry.id(e)) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>
}:
  +hv => +hg =>
    %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Line.versions(s, c), Some{vs}, hv): {Answers.Line.find.of(Lines.Entry.id(e), _) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>}
    %Equal.sym(Maybe<&2, Nat>, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, Lines.Entry.id(e)), Some{k}, Versions.Line.versions_index(s, c, vs, k, e)(hv)(hg)): {Answers.Versions.find.at(vs, _) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>}
    %Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, vs, k), Some{e}, hg): {Maybe.map(&2, Types.Entry, Answers.Found, e2 => Answers.Found{k, e2}, _) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>}
    {==}

# the entry e is version k of the line c, found there for the id i, and its
# request is r
def Made.At(s: Facts.Facts(), c: Ledgers.Line, k: Nat, i: Ledgers.Id, r: Spec.Request, e: Types.Entry) -> Type:
  {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>}
    & (
      {Answers.Line.find(s, c, i) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>}
        & {Answers.Entry.request(e) == r: Spec.Request}
    )

# Made.at, once the entry e of the version and its place in the versions vs are known
def Made.at.fin(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +r: Spec.Request, +e: Types.Entry, ha: {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>}, +hf: {
  Answers.Line.find(s, c, i) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>
}, hr: {Answers.Answer.of(s, Spec.Question.Request{c, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>}) -> Made.At(s, c, k, i, r, e):
  (
    ha,
    (
      hf,
      Equal.cong(
        Maybe<&2, Spec.Reply>,
        Spec.Request,
        x => Reply.to_ask(x, r),
        Some{Spec.Reply.Ask{Answers.Entry.request(e)}},
        Some{Spec.Reply.Ask{r}},
        Eq.to(
          Maybe<&2, Answers.Found>,
          y => {Answers.Reply.ask(y) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>},
          Answers.Line.find(s, c, i),
          Some{Answers.Found{k, e}},
          hf,
          hr
        )
      )
    )
  )

# Made.at, once the entry e of the version is known
def Made.at.of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +r: Spec.Request, +e: Types.Entry, +ha: {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>}, hi: {Lines.Entry.id(e) == i: Ledgers.Id}, hr: {Answers.Answer.of(s, Spec.Question.Request{c, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>}) -> Made.At(s, c, k, i, r, e):
  Ex.by(
    List<&2, Types.Entry>,
    vs => {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} & {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>},
    Made.At(s, c, k, i, r, e),
    Line.at_some(s, c, k, e)(ha),
    +vs => w => And.by(
      {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
      {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>},
      Made.At(s, c, k, i, r, e),
      w,
      hv => hg => Made.at.fin(
        s,
        c,
        k,
        i,
        r,
        e,
        ha,
        Eq.to(
          Ledgers.Id,
          y => {Answers.Line.find(s, c, y) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>},
          Lines.Entry.id(e),
          i,
          hi,
          Line.find_at(s, c, vs, k, e)(hv)(hg)
        ),
        hr
      )
    )
  )

# a version made by a request is an entry of the line, found for its id, of
# that request
def Made.at(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +r: Spec.Request) -> Mirror.Made(s, c, k, i, r) -> Exists(
  Types.Entry,
  e => Made.At(s, c, k, i, r, e)
):
  m => And.by(
    {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>},
    {Answers.Answer.of(s, Spec.Question.Request{c, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>},
    Exists(Types.Entry, e => Made.At(s, c, k, i, r, e)),
    m,
    hv => hr => Ex.by(
      Types.Entry,
      e => {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id},
      Exists(Types.Entry, e => Made.At(s, c, k, i, r, e)),
      Reply.id_some(Lines.Line.at(s, c, k), i)(hv),
      +e => w => And.by(
        {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>},
        {Lines.Entry.id(e) == i: Ledgers.Id},
        Exists(Types.Entry, e2 => Made.At(s, c, k, i, r, e2)),
        w,
        ha => hi => (e, Made.at.of(s, c, k, i, r, e, ha, hi, hr))
      )
    )
  )

# what follows from the entry of a version made by a request, follows
def Made.by(-Q: Type, +s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +r: Spec.Request, m: Mirror.Made(s, c, k, i, r), f: @e: Types.Entry -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Answers.Line.find(s, c, i) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>} -> {
  Answers.Entry.request(e) == r: Spec.Request
} -> Q) -> Q:
  Ex.by(
    Types.Entry,
    e => Made.At(s, c, k, i, r, e),
    Q,
    Made.at(s, c, k, i, r)(m),
    e => w => And.by(
      {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>},
      {Answers.Line.find(s, c, i) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>} & {Answers.Entry.request(e) == r: Spec.Request},
      Q,
      w,
      ha => w2 => And.by(
        {Answers.Line.find(s, c, i) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>},
        {Answers.Entry.request(e) == r: Spec.Request},
        Q,
        w2,
        hf => hr => f(e)(ha)(hf)(hr)
      )
    )
  )

# One version
# -----------

# the content of version 1+k, read with some fuel, comes from contents read
# with the same fuel
def Content.at_step(g: Nat, +s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, -t: Files.Files()) -> {
  Contents.Content.at(g, s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>
} -> {
  Contents.Content.next(
    Lines.Line.at(s, c, 1n+k),
    Contents.Entry.fits(s, c, k, Lines.Line.at(s, c, 1n+k)),
    Contents.Content.at(g, s, c, k),
    Sub.taken(g, s, c, Lines.Line.at(s, c, 1n+k)),
    Sub.based(g, s, c, Lines.Line.at(s, c, 1n+k))
  )
    == Some{t}: Maybe<&2, Files.Files()>
}:
  match g:
    case 0n:
      h => Empty.absurd(
        {
          Contents.Content.next(
            Lines.Line.at(s, c, 1n+k),
            Contents.Entry.fits(s, c, k, Lines.Line.at(s, c, 1n+k)),
            Contents.Content.at(0n, s, c, k),
            Sub.taken(0n, s, c, Lines.Line.at(s, c, 1n+k)),
            Sub.based(0n, s, c, Lines.Line.at(s, c, 1n+k))
          )
            == Some{t}: Maybe<&2, Files.Files()>
        },
        Shared.Maybe.none_ne_some(Files.Files(), t, h)
      )
    case 1n+(+f):
      h => Content.next_le(
        Lines.Line.at(s, c, 1n+k),
        Contents.Entry.fits(s, c, k, Lines.Line.at(s, c, 1n+k)),
        Contents.Content.at(f, s, c, k),
        Sub.taken(f, s, c, Lines.Line.at(s, c, 1n+k)),
        Sub.based(f, s, c, Lines.Line.at(s, c, 1n+k)),
        Contents.Entry.fits(s, c, k, Lines.Line.at(s, c, 1n+k)),
        Contents.Content.at(1n+f, s, c, k),
        Sub.taken(1n+f, s, c, Lines.Line.at(s, c, 1n+k)),
        Sub.based(1n+f, s, c, Lines.Line.at(s, c, 1n+k)),
        t
      )(e => e)(
        Content.at_more(f, s, c, k)
      )(
        Content.at_more(
          f,
          s,
          Spec.Point.line(Contents.Entry.taken(c, Lines.Line.at(s, c, 1n+k))),
          Spec.Point.n(Contents.Entry.taken(c, Lines.Line.at(s, c, 1n+k)))
        )
      )(
        Content.at_more(
          f,
          s,
          Spec.Point.line(Contents.Entry.based(c, Lines.Line.at(s, c, 1n+k))),
          Spec.Point.n(Contents.Entry.based(c, Lines.Line.at(s, c, 1n+k)))
        )
      )(h)

# the content of version 1+k of a line, the entry e, is what the request of e
# gives from the content of version k, of the version that e takes and of its
# base
def Content.of_step(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, -t: Files.Files()) -> {
  Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>} -> {
  Contents.Content.apply(
    Answers.Entry.request(e),
    Contents.Merge.fits(s, c, k, e),
    Contents.Content.of(s, c, k),
    Contents.Content.of(
      s,
      Spec.Point.line(Contents.Point.or(c, Contents.Entry.takes(e))),
      Spec.Point.n(Contents.Point.or(c, Contents.Entry.takes(e)))
    ),
    Contents.Content.of(
      s,
      Spec.Point.line(Contents.Point.or(c, Contents.Entry.base(e))),
      Spec.Point.n(Contents.Point.or(c, Contents.Entry.base(e)))
    )
  )
    == Some{t}: Maybe<&2, Files.Files()>
}:
  ha => h => Eq.to(
    Maybe<&2, Types.Entry>,
    m => {
      Contents.Content.next(
        m,
        Contents.Entry.fits(s, c, k, m),
        Contents.Content.at(Facts.Facts.fuel(s), s, c, k),
        Sub.taken(Facts.Facts.fuel(s), s, c, m),
        Sub.based(Facts.Facts.fuel(s), s, c, m)
      )
        == Some{t}: Maybe<&2, Files.Files()>
    },
    Lines.Line.at(s, c, 1n+k),
    Some{e},
    ha,
    Content.at_step(Facts.Facts.fuel(s), s, c, k, t)(h)
  )

# Writes
# ------

# the content of a version made by a write is the content before with the
# write
def Write.prev(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, -b: Ledgers.Line, +p: String, +ws: Maybe<&2, List<&2, U32>>, -t: Files.Files()) -> {
  Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Answers.Entry.request(e) == Spec.Request.Write{b, p, ws}: Spec.Request} -> {
  Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>
} -> Exists(
  Files.Files(),
  prev => {Contents.Content.of(s, c, k) == Some{prev}: Maybe<&2, Files.Files()>} & {Files.Files.set(prev, p, ws) == t: Files.Files()}
):
  ha => hr => h => Content.write_some(p, ws, Contents.Content.of(s, c, k), t)(
    Eq.to(
      Spec.Request,
      r => {
        Contents.Content.apply(
          r,
          Contents.Merge.fits(s, c, k, e),
          Contents.Content.of(s, c, k),
          Contents.Content.of(
            s,
            Spec.Point.line(Contents.Point.or(c, Contents.Entry.takes(e))),
            Spec.Point.n(Contents.Point.or(c, Contents.Entry.takes(e)))
          ),
          Contents.Content.of(
            s,
            Spec.Point.line(Contents.Point.or(c, Contents.Entry.base(e))),
            Spec.Point.n(Contents.Point.or(c, Contents.Entry.base(e)))
          )
        )
          == Some{t}: Maybe<&2, Files.Files()>
      },
      Answers.Entry.request(e),
      Spec.Request.Write{b, p, ws},
      hr,
      Content.of_step(s, c, k, e, t)(ha)(h)
    )
  )

# the first part of Core.write_writes
def Write.same(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, -b: Ledgers.Line, +p: String, +ws: Maybe<&2, List<&2, U32>>, -x: Maybe<&2, List<&2, U32>>) -> {
  Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Answers.Entry.request(e) == Spec.Request.Write{b, p, ws}: Spec.Request} -> {
  Contents.Content.read(s, c, 1n+k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {x == ws: Maybe<&2, List<&2, U32>>}:
  +ha => +hr => h => Ex.by(
    Files.Files(),
    t => {Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>} & {Files.Files.get(t, p) == x: Maybe<&2, List<&2, U32>>},
    {x == ws: Maybe<&2, List<&2, U32>>},
    Content.get_some(Contents.Content.of(s, c, 1n+k), p, x)(h),
    t => w => And.by(
      {Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>},
      {Files.Files.get(t, p) == x: Maybe<&2, List<&2, U32>>},
      {x == ws: Maybe<&2, List<&2, U32>>},
      w,
      ht => hx => Ex.by(
        Files.Files(),
        prev => {Contents.Content.of(s, c, k) == Some{prev}: Maybe<&2, Files.Files()>} & {Files.Files.set(prev, p, ws) == t: Files.Files()},
        {x == ws: Maybe<&2, List<&2, U32>>},
        Write.prev(s, c, k, e, b, p, ws, t)(ha)(hr)(ht),
        prev => w2 => And.by(
          {Contents.Content.of(s, c, k) == Some{prev}: Maybe<&2, Files.Files()>},
          {Files.Files.set(prev, p, ws) == t: Files.Files()},
          {x == ws: Maybe<&2, List<&2, U32>>},
          w2,
          hp => hs => Eq.to(
            Maybe<&2, List<&2, U32>>,
            y => {y == ws: Maybe<&2, List<&2, U32>>},
            Files.Files.get(t, p),
            x,
            hx,
            Eq.to(
              Files.Files(),
              y => {Files.Files.get(y, p) == ws: Maybe<&2, List<&2, U32>>},
              Files.Files.set(prev, p, ws),
              t,
              hs,
              Files.Files.get_set_same(prev, p, ws)
            )
          )
        )
      )
    )
  )

# the second part of Core.write_writes
def Write.other(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, -b: Ledgers.Line, +p: String, +ws: Maybe<&2, List<&2, U32>>, +q: String, -x: Maybe<&2, List<&2, U32>>, -y: Maybe<&2, List<&2, U32>>) -> {
  Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Answers.Entry.request(e) == Spec.Request.Write{b, p, ws}: Spec.Request} -> {String.eq(p, q) == False{}: Bool} -> {
  Contents.Content.read(s, c, 1n+k, q) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Contents.Content.read(s, c, k, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>} -> {x == y: Maybe<&2, List<&2, U32>>}:
  +ha => +hr => hne => h => h2 => Ex.by(
    Files.Files(),
    t => {Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>} & {Files.Files.get(t, q) == x: Maybe<&2, List<&2, U32>>},
    {x == y: Maybe<&2, List<&2, U32>>},
    Content.get_some(Contents.Content.of(s, c, 1n+k), q, x)(h),
    t => w => And.by(
      {Contents.Content.of(s, c, 1n+k) == Some{t}: Maybe<&2, Files.Files()>},
      {Files.Files.get(t, q) == x: Maybe<&2, List<&2, U32>>},
      {x == y: Maybe<&2, List<&2, U32>>},
      w,
      ht => hx => Ex.by(
        Files.Files(),
        prev => {Contents.Content.of(s, c, k) == Some{prev}: Maybe<&2, Files.Files()>} & {Files.Files.set(prev, p, ws) == t: Files.Files()},
        {x == y: Maybe<&2, List<&2, U32>>},
        Write.prev(s, c, k, e, b, p, ws, t)(ha)(hr)(ht),
        prev => w2 => And.by(
          {Contents.Content.of(s, c, k) == Some{prev}: Maybe<&2, Files.Files()>},
          {Files.Files.set(prev, p, ws) == t: Files.Files()},
          {x == y: Maybe<&2, List<&2, U32>>},
          w2,
          hp => hs => Eq.to(
            Maybe<&2, List<&2, U32>>,
            z => {x == z: Maybe<&2, List<&2, U32>>},
            Files.Files.get(prev, q),
            y,
            Shared.Maybe.some_inj(
              Maybe<&2, List<&2, U32>>,
              Files.Files.get(prev, q),
              y,
              Eq.to(Maybe<&2, Files.Files()>, m => {Contents.Content.get(m, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, Contents.Content.of(s, c, k), Some{prev}, hp, h2)
            ),
            Eq.to(
              Maybe<&2, List<&2, U32>>,
              z => {z == Files.Files.get(prev, q): Maybe<&2, List<&2, U32>>},
              Files.Files.get(t, q),
              x,
              hx,
              Eq.to(
                Files.Files(),
                z => {Files.Files.get(z, q) == Files.Files.get(prev, q): Maybe<&2, List<&2, U32>>},
                Files.Files.set(prev, p, ws),
                t,
                hs,
                Files.Files.get_set_other(prev, p, ws, q)(hne)
              )
            )
          )
        )
      )
    )
  )

# Core.write_writes, once the entry of the version is known
def Core.write_writes.of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, +p: String, +ws: Maybe<&2, List<&2, U32>>, +q: String, -x: Maybe<&2, List<&2, U32>>, -y: Maybe<&2, List<&2, U32>>, +ha: {
  Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
}, +hr: {Answers.Entry.request(e) == Spec.Request.Write{c, p, ws}: Spec.Request}) -> (
  {
    Contents.Content.read(s, c, 1n+k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {x == ws: Maybe<&2, List<&2, U32>>}
)
  & (
    (
      {String.eq(p, q) == False{}: Bool}
    ) -> {
      Contents.Content.read(s, c, 1n+k, q) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {
      Contents.Content.read(s, c, k, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {x == y: Maybe<&2, List<&2, U32>>}
  ):
  (Write.same(s, c, k, e, c, p, ws, x)(ha)(hr), Write.other(s, c, k, e, c, p, ws, q, x, y)(ha)(hr))

# a version made by a write holds the write at its path, and at each other
# path what the version before held
def Core.write_writes(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +p: String, +ws: Maybe<&2, List<&2, U32>>, +q: String, +x: Maybe<&2, List<&2, U32>>, +y: Maybe<&2, List<&2, U32>>) -> Mirror.Made(
  s,
  c,
  1n+k,
  i,
  Spec.Request.Write{c, p, ws}
) -> (
  {
    Contents.Content.read(s, c, 1n+k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {x == ws: Maybe<&2, List<&2, U32>>}
)
  & (
    (
      {String.eq(p, q) == False{}: Bool}
    ) -> {
      Contents.Content.read(s, c, 1n+k, q) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {
      Contents.Content.read(s, c, k, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    } -> {x == y: Maybe<&2, List<&2, U32>>}
  ):
  m => Made.by(
    (
      {
        Contents.Content.read(s, c, 1n+k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {x == ws: Maybe<&2, List<&2, U32>>}
    )
      & (
        (
          {String.eq(p, q) == False{}: Bool}
        ) -> {
          Contents.Content.read(s, c, 1n+k, q) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        } -> {
          Contents.Content.read(s, c, k, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        } -> {x == y: Maybe<&2, List<&2, U32>>}
      ),
    s,
    c,
    1n+k,
    i,
    Spec.Request.Write{c, p, ws},
    m,
    +e => +ha => hf => +hr => Core.write_writes.of(s, c, k, e, p, ws, q, x, y, ha, hr)
  )
