import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./mirror.bend as Mirror
import ./rounds.bend as Rounds
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as Files
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions

# Laws of the answers
# -------------------
# The laws of the spec that follow from how a reply is read from the versions
# of a line, each in its core form: said of the facts s of a node.

# Replies taken apart
# -------------------

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

# the status of the reply m, or d
def Reply.to_status(m: Maybe<&2, Spec.Reply>, d: Spec.Status) -> Spec.Status:
  match m:
    case Some{Spec.Reply.Status{x}}:
      x
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

# what holds of a holds of b, equal to it
def Core.cast(-A: Type, -P: A -> Type, -a: A, -b: A, e: {a == b: A}, p: P(a)) -> P(b):
  %e: P(_)
  p

# version k of the versions of a line is version k of the line
def Line.at_of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  -vs: List<&2, Types.Entry>,
  -k: Nat,
  -e: Types.Entry
) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  hv => hg =>
    %Equal.sym(
      Maybe<&2, List<&2, Types.Entry>>,
      Lines.Line.versions(s, c),
      Some{vs},
      hv
    ): {RLines.Line.at.of(_, k) == Some{e}: Maybe<&2, Types.Entry>}
    hg

# the entry found for the id of version k of a line is version k
def Line.find_at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +e: Types.Entry
) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {
  Answers.Line.find(s, c, RLines.Entry.id(e)) == Some{RKnown.Found{k, e}}: Maybe<&2, RKnown.Found>
}:
  +hv => +hg =>
    %Equal.sym(
      Maybe<&2, List<&2, Types.Entry>>,
      Lines.Line.versions(s, c),
      Some{vs},
      hv
    ): {
      RAnswers.Line.find.of(
        RLines.Entry.id(e),
        _
      )
        == Some{RKnown.Found{k, e}}: Maybe<&2, RKnown.Found>
    }
    %Equal.sym(
      Maybe<&2, Nat>,
      Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Entry.id(e)),
      Some{k},
      Versions.Line.versions_index(s, c, vs, k, e)(hv)(hg)
    ): {RAnswers.Versions.find.at(vs, _) == Some{RKnown.Found{k, e}}: Maybe<&2, RKnown.Found>}
    %Equal.sym(
      Maybe<&2, Types.Entry>,
      List.get(&2, Types.Entry, vs, k),
      Some{e},
      hg
    ): {
      Maybe.map(
        &2,
        Types.Entry,
        RKnown.Found,
        e2 => RKnown.Found{k, e2},
        _
      )
        == Some{RKnown.Found{k, e}}: Maybe<&2, RKnown.Found>
    }
    {==}

# what follows from a witness and its fact follows from that there is one
def Exists.use(-A: Type, -B: @-x: A -> Type, -C: Type, p: Exists(A, B), k: @x: A -> B(x) -> C) -> C:
  (x, b) = p
  k(x)(b)

# what follows from two facts follows from their pair
def Pair.use(-A: Type, -B: Type, -C: Type, p: A & B, k: A -> B -> C) -> C:
  (a, b) = p
  k(a)(b)

# Made
# ----

# Core.made_at, once version k (m) and the versions of the line (v) are known
def Core.made_at.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +r: Spec.Request,
  m: Maybe<&2, Types.Entry>,
  v: Maybe<&2, List<&2, Types.Entry>>
) -> {
  RLines.Line.at.of(v, k) == m: Maybe<&2, Types.Entry>
} -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {
  RAnswers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.ask(Answers.Line.find(s, c, i)) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Types.Entry,
  e => {
    Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
  }
    & ({RLines.Entry.id(e) == i: Ledgers.Id} & {RAnswers.Entry.request(e) == r: Spec.Request})
):
  match m v:
    case None{} v2:
      em => ev => hv => hr => Empty.absurd(
        Exists(
          Types.Entry,
          e => {
            Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & (
              {RLines.Entry.id(e) == i: Ledgers.Id} & {RAnswers.Entry.request(e) == r: Spec.Request}
            )
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, hv)
      )
    case Some{e} None{}:
      em => ev => hv => hr => Empty.absurd(
        Exists(
          Types.Entry,
          e2 => {
            Lines.Line.at(s, c, k) == Some{e2}: Maybe<&2, Types.Entry>
          }
            & (
              {
                RLines.Entry.id(e2) == i: Ledgers.Id
              }
                & {RAnswers.Entry.request(e2) == r: Spec.Request}
            )
        ),
        Shared.Maybe.none_ne_some(Types.Entry, e, em)
      )
    case Some{+e} Some{+vs}:
      +em => +ev => hv => hr => (
        +hi = Equal.cong(Maybe<&2, Spec.Reply>, Ledgers.Id, x => Reply.to_id(x, i), Some{Spec.Reply.Id{RLines.Entry.id(e)}}, Some{Spec.Reply.Id{i}}, hv)
        (e, (Line.at_of(s, c, vs, k, e)(ev)(em), (hi, Equal.cong(Maybe<&2, Spec.Reply>, Spec.Request, x => Reply.to_ask(x, r), Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}, Some{Spec.Reply.Ask{r}}, Core.cast(Maybe<&2, RKnown.Found>, f => {RAnswers.Reply.ask(f) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>}, Answers.Line.find(s, c, i), Some{RKnown.Found{k, e}}, Core.cast(Ledgers.Id, x => {Answers.Line.find(s, c, x) == Some{RKnown.Found{k, e}}: Maybe<&2, RKnown.Found>}, RLines.Entry.id(e), i, hi, Line.find_at(s, c, vs, k, e)(ev)(em)), hr))))))

# a version made by a request is an entry of the line, of its id and request
def Core.made_at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +r: Spec.Request
) -> Mirror.Made(
  s,
  c,
  k,
  i,
  r
) -> Exists(
  Types.Entry,
  e => {
    Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
  }
    & ({RLines.Entry.id(e) == i: Ledgers.Id} & {RAnswers.Entry.request(e) == r: Spec.Request})
):
  m => Pair.use(
    {
      Answers.Answer.of(
        s,
        Spec.Question.Version{c, k}
      )
        == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
    },
    {
      Answers.Answer.of(
        s,
        Spec.Question.Request{c, i}
      )
        == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
    },
    Exists(
      Types.Entry,
      e => {
        Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
      }
        & ({RLines.Entry.id(e) == i: Ledgers.Id} & {RAnswers.Entry.request(e) == r: Spec.Request})
    ),
    m,
    hv => hr => Core.made_at.of(
      s,
      c,
      k,
      i,
      r,
      Lines.Line.at(s, c, k),
      Lines.Line.versions(s, c)
    )({==})({==})(hv)(hr)
  )

# Core.at_made, once the versions of the line (v) are known
def Core.at_made.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +e: Types.Entry,
  v: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {
  RLines.Line.at.of(v, k) == Some{e}: Maybe<&2, Types.Entry>
} -> Mirror.Made(s, c, k, RLines.Entry.id(e), RAnswers.Entry.request(e)):
  match v:
    case None{}:
      ev => ha => Empty.absurd(
        Mirror.Made(s, c, k, RLines.Entry.id(e), RAnswers.Entry.request(e)),
        Shared.Maybe.none_ne_some(Types.Entry, e, ha)
      )
    case Some{+vs}:
      +ev => +ha => (
        Core.cast(
          Maybe<&2, Types.Entry>,
          m => {
            RAnswers.Reply.id(m) == Some{Spec.Reply.Id{RLines.Entry.id(e)}}: Maybe<&2, Spec.Reply>
          },
          Some{e},
          Lines.Line.at(s, c, k),
          Equal.sym(
            Maybe<&2, Types.Entry>,
            Lines.Line.at(s, c, k),
            Some{e},
            Line.at_of(s, c, vs, k, e)(ev)(ha)
          ),
          {==}
        ),
        Core.cast(
          Maybe<&2, RKnown.Found>,
          f => {
            RAnswers.Reply.ask(
              f
            )
              == Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}}: Maybe<&2, Spec.Reply>
          },
          Some{RKnown.Found{k, e}},
          Answers.Line.find(s, c, RLines.Entry.id(e)),
          Equal.sym(
            Maybe<&2, RKnown.Found>,
            Answers.Line.find(s, c, RLines.Entry.id(e)),
            Some{RKnown.Found{k, e}},
            Line.find_at(s, c, vs, k, e)(ev)(ha)
          ),
          {==}
        )
      )

# the entry at version k of a line is made by its id, which asked for its
# request
def Core.at_made(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +e: Types.Entry
) -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> Mirror.Made(s, c, k, RLines.Entry.id(e), RAnswers.Entry.request(e)):
  ha => Core.at_made.of(s, c, k, e, Lines.Line.versions(s, c))({==})(ha)

# A reply fits its question
# -------------------------

# no reply fits nothing
def Fit.none(
  q: Spec.Question,
  -r: Spec.Reply
) -> {None{} == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  h => Empty.absurd(
    {Spec.Reply.fits(q, r) == True{}: Bool},
    Shared.Maybe.none_ne_some(Spec.Reply, r, h)
  )

# a reply that is x fits when x fits
def Fit.some(
  q: Spec.Question,
  -x: Spec.Reply,
  -r: Spec.Reply
) -> {
  Spec.Reply.fits(q, x) == True{}: Bool
} -> {Some{x} == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  hf => h =>
    %Shared.Maybe.some_inj(Spec.Reply, x, r, h): {Spec.Reply.fits(q, _) == True{}: Bool}
    hf

# a reply of an id fits a question that ids fit
def Fit.id(
  q: Spec.Question,
  m: Maybe<&2, Types.Entry>,
  -r: Spec.Reply
) -> (
  @x: Ledgers.Id -> {Spec.Reply.fits(q, Spec.Reply.Id{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.id(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{e}:
      f => Fit.some(q, Spec.Reply.Id{RLines.Entry.id(e)}, r)(f(RLines.Entry.id(e)))

# a reply of a request fits a question that requests fit
def Fit.ask(
  q: Spec.Question,
  m: Maybe<&2, RKnown.Found>,
  -r: Spec.Reply
) -> (
  @x: Spec.Request -> {Spec.Reply.fits(q, Spec.Reply.Ask{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.ask(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{RKnown.Found{k, e}}:
      f => Fit.some(q, Spec.Reply.Ask{RAnswers.Entry.request(e)}, r)(f(RAnswers.Entry.request(e)))

# a reply of a count fits a question that numbers fit
def Fit.count(
  q: Spec.Question,
  m: Maybe<&2, List<&2, Types.Entry>>,
  -r: Spec.Reply
) -> (
  @x: Nat -> {Spec.Reply.fits(q, Spec.Reply.Number{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.count(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{vs}:
      f => Fit.some(
        q,
        Spec.Reply.Number{List.length(&2, Types.Entry, vs)},
        r
      )(f(List.length(&2, Types.Entry, vs)))

# a reply of names fits a question that names fit
def Fit.names(
  q: Spec.Question,
  m: Maybe<&2, List<&2, String>>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.names(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{ns}:
      f => Fit.some(q, Spec.Reply.Names{ns}, r)(f(ns))

# a reply of a number fits a question that numbers fit
def Fit.number(
  q: Spec.Question,
  m: Maybe<&2, Nat>,
  -r: Spec.Reply
) -> (
  @x: Nat -> {Spec.Reply.fits(q, Spec.Reply.Number{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.number(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{k}:
      f => Fit.some(q, Spec.Reply.Number{k}, r)(f(k))

# a reply of a point fits a question that points fit
def Fit.point(
  q: Spec.Question,
  m: Maybe<&2, Spec.Point>,
  -r: Spec.Reply
) -> (
  @x: Spec.Point -> {Spec.Reply.fits(q, Spec.Reply.Point{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.point(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{x}:
      f => Fit.some(q, Spec.Reply.Point{x}, r)(f(x))

# a reply of a hash fits a question that hashes fit
def Fit.hash(
  q: Spec.Question,
  m: Maybe<&2, Files.Files()>,
  -r: Spec.Reply
) -> (
  @x: Hashes.Hash -> {Spec.Reply.fits(q, Spec.Reply.Hash{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.hash(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{t}:
      f => Fit.some(q, Spec.Reply.Hash{Files.Files.hash(t)}, r)(f(Files.Files.hash(t)))

# a reply of a yes fits a question that a yes fits
def Fit.yes(
  q: Spec.Question,
  m: Maybe<&2, Bool>,
  -r: Spec.Reply
) -> (
  @x: Bool -> {Spec.Reply.fits(q, Spec.Reply.Yes{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.yes(m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{y}:
      f => Fit.some(q, Spec.Reply.Yes{y}, r)(f(y))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# a reply of parents fits a question that points fit
def Fit.parents(
  q: Spec.Question,
  c: Ledgers.Line,
  k: Nat,
  m: Maybe<&2, Types.Entry>,
  -r: Spec.Reply
) -> (
  @x: List<&2, Spec.Point> -> {Spec.Reply.fits(q, Spec.Reply.Points{x}) == True{}: Bool}
) -> {
  RAnswers.Reply.parents(c, k, m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{e}:
      f => Fit.some(
        q,
        Spec.Reply.Points{RContents.Entry.parents(c, k, e)},
        r
      )(f(RContents.Entry.parents(c, k, e)))

# a reply of a status fits a question that a status fits
def Fit.status(
  q: Spec.Question,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, RKnown.Found>,
  -r: Spec.Reply
) -> (
  @x: Spec.Status -> {Spec.Reply.fits(q, Spec.Reply.Status{x}) == True{}: Bool}
) -> {
  Answers.Reply.status(s, c, v, m) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match v m:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{vs} None{}:
      f => Fit.none(q, r)
    case Some{+vs} Some{RKnown.Found{+k, +e}}:
      f => Fit.some(
        q,
        Spec.Reply.Status{Answers.Status.of(s, c, vs, k, e)},
        r
      )(f(Answers.Status.of(s, c, vs, k, e)))

# the reply of the nodes of a rule fits a question that names fit
def Fit.group(
  q: Spec.Question,
  u: Maybe<&2, RLines.Rule>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {
  Maybe.bind(&2, RLines.Rule, Spec.Reply, u, RAnswers.Rule.group) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match u:
    case None{}:
      f => Fit.none(q, r)
    case Some{RLines.Rule{None{}, ns}}:
      f => Fit.none(q, r)
    case Some{RLines.Rule{Some{g}, ns}}:
      f => Fit.some(q, Spec.Reply.Names{ns}, r)(f(ns))

# the reply of the owner of a rule fits a question that a name fits
def Fit.owner(
  q: Spec.Question,
  u: Maybe<&2, RLines.Rule>,
  -r: Spec.Reply
) -> (
  @x: String -> {Spec.Reply.fits(q, Spec.Reply.Name{x}) == True{}: Bool}
) -> {
  Maybe.bind(&2, RLines.Rule, Spec.Reply, u, RAnswers.Rule.owner) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match u:
    case None{}:
      f => Fit.none(q, r)
    case Some{RLines.Rule{None{}, ns}}:
      f => Fit.none(q, r)
    case Some{RLines.Rule{Some{g}, ns}}:
      f => Fit.some(q, Spec.Reply.Name{g}, r)(f(g))

# a reply given when b holds fits when it fits
def Fit.when(
  q: Spec.Question,
  b: Bool,
  -x: Spec.Reply,
  -r: Spec.Reply
) -> {
  Spec.Reply.fits(q, x) == True{}: Bool
} -> {
  Shared.Maybe.when(Spec.Reply, b, u => Some{x}) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match b:
    case True{}:
      Fit.some(q, x, r)
    case False{}:
      hf => Fit.none(q, r)

# the reply of the voters of a version fits a question that names fit
def Fit.owners(
  q: Spec.Question,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>,
  u: Maybe<&2, RLines.Rule>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {
  Answers.Owners.of(s, c, m, u) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m u:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{e} None{}:
      f => Fit.none(q, r)
    case Some{Types.Entry{+pk, +k}} Some{RLines.Rule{g, +ns}}:
      f => Fit.when(
        q,
        Shared.Bool.when(
          Bool,
          Bool.not(List.is_empty(&2, String, ns)),
          un => RRounds.Slot.backed(
            Rounds.Slot.ballots(s, c, k),
            ns,
            k,
            Lists.List.lead(String, ns),
            pk
          ),
          un => False{}
        ),
        Spec.Reply.Names{Lists.List.lead(String, ns)},
        r
      )(f(Lists.List.lead(String, ns)))

# Fit.affects, once the reached paths seen are known
def Fit.affects.at(
  q: Spec.Question,
  a: Files.Files(),
  b: Files.Files(),
  seen: List<&2, String>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {
  Some{
    Spec.Reply.Names{RAnswers.Delta.changed(RAnswers.Delta{a, b}, seen)}
  }
    == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  f => Fit.some(
    q,
    Spec.Reply.Names{RAnswers.Delta.changed(RAnswers.Delta{a, b}, seen)},
    r
  )(f(RAnswers.Delta.changed(RAnswers.Delta{a, b}, seen)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the reply of the paths that changed fits a question that names fit
def Fit.affects(
  q: Spec.Question,
  old: Maybe<&2, Files.Files()>,
  new: Maybe<&2, Files.Files()>,
  us: List<&2, String>,
  bs: List<&2, String>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {
  RAnswers.Affects.of(old, new, us, bs) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match old new:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{a} None{}:
      f => Fit.none(q, r)
    case Some{a} Some{+b}:
      Fit.affects.at(q, a, b, RAnswers.Reach.of(b, bs, us), r)

# A reply fits its question.
def Core.answer_fits(
  +s: Facts.Facts(),
  +q: Spec.Question,
  +r: Spec.Reply
) -> {
  Answers.Answer.of(s, q) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match q:
    case Spec.Question.Status{c, i}:
      Fit.status(
        Spec.Question.Status{c, i},
        s,
        c,
        Lines.Line.versions(s, c),
        Answers.Line.find(s, c, i),
        r
      )(x => {==})
    case Spec.Question.Request{c, i}:
      Fit.ask(Spec.Question.Request{c, i}, Answers.Line.find(s, c, i), r)(x => {==})
    case Spec.Question.Version{c, k}:
      Fit.id(Spec.Question.Version{c, k}, Lines.Line.at(s, c, k), r)(x => {==})
    case Spec.Question.Content{c, k}:
      Fit.hash(Spec.Question.Content{c, k}, Contents.Content.of(s, c, k), r)(x => {==})
    case Spec.Question.Group{c, k}:
      Fit.group(Spec.Question.Group{c, k}, Answers.Rule.for(s, c, k), r)(x => {==})
    case Spec.Question.Owners{c, k}:
      Fit.owners(
        Spec.Question.Owners{c, k},
        s,
        c,
        Lines.Line.at(s, c, k),
        Answers.Rule.for(s, c, k),
        r
      )(x => {==})
    case Spec.Question.Members{h, g, m}:
      Fit.names(
        Spec.Question.Members{h, g, m},
        Answers.Store.read(List<&2, String>, s, h, m, R => Groups.Groups.members(R, h, g, m)),
        r
      )(x => {==})
    case Spec.Question.Nodes{h, g, m}:
      Fit.names(
        Spec.Question.Nodes{h, g, m},
        Answers.Store.read(List<&2, String>, s, h, m, R => Groups.Groups.nodes(R, h, g, m)),
        r
      )(x => {==})
    case Spec.Question.IsGroup{h, g, m}:
      Fit.yes(
        Spec.Question.IsGroup{h, g, m},
        Answers.Store.read(Bool, s, h, m, R => Groups.Groups.is_group(R, h, g, m)),
        r
      )(x => {==})
    case Spec.Question.Mark{c, m}:
      Fit.number(
        Spec.Question.Mark{c, m},
        RAnswers.Mark.of(m, Lines.Line.versions(s, c)),
        r
      )(x => {==})
    case Spec.Question.Count{c}:
      Fit.count(Spec.Question.Count{c}, Lines.Line.versions(s, c), r)(x => {==})
    case Spec.Question.Clashes{c, i}:
      Fit.names(
        Spec.Question.Clashes{c, i},
        RAnswers.Found.then(
          List<&2, String>,
          Answers.Line.find(s, c, i),
          k => e => Answers.Clashes.of(s, c, k, e)
        ),
        r
      )(x => {==})
    case Spec.Question.Affects{c, a, b, us, bs}:
      Fit.affects(
        Spec.Question.Affects{c, a, b, us, bs},
        Contents.Content.of(s, c, a),
        Contents.Content.of(s, c, b),
        us,
        bs,
        r
      )(x => {==})
    case Spec.Question.Parents{c, k}:
      Fit.parents(Spec.Question.Parents{c, k}, c, k, Lines.Line.at(s, c, k), r)(x => {==})
    case Spec.Question.Base{c, i}:
      Fit.point(
        Spec.Question.Base{c, i},
        RAnswers.Found.then(
          Spec.Point,
          Answers.Line.find(s, c, i),
          k => e => Answers.Base.of(s, c, k, e)
        ),
        r
      )(x => {==})
    case Spec.Question.Owner{c, k}:
      Fit.owner(Spec.Question.Owner{c, k}, Answers.Rule.for(s, c, k), r)(x => {==})
    case Spec.Question.Era{c, k}:
      Fit.number(Spec.Question.Era{c, k}, Answers.Era.for(s, c, k), r)(x => {==})

# A request counts once
# ---------------------

# the id of version k of the versions of a line is first at k
def Entries.id_index(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +i: Ledgers.Id,
  m: Maybe<&2, Types.Entry>
) -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> {
  List.get(&2, Types.Entry, vs, k) == m: Maybe<&2, Types.Entry>
} -> {
  RAnswers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == Some{k}: Maybe<&2, Nat>
}:
  match m:
    case None{}:
      hv => hg => h => Empty.absurd(
        {
          Lists.List.index(
            ~Types.Entry,
            ~Ledgers.Id,
            ~RLines.Entry.is_of,
            vs,
            i
          )
            == Some{k}: Maybe<&2, Nat>
        },
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h)
      )
    case Some{+e}:
      hv => hg => h => Core.cast(
        Ledgers.Id,
        x => {
          Lists.List.index(
            ~Types.Entry,
            ~Ledgers.Id,
            ~RLines.Entry.is_of,
            vs,
            x
          )
            == Some{k}: Maybe<&2, Nat>
        },
        RLines.Entry.id(e),
        i,
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Ledgers.Id,
          x => Reply.to_id(x, i),
          Some{Spec.Reply.Id{RLines.Entry.id(e)}},
          Some{Spec.Reply.Id{i}},
          h
        ),
        Versions.Line.versions_index(s, c, vs, k, e)(hv)(hg)
      )

# Core.counts_once, once the versions of the line (v) are known
def Core.counts_once.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Nat,
  +b: Nat,
  v: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {
  RAnswers.Reply.id(RLines.Line.at.of(v, a)) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.id(RLines.Line.at.of(v, b)) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {a == b: Nat}:
  match v:
    case None{}:
      ev => h1 => h2 => Empty.absurd(
        {a == b: Nat},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h1)
      )
    case Some{+vs}:
      +ev => h1 => h2 => Shared.Maybe.some_inj(
        Nat,
        a,
        b,
        Equal.trans(
          Maybe<&2, Nat>,
          Some{a},
          Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
          Some{b},
          Equal.sym(
            Maybe<&2, Nat>,
            Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
            Some{a},
            Entries.id_index(s, c, vs, a, i, List.get(&2, Types.Entry, vs, a))(ev)({==})(h1)
          ),
          Entries.id_index(s, c, vs, b, i, List.get(&2, Types.Entry, vs, b))(ev)({==})(h2)
        )
      )

# A request counts once: it makes at most one version of a line.
def Core.counts_once(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +a: Nat,
  +b: Nat
) -> {
  Answers.Answer.of(s, Spec.Question.Version{c, a}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(s, Spec.Question.Version{c, b}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {a == b: Nat}:
  h1 => h2 => Core.counts_once.of(s, c, i, a, b, Lines.Line.versions(s, c))({==})(h1)(h2)

# Found entries
# -------------

# the version of the found entry m, or d
def Found.to_n(m: Maybe<&2, RKnown.Found>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{RKnown.Found{k, e}}:
      k

# the entry of the found entry m
def Found.to_entry(m: Maybe<&2, RKnown.Found>) -> Maybe<&2, Types.Entry>:
  match m:
    case None{}:
      None{}
    case Some{RKnown.Found{k, e}}:
      Some{e}

# an entry found as version k is version k, the entry g
def Found.map_some(
  +k: Nat,
  -n: Nat,
  -e: Types.Entry,
  g: Maybe<&2, Types.Entry>
) -> {
  Maybe.map(
    &2,
    Types.Entry,
    RKnown.Found,
    e2 => RKnown.Found{k, e2},
    g
  )
    == Some{RKnown.Found{n, e}}: Maybe<&2, RKnown.Found>
} -> {k == n: Nat}
  & {g == Some{e}: Maybe<&2, Types.Entry>}:
  match g:
    case None{}:
      h => Empty.absurd(
        {k == n: Nat} & {None{} == Some{e}: Maybe<&2, Types.Entry>},
        Shared.Maybe.none_ne_some(RKnown.Found, RKnown.Found{n, e}, h)
      )
    case Some{e2}:
      +h => (
        Equal.cong(
          Maybe<&2, RKnown.Found>,
          Nat,
          x => Found.to_n(x, k),
          Some{RKnown.Found{k, e2}},
          Some{RKnown.Found{n, e}},
          h
        ),
        Equal.cong(
          Maybe<&2, RKnown.Found>,
          Maybe<&2, Types.Entry>,
          Found.to_entry,
          Some{RKnown.Found{k, e2}},
          Some{RKnown.Found{n, e}},
          h
        )
      )

# Entries.find_some.at, with its two facts as a pair
def Entries.find_some.by(
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  -n: Nat,
  -e: Types.Entry,
  w: {k == n: Nat} & {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
) -> {
  Some{k} == Some{n}: Maybe<&2, Nat>
}
  & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  (+ek, hg) = w
  (
    Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, k, n, ek),
    Core.cast(
      Nat,
      x => {List.get(&2, Types.Entry, vs, x) == Some{e}: Maybe<&2, Types.Entry>},
      k,
      n,
      ek,
      hg
    )
  )

# Entries.find_some, once the index m of the id is known
def Entries.find_some.at(
  +vs: List<&2, Types.Entry>,
  m: Maybe<&2, Nat>,
  -n: Nat,
  -e: Types.Entry
) -> {
  RAnswers.Versions.find.at(vs, m) == Some{RKnown.Found{n, e}}: Maybe<&2, RKnown.Found>
} -> {
  m == Some{n}: Maybe<&2, Nat>
}
  & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {
          None{} == Some{n}: Maybe<&2, Nat>
        }
          & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>},
        Shared.Maybe.none_ne_some(RKnown.Found, RKnown.Found{n, e}, h)
      )
    case Some{+k}:
      h => Entries.find_some.by(
        vs,
        k,
        n,
        e,
        Found.map_some(k, n, e, List.get(&2, Types.Entry, vs, k))(h)
      )

# the entry found for an id among versions is at the first index of the id
def Entries.find_some(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  -n: Nat,
  -e: Types.Entry
) -> {
  RAnswers.Versions.find(vs, i) == Some{RKnown.Found{n, e}}: Maybe<&2, RKnown.Found>
} -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i) == Some{n}: Maybe<&2, Nat>
}
  & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  h => Entries.find_some.at(
    vs,
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i),
    n,
    e
  )(h)

# Entries.find_id.by, with the element at the index of the id
def Entries.find_id.at(
  -vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  -n: Nat,
  +e: Types.Entry,
  hg: {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>},
  w: Exists(
    Types.Entry,
    x => {
      List.get(&2, Types.Entry, vs, n) == Some{x}: Maybe<&2, Types.Entry>
    }
      & {RLines.Entry.is_of(i, x) == True{}: Bool}
  )
) -> {RLines.Entry.id(e) == i: Ledgers.Id}:
  (x, w1) = w
  (hx, ho) = w1
  Ledgers.Id.is_eq_sound(
    RLines.Entry.id(e),
    i
  )(
    Core.cast(
      Types.Entry,
      y => {RLines.Entry.is_of(i, y) == True{}: Bool},
      x,
      e,
      Shared.Maybe.some_inj(
        Types.Entry,
        x,
        e,
        Equal.trans(
          Maybe<&2, Types.Entry>,
          Some{x},
          List.get(&2, Types.Entry, vs, n),
          Some{e},
          Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, vs, n), Some{x}, hx),
          hg
        )
      ),
      ho
    )
  )

# Entries.find_id, with the two facts of the found entry as a pair
def Entries.find_id.by(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  -n: Nat,
  +e: Types.Entry,
  w: {
    Lists.List.index(
      ~Types.Entry,
      ~Ledgers.Id,
      ~RLines.Entry.is_of,
      vs,
      i
    )
      == Some{n}: Maybe<&2, Nat>
  }
    & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}
) -> {
  List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>
}
  & {RLines.Entry.id(e) == i: Ledgers.Id}:
  (hi, +hg) = w
  (
    hg,
    Entries.find_id.at(
      vs,
      i,
      n,
      e,
      hg,
      Lists.List.index_get(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, i, n)(hi)
    )
  )

# the entry found for the id i among versions is version n of them, of the id i
def Entries.find_id(
  +vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  -n: Nat,
  +e: Types.Entry
) -> {
  RAnswers.Versions.find(vs, i) == Some{RKnown.Found{n, e}}: Maybe<&2, RKnown.Found>
} -> {
  List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>
}
  & {RLines.Entry.id(e) == i: Ledgers.Id}:
  h => Entries.find_id.by(vs, i, n, e, Entries.find_some(vs, i, n, e)(h))

# A request that is Written made a version
# ----------------------------------------

# Core.written_made.of, with the two facts of the found entry as a pair
def Core.written_made.by(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  -vs: List<&2, Types.Entry>,
  +n: Nat,
  +e: Types.Entry,
  ev: {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  w: {
    List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>
  }
    & {RLines.Entry.id(e) == i: Ledgers.Id}
) -> Exists(
  Nat,
  k => {
    Answers.Answer.of(
      s,
      Spec.Question.Version{c, k}
    )
      == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
  }
):
  (hg, hi) = w
  (
    n,
    Core.cast(
      Maybe<&2, Types.Entry>,
      m => {RAnswers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>},
      Some{e},
      Lines.Line.at(s, c, n),
      Equal.sym(
        Maybe<&2, Types.Entry>,
        Lines.Line.at(s, c, n),
        Some{e},
        Line.at_of(s, c, vs, n, e)(ev)(hg)
      ),
      Equal.cong(
        Ledgers.Id,
        Maybe<&2, Spec.Reply>,
        x => Some{Spec.Reply.Id{x}},
        RLines.Entry.id(e),
        i,
        hi
      )
    )
  )

# Core.written_made, once the versions of the line (v) and the found entry
# (f) are known
def Core.written_made.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  v: Maybe<&2, List<&2, Types.Entry>>,
  f: Maybe<&2, RKnown.Found>
) -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {
  RAnswers.Line.find.of(i, v) == f: Maybe<&2, RKnown.Found>
} -> {
  Answers.Reply.status(
    s,
    c,
    v,
    f
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  k => {
    Answers.Answer.of(
      s,
      Spec.Question.Version{c, k}
    )
      == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
  }
):
  match v f:
    case None{} None{}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {
            Answers.Answer.of(
              s,
              Spec.Question.Version{c, k}
            )
              == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case None{} Some{x}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {
            Answers.Answer.of(
              s,
              Spec.Question.Version{c, k}
            )
              == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case Some{vs} None{}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {
            Answers.Answer.of(
              s,
              Spec.Question.Version{c, k}
            )
              == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
          }
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case Some{+vs} Some{RKnown.Found{+n, +e}}:
      ev => ef => h => Core.written_made.by(s, c, i, vs, n, e, ev, Entries.find_id(vs, i, n, e)(ef))

# A request that is Written made a version.
def Core.written_made(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Status{c, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  k => {
    Answers.Answer.of(
      s,
      Spec.Question.Version{c, k}
    )
      == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
  }
):
  h => Core.written_made.of(
    s,
    c,
    i,
    Lines.Line.versions(s, c),
    Answers.Line.find(s, c, i)
  )({==})({==})(h)

# A mark that is Written names its version
# ----------------------------------------

# the status x is Written
def Status.is_written(x: Spec.Status) -> Bool:
  match x:
    case Spec.Status.Written{}:
      True{}
    case _:
      False{}

# a status picked by b is Written only when b holds, if the other is not
def Status.pick_written(
  b: Bool,
  -x: Spec.Status
) -> {
  Status.is_written(x) == False{}: Bool
} -> {
  Bool.pick(Spec.Status, b, Spec.Status.Written{}, x) == Spec.Status.Written{}: Spec.Status
} -> {b == True{}: Bool}:
  match b:
    case True{}:
      hx => h => {==}
    case False{}:
      hx => h => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Status.is_written(x),
            True{},
            Equal.sym(Bool, Status.is_written(x), False{}, hx),
            Equal.cong(Spec.Status, Bool, Status.is_written, x, Spec.Status.Written{}, h)
          )
        )
      )

# Core.mark_names.of, with the two facts of the found entry as a pair
def Core.mark_names.by(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +m: String,
  +v: Nat,
  +vs: List<&2, Types.Entry>,
  +n: Nat,
  +e: Types.Entry,
  w: {
    List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>
  }
    & {RLines.Entry.id(e) == RLines.Entry.id(e): Ledgers.Id},
  hq: {RAnswers.Entry.request(e) == Spec.Request.Mark{c, m, v}: Spec.Request},
  hs: {Answers.Status.of(s, c, vs, n, e) == Spec.Status.Written{}: Spec.Status}
) -> {
  RAnswers.Reply.number(
    RAnswers.Mark.of(m, Some{vs})
  )
    == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
}:
  (hg, hi) = w
  +hq = hq
  %Equal.sym(
    Maybe<&2, Nat>,
    Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m),
    Some{n},
    Shared.Maybe.is_eq_sound(
      ~Nat,
      ~Nat.is_eq,
      x => y => Shared.Nat.is_eq_sound(x, y),
      Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m),
      Some{n}
    )(
      Status.pick_written(
        Shared.Maybe.is_eq(
          ~Nat,
          ~Nat.is_eq,
          Lists.List.index(~Types.Entry, ~String, ~RAnswers.Entry.marks, vs, m),
          Some{n}
        ),
        Spec.Status.Stale{}
      )(
        {==}
      )(
        Core.cast(
          Spec.Request,
          rq => {
            RAnswers.Status.by(
              vs,
              n,
              RLines.Entry.id(e),
              rq,
              Answers.Clashes.of(s, c, n, e)
            )
              == Spec.Status.Written{}: Spec.Status
          },
          RAnswers.Entry.request(e),
          Spec.Request.Mark{c, m, v},
          hq,
          hs
        )
      )
    )
  ): {
    RAnswers.Reply.number(
      RAnswers.Mark.at(vs, _)
    )
      == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
  }
  %Equal.sym(
    Maybe<&2, Types.Entry>,
    List.get(&2, Types.Entry, vs, n),
    Some{e},
    hg
  ): {
    RAnswers.Reply.number(RAnswers.Mark.in(_)) == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
  }
  %Equal.sym(
    Spec.Request,
    RAnswers.Entry.request(e),
    Spec.Request.Mark{c, m, v},
    hq
  ): {
    RAnswers.Reply.number(
      RAnswers.Request.marked(_)
    )
      == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
  }
  {==}

# Core.mark_names, once the versions of the line (vv) and the found entry (f)
# are known
def Core.mark_names.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +m: String,
  +v: Nat,
  vv: Maybe<&2, List<&2, Types.Entry>>,
  f: Maybe<&2, RKnown.Found>
) -> {
  RAnswers.Line.find.of(i, vv) == f: Maybe<&2, RKnown.Found>
} -> {
  Answers.Reply.status(
    s,
    c,
    vv,
    f
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.ask(f) == Some{Spec.Reply.Ask{Spec.Request.Mark{c, m, v}}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.number(
    RAnswers.Mark.of(m, vv)
  )
    == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
}:
  match vv f:
    case None{} None{}:
      ef => hs => hq => Empty.absurd(
        {
          RAnswers.Reply.number(
            RAnswers.Mark.of(m, None{})
          )
            == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
        },
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case None{} Some{x}:
      ef => hs => hq => Empty.absurd(
        {
          RAnswers.Reply.number(
            RAnswers.Mark.of(m, None{})
          )
            == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
        },
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case Some{vs} None{}:
      ef => hs => hq => Empty.absurd(
        {
          RAnswers.Reply.number(
            RAnswers.Mark.of(m, Some{vs})
          )
            == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
        },
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case Some{+vs} Some{RKnown.Found{+n, +e}}:
      ef => hs => hq => Core.mark_names.by(
        s,
        c,
        m,
        v,
        vs,
        n,
        e,
        (
          Pair.fst(
            {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>},
            {RLines.Entry.id(e) == i: Ledgers.Id},
            Entries.find_id(vs, i, n, e)(ef)
          ),
          {==}
        ),
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Spec.Request,
          x => Reply.to_ask(x, Spec.Request.Mark{c, m, v}),
          Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}},
          Some{Spec.Reply.Ask{Spec.Request.Mark{c, m, v}}},
          hq
        ),
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Spec.Status,
          x => Reply.to_status(x, Spec.Status.Written{}),
          Some{Spec.Reply.Status{Answers.Status.of(s, c, vs, n, e)}},
          Some{Spec.Reply.Status{Spec.Status.Written{}}},
          hs
        )
      )

# A mark that is Written names its version for good.
def Core.mark_names(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +m: String,
  +v: Nat
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Status{c, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Request{c, i}
  )
    == Some{Spec.Reply.Ask{Spec.Request.Mark{c, m, v}}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Mark{c, m}
  )
    == Some{Spec.Reply.Number{v}}: Maybe<&2, Spec.Reply>
}:
  hs => hq => Core.mark_names.of(
    s,
    c,
    i,
    m,
    v,
    Lines.Line.versions(s, c),
    Answers.Line.find(s, c, i)
  )({==})(hs)(hq)

# A merge is Written once its clashes are resolved
# ------------------------------------------------

# List.some_at, from the tail of a list to the list
def List.some_at.up(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  -z: A,
  -r: List<&2, A>,
  -g: V,
  w: Exists(
    Nat,
    k => Exists(
      A,
      x => {List.get(&2, A, r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
    )
  )
) -> Exists(
  Nat,
  k => Exists(
    A,
    x => {List.get(&2, A, z <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
  )
):
  (k, w1) = w
  (1n+k, w1)

# a list that p holds of some element of holds, at some index, an element
# that p holds of
def List.some_at(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  xs: List<&2, A>,
  +g: V
) -> {
  Shared.List.some(~A, ~V, ~p, xs, g) == True{}: Bool
} -> Exists(
  Nat,
  k => Exists(A, x => {List.get(&2, A, xs, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool})
):
  match xs:
    case Nil{}:
      h => Empty.absurd(
        Exists(
          Nat,
          k => Exists(
            A,
            x => {List.get(&2, A, [], k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
          )
        ),
        Shared.Bool.false_ne_true(h)
      )
    case Con{+z, +r}:
      Lists.Bool.by(
        b => {
          List.any.if(u => Shared.List.some(~A, ~V, ~p, r, g), b) == True{}: Bool
        } -> Exists(
          Nat,
          k => Exists(
            A,
            x => {List.get(&2, A, z <> r, k) == Some{x}: Maybe<&2, A>} & {p(g)(x) == True{}: Bool}
          )
        ),
        p(g)(z),
        et => h => (0n, (z, ({==}, et))),
        ef => h => List.some_at.up(~A, ~V, ~p, z, r, g, List.some_at(~A, ~V, ~p, r, g)(h))
      )

# a request that resolves the path p of the merge i
def Request.Resolves(i: Ledgers.Id, p: String, r: Spec.Request) -> Type:
  Exists(Maybe<&2, List<&2, U32>>, ws => {r == Spec.Request.Resolve{i, p, ws}: Spec.Request})

# a request that resolves the path p of the merge i is a Resolve of them
def Request.resolves_is(
  +i: Ledgers.Id,
  +p: String,
  r: Spec.Request
) -> {RAnswers.Request.resolves(i, p, r) == True{}: Bool} -> Request.Resolves(i, p, r):
  match r:
    case Spec.Request.Start{os}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Start{os}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Write{b, q, ws}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Write{b, q, ws}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Merge{f, x}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Merge{f, x}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Resolve{+m, +q, +w}:
      +h => (w, (
          %Ledgers.Id.is_eq_sound(m, i)(Shared.Bool.and_true_left(Ledgers.Id.is_eq(m, i), String.eq(q, p))(h)): {Spec.Request.Resolve{m, q, w} == Spec.Request.Resolve{_, p, w}: Spec.Request}
          %Texts.String.eq_sound(q, p)(Shared.Bool.and_true_right(Ledgers.Id.is_eq(m, i), String.eq(q, p))(h)): {Spec.Request.Resolve{m, q, w} == Spec.Request.Resolve{m, _, w}: Spec.Request}
          {==}))
    case Spec.Request.Mark{b, name, v}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Mark{b, name, v}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{b, t, v}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Move{b, t, v}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Group{st, name, ms}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Group{st, name, ms}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{l, g}:
      h => Empty.absurd(
        Request.Resolves(i, p, Spec.Request.Own{l, g}),
        Shared.Bool.false_ne_true(h)
      )

# a version of the line c is a decided Resolve of the path p of the merge i
def Core.Resolved(s: Facts.Facts(), c: Ledgers.Line, i: Ledgers.Id, p: String) -> Type:
  Exists(
    Nat,
    k => Exists(
      Ledgers.Id,
      j => Exists(
        Maybe<&2, List<&2, U32>>,
        ws => Mirror.Made(s, c, k, j, Spec.Request.Resolve{i, p, ws})
      )
    )
  )

# Core.merge_resolved.at, with the version k (the entry x) that resolves
def Core.merge_resolved.by(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +p: String,
  +k: Nat,
  +x: Types.Entry,
  ha: {Lines.Line.at(s, c, k) == Some{x}: Maybe<&2, Types.Entry>},
  w: Request.Resolves(i, p, RAnswers.Entry.request(x))
) -> Core.Resolved(s, c, i, p):
  (+ws, he) = w
  (
    k,
    (
      RLines.Entry.id(x),
      (
        ws,
        Core.cast(
          Spec.Request,
          rq => Mirror.Made(s, c, k, RLines.Entry.id(x), rq),
          RAnswers.Entry.request(x),
          Spec.Request.Resolve{i, p, ws},
          he,
          Core.at_made(s, c, k, x)(ha)
        )
      )
    )
  )

# a version among vs that resolves the path p of the merge i is a decided
# Resolve of them
def Core.merge_resolved.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +p: String,
  +vs: List<&2, Types.Entry>,
  ev: {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  w: Exists(
    Nat,
    k => Exists(
      Types.Entry,
      x => {
        List.get(&2, Types.Entry, vs, k) == Some{x}: Maybe<&2, Types.Entry>
      }
        & {RAnswers.Entry.resolves(RAnswers.Clash{i, p}, x) == True{}: Bool}
    )
  )
) -> Core.Resolved(s, c, i, p):
  (+k, w1) = w
  (+x, w2) = w1
  (hg, hx) = w2
  Core.merge_resolved.by(
    s,
    c,
    i,
    p,
    k,
    x,
    Line.at_of(s, c, vs, k, x)(ev)(hg),
    Request.resolves_is(i, p, RAnswers.Entry.request(x))(hx)
  )

# a reply of names comes from those names
def Reply.names_some(
  m: Maybe<&2, List<&2, String>>,
  -ps: List<&2, String>
) -> {
  RAnswers.Reply.names(m) == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> {m == Some{ps}: Maybe<&2, List<&2, String>>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{ps}: Maybe<&2, List<&2, String>>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{ps}, h)
      )
    case Some{ns}:
      h => Equal.cong(
        Maybe<&2, Spec.Reply>,
        Maybe<&2, List<&2, String>>,
        x => Some{Reply.to_names(x, ps)},
        Some{Spec.Reply.Names{ns}},
        Some{Spec.Reply.Names{ps}},
        h
      )

# Core.merge_resolved.of, with the facts of the found entry
def Core.merge_resolved.in(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +f: Ledgers.Line,
  +ps: List<&2, String>,
  +p: String,
  +vs: List<&2, Types.Entry>,
  +n: Nat,
  +e: Types.Entry,
  ev: {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>},
  w: {
    List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>
  }
    & {RLines.Entry.id(e) == i: Ledgers.Id},
  hq: {RAnswers.Entry.request(e) == Spec.Request.Merge{f, c}: Spec.Request},
  hs: {Answers.Status.of(s, c, vs, n, e) == Spec.Status.Written{}: Spec.Status},
  hc: {Answers.Clashes.of(s, c, n, e) == Some{ps}: Maybe<&2, List<&2, String>>},
  hp: {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}
) -> Core.Resolved(s, c, i, p):
  (hg, hi) = w
  Core.merge_resolved.at(
    s,
    c,
    i,
    p,
    vs,
    ev,
    List.some_at(
      ~Types.Entry,
      ~RAnswers.Clash,
      ~RAnswers.Entry.resolves,
      vs,
      RAnswers.Clash{i, p}
    )(
      Core.cast(
        Ledgers.Id,
        j => {RAnswers.Resolved.has(RAnswers.Resolved{vs, j}, p) == True{}: Bool},
        RLines.Entry.id(e),
        i,
        hi,
        Lists.List.holds_in(
          ~String,
          ~RAnswers.Resolved,
          ~RAnswers.Resolved.has,
          ~String.eq,
          ~Texts.String.laws(),
          ps,
          RAnswers.Resolved{vs, RLines.Entry.id(e)},
          p
        )(
          Status.pick_written(
            Shared.List.holds(
              ~String,
              ~RAnswers.Resolved,
              ~RAnswers.Resolved.has,
              ps,
              RAnswers.Resolved{vs, RLines.Entry.id(e)}
            ),
            Spec.Status.Conflicted{RLines.Entry.id(e)}
          )(
            {==}
          )(
            Core.cast(
              Maybe<&2, List<&2, String>>,
              cs => {
                RAnswers.Status.merge(
                  vs,
                  RLines.Entry.id(e),
                  cs
                )
                  == Spec.Status.Written{}: Spec.Status
              },
              Answers.Clashes.of(s, c, n, e),
              Some{ps},
              hc,
              Core.cast(
                Spec.Request,
                rq => {
                  RAnswers.Status.by(
                    vs,
                    n,
                    RLines.Entry.id(e),
                    rq,
                    Answers.Clashes.of(s, c, n, e)
                  )
                    == Spec.Status.Written{}: Spec.Status
                },
                RAnswers.Entry.request(e),
                Spec.Request.Merge{f, c},
                hq,
                hs
              )
            )
          )
        )(hp)
      )
    )
  )

# Core.merge_resolved, once the versions of the line (vv) and the found entry
# (fd) are known
def Core.merge_resolved.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +f: Ledgers.Line,
  +ps: List<&2, String>,
  +p: String,
  vv: Maybe<&2, List<&2, Types.Entry>>,
  fd: Maybe<&2, RKnown.Found>
) -> {
  Lines.Line.versions(s, c) == vv: Maybe<&2, List<&2, Types.Entry>>
} -> {
  RAnswers.Line.find.of(i, vv) == fd: Maybe<&2, RKnown.Found>
} -> {
  Answers.Reply.status(
    s,
    c,
    vv,
    fd
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.ask(fd) == Some{Spec.Reply.Ask{Spec.Request.Merge{f, c}}}: Maybe<&2, Spec.Reply>
} -> {
  RAnswers.Reply.names(
    RAnswers.Found.then(List<&2, String>, fd, k => e => Answers.Clashes.of(s, c, k, e))
  )
    == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool} -> Core.Resolved(s, c, i, p):
  match vv fd:
    case None{} None{}:
      ev => ef => hs => hq => hc => hp => Empty.absurd(
        Core.Resolved(s, c, i, p),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case None{} Some{x}:
      ev => ef => hs => hq => hc => hp => Empty.absurd(
        Core.Resolved(s, c, i, p),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case Some{vs} None{}:
      ev => ef => hs => hq => hc => hp => Empty.absurd(
        Core.Resolved(s, c, i, p),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, hs)
      )
    case Some{+vs} Some{RKnown.Found{+n, +e}}:
      ev => ef => hs => hq => hc => hp => Core.merge_resolved.in(
        s,
        c,
        i,
        f,
        ps,
        p,
        vs,
        n,
        e,
        ev,
        Entries.find_id(vs, i, n, e)(ef),
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Spec.Request,
          x => Reply.to_ask(x, Spec.Request.Merge{f, c}),
          Some{Spec.Reply.Ask{RAnswers.Entry.request(e)}},
          Some{Spec.Reply.Ask{Spec.Request.Merge{f, c}}},
          hq
        ),
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Spec.Status,
          x => Reply.to_status(x, Spec.Status.Written{}),
          Some{Spec.Reply.Status{Answers.Status.of(s, c, vs, n, e)}},
          Some{Spec.Reply.Status{Spec.Status.Written{}}},
          hs
        ),
        Reply.names_some(Answers.Clashes.of(s, c, n, e), ps)(hc),
        hp
      )

# A merge turns Written only once each resource that clashed in it is
# resolved.
def Core.merge_resolved(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +f: Ledgers.Line,
  +ps: List<&2, String>,
  +p: String
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Status{c, i}
  )
    == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Request{c, i}
  )
    == Some{Spec.Reply.Ask{Spec.Request.Merge{f, c}}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Clashes{c, i}
  )
    == Some{Spec.Reply.Names{ps}}: Maybe<&2, Spec.Reply>
} -> {
  List.contains(~String, ~String.eq, ps, p) == True{}: Bool
} -> Exists(
  Nat,
  k => Exists(
    Ledgers.Id,
    j => Exists(
      Maybe<&2, List<&2, U32>>,
      ws => Mirror.Made(s, c, k, j, Spec.Request.Resolve{i, p, ws})
    )
  )
):
  hs => hq => hc => hp => Core.merge_resolved.of(
    s,
    c,
    i,
    f,
    ps,
    p,
    Lines.Line.versions(s, c),
    Answers.Line.find(s, c, i)
  )({==})({==})(hs)(hq)(hc)(hp)

# A majority decides
# ------------------

# the nodes os are within the nodes gs, more than half of them, and the facts
# s hold a ballot of each of os
def Core.Majority(s: Facts.Facts(), os: List<&2, String>, gs: List<&2, String>) -> Type:
  {
    Shared.List.within(~String, ~String.eq, os, gs) == True{}: Bool
  }
    & (
      {
        Nat.is_lt(
          List.length(&2, String, gs),
          Nat.add(List.length(&2, String, os), List.length(&2, String, os))
        )
          == True{}: Bool
      }
        & (
          @v: String -> {
            List.contains(~String, ~String.eq, os, v) == True{}: Bool
          } -> Exists(
            Types.Change,
            ch => {
              Facts.Facts.holds(s, ch) == True{}: Bool
            }
              & Exists(
                List<&2, U32>,
                st => Exists(
                  List<&2, U32>,
                  x => {
                    RFacts.Change.ballot(ch) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                  }
                )
              )
          )
        )
    )

# a reply given when b holds is given only when b holds
def When.some(
  b: Bool,
  -x: Spec.Reply,
  -r: Spec.Reply
) -> {
  Shared.Maybe.when(Spec.Reply, b, u => Some{x}) == Some{r}: Maybe<&2, Spec.Reply>
} -> {b == True{}: Bool}
  & {Some{x} == Some{r}: Maybe<&2, Spec.Reply>}:
  match b:
    case True{}:
      h => ({==}, h)
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool} & {Some{x} == Some{r}: Maybe<&2, Spec.Reply>},
        Shared.Maybe.none_ne_some(Spec.Reply, r, h)
      )

# the change that a ballot of the node v for the slot k of the line c is
def Core.majority_decides.vote(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +v: String,
  w0: Exists(
    Nat,
    t => Exists(
      Types.Cast,
      x => {Facts.Facts.has(s, Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}) == True{}: Bool}
    )
  )
) -> Exists(
  Types.Change,
  ch => {
    Facts.Facts.holds(s, ch) == True{}: Bool
  }
    & Exists(
      List<&2, U32>,
      st => Exists(
        List<&2, U32>,
        x => {RFacts.Change.ballot(ch) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>}
      )
    )
):
  (+t, w1) = w0
  (+x, h) = w1
  (
    Types.Change.Fact{Types.Fact.Vote{v, Types.Step.At{c, k, t}, x}},
    (h, (Coded.Step.words(Types.Step.At{c, k, t}), (Coded.Cast.words(x), {==})))
  )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the first majority of the nodes ns that all voted for the pick pk at the
# slot k of the line c is a majority that decides
def Core.majority_decides.by(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +os: List<&2, String>,
  +gs: List<&2, String>,
  +pk: Types.Pick,
  +k: Nat,
  +ns: List<&2, String>,
  eg: {ns == gs: List<&2, String>},
  w: {
    Shared.Bool.when(
      Bool,
      Bool.not(List.is_empty(&2, String, ns)),
      un => RRounds.Slot.backed(
        Rounds.Slot.ballots(s, c, k),
        ns,
        k,
        Lists.List.lead(String, ns),
        pk
      ),
      un => False{}
    )
      == True{}: Bool
  }
    & {
      Some{
        Spec.Reply.Names{Lists.List.lead(String, ns)}
      }
        == Some{Spec.Reply.Names{os}}: Maybe<&2, Spec.Reply>
    }
) -> Core.Majority(s, os, gs):
  (hw, hn) = w
  +hb = Equal.trans(
    Bool,
    Bool.and(
      Bool.not(List.is_empty(&2, String, ns)),
      RRounds.Slot.backed(Rounds.Slot.ballots(s, c, k), ns, k, Lists.List.lead(String, ns), pk)
    ),
    Shared.Bool.when(
      Bool,
      Bool.not(List.is_empty(&2, String, ns)),
      un => RRounds.Slot.backed(
        Rounds.Slot.ballots(s, c, k),
        ns,
        k,
        Lists.List.lead(String, ns),
        pk
      ),
      un => False{}
    ),
    True{},
    Lists.Bool.and_when(
      Bool.not(List.is_empty(&2, String, ns)),
      un => RRounds.Slot.backed(
        Rounds.Slot.ballots(s, c, k),
        ns,
        k,
        Lists.List.lead(String, ns),
        pk
      )
    ),
    hw
  )
  Core.cast(
    List<&2, String>,
    x => Core.Majority(s, x, gs),
    Lists.List.lead(String, ns),
    os,
    Equal.cong(
      Maybe<&2, Spec.Reply>,
      List<&2, String>,
      x => Reply.to_names(x, os),
      Some{Spec.Reply.Names{Lists.List.lead(String, ns)}},
      Some{Spec.Reply.Names{os}},
      hn
    ),
    Core.cast(
      List<&2, String>,
      y => Core.Majority(s, Lists.List.lead(String, ns), y),
      ns,
      gs,
      eg,
      (
        Lists.List.lead_within(~String, ~String.eq, ~Texts.String.laws(), ns),
        (
          Lists.List.lead_most(
            String,
            ns
          )(
            Shared.Bool.not_true(
              List.is_empty(&2, String, ns)
            )(
              Shared.Bool.and_true_left(
                Bool.not(List.is_empty(&2, String, ns)),
                RRounds.Slot.backed(
                  Rounds.Slot.ballots(s, c, k),
                  ns,
                  k,
                  Lists.List.lead(String, ns),
                  pk
                )
              )(hb)
            )
          ),
          +v => hin => Core.majority_decides.vote(
            s,
            c,
            k,
            v,
            Rounds.Votes.backed_voted(
              s,
              c,
              k,
              ns,
              Lists.List.lead(String, ns),
              pk,
              v
            )(
              Shared.Bool.and_true_right(
                Bool.not(List.is_empty(&2, String, ns)),
                RRounds.Slot.backed(
                  Rounds.Slot.ballots(s, c, k),
                  ns,
                  k,
                  Lists.List.lead(String, ns),
                  pk
                )
              )(hb)
            )(hin)
          )
        )
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Core.majority_decides, once the entry of the version (m) and its rule (u)
# are known
def Core.majority_decides.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +os: List<&2, String>,
  +gs: List<&2, String>,
  m: Maybe<&2, Types.Entry>,
  u: Maybe<&2, RLines.Rule>
) -> {
  Answers.Owners.of(s, c, m, u) == Some{Spec.Reply.Names{os}}: Maybe<&2, Spec.Reply>
} -> {
  Maybe.bind(
    &2,
    RLines.Rule,
    Spec.Reply,
    u,
    RAnswers.Rule.group
  )
    == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
} -> Core.Majority(s, os, gs):
  match m u:
    case None{} None{}:
      h1 => h2 => Empty.absurd(
        Core.Majority(s, os, gs),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{os}, h1)
      )
    case None{} Some{x}:
      h1 => h2 => Empty.absurd(
        Core.Majority(s, os, gs),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{os}, h1)
      )
    case Some{e} None{}:
      h1 => h2 => Empty.absurd(
        Core.Majority(s, os, gs),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{os}, h1)
      )
    case Some{Types.Entry{pk, k}} Some{RLines.Rule{None{}, ns}}:
      h1 => h2 => Empty.absurd(
        Core.Majority(s, os, gs),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Names{gs}, h2)
      )
    case Some{Types.Entry{+pk, +k}} Some{RLines.Rule{Some{g}, +ns}}:
      h1 => h2 => Core.majority_decides.by(
        s,
        c,
        os,
        gs,
        pk,
        k,
        ns,
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          List<&2, String>,
          x => Reply.to_names(x, gs),
          Some{Spec.Reply.Names{ns}},
          Some{Spec.Reply.Names{gs}},
          h2
        ),
        When.some(
          Shared.Bool.when(
            Bool,
            Bool.not(List.is_empty(&2, String, ns)),
            un => RRounds.Slot.backed(
              Rounds.Slot.ballots(s, c, k),
              ns,
              k,
              Lists.List.lead(String, ns),
              pk
            ),
            un => False{}
          ),
          Spec.Reply.Names{Lists.List.lead(String, ns)},
          Spec.Reply.Names{os}
        )(h1)
      )

# A version is decided by a majority of the nodes of its owner group, each by
# a ballot that the node holds.
def Core.majority_decides(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +os: List<&2, String>,
  +gs: List<&2, String>
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Owners{c, k}
  )
    == Some{Spec.Reply.Names{os}}: Maybe<&2, Spec.Reply>
} -> {
  Answers.Answer.of(
    s,
    Spec.Question.Group{c, k}
  )
    == Some{Spec.Reply.Names{gs}}: Maybe<&2, Spec.Reply>
} -> {
  Shared.List.within(~String, ~String.eq, os, gs) == True{}: Bool
}
  & (
    {
      Nat.is_lt(
        List.length(&2, String, gs),
        Nat.add(List.length(&2, String, os), List.length(&2, String, os))
      )
        == True{}: Bool
    }
      & (
        @v: String -> {
          List.contains(~String, ~String.eq, os, v) == True{}: Bool
        } -> Exists(
          Types.Change,
          ch => {
            Facts.Facts.holds(s, ch) == True{}: Bool
          }
            & Exists(
              List<&2, U32>,
              st => Exists(
                List<&2, U32>,
                x => {
                  RFacts.Change.ballot(ch) == Some{Spec.Ballot{v, st, x}}: Maybe<&2, Spec.Ballot>
                }
              )
            )
        )
      )
  ):
  h1 => h2 => Core.majority_decides.of(
    s,
    c,
    os,
    gs,
    Lines.Line.at(s, c, k),
    Answers.Rule.for(s, c, k)
  )(h1)(h2)

# A branch is decided by its store
# --------------------------------

# a request that makes a group the owner of the line c
def Request.Owns(c: Ledgers.Line, r: Spec.Request) -> Type:
  Exists(String, g => {r == Spec.Request.Own{c, g}: Spec.Request})

# a request that makes a group the owner of the line c is an Own of c
def Request.owns_is(
  +c: Ledgers.Line,
  r: Spec.Request
) -> {RLines.Request.owns(c, r) == True{}: Bool} -> Request.Owns(c, r):
  match r:
    case Spec.Request.Start{os}:
      h => Empty.absurd(Request.Owns(c, Spec.Request.Start{os}), Shared.Bool.false_ne_true(h))
    case Spec.Request.Write{b, q, ws}:
      h => Empty.absurd(Request.Owns(c, Spec.Request.Write{b, q, ws}), Shared.Bool.false_ne_true(h))
    case Spec.Request.Merge{f, x}:
      h => Empty.absurd(Request.Owns(c, Spec.Request.Merge{f, x}), Shared.Bool.false_ne_true(h))
    case Spec.Request.Resolve{m, q, w}:
      h => Empty.absurd(
        Request.Owns(c, Spec.Request.Resolve{m, q, w}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Mark{b, name, v}:
      h => Empty.absurd(
        Request.Owns(c, Spec.Request.Mark{b, name, v}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Move{b, t, v}:
      h => Empty.absurd(Request.Owns(c, Spec.Request.Move{b, t, v}), Shared.Bool.false_ne_true(h))
    case Spec.Request.Group{st, name, ms}:
      h => Empty.absurd(
        Request.Owns(c, Spec.Request.Group{st, name, ms}),
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Request.Own{+l, +g}:
      h => (g, (
          %Ledgers.Line.is_eq_sound(l, c)(h): {Spec.Request.Own{l, g} == Spec.Request.Own{_, g}: Spec.Request}
          {==}))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- a proposition does not run: its second use of the binder is not consumed, and the checker accepts it
# a version of the store of the root r is a decided Own of its branch b
def Core.Owned(s: Facts.Facts(), r: Hashes.Hash, b: String) -> Type:
  Exists(
    Nat,
    k => Exists(
      Ledgers.Id,
      i => Exists(
        String,
        g => Mirror.Made(
          s,
          Ledgers.Line{r, None{}},
          k,
          i,
          Spec.Request.Own{Ledgers.Line{r, Some{b}}, g}
        )
      )
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Core.branches_decided.at, with the version k (the entry e) that owns
def Core.branches_decided.by(
  +s: Facts.Facts(),
  +r: Hashes.Hash,
  +b: String,
  +k: Nat,
  +e: Types.Entry,
  ha: {Lines.Line.at(s, Ledgers.Line{r, None{}}, k) == Some{e}: Maybe<&2, Types.Entry>},
  w: Request.Owns(Ledgers.Line{r, Some{b}}, RAnswers.Entry.request(e))
) -> Core.Owned(s, r, b):
  (+g, he) = w
  (
    k,
    (
      RLines.Entry.id(e),
      (
        g,
        Core.cast(
          Spec.Request,
          rq => Mirror.Made(s, Ledgers.Line{r, None{}}, k, RLines.Entry.id(e), rq),
          RAnswers.Entry.request(e),
          Spec.Request.Own{Ledgers.Line{r, Some{b}}, g},
          he,
          Core.at_made(s, Ledgers.Line{r, None{}}, k, e)(ha)
        )
      )
    )
  )

# a version of the store that owns the branch is a decided Own of it
def Core.branches_decided.at(
  +s: Facts.Facts(),
  +r: Hashes.Hash,
  +b: String,
  w: Exists(
    List<&2, Types.Entry>,
    R => {
      Lines.Line.versions(s, Ledgers.Line{r, None{}}) == Some{R}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Exists(
        Nat,
        k => Exists(
          Types.Entry,
          e => {
            List.get(&2, Types.Entry, R, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & {RLines.Entry.owns(Ledgers.Line{r, Some{b}}, e) == True{}: Bool}
        )
      )
  )
) -> Core.Owned(s, r, b):
  (+R, w1) = w
  (h_r, w2) = w1
  (+k, w3) = w2
  (+e, w4) = w3
  (hg, ho) = w4
  Core.branches_decided.by(
    s,
    r,
    b,
    k,
    e,
    Line.at_of(s, Ledgers.Line{r, None{}}, R, k, e)(h_r)(hg),
    Request.owns_is(Ledgers.Line{r, Some{b}}, RAnswers.Entry.request(e))(ho)
  )

# Core.branches_decided, once the versions of the branch (v) are known
def Core.branches_decided.of(
  +s: Facts.Facts(),
  +r: Hashes.Hash,
  +b: String,
  -x: Spec.Reply,
  v: Maybe<&2, List<&2, Types.Entry>>
) -> {
  Lines.Line.versions(s, Ledgers.Line{r, Some{b}}) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {RAnswers.Reply.count(v) == Some{x}: Maybe<&2, Spec.Reply>} -> Core.Owned(s, r, b):
  match v:
    case None{}:
      ev => h => Empty.absurd(Core.Owned(s, r, b), Shared.Maybe.none_ne_some(Spec.Reply, x, h))
    case Some{+vs}:
      ev => h => Core.branches_decided.at(s, r, b, Versions.Line.branch_owned(s, r, b, vs)(ev))

# A branch exists only when the owner group of its store decided it.
def Core.branches_decided(
  +s: Facts.Facts(),
  +r: Hashes.Hash,
  +b: String,
  +x: Spec.Reply
) -> {
  Answers.Answer.of(
    s,
    Spec.Question.Count{Ledgers.Line{r, Some{b}}}
  )
    == Some{x}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  k => Exists(
    Ledgers.Id,
    i => Exists(
      String,
      g => Mirror.Made(
        s,
        Ledgers.Line{r, None{}},
        k,
        i,
        Spec.Request.Own{Ledgers.Line{r, Some{b}}, g}
      )
    )
  )
):
  h => Core.branches_decided.of(
    s,
    r,
    b,
    x,
    Lines.Line.versions(s, Ledgers.Line{r, Some{b}})
  )({==})(h)

# The parents of a version
# ------------------------

# version 0 comes from no version
def Core.parents_zero(
  c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>,
  -ps: List<&2, Spec.Point>
) -> {
  RAnswers.Reply.parents(c, 0n, m) == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
} -> {ps == []: List<&2, Spec.Point>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {ps == []: List<&2, Spec.Point>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Points{ps}, h)
      )
    case Some{e}:
      h => Equal.sym(
        List<&2, Spec.Point>,
        [],
        ps,
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          List<&2, Spec.Point>,
          x => Reply.to_points(x, ps),
          Some{Spec.Reply.Points{[]}},
          Some{Spec.Reply.Points{ps}},
          h
        )
      )

# the version before and what the request r takes are the parents of a
# version made by r
def Request.takes_parents(
  r: Spec.Request,
  +from: Nat,
  +c: Ledgers.Line,
  +k: Nat,
  -ps: List<&2, Spec.Point>
) -> {
  Spec.Point{
    c,
    k
  }
    <> Shared.Maybe.cons(Spec.Point, RContents.Request.takes(r, from), [])
    == ps: List<&2, Spec.Point>
} -> Mirror.Request.Parents(r, c, k, ps):
  match r:
    case Spec.Request.Start{os}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)
    case Spec.Request.Write{b, q, ws}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)
    case Spec.Request.Merge{f, x}:
      h => (from, Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}, Spec.Point{f, from}], ps, h))
    case Spec.Request.Resolve{m, q, w}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)
    case Spec.Request.Mark{b, name, v}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)
    case Spec.Request.Move{b, t, v}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}, Spec.Point{t, v}], ps, h)
    case Spec.Request.Group{st, name, ms}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)
    case Spec.Request.Own{l, g}:
      h => Equal.sym(List<&2, Spec.Point>, [Spec.Point{c, k}], ps, h)

# the version before and what the entry e takes are the parents of a version
# made by the request of e
def Entry.parents_of(
  e: Types.Entry,
  +c: Ledgers.Line,
  +k: Nat,
  -ps: List<&2, Spec.Point>
) -> {
  Spec.Point{
    c,
    k
  }
    <> Shared.Maybe.cons(Spec.Point, RContents.Entry.takes(e), [])
    == ps: List<&2, Spec.Point>
} -> Mirror.Request.Parents(RAnswers.Entry.request(e), c, k, ps):
  match e:
    case Types.Entry{
      Types.Pick{Types.Ask{i, n, r}, Types.Pins{era, from, base, ours, theirs}},
      slot
    }:
      Request.takes_parents(r, from, c, k, ps)

# Core.parents_are, with the entry of the version
def Core.parents_are.by(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  -i: Ledgers.Id,
  -r: Spec.Request,
  -ps: List<&2, Spec.Point>,
  w: Exists(
    Types.Entry,
    e => {
      Lines.Line.at(s, c, 1n+k) == Some{e}: Maybe<&2, Types.Entry>
    }
      & ({RLines.Entry.id(e) == i: Ledgers.Id} & {RAnswers.Entry.request(e) == r: Spec.Request})
  ),
  h: {
    RAnswers.Reply.parents(
      c,
      1n+k,
      Lines.Line.at(s, c, 1n+k)
    )
      == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
  }
) -> Mirror.Request.Parents(r, c, k, ps):
  (+e, w1) = w
  (ha, w2) = w1
  (hi, hr) = w2
  Core.cast(
    Spec.Request,
    x => Mirror.Request.Parents(x, c, k, ps),
    RAnswers.Entry.request(e),
    r,
    hr,
    Entry.parents_of(
      e,
      c,
      k,
      ps
    )(
      Equal.cong(
        Maybe<&2, Spec.Reply>,
        List<&2, Spec.Point>,
        x => Reply.to_points(x, ps),
        Some{Spec.Reply.Points{RContents.Entry.parents(c, 1n+k, e)}},
        Some{Spec.Reply.Points{ps}},
        Core.cast(
          Maybe<&2, Types.Entry>,
          m => {
            RAnswers.Reply.parents(c, 1n+k, m) == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
          },
          Lines.Line.at(s, c, 1n+k),
          Some{e},
          ha,
          h
        )
      )
    )
  )

# A version comes from the version before it, and also from the version that
# a merge or a move takes; the first version comes from none.
def Core.parents_are(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +ps: List<&2, Spec.Point>
) -> (
  {
    Answers.Answer.of(
      s,
      Spec.Question.Parents{c, 0n}
    )
      == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
  } -> {ps == []: List<&2, Spec.Point>}
)
  & (
    Mirror.Made(
      s,
      c,
      1n+k,
      i,
      r
    ) -> {
      Answers.Answer.of(
        s,
        Spec.Question.Parents{c, 1n+k}
      )
        == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
    } -> Mirror.Request.Parents(r, c, k, ps)
  ):
  (
    h => Core.parents_zero(c, Lines.Line.at(s, c, 0n), ps)(h),
    md => h => Core.parents_are.by(s, c, k, i, r, ps, Core.made_at(s, c, 1n+k, i, r)(md), h)
  )
