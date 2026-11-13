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
import ./shared/files.bend as Files
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
  hv => hg =>
    %Equal.sym(Maybe<&2, List<&2, Types.Entry>>, Lines.Line.versions(s, c), Some{vs}, hv): {Lines.Line.at.of(_, k) == Some{e}: Maybe<&2, Types.Entry>}
    hg

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
) -> {Lines.Line.at.of(v, k) == m: Maybe<&2, Types.Entry>} -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {Answers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>} -> {
  Answers.Reply.ask(Answers.Line.find(s, c, i)) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Types.Entry,
  e => {
    Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
  }
    & ({Lines.Entry.id(e) == i: Ledgers.Id} & {Answers.Entry.request(e) == r: Spec.Request})
):
  match m v:
    case None{} v2:
      em => ev => hv => hr => Empty.absurd(
        Exists(
          Types.Entry,
          e => {
            Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
          }
            & ({Lines.Entry.id(e) == i: Ledgers.Id} & {Answers.Entry.request(e) == r: Spec.Request})
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
            & ({Lines.Entry.id(e2) == i: Ledgers.Id} & {Answers.Entry.request(e2) == r: Spec.Request})
        ),
        Shared.Maybe.none_ne_some(Types.Entry, e, em)
      )
    case Some{+e} Some{+vs}:
      +em => +ev => hv => hr => (
        +hi = Equal.cong(
          Maybe<&2, Spec.Reply>,
          Ledgers.Id,
          x => Reply.to_id(x, i),
          Some{Spec.Reply.Id{Lines.Entry.id(e)}},
          Some{Spec.Reply.Id{i}},
          hv
        )
        (
          e,
          (
            Line.at_of(s, c, vs, k, e)(ev)(em),
            (
              hi,
              Equal.cong(
                Maybe<&2, Spec.Reply>,
                Spec.Request,
                x => Reply.to_ask(x, r),
                Some{Spec.Reply.Ask{Answers.Entry.request(e)}},
                Some{Spec.Reply.Ask{r}},
                Core.cast(
                  Maybe<&2, Answers.Found>,
                  f => {Answers.Reply.ask(f) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>},
                  Answers.Line.find(s, c, i),
                  Some{Answers.Found{k, e}},
                  Core.cast(
                    Ledgers.Id,
                    x => {Answers.Line.find(s, c, x) == Some{Answers.Found{k, e}}: Maybe<&2, Answers.Found>},
                    Lines.Entry.id(e),
                    i,
                    hi,
                    Line.find_at(s, c, vs, k, e)(ev)(em)
                  ),
                  hr
                )
              )
            )
          )
        )
      )

# a version made by a request is an entry of the line, of its id and request
def Core.made_at(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +i: Ledgers.Id, +r: Spec.Request) -> Mirror.Made(s, c, k, i, r) -> Exists(
  Types.Entry,
  e => {
    Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
  }
    & ({Lines.Entry.id(e) == i: Ledgers.Id} & {Answers.Entry.request(e) == r: Spec.Request})
):
  m => Pair.use(
    {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>},
    {Answers.Answer.of(s, Spec.Question.Request{c, i}) == Some{Spec.Reply.Ask{r}}: Maybe<&2, Spec.Reply>},
    Exists(
      Types.Entry,
      e => {
        Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
      }
        & ({Lines.Entry.id(e) == i: Ledgers.Id} & {Answers.Entry.request(e) == r: Spec.Request})
    ),
    m,
    hv => hr => Core.made_at.of(s, c, k, i, r, Lines.Line.at(s, c, k), Lines.Line.versions(s, c))({==})({==})(hv)(hr)
  )

# Core.at_made, once the versions of the line (v) are known
def Core.at_made.of(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry, v: Maybe<&2, List<&2, Types.Entry>>) -> {
  Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>
} -> {Lines.Line.at.of(v, k) == Some{e}: Maybe<&2, Types.Entry>} -> Mirror.Made(s, c, k, Lines.Entry.id(e), Answers.Entry.request(e)):
  match v:
    case None{}:
      ev => ha => Empty.absurd(
        Mirror.Made(s, c, k, Lines.Entry.id(e), Answers.Entry.request(e)),
        Shared.Maybe.none_ne_some(Types.Entry, e, ha)
      )
    case Some{+vs}:
      +ev => +ha => (
        Core.cast(
          Maybe<&2, Types.Entry>,
          m => {Answers.Reply.id(m) == Some{Spec.Reply.Id{Lines.Entry.id(e)}}: Maybe<&2, Spec.Reply>},
          Some{e},
          Lines.Line.at(s, c, k),
          Equal.sym(Maybe<&2, Types.Entry>, Lines.Line.at(s, c, k), Some{e}, Line.at_of(s, c, vs, k, e)(ev)(ha)),
          {==}
        ),
        Core.cast(
          Maybe<&2, Answers.Found>,
          f => {Answers.Reply.ask(f) == Some{Spec.Reply.Ask{Answers.Entry.request(e)}}: Maybe<&2, Spec.Reply>},
          Some{Answers.Found{k, e}},
          Answers.Line.find(s, c, Lines.Entry.id(e)),
          Equal.sym(Maybe<&2, Answers.Found>, Answers.Line.find(s, c, Lines.Entry.id(e)), Some{Answers.Found{k, e}}, Line.find_at(s, c, vs, k, e)(ev)(ha)),
          {==}
        )
      )

# the entry at version k of a line is made by its id, which asked for its
# request
def Core.at_made(+s: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry) -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> Mirror.Made(s, c, k, Lines.Entry.id(e), Answers.Entry.request(e)):
  ha => Core.at_made.of(s, c, k, e, Lines.Line.versions(s, c))({==})(ha)

# A reply fits its question
# -------------------------

# no reply fits nothing
def Fit.none(q: Spec.Question, -r: Spec.Reply) -> {None{} == Some{r}: Maybe<&2, Spec.Reply>} -> {
  Spec.Reply.fits(q, r) == True{}: Bool
}:
  h => Empty.absurd({Spec.Reply.fits(q, r) == True{}: Bool}, Shared.Maybe.none_ne_some(Spec.Reply, r, h))

# a reply that is x fits when x fits
def Fit.some(q: Spec.Question, -x: Spec.Reply, -r: Spec.Reply) -> {Spec.Reply.fits(q, x) == True{}: Bool} -> {
  Some{x} == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  hf => h =>
    %Shared.Maybe.some_inj(Spec.Reply, x, r, h): {Spec.Reply.fits(q, _) == True{}: Bool}
    hf

# a reply of an id fits a question that ids fit
def Fit.id(q: Spec.Question, m: Maybe<&2, Types.Entry>, -r: Spec.Reply) -> (
  @x: Ledgers.Id -> {Spec.Reply.fits(q, Spec.Reply.Id{x}) == True{}: Bool}
) -> {Answers.Reply.id(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{e}:
      f => Fit.some(q, Spec.Reply.Id{Lines.Entry.id(e)}, r)(f(Lines.Entry.id(e)))

# a reply of a request fits a question that requests fit
def Fit.ask(q: Spec.Question, m: Maybe<&2, Answers.Found>, -r: Spec.Reply) -> (
  @x: Spec.Request -> {Spec.Reply.fits(q, Spec.Reply.Ask{x}) == True{}: Bool}
) -> {Answers.Reply.ask(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{Answers.Found{k, e}}:
      f => Fit.some(q, Spec.Reply.Ask{Answers.Entry.request(e)}, r)(f(Answers.Entry.request(e)))

# a reply of a count fits a question that numbers fit
def Fit.count(q: Spec.Question, m: Maybe<&2, List<&2, Types.Entry>>, -r: Spec.Reply) -> (
  @x: Nat -> {Spec.Reply.fits(q, Spec.Reply.Number{x}) == True{}: Bool}
) -> {Answers.Reply.count(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{vs}:
      f => Fit.some(q, Spec.Reply.Number{List.length(&2, Types.Entry, vs)}, r)(f(List.length(&2, Types.Entry, vs)))

# a reply of names fits a question that names fit
def Fit.names(q: Spec.Question, m: Maybe<&2, List<&2, String>>, -r: Spec.Reply) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {Answers.Reply.names(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{ns}:
      f => Fit.some(q, Spec.Reply.Names{ns}, r)(f(ns))

# a reply of a number fits a question that numbers fit
def Fit.number(q: Spec.Question, m: Maybe<&2, Nat>, -r: Spec.Reply) -> (
  @x: Nat -> {Spec.Reply.fits(q, Spec.Reply.Number{x}) == True{}: Bool}
) -> {Answers.Reply.number(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{k}:
      f => Fit.some(q, Spec.Reply.Number{k}, r)(f(k))

# a reply of a point fits a question that points fit
def Fit.point(q: Spec.Question, m: Maybe<&2, Spec.Point>, -r: Spec.Reply) -> (
  @x: Spec.Point -> {Spec.Reply.fits(q, Spec.Reply.Point{x}) == True{}: Bool}
) -> {Answers.Reply.point(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{x}:
      f => Fit.some(q, Spec.Reply.Point{x}, r)(f(x))

# a reply of a hash fits a question that hashes fit
def Fit.hash(q: Spec.Question, m: Maybe<&2, Files.Files()>, -r: Spec.Reply) -> (
  @x: Hashes.Hash -> {Spec.Reply.fits(q, Spec.Reply.Hash{x}) == True{}: Bool}
) -> {Answers.Reply.hash(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{t}:
      f => Fit.some(q, Spec.Reply.Hash{Files.Files.hash(t)}, r)(f(Files.Files.hash(t)))

# a reply of a yes fits a question that a yes fits
def Fit.yes(q: Spec.Question, m: Maybe<&2, Bool>, -r: Spec.Reply) -> (
  @x: Bool -> {Spec.Reply.fits(q, Spec.Reply.Yes{x}) == True{}: Bool}
) -> {Answers.Reply.yes(m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{y}:
      f => Fit.some(q, Spec.Reply.Yes{y}, r)(f(y))

# a reply of parents fits a question that points fit
def Fit.parents(q: Spec.Question, c: Ledgers.Line, k: Nat, m: Maybe<&2, Types.Entry>, -r: Spec.Reply) -> (
  @x: List<&2, Spec.Point> -> {Spec.Reply.fits(q, Spec.Reply.Points{x}) == True{}: Bool}
) -> {Answers.Reply.parents(c, k, m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{e}:
      f => Fit.some(q, Spec.Reply.Points{Contents.Entry.parents(c, k, e)}, r)(f(Contents.Entry.parents(c, k, e)))

# a reply of a status fits a question that a status fits
def Fit.status(
  q: Spec.Question,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, Answers.Found>,
  -r: Spec.Reply
) -> (
  @x: Spec.Status -> {Spec.Reply.fits(q, Spec.Reply.Status{x}) == True{}: Bool}
) -> {Answers.Reply.status(s, c, v, m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match v m:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{vs} None{}:
      f => Fit.none(q, r)
    case Some{+vs} Some{Answers.Found{+k, +e}}:
      f => Fit.some(q, Spec.Reply.Status{Answers.Status.of(s, c, vs, k, e)}, r)(f(Answers.Status.of(s, c, vs, k, e)))

# the reply of the nodes of a rule fits a question that names fit
def Fit.group(q: Spec.Question, u: Maybe<&2, Lines.Rule>, -r: Spec.Reply) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {Maybe.bind(&2, Lines.Rule, Spec.Reply, u, Answers.Rule.group) == Some{r}: Maybe<&2, Spec.Reply>} -> {
  Spec.Reply.fits(q, r) == True{}: Bool
}:
  match u:
    case None{}:
      f => Fit.none(q, r)
    case Some{Lines.Rule{None{}, ns}}:
      f => Fit.none(q, r)
    case Some{Lines.Rule{Some{g}, ns}}:
      f => Fit.some(q, Spec.Reply.Names{ns}, r)(f(ns))

# the reply of the owner of a rule fits a question that a name fits
def Fit.owner(q: Spec.Question, u: Maybe<&2, Lines.Rule>, -r: Spec.Reply) -> (
  @x: String -> {Spec.Reply.fits(q, Spec.Reply.Name{x}) == True{}: Bool}
) -> {Maybe.bind(&2, Lines.Rule, Spec.Reply, u, Answers.Rule.owner) == Some{r}: Maybe<&2, Spec.Reply>} -> {
  Spec.Reply.fits(q, r) == True{}: Bool
}:
  match u:
    case None{}:
      f => Fit.none(q, r)
    case Some{Lines.Rule{None{}, ns}}:
      f => Fit.none(q, r)
    case Some{Lines.Rule{Some{g}, ns}}:
      f => Fit.some(q, Spec.Reply.Name{g}, r)(f(g))

# a reply given when b holds fits when it fits
def Fit.when(q: Spec.Question, b: Bool, -x: Spec.Reply, -r: Spec.Reply) -> {Spec.Reply.fits(q, x) == True{}: Bool} -> {
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
  u: Maybe<&2, Lines.Rule>,
  -r: Spec.Reply
) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {Answers.Owners.of(s, c, m, u) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m u:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{e} None{}:
      f => Fit.none(q, r)
    case Some{Types.Entry{+pk, +k}} Some{Lines.Rule{g, +ns}}:
      f => Fit.when(
        q,
        Bool.and(
          Bool.not(List.is_empty(&2, String, ns)),
          Shared.List.holds(~String, ~Lines.Voting, ~Lines.Voting.voted, Lists.List.lead(String, ns), Lines.Voting{s, Types.Step.At{c, k}, pk})
        ),
        Spec.Reply.Names{Lists.List.lead(String, ns)},
        r
      )(f(Lists.List.lead(String, ns)))

# Fit.affects, once the reached paths m are known
def Fit.affects.at(q: Spec.Question, a: Files.Files(), b: Files.Files(), m: Maybe<&2, List<&2, String>>, -r: Spec.Reply) -> (
  @x: List<&2, String> -> {Spec.Reply.fits(q, Spec.Reply.Names{x}) == True{}: Bool}
) -> {Answers.Affects.at(a, b, m) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match m:
    case None{}:
      f => Fit.none(q, r)
    case Some{seen}:
      f => Fit.some(q, Spec.Reply.Names{Answers.Delta.changed(Answers.Delta{a, b}, seen)}, r)(f(Answers.Delta.changed(Answers.Delta{a, b}, seen)))

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
) -> {Answers.Affects.of(old, new, us, bs) == Some{r}: Maybe<&2, Spec.Reply>} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match old new:
    case None{} None{}:
      f => Fit.none(q, r)
    case None{} Some{x}:
      f => Fit.none(q, r)
    case Some{a} None{}:
      f => Fit.none(q, r)
    case Some{a} Some{+b}:
      Fit.affects.at(q, a, b, Answers.Reach.of(b, bs, us), r)

# A reply fits its question.
def Core.answer_fits(+s: Facts.Facts(), +q: Spec.Question, +r: Spec.Reply) -> {
  Answers.Answer.of(s, q) == Some{r}: Maybe<&2, Spec.Reply>
} -> {Spec.Reply.fits(q, r) == True{}: Bool}:
  match q:
    case Spec.Question.Status{c, i}:
      Fit.status(Spec.Question.Status{c, i}, s, c, Lines.Line.versions(s, c), Answers.Line.find(s, c, i), r)(x => {==})
    case Spec.Question.Request{c, i}:
      Fit.ask(Spec.Question.Request{c, i}, Answers.Line.find(s, c, i), r)(x => {==})
    case Spec.Question.Version{c, k}:
      Fit.id(Spec.Question.Version{c, k}, Lines.Line.at(s, c, k), r)(x => {==})
    case Spec.Question.Content{c, k}:
      Fit.hash(Spec.Question.Content{c, k}, Contents.Content.of(s, c, k), r)(x => {==})
    case Spec.Question.Group{c, k}:
      Fit.group(Spec.Question.Group{c, k}, Answers.Rule.for(s, c, k), r)(x => {==})
    case Spec.Question.Owners{c, k}:
      Fit.owners(Spec.Question.Owners{c, k}, s, c, Lines.Line.at(s, c, k), Answers.Rule.for(s, c, k), r)(x => {==})
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
      Fit.number(Spec.Question.Mark{c, m}, Answers.Mark.of(m, Lines.Line.versions(s, c)), r)(x => {==})
    case Spec.Question.Count{c}:
      Fit.count(Spec.Question.Count{c}, Lines.Line.versions(s, c), r)(x => {==})
    case Spec.Question.Clashes{c, i}:
      Fit.names(
        Spec.Question.Clashes{c, i},
        Answers.Found.then(List<&2, String>, Answers.Line.find(s, c, i), k => e => Answers.Clashes.of(s, c, k, e)),
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
        Answers.Found.then(Spec.Point, Answers.Line.find(s, c, i), k => e => Answers.Base.of(s, c, k, e)),
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
) -> {Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>} -> {
  List.get(&2, Types.Entry, vs, k) == m: Maybe<&2, Types.Entry>
} -> {Answers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>} -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == Some{k}: Maybe<&2, Nat>
}:
  match m:
    case None{}:
      hv => hg => h => Empty.absurd(
        {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == Some{k}: Maybe<&2, Nat>},
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h)
      )
    case Some{+e}:
      hv => hg => h => Core.cast(
        Ledgers.Id,
        x => {Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, x) == Some{k}: Maybe<&2, Nat>},
        Lines.Entry.id(e),
        i,
        Equal.cong(
          Maybe<&2, Spec.Reply>,
          Ledgers.Id,
          x => Reply.to_id(x, i),
          Some{Spec.Reply.Id{Lines.Entry.id(e)}},
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
) -> {Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>} -> {
  Answers.Reply.id(Lines.Line.at.of(v, a)) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {Answers.Reply.id(Lines.Line.at.of(v, b)) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>} -> {a == b: Nat}:
  match v:
    case None{}:
      ev => h1 => h2 => Empty.absurd({a == b: Nat}, Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Id{i}, h1))
    case Some{+vs}:
      +ev => h1 => h2 => Shared.Maybe.some_inj(
        Nat,
        a,
        b,
        Equal.trans(
          Maybe<&2, Nat>,
          Some{a},
          Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i),
          Some{b},
          Equal.sym(
            Maybe<&2, Nat>,
            Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i),
            Some{a},
            Entries.id_index(s, c, vs, a, i, List.get(&2, Types.Entry, vs, a))(ev)({==})(h1)
          ),
          Entries.id_index(s, c, vs, b, i, List.get(&2, Types.Entry, vs, b))(ev)({==})(h2)
        )
      )

# A request counts once: it makes at most one version of a line.
def Core.counts_once(+s: Facts.Facts(), +c: Ledgers.Line, +i: Ledgers.Id, +a: Nat, +b: Nat) -> {
  Answers.Answer.of(s, Spec.Question.Version{c, a}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
} -> {Answers.Answer.of(s, Spec.Question.Version{c, b}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>} -> {
  a == b: Nat
}:
  h1 => h2 => Core.counts_once.of(s, c, i, a, b, Lines.Line.versions(s, c))({==})(h1)(h2)

# Found entries
# -------------

# the version of the found entry m, or d
def Found.to_n(m: Maybe<&2, Answers.Found>, d: Nat) -> Nat:
  match m:
    case None{}:
      d
    case Some{Answers.Found{k, e}}:
      k

# the entry of the found entry m
def Found.to_entry(m: Maybe<&2, Answers.Found>) -> Maybe<&2, Types.Entry>:
  match m:
    case None{}:
      None{}
    case Some{Answers.Found{k, e}}:
      Some{e}

# an entry found as version k is version k, the entry g
def Found.map_some(+k: Nat, -n: Nat, -e: Types.Entry, g: Maybe<&2, Types.Entry>) -> {
  Maybe.map(&2, Types.Entry, Answers.Found, e2 => Answers.Found{k, e2}, g) == Some{Answers.Found{n, e}}: Maybe<&2, Answers.Found>
} -> {k == n: Nat} & {g == Some{e}: Maybe<&2, Types.Entry>}:
  match g:
    case None{}:
      h => Empty.absurd(
        {k == n: Nat} & {None{} == Some{e}: Maybe<&2, Types.Entry>},
        Shared.Maybe.none_ne_some(Answers.Found, Answers.Found{n, e}, h)
      )
    case Some{e2}:
      +h => (
        Equal.cong(Maybe<&2, Answers.Found>, Nat, x => Found.to_n(x, k), Some{Answers.Found{k, e2}}, Some{Answers.Found{n, e}}, h),
        Equal.cong(
          Maybe<&2, Answers.Found>,
          Maybe<&2, Types.Entry>,
          Found.to_entry,
          Some{Answers.Found{k, e2}},
          Some{Answers.Found{n, e}},
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
) -> {Some{k} == Some{n}: Maybe<&2, Nat>} & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  (+ek, hg) = w
  (
    Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, k, n, ek),
    Core.cast(Nat, x => {List.get(&2, Types.Entry, vs, x) == Some{e}: Maybe<&2, Types.Entry>}, k, n, ek, hg)
  )

# Entries.find_some, once the index m of the id is known
def Entries.find_some.at(+vs: List<&2, Types.Entry>, m: Maybe<&2, Nat>, -n: Nat, -e: Types.Entry) -> {
  Answers.Versions.find.at(vs, m) == Some{Answers.Found{n, e}}: Maybe<&2, Answers.Found>
} -> {m == Some{n}: Maybe<&2, Nat>} & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{n}: Maybe<&2, Nat>} & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>},
        Shared.Maybe.none_ne_some(Answers.Found, Answers.Found{n, e}, h)
      )
    case Some{+k}:
      h => Entries.find_some.by(vs, k, n, e, Found.map_some(k, n, e, List.get(&2, Types.Entry, vs, k))(h))

# the entry found for an id among versions is at the first index of the id
def Entries.find_some(+vs: List<&2, Types.Entry>, +i: Ledgers.Id, -n: Nat, -e: Types.Entry) -> {
  Answers.Versions.find(vs, i) == Some{Answers.Found{n, e}}: Maybe<&2, Answers.Found>
} -> {
  Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == Some{n}: Maybe<&2, Nat>
}
  & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}:
  h => Entries.find_some.at(vs, Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i), n, e)(h)

# Entries.find_id.by, with the element at the index of the id
def Entries.find_id.at(
  -vs: List<&2, Types.Entry>,
  +i: Ledgers.Id,
  -n: Nat,
  +e: Types.Entry,
  hg: {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>},
  w: Exists(
    Types.Entry,
    x => {List.get(&2, Types.Entry, vs, n) == Some{x}: Maybe<&2, Types.Entry>} & {Lines.Entry.is_of(i, x) == True{}: Bool}
  )
) -> {Lines.Entry.id(e) == i: Ledgers.Id}:
  (x, w1) = w
  (hx, ho) = w1
  Ledgers.Id.is_eq_sound(Lines.Entry.id(e), i)(
    Core.cast(
      Types.Entry,
      y => {Lines.Entry.is_of(i, y) == True{}: Bool},
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
    Lists.List.index(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i) == Some{n}: Maybe<&2, Nat>
  }
    & {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>}
) -> {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}:
  (hi, +hg) = w
  (
    hg,
    Entries.find_id.at(vs, i, n, e, hg, Lists.List.index_get(~Types.Entry, ~Ledgers.Id, ~Lines.Entry.is_of, vs, i, n)(hi))
  )

# the entry found for the id i among versions is version n of them, of the id i
def Entries.find_id(+vs: List<&2, Types.Entry>, +i: Ledgers.Id, -n: Nat, +e: Types.Entry) -> {
  Answers.Versions.find(vs, i) == Some{Answers.Found{n, e}}: Maybe<&2, Answers.Found>
} -> {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}:
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
  w: {List.get(&2, Types.Entry, vs, n) == Some{e}: Maybe<&2, Types.Entry>} & {Lines.Entry.id(e) == i: Ledgers.Id}
) -> Exists(
  Nat,
  k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
):
  (hg, hi) = w
  (
    n,
    Core.cast(
      Maybe<&2, Types.Entry>,
      m => {Answers.Reply.id(m) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>},
      Some{e},
      Lines.Line.at(s, c, n),
      Equal.sym(Maybe<&2, Types.Entry>, Lines.Line.at(s, c, n), Some{e}, Line.at_of(s, c, vs, n, e)(ev)(hg)),
      Equal.cong(Ledgers.Id, Maybe<&2, Spec.Reply>, x => Some{Spec.Reply.Id{x}}, Lines.Entry.id(e), i, hi)
    )
  )

# Core.written_made, once the versions of the line (v) and the found entry
# (f) are known
def Core.written_made.of(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  v: Maybe<&2, List<&2, Types.Entry>>,
  f: Maybe<&2, Answers.Found>
) -> {Lines.Line.versions(s, c) == v: Maybe<&2, List<&2, Types.Entry>>} -> {
  Answers.Line.find.of(i, v) == f: Maybe<&2, Answers.Found>
} -> {
  Answers.Reply.status(s, c, v, f) == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
):
  match v f:
    case None{} None{}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case None{} Some{x}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case Some{vs} None{}:
      ev => ef => h => Empty.absurd(
        Exists(
          Nat,
          k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
        ),
        Shared.Maybe.none_ne_some(Spec.Reply, Spec.Reply.Status{Spec.Status.Written{}}, h)
      )
    case Some{+vs} Some{Answers.Found{+n, +e}}:
      ev => ef => h => Core.written_made.by(s, c, i, vs, n, e, ev, Entries.find_id(vs, i, n, e)(ef))

# A request that is Written made a version.
def Core.written_made(+s: Facts.Facts(), +c: Ledgers.Line, +i: Ledgers.Id) -> {
  Answers.Answer.of(s, Spec.Question.Status{c, i}) == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
} -> Exists(
  Nat,
  k => {Answers.Answer.of(s, Spec.Question.Version{c, k}) == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>}
):
  h => Core.written_made.of(s, c, i, Lines.Line.versions(s, c), Answers.Line.find(s, c, i))({==})({==})(h)
