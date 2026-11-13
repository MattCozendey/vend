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
  m => (
    (hv, hr) = m
    Core.made_at.of(s, c, k, i, r, Lines.Line.at(s, c, k), Lines.Line.versions(s, c))({==})({==})(hv)(hr)
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
