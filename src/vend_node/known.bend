import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./moves.bend as Moves
import ./groups.bend as Groups
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/files.bend as RFiles
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/rounds.bend as RRounds
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions

# Known states: laws
# ------------------
# A node keeps the states of the lines that it has read in a table
# (run/known.bend). Here: a table that is right for the facts
# (RKnown.Known.ok) changes no read of a line, and it stays right when the
# node learns a state, takes in an ask that starts no store, or casts a vote.

# Same states
# -----------

# Entry.same is True for an entry and itself
def Entry.same_refl(a: Types.Entry) -> {RKnown.Entry.same(a, a) == True{}: Bool}:
  match a:
    case Types.Entry{+p, +k}:
      Shared.Bool.and_both(Coded.Pick.is_eq(p, p), Nat.is_eq(k, k))(Coded.Pick.is_eq_refl(p))(Shared.Nat.is_eq_refl(k))

# Entry.same is True only for equal entries
def Entry.same_sound(
  a: Types.Entry,
  b: Types.Entry
) -> {RKnown.Entry.same(a, b) == True{}: Bool} -> {a == b: Types.Entry}:
  match a b:
    case Types.Entry{+p1, +k1} Types.Entry{+p2, +k2}:
      +h => (
        %Coded.Pick.is_eq_sound(p1, p2)(Shared.Bool.and_true_left(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))(h)): {Types.Entry{p1, k1} == Types.Entry{_, k2}: Types.Entry}
        %Shared.Nat.is_eq_sound(k1, k2)(Shared.Bool.and_true_right(Coded.Pick.is_eq(p1, p2), Nat.is_eq(k1, k2))(h)): {Types.Entry{p1, k1} == Types.Entry{p1, _}: Types.Entry}
        {==})

# Entries.same is True for versions and themselves
def Entries.same_refl(xs: List<&2, Types.Entry>) -> {RKnown.Entries.same(xs, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(RKnown.Entry.same(x, x), RKnown.Entries.same(r, r))(Entry.same_refl(x))(Entries.same_refl(r))

# Entries.same is True only for equal versions
def Entries.same_sound(
  xs: List<&2, Types.Entry>,
  ys: List<&2, Types.Entry>
) -> {RKnown.Entries.same(xs, ys) == True{}: Bool} -> {xs == ys: List<&2, Types.Entry>}:
  match xs ys:
    case Nil{} Nil{}:
      h => {==}
    case Nil{} Con{y, yr}:
      h => Empty.absurd({Nil{} == Con{y, yr}: List<&2, Types.Entry>}, Shared.Bool.false_ne_true(h))
    case Con{x, xr} Nil{}:
      h => Empty.absurd({Con{x, xr} == Nil{}: List<&2, Types.Entry>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +xr} Con{+y, +yr}:
      +h => (
        %Entry.same_sound(x, y)(Shared.Bool.and_true_left(RKnown.Entry.same(x, y), RKnown.Entries.same(xr, yr))(h)): {Con{x, xr} == Con{_, yr}: List<&2, Types.Entry>}
        %Entries.same_sound(xr, yr)(Shared.Bool.and_true_right(RKnown.Entry.same(x, y), RKnown.Entries.same(xr, yr))(h)): {Con{x, xr} == Con{x, _}: List<&2, Types.Entry>}
        {==})

# State.same is True for a state and itself
def State.same_refl(a: RLines.State) -> {RKnown.State.same(a, a) == True{}: Bool}:
  match a:
    case RLines.State{+vs, +k}:
      Shared.Bool.and_both(RKnown.Entries.same(vs, vs), Nat.is_eq(k, k))(Entries.same_refl(vs))(Shared.Nat.is_eq_refl(k))

# State.same is True only for equal states
def State.same_sound(
  a: RLines.State,
  b: RLines.State
) -> {RKnown.State.same(a, b) == True{}: Bool} -> {a == b: RLines.State}:
  match a b:
    case RLines.State{+v1, +k1} RLines.State{+v2, +k2}:
      +h => (
        %Entries.same_sound(v1, v2)(Shared.Bool.and_true_left(RKnown.Entries.same(v1, v2), Nat.is_eq(k1, k2))(h)): {RLines.State{v1, k1} == RLines.State{_, k2}: RLines.State}
        %Shared.Nat.is_eq_sound(k1, k2)(Shared.Bool.and_true_right(RKnown.Entries.same(v1, v2), Nat.is_eq(k1, k2))(h)): {RLines.State{v1, k1} == RLines.State{v1, _}: RLines.State}
        {==})

# a state that fits st is st
def State.fits_sound(
  m: Maybe<&2, RLines.State>,
  +st: RLines.State
) -> {RKnown.State.fits(m, st) == True{}: Bool} -> {m == Some{st}: Maybe<&2, RLines.State>}:
  match m:
    case None{}:
      h => Empty.absurd({None{} == Some{st}: Maybe<&2, RLines.State>}, Shared.Bool.false_ne_true(h))
    case Some{+x}:
      h => Equal.cong(RLines.State, Maybe<&2, RLines.State>, y => Some{y}, x, st, State.same_sound(x, st)(h))

# the state st fits what is st
def State.fits_of(
  m: Maybe<&2, RLines.State>,
  +st: RLines.State
) -> {m == Some{st}: Maybe<&2, RLines.State>} -> {RKnown.State.fits(m, st) == True{}: Bool}:
  e => (
    %Equal.sym(Maybe<&2, RLines.State>, m, Some{st}, e): {RKnown.State.fits(_, st) == True{}: Bool}
    State.same_refl(st))

# What a right table holds
# ------------------------

# no side of a false or is true
def Bool.or_false_left(a: Bool, b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {a == False{}: Bool}:
  match a:
    case True{}:
      h => h
    case False{}:
      h => {==}

# no side of a false or is true
def Bool.or_false_right(a: Bool, b: Bool) -> {Bool.or(a, b) == False{}: Bool} -> {b == False{}: Bool}:
  match a:
    case True{}:
      h => Empty.absurd({b == False{}: Bool}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => h

# the state that a right table holds for a line is the state that the facts
# give the line
def Known.find_ok(
  kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, c) == Some{st}: Maybe<&2, RLines.State>
} -> {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>}:
  match kn:
    case Nil{}:
      ok => e => Empty.absurd(
        {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>},
        Shared.Maybe.none_ne_some(RLines.State, st, e)
      )
    case Con{RKnown.Kept{+c2, +st2}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          Shared.Bool.when(
            Maybe<&2, RLines.State>,
            b,
            u => Some{st2},
            u => RKnown.Known.find(rest, c)
          )
            == Some{st}: Maybe<&2, RLines.State>
        } -> {RLines.Line.state(s, c) == Some{st}: Maybe<&2, RLines.State>},
        Ledgers.Line.is_eq(c2, c),
        +et => +e => (
          %Ledgers.Line.is_eq_sound(c2, c)(et): {RLines.Line.state(s, _) == Some{st}: Maybe<&2, RLines.State>}
          %e: {RLines.Line.state(s, c2) == _: Maybe<&2, RLines.State>}
          State.fits_sound(RLines.Line.state(s, c2), st2)(
            Shared.Bool.and_true_left(
              RKnown.State.fits(RLines.Line.state(s, c2), st2),
              RKnown.Known.ok(rest, s)
            )(ok)
          )),
        ef => e => Known.find_ok(rest, s, c, st)(
          Shared.Bool.and_true_right(
            RKnown.State.fits(RLines.Line.state(s, c2), st2),
            RKnown.Known.ok(rest, s)
          )(ok)
        )(e)
      )

# the state of a line, computed with the state R and k of its store, is the
# state that the facts give it
def Known.fresh_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +R: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{R, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.fresh.at(s, c, R, k) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => Equal.sym(
        Maybe<&2, RLines.State>,
        RLines.Line.state(s, Ledgers.Line{h, None{}}),
        Some{RLines.State{R, k}},
        e
      )
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{R, k}}, e): {RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{R}) == RLines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.State>}
        {==})

# the state of a line, computed with the state x that a right table holds
# for its store, is the state that the facts give it
def Known.fresh_ok.at(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  x: RLines.State
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, RKnown.Known.root(c)) == Some{x}: Maybe<&2, RLines.State>
} -> {RKnown.Known.fresh.of(Some{x}, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  match x:
    case RLines.State{+R, +k}:
      ok => e => Known.fresh_at_ok(s, c, R, k)(
        Known.find_ok(kn, s, RKnown.Known.root(c), RLines.State{R, k})(ok)(e)
      )

# the state of a line, computed with the state that a right table holds for
# its store, is the state that the facts give it
def Known.fresh_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.fresh(kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.fresh.of(m, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>},
    RKnown.Known.find(kn, RKnown.Known.root(c)),
    en => {==},
    x => ex => Known.fresh_ok.at(kn, s, c, x)(ok)(ex)
  )

# a right table changes no read of the state of a line
def Known.state_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.state(kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>}:
  +ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.state.of(m, kn, s, c) == RLines.Line.state(s, c): Maybe<&2, RLines.State>},
    RKnown.Known.find(kn, c),
    en => Known.fresh_ok(kn, s, c)(ok),
    +x => ex => Equal.sym(
      Maybe<&2, RLines.State>,
      RLines.Line.state(s, c),
      Some{x},
      Known.find_ok(kn, s, c, x)(ok)(ex)
    )
  )

# a right table changes no read of the versions of a line
def Known.versions_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.versions(kn, s, c) == RLines.Line.versions(s, c): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Equal.cong(
    Maybe<&2, RLines.State>,
    Maybe<&2, List<&2, Types.Entry>>,
    m => Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m),
    RKnown.Known.state(kn, s, c),
    RLines.Line.state(s, c),
    Known.state_ok(kn, s, c)(ok)
  )

# a right table changes no read of a version of a line
def Known.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.at(kn, s, c, k) == RLines.Line.at(s, c, k): Maybe<&2, Types.Entry>}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, Types.Entry>,
    m => RLines.Line.at.of(m, k),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no read of the versions of a store
def Known.store_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.store(kn, s, h) == RLines.Store.versions(s, h): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Known.versions_ok(kn, s, Ledgers.Line{h, None{}})(ok)

# the rule after the versions vs of a line, with the versions R of its
# store, is the rule that the facts give
def Known.rule_at_ok(
  +s: RFacts.Plain(),
  c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +R: List<&2, Types.Entry>,
  +k: Nat
) -> {
  RLines.Line.state(s, RKnown.Known.root(c)) == Some{RLines.State{R, k}}: Maybe<&2, RLines.State>
} -> {RKnown.Known.rule.at(c, vs, R) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      e => {==}
    case Ledgers.Line{+h, Some{+b}}:
      e => (
        %Equal.sym(Maybe<&2, RLines.State>, RLines.Store.state(s, h), Some{RLines.State{R, k}}, e): {RLines.Line.rule(Some{R}, Ledgers.Line{h, Some{b}}, vs) == RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)): Maybe<&2, RLines.Rule>}
        {==})

# the rule after the versions vs of a line, with the state x that a right
# table holds for its store, is the rule that the facts give
def Known.rule_ok.at(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  x: RLines.State
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RKnown.Known.find(kn, RKnown.Known.root(c)) == Some{x}: Maybe<&2, RLines.State>
} -> {RKnown.Known.rule.of(Some{x}, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  match x:
    case RLines.State{+R, +k}:
      ok => e => Known.rule_at_ok(s, c, vs, R, k)(
        Known.find_ok(kn, s, RKnown.Known.root(c), RLines.State{R, k})(ok)(e)
      )

# a right table changes no read of the rule of the next version of a line
def Known.rule_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.rule(kn, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>}:
  ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.rule.of(m, s, c, vs) == RLines.Rule.after(s, c, vs): Maybe<&2, RLines.Rule>},
    RKnown.Known.find(kn, RKnown.Known.root(c)),
    en => {==},
    x => ex => Known.rule_ok.at(kn, s, c, vs, x)(ok)(ex)
  )

# A table stays right
# -------------------

# a right table with the state that the facts give a line is right
def Known.put_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>
} -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.ok(RKnown.Known.put(kn, c, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+st}:
      e => ok => Shared.Bool.and_both(
        RKnown.State.fits(RLines.Line.state(s, c), st),
        RKnown.Known.ok(kn, s)
      )(State.fits_of(RLines.Line.state(s, c), st)(e))(ok)

# a right table that learns the state of a line is right
def Known.learn_one_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.ok(RKnown.Known.learn.one(kn, s, c), s) == True{}: Bool}:
  +ok => Lists.Maybe.by(
    RLines.State,
    m => {RKnown.Known.ok(RKnown.Known.learn.of(kn, s, c, m), s) == True{}: Bool},
    RKnown.Known.find(kn, c),
    en => Known.put_ok(kn, s, c, RKnown.Known.fresh(kn, s, c))(
      Equal.sym(
        Maybe<&2, RLines.State>,
        RKnown.Known.fresh(kn, s, c),
        RLines.Line.state(s, c),
        Known.fresh_ok(kn, s, c)(ok)
      )
    )(ok),
    x => ex => ok
  )

# a right table that learns the states of a line and of its store is right
def Known.learn_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.ok(RKnown.Known.learn(kn, s, c), s) == True{}: Bool}:
  ok => Known.learn_one_ok(RKnown.Known.learn.one(kn, s, RKnown.Known.root(c)), s, c)(
    Known.learn_one_ok(kn, s, RKnown.Known.root(c))(ok)
  )

# a table that is right for the facts s is right after a node takes in an
# ask that starts no store
def Known.asked_ok(
  kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +a: Types.Ask
) -> {
  RFacts.Request.is_start(RLines.Ask.request(a)) == False{}: Bool
} -> {
  RKnown.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.ok(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a}))) == True{}: Bool
}:
  match kn:
    case Nil{}:
      e => ok => {==}
    case Con{RKnown.Kept{+c, +st}, +rest}:
      +e => +ok => Shared.Bool.and_both(
        RKnown.State.fits(Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c), st),
        RKnown.Known.ok(rest, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{a})))
      )(
        %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.take(name, s, Types.Fact.Ask{a}), c), Lines.Line.state(s, c), Moves.Line.state_asked(name, s, a, c)(e)): {RKnown.State.fits(_, st) == True{}: Bool}
        Shared.Bool.and_true_left(
          RKnown.State.fits(Lines.Line.state(s, c), st),
          RKnown.Known.ok(rest, Facts.Facts.crit(s))
        )(ok)
      )(
        Known.asked_ok(rest, name, s, a)(e)(
          Shared.Bool.and_true_right(
            RKnown.State.fits(Lines.Line.state(s, c), st),
            RKnown.Known.ok(rest, Facts.Facts.crit(s))
          )(ok)
        )
      )

# a vote for a slot of the line c changes no state of a line that it does
# not hit
def Line.state_voted(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  c2: Ledgers.Line
) -> {
  RKnown.Known.hit(c, c2) == False{}: Bool
} -> {
  Lines.Line.state(
    Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
    c2
  )
    == Lines.Line.state(s, c2): Maybe<&2, RLines.State>
}:
  match c2:
    case Ledgers.Line{+h, None{}}:
      h0 => Moves.Store.same(Moves.Delta.Vote{name, c, k, t, x}, s, h)({==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), False{}, Bool.or_false_left(Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})
    case Ledgers.Line{+h, Some{+b}}:
      +h0 => Moves.Branch.same(Moves.Delta.Vote{name, c, k, t, x}, s, h, b)({==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c), False{}, Bool.or_false_right(Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})(
        %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), False{}, Bool.or_false_left(Ledgers.Line.is_eq(Ledgers.Line{h, Some{b}}, c), Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, c))(h0)): {Bool.not(_) == True{}: Bool}
        {==})

# a table that is right for the facts s, without the states that a vote for
# the line c may change, is right after the vote
def Known.voted_ok(
  kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RKnown.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.ok(
    RKnown.Known.voted(kn, c),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  match kn:
    case Nil{}:
      ok => {==}
    case Con{RKnown.Kept{+c2, +st}, +rest}:
      +ok => Lists.Bool.by(
        b => {
          RKnown.Known.ok(
            List.filter.put(RKnown.Kept, RKnown.Kept{c2, st}, RKnown.Known.voted(rest, c), Bool.not(b)),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
            == True{}: Bool
        },
        RKnown.Known.hit(c, c2),
        et => Known.voted_ok(rest, name, s, c, k, t, x)(
          Shared.Bool.and_true_right(
            RKnown.State.fits(Lines.Line.state(s, c2), st),
            RKnown.Known.ok(rest, Facts.Facts.crit(s))
          )(ok)
        ),
        ef => Shared.Bool.and_both(
          RKnown.State.fits(
            Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c2),
            st
          ),
          RKnown.Known.ok(
            RKnown.Known.voted(rest, c),
            Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
          )
        )(
          %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.state(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c2), Lines.Line.state(s, c2), Line.state_voted(name, s, c, k, t, x, c2)(ef)): {RKnown.State.fits(_, st) == True{}: Bool}
          Shared.Bool.and_true_left(
            RKnown.State.fits(Lines.Line.state(s, c2), st),
            RKnown.Known.ok(rest, Facts.Facts.crit(s))
          )(ok)
        )(
          Known.voted_ok(rest, name, s, c, k, t, x)(
            Shared.Bool.and_true_right(
              RKnown.State.fits(Lines.Line.state(s, c2), st),
              RKnown.Known.ok(rest, Facts.Facts.crit(s))
            )(ok)
          )
        )
      )

# A work reads through a right table
# ----------------------------------

# a right table changes no pins
def Pins.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +m: Nat,
  r: Spec.Request
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Pins.for(kn, s, c, vs, m, r) == RWorks.Pins.for(RKnown.Known.none(), s, c, vs, m, r): Types.Pins
}:
  match r:
    case Spec.Request.Merge{+f, x}:
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Types.Pins,
        fv => RWorks.Pins.merge(m, c, f, vs, fv),
        RKnown.Known.versions(kn, s, f),
        RLines.Line.versions(s, f),
        Known.versions_ok(kn, s, f)(ok)
      )
    case Spec.Request.Start{os}:
      ok => {==}
    case Spec.Request.Write{b, p, w}:
      ok => {==}
    case Spec.Request.Resolve{j, p, w}:
      ok => {==}
    case Spec.Request.Mark{b, j, v}:
      ok => {==}
    case Spec.Request.Move{b, j, v}:
      ok => {==}
    case Spec.Request.Group{h, g, ms}:
      ok => {==}
    case Spec.Request.Own{b, g}:
      ok => {==}

# a right table changes no era that the node pins
def Era.now_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Era.now(kn, s, c) == RWorks.Era.now(RKnown.Known.none(), s, c): Nat
}:
  match c:
    case Ledgers.Line{+h, b}:
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Nat,
        m => RWorks.Era.now.of(m),
        RKnown.Known.store(kn, s, h),
        RLines.Store.versions(s, h),
        Known.store_ok(kn, s, h)(ok)
      )

# a right table changes no rule of the next version of a line
def Work.rule_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.rule(kn, s, c, m) == RWorks.Work.rule(RKnown.Known.none(), s, c, m): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RLines.State{+vs, k}}:
      ok => Known.rule_ok(kn, s, c, vs)(ok)

# a right table changes no next slot of a line
def Work.open_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.open(kn, s, name, c) == RWorks.Work.open(RKnown.Known.none(), s, name, c): Maybe<&2, RWorks.Open>
}:
  +ok => (
    %Known.state_ok(kn, s, c)(ok): {RWorks.Work.open(kn, s, name, c) == RWorks.Work.open.at(name, _, RWorks.Work.rule(RKnown.Known.none(), s, c, _)): Maybe<&2, RWorks.Open>}
    %Work.rule_ok(kn, s, c, RKnown.Known.state(kn, s, c))(ok): {RWorks.Work.open(kn, s, name, c) == RWorks.Work.open.at(name, RKnown.Known.state(kn, s, c), _): Maybe<&2, RWorks.Open>}
    {==})

# a right table changes no vote for an ask at the next slot of a line
def Work.offer.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RWorks.Open>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer.at(kn, s, name, c, a, m) == RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RWorks.Open{+vs, +k, +ns}}:
      +ok => (
        %Era.now_ok(kn, s, c)(ok): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(
        RWorks.Plan,
        Bool.not(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))
        ),
        u => RWorks.Plan.of(
          c,
          k,
          RWorks.Work.offer.of(
            u2 => Types.Pick{a, RWorks.Pins.for(RKnown.Known.none(), s, c, vs, _, RLines.Ask.request(a))},
            RRounds.Slot.chance(RWorks.Work.ballots(s, c, k), ns, k, name)
          )
        )
      ): Maybe<&2, RWorks.Plan>}
        %Pins.for_ok(kn, s, c, vs, RWorks.Era.now(kn, s, c), RLines.Ask.request(a))(ok): {RWorks.Work.offer.at(kn, s, name, c, a, Some{RWorks.Open{vs, k, ns}}) == Shared.Maybe.when(
        RWorks.Plan,
        Bool.not(
          Shared.List.some(~Types.Entry, ~Ledgers.Id, ~RLines.Entry.is_of, vs, RLines.Ask.id(a))
        ),
        u => RWorks.Plan.of(
          c,
          k,
          RWorks.Work.offer.of(
            u2 => Types.Pick{a, _},
            RRounds.Slot.chance(RWorks.Work.ballots(s, c, k), ns, k, name)
          )
        )
      ): Maybe<&2, RWorks.Plan>}
        {==})

# a right table changes no vote for an ask on its line
def Work.offer.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer.on(kn, s, name, a, m) == RWorks.Work.offer.on(RKnown.Known.none(), s, name, a, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+c}:
      +ok => (
        %Work.open_ok(kn, s, name, c)(ok): {RWorks.Work.offer.on(kn, s, name, a, Some{c}) == RWorks.Work.offer.at(RKnown.Known.none(), s, name, c, a, _): Maybe<&2, RWorks.Plan>}
        Work.offer.at_ok(kn, s, name, c, a, RWorks.Work.open(kn, s, name, c))(ok))

# a right table changes no vote for an ask
def Work.offer_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +a: Types.Ask
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.offer(kn, s, name, a) == RWorks.Work.offer(RKnown.Known.none(), s, name, a): Maybe<&2, RWorks.Plan>
}:
  ok => Work.offer.on_ok(
    kn,
    s,
    name,
    a,
    RWorks.Request.line(RFacts.Facts.list(s), RLines.Ask.request(a))
  )(ok)

# a right table changes no ask that the node may vote for
def Work.ready_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.ready(kn, s, name, fs) == RWorks.Work.ready(RKnown.Known.none(), s, name, fs): List<&2, Types.Ask>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      ok => Work.ready_ok(kn, s, name, rest)(ok)
    case Con{Types.Fact.Ask{+a}, +rest}:
      +ok => (
        %Work.ready_ok(kn, s, name, rest)(ok): {RWorks.Work.ready(kn, s, name, Types.Fact.Ask{a} <> rest) == List.filter.put(Types.Ask, a, _, Maybe.is_some(&2, RWorks.Plan, RWorks.Work.offer(RKnown.Known.none(), s, name, a))): List<&2, Types.Ask>}
        %Work.offer_ok(kn, s, name, a)(ok): {RWorks.Work.ready(kn, s, name, Types.Fact.Ask{a} <> rest) == List.filter.put(Types.Ask, a, RWorks.Work.ready(kn, s, name, rest), Maybe.is_some(&2, RWorks.Plan, _)): List<&2, Types.Ask>}
        {==})

# a right table changes no vote for the ask m
def Work.propose.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  m: Maybe<&2, Types.Ask>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.propose.of(kn, s, name, m) == RWorks.Work.propose.of(RKnown.Known.none(), s, name, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+a}:
      ok => Work.offer_ok(kn, s, name, a)(ok)

# a right table changes no vote that the node proposes
def Work.propose_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.propose(kn, s, name) == RWorks.Work.propose(RKnown.Known.none(), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => (
    %Work.ready_ok(kn, s, name, RFacts.Facts.list(s))(ok): {RWorks.Work.propose(kn, s, name) == RWorks.Work.propose.of(RKnown.Known.none(), s, name, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, _)): Maybe<&2, RWorks.Plan>}
    Work.propose.of_ok(kn, s, name, Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RWorks.Work.ready(kn, s, name, RFacts.Facts.list(s))))(ok))

# a right table changes no vote at the slot of a ballot
def Work.follow.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.follow.of(kn, s, name, f) == RWorks.Work.follow.of(RKnown.Known.none(), s, name, f): Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      ok => Equal.cong(
        Maybe<&2, RWorks.Open>,
        Maybe<&2, RWorks.Plan>,
        m => RWorks.Work.follow.at(s, name, c, k, m),
        RWorks.Work.open(kn, s, name, c),
        RWorks.Work.open(RKnown.Known.none(), s, name, c),
        Work.open_ok(kn, s, name, c)(ok)
      )
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => {==}
    case Types.Fact.Ask{a}:
      ok => {==}

# a right table changes no vote at the slot of a ballot among fs
def Work.follow_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.follow(kn, s, name, fs) == RWorks.Work.follow(RKnown.Known.none(), s, name, fs): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{+f, +rest}:
      +ok => (
        %Work.follow.of_ok(kn, s, name, f)(ok): {RWorks.Work.follow(kn, s, name, f <> rest) == RWorks.Work.follow.or(_, u => RWorks.Work.follow(RKnown.Known.none(), s, name, rest)): Maybe<&2, RWorks.Plan>}
        %Work.follow_ok(kn, s, name, rest)(ok): {RWorks.Work.follow(kn, s, name, f <> rest) == RWorks.Work.follow.or(RWorks.Work.follow.of(kn, s, name, f), u => _): Maybe<&2, RWorks.Plan>}
        {==})

# a right table changes no pass for a request on its line
def Work.pass.on_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Line>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass.on(kn, s, name, i, m) == RWorks.Work.pass.on(RKnown.Known.none(), s, name, i, m): Maybe<&2, RWorks.Plan>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+c}:
      ok => Equal.cong(
        Maybe<&2, RWorks.Open>,
        Maybe<&2, RWorks.Plan>,
        o => RWorks.Work.pass.at(s, name, c, None{}, Some{i}, o),
        RWorks.Work.open(kn, s, name, c),
        RWorks.Work.open(RKnown.Known.none(), s, name, c),
        Work.open_ok(kn, s, name, c)(ok)
      )

# a right table changes no pass at the slot of a fact
def Work.pass.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  f: Types.Fact
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass.of(kn, s, name, f) == RWorks.Work.pass.of(RKnown.Known.none(), s, name, f): Maybe<&2, RWorks.Plan>
}:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      ok => Equal.cong(
        Maybe<&2, RWorks.Open>,
        Maybe<&2, RWorks.Plan>,
        o => RWorks.Work.pass.at(s, name, c, Some{k}, None{}, o),
        RWorks.Work.open(kn, s, name, c),
        RWorks.Work.open(RKnown.Known.none(), s, name, c),
        Work.open_ok(kn, s, name, c)(ok)
      )
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      ok => {==}
    case Types.Fact.Ask{Types.Ask{+i, n, +r}}:
      ok => Work.pass.on_ok(kn, s, name, i, RWorks.Request.line(RFacts.Facts.list(s), r))(ok)

# a right table changes no pass at the slot of a fact among fs
def Work.pass_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.pass(kn, s, name, fs) == RWorks.Work.pass(RKnown.Known.none(), s, name, fs): Maybe<&2, RWorks.Plan>
}:
  match fs:
    case Nil{}:
      ok => {==}
    case Con{+f, +rest}:
      +ok => (
        %Work.pass.of_ok(kn, s, name, f)(ok): {RWorks.Work.pass(kn, s, name, f <> rest) == RWorks.Work.follow.or(_, u => RWorks.Work.pass(RKnown.Known.none(), s, name, rest)): Maybe<&2, RWorks.Plan>}
        %Work.pass_ok(kn, s, name, rest)(ok): {RWorks.Work.pass(kn, s, name, f <> rest) == RWorks.Work.follow.or(RWorks.Work.pass.of(kn, s, name, f), u => _): Maybe<&2, RWorks.Plan>}
        {==})

# a right table changes no ballot that the node casts next
def Work.plan_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.plan(kn, s, name) == RWorks.Work.plan(RKnown.Known.none(), s, name): Maybe<&2, RWorks.Plan>
}:
  +ok => (
    %Work.propose_ok(kn, s, name)(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(_, u => RWorks.Work.follow.or(RWorks.Work.follow(RKnown.Known.none(), s, name, RFacts.Facts.list(s)), u2 => RWorks.Work.pass(RKnown.Known.none(), s, name, RFacts.Facts.list(s)))): Maybe<&2, RWorks.Plan>}
    %Work.follow_ok(kn, s, name, RFacts.Facts.list(s))(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose(kn, s, name), u => RWorks.Work.follow.or(_, u2 => RWorks.Work.pass(RKnown.Known.none(), s, name, RFacts.Facts.list(s)))): Maybe<&2, RWorks.Plan>}
    %Work.pass_ok(kn, s, name, RFacts.Facts.list(s))(ok): {RWorks.Work.plan(kn, s, name) == RWorks.Work.follow.or(RWorks.Work.propose(kn, s, name), u => RWorks.Work.follow.or(RWorks.Work.follow(kn, s, name, RFacts.Facts.list(s)), u2 => _)): Maybe<&2, RWorks.Plan>}
    {==})

# a right table changes no work
def Work.does_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RWorks.Work.does(kn, s, name) == RWorks.Work.does(RKnown.Known.none(), s, name): RFacts.Plain()
}:
  ok => Equal.cong(
    Maybe<&2, RWorks.Plan>,
    RFacts.Plain(),
    m => RWorks.Work.cast(s, name, m),
    RWorks.Work.plan(kn, s, name),
    RWorks.Work.plan(RKnown.Known.none(), s, name),
    Work.plan_ok(kn, s, name)(ok)
  )

# The content and the answers read through a right table
# -----------------------------------------------------

# a right table changes no step of a way
def Way.hop_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Spec.Point
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Way.hop(kn, s, c, k, w) == RContents.Way.hop(RKnown.Known.none(), s, c, k, w): Bool
}:
  ok => Equal.cong(
    Maybe<&2, Types.Entry>,
    Bool,
    m => RContents.Way.hop.of(c, k, w, m),
    RKnown.Known.at(kn, s, c, k),
    RLines.Line.at(s, c, k),
    Known.at_ok(kn, s, c, k)(ok)
  )

# a right table changes no way
def Way.ok_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +a: Spec.Point,
  ws: List<&2, Spec.Point>,
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Way.ok(kn, s, a, ws, c, k) == RContents.Way.ok(RKnown.Known.none(), s, a, ws, c, k): Bool
}:
  match ws:
    case Nil{}:
      ok => {==}
    case Con{+w, +rest}:
      +ok => (
        %Way.hop_ok(kn, s, c, k, w)(ok): {RContents.Way.ok(kn, s, a, w <> rest, c, k) == Bool.and(_, RContents.Way.ok(RKnown.Known.none(), s, a, rest, Spec.Point.line(w), Spec.Point.n(w))): Bool}
        %Way.ok_ok(kn, s, a, rest, Spec.Point.line(w), Spec.Point.n(w))(ok): {RContents.Way.ok(kn, s, a, w <> rest, c, k) == Bool.and(RContents.Way.hop(kn, s, c, k, w), _): Bool}
        {==})

# a right table changes no check of the ways of a merge
def Merge.fits.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Spec.Point>,
  +ours: List<&2, Spec.Point>,
  +theirs: List<&2, Spec.Point>,
  +t: Spec.Point
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Merge.fits.of(kn, s, c, j, m, ours, theirs, t) == RContents.Merge.fits.of(RKnown.Known.none(), s, c, j, m, ours, theirs, t): Bool
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+a}:
      +ok => (
        %Way.ok_ok(kn, s, a, ours, c, j)(ok): {RContents.Merge.fits.of(kn, s, c, j, Some{a}, ours, theirs, t) == Bool.and(_, RContents.Way.ok(RKnown.Known.none(), s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))): Bool}
        %Way.ok_ok(kn, s, a, theirs, Spec.Point.line(t), Spec.Point.n(t))(ok): {RContents.Merge.fits.of(kn, s, c, j, Some{a}, ours, theirs, t) == Bool.and(RContents.Way.ok(kn, s, a, ours, c, j), _): Bool}
        {==})

# a right table changes no check of a merge
def Merge.fits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  +e: Types.Entry
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Merge.fits(kn, s, c, j, e) == RContents.Merge.fits(RKnown.Known.none(), s, c, j, e): Bool
}:
  ok => Merge.fits.of_ok(
    kn,
    s,
    c,
    j,
    RContents.Entry.base(e),
    RContents.Entry.ours(e),
    RContents.Entry.theirs(e),
    RContents.Point.or(c, RContents.Entry.takes(e))
  )(ok)

# a right table changes no check of a version
def Entry.fits_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat,
  m: Maybe<&2, Types.Entry>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Entry.fits(kn, s, c, j, m) == RContents.Entry.fits(RKnown.Known.none(), s, c, j, m): Bool
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+e}:
      ok => Merge.fits_ok(kn, s, c, j, e)(ok)

# a right table changes no content of a version
def Content.at_ok(
  fuel: Nat,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.at(fuel, kn, s, c, k) == RContents.Content.at(fuel, RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
}:
  match fuel k:
    case 0n k:
      ok => {==}
    case 1n+f 0n:
      ok => Equal.cong(
        Maybe<&2, Types.Entry>,
        Maybe<&2, RFiles.Files()>,
        m => RContents.Content.first(m),
        RKnown.Known.at(kn, s, c, 0n),
        RLines.Line.at(s, c, 0n),
        Known.at_ok(kn, s, c, 0n)(ok)
      )
    case 1n+(+f) 1n+(+j):
      +ok => (
        %Known.at_ok(kn, s, c, 1n+j)(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(_, RContents.Entry.fits(RKnown.Known.none(), s, c, j, _), RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, _)), Spec.Point.n(RContents.Entry.taken(c, _))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, _)), Spec.Point.n(RContents.Entry.based(c, _)))): Maybe<&2, RFiles.Files()>}
        %Entry.fits_ok(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j))(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), _, RContents.Content.at(f, RKnown.Known.none(), s, c, j), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Content.at_ok(f, kn, s, c, j)(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.at(f, kn, s, c, j), _, RContents.Content.at(f, RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))): Maybe<&2, RFiles.Files()>}
        %Content.at_ok(f, kn, s, Spec.Point.line(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.based(c, RKnown.Known.at(kn, s, c, 1n+j))))(ok): {RContents.Content.at(1n+f, kn, s, c, 1n+j) == RContents.Content.next(RKnown.Known.at(kn, s, c, 1n+j), RContents.Entry.fits(kn, s, c, j, RKnown.Known.at(kn, s, c, 1n+j)), RContents.Content.at(f, kn, s, c, j), RContents.Content.at(f, kn, s, Spec.Point.line(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j))), Spec.Point.n(RContents.Entry.taken(c, RKnown.Known.at(kn, s, c, 1n+j)))), _): Maybe<&2, RFiles.Files()>}
        {==})

# a right table changes no content
def Content.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.of(kn, s, c, k) == RContents.Content.of(RKnown.Known.none(), s, c, k): Maybe<&2, RFiles.Files()>
}:
  ok => Content.at_ok(RFacts.Facts.fuel(s), kn, s, c, k)(ok)

# a right table changes no read of a resource
def Content.read_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RContents.Content.read(kn, s, c, k, p) == RContents.Content.read(RKnown.Known.none(), s, c, k, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  ok => Equal.cong(
    Maybe<&2, RFiles.Files()>,
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    m => RContents.Content.get(m, p),
    RContents.Content.of(kn, s, c, k),
    RContents.Content.of(RKnown.Known.none(), s, c, k),
    Content.of_ok(kn, s, c, k)(ok)
  )

# a right table changes no clash
def Clashes.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Clashes.of(kn, s, c, k, e) == RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e): Maybe<&2, List<&2, String>>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      +ok => (
        %Merge.fits_ok(kn, s, c, j, e)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), _), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), _, RContents.Content.of(RKnown.Known.none(), s, c, j), RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, c, j)(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), _, RContents.Content.of(RKnown.Known.none(), s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))): Maybe<&2, List<&2, String>>}
        %Content.of_ok(kn, s, Spec.Point.line(RContents.Entry.taken(c, Some{e})), Spec.Point.n(RContents.Entry.taken(c, Some{e})))(ok): {RAnswers.Clashes.of(kn, s, c, 1n+j, e) == RAnswers.Clashes.at(Bool.and(RContents.Request.is_merge(RAnswers.Entry.request(e)), RContents.Merge.fits(kn, s, c, j, e)), RContents.Content.of(kn, s, Spec.Point.line(RContents.Entry.based(c, Some{e})), Spec.Point.n(RContents.Entry.based(c, Some{e}))), RContents.Content.of(kn, s, c, j), _): Maybe<&2, List<&2, String>>}
        {==})

# a right table changes no base of a merge
def Base.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat,
  +e: Types.Entry
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Base.of(kn, s, c, k, e) == RAnswers.Base.of(RKnown.Known.none(), s, c, k, e): Maybe<&2, Spec.Point>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      ok => Equal.cong(
        Bool,
        Maybe<&2, Spec.Point>,
        b => Shared.Maybe.when(Spec.Point, b, u => RContents.Entry.base(e)),
        RContents.Merge.fits(kn, s, c, j, e),
        RContents.Merge.fits(RKnown.Known.none(), s, c, j, e),
        Merge.fits_ok(kn, s, c, j, e)(ok)
      )

# a right table changes no status
def Status.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +k: Nat,
  +e: Types.Entry
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Status.of(kn, s, c, vs, k, e) == RAnswers.Status.of(RKnown.Known.none(), s, c, vs, k, e): Spec.Status
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, String>>,
    Spec.Status,
    cs => RAnswers.Status.by(vs, k, RLines.Entry.id(e), RAnswers.Entry.request(e), cs),
    RAnswers.Clashes.of(kn, s, c, k, e),
    RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e),
    Clashes.of_ok(kn, s, c, k, e)(ok)
  )

# a right table changes no versions before a version
def Line.before_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +j: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Line.before(kn, s, c, j) == RAnswers.Line.before(RKnown.Known.none(), s, c, j): Maybe<&2, List<&2, Types.Entry>>
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, List<&2, Types.Entry>>,
    m => RAnswers.Line.before.of(j, m),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no rule after the versions m
def Rule.for.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Rule.for.of(kn, s, c, m) == RAnswers.Rule.for.of(RKnown.Known.none(), s, c, m): Maybe<&2, RLines.Rule>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+vs}:
      ok => Known.rule_ok(kn, s, c, vs)(ok)

# a right table changes no rule of a version
def Rule.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Rule.for(kn, s, c, k) == RAnswers.Rule.for(RKnown.Known.none(), s, c, k): Maybe<&2, RLines.Rule>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      +ok => (
        %Line.before_ok(kn, s, c, j)(ok): {RAnswers.Rule.for(kn, s, c, 1n+j) == RAnswers.Rule.for.of(RKnown.Known.none(), s, c, _): Maybe<&2, RLines.Rule>}
        Rule.for.of_ok(kn, s, c, RAnswers.Line.before(kn, s, c, j))(ok))

# a right table changes no era of a version
def Era.for_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  k: Nat
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Era.for(kn, s, c, k) == RAnswers.Era.for(RKnown.Known.none(), s, c, k): Maybe<&2, Nat>
}:
  match k:
    case 0n:
      ok => {==}
    case 1n+(+j):
      ok => Equal.cong(
        Maybe<&2, List<&2, Types.Entry>>,
        Maybe<&2, Nat>,
        m => Maybe.map(&2, List<&2, Types.Entry>, Nat, vs => RLines.Line.era(c, vs), m),
        RAnswers.Line.before(kn, s, c, j),
        RAnswers.Line.before(RKnown.Known.none(), s, c, j),
        Line.before_ok(kn, s, c, j)(ok)
      )

# a right table changes no read of the versions of a store
def Store.read_ok(
  -A: Data,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +h: Hashes.Hash,
  +m: Nat,
  -f: List<&2, Types.Entry> -> Maybe<&2, A>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Store.read(A, kn, s, h, m, f) == RAnswers.Store.read(A, RKnown.Known.none(), s, h, m, f): Maybe<&2, A>
}:
  ok => (
    %Known.store_ok(kn, s, h)(ok): {RAnswers.Store.read(A, kn, s, h, m, f) == RAnswers.Store.read.of(A, m, f, _): Maybe<&2, A>}
    {==})

# a right table changes no search of a request
def Line.find_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +i: Ledgers.Id
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Line.find(kn, s, c, i) == RAnswers.Line.find(RKnown.Known.none(), s, c, i): Maybe<&2, RAnswers.Found>
}:
  ok => Equal.cong(
    Maybe<&2, List<&2, Types.Entry>>,
    Maybe<&2, RAnswers.Found>,
    m => RAnswers.Line.find.of(i, m),
    RKnown.Known.versions(kn, s, c),
    RLines.Line.versions(s, c),
    Known.versions_ok(kn, s, c)(ok)
  )

# a right table changes no reply with a status
def Reply.status_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  v: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, RAnswers.Found>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Reply.status(kn, s, c, v, m) == RAnswers.Reply.status(RKnown.Known.none(), s, c, v, m): Maybe<&2, Spec.Reply>
}:
  match v m:
    case None{} None{}:
      ok => {==}
    case None{} Some{x}:
      ok => {==}
    case Some{vs} None{}:
      ok => {==}
    case Some{+vs} Some{RAnswers.Found{+k, +e}}:
      ok => Equal.cong(
        Spec.Status,
        Maybe<&2, Spec.Reply>,
        x => Some{Spec.Reply.Status{x}},
        RAnswers.Status.of(kn, s, c, vs, k, e),
        RAnswers.Status.of(RKnown.Known.none(), s, c, vs, k, e),
        Status.of_ok(kn, s, c, vs, k, e)(ok)
      )

# a right table changes no clash of a found request
def Clashes.then_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RAnswers.Found>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Found.then(List<&2, String>, m, k => e => RAnswers.Clashes.of(kn, s, c, k, e)) == RAnswers.Found.then(List<&2, String>, m, k => e => RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e)): Maybe<&2, List<&2, String>>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RAnswers.Found{+k, +e}}:
      ok => Clashes.of_ok(kn, s, c, k, e)(ok)

# a right table changes no base of a found merge
def Base.then_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RAnswers.Found>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Found.then(Spec.Point, m, k => e => RAnswers.Base.of(kn, s, c, k, e)) == RAnswers.Found.then(Spec.Point, m, k => e => RAnswers.Base.of(RKnown.Known.none(), s, c, k, e)): Maybe<&2, Spec.Point>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{RAnswers.Found{+k, +e}}:
      ok => Base.of_ok(kn, s, c, k, e)(ok)

# a right table changes no reply
def Answer.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  q: Spec.Question
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.Answer.of(kn, s, q) == RAnswers.Answer.of(RKnown.Known.none(), s, q): Maybe<&2, Spec.Reply>
}:
  match q:
    case Spec.Question.Status{+c, +i}:
      +ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Status{c, i}) == RAnswers.Reply.status(RKnown.Known.none(), s, c, _, RAnswers.Line.find(RKnown.Known.none(), s, c, i)): Maybe<&2, Spec.Reply>}
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Status{c, i}) == RAnswers.Reply.status(RKnown.Known.none(), s, c, RKnown.Known.versions(kn, s, c), _): Maybe<&2, Spec.Reply>}
        Reply.status_ok(kn, s, c, RKnown.Known.versions(kn, s, c), RAnswers.Line.find(kn, s, c, i))(ok))
    case Spec.Question.Request{+c, +i}:
      ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Request{c, i}) == RAnswers.Reply.ask(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Version{+c, +k}:
      ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Version{c, k}) == RAnswers.Reply.id(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Content{+c, +k}:
      ok => (
        %Content.of_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Content{c, k}) == RAnswers.Reply.hash(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Group{+c, +k}:
      ok => (
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Group{c, k}) == Maybe.bind(&2, RLines.Rule, Spec.Reply, _, RAnswers.Rule.group): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Owners{+c, +k}:
      +ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owners{c, k}) == RAnswers.Owners.of(s, c, _, RAnswers.Rule.for(RKnown.Known.none(), s, c, k)): Maybe<&2, Spec.Reply>}
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owners{c, k}) == RAnswers.Owners.of(s, c, RKnown.Known.at(kn, s, c, k), _): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Members{+h, +g, +m}:
      ok => (
        %Store.read_ok(List<&2, String>, kn, s, h, m, R => Groups.Groups.members(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Members{h, g, m}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Nodes{+h, +g, +m}:
      ok => (
        %Store.read_ok(List<&2, String>, kn, s, h, m, R => Groups.Groups.nodes(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Nodes{h, g, m}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.IsGroup{+h, +g, +m}:
      ok => (
        %Store.read_ok(Bool, kn, s, h, m, R => Groups.Groups.is_group(R, h, g, m))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.IsGroup{h, g, m}) == RAnswers.Reply.yes(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Mark{+c, +m}:
      ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Mark{c, m}) == RAnswers.Reply.number(RAnswers.Mark.of(m, _)): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Count{+c}:
      ok => (
        %Known.versions_ok(kn, s, c)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Count{c}) == RAnswers.Reply.count(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Clashes{+c, +i}:
      +ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Clashes{c, i}) == RAnswers.Reply.names(RAnswers.Found.then(List<&2, String>, _, k => e => RAnswers.Clashes.of(RKnown.Known.none(), s, c, k, e))): Maybe<&2, Spec.Reply>}
        %Clashes.then_ok(kn, s, c, RAnswers.Line.find(kn, s, c, i))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Clashes{c, i}) == RAnswers.Reply.names(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Affects{+c, +a, +b, +us, +bs}:
      +ok => (
        %Content.of_ok(kn, s, c, a)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Affects{c, a, b, us, bs}) == RAnswers.Affects.of(_, RContents.Content.of(RKnown.Known.none(), s, c, b), us, bs): Maybe<&2, Spec.Reply>}
        %Content.of_ok(kn, s, c, b)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Affects{c, a, b, us, bs}) == RAnswers.Affects.of(RContents.Content.of(kn, s, c, a), _, us, bs): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Parents{+c, +k}:
      ok => (
        %Known.at_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Parents{c, k}) == RAnswers.Reply.parents(c, k, _): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Base{+c, +i}:
      +ok => (
        %Line.find_ok(kn, s, c, i)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Base{c, i}) == RAnswers.Reply.point(RAnswers.Found.then(Spec.Point, _, k => e => RAnswers.Base.of(RKnown.Known.none(), s, c, k, e))): Maybe<&2, Spec.Reply>}
        %Base.then_ok(kn, s, c, RAnswers.Line.find(kn, s, c, i))(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Base{c, i}) == RAnswers.Reply.point(_): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Owner{+c, +k}:
      ok => (
        %Rule.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Owner{c, k}) == Maybe.bind(&2, RLines.Rule, Spec.Reply, _, RAnswers.Rule.owner): Maybe<&2, Spec.Reply>}
        {==})
    case Spec.Question.Era{+c, +k}:
      ok => (
        %Era.for_ok(kn, s, c, k)(ok): {RAnswers.Answer.of(kn, s, Spec.Question.Era{c, k}) == RAnswers.Reply.number(_): Maybe<&2, Spec.Reply>}
        {==})

# a right table changes no view of the newest version
def View.newest_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.newest(kn, s, b, p, m) == RAnswers.View.newest(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match m:
    case None{}:
      ok => {==}
    case Some{+vs}:
      ok => Content.read_ok(kn, s, b, Nat.sub(List.length(&2, Types.Entry, vs), 1n), p)(ok)

# a right table changes no view after the write m
def View.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +b: Ledgers.Line,
  +p: String,
  m: Maybe<&2, Types.Ask>
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.of(kn, s, b, p, m) == RAnswers.View.of(RKnown.Known.none(), s, b, p, m): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match m:
    case None{}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.of(kn, s, b, p, None{}) == RAnswers.View.newest(RKnown.Known.none(), s, b, p, _): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok))
    case Some{+a}:
      +ok => (
        %Known.versions_ok(kn, s, b)(ok): {RAnswers.View.of(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, _), u => RAnswers.View.newest(RKnown.Known.none(), s, b, p, _), u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        %View.newest_ok(kn, s, b, p, RKnown.Known.versions(kn, s, b))(ok): {RAnswers.View.of(kn, s, b, p, Some{a}) == Shared.Bool.when(Maybe<&2, Maybe<&2, List<&2, U32>>>, RAnswers.View.decided(a, RKnown.Known.versions(kn, s, b)), u => _, u => Some{RAnswers.Request.words(RLines.Ask.request(a))}): Maybe<&2, Maybe<&2, List<&2, U32>>>}
        {==})

# a right table changes no view
def View.at_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {
  RAnswers.View.at(kn, s, w, b, p) == RAnswers.View.at(RKnown.Known.none(), s, w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  ok => View.of_ok(
    kn,
    s,
    b,
    p,
    Lists.List.top(~Types.Ask, ~RFacts.Ask.seq, RAnswers.Writes.of(RFacts.Facts.list(s), RAnswers.Place{w, b, p}))
  )(ok)

# A vote continues a run
# ----------------------

# 0 added to a number is the number
def Nat.add_zero(a: Nat) -> {Nat.add(a, 0n) == a: Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, Nat.add_zero(p))

# a sum is the sum of its terms in the other order
def Nat.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a): Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Nat.add_zero(b))
    case 1n+(+p):
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Shared.Nat.add_succ(b, p)): {1n+Nat.add(p, b) == _: Nat}
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, b), Nat.add(b, p), Nat.add_comm(p, b))

# a number is below one more than its sum with another
def Nat.lt_succ_add(+a: Nat, +b: Nat) -> {Nat.is_lt(a, 1n+Nat.add(a, b)) == True{}: Bool}:
  Shared.Nat.le_lt(a, Nat.add(a, b), 1n+Nat.add(a, b))(Shared.Nat.le_add_first(a, b))(Shared.Nat.lt_succ(Nat.add(a, b)))

# a run whose next slot is not decided stays where it is
def Run.none(
  g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {Lines.Line.run(g, s, r, c, st, None{}) == st: RLines.State}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a run of f and g slots is a run of g slots from where a run of f slots ends
def Run.plus(
  f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st))
    == Lines.Line.run(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))): RLines.State
}:
  match f:
    case 0n:
      {==}
    case 1n+(+p):
      Lists.Maybe.by(
        RLines.State,
        m => {
          Lines.Line.run(1n+Nat.add(p, g), s, r, c, st, m)
            == Lines.Line.run(g, s, r, c, Lines.Line.run(1n+p, s, r, c, st, m), Lines.Line.step(s, r, c, Lines.Line.run(1n+p, s, r, c, st, m))): RLines.State
        },
        Lines.Line.step(s, r, c, st),
        en => (
          %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(s, r, c, st), None{}, en): {st == Lines.Line.run(g, s, r, c, st, _): RLines.State}
          Equal.sym(RLines.State, Lines.Line.run(g, s, r, c, st, None{}), st, Run.none(g, s, r, c, st))),
        +st2 => e2 => Run.plus(p, g, s, r, c, st2)
      )

# a run that may go past the bound of the line ends where it ends with more
# slots to go
def Run.more(
  +f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(s), c), Nat.add(f, RLines.State.slot(st))) == True{}: Bool} -> {
  Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)) == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State
}:
  h => (
    %Equal.sym(RLines.State, Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.run(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))), Run.plus(f, g, s, r, c, st)): {_ == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), None{}, Versions.Run.stops(f, s, r, c, st)(h)): {Lines.Line.run(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), _) == Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
    Run.none(g, s, r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))))

# two runs that may go past the bound of the line end at the same state
def Run.fuel(
  +f: Nat,
  +g: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(s), c), Nat.add(f, RLines.State.slot(st))) == True{}: Bool} -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(s), c), Nat.add(g, RLines.State.slot(st))) == True{}: Bool} -> {
  Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)) == Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State
}:
  hf => hg => Equal.trans(
    RLines.State,
    Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)),
    Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)),
    Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)),
    Equal.sym(RLines.State, Lines.Line.run(Nat.add(f, g), s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), Run.more(f, g, s, r, c, st)(hf)),
    (
      %Equal.sym(Nat, Nat.add(f, g), Nat.add(g, f), Nat.add_comm(f, g)): {Lines.Line.run(_, s, r, c, st, Lines.Line.step(s, r, c, st)) == Lines.Line.run(g, s, r, c, st, Lines.Line.step(s, r, c, st)): RLines.State}
      Run.more(g, f, s, r, c, st)(hg))
  )

# a vote for the slot k of the line c is no vote for a slot of c below k
def Cast.keeps(
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  +j: Nat
) -> {
  Nat.is_le(1n+j, k) == True{}: Bool
} -> {Moves.Delta.keeps(Moves.Delta.Vote{name, c, k, t, x}, c, j) == True{}: Bool}:
  lt => (
    %Equal.sym(Bool, Nat.is_eq(j, k), False{}, Moves.Nat.lt_ne(j, k)(lt)): {Bool.not(Bool.and(Ledgers.Line.is_eq(c, c), _)) == True{}: Bool}
    %Equal.sym(Bool, Bool.and(Ledgers.Line.is_eq(c, c), False{}), False{}, Shared.Bool.and_false_right(Ledgers.Line.is_eq(c, c))): {Bool.not(_) == True{}: Bool}
    {==})

# after a vote for the next slot of the state st, a run from st that may go
# past the bound of the line ends where the continued run ends
def Cast.stop(
  +f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State
) -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {
  Lines.Line.run(f2, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st)): RLines.State
}:
  hw => Run.fuel(f2, 1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st)(hw)(
    Nat.lt_succ_add(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), RLines.State.slot(st))
  )

# from a state whose slot is below the slot of the vote and decided, a run
# after the vote does what a run from the state after that slot does (ih)
def Cast.go(
  f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State,
  +st2: RLines.State,
  +X: RLines.State,
  +e2: {Lines.Line.step(s, r, c, st) == Some{st2}: Maybe<&2, RLines.State>},
  lt: {Nat.is_le(1n+RLines.State.slot(st), RLines.State.slot(X)) == True{}: Bool},
  ih: @f3: Nat -> {Nat.is_lt(RLines.State.slot(X), Nat.add(f3, RLines.State.slot(st2))) == True{}: Bool} -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Nat.add(f3, RLines.State.slot(st2))) == True{}: Bool} -> {Lines.Line.run(f3, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st2, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st2)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X)): RLines.State}
) -> {Nat.is_lt(RLines.State.slot(X), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Lines.Line.run(f2, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X)): RLines.State}:
  match f2:
    case 0n:
      hv => hw => Lists.Bool.clash(
        {Lines.Line.run(0n, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X)): RLines.State},
        Nat.is_lt(RLines.State.slot(X), RLines.State.slot(st)),
        Shared.Nat.le_nlt(RLines.State.slot(st), RLines.State.slot(X))(
          Shared.Nat.le_trans(RLines.State.slot(st), 1n+RLines.State.slot(st), RLines.State.slot(X))(
            Shared.Nat.le_succ(RLines.State.slot(st), RLines.State.slot(st))(Shared.Nat.le_refl(RLines.State.slot(st)))
          )(lt)
        ),
        hv
      )
    case 1n+(+p):
      hv => hw => (
        %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st), Some{st2}, Equal.trans(Maybe<&2, RLines.State>, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st), Lines.Line.step(s, r, c, st), Some{st2}, Moves.Step.kept.at(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s, c, st, RLines.Line.rule(r, c, RLines.State.versions(st)))(Cast.keeps(name, c, RLines.State.slot(X), t, x, RLines.State.slot(st))(lt)), e2)): {Lines.Line.run(1n+p, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, st, _) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s), r, c, X)): RLines.State}
        ih(p)(
          %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.State.slot(X), Nat.add(p, _)) == True{}: Bool}
          %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.State.slot(X), _) == True{}: Bool}
          hv)(
          %Equal.sym(Nat, RLines.State.slot(st2), 1n+RLines.State.slot(st), Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), Nat.add(p, _)) == True{}: Bool}
          %Equal.sym(Nat, Nat.add(p, 1n+RLines.State.slot(st)), 1n+Nat.add(p, RLines.State.slot(st)), Shared.Nat.add_succ(p, RLines.State.slot(st))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(X), t, x}, s)), c), _) == True{}: Bool}
          hw))

# when a run of f slots before the vote ends at a state, and the vote is for
# the next slot of that state, a run of f2 slots after the vote, that may go
# past that slot and past the bound of the line, ends where the continued
# run from that state ends
def Cast.run(
  f: Nat,
  +f2: Nat,
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +st: RLines.State
) -> {Nat.is_lt(RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s)), c), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Lines.Line.run(f2, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s), r, c, st)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s), r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)), Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))), t, x}, s), r, c, Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))): RLines.State}:
  match f:
    case 0n:
      hv => hw => Cast.stop(f2, name, s, c, t, x, r, st)(hw)
    case 1n+(+p):
      Lists.Maybe.by(
        RLines.State,
        m => {Nat.is_lt(RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s)), c), Nat.add(f2, RLines.State.slot(st))) == True{}: Bool} -> {Lines.Line.run(f2, Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s), r, c, st)) == Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s), r, c, Lines.Line.run(1n+p, s, r, c, st, m), Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.run(1n+p, s, r, c, st, m)), t, x}, s), r, c, Lines.Line.run(1n+p, s, r, c, st, m))): RLines.State},
        Lines.Line.step(s, r, c, st),
        en => hv => hw => Cast.stop(f2, name, s, c, t, x, r, st)(hw),
        +st2 => +e2 => hv => hw => Cast.go(
          f2,
          name, s, c, t, x, r,
          st,
          st2,
          Lines.Line.run(p, s, r, c, st2, Lines.Line.step(s, r, c, st2)),
          e2,
          (
            %Moves.Next.slot(st, st2, Moves.Step.next(s, r, c, st, st2)(e2)): {Nat.is_le(_, RLines.State.slot(Lines.Line.run(p, s, r, c, st2, Lines.Line.step(s, r, c, st2)))) == True{}: Bool}
            Moves.Run.slot_le(p, s, r, c, st2)),
          +f3 => h3 => h4 => Cast.run(p, f3, name, s, c, t, x, r, st2)(h3)(h4)
        )(hv)(hw)
      )

# after a vote for the next slot of the state st that a line was read up to
# from its version 0 m, the line reads up to where the run continued from st
# ends
def From.cast(
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +t: Nat,
  +x: Types.Cast,
  +r: Maybe<&2, List<&2, Types.Entry>>,
  m: Maybe<&2, Types.Entry>,
  +st: RLines.State
) -> {
  Lines.Line.from(s, r, c, m) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.from(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, m) == Some{Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st))}: Maybe<&2, RLines.State>
}:
  match m:
    case None{}:
      e => Empty.absurd(
        {None{} == Some{Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(st), t, x}, s), r, c, st))}: Maybe<&2, RLines.State>},
        Shared.Maybe.none_ne_some(RLines.State, st, e)
      )
    case Some{+e0}:
      e => (
        %Shared.Maybe.some_inj(RLines.State, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}), st, e): {Lines.Line.from(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, Some{e0}) == Some{Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, _, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(_), t, x}, s), r, c, _))}: Maybe<&2, RLines.State>}
        Equal.cong(
          RLines.State,
          Maybe<&2, RLines.State>,
          y => Some{y},
          Lines.Line.run(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, RLines.State{[e0], 1n}, Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, RLines.State{[e0], 1n})),
          Lines.Line.run(1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}), Lines.Line.step(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), r, c, Lines.Line.start(s, r, c, RLines.State{[e0], 1n}))),
          Cast.run(RLines.Line.bound(Facts.Facts.list(s), c), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), name, s, c, t, x, r, RLines.State{[e0], 1n})(
            Shared.Nat.lt_le(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Nat.add(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n))(
              Shared.Nat.lt_le(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), 1n+RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c))(Shared.Nat.lt_succ(RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n}))))(
                Moves.Bound.ge(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c, name, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), RRounds.Draft{t, x})(
                  Facts.Facts.has_in(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s), Types.Fact.Vote{name, Types.Step.At{c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t}, x})(Facts.Facts.add_has(s, Types.Fact.Vote{name, Types.Step.At{c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t}, x}))
                )
              )
            )(Shared.Nat.le_add_first(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n))
          )(
            %Equal.sym(Nat, Nat.add(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), 1n), 1n+RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), Crits.Crit.add_one(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c))): {Nat.is_lt(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c), _) == True{}: Bool}
            Shared.Nat.lt_succ(RLines.Line.bound(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, c, RLines.State.slot(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), t, x}, s)), c)))
        ))

# after a vote for the next slot of the state st of a store, the state of
# the store is the run continued from st
def Store.state_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +t: Nat,
  +x: Types.Cast,
  +st: RLines.State
) -> {
  Lines.Store.state(s, h) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s), h) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>
}:
  e => (
    %Equal.sym(Maybe<&2, Types.Entry>, RLines.Store.first(Facts.Facts.list(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s)), h), RLines.Store.first(Facts.Facts.list(s), h), Moves.First.same(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s, h)({==})): {Lines.Line.from(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s), None{}, Ledgers.Line{h, None{}}, _) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
    From.cast(name, s, Ledgers.Line{h, None{}}, t, x, None{}, RLines.Store.first(Facts.Facts.list(s), h), st)(e))

# after a vote for the next slot of the state st of a branch, whose store
# has the versions R, the state of the branch is the run continued from st
def Branch.state_cast(
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +t: Nat,
  +x: Types.Cast,
  +R: List<&2, Types.Entry>,
  +j: Nat,
  +st: RLines.State
) -> {
  Lines.Line.state(s, Ledgers.Line{h, Some{b}}) == Some{st}: Maybe<&2, RLines.State>
} -> {
  Lines.Store.state(s, h) == Some{RLines.State{R, j}}: Maybe<&2, RLines.State>
} -> {
  Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>
}:
  e => +es => (
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), h), Lines.Store.state(s, h), Moves.Store.same(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s, h)({==})(
      %Equal.sym(Bool, Ledgers.Line.is_eq(Ledgers.Line{h, None{}}, Ledgers.Line{h, Some{b}}), False{}, Moves.Line.root_ne(h, b)): {Bool.not(_) == True{}: Bool}
      {==})): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
    %Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{R, j}}, es): {Lines.Branch.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s), Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, _)) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, RLines.State.slot(st), t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
    From.cast(name, s, Ledgers.Line{h, Some{b}}, t, x, Some{R}, RLines.Branch.first(R, Ledgers.Line{h, Some{b}}), st)(
      Equal.trans(
        Maybe<&2, RLines.State>,
        Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Some{R}),
        Lines.Line.state(s, Ledgers.Line{h, Some{b}}),
        Some{st},
        Equal.cong(
          Maybe<&2, RLines.State>,
          Maybe<&2, RLines.State>,
          m => Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, m)),
          Some{RLines.State{R, j}},
          Lines.Store.state(s, h),
          Equal.sym(Maybe<&2, RLines.State>, Lines.Store.state(s, h), Some{RLines.State{R, j}}, es)
        ),
        e
      )
    ))

# the state m, if any, is the state x
def Put.Ok(x: Maybe<&2, RLines.State>, m: Maybe<&2, RLines.State>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{st}:
      {x == Some{st}: Maybe<&2, RLines.State>}

# a right table with a state of a line, if any, that is the state that the
# facts give the line, is right
def Known.put_fits(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> Put.Ok(RLines.Line.state(s, c), m) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> {RKnown.Known.ok(RKnown.Known.put(kn, c, m), s) == True{}: Bool}:
  match m:
    case None{}:
      e => ok => ok
    case Some{+st}:
      e => ok => Shared.Bool.and_both(
        RKnown.State.fits(RLines.Line.state(s, c), st),
        RKnown.Known.ok(kn, s)
      )(State.fits_of(RLines.Line.state(s, c), st)(e))(ok)

# what is known of a state that the table holds: a state that is some state
# is not none, so it is what the facts give
def Known.have(
  -A: Data,
  -m: Maybe<&2, RLines.State>,
  -x: Maybe<&2, RLines.State>,
  -st: RLines.State,
  e: {Some{st} == None{}: Maybe<&2, RLines.State>} | {x == Some{st}: Maybe<&2, RLines.State>}
) -> {x == Some{st}: Maybe<&2, RLines.State>}:
  match e:
    case Inl{n}:
      Empty.absurd({x == Some{st}: Maybe<&2, RLines.State>}, Shared.Maybe.none_ne_some(RLines.State, st, Equal.sym(Maybe<&2, RLines.State>, Some{st}, None{}, n)))
    case Inr{y}:
      y

# the state that a vote for the slot k of the line c continues, from the
# state m of c and the state ms of its store in the facts before the vote,
# is the state of c after the vote
def Known.next_ok(
  +name: String,
  +s: Facts.Facts(),
  c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast,
  m: Maybe<&2, RLines.State>,
  ms: Maybe<&2, RLines.State>
) -> ({m == None{}: Maybe<&2, RLines.State>} | {Lines.Line.state(s, c) == m: Maybe<&2, RLines.State>}) -> ({ms == None{}: Maybe<&2, RLines.State>} | {
  Lines.Line.state(s, RKnown.Known.root(c)) == ms: Maybe<&2, RLines.State>
}) -> Put.Ok(Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s), c), RKnown.Known.next.of(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, c, k, t, x}, s)), c, k, m, RKnown.Known.over(c, ms))):
  match c m ms:
    case Ledgers.Line{h, None{}} None{} None{}:
      e => es => Unit{}
    case Ledgers.Line{h, None{}} None{} Some{y}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} None{} None{}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} None{} Some{RLines.State{R, j}}:
      e => es => Unit{}
    case Ledgers.Line{h, Some{b}} Some{st} None{}:
      e => es => Unit{}
    case Ledgers.Line{+h, None{}} Some{+st} None{}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s), Ledgers.Line{h, None{}}),
          Shared.Maybe.when(RLines.State, y, u => Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})})
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s), Ledgers.Line{h, None{}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
          Store.state_cast(name, s, h, t, x, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Store.state(s, h), st, e))),
        ef => Unit{}
      )
    case Ledgers.Line{+h, None{}} Some{+st} Some{y}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s), Ledgers.Line{h, None{}}),
          Shared.Maybe.when(RLines.State, y, u => Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, k, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})})
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s), Ledgers.Line{h, None{}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, None{}}, _, t, x}, s)), Ledgers.Line{h, None{}}, st, None{})}: Maybe<&2, RLines.State>}
          Store.state_cast(name, s, h, t, x, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Store.state(s, h), st, e))),
        ef => Unit{}
      )
    case Ledgers.Line{+h, Some{+b}} Some{+st} Some{RLines.State{+R, +j}}:
      e => es => Lists.Bool.by(
        y => Put.Ok(
          Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s), Ledgers.Line{h, Some{b}}),
          Shared.Maybe.when(RLines.State, y, u => Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, k, t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})})
        ),
        Nat.is_eq(RLines.State.slot(st), k),
        et => (
          %Shared.Nat.is_eq_sound(RLines.State.slot(st), k)(et): {Lines.Line.state(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, _, t, x}, s), Ledgers.Line{h, Some{b}}) == Some{RKnown.Known.go.at(Facts.Facts.crit(Moves.Delta.to(Moves.Delta.Vote{name, Ledgers.Line{h, Some{b}}, _, t, x}, s)), Ledgers.Line{h, Some{b}}, st, Some{R})}: Maybe<&2, RLines.State>}
          Branch.state_cast(name, s, h, b, t, x, R, j, st)(Known.have(Maybe<&2, RLines.State>, Some{st}, Lines.Line.state(s, Ledgers.Line{h, Some{b}}), st, e))(Known.have(Maybe<&2, RLines.State>, Some{RLines.State{R, j}}, Lines.Store.state(s, h), RLines.State{R, j}, es))),
        ef => Unit{}
      )

# the state that a right table holds for a line, if any, is the state that
# the facts give the line
def Known.found(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line
) -> {
  RKnown.Known.ok(kn, s) == True{}: Bool
} -> ({RKnown.Known.find(kn, c) == None{}: Maybe<&2, RLines.State>} | {
  RLines.Line.state(s, c) == RKnown.Known.find(kn, c): Maybe<&2, RLines.State>
}):
  ok => Lists.Maybe.by(
    RLines.State,
    m => ({m == None{}: Maybe<&2, RLines.State>} | {RLines.Line.state(s, c) == m: Maybe<&2, RLines.State>}),
    RKnown.Known.find(kn, c),
    en => Inl{{==}},
    +y => ey => Inr{Known.find_ok(kn, s, c, y)(ok)(ey)}
  )

# a table that is right for the facts s, after a ballot for the slot k of
# the line c (without the states that the ballot may change, and with the
# state of c continued from its known state), is right for the facts with
# the ballot
def Known.cast_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RKnown.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RKnown.Known.ok(
    RKnown.Known.cast(
      kn,
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k
    ),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}))
  )
    == True{}: Bool
}:
  +ok => Known.put_fits(
    RKnown.Known.voted(kn, c),
    Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
    c,
    RKnown.Known.next.of(
      Facts.Facts.crit(Facts.Facts.add(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})),
      c,
      k,
      RKnown.Known.find(kn, c),
      RKnown.Known.over(c, RKnown.Known.find(kn, RKnown.Known.root(c)))
    )
  )(
    Known.next_ok(
      name,
      s,
      c,
      k,
      t,
      x,
      RKnown.Known.find(kn, c),
      RKnown.Known.find(kn, RKnown.Known.root(c))
    )(Known.found(kn, Facts.Facts.crit(s), c)(ok))(
      Known.found(kn, Facts.Facts.crit(s), RKnown.Known.root(c))(ok)
    )
  )(Known.voted_ok(kn, name, s, c, k, t, x)(ok))
