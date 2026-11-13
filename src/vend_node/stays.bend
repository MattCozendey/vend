import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# What stays as the facts grow
# ----------------------------
# The versions that a set of facts decides stay when the set grows, while the
# larger set names no liar and is sound for its node: two picks cannot both
# have more than half of the votes of a slot unless a voter cast two votes.
# Premises, each an equation: w says that s2 is wider than s, h that s2 names
# no liar, o that s2 is sound for the node name.

# Votes
# -----

# the picks for a step of some facts are among the picks of one more fact and them
def Votes.picks_cons(g: Types.Fact, +r: List<&2, Types.Fact>, +st: Types.Step, +pk: Types.Pick) -> {
  List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(r, st), pk) == True{}: Bool
} -> {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(g <> r, st), pk) == True{}: Bool}:
  match g:
    case Types.Fact.Ask{a}:
      h => h
    case Types.Fact.Vote{w, +st2, +q}:
      +h => Lists.Bool.by(
        k => {
          List.contains(~Types.Pick, ~Coded.Pick.is_eq, List.filter.put(Types.Pick, q, Lines.Votes.picks(r, st), k), pk) == True{}: Bool
        },
        Coded.Step.is_eq(st2, st),
        et => Shared.List.contains_cons(~Types.Pick, ~Coded.Pick.is_eq, q, Lines.Votes.picks(r, st), pk)(h),
        ef => h
      )

# the pick of a vote among fs for the step st is among the picks of fs for st
def Votes.picks_in(fs: List<&2, Types.Fact>, +st: Types.Step, +v: String, +pk: Types.Pick) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Vote{v, st, pk}) == True{}: Bool
} -> {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(fs, st), pk) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => h
    case Con{+g, +r}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(g <> r, st), pk) == True{}: Bool},
        g,
        r,
        Types.Fact.Vote{v, st, pk},
        hin,
        eg => (
          %Equal.sym(Types.Fact, g, Types.Fact.Vote{v, st, pk}, eg): {
            List.contains(~Types.Pick, ~Coded.Pick.is_eq, Lines.Votes.picks(_ <> r, st), pk) == True{}: Bool
          }
          %Equal.sym(Bool, Coded.Step.is_eq(st, st), True{}, Coded.Step.is_eq_refl(st)): {
            List.contains(~Types.Pick, ~Coded.Pick.is_eq, List.filter.put(Types.Pick, pk, Lines.Votes.picks(r, st), _), pk) == True{}: Bool
          }
          Lists.List.contains_head(~Types.Pick, ~Coded.Pick.is_eq, ~Coded.Pick.laws(), pk, Lines.Votes.picks(r, st))
        ),
        c => Votes.picks_cons(g, r, st, pk)(Votes.picks_in(r, st, v, pk)(c))
      )

# Votes.most_one, with the voter that voted for both picks
def Votes.most_one.of(
  +s: Facts.Facts(),
  +st: Types.Step,
  +ds: List<&2, String>,
  +p: Types.Pick,
  +q: Types.Pick,
  hn: {Facts.Facts.liars(s) == []: List<&2, String>},
  r: Exists(
    String,
    x => {List.contains(~String, ~String.eq, ds, x) == True{}: Bool}
      & ({Lines.Voting.voted(Lines.Voting{s, st, p})(x) == True{}: Bool}
        & {Lines.Voting.voted(Lines.Voting{s, st, q})(x) == True{}: Bool})
  )
) -> {p == q: Types.Pick}:
  (+x, w) = r
  (c, w2) = w
  (a, b) = w2
  Facts.Facts.honest_one(s, x, st, p, q)(hn)(a)(b)

# in a set that names no liar, two picks that more than half of the nodes ds
# voted for, for one step, are one pick
def Votes.most_one(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +p: Types.Pick, +q: Types.Pick) -> {
  Facts.Facts.liars(s) == []: List<&2, String>
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, p}) == True{}: Bool} -> {
  Lines.Voting.most(ds, Lines.Voting{s, st, q}) == True{}: Bool
} -> {p == q: Types.Pick}:
  hn => mp => mq => Votes.most_one.of(
    s,
    st,
    ds,
    p,
    q,
    hn,
    Lists.List.most_meet(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ~Lines.Voting.voted,
      ~String.eq,
      ~Texts.String.laws(),
      ds,
      Lines.Voting{s, st, p},
      Lines.Voting{s, st, q}
    )(mp)(mq)
  )

# the poll g2 is the poll g1 in a wider set
def Voting.Grown(g1: Lines.Voting, g2: Lines.Voting) -> Data:
  match g1 g2:
    case Lines.Voting{s, st, pk} Lines.Voting{s2, st2, pk2}:
      Sigma<&2, &2, {Facts.Facts.wider(s, s2) == True{}: Bool}, _ => Sigma<&2, &2, {st == st2: Types.Step}, _ => {pk == pk2: Types.Pick}>>

# Voting.grown, with the two polls in parts
def Voting.grown.of(
  +s: Facts.Facts(),
  +st: Types.Step,
  +pk: Types.Pick,
  +s2: Facts.Facts(),
  -st2: Types.Step,
  -pk2: Types.Pick,
  +x: String,
  h: Sigma<&2, &2, {Facts.Facts.wider(s, s2) == True{}: Bool}, _ => Sigma<&2, &2, {st == st2: Types.Step}, _ => {pk == pk2: Types.Pick}>>,
  hv: {Facts.Facts.has(s, Types.Fact.Vote{x, st, pk}) == True{}: Bool}
) -> {Facts.Facts.has(s2, Types.Fact.Vote{x, st2, pk2}) == True{}: Bool}:
  (w, es) = h
  (e1, e2) = es
  %e1: {Facts.Facts.has(s2, Types.Fact.Vote{x, _, pk2}) == True{}: Bool}
  %e2: {Facts.Facts.has(s2, Types.Fact.Vote{x, st, _}) == True{}: Bool}
  Facts.Facts.wider_has(s, s2, Types.Fact.Vote{x, st, pk})(w)(hv)

# a vote that a poll counts, the poll in a wider set counts
def Voting.grown(g1: Lines.Voting, g2: Lines.Voting) -> Voting.Grown(g1, g2) -> @x: String -> {
  Lines.Voting.voted(g1)(x) == True{}: Bool
} -> {Lines.Voting.voted(g2)(x) == True{}: Bool}:
  match g1 g2:
    case Lines.Voting{+s, +st, +pk} Lines.Voting{+s2, +st2, +pk2}:
      h => +x => hv => Voting.grown.of(s, st, pk, s2, st2, pk2, x, h, hv)

# more than half of the nodes voted for a pick in a wider set, when they did in the set
def Voting.most_stays(+s: Facts.Facts(), +s2: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, pk}) == True{}: Bool} -> {
  Lines.Voting.most(ds, Lines.Voting{s2, st, pk}) == True{}: Bool
}:
  w => m => Lists.Nat.most_mono(
    List.length(&2, String, ds),
    Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s, st, pk}),
    Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s2, st, pk})
  )(
    Lists.List.count_mono(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ~Lines.Voting.voted,
      ~Voting.Grown,
      ~Voting.grown,
      ds,
      Lines.Voting{s, st, pk},
      Lines.Voting{s2, st, pk},
      (w, ({==}, {==}))
    )
  )(m)

# a pick that more than half of the nodes voted for, in a set that names no
# liar, is not stood against by any pick
def Rival.beats_all(+s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pks: List<&2, Types.Pick>, +pk: Types.Pick, +q: Types.Pick) -> {
  Facts.Facts.liars(s) == []: List<&2, String>
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, pk}) == True{}: Bool} -> {
  Lines.Rival.beats(Lines.Rival{Lines.Tally{s, st, ds, pks}, pk}, q) == True{}: Bool
}:
  hn => m => Lists.Bool.by(
    b => {Bool.or(Coded.Pick.is_eq(q, pk), Bool.not(b)) == True{}: Bool},
    Lines.Voting.most(ds, Lines.Voting{s, st, q}),
    et => Facts.Case.or_left(Coded.Pick.is_eq(q, pk), Bool.not(True{}))(
      (
        %Votes.most_one(s, st, ds, q, pk)(hn)(et)(m): {Coded.Pick.is_eq(q, _) == True{}: Bool}
        Coded.Pick.is_eq_refl(q)
      )
    ),
    ef => Facts.Case.or_right(Coded.Pick.is_eq(q, pk), Bool.not(False{}))({==})
  )

# no pick of qs stands against a pick that more than half of the nodes voted
# for, in a set that names no liar
def Rival.holds_all(qs: List<&2, Types.Pick>, +s: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pks: List<&2, Types.Pick>, +pk: Types.Pick) -> {
  Facts.Facts.liars(s) == []: List<&2, String>
} -> {Lines.Voting.most(ds, Lines.Voting{s, st, pk}) == True{}: Bool} -> {
  Shared.List.holds(~Types.Pick, ~Lines.Rival, ~Lines.Rival.beats, qs, Lines.Rival{Lines.Tally{s, st, ds, pks}, pk}) == True{}: Bool
}:
  match qs:
    case Nil{}:
      hn => m => {==}
    case Con{+q, +r}:
      +hn => +m => (
        %Equal.sym(
          Bool,
          Lines.Rival.beats(Lines.Rival{Lines.Tally{s, st, ds, pks}, pk}, q),
          True{},
          Rival.beats_all(s, st, ds, pks, pk, q)(hn)(m)
        ): {
          List.all.if(
            u => Shared.List.holds(~Types.Pick, ~Lines.Rival, ~Lines.Rival.beats, r, Lines.Rival{Lines.Tally{s, st, ds, pks}, pk}),
            _
          ) == True{}: Bool
        }
        Rival.holds_all(r, s, st, ds, pks, pk)(hn)(m)
      )

# Votes.decided_stays.at, with a node that voted for the pick
def Votes.decided_stays.of(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +st: Types.Step,
  +ds: List<&2, String>,
  +pk: Types.Pick,
  w: {Facts.Facts.wider(s, s2) == True{}: Bool},
  +h: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +m2: {Lines.Voting.most(ds, Lines.Voting{s2, st, pk}) == True{}: Bool},
  r: Exists(
    String,
    x => {List.contains(~String, ~String.eq, ds, x) == True{}: Bool}
      & {Lines.Voting.voted(Lines.Voting{s, st, pk})(x) == True{}: Bool}
  )
) -> {Lines.Votes.decided(s2, st, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  (+x, w1) = r
  (c, hv) = w1
  Lists.List.pick_one(
    ~Types.Pick,
    ~Lines.Tally,
    ~Lines.Tally.wins,
    ~Coded.Pick.is_eq,
    ~Coded.Pick.laws(),
    Lines.Votes.picks(Facts.Facts.list(s2), st),
    Lines.Tally{s2, st, ds, Lines.Votes.picks(Facts.Facts.list(s2), st)},
    pk
  )(
    Votes.picks_in(Facts.Facts.list(s2), st, x, pk)(
      Facts.Facts.has_in(s2, Types.Fact.Vote{x, st, pk})(
        Facts.Facts.wider_has(s, s2, Types.Fact.Vote{x, st, pk})(w)(hv)
      )
    )
  )(
    Shared.Bool.and_both(
      Lines.Voting.most(ds, Lines.Voting{s2, st, pk}),
      Shared.List.holds(
        ~Types.Pick,
        ~Lines.Rival,
        ~Lines.Rival.beats,
        Lines.Votes.picks(Facts.Facts.list(s2), st),
        Lines.Rival{Lines.Tally{s2, st, ds, Lines.Votes.picks(Facts.Facts.list(s2), st)}, pk}
      )
    )(m2)(
      Rival.holds_all(
        Lines.Votes.picks(Facts.Facts.list(s2), st),
        s2,
        st,
        ds,
        Lines.Votes.picks(Facts.Facts.list(s2), st),
        pk
      )(h)(m2)
    )
  )(
    +y => hy => ty => Votes.most_one(s2, st, ds, y, pk)(h)(
      Shared.Bool.and_true_left(
        Lines.Voting.most(ds, Lines.Voting{s2, st, y}),
        Shared.List.holds(
          ~Types.Pick,
          ~Lines.Rival,
          ~Lines.Rival.beats,
          Lines.Votes.picks(Facts.Facts.list(s2), st),
          Lines.Rival{Lines.Tally{s2, st, ds, Lines.Votes.picks(Facts.Facts.list(s2), st)}, y}
        )
      )(ty)
    )(m2)
  )

# Votes.decided_stays, once more than half of the nodes voted for the pick in s
def Votes.decided_stays.at(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +st: Types.Step,
  +ds: List<&2, String>,
  +pk: Types.Pick,
  +w: {Facts.Facts.wider(s, s2) == True{}: Bool},
  h: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +m: {Lines.Voting.most(ds, Lines.Voting{s, st, pk}) == True{}: Bool}
) -> {Lines.Votes.decided(s2, st, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  Votes.decided_stays.of(
    s,
    s2,
    st,
    ds,
    pk,
    w,
    h,
    Voting.most_stays(s, s2, st, ds, pk)(w)(m),
    Lists.List.count_pos(
      ~String,
      ~Lines.Voting,
      ~Lines.Voting.voted,
      ~String.eq,
      ~Texts.String.laws(),
      ds,
      Lines.Voting{s, st, pk}
    )(
      Lists.Nat.most_pos(
        List.length(&2, String, ds),
        Lists.List.count(~String, ~Lines.Voting, ~Lines.Voting.voted, ds, Lines.Voting{s, st, pk})
      )(m)
    )
  )

# a decided pick stays decided
def Votes.decided_stays(+s: Facts.Facts(), +s2: Facts.Facts(), +st: Types.Step, +ds: List<&2, String>, +pk: Types.Pick) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {
  Lines.Votes.decided(s, st, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Lines.Votes.decided(s2, st, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  +w => +h => e => Votes.decided_stays.at(
    s,
    s2,
    st,
    ds,
    pk,
    w,
    h,
    Shared.Bool.and_true_left(
      Lines.Voting.most(ds, Lines.Voting{s, st, pk}),
      Shared.List.holds(
        ~Types.Pick,
        ~Lines.Rival,
        ~Lines.Rival.beats,
        Lines.Votes.picks(Facts.Facts.list(s), st),
        Lines.Rival{Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)}, pk}
      )
    )(
      Lists.List.pick_hit(
        ~Types.Pick,
        ~Lines.Tally,
        ~Lines.Tally.wins,
        Lines.Votes.picks(Facts.Facts.list(s), st),
        Lines.Tally{s, st, ds, Lines.Votes.picks(Facts.Facts.list(s), st)},
        pk
      )(e)
    )
  )

# Rules
# -----

# a number below another has its next number at most the other
def Nat.lt_up(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(1n+a, b) == True{}: Bool}:
  match a b:
    case 0n 0n:
      h => Empty.absurd({Nat.is_le(1n, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 0n 1n+q:
      h => Shared.Nat.le_zero(q)
    case 1n+p 0n:
      h => Empty.absurd({Nat.is_le(2n+p, 0n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case 1n+p 1n+q:
      Nat.lt_up(p, q)

# the versions m of a store with the versions zs after them; nothing for none
def Store.grow(m: Maybe<&2, List<&2, Types.Entry>>, zs: List<&2, Types.Entry>) -> Maybe<&2, List<&2, Types.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{List.append(&2, Types.Entry, r, zs)}

# a store that has versions keeps the owners that it started with as it grows
def Store.owners_append(R: List<&2, Types.Entry>, -zs: List<&2, Types.Entry>, +m: Nat) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, R)) == True{}: Bool
} -> {Lines.Store.owners(R) == Lines.Store.owners(List.append(&2, Types.Entry, R, zs)): List<&2, String>}:
  match R:
    case Nil{}:
      h => Lists.Bool.clash(
        {Lines.Store.owners([]) == Lines.Store.owners(List.append(&2, Types.Entry, [], zs)): List<&2, String>},
        Nat.is_lt(m, 0n),
        Shared.Nat.le_nlt(0n, m)(Shared.Nat.le_zero(m)),
        h
      )
    case Con{e, r}:
      h => {==}

# the rule of an owner group at an era is the same with more versions after
# the era, when the store starts with the same owners
def Rule.of_append(+R: List<&2, Types.Entry>, +A: List<&2, Types.Entry>, +c: Ledgers.Line, +m: Nat, g: Maybe<&2, String>) -> {
  List.take(&2, Types.Entry, R, 1n+m) == List.take(&2, Types.Entry, A, 1n+m): List<&2, Types.Entry>
} -> {Lines.Store.owners(R) == Lines.Store.owners(A): List<&2, String>} -> {
  Lines.Rule.of(R, c, m, g) == Lines.Rule.of(A, c, m, g): Maybe<&2, Lines.Rule>
}:
  match g:
    case Some{+name}:
      et => eo => (
        %Groups.Groups.nodes_take(R, A, Lines.Line.root(c), name, m, et): {
          Maybe.map(&2, List<&2, String>, Lines.Rule, ns => Lines.Rule{Some{name}, ns}, Groups.Groups.nodes(R, Lines.Line.root(c), name, m)) == Maybe.map(&2, List<&2, String>, Lines.Rule, ns => Lines.Rule{Some{name}, ns}, _): Maybe<&2, Lines.Rule>
        }
        {==}
      )
    case None{}:
      et => eo => (
        %eo: {
          Shared.Maybe.when(Lines.Rule, Lines.Line.is_root(c), u => Some{Lines.Rule{None{}, Lines.Store.owners(R)}}) == Shared.Maybe.when(Lines.Rule, Lines.Line.is_root(c), u => Some{Lines.Rule{None{}, _}}): Maybe<&2, Lines.Rule>
        }
        {==}
      )

# Rule.at_append, with what the first versions and the owners are
def Rule.at_append.of(
  +R: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -u: Lines.Rule,
  el: {Nat.is_lt(m, List.length(&2, Types.Entry, List.append(&2, Types.Entry, R, zs))) == True{}: Bool},
  +et: {List.take(&2, Types.Entry, R, 1n+m) == List.take(&2, Types.Entry, List.append(&2, Types.Entry, R, zs), 1n+m): List<&2, Types.Entry>},
  eo: {Lines.Store.owners(R) == Lines.Store.owners(List.append(&2, Types.Entry, R, zs)): List<&2, String>},
  e: {Lines.Rule.of(R, c, m, Groups.Groups.owner(R, c, m)) == Some{u}: Maybe<&2, Lines.Rule>}
) -> {Lines.Rule.at(List.append(&2, Types.Entry, R, zs), c, m) == Some{u}: Maybe<&2, Lines.Rule>}:
  %Equal.sym(Bool, Nat.is_lt(m, List.length(&2, Types.Entry, List.append(&2, Types.Entry, R, zs))), True{}, el): {
    Shared.Maybe.when(
      Lines.Rule,
      _,
      x => Lines.Rule.of(List.append(&2, Types.Entry, R, zs), c, m, Groups.Groups.owner(List.append(&2, Types.Entry, R, zs), c, m))
    ) == Some{u}: Maybe<&2, Lines.Rule>
  }
  %Groups.Groups.owner_take(R, List.append(&2, Types.Entry, R, zs), c, m, et): {
    Lines.Rule.of(List.append(&2, Types.Entry, R, zs), c, m, _) == Some{u}: Maybe<&2, Lines.Rule>
  }
  %Rule.of_append(R, List.append(&2, Types.Entry, R, zs), c, m, Groups.Groups.owner(R, c, m))(et)(eo): {
    _ == Some{u}: Maybe<&2, Lines.Rule>
  }
  e

# the rule that an era decides stays as the store grows
def Rule.at_append(+R: List<&2, Types.Entry>, +zs: List<&2, Types.Entry>, +c: Ledgers.Line, +m: Nat, -u: Lines.Rule) -> {
  Lines.Rule.at(R, c, m) == Some{u}: Maybe<&2, Lines.Rule>
} -> {Lines.Rule.at(List.append(&2, Types.Entry, R, zs), c, m) == Some{u}: Maybe<&2, Lines.Rule>}:
  Lists.Bool.by(
    b => {
      Shared.Maybe.when(Lines.Rule, b, x => Lines.Rule.of(R, c, m, Groups.Groups.owner(R, c, m))) == Some{u}: Maybe<&2, Lines.Rule>
    } -> {Lines.Rule.at(List.append(&2, Types.Entry, R, zs), c, m) == Some{u}: Maybe<&2, Lines.Rule>},
    Nat.is_lt(m, List.length(&2, Types.Entry, R)),
    +el => e => Rule.at_append.of(
      R,
      zs,
      c,
      m,
      u,
      Shared.Nat.lt_le(
        m,
        List.length(&2, Types.Entry, R),
        List.length(&2, Types.Entry, List.append(&2, Types.Entry, R, zs))
      )(el)(Lists.List.length_append_le(Types.Entry, R, zs)),
      Equal.sym(
        List<&2, Types.Entry>,
        List.take(&2, Types.Entry, List.append(&2, Types.Entry, R, zs), 1n+m),
        List.take(&2, Types.Entry, R, 1n+m),
        Lists.List.take_append(Types.Entry, R, zs, 1n+m)(Nat.lt_up(m, List.length(&2, Types.Entry, R))(el))
      ),
      Store.owners_append(R, zs, m)(el),
      e
    ),
    ef => e => Empty.absurd(
      {Lines.Rule.at(List.append(&2, Types.Entry, R, zs), c, m) == Some{u}: Maybe<&2, Lines.Rule>},
      Shared.Maybe.none_ne_some(Lines.Rule, u, e)
    )
  )

# the rule of the next version stays as the store of the line grows
def Rule.grows(m: Maybe<&2, List<&2, Types.Entry>>, +zs: List<&2, Types.Entry>, +c: Ledgers.Line, +vs: List<&2, Types.Entry>, -u: Lines.Rule) -> {
  Lines.Line.rule(m, c, vs) == Some{u}: Maybe<&2, Lines.Rule>
} -> {Lines.Line.rule(Store.grow(m, zs), c, vs) == Some{u}: Maybe<&2, Lines.Rule>}:
  match m:
    case None{}:
      e => e
    case Some{+R}:
      e => Rule.at_append(R, zs, c, Lines.Line.era(c, vs), u)(e)

# the versions of a line stay: the larger set decides them, and maybe more
# after them
def Line.versions_stay(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  ?TODO

# a version of a line stays
def Line.at_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +k: Nat, +e: Types.Entry) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  ?TODO

# the rule of the version after some versions stays
def Rule.after_stays(+name: String, +s: Facts.Facts(), +s2: Facts.Facts(), +c: Ledgers.Line, +vs: List<&2, Types.Entry>, +u: Lines.Rule) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {Facts.Facts.liars(s2) == []: List<&2, String>} -> {Facts.Facts.ok(name, s2) == True{}: Bool} -> {
  Lines.Rule.after(s, c, vs) == Some{u}: Maybe<&2, Lines.Rule>
} -> {Lines.Rule.after(s2, c, vs) == Some{u}: Maybe<&2, Lines.Rule>}:
  ?TODO
