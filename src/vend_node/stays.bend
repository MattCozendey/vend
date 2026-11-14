import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./groups.bend as Groups
import ./lines.bend as Lines
import ./rounds.bend as Rounds
import ./run/facts.bend as RFacts
import ./run/lines.bend as RLines
import ./shared/lists.bend as Lists
import ./types.bend as Types
import ./versions.bend as Versions

# What stays as the facts grow
# ----------------------------
# The versions that a set of facts decides stay when the set grows, while the
# larger set names no liar and is sound for its node: two picks cannot both
# have more than half of the votes of a slot unless a voter cast two votes.
# Premises, each an equation: w says that s2 is wider than s, h that s2 names
# no liar, o that s2 is sound for the node name.

# Votes
# -----

# a decided pick stays decided: every later sound vote is for it (the laws
# of the rounds, rounds.bend)
def Votes.decided_stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>,
  +pk: Types.Pick
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Lines.Votes.decided(s, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>
} -> {Lines.Votes.decided(s2, c, k, ds) == Some{pk}: Maybe<&2, Types.Pick>}:
  w => h => e => Rounds.Votes.decided_stays(s, s2, c, k, ds, pk)(w)(h)(e)

# Rules
# -----

# a number below another has its next number at most the other
def Nat.lt_up(
  a: Nat,
  b: Nat
) -> {Nat.is_lt(a, b) == True{}: Bool} -> {Nat.is_le(1n+a, b) == True{}: Bool}:
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
def Store.grow(
  m: Maybe<&2, List<&2, Types.Entry>>,
  zs: List<&2, Types.Entry>
) -> Maybe<&2, List<&2, Types.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{r}:
      Some{List.append(&2, Types.Entry, r, zs)}

# a store that has versions keeps the owners that it started with as it grows
def Store.owners_append(
  store: List<&2, Types.Entry>,
  -zs: List<&2, Types.Entry>,
  +m: Nat
) -> {
  Nat.is_lt(m, List.length(&2, Types.Entry, store)) == True{}: Bool
} -> {
  RLines.Store.owners(
    store
  )
    == RLines.Store.owners(List.append(&2, Types.Entry, store, zs)): List<&2, String>
}:
  match store:
    case Nil{}:
      h => Lists.Bool.clash(
        {
          RLines.Store.owners(
            []
          )
            == RLines.Store.owners(List.append(&2, Types.Entry, [], zs)): List<&2, String>
        },
        Nat.is_lt(m, 0n),
        Shared.Nat.le_nlt(0n, m)(Shared.Nat.le_zero(m)),
        h
      )
    case Con{e, r}:
      h => {==}

# the rule of an owner group at an era is the same with more versions after
# the era, when the store starts with the same owners
def Rule.of_append(
  +r: List<&2, Types.Entry>,
  +a: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  g: Maybe<&2, String>
) -> {
  List.take(&2, Types.Entry, r, 1n+m) == List.take(&2, Types.Entry, a, 1n+m): List<&2, Types.Entry>
} -> {
  RLines.Store.owners(r) == RLines.Store.owners(a): List<&2, String>
} -> {RLines.Rule.of(r, c, m, g) == RLines.Rule.of(a, c, m, g): Maybe<&2, RLines.Rule>}:
  match g:
    case Some{+name}:
      et => eo => (
        %Groups.Groups.nodes_take(r, a, RLines.Line.root(c), name, m, et): {Maybe.map(&2, List<&2, String>, RLines.Rule, ns => RLines.Rule{Some{name}, ns}, Groups.Groups.nodes(r, RLines.Line.root(c), name, m)) == Maybe.map(&2, List<&2, String>, RLines.Rule, ns => RLines.Rule{Some{name}, ns}, _): Maybe<&2, RLines.Rule>}
        {==})
    case None{}:
      et => eo => (
        %eo: {Shared.Maybe.when(RLines.Rule, RLines.Line.is_root(c), u => Some{RLines.Rule{None{}, RLines.Store.owners(r)}}) == Shared.Maybe.when(RLines.Rule, RLines.Line.is_root(c), u => Some{RLines.Rule{None{}, _}}): Maybe<&2, RLines.Rule>}
        {==})

# Rule.at_append, with what the first versions and the owners are
def Rule.at_append.of(
  +r: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -u: RLines.Rule,
  el: {
    Nat.is_lt(m, List.length(&2, Types.Entry, List.append(&2, Types.Entry, r, zs))) == True{}: Bool
  },
  +et: {
    List.take(
      &2,
      Types.Entry,
      r,
      1n+m
    )
      == List.take(
        &2,
        Types.Entry,
        List.append(&2, Types.Entry, r, zs),
        1n+m
      ): List<&2, Types.Entry>
  },
  eo: {
    RLines.Store.owners(
      r
    )
      == RLines.Store.owners(List.append(&2, Types.Entry, r, zs)): List<&2, String>
  },
  e: {RLines.Rule.of(r, c, m, Groups.Groups.owner(r, c, m)) == Some{u}: Maybe<&2, RLines.Rule>}
) -> {RLines.Rule.at(List.append(&2, Types.Entry, r, zs), c, m) == Some{u}: Maybe<&2, RLines.Rule>}:
  %Equal.sym(
    Bool,
    Nat.is_lt(m, List.length(&2, Types.Entry, List.append(&2, Types.Entry, r, zs))),
    True{},
    el
  ): {
    Shared.Maybe.when(
      RLines.Rule,
      _,
      x => RLines.Rule.of(
        List.append(&2, Types.Entry, r, zs),
        c,
        m,
        Groups.Groups.owner(List.append(&2, Types.Entry, r, zs), c, m)
      )
    )
      == Some{u}: Maybe<&2, RLines.Rule>
  }
  %Groups.Groups.owner_take(
    r,
    List.append(&2, Types.Entry, r, zs),
    c,
    m,
    et
  ): {
    RLines.Rule.of(List.append(&2, Types.Entry, r, zs), c, m, _) == Some{u}: Maybe<&2, RLines.Rule>
  }
  %Rule.of_append(
    r,
    List.append(&2, Types.Entry, r, zs),
    c,
    m,
    Groups.Groups.owner(r, c, m)
  )(et)(eo): {_ == Some{u}: Maybe<&2, RLines.Rule>}
  e

# the rule that an era decides stays as the store grows
def Rule.at_append(
  +r: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +m: Nat,
  -u: RLines.Rule
) -> {
  RLines.Rule.at(r, c, m) == Some{u}: Maybe<&2, RLines.Rule>
} -> {RLines.Rule.at(List.append(&2, Types.Entry, r, zs), c, m) == Some{u}: Maybe<&2, RLines.Rule>}:
  Lists.Bool.by(
    b => {
      Shared.Maybe.when(
        RLines.Rule,
        b,
        x => RLines.Rule.of(r, c, m, Groups.Groups.owner(r, c, m))
      )
        == Some{u}: Maybe<&2, RLines.Rule>
    } -> {
      RLines.Rule.at(List.append(&2, Types.Entry, r, zs), c, m) == Some{u}: Maybe<&2, RLines.Rule>
    },
    Nat.is_lt(m, List.length(&2, Types.Entry, r)),
    +el => e => Rule.at_append.of(
      r,
      zs,
      c,
      m,
      u,
      Shared.Nat.lt_le(
        m,
        List.length(&2, Types.Entry, r),
        List.length(&2, Types.Entry, List.append(&2, Types.Entry, r, zs))
      )(el)(Lists.List.length_append_le(Types.Entry, r, zs)),
      Equal.sym(
        List<&2, Types.Entry>,
        List.take(&2, Types.Entry, List.append(&2, Types.Entry, r, zs), 1n+m),
        List.take(&2, Types.Entry, r, 1n+m),
        Lists.List.take_append(
          Types.Entry,
          r,
          zs,
          1n+m
        )(Nat.lt_up(m, List.length(&2, Types.Entry, r))(el))
      ),
      Store.owners_append(r, zs, m)(el),
      e
    ),
    ef => e => Empty.absurd(
      {
        RLines.Rule.at(List.append(&2, Types.Entry, r, zs), c, m) == Some{u}: Maybe<&2, RLines.Rule>
      },
      Shared.Maybe.none_ne_some(RLines.Rule, u, e)
    )
  )

# the rule of the next version stays as the store of the line grows
def Rule.grows(
  m: Maybe<&2, List<&2, Types.Entry>>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  -u: RLines.Rule
) -> {
  RLines.Line.rule(m, c, vs) == Some{u}: Maybe<&2, RLines.Rule>
} -> {RLines.Line.rule(Store.grow(m, zs), c, vs) == Some{u}: Maybe<&2, RLines.Rule>}:
  match m:
    case None{}:
      e => e
    case Some{+R}:
      e => Rule.at_append(R, zs, c, RLines.Line.era(c, vs), u)(e)

# The run
# -------

# a decided slot stays decided in a wider set that names no liar, as the store
# of the line grows
def Step.stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  st: RLines.State,
  -st1: RLines.State
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Lines.Line.step(s, r, c, st) == Some{st1}: Maybe<&2, RLines.State>
} -> {Lines.Line.step(s2, Store.grow(r, zs), c, st) == Some{st1}: Maybe<&2, RLines.State>}:
  match st:
    case RLines.State{+vs, +k}:
      w => h => e => Versions.Step.at_by(
        {
          Lines.Line.step(
            s2,
            Store.grow(r, zs),
            c,
            RLines.State{vs, k}
          )
            == Some{st1}: Maybe<&2, RLines.State>
        },
        s,
        c,
        RLines.State{vs, k},
        st1,
        RLines.Line.rule(r, c, vs),
        Versions.Step.at_inv(s, c, RLines.State{vs, k}, st1, RLines.Line.rule(r, c, vs))(e),
        +u => +pk => eu => ed => eb => (
          %Equal.sym(Maybe<&2, RLines.Rule>, RLines.Line.rule(Store.grow(r, zs), c, vs), Some{u}, Rule.grows(r, zs, c, vs, u)(eu)): {Lines.Line.step.at(s2, c, RLines.State{vs, k}, _) == Some{st1}: Maybe<&2, RLines.State>}
          %Equal.sym(Maybe<&2, Types.Pick>, Lines.Votes.decided(s2, c, k, RLines.Rule.nodes(u)), Some{pk}, Votes.decided_stays(s, s2, c, k, RLines.Rule.nodes(u), pk)(w)(h)(ed)): {RLines.Line.step.of(RLines.State{vs, k}, _) == Some{st1}: Maybe<&2, RLines.State>}
          %eb: {Some{RLines.State.put(vs, k, pk)} == Some{_}: Maybe<&2, RLines.State>}
          {==})
      )

# the versions after a run of any length extend the versions before it
def Run.grows(
  f: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> Lists.List.Ext(
  Types.Entry,
  RLines.State.versions(st),
  RLines.State.versions(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st)))
):
  Versions.Run.keeps(
    ~List<&2, Types.Entry>,
    ~Versions.Run.Ext,
    ~Versions.Run.ext_step,
    f,
    RLines.State.versions(st),
    s,
    r,
    c,
    st,
    Lists.List.ext_refl(Types.Entry, RLines.State.versions(st))
  )

# the versions after a run in a wider set that names no liar, with a store
# that grew and at least as many slots, extend the versions after the run
def Run.stays(
  f: Nat,
  f2: Nat,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Nat.is_le(f, f2) == True{}: Bool
} -> Lists.List.Ext(
  Types.Entry,
  RLines.State.versions(Lines.Line.run(f, s, r, c, st, Lines.Line.step(s, r, c, st))),
  RLines.State.versions(
    Lines.Line.run(f2, s2, Store.grow(r, zs), c, st, Lines.Line.step(s2, Store.grow(r, zs), c, st))
  )
):
  match f f2:
    case 0n g:
      w => h => l => Run.grows(g, s2, Store.grow(r, zs), c, st)
    case 1n+p 0n:
      w => h => l => Empty.absurd(
        Lists.List.Ext(
          Types.Entry,
          RLines.State.versions(Lines.Line.run(1n+p, s, r, c, st, Lines.Line.step(s, r, c, st))),
          RLines.State.versions(st)
        ),
        Shared.Bool.false_ne_true(l)
      )
    case 1n+(+p) 1n+(+p2):
      +w => +h => l => Lists.Maybe.by(
        RLines.State,
        m => Lists.List.Ext(
          Types.Entry,
          RLines.State.versions(Lines.Line.run(1n+p, s, r, c, st, m)),
          RLines.State.versions(
            Lines.Line.run(
              1n+p2,
              s2,
              Store.grow(r, zs),
              c,
              st,
              Lines.Line.step(s2, Store.grow(r, zs), c, st)
            )
          )
        ),
        Lines.Line.step(s, r, c, st),
        en => Run.grows(1n+p2, s2, Store.grow(r, zs), c, st),
        +st1 => e1 => (
          %Equal.sym(Maybe<&2, RLines.State>, Lines.Line.step(s2, Store.grow(r, zs), c, st), Some{st1}, Step.stays(s, s2, r, zs, c, st, st1)(w)(h)(e1)): Lists.List.Ext(Types.Entry, RLines.State.versions(Lines.Line.run(p, s, r, c, st1, Lines.Line.step(s, r, c, st1))), RLines.State.versions(Lines.Line.run(1n+p2, s2, Store.grow(r, zs), c, st, _)))
          Run.stays(p, p2, s, s2, r, zs, c, st1)(w)(h)(l))
      )

# The slots that are read
# -----------------------

# the greater of two numbers that are at most n is at most n
def Nat.max_le(
  a: Nat,
  b: Nat,
  n: Nat
) -> {
  Nat.is_le(a, n) == True{}: Bool
} -> {Nat.is_le(b, n) == True{}: Bool} -> {Nat.is_le(Nat.max(a, b), n) == True{}: Bool}:
  match a b n:
    case 0n y z:
      ha => hb => hb
    case 1n+x 0n z:
      ha => hb => ha
    case 1n+x 1n+y 0n:
      ha => hb => ha
    case 1n+x 1n+y 1n+z:
      Nat.max_le(x, y, z)

# a hit and a rest that are both true: the hit is
def All.head(
  hit: Bool,
  -rest: Unit -> Bool
) -> {List.all.if(rest, hit) == True{}: Bool} -> {hit == True{}: Bool}:
  match hit:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a hit and a rest that are both true: the rest is
def All.tail(
  hit: Bool,
  -rest: Unit -> Bool
) -> {List.all.if(rest, hit) == True{}: Bool} -> {rest(Unit{}) == True{}: Bool}:
  match hit:
    case True{}:
      h => h
    case False{}:
      h => Empty.absurd({rest(Unit{}) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# the bound of the slots of a line is at least 1
def Line.bound_pos(
  fs: List<&2, Types.Fact>,
  +c: Ledgers.Line
) -> {Nat.is_le(1n, RLines.Line.bound(fs, c)) == True{}: Bool}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{a}, rest}:
      Line.bound_pos(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, pk}, rest}:
      Line.bound_pos(rest, c)
    case Con{Types.Fact.Vote{v, Types.Step.At{+c2, +k, +t}, pk}, +rest}:
      Shared.Nat.le_trans(
        1n,
        RLines.Line.bound(rest, c),
        Nat.max(RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k), RLines.Line.bound(rest, c))
      )(
        Line.bound_pos(rest, c)
      )(
        Lists.Nat.le_max_right(
          RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k),
          RLines.Line.bound(rest, c)
        )
      )

# the bound of the slots of a line does not shrink with one more fact
def Line.bound_cons(
  g: Types.Fact,
  +rest: List<&2, Types.Fact>,
  +c: Ledgers.Line
) -> {Nat.is_le(RLines.Line.bound(rest, c), RLines.Line.bound(g <> rest, c)) == True{}: Bool}:
  match g:
    case Types.Fact.Ask{a}:
      Shared.Nat.le_refl(RLines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.Broken{}, pk}:
      Shared.Nat.le_refl(RLines.Line.bound(rest, c))
    case Types.Fact.Vote{v, Types.Step.At{+c2, +k, +t}, pk}:
      Lists.Nat.le_max_right(
        RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k),
        RLines.Line.bound(rest, c)
      )

# the bound of the slots of a line is above each slot that a vote among fs is for
def Line.bound_ge(
  fs: List<&2, Types.Fact>,
  +c: Ledgers.Line,
  +v: String,
  +k: Nat,
  +t: Nat,
  +pk: Types.Cast
) -> {
  List.contains(
    ~Types.Fact,
    ~Coded.Fact.is_eq,
    fs,
    Types.Fact.Vote{v, Types.Step.At{c, k, t}, pk}
  )
    == True{}: Bool
} -> {Nat.is_le(1n+k, RLines.Line.bound(fs, c)) == True{}: Bool}:
  match fs:
    case Nil{}:
      h => Empty.absurd({Nat.is_le(1n+k, 1n) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{+g, +r}:
      hin => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {Nat.is_le(1n+k, RLines.Line.bound(g <> r, c)) == True{}: Bool},
        g,
        r,
        Types.Fact.Vote{v, Types.Step.At{c, k, t}, pk},
        hin,
        eg => (
          %Equal.sym(Types.Fact, g, Types.Fact.Vote{v, Types.Step.At{c, k, t}, pk}, eg): {Nat.is_le(1n+k, RLines.Line.bound(_ <> r, c)) == True{}: Bool}
          %Equal.sym(Bool, Ledgers.Line.is_eq(c, c), True{}, Ledgers.Line.is_eq_refl(c)): {Nat.is_le(1n+k, Nat.max(RLines.Line.bound.at(_, k), RLines.Line.bound(r, c))) == True{}: Bool}
          Lists.Nat.le_max_left(1n+k, RLines.Line.bound(r, c))),
        cin => Shared.Nat.le_trans(
          1n+k,
          RLines.Line.bound(r, c),
          RLines.Line.bound(g <> r, c)
        )(Line.bound_ge(r, c, v, k, t, pk)(cin))(Line.bound_cons(g, r, c))
      )

# the bound of the slots of a line, from facts that a set holds, is at most
# the bound from the facts of the set
def Line.bound_mono(
  fs: List<&2, Types.Fact>,
  +s2: Facts.Facts(),
  +c: Ledgers.Line
) -> {
  Shared.List.holds(
    ~Types.Fact,
    ~RFacts.Plain(),
    ~RFacts.Fact.held,
    fs,
    Facts.Facts.crit(s2)
  )
    == True{}: Bool
} -> {
  Nat.is_le(RLines.Line.bound(fs, c), RLines.Line.bound(Facts.Facts.list(s2), c)) == True{}: Bool
}:
  match fs:
    case Nil{}:
      h => Line.bound_pos(Facts.Facts.list(s2), c)
    case Con{Types.Fact.Ask{+a}, +rest}:
      h => Line.bound_mono(
        rest,
        s2,
        c
      )(
        All.tail(
          Facts.Facts.has(s2, Types.Fact.Ask{a}),
          u => Shared.List.holds(
            ~Types.Fact,
            ~RFacts.Plain(),
            ~RFacts.Fact.held,
            rest,
            Facts.Facts.crit(s2)
          )
        )(h)
      )
    case Con{Types.Fact.Vote{+v, Types.Step.Broken{}, +pk}, +rest}:
      h => Line.bound_mono(
        rest,
        s2,
        c
      )(
        All.tail(
          Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.Broken{}, pk}),
          u => Shared.List.holds(
            ~Types.Fact,
            ~RFacts.Plain(),
            ~RFacts.Fact.held,
            rest,
            Facts.Facts.crit(s2)
          )
        )(h)
      )
    case Con{Types.Fact.Vote{+v, Types.Step.At{+c2, +k, +t}, +pk}, +rest}:
      +h => Nat.max_le(
        RLines.Line.bound.at(Ledgers.Line.is_eq(c2, c), k),
        RLines.Line.bound(rest, c),
        RLines.Line.bound(Facts.Facts.list(s2), c)
      )(
        Lists.Bool.by(
          b => {
            Nat.is_le(
              RLines.Line.bound.at(b, k),
              RLines.Line.bound(Facts.Facts.list(s2), c)
            )
              == True{}: Bool
          },
          Ledgers.Line.is_eq(c2, c),
          et => Line.bound_ge(
            Facts.Facts.list(s2),
            c,
            v,
            k,
            t,
            pk
          )(Facts.Facts.has_in(s2, Types.Fact.Vote{v, Types.Step.At{c, k, t}, pk})((
                %Ledgers.Line.is_eq_sound(c2, c)(et): {Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{_, k, t}, pk}) == True{}: Bool}
                All.head(Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c2, k, t}, pk}), u => Shared.List.holds(~Types.Fact, ~RFacts.Plain(), ~RFacts.Fact.held, rest, Facts.Facts.crit(s2)))(h)))),
          ef => Shared.Nat.le_zero(RLines.Line.bound(Facts.Facts.list(s2), c))
        )
      )(
        Line.bound_mono(
          rest,
          s2,
          c
        )(
          All.tail(
            Facts.Facts.has(s2, Types.Fact.Vote{v, Types.Step.At{c2, k, t}, pk}),
            u => Shared.List.holds(
              ~Types.Fact,
              ~RFacts.Plain(),
              ~RFacts.Fact.held,
              rest,
              Facts.Facts.crit(s2)
            )
          )(h)
        )
      )

# the versions of a line from its version 0 on, in a wider set that names no
# liar and with a store that grew, extend its versions from version 0 on
def From.stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +e0: Types.Entry,
  -vs: List<&2, Types.Entry>
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Maybe.map(
    &2,
    RLines.State,
    List<&2, Types.Entry>,
    RLines.State.versions,
    Lines.Line.from(s, r, c, Some{e0})
  )
    == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Maybe.map(
      &2,
      RLines.State,
      List<&2, Types.Entry>,
      RLines.State.versions,
      Lines.Line.from(s2, Store.grow(r, zs), c, Some{e0})
    )
      == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  +w => hn => e => (
    RLines.State.versions(Lines.Line.start(s2, Store.grow(r, zs), c, RLines.State{[e0], 1n})),
    ({==}, (
        %Shared.Maybe.some_inj(List<&2, Types.Entry>, RLines.State.versions(Lines.Line.start(s, r, c, RLines.State{[e0], 1n})), vs, e): Lists.List.Ext(Types.Entry, _, RLines.State.versions(Lines.Line.start(s2, Store.grow(r, zs), c, RLines.State{[e0], 1n})))
        Run.stays(RLines.Line.bound(Facts.Facts.list(s), c), RLines.Line.bound(Facts.Facts.list(s2), c), s, s2, r, zs, c, RLines.State{[e0], 1n})(w)(hn)(Line.bound_mono(Facts.Facts.list(s), s2, c)(Shared.Bool.and_true_left(Shared.List.holds(~Types.Fact, ~RFacts.Plain(), ~RFacts.Fact.held, Facts.Facts.list(s), Facts.Facts.crit(s2)), Nat.is_le(Facts.Facts.fuel(s), Facts.Facts.fuel(s2)))(w)))))
  )

# Version 0
# ---------

# a member of xs that p(g) holds of: List.pick gives an element
def List.pick_some(
  ~A: Data,
  ~V: Data,
  ~p: V -> A -> Bool,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  xs: List<&2, A>,
  +g: V,
  +x: A
) -> {
  List.contains(~A, ~same, xs, x) == True{}: Bool
} -> {
  p(g)(x) == True{}: Bool
} -> Exists(A, y => {Lists.List.pick(~A, ~V, ~p, xs, g) == Some{y}: Maybe<&2, A>}):
  match xs:
    case Nil{}:
      hin => ht => Empty.absurd(
        Exists(A, y => {None{} == Some{y}: Maybe<&2, A>}),
        Shared.Bool.false_ne_true(hin)
      )
    case Con{+h, +r}:
      Lists.Bool.by(
        hit => {
          List.contains(~A, ~same, h <> r, x) == True{}: Bool
        } -> {
          p(g)(x) == True{}: Bool
        } -> Exists(
          A,
          y => {
            List.find.if(A, h, u => Lists.List.pick(~A, ~V, ~p, r, g), hit) == Some{y}: Maybe<&2, A>
          }
        ),
        p(g)(h),
        et => hin => ht => (h, {==}),
        +ef => hin => +ht => List.pick_some(
          ~A,
          ~V,
          ~p,
          ~same,
          ~laws,
          r,
          g,
          x
        )(
          Lists.List.contains_cons_by(
            ~A,
            ~same,
            ~laws,
            {List.contains(~A, ~same, r, x) == True{}: Bool},
            h,
            r,
            x,
            hin,
            exh => Lists.Bool.clash({List.contains(~A, ~same, r, x) == True{}: Bool}, p(g)(h), ef, (
                %Equal.sym(A, h, x, exh): {p(g)(_) == True{}: Bool}
                ht)),
            cin => cin
          )
        )(ht)
      )

# the starts of a store among some facts are among those of one more fact and them
def Starts.cons(
  g: Types.Fact,
  +r: List<&2, Types.Fact>,
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(r, h), a) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(g <> r, h), a) == True{}: Bool}:
  match g:
    case Types.Fact.Vote{v, st, pk}:
      e => e
    case Types.Fact.Ask{+b}:
      +e => Lists.Bool.by(
        k => {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            List.filter.put(Types.Ask, b, RLines.Starts.of(r, h), k),
            a
          )
            == True{}: Bool
        },
        RFacts.Ask.starts(h, b),
        et => Shared.List.contains_cons(
          ~Types.Ask,
          ~Coded.Ask.is_eq,
          b,
          RLines.Starts.of(r, h),
          a
        )(e),
        ef => e
      )

# an ask among fs that starts the store of h is among the starts of the store
def Starts.in(
  fs: List<&2, Types.Fact>,
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  RFacts.Ask.starts(h, a) == True{}: Bool
} -> {List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(fs, h), a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => t => hin
    case Con{+g, +r}:
      hin => +t => Lists.List.contains_cons_by(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        ~Coded.Fact.laws(),
        {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            RLines.Starts.of(g <> r, h),
            a
          )
            == True{}: Bool
        },
        g,
        r,
        Types.Fact.Ask{a},
        hin,
        eg => (
          %Equal.sym(Types.Fact, g, Types.Fact.Ask{a}, eg): {List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(_ <> r, h), a) == True{}: Bool}
          %Equal.sym(Bool, RFacts.Ask.starts(h, a), True{}, t): {List.contains(~Types.Ask, ~Coded.Ask.is_eq, List.filter.put(Types.Ask, a, RLines.Starts.of(r, h), _), a) == True{}: Bool}
          Lists.List.contains_head(~Types.Ask, ~Coded.Ask.is_eq, ~Coded.Ask.laws(), a, RLines.Starts.of(r, h))),
        cin => Starts.cons(g, r, h, a)(Starts.in(r, h, a)(cin)(t))
      )

# a start of a store among fs is an ask among fs
def Starts.of_held(
  fs: List<&2, Types.Fact>,
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(fs, h), a) == True{}: Bool
} -> {List.contains(~Types.Fact, ~Coded.Fact.is_eq, fs, Types.Fact.Ask{a}) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => hin
    case Con{Types.Fact.Vote{+v, +st, +pk}, +r}:
      hin => Shared.List.contains_cons(
        ~Types.Fact,
        ~Coded.Fact.is_eq,
        Types.Fact.Vote{v, st, pk},
        r,
        Types.Fact.Ask{a}
      )(Starts.of_held(r, h, a)(hin))
    case Con{Types.Fact.Ask{+b}, +r}:
      Lists.Bool.by(
        k => {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            List.filter.put(Types.Ask, b, RLines.Starts.of(r, h), k),
            a
          )
            == True{}: Bool
        } -> {
          List.contains(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Ask{b} <> r,
            Types.Fact.Ask{a}
          )
            == True{}: Bool
        },
        RFacts.Ask.starts(h, b),
        et => hin => Lists.List.contains_cons_by(
          ~Types.Ask,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          {
            List.contains(
              ~Types.Fact,
              ~Coded.Fact.is_eq,
              Types.Fact.Ask{b} <> r,
              Types.Fact.Ask{a}
            )
              == True{}: Bool
          },
          b,
          RLines.Starts.of(r, h),
          a,
          hin,
          eb => (
            %eb: {List.contains(~Types.Fact, ~Coded.Fact.is_eq, Types.Fact.Ask{b} <> r, Types.Fact.Ask{_}) == True{}: Bool}
            Lists.List.contains_head(~Types.Fact, ~Coded.Fact.is_eq, ~Coded.Fact.laws(), Types.Fact.Ask{b}, r)),
          cin => Shared.List.contains_cons(
            ~Types.Fact,
            ~Coded.Fact.is_eq,
            Types.Fact.Ask{b},
            r,
            Types.Fact.Ask{a}
          )(Starts.of_held(r, h, a)(cin))
        ),
        ef => hin => Shared.List.contains_cons(
          ~Types.Fact,
          ~Coded.Fact.is_eq,
          Types.Fact.Ask{b},
          r,
          Types.Fact.Ask{a}
        )(Starts.of_held(r, h, a)(hin))
      )

# a start of a store among fs starts the store
def Starts.of_starts(
  fs: List<&2, Types.Fact>,
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  List.contains(~Types.Ask, ~Coded.Ask.is_eq, RLines.Starts.of(fs, h), a) == True{}: Bool
} -> {RFacts.Ask.starts(h, a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hin => Empty.absurd({RFacts.Ask.starts(h, a) == True{}: Bool}, Shared.Bool.false_ne_true(hin))
    case Con{Types.Fact.Vote{v, st, pk}, +r}:
      hin => Starts.of_starts(r, h, a)(hin)
    case Con{Types.Fact.Ask{+b}, +r}:
      Lists.Bool.by(
        k => {
          RFacts.Ask.starts(h, b) == k: Bool
        } -> {
          List.contains(
            ~Types.Ask,
            ~Coded.Ask.is_eq,
            List.filter.put(Types.Ask, b, RLines.Starts.of(r, h), k),
            a
          )
            == True{}: Bool
        } -> {RFacts.Ask.starts(h, a) == True{}: Bool},
        RFacts.Ask.starts(h, b),
        et => tb => hin => Lists.List.contains_cons_by(
          ~Types.Ask,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          {RFacts.Ask.starts(h, a) == True{}: Bool},
          b,
          RLines.Starts.of(r, h),
          a,
          hin,
          eb => (
            %eb: {RFacts.Ask.starts(h, _) == True{}: Bool}
            tb),
          cin => Starts.of_starts(r, h, a)(cin)
        ),
        ef => tb => hin => Starts.of_starts(r, h, a)(hin)
      )({==})

# in a set that is sound for a node and names no liar, an ask of the set that
# starts a store leads the starts of the store among facts of the set
def Starts.led(
  fs: List<&2, Types.Fact>,
  +name: String,
  +s: Facts.Facts(),
  +h: Hashes.Hash,
  +a: Types.Ask
) -> {
  Facts.Facts.liars(s) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  Facts.Facts.has(s, Types.Fact.Ask{a}) == True{}: Bool
} -> {
  RFacts.Ask.starts(h, a) == True{}: Bool
} -> {
  Shared.List.holds(
    ~Types.Fact,
    ~RFacts.Plain(),
    ~RFacts.Fact.held,
    fs,
    Facts.Facts.crit(s)
  )
    == True{}: Bool
} -> {RLines.Ask.leads(RLines.Starts.of(fs, h), a) == True{}: Bool}:
  match fs:
    case Nil{}:
      hn => o => ha => ta => hh => {==}
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      hn => o => ha => ta => hh => Starts.led(
        rest,
        name,
        s,
        h,
        a
      )(
        hn
      )(
        o
      )(
        ha
      )(
        ta
      )(
        All.tail(
          Facts.Facts.has(s, Types.Fact.Vote{v, st, pk}),
          u => Shared.List.holds(
            ~Types.Fact,
            ~RFacts.Plain(),
            ~RFacts.Fact.held,
            rest,
            Facts.Facts.crit(s)
          )
        )(hh)
      )
    case Con{Types.Fact.Ask{+b}, +rest}:
      +hn => +o => +ha => +ta => +hh => Lists.Bool.by(
        k => {
          RFacts.Ask.starts(h, b) == k: Bool
        } -> {
          Shared.List.holds(
            ~Types.Ask,
            ~Types.Ask,
            ~RLines.Ask.led,
            List.filter.put(Types.Ask, b, RLines.Starts.of(rest, h), k),
            a
          )
            == True{}: Bool
        },
        RFacts.Ask.starts(h, b),
        et => tb => (
          %Equal.sym(Bool, RLines.Ask.led(a, b), True{}, Facts.Case.or_left(RFacts.Ask.alike(a, b), Nat.is_lt(RFacts.Ask.seq(b), RFacts.Ask.seq(a)))(Facts.Facts.honest_starts(name, s, h, a, b)(o)(hn)(ha)(All.head(Facts.Facts.has(s, Types.Fact.Ask{b}), u => Shared.List.holds(~Types.Fact, ~RFacts.Plain(), ~RFacts.Fact.held, rest, Facts.Facts.crit(s)))(hh))(ta)(tb))): {List.all.if(u => Shared.List.holds(~Types.Ask, ~Types.Ask, ~RLines.Ask.led, RLines.Starts.of(rest, h), a), _) == True{}: Bool}
          Starts.led(rest, name, s, h, a)(hn)(o)(ha)(ta)(All.tail(Facts.Facts.has(s, Types.Fact.Ask{b}), u => Shared.List.holds(~Types.Fact, ~RFacts.Plain(), ~RFacts.Fact.held, rest, Facts.Facts.crit(s)))(hh))),
        ef => tb => Starts.led(
          rest,
          name,
          s,
          h,
          a
        )(
          hn
        )(
          o
        )(
          ha
        )(
          ta
        )(
          All.tail(
            Facts.Facts.has(s, Types.Fact.Ask{b}),
            u => Shared.List.holds(
              ~Types.Fact,
              ~RFacts.Plain(),
              ~RFacts.Fact.held,
              rest,
              Facts.Facts.crit(s)
            )
          )(hh)
        )
      )({==})

# asks of one id and one request give the same version 0 of a store
def Store.first.alike(
  a: Types.Ask,
  x: Types.Ask
) -> {
  RFacts.Ask.alike(a, x) == True{}: Bool
} -> {RLines.Store.first.of(Some{a}) == RLines.Store.first.of(Some{x}): Maybe<&2, Types.Entry>}:
  match a x:
    case Types.Ask{+i, k, +r} Types.Ask{+j, l, +q}:
      +al => (
        %Ledgers.Id.is_eq_sound(i, j)(Shared.Bool.and_true_left(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))(al)): {Some{RLines.Entry.first(i, r, 0n)} == Some{RLines.Entry.first(_, q, 0n)}: Maybe<&2, Types.Entry>}
        %Coded.Request.is_eq_sound(r, q)(Shared.Bool.and_true_right(Ledgers.Id.is_eq(i, j), Coded.Request.is_eq(r, q))(al)): {Some{RLines.Entry.first(i, r, 0n)} == Some{RLines.Entry.first(i, _, 0n)}: Maybe<&2, Types.Entry>}
        {==})

# Store.first_stays, with the ask x that the wider set picks
def Store.first_stays.fin(
  +name: String,
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  -e0: Types.Entry,
  +a: Types.Ask,
  +x: Types.Ask,
  hn: {Facts.Facts.liars(s2) == []: List<&2, String>},
  o: {Facts.Facts.ok(name, s2) == True{}: Bool},
  ha: {Facts.Facts.has(s2, Types.Fact.Ask{a}) == True{}: Bool},
  ta: {RFacts.Ask.starts(h, a) == True{}: Bool},
  e: {RLines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>},
  +ex: {
    Lists.List.pick(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~RLines.Ask.leads,
      RLines.Starts.of(Facts.Facts.list(s2), h),
      RLines.Starts.of(Facts.Facts.list(s2), h)
    )
      == Some{x}: Maybe<&2, Types.Ask>
  }
) -> {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>}:
  %Equal.sym(
    Maybe<&2, Types.Ask>,
    Lists.List.pick(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~RLines.Ask.leads,
      RLines.Starts.of(Facts.Facts.list(s2), h),
      RLines.Starts.of(Facts.Facts.list(s2), h)
    ),
    Some{x},
    ex
  ): {RLines.Store.first.of(_) == Some{e0}: Maybe<&2, Types.Entry>}
  %Store.first.alike(
    a,
    x
  )(
    Facts.Facts.honest_starts(
      name,
      s2,
      h,
      a,
      x
    )(
      o
    )(
      hn
    )(
      ha
    )(
      Facts.Facts.in_has(
        s2,
        Types.Fact.Ask{x}
      )(
        Starts.of_held(
          Facts.Facts.list(s2),
          h,
          x
        )(
          Lists.List.pick_in(
            ~Types.Ask,
            ~List<&2, Types.Ask>,
            ~RLines.Ask.leads,
            ~Coded.Ask.is_eq,
            ~Coded.Ask.laws(),
            RLines.Starts.of(Facts.Facts.list(s2), h),
            RLines.Starts.of(Facts.Facts.list(s2), h),
            x
          )(ex)
        )
      )
    )(
      ta
    )(
      Starts.of_starts(
        Facts.Facts.list(s2),
        h,
        x
      )(
        Lists.List.pick_in(
          ~Types.Ask,
          ~List<&2, Types.Ask>,
          ~RLines.Ask.leads,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          RLines.Starts.of(Facts.Facts.list(s2), h),
          RLines.Starts.of(Facts.Facts.list(s2), h),
          x
        )(ex)
      )
    )
  ): {_ == Some{e0}: Maybe<&2, Types.Entry>}
  e

# Store.first_stays, with the ask that the wider set picks
def Store.first_stays.of(
  +name: String,
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  -e0: Types.Entry,
  +a: Types.Ask,
  hn: {Facts.Facts.liars(s2) == []: List<&2, String>},
  o: {Facts.Facts.ok(name, s2) == True{}: Bool},
  ha: {Facts.Facts.has(s2, Types.Fact.Ask{a}) == True{}: Bool},
  ta: {RFacts.Ask.starts(h, a) == True{}: Bool},
  e: {RLines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>},
  r: Exists(
    Types.Ask,
    x => {
      Lists.List.pick(
        ~Types.Ask,
        ~List<&2, Types.Ask>,
        ~RLines.Ask.leads,
        RLines.Starts.of(Facts.Facts.list(s2), h),
        RLines.Starts.of(Facts.Facts.list(s2), h)
      )
        == Some{x}: Maybe<&2, Types.Ask>
    }
  )
) -> {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>}:
  (+x, ex) = r
  Store.first_stays.fin(name, s2, h, e0, a, x, hn, o, ha, ta, e, ex)

# Store.first_stays, with the ask that the set picks, which the wider set holds
def Store.first_stays.at(
  +name: String,
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  -e0: Types.Entry,
  +a: Types.Ask,
  +hn: {Facts.Facts.liars(s2) == []: List<&2, String>},
  +o: {Facts.Facts.ok(name, s2) == True{}: Bool},
  +ha: {Facts.Facts.has(s2, Types.Fact.Ask{a}) == True{}: Bool},
  +ta: {RFacts.Ask.starts(h, a) == True{}: Bool},
  e: {RLines.Store.first.of(Some{a}) == Some{e0}: Maybe<&2, Types.Entry>}
) -> {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>}:
  Store.first_stays.of(
    name,
    s2,
    h,
    e0,
    a,
    hn,
    o,
    ha,
    ta,
    e,
    List.pick_some(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~RLines.Ask.leads,
      ~Coded.Ask.is_eq,
      ~Coded.Ask.laws(),
      RLines.Starts.of(Facts.Facts.list(s2), h),
      RLines.Starts.of(Facts.Facts.list(s2), h),
      a
    )(
      Starts.in(Facts.Facts.list(s2), h, a)(Facts.Facts.has_in(s2, Types.Fact.Ask{a})(ha))(ta)
    )(
      Starts.led(
        Facts.Facts.list(s2),
        name,
        s2,
        h,
        a
      )(
        hn
      )(
        o
      )(
        ha
      )(
        ta
      )(
        Shared.Bool.and_true_left(
          Shared.List.holds(
            ~Types.Fact,
            ~RFacts.Plain(),
            ~RFacts.Fact.held,
            Facts.Facts.list(s2),
            Facts.Facts.crit(s2)
          ),
          Nat.is_le(Facts.Facts.fuel(s2), Facts.Facts.fuel(s2))
        )(Facts.Facts.wider_refl(s2))
      )
    )
  )

# version 0 of a store stays
def Store.first_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  -e0: Types.Entry
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  RLines.Store.first(Facts.Facts.list(s), h) == Some{e0}: Maybe<&2, Types.Entry>
} -> {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>}:
  w => hn => o => e => Lists.Maybe.by(
    Types.Ask,
    m => {
      RLines.Store.first.of(m) == Some{e0}: Maybe<&2, Types.Entry>
    } -> {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>},
    Lists.List.pick(
      ~Types.Ask,
      ~List<&2, Types.Ask>,
      ~RLines.Ask.leads,
      RLines.Starts.of(Facts.Facts.list(s), h),
      RLines.Starts.of(Facts.Facts.list(s), h)
    ),
    en => x => Empty.absurd(
      {RLines.Store.first(Facts.Facts.list(s2), h) == Some{e0}: Maybe<&2, Types.Entry>},
      Shared.Maybe.none_ne_some(Types.Entry, e0, x)
    ),
    +a => +ea => x => Store.first_stays.at(
      name,
      s2,
      h,
      e0,
      a,
      hn,
      o,
      Facts.Facts.wider_has(
        s,
        s2,
        Types.Fact.Ask{a}
      )(
        w
      )(
        Facts.Facts.in_has(
          s,
          Types.Fact.Ask{a}
        )(
          Starts.of_held(
            Facts.Facts.list(s),
            h,
            a
          )(
            Lists.List.pick_in(
              ~Types.Ask,
              ~List<&2, Types.Ask>,
              ~RLines.Ask.leads,
              ~Coded.Ask.is_eq,
              ~Coded.Ask.laws(),
              RLines.Starts.of(Facts.Facts.list(s), h),
              RLines.Starts.of(Facts.Facts.list(s), h),
              a
            )(ea)
          )
        )
      ),
      Starts.of_starts(
        Facts.Facts.list(s),
        h,
        a
      )(
        Lists.List.pick_in(
          ~Types.Ask,
          ~List<&2, Types.Ask>,
          ~RLines.Ask.leads,
          ~Coded.Ask.is_eq,
          ~Coded.Ask.laws(),
          RLines.Starts.of(Facts.Facts.list(s), h),
          RLines.Starts.of(Facts.Facts.list(s), h),
          a
        )(ea)
      ),
      x
    )
  )(e)

# version 0 of a branch stays as its store grows
def Branch.first_append(
  +r: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  -e0: Types.Entry
) -> {
  RLines.Branch.first(r, c) == Some{e0}: Maybe<&2, Types.Entry>
} -> {
  RLines.Branch.first(List.append(&2, Types.Entry, r, zs), c) == Some{e0}: Maybe<&2, Types.Entry>
}:
  e => Lists.Maybe.by(
    Nat,
    j => {
      RLines.Branch.first.at(r, j) == Some{e0}: Maybe<&2, Types.Entry>
    } -> {
      RLines.Branch.first(
        List.append(&2, Types.Entry, r, zs),
        c
      )
        == Some{e0}: Maybe<&2, Types.Entry>
    },
    Lists.List.index(~Types.Entry, ~Ledgers.Line, ~RLines.Entry.owns, r, c),
    en => x => Empty.absurd(
      {
        RLines.Branch.first(
          List.append(&2, Types.Entry, r, zs),
          c
        )
          == Some{e0}: Maybe<&2, Types.Entry>
      },
      Shared.Maybe.none_ne_some(Types.Entry, e0, x)
    ),
    +n => ej => x => Lists.Maybe.by(
      Types.Entry,
      m => {
        RLines.Branch.first.of(n, m) == Some{e0}: Maybe<&2, Types.Entry>
      } -> {
        RLines.Branch.first(
          List.append(&2, Types.Entry, r, zs),
          c
        )
          == Some{e0}: Maybe<&2, Types.Entry>
      },
      List.get(&2, Types.Entry, r, n),
      en => y => Empty.absurd(
        {
          RLines.Branch.first(
            List.append(&2, Types.Entry, r, zs),
            c
          )
            == Some{e0}: Maybe<&2, Types.Entry>
        },
        Shared.Maybe.none_ne_some(Types.Entry, e0, y)
      ),
      +v => ev => y => (
        %Equal.sym(Maybe<&2, Nat>, Lists.List.index(~Types.Entry, ~Ledgers.Line, ~RLines.Entry.owns, List.append(&2, Types.Entry, r, zs), c), Some{n}, Lists.List.index_append(~Types.Entry, ~Ledgers.Line, ~RLines.Entry.owns, r, zs, c, n)(ej)): {RLines.Branch.first.at(List.append(&2, Types.Entry, r, zs), _) == Some{e0}: Maybe<&2, Types.Entry>}
        %Equal.sym(Maybe<&2, Types.Entry>, List.get(&2, Types.Entry, List.append(&2, Types.Entry, r, zs), n), Some{v}, Lists.List.get_append(Types.Entry, r, zs, n, v)(ev)): {RLines.Branch.first.of(n, _) == Some{e0}: Maybe<&2, Types.Entry>}
        y)
    )(x)
  )(e)

# The versions
# ------------

# the versions of a store stay: the larger set decides them, and maybe more
def Store.stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  -vs: List<&2, Types.Entry>
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  Lines.Store.versions(s, h) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Store.versions(s2, h) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  +w => +hn => o => e => Lists.Maybe.by(
    Types.Entry,
    m => {
      Maybe.map(
        &2,
        RLines.State,
        List<&2, Types.Entry>,
        RLines.State.versions,
        Lines.Line.from(s, None{}, Ledgers.Line{h, None{}}, m)
      )
        == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
    } -> Exists(
      List<&2, Types.Entry>,
      vs2 => {
        Lines.Store.versions(s2, h) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
      }
        & Lists.List.Ext(Types.Entry, vs, vs2)
    ),
    RLines.Store.first(Facts.Facts.list(s), h),
    en => x => Empty.absurd(
      Exists(
        List<&2, Types.Entry>,
        vs2 => {
          Lines.Store.versions(s2, h) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
        }
          & Lists.List.Ext(Types.Entry, vs, vs2)
      ),
      Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, x)
    ),
    +e0 => e1 => x => (
      %Equal.sym(Maybe<&2, Types.Entry>, RLines.Store.first(Facts.Facts.list(s2), h), Some{e0}, Store.first_stays(name, s, s2, h, e0)(w)(hn)(o)(e1)): Exists(List<&2, Types.Entry>, vs2 => {Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, Lines.Line.from(s2, None{}, Ledgers.Line{h, None{}}, _)) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>} & Lists.List.Ext(Types.Entry, vs, vs2))
      From.stays(s, s2, None{}, [], Ledgers.Line{h, None{}}, e0, vs)(w)(hn)(x))
  )(e)

# Branch.stays, with version 0 of the branch in the set
def Branch.stays.at(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +r: List<&2, Types.Entry>,
  +zs: List<&2, Types.Entry>,
  -vs: List<&2, Types.Entry>,
  w: {Facts.Facts.wider(s, s2) == True{}: Bool},
  hn: {Facts.Facts.liars(s2) == []: List<&2, String>},
  e: {
    Maybe.map(
      &2,
      RLines.State,
      List<&2, Types.Entry>,
      RLines.State.versions,
      Lines.Line.from(
        s,
        Some{r},
        Ledgers.Line{h, Some{b}},
        RLines.Branch.first(r, Ledgers.Line{h, Some{b}})
      )
    )
      == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
  }
) -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Maybe.map(
      &2,
      RLines.State,
      List<&2, Types.Entry>,
      RLines.State.versions,
      Lines.Line.from(
        s2,
        Some{List.append(&2, Types.Entry, r, zs)},
        Ledgers.Line{h, Some{b}},
        RLines.Branch.first(List.append(&2, Types.Entry, r, zs), Ledgers.Line{h, Some{b}})
      )
    )
      == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  Lists.Maybe.by(
    Types.Entry,
    m => {
      Maybe.map(
        &2,
        RLines.State,
        List<&2, Types.Entry>,
        RLines.State.versions,
        Lines.Line.from(s, Some{r}, Ledgers.Line{h, Some{b}}, m)
      )
        == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
    } -> Exists(
      List<&2, Types.Entry>,
      vs2 => {
        Maybe.map(
          &2,
          RLines.State,
          List<&2, Types.Entry>,
          RLines.State.versions,
          Lines.Line.from(
            s2,
            Some{List.append(&2, Types.Entry, r, zs)},
            Ledgers.Line{h, Some{b}},
            RLines.Branch.first(List.append(&2, Types.Entry, r, zs), Ledgers.Line{h, Some{b}})
          )
        )
          == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
      }
        & Lists.List.Ext(Types.Entry, vs, vs2)
    ),
    RLines.Branch.first(r, Ledgers.Line{h, Some{b}}),
    en => x => Empty.absurd(
      Exists(
        List<&2, Types.Entry>,
        vs2 => {
          Maybe.map(
            &2,
            RLines.State,
            List<&2, Types.Entry>,
            RLines.State.versions,
            Lines.Line.from(
              s2,
              Some{List.append(&2, Types.Entry, r, zs)},
              Ledgers.Line{h, Some{b}},
              RLines.Branch.first(List.append(&2, Types.Entry, r, zs), Ledgers.Line{h, Some{b}})
            )
          )
            == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
        }
          & Lists.List.Ext(Types.Entry, vs, vs2)
      ),
      Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, x)
    ),
    +e0 => e1 => x => (
      %Equal.sym(Maybe<&2, Types.Entry>, RLines.Branch.first(List.append(&2, Types.Entry, r, zs), Ledgers.Line{h, Some{b}}), Some{e0}, Branch.first_append(r, zs, Ledgers.Line{h, Some{b}}, e0)(e1)): Exists(List<&2, Types.Entry>, vs2 => {Maybe.map(&2, RLines.State, List<&2, Types.Entry>, RLines.State.versions, Lines.Line.from(s2, Some{List.append(&2, Types.Entry, r, zs)}, Ledgers.Line{h, Some{b}}, _)) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>} & Lists.List.Ext(Types.Entry, vs, vs2))
      From.stays(s, s2, Some{r}, zs, Ledgers.Line{h, Some{b}}, e0, vs)(w)(hn)(x))
  )(e)

# the versions of a branch stay, with the versions of its store in the wider set
def Branch.stays(
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +store: List<&2, Types.Entry>,
  -vs: List<&2, Types.Entry>,
  w: {Facts.Facts.wider(s, s2) == True{}: Bool},
  hn: {Facts.Facts.liars(s2) == []: List<&2, String>},
  r: Exists(
    List<&2, Types.Entry>,
    R2 => {
      Lines.Store.versions(s2, h) == Some{R2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, store, R2)
  ),
  e: {
    Maybe.map(
      &2,
      RLines.State,
      List<&2, Types.Entry>,
      RLines.State.versions,
      Lines.Line.from(
        s,
        Some{store},
        Ledgers.Line{h, Some{b}},
        RLines.Branch.first(store, Ledgers.Line{h, Some{b}})
      )
    )
      == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
  }
) -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(s2, Ledgers.Line{h, Some{b}}) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  (+R2, p) = r
  (e2, x) = p
  (+zs, ez) = x
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    Lines.Store.versions(s2, h),
    Some{R2},
    e2
  ): Exists(
    List<&2, Types.Entry>,
    vs2 => {
      Maybe.map(
        &2,
        RLines.State,
        List<&2, Types.Entry>,
        RLines.State.versions,
        Lines.Branch.state(s2, Ledgers.Line{h, Some{b}}, _)
      )
        == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, vs, vs2)
  )
  %Equal.sym(
    List<&2, Types.Entry>,
    R2,
    List.append(&2, Types.Entry, store, zs),
    ez
  ): Exists(
    List<&2, Types.Entry>,
    vs2 => {
      Maybe.map(
        &2,
        RLines.State,
        List<&2, Types.Entry>,
        RLines.State.versions,
        Lines.Line.from(
          s2,
          Some{_},
          Ledgers.Line{h, Some{b}},
          RLines.Branch.first(_, Ledgers.Line{h, Some{b}})
        )
      )
        == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, vs, vs2)
  )
  Branch.stays.at(s, s2, h, b, store, zs, vs, w, hn, e)

# the versions of a line stay: the larger set decides them, and maybe more
# after them
def Line.versions_stay(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  Lines.Line.versions(s, c) == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
} -> Exists(
  List<&2, Types.Entry>,
  vs2 => {
    Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
  }
    & Lists.List.Ext(Types.Entry, vs, vs2)
):
  match c:
    case Ledgers.Line{+h, None{}}:
      w => hn => o => e => Store.stays(name, s, s2, h, vs)(w)(hn)(o)(e)
    case Ledgers.Line{+h, Some{+b}}:
      +w => +hn => o => e => Lists.Maybe.by(
        List<&2, Types.Entry>,
        m => {
          Maybe.map(
            &2,
            RLines.State,
            List<&2, Types.Entry>,
            RLines.State.versions,
            Lines.Branch.state(s, Ledgers.Line{h, Some{b}}, m)
          )
            == Some{vs}: Maybe<&2, List<&2, Types.Entry>>
        } -> Exists(
          List<&2, Types.Entry>,
          vs2 => {
            Lines.Line.versions(
              s2,
              Ledgers.Line{h, Some{b}}
            )
              == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
          }
            & Lists.List.Ext(Types.Entry, vs, vs2)
        ),
        Lines.Store.versions(s, h),
        en => x => Empty.absurd(
          Exists(
            List<&2, Types.Entry>,
            vs2 => {
              Lines.Line.versions(
                s2,
                Ledgers.Line{h, Some{b}}
              )
                == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
            }
              & Lists.List.Ext(Types.Entry, vs, vs2)
          ),
          Shared.Maybe.none_ne_some(List<&2, Types.Entry>, vs, x)
        ),
        +R => e_r => x => Branch.stays(
          s,
          s2,
          h,
          b,
          R,
          vs,
          w,
          hn,
          Store.stays(name, s, s2, h, R)(w)(hn)(o)(e_r),
          x
        )
      )(e)

# Line.at_stays, with the versions in the wider set
def Line.at_stays.of(
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  -e: Types.Entry,
  +vs: List<&2, Types.Entry>,
  r: Exists(
    List<&2, Types.Entry>,
    vs2 => {
      Lines.Line.versions(s2, c) == Some{vs2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, vs, vs2)
  ),
  eg: {List.get(&2, Types.Entry, vs, k) == Some{e}: Maybe<&2, Types.Entry>}
) -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  (+vs2, p) = r
  (e2, x) = p
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    Lines.Line.versions(s2, c),
    Some{vs2},
    e2
  ): {RLines.Line.at.of(_, k) == Some{e}: Maybe<&2, Types.Entry>}
  Lists.List.ext_get(Types.Entry, vs, vs2, k, e)(x)(eg)

# a version of a line stays
def Line.at_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +e: Types.Entry
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  Lines.Line.at(s, c, k) == Some{e}: Maybe<&2, Types.Entry>
} -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>}:
  w => hn => o => eg => Lists.Maybe.by(
    List<&2, Types.Entry>,
    m => {
      RLines.Line.at.of(m, k) == Some{e}: Maybe<&2, Types.Entry>
    } -> {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>},
    Lines.Line.versions(s, c),
    en => x => Empty.absurd(
      {Lines.Line.at(s2, c, k) == Some{e}: Maybe<&2, Types.Entry>},
      Shared.Maybe.none_ne_some(Types.Entry, e, x)
    ),
    +vs => ev => x => Line.at_stays.of(
      s2,
      c,
      k,
      e,
      vs,
      Line.versions_stay(name, s, s2, c, vs)(w)(hn)(o)(ev),
      x
    )
  )(eg)

# Rule.after_stays for a branch, with the versions of its store in the wider set
def Rule.after_stays.of(
  +s2: Facts.Facts(),
  +h: Hashes.Hash,
  +b: String,
  +vs: List<&2, Types.Entry>,
  -u: RLines.Rule,
  +store: List<&2, Types.Entry>,
  r: Exists(
    List<&2, Types.Entry>,
    R2 => {
      Lines.Store.versions(s2, h) == Some{R2}: Maybe<&2, List<&2, Types.Entry>>
    }
      & Lists.List.Ext(Types.Entry, store, R2)
  ),
  e: {
    RLines.Line.rule(Some{store}, Ledgers.Line{h, Some{b}}, vs) == Some{u}: Maybe<&2, RLines.Rule>
  }
) -> {Lines.Rule.after(s2, Ledgers.Line{h, Some{b}}, vs) == Some{u}: Maybe<&2, RLines.Rule>}:
  (+R2, p) = r
  (e2, x) = p
  (+zs, ez) = x
  %Equal.sym(
    Maybe<&2, List<&2, Types.Entry>>,
    Lines.Store.versions(s2, h),
    Some{R2},
    e2
  ): {RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, _) == Some{u}: Maybe<&2, RLines.Rule>}
  %Equal.sym(
    List<&2, Types.Entry>,
    R2,
    List.append(&2, Types.Entry, store, zs),
    ez
  ): {RLines.Line.rule(Some{_}, Ledgers.Line{h, Some{b}}, vs) == Some{u}: Maybe<&2, RLines.Rule>}
  Rule.grows(Some{store}, zs, Ledgers.Line{h, Some{b}}, vs, u)(e)

# the rule of the version after some versions stays
def Rule.after_stays(
  +name: String,
  +s: Facts.Facts(),
  +s2: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  +u: RLines.Rule
) -> {
  Facts.Facts.wider(s, s2) == True{}: Bool
} -> {
  Facts.Facts.liars(s2) == []: List<&2, String>
} -> {
  Facts.Facts.ok(name, s2) == True{}: Bool
} -> {
  Lines.Rule.after(s, c, vs) == Some{u}: Maybe<&2, RLines.Rule>
} -> {Lines.Rule.after(s2, c, vs) == Some{u}: Maybe<&2, RLines.Rule>}:
  match c:
    case Ledgers.Line{+h, None{}}:
      w => hn => o => e => e
    case Ledgers.Line{+h, Some{+b}}:
      w => hn => o => e => Lists.Maybe.by(
        List<&2, Types.Entry>,
        m => {
          RLines.Rule.after.of(Ledgers.Line{h, Some{b}}, vs, m) == Some{u}: Maybe<&2, RLines.Rule>
        } -> {
          Lines.Rule.after(s2, Ledgers.Line{h, Some{b}}, vs) == Some{u}: Maybe<&2, RLines.Rule>
        },
        Lines.Store.versions(s, h),
        en => x => Empty.absurd(
          {Lines.Rule.after(s2, Ledgers.Line{h, Some{b}}, vs) == Some{u}: Maybe<&2, RLines.Rule>},
          Shared.Maybe.none_ne_some(RLines.Rule, u, x)
        ),
        +R => e_r => x => Rule.after_stays.of(
          s2,
          h,
          b,
          vs,
          u,
          R,
          Store.stays(name, s, s2, h, R)(w)(hn)(o)(e_r),
          x
        )
      )(e)
