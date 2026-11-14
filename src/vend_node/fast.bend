import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ./codes.bend as Coded
import ./facts.bend as Facts
import ./impl.bend as Impl
import ./known.bend as Knowns
import ./node.bend as Nodes
import ./run/answers.bend as RAnswers
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/fast.bend as RFasts
import ./run/known.bend as RKnown
import ./run/parts.bend as RParts
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# The fast node: laws
# -------------------
# A fast node (run/fast.bend) is the state of a node with a table of the
# states of the lines that it has read. Here: while the table is right
# (RFasts.Fast.ok), the state of a fast node after a deed is the state that
# Nodes.Raw.does gives (Fast.does_raw), the table stays right
# (Fast.does_ok), and the fast node shows what its state shows
# (Fast.answer_raw, Fast.read_raw, Fast.view_raw). So a fast node that starts
# from Fast.new and does deeds is, at each step, the node of the spec.

# What a work learns
# ------------------

# a right table that learns the states of the line m, if any, is right
def Learn.line_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  m: Maybe<&2, Ledgers.Line>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.line(kn, s, m), s) == True{}: Bool}:
  match m:
    case None{}:
      ok => ok
    case Some{+c}:
      ok => Knowns.Known.learn_ok(kn, s, c)(ok)

# a right table that learns the states of the line that a merge takes from is
# right
def Learn.merge_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  r: Spec.Request
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.merge(kn, s, r), s) == True{}: Bool}:
  match r:
    case Spec.Request.Merge{+f, x}:
      ok => Knowns.Known.learn_ok(kn, s, f)(ok)
    case Spec.Request.Start{os}:
      ok => ok
    case Spec.Request.Write{b, p, w}:
      ok => ok
    case Spec.Request.Resolve{j, p, w}:
      ok => ok
    case Spec.Request.Mark{b, j, v}:
      ok => ok
    case Spec.Request.Move{b, j, v}:
      ok => ok
    case Spec.Request.Group{h, g, ms}:
      ok => ok
    case Spec.Request.Own{b, g}:
      ok => ok

# a right table that learns the states of the lines of a request is right
def Learn.request_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +r: Spec.Request
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.request(kn, s, all, r), s) == True{}: Bool}:
  ok => Learn.merge_ok(
    RFasts.Learn.line(kn, s, RWorks.Request.line(all, r)),
    s,
    r
  )(Learn.line_ok(kn, s, RWorks.Request.line(all, r))(ok))

# a right table that learns the states of the lines of the facts fs is right
def Learn.facts_ok(
  fs: List<&2, Types.Fact>,
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.facts(fs, kn, s, all), s) == True{}: Bool}:
  match fs:
    case Nil{}:
      ok => ok
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      ok => Learn.facts_ok(rest, kn, s, all)(ok)
    case Con{Types.Fact.Vote{v, Types.Step.At{+c, k, t}, x}, rest}:
      ok => Learn.facts_ok(
        rest,
        RKnown.Known.learn(kn, s, c),
        s,
        all
      )(Knowns.Known.learn_ok(kn, s, c)(ok))
    case Con{Types.Fact.Ask{Types.Ask{i, n, +r}}, rest}:
      ok => Learn.facts_ok(
        rest,
        RFasts.Learn.request(kn, s, all, r),
        s,
        all
      )(Learn.request_ok(kn, s, all, r)(ok))

# a right table that learns the states of the lines that a work reads is
# right
def Learn.work_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.work(kn, s), s) == True{}: Bool}:
  ok => Learn.facts_ok(RFacts.Facts.list(s), kn, s, RFacts.Facts.list(s))(ok)

# a right table that learns the states of the lines that a work reads,
# unless it holds them, is right
def Learn.if_ok(
  ld: Bool,
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.if(ld, kn, s), s) == True{}: Bool}:
  match ld:
    case True{}:
      ok => ok
    case False{}:
      ok => Learn.work_ok(kn, s)(ok)

# a fast node whose table is right for its state, after it took in a
# request, holds a right table
def Fast.asked_ok(
  +r: Nodes.Raw,
  +kn: RKnown.Known(),
  ld: Bool,
  +q: Spec.Request
) -> {
  RContents.Known.ok(kn, Nodes.Raw.facts(r)) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.asked(r, kn, ld, q)) == True{}: Bool}:
  match ld:
    case False{}:
      ok => ok
    case True{}:
      ok => Learn.request_ok(kn, Nodes.Raw.facts(r), RFacts.Facts.list(Nodes.Raw.facts(r)), q)(ok)

# a fast node after it took in a request has the state that it was given
def Fast.asked_raw(
  +r: Nodes.Raw,
  +kn: RKnown.Known(),
  ld: Bool,
  +q: Spec.Request
) -> {RFasts.Fast.raw(RFasts.Fast.asked(r, kn, ld, q)) == r: Nodes.Raw}:
  match ld:
    case False{}:
      {==}
    case True{}:
      {==}

# What a deed leaves of the table
# -------------------------------

# the table that a ballot at the step st leaves of a right table is right
# for the facts with the ballot
def Table.voted_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  st: Types.Step,
  +x: Types.Cast
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    RFasts.Table.voted(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x}), st),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x})
  )
    == True{}: Bool
}:
  match st:
    case Types.Step.Broken{}:
      ok => {==}
    case Types.Step.At{+c, +k, +t}:
      ok => Knowns.Known.learn_ok(
        RContents.Known.grow(
          kn,
          RKnown.Known.cast(
            kn,
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c,
            k
          ),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          c
        ),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        c
      )(
        Knowns.Known.grow_ok(
          kn,
          RKnown.Known.cast(
            kn,
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c,
            k
          ),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          c
        )(Knowns.Known.cast_ok(kn, name, s, c, k, t, x)(ok))
      )

# What a fast node casts
# ----------------------

# Step.same is True for a step and itself
def Step.same_refl(a: Types.Step) -> {RFasts.Step.same(a, a) == True{}: Bool}:
  match a:
    case Types.Step.Broken{}:
      {==}
    case Types.Step.At{+c, +k, +t}:
      Shared.List.all.if_both(
        Nat.is_eq(k, k),
        u => List.all.if(u2 => Ledgers.Line.is_eq(c, c), Nat.is_eq(t, t))
      )(
        Shared.Nat.is_eq_refl(k)
      )(
        Shared.List.all.if_both(
          Nat.is_eq(t, t),
          u2 => Ledgers.Line.is_eq(c, c)
        )(Shared.Nat.is_eq_refl(t))(Ledgers.Line.is_eq_refl(c))
      )

# Step.same is True only for equal steps
def Step.same_sound(
  a: Types.Step,
  b: Types.Step
) -> {RFasts.Step.same(a, b) == True{}: Bool} -> {a == b: Types.Step}:
  match a b:
    case Types.Step.Broken{} Types.Step.Broken{}:
      h => {==}
    case Types.Step.Broken{} Types.Step.At{c2, k2, t2}:
      h => Empty.absurd(
        {Types.Step.Broken{} == Types.Step.At{c2, k2, t2}: Types.Step},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Step.At{c1, k1, t1} Types.Step.Broken{}:
      h => Empty.absurd(
        {Types.Step.At{c1, k1, t1} == Types.Step.Broken{}: Types.Step},
        Shared.Bool.false_ne_true(h)
      )
    case Types.Step.At{+c1, +k1, +t1} Types.Step.At{+c2, +k2, +t2}:
      +h =>
        %Shared.Nat.is_eq_sound(
          k1,
          k2
        )(
          Shared.List.all.if_hit(
            Nat.is_eq(k1, k2),
            u => List.all.if(u2 => Ledgers.Line.is_eq(c1, c2), Nat.is_eq(t1, t2))
          )(h)
        ): {Types.Step.At{c1, k1, t1} == Types.Step.At{c2, _, t2}: Types.Step}
        %Shared.Nat.is_eq_sound(
          t1,
          t2
        )(
          Shared.List.all.if_hit(
            Nat.is_eq(t1, t2),
            u2 => Ledgers.Line.is_eq(c1, c2)
          )(
            Shared.List.all.if_rest(
              Nat.is_eq(k1, k2),
              u => List.all.if(u2 => Ledgers.Line.is_eq(c1, c2), Nat.is_eq(t1, t2))
            )(h)
          )
        ): {Types.Step.At{c1, k1, t1} == Types.Step.At{c2, k1, _}: Types.Step}
        %Ledgers.Line.is_eq_sound(
          c1,
          c2
        )(
          Shared.List.all.if_rest(
            Nat.is_eq(t1, t2),
            u2 => Ledgers.Line.is_eq(c1, c2)
          )(
            Shared.List.all.if_rest(
              Nat.is_eq(k1, k2),
              u => List.all.if(u2 => Ledgers.Line.is_eq(c1, c2), Nat.is_eq(t1, t2))
            )(h)
          )
        ): {Types.Step.At{c1, k1, t1} == Types.Step.At{_, k1, t1}: Types.Step}
        {==}

# Step.same is the test of the codes
def Step.same_eq(
  +a: Types.Step,
  +b: Types.Step
) -> {RFasts.Step.same(a, b) == Coded.Step.is_eq(a, b): Bool}:
  Lists.Bool.by(x => {x == Coded.Step.is_eq(a, b): Bool}, RFasts.Step.same(a, b), et => (
      %Step.same_sound(a, b)(et): {True{} == Coded.Step.is_eq(a, _): Bool}
      Equal.sym(Bool, Coded.Step.is_eq(a, a), True{}, Coded.Step.is_eq_refl(a))), +ef => Lists.Bool.by(y => {False{} == y: Bool}, Coded.Step.is_eq(a, b), et2 => Equal.trans(Bool, False{}, RFasts.Step.same(a, b), True{}, Equal.sym(Bool, RFasts.Step.same(a, b), False{}, ef), (
          %Coded.Step.is_eq_sound(a, b)(et2): {RFasts.Step.same(a, _) == True{}: Bool}
          Step.same_refl(a))), ef2 => {==}))

# Fact.sits is Fact.is_cast
def Fact.sits_cast(
  g: RFacts.Seat,
  f: Types.Fact
) -> {RFasts.Fact.sits(g, f) == RFacts.Fact.is_cast(g, f): Bool}:
  match g f:
    case RFacts.Seat{+name, +st} Types.Fact.Vote{+v, +st2, pk}:
      Lists.Bool.by(
        x => {
          List.all.if(
            u => RFasts.Step.same(st2, st),
            x
          )
            == Bool.and(x, Coded.Step.is_eq(st2, st)): Bool
        },
        String.eq(v, name),
        et => Step.same_eq(st2, st),
        ef => {==}
      )
    case RFacts.Seat{name, st} Types.Fact.Ask{a}:
      {==}

# a vote of the node sits among fs exactly when one is cast among fs
def Seats.cast_eq(
  fs: List<&2, Types.Fact>,
  +g: RFacts.Seat
) -> {
  Shared.List.some(
    ~Types.Fact,
    ~RFacts.Seat,
    ~RFasts.Fact.sits,
    fs,
    g
  )
    == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFacts.Fact.is_cast, fs, g): Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{+f, +rest}:
      %Equal.sym(
        Bool,
        RFasts.Fact.sits(g, f),
        RFacts.Fact.is_cast(g, f),
        Fact.sits_cast(g, f)
      ): {
        List.any.if(
          u => Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, rest, g),
          _
        )
          == List.any.if(
            u => Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFacts.Fact.is_cast, rest, g),
            RFacts.Fact.is_cast(g, f)
          ): Bool
      }
      Equal.cong(
        Bool,
        Bool,
        y => List.any.if(u => y, RFacts.Fact.is_cast(g, f)),
        Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, rest, g),
        Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFacts.Fact.is_cast, rest, g),
        Seats.cast_eq(rest, g)
      )

# Seat.cast is Facts.cast
def Seat.cast_eq(
  +s: RFacts.Plain(),
  +name: String,
  +st: Types.Step
) -> {RFasts.Seat.cast(s, name, st) == RFacts.Facts.cast(s, name, st): Bool}:
  Seats.cast_eq(RFacts.Facts.list(s), RFacts.Seat{name, st})

# the table kn after a work of the node name on the facts s casts the ballot
# m, if any (as Works.Work.cast does: not when s holds a ballot of the node
# with the same number)
def Table.cast(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  m: Maybe<&2, RWorks.Plan>
) -> RKnown.Known():
  match m:
    case None{}:
      kn
    case Some{RWorks.Plan{+st, x}}:
      Shared.Bool.when(
        RKnown.Known(),
        RFacts.Facts.cast(s, name, st),
        u => kn,
        u => RFasts.Table.voted(kn, RFacts.Facts.add(s, Types.Fact.Vote{name, st, x}), st)
      )

# after a work of the node name on the facts s that plans the ballot m, the
# table holds what a work reads: unless the ballot is cast and may change the
# state of a line that is not its own
def Cast.read(+s: RFacts.Plain(), +name: String, m: Maybe<&2, RWorks.Plan>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{RWorks.Plan{+st, x}}:
      Shared.Bool.when(
        Bool,
        RFacts.Facts.cast(s, name, st),
        u => True{},
        u => RFasts.Step.spares(st)
      )

# the fast node after a work that plans the ballot m: its facts are those
# that RWorks.Work.cast gives, and its table is Table.cast
def Fast.works_at_eq(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  m: Maybe<&2, RWorks.Plan>
) -> {
  RFasts.Fast.works.at(
    name,
    ws,
    ms,
    fs,
    ps,
    kn,
    m
  )
    == RFasts.Fast{
      Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
      Table.cast(kn, fs, name, m),
      Cast.read(fs, name, m)
    }: RFasts.Fast
}:
  match m:
    case None{}:
      {==}
    case Some{RWorks.Plan{+st, +x}}:
      %Equal.sym(
        Bool,
        RFasts.Seat.cast(fs, name, st),
        RFacts.Facts.cast(fs, name, st),
        Seat.cast_eq(fs, name, st)
      ): {
        RFasts.Fast.casts.if(
          _,
          name,
          ws,
          ms,
          fs,
          ps,
          kn,
          st,
          x
        )
          == RFasts.Fast{
            Nodes.Raw{
              name,
              ws,
              ms,
              False{},
              RWorks.Work.cast(fs, name, Some{RWorks.Plan{st, x}}),
              ps
            },
            Table.cast(kn, fs, name, Some{RWorks.Plan{st, x}}),
            Cast.read(fs, name, Some{RWorks.Plan{st, x}})
          }: RFasts.Fast
      }
      Lists.Bool.by(
        b => {
          RFasts.Fast.casts.if(
            b,
            name,
            ws,
            ms,
            fs,
            ps,
            kn,
            st,
            x
          )
            == RFasts.Fast{
              Nodes.Raw{
                name,
                ws,
                ms,
                False{},
                Shared.Bool.when(
                  RFacts.Plain(),
                  b,
                  u => fs,
                  u => RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x})
                ),
                ps
              },
              Shared.Bool.when(
                RKnown.Known(),
                b,
                u => kn,
                u => RFasts.Table.voted(kn, RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x}), st)
              ),
              Shared.Bool.when(Bool, b, u => True{}, u => RFasts.Step.spares(st))
            }: RFasts.Fast
        },
        RFacts.Facts.cast(fs, name, st),
        et => {==},
        ef => {==}
      )

# the table that a work leaves of a right table is right for the facts after
# the work
def Table.cast_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  m: Maybe<&2, RWorks.Plan>
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    Table.cast(kn, Facts.Facts.crit(s), name, m),
    RWorks.Work.cast(Facts.Facts.crit(s), name, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      ok => ok
    case Some{RWorks.Plan{+st, +x}}:
      +ok => Lists.Bool.by(
        b => {
          RContents.Known.ok(
            Shared.Bool.when(
              RKnown.Known(),
              b,
              u => kn,
              u => RFasts.Table.voted(
                kn,
                RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x}),
                st
              )
            ),
            Shared.Bool.when(
              RFacts.Plain(),
              b,
              u => Facts.Facts.crit(s),
              u => RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x})
            )
          )
            == True{}: Bool
        },
        RFacts.Facts.cast(Facts.Facts.crit(s), name, st),
        et => ok,
        ef => Table.voted_ok(kn, name, s, st, x)(ok)
      )

# the table that a request leaves of a right table is right for the same
# facts
def Table.asked_same(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  r: Spec.Request
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Table.asked(kn, r), s) == True{}: Bool}:
  ok => Lists.Bool.by(
    b => {
      RContents.Known.ok(
        Shared.Bool.when(RKnown.Known(), b, u => RKnown.Known.none(), u => kn),
        s
      )
        == True{}: Bool
    },
    RFacts.Request.is_start(r),
    et => {==},
    ef => ok
  )

# the table that a request leaves of a right table is right for the facts
# after the node takes the request in
def Table.asked_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RContents.Known.ok(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    RFasts.Table.asked(kn, r),
    RFacts.Facts.ask(name, Facts.Facts.crit(s), i, r)
  )
    == True{}: Bool
}:
  +ok => Lists.Bool.by(
    b => {
      RContents.Known.ok(
        Shared.Bool.when(RKnown.Known(), b, u => RKnown.Known.none(), u => kn),
        RFacts.Facts.ask(name, Facts.Facts.crit(s), i, r)
      )
        == True{}: Bool
    },
    RFacts.Request.is_start(r),
    et => {==},
    ef => (
      %Facts.Facts.take_crit(name, s, Types.Fact.Ask{Facts.Facts.asked(s, i, r)}): {RContents.Known.ok(kn, _) == True{}: Bool}
      Knowns.Known.asked_ok(kn, name, s, Facts.Facts.asked(s, i, r))(ef)(ok))
  )

# What a fast node does
# ---------------------

# a right table changes no part that the node needs
def Needs.of_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  ms: List<&2, Nodes.Mounted>
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {
  Nodes.Needs.of(
    kn,
    s,
    name,
    ms
  )
    == Nodes.Needs.of(RKnown.Known.none(), s, name, ms): List<&2, Hashes.Hash>
}:
  match ms:
    case Nil{}:
      ok => {==}
    case Con{Nodes.Mounted{+a, +b, +p}, +rest}:
      +ok => (
        %Knowns.View.at_ok(kn, s, name, b, p)(ok): {Nodes.Needs.of(kn, s, name, Nodes.Mounted{a, b, p} <> rest) == Nodes.Needs.put(_, Nodes.Needs.of(RKnown.Known.none(), s, name, rest)): List<&2, Hashes.Hash>}
        %Needs.of_ok(kn, s, name, rest)(ok): {Nodes.Needs.of(kn, s, name, Nodes.Mounted{a, b, p} <> rest) == Nodes.Needs.put(RAnswers.View.at(kn, s, name, b, p), _): List<&2, Hashes.Hash>}
        {==})

# Fast.works_at_eq, read from right to left
def Fast.works_at_sym(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  +m: Maybe<&2, RWorks.Plan>
) -> {
  RFasts.Fast{
    Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
    Table.cast(kn, fs, name, m),
    Cast.read(fs, name, m)
  }
    == RFasts.Fast.works.at(name, ws, ms, fs, ps, kn, m): RFasts.Fast
}:
  Equal.sym(
    RFasts.Fast,
    RFasts.Fast.works.at(name, ws, ms, fs, ps, kn, m),
    RFasts.Fast{
      Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
      Table.cast(kn, fs, name, m),
      Cast.read(fs, name, m)
    },
    Fast.works_at_eq(name, ws, ms, fs, ps, kn, m)
  )

# What a fast node takes in
# -------------------------

# the ask of a request that starts no store collides with no ask among all
def Collided.none(
  all: List<&2, Types.Fact>,
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  Shared.List.some(
    ~Types.Fact,
    ~Types.Ask,
    ~RFacts.Fact.collides,
    all,
    Types.Ask{i, k, r}
  )
    == False{}: Bool
}:
  match all:
    case Nil{}:
      e => {==}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      e => Collided.none(rest, i, k, r)(e)
    case Con{Types.Fact.Ask{+b}, +rest}:
      +e =>
        %Equal.sym(
          Bool,
          RFacts.Request.is_start(r),
          False{},
          e
        ): {
          List.any.if(
            u => Shared.List.some(
              ~Types.Fact,
              ~Types.Ask,
              ~RFacts.Fact.collides,
              rest,
              Types.Ask{i, k, r}
            ),
            Bool.and(
              Bool.and(
                _,
                Hashes.Hash.is_eq(RFacts.Start.root(i, r), RFacts.Ask.root(Types.Ask{i, k, r}))
              ),
              Bool.and(
                RFacts.Ask.starts(RFacts.Ask.root(Types.Ask{i, k, r}), b),
                Bool.not(RFacts.Ask.alike(Types.Ask{i, k, r}, b))
              )
            )
          )
            == False{}: Bool
        }
        Collided.none(rest, i, k, r)(e)

# the facts that a fast node has after it takes in a request are those that
# RFacts.Facts.ask gives
def Asked.take_raw(
  +name: String,
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {RFasts.Asked.take(name, s, i, r) == RFacts.Facts.ask(name, s, i, r): RFacts.Plain()}:
  Lists.Bool.by(
    b => {
      Shared.Bool.when(
        RFacts.Plain(),
        b,
        u => RFacts.Facts.ask(name, s, i, r),
        u => RFacts.Facts.add(s, Types.Fact.Ask{RFacts.Facts.asked(s, i, r)})
      )
        == RFacts.Facts.ask(name, s, i, r): RFacts.Plain()
    },
    RFacts.Request.is_start(r),
    et => {==},
    ef => Equal.sym(
      RFacts.Plain(),
      RFacts.Facts.ask(name, s, i, r),
      RFacts.Facts.add(s, Types.Fact.Ask{RFacts.Facts.asked(s, i, r)}),
      Equal.cong(
        Bool,
        RFacts.Plain(),
        b => Shared.Bool.when(
          RFacts.Plain(),
          b,
          u => RFacts.Trust.break(
            RFacts.Facts.add(s, Types.Fact.Ask{RFacts.Facts.asked(s, i, r)}),
            name
          ),
          u => RFacts.Facts.add(s, Types.Fact.Ask{RFacts.Facts.asked(s, i, r)})
        ),
        Shared.List.some(
          ~Types.Fact,
          ~Types.Ask,
          ~RFacts.Fact.collides,
          RFacts.Facts.list(s),
          Types.Ask{i, 1n+RFacts.Seq.peak(RFacts.Facts.list(s)), r}
        ),
        False{},
        Collided.none(RFacts.Facts.list(s), i, 1n+RFacts.Seq.peak(RFacts.Facts.list(s)), r)(ef)
      )
    )
  )

# the state of a fast node that takes in a request, when it may (go), is the
# state that Nodes.Raw.asks gives
def Fast.asks_raw(
  go: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RFasts.Fast.asks(
    name,
    ws,
    ms,
    st,
    fs,
    ps,
    i,
    r,
    go
  )
    == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go): Nodes.Raw
}:
  match go:
    case False{}:
      {==}
    case True{}:
      Equal.cong(
        RFacts.Plain(),
        Nodes.Raw,
        x => Nodes.Raw{name, ws, ms, st, x, Nodes.Kept.with(ps, Nodes.Request.content(r))},
        RFasts.Asked.take(name, fs, i, r),
        RFacts.Facts.ask(name, fs, i, r),
        Asked.take_raw(name, fs, i, r)
      )

# the table of a fast node that takes in a request, when it may (go), stays
# right
def Fast.asks_ok(
  go: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +kn: RKnown.Known(),
  +okr: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  RContents.Known.ok(kn, fs) == True{}: Bool
} -> {
  RContents.Known.ok(
    RFasts.Table.asked(kn, r),
    Nodes.Raw.facts(RFasts.Fast.asks(name, ws, ms, st, fs, ps, i, r, go))
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      ok => Table.asked_same(kn, fs, r)(ok)
    case True{}:
      ok => (
        %Equal.sym(RFacts.Plain(), RFasts.Asked.take(name, fs, i, r), RFacts.Facts.ask(name, fs, i, r), Asked.take_raw(name, fs, i, r)): {RContents.Known.ok(RFasts.Table.asked(kn, r), _) == True{}: Bool}
        Table.asked_ok(kn, name, Impl.Node.set(name, fs, ps, okr), i, r)(ok))

# the table of a fast node stays right after a work
def Fast.works_ok(
  st: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  +ld: Bool,
  +okr: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  RContents.Known.ok(kn, fs) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.works(name, ws, ms, st, fs, ps, kn, ld)) == True{}: Bool}:
  match st:
    case True{}:
      ok => ok
    case False{}:
      ok => (
        %Fast.works_at_sym(name, ws, ms, fs, ps, RFasts.Learn.if(ld, kn, fs), RWorks.Work.plan(RFasts.Learn.if(ld, kn, fs), fs, name)): {RFasts.Fast.ok(_) == True{}: Bool}
        Table.cast_ok(RFasts.Learn.if(ld, kn, fs), name, Impl.Node.set(name, fs, ps, okr), RWorks.Work.plan(RFasts.Learn.if(ld, kn, fs), fs, name))(Learn.if_ok(ld, kn, fs)(ok)))

# the table of a fast node whose state can be a node stays right after any
# deed
def Fast.does_ok(
  f: RFasts.Fast,
  a: Nodes.Act
) -> {
  Nodes.Raw.ok(RFasts.Fast.raw(f)) == True{}: Bool
} -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.does(f, a)) == True{}: Bool}:
  match f a:
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Connect{w}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Leave{w}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Ask{+i, +q}:
      +okr => ok => Fast.asked_ok(
        RFasts.Fast.asks(
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q,
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
        ),
        RFasts.Table.asked(kn, q),
        ld,
        q
      )(
        Fast.asks_ok(
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))),
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q,
          kn,
          okr
        )(ok)
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Sync{from}:
      okr => ok => {==}
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn,
      +ld
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      +okr => ok => Fast.asked_ok(
        RFasts.Fast.asks(
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}},
          Bool.not(st)
        ),
        kn,
        ld,
        Spec.Request.Write{b, p, None{}}
      )(
        Fast.asks_ok(
          Bool.not(st),
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}},
          kn,
          okr
        )(ok)
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Unmount{a}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Work{}:
      +okr => ok => Fast.works_ok(st, name, ws, ms, fs, ps, kn, ld, okr)(ok)
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Drop{}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Stop{force}:
      okr => ok => ok

# the state of a fast node after a work is the state that a node has after a
# work
def Fast.works_raw(
  st: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  +ld: Bool
) -> {
  RContents.Known.ok(kn, fs) == True{}: Bool
} -> {
  RFasts.Fast.raw(
    RFasts.Fast.works(name, ws, ms, st, fs, ps, kn, ld)
  )
    == Nodes.Raw.works(name, ws, ms, st, fs, ps): Nodes.Raw
}:
  match st:
    case True{}:
      ok => {==}
    case False{}:
      ok =>
        %Fast.works_at_sym(
          name,
          ws,
          ms,
          fs,
          ps,
          RFasts.Learn.if(ld, kn, fs),
          RWorks.Work.plan(RFasts.Learn.if(ld, kn, fs), fs, name)
        ): {RFasts.Fast.raw(_) == Nodes.Raw.works(name, ws, ms, False{}, fs, ps): Nodes.Raw}
        Equal.cong(
          Maybe<&2, RWorks.Plan>,
          Nodes.Raw,
          m => Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
          RWorks.Work.plan(RFasts.Learn.if(ld, kn, fs), fs, name),
          RWorks.Work.plan(RKnown.Known.none(), fs, name),
          Knowns.Work.plan_ok(RFasts.Learn.if(ld, kn, fs), fs, name)(Learn.if_ok(ld, kn, fs)(ok))
        )

# the state of a fast node with a right table after a deed is the state that
# Nodes.Raw.does gives: a fast node does what a node does
def Fast.does_raw(
  f: RFasts.Fast,
  a: Nodes.Act
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.raw(RFasts.Fast.does(f, a)) == Nodes.Raw.does(RFasts.Fast.raw(f), a): Nodes.Raw}:
  match f a:
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Connect{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Leave{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Ask{+i, +q}:
      ok => Equal.trans(
        Nodes.Raw,
        RFasts.Fast.raw(
          RFasts.Fast.asked(
            RFasts.Fast.asks(
              name,
              ws,
              ms,
              st,
              fs,
              ps,
              i,
              q,
              Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
            ),
            RFasts.Table.asked(kn, q),
            ld,
            q
          )
        ),
        RFasts.Fast.asks(
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q,
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
        ),
        Nodes.Raw.asks(
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q,
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
        ),
        Fast.asked_raw(
          RFasts.Fast.asks(
            name,
            ws,
            ms,
            st,
            fs,
            ps,
            i,
            q,
            Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
          ),
          RFasts.Table.asked(kn, q),
          ld,
          q
        ),
        Fast.asks_raw(
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))),
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          i,
          q
        )
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Sync{from}:
      ok => {==}
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn,
      +ld
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      ok => Equal.trans(
        Nodes.Raw,
        RFasts.Fast.raw(
          RFasts.Fast.asked(
            RFasts.Fast.asks(
              name,
              ws,
              Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
              st,
              fs,
              ps,
              Nodes.Mount.id(name, a),
              Spec.Request.Write{b, p, Some{held}},
              Bool.not(st)
            ),
            kn,
            ld,
            Spec.Request.Write{b, p, None{}}
          )
        ),
        RFasts.Fast.asks(
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}},
          Bool.not(st)
        ),
        Nodes.Raw.asks(
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}},
          Bool.not(st)
        ),
        Fast.asked_raw(
          RFasts.Fast.asks(
            name,
            ws,
            Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
            st,
            fs,
            ps,
            Nodes.Mount.id(name, a),
            Spec.Request.Write{b, p, Some{held}},
            Bool.not(st)
          ),
          kn,
          ld,
          Spec.Request.Write{b, p, None{}}
        ),
        Fast.asks_raw(
          Bool.not(st),
          name,
          ws,
          Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
          st,
          fs,
          ps,
          Nodes.Mount.id(name, a),
          Spec.Request.Write{b, p, Some{held}}
        )
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Unmount{a}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Work{}:
      ok => Fast.works_raw(st, name, ws, ms, fs, ps, kn, ld)(ok)
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Drop{}:
      ok => Equal.cong(
        List<&2, Hashes.Hash>,
        Nodes.Raw,
        hs => Nodes.Raw{name, ws, ms, st, fs, RParts.Parts.only(ps, hs)},
        Nodes.Needs.of(kn, fs, name, ms),
        Nodes.Needs.of(RKnown.Known.none(), fs, name, ms),
        Needs.of_ok(kn, fs, name, ms)(ok)
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn, +ld} Nodes.Act.Stop{force}:
      ok => {==}

# a new fast node holds a right table
def Fast.new_ok(name: String) -> {RFasts.Fast.ok(RFasts.Fast.new(name)) == True{}: Bool}:
  {==}

# a fast node that learns the states of a line keeps its state
def Fast.learn_raw(
  f: RFasts.Fast,
  +c: Ledgers.Line
) -> {RFasts.Fast.raw(RFasts.Fast.learn(f, c)) == RFasts.Fast.raw(f): Nodes.Raw}:
  match f:
    case RFasts.Fast{r, kn, ld}:
      {==}

# the table of a fast node that learns the states of a line stays right
def Fast.learn_ok(
  f: RFasts.Fast,
  +c: Ledgers.Line
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.learn(f, c)) == True{}: Bool}:
  match f:
    case RFasts.Fast{+r, +kn, ld}:
      ok => Knowns.Known.warm_ok(
        RKnown.Known.learn(kn, Nodes.Raw.facts(r), c),
        Nodes.Raw.facts(r),
        c
      )(Knowns.Known.learn_ok(kn, Nodes.Raw.facts(r), c)(ok))

# What a fast node shows
# ----------------------

# a fast node with a right table replies as its state does
def Fast.answer_raw(
  f: RFasts.Fast,
  +q: Spec.Question
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.answer(f, q) == Nodes.Raw.answer(RFasts.Fast.raw(f), q): Maybe<&2, Spec.Reply>}:
  match f:
    case RFasts.Fast{+r, +kn, ld}:
      ok => Knowns.Answer.of_ok(kn, Nodes.Raw.facts(r), q)(ok)

# a fast node with a right table reads a resource as its state does
def Fast.read_raw(
  f: RFasts.Fast,
  +c: Ledgers.Line,
  +k: Nat,
  +p: String
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {
  RFasts.Fast.read(
    f,
    c,
    k,
    p
  )
    == Nodes.Raw.read(RFasts.Fast.raw(f), c, k, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match f:
    case RFasts.Fast{+r, +kn, ld}:
      ok => Knowns.Content.read_ok(kn, Nodes.Raw.facts(r), c, k, p)(ok)

# a fast node with a right table shows a resource as its state does
def Fast.view_raw(
  f: RFasts.Fast,
  +w: String,
  +b: Ledgers.Line,
  +p: String
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {
  RFasts.Fast.view(
    f,
    w,
    b,
    p
  )
    == Nodes.Raw.view(RFasts.Fast.raw(f), w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match f:
    case RFasts.Fast{+r, +kn, ld}:
      ok => Knowns.View.at_ok(kn, Nodes.Raw.facts(r), w, b, p)(ok)
