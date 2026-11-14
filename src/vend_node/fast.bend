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
import ./run/lines.bend as RLines
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
# A table is right when each state and content that it holds is what the
# facts give (RContents.Known.ok); it fits when, besides, the facts that it
# holds for a work are those that a work may still act on
# (RContents.Known.fit).

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

# a table that learns the states of the line m, if any, holds the same facts
# for a work
def Learn.line_open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  m: Maybe<&2, Ledgers.Line>
) -> {
  RKnown.Known.shelf(kn) == RKnown.Known.shelf(RFasts.Learn.line(kn, s, m)): Maybe<&2, RKnown.Kept>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Knowns.Known.learn_open(kn, s, c)

# a table that learns the states of the line that a merge takes from holds
# the same facts for a work
def Learn.merge_open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  r: Spec.Request
) -> {
  RKnown.Known.shelf(kn) == RKnown.Known.shelf(RFasts.Learn.merge(kn, s, r)): Maybe<&2, RKnown.Kept>
}:
  match r:
    case Spec.Request.Merge{+f, x}:
      Knowns.Known.learn_open(kn, s, f)
    case Spec.Request.Start{os}:
      {==}
    case Spec.Request.Write{b, p, w}:
      {==}
    case Spec.Request.Resolve{j, p, w}:
      {==}
    case Spec.Request.Mark{b, j, v}:
      {==}
    case Spec.Request.Move{b, j, v}:
      {==}
    case Spec.Request.Group{h, g, ms}:
      {==}
    case Spec.Request.Own{b, g}:
      {==}

# a table that learns the states of the lines of a request holds the same
# facts for a work
def Learn.request_open(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +r: Spec.Request
) -> {
  RKnown.Known.shelf(
    kn
  )
    == RKnown.Known.shelf(RFasts.Learn.request(kn, s, all, r)): Maybe<&2, RKnown.Kept>
}:
  Equal.trans(
    Maybe<&2, RKnown.Kept>,
    RKnown.Known.shelf(kn),
    RKnown.Known.shelf(RFasts.Learn.line(kn, s, RWorks.Request.line(all, r))),
    RKnown.Known.shelf(RFasts.Learn.request(kn, s, all, r)),
    Learn.line_open(kn, s, RWorks.Request.line(all, r)),
    Learn.merge_open(RFasts.Learn.line(kn, s, RWorks.Request.line(all, r)), s, r)
  )

# a table that fits, after it learns the states of the lines of a request,
# fits
def Learn.request_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +all: List<&2, Types.Fact>,
  +r: Spec.Request
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RFasts.Learn.request(kn, s, all, r), s) == True{}: Bool}:
  +h => Knowns.Fit.both(
    RFasts.Learn.request(kn, s, all, r),
    s
  )(Learn.request_ok(kn, s, all, r)(Knowns.Fit.ok(kn, s)(h)))((
      %Learn.request_open(kn, s, all, r): {RContents.Shelf.fits(_, s) == True{}: Bool}
      Knowns.Fit.open(kn, s)(h)))

# a table that fits, after it learns the states of the lines that a work
# reads and the facts that a work may act on, unless it holds them, fits
def Learn.if_fit(
  ld: Bool,
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RFasts.Learn.if(ld, kn, s), s) == True{}: Bool}:
  match ld:
    case True{}:
      h => h
    case False{}:
      h => Knowns.Known.opened_fit(
        RFasts.Learn.work(kn, s),
        s
      )(Learn.work_ok(kn, s)(Knowns.Fit.ok(kn, s)(h)))

# What a fast node takes in
# -------------------------

# a fast node after it took in a request has the state that it was given
def Fast.asked_raw(
  +r: Nodes.Raw,
  +kn: RKnown.Known(),
  ld: Bool,
  +q: Spec.Request,
  +m: Maybe<&2, Types.Fact>
) -> {RFasts.Fast.raw(RFasts.Fast.asked(r, kn, ld, q, m)) == r: Nodes.Raw}:
  match ld:
    case False{}:
      {==}
    case True{}:
      {==}

# a fast node whose table fits its state, after it learned what a work reads
# for a request, holds a table that fits
def Fast.asked_fit(
  +r: Nodes.Raw,
  +kn: RKnown.Known(),
  ld: Bool,
  +q: Spec.Request
) -> {
  RContents.Known.fit(kn, Nodes.Raw.facts(r)) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.asked(r, kn, ld, q, None{})) == True{}: Bool}:
  match ld:
    case False{}:
      h => h
    case True{}:
      h => Learn.request_fit(
        kn,
        Nodes.Raw.facts(r),
        RKnown.Known.facts(kn, Nodes.Raw.facts(r)),
        q
      )(h)

# a fast node whose table fits its state, after it took in an ask that
# starts no store and a work may act on the ask, holds a table that fits
def Fast.asked_join(
  ld: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +ps: RParts.Parts,
  +s: Facts.Facts(),
  +i: Ledgers.Id,
  +n: Nat,
  +r: Spec.Request,
  +q: Spec.Request,
  +kn: RKnown.Known()
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RFasts.Fast.ok(
    RFasts.Fast.asked(
      Nodes.Raw{
        name,
        ws,
        ms,
        st,
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}),
        ps
      },
      kn,
      ld,
      q,
      Some{Types.Fact.Ask{Types.Ask{i, n, r}}}
    )
  )
    == True{}: Bool
}:
  match ld:
    case False{}:
      +e => +h => (
        %Knowns.Take.ask(name, s, i, n, r)(e): {RFasts.Fast.ok(RFasts.Fast.asked(Nodes.Raw{name, ws, ms, st, _, ps}, kn, False{}, q, Some{Types.Fact.Ask{Types.Ask{i, n, r}}})) == True{}: Bool}
        Knowns.Known.joined_fit(kn, name, s, i, n, r)(e)(Knowns.Known.asked_ok(kn, name, s, Types.Ask{i, n, r})(e)(Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h)))(Knowns.Fit.open(kn, Facts.Facts.crit(s))(h)))
    case True{}:
      +e => +h => (
        %Knowns.Take.ask(name, s, i, n, r)(e): {RFasts.Fast.ok(RFasts.Fast.asked(Nodes.Raw{name, ws, ms, st, _, ps}, kn, True{}, q, Some{Types.Fact.Ask{Types.Ask{i, n, r}}})) == True{}: Bool}
        Knowns.Known.joined_fit(RFasts.Learn.asked(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), q), name, s, i, n, r)(e)(Learn.request_ok(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), RKnown.Known.facts(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), q)(Knowns.Known.asked_ok(kn, name, s, Types.Ask{i, n, r})(e)(Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h))))((
          %Learn.request_open(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), RKnown.Known.facts(kn, Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))), q): {RContents.Shelf.fits(_, Facts.Facts.crit(s)) == True{}: Bool}
          Knowns.Fit.open(kn, Facts.Facts.crit(s))(h))))

# the ask that a fast node whose table fits gives a request is the one that
# RFacts.Facts.asked gives
def Asked.ask_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RFasts.Asked.ask(kn, s, i, r) == RFacts.Facts.asked(s, i, r): Types.Ask}:
  h => Equal.cong(
    Nat,
    Types.Ask,
    y => Types.Ask{i, 1n+y, r},
    RKnown.Known.peak(kn, s),
    RFacts.Seq.peak(RFacts.Facts.list(s)),
    Knowns.Known.peak_fit(kn, s)(h)
  )

# the facts that a fast node has after it takes in a request are those that
# RFacts.Facts.ask gives
def Asked.take_raw(
  +name: String,
  +s: RFacts.Plain(),
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  RFasts.Asked.take(
    name,
    s,
    RFacts.Facts.asked(s, i, r)
  )
    == RFacts.Facts.ask(name, s, i, r): RFacts.Plain()
}:
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
        Knowns.Collided.none(
          RFacts.Facts.list(s),
          i,
          1n+RFacts.Seq.peak(RFacts.Facts.list(s)),
          r
        )(ef)
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
    RFacts.Facts.asked(fs, i, r),
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
        RFasts.Asked.take(name, fs, RFacts.Facts.asked(fs, i, r)),
        RFacts.Facts.ask(name, fs, i, r),
        Asked.take_raw(name, fs, i, r)
      )

# the state of a fast node that takes in a request with the table kn, when
# it may (go), is the state that Nodes.Raw.asks gives
def Fast.asks_to_raw(
  +go: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +q: Spec.Request,
  +kn: RKnown.Known()
) -> {
  RFasts.Fast.raw(
    RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, RFacts.Facts.asked(fs, i, r), q, go)
  )
    == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go): Nodes.Raw
}:
  Equal.trans(
    Nodes.Raw,
    RFasts.Fast.raw(
      RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, RFacts.Facts.asked(fs, i, r), q, go)
    ),
    RFasts.Fast.asks(name, ws, ms, st, fs, ps, RFacts.Facts.asked(fs, i, r), go),
    Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go),
    Fast.asked_raw(
      RFasts.Fast.asks(name, ws, ms, st, fs, ps, RFacts.Facts.asked(fs, i, r), go),
      kn,
      RFasts.Table.read(kn),
      q,
      RFasts.Asked.fact(RFacts.Facts.asked(fs, i, r), go)
    ),
    Fast.asks_raw(go, name, ws, ms, st, fs, ps, i, r)
  )

# the table of a fast node that takes in a request, when it may (go), fits:
# kn is the table that fits its state before, or that fits whatever the
# request leaves when it starts a store
def Fast.asks_fit(
  go: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +q: Spec.Request,
  +kn: RKnown.Known(),
  +okr: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  RContents.Known.fit(kn, fs) == True{}: Bool
} -> (
  {
    RFacts.Request.is_start(r) == True{}: Bool
  } -> {
    RContents.Known.fit(
      kn,
      RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)})
    )
      == True{}: Bool
  }
) -> {
  RFasts.Fast.ok(
    RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, RFacts.Facts.asked(fs, i, r), q, go)
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      h => hs => Fast.asked_fit(
        Nodes.Raw{name, ws, ms, st, fs, ps},
        kn,
        RFasts.Table.read(kn),
        q
      )(h)
    case True{}:
      h => hs => Lists.Bool.by(
        y => {
          RFasts.Fast.ok(
            RFasts.Fast.asked(
              Nodes.Raw{
                name,
                ws,
                ms,
                st,
                Shared.Bool.when(
                  RFacts.Plain(),
                  y,
                  u => RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)}),
                  u => RFacts.Facts.add(fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)})
                ),
                Nodes.Kept.with(ps, Nodes.Request.content(r))
              },
              kn,
              RFasts.Table.read(kn),
              q,
              Shared.Maybe.when(
                Types.Fact,
                Bool.not(y),
                u => Some{Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)}}
              )
            )
          )
            == True{}: Bool
        },
        RFacts.Request.is_start(r),
        et => Fast.asked_fit(
          Nodes.Raw{
            name,
            ws,
            ms,
            st,
            RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)}),
            Nodes.Kept.with(ps, Nodes.Request.content(r))
          },
          kn,
          RFasts.Table.read(kn),
          q
        )(hs(et)),
        ef => Fast.asked_join(
          RFasts.Table.read(kn),
          name,
          ws,
          ms,
          st,
          Nodes.Kept.with(ps, Nodes.Request.content(r)),
          Impl.Node.set(name, fs, ps, okr),
          i,
          1n+RFacts.Seq.peak(RFacts.Facts.list(fs)),
          r,
          q,
          kn
        )(ef)(h)
      )

# the table that a request leaves of a table that fits fits the same facts
def Table.asked_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  r: Spec.Request
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RFasts.Table.asked(kn, r), s) == True{}: Bool}:
  h => Lists.Bool.by(
    b => {
      RContents.Known.fit(
        Shared.Bool.when(RKnown.Known(), b, u => RKnown.Known.none(), u => kn),
        s
      )
        == True{}: Bool
    },
    RFacts.Request.is_start(r),
    et => {==},
    ef => h
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

# no vote of the node sits at a fact that is put before facts, when it is
# there (w), if none sits at the fact
def Sits.put(
  +g: RFacts.Seat,
  +f: Types.Fact,
  +fs: List<&2, Types.Fact>,
  w: Bool
) -> {
  RFasts.Fact.sits(g, f) == False{}: Bool
} -> {
  Shared.List.some(
    ~Types.Fact,
    ~RFacts.Seat,
    ~RFasts.Fact.sits,
    List.filter.put(Types.Fact, f, fs, w),
    g
  )
    == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, fs, g): Bool
}:
  match w:
    case True{}:
      e => (
        %Equal.sym(Bool, RFasts.Fact.sits(g, f), False{}, e): {List.any.if(u => Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, fs, g), _) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, fs, g): Bool}
        {==})
    case False{}:
      e => {==}

# a work may act on a vote of the node at a step whose slot waits
def Sits.waits(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  f: Types.Fact
) -> {
  RFasts.Fact.sits(RFacts.Seat{name, Types.Step.At{c, k, t}}, f) == True{}: Bool
} -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == True{}: Bool
} -> {RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f) == True{}: Bool}:
  match f:
    case Types.Fact.Ask{a}:
      h => w => Empty.absurd(
        {
          RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, Types.Fact.Ask{a}) == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Types.Fact.Vote{+v, +st2, +x2}:
      h => w => (
        %Equal.sym(Types.Step, st2, Types.Step.At{c, k, t}, Step.same_sound(st2, Types.Step.At{c, k, t})(Shared.List.all.if_rest(String.eq(v, name), u => RFasts.Step.same(st2, Types.Step.At{c, k, t}))(h))): {RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, Types.Fact.Vote{v, _, x2}) == True{}: Bool}
        w)

# the facts that a work may act on hold each vote of the node at a step
# whose slot waits
def Sits.open(
  +s: RFacts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  fs: List<&2, Types.Fact>
) -> {
  RKnown.Slot.waits(RLines.Line.state(s, c), k) == True{}: Bool
} -> {
  Shared.List.some(
    ~Types.Fact,
    ~RFacts.Seat,
    ~RFasts.Fact.sits,
    RKnown.Open.of(fs, RKnown.Scene{RKnown.Known.none(), s}),
    RFacts.Seat{name, Types.Step.At{c, k, t}}
  )
    == Shared.List.some(
      ~Types.Fact,
      ~RFacts.Seat,
      ~RFasts.Fact.sits,
      fs,
      RFacts.Seat{name, Types.Step.At{c, k, t}}
    ): Bool
}:
  match fs:
    case Nil{}:
      w => {==}
    case Con{+f, +rest}:
      +w => Lists.Bool.by(
        b => {
          RFasts.Fact.sits(RFacts.Seat{name, Types.Step.At{c, k, t}}, f) == b: Bool
        } -> {
          Shared.List.some(
            ~Types.Fact,
            ~RFacts.Seat,
            ~RFasts.Fact.sits,
            List.filter.put(
              Types.Fact,
              f,
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f)
            ),
            RFacts.Seat{name, Types.Step.At{c, k, t}}
          )
            == Shared.List.some(
              ~Types.Fact,
              ~RFacts.Seat,
              ~RFasts.Fact.sits,
              f <> rest,
              RFacts.Seat{name, Types.Step.At{c, k, t}}
            ): Bool
        },
        RFasts.Fact.sits(RFacts.Seat{name, Types.Step.At{c, k, t}}, f),
        et => eq => (
          %Equal.sym(Bool, RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f), True{}, Sits.waits(s, name, c, k, t, f)(eq)(w)): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, List.filter.put(Types.Fact, f, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), _), RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, f <> rest, RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}
          %Sits.open(s, name, c, k, t, rest)(w): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, f <> RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RFacts.Seat{name, Types.Step.At{c, k, t}}) == List.any.if(u => _, RFasts.Fact.sits(RFacts.Seat{name, Types.Step.At{c, k, t}}, f)): Bool}
          {==}),
        ef => +eq => Equal.trans(
          Bool,
          Shared.List.some(
            ~Types.Fact,
            ~RFacts.Seat,
            ~RFasts.Fact.sits,
            List.filter.put(
              Types.Fact,
              f,
              RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
              RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f)
            ),
            RFacts.Seat{name, Types.Step.At{c, k, t}}
          ),
          Shared.List.some(
            ~Types.Fact,
            ~RFacts.Seat,
            ~RFasts.Fact.sits,
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
            RFacts.Seat{name, Types.Step.At{c, k, t}}
          ),
          Shared.List.some(
            ~Types.Fact,
            ~RFacts.Seat,
            ~RFasts.Fact.sits,
            f <> rest,
            RFacts.Seat{name, Types.Step.At{c, k, t}}
          ),
          Sits.put(
            RFacts.Seat{name, Types.Step.At{c, k, t}},
            f,
            RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}),
            RKnown.Fact.waits(RKnown.Scene{RKnown.Known.none(), s}, f)
          )(eq),
          (
            %Equal.sym(Bool, RFasts.Fact.sits(RFacts.Seat{name, Types.Step.At{c, k, t}}, f), False{}, eq): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RKnown.Open.of(rest, RKnown.Scene{RKnown.Known.none(), s}), RFacts.Seat{name, Types.Step.At{c, k, t}}) == List.any.if(u => Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, rest, RFacts.Seat{name, Types.Step.At{c, k, t}}), _): Bool}
            Sits.open(s, name, c, k, t, rest)(w))
        )
      )({==})

# Seat.cast, read through a table that fits, is Facts.cast
def Seat.cast_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +name: String,
  st: Types.Step
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RFasts.Seat.cast(kn, s, name, st) == RFacts.Facts.cast(s, name, st): Bool}:
  match st:
    case Types.Step.Broken{}:
      h => Seats.cast_eq(RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.Broken{}})
    case Types.Step.At{+c, +k, +t}:
      +h => Equal.trans(
        Bool,
        RFasts.Seat.cast(kn, s, name, Types.Step.At{c, k, t}),
        Shared.List.some(
          ~Types.Fact,
          ~RFacts.Seat,
          ~RFasts.Fact.sits,
          RFacts.Facts.list(s),
          RFacts.Seat{name, Types.Step.At{c, k, t}}
        ),
        RFacts.Facts.cast(s, name, Types.Step.At{c, k, t}),
        (
          %Equal.sym(Maybe<&2, RLines.State>, RKnown.Known.state(kn, s, c), RLines.Line.state(s, c), Knowns.Known.state_ok(kn, s, c)(Knowns.Fit.ok(kn, s)(h))): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, Shared.Bool.when(List<&2, Types.Fact>, RKnown.Slot.waits(_, k), u => RKnown.Known.facts(kn, s), u => RFacts.Facts.list(s)), RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}
          Lists.Bool.by(b => {RKnown.Slot.waits(RLines.Line.state(s, c), k) == b: Bool} -> {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, Shared.Bool.when(List<&2, Types.Fact>, b, u => RKnown.Known.facts(kn, s), u => RFacts.Facts.list(s)), RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}, RKnown.Slot.waits(RLines.Line.state(s, c), k), et => ew => Lists.Maybe.by(List<&2, Types.Fact>, m => {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RKnown.Open.or(m, s), RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}, RKnown.Known.open(kn), en => {==}, +fs => es => (
              %Equal.sym(List<&2, Types.Fact>, fs, RKnown.Open.of(RFacts.Facts.list(s), RKnown.Scene{RKnown.Known.none(), s}), Knowns.Known.open_fit(kn, s, fs)(h)(es)): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, _, RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}
              Sits.open(s, name, c, k, t, RFacts.Facts.list(s))(ew))), ef => ew => {==})({==})),
        Seats.cast_eq(RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}})
      )

# What a deed leaves of the table
# -------------------------------

# the table kn after a ballot for the slot k of the line c, where s is the
# facts with the ballot, before the facts that a work may act on join it;
# the run that continues the line reads the facts w, if known
def Table.mid(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  w: Maybe<&2, List<&2, Types.Fact>>
) -> RKnown.Known():
  RKnown.Known.learn(RContents.Known.grow(kn, RKnown.Known.cast(kn, s, c, k, w), s, c), s, c)

# the table that a ballot leaves of a table that fits, before the facts that
# a work may act on join it, is right for the facts with the ballot
def Table.mid_ok(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.ok(
    Table.mid(
      kn,
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      c,
      k,
      RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
    ),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  )
    == True{}: Bool
}:
  +h => (
    %Equal.sym(RKnown.Known(), RKnown.Known.cast(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k, RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})), RKnown.Known.cast(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k, None{}), Knowns.Known.cast_walk(kn, name, s, c, k, t, x)(h)): {RContents.Known.ok(RKnown.Known.learn(RContents.Known.grow(kn, _, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})) == True{}: Bool}
    Knowns.Known.learn_ok(RContents.Known.grow(kn, RKnown.Known.cast(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k, None{}), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c)(Knowns.Known.grow_ok(kn, RKnown.Known.cast(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k, None{}), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c)(Knowns.Known.cast_ok(kn, name, s, c, k, t, x)(Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h)))))

# the table that a ballot leaves, before the facts that a work may act on
# join it, holds no facts for a work
def Table.mid_shut(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  +c: Ledgers.Line,
  +k: Nat,
  +w: Maybe<&2, List<&2, Types.Fact>>
) -> {RKnown.Known.shelf(Table.mid(kn, s, c, k, w)) == None{}: Maybe<&2, RKnown.Kept>}:
  (
    %Knowns.Known.learn_open(RContents.Known.grow(kn, RKnown.Known.cast(kn, s, c, k, w), s, c), s, c): {_ == None{}: Maybe<&2, RKnown.Kept>}
    %Knowns.Known.grow_open(Maybe.is_some(&2, Nat, RKnown.Known.depth(RKnown.Known.cast(kn, s, c, k, w), c, Nat.sub(RContents.State.count(RKnown.Known.find(kn, c)), 1n))), RContents.State.count(RKnown.Known.find(kn, c)), RContents.State.count(RKnown.Known.find(RKnown.Known.cast(kn, s, c, k, w), c)), RKnown.Known.cast(kn, s, c, k, w), s, c): {_ == None{}: Maybe<&2, RKnown.Kept>}
    Knowns.Known.cast_shut(kn, s, c, k, w))

# the table that a ballot at the step st leaves of a table that fits fits
# the facts with the ballot
def Table.voted_fit(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  st: Types.Step,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.fit(
    RFasts.Table.voted(
      kn,
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x}),
      st,
      Types.Fact.Vote{name, st, x}
    ),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x})
  )
    == True{}: Bool
}:
  match st:
    case Types.Step.Broken{}:
      h => {==}
    case Types.Step.At{+c, +k, +t}:
      +h => Knowns.Known.moved_fit(
        Table.mid(
          kn,
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          c,
          k,
          RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
        ),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        RKnown.Known.walk.if(
          RKnown.Known.safe(
            c,
            RKnown.Known.find(kn, c),
            RKnown.Known.find(kn, RKnown.Known.root(c)),
            k
          ),
          RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
        ),
        Nat.max(
          RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          RKnown.Shelf.top(RKnown.Known.shelf(kn))
        )
      )(
        Table.mid_ok(kn, name, s, c, k, t, x)(h)
      )(
        Table.mid_shut(
          kn,
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          c,
          k,
          RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
        )
      )(
        Knowns.Voted.moved_ok(kn, name, s, c, k, t, x)(h)
      )(Knowns.Voted.top(kn, name, s, c, k, t, x)(h))

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
    case Some{RWorks.Plan{+st, +x}}:
      Shared.Bool.when(
        RKnown.Known(),
        RFacts.Facts.cast(s, name, st),
        u => kn,
        u => RFasts.Table.voted(
          kn,
          RFacts.Facts.add(s, Types.Fact.Vote{name, st, x}),
          st,
          Types.Fact.Vote{name, st, x}
        )
      )

# the fast node after a work that plans the ballot m, with a table that
# fits: its facts are those that RWorks.Work.cast gives, and its table is
# Table.cast
def Fast.works_at_eq(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  m: Maybe<&2, RWorks.Plan>
) -> {
  RContents.Known.fit(kn, fs) == True{}: Bool
} -> {
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
      Table.cast(kn, fs, name, m)
    }: RFasts.Fast
}:
  match m:
    case None{}:
      h => {==}
    case Some{RWorks.Plan{+st, +x}}:
      h => (
        %Equal.sym(Bool, RFasts.Seat.cast(kn, fs, name, st), RFacts.Facts.cast(fs, name, st), Seat.cast_fit(kn, fs, name, st)(h)): {RFasts.Fast.casts.if(_, name, ws, ms, fs, ps, kn, st, x) == RFasts.Fast{Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, Some{RWorks.Plan{st, x}}), ps}, Table.cast(kn, fs, name, Some{RWorks.Plan{st, x}})}: RFasts.Fast}
        Lists.Bool.by(b => {RFasts.Fast.casts.if(b, name, ws, ms, fs, ps, kn, st, x) == RFasts.Fast{Nodes.Raw{name, ws, ms, False{}, Shared.Bool.when(RFacts.Plain(), b, u => fs, u => RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x})), ps}, Shared.Bool.when(RKnown.Known(), b, u => kn, u => RFasts.Table.voted(kn, RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x}), st, Types.Fact.Vote{name, st, x}))}: RFasts.Fast}, RFacts.Facts.cast(fs, name, st), et => {==}, ef => {==}))

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
  RContents.Known.fit(kn, fs) == True{}: Bool
} -> {
  RFasts.Fast{
    Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
    Table.cast(kn, fs, name, m)
  }
    == RFasts.Fast.works.at(name, ws, ms, fs, ps, kn, m): RFasts.Fast
}:
  h => Equal.sym(
    RFasts.Fast,
    RFasts.Fast.works.at(name, ws, ms, fs, ps, kn, m),
    RFasts.Fast{
      Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
      Table.cast(kn, fs, name, m)
    },
    Fast.works_at_eq(name, ws, ms, fs, ps, kn, m)(h)
  )

# the table that a work leaves of a table that fits fits the facts after the
# work
def Table.cast_fit(
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  m: Maybe<&2, RWorks.Plan>
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.fit(
    Table.cast(kn, Facts.Facts.crit(s), name, m),
    RWorks.Work.cast(Facts.Facts.crit(s), name, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      h => h
    case Some{RWorks.Plan{+st, +x}}:
      +h => Lists.Bool.by(
        b => {
          RContents.Known.fit(
            Shared.Bool.when(
              RKnown.Known(),
              b,
              u => kn,
              u => RFasts.Table.voted(
                kn,
                RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x}),
                st,
                Types.Fact.Vote{name, st, x}
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
        et => h,
        ef => Table.voted_fit(kn, name, s, st, x)(h)
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

# the table of a fast node fits after a work
def Fast.works_fit(
  st: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  +okr: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  RContents.Known.fit(kn, fs) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.works(name, ws, ms, st, fs, ps, kn)) == True{}: Bool}:
  match st:
    case True{}:
      h => h
    case False{}:
      +h => (
        %Fast.works_at_sym(name, ws, ms, fs, ps, RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), RWorks.Work.plan(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), fs, name))(Learn.if_fit(RFasts.Table.read(kn), kn, fs)(h)): {RFasts.Fast.ok(_) == True{}: Bool}
        Table.cast_fit(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), name, Impl.Node.set(name, fs, ps, okr), RWorks.Work.plan(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), fs, name))(Learn.if_fit(RFasts.Table.read(kn), kn, fs)(h)))

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
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Connect{w}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Leave{w}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Ask{+i, +q}:
      +okr => +ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, i, q), RFacts.Facts.asked(fs, i, q), Asked.ask_fit(kn, fs, i, q)(ok)): {RFasts.Fast.ok(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, RFasts.Table.asked(kn, q), _, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))))) == True{}: Bool}
        Fast.asks_fit(Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), name, ws, ms, st, fs, ps, i, q, q, RFasts.Table.asked(kn, q), okr)(Table.asked_fit(kn, fs, q)(ok))(et => (
          %Equal.sym(Bool, RFacts.Request.is_start(q), True{}, et): {RContents.Known.fit(Shared.Bool.when(RKnown.Known(), _, u => RKnown.Known.none(), u => kn), RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, q)})) == True{}: Bool}
          {==})))
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Sync{from}:
      okr => ok => {==}
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      +okr => +ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), RFacts.Facts.asked(fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), Asked.ask_fit(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}})(ok)): {RFasts.Fast.ok(RFasts.Fast.asks.to(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, kn, _, Spec.Request.Write{b, p, None{}}, Bool.not(st))) == True{}: Bool}
        Fast.asks_fit(Bool.not(st), name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Spec.Request.Write{b, p, None{}}, kn, okr)(ok)(et => Empty.absurd({RContents.Known.fit(kn, RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}})})) == True{}: Bool}, Shared.Bool.false_ne_true(et))))
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Unmount{a}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Work{}:
      +okr => ok => Fast.works_fit(st, name, ws, ms, fs, ps, kn, okr)(ok)
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Drop{}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Stop{force}:
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
  +kn: RKnown.Known()
) -> {
  RContents.Known.fit(kn, fs) == True{}: Bool
} -> {
  RFasts.Fast.raw(
    RFasts.Fast.works(name, ws, ms, st, fs, ps, kn)
  )
    == Nodes.Raw.works(name, ws, ms, st, fs, ps): Nodes.Raw
}:
  match st:
    case True{}:
      h => {==}
    case False{}:
      +h => (
        %Fast.works_at_sym(name, ws, ms, fs, ps, RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), RWorks.Work.plan(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), fs, name))(Learn.if_fit(RFasts.Table.read(kn), kn, fs)(h)): {RFasts.Fast.raw(_) == Nodes.Raw.works(name, ws, ms, False{}, fs, ps): Nodes.Raw}
        Equal.cong(Maybe<&2, RWorks.Plan>, Nodes.Raw, m => Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps}, RWorks.Work.plan(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), fs, name), RWorks.Work.plan(RKnown.Known.none(), fs, name), Knowns.Work.plan_ok(RFasts.Learn.if(RFasts.Table.read(kn), kn, fs), fs, name)(Learn.if_fit(RFasts.Table.read(kn), kn, fs)(h))))

# the state of a fast node with a right table after a deed is the state that
# Nodes.Raw.does gives: a fast node does what a node does
def Fast.does_raw(
  f: RFasts.Fast,
  a: Nodes.Act
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.raw(RFasts.Fast.does(f, a)) == Nodes.Raw.does(RFasts.Fast.raw(f), a): Nodes.Raw}:
  match f a:
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Connect{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Leave{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Ask{+i, +q}:
      ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, i, q), RFacts.Facts.asked(fs, i, q), Asked.ask_fit(kn, fs, i, q)(ok)): {RFasts.Fast.raw(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, RFasts.Table.asked(kn, q), _, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))))) == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))): Nodes.Raw}
        Fast.asks_to_raw(Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), name, ws, ms, st, fs, ps, i, q, q, RFasts.Table.asked(kn, q)))
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Sync{from}:
      ok => {==}
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), RFacts.Facts.asked(fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), Asked.ask_fit(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}})(ok)): {RFasts.Fast.raw(RFasts.Fast.asks.to(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, kn, _, Spec.Request.Write{b, p, None{}}, Bool.not(st))) == Nodes.Raw.asks(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Bool.not(st)): Nodes.Raw}
        Fast.asks_to_raw(Bool.not(st), name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Spec.Request.Write{b, p, None{}}, kn))
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Unmount{a}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Work{}:
      ok => Fast.works_raw(st, name, ws, ms, fs, ps, kn)(ok)
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Drop{}:
      ok => Equal.cong(
        List<&2, Hashes.Hash>,
        Nodes.Raw,
        hs => Nodes.Raw{name, ws, ms, st, fs, RParts.Parts.only(ps, hs)},
        Nodes.Needs.of(kn, fs, name, ms),
        Nodes.Needs.of(RKnown.Known.none(), fs, name, ms),
        Needs.of_ok(kn, fs, name, ms)(Knowns.Fit.ok(kn, fs)(ok))
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Stop{force}:
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
    case RFasts.Fast{r, kn}:
      {==}

# the table of a fast node that learns the states of a line stays right
def Fast.learn_ok(
  f: RFasts.Fast,
  +c: Ledgers.Line
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.learn(f, c)) == True{}: Bool}:
  match f:
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.Known.warm_fit(
        RKnown.Known.learn(kn, Nodes.Raw.facts(r), c),
        Nodes.Raw.facts(r),
        c
      )(Knowns.Known.learn_fit(kn, Nodes.Raw.facts(r), c)(ok))

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
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.Answer.of_ok(
        kn,
        Nodes.Raw.facts(r),
        q
      )(Knowns.Fit.ok(kn, Nodes.Raw.facts(r))(ok))

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
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.Content.read_ok(
        kn,
        Nodes.Raw.facts(r),
        c,
        k,
        p
      )(Knowns.Fit.ok(kn, Nodes.Raw.facts(r))(ok))

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
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.View.at_ok(
        kn,
        Nodes.Raw.facts(r),
        w,
        b,
        p
      )(Knowns.Fit.ok(kn, Nodes.Raw.facts(r))(ok))
