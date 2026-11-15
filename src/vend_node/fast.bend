import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
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
import ./seen.bend as Seens
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
    RFasts.Learn.line(kn, s, RWorks.Request.line(kn, all, r)),
    s,
    r
  )(Learn.line_ok(kn, s, RWorks.Request.line(kn, all, r))(ok))

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
    RKnown.Known.shelf(RFasts.Learn.line(kn, s, RWorks.Request.line(kn, all, r))),
    RKnown.Known.shelf(RFasts.Learn.request(kn, s, all, r)),
    Learn.line_open(kn, s, RWorks.Request.line(kn, all, r)),
    Learn.merge_open(RFasts.Learn.line(kn, s, RWorks.Request.line(kn, all, r)), s, r)
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

# a fast node whose table fits its state, after it took in a fresh ask that
# a work may act on, holds a table that fits
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
  RLines.Request.fresh(Facts.Facts.crit(s), i, r) == True{}: Bool
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
    RFacts.Facts.asked(s, i, r),
    RLines.Request.fresh(s, i, r)
  )
    == RFacts.Facts.ask(name, s, i, r): RFacts.Plain()
}:
  Lists.Bool.by(
    b => {
      RFasts.Asked.take(
        name,
        s,
        RFacts.Facts.asked(s, i, r),
        b
      )
        == RFacts.Facts.ask(name, s, i, r): RFacts.Plain()
    },
    RLines.Request.fresh(s, i, r),
    et => Equal.sym(
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
        Knowns.Collided.kept(s, i, 1n+RFacts.Seq.peak(RFacts.Facts.list(s)), r)(et)
      )
    ),
    ef => {==}
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
    go,
    RLines.Request.fresh(fs, i, r)
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
        RFasts.Asked.take(name, fs, RFacts.Facts.asked(fs, i, r), RLines.Request.fresh(fs, i, r)),
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
    RFasts.Fast.asks.to(
      name,
      ws,
      ms,
      st,
      fs,
      ps,
      kn,
      RFacts.Facts.asked(fs, i, r),
      q,
      go,
      RLines.Request.fresh(fs, i, r)
    )
  )
    == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go): Nodes.Raw
}:
  Equal.trans(
    Nodes.Raw,
    RFasts.Fast.raw(
      RFasts.Fast.asks.to(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        kn,
        RFacts.Facts.asked(fs, i, r),
        q,
        go,
        RLines.Request.fresh(fs, i, r)
      )
    ),
    RFasts.Fast.asks(
      name,
      ws,
      ms,
      st,
      fs,
      ps,
      RFacts.Facts.asked(fs, i, r),
      go,
      RLines.Request.fresh(fs, i, r)
    ),
    Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go),
    Fast.asked_raw(
      RFasts.Fast.asks(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        RFacts.Facts.asked(fs, i, r),
        go,
        RLines.Request.fresh(fs, i, r)
      ),
      RFasts.Table.asked(kn, RLines.Request.fresh(fs, i, r)),
      RFasts.Table.read(RFasts.Table.asked(kn, RLines.Request.fresh(fs, i, r))),
      q,
      RFasts.Asked.fact(RFacts.Facts.asked(fs, i, r), go)
    ),
    Fast.asks_raw(go, name, ws, ms, st, fs, ps, i, r)
  )

# the table that a request leaves of a table that fits fits the same facts
def Table.asked_fit(
  +kn: RKnown.Known(),
  +s: RFacts.Plain(),
  b: Bool
) -> {
  RContents.Known.fit(kn, s) == True{}: Bool
} -> {RContents.Known.fit(RFasts.Table.asked(kn, b), s) == True{}: Bool}:
  match b:
    case False{}:
      x => Knowns.Fit.none(s)
    case True{}:
      x => x

# the table of a fast node that takes in a request, when it may (go), fits,
# when the table kn fits its state before
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
} -> {
  RFasts.Fast.ok(
    RFasts.Fast.asks.to(
      name,
      ws,
      ms,
      st,
      fs,
      ps,
      kn,
      RFacts.Facts.asked(fs, i, r),
      q,
      go,
      RLines.Request.fresh(fs, i, r)
    )
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      h => Fast.asked_fit(
        Nodes.Raw{name, ws, ms, st, fs, ps},
        RFasts.Table.asked(kn, RLines.Request.fresh(fs, i, r)),
        RFasts.Table.read(RFasts.Table.asked(kn, RLines.Request.fresh(fs, i, r))),
        q
      )(Table.asked_fit(kn, fs, RLines.Request.fresh(fs, i, r))(h))
    case True{}:
      +h => Lists.Bool.by(
        y => {
          RFasts.Fast.ok(
            RFasts.Fast.asked(
              Nodes.Raw{
                name,
                ws,
                ms,
                st,
                RFasts.Asked.take(name, fs, RFacts.Facts.asked(fs, i, r), y),
                Nodes.Kept.with(ps, Nodes.Request.content(r))
              },
              RFasts.Table.asked(kn, y),
              RFasts.Table.read(RFasts.Table.asked(kn, y)),
              q,
              Some{Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)}}
            )
          )
            == True{}: Bool
        },
        RLines.Request.fresh(fs, i, r),
        et => Fast.asked_join(
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
        )(et)(h),
        ef => Knowns.Fit.none(
          RFacts.Facts.take(name, fs, Types.Fact.Ask{RFacts.Facts.asked(fs, i, r)})
        )
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
          %Equal.sym(Bool, RKnown.Vote.waits(kn, s, c, k), RKnown.Slot.waits(RLines.Line.state(s, c), k), Knowns.Vote.waits_ok(kn, s, c, k)(Knowns.Fit.ok(kn, s)(h))): {Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, Shared.Bool.when(List<&2, Types.Fact>, _, u => RKnown.Known.facts(kn, s), u => RFacts.Facts.list(s)), RFacts.Seat{name, Types.Step.At{c, k, t}}) == Shared.List.some(~Types.Fact, ~RFacts.Seat, ~RFasts.Fact.sits, RFacts.Facts.list(s), RFacts.Seat{name, Types.Step.At{c, k, t}}): Bool}
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
  Facts.Facts.has(s, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}) == False{}: Bool
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
  +h => hf => Knowns.Known.learn_ok(
    RContents.Known.grow(
      kn,
      RKnown.Known.cast(
        kn,
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        c,
        k,
        RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
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
        k,
        RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
      ),
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      c
    )(Knowns.Known.cast_fits(kn, name, s, c, k, t, x)(h)(hf))
  )

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
    %Knowns.Known.grow_open(Maybe.is_some(&2, Nat, RKnown.Known.depth(RKnown.Known.cast(kn, s, c, k, w), c, Nat.sub(RContents.Known.tally(kn, c), 1n))), RContents.Known.tally(kn, c), RContents.Known.tally(RKnown.Known.cast(kn, s, c, k, w), c), RKnown.Known.cast(kn, s, c, k, w), s, c): {_ == None{}: Maybe<&2, RKnown.Kept>}
    Knowns.Known.cast_shuts(kn, s, c, k, w))

# the table that a ballot for the slot k of the line c leaves of a table
# that fits, as Table.move leaves it, fits the facts with the ballot
def Table.move_fit(
  sound: Bool,
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RKnown.Known.sound(kn, c, k) == sound: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RFacts.Facts.cast(Facts.Facts.crit(s), name, Types.Step.At{c, k, t}) == False{}: Bool
} -> {
  RContents.Known.fit(
    RFasts.Table.move(
      sound,
      kn,
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      c,
      k,
      Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
    ),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  )
    == True{}: Bool
}:
  hs => +h => hc =>
    %hs: {
      RContents.Known.fit(
        RKnown.Known.moved(
          Table.mid(
            kn,
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c,
            k,
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          ),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          RKnown.Known.walk.if(
            _,
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          ),
          Nat.max(
            RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            RKnown.Shelf.top(RKnown.Known.shelf(kn))
          ),
          RKnown.Shelf.tops(RKnown.Known.shelf(kn)),
          RKnown.Shelf.merges(RKnown.Known.shelf(kn)),
          RKnown.Shelf.roots(RKnown.Known.shelf(kn))
        ),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
      )
        == True{}: Bool
    }
    %Equal.sym(
      Bool,
      RKnown.Known.sound(kn, c, k),
      RKnown.Known.safe(
        c,
        RKnown.Known.find(kn, c),
        RKnown.Known.find(kn, RKnown.Known.root(c)),
        k
      ),
      Seens.Known.sound_eq(kn, c, k)
    ): {
      RContents.Known.fit(
        RKnown.Known.moved(
          Table.mid(
            kn,
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            c,
            k,
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          ),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          RKnown.Known.walk.if(
            _,
            RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          ),
          Nat.max(
            RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            RKnown.Shelf.top(RKnown.Known.shelf(kn))
          ),
          RKnown.Shelf.tops(RKnown.Known.shelf(kn)),
          RKnown.Shelf.merges(RKnown.Known.shelf(kn)),
          RKnown.Shelf.roots(RKnown.Known.shelf(kn))
        ),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
      )
        == True{}: Bool
    }
    Knowns.Known.moved_fit(
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
      ),
      RKnown.Shelf.tops(RKnown.Known.shelf(kn)),
      RKnown.Shelf.merges(RKnown.Known.shelf(kn)),
      RKnown.Shelf.roots(RKnown.Known.shelf(kn))
    )(
      Table.mid_ok(
        kn,
        name,
        s,
        c,
        k,
        t,
        x
      )(h)(Knowns.Vote.fresh(name, s, Types.Step.At{c, k, t}, x)(hc))
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
    )(
      Knowns.Voted.top(kn, name, s, c, k, t, x)(h)
    )(
      Knowns.Voted.tops(kn, name, s, c, k, t, x)(h)
    )(
      Knowns.Voted.merges(kn, name, s, c, k, t, x)(h)
    )(Knowns.Voted.roots(kn, name, s, c, k, t, x)(h))

# the table that a ballot for the slot k of the line c leaves of a table
# that fits, once it is known whether the ballot only continues the versions
# of each line (sound), fits the facts with the ballot
def Table.voted.at_fit(
  sound: Bool,
  +kn: RKnown.Known(),
  +name: String,
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +k: Nat,
  +t: Nat,
  +x: Types.Cast
) -> {
  RKnown.Known.sound(kn, c, k) == sound: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RFacts.Facts.cast(Facts.Facts.crit(s), name, Types.Step.At{c, k, t}) == False{}: Bool
} -> {
  RContents.Known.fit(
    RFasts.Table.voted.at(
      sound,
      kn,
      Facts.Facts.crit(s),
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
      c,
      k,
      Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
    ),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
  )
    == True{}: Bool
}:
  match sound:
    case True{}:
      hs => h => hc => Table.move_fit(True{}, kn, name, s, c, k, t, x)(hs)(h)(hc)
    case False{}:
      hs => +h => +hc => Lists.Bool.by(
        y => {
          RContents.Known.fit(
            RFasts.Table.kept(
              y,
              kn,
              RFacts.Facts.add(
                Facts.Facts.crit(s),
                Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
              ),
              c,
              k,
              Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}
            ),
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x})
          )
            == True{}: Bool
        },
        RKnown.Known.late(
          kn,
          Facts.Facts.crit(s),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          c,
          k
        ),
        +et => Knowns.Known.moved_fit(
          RKnown.Known.shut(kn),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          RKnown.Known.walk(kn, Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
          Nat.max(
            RFacts.Seq.of(Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
            RKnown.Shelf.top(RKnown.Known.shelf(kn))
          ),
          RKnown.Shelf.tops(RKnown.Known.shelf(kn)),
          RKnown.Shelf.merges(RKnown.Known.shelf(kn)),
          RKnown.Shelf.roots(RKnown.Known.shelf(kn))
        )(
          Knowns.Late.ok(
            kn,
            name,
            s,
            c,
            k,
            t,
            x
          )(
            Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h)
          )(
            Knowns.Known.late_ok(
              kn,
              name,
              s,
              c,
              k,
              t,
              x
            )(Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h))(et)
          )(Knowns.Vote.fresh(name, s, Types.Step.At{c, k, t}, x)(hc))
        )(
          Knowns.Known.shut_shelf(kn)
        )(
          Knowns.Late.moved_ok(
            kn,
            name,
            s,
            c,
            k,
            t,
            x
          )(
            h
          )(
            Knowns.Known.late_ok(
              kn,
              name,
              s,
              c,
              k,
              t,
              x
            )(Knowns.Fit.ok(kn, Facts.Facts.crit(s))(h))(et)
          )
        )(
          Knowns.Voted.top.at(
            RKnown.Known.shelf(kn),
            name,
            s,
            c,
            k,
            t,
            x
          )(Knowns.Fit.open(kn, Facts.Facts.crit(s))(h))
        )(
          Knowns.Voted.tops(kn, name, s, c, k, t, x)(h)
        )(
          Knowns.Voted.merges(kn, name, s, c, k, t, x)(h)
        )(Knowns.Voted.roots(kn, name, s, c, k, t, x)(h)),
        ef => Table.move_fit(False{}, kn, name, s, c, k, t, x)(hs)(h)(hc)
      )

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
  RFacts.Facts.cast(Facts.Facts.crit(s), name, st) == False{}: Bool
} -> {
  RContents.Known.fit(
    RFasts.Table.voted(
      kn,
      Facts.Facts.crit(s),
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
      h => hc => Knowns.Fit.none(
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.Broken{}, x})
      )
    case Types.Step.At{+c, +k, +t}:
      h => hc => Table.voted.at_fit(
        RKnown.Known.sound(kn, c, k),
        kn,
        name,
        s,
        c,
        k,
        t,
        x
      )({==})(h)(hc)

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
          s,
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
        Lists.Bool.by(b => {RFasts.Fast.casts.if(b, name, ws, ms, fs, ps, kn, st, x) == RFasts.Fast{Nodes.Raw{name, ws, ms, False{}, Shared.Bool.when(RFacts.Plain(), b, u => fs, u => RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x})), ps}, Shared.Bool.when(RKnown.Known(), b, u => kn, u => RFasts.Table.voted(kn, fs, RFacts.Facts.add(fs, Types.Fact.Vote{name, st, x}), st, Types.Fact.Vote{name, st, x}))}: RFasts.Fast}, RFacts.Facts.cast(fs, name, st), et => {==}, ef => {==}))

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
                Facts.Facts.crit(s),
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
        ef => Table.voted_fit(kn, name, s, st, x)(h)(ef)
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
  RContents.Known.fit(kn, s) == True{}: Bool
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
# What a fast node takes in from another node
# ------------------------------------------

# t is the facts s2, with a table that fits them
def Sync.Is(t: RFasts.Taken, s2: Facts.Facts()) -> Type:
  Exists(
    RKnown.Known(),
    kn2 => {
      t == RFasts.Taken{Facts.Facts.crit(s2), kn2}: RFasts.Taken
    }
      & {RContents.Known.fit(kn2, Facts.Facts.crit(s2)) == True{}: Bool}
  )

# a node that takes in a fact with Facts.take, and leaves no table, has the
# facts that Facts.take gives, with a table that fits them
def Sync.none_is(
  +name: String,
  +s: Facts.Facts(),
  +f: Types.Fact
) -> Sync.Is(
  RFasts.Taken{RFacts.Facts.take(name, Facts.Facts.crit(s), f), RKnown.Known.none()},
  Facts.Facts.take(name, s, f)
):
  (
    RKnown.Known.none(),
    (
      Equal.cong(
        RFacts.Plain(),
        RFasts.Taken,
        z => RFasts.Taken{z, RKnown.Known.none()},
        RFacts.Facts.take(name, Facts.Facts.crit(s), f),
        Facts.Facts.crit(Facts.Facts.take(name, s, f)),
        Equal.sym(
          RFacts.Plain(),
          Facts.Facts.crit(Facts.Facts.take(name, s, f)),
          RFacts.Facts.take(name, Facts.Facts.crit(s), f),
          Facts.Facts.take_crit(name, s, f)
        )
      ),
      Knowns.Fit.none(Facts.Facts.crit(Facts.Facts.take(name, s, f)))
    )
  )

# the table that the ballot of another voter leaves of a table that fits
# fits the facts with the ballot
def Table.heard_fit(
  +kn: RKnown.Known(),
  +s: Facts.Facts(),
  +v: String,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> {
  RContents.Known.fit(
    RFasts.Table.heard(
      kn,
      Facts.Facts.crit(s),
      RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
      v,
      st,
      Types.Fact.Vote{v, st, x}
    ),
    RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x})
  )
    == True{}: Bool
}:
  +h => Lists.Bool.by(
    z => {
      RFasts.Seat.cast(kn, Facts.Facts.crit(s), v, st) == z: Bool
    } -> {
      RContents.Known.fit(
        Shared.Bool.when(
          RKnown.Known(),
          z,
          u => RKnown.Known.none(),
          u => RFasts.Table.voted(
            kn,
            Facts.Facts.crit(s),
            RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
            st,
            Types.Fact.Vote{v, st, x}
          )
        ),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x})
      )
        == True{}: Bool
    },
    RFasts.Seat.cast(kn, Facts.Facts.crit(s), v, st),
    et => e => Knowns.Fit.none(RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x})),
    ef => e => Table.voted_fit(
      kn,
      v,
      s,
      st,
      x
    )(
      h
    )(
      Equal.trans(
        Bool,
        RFacts.Facts.cast(Facts.Facts.crit(s), v, st),
        RFasts.Seat.cast(kn, Facts.Facts.crit(s), v, st),
        False{},
        Equal.sym(
          Bool,
          RFasts.Seat.cast(kn, Facts.Facts.crit(s), v, st),
          RFacts.Facts.cast(Facts.Facts.crit(s), v, st),
          Seat.cast_fit(kn, Facts.Facts.crit(s), v, st)(h)
        ),
        e
      )
    )
  )({==})

# a node that takes in a vote has the facts that Facts.take gives, with a
# table that fits them
def Sync.vote_is(
  +name: String,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  +v: String,
  +st: Types.Step,
  +x: Types.Cast
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(
  RFasts.Sync.vote(name, Facts.Facts.crit(s), kn, v, st, x),
  Facts.Facts.take(name, s, Types.Fact.Vote{v, st, x})
):
  +h => Lists.Bool.by(
    z => {
      String.eq(v, name) == z: Bool
    } -> Sync.Is(
      Shared.Bool.when(
        RFasts.Taken,
        z,
        u => RFasts.Taken{
          RFacts.Facts.take(name, Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
          RKnown.Known.none()
        },
        u => RFasts.Sync.vote.to(
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
          Facts.Facts.crit(s),
          kn,
          v,
          st,
          Types.Fact.Vote{v, st, x}
        )
      ),
      Facts.Facts.take(name, s, Types.Fact.Vote{v, st, x})
    ),
    String.eq(v, name),
    et => e => Sync.none_is(name, s, Types.Fact.Vote{v, st, x}),
    ef => e => Lists.Equal.to(
      Facts.Facts(),
      z => Sync.Is(
        RFasts.Sync.vote.to(
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
          Facts.Facts.crit(s),
          kn,
          v,
          st,
          Types.Fact.Vote{v, st, x}
        ),
        z
      ),
      Facts.Facts.add(s, Types.Fact.Vote{v, st, x}),
      Facts.Facts.take(name, s, Types.Fact.Vote{v, st, x}),
      Equal.sym(
        Facts.Facts(),
        Facts.Facts.take(name, s, Types.Fact.Vote{v, st, x}),
        Facts.Facts.add(s, Types.Fact.Vote{v, st, x}),
        Facts.Facts.take_vote(name, s, v, st, x)(e)
      ),
      (
        RFasts.Table.heard(
          kn,
          Facts.Facts.crit(s),
          RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{v, st, x}),
          v,
          st,
          Types.Fact.Vote{v, st, x}
        ),
        ({==}, Table.heard_fit(kn, s, v, st, x)(h))
      )
    )
  )({==})

# a node that takes in an ask has the facts that Facts.take gives, with a
# table that fits them
def Sync.ask_is(
  +name: String,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  a: Types.Ask
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(
  RFasts.Sync.ask(name, Facts.Facts.crit(s), kn, a),
  Facts.Facts.take(name, s, Types.Fact.Ask{a})
):
  match a:
    case Types.Ask{+i, +n, +r}:
      +h => (
        %Equal.sym(Bool, RKnown.Known.fresh_ask(kn, Facts.Facts.crit(s), i, r), RLines.Request.fresh(Facts.Facts.crit(s), i, r), Knowns.Known.fresh_fit(kn, Facts.Facts.crit(s), i, r)(h)): Sync.Is(RFasts.Sync.ask.of(name, Facts.Facts.crit(s), kn, Types.Ask{i, n, r}, _), Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}}))
        Lists.Bool.by(z => Sync.Is(RFasts.Sync.ask.of(name, Facts.Facts.crit(s), kn, Types.Ask{i, n, r}, z), Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), RLines.Request.fresh(Facts.Facts.crit(s), i, r), +et => (RFasts.Table.asks(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), RFasts.Table.read(kn), r, Some{Types.Fact.Ask{Types.Ask{i, n, r}}}), (Equal.cong(RFacts.Plain(), RFasts.Taken, z => RFasts.Taken{z, RFasts.Table.asks(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), RFasts.Table.read(kn), r, Some{Types.Fact.Ask{Types.Ask{i, n, r}}})}, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), Equal.sym(RFacts.Plain(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), Knowns.Take.ask(name, s, i, n, r)(et))), Lists.Equal.to(RFacts.Plain(), z => {RContents.Known.fit(RFasts.Table.asks(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), RFasts.Table.read(kn), r, Some{Types.Fact.Ask{Types.Ask{i, n, r}}}), z) == True{}: Bool}, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), Equal.sym(RFacts.Plain(), Facts.Facts.crit(Facts.Facts.take(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})), RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Ask{Types.Ask{i, n, r}}), Knowns.Take.ask(name, s, i, n, r)(et)), Fast.asked_join(RFasts.Table.read(kn), name, [], [], False{}, RParts.Parts.new(), s, i, n, r, r, kn)(et)(h)))), ef => Sync.none_is(name, s, Types.Fact.Ask{Types.Ask{i, n, r}})))

# a node that takes in a fact that it may not hold has the facts that
# Facts.take gives, with a table that fits them
def Sync.new_is(
  +name: String,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  f: Types.Fact
) -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(RFasts.Sync.new(name, Facts.Facts.crit(s), kn, f), Facts.Facts.take(name, s, f)):
  match f:
    case Types.Fact.Ask{+a}:
      h => Sync.ask_is(name, s, kn, a)(h)
    case Types.Fact.Vote{+v, +st, +x}:
      h => Sync.vote_is(name, s, kn, v, st, x)(h)

# a node that takes in a fact has the facts that Facts.take gives, with a
# table that fits them, when its set is sound for it and its table fits
def Sync.take_is(
  +name: String,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  +f: Types.Fact
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(
  RFasts.Sync.take(name, RFasts.Taken{Facts.Facts.crit(s), kn}, f),
  Facts.Facts.take(name, s, f)
):
  ok => +h => Lists.Bool.by(
    z => {
      Facts.Facts.has(s, f) == z: Bool
    } -> Sync.Is(
      Shared.Bool.when(
        RFasts.Taken,
        z,
        u => RFasts.Taken{Facts.Facts.crit(s), kn},
        u => RFasts.Sync.new(name, Facts.Facts.crit(s), kn, f)
      ),
      Facts.Facts.take(name, s, f)
    ),
    Facts.Facts.has(s, f),
    et => e => Lists.Equal.to(
      Facts.Facts(),
      z => Sync.Is(RFasts.Taken{Facts.Facts.crit(s), kn}, z),
      s,
      Facts.Facts.take(name, s, f),
      Equal.sym(
        Facts.Facts(),
        Facts.Facts.take(name, s, f),
        s,
        Facts.Facts.take_held(name, s, f)(ok)(e)
      ),
      (kn, ({==}, h))
    ),
    ef => e => Sync.new_is(name, s, kn, f)(h)
  )({==})

# a node that takes in the fact f, which the other node holds under the key
# k, has the facts that Facts.take gives, with a table that fits them, when
# its set is sound for it and its table fits
def Sync.bind_is(
  +name: String,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  +k: List<&2, U32>,
  +f: Types.Fact
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(
  RFasts.Sync.bind(name, RFasts.Taken{Facts.Facts.crit(s), kn}, k, f),
  Facts.Facts.take(name, s, f)
):
  +ok => +h => Lists.Bool.by(
    z => {
      RFacts.Facts.held(Facts.Facts.crit(s), k, f) == z: Bool
    } -> Sync.Is(
      Shared.Bool.when(
        RFasts.Taken,
        z,
        u => RFasts.Taken{Facts.Facts.crit(s), kn},
        u => RFasts.Sync.take(name, RFasts.Taken{Facts.Facts.crit(s), kn}, f)
      ),
      Facts.Facts.take(name, s, f)
    ),
    RFacts.Facts.held(Facts.Facts.crit(s), k, f),
    et => e => Lists.Equal.to(
      Facts.Facts(),
      z => Sync.Is(RFasts.Taken{Facts.Facts.crit(s), kn}, z),
      s,
      Facts.Facts.take(name, s, f),
      Equal.sym(
        Facts.Facts(),
        Facts.Facts.take(name, s, f),
        s,
        Facts.Facts.take_held(name, s, f)(ok)(Facts.Facts.held_has(s, k, f)(e))
      ),
      (kn, ({==}, h))
    ),
    ef => e => Sync.take_is(name, s, kn, f)(ok)(h)
  )({==})

# Sync.binds_is, for a fact f under the key k and then the entries rest,
# once what the node has after it takes in f is known (r), with rec for rest
def Sync.binds_is.next(
  +name: String,
  +rest: List<&2, Crits.Bind<Types.Fact>>,
  +s: Facts.Facts(),
  +kn: RKnown.Known(),
  +k: List<&2, U32>,
  +f: Types.Fact,
  r: Sync.Is(
    RFasts.Sync.bind(name, RFasts.Taken{Facts.Facts.crit(s), kn}, k, f),
    Facts.Facts.take(name, s, f)
  ),
  rec: @kn2: RKnown.Known() -> {
    RContents.Known.fit(kn2, Facts.Facts.crit(Facts.Facts.take(name, s, f))) == True{}: Bool
  } -> Sync.Is(
    RFasts.Sync.binds(
      name,
      rest,
      RFasts.Taken{Facts.Facts.crit(Facts.Facts.take(name, s, f)), kn2}
    ),
    Facts.Facts.take_all(name, Crits.Binds.values(Types.Fact, rest), Facts.Facts.take(name, s, f))
  )
) -> Sync.Is(
  RFasts.Sync.binds(
    name,
    rest,
    RFasts.Sync.bind(name, RFasts.Taken{Facts.Facts.crit(s), kn}, k, f)
  ),
  Facts.Facts.take_all(name, Crits.Binds.values(Types.Fact, rest), Facts.Facts.take(name, s, f))
):
  (+kn2, p) = r
  (e, h2) = p
  Lists.Equal.to(
    RFasts.Taken,
    z => Sync.Is(
      RFasts.Sync.binds(name, rest, z),
      Facts.Facts.take_all(name, Crits.Binds.values(Types.Fact, rest), Facts.Facts.take(name, s, f))
    ),
    RFasts.Taken{Facts.Facts.crit(Facts.Facts.take(name, s, f)), kn2},
    RFasts.Sync.bind(name, RFasts.Taken{Facts.Facts.crit(s), kn}, k, f),
    Equal.sym(
      RFasts.Taken,
      RFasts.Sync.bind(name, RFasts.Taken{Facts.Facts.crit(s), kn}, k, f),
      RFasts.Taken{Facts.Facts.crit(Facts.Facts.take(name, s, f)), kn2},
      e
    ),
    rec(kn2)(h2)
  )

# a node that takes in the facts of the entries es, each under its key, has
# the facts that Facts.take_all gives, with a table that fits them, when its
# set is sound for it and its table fits
def Sync.binds_is(
  +name: String,
  es: List<&2, Crits.Bind<Types.Fact>>,
  +s: Facts.Facts(),
  +kn: RKnown.Known()
) -> {
  Facts.Facts.ok(name, s) == True{}: Bool
} -> {
  RContents.Known.fit(kn, Facts.Facts.crit(s)) == True{}: Bool
} -> Sync.Is(
  RFasts.Sync.binds(name, es, RFasts.Taken{Facts.Facts.crit(s), kn}),
  Facts.Facts.take_all(name, Crits.Binds.values(Types.Fact, es), s)
):
  match es:
    case Nil{}:
      ok => h => (kn, ({==}, h))
    case Con{Crits.Bind{+k, +f}, +rest}:
      +ok => h => Sync.binds_is.next(
        name,
        rest,
        s,
        kn,
        k,
        f,
        Sync.bind_is(name, s, kn, k, f)(ok)(h),
        +kn2 => h2 => Sync.binds_is(
          name,
          rest,
          Facts.Facts.take(name, s, f),
          kn2
        )(Facts.Facts.take_ok(name, s, f)(ok))(h2)
      )

# the state of a fast node after a Sync whose facts are s2, with a table
# that fits them, is the state with the map of s2
def Fast.synced_raw(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +ps: RParts.Parts,
  +t: RFasts.Taken,
  +s2: Facts.Facts(),
  r: Sync.Is(t, s2)
) -> {
  RFasts.Fast.raw(
    RFasts.Fast.synced(name, ws, ms, st, ps, t)
  )
    == Nodes.Raw{name, ws, ms, st, Facts.Facts.crit(s2), ps}: Nodes.Raw
}:
  (+kn2, p) = r
  (e, h) = p
  Lists.Equal.to(
    RFasts.Taken,
    z => {
      RFasts.Fast.raw(
        RFasts.Fast.synced(name, ws, ms, st, ps, z)
      )
        == Nodes.Raw{name, ws, ms, st, Facts.Facts.crit(s2), ps}: Nodes.Raw
    },
    RFasts.Taken{Facts.Facts.crit(s2), kn2},
    t,
    Equal.sym(RFasts.Taken, t, RFasts.Taken{Facts.Facts.crit(s2), kn2}, e),
    {==}
  )

# the table of a fast node after a Sync whose facts are s2, with a table
# that fits them, fits
def Fast.synced_fit(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +ps: RParts.Parts,
  +t: RFasts.Taken,
  +s2: Facts.Facts(),
  r: Sync.Is(t, s2)
) -> {RFasts.Fast.ok(RFasts.Fast.synced(name, ws, ms, st, ps, t)) == True{}: Bool}:
  (+kn2, p) = r
  (e, h) = p
  Lists.Equal.to(
    RFasts.Taken,
    z => {RFasts.Fast.ok(RFasts.Fast.synced(name, ws, ms, st, ps, z)) == True{}: Bool},
    RFasts.Taken{Facts.Facts.crit(s2), kn2},
    t,
    Equal.sym(RFasts.Taken, t, RFasts.Taken{Facts.Facts.crit(s2), kn2}, e),
    h
  )

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
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, i, q), RFacts.Facts.asked(fs, i, q), Asked.ask_fit(kn, fs, i, q)(ok)): {RFasts.Fast.ok(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, _, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), RKnown.Known.fresh_ask(kn, fs, i, q))) == True{}: Bool}
        %Equal.sym(Bool, RKnown.Known.fresh_ask(kn, fs, i, q), RLines.Request.fresh(fs, i, q), Knowns.Known.fresh_fit(kn, fs, i, q)(ok)): {RFasts.Fast.ok(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, RFacts.Facts.asked(fs, i, q), q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), _)) == True{}: Bool}
        Fast.asks_fit(Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), name, ws, ms, st, fs, ps, i, q, q, kn, okr)(ok))
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Sync{Nodes.Raw{name2, ws2, ms2, st2, +fs2, +ps2}}:
      +okr => ok => Fast.synced_fit(
        name,
        ws,
        ms,
        st,
        RParts.Parts.join(ps, ps2),
        RFasts.Sync.binds(name, Crits.Crit.entries(Types.Fact, fs2), RFasts.Taken{fs, kn}),
        Facts.Facts.take_all(name, RFacts.Facts.list(fs2), Impl.Node.set(name, fs, ps, okr)),
        Sync.binds_is(
          name,
          Crits.Crit.entries(Types.Fact, fs2),
          Impl.Node.set(name, fs, ps, okr),
          kn
        )(Impl.Node.sound(name, fs, ps, okr))(ok)
      )
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      +okr => +ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), RFacts.Facts.asked(fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), Asked.ask_fit(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}})(ok)): {RFasts.Fast.ok(RFasts.Fast.asks.to(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, kn, _, Spec.Request.Write{b, p, None{}}, Bool.not(st), True{})) == True{}: Bool}
        Fast.asks_fit(Bool.not(st), name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Spec.Request.Write{b, p, None{}}, kn, okr)(ok))
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
  Nodes.Raw.ok(RFasts.Fast.raw(f)) == True{}: Bool
} -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {RFasts.Fast.raw(RFasts.Fast.does(f, a)) == Nodes.Raw.does(RFasts.Fast.raw(f), a): Nodes.Raw}:
  match f a:
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Connect{w}:
      okr => ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Leave{w}:
      okr => ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Ask{+i, +q}:
      okr => +ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, i, q), RFacts.Facts.asked(fs, i, q), Asked.ask_fit(kn, fs, i, q)(ok)): {RFasts.Fast.raw(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, _, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), RKnown.Known.fresh_ask(kn, fs, i, q))) == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))): Nodes.Raw}
        %Equal.sym(Bool, RKnown.Known.fresh_ask(kn, fs, i, q), RLines.Request.fresh(fs, i, q), Knowns.Known.fresh_fit(kn, fs, i, q)(ok)): {RFasts.Fast.raw(RFasts.Fast.asks.to(name, ws, ms, st, fs, ps, kn, RFacts.Facts.asked(fs, i, q), q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), _)) == Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, q, Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))): Nodes.Raw}
        Fast.asks_to_raw(Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))), name, ws, ms, st, fs, ps, i, q, q, kn))
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Sync{Nodes.Raw{name2, ws2, ms2, st2, +fs2, +ps2}}:
      +okr => ok => Equal.trans(
        Nodes.Raw,
        RFasts.Fast.raw(
          RFasts.Fast.synced(
            name,
            ws,
            ms,
            st,
            RParts.Parts.join(ps, ps2),
            RFasts.Sync.binds(name, Crits.Crit.entries(Types.Fact, fs2), RFasts.Taken{fs, kn})
          )
        ),
        Nodes.Raw{
          name,
          ws,
          ms,
          st,
          Facts.Facts.crit(
            Facts.Facts.take_all(name, RFacts.Facts.list(fs2), Impl.Node.set(name, fs, ps, okr))
          ),
          RParts.Parts.join(ps, ps2)
        },
        Nodes.Raw{
          name,
          ws,
          ms,
          st,
          RFacts.Facts.take_all(name, RFacts.Facts.list(fs2), fs),
          RParts.Parts.join(ps, ps2)
        },
        Fast.synced_raw(
          name,
          ws,
          ms,
          st,
          RParts.Parts.join(ps, ps2),
          RFasts.Sync.binds(name, Crits.Crit.entries(Types.Fact, fs2), RFasts.Taken{fs, kn}),
          Facts.Facts.take_all(name, RFacts.Facts.list(fs2), Impl.Node.set(name, fs, ps, okr)),
          Sync.binds_is(
            name,
            Crits.Crit.entries(Types.Fact, fs2),
            Impl.Node.set(name, fs, ps, okr),
            kn
          )(Impl.Node.sound(name, fs, ps, okr))(ok)
        ),
        Equal.cong(
          RFacts.Plain(),
          Nodes.Raw,
          z => Nodes.Raw{name, ws, ms, st, z, RParts.Parts.join(ps, ps2)},
          Facts.Facts.crit(
            Facts.Facts.take_all(name, RFacts.Facts.list(fs2), Impl.Node.set(name, fs, ps, okr))
          ),
          RFacts.Facts.take_all(name, RFacts.Facts.list(fs2), fs),
          Facts.Facts.take_all_crit(name, RFacts.Facts.list(fs2), Impl.Node.set(name, fs, ps, okr))
        )
      )
    case RFasts.Fast{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +kn
    } Nodes.Act.Mount{+a, +b, +p, +held}:
      okr => ok => (
        %Equal.sym(Types.Ask, RFasts.Asked.ask(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), RFacts.Facts.asked(fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}), Asked.ask_fit(kn, fs, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}})(ok)): {RFasts.Fast.raw(RFasts.Fast.asks.to(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, kn, _, Spec.Request.Write{b, p, None{}}, Bool.not(st), True{})) == Nodes.Raw.asks(name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Bool.not(st)): Nodes.Raw}
        Fast.asks_to_raw(Bool.not(st), name, ws, Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a), st, fs, ps, Nodes.Mount.id(name, a), Spec.Request.Write{b, p, Some{held}}, Spec.Request.Write{b, p, None{}}, kn))
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Unmount{a}:
      okr => ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Work{}:
      okr => ok => Fast.works_raw(st, name, ws, ms, fs, ps, kn)(ok)
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Drop{}:
      okr => ok => Equal.cong(
        List<&2, Hashes.Hash>,
        Nodes.Raw,
        hs => Nodes.Raw{name, ws, ms, st, fs, RParts.Parts.only(ps, hs)},
        Nodes.Needs.of(kn, fs, name, ms),
        Nodes.Needs.of(RKnown.Known.none(), fs, name, ms),
        Needs.of_ok(kn, fs, name, ms)(ok)
      )
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Stop{force}:
      okr => ok => {==}

# a new fast node holds a right table
def Fast.new_ok(name: String) -> {RFasts.Fast.ok(RFasts.Fast.new(name)) == True{}: Bool}:
  {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a fast node of any state whose table knows nothing holds a right table: a
# node resumes from its facts with no Sync
def Fast.none_ok(
  r: Nodes.Raw
) -> {RFasts.Fast.ok(RFasts.Fast{r, RKnown.Known.none()}) == True{}: Bool}:
  %Equal.sym(
    Bool,
    RContents.Known.ok(RKnown.Known.none(), Nodes.Raw.facts(r)),
    True{},
    Knowns.Ok.none(Nodes.Raw.facts(r))
  ):
    {Bool.and(_, True{}) == True{}: Bool}
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# The soundness that a node resumes from
# --------------------------------------
# RFacts.Facts.ok.fast reads only the votes of the node and the starts; it is
# RFacts.Facts.ok, so Nodes.Raw.ok.fast is Nodes.Raw.ok.

# an ask that starts no store starts not the store h
def Ask.starts_not(
  +h: Hashes.Hash,
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {RFacts.Ask.starts(h, Types.Ask{i, k, r}) == False{}: Bool}:
  x => (%Equal.sym(
    Bool,
    RFacts.Request.is_start(r),
    False{},
    x
  ): {
    Shared.Bool.when(
      Bool,
      _,
      u => Hashes.Hash.is_eq(RFacts.Start.root(i, r), h),
      u => False{}
    )
      == False{}: Bool
  }; {==})

# no ask collides with an ask that starts no store
def Ask.collides_not_right(
  +a: Types.Ask,
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {RFacts.Ask.collides(a, Types.Ask{i, k, r}) == False{}: Bool}:
  x => Knowns.Collides.off(a, Types.Ask{i, k, r})(Ask.starts_not(RFacts.Ask.root(a), i, k, r)(x))

# an ask that starts no store collides with no ask
def Ask.collides_not_left(
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request,
  +b: Types.Ask
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {RFacts.Ask.collides(Types.Ask{i, k, r}, b) == False{}: Bool}:
  x => (%Equal.sym(
    Bool,
    RFacts.Request.is_start(r),
    False{},
    x
  ): {
    Shared.Bool.when(
      Bool,
      Shared.Bool.when(
        Bool,
        _,
        u => Hashes.Hash.is_eq(RFacts.Start.root(i, r), RFacts.Ask.root(Types.Ask{i, k, r})),
        u => False{}
      ),
      un => Shared.Bool.when(
        Bool,
        RFacts.Ask.starts(RFacts.Ask.root(Types.Ask{i, k, r}), b),
        u => Bool.not(RFacts.Ask.alike(Types.Ask{i, k, r}, b)),
        u => False{}
      ),
      un => False{}
    )
      == False{}: Bool
  }; {==})

# an ask that starts no store collides with none of the asks xs
def Asks.none(
  +i: Ledgers.Id,
  +k: Nat,
  +r: Spec.Request,
  xs: List<&2, Types.Ask>
) -> {
  RFacts.Request.is_start(r) == False{}: Bool
} -> {
  Shared.List.some(
    ~Types.Ask,
    ~Types.Ask,
    ~(x => y => RFacts.Ask.collides(x, y)),
    xs,
    Types.Ask{i, k, r}
  )
    == False{}: Bool
}:
  match xs:
    case Nil{}:
      h => {==}
    case Con{x, +rest}:
      +h =>
        %Equal.sym(
          Bool,
          RFacts.Ask.collides(Types.Ask{i, k, r}, x),
          False{},
          Ask.collides_not_left(i, k, r, x)(h)
        ): {
          List.any.if(
            u => Shared.List.some(
              ~Types.Ask,
              ~Types.Ask,
              ~(x => y => RFacts.Ask.collides(x, y)),
              rest,
              Types.Ask{i, k, r}
            ),
            _
          )
            == False{}: Bool
        }
        Asks.none(i, k, r, rest)(h)

# an ask collides with a fact of fs exactly when it collides with a start
# among fs
def Starts.collides_has(
  +a: Types.Ask,
  fs: List<&2, Types.Fact>
) -> {
  Shared.List.some(
    ~Types.Fact,
    ~Types.Ask,
    ~RFacts.Fact.collides,
    fs,
    a
  )
    == Shared.List.some(
      ~Types.Ask,
      ~Types.Ask,
      ~(x => y => RFacts.Ask.collides(x, y)),
      RFacts.Facts.starts(fs),
      a
    ): Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Starts.collides_has(a, rest)
    case Con{Types.Fact.Ask{Types.Ask{+i, +k, +r}}, +rest}:
      Lists.Bool.by(
        d => {RFacts.Request.is_start(r) == d: Bool} -> {List.any.if(u => Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, rest, a), RFacts.Ask.collides(a, Types.Ask{i, k, r})) == Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), List.filter.put(Types.Ask, Types.Ask{i, k, r}, RFacts.Facts.starts(rest), d), a): Bool},
        RFacts.Request.is_start(r),
        et => e => Equal.cong(Bool, Bool, z => List.any.if(u => z, RFacts.Ask.collides(a, Types.Ask{i, k, r})), Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, rest, a), Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(rest), a), Starts.collides_has(a, rest)),
        ef => e =>
          %Equal.sym(Bool, RFacts.Ask.collides(a, Types.Ask{i, k, r}), False{}, Ask.collides_not_right(a, i, k, r)(e)): {List.any.if(u => Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, rest, a), _) == Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(rest), a): Bool}
          Starts.collides_has(a, rest))({==})

# a fact of fs collides with a fact of all exactly when a start among fs
# collides with a start among all
def Starts.collided_has(
  +all: List<&2, Types.Fact>,
  fs: List<&2, Types.Fact>
) -> {
  Shared.List.some(
    ~Types.Fact,
    ~List<&2, Types.Fact>,
    ~RFacts.Fact.collided,
    fs,
    all
  )
    == RFacts.Asks.collide(RFacts.Facts.starts(all), RFacts.Facts.starts(fs)): Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Starts.collided_has(all, rest)
    case Con{Types.Fact.Ask{Types.Ask{+i, +k, +r}}, +rest}:
      Lists.Bool.by(
        d => {RFacts.Request.is_start(r) == d: Bool} -> {List.any.if(u => Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, all, Types.Ask{i, k, r})) == RFacts.Asks.collide(RFacts.Facts.starts(all), List.filter.put(Types.Ask, Types.Ask{i, k, r}, RFacts.Facts.starts(rest), d)): Bool},
        RFacts.Request.is_start(r),
        et => e => Equal.trans(Bool, List.any.if(u => Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, all, Types.Ask{i, k, r})), List.any.if(u => Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(all), Types.Ask{i, k, r})), List.any.if(u => RFacts.Asks.collide(RFacts.Facts.starts(all), RFacts.Facts.starts(rest)), Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(all), Types.Ask{i, k, r})), Equal.cong(Bool, Bool, z => List.any.if(u => Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), z), Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, all, Types.Ask{i, k, r}), Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(all), Types.Ask{i, k, r}), Starts.collides_has(Types.Ask{i, k, r}, all)), Equal.cong(Bool, Bool, z => List.any.if(u => z, Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(all), Types.Ask{i, k, r})), Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), RFacts.Asks.collide(RFacts.Facts.starts(all), RFacts.Facts.starts(rest)), Starts.collided_has(all, rest))),
        ef => e =>
          %Equal.sym(Bool, Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, all, Types.Ask{i, k, r}), False{}, Equal.trans(Bool, Shared.List.some(~Types.Fact, ~Types.Ask, ~RFacts.Fact.collides, all, Types.Ask{i, k, r}), Shared.List.some(~Types.Ask, ~Types.Ask, ~(x => y => RFacts.Ask.collides(x, y)), RFacts.Facts.starts(all), Types.Ask{i, k, r}), False{}, Starts.collides_has(Types.Ask{i, k, r}, all), Asks.none(i, k, r, RFacts.Facts.starts(all))(e))): {List.any.if(u => Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, rest, all), _) == RFacts.Asks.collide(RFacts.Facts.starts(all), RFacts.Facts.starts(rest)): Bool}
          Starts.collided_has(all, rest))({==})

# two names that are not the same, the other way round
def Name.ne_sym(
  +a: String,
  +b: String
) -> {String.eq(a, b) == False{}: Bool} -> {String.eq(b, a) == False{}: Bool}:
  h => Lists.Bool.by(
    d => {String.eq(b, a) == d: Bool} -> {d == False{}: Bool},
    String.eq(b, a),
    et => e => Empty.absurd(
      {True{} == False{}: Bool},
      Shared.Bool.true_ne_false(
        Equal.trans(
          Bool,
          True{},
          String.eq(a, a),
          False{},
          Equal.sym(Bool, String.eq(a, a), True{}, Texts.String.eq_refl(a)),
          (%Texts.String.eq_sound(b, a)(e): {String.eq(a, _) == False{}: Bool}; h)
        )
      )
    ),
    ef => e => {==}
  )({==})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof does not run
# the ballots among bs of the step whose words are k, in order
def Steps.only(bs: List<&2, Spec.Ballot>, +k: List<&2, U32>) -> List<&2, Spec.Ballot>:
  match bs:
    case Nil{}:
      []
    case Con{Spec.Ballot{+v, +st, +x}, rest}:
      List.filter.put(
        Spec.Ballot,
        Spec.Ballot{v, st, x},
        Steps.only(rest, k),
        Crits.Key.is_eq(k, st)
      )

# the map of ballots by step is well formed
def Steps.wf(
  bs: List<&2, Spec.Ballot>
) -> {Crits.Crit.wf(~List<&2, Spec.Ballot>, RFacts.Ballots.by_step(bs), 0n) == True{}: Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Spec.Ballot{voter, step, choice}:
          +step = step
          +tail = tail
          Crits.Crit.upsert_wf(
            ~List<&2, Spec.Ballot>,
            ~w => x => x,
            RFacts.Ballots.by_step(tail),
            step,
            Spec.Ballot{
              voter,
              step,
              choice
            }
              <> RFacts.Bucket.of(
                Crits.Crit.get.fuel(
                  List<&2, Spec.Ballot>,
                  1n+Crits.Key.size(step),
                  RFacts.Ballots.by_step(tail),
                  0n,
                  Crits.Cur{0n, step},
                  step
                )
              )
          )(Steps.wf(tail))

# under the words k of a step, the map of ballots by step holds the ballots
# of that step, in order
def Steps.get(
  bs: List<&2, Spec.Ballot>,
  +k: List<&2, U32>
) -> {
  RFacts.Bucket.of(
    Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(bs), k)
  )
    == Steps.only(bs, k): List<&2, Spec.Ballot>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{Spec.Ballot{+v, +st, +x}, +rest}:
      %Equal.sym(
        Maybe<&2, List<&2, Spec.Ballot>>,
        Crits.Crit.get(
          List<&2, Spec.Ballot>,
          Crits.Crit.set(
            ~List<&2, Spec.Ballot>,
            RFacts.Ballots.by_step(rest),
            st,
            Spec.Ballot{
              v,
              st,
              x
            }
              <> RFacts.Bucket.of(
                Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)
              )
          ),
          k
        ),
        Bool.pick(
          Maybe<&2, List<&2, Spec.Ballot>>,
          Crits.Key.is_eq(k, st),
          Some{
            Spec.Ballot{
              v,
              st,
              x
            }
              <> RFacts.Bucket.of(
                Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)
              )
          },
          Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), k)
        ),
        Crits.Dict.get_set.at(
          ~List<&2, Spec.Ballot>,
          RFacts.Ballots.by_step(rest),
          st,
          Spec.Ballot{
            v,
            st,
            x
          }
            <> RFacts.Bucket.of(
              Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)
            ),
          k
        )(Steps.wf(rest))
      ): {
        RFacts.Bucket.of(
          _
        )
          == List.filter.put(
            Spec.Ballot,
            Spec.Ballot{v, st, x},
            Steps.only(rest, k),
            Crits.Key.is_eq(k, st)
          ): List<&2, Spec.Ballot>
      }
      Lists.Bool.by(
        d => {
          Crits.Key.is_eq(k, st) == d: Bool
        } -> {
          RFacts.Bucket.of(
            Bool.pick(
              Maybe<&2, List<&2, Spec.Ballot>>,
              d,
              Some{
                Spec.Ballot{
                  v,
                  st,
                  x
                }
                  <> RFacts.Bucket.of(
                    Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)
                  )
              },
              Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), k)
            )
          )
            == List.filter.put(
              Spec.Ballot,
              Spec.Ballot{v, st, x},
              Steps.only(rest, k),
              d
            ): List<&2, Spec.Ballot>
        },
        Crits.Key.is_eq(k, st),
        et => e => Equal.cong(
          List<&2, Spec.Ballot>,
          List<&2, Spec.Ballot>,
          l => Spec.Ballot{v, st, x} <> l,
          RFacts.Bucket.of(Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)),
          Steps.only(rest, k),
          Equal.trans(
            List<&2, Spec.Ballot>,
            RFacts.Bucket.of(
              Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), st)
            ),
            RFacts.Bucket.of(
              Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), k)
            ),
            Steps.only(rest, k),
            Equal.cong(
              List<&2, U32>,
              List<&2, Spec.Ballot>,
              z => RFacts.Bucket.of(
                Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(rest), z)
              ),
              st,
              k,
              Equal.sym(List<&2, U32>, k, st, Crits.Key.is_eq_sound(k, st)(e))
            ),
            Steps.get(rest, k)
          )
        ),
        ef => e => Steps.get(rest, k)
      )({==})

# a test that is False either way is False
def Lazy.false(c: Bool) -> {Shared.Bool.when(Bool, c, u => False{}, u => False{}) == False{}: Bool}:
  +c = c
  %Equal.sym(
    Bool,
    Shared.Bool.when(Bool, c, u => False{}, u => False{}),
    Bool.pick(Bool, c, False{}, False{}),
    Knowns.Bool.when_pick(Bool, c, False{}, False{})
  ): {_ == False{}: Bool}; Crits.Crit.pick_self(Bool, c, False{})

# two ballots of other steps do not clash
def Steps.apart(
  +v: String,
  +sw: List<&2, U32>,
  +x: List<&2, U32>,
  +w: String,
  +tw: List<&2, U32>,
  +y: List<&2, U32>
) -> {
  Crits.Key.is_eq(sw, tw) == False{}: Bool
} -> {RFacts.Ballot.clash.lazy(Spec.Ballot{v, sw, x}, Spec.Ballot{w, tw, y}) == False{}: Bool}:
  h =>
    %Equal.sym(
      Bool,
      Shared.List.is_eq(~U32, ~U32.is_eq, sw, tw),
      False{},
      Equal.trans(
        Bool,
        Shared.List.is_eq(~U32, ~U32.is_eq, sw, tw),
        Crits.Key.is_eq(sw, tw),
        False{},
        Equal.sym(
          Bool,
          Crits.Key.is_eq(sw, tw),
          Shared.List.is_eq(~U32, ~U32.is_eq, sw, tw),
          Crits.Key.is_eq_list(sw, tw)
        ),
        h
      )
    ): {
      Shared.Bool.when(
        Bool,
        String.eq(v, w),
        u => Shared.Bool.when(Bool, _, u2 => Bool.not(RFacts.Words.is_eq(x, y)), u2 => False{}),
        u => False{}
      )
        == False{}: Bool
    }
    Lazy.false(String.eq(v, w))

# a ballot clashes with one of all exactly when it clashes with one of its
# step among all
def Steps.some_only(
  +v: String,
  +sw: List<&2, U32>,
  +x: List<&2, U32>,
  all: List<&2, Spec.Ballot>
) -> {
  Shared.List.some(
    ~Spec.Ballot,
    ~Spec.Ballot,
    ~RFacts.Ballot.clash.lazy,
    Steps.only(all, sw),
    Spec.Ballot{v, sw, x}
  )
    == Shared.List.some(
      ~Spec.Ballot,
      ~Spec.Ballot,
      ~RFacts.Ballot.clash.lazy,
      all,
      Spec.Ballot{v, sw, x}
    ): Bool
}:
  match all:
    case Nil{}:
      {==}
    case Con{Spec.Ballot{+w, +tw, +y}, +rest}:
      Lists.Bool.by(
        d => {Crits.Key.is_eq(sw, tw) == d: Bool} -> {Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, List.filter.put(Spec.Ballot, Spec.Ballot{w, tw, y}, Steps.only(rest, sw), d), Spec.Ballot{v, sw, x}) == List.any.if(u => Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, rest, Spec.Ballot{v, sw, x}), RFacts.Ballot.clash.lazy(Spec.Ballot{v, sw, x}, Spec.Ballot{w, tw, y})): Bool},
        Crits.Key.is_eq(sw, tw),
        et => e => Equal.cong(Bool, Bool, z => List.any.if(u => z, RFacts.Ballot.clash.lazy(Spec.Ballot{v, sw, x}, Spec.Ballot{w, tw, y})), Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, Steps.only(rest, sw), Spec.Ballot{v, sw, x}), Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, rest, Spec.Ballot{v, sw, x}), Steps.some_only(v, sw, x, rest)),
        ef => e =>
          %Equal.sym(Bool, RFacts.Ballot.clash.lazy(Spec.Ballot{v, sw, x}, Spec.Ballot{w, tw, y}), False{}, Steps.apart(v, sw, x, w, tw, y)(e)): {Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, Steps.only(rest, sw), Spec.Ballot{v, sw, x}) == List.any.if(u => Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, rest, Spec.Ballot{v, sw, x}), _): Bool}
          Steps.some_only(v, sw, x, rest))({==})

# Ballots.clash.by, with the ballots of all by step, is Ballots.clash
def Steps.clash_by(
  +all: List<&2, Spec.Ballot>,
  bs: List<&2, Spec.Ballot>
) -> {
  RFacts.Ballots.clash.by(RFacts.Ballots.by_step(all), bs) == RFacts.Ballots.clash(all, bs): Bool
}:
  match bs:
    case Nil{}:
      {==}
    case Con{head, tail}:
      match head:
        case Spec.Ballot{voter, step, choice}:
          +step = step
          %Equal.sym(
            List<&2, Spec.Ballot>,
            RFacts.Bucket.of(
              Crits.Crit.get(List<&2, Spec.Ballot>, RFacts.Ballots.by_step(all), step)
            ),
            Steps.only(all, step),
            Steps.get(all, step)
          ):
            {
              List.any.if(
                u => RFacts.Ballots.clash.by(RFacts.Ballots.by_step(all), tail),
                Shared.List.some(
                  Spec.Ballot,
                  Spec.Ballot,
                  RFacts.Ballot.clash.lazy,
                  _,
                  Spec.Ballot{voter, step, choice}
                )
              )
                == List.any.if(
                  u => RFacts.Ballots.clash(all, tail),
                  Shared.List.some(
                    Spec.Ballot,
                    Spec.Ballot,
                    RFacts.Ballot.clash.lazy,
                    all,
                    Spec.Ballot{voter, step, choice}
                  )
                ): Bool
            }
          %Equal.sym(
            Bool,
            Shared.List.some(
              Spec.Ballot,
              Spec.Ballot,
              RFacts.Ballot.clash.lazy,
              Steps.only(all, step),
              Spec.Ballot{voter, step, choice}
            ),
            Shared.List.some(
              Spec.Ballot,
              Spec.Ballot,
              RFacts.Ballot.clash.lazy,
              all,
              Spec.Ballot{voter, step, choice}
            ),
            Steps.some_only(voter, step, choice, all)
          ):
            {
              List.any.if(
                u => RFacts.Ballots.clash.by(RFacts.Ballots.by_step(all), tail),
                _
              )
                == List.any.if(
                  u => RFacts.Ballots.clash(all, tail),
                  Shared.List.some(
                    Spec.Ballot,
                    Spec.Ballot,
                    RFacts.Ballot.clash.lazy,
                    all,
                    Spec.Ballot{voter, step, choice}
                  )
                ): Bool
            }
          %Equal.sym(
            Bool,
            RFacts.Ballots.clash.by(RFacts.Ballots.by_step(all), tail),
            RFacts.Ballots.clash(all, tail),
            Steps.clash_by(all, tail)
          ):
            {
              List.any.if(
                u => _,
                Shared.List.some(
                  Spec.Ballot,
                  Spec.Ballot,
                  RFacts.Ballot.clash.lazy,
                  all,
                  Spec.Ballot{voter, step, choice}
                )
              )
                == List.any.if(
                  u => RFacts.Ballots.clash(all, tail),
                  Shared.List.some(
                    Spec.Ballot,
                    Spec.Ballot,
                    RFacts.Ballot.clash.lazy,
                    all,
                    Spec.Ballot{voter, step, choice}
                  )
                ): Bool
            }
          {==}

# a test that reads b only when a is True is Bool.and
def Lazy.and(
  a: Bool,
  b: Bool
) -> {Shared.Bool.when(Bool, a, u => b, u => False{}) == Bool.and(a, b): Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# Ballot.clash.lazy is Ballot.clash
def Ballot.lazy_eq(
  a: Spec.Ballot,
  b: Spec.Ballot
) -> {RFacts.Ballot.clash.lazy(a, b) == RFacts.Ballot.clash(a, b): Bool}:
  match a b:
    case Spec.Ballot{+v, +s, +x} Spec.Ballot{+w, +t, +y}:
      Equal.trans(
        Bool,
        Shared.Bool.when(
          Bool,
          String.eq(v, w),
          u => Shared.Bool.when(
            Bool,
            RFacts.Words.is_eq(s, t),
            u2 => Bool.not(RFacts.Words.is_eq(x, y)),
            u2 => False{}
          ),
          u => False{}
        ),
        Shared.Bool.when(
          Bool,
          String.eq(v, w),
          u => Bool.and(RFacts.Words.is_eq(s, t), Bool.not(RFacts.Words.is_eq(x, y))),
          u => False{}
        ),
        Bool.and(
          String.eq(v, w),
          Bool.and(RFacts.Words.is_eq(s, t), Bool.not(RFacts.Words.is_eq(x, y)))
        ),
        Equal.cong(
          Bool,
          Bool,
          z => Shared.Bool.when(Bool, String.eq(v, w), u => z, u => False{}),
          Shared.Bool.when(
            Bool,
            RFacts.Words.is_eq(s, t),
            u2 => Bool.not(RFacts.Words.is_eq(x, y)),
            u2 => False{}
          ),
          Bool.and(RFacts.Words.is_eq(s, t), Bool.not(RFacts.Words.is_eq(x, y))),
          Lazy.and(RFacts.Words.is_eq(s, t), Bool.not(RFacts.Words.is_eq(x, y)))
        ),
        Lazy.and(
          String.eq(v, w),
          Bool.and(RFacts.Words.is_eq(s, t), Bool.not(RFacts.Words.is_eq(x, y)))
        )
      )

# a ballot of the voter name clashes with a fact of fs exactly when it
# clashes with a ballot of name among fs
def Own.clash_has(
  +w: String,
  +sw: List<&2, U32>,
  +cw: List<&2, U32>,
  +name: String,
  fs: List<&2, Types.Fact>
) -> {
  String.eq(w, name) == True{}: Bool
} -> {
  Shared.List.some(
    ~Types.Fact,
    ~Spec.Ballot,
    ~RFacts.Fact.clashes,
    fs,
    Spec.Ballot{w, sw, cw}
  )
    == Shared.List.some(
      ~Spec.Ballot,
      ~Spec.Ballot,
      ~RFacts.Ballot.clash.lazy,
      RFacts.Facts.own(name, fs),
      Spec.Ballot{w, sw, cw}
    ): Bool
}:
  match fs:
    case Nil{}:
      hw => {==}
    case Con{Types.Fact.Ask{q}, rest}:
      hw => Own.clash_has(w, sw, cw, name, rest)(hw)
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      +hw => Lists.Bool.by(
        d => {String.eq(v, name) == d: Bool} -> {List.any.if(u => Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, rest, Spec.Ballot{w, sw, cw}), RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})) == Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, List.filter.put(Spec.Ballot, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}, RFacts.Facts.own(name, rest), d), Spec.Ballot{w, sw, cw}): Bool},
        String.eq(v, name),
        et => e => Equal.trans(Bool, List.any.if(u => Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, rest, Spec.Ballot{w, sw, cw}), RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})), List.any.if(u => Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, RFacts.Facts.own(name, rest), Spec.Ballot{w, sw, cw}), RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})), List.any.if(u => Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, RFacts.Facts.own(name, rest), Spec.Ballot{w, sw, cw}), RFacts.Ballot.clash.lazy(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})), Equal.cong(Bool, Bool, z => List.any.if(u => z, RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})), Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, rest, Spec.Ballot{w, sw, cw}), Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, RFacts.Facts.own(name, rest), Spec.Ballot{w, sw, cw}), Own.clash_has(w, sw, cw, name, rest)(hw)), Equal.cong(Bool, Bool, z => List.any.if(u => Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, RFacts.Facts.own(name, rest), Spec.Ballot{w, sw, cw}), z), RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), RFacts.Ballot.clash.lazy(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), Equal.sym(Bool, RFacts.Ballot.clash.lazy(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), RFacts.Ballot.clash(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), Ballot.lazy_eq(Spec.Ballot{w, sw, cw}, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})))),
        ef => e =>
          %Equal.sym(Bool, String.eq(w, v), False{}, (%Equal.sym(String, w, name, Texts.String.eq_sound(w, name)(hw)): {String.eq(_, v) == False{}: Bool}; Name.ne_sym(v, name)(e))): {List.any.if(u => Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, rest, Spec.Ballot{w, sw, cw}), Bool.and(_, Bool.and(RFacts.Words.is_eq(sw, Coded.Step.words(st)), Bool.not(RFacts.Words.is_eq(cw, Coded.Cast.words(pk)))))) == Shared.List.some(~Spec.Ballot, ~Spec.Ballot, ~RFacts.Ballot.clash.lazy, RFacts.Facts.own(name, rest), Spec.Ballot{w, sw, cw}): Bool}
          Own.clash_has(w, sw, cw, name, rest)(hw))({==})

# a fact of fs names name a liar, against the facts all, exactly when a
# ballot of name among fs clashes with one among all
def Own.liars_has(
  +name: String,
  +all: List<&2, Types.Fact>,
  fs: List<&2, Types.Fact>
) -> {
  List.contains(
    ~String,
    ~String.eq,
    RFacts.Facts.liars.go(all, fs),
    name
  )
    == RFacts.Ballots.clash(RFacts.Facts.own(name, all), RFacts.Facts.own(name, fs)): Bool
}:
  match fs:
    case Nil{}:
      {==}
    case Con{Types.Fact.Ask{q}, rest}:
      Own.liars_has(name, all, rest)
    case Con{Types.Fact.Vote{+v, +st, +pk}, +rest}:
      Lists.Bool.by(
        d => {String.eq(v, name) == d: Bool} -> {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Shared.Maybe.when(String, Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), u => Some{RFacts.Ballot.voter(Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})}), RFacts.Facts.liars.go(all, rest)), name) == RFacts.Ballots.clash(RFacts.Facts.own(name, all), List.filter.put(Spec.Ballot, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}, RFacts.Facts.own(name, rest), d)): Bool},
        String.eq(v, name),
        +et => +e =>
          %Own.clash_has(v, Coded.Step.words(st), Coded.Cast.words(pk), name, all)(e): {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Shared.Maybe.when(String, Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}), u => Some{RFacts.Ballot.voter(Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)})}), RFacts.Facts.liars.go(all, rest)), name) == List.any.if(u => RFacts.Ballots.clash(RFacts.Facts.own(name, all), RFacts.Facts.own(name, rest)), _): Bool}
          Lists.Bool.by(
        d2 => {Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}) == d2: Bool} -> {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Shared.Maybe.when(String, d2, u => Some{v}), RFacts.Facts.liars.go(all, rest)), name) == List.any.if(u => RFacts.Ballots.clash(RFacts.Facts.own(name, all), RFacts.Facts.own(name, rest)), d2): Bool},
        Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}),
        ct => e2 =>
          %Equal.sym(Bool, String.eq(v, name), True{}, e): {List.any.if(u => List.contains(~String, ~String.eq, RFacts.Facts.liars.go(all, rest), name), _) == True{}: Bool}
          {==},
        cf => e2 => Own.liars_has(name, all, rest))({==}),
        ef => e => Lists.Bool.by(
        d2 => {Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}) == d2: Bool} -> {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Shared.Maybe.when(String, d2, u => Some{v}), RFacts.Facts.liars.go(all, rest)), name) == RFacts.Ballots.clash(RFacts.Facts.own(name, all), RFacts.Facts.own(name, rest)): Bool},
        Shared.List.some(~Types.Fact, ~Spec.Ballot, ~RFacts.Fact.clashes, all, Spec.Ballot{v, Coded.Step.words(st), Coded.Cast.words(pk)}),
        ct => e2 =>
          %Equal.sym(Bool, String.eq(v, name), False{}, e): {List.any.if(u => List.contains(~String, ~String.eq, RFacts.Facts.liars.go(all, rest), name), _) == RFacts.Ballots.clash(RFacts.Facts.own(name, all), RFacts.Facts.own(name, rest)): Bool}
          Own.liars_has(name, all, rest),
        cf => e2 => Own.liars_has(name, all, rest))({==}))({==})

# a test that is True unless c holds, and then is r, is Bool.and(not c, r)
def Lazy.not_and(
  c: Bool,
  r: Bool
) -> {Shared.Bool.when(Bool, c, u => False{}, u => r) == Bool.and(Bool.not(c), r): Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# a test that is b when c holds, else True, is Bool.or(not c, b)
def Lazy.not_or(
  c: Bool,
  b: Bool
) -> {Shared.Bool.when(Bool, c, u => b, u => True{}) == Bool.or(Bool.not(c), b): Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

# RFacts.Facts.ok.fast, with each test read whole, is RFacts.Facts.ok
def Sound.eager(
  +name: String,
  +s: RFacts.Plain()
) -> {
  Bool.and(
    Bool.not(
      RFacts.Ballots.clash(
        RFacts.Facts.own(name, RFacts.Facts.list(s)),
        RFacts.Facts.own(name, RFacts.Facts.list(s))
      )
    ),
    Bool.or(
      Bool.not(
        RFacts.Asks.collide(
          RFacts.Facts.starts(RFacts.Facts.list(s)),
          RFacts.Facts.starts(RFacts.Facts.list(s))
        )
      ),
      RFacts.Trust.broken(s, name)
    )
  )
    == RFacts.Facts.ok(name, s): Bool
}:
  +fs = RFacts.Facts.list(s)
  %Equal.sym(
    Bool,
    List.contains(~String, ~String.eq, RFacts.Facts.liars.go(fs, fs), name),
    RFacts.Ballots.clash(RFacts.Facts.own(name, fs), RFacts.Facts.own(name, fs)),
    Own.liars_has(name, fs, fs)
  ): {
    Bool.and(
      Bool.not(
        RFacts.Ballots.clash(
          RFacts.Facts.own(name, RFacts.Facts.list(s)),
          RFacts.Facts.own(name, RFacts.Facts.list(s))
        )
      ),
      Bool.or(
        Bool.not(
          RFacts.Asks.collide(
            RFacts.Facts.starts(RFacts.Facts.list(s)),
            RFacts.Facts.starts(RFacts.Facts.list(s))
          )
        ),
        RFacts.Trust.broken(s, name)
      )
    )
      == Bool.and(
        Bool.not(_),
        Bool.or(Bool.not(RFacts.Facts.collide(s)), RFacts.Trust.broken(s, name))
      ): Bool
  }
  %Equal.sym(
    Bool,
    Shared.List.some(~Types.Fact, ~List<&2, Types.Fact>, ~RFacts.Fact.collided, fs, fs),
    RFacts.Asks.collide(RFacts.Facts.starts(fs), RFacts.Facts.starts(fs)),
    Starts.collided_has(fs, fs)
  ): {
    Bool.and(
      Bool.not(
        RFacts.Ballots.clash(
          RFacts.Facts.own(name, RFacts.Facts.list(s)),
          RFacts.Facts.own(name, RFacts.Facts.list(s))
        )
      ),
      Bool.or(
        Bool.not(
          RFacts.Asks.collide(
            RFacts.Facts.starts(RFacts.Facts.list(s)),
            RFacts.Facts.starts(RFacts.Facts.list(s))
          )
        ),
        RFacts.Trust.broken(s, name)
      )
    )
      == Bool.and(
        Bool.not(RFacts.Ballots.clash(RFacts.Facts.own(name, fs), RFacts.Facts.own(name, fs))),
        Bool.or(Bool.not(_), RFacts.Trust.broken(s, name))
      ): Bool
  }
  {==}

# RFacts.Facts.ok.fast is RFacts.Facts.ok
def Sound.ok_fast(
  +name: String,
  +s: RFacts.Plain()
) -> {RFacts.Facts.ok.fast(name, s) == RFacts.Facts.ok(name, s): Bool}:
  Equal.trans(
    Bool,
    RFacts.Facts.ok.fast(name, s),
    Shared.Bool.when(
      Bool,
      RFacts.Ballots.clash(
        RFacts.Facts.own(name, RFacts.Facts.list(s)),
        RFacts.Facts.own(name, RFacts.Facts.list(s))
      ),
      u => False{},
      u => Shared.Bool.when(
        Bool,
        RFacts.Asks.collide(
          RFacts.Facts.starts(RFacts.Facts.list(s)),
          RFacts.Facts.starts(RFacts.Facts.list(s))
        ),
        u2 => RFacts.Trust.broken(s, name),
        u2 => True{}
      )
    ),
    RFacts.Facts.ok(name, s),
    Equal.cong(
      Bool,
      Bool,
      z => Shared.Bool.when(
        Bool,
        z,
        u => False{},
        u => Shared.Bool.when(
          Bool,
          RFacts.Asks.collide(
            RFacts.Facts.starts(RFacts.Facts.list(s)),
            RFacts.Facts.starts(RFacts.Facts.list(s))
          ),
          u2 => RFacts.Trust.broken(s, name),
          u2 => True{}
        )
      ),
      RFacts.Ballots.clash.by(
        RFacts.Ballots.by_step(RFacts.Facts.own(name, RFacts.Facts.list(s))),
        RFacts.Facts.own(name, RFacts.Facts.list(s))
      ),
      RFacts.Ballots.clash(
        RFacts.Facts.own(name, RFacts.Facts.list(s)),
        RFacts.Facts.own(name, RFacts.Facts.list(s))
      ),
      Steps.clash_by(
        RFacts.Facts.own(name, RFacts.Facts.list(s)),
        RFacts.Facts.own(name, RFacts.Facts.list(s))
      )
    ),
    Equal.trans(
      Bool,
      Shared.Bool.when(
        Bool,
        RFacts.Ballots.clash(
          RFacts.Facts.own(name, RFacts.Facts.list(s)),
          RFacts.Facts.own(name, RFacts.Facts.list(s))
        ),
        u => False{},
        u => Shared.Bool.when(
          Bool,
          RFacts.Asks.collide(
            RFacts.Facts.starts(RFacts.Facts.list(s)),
            RFacts.Facts.starts(RFacts.Facts.list(s))
          ),
          u2 => RFacts.Trust.broken(s, name),
          u2 => True{}
        )
      ),
      Bool.and(
        Bool.not(
          RFacts.Ballots.clash(
            RFacts.Facts.own(name, RFacts.Facts.list(s)),
            RFacts.Facts.own(name, RFacts.Facts.list(s))
          )
        ),
        Bool.or(
          Bool.not(
            RFacts.Asks.collide(
              RFacts.Facts.starts(RFacts.Facts.list(s)),
              RFacts.Facts.starts(RFacts.Facts.list(s))
            )
          ),
          RFacts.Trust.broken(s, name)
        )
      ),
      RFacts.Facts.ok(name, s),
      Equal.trans(
        Bool,
        Shared.Bool.when(
          Bool,
          RFacts.Ballots.clash(
            RFacts.Facts.own(name, RFacts.Facts.list(s)),
            RFacts.Facts.own(name, RFacts.Facts.list(s))
          ),
          u => False{},
          u => Shared.Bool.when(
            Bool,
            RFacts.Asks.collide(
              RFacts.Facts.starts(RFacts.Facts.list(s)),
              RFacts.Facts.starts(RFacts.Facts.list(s))
            ),
            u2 => RFacts.Trust.broken(s, name),
            u2 => True{}
          )
        ),
        Shared.Bool.when(
          Bool,
          RFacts.Ballots.clash(
            RFacts.Facts.own(name, RFacts.Facts.list(s)),
            RFacts.Facts.own(name, RFacts.Facts.list(s))
          ),
          u => False{},
          u => Bool.or(
            Bool.not(
              RFacts.Asks.collide(
                RFacts.Facts.starts(RFacts.Facts.list(s)),
                RFacts.Facts.starts(RFacts.Facts.list(s))
              )
            ),
            RFacts.Trust.broken(s, name)
          )
        ),
        Bool.and(
          Bool.not(
            RFacts.Ballots.clash(
              RFacts.Facts.own(name, RFacts.Facts.list(s)),
              RFacts.Facts.own(name, RFacts.Facts.list(s))
            )
          ),
          Bool.or(
            Bool.not(
              RFacts.Asks.collide(
                RFacts.Facts.starts(RFacts.Facts.list(s)),
                RFacts.Facts.starts(RFacts.Facts.list(s))
              )
            ),
            RFacts.Trust.broken(s, name)
          )
        ),
        Equal.cong(
          Bool,
          Bool,
          z => Shared.Bool.when(
            Bool,
            RFacts.Ballots.clash(
              RFacts.Facts.own(name, RFacts.Facts.list(s)),
              RFacts.Facts.own(name, RFacts.Facts.list(s))
            ),
            u => False{},
            u => z
          ),
          Shared.Bool.when(
            Bool,
            RFacts.Asks.collide(
              RFacts.Facts.starts(RFacts.Facts.list(s)),
              RFacts.Facts.starts(RFacts.Facts.list(s))
            ),
            u2 => RFacts.Trust.broken(s, name),
            u2 => True{}
          ),
          Bool.or(
            Bool.not(
              RFacts.Asks.collide(
                RFacts.Facts.starts(RFacts.Facts.list(s)),
                RFacts.Facts.starts(RFacts.Facts.list(s))
              )
            ),
            RFacts.Trust.broken(s, name)
          ),
          Lazy.not_or(
            RFacts.Asks.collide(
              RFacts.Facts.starts(RFacts.Facts.list(s)),
              RFacts.Facts.starts(RFacts.Facts.list(s))
            ),
            RFacts.Trust.broken(s, name)
          )
        ),
        Lazy.not_and(
          RFacts.Ballots.clash(
            RFacts.Facts.own(name, RFacts.Facts.list(s)),
            RFacts.Facts.own(name, RFacts.Facts.list(s))
          ),
          Bool.or(
            Bool.not(
              RFacts.Asks.collide(
                RFacts.Facts.starts(RFacts.Facts.list(s)),
                RFacts.Facts.starts(RFacts.Facts.list(s))
              )
            ),
            RFacts.Trust.broken(s, name)
          )
        )
      ),
      Sound.eager(name, s)
    )
  )

# Raw.ok.fast is Raw.ok
def Raw.ok_fast(r: Nodes.Raw) -> {Nodes.Raw.ok.fast(r) == Nodes.Raw.ok(r): Bool}:
  match r:
    case Nodes.Raw{+name, ws, ms, st, +fs, +ps}:
      Equal.trans(
        Bool,
        Shared.Bool.when(
          Bool,
          Nodes.Raw.set(fs, ps),
          u => Shared.Bool.when(
            Bool,
            RFacts.Facts.ok.fast(name, fs),
            u2 => Bool.not(RFacts.Trust.reserved(name)),
            u2 => False{}
          ),
          u => False{}
        ),
        Bool.and(
          Nodes.Raw.set(fs, ps),
          Bool.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name)))
        ),
        Nodes.Raw.ok(Nodes.Raw{name, ws, ms, st, fs, ps}),
        Equal.trans(
          Bool,
          Shared.Bool.when(
            Bool,
            Nodes.Raw.set(fs, ps),
            u => Shared.Bool.when(
              Bool,
              RFacts.Facts.ok.fast(name, fs),
              u2 => Bool.not(RFacts.Trust.reserved(name)),
              u2 => False{}
            ),
            u => False{}
          ),
          Shared.Bool.when(
            Bool,
            Nodes.Raw.set(fs, ps),
            u => Bool.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name))),
            u => False{}
          ),
          Bool.and(
            Nodes.Raw.set(fs, ps),
            Bool.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name)))
          ),
          Equal.cong(
            Bool,
            Bool,
            z => Shared.Bool.when(Bool, Nodes.Raw.set(fs, ps), u => z, u => False{}),
            Shared.Bool.when(
              Bool,
              RFacts.Facts.ok.fast(name, fs),
              u2 => Bool.not(RFacts.Trust.reserved(name)),
              u2 => False{}
            ),
            Bool.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name))),
            Lazy.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name)))
          ),
          Lazy.and(
            Nodes.Raw.set(fs, ps),
            Bool.and(RFacts.Facts.ok.fast(name, fs), Bool.not(RFacts.Trust.reserved(name)))
          )
        ),
        Equal.cong(
          Bool,
          Bool,
          z => Bool.and(Nodes.Raw.set(fs, ps), Bool.and(z, Bool.not(RFacts.Trust.reserved(name)))),
          RFacts.Facts.ok.fast(name, fs),
          RFacts.Facts.ok(name, fs),
          Sound.ok_fast(name, fs)
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
      ok => Knowns.View.at_ok(kn, Nodes.Raw.facts(r), w, b, p)(ok)
