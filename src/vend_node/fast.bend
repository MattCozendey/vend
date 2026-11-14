import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
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
      ok => Learn.facts_ok(rest, RKnown.Known.learn(kn, s, c), s, all)(Knowns.Known.learn_ok(kn, s, c)(ok))
    case Con{Types.Fact.Ask{Types.Ask{i, n, +r}}, rest}:
      ok => Learn.facts_ok(rest, RFasts.Learn.request(kn, s, all, r), s, all)(
        Learn.request_ok(kn, s, all, r)(ok)
      )

# a right table that learns the states of the lines that a work reads is
# right
def Learn.work_ok(
  +kn: RKnown.Known(),
  +s: RFacts.Plain()
) -> {
  RContents.Known.ok(kn, s) == True{}: Bool
} -> {RContents.Known.ok(RFasts.Learn.work(kn, s), s) == True{}: Bool}:
  ok => Learn.facts_ok(RFacts.Facts.list(s), kn, s, RFacts.Facts.list(s))(ok)

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
      ok => Knowns.Known.grow_ok(
        kn,
        RKnown.Known.cast(kn, RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}), c, k),
        RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, Types.Step.At{c, k, t}, x}),
        c
      )(Knowns.Known.cast_ok(kn, name, s, c, k, t, x)(ok))

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
    RFasts.Table.cast(kn, Facts.Facts.crit(s), name, m),
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
  Nodes.Needs.of(kn, s, name, ms) == Nodes.Needs.of(RKnown.Known.none(), s, name, ms): List<&2, Hashes.Hash>
}:
  match ms:
    case Nil{}:
      ok => {==}
    case Con{Nodes.Mounted{+a, +b, +p}, +rest}:
      +ok => (
        %Knowns.View.at_ok(kn, s, name, b, p)(ok): {Nodes.Needs.of(kn, s, name, Nodes.Mounted{a, b, p} <> rest) == Nodes.Needs.put(_, Nodes.Needs.of(RKnown.Known.none(), s, name, rest)): List<&2, Hashes.Hash>}
        %Needs.of_ok(kn, s, name, rest)(ok): {Nodes.Needs.of(kn, s, name, Nodes.Mounted{a, b, p} <> rest) == Nodes.Needs.put(RAnswers.View.at(kn, s, name, b, p), _): List<&2, Hashes.Hash>}
        {==})

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
    Nodes.Raw.facts(Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go))
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      ok => Table.asked_same(kn, fs, r)(ok)
    case True{}:
      ok => Table.asked_ok(kn, name, Impl.Node.set(name, fs, ps, okr), i, r)(ok)

# the table of a fast node stays right after a work
def Fast.works_ok(
  st: Bool,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +kn: RKnown.Known(),
  +okr: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  RContents.Known.ok(kn, fs) == True{}: Bool
} -> {RFasts.Fast.ok(RFasts.Fast.works(name, ws, ms, st, fs, ps, kn)) == True{}: Bool}:
  match st:
    case True{}:
      ok => ok
    case False{}:
      ok => Table.cast_ok(
        RFasts.Learn.work(kn, fs),
        name,
        Impl.Node.set(name, fs, ps, okr),
        RWorks.Work.plan(RFasts.Learn.work(kn, fs), fs, name)
      )(Learn.work_ok(kn, fs)(ok))

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
      +okr => ok => Fast.asks_ok(
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
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Sync{from}:
      okr => ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Mount{+a, +b, +p, +held}:
      +okr => ok => Fast.asks_ok(
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
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Unmount{a}:
      okr => ok => ok
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Work{}:
      +okr => ok => Fast.works_ok(st, name, ws, ms, fs, ps, kn, okr)(ok)
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
  RContents.Known.ok(kn, fs) == True{}: Bool
} -> {
  RFasts.Fast.raw(RFasts.Fast.works(name, ws, ms, st, fs, ps, kn)) == Nodes.Raw.works(name, ws, ms, st, fs, ps): Nodes.Raw
}:
  match st:
    case True{}:
      ok => {==}
    case False{}:
      ok => Equal.cong(
        Maybe<&2, RWorks.Plan>,
        Nodes.Raw,
        m => Nodes.Raw{name, ws, ms, False{}, RWorks.Work.cast(fs, name, m), ps},
        RWorks.Work.plan(RFasts.Learn.work(kn, fs), fs, name),
        RWorks.Work.plan(RKnown.Known.none(), fs, name),
        Knowns.Work.plan_ok(RFasts.Learn.work(kn, fs), fs, name)(Learn.work_ok(kn, fs)(ok))
      )

# the state of a fast node with a right table after a deed is the state that
# Nodes.Raw.does gives: a fast node does what a node does
def Fast.does_raw(
  f: RFasts.Fast,
  a: Nodes.Act
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {
  RFasts.Fast.raw(RFasts.Fast.does(f, a)) == Nodes.Raw.does(RFasts.Fast.raw(f), a): Nodes.Raw
}:
  match f a:
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Connect{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Leave{w}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Ask{i, q}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Sync{from}:
      ok => {==}
    case RFasts.Fast{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +kn} Nodes.Act.Mount{a, b, p, held}:
      ok => {==}
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
        Needs.of_ok(kn, fs, name, ms)(ok)
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
) -> {RFasts.Fast.ok(f) == True{}: Bool} -> {RFasts.Fast.ok(RFasts.Fast.learn(f, c)) == True{}: Bool}:
  match f:
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.Known.warm_ok(RKnown.Known.learn(kn, Nodes.Raw.facts(r), c), Nodes.Raw.facts(r), c)(
        Knowns.Known.learn_ok(kn, Nodes.Raw.facts(r), c)(ok)
      )

# What a fast node shows
# ----------------------

# a fast node with a right table replies as its state does
def Fast.answer_raw(
  f: RFasts.Fast,
  +q: Spec.Question
) -> {
  RFasts.Fast.ok(f) == True{}: Bool
} -> {
  RFasts.Fast.answer(f, q) == Nodes.Raw.answer(RFasts.Fast.raw(f), q): Maybe<&2, Spec.Reply>
}:
  match f:
    case RFasts.Fast{+r, +kn}:
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
  RFasts.Fast.read(f, c, k, p) == Nodes.Raw.read(RFasts.Fast.raw(f), c, k, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match f:
    case RFasts.Fast{+r, +kn}:
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
  RFasts.Fast.view(f, w, b, p) == Nodes.Raw.view(RFasts.Fast.raw(f), w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match f:
    case RFasts.Fast{+r, +kn}:
      ok => Knowns.View.at_ok(kn, Nodes.Raw.facts(r), w, b, p)(ok)
