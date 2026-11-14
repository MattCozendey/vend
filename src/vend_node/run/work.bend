import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/shared.bend as Shared
import ./content.bend as Contents
import ./facts.bend as Facts
import ./known.bend as Known
import ./lines.bend as Lines
import ./rounds.bend as Rounds
import ../shared/lists.bend as Lists
import ../spec.bend as Spec
import ../types.bend as Types

# Work
# ----
# What a node does by itself: it casts at most one ballot per work, under
# its own name, for the next slot of a line that it decides, with the next
# number of its own ballots for the slot. So it never casts two ballots with
# one number. A slot is decided in rounds (Rounds): the node whose turn a
# round is proposes the request that it took in last, or what the votes of
# the rounds before bind it to; the others vote as it did. A node that has
# nothing to vote for passes to a later round, so a lost node does not stop
# a slot.

# Where a request goes
# --------------------

# the line that the merge of the id i merges into, as an ask among fs says
def Merge.line(fs: List<&2, Types.Fact>, +i: Ledgers.Id) -> Maybe<&2, Ledgers.Line>:
  match fs:
    case Nil{}:
      None{}
    case Con{Types.Fact.Vote{v, st, pk}, rest}:
      Merge.line(rest, i)
    case Con{Types.Fact.Ask{Types.Ask{j, k, Spec.Request.Merge{f, x}}}, rest}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Line>,
        Ledgers.Id.is_eq(j, i),
        u => Some{x},
        u => Merge.line(rest, i)
      )
    case Con{Types.Fact.Ask{a}, rest}:
      Merge.line(rest, i)

# the line whose versions the request r is for
def Request.line(fs: List<&2, Types.Fact>, r: Spec.Request) -> Maybe<&2, Ledgers.Line>:
  match r:
    case Spec.Request.Start{os}:
      None{}
    case Spec.Request.Write{b, p, w}:
      Some{b}
    case Spec.Request.Merge{f, x}:
      Some{x}
    case Spec.Request.Resolve{m, p, w}:
      Merge.line(fs, m)
    case Spec.Request.Mark{b, m, v}:
      Some{b}
    case Spec.Request.Move{b, t, v}:
      Some{b}
    case Spec.Request.Group{h, g, ms}:
      Some{Ledgers.Line{h, None{}}}
    case Spec.Request.Own{Ledgers.Line{h, b}, g}:
      Some{Ledgers.Line{h, None{}}}

# Pins
# ----

# a version that takes a version of another line: its number, and the number
# of the version that it takes
type Took is Data:
  Took{at: Nat, version: Nat}

# found, or the version k when it takes a version of the line c (m)
def Takes.pick(
  c: Ledgers.Line,
  k: Nat,
  m: Maybe<&2, Spec.Point>,
  found: Maybe<&2, Took>
) -> Maybe<&2, Took>:
  match m:
    case None{}:
      found
    case Some{Spec.Point{t, v}}:
      Bool.pick(Maybe<&2, Took>, Ledgers.Line.is_eq(t, c), Some{Took{k, v}}, found)

# the newest version among vs, from the version k on, that takes a version of
# the line c: its number, and the version that it takes
def Takes.last(
  vs: List<&2, Types.Entry>,
  +c: Ledgers.Line,
  +k: Nat,
  found: Maybe<&2, Took>
) -> Maybe<&2, Took>:
  match vs:
    case Nil{}:
      found
    case Con{e, rest}:
      Takes.last(rest, c, 1n+k, Takes.pick(c, k, Contents.Entry.takes(e), found))

# the pins of a merge of the line f into the line c: the newest version of f,
# and as base the newest version of c that f took, else the newest version of
# f that c took, else none
def Pins.merge.of(
  m: Nat,
  +c: Ledgers.Line,
  +f: Ledgers.Line,
  from: Nat,
  theirs: Maybe<&2, Took>,
  ours: Maybe<&2, Took>
) -> Types.Pins:
  match theirs ours:
    case Some{Took{+j, +v}} _:
      Types.Pins{
        m,
        from,
        Some{Spec.Point{c, v}},
        [Spec.Point{c, v}],
        [Spec.Point{f, j}, Spec.Point{c, v}]
      }
    case None{} Some{Took{+j, +v}}:
      Types.Pins{
        m,
        from,
        Some{Spec.Point{f, v}},
        [Spec.Point{c, j}, Spec.Point{f, v}],
        [Spec.Point{f, v}]
      }
    case None{} None{}:
      Types.Pins{m, from, None{}, [], []}

# the pins of a merge of the line f, of the versions fv if known, into the
# line c, of the versions vs
def Pins.merge(
  m: Nat,
  +c: Ledgers.Line,
  +f: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  fv: Maybe<&2, List<&2, Types.Entry>>
) -> Types.Pins:
  match fv:
    case None{}:
      Lines.Pins.plain(m)
    case Some{+fs}:
      Pins.merge.of(
        m,
        c,
        f,
        Nat.sub(List.length(&2, Types.Entry, fs), 1n),
        Takes.last(fs, c, 0n, None{}),
        Takes.last(vs, f, 0n, None{})
      )

# the pins that the node gives the request r for the line c, of the versions
# vs, at the era m
def Pins.for(
  +kn: Known.Known(), +s: Facts.Plain(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  m: Nat,
  r: Spec.Request
) -> Types.Pins:
  match r:
    case Spec.Request.Merge{+f, x}:
      Pins.merge(m, c, f, vs, Known.Known.versions(kn, s, f))
    case _:
      Lines.Pins.plain(m)

# the newest of the versions m
def Era.now.of(m: Maybe<&2, List<&2, Types.Entry>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{R}:
      Nat.sub(List.length(&2, Types.Entry, R), 1n)

# the era that the node pins for the line c: the newest version of its store
# that it holds
def Era.now(+kn: Known.Known(), +s: Facts.Plain(), c: Ledgers.Line) -> Nat:
  match c:
    case Ledgers.Line{h, b}:
      Era.now.of(Known.Known.store(kn, s, h))

# The next ballot
# ---------------

# a ballot that the node may cast: where, and what
type Plan is Data:
  Plan{step: Types.Step, cast: Types.Cast}

# the next slot of a line that a node decides: the versions of the line, the
# slot, and the nodes that decide it
type Open is Data:
  Open{versions: List<&2, Types.Entry>, slot: Nat, nodes: List<&2, String>}

# the rule of the next version of the line c, in the state m
def Work.rule(
  +kn: Known.Known(), +s: Facts.Plain(),
  +c: Ledgers.Line,
  m: Maybe<&2, Lines.State>
) -> Maybe<&2, Lines.Rule>:
  match m:
    case None{}:
      None{}
    case Some{Lines.State{vs, k}}:
      Known.Known.rule(kn, s, c, vs)

# the next slot of a line in the state m with the rule u, when the node name
# is one of the nodes that decide it
def Work.open.at(
  +name: String,
  m: Maybe<&2, Lines.State>,
  u: Maybe<&2, Lines.Rule>
) -> Maybe<&2, Open>:
  match m u:
    case Some{Lines.State{vs, k}} Some{Lines.Rule{g, +ns}}:
      Shared.Maybe.when(
        Open,
        List.contains(~String, ~String.eq, ns, name),
        u2 => Some{Open{vs, k, ns}}
      )
    case _ _:
      None{}

# the rule m that the table holds, or else the rule of the next version of
# the line c in the state st
def Work.rule.or(
  m: Maybe<&2, Lines.Rule>,
  +kn: Known.Known(),
  +s: Facts.Plain(),
  +c: Ledgers.Line,
  st: Maybe<&2, Lines.State>
) -> Maybe<&2, Lines.Rule>:
  match m:
    case Some{u}:
      Some{u}
    case None{}:
      Work.rule(kn, s, c, st)

# the next slot of the line c, when the node name is one of the nodes that
# decide it
def Work.open(+kn: Known.Known(), +s: Facts.Plain(), +name: String, +c: Ledgers.Line) -> Maybe<&2, Open>:
  +st = Known.Known.state(kn, s, c)
  Work.open.at(name, st, Work.rule.or(Known.Known.ruled(kn, c), kn, s, c, st))

# the ballots that s holds for the slot k of the line c
def Work.ballots(s: Facts.Plain(), +c: Ledgers.Line, +k: Nat) -> List<&2, Rounds.Ballot>:
  Rounds.Slot.ballots(Facts.Facts.list(s), c, k)

# the plan to cast the ballot m, if any, for the slot k of the line c
def Plan.of(c: Ledgers.Line, k: Nat, m: Maybe<&2, Rounds.Draft>) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{Rounds.Draft{t, x}}:
      Some{Plan{Types.Step.At{c, k, t}, x}}

# the vote for the pick that pk gives, when the chance m to lead a round
# leaves the node free
def Work.offer.of(pk: Unit -> Types.Pick, m: Maybe<&2, Rounds.Chance>) -> Maybe<&2, Rounds.Draft>:
  match m:
    case Some{Rounds.Chance{t, r, basis, Rounds.Force.Free{}}}:
      Some{Rounds.Draft{t, Types.Cast.Vote{r, pk(Unit{}), basis}}}
    case _:
      None{}

# the vote of the node name for the ask a at the next slot m of the line c:
# when it is its turn, the votes of the rounds before leave it free, and the
# request made no version of the line yet
def Work.offer.at(
  +kn: Known.Known(), +s: Facts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, Open>
) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{Open{+vs, +k, +ns}}:
      Shared.Maybe.when(
        Plan,
        Bool.not(Known.Known.made(kn, c, vs, Lines.Ask.id(a))),
        u => Plan.of(
          c,
          k,
          Work.offer.of(
            u2 => Types.Pick{a, Pins.for(kn, s, c, vs, Era.now(kn, s, c), Lines.Ask.request(a))},
            Rounds.Slot.chance(Work.ballots(s, c, k), ns, k, name)
          )
        )
      )

# the vote of the node name for the ask a, on the line m that it is for
def Work.offer.on(
  +kn: Known.Known(), +s: Facts.Plain(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Work.offer.at(kn, s, name, c, a, Work.open(kn, s, name, c))

# the vote that the node name may cast for the ask a, where all is the facts
# of s
def Work.offer(
  +kn: Known.Known(), +s: Facts.Plain(),
  all: List<&2, Types.Fact>,
  +name: String,
  +a: Types.Ask
) -> Maybe<&2, Plan>:
  Work.offer.on(kn, s, name, a, Request.line(all, Lines.Ask.request(a)))

# the asks among fs that the node name may vote for, where all is the facts
# of s
def Work.ready(
  fs: List<&2, Types.Fact>,
  +kn: Known.Known(), +s: Facts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String
) -> List<&2, Types.Ask>:
  match fs:
    case Nil{}:
      []
    case Con{Types.Fact.Vote{v, st, x}, rest}:
      Work.ready(rest, kn, s, all, name)
    case Con{Types.Fact.Ask{+a}, rest}:
      List.filter.put(
        Types.Ask,
        a,
        Work.ready(rest, kn, s, all, name),
        Maybe.is_some(&2, Plan, Work.offer(kn, s, all, name, a))
      )

# the vote of the node name for the ask m, if any, where all is the facts of
# s
def Work.propose.of(
  m: Maybe<&2, Types.Ask>,
  +kn: Known.Known(), +s: Facts.Plain(),
  all: List<&2, Types.Fact>,
  +name: String
) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{a}:
      Work.offer(kn, s, all, name, a)

# the vote that the node name proposes: for the ask that it took in last,
# among those that it may vote for
def Work.propose(+kn: Known.Known(), +s: Facts.Plain(), +name: String) -> Maybe<&2, Plan>:
  +all = Facts.Facts.list(s)
  Work.propose.of(
    Lists.List.top(~Types.Ask, ~Facts.Ask.seq, Work.ready(all, kn, s, all, name)),
    kn, s,
    all,
    name
  )

# the vote of the node name at the slot k of the line c, when it is the next
# slot m of the line: as a sound vote that it holds, or as the votes of the
# rounds before bind it
def Work.follow.at(
  +s: Facts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  +k: Nat,
  m: Maybe<&2, Open>
) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{Open{vs, k2, +ns}}:
      Shared.Maybe.when(
        Plan,
        Nat.is_eq(k2, k),
        u => Plan.of(c, k, Rounds.Slot.follow(Work.ballots(s, c, k), ns, k, name))
      )

# the vote of the node name at the slot of the fact f, if f is a ballot
def Work.follow.of(+kn: Known.Known(), +s: Facts.Plain(), +name: String, f: Types.Fact) -> Maybe<&2, Plan>:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, +k, t}, x}:
      Work.follow.at(s, name, c, k, Work.open(kn, s, name, c))
    case _:
      None{}

# the plan m, or else the one that rest gives
def Work.follow.or(m: Maybe<&2, Plan>, rest: Unit -> Maybe<&2, Plan>) -> Maybe<&2, Plan>:
  match m:
    case Some{f}:
      Some{f}
    case None{}:
      rest(Unit{})

# the first vote that the node name may cast at the slot of a ballot among fs
def Work.follow(+kn: Known.Known(), +s: Facts.Plain(), +name: String, fs: List<&2, Types.Fact>) -> Maybe<&2, Plan>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Work.follow.or(Work.follow.of(kn, s, name, f), u => Work.follow(kn, s, name, rest))

# the pass of the node name at the next slot m of the line c: when it is the
# slot k, if any, and the request of the id i, if any, made no version of
# the line yet, as read through the table kn
def Work.pass.at(
  kn: Known.Known(),
  +s: Facts.Plain(),
  +name: String,
  +c: Ledgers.Line,
  k: Maybe<&2, Nat>,
  i: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Open>
) -> Maybe<&2, Plan>:
  match k i m:
    case _ _ None{}:
      None{}
    case Some{k1} _ Some{Open{vs, +k2, ns}}:
      Shared.Maybe.when(
        Plan,
        Nat.is_eq(k2, k1),
        u => Plan.of(c, k2, Rounds.Slot.pass(Work.ballots(s, c, k2), name))
      )
    case None{} Some{id} Some{Open{vs, +k2, ns}}:
      Shared.Maybe.when(
        Plan,
        Bool.not(Known.Known.made(kn, c, vs, id)),
        u => Plan.of(c, k2, Rounds.Slot.pass(Work.ballots(s, c, k2), name))
      )
    case None{} None{} _:
      None{}

# the pass of the node name for the request of the id i, on the line m that
# it is for
def Work.pass.on(
  +kn: Known.Known(), +s: Facts.Plain(),
  +name: String,
  i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Line>
) -> Maybe<&2, Plan>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Work.pass.at(kn, s, name, c, None{}, Some{i}, Work.open(kn, s, name, c))

# the pass of the node name at the slot that the fact f is about: the slot
# of a ballot, or the next slot of the line of a request that waits; all is
# the facts of s
def Work.pass.of(
  f: Types.Fact,
  +kn: Known.Known(), +s: Facts.Plain(),
  all: List<&2, Types.Fact>,
  +name: String
) -> Maybe<&2, Plan>:
  match f:
    case Types.Fact.Vote{v, Types.Step.At{+c, k, t}, x}:
      Work.pass.at(kn, s, name, c, Some{k}, None{}, Work.open(kn, s, name, c))
    case Types.Fact.Vote{v, Types.Step.Broken{}, x}:
      None{}
    case Types.Fact.Ask{Types.Ask{i, n, +r}}:
      Work.pass.on(kn, s, name, i, Request.line(all, r))

# the first pass that the node name may cast at the slot of a fact among fs,
# where all is the facts of s
def Work.pass(
  fs: List<&2, Types.Fact>,
  +kn: Known.Known(), +s: Facts.Plain(),
  +all: List<&2, Types.Fact>,
  +name: String
) -> Maybe<&2, Plan>:
  match fs:
    case Nil{}:
      None{}
    case Con{f, rest}:
      Work.follow.or(Work.pass.of(f, kn, s, all, name), u => Work.pass(rest, kn, s, all, name))

# the first pass that the node name may cast at the slot of a fact of s, the
# facts all
def Work.pass.all(+all: List<&2, Types.Fact>, +kn: Known.Known(), +s: Facts.Plain(), +name: String) -> Maybe<&2, Plan>:
  Work.pass(all, kn, s, all, name)

# the ballot that the node name casts next: the vote that it proposes, else
# a vote at a slot that it holds a ballot for, else a pass at a slot that
# waits
def Work.plan(+kn: Known.Known(), +s: Facts.Plain(), +name: String) -> Maybe<&2, Plan>:
  Work.follow.or(
    Work.propose(kn, s, name),
    u => Work.follow.or(
      Work.follow(kn, s, name, Facts.Facts.list(s)),
      u2 => Work.pass.all(Facts.Facts.list(s), kn, s, name)
    )
  )

# the facts s with the ballot m, if any, of the node name: unless s holds a
# ballot of the node with the same number
def Work.cast(+s: Facts.Plain(), +name: String, m: Maybe<&2, Plan>) -> Facts.Plain():
  match m:
    case None{}:
      s
    case Some{Plan{+st, x}}:
      Shared.Bool.when(
        Facts.Plain(),
        Facts.Facts.cast(s, name, st),
        u => s,
        u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})
      )

# the facts s after a work of the node name
def Work.does(+kn: Known.Known(), +s: Facts.Plain(), +name: String) -> Facts.Plain():
  Work.cast(s, name, Work.plan(kn, s, name))
