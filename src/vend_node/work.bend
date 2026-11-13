import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Work
# ----
# What a node does by itself: it casts at most one ballot per work, under
# its own name, for the next slot of a line that it decides, with a number
# that it holds no ballot of its own with. So it never casts two ballots with
# one number. A slot is decided in rounds (run/rounds.bend): the node whose
# turn a round is proposes the request that it took in last, or what the
# votes of the rounds before bind it to; the others vote as it did, and a
# node that has nothing to vote for passes to a later round.
#
# The code that runs is in run/work.bend: it reads the plain map of the facts
# and builds no proof. Here each def that reads the facts is that code on the
# map of a set of facts (Facts.crit), so the laws said of the set are laws of
# the code that runs.

# Pins
# ----

# the pins that the node gives the request r for the line c, of the versions
# vs, at the era m
def Pins.for(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>,
  m: Nat,
  r: Spec.Request
) -> Types.Pins:
  RWorks.Pins.for(RKnown.Known.none(), Facts.Facts.crit(s), c, vs, m, r)

# the era that the node pins for the line c: the newest version of its store
# that it holds
def Era.now(+s: Facts.Facts(), c: Ledgers.Line) -> Nat:
  RWorks.Era.now(RKnown.Known.none(), Facts.Facts.crit(s), c)

# The next ballot
# ---------------

# the rule of the next version of the line c, in the state m
def Work.rule(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> Maybe<&2, RLines.Rule>:
  RWorks.Work.rule(RKnown.Known.none(), Facts.Facts.crit(s), c, m)

# the next slot of the line c, when the node name is one of the nodes that
# decide it
def Work.open(+s: Facts.Facts(), +name: String, +c: Ledgers.Line) -> Maybe<&2, RWorks.Open>:
  RWorks.Work.open(RKnown.Known.none(), Facts.Facts.crit(s), name, c)

# the vote of the node name for the ask a at the next slot m of the line c:
# when it is its turn, the votes of the rounds before leave it free, and the
# request made no version of the line yet
def Work.offer.at(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RWorks.Open>
) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.offer.at(RKnown.Known.none(), Facts.Facts.crit(s), name, c, a, m)

# the vote of the node name for the ask a, on the line m that it is for
def Work.offer.on(
  +s: Facts.Facts(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.offer.on(RKnown.Known.none(), Facts.Facts.crit(s), name, a, m)

# the vote that the node name may cast for the ask a
def Work.offer(+s: Facts.Facts(), +name: String, +a: Types.Ask) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.offer(RKnown.Known.none(), Facts.Facts.crit(s), name, a)

# the asks among fs that the node name may vote for
def Work.ready(+s: Facts.Facts(), +name: String, fs: List<&2, Types.Fact>) -> List<&2, Types.Ask>:
  RWorks.Work.ready(RKnown.Known.none(), Facts.Facts.crit(s), name, fs)

# the vote of the node name for the ask m, if any
def Work.propose.of(
  +s: Facts.Facts(),
  +name: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.propose.of(RKnown.Known.none(), Facts.Facts.crit(s), name, m)

# the vote that the node name proposes: for the ask that it took in last,
# among those that it may vote for
def Work.propose(+s: Facts.Facts(), +name: String) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.propose(RKnown.Known.none(), Facts.Facts.crit(s), name)

# the ballot that the node name casts next: the vote that it proposes, else
# a vote at a slot that it holds a ballot for, else a pass at a slot that
# waits
def Work.plan(+s: Facts.Facts(), +name: String) -> Maybe<&2, RWorks.Plan>:
  RWorks.Work.plan(RKnown.Known.none(), Facts.Facts.crit(s), name)

# the facts s with the ballot m, if any, of the node name: unless s holds a
# ballot of the node with the same number
def Work.cast(+s: Facts.Facts(), +name: String, m: Maybe<&2, RWorks.Plan>) -> Facts.Facts():
  match m:
    case None{}:
      s
    case Some{RWorks.Plan{+st, x}}:
      Shared.Bool.when(
        Facts.Facts(),
        Facts.Facts.cast(s, name, st),
        u => s,
        u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})
      )

# the facts s after a work of the node name
def Work.does(+s: Facts.Facts(), +name: String) -> Facts.Facts():
  Work.cast(s, name, Work.plan(s, name))

# Laws of the maps
# ----------------

# the map of the facts with a ballot m is what the code that runs gives
def Work.cast_crit(
  +s: Facts.Facts(),
  +name: String,
  m: Maybe<&2, RWorks.Plan>
) -> {
  Facts.Facts.crit(Work.cast(s, name, m)) == RWorks.Work.cast(Facts.Facts.crit(s), name, m): RFacts.Plain()
}:
  match m:
    case None{}:
      {==}
    case Some{RWorks.Plan{+st, +x}}:
      Lists.Bool.by(
        b => {
          Facts.Facts.crit(
            Shared.Bool.when(
              Facts.Facts(),
              b,
              u => s,
              u => Facts.Facts.add(s, Types.Fact.Vote{name, st, x})
            )
          )
            == Shared.Bool.when(
              RFacts.Plain(),
              b,
              u => Facts.Facts.crit(s),
              u => RFacts.Facts.add(Facts.Facts.crit(s), Types.Fact.Vote{name, st, x})
            ): RFacts.Plain()
        },
        Facts.Facts.cast(s, name, st),
        et => {==},
        ef => {==}
      )

# the map of the facts after a work is what the code that runs gives
def Work.does_crit(
  +s: Facts.Facts(),
  +name: String
) -> {
  Facts.Facts.crit(Work.does(s, name)) == RWorks.Work.does(RKnown.Known.none(), Facts.Facts.crit(s), name): RFacts.Plain()
}:
  Work.cast_crit(s, name, Work.plan(s, name))
