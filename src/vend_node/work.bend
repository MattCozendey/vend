import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/shared.bend as Shared
import ./content.bend as Contents
import ./facts.bend as Facts
import ./lines.bend as Lines
import ./run/content.bend as RContents
import ./run/facts.bend as RFacts
import ./run/lines.bend as RLines
import ./run/work.bend as RWorks
import ./shared/lists.bend as Lists
import ./spec.bend as Spec
import ./types.bend as Types

# Work
# ----
# What a node does by itself: it casts at most one vote per work, under its
# own name, for the next slot of a line that it decides, and only when it
# holds no vote of its own for that slot. So it never casts two votes for one
# slot. The nodes of a slot take turns: the node whose turn it is proposes the
# request that it took in last; the others vote as it did. So the votes of
# nodes that follow this never split.
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
  RWorks.Pins.for(Facts.Facts.crit(s), c, vs, m, r)

# the era that the node pins for the line c: the newest version of its store
# that it holds
def Era.now(+s: Facts.Facts(), c: Ledgers.Line) -> Nat:
  RWorks.Era.now(Facts.Facts.crit(s), c)

# The next vote
# -------------

# the node name may vote for the next slot of the line c, in the state st: it
# is one of the nodes of the rule u, and holds no vote of its own for the slot
def Work.free(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  k: Nat,
  ns: List<&2, String>
) -> Bool:
  RWorks.Work.free(Facts.Facts.crit(s), name, c, k, ns)

# the vote of the node name for the ask a at the next slot of the line c, in
# the state m with the rule u, when it is its turn, it may vote, and the
# request made no version of the line yet
def Work.offer.at(
  +s: Facts.Facts(),
  +name: String,
  +c: Ledgers.Line,
  +a: Types.Ask,
  m: Maybe<&2, RLines.State>,
  u: Maybe<&2, RLines.Rule>
) -> Maybe<&2, Types.Fact>:
  RWorks.Work.offer.at(Facts.Facts.crit(s), name, c, a, m, u)

# the rule of the next version of the line c, in the state m
def Work.rule(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, RLines.State>
) -> Maybe<&2, RLines.Rule>:
  RWorks.Work.rule(Facts.Facts.crit(s), c, m)

# the vote of the node name for the ask a, on the line m that it is for
def Work.offer.on(
  +s: Facts.Facts(),
  +name: String,
  +a: Types.Ask,
  m: Maybe<&2, Ledgers.Line>
) -> Maybe<&2, Types.Fact>:
  RWorks.Work.offer.on(Facts.Facts.crit(s), name, a, m)

# the vote that the node name may cast for the ask a
def Work.offer(+s: Facts.Facts(), +name: String, +a: Types.Ask) -> Maybe<&2, Types.Fact>:
  RWorks.Work.offer(Facts.Facts.crit(s), name, a)

# the asks among fs that the node name may vote for
def Work.ready(+s: Facts.Facts(), +name: String, fs: List<&2, Types.Fact>) -> List<&2, Types.Ask>:
  RWorks.Work.ready(Facts.Facts.crit(s), name, fs)

# the vote of the node name for the ask m, if any
def Work.propose.of(
  +s: Facts.Facts(),
  +name: String,
  m: Maybe<&2, Types.Ask>
) -> Maybe<&2, Types.Fact>:
  RWorks.Work.propose.of(Facts.Facts.crit(s), name, m)

# the vote that the node name proposes: for the ask that it took in last,
# among those that it may vote for
def Work.propose(+s: Facts.Facts(), +name: String) -> Maybe<&2, Types.Fact>:
  RWorks.Work.propose(Facts.Facts.crit(s), name)

# the vote of the node name that follows the vote of v for the pick pk at the
# slot k of the line c, in the state m with the rule u: when the slot is the
# next one, it was the turn of v, and the node may vote
def Work.follow.at(
  +s: Facts.Facts(),
  +name: String,
  v: String,
  +c: Ledgers.Line,
  +k: Nat,
  pk: Types.Pick,
  m: Maybe<&2, RLines.State>,
  u: Maybe<&2, RLines.Rule>
) -> Maybe<&2, Types.Fact>:
  RWorks.Work.follow.at(Facts.Facts.crit(s), name, v, c, k, pk, m, u)

# the vote of the node name that follows the fact f, if f is a vote to follow
def Work.follow.of(+s: Facts.Facts(), +name: String, f: Types.Fact) -> Maybe<&2, Types.Fact>:
  RWorks.Work.follow.of(Facts.Facts.crit(s), name, f)

# the first vote that the node name may cast to follow a vote among fs
def Work.follow(
  +s: Facts.Facts(),
  +name: String,
  fs: List<&2, Types.Fact>
) -> Maybe<&2, Types.Fact>:
  RWorks.Work.follow(Facts.Facts.crit(s), name, fs)

# the vote that the node name casts next: the one that it proposes, else one
# that follows a vote that it holds
def Work.vote(+s: Facts.Facts(), +name: String) -> Maybe<&2, Types.Fact>:
  RWorks.Work.vote(Facts.Facts.crit(s), name)

# the facts s after a work of the node name
def Work.does.of(s: Facts.Facts(), m: Maybe<&2, Types.Fact>) -> Facts.Facts():
  match m:
    case None{}:
      s
    case Some{f}:
      Facts.Facts.add(s, f)

# the facts s after a work of the node name
def Work.does(+s: Facts.Facts(), +name: String) -> Facts.Facts():
  Work.does.of(s, Work.vote(s, name))

# Laws of the maps
# ----------------

# the map of the facts after a vote m is what the code that runs gives
def Work.does.of_crit(
  -s: Facts.Facts(),
  m: Maybe<&2, Types.Fact>
) -> {
  Facts.Facts.crit(Work.does.of(s, m)) == RWorks.Work.does.of(Facts.Facts.crit(s), m): RFacts.Plain()
}:
  match m:
    case None{}:
      {==}
    case Some{f}:
      {==}

# the map of the facts after a work is what the code that runs gives
def Work.does_crit(
  +s: Facts.Facts(),
  +name: String
) -> {
  Facts.Facts.crit(Work.does(s, name)) == RWorks.Work.does(Facts.Facts.crit(s), name): RFacts.Plain()
}:
  Work.does.of_crit(s, Work.vote(s, name))
