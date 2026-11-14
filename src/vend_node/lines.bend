import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ./facts.bend as Facts
import ./run/lines.bend as RLines
import ./types.bend as Types

# Lines
# -----
# The versions of a line are read from the facts. Version 0 needs no vote: of
# a store, it is the request that started it; of a branch, the first request
# of the store that owns it. Each later version is made by a slot of the line:
# the pick that more than half of the nodes that decide the slot voted for
# in one round (run/rounds.bend). A slot whose request already made a version
# of the line makes none, so a request counts once. Owners are trusted only
# to cast no two votes for one slot: what a decided request does is read by
# every node, from the versions.
#
# The code that runs is in run/lines.bend: it reads the plain map of the facts
# and builds no proof. Here each def that reads the facts is that code on the
# map of a set of facts (Facts.crit), so the laws said of the set are laws of
# the code that runs.

# Votes
# -----

# the pick that the nodes ds decided for the slot k of the line c, in the
# facts s
def Votes.decided(
  +s: Facts.Facts(),
  c: Ledgers.Line,
  +k: Nat,
  +ds: List<&2, String>
) -> Maybe<&2, Types.Pick>:
  RLines.Votes.decided(Facts.Facts.crit(s), c, k, ds)

# Slots
# -----

# the state after the next slot of st, once the rule u of the slot is known
def Line.step.at(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +st: RLines.State,
  u: Maybe<&2, RLines.Rule>
) -> Maybe<&2, RLines.State>:
  RLines.Line.step.at(Facts.Facts.crit(s), c, st, u)

# the state of the line c after the next slot of st (nothing while the slot is
# not decided, or who decides it is not known)
def Line.step(
  +s: Facts.Facts(),
  r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> Maybe<&2, RLines.State>:
  RLines.Line.step(Facts.Facts.crit(s), r, c, st)

# the state of the line c after each decided slot from st on, at most fuel of
# them; m is the state after the next slot of st, if it is decided
def Line.run(
  fuel: Nat,
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  st: RLines.State,
  m: Maybe<&2, RLines.State>
) -> RLines.State:
  RLines.Line.run(fuel, Facts.Facts.crit(s), r, c, st, m)

# The versions of a line
# ----------------------

# the state of the line c after each decided slot from st on
def Line.start(
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  +st: RLines.State
) -> RLines.State:
  RLines.Line.start(Facts.Facts.crit(s), r, c, st)

# the state of a line from its version 0 on, if it has one
def Line.from(
  +s: Facts.Facts(),
  +r: Maybe<&2, List<&2, Types.Entry>>,
  +c: Ledgers.Line,
  m: Maybe<&2, Types.Entry>
) -> Maybe<&2, RLines.State>:
  RLines.Line.from(Facts.Facts.crit(s), r, c, m)

# the state of the store of the root h
def Store.state(+s: Facts.Facts(), +h: Hashes.Hash) -> Maybe<&2, RLines.State>:
  RLines.Store.state(Facts.Facts.crit(s), h)

# the versions of the store of the root h
def Store.versions(+s: Facts.Facts(), +h: Hashes.Hash) -> Maybe<&2, List<&2, Types.Entry>>:
  RLines.Store.versions(Facts.Facts.crit(s), h)

# the state of the branch c, once the versions m of its store are known
def Branch.state(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  m: Maybe<&2, List<&2, Types.Entry>>
) -> Maybe<&2, RLines.State>:
  RLines.Branch.state(Facts.Facts.crit(s), c, m)

# the state of the line c in the facts s (nothing while s does not hold its
# version 0)
def Line.state(+s: Facts.Facts(), +c: Ledgers.Line) -> Maybe<&2, RLines.State>:
  RLines.Line.state(Facts.Facts.crit(s), c)

# the versions of the line c in the facts s, oldest first
def Line.versions(+s: Facts.Facts(), +c: Ledgers.Line) -> Maybe<&2, List<&2, Types.Entry>>:
  RLines.Line.versions(Facts.Facts.crit(s), c)

# version k of the line c in the facts s
def Line.at(+s: Facts.Facts(), +c: Ledgers.Line, k: Nat) -> Maybe<&2, Types.Entry>:
  RLines.Line.at(Facts.Facts.crit(s), c, k)

# The rule of the next version
# ----------------------------

# the rule of the version of the line c that comes after the versions vs
def Rule.after(
  +s: Facts.Facts(),
  +c: Ledgers.Line,
  +vs: List<&2, Types.Entry>
) -> Maybe<&2, RLines.Rule>:
  RLines.Rule.after(Facts.Facts.crit(s), c, vs)

# the state of the line c after the next slot of st
def Line.next(+s: Facts.Facts(), +c: Ledgers.Line, +st: RLines.State) -> Maybe<&2, RLines.State>:
  RLines.Line.next(Facts.Facts.crit(s), c, st)
