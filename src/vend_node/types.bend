import Base
import ../shared/shared/ledger.bend as Ledgers
import ./spec.bend as Spec

# The words of the core of a Vend Node
# ------------------------------------
# A node holds facts: requests, as writers asked for them, and votes. All
# that a node answers is a function of the set of its facts.

# a request as a node took it in: its id, the number that the node gave it
# (above every number that the node had seen), and what it asks for
type Ask is Data:
  Ask{id: Ledgers.Id, seq: Nat, request: Spec.Request}

# what the voters of a step fix beside its request. era: the version of the
# store whose groups decide the next versions of the line (it never goes
# back). For a merge: from is the version of the other line that it takes,
# base the version that both come from (none: they share none), and ours and
# theirs the ways back to it from each side
type Pins is Data:
  Pins{
    era: Nat,
    from: Nat,
    base: Maybe<&2, Spec.Point>,
    ours: List<&2, Spec.Point>,
    theirs: List<&2, Spec.Point>
  }

# what a vote is for: a request, with its pins
type Pick is Data:
  Pick{ask: Ask, pins: Pins}

# where a ballot is cast. At: the slot of a line (a slot makes the next
# version of the line, or none when its request already made one), and the
# number of the ballot among those of its voter for the slot: 0, 1, 2, ...
# Broken: no decision; the ballots of a node that saw its trust break (Trust)
type Step is Data:
  Step.At{line: Ledgers.Line, slot: Nat, turn: Nat}
  Step.Broken{}

# the ballots of a voter for a slot, up to (not with) the one of the number
# turn
type Ref is Data:
  Ref{voter: String, turn: Nat}

# what a voter casts for a slot. A slot is decided in rounds: 0, 1, 2, ...
# Vote: for the pick, in the round. Pass: the voter leaves the rounds below
# round. The basis of the vote of the node whose turn a round above 0 is: for
# other nodes of the slot, ballots of theirs after which they vote in no
# round below
type Cast is Data:
  Cast.Vote{round: Nat, pick: Pick, basis: List<&2, Ref>}
  Cast.Pass{round: Nat}

# what a node holds
type Fact is Data:
  Fact.Ask{ask: Ask}
  Fact.Vote{voter: String, step: Step, cast: Cast}

# what nodes share: a fact, or the two ballots of a voter that lied
type Change is Data:
  Change.Fact{fact: Fact}
  Change.Lie{voter: String, step: Step, one: Cast, two: Cast}

# a version of a line: the pick that made it, and the slot that decided it
type Entry is Data:
  Entry{pick: Pick, slot: Nat}
