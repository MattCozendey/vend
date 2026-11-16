import Base
import ../shared/monotone_queries/spec.bend as MonotoneQueries
import ../shared/shared/shared/word_list_sets/spec.bend as WordListSets

# Slot consensus decides, for each step (a slot of a line), one
# choice (words), by the ballots of the voters of that step. The voters are a
# parameter: a module above says who they are.
#
# The rule, Paxos with chains:
# - A voter's ballots for a step form a chain, indexed 0, 1, 2... A ballot is
#   judged only when the voter's ballots of every lower index are there.
# - Rounds are numbered. The leader of round r is the voter at r modulo their
#   number. A voter joins a round (JoinRound), the leader leads it
#   (LeadRound), and voters vote for the lead's choice (VoteForLead).
# - A lead names, as its basis, voters that joined its round. It is judged once
#   every voter of its basis joined, with its ballots below its join there and
#   every vote that it cast before its join judged. It is sound when its basis
#   holds more than half of the voters, and its choice is that of the highest
#   sound vote that those voters cast before they joined (any choice if none).
# - A vote, or a lead (the leader's own vote), is placed when its voter had not
#   joined a higher round before it. A vote is sound when it is placed and the
#   leader's lead of its round is sound and has its choice.
# - A step is decided for a choice when more than half of the voters cast sound
#   votes for it in one round.
# - Two ballots of one voter for one step contradict when they have one index
#   but differ, or lead one round with different choices. A voter that signs
#   two such ballots lied, and the step's answer is Contradicted, with their keys.
#
# Each ballot is judged sound, unsound, or not yet: a judgment waits until all
# that it rests on is there, and never changes after. Ballots of voters that
# are not voters of the step count for nothing, so strangers change nothing.

# what a ballot does
type BallotAction is Data:
  JoinRound{}
  LeadRound{choice: List<&2, U32>, basis: List<&2, List<&2, U32>>}
  VoteForLead{choice: List<&2, U32>}

# a step: the slot number slot of the line named line
type Step is Data:
  Step{line: List<&2, U32>, slot: Nat}

# a and b are the same step
def Step.same(a: Step, b: Step) -> Bool:
  match a b:
    case Step{la, na} Step{lb, nb}:
      Bool.and(WordListSets.same(la, lb), Nat.is_eq(na, nb))

# a ballot: the key of the record it comes from, its voter, its step, its index in
# the voter's chain for the step, its round, and what it does
type Ballot is Data:
  Ballot{
    key: List<&2, U32>,
    voter: List<&2, U32>,
    step: Step,
    index: Nat,
    round: Nat,
    cast: BallotAction
  }

# a ballot that is judged: sound or not
type JudgedBallot is Data:
  JudgedBallot{ballot: Ballot, sound: Bool}

# what the sound votes that a set of voters cast before they joined a round
# say: whether all of those votes are judged yet, and the round and choice of
# the highest sound one, if any
type VotesBeforeJoin is Data:
  VotesBeforeJoin{known: Bool, best: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- this is the reference rule that SlotConsensus.decision_is_monotone states; the code that runs is a fast incremental version proven equal to it (IncrementalStateMatchesQuery), so what this rule computes in excess costs nothing at run time
# Ballots
# -------

# the key of the record of b
def Ballot.key(b: Ballot) -> List<&2, U32>:
  match b:
    case Ballot{k, v, s, i, r, c}:
      k

# a and b are the same cast
def BallotAction.same(a: BallotAction, b: BallotAction) -> Bool:
  match a b:
    case JoinRound{} JoinRound{}:
      True{}
    case LeadRound{x, xs} LeadRound{y, ys}:
      Bool.and(WordListSets.same(x, y), WordListSets.same_lists(xs, ys))
    case VoteForLead{x} VoteForLead{y}:
      WordListSets.same(x, y)
    case _ _:
      False{}

# the voter of the ballot b
def Ballot.voter(b: Ballot) -> List<&2, U32>:
  match b:
    case Ballot{k, v, s, i, r, c}:
      v

# a and b are the same ballot
def Ballot.same(a: Ballot, b: Ballot) -> Bool:
  match a b:
    case Ballot{ka, va, sa, ia, ra, ca} Ballot{kb, vb, sb, ib, rb, cb}:
      Bool.and(
        Bool.and(WordListSets.same(ka, kb), Bool.and(WordListSets.same(va, vb), Step.same(sa, sb))),
        Bool.and(Bool.and(Nat.is_eq(ia, ib), Nat.is_eq(ra, rb)), BallotAction.same(ca, cb))
      )

# c is a lead
def BallotAction.is_lead(c: BallotAction) -> Bool:
  match c:
    case LeadRound{x, xs}:
      True{}
    case _:
      False{}

# a and b, two ballots of one voter for one step, contradict: one index but
# different rounds or casts, or leads of one round with different choices
def Ballot.contradicts(a: Ballot, b: Ballot) -> Bool:
  match a b:
    case Ballot{ka, va, sa, ia, ra, +ca} Ballot{kb, vb, sb, ib, rb, +cb}:
      +same_round = Nat.is_eq(ra, rb)
      +same_cast = BallotAction.same(ca, cb)
      Bool.and(
        Bool.and(WordListSets.same(va, vb), Step.same(sa, sb)),
        Bool.or(
          Bool.and(Nat.is_eq(ia, ib), Bool.not(Bool.and(same_round, same_cast))),
          Bool.and(
            Bool.and(same_round, Bool.and(BallotAction.is_lead(ca), BallotAction.is_lead(cb))),
            Bool.not(same_cast)
          )
        )
      )

# the ballot b is of a voter of vs, for the step s
def Ballot.is_of(b: Ballot, vs: List<&2, List<&2, U32>>, s: Step) -> Bool:
  match b:
    case Ballot{k, v, st, i, r, c}:
      Bool.and(WordListSets.contains(vs, v), Step.same(st, s))

# the key of a ballot of all that contradicts a, if any
def Ballots.contradicting(all: List<&2, Ballot>, +a: Ballot) -> Maybe<&2, List<&2, U32>>:
  match all:
    case Nil{}:
      None{}
    case Con{+b, rest}:
      Bool.pick(
        Maybe<&2, List<&2, U32>>,
        Ballot.contradicts(a, b),
        Some{Ballot.key(b)},
        Ballots.contradicting(rest, a)
      )

# the keys k and the key of the ballot that k contradicts, if any
def Ballots.lie.proof(
  k: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{j}:
      Some{[k, j]}

# the keys of two ballots of all that contradict each other, the first of them
# a ballot of bs by a voter of vs for the step s, if any
def Ballots.lie(
  bs: List<&2, Ballot>,
  +vs: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match bs:
    case Nil{}:
      None{}
    case Con{+b, rest}:
      Maybe.or(
        &2,
        List<&2, List<&2, U32>>,
        Bool.pick(
          Maybe<&2, List<&2, List<&2, U32>>>,
          Ballot.is_of(b, vs, s),
          Ballots.lie.proof(Ballot.key(b), Ballots.contradicting(all, b)),
          None{}
        ),
        Ballots.lie(rest, vs, s, all)
      )

# Chains
# ------

# all has a ballot of the voter v for the step s with the index i
def Ballots.has_index(all: List<&2, Ballot>, +v: List<&2, U32>, +s: Step, +i: Nat) -> Bool:
  match all:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, j, r, c}, rest}:
      Bool.or(
        Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_eq(j, i)),
        Ballots.has_index(rest, v, s, i)
      )

# all has the ballots of the voter v for the step s of every index below i
def Ballots.chain_below(+i: Nat, +all: List<&2, Ballot>, +v: List<&2, U32>, +s: Step) -> Bool:
  match i:
    case 0n:
      True{}
    case 1n+j:
      Bool.and(Ballots.has_index(all, v, s, j), Ballots.chain_below(j, all, v, s))

# the voter v joined, for the step s, a round above r with a ballot of an index
# below i
def Ballots.joined_above(
  all: List<&2, Ballot>,
  +v: List<&2, U32>,
  +s: Step,
  +r: Nat,
  +i: Nat
) -> Bool:
  match all:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, j, q, c}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_lt(j, i)),
          Bool.and(Nat.is_lt(r, q), BallotAction.same(c, JoinRound{}))
        ),
        Ballots.joined_above(rest, v, s, r, i)
      )

# the lower of two numbers, either of which may be missing
def Nat.min_some(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a b:
    case None{} b:
      b
    case a None{}:
      a
    case Some{+x} Some{+y}:
      Some{Bool.pick(Nat, Nat.is_le(x, y), x, y)}

# the lowest index of a Join of round r by the voter v for the step s whose
# chain below is all there, if any
def Ballots.first_join(
  bs: List<&2, Ballot>,
  +all: List<&2, Ballot>,
  +v: List<&2, U32>,
  +s: Step,
  +r: Nat
) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{Ballot{k, w, st, +j, q, c}, rest}:
      here = Bool.and(
        Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_eq(q, r)),
        Bool.and(BallotAction.same(c, JoinRound{}), Ballots.chain_below(j, all, v, s))
      )
      Nat.min_some(
        Bool.pick(Maybe<&2, Nat>, here, Some{j}, None{}),
        Ballots.first_join(rest, all, v, s, r)
      )

# Rounds
# ------

# the voter at index k of vs, if any
def voter_at(vs: List<&2, List<&2, U32>>, k: Nat) -> Maybe<&2, List<&2, U32>>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, rest}:
      match k:
        case 0n:
          Some{v}
        case 1n+j:
          voter_at(rest, j)

# m is the voter v
def names_voter(m: Maybe<&2, List<&2, U32>>, v: List<&2, U32>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      WordListSets.same(w, v)

# v leads round r among the n voters vs
def leads_round(vs: List<&2, List<&2, U32>>, n: Nat, r: Nat, v: List<&2, U32>) -> Bool:
  names_voter(voter_at(vs, Nat.mod(r, n)), v)

# n is less than twice c: c is more than half of n
def is_more_than_half(c: Nat, n: Nat) -> Bool:
  Nat.is_lt(n, Nat.mul(2n, c))

# Judging
# -------

# the higher of two rounds with their choices, the first on a tie
def VotesBeforeJoin.higher(
  a: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>,
  b: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>
) -> Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>:
  match a b:
    case None{} b:
      b
    case a None{}:
      a
    case Some{(+ra, xa)} Some{(+rb, xb)}:
      Bool.pick(
        Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>,
        Nat.is_le(rb, ra),
        Some{(ra, xa)},
        Some{(rb, xb)}
      )

# a and b together: both known; the higher best, the first on a tie
def VotesBeforeJoin.join(a: VotesBeforeJoin, b: VotesBeforeJoin) -> VotesBeforeJoin:
  match a b:
    case VotesBeforeJoin{ka, xa} VotesBeforeJoin{kb, xb}:
      VotesBeforeJoin{Bool.and(ka, kb), VotesBeforeJoin.higher(xa, xb)}

# how the judged ballots say a ballot of the voter v for the step s with the
# index i is: sound, unsound, or not judged yet
def JudgedBallot.find(
  js: List<&2, JudgedBallot>,
  +v: List<&2, U32>,
  +s: Step,
  +i: Nat
) -> Maybe<&2, Bool>:
  match js:
    case Nil{}:
      None{}
    case Con{JudgedBallot{Ballot{k, w, st, j, r, c}, ok}, rest}:
      Maybe.or(
        &2,
        Bool,
        Bool.pick(
          Maybe<&2, Bool>,
          Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_eq(j, i)),
          Some{ok},
          None{}
        ),
        JudgedBallot.find(rest, v, s, i)
      )

# what the judgment j of a vote of round r for the choice x adds to priors
def VotesBeforeJoin.of_judgment(j: Maybe<&2, Bool>, r: Nat, x: List<&2, U32>) -> VotesBeforeJoin:
  match j:
    case None{}:
      VotesBeforeJoin{False{}, None{}}
    case Some{True{}}:
      VotesBeforeJoin{True{}, Some{(r, x)}}
    case Some{False{}}:
      VotesBeforeJoin{True{}, None{}}

# what the ballot b says as a vote of the voter v for the step s below the
# index i, as the judged ballots js judge it
def VotesBeforeJoin.of_ballot(
  b: Ballot,
  js: List<&2, JudgedBallot>,
  v: List<&2, U32>,
  s: Step,
  i: Nat
) -> VotesBeforeJoin:
  match b:
    case Ballot{k, +w, +st, +j, r, LeadRound{x, basis}}:
      Bool.pick(
        VotesBeforeJoin,
        Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_lt(j, i)),
        VotesBeforeJoin.of_judgment(JudgedBallot.find(js, w, st, j), r, x),
        VotesBeforeJoin{True{}, None{}}
      )
    case Ballot{k, +w, +st, +j, r, VoteForLead{x}}:
      Bool.pick(
        VotesBeforeJoin,
        Bool.and(Bool.and(WordListSets.same(w, v), Step.same(st, s)), Nat.is_lt(j, i)),
        VotesBeforeJoin.of_judgment(JudgedBallot.find(js, w, st, j), r, x),
        VotesBeforeJoin{True{}, None{}}
      )
    case _:
      VotesBeforeJoin{True{}, None{}}

# what the votes of all of the voter v for the step s below the index i say
def VotesBeforeJoin.below(
  bs: List<&2, Ballot>,
  +js: List<&2, JudgedBallot>,
  +v: List<&2, U32>,
  +s: Step,
  +i: Nat
) -> VotesBeforeJoin:
  match bs:
    case Nil{}:
      VotesBeforeJoin{True{}, None{}}
    case Con{b, rest}:
      VotesBeforeJoin.join(
        VotesBeforeJoin.of_ballot(b, js, v, s, i),
        VotesBeforeJoin.below(rest, js, v, s, i)
      )

# how many voters of us joined round r, and what their votes before they
# joined say
type JoinTally is Data:
  JoinTally{count: Nat, priors: VotesBeforeJoin}

# what the first join of round r of a voter adds to a tally
def JoinTally.of_join(
  m: Maybe<&2, Nat>,
  all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  v: List<&2, U32>,
  s: Step
) -> JoinTally:
  match m:
    case None{}:
      JoinTally{0n, VotesBeforeJoin{False{}, None{}}}
    case Some{i}:
      JoinTally{1n, VotesBeforeJoin.below(all, js, v, s, i)}

# a and b added
def JoinTally.add(a: JoinTally, b: JoinTally) -> JoinTally:
  match a b:
    case JoinTally{ca, pa} JoinTally{cb, pb}:
      JoinTally{Nat.add(ca, cb), VotesBeforeJoin.join(pa, pb)}

# the tally of the voters us (each once), those of vs that joined round r for
# the step s
def JoinTally.of(
  us: List<&2, List<&2, U32>>,
  +all: List<&2, Ballot>,
  +js: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +s: Step,
  +r: Nat
) -> JoinTally:
  match us:
    case Nil{}:
      JoinTally{0n, VotesBeforeJoin{True{}, None{}}}
    case Con{+u, rest}:
      JoinTally.add(
        Bool.pick(
          JoinTally,
          WordListSets.contains(vs, u),
          JoinTally.of_join(Ballots.first_join(all, all, u, s, r), all, js, u, s),
          JoinTally{0n, VotesBeforeJoin{True{}, None{}}}
        ),
        JoinTally.of(rest, all, js, vs, s, r)
      )

# the choice x is the one that priors require
def VotesBeforeJoin.allow(p: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>, x: List<&2, U32>) -> Bool:
  match p:
    case None{}:
      True{}
    case Some{(r, y)}:
      WordListSets.same(x, y)

# the judgment of a lead for the choice x from its tally: not yet while fewer
# than more than half joined, or while a vote before a join is not judged
def Judge.lead.of_tally(t: JoinTally, n: Nat, x: List<&2, U32>) -> Maybe<&2, Bool>:
  match t:
    case JoinTally{c, VotesBeforeJoin{known, best}}:
      Bool.pick(
        Maybe<&2, Bool>,
        Bool.and(is_more_than_half(c, n), known),
        Some{VotesBeforeJoin.allow(best, x)},
        None{}
      )

# the judgment of the ballot b, if it is a lead of round r for the step s by a
# voter of vs, given the judged ballots js of the rounds below
def Judge.lead(
  b: Ballot,
  +all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +s: Step,
  +r: Nat
) -> Maybe<&2, Bool>:
  match b:
    case Ballot{k, +v, st, +i, q, LeadRound{x, basis}}:
      mine = Bool.and(Step.same(st, s), Nat.is_eq(q, r))
      chain = Ballots.chain_below(i, all, v, s)
      placed = Bool.and(leads_round(vs, n, r, v), Bool.not(Ballots.joined_above(all, v, s, r, i)))
      Bool.pick(
        Maybe<&2, Bool>,
        Bool.and(mine, chain),
        Bool.pick(
          Maybe<&2, Bool>,
          placed,
          Judge.lead.of_tally(JoinTally.of(WordListSets.dedupe(basis), all, js, vs, s, r), n, x),
          Some{False{}}
        ),
        None{}
      )
    case _:
      None{}

# the judgment of a vote for the choice x in round r by the judged leads ls of
# that round, of which only the lead of the round's leader among the n voters
# vs counts: sound when that lead is sound and has the choice x, unsound when it
# is judged otherwise, not yet while it is not judged
def Judge.vote.by_leads(
  ls: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +r: Nat,
  +x: List<&2, U32>
) -> Maybe<&2, Bool>:
  match ls:
    case Nil{}:
      None{}
    case Con{JudgedBallot{Ballot{k, v, s, i, q, LeadRound{y, basis}}, ok}, rest}:
      Bool.pick(
        Maybe<&2, Bool>,
        leads_round(vs, n, r, v),
        Some{Bool.and(ok, WordListSets.same(x, y))},
        Judge.vote.by_leads(rest, vs, n, r, x)
      )
    case Con{j, rest}:
      Judge.vote.by_leads(rest, vs, n, r, x)

# the judgment of the ballot b, if it is a vote of round r for the step s by a
# voter of vs, given the judged leads ls of round r
def Judge.vote(
  b: Ballot,
  +all: List<&2, Ballot>,
  ls: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  n: Nat,
  +s: Step,
  +r: Nat
) -> Maybe<&2, Bool>:
  match b:
    case Ballot{k, +v, st, +i, q, VoteForLead{x}}:
      mine = Bool.and(Bool.and(Step.same(st, s), Nat.is_eq(q, r)), WordListSets.contains(vs, v))
      Bool.pick(
        Maybe<&2, Bool>,
        Bool.and(mine, Ballots.chain_below(i, all, v, s)),
        Bool.pick(
          Maybe<&2, Bool>,
          Ballots.joined_above(all, v, s, r, i),
          Some{False{}},
          Judge.vote.by_leads(ls, vs, n, r, x)
        ),
        None{}
      )
    case _:
      None{}

# the ballot b with its judgment j, when it is judged
def JudgedBallot.of(b: Ballot, j: Maybe<&2, Bool>) -> List<&2, JudgedBallot>:
  match j:
    case None{}:
      []
    case Some{ok}:
      [JudgedBallot{b, ok}]

# the leads of bs in round r, judged
def Judge.leads(
  bs: List<&2, Ballot>,
  +all: List<&2, Ballot>,
  +js: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +s: Step,
  +r: Nat
) -> List<&2, JudgedBallot>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      List.append(
        &2,
        JudgedBallot,
        JudgedBallot.of(b, Judge.lead(b, all, js, vs, n, s, r)),
        Judge.leads(rest, all, js, vs, n, s, r)
      )

# the votes of bs in round r, judged by the judged leads ls of round r
def Judge.votes(
  bs: List<&2, Ballot>,
  +all: List<&2, Ballot>,
  +ls: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +s: Step,
  +r: Nat
) -> List<&2, JudgedBallot>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      List.append(
        &2,
        JudgedBallot,
        JudgedBallot.of(b, Judge.vote(b, all, ls, vs, n, s, r)),
        Judge.votes(rest, all, ls, vs, n, s, r)
      )

# the leads and votes of all for the step s in the rounds below k, judged; n
# is the number of voters vs
def Judge.below(
  +k: Nat,
  +all: List<&2, Ballot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +s: Step
) -> List<&2, JudgedBallot>:
  match k:
    case 0n:
      []
    case 1n+r:
      +js = Judge.below(r, all, vs, n, s)
      +ls = Judge.leads(all, all, js, vs, n, s, r)
      List.append(
        &2,
        JudgedBallot,
        js,
        List.append(&2, JudgedBallot, ls, Judge.votes(all, all, ls, vs, n, s, r))
      )

# the highest round of the ballots of bs for the step s
def Ballots.top_round(bs: List<&2, Ballot>, +s: Step) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{Ballot{k, v, st, i, +r, c}, rest}:
      +rest_top = Ballots.top_round(rest, s)
      Bool.pick(Nat, Bool.and(Step.same(st, s), Nat.is_lt(rest_top, r)), r, rest_top)

# Deciding
# --------

# the voters of the sound judged ballots of js of round r for the choice x
def Decide.voters(
  js: List<&2, JudgedBallot>,
  +r: Nat,
  +x: List<&2, U32>
) -> List<&2, List<&2, U32>>:
  match js:
    case Nil{}:
      []
    case Con{JudgedBallot{Ballot{k, v, s, i, q, LeadRound{y, basis}}, ok}, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(
          List<&2, List<&2, U32>>,
          Bool.and(ok, Bool.and(Nat.is_eq(q, r), WordListSets.same(x, y))),
          [v],
          []
        ),
        Decide.voters(rest, r, x)
      )
    case Con{JudgedBallot{Ballot{k, v, s, i, q, VoteForLead{y}}, ok}, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(
          List<&2, List<&2, U32>>,
          Bool.and(ok, Bool.and(Nat.is_eq(q, r), WordListSets.same(x, y))),
          [v],
          []
        ),
        Decide.voters(rest, r, x)
      )
    case Con{j, rest}:
      Decide.voters(rest, r, x)

# the choice x of round r, when more than half of the n voters cast sound votes
# for it among js
def Decide.check(
  js: List<&2, JudgedBallot>,
  n: Nat,
  r: Nat,
  +x: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  Bool.pick(
    Maybe<&2, List<&2, U32>>,
    is_more_than_half(
      List.length(&2, List<&2, U32>, WordListSets.dedupe(Decide.voters(js, r, x))),
      n
    ),
    Some{x},
    None{}
  )

# the first choice, among the sound votes of cs, that more than half of the n
# voters cast sound votes for in one round among js
def Decide.find(
  cs: List<&2, JudgedBallot>,
  +js: List<&2, JudgedBallot>,
  +n: Nat
) -> Maybe<&2, List<&2, U32>>:
  match cs:
    case Nil{}:
      None{}
    case Con{JudgedBallot{Ballot{k, v, s, i, r, LeadRound{x, basis}}, True{}}, rest}:
      Maybe.or(&2, List<&2, U32>, Decide.check(js, n, r, x), Decide.find(rest, js, n))
    case Con{JudgedBallot{Ballot{k, v, s, i, r, VoteForLead{x}}, True{}}, rest}:
      Maybe.or(&2, List<&2, U32>, Decide.check(js, n, r, x), Decide.find(rest, js, n))
    case Con{j, rest}:
      Decide.find(rest, js, n)

# the answer for the decided choice m
def Decide.answer(m: Maybe<&2, List<&2, U32>>) -> MonotoneQueries.MonotoneAnswer<List<&2, U32>>:
  match m:
    case None{}:
      MonotoneQueries.Unknown{}
    case Some{x}:
      MonotoneQueries.Known{x}

# the answer for the step s among the deduped voters vs and the ballots all,
# after the search for a lie found l
def SlotConsensus.decision.after(
  l: Maybe<&2, List<&2, List<&2, U32>>>,
  +vs: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>
) -> MonotoneQueries.MonotoneAnswer<List<&2, U32>>:
  match l:
    case Some{p}:
      MonotoneQueries.Contradicted{p}
    case None{}:
      +n = List.length(&2, List<&2, U32>, vs)
      +js = Judge.below(1n+Ballots.top_round(all, s), all, vs, n, s)
      Decide.answer(Decide.find(js, js, n))

# what the ballots all decide for the step s, whose voters are voters: Contradicted
# when a voter lied, the choice once more than half of the voters cast sound
# votes for it in one round, else Unknown
def SlotConsensus.decision(
  voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>
) -> MonotoneQueries.MonotoneAnswer<List<&2, U32>>:
  +vs = WordListSets.dedupe(voters)
  SlotConsensus.decision.after(Ballots.lie(all, vs, s, all), vs, s, all)
# Judgments
# ---------

# the judgment of the ballot b among the ballots all for the step s, whose
# voters are voters: sound, unsound, or not yet
def SlotConsensus.judgment(
  voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>,
  b: Ballot
) -> Maybe<&2, Bool>:
  match b:
    case Ballot{k, v, st, i, r, a}:
      +vs = WordListSets.dedupe(voters)
      n = List.length(&2, List<&2, U32>, vs)
      JudgedBallot.find(Judge.below(1n+Ballots.top_round(all, s), all, vs, n, s), v, st, i)

# Casting
# -------
# What an honest voter signs next. It casts at most one ballot per call, at
# the index after its highest one, and the node calls again after each change.

# a ballot that a voter is about to sign: its index in the voter's chain, its
# round, and its action
type BallotToSign is Data:
  BallotToSign{index: Nat, round: Nat, action: BallotAction}

# the ballot c of the voter me for the step s, signed as the record whose key
# is k
def BallotToSign.signed(c: BallotToSign, k: List<&2, U32>, me: List<&2, U32>, s: Step) -> Ballot:
  match c:
    case BallotToSign{i, r, a}:
      Ballot{k, me, s, i, r, a}

# c joins a round
def BallotToSign.joins(c: BallotToSign) -> Bool:
  match c:
    case BallotToSign{i, r, JoinRound{}}:
      True{}
    case _:
      False{}

# the higher of two numbers, either of which may be missing
def Nat.max_some(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match a b:
    case None{} b:
      b
    case a None{}:
      a
    case Some{x} Some{y}:
      Some{Nat.max(x, y)}

# the index after the highest index of the ballots of me for the step s in bs;
# 0 when there is none
def Ballots.next_index(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: Step) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{Ballot{k, w, st, +i, r, a}, rest}:
      +later = Ballots.next_index(rest, me, s)
      Bool.pick(
        Nat,
        Bool.and(Bool.and(WordListSets.same(w, me), Step.same(st, s)), Nat.is_le(later, i)),
        1n+i,
        later
      )

# the highest round of the ballots of me for the step s in bs, if any
def Ballots.top_round_of(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: Step) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Nat.max_some(
        Bool.pick(
          Maybe<&2, Nat>,
          Bool.and(WordListSets.same(w, me), Step.same(st, s)),
          Some{q},
          None{}
        ),
        Ballots.top_round_of(rest, me, s)
      )

# me has, for the step s, a lead or a vote of round r
def Ballots.acted_in(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: Step, +r: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(WordListSets.same(w, me), Step.same(st, s)),
          Bool.and(Nat.is_eq(q, r), Bool.not(BallotAction.same(a, JoinRound{})))
        ),
        Ballots.acted_in(rest, me, s, r)
      )

# me has, for the step s, a lead of round r
def Ballots.led(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: Step, +r: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(WordListSets.same(w, me), Step.same(st, s)),
          Bool.and(Nat.is_eq(q, r), BallotAction.is_lead(a))
        ),
        Ballots.led(rest, me, s, r)
      )

# the round and choice of the highest sound lead among js, if any
def JudgedBallot.top_sound_lead(
  js: List<&2, JudgedBallot>
) -> Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>:
  match js:
    case Nil{}:
      None{}
    case Con{JudgedBallot{Ballot{k, v, s, i, r, LeadRound{x, basis}}, True{}}, rest}:
      VotesBeforeJoin.higher(Some{(r, x)}, JudgedBallot.top_sound_lead(rest))
    case Con{j, rest}:
      JudgedBallot.top_sound_lead(rest)

# the voters that joined a round for a step, with every vote that they cast
# before their join there and judged, and what those votes say
type ReadyJoiners is Data:
  ReadyJoiners{basis: List<&2, List<&2, U32>>, votes: VotesBeforeJoin}

# the highest sound vote best, if any, is for a choice that acceptable accepts
# for the step s among the ballots all, in the context context
def NextBallot.accepts_prior(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  s: Step,
  all: List<&2, Ballot>,
  best: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>
) -> Bool:
  match best:
    case None{}:
      True{}
    case Some{(r, x)}:
      acceptable(context, s, all, x)

# the voter v, when what its votes before its join say, p, is all judged and
# its highest sound vote is for an acceptable choice
def ReadyJoiners.of_votes(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  s: Step,
  all: List<&2, Ballot>,
  p: VotesBeforeJoin,
  v: List<&2, U32>
) -> ReadyJoiners:
  match p:
    case VotesBeforeJoin{True{}, +best}:
      Bool.pick(
        ReadyJoiners,
        NextBallot.accepts_prior(~Context, ~acceptable, context, s, all, best),
        ReadyJoiners{[v], VotesBeforeJoin{True{}, best}},
        ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}
      )
    case VotesBeforeJoin{False{}, best}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}

# the voter v, when its first join m is there and ready
def ReadyJoiners.of_join(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  m: Maybe<&2, Nat>,
  +all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  +v: List<&2, U32>,
  +s: Step
) -> ReadyJoiners:
  match m:
    case None{}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}
    case Some{i}:
      ReadyJoiners.of_votes(
        ~Context,
        ~acceptable,
        context,
        s,
        all,
        VotesBeforeJoin.below(all, js, v, s, i),
        v
      )

# a and b together
def ReadyJoiners.add(a: ReadyJoiners, b: ReadyJoiners) -> ReadyJoiners:
  match a b:
    case ReadyJoiners{xa, pa} ReadyJoiners{xb, pb}:
      ReadyJoiners{List.append(&2, List<&2, U32>, xa, xb), VotesBeforeJoin.join(pa, pb)}

# the voters of us that are ready joiners of round r for the step s
def ReadyJoiners.of(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  us: List<&2, List<&2, U32>>,
  +context: Context,
  +all: List<&2, Ballot>,
  +js: List<&2, JudgedBallot>,
  +s: Step,
  +r: Nat
) -> ReadyJoiners:
  match us:
    case Nil{}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}
    case Con{+u, rest}:
      ReadyJoiners.add(
        ReadyJoiners.of_join(
          ~Context,
          ~acceptable,
          context,
          Ballots.first_join(all, all, u, s, r),
          all,
          js,
          u,
          s
        ),
        ReadyJoiners.of(~Context, ~acceptable, rest, context, all, js, s, r)
      )

# the choice that a lead must have: that of the highest sound vote best, or
# proposal when there is none
def NextBallot.choice(
  best: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>,
  proposal: List<&2, U32>
) -> List<&2, U32>:
  match best:
    case None{}:
      proposal
    case Some{(q, y)}:
      y

# a lead of round r with the ready joiners rj as its basis, when they are more
# than half of the n voters
def NextBallot.lead_of(
  rj: ReadyJoiners,
  n: Nat,
  r: Nat,
  i: Nat,
  proposal: List<&2, U32>
) -> Maybe<&2, BallotToSign>:
  match rj:
    case ReadyJoiners{+basis, VotesBeforeJoin{known, best}}:
      Bool.pick(
        Maybe<&2, BallotToSign>,
        is_more_than_half(List.length(&2, List<&2, U32>, basis), n),
        Some{BallotToSign{i, r, LeadRound{NextBallot.choice(best, proposal), basis}}},
        None{}
      )

# a vote for the highest sound lead top, when me may still vote in its round
# and accepts its choice: me has not acted in it, has not joined a higher
# round, does not lead it, and acceptable accepts the choice
def NextBallot.vote(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  top: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>,
  +all: List<&2, Ballot>,
  vs: List<&2, List<&2, U32>>,
  n: Nat,
  +me: List<&2, U32>,
  +s: Step,
  +i: Nat
) -> Maybe<&2, BallotToSign>:
  match top:
    case None{}:
      None{}
    case Some{(+r, +x)}:
      Bool.pick(
        Maybe<&2, BallotToSign>,
        Bool.and(
          Bool.and(Bool.not(Ballots.acted_in(all, me, s, r)), acceptable(context, s, all, x)),
          Bool.and(
            Bool.not(Ballots.joined_above(all, me, s, r, i)),
            Bool.not(leads_round(vs, n, r, me))
          )
        ),
        Some{BallotToSign{i, r, VoteForLead{x}}},
        None{}
      )

# a lead of the round mine, the highest round that me has a ballot in, when me
# leads it, joined it, and has not led it yet; its basis is the ready joiners
# whose highest sound vote is for an acceptable choice
def NextBallot.lead(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  mine: Maybe<&2, Nat>,
  +all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +me: List<&2, U32>,
  +s: Step,
  i: Nat,
  proposal: List<&2, U32>
) -> Maybe<&2, BallotToSign>:
  match mine:
    case None{}:
      None{}
    case Some{+r}:
      Bool.pick(
        Maybe<&2, BallotToSign>,
        Bool.and(
          leads_round(vs, n, r, me),
          Bool.and(
            Maybe.is_some(&2, Nat, Ballots.first_join(all, all, me, s, r)),
            Bool.not(Ballots.led(all, me, s, r))
          )
        ),
        NextBallot.lead_of(
          ReadyJoiners.of(~Context, ~acceptable, vs, context, all, js, s, r),
          n,
          r,
          i,
          proposal
        ),
        None{}
      )

# 1 when the highest round m of a voter is r or above, else 0
def Ballots.count_reached.of(m: Maybe<&2, Nat>, r: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{q}:
      Bool.pick(Nat, Nat.is_le(r, q), 1n, 0n)

# how many voters of vs have, for the step s, a ballot in round r or above
def Ballots.count_reached(
  vs: List<&2, List<&2, U32>>,
  +all: List<&2, Ballot>,
  +s: Step,
  +r: Nat
) -> Nat:
  match vs:
    case Nil{}:
      0n
    case Con{v, rest}:
      Nat.add(
        Ballots.count_reached.of(Ballots.top_round_of(all, v, s), r),
        Ballots.count_reached(rest, all, s, r)
      )

# the highest round m of a voter, when at least need voters of vs reached it
def Ballots.catch_up.of(
  m: Maybe<&2, Nat>,
  vs: List<&2, List<&2, U32>>,
  all: List<&2, Ballot>,
  s: Step,
  need: Nat
) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{+r}:
      Bool.pick(
        Maybe<&2, Nat>,
        Nat.is_le(need, Ballots.count_reached(vs, all, s, r)),
        Some{r},
        None{}
      )

# the highest round that at least need voters of vs reached for the step s,
# among the highest rounds of the voters us; such a round is reached by a voter
# that is not a stranger whenever need is at least half of the voters
def Ballots.catch_up(
  us: List<&2, List<&2, U32>>,
  +vs: List<&2, List<&2, U32>>,
  +all: List<&2, Ballot>,
  +s: Step,
  +need: Nat
) -> Maybe<&2, Nat>:
  match us:
    case Nil{}:
      None{}
    case Con{u, rest}:
      Nat.max_some(
        Ballots.catch_up.of(Ballots.top_round_of(all, u, s), vs, all, s, need),
        Ballots.catch_up(rest, vs, all, s, need)
      )

# a join of the round target, when it is above every round of me
def NextBallot.join(
  target: Maybe<&2, Nat>,
  mine: Maybe<&2, Nat>,
  i: Nat
) -> Maybe<&2, BallotToSign>:
  match target mine:
    case None{} m:
      None{}
    case Some{r} None{}:
      Some{BallotToSign{i, r, JoinRound{}}}
    case Some{+r} Some{m}:
      Bool.pick(
        Maybe<&2, BallotToSign>,
        Nat.is_lt(m, r),
        Some{BallotToSign{i, r, JoinRound{}}},
        None{}
      )

# a join of round 0, when me has no ballot for the step yet
def NextBallot.start(mine: Maybe<&2, Nat>, i: Nat) -> Maybe<&2, BallotToSign>:
  match mine:
    case None{}:
      Some{BallotToSign{i, 0n, JoinRound{}}}
    case Some{r}:
      None{}

# on a tick, a join of the round after the highest round mine of me
def NextBallot.tick(ticked: Bool, mine: Maybe<&2, Nat>, i: Nat) -> Maybe<&2, BallotToSign>:
  match ticked mine:
    case True{} Some{r}:
      Some{BallotToSign{i, 1n+r, JoinRound{}}}
    case _ _:
      None{}

# the answer a is still Unknown
def is_unknown(a: MonotoneQueries.MonotoneAnswer<List<&2, U32>>) -> Bool:
  match a:
    case MonotoneQueries.Unknown{}:
      True{}
    case _:
      False{}

# what the voter me signs next for the step s, given the ballots all, the
# choice proposal that it leads with when free, whether its round timer ran out
# (ticked), and which choices it accepts (acceptable, in the context context). Nothing once the step is decided or contradicted, when me is
# not a voter, or while a ballot of its own chain is missing. Else the first of:
# a vote for the highest sound lead that it may still vote for and accepts; a
# lead of its round; a join of the highest round that at least half of the voters reached,
# when it is above its own; a join of round 0 when it has no ballot yet; on a
# tick, a join of the round after its own.
def SlotConsensus.next_ballot(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  +context: Context,
  +voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>,
  +me: List<&2, U32>,
  proposal: List<&2, U32>,
  ticked: Bool
) -> Maybe<&2, BallotToSign>:
  +vs = WordListSets.dedupe(voters)
  +n = List.length(&2, List<&2, U32>, vs)
  +i = Ballots.next_index(all, me, s)
  +js = Judge.below(1n+Ballots.top_round(all, s), all, vs, n, s)
  +mine = Ballots.top_round_of(all, me, s)
  Bool.pick(
    Maybe<&2, BallotToSign>,
    Bool.and(
      is_unknown(SlotConsensus.decision(voters, s, all)),
      Bool.and(WordListSets.contains(vs, me), Ballots.chain_below(i, all, me, s))
    ),
    Maybe.or(
      &2,
      BallotToSign,
      NextBallot.vote(
        ~Context,
        ~acceptable,
        context,
        JudgedBallot.top_sound_lead(js),
        all,
        vs,
        n,
        me,
        s,
        i
      ),
      Maybe.or(
        &2,
        BallotToSign,
        NextBallot.lead(~Context, ~acceptable, context, mine, all, js, vs, n, me, s, i, proposal),
        Maybe.or(
          &2,
          BallotToSign,
          NextBallot.join(Ballots.catch_up(vs, vs, all, s, Nat.div(1n+n, 2n)), mine, i),
          Maybe.or(&2, BallotToSign, NextBallot.start(mine, i), NextBallot.tick(ticked, mine, i))
        )
      )
    ),
    None{}
  )

# Runs
# ----
# A good phase: every honest voter holds the same ballots, every ballot that an
# honest voter casts reaches every honest voter before the next exchange, and
# the other voters add whatever ballots they like at each exchange. The
# network makes good phases happen; the laws below say what one does.

# the ballot that the voter h is about to sign, m, signed for the step s
def Run.signed(m: Maybe<&2, BallotToSign>, h: List<&2, U32>, s: Step) -> List<&2, Ballot>:
  match m:
    case None{}:
      []
    case Some{c}:
      [BallotToSign.signed(c, [], h, s)]

# the ballots that the voters hs sign next for the step s from the ballots all
def Run.casts(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  hs: List<&2, List<&2, U32>>,
  +context: Context,
  +voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>,
  +p: List<&2, U32>,
  +ticked: Bool
) -> List<&2, Ballot>:
  match hs:
    case Nil{}:
      []
    case Con{+h, rest}:
      List.append(
        &2,
        Ballot,
        Run.signed(
          SlotConsensus.next_ballot(~Context, ~acceptable, context, voters, s, all, h, p, ticked),
          h,
          s
        ),
        Run.casts(~Context, ~acceptable, rest, context, voters, s, all, p, ticked)
      )

# one exchange: the ballots all, with what the honest voters hs sign next from
# them, and the ballots extra of the other voters
def Run.exchange(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  +all: List<&2, Ballot>,
  hs: List<&2, List<&2, U32>>,
  voters: List<&2, List<&2, U32>>,
  s: Step,
  p: List<&2, U32>,
  ticked: Bool,
  extra: List<&2, Ballot>
) -> List<&2, Ballot>:
  List.append(
    &2,
    Ballot,
    all,
    List.append(
      &2,
      Ballot,
      Run.casts(~Context, ~acceptable, hs, context, voters, s, all, p, ticked),
      extra
    )
  )

# a good phase from the ballots all: an exchange in which every honest voter
# of hs ticks, then two exchanges without a tick; x0, x1 and x2 are what the
# other voters add at each
def Run.good_phase(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  +context: Context,
  +voters: List<&2, List<&2, U32>>,
  +s: Step,
  all: List<&2, Ballot>,
  +hs: List<&2, List<&2, U32>>,
  +p: List<&2, U32>,
  x0: List<&2, Ballot>,
  x1: List<&2, Ballot>,
  x2: List<&2, Ballot>
) -> List<&2, Ballot>:
  a1 = Run.exchange(~Context, ~acceptable, context, all, hs, voters, s, p, True{}, x0)
  a2 = Run.exchange(~Context, ~acceptable, context, a1, hs, voters, s, p, False{}, x1)
  Run.exchange(~Context, ~acceptable, context, a2, hs, voters, s, p, False{}, x2)

# no ballot of xs is by a voter of hs
def Run.none_by(xs: List<&2, Ballot>, +hs: List<&2, List<&2, U32>>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{Ballot{k, v, st, i, r, a}, rest}:
      Bool.and(Bool.not(WordListSets.contains(hs, v)), Run.none_by(rest, hs))

# every voter of hs signs nothing next for the step s without a tick
def Run.quiet(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  hs: List<&2, List<&2, U32>>,
  +context: Context,
  +voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>,
  +p: List<&2, U32>
) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, rest}:
      Bool.and(
        Maybe.is_none(
          &2,
          BallotToSign,
          SlotConsensus.next_ballot(~Context, ~acceptable, context, voters, s, all, h, p, False{})
        ),
        Run.quiet(~Context, ~acceptable, rest, context, voters, s, all, p)
      )

# the highest round m is t
def Run.is_round(m: Maybe<&2, Nat>, t: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      Nat.is_eq(r, t)

# every voter of hs has, for the step s, its highest ballot in round t, and
# every ballot of its chain below its next index
def Run.level(hs: List<&2, List<&2, U32>>, +all: List<&2, Ballot>, +s: Step, +t: Nat) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{+h, rest}:
      Bool.and(
        Bool.and(
          Run.is_round(Ballots.top_round_of(all, h, s), t),
          Ballots.chain_below(Ballots.next_index(all, h, s), all, h, s)
        ),
        Run.level(rest, all, s, t)
      )

# the lead or vote b, if it is by a voter of hs for the step s, is judged
# among the ballots all
def Run.judged.one(
  b: Ballot,
  hs: List<&2, List<&2, U32>>,
  voters: List<&2, List<&2, U32>>,
  +s: Step,
  all: List<&2, Ballot>
) -> Bool:
  match b:
    case Ballot{k, v, st, i, r, JoinRound{}}:
      True{}
    case Ballot{+k, +v, +st, +i, +r, +a}:
      Bool.or(
        Bool.not(Bool.and(WordListSets.contains(hs, v), Step.same(st, s))),
        Maybe.is_some(&2, Bool, SlotConsensus.judgment(voters, s, all, Ballot{k, v, st, i, r, a}))
      )

# every lead and vote of bs by a voter of hs for the step s is judged among the
# ballots all
def Run.judged(
  bs: List<&2, Ballot>,
  +hs: List<&2, List<&2, U32>>,
  +voters: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>
) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      Bool.and(Run.judged.one(b, hs, voters, s, all), Run.judged(rest, hs, voters, s, all))

# the lead or vote b, if it is by a voter of hs for the step s, is for a
# choice that acceptable accepts among the ballots all
def Run.accepted.one(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  b: Ballot,
  context: Context,
  hs: List<&2, List<&2, U32>>,
  +s: Step,
  all: List<&2, Ballot>
) -> Bool:
  match b:
    case Ballot{k, v, st, i, r, LeadRound{x, basis}}:
      Bool.or(
        Bool.not(Bool.and(WordListSets.contains(hs, v), Step.same(st, s))),
        acceptable(context, s, all, x)
      )
    case Ballot{k, +v, +st, i, r, VoteForLead{x}}:
      Bool.or(
        Bool.not(Bool.and(WordListSets.contains(hs, v), Step.same(st, s))),
        acceptable(context, s, all, x)
      )
    case _:
      True{}

# every lead and vote of bs by a voter of hs for the step s is for a choice
# that acceptable accepts among the ballots all
def Run.accepted(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  bs: List<&2, Ballot>,
  +context: Context,
  +hs: List<&2, List<&2, U32>>,
  +s: Step,
  +all: List<&2, Ballot>
) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case Con{b, rest}:
      Bool.and(
        Run.accepted.one(~Context, ~acceptable, b, context, hs, s, all),
        Run.accepted(~Context, ~acceptable, rest, context, hs, s, all)
      )

# the voter m, if there, is one of hs
def Run.names_one_of(m: Maybe<&2, List<&2, U32>>, hs: List<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      WordListSets.contains(hs, v)

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Laws
# ----

# every ballot of a is in b
def Ballots.Grows(a: List<&2, Ballot>, b: List<&2, Ballot>) -> Type:
  @x: Ballot
    -> {List.contains(~Ballot, ~Ballot.same, a, x) == True{}: Bool}
    -> {List.contains(~Ballot, ~Ballot.same, b, x) == True{}: Bool}

# a and b are the same list of words
def EqualWordLists(a: List<&2, U32>, b: List<&2, U32>) -> Type:
  {a == b: List<&2, U32>}

# acceptable is monotone: a choice that it accepts for a step among some
# ballots, it accepts among any more ballots
def AcceptableIsMonotone(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool
) -> Type:
  @ctx: Context -> @s: Step -> @a: List<&2, Ballot> -> @b: List<&2, Ballot> -> @x: List<&2, U32>
    -> Ballots.Grows(a, b)
    -> {acceptable(ctx, s, a, x) == True{}: Bool}
    -> {acceptable(ctx, s, b, x) == True{}: Bool}

# the choice of the ballot c, if it leads or votes, is the proposal p or a
# choice that acceptable accepts for the step s among the ballots all
def BallotToSign.choice_accepted(
  ~Context: Data,
  ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool,
  context: Context,
  s: Step,
  all: List<&2, Ballot>,
  p: List<&2, U32>,
  c: BallotToSign
) -> Bool:
  match c:
    case BallotToSign{i, r, VoteForLead{x}}:
      acceptable(context, s, all, x)
    case BallotToSign{i, r, LeadRound{+x, basis}}:
      Bool.or(WordListSets.same(x, p), acceptable(context, s, all, x))
    case _:
      True{}

# Means: with more ballots, what a step decides only knows more: Unknown may
# become a choice or Contradicted, a choice may become Contradicted, and nothing else
# changes.
# For free: two nodes never decide two different choices for one step unless
# a voter of that step signed two ballots that contradict each other, because
# the answer on their ballots together knows more than both (agreement); a
# decided choice can be cached for good; the order in which ballots arrive does
# not matter.
# For the goal: one history (Trust 4) with trust in the voters only for not
# contradicting themselves (Trust 3), and no premise that names no liar: a lie
# shows as Contradicted, with proof.
# Example: once more than half of the voters of slot 5 voted for request w7 in
# round 2, every node that holds those ballots, and any more, answers w7 for
# slot 5, or Contradicted.
law SlotConsensus.decision_is_monotone:
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for a: List<&2, Ballot>
  for b: List<&2, Ballot>
  Ballots.Grows(a, b)
    -> MonotoneQueries.MonotoneAnswer.Below(
      ~(List<&2, U32>),
      ~EqualWordLists,
      SlotConsensus.decision(voters, s, a),
      SlotConsensus.decision(voters, s, b)
    )

# Means: what an honest voter signs next never contradicts a ballot that it
# signed before: it has the next index of the voter's chain, and it leads a
# round only if the voter has not led that round.
# For free: an honest voter is never named a liar, so its slots are never
# Contradicted by its own fault, even after a restart with all of its ballots.
# For the goal: the trust in a voter (Trust 3) is exactly what this law makes
# true for the program's own voters.
# Example: a voter whose highest ballot for slot 5 has index 3 signs its next
# ballot for slot 5 with index 4.
law SlotConsensus.next_ballot_contradicts_nothing:
  for ~Context: Data
  for ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool
  for context: Context
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for all: List<&2, Ballot>
  for me: List<&2, U32>
  for proposal: List<&2, U32>
  for ticked: Bool
  for c: BallotToSign
  for k: List<&2, U32>
  for b: Ballot
  {
    SlotConsensus.next_ballot(
      ~Context,
      ~acceptable,
      context,
      voters,
      s,
      all,
      me,
      proposal,
      ticked
    )
      == Some{c}: Maybe<&2, BallotToSign>
  }
    -> {List.contains(~Ballot, ~Ballot.same, all, b) == True{}: Bool}
    -> {Ballot.contradicts(b, BallotToSign.signed(c, k, me, s)) == False{}: Bool}

# Means: what an honest voter signs next leads or votes only for its own
# proposal or for a choice that it accepts.
# For free: a decided choice was accepted by at least one honest voter, since
# more than half of the voters voted for it; strangers and faulty leaders
# cannot get a choice decided that no honest voter accepts.
# For the goal: a hook (owner groups, Vend) says which choices are acceptable,
# and nothing else gets decided, so a faulty leader cannot make a line wait on
# an era or a request that does not exist.
# Example: a voter that does not know era 12 yet does not vote for a choice
# that names era 12.
law SlotConsensus.next_ballot_accepts_its_choice:
  for ~Context: Data
  for ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool
  for context: Context
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for all: List<&2, Ballot>
  for me: List<&2, U32>
  for proposal: List<&2, U32>
  for ticked: Bool
  for c: BallotToSign
  {
    SlotConsensus.next_ballot(
      ~Context,
      ~acceptable,
      context,
      voters,
      s,
      all,
      me,
      proposal,
      ticked
    )
      == Some{c}: Maybe<&2, BallotToSign>
  }
    -> {
      BallotToSign.choice_accepted(
        ~Context,
        ~acceptable,
        context,
        s,
        all,
        proposal,
        c
      )
        == True{}: Bool
    }

# Means: a lead or a vote that an honest voter signs next is judged sound among
# the ballots it had, together with the new one.
# For free: with the law below, it stays sound on every node that holds those
# ballots; an honest voter's votes always count toward a decision.
# For the goal: honest voters never waste a vote, so more than half of honest
# voters that hear one another decide (Trust 4, progress).
# Example: a voter that sees the sound lead of round 2 for w7 votes for w7 in
# round 2, and that vote is sound.
law SlotConsensus.next_ballot_is_judged_sound:
  for ~Context: Data
  for ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool
  for context: Context
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for all: List<&2, Ballot>
  for me: List<&2, U32>
  for proposal: List<&2, U32>
  for ticked: Bool
  for c: BallotToSign
  for k: List<&2, U32>
  {
    SlotConsensus.next_ballot(
      ~Context,
      ~acceptable,
      context,
      voters,
      s,
      all,
      me,
      proposal,
      ticked
    )
      == Some{c}: Maybe<&2, BallotToSign>
  }
    -> {BallotToSign.joins(c) == False{}: Bool}
    -> {
      SlotConsensus.judgment(
        voters,
        s,
        List.append(&2, Ballot, all, [BallotToSign.signed(c, k, me, s)]),
        BallotToSign.signed(c, k, me, s)
      )
        == Some{True{}}: Maybe<&2, Bool>
    }

# Means: with more ballots, and no voter of the step that contradicts itself,
# a ballot that is judged keeps its judgment.
# For free: a sound vote counts for good; a lead, once judged, binds every vote
# of its round for good; a decision rests only on judgments that never change.
# For the goal: a decision only knows more (the law above), and a node can
# keep each judgment instead of judging again.
# Example: a vote of round 2 judged sound on a node stays sound when the node
# learns the ballots of round 3.
law SlotConsensus.judgment_never_changes:
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for a: List<&2, Ballot>
  for b: List<&2, Ballot>
  for x: Ballot
  for j: Bool
  Ballots.Grows(a, b)
    -> {
      Ballots.lie(
        b,
        WordListSets.dedupe(voters),
        s,
        b
      )
        == None{}: Maybe<&2, List<&2, List<&2, U32>>>
    }
    -> {SlotConsensus.judgment(voters, s, a, x) == Some{j}: Maybe<&2, Bool>}
    -> {SlotConsensus.judgment(voters, s, b, x) == Some{j}: Maybe<&2, Bool>}

# Means: from ballots that every honest voter holds, where the honest voters
# are more than half of the voters, all have their highest ballot in one round,
# have whole chains, have every lead and vote judged and for choices they
# accept, and have nothing more to sign without a tick, where they accept the
# proposal and accept for good what they accept, and where the leader of the
# next round is honest: after
# one exchange in which each honest voter ticks and two more exchanges, the
# step is decided or Contradicted, whatever the other voters add.
# For free: a slot is decided within one good phase whose leader is honest;
# among any number of consecutive rounds equal to the number of voters, one
# has an honest leader, so as many good phases decide every slot; nothing that
# strangers or faulty voters send can stop a good phase.
# For the goal: a slot gets decided once the network lets honest voters hear
# one another in time (Trust 4, progress), and a request stays pending only
# while it does not.
# Example: three honest voters of five, all at round 6, tick; the leader of
# round 7 is honest; two exchanges later slot 5 is decided.
law SlotConsensus.good_phase_decides:
  for ~Context: Data
  for ~acceptable: Context -> Step -> List<&2, Ballot> -> List<&2, U32> -> Bool
  for context: Context
  for voters: List<&2, List<&2, U32>>
  for s: Step
  for all: List<&2, Ballot>
  for hs: List<&2, List<&2, U32>>
  for p: List<&2, U32>
  for t: Nat
  for x0: List<&2, Ballot>
  for x1: List<&2, Ballot>
  for x2: List<&2, Ballot>
  {WordListSets.within(hs, WordListSets.dedupe(voters)) == True{}: Bool}
    -> {
      is_more_than_half(
        List.length(&2, List<&2, U32>, WordListSets.dedupe(hs)),
        List.length(&2, List<&2, U32>, WordListSets.dedupe(voters))
      )
        == True{}: Bool
    }
    -> {Run.level(hs, all, s, t) == True{}: Bool}
    -> {Run.judged(all, hs, voters, s, all) == True{}: Bool}
    -> AcceptableIsMonotone(~Context, ~acceptable)
    -> {acceptable(context, s, all, p) == True{}: Bool}
    -> {Run.accepted(~Context, ~acceptable, all, context, hs, s, all) == True{}: Bool}
    -> {Run.quiet(~Context, ~acceptable, hs, context, voters, s, all, p) == True{}: Bool}
    -> {
      Run.names_one_of(
        voter_at(
          WordListSets.dedupe(voters),
          Nat.mod(1n+t, List.length(&2, List<&2, U32>, WordListSets.dedupe(voters)))
        ),
        hs
      )
        == True{}: Bool
    }
    -> {
      Bool.and(
        Run.none_by(x0, hs),
        Bool.and(Run.none_by(x1, hs), Run.none_by(x2, hs))
      )
        == True{}: Bool
    }
    -> {
      is_unknown(
        SlotConsensus.decision(
          voters,
          s,
          Run.good_phase(~Context, ~acceptable, context, voters, s, all, hs, p, x0, x1, x2)
        )
      )
        == False{}: Bool
    }
