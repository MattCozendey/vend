import Base
import ../shared/monotone_queries/spec.bend as MonotoneQueries
import ../shared/shared/shared/word_list_sets/spec.bend as WordListSets

# Slot consensus decides, for each step (a slot of a line, named by words), one
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

# a ballot: the key of the record it comes from, its voter, its step, its index in
# the voter's chain for the step, its round, and what it does
type Ballot is Data:
  Ballot{
    key: List<&2, U32>,
    voter: List<&2, U32>,
    step: List<&2, U32>,
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

# a and b are the same ballot
def Ballot.same(a: Ballot, b: Ballot) -> Bool:
  match a b:
    case Ballot{ka, va, sa, ia, ra, ca} Ballot{kb, vb, sb, ib, rb, cb}:
      Bool.and(
        Bool.and(
          WordListSets.same(ka, kb),
          Bool.and(WordListSets.same(va, vb), WordListSets.same(sa, sb))
        ),
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
        Bool.and(WordListSets.same(va, vb), WordListSets.same(sa, sb)),
        Bool.or(
          Bool.and(Nat.is_eq(ia, ib), Bool.not(Bool.and(same_round, same_cast))),
          Bool.and(
            Bool.and(same_round, Bool.and(BallotAction.is_lead(ca), BallotAction.is_lead(cb))),
            Bool.not(same_cast)
          )
        )
      )

# the ballot b is of a voter of vs, for the step s
def Ballot.is_of(b: Ballot, vs: List<&2, List<&2, U32>>, s: List<&2, U32>) -> Bool:
  match b:
    case Ballot{k, v, st, i, r, c}:
      Bool.and(WordListSets.contains(vs, v), WordListSets.same(st, s))

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
  +s: List<&2, U32>,
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
def Ballots.has_index(all: List<&2, Ballot>, +v: List<&2, U32>, +s: List<&2, U32>, +i: Nat) -> Bool:
  match all:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, j, r, c}, rest}:
      Bool.or(
        Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_eq(j, i)),
        Ballots.has_index(rest, v, s, i)
      )

# all has the ballots of the voter v for the step s of every index below i
def Ballots.chain_below(
  +i: Nat,
  +all: List<&2, Ballot>,
  +v: List<&2, U32>,
  +s: List<&2, U32>
) -> Bool:
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
  +s: List<&2, U32>,
  +r: Nat,
  +i: Nat
) -> Bool:
  match all:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, j, q, c}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_lt(j, i)),
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
  +s: List<&2, U32>,
  +r: Nat
) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{Ballot{k, w, st, +j, q, c}, rest}:
      here = Bool.and(
        Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_eq(q, r)),
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
  +s: List<&2, U32>,
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
          Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_eq(j, i)),
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
  s: List<&2, U32>,
  i: Nat
) -> VotesBeforeJoin:
  match b:
    case Ballot{k, +w, +st, +j, r, LeadRound{x, basis}}:
      Bool.pick(
        VotesBeforeJoin,
        Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_lt(j, i)),
        VotesBeforeJoin.of_judgment(JudgedBallot.find(js, w, st, j), r, x),
        VotesBeforeJoin{True{}, None{}}
      )
    case Ballot{k, +w, +st, +j, r, VoteForLead{x}}:
      Bool.pick(
        VotesBeforeJoin,
        Bool.and(Bool.and(WordListSets.same(w, v), WordListSets.same(st, s)), Nat.is_lt(j, i)),
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
  +s: List<&2, U32>,
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
  s: List<&2, U32>
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
  +s: List<&2, U32>,
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
  +s: List<&2, U32>,
  +r: Nat
) -> Maybe<&2, Bool>:
  match b:
    case Ballot{k, +v, st, +i, q, LeadRound{x, basis}}:
      mine = Bool.and(WordListSets.same(st, s), Nat.is_eq(q, r))
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
  +s: List<&2, U32>,
  +r: Nat
) -> Maybe<&2, Bool>:
  match b:
    case Ballot{k, +v, st, +i, q, VoteForLead{x}}:
      mine = Bool.and(
        Bool.and(WordListSets.same(st, s), Nat.is_eq(q, r)),
        WordListSets.contains(vs, v)
      )
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
  +s: List<&2, U32>,
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
  +s: List<&2, U32>,
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
  +s: List<&2, U32>
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
def Ballots.top_round(bs: List<&2, Ballot>, +s: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{Ballot{k, v, st, i, +r, c}, rest}:
      +rest_top = Ballots.top_round(rest, s)
      Bool.pick(Nat, Bool.and(WordListSets.same(st, s), Nat.is_lt(rest_top, r)), r, rest_top)

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
  +s: List<&2, U32>,
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
  +s: List<&2, U32>,
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
  +s: List<&2, U32>,
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
def BallotToSign.signed(
  c: BallotToSign,
  k: List<&2, U32>,
  me: List<&2, U32>,
  s: List<&2, U32>
) -> Ballot:
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

# one more than m, if m is there
def Nat.succ_some(m: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{1n+x}

# the position of the voter v in vs, if v is one of them
def position(vs: List<&2, List<&2, U32>>, +v: List<&2, U32>) -> Maybe<&2, Nat>:
  match vs:
    case Nil{}:
      None{}
    case Con{w, rest}:
      Bool.pick(Maybe<&2, Nat>, WordListSets.same(w, v), Some{0n}, Nat.succ_some(position(rest, v)))

# the index after the highest index of the ballots of me for the step s in bs;
# 0 when there is none
def Ballots.next_index(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: List<&2, U32>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{Ballot{k, w, st, +i, r, a}, rest}:
      +later = Ballots.next_index(rest, me, s)
      Bool.pick(
        Nat,
        Bool.and(Bool.and(WordListSets.same(w, me), WordListSets.same(st, s)), Nat.is_le(later, i)),
        1n+i,
        later
      )

# the highest round of the ballots of me for the step s in bs, if any
def Ballots.top_round_of(
  bs: List<&2, Ballot>,
  +me: List<&2, U32>,
  +s: List<&2, U32>
) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Nat.max_some(
        Bool.pick(
          Maybe<&2, Nat>,
          Bool.and(WordListSets.same(w, me), WordListSets.same(st, s)),
          Some{q},
          None{}
        ),
        Ballots.top_round_of(rest, me, s)
      )

# me has, for the step s, a lead or a vote of round r
def Ballots.acted_in(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: List<&2, U32>, +r: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(WordListSets.same(w, me), WordListSets.same(st, s)),
          Bool.and(Nat.is_eq(q, r), Bool.not(BallotAction.same(a, JoinRound{})))
        ),
        Ballots.acted_in(rest, me, s, r)
      )

# me has, for the step s, a lead of round r
def Ballots.led(bs: List<&2, Ballot>, +me: List<&2, U32>, +s: List<&2, U32>, +r: Nat) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{Ballot{k, w, st, i, q, a}, rest}:
      Bool.or(
        Bool.and(
          Bool.and(WordListSets.same(w, me), WordListSets.same(st, s)),
          Bool.and(Nat.is_eq(q, r), BallotAction.is_lead(a))
        ),
        Ballots.led(rest, me, s, r)
      )

# the highest round for the step s in which the round's leader among the n
# voters vs cast a ballot: the highest round that is alive, if any
def Ballots.top_alive(
  bs: List<&2, Ballot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +s: List<&2, U32>
) -> Maybe<&2, Nat>:
  match bs:
    case Nil{}:
      None{}
    case Con{Ballot{k, w, st, i, +q, a}, rest}:
      Nat.max_some(
        Bool.pick(
          Maybe<&2, Nat>,
          Bool.and(WordListSets.same(st, s), leads_round(vs, n, q, w)),
          Some{q},
          None{}
        ),
        Ballots.top_alive(rest, vs, n, s)
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

# the voter v, when what its votes before its join say, p, is all judged
def ReadyJoiners.of_votes(p: VotesBeforeJoin, v: List<&2, U32>) -> ReadyJoiners:
  match p:
    case VotesBeforeJoin{True{}, best}:
      ReadyJoiners{[v], VotesBeforeJoin{True{}, best}}
    case VotesBeforeJoin{False{}, best}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}

# the voter v, when its first join m is there and ready
def ReadyJoiners.of_join(
  m: Maybe<&2, Nat>,
  all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  +v: List<&2, U32>,
  s: List<&2, U32>
) -> ReadyJoiners:
  match m:
    case None{}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}
    case Some{i}:
      ReadyJoiners.of_votes(VotesBeforeJoin.below(all, js, v, s, i), v)

# a and b together
def ReadyJoiners.add(a: ReadyJoiners, b: ReadyJoiners) -> ReadyJoiners:
  match a b:
    case ReadyJoiners{xa, pa} ReadyJoiners{xb, pb}:
      ReadyJoiners{List.append(&2, List<&2, U32>, xa, xb), VotesBeforeJoin.join(pa, pb)}

# the voters of us that are ready joiners of round r for the step s
def ReadyJoiners.of(
  us: List<&2, List<&2, U32>>,
  +all: List<&2, Ballot>,
  +js: List<&2, JudgedBallot>,
  +s: List<&2, U32>,
  +r: Nat
) -> ReadyJoiners:
  match us:
    case Nil{}:
      ReadyJoiners{[], VotesBeforeJoin{True{}, None{}}}
    case Con{+u, rest}:
      ReadyJoiners.add(
        ReadyJoiners.of_join(Ballots.first_join(all, all, u, s, r), all, js, u, s),
        ReadyJoiners.of(rest, all, js, s, r)
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

# a vote for the highest sound lead top, when me may still vote in its round:
# me has not acted in it, has not joined a higher round, and does not lead it
def NextBallot.vote(
  top: Maybe<&2, +Sigma<Nat, _ => List<&2, U32>>>,
  +all: List<&2, Ballot>,
  vs: List<&2, List<&2, U32>>,
  n: Nat,
  +me: List<&2, U32>,
  +s: List<&2, U32>,
  +i: Nat
) -> Maybe<&2, BallotToSign>:
  match top:
    case None{}:
      None{}
    case Some{(+r, x)}:
      Bool.pick(
        Maybe<&2, BallotToSign>,
        Bool.and(
          Bool.not(Ballots.acted_in(all, me, s, r)),
          Bool.and(
            Bool.not(Ballots.joined_above(all, me, s, r, i)),
            Bool.not(leads_round(vs, n, r, me))
          )
        ),
        Some{BallotToSign{i, r, VoteForLead{x}}},
        None{}
      )

# a lead of the round mine, the highest round that me has a ballot in, when me
# leads it, joined it, and has not led it yet
def NextBallot.lead(
  mine: Maybe<&2, Nat>,
  +all: List<&2, Ballot>,
  js: List<&2, JudgedBallot>,
  +vs: List<&2, List<&2, U32>>,
  +n: Nat,
  +me: List<&2, U32>,
  +s: List<&2, U32>,
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
        NextBallot.lead_of(ReadyJoiners.of(vs, all, js, s, r), n, r, i, proposal),
        None{}
      )

# a join of the highest alive round, when it is above every round of me
def NextBallot.join(alive: Maybe<&2, Nat>, mine: Maybe<&2, Nat>, i: Nat) -> Maybe<&2, BallotToSign>:
  match alive mine:
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

# the lowest round above t whose leader is at position q among n voters
def NextBallot.round_after(+q: Nat, +n: Nat, +t: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_lt(t, q), q, Nat.add(q, Nat.mul(n, 1n+Nat.div(Nat.sub(t, q), n))))

# on a tick, a join of the lowest round above t that the voter at position p
# among n voters leads
def NextBallot.call(
  ticked: Bool,
  p: Maybe<&2, Nat>,
  n: Nat,
  t: Nat,
  i: Nat
) -> Maybe<&2, BallotToSign>:
  match ticked p:
    case True{} Some{q}:
      Some{BallotToSign{i, NextBallot.round_after(q, n, t), JoinRound{}}}
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
# choice proposal that it leads with when free, and whether its round timer ran
# out (ticked). Nothing once the step is decided or contradicted, when me is
# not a voter, or while a ballot of its own chain is missing. Else the first of:
# a vote for the highest sound lead that it may still vote for; a lead of its
# round; a join of the highest alive round; on a tick, a join of the next round
# that it leads.
def SlotConsensus.next_ballot(
  +voters: List<&2, List<&2, U32>>,
  +s: List<&2, U32>,
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
      NextBallot.vote(JudgedBallot.top_sound_lead(js), all, vs, n, me, s, i),
      Maybe.or(
        &2,
        BallotToSign,
        NextBallot.lead(mine, all, js, vs, n, me, s, i, proposal),
        Maybe.or(
          &2,
          BallotToSign,
          NextBallot.join(Ballots.top_alive(all, vs, n, s), mine, i),
          NextBallot.call(ticked, position(vs, me), n, Ballots.top_round(all, s), i)
        )
      )
    ),
    None{}
  )

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
  for s: List<&2, U32>
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
  for voters: List<&2, List<&2, U32>>
  for s: List<&2, U32>
  for all: List<&2, Ballot>
  for me: List<&2, U32>
  for proposal: List<&2, U32>
  for ticked: Bool
  for c: BallotToSign
  for k: List<&2, U32>
  for b: Ballot
  {
    SlotConsensus.next_ballot(
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

# Means: a lead or a vote that an honest voter signs next is judged sound among
# the ballots it had, together with the new one.
# For free: with the law below, it stays sound on every node that holds those
# ballots; an honest voter's votes always count toward a decision.
# For the goal: honest voters never waste a vote, so more than half of honest
# voters that hear one another decide (Trust 4, progress).
# Example: a voter that sees the sound lead of round 2 for w7 votes for w7 in
# round 2, and that vote is sound.
law SlotConsensus.next_ballot_is_judged_sound:
  for voters: List<&2, List<&2, U32>>
  for s: List<&2, U32>
  for all: List<&2, Ballot>
  for me: List<&2, U32>
  for proposal: List<&2, U32>
  for ticked: Bool
  for c: BallotToSign
  for k: List<&2, U32>
  {
    SlotConsensus.next_ballot(
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
  for s: List<&2, U32>
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
