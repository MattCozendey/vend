# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/missed_fork@hint -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/shared/quorum.bend as Quorums
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/shared/text.bend as Texts
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../voting.bend as Voting
import ./histories.bend as ProofHistories
import ./lines.bend as ProofLines
import ./trees.bend as ProofTrees
import ../../replica/impl.bend as Replicas

# Rounds
# ------
# Two rounds of one height decide the same step (Spec.Rounds.one). A majority
# cast the step v1 in the round r1. A vote of a later round names a majority
# that passed to it; one of them cast v1 in r1 (two majorities share a node),
# and its pass names a vote of r1 or later. So the vote is the last vote of a
# round from r1 on, which is v1 by the same argument, by induction on the
# round.

# the ballots of the owners os in the round r of the height h of the line c
def Round.ballots(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  os: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Ledgers.Vote>>>:
  Ledgers.Bucket.ballots(
    ~Basics.Ask,
    Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
    os
  )

# the node o cast for the step v in the round r, as a count of ballots reads it
def Round.hit(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h: U32, r: Nat, o: String, v: Ledgers.Vote) -> Bool:
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(
      ~Basics.Ask,
      Ledgers.State.get(
        ~Basics.Ask,
        Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      )
    ),
    v
  )

# a cell that counts for the step v holds a vote for v
def Hit.step(
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  v: Ledgers.Vote
) -> {
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(~Basics.Ask, m),
    v
  )
    == True{}: Bool
} -> {Sealing.Cast.step(m) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.Many{}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Ask{i, t, q}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Data{ws}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Pass{p}}, l}}}
    }:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{
        Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Vote{x, from}}, l}}
      }
    }:
      e => Equal.cong(
        Ledgers.Vote,
        Maybe<&2, Ledgers.Vote>,
        y => Some{y},
        x,
        v,
        Ledgers.Vote.is_eq_sound(x, v)(e)
      )

# a node that counts for the step v in a round cast v there
def Hit.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +o: String,
  v: Ledgers.Vote
) -> {
  Round.hit(s, c, h, r, o, v) == True{}: Bool
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, o) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Slot.bucket(c, h, r),
      Ledgers.Slot.ballot(o)
    ): {Sealing.Cast.step(_) == Some{v}: Maybe<&2, Ledgers.Vote>}
    Hit.step(
      Ledgers.State.get(
        ~Basics.Ask,
        Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      ),
      v
    )(e)

# a vote moved to an equal round
def Cast.moved(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  a: Nat,
  b: Nat,
  v: Ledgers.Vote,
  e: {a == b: Nat}
) -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, a}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, b}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  k =>
    %e: {Sealing.Cast.of(s, Ledgers.Where{c, h, _}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}
    k

# o when it is a hit, else rest
def Voter.if(+hit: Bool, o: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      rest

# the first node of os that cast for the step v in the round r, if any did
def Round.voter(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case Con{+o, rest}:
      Voter.if(Round.hit(s, c, h, r, o, v), o, Round.voter(s, c, h, r, rest, v))

# no hit and no voter in the rest, when there is no voter
def Voter.if_hit(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {hit == False{}: Bool}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => {==}

def Voter.if_rest(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {rest == None{}: Maybe<&2, String>}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {rest == None{}: Maybe<&2, String>},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => e

# Voter.cast once the hit of the first node is known
def Voter.cast.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  rest: Maybe<&2, String>,
  v: Ledgers.Vote,
  p: String,
  +hit: Bool,
  eh: {Round.hit(s, c, h, r, o, v) == hit: Bool},
  ih: {
    rest == Some{p}: Maybe<&2, String>
  } -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voter.if(hit, o, rest) == Some{p}: Maybe<&2, String>
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match hit:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          String,
          o,
          p,
          e
        ): {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Hit.cast(s, c, h, r, o, v)(eh)
    case False{}:
      e => ih(e)

# the voter cast for the step
def Voter.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote,
  +p: String
) -> {
  Round.voter(s, c, h, r, os, v) == Some{p}: Maybe<&2, String>
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match os:
    case Nil{}:
      e => Empty.absurd(
        {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(String, p, e)
      )
    case Con{+o, +rest}:
      Voter.cast.at(
        s,
        c,
        h,
        r,
        o,
        Round.voter(s, c, h, r, rest, v),
        v,
        p,
        Round.hit(s, c, h, r, o, v),
        {==},
        Voter.cast(s, c, h, r, rest, v, p)
      )

# Voter.yes once the hit of the first node is known
def Voter.yes.at(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>,
  y: Nat,
  ih: {rest == None{}: Maybe<&2, String>} -> {y == 0n: Nat}
) -> {
  Voter.if(hit, o, rest) == None{}: Maybe<&2, String>
} -> {Shared.Nat.add_if(hit, y) == 0n: Nat}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {1n+y == 0n: Nat},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => ih(e)

# with no voter, no ballot is for the step
def Voter.yes(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Round.voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>
} -> {
  Quorums.Quorum.yes(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == 0n: Nat
}:
  match os:
    case Nil{}:
      e => {==}
    case Con{o, rest}:
      Voter.yes.at(
        Round.hit(s, c, h, r, o, v),
        o,
        Round.voter(s, c, h, r, rest, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        Voter.yes(s, c, h, r, rest, v)
      )

# nothing is less than a number that is zero
def Lt.none(n: Nat, y: Nat, e: {y == 0n: Nat}) -> {Nat.is_lt(n, y) == True{}: Bool} -> Empty:
  k =>
    Shared.Nat.lt_zero(n)(
      %e: {Nat.is_lt(n, _) == True{}: Bool}
      k)

# a step with a majority has a voter
def Has.voter(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Round.voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>} -> Empty:
  hh => e =>
    Lt.none(
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Voter.yes(s, c, h, r, os, v)(e)
    )(hh)

# Sub.count for a first owner o and a first node f, once it is known whether
# they are the same (b)
def Sub.count.at(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  o: String,
  rest: List<&2, String>,
  +f: String,
  +fs: List<&2, String>,
  +v: Ledgers.Vote,
  b: Bool,
  eb: {String.eq(f, o) == b: Bool},
  ih1: {
    Voting.Owners.sub(rest, fs) == True{}: Bool
  } -> {
    Round.voter(s, c, h, r, fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
      == True{}: Bool
  },
  ih2: {
    Voting.Owners.sub(rest, f <> fs) == True{}: Bool
  } -> {
    Round.voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      1n+List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
      == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Bool,
    b,
    u => Voting.Owners.sub(rest, fs),
    u => Voting.Owners.sub(rest, f <> fs)
  )
    == True{}: Bool
} -> {
  Round.voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    1n+List.length(&2, String, fs),
    Shared.Nat.add_if(
      Bool.not(Round.hit(s, c, h, r, o, v)),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      es => +ev =>
        %Texts.String.eq_sound(
          f,
          o
        )(
          eb
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(Round.hit(s, c, h, r, _, v)),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Round.hit(s, c, h, r, f, v),
          False{},
          Voter.if_hit(Round.hit(s, c, h, r, f, v), f, Round.voter(s, c, h, r, fs, v))(ev)
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(_),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        ih1(es)(Voter.if_rest(Round.hit(s, c, h, r, f, v), f, Round.voter(s, c, h, r, fs, v))(ev))
    case False{}:
      es => ev =>
        Shared.Nat.le_add_if(
          Bool.not(Round.hit(s, c, h, r, o, v)),
          1n+List.length(&2, String, fs),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
        )(ih2(es)(ev))

# nodes that are some of the owners, none of which cast for the step v, are
# at most the ballots that are not for v
def Sub.count(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Voting.Owners.sub(os, from) == True{}: Bool
} -> {
  Round.voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    List.length(&2, String, from),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
  )
    == True{}: Bool
}:
  match os from:
    case Nil{} Nil{}:
      es => ev => {==}
    case Nil{} Con{f, fs}:
      es => ev => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(es))
    case Con{o, rest} Nil{}:
      es => ev => Shared.Nat.le_zero(
        Quorums.Quorum.no(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(s, c, h, r, o <> rest),
          v
        )
      )
    case Con{+o, +rest} Con{+f, +fs}:
      Sub.count.at(
        s,
        c,
        h,
        r,
        o,
        rest,
        f,
        fs,
        v,
        String.eq(f, o),
        {==},
        Sub.count(s, c, h, r, rest, fs, v),
        Sub.count(s, c, h, r, rest, f <> fs, v)
      )

# Count.total once the hit of the first node is known
def Count.total.at(
  hit: Bool,
  y: Nat,
  n: Nat,
  l: Nat,
  ih: {Nat.add(y, n) == l: Nat}
) -> {Nat.add(Shared.Nat.add_if(hit, y), Shared.Nat.add_if(Bool.not(hit), n)) == 1n+l: Nat}:
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
    case False{}:
      Equal.trans(
        Nat,
        Nat.add(y, 1n+n),
        1n+Nat.add(y, n),
        1n+l,
        Shared.Nat.add_succ(y, n),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
      )

# each owner's ballot is for the step v, or is not
def Count.total(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Nat.add(
    Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
  )
    == List.length(&2, String, os): Nat
}:
  match os:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      Count.total.at(
        Round.hit(s, c, h, r, o, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        List.length(&2, String, rest),
        Count.total(s, c, h, r, rest, v)
      )

# a number is at most a number equal to it
def Le.same(a: Nat, b: Nat, e: {a == b: Nat}) -> {Nat.is_le(a, b) == True{}: Bool}:
  %e: {Nat.is_le(a, _) == True{}: Bool}
  Shared.Nat.le_refl(a)

# two majorities share a node: nodes that are a majority of the owners, none
# of which cast for the step v, leave v no majority
def Major.meets(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Voting.Owners.sub(os, from) == True{}: Bool}
  -> {Voting.Owners.major(os, from) == True{}: Bool}
  -> {Round.voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>}
  -> Empty:
  hh => es => em => ev =>
    Shared.Nat.pigeon(
      List.length(&2, String, from),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      List.length(&2, String, os)
    )(
      Sub.count(s, c, h, r, os, from, v)(es)(ev)
    )(
      hh
    )(
      Le.same(
        Nat.add(
          Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
        ),
        List.length(&2, String, os),
        Count.total(s, c, h, r, os, v)
      )
    )(em)

# the round of a last vote, 0 without one
def Last.round(m: Maybe<&2, Ledgers.Last>) -> Nat:
  match m:
    case Some{Ledgers.Last{r, v}}:
      r
    case None{}:
      0n

# the step of a last vote, d without one
def Last.step(d: Ledgers.Vote, m: Maybe<&2, Ledgers.Last>) -> Ledgers.Vote:
  match m:
    case Some{Ledgers.Last{r, v}}:
      v
    case None{}:
      d

# the last vote m is of the round r1 or of a later one
def Last.from(m: Maybe<&2, Ledgers.Last>, r1: Nat) -> Bool:
  match m:
    case Some{Ledgers.Last{r, v}}:
      Nat.is_le(r1, r)
    case None{}:
      False{}

# Mine.le for one round
def Mine.le.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Nat.is_le(r, k) == True{}: Bool}
) -> {
  Voting.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, k) == True{}: Bool}:
  match m:
    case Some{y}:
      e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Nat.is_le(_, k) == True{}: Bool}
        Shared.Nat.le_refl(k)
    case None{}:
      e => ih(e)

# the last vote of a node up to the round p is of a round up to p
def Mine.le(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Voting.Last.mine(q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, p) == True{}: Bool}:
  match p:
    case 0n:
      Mine.le.or(
        0n,
        Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
        None{},
        r,
        x,
        e => Empty.absurd(
          {Nat.is_le(r, 0n) == True{}: Bool},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.le.or(
        1n+j,
        Sealing.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
        Voting.Last.mine(q, s, c, h, j),
        r,
        x,
        e => Shared.Nat.le_succ(r, j)(Mine.le(s, c, h, q, j, r, x)(e))
      )

# Mine.cast for one round
def Mine.cast.or(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  em: {Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q) == m: Maybe<&2, Ledgers.Vote>},
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voting.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case Some{y}:
      +e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Sealing.Cast.of(s, Ledgers.Where{c, h, _}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Ledgers.Vote,
          Last.step(y),
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q) == Some{_}: Maybe<&2, Ledgers.Vote>}
        em
    case None{}:
      e => ih(e)

# the last vote of a node is a vote that it cast
def Mine.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Voting.Last.mine(q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match p:
    case 0n:
      Mine.cast.or(
        s,
        c,
        h,
        q,
        0n,
        Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
        {==},
        None{},
        r,
        x,
        e => Empty.absurd(
          {Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.cast.or(
        s,
        c,
        h,
        q,
        1n+j,
        Sealing.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
        {==},
        Voting.Last.mine(q, s, c, h, j),
        r,
        x,
        Mine.cast(s, c, h, q, j, r, x)
      )

# Cast.apart once it is known whether the rounds are the same (b)
def Cast.apart.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote,
  b: Bool,
  eb: {Nat.is_eq(r1, k) == b: Bool}
) -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {b == False{}: Bool}:
  match b:
    case True{}:
      e1 => en => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          Ledgers.Vote,
          v1,
          Equal.trans(
            Maybe<&2, Ledgers.Vote>,
            None{},
            Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q),
            Some{v1},
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q),
              None{},
              en
            ),
            Cast.moved(s, c, h, q, r1, k, v1, Shared.Nat.is_eq_sound(r1, k)(eb))(e1)
          )
        )
      )
    case False{}:
      e1 => en => {==}

# a round with a vote of a node is not a round without one
def Cast.apart(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote
) -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {Nat.is_eq(r1, k) == False{}: Bool}:
  e1 => en => Cast.apart.at(s, c, h, q, r1, k, v1, Nat.is_eq(r1, k), {==})(e1)(en)

# Mine.from for one round
def Mine.from.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Nat.is_le(r1, k) == True{}: Bool
} -> (
  {m == None{}: Maybe<&2, Ledgers.Vote>} -> {Last.from(rest, r1) == True{}: Bool}
) -> {Last.from(Voting.Last.or(k, m, u => rest), r1) == True{}: Bool}:
  match m:
    case Some{y}:
      hk => ih => hk
    case None{}:
      hk => ih => ih({==})

# a node that cast in the round r1 has a last vote of r1 or later, up to any
# round from r1 on
def Mine.from(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Sealing.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Nat.is_le(r1, p) == True{}: Bool
} -> {Last.from(Voting.Last.mine(q, s, c, h, p), r1) == True{}: Bool}:
  match p:
    case 0n:
      +e1 => +le =>
        Mine.from.or(
          0n,
          Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
          None{},
          r1
        )(
          le
        )(
          en => Empty.absurd(
            {False{} == True{}: Bool},
            Shared.Maybe.none_ne_some(
              Ledgers.Vote,
              v1,
              Equal.trans(
                Maybe<&2, Ledgers.Vote>,
                None{},
                Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
                Some{v1},
                Equal.sym(
                  Maybe<&2, Ledgers.Vote>,
                  Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
                  None{},
                  en
                ),
                Cast.moved(s, c, h, q, r1, 0n, v1, Shared.Nat.le_zero_eq(r1)(le))(e1)
              )
            )
          )
        )
    case 1n+(+j):
      +e1 => +le =>
        Mine.from.or(
          1n+j,
          Sealing.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
          Voting.Last.mine(q, s, c, h, j),
          r1
        )(
          le
        )(
          en => Mine.from(
            s,
            c,
            h,
            q,
            j,
            r1,
            v1
          )(e1)(Shared.Nat.le_step(r1, j)(le)(Cast.apart(s, c, h, q, r1, 1n+j, v1)(e1)(en)))
        )

# Newer.left once it is known whether the round of a is less than that of b
def Newer.left.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, ra) == False{}: Bool}:
  match b:
    case True{}:
      e => Shared.Nat.nle_trans(r1, ra, rb)(e)(Shared.Nat.lt_weak(ra, rb)(eb))
    case False{}:
      e => e

# when the newer of two last votes is before the round r1, so is the first
def Newer.left(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Last.from(Voting.Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(a, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => {==}
    case Some{x} None{}:
      e => e
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.left.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# Newer.right once it is known whether the round of a is less than that of b
def Newer.right.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, rb) == False{}: Bool}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Shared.Nat.nle_trans(r1, rb, ra)(e)(Shared.Nat.nlt_le(ra, rb)(eb))

# when the newer of two last votes is before the round r1, so is the second
def Newer.right(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Last.from(Voting.Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(b, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => e
    case Some{x} None{}:
      e => {==}
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.right.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# the rule that the passes that a vote names allow it, at the head hd whose tip is tp
def Rules.allow(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Voting.Rounds.Allow(s, c, Sealing.Head.next(hd), Replicas.Tip.owners(tp)):
  Shared.Pair.first(
    Voting.Rounds.Allow(s, c, Sealing.Head.next(hd), Replicas.Tip.owners(tp)),
    Voting.Rounds.Last(
      s,
      c,
      Sealing.Head.next(hd)
    )
      & Voting.Rounds.Same(s, c, Sealing.Head.next(hd)),
    rules(hd)(tp)(ok)
  )

# the rule that a pass names the last vote of its node below its round, at the head hd whose tip is tp
def Rules.last(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Voting.Rounds.Last(s, c, Sealing.Head.next(hd)):
  Shared.Pair.first(
    Voting.Rounds.Last(s, c, Sealing.Head.next(hd)),
    Voting.Rounds.Same(s, c, Sealing.Head.next(hd)),
    Shared.Pair.second(
      Voting.Rounds.Allow(s, c, Sealing.Head.next(hd), Replicas.Tip.owners(tp)),
      Voting.Rounds.Last(
        s,
        c,
        Sealing.Head.next(hd)
      )
        & Voting.Rounds.Same(s, c, Sealing.Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# the rule that the votes of one round are for one step, at the head hd whose tip is tp
def Rules.same(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Voting.Rounds.Same(s, c, Sealing.Head.next(hd)):
  Shared.Pair.second(
    Voting.Rounds.Last(s, c, Sealing.Head.next(hd)),
    Voting.Rounds.Same(s, c, Sealing.Head.next(hd)),
    Shared.Pair.second(
      Voting.Rounds.Allow(s, c, Sealing.Head.next(hd), Replicas.Tip.owners(tp)),
      Voting.Rounds.Last(
        s,
        c,
        Sealing.Head.next(hd)
      )
        & Voting.Rounds.Same(s, c, Sealing.Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# Pass.miss for a first node o, once its hit in the round r1 (hit) and its
# pass (m) are known
def Pass.miss.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  +o: String,
  rest: Maybe<&2, String>,
  hit: Bool,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> {Round.hit(s, c, Sealing.Head.next(hd), r1, o, v1) == hit: Bool}
  -> {
    Ledgers.State.passed(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
      o
    )
      == m: Maybe<&2, Maybe<&2, Ledgers.Last>>
  }
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, m) == True{}: Bool}
  -> {Last.from(Voting.Passed.last(m), r1) == False{}: Bool}
  -> {rest == None{}: Maybe<&2, String>}
  -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>}:
  match hit m:
    case False{} y:
      eh => em => le => es => ef => ih => ih
    case True{} None{}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(es)
      )
    case True{} Some{l}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(Equal.trans(
            Bool,
            False{},
            Last.from(l, r1),
            True{},
            Equal.sym(Bool, Last.from(l, r1), False{}, ef),
            %Equal.sym(Maybe<&2, Ledgers.Last>, l, Voting.Last.mine(o, s, c, Sealing.Head.next(hd), p), Rules.last(~s, ~c, ~rules, hd, tp, ok)(1n+p)(o)(l)(em)): {Last.from(_, r1) == True{}: Bool}
            Mine.from(s, c, Sealing.Head.next(hd), o, p, r1, v1)(Hit.cast(s, c, Sealing.Head.next(hd), r1, o, v1)(eh))(le)))
      )

# when the passes of the nodes from to the round 1 + p name no vote of the
# round r1 or later, none of them cast in r1
def Pass.miss(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  from: List<&2, String>
) -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from) == True{}: Bool}
  -> {
    Last.from(
      Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
      r1
    )
      == False{}: Bool
  }
  -> {Round.voter(s, c, Sealing.Head.next(hd), r1, from, v1) == None{}: Maybe<&2, String>}:
  match from:
    case Nil{}:
      le => ea => ef => {==}
    case Con{+o, +rest}:
      +le => +ea => +ef =>
        Pass.miss.at(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          p,
          r1,
          v1,
          o,
          Round.voter(s, c, Sealing.Head.next(hd), r1, rest, v1),
          Round.hit(s, c, Sealing.Head.next(hd), r1, o, v1),
          Ledgers.State.passed(
            ~Basics.Ask,
            Replicas.State.ledger(~Basics.Ask.machine(), s),
            Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
            o
          )
        )(
          {==}
        )(
          {==}
        )(
          le
        )(
          Shared.List.all.if_hit(
            Maybe.is_some(
              &2,
              Maybe<&2, Ledgers.Last>,
              Ledgers.State.passed(
                ~Basics.Ask,
                Replicas.State.ledger(~Basics.Ask.machine(), s),
                Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
                o
              )
            ),
            u => Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, rest)
          )(ea)
        )(
          Newer.left(
            Voting.Passed.last(
              Ledgers.State.passed(
                ~Basics.Ask,
                Replicas.State.ledger(~Basics.Ask.machine(), s),
                Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
                o
              )
            ),
            Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, rest),
            r1
          )(ef)
        )(
          Pass.miss(
            ~s,
            ~c,
            ~rules,
            hd,
            tp,
            ok,
            p,
            r1,
            v1,
            rest
          )(
            le
          )(
            Shared.List.all.if_rest(
              Maybe.is_some(
                &2,
                Maybe<&2, Ledgers.Last>,
                Ledgers.State.passed(
                  ~Basics.Ask,
                  Replicas.State.ledger(~Basics.Ask.machine(), s),
                  Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
                  o
                )
              ),
              u => Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, rest)
            )(ea)
          )(
            Newer.right(
              Voting.Passed.last(
                Ledgers.State.passed(
                  ~Basics.Ask,
                  Replicas.State.ledger(~Basics.Ask.machine(), s),
                  Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
                  o
                )
              ),
              Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, rest),
              r1
            )(ef)
          )
        )

# the case of a choice by b
def When.elim(
  -R: Type,
  x: Bool,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  l: Ledgers.Last
) -> {
  Shared.Bool.when(Maybe<&2, Ledgers.Last>, x, u => b, u => a) == Some{l}: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> R
) -> ({a == Some{l}: Maybe<&2, Ledgers.Last>} -> R) -> R:
  match x:
    case True{}:
      e => f => g => f(e)
    case False{}:
      e => f => g => g(e)

# that the pass of some node to the place w names the last vote l
def Named(-R: Type, s: Replicas.Node<Basics.Ask>, w: Ledgers.Where, l: Ledgers.Last) -> Type:
  (
    @q: String -> {
      Voting.Passed.last(
        Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, q)
      )
        == Some{l}: Maybe<&2, Ledgers.Last>
    } -> R
  ) -> R

# Last.elim for a first node o, once what it named (a) and what the rest
# named (b) are known
def Last.elim.at(
  -R: Type,
  s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  o: String,
  l: Ledgers.Last,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {
  Voting.Passed.last(
    Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)
  )
    == a: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l)
) -> {Voting.Last.newer(a, b) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
  match a b:
    case None{} y:
      ea => ih => e => ih(e)
    case Some{x} None{}:
      ea => ih => e => k => k(
        o
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          Voting.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
          Some{x},
          Some{l},
          ea,
          e
        )
      )
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      ea => ih => e =>
        When.elim(
          Named(R, s, w, l),
          Nat.is_lt(ra, rb),
          Some{Ledgers.Last{ra, va}},
          Some{Ledgers.Last{rb, vb}},
          l
        )(
          e
        )(
          ih
        )(
          e2 => k => k(
            o
          )(
            Equal.trans(
              Maybe<&2, Ledgers.Last>,
              Voting.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
              Some{Ledgers.Last{ra, va}},
              Some{l},
              ea,
              e2
            )
          )
        )

# the last vote of the highest round that passes name is named by one of them
def Last.elim(
  -R: Type,
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  from: List<&2, String>,
  +l: Ledgers.Last
) -> {Voting.Passes.last(s, w, from) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
  match from:
    case Nil{}:
      e => k => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Last, l, e))
    case Con{+o, +rest}:
      Last.elim.at(
        R,
        s,
        w,
        o,
        l,
        Voting.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
        Voting.Passes.last(s, w, rest)
      )({==})(Last.elim(R, s, w, rest, l))

# a pass that names a last vote is held
def Passed.some(
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  l: Ledgers.Last
) -> {
  Voting.Passed.last(m) == Some{l}: Maybe<&2, Ledgers.Last>
} -> {m == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {None{} == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>},
        Shared.Maybe.none_ne_some(Ledgers.Last, l, e)
      )
    case Some{x}:
      e => Equal.cong(
        Maybe<&2, Ledgers.Last>,
        Maybe<&2, Maybe<&2, Ledgers.Last>>,
        y => Some{y},
        x,
        Some{l},
        e
      )

# the parts of the rule of a later round
def Later.all(a: Bool, b: Bool, c: Bool, d: Bool) -> Bool:
  List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => d, c), b), a)

def Later.all.a(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => e

def Later.all.b(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {b == True{}: Bool}:
  match a b:
    case True{} True{}:
      e => {==}
    case True{} False{}:
      e => e
    case False{} y:
      e => Empty.absurd({y == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.c(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {c == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => {==}
    case True{} True{} False{}:
      e => e
    case True{} False{} z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.d(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {d == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => e
    case True{} True{} False{}:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case True{} False{} z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))

# that each vote of a round from r1 on, below the round j, is for the step v1
def Rounds.Below(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r1: Nat,
  v1: Ledgers.Vote,
  j: Nat
) -> Type:
  @rm: Nat -> @qm: String -> @vm: Ledgers.Vote -> {
    Nat.is_lt(rm, j) == True{}: Bool
  } -> {
    Nat.is_le(r1, rm) == True{}: Bool
  } -> {
    Sealing.Cast.of(s, Ledgers.Where{c, h, rm}, qm) == Some{vm}: Maybe<&2, Ledgers.Vote>
  } -> {vm == v1: Ledgers.Vote}

# Rounds.last once the node qw that named the last vote is known, with its
# last vote
def Rounds.named(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  j: Nat,
  +rm: Nat,
  +vm: Ledgers.Vote,
  +qw: String,
  +em: {
    Voting.Last.mine(
      qw,
      s,
      c,
      Sealing.Head.next(hd),
      p
    )
      == Some{Ledgers.Last{rm, vm}}: Maybe<&2, Ledgers.Last>
  },
  lt: {Nat.is_lt(p, j) == True{}: Bool},
  le: {Nat.is_le(r1, rm) == True{}: Bool},
  ih: Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, j)
) -> {vm == v1: Ledgers.Vote}:
  ih(
    rm
  )(
    qw
  )(
    vm
  )(
    Shared.Nat.le_lt(rm, p, j)(Mine.le(s, c, Sealing.Head.next(hd), qw, p, rm, vm)(em))(lt)
  )(le)(Mine.cast(s, c, Sealing.Head.next(hd), qw, p, rm, vm)(em))

# Rounds.round once the last vote m that the passes name is known: it is of
# the round r1 or later, and the vote x is for its step
def Rounds.last(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  x: Ledgers.Vote,
  j: Nat,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Voting.Passes.last(
    s,
    Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
    from
  )
    == m: Maybe<&2, Ledgers.Last>
}
  -> {Last.from(m, r1) == True{}: Bool}
  -> {Voting.Last.is(m, x) == True{}: Bool}
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => ef => ei => lt => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(ef)
      )
    case Some{Ledgers.Last{+rm, +vm}}:
      em => ef => ei => lt => ih =>
        Last.elim(
          {x == v1: Ledgers.Vote},
          s,
          Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
          from,
          Ledgers.Last{rm, vm}
        )(em)(
          +qw => ew =>
            %Ledgers.Vote.is_eq_sound(vm, x)(ei): {_ == v1: Ledgers.Vote}
            Rounds.named(~s, ~c, ~rules, hd, tp, ok, r1, v1, p, j, rm, vm, qw, Equal.sym(Maybe<&2, Ledgers.Last>, Some{Ledgers.Last{rm, vm}}, Voting.Last.mine(qw, s, c, Sealing.Head.next(hd), p), Rules.last(~s, ~c, ~rules, hd, tp, ok)(1n+p)(qw)(Some{Ledgers.Last{rm, vm}})(Passed.some(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, qw), Ledgers.Last{rm, vm})(ew))), lt, ef, ih))

# Rounds.round once it is known whether the passes name a vote of the round
# r1 or later (f)
def Rounds.pick(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +p: Nat,
  +x: Ledgers.Vote,
  j: Nat,
  +from: List<&2, String>,
  f: Bool
) -> {
  Last.from(
    Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
    r1
  )
    == f: Bool
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, j)
  -> {
    Later.all(
      Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
      Voting.Owners.sub(Replicas.Tip.owners(tp), from),
      Voting.Owners.major(Replicas.Tip.owners(tp), from),
      Voting.Last.is(Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from), x)
    )
      == True{}: Bool
  }
  -> {x == v1: Ledgers.Vote}:
  match f:
    case False{}:
      ef => hh => lt => le => ih => +al =>
        Empty.absurd(
          {x == v1: Ledgers.Vote},
          Major.meets(
            s,
            c,
            Sealing.Head.next(hd),
            r1,
            Replicas.Tip.owners(tp),
            from,
            v1
          )(
            hh
          )(
            Later.all.b(
              Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
              Voting.Owners.sub(Replicas.Tip.owners(tp), from),
              Voting.Owners.major(Replicas.Tip.owners(tp), from),
              Voting.Last.is(
                Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Later.all.c(
              Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
              Voting.Owners.sub(Replicas.Tip.owners(tp), from),
              Voting.Owners.major(Replicas.Tip.owners(tp), from),
              Voting.Last.is(
                Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Pass.miss(
              ~s,
              ~c,
              ~rules,
              hd,
              tp,
              ok,
              p,
              r1,
              v1,
              from
            )(
              le
            )(
              Later.all.a(
                Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
                Voting.Owners.sub(Replicas.Tip.owners(tp), from),
                Voting.Owners.major(Replicas.Tip.owners(tp), from),
                Voting.Last.is(
                  Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
                  x
                )
              )(al)
            )(ef)
          )
        )
    case True{}:
      ef => hh => lt => le => ih => al =>
        Rounds.last(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          from,
          Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from)
        )(
          {==}
        )(
          ef
        )(
          Later.all.d(
            Voting.Passed.all(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
            Voting.Owners.sub(Replicas.Tip.owners(tp), from),
            Voting.Owners.major(Replicas.Tip.owners(tp), from),
            Voting.Last.is(
              Voting.Passes.last(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, from),
              x
            )
          )(al)
        )(lt)(ih)

# Rounds.same at the round r1 itself, once a voter m of the step v1 is known
def Rounds.base(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  q: String,
  x: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(
    s,
    c,
    Sealing.Head.next(hd),
    r1,
    Replicas.Tip.owners(tp),
    v1
  )
    == m: Maybe<&2, String>
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Sealing.Cast.of(
      s,
      Ledgers.Where{c, Sealing.Head.next(hd), r1},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => hh => e => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Has.voter(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp), v1)(hh)(em)
      )
    case Some{+o}:
      em => hh => e => Rules.same(
        ~s,
        ~c,
        ~rules,
        hd,
        tp,
        ok
      )(
        r1
      )(
        q
      )(
        o
      )(x)(v1)(e)(Voter.cast(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp), v1, o)(em))

# Rounds.same in a round after r1
def Rounds.step(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  v1: Ledgers.Vote,
  r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat
) -> {Nat.is_eq(r1, r) == False{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Sealing.Cast.of(
      s,
      Ledgers.Where{c, Sealing.Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match r:
    case 0n:
      ne => hh => lt => le => e => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_eq(r1, 0n),
            True{},
            Equal.sym(Bool, Nat.is_eq(r1, 0n), False{}, ne),
            Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), r1, 0n, Shared.Nat.le_zero_eq(r1)(le))
          )
        )
      )
    case 1n+(+p):
      ne => hh => lt => le => e => ih =>
        Rounds.pick(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          Voting.Cast.from(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, q),
          Last.from(
            Voting.Passes.last(
              s,
              Ledgers.Where{c, Sealing.Head.next(hd), 1n+p},
              Voting.Cast.from(s, Ledgers.Where{c, Sealing.Head.next(hd), 1n+p}, q)
            ),
            r1
          )
        )(
          {==}
        )(
          hh
        )(
          lt
        )(
          Shared.Nat.le_step(r1, p)(le)(ne)
        )(ih)(Rules.allow(~s, ~c, ~rules, hd, tp, ok)(1n+p)(q)(x)(e))

# Rounds.same once it is known whether the round is r1 (b)
def Rounds.same.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat,
  b: Bool
) -> {Nat.is_eq(r1, r) == b: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Sealing.Cast.of(
      s,
      Ledgers.Where{c, Sealing.Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match b:
    case True{}:
      eb => hh => lt => le => e => ih =>
        Rounds.base(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          q,
          x,
          Round.voter(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp), v1)
        )(
          {==}
        )(
          hh
        )(
          Cast.moved(
            s,
            c,
            Sealing.Head.next(hd),
            q,
            r,
            r1,
            x,
            Equal.sym(Nat, r1, r, Shared.Nat.is_eq_sound(r1, r)(eb))
          )(e)
        )
    case False{}:
      eb => hh => lt => le => e => ih =>
        Rounds.step(~s, ~c, ~rules, hd, tp, ok, r1, v1, r, q, x, j)(eb)(hh)(lt)(le)(e)(ih)

# each vote of a round from r1 on, below the round k, is for the step that a
# majority cast in r1
def Rounds.same(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
    v1
  )
    == True{}: Bool
} -> Rounds.Below(s, c, Sealing.Head.next(hd), r1, v1, k):
  match k:
    case 0n:
      hh => rm => qm => vm => lt => le => e => Empty.absurd(
        {vm == v1: Ledgers.Vote},
        Shared.Nat.lt_zero(rm)(lt)
      )
    case 1n+(+j):
      +hh => +rm => qm => vm => lt => le => e =>
        Rounds.same.at(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          rm,
          qm,
          vm,
          j,
          Nat.is_eq(r1, rm)
        )({==})(hh)(lt)(le)(e)(Rounds.same(~s, ~c, ~rules, hd, tp, ok, j, r1, v1)(hh))

# Rounds.later once a voter m of the step v2 in the round r2 is known
def Rounds.later.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(
    s,
    c,
    Sealing.Head.next(hd),
    r2,
    Replicas.Tip.owners(tp),
    v2
  )
    == m: Maybe<&2, String>
}
  -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Sealing.Head.next(hd), r2, Replicas.Tip.owners(tp)),
      v2
    )
      == True{}: Bool
  }
  -> {v2 == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => le => h1 => h2 => Empty.absurd(
        {v2 == v1: Ledgers.Vote},
        Has.voter(s, c, Sealing.Head.next(hd), r2, Replicas.Tip.owners(tp), v2)(h2)(em)
      )
    case Some{+o}:
      em => le => h1 => h2 =>
        Rounds.same(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          1n+r2,
          r1,
          v1
        )(
          h1
        )(
          r2
        )(
          o
        )(
          v2
        )(
          Shared.Nat.lt_succ(r2)
        )(le)(Voter.cast(s, c, Sealing.Head.next(hd), r2, Replicas.Tip.owners(tp), v2, o)(em))

# a round decides what an earlier round of its height decided
def Rounds.later(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +r2: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote
) -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Sealing.Head.next(hd), r1},
      Replicas.Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Sealing.Head.next(hd), r2},
      Replicas.Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v2 == v1: Ledgers.Vote}:
  le => d1 => d2 =>
    Rounds.later.at(
      ~s,
      ~c,
      ~rules,
      hd,
      tp,
      ok,
      r1,
      r2,
      v1,
      v2,
      Round.voter(s, c, Sealing.Head.next(hd), r2, Replicas.Tip.owners(tp), v2)
    )(
      {==}
    )(
      le
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, Sealing.Head.next(hd), r1, Replicas.Tip.owners(tp)),
        v1
      )(d1)
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, Sealing.Head.next(hd), r2, Replicas.Tip.owners(tp)),
        v2
      )(d2)
    )

# Rounds.one once it is known whether r1 is at most r2 (b)
def Rounds.one.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  v2: Ledgers.Vote,
  b: Bool
) -> {Nat.is_le(r1, r2) == b: Bool}
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Sealing.Head.next(hd), r1},
      Replicas.Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Sealing.Head.next(hd), r2},
      Replicas.Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v1 == v2: Ledgers.Vote}:
  match b:
    case True{}:
      eb => d1 => d2 => Equal.sym(
        Ledgers.Vote,
        v2,
        v1,
        Rounds.later(~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2)(eb)(d1)(d2)
      )
    case False{}:
      eb => d1 => d2 =>
        Rounds.later(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r2,
          r1,
          v2,
          v1
        )(Shared.Nat.nle_le(r1, r2)(eb))(d2)(d1)

# the rounds of a height decide one step, when the ballots follow the rules
# of rounds: a later round can only decide what an earlier round decided
def Rounds.one(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c)
) -> ProofHistories.Line.One(s, c):
  +hd => +tp => +ok => +r1 => +r2 => v1 => v2 => d1 => d2 =>
    Rounds.one.at(~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2, Nat.is_le(r1, r2))({==})(d1)(d2)

# the rounds of each of k heights decide one step, when the ballots follow the
# rules of rounds
def Rounds.ones(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Voting.Rounds.Rules(s, c),
  k: Nat
) -> ProofHistories.Line.Ones(k, s, c):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      (Rounds.ones(~s, ~c, ~rules, p), Rounds.one(~s, ~c, ~rules))

def Spec.Line.at_agrees(u, c, rules, rs1, rs2, a, b, h, x, y):
  ga => gb => el => ea => eb =>
    ProofHistories.At.same(
      rs1,
      rs2,
      u,
      c,
      h,
      x,
      y
    )(
      Rounds.ones(~u, ~c, ~rules, List.length(&2, Nat, rs1))
    )(
      el
    )(
      Spec.Line.at_grows(rs1, a, u, c, h, x)(ga)(ea)
    )(Spec.Line.at_grows(rs2, b, u, c, h, y)(gb)(eb))

def Spec.Cast.put_keeps(n, w, th, qs, from, s2, t2, s, s3):
  +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Replicas.Node<Basics.Ask>>,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      Some{s3},
      e
    ): {Reading.Node.grows(s2, Sealing.Cast.vote(s, _, w, n, a0)) == True{}: Bool}
    ProofTrees.Grows.trans(
      s2,
      s4,
      Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
    )(
      ProofTrees.Grows.to(
        s2,
        s3,
        s4,
        ProofTrees.Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
        ProofLines.Put.grew(s2, [Replicas.Tip.words(t2)], s3, e)
      )
    )(ProofTrees.Cast.seal.grows(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n)))

def Spec.Cast.put_tip(n, w, th, qs, from, s2, t2, s, s3):
  +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Replicas.Node<Basics.Ask>>,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      Some{s3},
      e
    ): {
      Replicas.Tip.at(~Basics.Ask.machine(), 
        Sealing.Cast.vote(s, _, w, n, a0),
        Replicas.Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Replicas.Tip>
    }
    ProofLines.Tip.at.grows(
      s3,
      Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n)),
      Replicas.Tip.hash(t2),
      t2,
      ProofTrees.Grows.trans(
        s3,
        s4,
        Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
      )(
        ProofTrees.Grows.to(
          s3,
          s3,
          s4,
          ProofTrees.Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
          ProofTrees.Grows.refl(s3)
        )
      )(ProofTrees.Cast.seal.grows(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n)))
    )(ProofLines.Tip.put.at(s2, t2, s3)(e))

# lines with the same key have the same key
def Key.same(
  c2: Ledgers.Chain,
  c: Ledgers.Chain
) -> {
  Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool
} -> {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}:
  Shared.List.is_eq_sound(
    ~Bool,
    ~Shared.Bool.is_eq,
    ~Shared.Bool.laws(),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c)
  )

def Spec.Node.affects_used(s, b):
  +g = Reading.Seen.of(s, b)
  Shared.List.keep_holds(
    ~Reading.Touch,
    ~Reading.Seen,
    ~Reading.Touch.holds,
    Reading.Affects.cands(s, b, g),
    g
  )
