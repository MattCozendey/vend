import Base
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../codes.bend as Coded
import ../shared/lists.bend as Lists
import ../types.bend as Types

# Rounds
# ------
# A slot of a line is decided in rounds: 0, 1, 2, ... Each round is the turn
# of one of the nodes that decide the slot: it votes for a pick, and the
# others vote as it did. A slot is decided for a pick when, in one round,
# more than half of the nodes cast a sound vote for it. When the node whose
# turn a round is cast no ballot there, another node calls its own next
# round and the others promise it (Slot.pass), so a lost node does not stop
# a slot.
#
# The ballots of a voter for a slot are a chain: they have the numbers 0, 1,
# 2, ..., and a ballot is read only when all the ballots before it are held.
# So a voter cannot hide a ballot: two ballots with one number are a lie.
# Every reader checks the ballots, and reads the same from them, whatever
# the voters did: a voter is trusted only to cast no two ballots with one
# number.

# Turns
# -----

# the node whose turn is k steps after y, in the round of x then ns, where r
# are the nodes after y
def Turn.go(k: Nat, +x: String, +ns: List<&2, String>, y: String, r: List<&2, String>) -> String:
  match k r:
    case 0n _:
      y
    case 1n+j Nil{}:
      Turn.go(j, x, ns, x, ns)
    case 1n+j Con{z, r2}:
      Turn.go(j, x, ns, z, r2)

# the node among ns whose turn the number k is, by a walk of k steps: a
# clear def, for the laws
def Turn.walk(ns: List<&2, String>, k: Nat) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{+x, +r}:
      Turn.go(k, x, r, x, r)

# the node at the place j among ns; "" when ns ends before
def Turn.nth(ns: List<&2, String>, j: Nat) -> String:
  match ns j:
    case Nil{} j2:
      ""
    case Con{y, r} 0n:
      y
    case Con{y, r} 1n+p:
      Turn.nth(r, p)

# the node among ns whose turn the number k is: the one at the place of k
# in a round, with no walk (rounds.bend proves that it is Turn.walk)
def Turn.of(ns: List<&2, String>, k: Nat) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{x, +r}:
      Turn.nth(x <> r, Nat.mod(k, 1n+List.length(&2, String, r)))

# The ballots of a slot
# ---------------------

# a ballot for a slot: who cast it, its number, and what it casts
type Ballot is Data:
  Ballot{voter: String, turn: Nat, cast: Types.Cast}

# the ballots among fs for the slot k of the line c
def Slot.ballots(fs: List<&2, Types.Fact>, +c: Ledgers.Line, +k: Nat) -> List<&2, Ballot>:
  match fs:
    case Nil{}:
      []
    case Con{Types.Fact.Ask{a}, rest}:
      Slot.ballots(rest, c, k)
    case Con{Types.Fact.Vote{v, Types.Step.Broken{}, x}, rest}:
      Slot.ballots(rest, c, k)
    case Con{Types.Fact.Vote{v, Types.Step.At{c2, k2, t}, x}, rest}:
      List.filter.put(
        Ballot,
        Ballot{v, t, x},
        Slot.ballots(rest, c, k),
        Bool.and(Ledgers.Line.is_eq(c2, c), Nat.is_eq(k2, k))
      )

# what the ballot b casts, when it is the one that g names
def Ballot.casts(g: Types.Ref, b: Ballot) -> Maybe<&2, Types.Cast>:
  match g b:
    case Types.Ref{v, t} Ballot{w, u, x}:
      Shared.Maybe.when(Types.Cast, Bool.and(String.eq(w, v), Nat.is_eq(u, t)), z => Some{x})

# what the ballots among bs that g names cast
def Casts.of(bs: List<&2, Ballot>, +g: Types.Ref) -> List<&2, Types.Cast>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      Shared.Maybe.cons(Types.Cast, Ballot.casts(g, b), Casts.of(rest, g))

# what the voter v casts with its ballot of the number t, among bs: nothing
# when bs holds none, or two that differ
def Ballots.at(bs: List<&2, Ballot>, v: String, t: Nat) -> Maybe<&2, Types.Cast>:
  Shared.List.agreed(~Types.Cast, ~Coded.Cast.is_eq, Casts.of(bs, Types.Ref{v, t}))

# the round of the cast x
def Cast.round(x: Types.Cast) -> Nat:
  match x:
    case Types.Cast.Vote{r, p, b}:
      r
    case Types.Cast.Pass{r}:
      r

# the round of the ballot b
def Ballot.round(b: Ballot) -> Nat:
  match b:
    case Ballot{v, t, x}:
      Cast.round(x)

# the number of the ballot b
def Ballot.turn(b: Ballot) -> Nat:
  match b:
    case Ballot{v, t, x}:
      t

# Chains
# ------
# The ballots of a voter are read in order, and the ones that break the
# rules are skipped: a voter votes once in a round at most, and in no round
# below one that it voted in, or passed to.

# a vote that counts: its round and its pick
type Voted is Data:
  Voted{round: Nat, pick: Types.Pick}

# what a reader knows after some ballots of a voter: the lowest round that
# the voter may still vote in, and its votes that count, newest first
type Seen is Data:
  Seen{floor: Nat, votes: List<&2, Voted>}

# the lowest round that a voter seen as m may vote in
def Seen.floor(m: Seen) -> Nat:
  match m:
    case Seen{fl, vs}:
      fl

# the votes of a voter seen as m
def Seen.votes(m: Seen) -> List<&2, Voted>:
  match m:
    case Seen{fl, vs}:
      vs

# what is known of a voter seen as m, after it casts x: a vote counts in a
# round that the voter may vote in, and the voter may not vote in that round
# again; a pass counts when it is to no lower round
def Seen.step(m: Seen, x: Types.Cast) -> Seen:
  match m x:
    case Seen{+fl, +vs} Types.Cast.Vote{+r, p, b}:
      Bool.pick(Seen, Nat.is_le(fl, r), Seen{1n+r, Voted{r, p} <> vs}, Seen{fl, vs})
    case Seen{+fl, +vs} Types.Cast.Pass{+r}:
      Bool.pick(Seen, Nat.is_le(fl, r), Seen{r, vs}, Seen{fl, vs})

# m after the next ballot x, when both are known
def Chain.seen.next(m: Maybe<&2, Seen>, x: Maybe<&2, Types.Cast>) -> Maybe<&2, Seen>:
  match m x:
    case Some{seen} Some{cast}:
      Some{Seen.step(seen, cast)}
    case _ _:
      None{}

# what the ballots bs tell of the voter v before its ballot of the number t:
# nothing while bs does not hold each ballot of v before it
def Chain.seen(+bs: List<&2, Ballot>, +v: String, t: Nat) -> Maybe<&2, Seen>:
  match t:
    case 0n:
      Some{Seen{0n, []}}
    case 1n++j:
      Chain.seen.next(Chain.seen(bs, v, j), Ballots.at(bs, v, j))

# m is known, and a vote of the round r counts after it
def Seen.takes(r: Nat, m: Maybe<&2, Seen>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Seen{fl, vs}}:
      Nat.is_le(fl, r)

# the cast m is the cast x
def Cast.is(x: Types.Cast, m: Maybe<&2, Types.Cast>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{y}:
      Coded.Cast.is_eq(y, x)

# some ballots, a voter and a round
type Roll is Data:
  Roll{ballots: List<&2, Ballot>, voter: String, round: Nat}

# the ballot b is a vote of the voter of g in the round of g that counts
# among the ballots of g
def Ballot.counts(g: Roll, b: Ballot) -> Bool:
  match g b:
    case Roll{+bs, +v, r} Ballot{w, +t, Types.Cast.Vote{+r2, p, basis}}:
      Shared.Bool.when(
        Bool,
        Bool.and(String.eq(w, v), Nat.is_eq(r2, r)),
        un => Shared.Bool.when(
          Bool,
          Seen.takes(r2, Chain.seen(bs, v, t)),
          u => Cast.is(Types.Cast.Vote{r2, p, basis}, Ballots.at(bs, v, t)),
          u => False{}
        ),
        un => False{}
      )
    case Roll{bs, v, r} Ballot{w, t, Types.Cast.Pass{r2}}:
      False{}

# the vote of the voter v in the round r that counts among bs, if any
def Vote.of(+bs: List<&2, Ballot>, v: String, r: Nat) -> Maybe<&2, Ballot>:
  Lists.List.pick(~Ballot, ~Roll, ~Ballot.counts, bs, Roll{bs, v, r})

# the ballot m is a vote for the pick p
def Vote.is_for(p: Types.Pick, m: Maybe<&2, Ballot>) -> Bool:
  match m:
    case Some{Ballot{v, t, Types.Cast.Vote{r, q, basis}}}:
      Coded.Pick.is_eq(q, p)
    case _:
      False{}

# some ballots, a round and a pick
type Tally is Data:
  Tally{ballots: List<&2, Ballot>, round: Nat, pick: Types.Pick}

# the node d voted for the pick of g in the round of g, and the vote counts
def Tally.voted(g: Tally, d: String) -> Bool:
  match g:
    case Tally{+bs, r, p}:
      Vote.is_for(p, Vote.of(bs, d, r))

# more than half of the nodes ds voted for the pick p in the round r, with
# votes that count
def Tally.most(+bs: List<&2, Ballot>, +ds: List<&2, String>, r: Nat, p: Types.Pick) -> Bool:
  Lists.Nat.most(
    List.length(&2, String, ds),
    Lists.List.count(~String, ~Tally, ~Tally.voted, ds, Tally{bs, r, p})
  )

# Sound votes
# -----------
# The vote of the node whose turn a round is, is the lead of the round. It
# is sound when it rests on promises of more than half of the nodes: each
# gave ballots after which it votes in no round below, and the lead is for
# the pick of the sound vote of the highest round among the votes that these
# nodes cast before (for any pick, if they cast no sound vote). Its own
# promise is its vote; the promises of the others are its basis. A vote of
# another node is sound when it is for the pick of the sound lead of its
# round. So the sound votes of a round are for one pick, and once more than
# half of the nodes cast a sound vote for a pick, every later sound vote is
# for it.

# what a reader knows of the lead of a round. Open: not enough yet. Void: it
# is not sound, and no vote of the round is. Sound: it is sound, for the pick
type Mind is Data:
  Mind.Open{}
  Mind.Void{}
  Mind.Sound{pick: Types.Pick}

# what the votes that a lead rests on leave it. Open: not known yet. Free:
# any pick. Bound: the pick, of the sound vote of the round
type Force is Data:
  Force.Open{}
  Force.Free{}
  Force.Bound{round: Nat, pick: Types.Pick}

# what a vote of the round r for the pick p leaves a lead, where m is what is
# known of the lead of the round r: it binds when it is sound
def Voted.force.at(+r: Nat, +p: Types.Pick, m: Maybe<&2, Mind>) -> Force:
  match m:
    case None{}:
      Force.Free{}
    case Some{Mind.Open{}}:
      Force.Open{}
    case Some{Mind.Void{}}:
      Force.Free{}
    case Some{Mind.Sound{q}}:
      Bool.pick(Force, Coded.Pick.is_eq(q, p), Force.Bound{r, p}, Force.Free{})

# what the vote x leaves a lead of the round after the rounds of ms, the
# leads of the rounds before it (a vote of no round of ms leaves it free)
def Voted.force(ms: List<&2, Mind>, x: Voted) -> Force:
  match x:
    case Voted{+r, +p}:
      Voted.force.at(r, p, List.get(&2, Mind, ms, r))

# what a and b leave together: the pick of the higher round
def Force.join(a: Force, b: Force) -> Force:
  match a b:
    case Force.Open{} _:
      Force.Open{}
    case Force.Free{} y:
      y
    case Force.Bound{r, p} Force.Open{}:
      Force.Open{}
    case Force.Bound{r, p} Force.Free{}:
      Force.Bound{r, p}
    case Force.Bound{+r, p} Force.Bound{+r2, p2}:
      Bool.pick(Force, Nat.is_lt(r, r2), Force.Bound{r2, p2}, Force.Bound{r, p})

# bend-lint: expect-begin bend-lint-rules/performance/list_index_loop@warning -- ms holds one lead for each round of one slot, and a slot takes a new round only when a lead fails: the list stays short
# what the votes vs leave a lead, with the leads ms of the rounds before it
def Votes.force(+ms: List<&2, Mind>, vs: List<&2, Voted>) -> Force:
  match vs:
    case Nil{}:
      Force.Free{}
    case Con{x, rest}:
      Force.join(Voted.force(ms, x), Votes.force(ms, rest))
# bend-lint: expect-end bend-lint-rules/performance/list_index_loop@warning

# what a node gave a lead. Open: not known yet. None: nothing. Held: a
# promise to vote in no round below, and the votes that it cast before
type Promise is Data:
  Promise.Open{}
  Promise.None{}
  Promise.Held{votes: List<&2, Voted>}

# the promise for the round r of a voter seen as m: it may vote in no round
# below r
def Promise.of(r: Nat, m: Maybe<&2, Seen>) -> Promise:
  match m:
    case None{}:
      Promise.Open{}
    case Some{Seen{fl, vs}}:
      Bool.pick(Promise, Nat.is_le(r, fl), Promise.Held{vs}, Promise.None{})

# the promise of the lead itself, seen as m before its vote
def Promise.own(m: Maybe<&2, Seen>) -> Promise:
  match m:
    case None{}:
      Promise.Open{}
    case Some{Seen{fl, vs}}:
      Promise.Held{vs}

# how many ballots of the voter d the basis names (none: no ballot)
def Basis.find(basis: List<&2, Types.Ref>, +d: String) -> Nat:
  match basis:
    case Nil{}:
      0n
    case Con{Types.Ref{v, n}, rest}:
      Shared.Bool.when(Nat, String.eq(v, d), u => n, u => Basis.find(rest, d))

# a lead: the ballots, its round, its voter, its number, its basis, and the
# leads of the rounds before
type Lead is Data:
  Lead{
    ballots: List<&2, Ballot>,
    round: Nat,
    voter: String,
    turn: Nat,
    basis: List<&2, Types.Ref>,
    minds: List<&2, Mind>
  }

# what the node d gave the lead g
def Promise.read(g: Lead, d: String) -> Promise:
  match g:
    case Lead{+bs, +r, +h, +t, +basis, ms}:
      +d = d
      Shared.Bool.when(
        Promise,
        String.eq(d, h),
        u => Promise.own(Chain.seen(bs, h, t)),
        u => Promise.of(r, Chain.seen(bs, d, Basis.find(basis, d)))
      )

# the promise m is held
def Promise.is_held(m: Promise) -> Bool:
  match m:
    case Promise.Held{vs}:
      True{}
    case _:
      False{}

# the node d gave the lead g a promise
def Promise.held(g: Lead, d: String) -> Bool:
  Promise.is_held(Promise.read(g, d))

# what the promise m leaves a lead, with the leads ms of the rounds before
def Promise.force(ms: List<&2, Mind>, m: Promise) -> Force:
  match m:
    case Promise.Open{}:
      Force.Open{}
    case Promise.None{}:
      Force.Free{}
    case Promise.Held{vs}:
      Votes.force(ms, vs)

# the leads of the rounds before the lead g
def Lead.minds(g: Lead) -> List<&2, Mind>:
  match g:
    case Lead{bs, r, h, t, basis, ms}:
      ms

# what the nodes ds leave the lead g: open while what one of them gave is
# not known
def Lead.force(+g: Lead, ds: List<&2, String>) -> Force:
  match ds:
    case Nil{}:
      Force.Free{}
    case Con{d, rest}:
      Force.join(Promise.force(Lead.minds(g), Promise.read(g, d)), Lead.force(g, rest))

# more than half of the nodes ds gave the lead g a promise
def Lead.most(+g: Lead, +ds: List<&2, String>) -> Bool:
  Lists.Nat.most(
    List.length(&2, String, ds),
    Lists.List.count(~String, ~Lead, ~Promise.held, ds, g)
  )

# what is known of a lead for the pick p, left f by the nodes, with promises
# of more than half of them or not (most)
def Lead.mind.of(+p: Types.Pick, f: Force, most: Bool) -> Mind:
  match f most:
    case Force.Open{} _:
      Mind.Open{}
    case Force.Free{} True{}:
      Mind.Sound{p}
    case Force.Bound{r, q} True{}:
      Bool.pick(Mind, Coded.Pick.is_eq(q, p), Mind.Sound{p}, Mind.Void{})
    case _ False{}:
      Mind.Void{}

# what is known of the lead g for the pick p, where the nodes ds decide
def Lead.mind.by(+p: Types.Pick, +g: Lead, +ds: List<&2, String>) -> Mind:
  Lead.mind.of(p, Lead.force(g, ds), Lead.most(g, ds))

# what is known of the lead of the round r among bs, where the nodes ds
# decide, h is the node whose turn it is, m its vote of the round, if any,
# and ms the leads of the rounds before
def Lead.mind.at(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +ms: List<&2, Mind>,
  +r: Nat,
  +h: String,
  m: Maybe<&2, Ballot>
) -> Mind:
  match m:
    case Some{Ballot{v, +t, Types.Cast.Vote{r2, +p, +basis}}}:
      Lead.mind.by(p, Lead{bs, r, h, t, basis, ms}, ds)
    case _:
      Mind.Open{}

# what is known of the lead of the round r of the slot k among bs, where the
# nodes ds decide and ms are the leads of the rounds before
def Lead.mind(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +r: Nat,
  +ms: List<&2, Mind>
) -> Mind:
  +h = Turn.of(ds, Nat.add(k, r))
  Lead.mind.at(bs, ds, ms, r, h, Vote.of(bs, h, r))

# what is known of the leads of the rounds below n of the slot k among bs,
# where the nodes ds decide
def Rounds.minds(+bs: List<&2, Ballot>, +ds: List<&2, String>, +k: Nat, n: Nat) -> List<&2, Mind>:
  match n:
    case 0n:
      []
    case 1n++j:
      +ms = Rounds.minds(bs, ds, k, j)
      List.append(&2, Mind, ms, [Lead.mind(bs, ds, k, j, ms)])

# Decided
# -------

# the pick that the round r decides, where m is what is known of its lead:
# more than half of the nodes ds cast a sound vote for it
def Round.won(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +r: Nat,
  m: Mind
) -> Maybe<&2, Types.Pick>:
  match m:
    case Mind.Sound{+p}:
      Shared.Maybe.when(Types.Pick, Tally.most(bs, ds, r, p), u => Some{p})
    case _:
      None{}

# the pick m, or else the one that rest gives
def Rounds.won.or(
  m: Maybe<&2, Types.Pick>,
  rest: Unit -> Maybe<&2, Types.Pick>
) -> Maybe<&2, Types.Pick>:
  match m:
    case Some{p}:
      Some{p}
    case None{}:
      rest(Unit{})

# the pick that the first of the rounds from r on decides, where ms is what
# is known of their leads
def Rounds.won(
  ms: List<&2, Mind>,
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +r: Nat
) -> Maybe<&2, Types.Pick>:
  match ms:
    case Nil{}:
      None{}
    case Con{m, rest}:
      Rounds.won.or(Round.won(bs, ds, r, m), u => Rounds.won(rest, bs, ds, 1n+r))

# the highest round of a ballot among bs
def Rounds.top(bs: List<&2, Ballot>) -> Nat:
  Lists.List.peak(~Ballot, ~Ballot.round, bs)

# the rounds that the ballots bs are of: one more than the highest
def Rounds.count(bs: List<&2, Ballot>) -> Nat:
  1n+Rounds.top(bs)

# the pick that the nodes ds decided for the slot k, of the ballots bs: the
# one that a round decides (all rounds decide the same)
def Slot.decided(+bs: List<&2, Ballot>, +ds: List<&2, String>, +k: Nat) -> Maybe<&2, Types.Pick>:
  Rounds.won(Rounds.minds(bs, ds, k, Rounds.count(bs)), bs, ds, 0n)

# the nodes os decided the pick pk in the round r, where m is what is known
# of its lead: the lead is sound for pk, and each of os voted for it
def Round.backs(
  +bs: List<&2, Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat,
  m: Mind
) -> Bool:
  match m:
    case Mind.Sound{q}:
      Shared.Bool.when(
        Bool,
        Coded.Pick.is_eq(q, pk),
        u => Shared.List.holds(~String, ~Tally, ~Tally.voted, os, Tally{bs, r, pk}),
        u => False{}
      )
    case _:
      False{}

# the nodes os decided the pick pk in one of the rounds from r on, where ms
# is what is known of their leads
def Rounds.back(
  ms: List<&2, Mind>,
  +bs: List<&2, Ballot>,
  +os: List<&2, String>,
  +pk: Types.Pick,
  +r: Nat
) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, rest}:
      List.any.if(u => Rounds.back(rest, bs, os, pk, 1n+r), Round.backs(bs, os, pk, r, m))

# the nodes os decided the pick pk for the slot k, of the ballots bs, where
# the nodes ds decide: in one round, each of os cast a sound vote for it
def Slot.backed(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +os: List<&2, String>,
  +pk: Types.Pick
) -> Bool:
  Rounds.back(Rounds.minds(bs, ds, k, Rounds.count(bs)), bs, os, pk, 0n)

# Casting
# -------
# What a node needs to cast its next ballot for a slot.

# how far the ballots of a voter are held: the number of the first one that
# is not, and what is known of the voter before it
type Reach is Data:
  Reach{turn: Nat, seen: Seen}

# how far the ballots of the voter v are held among bs, from the number t on,
# where m is what is known before it and x the ballot of the number t; at
# most fuel ballots further
def Chain.reach.go(
  fuel: Nat,
  +bs: List<&2, Ballot>,
  +v: String,
  +t: Nat,
  +m: Seen,
  x: Maybe<&2, Types.Cast>
) -> Reach:
  match fuel x:
    case 0n _:
      Reach{t, m}
    case 1n+f None{}:
      Reach{t, m}
    case 1n+f Some{cast}:
      Chain.reach.go(f, bs, v, 1n+t, Seen.step(m, cast), Ballots.at(bs, v, 1n+t))

# one more than the greatest number of a ballot among bs
def Turns.count(bs: List<&2, Ballot>) -> Nat:
  1n+Lists.List.peak(~Ballot, ~Ballot.turn, bs)

# how far the ballots of the voter v are held among bs
def Chain.reach(+bs: List<&2, Ballot>, +v: String) -> Reach:
  Chain.reach.go(Turns.count(bs), bs, v, 0n, Seen{0n, []}, Ballots.at(bs, v, 0n))

# rest, with the ballots of the node d as far as m, when d is another node
# than the lead (own is False), it cast some, and they promise the round r
def Basis.make.at(
  d: String,
  r: Nat,
  own: Bool,
  m: Reach,
  rest: List<&2, Types.Ref>
) -> List<&2, Types.Ref>:
  match own m:
    case True{} _:
      rest
    case False{} Reach{0n, m2}:
      rest
    case False{} Reach{1n+n, Seen{fl, vs}}:
      List.filter.put(Types.Ref, Types.Ref{d, 1n+n}, rest, Nat.is_le(r, fl))

# the basis that the node name can give for its lead of the round r: the
# ballots that it holds of each other node among ds that promise the round
def Basis.make(
  +bs: List<&2, Ballot>,
  +name: String,
  +r: Nat,
  ds: List<&2, String>
) -> List<&2, Types.Ref>:
  match ds:
    case Nil{}:
      []
    case Con{+d, rest}:
      Basis.make.at(d, r, String.eq(d, name), Chain.reach(bs, d), Basis.make(bs, name, r, rest))

# what a node may lead with: the number of its next ballot, the round, the
# basis, and what the basis leaves it
type Chance is Data:
  Chance{turn: Nat, round: Nat, basis: List<&2, Types.Ref>, force: Force}

# the chance of the lead g, where the nodes ds decide: when more than half
# of them gave it a promise
def Slot.chance.of(+g: Lead, +ds: List<&2, String>) -> Maybe<&2, Chance>:
  match g:
    case Lead{bs, r, h, t, basis, ms}:
      Shared.Maybe.when(Chance, Lead.most(g, ds), u => Some{Chance{t, r, basis, Lead.force(g, ds)}})

# the chance of the node name, whose next ballot is of the number t, to lead
# the round r of the slot k among bs, where the nodes ds decide: when the
# round is its turn
def Slot.chance.in(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  +t: Nat,
  +r: Nat
) -> Maybe<&2, Chance>:
  Shared.Maybe.when(
    Chance,
    String.eq(Turn.of(ds, Nat.add(k, r)), name),
    u => Slot.chance.of(
      Lead{bs, r, name, t, Basis.make(bs, name, r, ds), Rounds.minds(bs, ds, k, r)},
      ds
    )
  )

# the chance of the node name at the slot k among bs, where the nodes ds
# decide and m is how far its own ballots are held: in the highest round of
# a ballot, or the lowest round that it may vote in when that is above
def Slot.chance.at(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  m: Reach
) -> Maybe<&2, Chance>:
  match m:
    case Reach{t, Seen{fl, vs}}:
      Slot.chance.in(bs, ds, k, name, t, Nat.max(fl, Rounds.top(bs)))

# the chance of the node name to lead a round of the slot k among bs, where
# the nodes ds decide
def Slot.chance(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String
) -> Maybe<&2, Chance>:
  Slot.chance.at(bs, ds, k, name, Chain.reach(bs, name))

# rest, or the sound vote of the round r that m gives when a voter that may
# vote in no round below fl may vote in r, and rest gives none
def Minds.last.at(+fl: Nat, +r: Nat, rest: Maybe<&2, Voted>, m: Mind) -> Maybe<&2, Voted>:
  match rest m:
    case Some{x} _:
      Some{x}
    case None{} Mind.Sound{p}:
      Shared.Maybe.when(Voted, Nat.is_le(fl, r), u => Some{Voted{r, p}})
    case None{} _:
      None{}

# the sound lead of the highest round, from r on, that a voter may follow
# when it may vote in no round below fl, where ms is what is known of the
# leads from r on
def Minds.last(ms: List<&2, Mind>, +fl: Nat, +r: Nat) -> Maybe<&2, Voted>:
  match ms:
    case Nil{}:
      None{}
    case Con{m, rest}:
      Minds.last.at(fl, r, Minds.last(rest, fl, 1n+r), m)

# a ballot to cast: its number and what it casts
type Draft is Data:
  Draft{turn: Nat, cast: Types.Cast}

# the vote that the chance m binds a node to
def Slot.follow.bound(m: Maybe<&2, Chance>) -> Maybe<&2, Draft>:
  match m:
    case Some{Chance{t, r, basis, Force.Bound{r2, p}}}:
      Some{Draft{t, Types.Cast.Vote{r, p, basis}}}
    case _:
      None{}

# the vote of a node whose next ballot is of the number t: as the sound lead
# m, else as its chance c binds it
def Slot.follow.of(t: Nat, m: Maybe<&2, Voted>, c: Unit -> Maybe<&2, Chance>) -> Maybe<&2, Draft>:
  match m:
    case Some{Voted{r, p}}:
      Some{Draft{t, Types.Cast.Vote{r, p, []}}}
    case None{}:
      Slot.follow.bound(c(Unit{}))

# the vote that the node name casts next for the slot k among bs, where the
# nodes ds decide and m is how far its own ballots are held: as the sound
# lead of the highest round that it may still vote in, else as its own
# chance to lead binds it
def Slot.follow.at(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String,
  m: Reach
) -> Maybe<&2, Draft>:
  match m:
    case Reach{+t, Seen{+fl, +vs}}:
      Slot.follow.of(
        t,
        Minds.last(Rounds.minds(bs, ds, k, Rounds.count(bs)), fl, 0n),
        u => Slot.chance.at(bs, ds, k, name, Reach{t, Seen{fl, vs}})
      )

# the vote that the node name casts next for the slot k among bs, where the
# nodes ds decide, when it has one to follow
def Slot.follow(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String
) -> Maybe<&2, Draft>:
  Slot.follow.at(bs, ds, k, name, Chain.reach(bs, name))

# a voter and a round
type Call is Data:
  Call{voter: String, round: Nat}

# the voter of g cast the ballot b, of the round of g or of a round above
def Ballot.reaches(g: Call, b: Ballot) -> Bool:
  match g b:
    case Call{v, r} Ballot{w, t, x}:
      Shared.Bool.when(Bool, String.eq(w, v), u => Nat.is_le(r, Cast.round(x)), u => False{})

# bs holds a ballot of the voter h of the round r or of a round above: h
# came to the round
def Rounds.heard(bs: List<&2, Ballot>, h: String, r: Nat) -> Bool:
  Shared.List.some(~Ballot, ~Call, ~Ballot.reaches, bs, Call{h, r})

# the round top of the slot k is alive for the node name, where the nodes ds
# decide: it is the turn of name, or the node whose turn it is came to it
def Round.alive(
  bs: List<&2, Ballot>,
  ds: List<&2, String>,
  k: Nat,
  +name: String,
  +top: Nat
) -> Bool:
  +h = Turn.of(ds, Nat.add(k, top))
  Shared.Bool.when(Bool, String.eq(h, name), u => True{}, u => Rounds.heard(bs, h, top))

# the first round above r, among the n next ones, that is the turn of the
# node name at the slot k, where the nodes ds decide
def Rounds.mine(n: Nat, +ds: List<&2, String>, +k: Nat, +name: String, +r: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      Shared.Bool.when(
        Maybe<&2, Nat>,
        String.eq(Turn.of(ds, Nat.add(k, 1n+r)), name),
        u => Some{1n+r},
        u => Rounds.mine(m, ds, k, name, 1n+r)
      )

# the pass to the round m, if any, of the number t
def Slot.pass.to(t: Nat, m: Maybe<&2, Nat>) -> Maybe<&2, Draft>:
  match m:
    case None{}:
      None{}
    case Some{to}:
      Some{Draft{t, Types.Cast.Pass{to}}}

# the pass of a voter that may vote in no round below fl, whose next ballot
# is of the number t, where top is the highest round of a ballot for the
# slot. While top is alive: to top when the voter has not promised it (fl is
# below top), else none (it waits). Else: to own, its next round above top
def Slot.pass.of(
  t: Nat,
  fl: Nat,
  +top: Nat,
  alive: Bool,
  own: Unit -> Maybe<&2, Nat>
) -> Maybe<&2, Draft>:
  match alive:
    case True{}:
      Slot.pass.to(t, Shared.Maybe.when(Nat, Nat.is_lt(fl, top), u => Some{top}))
    case False{}:
      Slot.pass.to(t, own(Unit{}))

# the pass of a voter whose ballots are held as far as m
def Slot.pass.at(+top: Nat, alive: Bool, own: Unit -> Maybe<&2, Nat>, m: Reach) -> Maybe<&2, Draft>:
  match m:
    case Reach{t, Seen{fl, vs}}:
      Slot.pass.of(t, fl, top, alive, own)

# the pass that the node name casts next for the slot k of the ballots bs,
# where the nodes ds decide. It reads only the ballots, and a node passes
# once for the same ballots (rounds.bend: Slot.pass_once): while the highest
# round of a ballot is alive (it is the turn of the node, or the node whose
# turn it is came to it), the node promises it, and then waits; when it is
# not (the node whose turn it is cast no ballot there: it may be lost), the
# node calls its own next round, which the others then promise
def Slot.pass(
  +bs: List<&2, Ballot>,
  +ds: List<&2, String>,
  +k: Nat,
  +name: String
) -> Maybe<&2, Draft>:
  +top = Rounds.top(bs)
  Slot.pass.at(
    top,
    Round.alive(bs, ds, k, name, top),
    u => Rounds.mine(List.length(&2, String, ds), ds, k, name, top),
    Chain.reach(bs, name)
  )
