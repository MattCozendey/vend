import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ./judging.bend as Judging
import ./sealing.bend as Sealing
import ./stepping.bend as Stepping

# Rounds
# ------
# The decision of a height goes in rounds. In the round r the owner (h + r),
# in turn, proposes. In the first round it proposes freely. A node that waited
# too long passes to the next round: it casts no vote in the rounds below any
# more, and names its last vote at the height. In a later round the proposer
# needs the passes of a majority; it proposes the last vote of the highest
# round among them, if there is one, so a step that a round decided is the
# only one that a later round can decide.

# the round of the place w
def Where.round(w: Ledgers.Where) -> Nat:
  match w:
    case Ledgers.Where{c, h, r}:
      r

# what the node p did at the place w, in the cell m of its vote
def Cast.act.of(m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>) -> Maybe<&2, Ledgers.Act>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}}}}:
      Some{a}
    case x:
      None{}

# the vote of the node p at the place w, with the nodes whose passes allow
# it, if s holds it
def Cast.act(s: Basics.Node, w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Act>:
  Cast.act.of(Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.vote(w, p)))

# the nodes that the vote m names, if m is a vote
def Act.from(m: Maybe<&2, Ledgers.Act>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Act.Vote{v, from}}:
      from
    case x:
      []

# the nodes whose passes allow the vote of the node p at the place w, as the
# vote names them
def Cast.from(s: Basics.Node, w: Ledgers.Where, p: String) -> List<&2, String>:
  Act.from(Cast.act(s, w, p))

# the highest round, up to k, to which the node n passed at the height h of
# the line c (0: it passed to none)
def Round.mine(+n: String, +s: Basics.Node, +c: Ledgers.Chain, +h: U32, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+p):
      Shared.Bool.when(
        Nat,
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, 1n+p}, n)
        ),
        u => 1n+p,
        u => Round.mine(n, s, c, h, p)
      )

# the vote m of the round r, as a last vote, else what rest gives
def Last.or(
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Unit -> Maybe<&2, Ledgers.Last>
) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{v}:
      Some{Ledgers.Last{r, v}}
    case None{}:
      rest(Unit{})

# the last vote of the node n at the height h of the line c, in a round up to
# k, if it cast one
def Last.mine(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: U32,
  k: Nat
) -> Maybe<&2, Ledgers.Last>:
  match k:
    case 0n:
      Last.or(0n, Sealing.Cast.of(s, Ledgers.Where{c, h, 0n}, n), u => None{})
    case 1n+(+p):
      Last.or(1n+p, Sealing.Cast.of(s, Ledgers.Where{c, h, 1n+p}, n), u => Last.mine(n, s, c, h, p))

# the last vote of the node n at the height h of the line c, in a round below
# r, if it cast one
def Last.below(
  n: String,
  s: Basics.Node,
  c: Ledgers.Chain,
  h: U32,
  r: Nat
) -> Maybe<&2, Ledgers.Last>:
  match r:
    case 0n:
      None{}
    case 1n+p:
      Last.mine(n, s, c, h, p)

# the nodes of os whose pass to the place w the node s holds
def Passes.of(+s: Basics.Node, +w: Ledgers.Where, os: List<&2, String>) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{+o, r}:
      List.filter.put(
        String,
        o,
        Passes.of(s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), w, o)
        )
      )

# the last vote of the higher round of a and b
def Last.newer(a: Maybe<&2, Ledgers.Last>, b: Maybe<&2, Ledgers.Last>) -> Maybe<&2, Ledgers.Last>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{Ledgers.Last{+r1, v1}} Some{Ledgers.Last{+r2, v2}}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Last>,
        Nat.is_lt(r1, r2),
        u => Some{Ledgers.Last{r2, v2}},
        u => Some{Ledgers.Last{r1, v1}}
      )

# the last vote that a pass names, flattened
def Passed.last(m: Maybe<&2, Maybe<&2, Ledgers.Last>>) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{x}:
      x
    case None{}:
      None{}

# the last vote of the highest round that the passes of the nodes from to the
# place w name, if any names one
def Passes.last(
  +s: Basics.Node,
  +w: Ledgers.Where,
  from: List<&2, String>
) -> Maybe<&2, Ledgers.Last>:
  match from:
    case Nil{}:
      None{}
    case Con{o, r}:
      Last.newer(
        Passed.last(Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), w, o)),
        Passes.last(s, w, r)
      )

# the nodes from are a majority of the owners os
def Owners.major(os: List<&2, String>, +from: List<&2, String>) -> Bool:
  Nat.is_lt(
    List.length(&2, String, os),
    Nat.add(List.length(&2, String, from), List.length(&2, String, from))
  )

# the last vote m, if any, is for the step v
def Last.is(m: Maybe<&2, Ledgers.Last>, v: Ledgers.Vote) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Last{r, x}}:
      Ledgers.Vote.is_eq(x, v)

# the node s holds the pass to the place w of each of the nodes from
def Passed.all(+s: Basics.Node, +w: Ledgers.Where, from: List<&2, String>) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, r}:
      List.all.if(
        u => Passed.all(s, w, r),
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), w, o)
        )
      )

# the nodes from are some of the owners os, each once, in their order
def Owners.sub(os: List<&2, String>, from: List<&2, String>) -> Bool:
  match os from:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{f, fs}:
      False{}
    case Con{o, r} Nil{}:
      True{}
    case Con{o, +r} Con{+f, +fs}:
      Shared.Bool.when(Bool, String.eq(f, o), u => Owners.sub(r, fs), u => Owners.sub(r, f <> fs))

# the passes of the nodes from allow a vote for the step v at the place w of
# the owners os: in the first round, any step; later, the node holds the pass
# to w of each of them, they are owners and a majority, and v is the last vote
# of the highest round among them, if any
def Vote.allowed(
  +s: Basics.Node,
  +w: Ledgers.Where,
  +os: List<&2, String>,
  v: Ledgers.Vote,
  +from: List<&2, String>
) -> Bool:
  List.any.if(
    u => List.all.if(
      u2 => List.all.if(
        u3 => List.all.if(u4 => Last.is(Passes.last(s, w, from), v), Owners.major(os, from)),
        Owners.sub(os, from)
      ),
      Passed.all(s, w, from)
    ),
    Nat.is_eq(Where.round(w), 0n)
  )

# the plan of the proposer of a later round at the place w, once the nodes
# from that passed to it are known: none until they are a majority; then the
# last vote of the highest round among them, else what waits at the proposer
def Plan.later(
  s: Basics.Node,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Basics.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  +from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> Sealing.Plan:
  match m:
    case None{}:
      Shared.Bool.when(
        Sealing.Plan,
        Owners.major(os, from),
        u => Sealing.Plan.own(s, c, t, from),
        u => Sealing.Plan{[], None{}, []}
      )
    case Some{Ledgers.Last{r, v}}:
      Shared.Bool.when(
        Sealing.Plan,
        Owners.major(os, from),
        u => Sealing.Plan.copy(s, c, t, th, Some{v}, from),
        u => Sealing.Plan{[], None{}, []}
      )

# the plan of the proposer at the place w
def Plan.lead(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Basics.Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> Sealing.Plan:
  +from = Passes.of(s, w, os)
  Shared.Bool.when(
    Sealing.Plan,
    Nat.is_eq(Where.round(w), 0n),
    u => Sealing.Plan.own(s, c, t, []),
    u => Plan.later(s, c, w, t, th, os, from, Passes.last(s, w, from))
  )

# the plan of another owner at the place w, once what the proposer did there
# is known (m): the proposer's step, when its passes allow it
def Plan.follow(
  +s: Basics.Node,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Basics.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> Sealing.Plan:
  match m:
    case Some{Ledgers.Act.Vote{+v, +from}}:
      Shared.Bool.when(
        Sealing.Plan,
        Vote.allowed(s, w, os, v, from),
        u => Sealing.Plan.copy(s, c, t, th, Some{v}, from),
        u => Sealing.Plan{[], None{}, []}
      )
    case x:
      Sealing.Plan{[], None{}, []}

# what the node n casts for at the place w of the line c, at the tip t of the
# hash th, with the owners os, when it is turn's turn to propose
def Plan.of(
  n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Basics.Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> Sealing.Plan:
  match turn:
    case None{}:
      Sealing.Plan{[], None{}, []}
    case Some{+p}:
      Shared.Bool.when(
        Sealing.Plan,
        String.eq(p, n),
        u => Plan.lead(s, c, w, t, th, os),
        u => Plan.follow(s, c, w, t, th, os, Cast.act(s, w, p))
      )

# s with the node n's pass to the place w, when n is one of the owners os and
# did not pass to w: it names its last vote at the height, in a round below
def Pass.to(+n: String, +s: Basics.Node, +w: Ledgers.Where, os: List<&2, String>) -> Basics.Node:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Shared.Bool.when(
        Basics.Node,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        u => Sealing.Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(n, s, c, h, r)},
          Sealing.Seal.chain(s, Sealing.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        u => s
      )

# s, after the owner n joined the highest round of which it holds a ballot at
# the height h of the line c: a node casts in the round that the others reached
def Round.join(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> Basics.Node:
  +top = Sealing.Round.seen(s, c, h)
  Shared.Bool.when(
    Basics.Node,
    Nat.is_lt(Round.mine(n, s, c, h, top), top),
    u => Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    u => s
  )

# Node.cast in the round of the node n at the height next of the line c, at
# the tip t of the hash th
def Cast.round(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Basics.Tip
) -> Basics.Node:
  +os = Basics.Line.owners(s, t)
  +r = Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(n, s, c, w, t, th, os, Sealing.Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Shared.Bool.when(
    Basics.Node,
    Sealing.Cast.may(n, s, w, t, Sealing.Plan.asks(p)),
    u => Sealing.Cast.put(
      n,
      w,
      th,
      Sealing.Plan.asks(p),
      Sealing.Plan.from(p),
      Sealing.Plan.run(p),
      s
    ),
    u => s
  )

# Node.cast at the head h of the line c, whose tip is m
def Cast.at(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> Basics.Node:
  match h m:
    case Basics.Head{r, b, +next, th} Some{+t}:
      Cast.round(n, Round.join(n, s, c, next, Basics.Line.owners(s, t)), c, next, th, t)
    case x y:
      s

# Node.pass at the head h of the line c, whose tip is m
def Pass.at(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> Basics.Node:
  match h m:
    case Basics.Head{r, b, +next, th} Some{t}:
      k = Sealing.Round.seen(s, c, next)
      Pass.to(
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(n, s, c, next, k)},
        Basics.Line.owners(s, t)
      )
    case x y:
      s

# Node.pass once the head m of the line c is known
def Pass.head(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{+h}:
      Pass.at(n, s, c, h, Basics.Head.tip(s, h))

# Node.cast once the head m of the line c is known
def Cast.head(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{+h}:
      Cast.at(n, s, c, h, Basics.Head.tip(s, h))

# s, after the node n cast its ballot for the next step of the line c, in its
# round (Rounds): when it is its turn, the step that the rules of the round
# give it; else the step that the owner whose turn it is cast, when the rules
# allow it and the node's own run of it gives the same tip
def Node.cast(n: String, +s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  Cast.head(n, s, c, Basics.Node.head_of(s, c))

# the state m at the head h of the line c, after a step that ran qs, else s
def Advance.moved(
  s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  c: Ledgers.Chain,
  h: Basics.Head,
  qs: List<&2, Ledgers.Id>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{s3}:
      Sealing.State.moved(Basics.State.led(s, Basics.State.ledger(s3)), c, h, qs)

# s at the head of the next height of the line c, when the run m of the
# decided requests qs gives the tip that the ballots name (after): a node
# checks a step before it keeps it
def Advance.ran(
  +s: Basics.Node,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{Stepping.Run{s2, +t2, ns}}:
      Shared.Bool.when(
        Basics.Node,
        Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}),
        u => Advance.moved(
          s,
          Judging.State.put(s2, [Basics.Tip.words(t2)]),
          c,
          Basics.Head{r, b, U32.inc(next), Some{Basics.Tip.hash(t2)}},
          qs
        ),
        u => s
      )

# Node.advance once the step m that the owners decided at the head is known
def Advance.step(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  t: Basics.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> Basics.Node:
  match h m:
    case Basics.Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Basics.Node,
        Sealing.Root.same(before, th),
        u => Advance.ran(s, c, r, b, next, after, qs, Stepping.Step.run(s, c, t, qs)),
        u => s
      )
    case x y:
      s

# the step m, if any, else the step that rest gives
def Vote.first(
  m: Maybe<&2, Ledgers.Vote>,
  rest: Unit -> Maybe<&2, Ledgers.Vote>
) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{v}:
      Some{v}
    case None{}:
      rest(Unit{})

# the step that the owners os decided at the height h of the line c, in a
# round up to k, the highest first, if they did. The rounds of a height decide
# one step (Height.One), so the order does not matter
def Height.decide(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: U32,
  +os: List<&2, String>,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  match k:
    case 0n:
      Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, 0n}, os)
    case 1n+(+p):
      Vote.first(
        Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, 1n+p}, os),
        u => Height.decide(s, c, h, os, p)
      )

# that the rounds of the height h of the line c decide one step in s, for the
# owners os: a law of rounds, and a premise of the laws of agreement
def Height.One(s: Basics.Node, c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r1: Nat -> @r2: Nat -> @v1: Ledgers.Vote -> @v2: Ledgers.Vote -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, h, r1},
      os
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  } -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, h, r2},
      os
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  } -> {v1 == v2: Ledgers.Vote}

# The rules of rounds, for the ballots that s holds at the height h of the line
# c. A node that follows them makes them true of its own ballots; that every
# node follows them is the premise of Rounds.one.

# that the passes that a vote names allow it (Vote.allowed), for the owners os
def Rounds.Allow(s: Basics.Node, c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r: Nat -> @q: String -> @v: Ledgers.Vote -> {
    Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> {
    Vote.allowed(
      s,
      Ledgers.Where{c, h, r},
      os,
      v,
      Cast.from(s, Ledgers.Where{c, h, r}, q)
    )
      == True{}: Bool
  }

# that a pass names the last vote of its node below its round: a node that
# passed to a round casts no vote below it
def Rounds.Last(s: Basics.Node, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q: String -> @l: Maybe<
    &2,
    Ledgers.Last> -> {
    Ledgers.State.passed(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, h, r},
      q
    )
      == Some{l}: Maybe<&2, Maybe<&2, Ledgers.Last>>
  } -> {l == Last.below(q, s, c, h, r): Maybe<&2, Ledgers.Last>}

# that the votes of one round are for one step: one owner proposes, and the
# others copy
def Rounds.Same(s: Basics.Node, c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q1: String -> @q2: String -> @a: Ledgers.Vote -> @b: Ledgers.Vote -> {
    Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q1) == Some{a}: Maybe<&2, Ledgers.Vote>
  } -> {
    Sealing.Cast.of(s, Ledgers.Where{c, h, r}, q2) == Some{b}: Maybe<&2, Ledgers.Vote>
  } -> {a == b: Ledgers.Vote}

# the rounds of a height decide one step, when the ballots follow the rules
# of rounds: a later round can only decide what an earlier round decided
law Rounds.one:
  for ~s: Basics.Node
  for ~c: Ledgers.Chain
  for ~h: U32
  for ~os: List<&2, String>
  for ~fa: Rounds.Allow(s, c, h, os)
  for ~fb: Rounds.Last(s, c, h)
  for ~fc: Rounds.Same(s, c, h)
  Height.One(s, c, h, os)

# Node.advance at the head h of the line c, whose tip is m
def Advance.at(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{+t}:
      Advance.step(
        s,
        c,
        h,
        t,
        Height.decide(
          s,
          c,
          Sealing.Head.next(h),
          Basics.Line.owners(s, t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )

# Node.advance once the head m of the line c is known
def Advance.head(+s: Basics.Node, c: Ledgers.Chain, m: Maybe<&2, Basics.Head>) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{+h}:
      Advance.at(s, c, h, Basics.Head.tip(s, h))

# s, with its head of the line c moved over the next step, when a majority of
# the owners in its tip cast it and the node's own run of it gives the same
# tip
def Node.advance(+s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  Advance.head(s, c, Basics.Node.head_of(s, c))

# the heads a and b are at the same height, or one is none
def Heads.level(a: Maybe<&2, Basics.Head>, b: Maybe<&2, Basics.Head>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      U32.is_eq(Sealing.Head.next(x), Sealing.Head.next(y))
    case x y:
      True{}

# Node.advances once the head m of the line c is known
def Advances.at(
  f: Nat,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> Basics.Node:
  match f m:
    case 1n+p Some{+h}:
      +s1 = Advance.at(s, c, h, Basics.Head.tip(s, h))
      +m1 = Basics.Node.head_of(s1, c)
      Shared.Bool.when(
        Basics.Node,
        Heads.level(Some{h}, m1),
        u => s1,
        u => Advances.at(p, s1, c, m1)
      )
    case g x:
      s

# s, with its head of the line c moved over each step that is decided, f
# steps at most
def Node.advances(f: Nat, +s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  Advances.at(f, s, c, Basics.Node.head_of(s, c))

# s, after the node n moved its head of the line c over each step that is
# decided, cast its ballot for the next step, and moved its head again
def Step.head(n: String, s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  s1 = Node.advances(4294967295n, s, c)
  Node.advances(4294967295n, Node.cast(n, s1, c), c)

# s, after the node n did what it can on the line c
def Node.step(n: String, s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  Step.head(n, Sealing.Node.open(s, c), c)

# s, after the owner n passed to the next round of the next step of the line
# c, and did what it can there: the round took too long (the proposer may be
# away). Transport asks for this; the core has no clock
def Node.pass(+n: String, +s: Basics.Node, +c: Ledgers.Chain) -> Basics.Node:
  Node.step(n, Pass.head(n, s, c, Basics.Node.head_of(s, c)), c)

# s, after the node n took in the new request q of e
def Node.ask.new(n: String, +s: Basics.Node, +e: Basics.Envelope, +q: Basics.Ask) -> Basics.Node:
  +i = Basics.Envelope.of(e)
  c = Basics.Ask.chain(i, q)
  s1 = Sealing.Node.arrive(
    Basics.State.led(
      s,
      Ledgers.State.ask(
        ~Basics.Ask,
        ~Basics.Ask.is_eq,
        Basics.State.ledger(s),
        i,
        Basics.Envelope.time(e),
        q
      )
    ),
    i,
    q
  )
  Node.step(n, s1, c)

# Node.ask once the cell m of the request's ID is known
def Node.ask.at(
  n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Basics.Node:
  match m:
    case Some{x}:
      s
    case None{}:
      Node.ask.new(
        n,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
        e,
        q
      )

# s, after the node n took in the request q of e, cast its ballot when it owns
# its line, and moved its head when that decides the step. A request ID that s
# holds counts once: asked again, it changes nothing
def Node.ask(n: String, +s: Basics.Node, +e: Basics.Envelope, q: Basics.Ask) -> Basics.Node:
  Node.ask.at(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.ask(Basics.Envelope.of(e)))
  )

# s, once it holds each request among the cells cs whose slot was empty in the
# ledger old: a request that the node held does not arrive again
def Take.asks(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Basics.Node
) -> Basics.Node:
  match cs:
    case Nil{}:
      s
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, q}}, rest}:
      Take.asks(
        rest,
        old,
        Shared.Bool.when(
          Basics.Node,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          u => Sealing.Node.arrive(s, i, q),
          u => s
        )
      )
    case Con{c, rest}:
      Take.asks(rest, old, s)

# l with the requests and the data among the cells cs, each in the slot that
# its own content names (a request by its ID, data by its hash). A ballot, a
# cell that is not one entry, and the slot that the sender gave are not kept:
# what another node sent is read, not believed
def Take.clean(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  l: Ledgers.State(Basics.Ask)
) -> Ledgers.State(Basics.Ask):
  match cs:
    case Nil{}:
      l
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, rest}:
      Take.clean(rest, Ledgers.State.ask(~Basics.Ask, ~Basics.Ask.is_eq, l, i, t, q))
    case Con{Cells.One{Ledgers.Entry.Data{ws}}, rest}:
      Take.clean(rest, Ledgers.State.put_data(~Basics.Ask, ~Basics.Ask.is_eq, l, ws))
    case Con{c, rest}:
      Take.clean(rest, l)

# Node.consent once the line m of the request is known
def Consent.at(
  n: String,
  +s: Basics.Node,
  i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Basics.Node:
  match m:
    case None{}:
      s
    case Some{c}:
      Node.step(n, Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)), c)

# s, after a writer connected to the node n asked for the request i, which s
# holds already (it came from another node): the request counts once, and the
# node now casts for it as one that was asked at it
def Node.consent(n: String, +s: Basics.Node, +i: Ledgers.Id) -> Basics.Node:
  Consent.at(n, s, i, Basics.Node.chain_of(s, i))

# the hash of the node that the look l lacks, if it lacks one
def Look.lack(l: Trees.Look) -> Maybe<&2, Hashes.Hash>:
  match l:
    case Trees.Look.Missing{x}:
      Some{x}
    case Trees.Look.Found{v}:
      None{}
    case Trees.Look.Absent{}:
      None{}

# the hash of the node that a read of the key k of the tree whose root is h
# lacks in s, if it lacks one: what the node asks another node for. A node
# keeps the part of a store that it uses, and fetches the rest on demand
def Node.lacks(
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Hashes.Hash>:
  Look.lack(Basics.Node.look(s, h, k))

# l with the data m, if any
def Serve.put(
  m: Maybe<&2, List<&2, U32>>,
  l: Ledgers.State(Basics.Ask)
) -> Ledgers.State(Basics.Ask):
  match m:
    case None{}:
      l
    case Some{ws}:
      Ledgers.State.put_data(~Basics.Ask, ~Basics.Ask.is_eq, l, ws)

# the data that s holds under the hashes hs, as a ledger: what a node sends
# to a node that asks for them (Node.fetch)
def Node.serve(+s: Basics.Node, hs: List<&2, Hashes.Hash>) -> Ledgers.State(Basics.Ask):
  match hs:
    case Nil{}:
      Ledgers.State.empty(~Basics.Ask)
    case Con{h, r}:
      Serve.put(Ledgers.State.data(~Basics.Ask, Basics.State.ledger(s), h), Node.serve(s, r))

# what the ledger r lacks of s: what a sync from s to a holder of r sends
def Node.missing(s: Basics.Node, r: Ledgers.State(Basics.Ask)) -> Ledgers.State(Basics.Ask):
  Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), r)

# what a node reads of the ledger t that another node sent: each request and
# each data, in the slot that its own content names (Take.clean)
def Node.reads(t: Ledgers.State(Basics.Ask)) -> Ledgers.State(Basics.Ask):
  Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )

# the ballots among the cells cs
def Ballots.of(cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>) -> List<&2, Ledgers.Ballot>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, rest}:
      b <> Ballots.of(rest)
    case Con{c, rest}:
      Ballots.of(rest)

# what a holder of s keeps of t, which another node sent. It checks everything
# before it keeps it: a request and data go to the slot that their own content
# names (Take.clean; data is read only under its hash), in the slots where s
# holds nothing; a ballot is kept when its node's chain leads to it and its
# key signs it (a ballot that it cannot check yet comes again with the next
# sync). Nothing that s holds is lost or changed. Each new request waits on
# its line: the cost is what t brings, not what s holds
def Node.take(+s: Basics.Node, +t: Ledgers.State(Basics.Ask)) -> Basics.Node:
  +sent = Node.reads(t)
  Sealing.Sealed.take(
    Ballots.of(
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
      )
    ),
    Take.asks(
      Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent),
      Basics.State.ledger(s),
      Basics.State.led(s, Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent))
    )
  )

# s, after the node n did what it can on each line of cs
def Node.steps(+n: String, cs: List<&2, Ledgers.Chain>, s: Basics.Node) -> Basics.Node:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.steps(n, rest, Node.step(n, s, c))

# the line of the first of the waiting requests qs, then rest
def Lines.waiting(
  s: Basics.Node,
  qs: List<&2, Ledgers.Id>,
  +rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match qs:
    case Nil{}:
      rest
    case Con{i, r}:
      Maybe.default(
        &2,
        List<&2, Ledgers.Chain>,
        Maybe.bind(
          &2,
          Ledgers.Chain,
          List<&2, Ledgers.Chain>,
          Basics.Node.chain_of(s, i),
          c => Some{c <> rest}
        ),
        rest
      )

# the lines of the lists of waiting requests qss
def Lines.waits(+s: Basics.Node, qss: List<&2, List<&2, Ledgers.Id>>) -> List<&2, Ledgers.Chain>:
  match qss:
    case Nil{}:
      []
    case Con{qs, r}:
      Lines.waiting(s, qs, Lines.waits(s, r))

# the lines of the requests and the ballots among the cells cs, then rest
def Lines.new(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match cs:
    case Nil{}:
      rest
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, r}:
      Basics.Ask.chain(i, q) <> Lines.new(r, rest)
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, r}:
      Sealing.Where.line(Sealing.Ballot.at(b)) <> Lines.new(r, rest)
    case Con{c, r}:
      Lines.new(r, rest)

# the lines that a sync of t into s may move, each once: those of the new
# requests and ballots of t, and those with waiting requests (new data can let
# them run). So a sync costs about what it brings, not every line of the node
def Sync.lines(
  s: Basics.Node,
  +s1: Basics.Node,
  t: Ledgers.State(Basics.Ask)
) -> List<&2, Ledgers.Chain>:
  Tries.Trie.unique(
    ~Ledgers.Chain,
    ~Ledgers.Chain.key,
    Lines.new(
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
      ),
      Lines.waits(s1, Tries.Trie.values(List<&2, Ledgers.Id>, Basics.State.waiting(s1)))
    ),
    Tries.Trie.new(Unit)
  )
