import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ./basics.bend as Basics
import ./judging.bend as Judging
import ./reading.bend as Reading
import ./sealing.bend as Sealing
import ./stepping.bend as Stepping
import ./voting.bend as Voting

# The pure core of a Vend Node (README): what it holds, what it answers, and
# the laws about both. transport/spec.bend carries it over IO.
#
# A line is a store, or one of its branches. What a line holds is a tip: its
# content, a tree of what it holds now, and its log, a tree that only gains
# keys (the outcome of each request, each version by its number, the count of
# versions, the marks, and the owners of the next step). So the answer to a
# request, the newest version, a version by number, a mark and the owners are
# each one read of a tree: about log(size) nodes, each checked by its hash.
#
# A step takes a tip to the next one: it runs a batch of requests, in order
# (Step.run), and any node can run it again. The owners of a line cast ballots
# for steps (Ledgers); a node moves its head of a line only to a step that the
# owners in its tip decided (a majority of them, in one round), and that it
# ran itself with the same result (Node.advance). A node's ledger only grows,
# and its heads only move along steps, so what it answers stays.

# Laws
# ----
# What README says of a Vend Node's core, as laws. src/daemon/DESIGN.md lists
# the laws that are not stated yet. A law of the ledger that asks for the laws
# of a change's equality holds of a node's ledger by Ask.same.

# two requests are the same exactly when they are equal
law Ask.same:
  Shared.Eq.Laws(Basics.Ask, Basics.Ask.is_eq)

# the owners of a line are the nodes inside its owner group: its owners take
# an Own only when its owners are the nodes inside its group, in the store
# tree that it names (Own.tree)
law Own.takes_inside:
  for +s: Basics.Node
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +g: String
  for +at: Maybe<&2, Ledgers.Id>
  for +os: List<&2, String>
  for +h: Maybe<&2, Hashes.Hash>
  {Judging.Own.takes(s, r, l, g, at, os, h) == Some{True{}}: Maybe<&2, Bool>}
    -> {os == Judging.Group.nodes(s, Judging.Own.tree(s, l, at, h), g): List<&2, String>}

# the tip that the step m names, if any
def Vote.tip(m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Ledgers.Vote{before, qs, after}}:
      after
    case None{}:
      None{}

# the head x one height up, at the tip y
def Head.up(x: Basics.Head, y: Hashes.Hash) -> Basics.Head:
  match x:
    case Basics.Head{r, b, n, th}:
      Basics.Head{r, b, U32.inc(n), Some{y}}

# the head x after the step m (none: no step, or one that names no tip)
def Head.moved(x: Basics.Head, m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Basics.Head>:
  Maybe.bind(&2, Hashes.Hash, Basics.Head, Vote.tip(m), y => Some{Head.up(x, y)})

# the step that the owners in the tip of the head x decided next on the line
# c, in the round r, if they did
def Advance.in(
  +s: Basics.Node,
  c: Ledgers.Chain,
  +x: Basics.Head,
  r: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Basics.Tip,
    Ledgers.Vote,
    Basics.Head.tip(s, x),
    t => Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, Sealing.Head.next(x), r},
      Basics.Line.owners(s, t)
    )
  )

# the head of the line c after one decided step for each round of rs, the
# last first, from the head h, by the ledger of s alone (none: a step is not
# decided in its round). A law's measure: no node runs it
def Line.at(
  rs: List<&2, Nat>,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head
) -> Maybe<&2, Basics.Head>:
  match rs:
    case Nil{}:
      Some{h}
    case Con{r, rest}:
      Maybe.bind(
        &2,
        Basics.Head,
        Basics.Head,
        Line.at(rest, s, c, h),
        +x => Head.moved(x, Advance.in(s, c, x, r))
      )

# that the rounds of each height of the line c decide one step in s
def Line.One(s: Basics.Node, c: Ledgers.Chain) -> Type:
  @x: Basics.Head -> @t: Basics.Tip -> {
    Basics.Head.tip(s, x) == Some{t}: Maybe<&2, Basics.Tip>
  } -> Voting.Height.One(s, c, Sealing.Head.next(x), Basics.Line.owners(s, t))

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(k: Nat, s: Basics.Node, c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(p, s, c) & Line.One(s, c)

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a node does next: it takes in a request, or what another node sent,
# or it does a sync, or it keeps new bytes, or a writer connected to it asks
# for a request that it holds, or it passes to the next round on a line
type Deed is Data:
  Deed.Ask{envelope: Basics.Envelope, ask: Basics.Ask}
  Deed.Take{sent: Ledgers.State(Basics.Ask)}
  Deed.Sync{sent: Ledgers.State(Basics.Ask)}
  Deed.Keep{bytes: Texts.Bytes()}
  Deed.Consent{id: Ledgers.Id}
  Deed.Pass{line: Ledgers.Chain}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# s, after the node n did ev
def Node.does(+n: String, +s: Basics.Node, ev: Deed) -> Basics.Node:
  match ev:
    case Deed.Ask{+e, +q}:
      Reading.Adopt.at(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Basics.Envelope.of(e), q))
    case Deed.Take{t}:
      Voting.Node.take(s, t)
    case Deed.Sync{t}:
      Reading.Node.sync(n, s, t)
    case Deed.Keep{b}:
      Basics.Node.keep(s, b)
    case Deed.Consent{+i}:
      Reading.Adopt.maybe(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i))
    case Deed.Pass{+c}:
      Reading.Adopt.at(n, Voting.Node.pass(n, s, c), c)

# s, after the node n did each of evs, in order: any later state of the node
def Node.after(+n: String, evs: List<&2, Deed>, s: Basics.Node) -> Basics.Node:
  match evs:
    case Nil{}:
      s
    case Con{ev, rest}:
      Node.after(n, rest, Node.does(n, s, ev))

# that b holds, in the log of each line, each key that a holds there, other
# than the owners of the next step and the count of versions
def Node.Keeps(a: Basics.Node, b: Basics.Node) -> Type:
  @c: Ledgers.Chain -> @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k) == False{}: Bool
  } -> {
    Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Basics.Line.get(b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# a node only grows, whatever it does
law Node.after_grows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  {Reading.Node.grows(s, Node.after(n, evs, s)) == True{}: Bool}

# a log only gains keys: what the log of a line holds, it holds for good,
# whatever the node does next
law Node.after_keeps:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  Node.Keeps(s, Node.after(n, evs, s))

# the head m has a tip
def Head.held(m: Maybe<&2, Basics.Head>) -> Bool:
  match m:
    case Some{Basics.Head{r, b, n, Some{t}}}:
      True{}
    case x:
      False{}

# that the head of the line c in s is some decided steps from the head h0, by
# the ledger of s
def Line.Reach(s: Basics.Node, c: Ledgers.Chain, h0: Basics.Head) -> Type:
  Exists(
    List<&2, Nat>,
    rs => Exists(
      Basics.Head,
      h => {
        Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
      }
        & {Line.at(rs, s, c, h0) == Some{h}: Maybe<&2, Basics.Head>}
    )
  )

# that each head of a that is some decided steps from a head with a tip is,
# in b, some decided steps from it
def Node.On(a: Basics.Node, b: Basics.Node) -> Type:
  @c: Ledgers.Chain -> @h0: Basics.Head -> {
    Head.held(Some{h0}) == True{}: Bool
  } -> Line.Reach(a, c, h0) -> Line.Reach(b, c, h0)

# every head is on the decided chain: a head that has a tip moves only over
# decided steps, whatever the node does next
law Node.after_on:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  Node.On(s, Node.after(n, evs, s))

# an outcome is final: a request that a step took stays taken, as the same
# version number, and one that its owners refused stays refused
law Node.out_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +i: Ledgers.Id
  for +o: Basics.Out
  {Basics.Node.out(s, i) == Some{o}: Maybe<&2, Basics.Out>}
    -> {Basics.Node.out(Node.after(n, evs, s), i) == Some{o}: Maybe<&2, Basics.Out>}

# a version never changes: the request that made it and the root of its
# content stay
law Node.made_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +v: Ledgers.Id
  for +x: Basics.Version
  {Basics.Node.made(s, v) == Some{x}: Maybe<&2, Basics.Version>}
    -> {Basics.Node.made(Node.after(n, evs, s), v) == Some{x}: Maybe<&2, Basics.Version>}

# the history of a line only grows at its end: the version of a number stays
law Chain.version_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +k: U32
  for +x: Basics.Version
  {Basics.Chain.version(s, c, k) == Some{x}: Maybe<&2, Basics.Version>}
    -> {Basics.Chain.version(Node.after(n, evs, s), c, k) == Some{x}: Maybe<&2, Basics.Version>}

# a mark names its version for good
law Chain.mark_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +m: String
  for +v: Ledgers.Id
  {Basics.Chain.mark(s, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}
    -> {Basics.Chain.mark(Node.after(n, evs, s), c, m) == Some{v}: Maybe<&2, Ledgers.Id>}

# the first tip of a branch is for good: what the log of a store holds for a
# branch, it holds whatever the node does next, so a node that opens the
# branch later opens it at the same tip
law Chain.start_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +r: Ledgers.Id
  for +b: String
  for +v: List<&2, U32>
  {
    Basics.Line.get(
      s,
      Ledgers.Chain{r, None{}},
      Basics.Log.start(b)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
    -> {
      Basics.Line.get(
        Node.after(n, evs, s),
        Ledgers.Chain{r, None{}},
        Basics.Log.start(b)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }

# answers only move forward: a request that a node answers stays answered;
# Stale and Refused are final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Basics.Node
  for +e: Basics.Envelope
  for +q: Basics.Ask
  for +x: Reading.Answer
  {Reading.Node.answer(s, e, q) == Some{x}: Maybe<&2, Reading.Answer>}
    -> {Reading.Answer.follows(x, Reading.Node.answer(Node.after(n, evs, s), e, q)) == True{}: Bool}

# while a write that the writer w asked for waits on its line, the node has a
# draft of the resource for w (the newest of its pending writes, by
# Draft.newer)
law Node.draft_some:
  for +s: Basics.Node
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +q2: String
  for +t: String
  for +q: Basics.Ask
  for +c: Basics.Content
  {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Sealing.Wait.of(s, Basics.Line.chain(r, Some{b})),
      Ledgers.Id{w, q2}
    )
      == True{}: Bool
  }
    -> {
      Basics.Node.asked(
        s,
        Ledgers.Id{w, q2}
      )
        == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Basics.Ask>>
    }
    -> {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>}
    -> {Maybe.is_some(&2, Basics.Content, Reading.Node.draft(s, w, r, b, n)) == True{}: Bool}

# a write that the owners take: in the node that the verdict holds, the
# resource reads as the content of the write
law Judge.write_reads:
  for +s: Basics.Node
  for +n: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +c: Basics.Content
  for +h: Maybe<&2, Hashes.Hash>
  for +h2: Maybe<&2, Hashes.Hash>
  for +ds: List<&2, List<&2, U32>>
  for +s3: Basics.Node
  for +m: Maybe<&2, Ropes.Root>
  {
    Judging.Judge.write(
      s,
      n,
      base,
      c,
      h
    )
      == Some{Basics.Verdict.Taken{h2, ds, s3}}: Maybe<&2, Basics.Verdict>
  }
    -> {Judging.Content.find(s, n, c) == Some{m}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Basics.Res.root(s3, h2, n) == m: Maybe<&2, Ropes.Root>}

# the work m, if any, reads the key k as v
def Work.Reads(k: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Judging.Work>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Judging.Work{s2, h2, ns2}}:
      {Basics.Node.get(s2, h2, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# a move records a version equal to its target: each resource of the version
# to is, with the same content, in the tree that a move to it gives
law Move.reads:
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +to: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +v: List<&2, U32>
  {
    Basics.Node.get(
      s,
      Basics.Node.root_of(s, Some{to}),
      Basics.Key.res(n)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
    -> Work.Reads(Basics.Key.res(n), v, Judging.Move.work(s, c, to, h))

# a node copies only a vote that the rules of rounds allow: when it plans to
# cast for the vote of the proposer, the passes that the vote names allow it
law Plan.follow_allowed:
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +w: Ledgers.Where
  for +t: Basics.Tip
  for +th: Maybe<&2, Hashes.Hash>
  for +os: List<&2, String>
  for +v: Ledgers.Vote
  for +from: List<&2, String>
  {
    Maybe.is_some(
      &2,
      Stepping.Run,
      Sealing.Plan.run(Voting.Plan.follow(s, c, w, t, th, os, Some{Ledgers.Act.Vote{v, from}}))
    )
      == True{}: Bool
  }
    -> {Voting.Vote.allowed(s, w, os, v, from) == True{}: Bool}

# the log of the run m, if any, holds an outcome of the request i
def Run.Outs(m: Maybe<&2, Stepping.Run>, i: Ledgers.Id) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Stepping.Run{s, t, ns}}:
      {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Basics.Node.get(s, Basics.Tip.log(t), Basics.Log.out(i))
        )
          == True{}: Bool
      }

# a request waits until its line gives it an outcome. A step gives each of
# its requests an outcome
law Step.run_outs:
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +t: Basics.Tip
  for +qs: List<&2, Ledgers.Id>
  for +i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool}
    -> Run.Outs(Stepping.Step.run(s, c, t, qs), i)

# and a head that moves over a step takes only the requests of the step off
# the requests that wait (State.moved, the one place that takes any off)
law Wait.left_keeps:
  for +ws: List<&2, Ledgers.Id>
  for +done: Tries.Trie<Unit>
  for +i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ws, i) == True{}: Bool}
    -> {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool}
    -> {
      List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.left(ws, done), i) == True{}: Bool
    }

# a merge turns Written once each clashing resource is resolved: a resolve
# gives the resource its content, and shuts its clash (a clash whose key holds
# no request is not open: Clash.shut)
law Resolve.reads:
  for +s: Basics.Node
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Work.Reads(Basics.Key.res(n), Basics.Res.code(m), Judging.Resolve.work(s, h, n, m))

law Resolve.shuts:
  for +s: Basics.Node
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Work.Reads(Basics.Key.clash(n), [], Judging.Resolve.work(s, h, n, m))

law Clash.shut:
  for +s: Basics.Node
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +f: Ledgers.Id
  {Basics.Node.get(s, h, Basics.Key.clash(n)) == Some{[]}: Maybe<&2, List<&2, U32>>}
    -> {Judging.Clash.open(s, h, n, f) == False{}: Bool}

# a merge of whole trees keeps what the merge of each resource takes: when the
# merge of the resource n takes the root x (Pick.merge_theirs, Pick.merge_ours:
# a change that only one side made), the tree that the merge gives holds n
# with x
law Merge.keeps:
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +from: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  for +x: Maybe<&2, Ropes.Root>
  {
    List.contains(
      ~Resources.Name,
      ~Resources.Name.is_eq,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      n
    )
      == True{}: Bool
  }
    -> {
      Basics.Res.find(
        s,
        Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
        n
      )
        == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>
    }
    -> {Basics.Res.find(s, h, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {
      Basics.Res.find(
        s,
        Basics.Node.root_of(s, Some{from}),
        n
      )
        == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>
    }
    -> {
      Judging.Pick.merge(
        Formats.Format.of(Resources.Name.path(n)),
        s,
        b,
        o,
        t
      )
        == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
    }
    -> Work.Reads(Basics.Key.res(n), Basics.Res.code(x), Judging.Merge.work(s, c, from, h))

# a merge keeps, for each resource, a change that only one side made: when
# ours is the base, it keeps theirs
law Pick.merge_theirs:
  for f: Formats.Format
  for s: Basics.Node
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Basics.Roots.same(o, b) == True{}: Bool}
    -> {Judging.Pick.merge(f, s, b, o, t) == Some{Judging.Pick.Take{t}}: Maybe<&2, Judging.Pick>}

# and when theirs is the base, it keeps ours
law Pick.merge_ours:
  for f: Formats.Format
  for s: Basics.Node
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Basics.Roots.same(o, b) == False{}: Bool}
    -> {Basics.Roots.same(t, b) == True{}: Bool}
    -> {Judging.Pick.merge(f, s, b, o, t) == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>}

# a node keeps only ballots that it checked: a ballot that it accepts is the
# next of its node's chain in its store, and the key of that chain signs it
law Seal.accept_fits:
  for +s: Basics.Node
  for +b: Ledgers.Ballot
  for +c: Basics.Keychain
  for +s2: Basics.Node
  {
    Sealing.Seal.chain(
      s,
      Sealing.Ballot.store(b),
      Sealing.Ballot.node(b)
    )
      == Some{c}: Maybe<&2, Basics.Keychain>
  }
    -> {Sealing.Seal.accept(s, b) == Some{s2}: Maybe<&2, Basics.Node>}
    -> {Sealing.Seal.fits(c, b) == True{}: Bool}

# a ballot that a node seals with the secret of its chain's key fits the chain.
# (That no other node can make one is the assumption of Seals: a hash has no
# known second input.)
law Seal.fits_own:
  for +seed: Hashes.Hash
  for +x: Ledgers.Signed
  for +last: Maybe<&2, Ledgers.Where>
  for +k: Hashes.Hash
  for +n: U32
  for +f: Hashes.Hash
  {
    Sealing.Seal.fits(
      Basics.Keychain{n, last, Seals.Seal.public(seed), f},
      Ledgers.Ballot.make(seed, x, last, k)
    )
      == True{}: Bool
  }

# a majority decides, in sequence: a head moves only over a step that the
# owners in its tip decided next, in some round
law Node.advance_at:
  for +s: Basics.Node
  for +c: Ledgers.Chain
  for +h: Basics.Head
  {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>}
    -> {
      Voting.Heads.level(
        Some{h},
        Basics.Node.head_of(Voting.Node.advance(s, c), c)
      )
        == False{}: Bool
    }
    -> Exists(
      Nat,
      q => {
        Line.at(
          [q],
          s,
          c,
          h
        )
          == Basics.Node.head_of(Voting.Node.advance(s, c), c): Maybe<&2, Basics.Head>
      }
    )

# the decided steps of a line stay as a node grows: a head that is some
# decided steps from a head h is so in any node that keeps every cell
law Line.at_grows:
  for +rs: List<&2, Nat>
  for +a: Basics.Node
  for +u: Basics.Node
  for +c: Ledgers.Chain
  for +h: Basics.Head
  for +x: Basics.Head
  {Reading.Node.grows(a, u) == True{}: Bool}
    -> {Line.at(rs, a, c, h) == Some{x}: Maybe<&2, Basics.Head>}
    -> {Line.at(rs, u, c, h) == Some{x}: Maybe<&2, Basics.Head>}

# so two nodes whose ledgers do not clash (one node u keeps every cell of
# both, and the rounds of each height decide one step in it), the same number
# of decided steps from the same head of a line, are at the same head,
# whatever the round of each step: one history
law Line.at_agrees:
  for +rs1: List<&2, Nat>
  for +rs2: List<&2, Nat>
  for +a: Basics.Node
  for +b: Basics.Node
  for +u: Basics.Node
  for +c: Ledgers.Chain
  for +h: Basics.Head
  for +x: Basics.Head
  for +y: Basics.Head
  {Reading.Node.grows(a, u) == True{}: Bool}
    -> {Reading.Node.grows(b, u) == True{}: Bool}
    -> Line.Ones(List.length(&2, Nat, rs1), u, c)
    -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
    -> {Line.at(rs1, a, c, h) == Some{x}: Maybe<&2, Basics.Head>}
    -> {Line.at(rs2, b, c, h) == Some{y}: Maybe<&2, Basics.Head>}
    -> {x == y: Basics.Head}

# a node fetches on demand: a node b that lacks the data of the hash h holds
# it after it takes in what a node a that holds it serves
law Node.fetch:
  for +a: Basics.Node
  for +b: Basics.Node
  for +h: Hashes.Hash
  for +ws: List<&2, U32>
  {Ledgers.State.data(~Basics.Ask, Basics.State.ledger(a), h) == Some{ws}: Maybe<&2, List<&2, U32>>}
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(b),
        Ledgers.Slot.data(h)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      Ledgers.State.data(
        ~Basics.Ask,
        Basics.State.ledger(Voting.Node.take(b, Voting.Node.serve(a, [h]))),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }

# every part is kept by enough nodes: a node that casts for a step keeps each
# new part of the step (what its own run of the step put: the node of the run
# is s2), so a majority of the owners holds each part of a decided step; and a
# node only grows (Node.after_grows)
law Cast.put_keeps:
  for +n: String
  for +w: Ledgers.Where
  for +th: Maybe<&2, Hashes.Hash>
  for +qs: List<&2, Ledgers.Id>
  for +from: List<&2, String>
  for +s2: Basics.Node
  for +t2: Basics.Tip
  for +ns: List<&2, List<&2, U32>>
  for +s: Basics.Node
  for +s3: Basics.Node
  {Judging.State.put(s2, [Basics.Tip.words(t2)]) == Some{s3}: Maybe<&2, Basics.Node>}
    -> {
      Reading.Node.grows(
        s2,
        Sealing.Cast.put(n, w, th, qs, from, Some{Stepping.Run{s2, t2, ns}}, s)
      )
        == True{}: Bool
    }

# and it holds the tip that it casts for
law Cast.put_tip:
  for +n: String
  for +w: Ledgers.Where
  for +th: Maybe<&2, Hashes.Hash>
  for +qs: List<&2, Ledgers.Id>
  for +from: List<&2, String>
  for +s2: Basics.Node
  for +t2: Basics.Tip
  for +ns: List<&2, List<&2, U32>>
  for +s: Basics.Node
  for +s3: Basics.Node
  {Judging.State.put(s2, [Basics.Tip.words(t2)]) == Some{s3}: Maybe<&2, Basics.Node>}
    -> {
      Basics.Tip.at(
        Sealing.Cast.put(n, w, th, qs, from, Some{Stepping.Run{s2, t2, ns}}, s),
        Basics.Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Basics.Tip>
    }

# a node holds what it takes in: an entry that it reads of what was sent, in
# a slot that it lacks, it then holds
law Node.take_holds:
  for +s: Basics.Node
  for +t: Ledgers.State(Basics.Ask)
  for +k: List<&2, Bool>
  for +e: Ledgers.Entry<Basics.Ask>
  {
    Ledgers.State.get(
      ~Basics.Ask,
      Voting.Node.reads(t),
      k
    )
      == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(s),
        k
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(Voting.Node.take(s, t)),
        k
      )
        == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }

# a pending write goes with its writer to another node: a request that a node
# takes in waits on its line there, so the node has a draft for its writer
# (Node.draft_some) and the writer's read shows it (Node.read_draft)
law Node.take_waits:
  for +s: Basics.Node
  for +t: Ledgers.State(Basics.Ask)
  for +i: Ledgers.Id
  for +time: String
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +ch: Basics.Change
  {
    Ledgers.State.get(
      ~Basics.Ask,
      Voting.Node.reads(t),
      Ledgers.Slot.ask(i)
    )
      == Some{
        Cells.One{Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}}
      }: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(s),
        Ledgers.Slot.ask(i)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Sealing.Wait.of(Voting.Node.take(s, t), Basics.Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }

# writers are told only about changes to what their work uses: each change
# that Node.affects gives for a branch holds (Touch.holds): another line made
# it, the branch lacks it, and it wrote a resource that a resource of the
# branch is, or uses through its imports, at any depth
law Node.affects_used:
  for +s: Basics.Node
  for +b: Reading.Branch
  {
    Shared.List.holds(
      ~Reading.Touch,
      ~Reading.Seen,
      ~Reading.Touch.holds,
      Reading.Node.affects(s, b),
      Reading.Seen.of(s, b)
    )
      == True{}: Bool
  }

# a writer reads its own pending write: at the head of a branch, its read is
# the bytes of its draft, not what the branch holds
law Node.read_draft:
  for +s: Basics.Node
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +c: Basics.Content
  {Reading.Node.draft(s, w, r, b, n) == Some{c}: Maybe<&2, Basics.Content>}
    -> {
      Reading.Node.read(
        s,
        w,
        n,
        Basics.Point.Head{r, b}
      )
        == Basics.Root.bytes(s, Judging.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }

# a change counts once on a node, however often it is asked: a node that took
# a request in changes nothing when its ID is asked again (across nodes: a
# node takes a request that it holds no second time, Node.take, and a step
# skips a request that its log holds, Step.fresh)
law Node.ask_once:
  for +n: String
  for +m: String
  for +s: Basics.Node
  for +e: Basics.Envelope
  for +q: Basics.Ask
  for +e2: Basics.Envelope
  for +q2: Basics.Ask
  {Basics.Envelope.of(e2) == Basics.Envelope.of(e): Ledgers.Id}
    -> {
      Voting.Node.ask(
        m,
        Voting.Node.ask(n, s, e, q),
        e2,
        q2
      )
        == Voting.Node.ask(n, s, e, q): Basics.Node
    }
