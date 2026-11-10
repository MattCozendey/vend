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
import ./stepping.bend as Stepping
import ../replica/impl.bend as Replicas

# The pure core of a Vend Node (README): what it holds, what it answers, and
# the laws about both. transport/spec.bend carries it over IO.
#
# A line is a store, or one of its branches. What a line holds is a tip: its
# content, a tree of what it holds now; its log, a tree that only gains keys
# (the outcome of each request, each version by its number, the marks); the
# count of its versions; and the owners of its next step. So the count and the
# owners are a read of the tip, and the answer to a request, a version by
# number and a mark are each one read of a tree: about log(size) nodes, each
# checked by its hash.
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
  for +s: Replicas.Node<Basics.Ask>
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
def Head.up(x: Replicas.Head, y: Hashes.Hash) -> Replicas.Head:
  match x:
    case Replicas.Head{r, b, n, th}:
      Replicas.Head{r, b, U32.inc(n), Some{y}}

# the head x after the step m (none: no step, or one that names no tip)
def Head.moved(x: Replicas.Head, m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Replicas.Head>:
  Maybe.bind(&2, Hashes.Hash, Replicas.Head, Vote.tip(m), y => Some{Head.up(x, y)})

# the step that the owners in the tip of the head x decided next on the line
# c, in the round r, if they did
def Advance.in(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +x: Replicas.Head,
  r: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Ledgers.Vote,
    Replicas.Head.tip(~Basics.Ask.machine(), s, x),
    t => Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(x), r},
      Replicas.Tip.owners(t)
    )
  )

# the head of the line c after one decided step for each round of rs, the
# last first, from the head h, by the ledger of s alone (none: a step is not
# decided in its round). A law's measure: no node runs it
def Line.at(
  rs: List<&2, Nat>,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head
) -> Maybe<&2, Replicas.Head>:
  match rs:
    case Nil{}:
      Some{h}
    case Con{r, rest}:
      Maybe.bind(
        &2,
        Replicas.Head,
        Replicas.Head,
        Line.at(rest, s, c, h),
        +x => Head.moved(x, Advance.in(s, c, x, r))
      )

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a node does next: it takes in a request, or what another node sent,
# or it does a sync, or it keeps new bytes, or a writer connected to it asks
# for a request that it holds, or it passes to the next round on a line
type Deed is Data:
  Deed.Ask{envelope: Replicas.Envelope, ask: Basics.Ask}
  Deed.Take{sent: Ledgers.State(Basics.Ask)}
  Deed.Sync{sent: Ledgers.State(Basics.Ask)}
  Deed.Keep{bytes: Texts.Bytes()}
  Deed.Consent{id: Ledgers.Id}
  Deed.Pass{line: Ledgers.Chain}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# s, after the node n did ev
def Node.does(+n: String, +s: Replicas.Node<Basics.Ask>, ev: Deed) -> Replicas.Node<Basics.Ask>:
  match ev:
    case Deed.Ask{+e, +q}:
      Reading.Adopt.at(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
    case Deed.Take{t}:
      Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
    case Deed.Sync{t}:
      Reading.Node.sync(n, s, t)
    case Deed.Keep{b}:
      Basics.Node.keep(s, b)
    case Deed.Consent{+i}:
      Reading.Adopt.maybe(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
    case Deed.Pass{+c}:
      Reading.Adopt.at(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)

# s, after the node n did each of evs, in order: any later state of the node
def Node.after(+n: String, evs: List<&2, Deed>, s: Replicas.Node<Basics.Ask>) -> Replicas.Node<Basics.Ask>:
  match evs:
    case Nil{}:
      s
    case Con{ev, rest}:
      Node.after(n, rest, Node.does(n, s, ev))

# that b holds, in the log of each line, each key that a holds there
def Node.Keeps(a: Replicas.Node<Basics.Ask>, b: Replicas.Node<Basics.Ask>) -> Type:
  @c: Ledgers.Chain -> @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Line.get(~Basics.Ask.machine(), b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# a node only grows, whatever it does
law Node.after_grows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  {Reading.Node.grows(s, Node.after(n, evs, s)) == True{}: Bool}

# a log only gains keys: what the log of a line holds, it holds for good,
# whatever the node does next
law Node.after_keeps:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  Node.Keeps(s, Node.after(n, evs, s))

# the head m has a tip
def Head.held(m: Maybe<&2, Replicas.Head>) -> Bool:
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      True{}
    case x:
      False{}

# that the head of the line c in s is some decided steps from the head h0, by
# the ledger of s
def Line.Reach(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h0: Replicas.Head) -> Type:
  Exists(
    List<&2, Nat>,
    rs => Exists(
      Replicas.Head,
      h => {
        Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
      }
        & {Line.at(rs, s, c, h0) == Some{h}: Maybe<&2, Replicas.Head>}
    )
  )

# that each head of a that is some decided steps from a head with a tip is,
# in b, some decided steps from it
def Node.On(a: Replicas.Node<Basics.Ask>, b: Replicas.Node<Basics.Ask>) -> Type:
  @c: Ledgers.Chain -> @h0: Replicas.Head -> {
    Head.held(Some{h0}) == True{}: Bool
  } -> Line.Reach(a, c, h0) -> Line.Reach(b, c, h0)

# every head is on the decided chain: a head that has a tip moves only over
# decided steps, whatever the node does next
law Node.after_on:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  Node.On(s, Node.after(n, evs, s))

# an outcome is final: a request that a step took stays taken, as the same
# version number, and one that its owners refused stays refused
law Node.out_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +i: Ledgers.Id
  for +o: Replicas.Out
  {Basics.Node.out(s, i) == Some{o}: Maybe<&2, Replicas.Out>}
    -> {Basics.Node.out(Node.after(n, evs, s), i) == Some{o}: Maybe<&2, Replicas.Out>}

# a version never changes: the request that made it and the root of its
# content stay
law Node.made_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +v: Ledgers.Id
  for +x: Replicas.Version
  {Basics.Node.made(s, v) == Some{x}: Maybe<&2, Replicas.Version>}
    -> {Basics.Node.made(Node.after(n, evs, s), v) == Some{x}: Maybe<&2, Replicas.Version>}

# the history of a line only grows at its end: the version of a number stays
law Chain.version_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +k: U32
  for +x: Replicas.Version
  {Replicas.Chain.version(~Basics.Ask.machine(), s, c, k) == Some{x}: Maybe<&2, Replicas.Version>}
    -> {Replicas.Chain.version(~Basics.Ask.machine(), Node.after(n, evs, s), c, k) == Some{x}: Maybe<&2, Replicas.Version>}

# a mark names its version for good
law Chain.mark_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +m: String
  for +v: Ledgers.Id
  {Replicas.Chain.mark(~Basics.Ask.machine(), s, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}
    -> {Replicas.Chain.mark(~Basics.Ask.machine(), Node.after(n, evs, s), c, m) == Some{v}: Maybe<&2, Ledgers.Id>}

# the first tip of a branch is for good: what the log of a store holds for a
# branch, it holds whatever the node does next, so a node that opens the
# branch later opens it at the same tip
law Chain.start_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +r: Ledgers.Id
  for +b: String
  for +v: List<&2, U32>
  {
    Replicas.Line.get(~Basics.Ask.machine(), 
      s,
      Ledgers.Chain{r, None{}},
      Replicas.Log.start(b)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
    -> {
      Replicas.Line.get(~Basics.Ask.machine(), 
        Node.after(n, evs, s),
        Ledgers.Chain{r, None{}},
        Replicas.Log.start(b)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }

# answers only move forward: a request that a node answers stays answered;
# Stale and Refused are final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: Replicas.Node<Basics.Ask>
  for +e: Replicas.Envelope
  for +q: Basics.Ask
  for +x: Reading.Answer
  {Reading.Node.answer(s, e, q) == Some{x}: Maybe<&2, Reading.Answer>}
    -> {Reading.Answer.follows(x, Reading.Node.answer(Node.after(n, evs, s), e, q)) == True{}: Bool}

# while a write that the writer w asked for waits on its line, the node has a
# draft of the resource for w (the newest of its pending writes, by
# Draft.newer)
law Node.draft_some:
  for +s: Replicas.Node<Basics.Ask>
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
      Replicas.Wait.of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      Ledgers.Id{w, q2}
    )
      == True{}: Bool
  }
    -> {
      Replicas.Node.asked(~Basics.Ask.machine(), 
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
  for +s: Replicas.Node<Basics.Ask>
  for +n: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +c: Basics.Content
  for +h: Maybe<&2, Hashes.Hash>
  for +h2: Maybe<&2, Hashes.Hash>
  for +s3: Replicas.Node<Basics.Ask>
  for +m: Maybe<&2, Ropes.Root>
  {
    Judging.Judge.write(
      s,
      n,
      base,
      c,
      h
    )
      == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
  }
    -> {Judging.Content.find(s, n, c) == Some{m}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Basics.Res.root(s3, h2, n) == m: Maybe<&2, Ropes.Root>}

# the work m, if any, reads the key k as v
def Work.Reads(k: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Replicas.Work<Basics.Ask>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Replicas.Work{s2, h2}}:
      {Replicas.Node.get(~Basics.Ask.machine(), s2, h2, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# a move records a version equal to its target: each resource of the version
# to is, with the same content, in the tree that a move to it gives
law Move.reads:
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +to: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +v: List<&2, U32>
  {
    Replicas.Node.get(~Basics.Ask.machine(), 
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
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +w: Ledgers.Where
  for +t: Replicas.Tip
  for +th: Maybe<&2, Hashes.Hash>
  for +os: List<&2, String>
  for +v: Ledgers.Vote
  for +from: List<&2, String>
  {
    Maybe.is_some(
      &2,
      Replicas.Run<Basics.Ask>,
      Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.follow(~Stepping.Ask.kernel(), s, c, w, t, th, os, Some{Ledgers.Act.Vote{v, from}}))
    )
      == True{}: Bool
  }
    -> {Replicas.Vote.allowed(~Basics.Ask.machine(), s, w, os, v, from) == True{}: Bool}

# the log of the run m, if any, holds an outcome of the request i
def Run.Outs(m: Maybe<&2, Replicas.Run<Basics.Ask>>, i: Ledgers.Id) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Replicas.Run{s, t}}:
      {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), Replicas.Log.out(i))
        )
          == True{}: Bool
      }

# a request waits until its line gives it an outcome. A step gives each of
# its requests an outcome
law Step.run_outs:
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +t: Replicas.Tip
  for +qs: List<&2, Ledgers.Id>
  for +i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool}
    -> Run.Outs(Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs), i)

# and a head that moves over a step takes only the requests of the step off
# the requests that wait (State.moved, the one place that takes any off)
law Wait.left_keeps:
  for +ws: List<&2, Ledgers.Id>
  for +done: Tries.Trie<Unit>
  for +i: Ledgers.Id
  {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ws, i) == True{}: Bool}
    -> {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool}
    -> {
      List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.left(ws, done), i) == True{}: Bool
    }

# a merge turns Written once each clashing resource is resolved: a resolve
# gives the resource its content, and shuts its clash (a clash whose key holds
# no request is not open: Clash.shut)
law Resolve.reads:
  for +s: Replicas.Node<Basics.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Work.Reads(Basics.Key.res(n), Basics.Res.code(m), Judging.Resolve.work(s, h, n, m))

law Resolve.shuts:
  for +s: Replicas.Node<Basics.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Work.Reads(Basics.Key.clash(n), [], Judging.Resolve.work(s, h, n, m))

law Clash.shut:
  for +s: Replicas.Node<Basics.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +f: Ledgers.Id
  {Replicas.Node.get(~Basics.Ask.machine(), s, h, Basics.Key.clash(n)) == Some{[]}: Maybe<&2, List<&2, U32>>}
    -> {Judging.Clash.open(s, h, n, f) == False{}: Bool}

# a merge of whole trees keeps what the merge of each resource takes: when the
# merge of the resource n takes the root x (Pick.merge_theirs, Pick.merge_ours:
# a change that only one side made), the tree that the merge gives holds n
# with x
law Merge.keeps:
  for +s: Replicas.Node<Basics.Ask>
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
  for s: Replicas.Node<Basics.Ask>
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Basics.Roots.same(o, b) == True{}: Bool}
    -> {Judging.Pick.merge(f, s, b, o, t) == Some{Judging.Pick.Take{t}}: Maybe<&2, Judging.Pick>}

# and when theirs is the base, it keeps ours
law Pick.merge_ours:
  for f: Formats.Format
  for s: Replicas.Node<Basics.Ask>
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Basics.Roots.same(o, b) == False{}: Bool}
    -> {Basics.Roots.same(t, b) == True{}: Bool}
    -> {Judging.Pick.merge(f, s, b, o, t) == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>}

# a node keeps only ballots that it checked: a ballot that it accepts is the
# next of its node's chain in its store, and the key of that chain signs it
law Seal.accept_fits:
  for +s: Replicas.Node<Basics.Ask>
  for +b: Ledgers.Ballot
  for +c: Replicas.Keychain
  for +s2: Replicas.Node<Basics.Ask>
  {
    Replicas.Seal.chain(~Stepping.Ask.kernel(), 
      s,
      Replicas.Ballot.store(b),
      Replicas.Ballot.node(b)
    )
      == Some{c}: Maybe<&2, Replicas.Keychain>
  }
    -> {Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b) == Some{s2}: Maybe<&2, Replicas.Node<Basics.Ask>>}
    -> {Replicas.Seal.fits(c, b) == True{}: Bool}

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
    Replicas.Seal.fits(
      Replicas.Keychain{n, last, Seals.Seal.public(seed), f},
      Ledgers.Ballot.make(seed, x, last, k)
    )
      == True{}: Bool
  }

# a majority decides, in sequence: a head moves only over a step that the
# owners in its tip decided next, in some round
law Node.advance_at:
  for +s: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +h: Replicas.Head
  {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>}
    -> {
      Replicas.Heads.level(
        Some{h},
        Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.Node.advance(~Stepping.Ask.kernel(), s, c), c)
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
          == Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.Node.advance(~Stepping.Ask.kernel(), s, c), c): Maybe<&2, Replicas.Head>
      }
    )

# the decided steps of a line stay as a node grows: a head that is some
# decided steps from a head h is so in any node that keeps every cell
law Line.at_grows:
  for +rs: List<&2, Nat>
  for +a: Replicas.Node<Basics.Ask>
  for +u: Replicas.Node<Basics.Ask>
  for +c: Ledgers.Chain
  for +h: Replicas.Head
  for +x: Replicas.Head
  {Reading.Node.grows(a, u) == True{}: Bool}
    -> {Line.at(rs, a, c, h) == Some{x}: Maybe<&2, Replicas.Head>}
    -> {Line.at(rs, u, c, h) == Some{x}: Maybe<&2, Replicas.Head>}

# one history: two nodes whose ledgers do not clash (one node u keeps every
# cell of both, and the ballots that u holds on the line follow the rules of
# rounds), the same number of decided steps from the same head of a line, are
# at the same head, whatever the round of each step
law Line.at_agrees:
  for ~u: Replicas.Node<Basics.Ask>
  for ~c: Ledgers.Chain
  for ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), u, c)
  for +rs1: List<&2, Nat>
  for +rs2: List<&2, Nat>
  for +a: Replicas.Node<Basics.Ask>
  for +b: Replicas.Node<Basics.Ask>
  for +h: Replicas.Head
  for +x: Replicas.Head
  for +y: Replicas.Head
  {Reading.Node.grows(a, u) == True{}: Bool}
    -> {Reading.Node.grows(b, u) == True{}: Bool}
    -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
    -> {Line.at(rs1, a, c, h) == Some{x}: Maybe<&2, Replicas.Head>}
    -> {Line.at(rs2, b, c, h) == Some{y}: Maybe<&2, Replicas.Head>}
    -> {x == y: Replicas.Head}

# a node fetches on demand: a node b that lacks the data of the hash h holds
# it after it takes in what a node a that holds it serves
law Node.fetch:
  for +a: Replicas.Node<Basics.Ask>
  for +b: Replicas.Node<Basics.Ask>
  for +h: Hashes.Hash
  for +ws: List<&2, U32>
  {Ledgers.State.data(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), h) == Some{ws}: Maybe<&2, List<&2, U32>>}
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), b),
        Ledgers.Slot.data(h)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      Ledgers.State.data(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.take(~Stepping.Ask.kernel(), b, Replicas.Node.serve(~Basics.Ask.machine(), a, [h]))),
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
  for +s2: Replicas.Node<Basics.Ask>
  for +t2: Replicas.Tip
  for +s: Replicas.Node<Basics.Ask>
  for +s3: Replicas.Node<Basics.Ask>
  {Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>}
    -> {
      Reading.Node.grows(
        s2,
        Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, qs, from, Some{Replicas.Run{s2, t2}}, s)
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
  for +s2: Replicas.Node<Basics.Ask>
  for +t2: Replicas.Tip
  for +s: Replicas.Node<Basics.Ask>
  for +s3: Replicas.Node<Basics.Ask>
  {Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>}
    -> {
      Replicas.Tip.at(~Basics.Ask.machine(), 
        Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, qs, from, Some{Replicas.Run{s2, t2}}, s),
        Replicas.Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Replicas.Tip>
    }

# a node holds what it takes in: an entry that it reads of what was sent, in
# a slot that it lacks, it then holds
law Node.take_holds:
  for +s: Replicas.Node<Basics.Ask>
  for +t: Ledgers.State(Basics.Ask)
  for +k: List<&2, Bool>
  for +e: Ledgers.Entry<Basics.Ask>
  {
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.Node.reads(~Basics.Ask.machine(), t),
      k
    )
      == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        k
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.take(~Stepping.Ask.kernel(), s, t)),
        k
      )
        == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }

# a pending write goes with its writer to another node: a request that a node
# takes in waits on its line there, so the node has a draft for its writer
# (Node.draft_some) and the writer's read shows it (Node.read_draft)
law Node.take_waits:
  for +s: Replicas.Node<Basics.Ask>
  for +t: Ledgers.State(Basics.Ask)
  for +i: Ledgers.Id
  for +time: String
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +ch: Basics.Change
  {
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.Node.reads(~Basics.Ask.machine(), t),
      Ledgers.Slot.ask(i)
    )
      == Some{
        Cells.One{Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}}
      }: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
    -> {
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        Ledgers.Slot.ask(i)
      )
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
    }
    -> {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Replicas.Wait.of(~Basics.Ask.machine(), Replicas.Node.take(~Stepping.Ask.kernel(), s, t), Replicas.Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }

# writers are told only about changes to what their work uses: each change
# that Node.affects gives for a branch holds (Touch.holds): another line made
# it, the branch lacks it, and it wrote a resource that a resource of the
# branch is, or uses through its imports, at any depth
law Node.affects_used:
  for +s: Replicas.Node<Basics.Ask>
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
  for +s: Replicas.Node<Basics.Ask>
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
  for +s: Replicas.Node<Basics.Ask>
  for +e: Replicas.Envelope
  for +q: Basics.Ask
  for +e2: Replicas.Envelope
  for +q2: Basics.Ask
  {Replicas.Envelope.of(e2) == Replicas.Envelope.of(e): Ledgers.Id}
    -> {
      Replicas.Node.ask(~Stepping.Ask.kernel(), 
        m,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        e2,
        q2
      )
        == Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q): Replicas.Node<Basics.Ask>
    }
