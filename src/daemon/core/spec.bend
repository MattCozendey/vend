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

# answers only move forward: a request that a node answers stays answered;
# Stale and Refused are final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for +n: String
  for +evs: List<&2, Replicas.Deed<Basics.Ask>>
  for +s: Replicas.Node<Basics.Ask>
  for +e: Replicas.Envelope
  for +q: Basics.Ask
  for +x: Reading.Answer
  {Reading.Node.answer(s, e, q) == Some{x}: Maybe<&2, Reading.Answer>}
    -> {Reading.Answer.follows(x, Reading.Node.answer(Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s), e, q)) == True{}: Bool}

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
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to}),
      Basics.Key.res(n)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
    -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Move.work(s, c, to, h))

# a merge turns Written once each clashing resource is resolved: a resolve
# gives the resource its content, and shuts its clash (a clash whose key holds
# no request is not open: Clash.shut)
law Resolve.reads:
  for +s: Replicas.Node<Basics.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(m), Judging.Resolve.work(s, h, n, m))

law Resolve.shuts:
  for +s: Replicas.Node<Basics.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.clash(n), [], Judging.Resolve.work(s, h, n, m))

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
      Judging.Merge.names(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
      n
    )
      == True{}: Bool
  }
    -> {
      Basics.Res.find(
        s,
        Replicas.Node.root_of(~Basics.Ask.machine(), s, Judging.Merge.base(s, c, from, h)),
        n
      )
        == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>
    }
    -> {Basics.Res.find(s, h, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {
      Basics.Res.find(
        s,
        Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from}),
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
    -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(x), Judging.Merge.work(s, c, from, h))

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
        == Replicas.Root.bytes(~Basics.Ask.machine(), s, Judging.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }

