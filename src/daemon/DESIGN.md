# Daemon core: design and state

README.md is the truth. This file says how the core is built, what is proven, and what is not yet.
Delete each open item when the code makes it true.

## 1. The design

**Rule: one source of truth for each thing, read in about log(size) steps, checked by hash.**

- **Ledger** (`shared/ledger.bend`): what nodes replicate. Requests, ballots and data, each in the
  slot that its own content names. A node takes in what it lacks and never changes what it holds
  (`State.take`), so a ledger only grows. A step is what a majority of a line's owners cast in
  one round of a height (`State.decide`), and nothing else. The ledger does not read a line's
  state.
- **Tip** (`core/spec.bend`): what a line holds, as two trees named by one hash.
  - Content: resources (each a root of a rope), clashes, version vector, owner group; for a store
    also its groups and the first key of each node.
  - Log: a tree that only gains keys. Owners of the next step, count of versions, outcome of each
    request, each version by number, each mark; for a store also the first tip of each branch.
    An outcome, a version, a mark and a first tip are written once (`Run.add`). A store makes a
    branch once (`Step.branch`).
- **Step**: a batch of requests, run in order from a tip (`Step.run`). A request that the log holds
  is skipped: a change counts once.
- **Node**: its ledger, its head of each line (height and tip), and the requests that wait on each
  line. Each step of a node reads its head by line. `Node.cast` casts the node's ballot for the
  step that runs the waiting requests. `Node.advance` moves a head only to a step that a majority
  of the owners in its tip cast and that the node ran itself with the same result. A run gives a
  node only its ledger: heads and waiting requests are the node's own, by construction. A head
  that has a tip moves only by a step (`State.first`).
- **Rounds**: a ballot has a place (line, height, round) and is a vote or a pass. The proposer of
  the round r at the height h is the owner (h + r) in turn (`Owners.turn`). In round 0 it
  proposes what waits. A node passes to the next round when transport tells it that the round
  took too long (`Deed.Pass`), and names its last vote below (`Last.below`). The proposer of a
  later round needs the passes of a majority of the owners, and proposes the last vote of the
  highest round among them, if any (`Plan.lead`). The others copy a vote that these rules allow
  (`Allowed`, `Plan.follow`). An owner casts for a change of who decides only when it was asked
  at it (`Node.consent`). All of this reads the ledger; a head holds no round.
- **Reads**: `Line.get` reads the log of a line at the node's head. An answer, a version, a mark
  and a writer's pending write are each a few reads of a tree, or of the requests that wait on one
  line.
- **Content** (`shared/rope.bend`): a change names content by the root of a content-defined rope,
  so a change, a tree and a sync cost about the size of an edit.
- **Seals** (`shared/shared/shared/seal.bend`, `Seal.*` in the core): one-time signatures on
  SHA-256 (Winternitz, w = 16). A ballot is a sealed record: its place, its node, the step, the
  place of the node's ballot before it in the store, the key of the next one, and the seal. So a
  node's ballots in one store are a chain, and each key signs once. The store gives a node the
  first key of its chain: a first owner's in the request that starts the store, then by a `Key`
  change that the store's owners decide (again after a node lost its secret). A node seals each
  ballot that it casts, and keeps a ballot of another node only when it is the next of that
  node's chain and the key of the chain signs it (`Seal.accept`). A ballot that it cannot check
  yet is not kept; it comes again with the next sync.
- **Missing is not absent** (`Tree.look`, `Node.find`): a judge reads with `Node.find`. It refuses
  only on what it knows, and waits for a node that it lacks.
- **Sync** steps only the lines that it may move: those of the new requests and ballots, and
  those with waiting requests (`Sync.lines`).
- **Formats** stay outside the judge: the judge sees a resource as a root and a format-given merge
  of bytes. A nested format is a new `Formats.Format`; the ledger, the trees and the steps do not
  change.

## 2. Proof speed (a rule, not a wish)

The checker runs a term when it compares two terms that are not the same text. One SHA-256 of
known words costs it about a million steps. So:

- A tree read and write look at the root node before they make the path of the key (`Node.get`,
  `Node.set`, proven equal to the tree's own by `Get.is` and `Set.is`).
- A proof never compares two hashes of known words (`Rope.put.go_nil` is the one place).
- A loop with a large fuel waits on a value that a proof does not know (`Advances.at`).

All of `core/impl.bend` checks in about 10 s (it was 175 s).

## 3. What is proven (`core/impl.bend` and every file below it print ALL PROOFS CHECK)

README claim, then the law.

- Catching up loses nothing: `Node.ask_grows`, `Node.take_grows`, `Node.sync_grows`,
  `Node.after_grows`; ledger `take_grows`, `take_join`, `join_comm`, `join_assoc`, `join_idem`.
- A node checks what it receives before it keeps it. By construction, not a law: `Node.take`
  puts each request and each data in the slot that its own content names (`Take.clean`), reads
  data only under its hash (`data_hash`), and keeps a ballot only when it checks
  (`Seal.accept_fits`).
- A change counts once: `Node.ask_once`; a step skips a request that the log holds (`Step.fresh`,
  by construction).
- Stale and Refused are final; answers only move forward: `Node.answer_follows`,
  `Node.out_final`.
- A version never changes; history only grows at its end; marks are for good:
  `Node.made_final`, `Chain.version_final`, `Chain.mark_final`, all from `Node.after_keeps` (a log
  only gains keys, whatever the node does next: `Run.kept`, then each step of a node).
- Owners sign: `Seal.accept_fits` (a node keeps only a ballot that is the next of its node's
  chain and that the chain's key signs), `Seal.fits_own` (a ballot sealed with the chain's
  secret fits), `Seal.check_sign`. That no other node can make one is the assumption of
  hash-based signatures; it is not a law.
- A majority decides, in sequence: `Node.advance_decided` (a head moves only to the tip that the
  owners in its tip decided next), `Node.advance_agrees` (two nodes at the same head, whose
  ledgers do not clash, move to the same head). Over a history, measured by `Line.at` (one
  decided step for each round of a list): `Node.advance_at` (a move is one decided step, in
  some round), `Line.at_grows` (decided steps stay as a node grows), `Line.at_agrees` (the same
  number of decided steps from the same head give the same head on any two nodes whose ledgers
  do not clash, whatever the round of each step).
- Every head is on the decided chain: `Node.after_on` (a head that is some decided steps from a
  head with a tip stays so, whatever the node does next). A node sets a head in four places: a
  step that it checked, and three that set only a head with no tip (`Path.moved`, `Path.set`).
- Every node opens a branch at the same first tip: `Chain.start_final` (the log of the store
  holds the first tip of a branch for good), with the one history of the store's line.
- A majority is enough, also when the proposer is away: `Rounds.one` (two rounds of one height
  decide the same step, so "the rounds of a height decide one step", the premise of the laws
  above, holds). Its premises are the rules of rounds, for the ballots that the node holds:
  `Rounds.Allow` (the passes that a vote names allow it), `Rounds.Last` (a pass names the last
  vote of its node below its round), `Rounds.Same` (the votes of one round are for one step).
  They say that the owners' nodes follow the protocol; a node that stops is fine, a node that
  lies is not. Below it: two majorities share a node (`Major.meets`).
- A writer's read shows its own pending write: `Node.draft_some` (a write that waits gives a
  draft), `Node.read_draft` (the read at the head of the branch is the bytes of the draft).
  After a switch of nodes: `Node.take_waits` (a request that a node takes in waits on its line
  there) and `Node.take_holds` (it holds the request), so the same two laws hold on the new
  node. Not a law yet: that a request waits until its line gives it an outcome.
- A node fetches the rest on demand: `Node.fetch` (a node that lacks the data of a hash holds it
  after it takes in what a node that holds it serves; `Node.lacks` gives the hash, `Node.serve`
  the data). Below it: `State.take_data`.
- Every part is kept by enough nodes: `Cast.put_keeps` (a node that casts for a step keeps each
  new part of the step, from its own run of it), `Cast.put_tip` (and the step's tip). A step is
  decided by a majority of the owners, and a node only grows, so a majority of the owners holds
  each part of each decided step. A part is lost only when a majority of the owners is lost;
  that each of them made the part before it cast is the protocol, as for rounds.
- Writers are told only about changes to what their work uses: `Node.affects_used` (each change
  that a branch is told of was made on another line, and wrote a resource that a resource of the
  branch is, or uses through its imports, at any depth).
- A taken write reads back: `Judge.write_reads`.
- A merge never loses a change made on only one side: `Pick.merge_theirs`, `Pick.merge_ours`.
- The owners of a line are the nodes inside its owner group: `Own.takes_inside`.
- Requests are the same exactly when equal: `Ask.same`.
- Below the core: quorum, trie, cell, tree (`get_set`, `get_other`, `get_grows`, ...), rope
  (`read_put`, `read_grows`), codes, formats, seal (`Seal.check_sign`).

## 4. Open

Design (each needs a decision or new work; none is a proof detail):

- **The rules of rounds are premises.** A node's own ballots follow them by construction
  (`Plan.lead`, `Plan.follow`, `Pass.to`, `Cast.round`), with no law yet. A node keeps a vote of
  another node without a check of `Allowed`; it only copies a vote that is allowed.
- **Missing is not absent, the rest.** The write, resolve, merge and Own judges wait. Still to
  do: the version vector, `Tree.list` and `Tree.diff` (they walk and give no sign of a node that
  they lack), so a merge or a move can still act on a part of a tree. Then the laws: a merge
  keeps a one-sided change as a whole (`Merge.work`, not only one pick), and a move records a
  version with the resources of its target.
- **Owners through a group.** After a group changes, each line that it owns gets its new owners
  by an Own request that any owner's node asks, once (`Node.adopt`). Target: a line reads its
  owners through its group at the store version that it names.
- **Walks that are left:** `Node.versions` lists every version (use a range); `Node.log`,
  `Touch.versions`, `Version.keys`, `Node.affects`, `Node.impact`, `Node.notices` read every
  version of every branch. Target: notices are made when a head moves, from the diff of the two
  contents and an index of imports by content root.
- **A put is done twice** for a taken request (`Work.put`, then `Run.content`): the second one
  makes growth independent of the judge. Target: prove that each judge only grows its node, and
  let the run keep the judge's node.
- **A sealed chain is checked in a few rounds.** A key that a store gives at height h is known
  only after the node moved there, so a node that is far behind needs one more sync for each
  `Key` change in between.
- **A request that can never run** (it names a version that no line makes) waits for good. It
  does not stop its line, but nothing removes it.
- **Names:** `State()` is `Node`; `Chain` (a line) and `Chained` (a chain of keys);
  `core/spec.bend` holds about 15 domains in one file.
- **Lint:** no error. Left: `layout/case` (false: constructors are PascalCase), hints in proof
  bodies.
- **Transport** (`transport/spec.bend`) is a spec only.
