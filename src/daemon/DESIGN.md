# Daemon core: design and state

README.md is the truth. This file says how the core is built, what is proven, and what the proofs
assume.

Files of the core (`core/`), each one domain, in the order in which they build on each other:

| File | Holds |
| --- | --- |
| `basics.bend` | names, the node, content, tips and logs, heads, ancestry |
| `judging.bend` | the judges: write, resolve, merge, move, groups, owners |
| `stepping.bend` | runs and steps |
| `sealing.bend` | seals and key chains |
| `voting.bend` | rounds, ballots, moves of a head, what a node does with a request |
| `reading.bend` | sync, reads, drafts, answers, notices |
| `spec.bend` | the laws, and the measures that only laws use |
| `proofs/*.bend` | the proofs, by subject; `impl.bend` gathers them: a check of it checks all |

## 1. The design

**Rule: one source of truth for each thing, read in about log(size) steps, checked by hash.**

- **Ledger** (`shared/ledger.bend`): what nodes replicate. Requests, ballots and data, each in the
  slot that its own content names. A node takes in what it lacks and never changes what it holds
  (`State.take`), so a ledger only grows. A step is what a majority of a line's owners cast in
  one round of a height (`State.decide`), and nothing else. The ledger does not read a line's
  state.
- **Tip** (`core/basics.bend`): what a line holds, as two trees named by one hash.
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
  (`Vote.allowed`, `Plan.follow`). An owner casts for a change of who decides only when it was asked
  at it (`Node.consent`). All of this reads the ledger; a head holds no round.
- **Notices** cost what is new, not the history: the new versions of a branch are a range of
  numbers (`Branch.since`), and the changes elsewhere that a branch did not take in are the
  versions after the places in its version vector (`Branch.lacked`).
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
  only on what it knows, and waits for a node that it lacks. A merge, a move and a new branch
  walk trees (`Tree.list`, `Tree.diff`); they wait until the node holds the whole of each
  (`Tree.whole`), so they never act on a part of a tree. A look gives the hash of that node
  (`Node.lacks`); another node serves the data of a hash (`Node.serve`).
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

All of `core/impl.bend` checks in about 13 s (it was 175 s). A proof file alone checks with no error; it reports as open only the laws that another file proves.

## 3. What is proven (`core/impl.bend` and every file below it print ALL PROOFS CHECK)

README claim, then the law.

- Catching up loses nothing: `Node.after_grows` (whatever the node does: a request, what
  another node sent, a sync); ledger `take_grows`, `take_join`, `join_comm`, `join_assoc`, `join_idem`.
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
- A majority decides, in sequence. A history is measured by `Line.at` (one decided step for
  each round of a list). `Node.advance_at` (a head moves only over a step that the owners in its
  tip decided next, in some round), `Line.at_grows` (decided steps stay as a node grows),
  `Line.at_agrees` (the same number of decided steps from the same head give the same head on
  any two nodes whose ledgers do not clash and hold ballots that follow the rules of rounds,
  whatever the round of each step).
- Every head is on the decided chain: `Node.after_on` (a head that is some decided steps from a
  head with a tip stays so, whatever the node does next). A node sets a head in four places: a
  step that it checked, and three that set only a head with no tip (`Path.moved`, `Path.set`).
- Every node opens a branch at the same first tip: `Chain.start_final` (the log of the store
  holds the first tip of a branch for good), with the one history of the store's line.
- A majority is enough, also when the proposer is away: two rounds of one height decide the
  same step (the lemma `Rounds.one`, inside the proof of `Line.at_agrees`). The premise of
  `Line.at_agrees` is the rules of rounds (`Rounds.Rules`), for the ballots that the node holds:
  `Rounds.Allow` (the passes that a vote names allow it), `Rounds.Last` (a pass names the last
  vote of its node below its round), `Rounds.Same` (the votes of one round are for one step).
  They say that the owners' nodes follow the protocol; a node that stops is fine, a node that
  lies is not. Below it: two majorities share a node (`Major.meets`).
- A writer's read shows its own pending write: `Node.draft_some` (a write that waits gives a
  draft), `Node.read_draft` (the read at the head of the branch is the bytes of the draft).
  After a switch of nodes: `Node.take_waits` (a request that a node takes in waits on its line
  there) and `Node.take_holds` (it holds the request), so the same two laws hold on the new
  node. A request waits until its line gives it an outcome: `Step.run_outs` (a step gives each
  of its requests an outcome) and `Wait.left_keeps` (a head that moves takes only the requests
  of its step off the requests that wait; `State.moved` is the one place that takes any off).
  A request that names a version that no line makes stays Pending, as the README says of a
  request whose owners were not reached.
- A node fetches the rest on demand: `Node.fetch` (a node that lacks the data of a hash holds it
  after it takes in what a node that holds it serves; `Node.lacks` gives the hash, `Node.serve`
  the data). Below it: `State.take_data`. A sync catches up in one go, also over each change
  of a key (`Sync.more`).
- Every part is kept by enough nodes: `Cast.put_keeps` (a node that casts for a step keeps each
  new part of the step, from its own run of it), `Cast.put_tip` (and the step's tip). A step is
  decided by a majority of the owners, and a node only grows, so a majority of the owners holds
  each part of each decided step. A part is lost only when a majority of the owners is lost;
  that each of them made the part before it cast is the protocol, as for rounds.
- Writers are told only about changes to what their work uses: `Node.affects_used` (each change
  that a branch is told of was made on another line, and wrote a resource that a resource of the
  branch is, or uses through its imports, at any depth).
- A merge turns Written once each clashing resource is resolved: `Resolve.reads` (a resolve gives
  the resource its content), `Resolve.shuts` and `Clash.shut` (it shuts the clash); the answer
  is Written when no clash of the merge is open (`Answer.left`, by construction).
- A move records a version equal to its target: `Move.reads` (each resource of the target is, with
  the same content, in the tree that the move gives; a move sets only keys of the version
  vector).
- A taken write reads back, in the node that the verdict holds: `Judge.write_reads`.
- A merge never loses a change made on only one side: `Pick.merge_theirs`, `Pick.merge_ours`
  (for one resource), and `Merge.keeps` (what the merge of a resource takes, the tree that a
  merge of whole trees gives holds for it).
- The owners of a line are the nodes inside its owner group: `Own.takes_inside`. A change of a
  group reaches each line that the group owns by the line's next decided step: a node that works
  on a line asks for that step by itself (`Adopt.at`, in `Node.does` and `Node.sync`), and the
  line's present owners decide it. This is by construction, with no law. A change at once,
  without the present owners, cannot be safe: two majorities could decide one height.
- Requests are the same exactly when equal: `Ask.same`.
- Below the core: quorum, trie, cell, tree (`get_set`, `get_other`, `get_grows`, ...), rope
  (`read_put`, `read_grows`), codes, formats, seal (`Seal.check_sign`).

## 4. What the proofs assume, and what was decided

- **Owners' nodes follow the protocol.** The rules of rounds (`Rounds.Allow`, `Rounds.Last`,
  `Rounds.Same`, together `Rounds.Rules`) are the premise of `Line.at_agrees`. A node that stops is fine; a node that lies is
  not. A node's own ballots follow the rules by construction (`Plan.lead`, `Pass.to`,
  `Cast.round`), and it copies only a vote that the rules allow (`Plan.follow_allowed`).
- **Hash-based signatures hold.** That no other node can make a node's seal is the assumption of
  one-time signatures on SHA-256.
- **A group change reaches a line by the line's next decided step** (README, Vend Owner Group).
  A change at once, without the line's present owners, cannot be safe.
- **A judge puts each new node once.** A verdict holds the node that the judge wrote
  (`Verdict`), and the run goes on from it (`Run.over`). "A node only grows" is a lemma for each
  judge (`Verdict.change`, `Grown.*` in `proofs/trees.bend`). A new format adds no judge: a
  format only merges bytes (`Pick.format`).
- **Reads of a history are by range**: `Node.versions` and `Node.log` take a first number and a
  count. `Node.affects` and `Node.impact` read each branch that the node follows once, and of
  each only the versions that the branch did not take in.
- **Transport** (`transport/spec.bend`) is a spec only; it is not part of the core.
- **Lint**: `LINTCONTEXT.md`.
