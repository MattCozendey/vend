# Daemon core: design and state

README.md is the truth. This file says how the core is built, what is proven, and what is not yet.
Delete each open item when the code makes it true.

## 1. The design

**Rule: one source of truth for each thing, read in about log(size) steps, checked by hash.**

- **Ledger** (`shared/ledger.bend`): what nodes replicate. Requests, ballots and data, each in the
  slot that its own content names. A node takes in what it lacks and never changes what it holds
  (`State.take`), so a ledger only grows. A step is what a majority of a line's owners cast at a
  height (`State.decide`). The ledger does not read a line's state.
- **Tip** (`core/spec.bend`): what a line holds, as two trees named by one hash.
  - Content: resources (each a root of a rope), clashes, version vector, owner group; for a store
    also its groups and the first tip of each branch.
  - Log: a tree that only gains keys. Owners of the next step, count of versions, outcome of each
    request, each version by number, each mark. An outcome, a version and a mark are written once
    (`Run.add`).
- **Step**: a batch of requests, run in order from a tip (`Step.run`). A request that the log holds
  is skipped: a change counts once.
- **Node**: its ledger, its head of each line (height and tip), and the requests that wait on each
  line. Each step of a node reads its head by line. `Node.cast` casts the node's ballot for the
  step that runs the waiting requests. `Node.advance` moves a head only to a step that a majority
  of the owners in its tip cast and that the node ran itself with the same result. A run gives a
  node only its ledger: heads and waiting requests are the node's own, by construction. A head
  that has a tip moves only by a step (`State.first`).
- **Reads**: `Line.get` reads the log of a line at the node's head. An answer, a version, a mark
  and a writer's pending write are each a few reads of a tree, or of the requests that wait on one
  line.
- **Content** (`shared/rope.bend`): a change names content by the root of a content-defined rope,
  so a change, a tree and a sync cost about the size of an edit.
- **Seals** (`shared/shared/shared/seal.bend`): one-time signatures on SHA-256 (Winternitz,
  w = 16). Not yet used by the ledger (section 4).
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

All of `core/impl.bend` checks in about 6 s (it was 175 s).

## 3. What is proven (every file prints ALL PROOFS CHECK)

README claim, then the law.

- A node checks what it receives before it keeps it; catching up loses nothing:
  `Node.ask_grows`, `Node.take_grows`, `Node.sync_grows`, `Node.after_grows`; ledger
  `take_grows`, `take_join`, `join_comm`, `join_assoc`, `join_idem`, `data_hash`.
- A change counts once: `Node.ask_once`; a step skips a request that the log holds (`Step.fresh`,
  by construction).
- Stale and Refused are final; answers only move forward: `Node.answer_follows`,
  `Node.out_final`.
- A version never changes; history only grows at its end; marks are for good:
  `Node.made_final`, `Chain.version_final`, `Chain.mark_final`, all from `Node.after_keeps` (a log
  only gains keys, whatever the node does next: `Run.kept`, then each step of a node).
- A majority decides, in sequence: `Node.advance_decided` (a head moves only to the tip that the
  owners in its tip decided next), `Node.advance_agrees` (two nodes at the same head, whose
  ledgers do not clash, move to the same head).
- A writer's read shows its own pending write: `Node.draft_some`.
- A taken write reads back: `Judge.write_reads`.
- A merge never loses a change made on only one side: `Pick.merge_theirs`, `Pick.merge_ours`.
- The owners of a line are the nodes inside its owner group: `Own.takes_inside`.
- Requests are the same exactly when equal: `Ask.same`.
- Below the core: quorum, trie, cell, tree (`get_set`, `get_other`, `get_grows`, ...), rope
  (`read_put`, `read_grows`), codes, formats, seal (`Seal.check_sign`).

## 4. Open

- **Seals in the ledger.** A ballot is an entry in a node's slot; nothing stops another node from
  writing it. To do: a ballot carries its place and a seal; it names the key of the node's next
  ballot on the line; `Node.take` drops a ballot whose seal fails; a restarted node starts a new
  key chain through its owner group.
- **Agreement over a whole history.** `Node.advance_agrees` is one step. The induction over
  heights (same first tip, then step by step) is not a law yet. It needs an invariant of a node:
  each head is the end of the chain of decided steps of its ledger.
- **Missing is not absent.** A tree read gives none for both. An owner that lacks data can refuse
  where it must wait. To do: `Found`, `Absent`, `Missing{hash}` in `tree.bend` and `rope.bend`,
  and the judge waits on `Missing`. Then also: a move records a version equal to its target (law).
- **Owners through a group.** `Node.adopt` still asks for a line's owners again after its group
  changes. Target: a line reads its owners through its group at the store version that it names.
- **Sync steps every line.** `Node.sync` walks every head. To do: step only the lines of the new
  requests and ballots (a ballot must carry its place), and the lines that wait for new data.
- **Walks that are left:** `Node.versions` lists every version (use a range); `Touch.versions`,
  `Version.keys`, `Node.affects`, `Node.impact`, `Node.notices` read every version of every
  branch; `Tree.list` walks a tree for names and clashes. Each needs an index in the log or the
  content.
- **The ledger's trie** is one node for each bit of a key. A compressed trie is in work.
- **A put is done twice** for a taken request (`Work.put`, then `Run.content`).
- **Transport** (`transport/spec.bend`) is a spec only.
