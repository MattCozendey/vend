# Daemon core: design and state

README.md is the truth. This file says how the core is built, what is proven, and what is not yet.
Delete each open item when the code makes it true.

## 1. The design

**Rule: one source of truth for each thing, read in about log(size) steps, checked by hash.**

- **Ledger** (`shared/ledger.bend`): what nodes replicate. Requests, ballots and data, each in the
  slot that its own content names. A node takes in what it lacks and never changes what it holds
  (`State.take`), so a ledger only grows. A step is what a majority of a line's owners cast at a
  height (`State.decide`). The ledger does not read a line's state. It has no facts and no epochs.
- **Tip** (`core/spec.bend`): what a line holds, as two trees named by one hash.
  - Content: resources (each a root of a rope), clashes, version vector, owner group; for a store
    also its groups and the first tip of each branch.
  - Log: a tree that only gains keys. Owners of the next step, count of versions, outcome of each
    request, each version by number, each mark.
  So an answer, the newest version, a version by number, a mark and the owners are each one read
  of a tree.
- **Step**: a batch of requests, run in order from a tip (`Step.run`). A run is a function of the
  tip, the requests and the versions that they name, so every node gets the same result. A request
  that the log holds is skipped: a change counts once.
- **Node**: its ledger, its head of each line (height and tip), and the requests that wait on each
  line. `Node.cast` casts the node's ballot for the step that runs the waiting requests.
  `Node.advance` moves a head only to a step that a majority of the owners in its tip cast and that
  the node ran itself with the same result: a node checks a step before it keeps it. A node that
  takes entries in (`Node.take`) pays for what is new, not for what it holds.
- **Content** (`shared/rope.bend`): a change names content by the root of a content-defined rope,
  so a change, a tree and a sync cost about the size of an edit.
- **Formats** stay outside the judge: the judge sees a resource as a root and a format-given merge
  of bytes. A nested format is a new `Formats.Format`; the ledger, the trees and the steps do not
  change.

Old design (facts, epochs, one request for each step, walks of a line): commit `c5a7cda` and
before. Its laws were all proven on that design; they are restated on this one in section 3.

## 2. What is proven now (every file prints ALL PROOFS CHECK)

- Ledger: `join_comm`, `join_assoc`, `join_idem`, `missing_join`, `take_grows`, `take_join`,
  `take_all`, `take_missing`, `decide_grows`, `add_grows`, `data_hash`, `data_grows`,
  `put_data_get`, `put_data_grows`.
- Quorum, trie, cell, tree, rope, codes, formats: as before (`Tree.get_set`, `get_other`,
  `get_grows`, `Rope.read_put`, `read_grows`, ...).
- Core: `Ask.same` (requests are the same exactly when equal), `Own.takes_inside` (the owners of a
  line are the nodes inside its owner group).

A run of the new core (not a law): one node starts a store, makes a branch, writes, refuses a
write with no base as Stale, writes on a base, marks, and a second node catches up by sync, writes
(Pending there, and its own read shows it), and is Written after the owner syncs.

## 3. Open: laws to state and prove on this design, in order

1. **A node's ledger only grows** through `ask`, `cast`, `advance`, `take`, `sync`.
2. **A log only gains keys** through `Step.run` (from `Tree.get_other`): then answers move forward
   only (Stale and Refused final, taken stays taken), versions only grow at the end, a version
   never changes, a mark is for good.
3. **A change counts once** (`ask` of a held ID changes nothing; a request in the log is skipped).
4. **A writer reads its own pending write** (the proof of the old `draft_own` carries over).
5. **A sole owner's write is Written and reads back**, with no premise about slots.
6. **A head is the end of a chain of decided, checked steps** (the invariant), kept by each
   operation.
7. A merge keeps a change that only one side made; a move records a version equal to its target.

## 4. Open: design

- **Missing is not absent.** A tree read gives none for both. An owner that lacks data can refuse
  where it must wait. Fix: `Found`, `Absent`, `Missing{hash}` in `tree.bend` and `rope.bend`.
- **Seals.** A ballot is an entry in a node's slot; nothing stops another node from writing it.
  The scheme needs foreign code or a pure-Bend implementation (your choice).
- **Owners through a group.** `Node.adopt` still asks for a line's owners again after its group
  changes. Target: a line reads its owners through its group at the store version that it names.
- **Walks that are left:** `Node.versions` lists every version (use a range); `Touch.versions`,
  `Version.keys`, `Node.affects`, `Node.impact`, `Node.notices` read every version of every
  branch; `Tree.list` walks a tree for names and clashes; `Writer.asks` reads every request of a
  writer. Each needs an index in the log or the content.
- **The ledger's trie** is one node for each bit of a key. Target: a compressed trie, proven equal.
- **Proof speed.** `core/impl.bend` checks in about 23 s; `rope.bend` costs 9 s in each file that
  imports it.
- **Transport** (`transport/spec.bend`) is a spec only.
