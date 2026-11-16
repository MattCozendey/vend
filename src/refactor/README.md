# Refactor

This folder holds a rewrite of Vend in two layers. The lower layer is a generic decentralized
system that knows nothing about versioning. Vend is a small set of hooks on top of it.

The root `README.md` stays the canon for what Vend is. This file is the plan for how to build it.

## Rules of the work

- Laws first. Each module gets its `spec.bend`, with every law stated and approved, before any
  implementation is written.
- Layout: the same onion as the rest of `src/`. Each layer has one `shared.bend` file or one
  `shared/` folder, and what is more general goes deeper. The generic decentralized system lives in
  the `shared` tree of this folder. Vend-specific modules live at the top level of `src/refactor/`.
- Self-sufficient: no file in `src/refactor/` imports a file outside it, except Bend's Base. Code
  from elsewhere in the repository is avoided. When it is needed, its file is copied into the layer
  of `src/refactor/` where it belongs (domain-agnostic code goes into the `shared` tree, at the
  depth its generality calls for) and adjusted there; the copy then follows every rule of this
  folder.

## Requirements

Trust

1. Only Bend's checker, the hash and signature functions, and the operating system are trusted.
   Everything else is proven.
2. Each law states exactly what is meant, never less.
3. Group members are trusted for one thing only: they never sign two votes that contradict each
   other. Nobody else is trusted at all.
4. Nodes can be offline, slow or lost, and there is still one history.

Shape

1. All nodes are equal. A "server" is a node that does more.
2. The generic layer comes first and knows nothing about versioning. Versioning is a small set of
   hooks on top of it.
3. Hooks can bring their own data and storage, so speed work happens in the hook, proven equal to
   the plain version.
4. Groups can contain groups, and they can change over time.

Behavior

1. Nodes with the same facts give the same answers, in whatever order they got them. Catching up
   never creates a conflict.
2. A node can hold only part of the data and still never give a wrong answer. It answers "unknown",
   or "within this range", until it knows.
3. No data is ever lost, because enough nodes keep each piece.
4. A request counts once, however often and wherever it is sent. A writer always sees their own
   changes, on any node, even before they are decided.

Cost

1. Cost does not grow with history. A small edit costs about its own size, even in huge files.
2. Caching is safe, now and for any cache added later.
3. The design is simpler and stronger than the current one: fewer separate things to prove, more
   guaranteed behavior.
4. It keeps room for everything the root `README.md` plans (formats, nested languages, mounts,
   submodules).

## Design

### Facts

The state of a node is a set of facts. A fact is signed by its author and named by the hash of its
code. A fact enters the set only if it checks by itself: its signature, and the hashes of the facts
and parts it refers to. A Sync is the union of two sets. Union is commutative, associative and
idempotent, so the order in which a node receives facts cannot change anything.

### Queries

A hook is a query over the set. There are two kinds.

- A **final** query answers Unknown, a value, or Broken. A value can also be a range that only
  narrows (for example "at least 3 versions"); Unknown is the widest range. Each final query proves
  that more facts never change a known answer, except to Broken. A known answer can therefore be
  cached forever.
- A **live** query is a function of the set too, so the same facts give the same answer. But its
  answer may change when facts arrive. A writer's view of a branch with their pending changes is a
  live query. A live query is never cached.

A query that always answers Unknown is final and useless. So each final query also states when it
must know: if the set holds these facts, the answer is known.

A hook may keep its own state, in any data structure, and update it one fact at a time. It then
proves that its state gives the same answer as the plain query over the set, whatever the order in
which the facts arrived.

### Ordering

Consensus is a hook, not the base. It is used only where one choice must win over another, for
example "which request is version 5 of this branch". Everything that only adds (a request exists, a
part exists, a node keeps a part) needs no consensus.

"Slot k is decided" is a final query over vote facts. It counts only the votes of members of the
group of that slot. Voting is the one act that is not monotone: a node must never sign two votes for
one step. If a member does, the slot's answer becomes Broken, with both votes as proof. The damage
stays in the groups that contain the liar. A stranger's votes count nowhere, so a stranger cannot
break anything.

### Groups

The members of a group are a final query over decided facts. A group can contain groups; its nodes
are all the nodes reachable through it. The votes of a slot count against the group as decided
before that slot, so a change of a group reaches each thing it owns at its next decided step.

### Time

The program reads the clock and gives the core a `Tick` deed when a round takes too long. On a
Tick, a node may call its next round. The core has no clock value. Safety does not depend on
Ticks; only progress does.

### Keeping data

A node may drop a part only when the set holds signed facts from enough trusted nodes saying that
they keep it. How many is enough is a parameter of the hook.

### Forgetting

The set only grows. A checkpoint is a decided fact that lets nodes drop the facts under it. Its
rule is stated and proven on its own.

## Requirement coverage

| Requirement | How |
| --- | --- |
| Trust 1 | Signatures and hashes are the only assumptions. |
| Trust 2 | Each final query has two laws: it never changes a known answer, and it knows when it must. |
| Trust 3 | Votes count only for members. A lying member makes only the groups that contain it Broken. |
| Trust 4 | One history: two majorities of a group always share a member. Progress: see Limits. |
| Shape 1, 2 | Nodes are one type; Vend is hooks. |
| Shape 3 | A hook's own state, proven equal to its plain query. |
| Shape 4 | Groups are a final query over decided facts. |
| Behavior 1 | Answers are functions of the set; Sync is union. |
| Behavior 2 | Final queries answer Unknown or a range until they know. |
| Behavior 3 | Keeping data. See Limits. |
| Behavior 4 | A request is one fact, and ordering puts it in at most one slot. A writer's view is a live query. |
| Cost 1 | Content is split into parts by hash inside the hooks; Sync compares hashes of subtrees; checkpoints. |
| Cost 2 | Final answers never change, so caches never need invalidation. Live queries are not cached. |
| Cost 3 | Agreement, validity and groups are proven once, for every hook. |
| Cost 4 | Formats, languages, mounts and submodules are hooks. |

## Limits

No design removes these. They are stated so that no law claims more.

- Progress needs a majority of each group to be reachable, and a round that lasts long enough for
  that majority to sync with its leader.
- Data is kept only as long as enough of the nodes that signed that they keep it are not lost.
- A Sync by hashes of subtrees can miss facts when two inputs have one hash. A missed fact makes
  answers less known, never wrong.
- Facts from strangers cost storage. The program limits them; the core has no rule for them.

## Sources

Read from abstracts and summaries only, not the full papers.

- Hellerstein and Alvaro, [Keeping CALM: when distributed consistency is easy](https://arxiv.org/abs/1901.01930)
  (2019): what needs no coordination is exactly what is monotone.
- Kuper and Newton, LVars ([POPL 2014 paper](https://www.cl.cam.ac.uk/~nk480/lvish-popl.pdf)):
  values that only move up a lattice, with reads that wait for a lower bound; an error state when
  two writes cannot join.
- Kleppmann and Howard, [Byzantine Eventual Consistency](https://arxiv.org/abs/2012.00472) (2020):
  what a peer-to-peer database can do with any number of faulty nodes and no consensus.
- Sanjuán et al., [Merkle-CRDTs](https://arxiv.org/abs/2004.00107) (2020): facts in a Merkle DAG as
  transport and storage for merging data types.
- Auvolat and Taïani, [Merkle Search Trees](https://g-trees.github.io/g_trees/assets/references/auvolat2019merkle.pdf)
  (SRDS 2019): a tree whose shape depends only on its content, so two nodes find their differences
  by comparing hashes.
