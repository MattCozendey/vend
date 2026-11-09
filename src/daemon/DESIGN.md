# Daemon core: state and redesign

README.md is the truth. This file says where the code is, where it falls short of README, and the
design that closes the gap. Delete each part when the code makes it true.

## 1. What is proven now

All files print ALL PROOFS CHECK. `core/spec.bend` has a map from README to laws above its laws.

| README | Law or construction |
| --- | --- |
| Syncs both ways; same changes, same answers, any order | `Node.take`; ledger `take_join`, `join_comm`, `join_assoc`, `join_idem`, `take_missing` |
| Catching up never creates conflicts | ledger `take_grows` (any input), `take_all`; `Node.sync_grows` |
| Checks what it receives before it keeps it | `Node.take` keeps no entry that contradicts one it holds; data is read only by hash (`data_hash`) |
| A change counts once | `Node.ask_once` |
| Five answers; Stale and Refused are final | `Answer` (5 constructors), `Node.ask_seen`, `Node.answer_kept` |
| Reads show the writer's own pending changes | `Node.read`, `Node.draft_own` |
| History only grows at its end | `Node.versions_grow` |
| A version never changes | `Node.version_kept`, `Node.content_kept` |
| Marks name versions for good | `Node.mark_kept` |
| A group's nodes own what it owns | `Own.takes_inside`, `Node.adopt` |
| Content once by hash; an edit costs its own size | `rope.bend` (`read_put`, `read_grows`), `Node.keep_reads`; a change names its content by root |
| The owner of a branch takes a write | `Node.write_written` (sole owner, 9 premises) |

## 2. Where the code falls short of README

Be skeptical of section 1: these are real gaps, not details.

1. **Laws with premises about slots.** `Node.write_written` needs `Write.Sole`: the tip has one
   owner, the vote slot is empty, no fact says where the request is, no other words are under the new
   hashes. A caller cannot check these. They exist because the ledger tolerates any state, and
   proves nothing about the states that a node can reach.
2. **Facts.** Where a request was decided, where an epoch began and where a line was made are
   entries that some node must write (`settle`, `land`). A read checks them, but nothing proves
   that they are there. With many owners a request can stay Pending after its step is decided,
   until a node lands the line. `land` is a patch.
3. **One change for each decision.** README: many changes for each decision. Each step takes one
   request, so each change costs one round of votes of a majority.
4. **Walks.** `Node.versions`, `Node.head`, `Node.log` and marks list every step of a line.
   `Node.vote` reads every entry of the state. The tip (`Line.tip`) is fast, but no law says that
   it is the end of the listing.
5. **Parts of a store.** A read gives none both when a key is absent and when the node does not
   hold a node of the tree. An owner that lacks data can refuse a write as Stale when it must wait.
6. **Signing.** A ballot is an entry in a node's slot. Nothing stops another node from writing it.
7. **Group changes reach a line only when an owner asks** (`Node.adopt`). No law says that the
   line's owners become the group's nodes after it (it needs facts, gap 2).
8. **Proven only by construction, no law:** a merge keeps a change of one side (`Pick.merge`), a
   move records a version equal to its target, told only about what the work uses (`Touch.holds`).
9. **Speed of proofs.** `core/impl.bend` checks in about 35 s (it was 10 s). `rope.bend` costs 9 s
   in each file that imports it.

## 3. The principled design

Root cause of gaps 1, 2, 3, 4 and 7: the ledger has two sources of truth (ballots, and facts about
ballots), and no invariant. The design below has one source of truth and one invariant.

**Rule: a line is its decided steps. Everything else is read from the tree that a step names, or
from an index that the node itself builds and that an invariant covers.**

1. **A step is a batch.** A ballot of a node at a height of a line is
   `Step{before: root, asks: List<Id>, after: root}`. `after` is the judge, folded over `asks`, from
   `before`: any node can compute it again. A height is one number for each line. Epochs go away.
2. **The tree is the whole state of a line.** It holds what it holds now, and also: the outcome of
   each request (taken or stale, and its sequence number), the version of each sequence number (ID
   and root), the count of versions, the owner group, and the owners of the next step. So the
   status of a request, the head, a version by number and the owners are reads of about log(size)
   nodes, each checked by its hash. No facts.
3. **Decided.** The step of height h is the one that a majority of `owners(h)` voted, and
   `owners(h)` is read from the tree after height h-1 (the first owners come from the request that
   starts the store, or from the store's record of the branch). A change of owners is a change of
   the tree, so it applies from the next step. `Node.adopt` goes away: the judge of a group change
   on the store writes the new owners of the store, and each branch reads its owners through its
   group at the store step that it names.
4. **One invariant.** A node is a record: name, ledger (synced, only grows), heads (local, never
   synced), writers, mounts. `heads` maps a line to its newest checked step. Only `Node.advance`
   writes it, after it checks that step h+1 is decided by the owners in the tree of step h.
   `Node.Good(n)`: each head is the end of a chain of decided steps from the start of its line.
   Laws: the empty node is Good; `ask`, `vote`, `take`, `advance` keep Good. Every other law takes
   a Good node and has no premise about slots. `write_written` becomes: a Good node that is the
   sole owner at the head of a branch, and holds the write's base, answers Written.
5. **Missing is not absent.** A tree read and a rope read give `Found`, `Absent` or
   `Missing{hash}`. A judge waits on Missing. The transport fetches the hash.
6. **Seals.** A ballot carries a seal. `Node.take` drops a ballot whose seal does not check
   against its node. The scheme is a parameter of the core (it needs foreign code or a large pure
   implementation: your choice).
7. **Speed.** Votes cost the pending requests (an index of requests whose outcome is not in the
   head tree), not the state. A compressed trie, proven equal to the binary one, replaces it under
   the ledger.

What stays: cells and `take`, `quorum.bend`, `tree.bend`, `rope.bend`, codes, reach, formats, and
the judge of each change (it already works on trees).

What goes: epochs, facts, `settle`, `land`, `Line.steps`, the `Sole` premises, `Node.adopt`.

## 4. Order of work

Each step ends with every file checking.

1. Outcomes and versions in the tree (rule 2). Status and head read the tree. Facts stay for one
   step.
2. Steps as batches, heights without epochs (rules 1 and 3). Facts and epochs go.
3. The node record, `advance`, `Good` and its laws (rule 4). Laws lose their premises.
4. Missing (rule 5), then seals (rule 6), then speed (rule 7).

This replaces `shared/ledger.bend` (6.4k lines) and most proofs of `core/impl.bend`. It is not
built yet.
