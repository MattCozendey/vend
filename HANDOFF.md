# Handoff

This file states what must hold, and the types and defs that make it hold. It does not say how to
build anything: a better implementation is free to exist, if the invariants hold.

## State

Check a file with `bend <file> --check-only`. Every file type-checks. Nothing was proven in the
last rounds: the work was to state laws and to construct types.

| File | Result |
| --- | --- |
| `src/shared/shared/shared/pack.bend` | 2 open laws |
| `src/shared/shared/rope.bend` | 1 open law |
| `src/shared/shared/formats.bend` | 1 open law |
| Every other file under `src/shared` but `replica.bend` | ALL PROOFS CHECK |
| `src/shared/replica.bend` | 3 open laws |
| `src/node/core/spec.bend` | 6 open laws (and the ones that it imports) |
| `src/node/transport/spec.bend` | 33 IO declarations, no implementation |
| `src/glob/impl.bend` | ALL PROOFS CHECK |

There is no implementation of a ledger, of a replica or of Vend's kernel. They are stated as records
(below).

## How correctness is built in

1. **An interface is a record that holds its own laws.** A value of the record type is a proof. The
   repo already did this for `Codec`. It now does it for:
   - `Ledgers.Ledger(Q, c)`: `Ledger.Kind` (the operations) and `Ledger.Laws`.
   - `Replicas.Kernel(mach, d)`: what a request does, and `Kernel.Stable`.
   - `Replicas.Replica(mach, d, kern)`: `Replica.Kind` (the operations) and `Replica.Laws`.
   - `Core.Kernel(d)`: a kernel of Vend, and `Kernel.Rules`.
2. **Every answer is a read of a ledger.** `Replicas.Line.head`, `Line.at` and `Line.get` are pure
   defs over a ledger. Every `Core.Node.*` read is a pure def over them. No answer reads the state
   of a replica. So two nodes that hold the same entries give the same answers.
3. **An entry is under the name that its content gives it.** `Ledgers.Entry.name` is the kind and
   the hash. A step names its requests by hash (`Step.asks`). The root of a line is the hash of the
   request that started it (`Line.root`).
4. **A request ID names one request for good, and the owners decide which.** The log holds, for an
   ID, the hash of the entry that got the outcome (`Replicas.Out`). Another entry with that ID is
   `Refused` on every node.
5. **A kernel gives an act, not a state.** `Replicas.Act` is data to add and a result. A kernel
   cannot change a log, a ballot or a request.
6. **A log only gains keys.** `Replicas.Run.add` is the one def that writes a log, and it refuses a
   key that the log holds.
7. **No rule reads another line.** A rule of Vend reads the ledger and the tip of its own line. The
   content of another line comes with the change, as `Requests.Source`: the root of a tree, and the
   version that it is said to be of. So the history of a line never depends on the history of
   another line, and `Kernel.Stable` needs no premise about ballots.
8. **Vend's kernel is one def.** `Core.Ask.act` says what every request does. `Kernel.Rules` is
   one equation: the kernel does what `Ask.act` says. What a node asks by itself is `Own.due`.
9. **The owners keep each part of what they decide.** A rule waits until the ledger holds the bytes
   and the trees of its result (`Root.held`, `Tree.kept`). A replica holds what its votes run
   (`Replica.Runs`).
10. **Trust is two defs.** `Replicas.Led.Single` (one vote at a place, one pass to it) and
    `Replicas.Rounds.Last` (a pass names the last vote). `Led.Honest` is both. No law assumes more.
11. **A resource carries its format.** A resource is `Requests.Res`: the hash of its format,
    which the ledger holds as data (`Formats.Format.code`), and the root of its bytes. No node
    reads a format from a name. `Formats.Format.guess` only suggests one to a front.
12. **An import keeps what it asked for, and states what it brings.** `Formats.Import` is the
    edge as written (`asked`), what it brings (`Brings`: the named items, the whole target, or
    the whole target and all that it brings) and how its target is found (`Find`). A language
    can make imports with no line (`Format.Code.implicit`). `Resources.Name.candidates` turns a
    target into names, in the order that the language looks.
13. **A key signs one ballot.** `Replicas.Key.secret` is a hash of the seed of a replica, the root
    and the number of the ballot. A replica keeps only its seed.

## What must be built

Each item is a value of a record type. Its laws are the fields.

### A ledger: `Ledgers.Ledger(Q, c)`

A ledger is what `Kind.get` gives. The laws state each other operation by it.

| Law | It says |
| --- | --- |
| `Laws.GetEmpty` | A ledger that holds nothing gives nothing. |
| `Laws.GetAdd` | A ledger with one more entry holds what it held, and the entry when its name was free. |
| `Laws.GetNamed` | An entry is under its own name. No data is under a hash that it does not match. |
| `Laws.AddComm` | Two entries that do not clash give the same ledger in either order. |
| `Laws.AddTwice` | An entry added twice is added once. |
| `Laws.Missing` | A sync sends each entry that the other ledger lacks, and no other. |
| `Laws.Ballots`, `Laws.Asks` | The ballots at a place, and the requests of an author, are exactly those that the ledger holds. |
| `Laws.Rounds`, `Laws.Heights` | No ballot is above the bound, and the bound is the round or the height of a ballot that the ledger holds, or 0. |
| `Laws.LiarsSound`, `Laws.LiarsComplete` | A voter is a liar exactly when the ledger holds a proof against it. |

Cost, stated on each operation: a read costs one name, a sync costs what differs.

### A replica: `Replicas.Replica(mach, d, kern)`

| Law | It says |
| --- | --- |
| `Laws.Empty`, `Laws.Keeps` | The name, the seed and the consents of a replica change only as a deed says. |
| `Laws.Grows` | A replica never loses or changes an entry, whatever it does. |
| `Laws.Good` | An empty replica is good, and a good replica stays good. The parts of good are below. |
| `Laws.Takes` | An entry that a deed brings, that checks, and whose name is free, the replica then holds. |
| `Laws.Detects` | A replica that sees two ballots signed with one key names the voter a liar. |
| `Laws.Passes` | A replica that passes on a line is then in a higher round. |

The parts of `Replica.Good`:

| Part | It says |
| --- | --- |
| `Led.Honest` | Its ledger holds one vote of a voter at a place and one pass to it, and each pass names the last vote. |
| `Led.Sound` | It holds only ballots that a key of the voter's chain signs, and only proofs that are proofs. |
| `Replica.Runs` | It can run each step that it voted for, and holds what the run adds. It voted for a change of who decides only when a client asked it. |
| `Replica.Asks` | It holds the request that the kernel says to ask for each line. |
| `Replica.Follows` | In the round that it is in, it holds its vote for the step of the voter whose turn it is, when the rules allow the step and it can run it. |
| `Replica.Leads` | When the turn is its own, it holds a vote of its own: in the first round when a request waits, in a later round when the rules allow a step that it can run. |

`Follows`, `Leads` and `Passes` hold for a replica that is a voter of the line and has a key under
its root (`Replica.Keyed`).

### Vend's kernel: `Core.Kernel(d)`

`Kernel.Stable`: an act stays as the ledger grows.

`Kernel.Rules`: the kernel does what `Ask.act` says, and asks what `Own.due` says. `Ask.act` sends
each change to its rule, on the line where it belongs, and refuses any other.

| Change | Def that is its meaning |
| --- | --- |
| Write | `Write.act`: taken when the resource holds what it held at the base, else stale. |
| Resolve | `Resolve.act`: while the clash is open, the resource holds the content and the clash is shut. |
| Merge | `Merge.act`: each resource that the two sides hold differently gets `Pick.merge`: theirs when ours is the base, ours when theirs is the base or both agree, else both merged in their format. Two sides in two formats clash. A submodule takes the pointer with the higher number on one branch (`Pointer.newer`). A clash keeps ours and puts the resource among the open clashes of the merge. |
| Move | `Move.act`: the content is the tree of the target, the same tree. |
| Mark | `Replicas.Act.Label`: a label on the newest version, for good. |
| Branch | `Branch.act`: the store opens the branch, empty or with the tree of its source. |
| Group | `Group.act`: the tree of the store holds the members; a group that would reach itself is refused. |
| Own | `Own.act`: taken when the owners are the nodes of the group (`Group.nodes`), and there is one at least. The line records its owner group. |
| Key | `Key.act`: the store holds the first key of a node. |

## Open laws

| Law | It says |
| --- | --- |
| `Packs.Pack.read_pieces` | Packed pieces read back as their bytes. |
| `Packs.Pack.words_unpack` | Words as bytes pack back to the words. |
| `Ropes.Rope.cut_with_flat` | The pieces of a cut by content, one after the other, are what was cut. |
| `Formats.Format.code_read` | A format reads back from its code. |
| `Core.Pointer.code_read` | A submodule pointer reads back from its code. |
| `Replicas.Line.at_grows` | One history: the tip of a line after k steps stays as the ledger grows, while the ballots are honest. |
| `Replicas.Line.get_grows` | What a log holds under a key, it holds for good. Outcomes, versions, marks and branch starts are each one key. |
| `Replicas.Step.run_outs` | A step gives each of its requests an outcome. |
| `Core.Node.answer_follows` | Answers only move forward: Stale and Refused are final, a taken change stays taken. |
| `Core.Merge.act_takes` | A merge never loses a change that only one side made: where the pick takes one side, the tree of the merge holds it. |
| `Core.Merge.act_clashes` | Where the pick clashes, the tree of the merge holds ours, and the clash is open. |
| `Core.Node.affects_holds` | Each touch that `Node.affects` gives holds (`Touch.holds`). |
| `Core.Node.affects_complete` | Each touch that holds is among the touches that `Node.affects` gives. |

## README, sentence by sentence

| README | Where it holds |
| --- | --- |
| Catching up never creates conflicts; a node checks what it receives | `Laws.Grows`, `Laws.Good`, `Laws.GetNamed` |
| Same changes, same answers, whatever the order | Item 2 above, with `Laws.AddComm` |
| A node stops only when nothing is mounted and no writer is connected | `Core.Node.may_stop` (a def) |
| A store is identified by the hash of the request that started it | `Ledgers.Line.root` |
| Content is stored once by hash; an edit costs about its own size, even in huge resources | `Laws.GetNamed`; `Ropes.Rope.of_bytes` cuts bytes by their content, in text and in any other bytes; trees and ropes share nodes |
| Each part is fetched on demand, and kept by enough nodes | `Laws.Takes`; item 9 above |
| The store's owner group decides which branch and group names exist | `Ask.act`: Branch, Group and Key are changes of the store line only |
| A change counts once, however often it is sent | `Laws.AddTwice`; a step skips an ID that has an outcome (`Step.fresh`) |
| Written, Conflicted, Pending, Stale, Refused | `Core.Node.answer` (a def), `Node.answer_follows` |
| Pending is still delivered later | `Replica.Follows`, `Replica.Leads`, `Laws.Passes` |
| Writers are told only about changes to what their work uses | `Core.Touch.holds` (a def), `Node.affects_holds`, `Node.affects_complete` |
| Every read shows the writer's own pending changes, at every node | `Core.Node.read` reads `Draft.newest` first; it is a read of the ledger |
| A majority decides, in sequence, many changes per decision | `Round.decide`, `Line.next`, `Step.run` |
| A group's nodes are all those reachable through it | `Core.Group.nodes`, by `Reaches.Graph.reach` |
| A change of a group changes the owners of what it owns | `Core.Own.due`, `Replica.Asks` |
| The history stays one | `Line.at_grows` |
| Nothing a writer sends is kept unless it checks | `Laws.Takes`, `Laws.Good` |
| History only grows; a version never changes; marks are for good | `Line.get_grows` |
| A move records a version equal to its target | `Move.act` |
| Each resource is read in its format; nested formats at any depth | `Requests.Res`, `Formats.Format` |
| Imports are tracked with their conditions and aliases | `Formats.Import`, `Core.Res.imports` |
| Merges go resource by resource, each in its own format | `Merge.act`, `Pick.merge` |
| A conflict is stored; the merge is Written once each clash is resolved | `Key.clashes`, `Resolve.act`, `Answer.merged` |
| A merge never loses a change made on only one side | `Merge.act_takes`; inside one resource, `Formats.Plain.merge.cuts` applies both changes or clashes |
| What a mounted resource held before is recorded as a change | `Core.Mount.change` (a def) |
| A submodule points to a branch and version of another store | `Core.Pointer`, `Pointer.code_read`, `Pointer.newer` |
| Mounting to another branch is a checkout; another resource on a second branch is a worktree | `Core.Mounts`: one branch for each resource |

## What is still not stated

1. **The claim of a source.** `Requests.Source` carries a tree and names the version that it is
   said to be of. No rule checks the claim, and none needs it for one history. A false claim gives a
   writer nothing that writes cannot give. A front must send true claims, and the base of a merge
   must be the newest version that both sides came from. Neither is stated.
2. **Consent to what a node asks by itself.** `Own.due` is a change of who decides, so a replica
   votes for it only when a client asked (`Replica.Runs`). The front of a node is that client: it
   checks `Own.due` and consents. This is decided, and not a law: a replica that consents by itself
   would have to trust a tree of another line.
3. **IO.** One node per address, mounts, checkout, worktree and the service of submodules are IO
   declarations in `transport/spec.bend`. A law cannot state them.
4. **A search that answers.** `Glob.Query.search` may answer `Unknown` for every query.


## Structure, laziness and parallel work

No law fixes how a ledger, a replica or a kernel is kept: each is a record, and any value of it
is lawful. No cache is stated. A cache comes later, on these structures, and must be proven equal
to the def that it stands for.

Structure that is decided:

1. **Content is packed and cut by its content.** A rope holds pieces, each packed four bytes in a
   word (`Packs.Pack`), cut at line ends and where the state of the bytes before says so
   (`Ropes.Gear`). The formats still work on a list with one byte in each element, for the time
   of one merge or diff.
2. **The open clashes of a merge are one key** (`Core.Key.clashes`). What a merge left is one
   read, not a walk of a tree.
3. **What touches a branch reads each thing once** (`Core.Branch.touches`): the resources of the
   branch, their imports turned round into one graph of users, and the history of the other
   branch.
4. **A choice runs only its chosen side.** Each branch of a rule is a thunk (`Shared.Bool.when`,
   `List.all.if`, `Draft.or`, `Touches.when`). A rule checks the cheap condition first.
5. **Parallel work is in the trees.** A trie forks at each node, and a tree goes 16 ways: these
   are balanced. The new defs fold lists, and a fork on a list is not balanced, so they do not
   fork. A merge reads its picks one after the other: to fork them, the differences of two trees
   must come as a tree, not as a list.

Defs that state a meaning, and are slow by design. A cache or a faster structure must equal each:

| Def | Its cost | What a faster one needs |
| --- | --- | --- |
| `Replicas.Line.head` | It runs a history from its start. | The head of each line, kept by a replica. |
| `Core.Tree.kept` | It walks a tree and reads each resource. | To know which trees a ledger holds whole. |
| `Core.Group.nodes`, `Tree.resources`, `Node.branches`, `Import.under` | Each lists a tree. | A tree for each kind of key (limit 6). |
| `Core.Node.affects` | The history of each other branch. | A mark of how far a reader is. |

Two concepts that have two representations, to unify when their proofs are open again:

1. `Ropes.Rope.cut` is `Ropes.Rope.cut.with` with no state.
2. `Core.Pick.merge` and `Formats.Merge.decide` are the same three-way rule (theirs, ours, both),
   on resources and on bytes.

## Limits

Ask about these before any implementation. Each is a cost or a risk of the design, with what is
now stated for it.

1. **A node lets go of data only as the laws allow.** Stated: `Ledgers.Laws.Drop`,
   `Replicas.Deed.Drop`, `Replicas.Laws.Drops`. A node keeps every request, proof of a lie and
   ballot of its own, and all that the lines it votes on rest on. All else may go, and a read
   then gives the same answer or none (`Line.get_grows`).
2. **A node never signs twice with one key.** Stated: `Replicas.Laws.Count`. The count of its
   ballots under a root never falls, and each of its ballots has its own number. Not stated, and
   an IO rule: a node keeps its count where it keeps its data before a ballot leaves it.
3. **A new node replays the history of each line that it uses.** No checkpoint: a checkpoint
   would trust owners for more than README does. A line is replayed when it is first used, and
   lines replay apart and in parallel, since no rule reads another line.
4. **A ballot holds a seal of 67 hashes** (about 2 KB). Batches divide the cost; a node that is
   not an owner of a line may let go of its ballots (limit 1). Signing a byte for each chain
   instead of 4 bits halves the size, at about 9 times the hashing.
5. **The ledger's map is free** (`Ledger.Kind`). It must not be the proven `Trie`, which keeps a
   key as a list of bits. The best known one: a map that splits the 256-bit name by words, with
   a hash in each node, so a sync compares hashes and costs what differs (`Laws.Missing`).
6. **The content tree has no range and no delete.** Not done. The best known structure is a
   tree sorted by key and cut by content (a prolly tree): one root for one content in any order
   of writes, shared nodes, ranges, delete and fast diff. It is a rope of sorted bindings, so it
   unifies with `Ropes`. The replica uses `Trees.Tree` directly: the next step is a record for
   the tree, as for the ledger, and a prolly tree that fills it.
7. **Conditions are read through a view.** Stated: `Formats.Cond.holds`, `Formats.Import.holds`;
   `Core.Topic.Affects` carries the view of a subscription. A test that the view does not name
   holds, so no use is missed. Conditions are matched as written: no expression is evaluated.
8. **Use is tracked per item, once a format splits items.** Stated: `Formats.Item` (name, bytes,
   uses), `Formats.Format.items`, `Formats.Edge.names`, `Formats.Import.pool`. No format splits
   yet: each gives the whole resource as one item, and no rule reads the names that an import
   asks for. The core still tracks per resource. A language that cannot be read without running
   it (a dynamic import) must count as using all.

## Points for the owner of README

1. A language finds the target of an import as `Formats.Find` says. A space whose names have
   no parts has no names but whole ones. README does not say how a target becomes a resource.

## Proven and kept

`shared`, `code`, `hash`, `seal`, `cell`, `trie`, `depot`, `text`, `spans`, `keyset`, `quorum`,
`reach`, `regex`, `search`, `rope`, `tree`, `formats`, the types and codes of `ledger`, `requests`,
`resources`, `uris`, and `glob`.
