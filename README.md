# Human Disclaimer

Only human hands may touch this file and it is the ultimate source of truth for the project. This necessarily means that any drift (be it in documentation or source code) is automatically wrong if it underrepresents the strongest versions of the claims herein declared.

# Glossary

## Vend Node

A Vend Node is a P2P decentralized versioning program that runs anywhere and syncs with other Vend Nodes bidirectionally. A Vend Node holds:
1 - Its own name
2 - The parts of the Vend Stores it uses (any number)
3 - The Vend Writers connected to it (any number)
4 - The Vend Resources mounted to it, like folders (any number)

All Vend Nodes are "equal", so a classic server can be defined as a Vend Node that owns the shared branches and keeps every part. A Vend Node that is behind catches up by itself. Catching up never creates conflicts, and a Vend Node checks everything it receives before it keeps it. Two Vend Nodes that hold the same changes give the same answers, whatever order they got them in. A Vend Node starts or resumes on a data address under its name, but only one Vend Node can run on an address at a time. Unless forced, a Vend Node only stops when no resources are mounted and no writers are connected.

## Vend Store

A Vend Store is a set of branches and their Vend Owner Groups sharing one history, permanently identified by the hash of the request that started it (so no one else can claim it) and named, for people, by that request's writer name + writer-chosen request id. A store can be held by many Vend Nodes, each keeping the part it uses and fetching the rest on demand, while every part is kept by enough Vend Nodes to never be lost. Content is stored once by hash and versions share every unchanged part, so an edit costs about its own size, even in huge resources; its own Vend Owner Group decides which branch and group names exist.

## Vend Writer

A Vend Writer is anyone (people, agents, tools) connected to a Vend Node under a name, reading and changing resources by request or through mounted resources (like a watched folder, whose every save becomes a version). Each change carries a writer-chosen request id, so it counts once however often and wherever it is sent; it is answered Written, Conflicted, Pending (owners not reached yet, still delivered later), Stale or Refused (both final). Writers are told only about changes to what their work uses in the build it declares, including everything it imports directly or not, and every read shows their own changes, even pending ones and even after switching Vend Nodes.

## Vend Owner Group

A Vend Owner Group is a composition of Vend Nodes that decide and sign the changes of a branch or of the Vend Store itself in sequence, many changes per decision, and a majority of its Vend Nodes is enough to decide. A member is a Vend Node or another Vend Owner Group, and a group's Vend Nodes are all those reachable through it, so changing a group changes the owners of everything it owns, each by its next decided step. Only the Vend Nodes of a Vend Owner Group are trusted, and only for one thing: to never sign two ballots that contradict each other for the same step. They can be offline, slow or lost, and the history stays one. Vend Writers and every other Vend Node are not trusted at all: two Vend Writers changing the same thing is just a conflict, and nothing they send is kept unless it checks.

## Vend Branch

A Vend Branch is a sequence of versions in a Vend Store, decided by one Vend Owner Group at a time, whose history only grows at its end (never rewritten, even when moved to another point, which records a new version equal to it). Marks name, for good, the versions that matter, and any version, Vend Branch (its newest) or Vend Branch@mark can be pointed at. Merges go resource by resource, each in its own format; a conflict is stored and shared, and the merge turns Written once each clashing resource is resolved.

## Vend Version

A Vend Version is the whole content of a Vend Branch after one decided change (even when decided with others), named by that change's writer and request id, and never changed afterwards.

## Vend Resource

A Vend Resource is anything with an address (a file, a folder, a server) that may be reachable or not. Each one is read in its format: items like functions and types for code (as far as the language can be read without running it), nested formats in their own (CSS in HTML, code in Markdown, at any depth), lines for unknown text, one whole part otherwise. Diffs, merges and conflicts follow the format, a merge never loses a change made on only one side, and its imports are tracked with their conditions (like C's #ifdef) and aliases. A resource mounted to a Vend Branch takes its newest content, and what it held before is recorded as a change; mounting it to another Vend Branch is a checkout, and mounting another resource to a second Vend Branch alongside it is a worktree. A submodule is a resource that points to a Vend Branch and version of another Vend Store, served by any Vend Node that has it.
# Caveats

Written by an agent at the human's request, for review. The glossary above states what Vend is to
be. This section states where the code of the branch `claude/vend-core` falls short of it. What is
not listed here is implemented in `src/vend_node/` and proven against `src/vend_node/spec.bend`,
unless marked "not checked". `HANDOFF.md` has the details.

## Whole program

- The program is a command line, `vend` (`src/main.bend`, built by `bun run build`), around the
  proven core: each command resumes the node from its data address, does one request or question
  as one writer, works until nothing changes, saves, and exits. `tools/e2e.sh` runs a scenario.
  The command line itself is not proven; it only reads and writes what the core decides.
- "Starts or resumes on a data address": a directory with the node's name, a log of its facts,
  each written once, and its parts by hash. "Only one Vend Node can run on an address": a lock
  file, made with an exclusive create; a node that crashed leaves it, and a person removes it.
- `vend <address> serve <port>` is a node that keeps running: it holds the lock, answers Syncs
  over TCP, works after each one, and watches its mounted folders, so it catches up by itself for
  what reaches it. Two nodes sync with `sync tcp:<host>:<port>`: each side sends only the facts
  and parts that the other lacks, found by one hash per fact (so a Sync still reads every fact).
  Each fact still goes in through the core, which checks it.
- Limits of the program: it serves one session at a time (a client waits at most 2 s for each
  part of a message); mount, unmount, sync and drop run only at the data address; every command
  resumes the node from its log (0.6 s at 800 writes).
- "Only one Vend Node can run on an address": the lock holds the process number; a lock whose
  process no longer runs is taken over. A third start within milliseconds of two takeovers of a
  crashed address could run a second node.
- Ballots are signed by the program around the core, not in the facts. A node's name is
  `<label>~<public key>`, so anyone checks a ballot from the name alone. A node signs each ballot
  that it casts with a hash-based signature (SHA-256 only; about 2^20 ballots per node; a
  signature is about 11.6 KB and takes about 0.2 s to make, 3 ms to check). A vote that comes from
  another node is kept only if its signature checks against the name of its voter. That an honest
  signature checks is proven (`Hyper.check_sign`); that nobody else can make one is the SHA-256
  assumption. A node never signs with one key twice while its data address is not restored from
  a copy (no fsync).

## Vend Node

A Vend Node is a P2P decentralized versioning program that runs anywhere and syncs with other Vend Nodes bidirectionally. A Vend Node holds:
1 - Its own name
2 - The parts of the Vend Stores it uses (any number)
3 - The Vend Writers connected to it (any number)
4 - The Vend Resources mounted to it, like folders (any number)

All Vend Nodes are "equal", so a classic server can be defined as a Vend Node that owns the shared branches and keeps every part. A Vend Node that is behind catches up by itself. Catching up never creates conflicts, and a Vend Node checks everything it receives before it keeps it. Two Vend Nodes that hold the same changes give the same answers, whatever order they got them in. A Vend Node starts or resumes on a data address under its name, but only one Vend Node can run on an address at a time. Unless forced, a Vend Node only stops when no resources are mounted and no writers are connected.

## Vend Store

A Vend Store is a set of branches and their Vend Owner Groups sharing one history, permanently identified by the hash of the request that started it (so no one else can claim it) and named, for people, by that request's writer name + writer-chosen request id. A store can be held by many Vend Nodes, each keeping the part it uses and fetching the rest on demand, while every part is kept by enough Vend Nodes to never be lost. Content is stored once by hash and versions share every unchanged part, so an edit costs about its own size, even in huge resources; its own Vend Owner Group decides which branch and group names exist.

## Vend Writer

A Vend Writer is anyone (people, agents, tools) connected to a Vend Node under a name, reading and changing resources by request or through mounted resources (like a watched folder, whose every save becomes a version). Each change carries a writer-chosen request id, so it counts once however often and wherever it is sent; it is answered Written, Conflicted, Pending (owners not reached yet, still delivered later), Stale or Refused (both final). Writers are told only about changes to what their work uses in the build it declares, including everything it imports directly or not, and every read shows their own changes, even pending ones and even after switching Vend Nodes.

## Vend Owner Group

A Vend Owner Group is a composition of Vend Nodes that decide and sign the changes of a branch or of the Vend Store itself in sequence, many changes per decision, and a majority of its Vend Nodes is enough to decide. A member is a Vend Node or another Vend Owner Group, and a group's Vend Nodes are all those reachable through it, so changing a group changes the owners of everything it owns, each by its next decided step. Only the Vend Nodes of a Vend Owner Group are trusted, and only for one thing: to never sign two ballots that contradict each other for the same step. They can be offline, slow or lost, and the history stays one. Vend Writers and every other Vend Node are not trusted at all: two Vend Writers changing the same thing is just a conflict, and nothing they send is kept unless it checks.

## Vend Branch

A Vend Branch is a sequence of versions in a Vend Store, decided by one Vend Owner Group at a time, whose history only grows at its end (never rewritten, even when moved to another point, which records a new version equal to it). Marks name, for good, the versions that matter, and any version, Vend Branch (its newest) or Vend Branch@mark can be pointed at. Merges go resource by resource, each in its own format; a conflict is stored and shared, and the merge turns Written once each clashing resource is resolved.

## Vend Version

A Vend Version is the whole content of a Vend Branch after one decided change (even when decided with others), named by that change's writer and request id, and never changed afterwards.

## Vend Resource

A Vend Resource is anything with an address (a file, a folder, a server) that may be reachable or not. Each one is read in its format: items like functions and types for code (as far as the language can be read without running it), nested formats in their own (CSS in HTML, code in Markdown, at any depth), lines for unknown text, one whole part otherwise. Diffs, merges and conflicts follow the format, a merge never loses a change made on only one side, and its imports are tracked with their conditions (like C's #ifdef) and aliases. A resource mounted to a Vend Branch takes its newest content, and what it held before is recorded as a change; mounting it to another Vend Branch is a checkout, and mounting another resource to a second Vend Branch alongside it is a worktree. A submodule is a resource that points to a Vend Branch and version of another Vend Store, served by any Vend Node that has it.
# Caveats

Written by an agent at the human's request, for review. The glossary above states what Vend is to
be. This section states where the code of the branch `claude/vend-core` falls short of it. What is
not listed here is implemented in `src/vend_node/` and proven against `src/vend_node/spec.bend`,
unless marked "not checked". `HANDOFF.md` has the details.

## Whole program

- The program is a command line, `vend` (`src/main.bend`, built by `bun run build`), around the
  proven core: each command resumes the node from its data address, does one request or question
  as one writer, works until nothing changes, saves, and exits. `tools/e2e.sh` runs a scenario.
  The command line itself is not proven; it only reads and writes what the core decides.
- "Starts or resumes on a data address": a directory with the node's name, a log of its facts,
  each written once, and its parts by hash. "Only one Vend Node can run on an address": a lock
  file, made with an exclusive create; a node that crashed leaves it, and a person removes it.
- `vend <address> serve <port>` is a node that keeps running: it holds the lock, answers Syncs
  over TCP, works after each one, and watches its mounted folders, so it catches up by itself for
  what reaches it. Two nodes sync with `sync tcp:<host>:<port>`: each side sends only the facts
  and parts that the other lacks, found by one hash per fact (so a Sync still reads every fact).
  Each fact still goes in through the core, which checks it.
- Limits of the program: a served node takes only `stop` from a remote writer (no other writer
  command over the wire); it serves one session at a time; a killed node leaves its lock; every
  command resumes the node from its log (0.6 s at 800 writes).
- Nothing is signed. A ballot carries the name of its voter, and the core trusts that name.
  Signatures are assumed to sit outside the core.

## Vend Node

- "Checks everything it receives before it keeps it": a node does not take a vote under its own
  name that contradicts one that it holds; it then records that its trust broke, as it does when
  it sees a second start of one store. It keeps every other fact; each reader then checks a
  ballot when it reads it.
- "Unless forced, only stops when no resources are mounted and no writers are connected": holds.
- "Two Vend Nodes that hold the same changes give the same answers": holds, proven.

## Vend Store

- "Each keeping the part it uses and fetching the rest on demand, while every part is kept by
  enough Vend Nodes to never be lost": not built. A node that takes in another node takes all of
  its requests and ballots. A node can let go only of cached content, never of a request; the spec
  requires that a request stays held with its words. Nothing counts how many nodes keep a part.
- "Content is stored once by hash and versions share every unchanged part": versions share
  unchanged files in memory, and parts are kept once by hash, on disk too. The log on disk keeps
  each request once; a vote names an earlier record instead of repeating its request.
- "An edit costs about its own size, even in huge resources": a write carries the whole words of
  the resource, not a difference. In time, each deed and answer of the core no longer grows with
  the history (measured), except a Sync, which reads every fact of the other node, and a late
  vote, a little.

## Vend Writer

- "Through mounted resources (like a watched folder, whose every save becomes a version)": a
  folder is mounted with `vend <address> <writer> mount <dir> <line> <path>`. A served node polls
  it every 500 ms, and each changed file becomes a write. Each command also reads every mounted
  file. File names with tabs or new lines are not supported.
- "Pending (owners not reached yet, still delivered later)": the core answers nothing for such a
  request (it has no Pending reply), and the command line prints "pending". The request is
  delivered by later Syncs.
- "Writers are told only about changes to what their work uses": the core answers the question
  (which paths changed among those that given paths reach through imports, in a build). Nothing
  tells a writer; there are no notices or subscriptions.
- "Every read shows their own changes, even pending ones and even after switching Vend Nodes":
  holds in the core once the other node has taken in the requests.

## Vend Owner Group

- "Decide and sign": each ballot is signed (see Whole program).
- "Many changes per decision": one request per decision.
- "A majority of its Vend Nodes is enough to decide": proven that two rounds never decide two
  things, with no assumption on who is honest. That every request gets decided is proven only in
  parts and tested with 2 and 3 nodes.
- "They can be offline, slow or lost, and the history stays one": the history stays one, proven.
  One case can leave a request undecided for good: the node whose turn it is joins the newest
  round and is then lost before its proposal reaches anyone. The fix needs a timeout, which the
  spec does not have.
- "Never sign two ballots that contradict each other": a node that does is named a liar by every
  node that sees both ballots, proven. The laws about answers then hold only for nodes that name
  no liar.

## Vend Branch, Vend Version

- Hold in the core, proven: history only grows, a move records a new equal version, marks,
  merges with stored conflicts that turn Written once resolved, the name of a version.
- "Merges go resource by resource, each in its own format": see Vend Resource for what a format
  is today.

## Vend Resource

- "Items like functions and types for code": not built. A code file is read as lines grouped into
  blocks by one simple rule for all languages. No language is parsed.
- Known formats, by file suffix: `.bend`, `.c`, `.h`, `.js`, `.mjs`, `.ts`, `.css`, `.html`,
  `.htm`, `.md`, `.module`, and whole parts for `.png`, `.jpg`, `.gif`, `.pdf`, `.zip`, `.wasm`.
  Every other file is lines.
- "Nested formats in their own (CSS in HTML, code in Markdown, at any depth)": CSS and scripts in
  HTML, and fenced code in Markdown (as lines, whatever its language). Deeper nesting was not
  checked.
- "Imports are tracked with their conditions (like C's #ifdef) and aliases": by one rule per
  format (how an import is written). Conditions exist for C only. An import reaches a whole file,
  not an item in it.
- "A merge never loses a change made on only one side": proven for the merge of the core.
- "Mounting it to another Vend Branch is a checkout", "a worktree": the core records mounts by
  address, branch and path. Nothing writes the content of a branch into a folder, so a mount only
  records what the folder holds; it is not a checkout.
- "A submodule ... served by any Vend Node that has it": a `.module` format exists; the core does
  not follow it into another store. Not built.
