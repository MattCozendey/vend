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

A Vend Store is a permanently named (writer name + writer-chosen request id) set of branches and their Vend Owner Groups sharing one history. A store can be held by many Vend Nodes, each keeping the part it uses and fetching the rest on demand, while every part is kept by enough Vend Nodes to never be lost. Content is stored once by hash and versions share every unchanged part, so an edit costs about its own size, even in huge resources; its own Vend Owner Group decides which branch and group names exist.

## Vend Writer

A Vend Writer is anyone (people, agents, tools) connected to a Vend Node under a name, reading and changing resources by request or through mounted resources (like a watched folder, whose every save becomes a version). Each change carries a writer-chosen request id, so it counts once however often and wherever it is sent; it is answered Written, Conflicted, Pending (owners not reached yet, still delivered later), Stale or Refused (both final). Writers are told only about changes to what their work uses, including everything it imports directly or not, and every read shows their own changes, even pending ones and even after switching Vend Nodes.

## Vend Owner Group

A Vend Owner Group is a composition of Vend Nodes that decide and sign the changes of a branch or of the Vend Store itself in sequence, many changes per decision, and a majority of its Vend Nodes is enough to decide. A member is a Vend Node or another Vend Owner Group, and a group's Vend Nodes are all those reachable through it, so changing a group changes the owners of everything it owns, each by its next decided step.

## Vend Branch

A Vend Branch is a sequence of versions in a Vend Store, decided by one Vend Owner Group at a time, whose history only grows at its end (never rewritten, even when moved to another point, which records a new version equal to it). Marks name, for good, the versions that matter, and any version, Vend Branch (its newest) or Vend Branch@mark can be pointed at. Merges go resource by resource, each in its own format; a conflict is stored and shared, and the merge turns Written once each clashing resource is resolved.

## Vend Version

A Vend Version is the whole content of a Vend Branch after one decided change (even when decided with others), named by that change's writer and request id, and never changed afterwards.

## Vend Resource

A Vend Resource is anything with an address (a file, a folder, a server) that may be reachable or not. Each one is read in its format: items like functions and types for code, nested formats in their own (CSS in HTML, code in Markdown, at any depth), lines for unknown text, one whole part otherwise. Diffs, merges and conflicts follow the format, a merge never loses a change made on only one side, and its imports are tracked with their conditions (like C's #ifdef) and aliases. A resource mounted to a Vend Branch takes its newest content, and what it held before is recorded as a change; mounting it to another Vend Branch is a checkout, and mounting another resource to a second Vend Branch alongside it is a worktree. A submodule is a resource that points to a Vend Branch and version of another Vend Store, served by any Vend Node that has it.