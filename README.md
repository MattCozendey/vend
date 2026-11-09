# Human Disclaimer

Only human hands may touch this file and it is the ultimate source of truth for the project. This necessarily means that any drift (be it in documentation or source code) is automatically wrong if it underrepresents the strongest versions of the claims herein declared.

# Glossary

## Vend Node

A Vend Node is a P2P decentralized versioning program that runs anywhere and syncs with other nodes bidirectionally. Vend Nodes hold:
1 - A name
2 - The parts of the Vend Stores it uses (any number)
3 - The Vend Writers connected to it (any number)
4 - The resources mounted to it, like folders (any number)

All Vend Nodes are "equal" (a classic server is just one that owns the shared branches and keeps every part); outdated ones catch up by themselves without ever creating conflicts, take in nothing unchecked (content by hash, decisions by signature), and agree once they saw the same changes. A Vend Node starts or resumes on a store address under its name (refused as Busy if another Vend Node runs there) and, unless forced, stops only with no resources mounted or writers connected.

## Vend Store

A Vend Store is a permanently named (writer name + writer-chosen request id) set of branches and their Owner Groups sharing one history. A store can be held by many Vend Nodes, each keeping the part it uses and fetching the rest on demand, while every part is kept by enough Vend Nodes to never be lost. Content is stored once by hash and versions share every unchanged part, so an edit costs about its own size, even in huge files; its own Owner Group decides which branch and group names exist.

## Vend Writer

A Vend Writer is anyone (people, agents, tools) connected to a Vend Node under a name, reading and changing resources with or without files on disk. Each change carries a writer-chosen request id, kept on retries, so sending it again to any Vend Node changes nothing more; it is answered Written, Conflicted, Pending (owners not reached yet, still delivered later), Stale or Refused (both final). Writers are told only about changes to what their work uses, imports included at any depth, and always see their own changes at once, even after switching Vend Nodes.

## Owner Group

An Owner Group is a composition of Vend Nodes that decide and sign the changes of a branch or of the Store itself in sequence.