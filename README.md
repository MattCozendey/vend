# Human Disclaimer

Only human hands may touch this file and it is the ultimate source of truth for the project. This necessarily means that any drift (be it in documentation or source code) is automatically wrong if it underrepresents the strongest versions of the claims herein declared.

# Glossary

## Vend Node

A Vend Node is a P2P decentralized versioning program that runs anywhere and syncs with other nodes bidirectionally. Vend Nodes hold:
1 - A name
2 - The parts of the Vend Stores it uses (any number)
3 - The Vend Writers connected to it (any number)
4 - The resources mounted to it, like folders (any number)

All Vend Nodes are "equal" (a classic server is just one that owns the shared branches and keeps every part); outdated ones catch up by themselves without ever creating conflicts, take in nothing unchecked (content by hash, decisions by signature), agree once they saw the same changes, and show their connected writers their own changes at once. A Vend Node starts or resumes on a store address under its name (refused as Busy if another Vend Node runs there) and, unless forced, stops only with no resources mounted or writers connected.

## Vend Store

Can be held by many other Vend Nodes.

## Owner Group

An Owner Group is a composition of Vend Nodes that decide and sign the changes of a branch or of the Store itself in sequence.