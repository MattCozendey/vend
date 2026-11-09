# Handoff

## State

- Branch `claude/dazzling-franklin-f4u2ur`. Every file checks: `src/shared.bend`, `daemon/shared/**`, `glob/impl.bend` and `core/impl.bend` print ALL PROOFS CHECK. `core/spec.bend` has 1 TODO (its law, proven in `core/impl.bend`); `transport/spec.bend` has 34 (the IO operations); `glob/spec.bend` is a spec.
- `bun run lint`: 0 findings. `git diff --check`: clean.
- Check without WSL: the `bend` on PATH can be `bun ~/.cache/bend-lint/bendlang/bend/v2.0.39/bend2/main.ts` (the Bend that lint and gen3 pin).

## Layout

- `src/shared.bend`: what glob and the daemon share (Eq, Bool, Maybe, List).
- `src/daemon/shared/`: the daemon's helpers: `ledger` (the replicated ledger), `formats`, `resources`, `uris`.
- `src/daemon/shared/shared/`: what those share: `text`, `trie`, `reach`.
- `src/daemon/shared/shared/shared/code.bend`: codes (values as U32 tokens with proven round trips); equality from codes.
- Import rule: `.agents/skills/experimental-bend-spec/SKILL.md`, Folder structure.

## Design (ledger + core)

- A ledger holds requests and votes in one trie of cells; a sync is a join (State.join_comm, join_assoc, join_idem, missing_join).
- A chain is the list of steps its owners decided; each step takes a request or refuses it as stale. A vote's bucket is its height, so a chain is a walk of a trie, with no fuel.
- A store is a root chain (Ask.start); its owners make its branches and groups (Change.make), so a name is made once.
- Laws: State.chain_kept, status_kept and refused_kept (finality), State.ask_decides (a sole owner decides at once), State.ask_holds; Node.write_written in the core. Every other read (content, merge, conflict, groups, affects, impact, notices) is a def in `core/spec.bend`.

## Decisions taken in this pass

- A creation race cannot replace a chain: creations are decided on the store's chain.
- Stale and Refused are final: owners vote a verdict, once.
- set-owner takes the nodes of a group as it is when the request is made: the owners of the next step must come from the line's own past, or two majorities could disagree.
- Defs in the spec are the spec; laws that restated a def are gone (bend2 skill, Laws that matter).
- Two requests are the same exactly when their codes are; the round-trip proofs in `core/impl.bend` follow one pattern per field.

## Speed (native build, sole owner, one branch)

- Bench: build a `main() -> IO(Unit)` that imports `core/spec.bend` and `core/impl.bend` (the spec has an open law) and run `bend x.bend -o x`.
- 200 writes of one file: 0.57s; 200 writes over 10 files: 0.96s (was 2.6x slower before the step-list content walk and 9-bit keys).
- A request still walks its chain once (about 6 microseconds a step); removing that needs a cache of decided steps (not started, by request).

## Next

1. Transport: the IO operations of `transport/spec.bend` in Bend (TCP, files, `IO.fork`): tokens to bytes at the socket, codes for the messages and for a ledger's entries, a store file, sync by `Node.missing`.
2. Compress: shorter rewrite types in the ledger's Landing and Kept reads proofs (lets unfold in rewrite types; `%e : P` needs `e : a == b` with the goal holding `b`).
3. Speed: a decided-steps cache, once wanted; the quorum count reads each owner's vote three times.
