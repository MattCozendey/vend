# Handoff

## State

- Branch `claude/dazzling-franklin-f4u2ur`. Every file checks: `src/shared.bend`, `daemon/shared/**`, `glob/impl.bend` and `core/impl.bend` print ALL PROOFS CHECK. `core/spec.bend` has 1 TODO (its law, proven in `core/impl.bend`); `transport/spec.bend` has 34 (the IO operations); `glob/spec.bend` is a spec.
- `bun run lint`: 0 findings. `git diff --check`: clean.
- Check without WSL: the `bend` on PATH can be `bun ~/.cache/bend-lint/bendlang/bend/v2.0.39/bend2/main.ts` (the Bend that lint and gen3 pin).

## Layout

- `src/shared.bend`: what glob and the daemon share (Eq, Bool, Maybe, List).
- `src/daemon/shared/`: the daemon's helpers: `ledger` (the replicated ledger), `formats`, `resources`, `uris`.
- `src/daemon/shared/shared/`: what those share: `text`, `trie`, `reach`.
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
- The equality proofs in `core/impl.bend` follow one mechanical pattern per constructor (the checker needs each pair of constructors spelled out).

## Next

1. Compress: equality from codes (encode/decode with a round-trip law) would replace the generated equality proofs and give the sync wire format; shorter rewrite motives in the ledger's Landing and Kept reads proofs; review the quorum section.
2. Speed (after compression): a snapshot fold per version instead of per-resource walks; path-compressed trie keys; lazy forms where the shaders guide asks.
3. Transport: implement the IO operations of `transport/spec.bend` (network, mounts, file watching).
