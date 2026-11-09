# Handoff

## State

- Branch `claude/dazzling-franklin-f4u2ur`. Every file checks: `src/shared.bend`, `daemon/shared/**`, `glob/impl.bend` and `core/impl.bend` print ALL PROOFS CHECK. `core/spec.bend` has 1 TODO (its law, proven in `core/impl.bend`); `transport/spec.bend` has 34 (the IO operations); `glob/spec.bend` is a spec.
- `bun run lint`: 0 findings. `git diff --check`: clean.
- Check without WSL: the `bend` on PATH can be `bun ~/.cache/bend-lint/bendlang/bend/v2.0.39/bend2/main.ts` (the Bend that lint and gen3 pin).

## Redesign (decided, not built)

A walk over history is replaced by fixed-key reads of replicated facts, so the cost of a write, read and sync does not grow with history (sync costs what differs). Every choice is judged only by the goal: strong, proven, fast, anywhere, eventually consistent, high throughput, graph based with groups, nested semantic data. Proof work is not a cost.

- Heights are 32-bit, high bit first. A line is a list of owner epochs (genesis cells); a step is the majority of the epoch's owners in its bucket; `where(i)` says where a request was decided.
- Strict finality: a sync only appends to a listing (prefix-closed, as `chain_kept` today), not per-step only.
- Versions are persistent trees in the ledger, from resource name to content. Each vote names the tree root it makes, and the next tree is a proven function of the tip tree and the request: a decided step fixes its tree, and any node can recheck it.
- Split votes: vote rounds, so a line with many owners does not stall on a split.
- Owner epochs: each read checks the whole epoch chain back (no weaker one-level check).
- Effects live in transport/IO, one adapter per resource type (file://, a server, any URI kind): each detects changes, retries and optimises in its own way (README). The core stays pure: it sees a resource only as a name (space:path) and bytes.
- Resource contents (bytes, whatever type the resource is) stored once by a hash; a collision shows as a conflict (many), never as wrong content.
- The ledger stays generic in the change type; equality is a structural is_eq per type, proven equal to code equality.
- Scope is not reduced: item-level formats for Bend and C are in scope, with everything else in README.md.
- First: experiments E1-E6 in scratch (32-bit descent and range scan; quorum over a list read once; tree get_set; flat write benchmark at 1k and 10k; visited-set reach transitivity; delta sync law), then the migration in order, each step checking.

## Compression pass (this branch)

- Shared plus core: 180.6k tokens to 167.3k (proofs 120.2k to 106.0k), with no law weakened.
- Generalized: the common end of two line lists is `List.fork` of the reversed lists (three reversal lemmas in formats); one UTF-8 case split proves both facts of a character; codes read a constructor's fields with `Code.one/two/three.read`, each with one law over `Codec(A)` bundles (encoder, decoder, round trip), so each core type's round trip is one law use per constructor; `Trie.get_set` (a read after a set, at every key) replaces `get_after_set` and makes the seen-chain record a set; `State.tip` is the tip of the chain's steps.
- Repeated proof terms are named once with lets (lets unfold in rewrite types). Tool: scratch `gen/lets.py FILE` checks each def and keeps only changes that check.
- Not done, small: merge `Quorum.yes_more`/`no_less` (one induction for both counts); `Cell.agrees_zero`/`agrees_one_side`. Not possible: merging `Fast.ask_state`/`ask_seen`, because `Seens.Inv` is a function type and cannot be used twice.

## Layout

- `src/shared.bend`: what glob and the daemon share (Eq, Bool, Maybe, List).
- `src/daemon/shared/`: the daemon's helpers: `ledger` (the replicated ledger), `formats`, `resources`, `uris`.
- `src/daemon/shared/shared/`: what those share: `text`, `trie`, `reach`.
- `src/daemon/shared/shared/shared/code.bend`: codes (values as U32 tokens with proven round trips): codecs, field readers, list/maybe/text/token codecs; equality from codes.
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
