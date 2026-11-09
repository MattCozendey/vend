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

### Ledger v2, concrete (shared)

- Built (`daemon/shared/ledger2.bend`, all checks): operations (keys, structural equality, state and sync, ballots read once, epochs from checked facts, tip by `Trie.top`, `where` checked on read, status, node ask with facts settled) and laws: equality laws, sync laws (comm, assoc, idem, missing_join), `decide_grows`, `decided_grows`, `status_grows`, `refused_kept`, `ask_grows` (a node's write only grows its state), `ask_holds`, `ask_decides` (a sole owner decides at once). Kept laws are stated under growth (`State.grows`, a Bool: every cell kept), and `State.grows_join` makes every sync that agrees a growth, so one law covers syncs and node writes.
- Shared: `shared/quorum.bend` (majority, else most votes once all are cast; laws), `shared/cell.bend` (cells, agreement, growth: refl, trans, join, `grows_get`, `read_grows`), `shared/shared/trie.bend` (moved down; `Trie.top` with `top_ok`/`top_max`, `Trie.get_set`), `shared.bend` (`Maybe.then`/`Maybe.when` with kept laws, `Maybe.laws`).
- Measured (native, sole owner, one line, judge always takes): 1,000 writes 0.23s, 10,000 writes 2.26s: about 226us per write at any length (old: 8.2ms per write at 1,000 and growing). Bench: scratch `bench/v2.bend`.
- Trust model (decided: B, Merkle): data is held under its SHA-256 hash (`shared/shared/shared/hash.bend`, tested against hashlib in `hash.test.bend`) and read only when it hashes to its key (`State.data_hash`). Each vote carries the hash of what its line holds after the step (`Vote.result`); the judge gets the head vote (`Line.head`) and returns a `Verdict{takes, result}`.
- Version trees (built, `daemon/shared/tree.bend`, all checks; generic over a store `~fetch: S -> Hash -> Maybe<List<U32>>`): a Merkle map from key words (a resource name's code) to value words, 16-way by the nibbles of the key's SHA-256 (a path: 64 Nat nibbles, highest first), a leaf as soon as a subtree holds one key, so depth is about log16 of the size. A tree is named by its root, a `Maybe<Hash>` (none: the empty tree), as each part of a branch is. Nodes are codes: leaf `[1, key, value]` (lengths first, `Code.words`), branch `[2, parts]` (each a hash or none, no empty part at the end: `Parts.put` trims); `[0]` is the empty node, what an empty part reads as, never stored. One code per node: a read refuses any other code (tags other than 0/1/2, count and value tags other than 0/1, a branch with an empty last part), and `Node.words_of` proves the node read from some words has those words (read-then-write laws `Code.Back` in code.bend for tokens, counts, values, items, lists, words; and for hashes, parts, nodes). `Tree.get` descends by nibbles (`Tree.get.go`, structural, no fuel). `Tree.set` gives the new subtree (`Put`: root and new nodes; the caller puts them as data), or none when the store does not hold a node on the key's path or the key's whole path is another key's (a SHA-256 collision): a write never drops a subtree. A split puts the old part's own reference into the new branch. Laws: `Node.of_words` (decode after code, for a node in its one code: `Node.ok`); `Node.words_of` (code after decode); `Tree.get_set` (after a set, the key reads as its new value in any store that holds the new nodes: `Tree.holds`, a Bool); `Tree.get_other` (another key reads as before, in a store that grows from the old one and holds the new nodes); `Tree.get_grows` (a read stays as the store grows); `Tree.set_some` (a set fails only on a missing node or a collision: `Tree.set.ok`). Growth is a template pair (`~grows`, `~kept: Tree.Keeps`), which the ledger's `State.grows` and `State.data_grows` fill. Ledger v2's `Vote.result` is the root, a `Maybe<Hash>`. Next for trees: the order-free law (same keys give the same root: sets of different keys commute, a second set of a key overrides the first). Measured (native, 1,000 / 10,000 set+get): about 0.6s / 9.5s (noisy machine); 64 nibble conversions per path cost about 4%.
- Then the core (plan): one tree per version of a line holds the whole state of the line, in key spaces (a tag before the key): resources (a name's code to its bytes), marks (a mark to the version and message), members (of a group line), open conflicts (a merge's clashing resources, until resolved), the version vector (each line to its newest height that this version came from), and imports (a resource to what it imports, from its format, at write time). Each change kind gives the next tree from the head's: write/resolve set a resource (a write is stale when the resource at the head differs from at its base: two tree reads); move takes the target's root; make takes `at`'s root (or the empty tree) and sets members; merge reads the base from the version vectors (the newest version of ours that `from` came from), lists the keys of the three trees, picks each resource three-way, sets the picks and the open conflicts, and joins the vectors; mark/members set their keys; own changes the epoch, not the tree. The judge computes the result root, and the nodes it adds go to the ledger with the vote (a `Verdict` carries them; the ledger puts them as data). Reads: content and marks are tree reads at a version's root (`State.decided` gives the vote, its result the root); a log walks the line's versions (a ledger listing of a line, by heights within epochs) and compares the resource before and after; ancestry is one vector read. Needed first: the ledger listing (with the strict-prefix law), verdicts that carry nodes, a tree key listing (`Tree.keys`, with a law: a key is listed exactly when it reads); then the core over these, `write_written` re-proved; then delete `ledger.bend`, rename `ledger2.bend`.
- Not yet: the strict-prefix listing law (spec listing by heights, cut at owner changes; fast tip = spec tip when every decided height has its predecessor decided); the core on v2 (then delete `ledger.bend` and rename); delta sync; visited-set reach; item formats for Bend and C; transport.

- Slots (bit keys, prefix-free): `ask(i)`; `vote(c, e, h, n)` = votes ++ chain key ++ 32-bit epoch ++ 32-bit height (high bit first) ++ node text; `genesis(c, e)`; `where(i)`.
- A vote carries the request's View, so a decided step needs no lookup of its request.
- Decide rule per bucket (c, e, h): the majority of the epoch's owners; else, once every owner voted (an owner that voted twice counts as voted, with no value), the most voted, ties by the smallest code. A pure function of the bucket: it only gains information as votes arrive, so a decision never changes, and a split no longer stalls a line whose owners all vote.
- Strict prefix: the listing of a line is the longest run of decided heights from 0 (spec). The fast tip is the highest decided height, found by descending the height bits; law: when every decided height above 0 has its height before decided (true for every state that honest owners make, since an owner votes at h only after h-1 is decided), the fast tip is the spec tip. Sync then only appends to a listing.
- `where(i)` and `genesis(c, e)` are facts any node may write; a read checks each against the bucket it names (O(owners)), so a wrong fact is never believed, only ignored.
- Measured (100k entries, native): building a ~390-bit key from text 7.8us; one trie op at ~390 bits deep ~15us; with 64-bit keys ~7us per op including the key. Plan: fixed-width fields now; later a path-compressed trie proven equal to the binary trie (fast/slow law pair), about log2(entries) hops.

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
