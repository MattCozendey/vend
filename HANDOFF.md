# HANDOFF

Checkpoint of the "compression by simplification" work. Written for an agent or a person who
continues with no other context.

## 1. Branches

| Branch | State |
|---|---|
| `master` | The start. Both feature branches are ahead of it, 0 behind. |
| `feature/refactor-4` | Last fully checked state (tip `b4fa0da`). Every entry file prints ALL PROOFS CHECK, `bun run lint` ends with `0 finding(s)`. |
| `feature/refactor-5` | `feature/refactor-4` plus the unfinished work of the agents, merged as a checkpoint. It can hold work that does not check. Section 6 states the exact state. |

## 2. The goal (the owner's words, short)

- Find what is general and move it to `src/shared`; the domains (`src/node`, `src/glob`) state fewer
  things.
- Guarantees hold by construction (design), not by many laws. One concept, one representation
  (exception: a faster form that is proven the same).
- No scope gets smaller. Fast, scalable, proven. No quadratic def on a run path.
- "Leave nothing open. Always prefer the widest, strongest statements."
- `README.md` is the canon and must stay true.

## 3. Layout now

```
src/shared/replica.bend                       generic replicated machine (code, then "# Proofs")
src/shared/shared/{ledger,tree,rope,formats,regex,search}.bend
src/shared/shared/shared/{quorum,reach,text,store,keyset}.bend
src/shared/shared/shared/shared/{trie,cell,hash,hash.test,code,seal,shared}.bend
src/node/core/{spec,impl}.bend                Vend's domain (spec: types, body-less op laws, claims)
src/node/transport/spec.bend                  spec only; its open laws are expected
src/node/shared/requests.bend                 Vend's requests and their machine
src/node/shared/shared/{resources,uris}.bend
src/glob/{spec,impl}.bend
```

The replica is generic over `~mach: Machine()`, `~kern: Kernel(mach)`, `~lawf: Lawful(mach)`.

## 4. How to check

```sh
bend <file> --check-only      # the judge; stops at the first error. replica.bend: about 40 s
bun run lint                  # must end with "0 finding(s)"
git diff --check
```

Entry files: `src/node/core/impl.bend`, `src/glob/impl.bend`, `src/shared/replica.bend`,
`src/shared/shared/ledger.bend`, `src/shared/shared/regex.bend`, `src/shared/shared/search.bend`,
`src/shared/shared/shared/keyset.bend`, `src/shared/shared/shared/reach.bend`,
`src/node/shared/shared/uris.bend`, `src/shared/shared/shared/shared/hash.test.bend`.

Facts that cost time to find:

- `bend` runs natively on Windows (the fork in `../bend`). **gen3 does not**: run it through WSL
  (`bun tools/gen3/gen3.ts prove <file> <def> --wait 60 --write`). `gen3 check` can be stale;
  `bend` is the judge. On the large files gen3 proves only small lemmas.
- Canonical format: replace `bend-lint.json` for a moment with a config that holds only
  `bend-lint-rules/layout/format`, run `bunx bend-lint 'src/**/*.bend' --fix-dangerously`, and
  restore the file byte for byte. No lint rule was ever removed.
- A "for every" hypothesis is a function, so it is affine: use it once, with the case split inside.
- A def calls only defs above it. Match a parameter, not a computed value. The shrinking parameter
  goes first.
- Git Bash heredocs break Python that holds backslashes; write scripts as files.
- Do not ask an agent to log its progress or its reasoning to a file (the owner's rule).

## 5. Done and checked (on `feature/refactor-4`)

- Core folded to `spec.bend` + `impl.bend`; no `proofs` folder; `daemon` is `node`; `src/shared` is
  layered folders.
- Replica plucked out of the core (Machine / Kernel / Lawful), with its lemmas and laws.
- Tip redesign, write-once log, O(1) wait queue, `Cast.free`, one-pass put (one SHA per node),
  root-first trees, fast `Reach` with a visited set (law `Reach.all_in`), trie module shrunk.
- **Intake check** (`Ballot.honest`, law `Seal.accept_honest`): a node refuses a pass that names the
  wrong last vote of its node, and a vote below a round that its node passed to.
- **Proof of a lie**: `Entry.Lie`, `Lie.checks`, `Lie.keep`, `Lie.detect`, `Node.liars`,
  `Notice.Lied`, `Topic.Lies`. The slot is named by the content of the lie, so two honest nodes
  never clash. Laws `Lie.keep_checks`, `Lie.checks_sealed`, `Lie.keep_named`, `Seal.accept_signs`,
  `Lie.detect_holds`.
- **Rounds safe by construction**: `Line.at_agrees` (one history) assumes only `Rounds.Last` (a pass
  names the true last vote of its node). `Rounds.Allow` and `Rounds.Same` are gone: a round decides
  a step only when a majority cast it and the proposer's vote for it is allowed (`Vote.allowed`,
  `Round.decide`).
- **Glob pluck, first part**: `regex.bend` (generic `Re<T>`, law `Re.accepts_matches`),
  `search.bend` (law `Cert.sound`), `keyset.bend`. `src/glob/impl.bend` 7,327 -> 5,720 lines; the
  five claims unchanged.
- README: the Vend Owner Group entry states who is trusted (the owner asked for the line).
- Comments in `resources.bend` and `uris.bend` no longer say that a path is '/'-separated.

## 6. `feature/refactor-5`: the unfinished work

### 6.1 Rounds follow-up (branch `worktree-agent-a4a44e5d370c90697`, merged)

Commits on top of `b4fa0da`:

- `e85d41b` Ledger: a ballot is read only as what it says. **Checked, lint 0.**
- `249cac8` WIP checkpoint (rounds). **All three files check; lint has 3 findings.**

**`e85d41b`, done.** The key of a line is any bit list (`Chain{root, sub}`), so two places can
share one slot. A read took the ballot of the slot as the ballot of the place asked for; then
`Rounds.Last` "for every line and height" is false. Now `Ballot.is(b, hk, r, n)` and
`Cell.ballot(m, hk, r, n)` (ledger.bend) check the node, the round and `Slot.height(c, h)`.
`Entry.ballot`, `Bucket.ballots`, `Bucket.decide`, `Passed.of` take `hk, r, n`; `State.bucket` and
`Ballot.many_kept` are gone. In replica.bend: `Cast.step`, `Cast.of`, `Cast.act.of`, `Cast.act`,
`Round.ballots`, `Round.hit`, `Hit.step` (new `Hit.vote`), `Hit.cast`, `Passed.up*`, `Act.up*`. No
law statement changed.

**`249cac8`, WIP.** Every def checks, no `?TODO`.

- `shared.bend`: `Nat.lt_succ_le`, `Nat.lt_before`.
- `ledger.bend`: `Spine.count`, `Spine.depth`, `State.round(s, c, h)` (the highest round of a height
  in which the ledger holds a cell); `Spine.above`, `State.round_top` (a held cell of round `r`
  gives `r <= State.round`).
- `replica.bend`: `Round.seen` is `Ledgers.State.round`. The rounds cache is gone (`rounds` field of
  `Keys`, `Rounds.at`, `Keys.rounds`, `Keys.saw`). `Ballot.first(s, b)`: the slot of `b` is empty.
  `Ballot.keeps` is fits, then first, then honest. New law `Seal.accept_first`.
- Lint, 3 findings, all `performance/unused_result` on proof binders: `ledger.bend` in
  `Spine.above` (two), `shared.bend` in `Nat.lt_succ_le`. Fix: the `expect-begin/-end
  unused_result` directive that the nearby proofs use.
- `git diff --check` was not run on this commit.

**Left, in order:**

1. **Close the WIP step.** The three directives. `State.round_top` has no user yet (step 2 uses
   it). Check comments that still speak of a round "seen" by the keys. Note: `State.add` leaves a
   full slot as it is (it does not make `Many`); before `Ballot.first` a second ballot was dropped
   while the chain moved on, now it is refused and that chain stops.
2. **`Node.Honest` and its first laws** (designed, nothing written).
   - `Node.Honest(~mach, s) = @c -> @h -> Rounds.Last(~mach, s, c, h)`. It reads only the ledger.
   - Ledger lemmas: `State.add_none` (add at an empty slot is put), `State.put_other` (a put keeps
     the other slots: `Trie.get_union`, `Shared.Maybe.join_none`), `State.keep_at`,
     `State.keep_other`, `Cell.kept` (with the slot empty, the read after `keep` is `Some{b}` when
     the slot is b's and `Ballot.is` holds, else the old read; in the first case the old read is
     `None`).
   - Core lemma: for `s2` with `State.ledger(s2) == keep(ledger s, b)`, `Ballot.first` and
     `Ballot.honest` true: `Honest(s) -> Honest(s2)`. Match `b`.
     - Pass: no vote read changes, so `Last.mine` and `Last.below` are the same (induction on the
       round). An old pass uses `Honest(s)`. The new pass: `Last.same` soundness
       (`Shared.Maybe.is_eq_sound`, the code of `Last`) and a new `Last.below.keyed`.
     - Vote: no pass read changes. A vote read at round `j` of a reader with a held pass at `r > j`
       changes only if `Ballot.is` holds; then `Passed.above(Round.seen, ...)` is true, against the
       intake. Needs a new `Passed.above_of` (induction on the bound) and `State.round_top`.
   - Laws: `Node.empty_honest`; `Seal.accept` keeps `Node.Honest`; the one-node corollary from
     `Line.at_agrees` with `u = a = b = s`, `~rules := x => t => e => honest(c)(Head.next(x))`,
     and `Grows.refl` twice ("a node never shows two histories", no assumption).
   - `Nat.lt_succ` was deleted earlier; add it again for `is_lt(p, 1n+p)`.
3. **The kernel can only add data.** Decision: by construction first; a separate premise only as
   fallback.
   - Problem: `Kernel.change` returns a `Run` with a free `Node`. Its ledger is installed at three
     sites with `State.led(s, State.ledger(s3))`: `Start.head`, `Cast.vote`, `Advance.moved`.
     `Lawful.Grows` only says that it grows. So a kernel could write a ballot.
   - Wanted: the kernel can only add content-named data (`State.add_data`, `State.add_datas`, the
     `Stores` interface), and the replica applies it. Then "a run keeps the ballots" is one lemma.
   - Not checked yet: what the Vend kernel in `impl.bend` writes (`Replicas.Work.after`,
     `Set.grows`, `Verdict.after`, `Made.after`, `Run.after`). Expected: only data through
     `Work.set`, `Work.keep`, `State.put`.
   - Ruled out: grafting the node's ballot region back at install (the proofs move tree reads from
     `s3` to the installed node through `Node.grows(s3, x)`, which fails if the kernel added a
     cell); putting the frame into `Lawful` (every law with `~lawf` gets formally weaker).
   - Fallback: a premise `Kernel.Frames` apart from `Lawful`, with a Bool relation "same ballots"
     (`State.grows` both ways on `State.under(ledger, [False, True])`), and about 25 lemmas in
     `impl.bend`.
4. **`Plan.lead` proposes only an allowed vote** (not started). Today an owner that votes against
   the proposer makes later passes name two votes of one round; then no vote with those passes is
   allowed and the height waits for ever. `Plan.lead` must pick `from`: a majority of owners whose
   passes it holds and for which `Vote.allowed` holds of its proposal (drop a pass that names
   another vote of the top round). Law `Plan.lead_allowed`, same shape as `Plan.follow_allowed`.
   Do it before step 5, so the frame lemma of `Plan.lead` is written once.
5. **Every deed of `Node.after` keeps `Node.Honest`.** About 40 frame lemmas for defs that keep no
   ballot, about 35 `Honest` lemmas for defs that call `Seal.accept`. Ledger writes outside
   `Seal.accept`: `put_datas`, `add_datas`, `put_data`, `ask`, the put of a lie, `State.take` of
   `Node.reads(t)` (asks and data only), the three run installs. Use the Bool relation of step 3
   (`Trie.all2_of_get` backward, `Trie.all2_under` forward); sub-trie equality after a union is
   hard.
6. **Own-ballot law.** Provable: the ballot of `Pass.to` and of `Cast.put` is `Ballot.first` and
   `Ballot.honest` where it is sealed. Not provable: `Seal.fits` (the key that the store holds for a
   node is content of the store; nothing ties it to the node's seed).
7. **Delete `Advance.head.grows`** (no user).

**Pitfall, still open:** a store member can craft a line key so that its ballot fills the slot of
another node's ballot. With `Ballot.first` that other ballot is refused. Safety holds (checked
reads); liveness does not. The real fix is a prefix-free code of the line key in the slot.

### 6.2 Glob follow-up (branch `worktree-agent-a7a0b163b6abfad50` and helpers)

**The agent's handoff had not arrived when this file was written. This part is from its last status
message and from what the worktrees show; it is not verified.**

| Item | State |
|---|---|
| 1. One matcher: the spec states matching through `regex.bend`; the spec's own matcher is gone | Reported done and checked (`7534766`): spec 481 lines, impl 5,168, the five claim statements byte-identical. |
| 2. Classes as intervals (no expansion of a range to a list; membership by comparison) | In work: a helper writes a generic span module with a representative law. The glob side (type, read, show, escape, alphabet) is not started. |
| 3. Speed | Baseline only (below). Profiling not started. |
| 4. Leftovers (`Reach.or_false`, `Reach.or_assoc`, `Rule.selects.fast`) | In work (a commit "Glob, Reach: delete defs that nothing calls and copies of shared lemmas" exists in a helper worktree). |
| 5. Absent over valid paths (the path automaton proven equal to `is_path`, the certificate on the product) | In work in a helper worktree. |

Compiled baseline (JavaScript from `bend -o`, run with node), old search against new:

| Query | Old | New |
|---|---|---|
| small, found | out of memory | 235 ms |
| small, absent | 215 ms | 198 ms |
| mid, found | out of memory | 475 ms |
| mid, absent | 402 ms | 334 ms |
| large, absent | 15,138 ms | 1,068 ms |
| large, found | not run | 1,462 ms |

Known and unchanged: `src/glob` is a glob for file-system-style paths only. Nothing in `src/node`
imports it and the README does not name it (the owner does not want a README entry).

### 6.3 Not started (the coordinator's own steps)

1. After 6.1: make the README sentence of the Vend Owner Group entry say exactly the assumption
   that the final laws need. Target: "an owner never signs two different ballots for the same
   position of its own chain". Today's sentence ("never sign two different decisions for the same
   step") is close.
2. Run the review skills on everything since the last review, in this order, and repeat until they
   find nothing: `thermo-nuclear-code-quality-review`, `cyclomatic-complexity`, `erasure`,
   `bun run lint`.
3. Final report to the owner: how much smaller the proven area is (lines, claims, laws, what each
   law now assumes), and an honest list of what is not done.

## 7. Known limits (say them, do not hide them)

- One history across nodes still assumes `Rounds.Last` of a node that holds both ledgers. Per node
  it becomes a proven invariant only when 6.1 steps 2, 3 and 5 are done.
- One lying owner can break one history (majority quorum). A lie is recorded and told
  (`Node.liars`, `Notice.Lied`), not prevented. A two-thirds quorum is a different, slower product.
- SHA-256 and the one-time signature are assumed unbroken.
- `Advance` runs a decided step again before it keeps it (the README: a node checks everything).
- Tree and rope builders hash each node once more to link.
- `src/node/transport/spec.bend` is a spec with open laws.
- An `expect` directive on `Holds.led` was added by an agent; its reason is not verified.
