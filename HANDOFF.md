# HANDOFF

Checkpoint of the "compression by simplification" work. Written for an agent or a person who
continues with no other context.

## 1. Branches

| Branch | State |
|---|---|
| `master` | The start (`ec7c3fd`). |
| `feature/refactor-4` | An older fully checked state (`b4fa0da`). |
| `feature/refactor-5` | Tip `36aa821`. Every entry file prints ALL PROOFS CHECK, `bun run lint` ends with `0 finding(s)`, `git diff --check` is clean. |
| `claude/vend-refactor-5-u8119r` | The working branch of the last agent; same tip as `feature/refactor-5`. |

## 2. The goal (the owner's words, short)

- Find what is general and move it to `src/shared`; the domains (`src/node`, `src/glob`) state fewer
  things.
- Guarantees hold by construction (design), not by many laws. One concept, one representation
  (exception: a faster form that is proven the same).
- No scope gets smaller. Fast, scalable, proven. No quadratic def on a run path.
- "Leave nothing open. Always prefer the widest, strongest statements."
- `README.md` is the canon and must stay true. Its line 3: only human hands change it, and code or
  docs that state less than its strongest claims are wrong.

## 3. Layout

```
src/shared/replica.bend                       generic replicated machine (code, then "# Proofs")
src/shared/shared/{ledger,tree,rope,formats,regex,search}.bend
src/shared/shared/shared/{quorum,reach,text,store,keyset,spans}.bend
src/shared/shared/shared/shared/{trie,cell,hash,hash.test,code,seal,shared}.bend
src/node/core/{spec,impl}.bend                Vend's domain (spec: types, body-less op laws, claims)
src/node/transport/spec.bend                  spec only; its open laws are expected
src/node/shared/requests.bend                 Vend's requests and their machine
src/node/shared/shared/{resources,uris}.bend
src/glob/{spec,impl}.bend
```

The replica is generic over `~mach: Machine()` and `~kern: Kernel(mach)`. A kernel returns an act
(`Act.Stale`, `Act.Mark`, `Act.Judged`, `Act.Made`), and the replica does it (`Act.run`). So the
machine laws hold for every kernel. `Lawful` is left only as internal plumbing that
`Kernel.lawful` builds from any kernel; no law assumes it.

## 4. How to check

```sh
bend <file> --check-only      # the judge; it prints to stderr. replica.bend: about 15 s
bun run lint                  # must end with "0 finding(s)"
git diff --check
```

Entry files: `src/shared/shared/shared/shared/shared.bend`, `src/shared/shared/shared/text.bend`,
`src/shared/shared/shared/reach.bend`, `src/shared/shared/shared/keyset.bend`,
`src/shared/shared/shared/spans.bend`, `src/shared/shared/regex.bend`,
`src/shared/shared/search.bend`, `src/shared/shared/ledger.bend`, `src/shared/replica.bend`,
`src/glob/impl.bend`, `src/node/core/impl.bend`, `src/node/shared/shared/uris.bend`,
`src/shared/shared/shared/shared/hash.test.bend`. `src/glob/spec.bend` and
`src/node/transport/spec.bend` alone print TODOs: those are their open laws, which impl files fill.

Facts that cost time to find:

- `bend` runs natively on Windows (the fork in `../bend`). **gen3 does not**: run it through WSL
  (`bun tools/gen3/gen3.ts prove <file> <def> --wait 60 --write`). `gen3 check` can be stale;
  `bend` is the judge. On the large files gen3 proves only small lemmas.
- Canonical format: replace `bend-lint.json` for a moment with a config that holds only
  `bend-lint-rules/layout/format`, run `bunx bend-lint 'src/**/*.bend' --fix-dangerously`, and
  restore the file byte for byte. No lint rule was ever removed.
- A "for every" hypothesis is a function, so it is affine: use it once, with the case split inside.
- A def calls only defs above it. Match a parameter, not a computed value, and not after a `let`
  or a rewrite: give the computed value its own helper with an equation parameter. The shrinking
  parameter goes first.
- A rewrite `%e: P` needs the goal as `P[b]` for `e: {a == b}`. Most failed steps had `e` the wrong
  way round: wrap it in `Equal.sym`.
- A spec def cannot call a body-less op of the same spec: impl.bend fills the op below it.
- A value of function type (a kernel, a continuation) cannot be used twice; pass it as a template
  parameter (`~kern`).
- A dead-code scan must count uses through an import alias (`Replicas.Node.find`). A scan that did
  not deleted live defs once; it was undone before any commit.
- Git Bash heredocs break Python that holds backslashes; write scripts as files.
- Do not ask an agent to log its progress or its reasoning to a file (the owner's rule).

## 5. Done on `feature/refactor-5` (since `783119f`)

Numbers (all of `src/**/*.bend`): laws 194 → 201; spec files 1,596 → 1,714 lines (they grew because
the rule of a write moved into the core spec); all `.bend` lines 81,799 → 92,497 (proofs added, and
about 1,580 lines of proofs deleted).

### 5.1 Rounds

- `Node.Honest`: each pass that a node holds names the last vote of its node below its round, at
  every height of every line.
- Laws: `Seal.accept_keeps_honest`, `Node.empty_honest`, `Node.after_honest` (any kernel, no
  premise), `Node.one_history` (an honest node shows one history), `Plan.lead_allowed` (the
  proposer proposes only an allowed step), `Round.mine_free` (a node votes in no round below a
  pass of its own).
- A kernel adds data only, by construction (`Run.data`). `Advance.head.grows` is deleted.
- Not provable as the code is: the ballot of `Pass.to` is first in its slot (`Pass.to` tests
  `passed`, not the slot), and `Seal.fits` (the key that a store holds for a node is content of the
  store; nothing ties it to the node's seed).

### 5.2 Glob

- `spans.bend`: every proof is closed. The span algebra (`Span.meet`, the chain cover) is there,
  not in the glob.
- A class holds spans: `src/glob/spec.bend` has `Class{neg, ss: List<Spans.Span>}`, and
  `Char.range` is gone (the owner accepted this change of the spec). Show writes each span in parts
  that read back (`Span.parts_has`, `Span.parts_fine`). `read_after_show`, `read_rejects_root`,
  `read_after_escape`, `search_found` and `search_absent` are still proven.
- Speed: `KeySet.unique` and `Search.push` make the key of a new value once (about 5% on six
  test queries). A profile of a large Absent query: the search and the certificate check take
  about half of the time each, and making keys about a third. The test queries were not saved in
  the repository. The method: a `main` that runs `Spec.Query.search`, `bend bench.bend -o
  bench.js`, rename to `.cjs` (the package is `type: module`), `node --stack-size=65500`.

### 5.3 Claims made stronger

- The rule of a write is a reference def in `src/node/core/spec.bend` (`Judge.write`, with
  `Judge.ready`, `Judge.ready_maybe`, `Judge.content`, `Judge.then`, `Judge.when`,
  `Judge.refuse`): take a write only when its resource holds at h what it held at base, refuse
  only a stale one, wait only for what the node cannot read.
- New law `Judge.write_keeps`: a taken write changes only its resource (replica lemma `Set.other`).
- `Pick.merge_ours` also covers "both sides made the same change"; with `Pick.merge_theirs` the
  rule of a merge is stated in full, up to the merge of both.
- New law `Merge.names_complete`: a merge sees each resource whose content differs between ours
  and theirs. With `Merge.keeps`, a change made on only one side is kept.
- Every kernel is lawful (section 3). The ten laws that assumed `~lawf: Lawful` take any kernel:
  `Node.after_grows`, `Node.after_keeps`, `Step.run_outs`, `Node.out_final`, `Node.made_final`,
  `Chain.version_final`, `Chain.mark_final`, `Chain.start_final`, `Node.after_on`,
  `Node.ask_once`. Vend's own lawfulness proofs (`Ask.lawful`, `Change.grows`, `Change.kept`,
  `Change.outs` and the defs only they used) are deleted.

### 5.4 Reviews

The review skills ran on the glob and spans work until they found nothing; dead defs went. They
did not run again on the claims work of 5.3; `bun run lint` did.

## 6. Next steps

Order chosen by the owner. Each is one commit that checks.

1. **One history across nodes, in the README's terms.** `Line.at_agrees` assumes a node u that
   holds both ledgers and whose passes name their node's last vote (`Rounds.Rules`). Each node
   that starts empty is honest (5.1). Missing: when no owner forks its chain, a node that takes in
   another node's ballots keeps all of them. That is a proof about `Node.sync` and `Sync.more`,
   which stop after a number of steps and keep a ballot whose key the store gives at a later height
   only once the head is there. It also needs an invariant: the ballots of an owner that a node
   holds are a prefix of the owner's one chain. Several days; the sync loop may have to change.
   The owner chose to do it.
2. **Writers are told of every change to what their work uses.** `Node.affects_used` states only
   that each listed touch holds. Missing: each touch that holds is listed. First make "a branch
   lacks a version" one concept: `Branch.lacked` uses version vectors, `Touch.lacks` uses
   `Node.has`. `Touch.holds` does not compare the touch's branch with the branch of its `Seen`.
   The spec also needs a meaning of its own for `Touch.holds`, `Seen.of`, `Group.nodes` and
   `Merge.base`. The depth part is proven in `reach.bend` (`Reach.all_in`, `Reach.in_through`).
3. **Operations that return "none".** `Work.Reads` is `Unit` for `None`, so `Move.reads`,
   `Resolve.reads`, `Resolve.shuts` and `Merge.keeps` hold when the operation gives up. The tree
   part is proven (`Tree.set_some`); missing are the replica's link from a set of the tree to the
   node, and the core consequences. Also: `Move.reads` both ways (a move adds no resource; it needs
   a frame law of a set that holds in every later store, as `Tree.get_other` does);
   `Node.read` at each kind of point; `Node.draft` gives exactly the newest pending write, and each
   draft comes from one; `Own.takes` both ways.
4. **Claims for the operations that have none:** `Node.versions`, `Node.log`, `Node.diff`,
   `Node.members`, `Node.resources`, `Node.notices`, `Node.impact`, `Vend.may_stop`. Most facts
   they need are replica laws already (`Chain.version_final` and the others).
5. **The glob search always decides** (Found or Absent, never Unknown). `search.bend` has only
   `Cert.sound`; `regex.bend` has no law that an expression has finitely many derivatives.
6. **One generic frame lemma** in place of the 59 lemmas of the Frames block of `replica.bend`,
   which copy the growth lemmas. The owner allowed a review of their proof bodies for this.
7. **`Lawful`**: rename or remove the internal plumbing (section 3).
8. Run the review skills again on everything since 5.4, in order
   (`thermo-nuclear-code-quality-review`, `cyclomatic-complexity`, `erasure`, `bun run lint`),
   until they find nothing; then the final report to the owner (spec size and laws before and
   after, what each law assumes, what is not done).

README: the Vend Owner Group entry says the owners are trusted "to never sign two different
decisions for the same step". The proofs assume that an owner never signs two different ballots
for the same position of its own chain. The owner decides whether to change the sentence; only
human hands change the README.

## 7. Known limits (say them, do not hide them)

- One history across nodes still assumes `Rounds.Rules` of a node that holds both ledgers (step 1).
  For one node it is proven with no premise.
- One lying owner can break one history (majority quorum). A lie is recorded and told
  (`Node.liars`, `Notice.Lied`), not prevented. A two-thirds quorum is a different, slower product.
- A member of a store can craft a line key so that its ballot fills the slot of another node's
  ballot; with `Ballot.first` that other ballot is refused. Safety holds (reads are checked);
  liveness does not. The fix is a prefix-free code of the line key in the slot.
- SHA-256 and the one-time signature are assumed unbroken.
- `Advance` runs a decided step again before it keeps it (the README: a node checks everything).
- Tree and rope builders hash each node once more to link.
- `src/node/transport/spec.bend` is a spec with open laws.
- `src/glob` is a glob for file-system-style paths only. Nothing in `src/node` imports it, and the
  README does not name it (the owner does not want a README entry).
- An `expect` directive on `Holds.led` was added by an agent; its reason is not verified.
