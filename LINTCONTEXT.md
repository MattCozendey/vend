# Lint: state and facts

`bun run lint` takes about 90 s on this repo (4 cores, 15 GB, Linux, bun 1.4.4), and ends with no
error. `bend src/daemon/core/impl.bend --check-only` takes about 13 s (it was 175 s: see
`src/daemon/DESIGN.md`, "Proof speed").

## What is left (178 findings)

- `layout/case` (155): it reports each constructor of each type (`Rename Tip to tip`), also in files
  that this branch did not change (`glob/spec.bend`: 31). The repo's constructors are PascalCase on
  purpose, so these are false findings.
- `performance/eager_branch` (11) and `performance/missed_fork` (12): in code that runs
  (`shared/shared/shared/trie.bend`, one in `shared/ledger.bend`). Not changed: laws state these
  defs as they are.

## Directives

- `src/daemon/core/impl.bend` holds only proofs. It has four `expect-file` directives, each with its
  reason: a proof does not run, and a second use of a binder in a proof sits in a rewrite motive or
  an erased argument.
- Other files have `expect-begin` / `expect-end` around the proofs that the same two rules report
  (`language/reused_binder`, `performance/unused_result`).
- For a proof, `language/reused_binder` and `language/unneeded_plus` can disagree on one binder.
  The checker decides: a `+` stays only where `bend --check-only` needs it.

## Other facts

- bend-lint 0.3.0 checks with Bend 2.0.39; the `bend` on PATH here is 2.0.40. bend-lint prints a
  warning about it.
- `--fix` changes nothing here: it prints `--fix makes no fix until Bend's checker in Bend can prove
  that a fix keeps the program`. The canonical format was applied with `--fix-dangerously` and a
  config that names only `layout/format`; each file was checked again after it.
- A run of `bun run lint` fails with `the checker failed: a check changed since its answer; run
  again` when a file changes while it runs.
