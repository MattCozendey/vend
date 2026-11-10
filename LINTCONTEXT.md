# Lint: state and facts

`bun run lint` ends with 0 findings. It takes a few minutes on this repo (4 cores, 15 GB, Linux,
bun 1.4.4). `bend src/daemon/core/impl.bend --check-only` checks all proofs of the core in about
13 s (it was 175 s: see `src/daemon/DESIGN.md`, "Proof speed").

## Directives

- A proof file (`src/daemon/core/proofs/*.bend`) has `expect-file` directives, each with its
  reason: a proof does not run, and a second use of a binder in a proof sits in a rewrite motive or
  an erased argument.
- Other files have `expect-begin` / `expect-end` around the proofs that the same rules report.
- `layout/case` reads a constructor as a law, and asks for snake_case. Constructors are PascalCase
  here, as in Base (`Some`, `Con`), so each `type` has an `expect` with that reason.
- `core/impl.bend` imports each proof file and uses none by name: a check of it checks all of
  them. A proof file that uses a law imports the file that proves it. Each has an `expect` for
  `no_unused/imports`.
- For a proof, `language/reused_binder` and `language/unneeded_plus` can disagree on one binder.
  The checker decides: a `+` stays only where `bend --check-only` needs it.

## Other facts

- bend-lint 0.3.0 checks with Bend 2.0.39; the `bend` on PATH here is 2.0.40. bend-lint prints a
  warning about it.
- `--fix` changes nothing here: it prints `--fix makes no fix until Bend's checker in Bend can prove
  that a fix keeps the program`. The canonical format was applied with `--fix-dangerously` and a
  config that names only the layout rules; each file was checked again after it.
- A run of `bun run lint` fails with `the checker failed: a check changed since its answer; run
  again` when a file changes while it runs.
