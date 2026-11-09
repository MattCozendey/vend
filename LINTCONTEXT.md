# Lint: the slow case

`bun run lint` takes about 2 minutes on this repo. One file takes most of it.

## The case

- File: `src/daemon/core/impl.bend` (about 2,800 lines; it imports `core/spec.bend`, `ledger.bend`,
  `tree.bend`, `rope.bend`).
- Commit: `d3e3a7b` on branch `claude/daemon-core-impl-kahuc3` (the numbers below), and each commit
  after it.

| Command | Time |
| --- | --- |
| `node_modules/.bin/bend-lint src/daemon/core/impl.bend` | 80 s (122 s at commit `9c1464f`) |
| `bend src/daemon/core/impl.bend --check-only` (Bend 2.0.40) | 38 s (57 s at `9c1464f`) |
| `node_modules/.bin/bend-lint src/daemon/shared/rope.bend` | 19 s |
| `bend src/daemon/shared/rope.bend --check-only` | 9 s |
| `node_modules/.bin/bend-lint src/daemon/transport/spec.bend` | 16 s |
| `node_modules/.bin/bend-lint src/daemon/shared/tree.bend` (12,576 lines) | 2 s |
| `node_modules/.bin/bend-lint src/daemon/shared/ledger.bend` (6,400 lines) | 6 s |
| each other file | under 2 s |

So the linter takes about 2 times as long as Bend's own check of the same file, and the check is
the slow part: size is not the cause (`tree.bend` is 4 times larger and takes 2 s).

## What makes the check slow

Measured with prefixes of the file (`head -n N impl.bend > part.bend; bend part.bend --check-only`):

- `import ../shared/rope.bend`: about 9 s in each file that imports it. In `rope.bend`, the time
  is in `Rope.put.step_holds`, `Rope.put.go_holds`, `Rope.put.step_reads` and `Rope.put.go_reads`
  (the file up to `# Puts` checks in 0.3 s).
- `def Spec.Own.takes_inside` (`impl.bend`): about 6 s for a 2-line proof. Its type holds
  `Spec.Group.nodes(s, Spec.Own.tree(s, l, at, h), g)`, a call with a large normal form
  (`Reaches.Reach.in`). An earlier form of the same law, with a `match` on two arguments and that
  call in each case, took 17 s to 32 s (commit `9c1464f`, `def Spec.Judge.own_inside`), and one run
  of a prefix that ended in it was killed for memory (exit 137 on a 15 GB machine).
- `def Keep.reads` and `def Spec.Node.keep_reads` (`impl.bend`): about 10 s. Their types hold
  `Ropes.Rope.put(cs)` three times.

Two checks of one term with itself are fast (a lemma `{Spec.Group.nodes(s, h, g) ==
Spec.Group.nodes(s, h, g)}` adds under 1 s), so the time goes to terms that are equal only after
they are reduced.

## To reproduce

```sh
bun install
time node_modules/.bin/bend-lint src/daemon/core/impl.bend
time bend src/daemon/core/impl.bend --check-only
```

## Other facts

- bend-lint 0.3.0 checks with Bend 2.0.39; the `bend` on PATH here is 2.0.40 (built from
  `MattCozendey/bend`, branch `claude/daemon-core-impl-kahuc3`, which is `main`). bend-lint prints
  a warning about it.
- Machine: 4 cores, 15 GB, Linux, bun 1.4.4.
- A run of `bun run lint` fails with `the checker failed: a check changed since its answer; run
  again` when a file changes while it runs.
- `--fix` changes nothing here: it prints `--fix makes no fix until Bend's checker in Bend can
  prove that a fix keeps the program`.
- The rule `layout/case` reports each constructor of each type (`Rename Tip to tip: a law that does
  not state a type is snake_case`), also in files that this branch did not change (`glob/spec.bend`:
  31). The repo's constructors are PascalCase on purpose, so these are false findings.
