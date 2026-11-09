# Handoff

## State

- Branch `feature/refactor-pass-3`, clean tree, last commit `1477762`. Nothing is pushed.
- Every file checks: shared/*.bend, glob/impl.bend and core/impl.bend print ALL PROOFS CHECK. core/spec.bend has 34 TODOs and transport/spec.bend has 67; both are expected (declared operations and laws that impl fills).
- `bun run lint`: only the 133 old `layout/case` findings (lowercase constructors).

## Done (this pass, after the replica pass on feature/refactor-pass-2)

1. `9ca170f` Eq.Laws everywhere (no more `~refl`/`~sound` pairs; each type has `X.laws()`).
2. `7350836` glob imports shared; its copies of shared lemmas are gone.
3. `0900f3e` `Cut<A>` for text and bytes (formats' `Found` is gone).
4. `7d5122e` Base's `List.contains` replaces shared's `List.has`; `List.union` is generic.
5. `0ba0b4b` shared.bend split: `shared/text.bend` (alias `Texts`), `shared/trie.bend` (alias `Tries`); Fork/Ends moved into formats.
6. `5cfd109` `List.same` is lazy; `Bytes.is_eq` is gone (bytes use List equality over U32).
7. `1477762` Names: `X.is_eq` for equality, alias `Replicas`, Bool names (`is_…`), the core's `Done.*` helpers.

## User's answers (latest)

- Q16 (spec defs in place of "exactly" laws): not wanted. Opaque operations plus "exactly" laws keep the impl free; a spec def would fix the implementation. Open to discussion if fixed implementation is optimal in data-structure.
- Q17: rename constructors to PascalCase, repo-wide (lint's `layout/case`).
- Q18: make glob's `Chars.has` / `Chars.is_eq` lazy and merge them into `List.contains` / `List.is_eq` (over `~Char.is_eq`). Proof rework is fine.

## Next

1. **Q17.** Lint lists 132 constructor names (pairs saved in the scratchpad as `case.json.pairs`; regenerate them with `npx --no-install bend-lint --json`). Rename each constructor at every `Name{` use, with any alias prefix (`Spec.`, `Core.`, `Replicas.`, `Shared.`, …). Watch for these:
   - one finding is `Q->q` (a type parameter, not a constructor): check it before renaming;
   - short names (`one`, `many`, `tip`, `bin`, `in`, `out`, `any`, `class`, …) must match only as constructors (followed by `{`);
   - make sure no new name collides with an existing type or def.
2. **Q18.** In glob, replace `Chars.has` with `List.contains(~Char, ~Char.is_eq, …)` and `Chars.is_eq` with `List.is_eq(~Char, ~Char.is_eq, …)`. Give Char a `Char.laws()`, rework the proofs that relied on the eager `Bool.or` / `Bool.and` shapes (use gen3), and delete the old defs.
3. After each step: format (lint's JSON fix), check every file in WSL, run `bun run lint` and `git diff --check`, then commit.
4. At the end: the review passes (thermo-nuclear, cyclomatic, erasure, lint), then a naming check.

## Working notes

- Check in WSL: `wsl -e bash -lc 'cd /mnt/c/Users/mathe/source/repos/vend/src && bend <file> --check-only'`. text.bend and trie.bend need their own check run.
- Formatting: `bend-lint --fix` makes no fix; apply the `layout/format` fix text from `--json` output.
- gen3: `bun tools/gen3/gen3.ts prove <file> <def> --wait 120 --budget 300`. It now handles template (`~`) defs.
- Bend rules learned:
  - a spec def cannot call an operation that the spec only declares;
  - a match reads only parameters, or pattern variables in binder order; to match a computed value, use a helper with that value as a parameter;
  - a destructuring `let` is a match;
  - template parameters come first;
  - a partial template application such as `~F(~A, ~same)` works as a template argument;
  - a pair `A & B` is a `Type`; use a named `Data` type when it must be copied.
- Open idea, not started: the two UTF-8 case-split proofs (char_back, char_bytes) could share one tree.
