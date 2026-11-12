# AGENTS

Contribution guidelines, for agents and humans alike.

The rules stated here have priority over any and all rules in any skill file or tool.

## 0. Core

- If a skill does not load, read its file in `.agents/skills/`.
- Do not change any `.md` file without asking me.

## 1. Communication

- Speak the language you are spoken to. Follow the `i-have-adhd` skill.
- Use a global counter for your non-trivial questions that grows throught the session. Repeat each
  open question in each response until I answer it or tell you to use common sense.

## 2. Code

- Do not use `@unsafe`.

- Ask me before you write a law.

- Do not try to prove that generated data, or a copy of a standard's text, matches its source. Check
  generated data with a test against an independent source (for example, another implementation, or
  the standard's own test vectors). That test does not replace laws for the code. Tell me which
  copies of standard text you changed, so that I can check them.

### Tools

- You are rarely, if ever, smarter than any linter, so do not work around a lint rule and only
  expect/suppress a finding when that makes sense (with a directive whose reason says why [for
  example, a measurement]).
- Deterministic tools always win over skill suggestions.
- Every test needs my approval first, and tests that suggest implementation details should not be
  suggested at all.
Before you show me your changes, do sweeps. A sweep:
  - Reads each changed area once with `thermo-nuclear-code-quality-review` and
    `erasure`, and the changed functions with `cyclomatic-complexity`. It fixes what they find.
  - Runs the project's lint and type check until they pass.
  - Commits its in-area changes, then its cross-area changes.

  Sweep 1 reads the branch diff from its base. Before each later sweep, ask me if it reads the whole
  repo, the whole diff, or the delta (the hunks changed since the previous sweep, and their
  callers). Repeat until a sweep finds nothing to delete, no structural regression, no missed large
  simplification and no spaghetti growth. After sweep 3, stop and ask me.

### Style

- Write functional code without mutation, except when speed is a priority for a file(ask me);
  wherein any and all optimization opportunities are fair game.
- Give each concept one representation in the whole codebase.
- Give each fact one location. A comment must not repeat what the docs state or clearly imply.

### Bend

Follow the `bend2` and the `experimental-bend-spec` skills.

- On Windows, run Bend natively only with the fork in `../bend` (branch `feature/cuda-and-windows`).
  Otherwise, use WSL.

## 3. Project

**vend** is a version control system written in Bend. README.md states what it is.

- Always use gen3 (`bun run gen3 prove <file.bend> <def>`) as the first step of every proof.
- README.md is the canon. Internals go in code comments.
- `bend-lint.json` picks the rules `bun run lint` runs (bend-lint's own, from BendHub).

```sh
bun install
bun run lint
git diff --check
```
