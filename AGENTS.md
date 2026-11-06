# AGENTS

Contribution guidelines, for agents and humans alike.

The rules stated here have priority over any and all rules in any skill file or tool.

## 0. Core

- If a skill does not load, read its file in `.agents/skills/`.
- Do not change any `.md` file without asking me.

## 1. Communication

- Speak the language you are spoken to; but shortly and without dropping important information in
  ASD-STE100(or language's equivalent), with learnings from the `i-have-adhd`.
- Use a global counter for your non-trivial questions that grows throught the session. Repeat each
  open question in each response until I answer it or tell you to use common sense.

## 2. Code

- Run `bend guide` once per session before you write Bend code. Use the `bend` on PATH, even if it
  is a fork or a different version. Also run `bend guide shaders` before parallel or performance
  work, and `bend guide effects` before a custom effect.

- Before you write a new def, look for it with `bend base <Name>`.

- Trust the checker. Bend is sound, so a proof that checks is correct. Do not look for
  counterexamples, before or after you write a law.

- Do not run `--verdict` unless I ask.

- Do not use `@unsafe`. Do not use foreign code unless I approve it.

- Use a law, not a test, but ask me before you write one. Use a test only for behavior that a law
  cannot state (for example, IO output).

- Write a law only for a property that matters. For example, a hardcoded list does not need a law
  that it has no duplicates.

- A law's statement is code, and obeys the same rules as other code. Its proof body does not, unless
  it is too expensive to check. Ask me before you review a proof body, or code that a proven law
  covers. Good laws and an ergonomic API are the priority.

- If a proven law covers a def, use that def. Do not write or use an unproven def that does the same
  thing.

- When a law replaces another law or a test, delete the old one in the same change.

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
- Before you present me your changes, run these in order, and repeat until they find nothing more
  about them:
  1. `thermo-nuclear-code-quality-review`. A file over 1000 lines can be fine. Ask me before you
     split one.
  2. `cyclomatic-complexity`.
  3. `erasure`.
  4. `bun run lint`.

### Style

- Write functional code without mutation, except when speed is a priority for a file(ask me);
  wherein any and all optimization opportunities are fair game.
- Give each concept one representation in the whole codebase.
- Give each fact one location. A comment must not repeat what the docs state or clearly imply.
- Use the helpers that exist. In Bend, a helper with one caller is fine, since Bend often needs one
  (a match on a computed value, a pair to take apart); do not add a def that only passes its
  arguments on.
- When you change something, delete the code, comments and docs it made obsolete.

### Bend

Follow the `bend2` and the `experimental-bend-spec` skills.

- On Windows, run Bend natively only with the fork in `../bend` (branch `feature/cuda-and-windows`).
  Otherwise, use WSL.

## 3. Project

**bend-ver** is a version control system written in Bend, built for many AI agents working at once.

- **It records everything, live.** Every save is a version, with no commit step. It records edits made by
  other tools too. Optional *marks* name the points that matter.
- **It understands content.** For Bend and C code, it versions by item (a function, a type) instead of by
  line. Changes, merges and conflicts are about meaning, not text layout. Unknown files still work at line
  level, like git.
- **It knows who depends on what.** It tracks imports, including conditional ones like C's `#ifdef`, and
  tells each agent only about changes to the things its work uses.
- **Agents work in parallel safely.** Each agent works on its own line (like a branch). Stale writes are
  refused instead of overwriting others, and lines merge back by item.
- **Resources aren't just files.** Anything with an address (a file, a server) is a stream that may be
  reachable or not. Files are the first kind.
- **It's built for speed and sharing.** Content is stored once by hash, edits cost little even in huge
  files, and histories from different machines can be joined.
- **It's proven correct.** Its rules are stated as laws that Bend's checker verifies, and a helper tool
  (gen2) writes many of those proofs automatically.

- README.md is for users and stays short. Internals go here and in code comments.
- `bend-lint.json` picks the rules `bun run lint` runs (bend-lint's own, from BendHub).

```sh
bun install
bun run lint
git diff --check
```
