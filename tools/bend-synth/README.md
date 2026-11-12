# bend-synth

Fills Bend 2 `?TODO`s: proofs (propositions) by search, programs (data defs) by search guided by
evidence. Budgeted, anytime, resumable, shared by many callers. Bend's checker accepts every step;
`bend <file> --check-only` remains the judge.

```sh
bun tools/bend-synth/synth.ts prove FILE DEF [--budget S] [--wait S] [--spec F.json] [--helpers] [--write] [--json]
bun tools/bend-synth/synth.ts goals FILE DEF          # each hole's goal, context, derived facts, applicable steps
bun tools/bend-synth/synth.ts submit JOB SKETCH.bend  # an agent's partial body; its holes join the live search
bun tools/bend-synth/synth.ts show|watch|resume|cancel|export JOB ; status ; stop
bun tools/bend-synth/synth.ts bench FILE [REGEX] [--budget S] [--verbose]   # hide each proven body, find it again
```

The exit code is 0 when the def is proven or synthesized (or has nothing to do), 2 when it stays open
or partial, 3 when the job is still running (the same command attaches to it), and 1 on an error. Bend is
found through `--bend-path`, then `$BEND_PATH`, then the nearest `bend2/` (or sibling `bend/bend2/`)
above the file, then this checkout. It runs on Windows and on Linux/WSL.

## How it works

**The checker makes the goals.** Bend's `term_check` reaches every `?TODO` with its exact type,
context, quantities and `lhs` (the descent columns). One in-memory patch reports them. A tactic is a
fragment of text with `?TODO`s, checked at its goal, and the holes it leaves are its subgoals. No context
is rebuilt by hand, and a recursive call is judged by Bend's own descent rule at the hole. A local check
takes microseconds; the target's def check takes about 0.1 ms. The whole book (with Base) is never
re-checked in a loop, which takes about 25 ms per check.

**Proofs** use proof-number search over an AND/OR tree. A goal is proven by any of its steps, a step by
all of its subgoals. Goals are keyed by a bounded normal form, which detects cycles and lets a proof
found in one branch be reused in another. A step is checked again in whole when its subgoals close,
because sibling holes can share an affine binder. The steps are:

- bind or split a pending binder (a λ-match, so Bend refines `lhs`)
- close by `{==}`, a unit, a fact, or `Empty.absurd`
- apply a hypothesis, the induction hypothesis, or a lemma (indexed by conclusion head)
- rewrite (`%e : P`), and subst (`%E@h : P`: J abstracting the endpoint and the proof)
- build a constructor of facts
- lift a goal into a helper def, optionally with a stuck call generalized or a derived fact of a sum
  type (an `Or` from the induction hypothesis) as a parameter, which the helper then splits first; inside a
  template the helper is a template too, with the same `~` constants, passed on by the call

These principles carry most of the reach:

- **One rule shape.** Lemmas, hypotheses and the induction hypothesis are all rules: a pattern plus
  premises that facts fill. Rules with an informative head are used backward from the goal. A rule
  whose conclusion is a bare-variable equation (`{r == m}`) carries no goal information, so it is used
  only forward, and its premises matched against the facts select it. Premises are read as stated and
  in normal form, and Bend keeps whichever reading holds (one may fail the descent rule while the other
  passes).
- **Templates follow Bend's rule.** A template's `~` parameters are constants (Bend makes them
  `k~name`). Every step can name them as the header does, they print back that way, and they serve as
  hypotheses and rewrite rules. A template lemma is usable from any def: its `~` arguments come from
  unification with the goal or from a closed constant of the right type (a laws record), never from a
  hole.
- **Recursion follows `lhs`.** The induction hypothesis is offered wherever a match has refined the
  goal's `lhs`, whoever wrote that match: the search, an agent's sketch, or the user's code.
- **Out of fuel is not a refutation.** A step that runs out keeps its place, costlier, and is tried
  again with four times the fuel. Such steps get half of the search time (dovetailing), nearest the root
  first, so neither exploration nor a long computation can starve the other. A goal whose `{==}` runs out
  is heavy, and so are the goals below it (Bend shares no reduction between checks), so nothing there
  is checked eagerly. A proven goal records the fuel its proof took, and the check of its parent gets
  that much. A step that earned more fuel than a slice runs to the job's own budget.
- **Nothing is computed before it's needed.** A rewrite step prints its motive and builds its rewritten
  goal only when the search reaches it. A goal keeps its key, not its normal forms, and the
  normal-form cache is bounded by the term nodes it holds.

**Programs** are handled differently, because any value of a data type checks. A data def is accepted
only on evidence: the laws that name it, sampled on small inputs, plus `--spec` examples
(`{"examples": [{"call": "len([1n])", "expect": "1n"}]}`). Shapes (no match, a match, a match on the
recursive field) are combined with small typed leaves per arm. Each leaf is first tried alone, with the
other arms left as `?TODO`. Bend evaluates that partial program with its holes opaque, so a clash that
doesn't depend on a hole refutes the leaf for every completion. The rest are combined simplest-first.
When the evidence doesn't pin an arm down, the report gives an alternative leaf that also passes.

**Hints come first.** Within `--wait`, every answer carries the goals with their contexts, the best
partial, what was tried and why Bend rejected it, nearby lemmas, similar proven defs, and (with
`--helpers`) each open hole stated as a lemma.

## Jobs, callers, resources

`synth.ts` starts a localhost supervisor that never loads Bend.

- **Jobs.** A request is keyed by the tool version, Bend version, file contents, target and options;
  identical requests attach to the same job, and calling a paused job again continues it.
- **Scheduling.** Jobs run in 1.5 s slices across `BEND_SYNTH_WORKERS` workers (default 1, at most
  4). A worker keeps a job's live search tree, so `resume` and `submit` continue the same tree.
- **Persistence.** Every goal a search proves is stored in SQLite (`BEND_SYNTH_STATE`, by default
  under the OS temp directory). The next search that meets that goal checks the stored proof first.
- **Limits.** Each worker runs below normal priority with `BEND_SYNTH_MEM_MB` of memory (default
  10% of RAM, at most 1024 MiB). On Windows a job object enforces that; on Linux and WSL the worker
  checks its own RSS, and between steps the search sheds its caches, then stops the slice, before the OS
  limit is reached. A watchdog kills a slice that runs 20 s past its job's remaining budget. Fuel bounds
  every check and every normal form.
- **Many callers.** A job waits up to a slice for the worker that holds its live tree rather than
  start cold elsewhere. The proven-goal cache travels only when a session starts, and a poll returns the
  report only when it changed.

`BEND_SYNTH_TRACE=1` (or a line cap) prints the explored tree on stderr.

## Measured (2026-11-12)

Every proven lemma of the five demo `PROOF.bend` files was searched again with its body hidden: 2 s
per lemma, one worker. The machine was in use during the runs, which were not repeated, so a lemma near
the 2 s limit can flip.

| demo | bend-synth | gen3 (parser shim) | the previous bend-synth |
| --- | ---: | ---: | ---: |
| proof_insertion_sort | 7 / 7 | 4 / 4 (sees 4) | 2 / 7 |
| proof_numerics | 11 / 11 | 6 / 11 | 6 / 11 |
| proof_typed_eval | 4 / 4 | 3 / 4 | 2 / 4 |
| app_slash_boss_3d | 13 / 15 | 10 / 15 | 0 / 15 |
| app_win_is_bug_2d | 10 / 18 | 8 / 17 | 0 / 18 |
| **total** | **45 / 55** | **31 / 51** | **10 / 55** |

The three proof demos take 0.2 to 0.3 s each in total. With a larger budget, `back_to_title` (whose
`{==}` alone takes 6.4 s in Bend) is found in about 20 s, and `esc_quits` in about 2 s, near the
limit. Still open: `toggle_twice` (three rewrites that put back the computed value of a split
constructor), win_is_bug's `chk_*_at`, `go_ok`, `off_F`, `you_cant_win` and `never_on_flag`, and its
programs (`chk`, `tx`, ...), which need larger shapes.

This copy runs as `bun run synth ...` from vend's root, on the Bend that the sibling `../bend` checkout
provides (the nearest `bend/bend2/` above the file; `--bend-path` overrides). Its behavior tests,
which run on that repository's demos, live with the tool there (`bun test tools/bend-synth`).
