// gen2.ts: a general, fast, deliberately incomplete prover for Bend2 proof holes.
// ================================================================================
//
// Dev tool, OUTSIDE the trust: bend2 checks each candidate in-process, and `bend <file> --check-only`
// is the judge of what it prints. It only helps a person or an agent who proves a law; it must stay
// fast, and never crash (every failure prints a message and exits non-zero).
//
// ORIGIN: copied from bend-bootstrap (src/Shared/scripts/gen2.ts, at 9286ee3) and adapted to bend-ver:
// bend2 comes from bend-lint's pinned download (tools/gen2/bend2.ts), bend2 loads the entry's
// imports itself (so `import ./spec.bend as Spec` and law fills `def Spec.law(..)` work), the
// shared-server pool and the --wp stepper (bend-bootstrap's own machine) are gone, and the induction
// module (gen2_ind.ts) also tries the whole goal as one arm (a stuck Bool or Cmp call generalized),
// introduces premises, splits enumeration parameters that premises block on, and generalizes a stuck
// enumeration call inside a hypothesis (pattern B). A rewrite also matches a lemma's side in normal
// form, and the index files each side by its normal-form head too (pattern D: Brk.char(Brk.of(c)) is
// Brk.char(Bool.pick(..)) in a goal's normal form).
//
// PURPOSE
// -------
// Given a .bend file and a def to prove (its whole body, or the ?TODO holes in its body), write a
// proof that bend2 accepts, or give up fast. Partial proofs (a skeleton whose open subgoals are
// ?TODO, each with its goal and context printed) are suggestions for the agent that owns the proof:
// never commit a partial as a finished proof.
//
// RUN (bun, from the repository root; `bun run gen2 ...` is the same):
//   bun tools/gen2/gen2.ts prove <file.bend> <def> [<def> ...] [--only RE] [options]
//       prove each <def> of <file.bend> (defs of the file itself, law fills such as Spec.law
//       included; with --only RE also every def of the file whose body is exactly ?TODO and whose
//       name matches RE), the book loaded once for all: a body that is exactly ?TODO is proven whole
//       (case splits allowed); otherwise each ?TODO in the body (leaf tactics, then decomposition).
//       Prints the proof text (ready to paste) on stdout, under a `# <def>` line when there are
//       several; a miss prints its partial; exit 2 if any miss.
//       To try laws: an impl file with `def Spec.<law>(<params>):\n  ?TODO` for each.
//   bun tools/gen2/gen2.ts serve <file.bend> [--port 7311]
//   bun tools/gen2/gen2.ts ask [--port 7311] <def> [<def> ...] [prove options]
//       serve keeps the book loaded (a local HTTP server on 127.0.0.1) and answers `ask`, which takes
//       the arguments of prove after the file and prints what prove prints (same exit code). Before
//       each ask, the entry is parsed again if its text changed: only its own defs are re-parsed (the
//       imports stay loaded). --budget defaults to 1000 there (not 4000).
//   bun tools/gen2/gen2.ts batch <file.bend> [--out DIR] [--only RE] [options]
//       every def of the book (the file and all it imports, not Base) with a ?TODO in its body: a body
//       that is exactly ?TODO is proven whole, other holes one by one. Writes DIR/report.txt (per hole:
//       the proof, or OPEN with its goal and context and the best partial with its open subgoals) and
//       DIR/gen2.patch (a unified diff from the repository root with the proven holes filled; apply
//       with `git apply DIR/gen2.patch`; partials never go in the patch). DIR defaults to ./gen2-out.
//   bun tools/gen2/gen2.ts bench <file.bend> [options]
//       benchmark: for each proven lemma of <file.bend> (in book order), forget its body, re-prove it
//       with only the defs before it, and report hit rate by size, time and tactics.
//   options:
//       --budget MS    time budget per def (default 4000)
//       --splits N     max case-split depth (default 6; 3 candidates at the top, 2 below depth 2, 1 below depth 4)
//       --depth N      max leaf depth: nesting of apply/premise (default 3)
//       --rw N         max rewrites in a chain (default 4)
//       --beam N       rewrite candidates explored per goal (default 4)
//       --fuel N       def lookups allowed per single check (default 300000)
//       --validate-book  validate the target file before searching (may fail on existing open claims)
//       --partial      on failure, print the best partial proof (holes with goals)
//       --partial-patch  batch: include partial whole-body skeletons in gen2.patch (still open)
//       --no-decomp    do not decompose open subgoals (see DESIGN)
//       --hole-budget MS  budget of each open subgoal in the decomposition (default budget/4, >= 300)
//       --stream       print startup timings and each closed subgoal to stderr
//       --only RE      bench: only defs whose name matches RE;  --max N: at most N defs
//       --json FILE    bench: write per-def results as JSON
//       --debug        print internal errors and failed final checks
//       --fresh        ask: search again, not the cached answer (the proof cache stays in use)
//       --check        no search: run bend2's def check on every def of the entry file (or on the named
//                      ones) in gen2's loaded book, as the file now is; prints each error and a summary
//                      (exit 2 on an error). With serve: `ask --check`, a few seconds, no bend2
//                      process. Not the gate (bend --check-only stays the judge).
//       --full-errors  check/prove: print every context entry of an error whole (see OUTPUT: errors)
//       --find RE      no search: every def of the book whose name matches RE (as the entry writes it),
//                      its statement in the entry's names, whether it has a body, and file:line (40 at most);
//                      then the defs that match in .bend files the entry does not import (an import needed)
//       --lemmas       no search: for each named def's goal (a body that is ?TODO) or each ?TODO in its
//                      body: the lemmas and hypotheses whose conclusion matches it, with what blocks each;
//                      the lemmas with the same head that do not match (their conclusions); the equations
//                      that rewrite a call in the goal. Usable lemmas only (before the def, not open).
//       --hole N       a body with several ?TODO: work on (or --lemmas for) the N-th only; the others stay
//       --no-ind       turn off the induction schemes (ON by default; --ind is accepted): a whole body
//                      the search did not prove gets induction schemes (gen2_ind.ts: bounded Nat
//                      enumeration, U32 words lifted to any width, word / Nat / functional induction) whose
//                      arms the leaf tactics close, with proven helper lemmas (generalized stuck calls, the
//                      arm's own goal); helpers print above the body. Also a clash through a predicate with
//                      type parameters (maybe.T(A, _)) and splits on Bool parameters only hypotheses name.
//                      Constructor steps in the arms: clashes, injectivity, inversion of sequencing helpers
//                      (Cir.exec.then, Cir.exec.if, ..), chains through the induction hypothesis.
//       --helpers      on a miss, each open hole (of a skeleton that closed a step, or a ?TODO inside a
//                      body) becomes a new lemma <def>.h<i> whose statement is exactly the hole's goal
//                      over its whole context (true iff the hole is), and the hole a call of it; at most
//                      6 per def; printed under "# HELPERS" (ask for each helper by name afterwards)
//       --write        apply the result to the file: a proof, or (with --helpers implied) the new body
//                      and the helpers above the def; skipped if the def's body changed since gen2 read
//                      it; statements are never touched (serve's reload then checks the new headers)
//   example:
//       bun tools/gen2/gen2.ts prove src/endpoints/impl.bend Spec.write_refused --partial
//
// DESIGN
// ------
// * In-process checking: the book is loaded once. Optional --validate-book checks the target file;
//   open claims elsewhere can prevent that check, so the default search uses the untrusted book.
//   Dependency proofs remain untrusted until the final kernel verdict. A candidate is proof TEXT,
//   parsed by bend2's parser in the def's file scope (its
//   namespace and aliases) with the subgoal's context names bound, then checked by bend2's
//   term_check against the subgoal's goal type in its context (never a bend2 process per try). The
//   final proof is checked with def_check on that def only. What is checked is what is printed.
// * Fuel and time: book.tlds is wrapped in a Proxy that counts def lookups (every unfolding goes
//   through it): each check gets --fuel lookups, and the whole def has a deadline (--budget). Out of
//   fuel = that candidate fails; past the deadline = the search stops and the best partial is kept.
//   A stack overflow in the checker is a failed candidate. The Proxy costs ~60 ns per lookup (about
//   3% of a miss: 0.9 M lookups in 1.7 s), so it stays.
// * Caches across asks (serve only, LRU, kept across reloads; see proofCache and answers): a closed
//   leaf goal's proof, reused only if it checks again at the new goal and names only defs the new
//   job may use; and each def's printed answer, by the options and the entry file's text up to the
//   end of that def (a later edit keeps it; a proven answer is checked again before reuse, a miss is
//   replayed as is). Within a job, a goal's targets and ordered callees are computed once (GoalInfo).
// * Normal form: nf(t) is a bounded strong normal form built on term_wnf: a stuck call stays a call
//   (bend2's canonical stuck form), its arguments are normalized, a closed constant (a def with no
//   parameter) is unfolded only when its value is tiny, and a node budget falls back to the raw term.
//   Literals are canonical (Succ/Zero chains to Nat literals, U32 words to U32 literals).
// * Lemma index (built once): every def with a body (or Base's) by the head symbol of its conclusion
//   (an equation: by the head of its left side; a bare type parameter: the ex-falso bucket), and a
//   rewrite index by the head of each side of an equation conclusion. Only defs before the target
//   in book order are candidates (the target itself only as the induction hypothesis).
// * Matching: first-order, on lowered terms, the conclusion (parameters as metavariables) against the
//   goal (raw, then its normal form). Parameters not fixed by the conclusion are fixed by matching
//   premises against hypotheses; if still open, the lemma is skipped (no enumeration).
// * Search, bounded everywhere (no blowups): iterative deepening on cost = split depth + leaf depth;
//   at most 3 split candidates per node (only pending binders that block evaluation); at most
//   --beam rewrite children per goal; at most 48 lemma candidates per goal; memo per (context, goal,
//   demand) of successes and of failures at a budget; a cycle check on the goal path; per-check fuel;
//   per-def deadline. Nothing ever enumerates combinations of arguments.
// * Decomposition (large goals): when the full search fails, a partial pass (splits <= 3, depth <= 2)
//   keeps the best skeleton (fewest holes, then most closed subgoals); each hole is then attacked
//   with its own budget (--hole-budget, deeper leaf depth); a hole that stays open takes one step
//   (bestStep: the most specific callee whose open premises are fewest and smallest, none restating
//   the goal) and its premises recurse, at most 2 levels, all holes within 2 x --budget. If every
//   hole closes, the proof is full (tag "decomp").
// * Guided split (whole bodies; tag "guided"): when nothing closed, the best lemmas whose conclusion
//   matches the goal are checked premise by premise (issuesOf); a premise that fits a hypothesis once
//   one root parameter is a given constructor (a clash: al.fresh's D.HSK(.., Nil) against hs's
//   D.HSK(.., ps)) gives `match ps:`, and that arm is decomposed on half the budget (the others: leaf).
// * Program stepping (goalTargets): lemmas are matched against the goal as stated, its normal form, and
//   the goal "stepped": each closed call in its spine (Sh.body) unfolded one step to its head
//   constructor (Cr.Cir.Stmt.seq{..}), so that statement lemmas (K.Ok.seq, X.set, X.if1) apply; also a
//   rewrite base. In a skeleton (bestStep), a predicate parameter that nothing fixes (K.Ok.seq's
//   invariant after the first statement) stays a hole for the agent (printed ?p<j>); a number never
//   does. bestStep tries premises with closers only (decompose then searches each hole) and keeps
//   its best step past the deadline. A hole that is its goal with one argument changed is "weak".
// * Premises: a callee's parameter that a hypothesis or a proof must give is a fact (isProp: also a
//   one-constructor type of facts, D.P2(..)) or a type that still names other parameters (isPrem:
//   D.HSK(?dk, ..), @st2 -> AlQ(..) -> Q(st2)). A parameter may be filled by a predicate (st2 => ..).
//
// TACTICS (in this order)
// -----------------------
// Node (a def body with pending binders):
//   1. leaf: introduce all pending binders, run the leaf tactics.
//   2. split: `match x:` on a pending binder x of a datatype that blocks evaluation (the strict
//      argument of a stuck call, in the goal or in a hypothesis), each arm solved recursively. The
//      self-call (induction hypothesis) is allowed only below a split; bend2 checks its descent.
// Leaf (a goal in a context), memoized:
//   1. closers: `{==}`, the unit constructor (Unit{}), a hypothesis whose type converts.
//   2. intro: a function goal gets `x => ...`.
//   3. absurd: a hypothesis whose normal form is Empty gives Empty.absurd(GOAL, h) (the goal as stated,
//      kernel rule R3); for Empty goals, a hypothesis that equates two different constructors is
//      discriminated by a predicate def on their type (`%h : P(_); Unit{}`); with depth, an ex-falso
//      lemma (conclusion: its own type parameter) whose premise a closer proves.
//   4. apply: hypotheses (functions, also through aliases), the induction hypothesis, then the indexed
//      lemmas whose conclusion matches (raw against raw goal and normal form, normal form of the
//      conclusion against the normal form of the goal; every distinct solution is tried), most
//      specific pattern first, at most CAPS[level] completions per goal (48, 12, 4, 2 by premise
//      level). A parameter that the conclusion leaves open is fixed by matching a premise against a
//      hypothesis (raw or normal form), else (top level only, depth >= 2) by unifying a premise with
//      an indexed lemma's conclusion (forward: le_trans's middle term). Premises at depth - 1.
//   5. rewrite: `%e : P; rest` with an equation from a hypothesis (raw or normal form, both
//      directions, Equal.sym), the induction hypothesis or an indexed lemma whose side matches a
//      subterm of the goal: of nf(goal), and of the goal as stated (a lemma stated on raw forms); P is
//      that base with the subterm replaced by `_` (kernel rule R2: rewrite, do not convert). In a
//      rewrite, a premise {a == x} with x an open parameter fixes x := a (then {==}). Rewrites of
//      blocking subterms first; a rewrite that closes by {==} wins at once; else the best --beam
//      continue with one less rewrite.
//
// OUTPUT
// ------
// * full proof: the body text on stdout, indented as a def body (two spaces), checked by def_check.
// * partial (--partial, and always in batch): the best skeleton (fewest holes, then most closed
//   subgoals) with ?TODO holes, then for each hole its case path, goal and context (raw and normal
//   form). A hole inside an applied lemma has the path <case path>#<callee>.<parameter index>.
// * streaming (--stream): each closed subgoal (its case path and first line) on stderr.
// * errors (--check, statement errors, failed checks): bend2's Err printed bounded, never with bend2's
//   err_show (its strong normal form of every type overflowed the stack on machine runs: 107 crashes in
//   the DeepSeek runs, and a dump that took 15 GB once). A mismatch prints expected and observed as
//   the checker holds them, then where they differ: the smallest subterms that differ after weak normal
//   forms, with their path (`left of == > List.get(..4)`: the 4th argument of List.get on the left side);
//   then the context with its types as stated, a type over 400 chars cut unless it names a variable of
//   a difference; in --check, a context entry that an earlier error printed is not printed again. Line
//   numbers are the file's.
// * a match bend2 cannot elaborate (a computed scrutinee, or a binder matched after a local statement:
//   a parse error of the whole file): gen2 loads the file with that block as ?TODO (so every other def
//   still works), and each answer prints the error with a fix: a helper def (its statement is the goal
//   at the match over its context; a computed scrutinee is a parameter sc with an equation {sc == v},
//   so the helper holds iff the goal does; its body is the block) and the call that replaces the block,
//   both checked in gen2's book (the result says which part fails).
// * statements: the book is not validated, so each def asked for has its statement checked first
//   (stmtError: "# STATEMENT ERROR", no search), and serve's reload checks every entry def whose
//   header changed ("[gen2] STATEMENT ERROR in <def>" on stderr).
// * on a miss (prove/ask/batch, not bench), for the first open goal: "# why": the lemmas whose
//   conclusion matches it (at most 4) and what blocks each (a premise open, a premise that fits a
//   hypothesis after a split, a premise that fits a part of a tuple hypothesis with the destructuring
//   that names it, a parameter to give); "# similar proven defs": up to 3 proven defs of
//   the entry file whose statements share the most names with it, with their first lines (templates).
//
// BENCHMARK
// ---------
// Rerun: bun tools/gen2/gen2.ts bench <file> --budget 3000 --partial
// Each proven lemma of <file> (book order; a def whose conclusion is a proposition) has its body
// forgotten in memory (no file is touched) and is re-proven with only the defs before it; size class =
// non-empty lines of its original body (S 1-3, M 4-10, L 11+). Measured at commit 95e13d5, budget 3000 ms:
//   file                   tried  full       S       M       L      partial (closed/total)  median
//   need_big.bend          119  81 (68%)   28/36   36/49   17/34   29 (123/161)               8 ms
//   heap_facts.bend         70  57 (81%)   14/14   33/40   10/16   11 (19/32)                 6 ms
//   statement_runs.bend     67  40 (60%)   18/18   19/28   3/21    10 (17/44)                31 ms
//   total                  256  178 (70%); every hit takes < 3 s (median a few ms); a miss runs to the budget,
//   then the partial pass and the decomposition (up to 3 x budget). The kernel (gate) accepts gen2's
//   need_big proofs pasted in place of the originals (bend2 ALL PROOFS CHECK, kdiag3 0 fail).
//   (History and raw results: bb-wt/reports/gen2.md and bb-wt/scratch/gen2/, if present.)
//
// LIMITS
// ------
// * No helper-lemma synthesis in the search (a match on a computed value or an introduced binder needs
//   its own def; gen2 writes that def only for a match the parser rejects, see OUTPUT).
// * Splits only in whole-body mode; ?TODO holes inside a body get leaf tactics only.
// * No lets (`+x = ...`) in output, no congruence tactic beyond rewriting, no templates (~ binders).
// * Matching is syntactic (after the bounded normal form): a lemma stated in a shape that only
//   converts to the goal by deeper computation is missed.
// * Hypotheses are never rewritten (forward reasoning): a fact that needs one hypothesis rewritten
//   by another before a lemma applies (k.cell_of) is missed.
// * Whole simulation proofs (moves.bend's holes) are out of reach: their structure is not found by
//   a bounded search; gen.ts writes those, and gen2 proves the leaves they state.
// * Printed names: a term of a file that the target file does not import under an alias prints as
//   its path name (in goals only; a candidate that needs one fails to parse and is skipped).
//
// NEXT (the ordered plan, for whoever continues; keep it current)
// ----
// 1. Book load between calls: DONE (serve/ask, commit ff24e5e; caches and budget 1000 in serve after
//    3f68666). Servers outside heavy.sh's slots, shared by many agents (per-ask text), replicas:
//    DONE (w/g2pool). Open: keep a few parsed texts (one per recent worktree) instead of re-parsing
//    on every switch; a statement check cache across switches.
// 2. The implementer's 3 misses, in bb-wt/impl src/Compiler/Machine/moves_copy.bend at commit
//    c28021c; the hand proofs there are the references (regression set: add them to a bench-like run
//    with `ask kc.at fs.arg.at kept.at.own --whole --partial`):
//    a. kc.at: destructure the hypothesis hkc : D.Kept.cells(..) (a Tuple of facts) with
//       `match hkc: case Tuple{_, Tuple{kg, _}}`, then apply kept.at.own with xs = List.append(ps, Nil)
//       (bound by matching kg's type) and its premise hm rewritten by mem.app.nil. Today the split
//       candidates open a record only when no blocker exists. Drafted, NOT tested, not committed:
//       open pending binders of one-constructor types with fields first (at most 2), except U32, F32,
//       Chr, Word.Con, Word.Nil (they are records too, and splitting them to bits is useless), in
//       splitCands before the blockers. Measure the three bench files after it (it may cost splits).
//    b. fs.arg.at: ps is general; the proof is one rewrite with e (Equal.sym) of every occurrence of
//       Cr.Cir.Cells.get(M, z) in the normal form of D.Fs(M, ps, z), then {==}. gen2 split on ps
//       instead (D.Mem(ps, z) blocks) and missed the rewrite: check why the leaf rewrite of the
//       unsplit goal fails (motive size cap 600 nodes in rewrite? the normal form keeps D.Fd(..)
//       calls?); with GEN2_TRACE=1 each rewrite candidate and motive is printed.
//    c. kept.at.own: needs U6.kg.at with premises from U13.own.lo, U13.own.end and D.u.lt (through
//       N.le_rw_r, a transitivity-like step with an explicit middle term), then a 2-step rewrite of the
//       D.Kept.if(Bool.or(..)) condition by hm and ht. The lead's diagnosis: induction on the fuel of
//       the recursive hypothesis hk : D.Kept.go(Nat.sub(..), ..) with the fuel generalized, through a
//       helper lemma: synthesize a helper def whose statement is the subgoal with the computed fuel
//       replaced by a fresh variable (and the hypotheses that mention it), prove it whole (split on the
//       fuel, IH), and apply it. That is item 5 below; until then this lemma is out of reach.
// 3. Functions counted as lemmas: FIXED (95e13d5): the bench took `ones` (a function returning
//    Word(n)) for a lemma and pasted another body; isPropType now accepts only propositions. Verified:
//    gen2's 81 need_big proofs pasted in place pass bend2 and the kernel (kdiag3: 0 fail).
// 4. Derived hypotheses (forward reasoning): rewrite a hypothesis by another equation, the term
//    `(%E : P; h)` used as a closer or to bind a lemma's premise (k.cell_of in statement_runs). Drafted
//    in bb-wt/scratch/gen2/p14.py (not applied, not tested). Should move statement_runs M (19/28).
// 5. Helper-lemma synthesis: a match on a computed value, an introduced binder, or a generalized
//    fuel needs its own def; emit the helper (its statement from the subgoal), prove it as a separate
//    job in the same book (parse it into a shadow book: Object.create(book.tlds), as def_check does
//    for templates), and output both. Should move need_big L (17/34) and kept.at.own.
// 6. Fail fast on misses: a miss costs budget + partial pass + decomposition (up to 3 x budget;
//    statement_runs L lemmas take 4-7 s each; serve's budget 1000 caps a miss near 1.7-3 s, and the
//    bench6 data shows 175/178 hits within 1000 ms). A premise not simpler than its goal should cost two
//    levels; memo rewrite candidates per goal; a cheaper decomposition pass.
// 7. Readable motives: stop the normal form at a wrapper def when its unfolding stays stuck
//    (Cr.Cir.is_cell(i, im, fi, nx) instead of its Bool.or body; Cmp.is_lt(U32.cmp(..)) instead of
//    U32.is_lt(..)). Cosmetic, but the hand proofs read better.
// 8. Closed rewrites: zero-parameter lemmas (literal facts such as lit_M) in the rewrite index
//    (need_big val_M, val_65536, sq_65536: S misses).
// 9. Splits inside ?TODO holes of a partial body (the hole's pending binders), not only whole bodies.
// 10. Read bb-wt/reports/impl.md (the implementer's list of leaves gen2 missed) and close those kinds.
//
// EXTEND
// ------
// A new leaf tactic goes in `leaf` (keep the order cheap -> expensive), returning a Pf or null and
// tagging itself in `tags` for the benchmark. A new node tactic goes in `solve`. Candidate lemmas come
// from `lemmaCands` (apply) and `rwIndex` (rewrite).

import * as fs from "node:fs";
import * as path from "node:path";
import * as os from "node:os";
// bend.ts is imported below the ask client (B = await import(..)): `ask` loads nothing, so it starts
// fast and runs in a worktree whose bend submodule is not linked; B.X in a type is erased by bun

type HTerm = B.HTerm;
type LTerm = B.LTerm;

// ---- options ----
const argv = process.argv.slice(2);
const MODE = argv[0], FILE = argv[1], TARGET = argv[2];
const opt = (k: string, d: string) => { const i = argv.indexOf("--" + k); return i >= 0 ? argv[i + 1] : d; };
const flag = (k: string) => argv.includes("--" + k);
let BUDGET = 0, MAX_SPLIT = 0, MAX_DEPTH = 0, MAX_RW = 0, BEAM = 0, FUEL_CHECK = 0, HOLE_BUDGET = 0, ONLY_HOLE = 0;
let DECOMP = true, PARTIAL = false, STREAM = false, DEBUG = false, HELPERS = false, WRITE = false, WP = false;
let IND = false; // --ind (gen2_ind.ts)
const readOpts = () => {
  BUDGET = +opt("budget", MODE === "serve" ? "1000" : "4000");
  MAX_SPLIT = +opt("splits", "6");
  MAX_DEPTH = +opt("depth", "3");
  MAX_RW = +opt("rw", "4");
  BEAM = +opt("beam", "4");
  FUEL_CHECK = +opt("fuel", "300000");
  DECOMP = !flag("no-decomp");
  HOLE_BUDGET = +opt("hole-budget", String(Math.max(300, BUDGET / 4)));
  PARTIAL = flag("partial"); STREAM = flag("stream"); DEBUG = flag("debug");
  WRITE = flag("write"); HELPERS = WRITE || flag("helpers"); ONLY_HOLE = +opt("hole", "0"); WP = flag("wp");
  IND = !flag("no-ind"); // on by default (the coordinator's decision, 2026-11-04); --ind is accepted
};
readOpts();
const FUEL_NF = 100000;
const FUEL_FINAL = 50000000;
const NF_NODES = 3000;
const MAX_CANDS = 48;
const CAPS = [48, 12, 4, 2]; // matched apply candidates tried, by premise level below the leaf
const MAX_SPLIT_CANDS = 3;
const MAX_DECOMP = 2;
const META = 1 << 20;

// ---- stack ----
// bend2's checker, normal forms and printer recurse on a term's depth; JSC's default stack (~40k
// frames, 8 MB on Linux) overflowed on machine-run defs (copy_gives_subst Cp.start, moves_call
// ref.postb). gen2 runs itself again once with a STACK-byte stack (JSC's limit, and the OS's on
// Linux): untouched stack costs no memory, and fuel and the deadline still bound every search.
const STACK = 1 << 30;
if (MODE !== "ask" && process.env.GEN2_STACK === undefined) {
  const env = { ...process.env, GEN2_STACK: String(process.pid), BUN_JSC_maxPerThreadStackUsage: String(STACK) };
  const cmd = process.platform === "win32" ? [process.execPath, ...process.argv.slice(1)]
    : ["sh", "-c", "ulimit -s " + (STACK >> 10) + " 2>/dev/null; exec \"$@\"", "sh", process.execPath, ...process.argv.slice(1)];
  const child = Bun.spawn(cmd, { env, stdio: ["inherit", "inherit", "inherit"] });
  for (const sig of ["SIGINT", "SIGTERM", "SIGHUP"] as const) process.on(sig, () => child.kill(sig));
  process.exit(await child.exited);
}
// the child stops when its parent is gone (a killed `serve` must not keep the port)
if (process.env.GEN2_STACK && process.platform !== "win32") {
  const parent = process.ppid;
  setInterval(() => { if (process.ppid !== parent) process.exit(1); }, 1000).unref();
}

// an Err that escapes: its message and place, never Bun's print of the object (it holds the whole book:
// 300 KB to 15 GB of output)
const fatal = (e: any) => {
  const s = e?.spn;
  console.error("[gen2] " + (e?.$ === "Err" ? "bend2 error: " + (typeof e.exp === "string" ? e.exp : "(a type mismatch)") + (typeof e.obs === "string" ? " (found " + e.obs + ")" : "")
    + (s?.file?.str ? " at line " + s.file.str.slice(0, s.beg).split("\n").length + (s.file.ns ? " of " + s.file.ns : "") + ": " + s.file.str.split("\n")[s.file.str.slice(0, s.beg).split("\n").length - 1]?.trim().slice(0, 300) : "")
    : String(e?.stack ?? e).slice(0, 3000)));
  process.exit(1);
};
process.on("uncaughtException", fatal);
process.on("unhandledRejection", fatal);

// ---- fuel and time ----
class Stop { constructor(readonly why: string) {} }
const OOF = new Stop("fuel"), TIMEOUT = new Stop("time"), LIN = new Stop("linearity");
let fuel = Infinity, deadline = Infinity, ticks = 0, internal = 0;
// the main search stops when no subgoal closed for stallWindow ms (0: off): no progress, answer early
let lastWin = 0, stallWindow = 0;

const attempt = <T>(n: number, f: () => T): T | undefined => {
  const old = fuel;
  fuel = n;
  try {
    return f();
  } catch (e: any) {
    if (e === TIMEOUT) throw e;
    if (!(e instanceof Stop) && !(e instanceof RangeError) && !(e && e.$ === "Err")) {
      internal++;
      if (DEBUG) console.error("[gen2] internal:", e?.stack ?? e);
    }
    return undefined;
  } finally {
    fuel = old;
  }
};

// ---- ask: a client of `serve` (loads nothing) ----
// With --file F: F is the asker's own copy of the entry; its text goes with the request (to the server on
// --port, default 7311).
const gitRoot = (f: string): string | null => {
  for (let d = path.dirname(f); ; d = path.dirname(d)) {
    if (fs.existsSync(path.join(d, ".git"))) return d;
    if (path.dirname(d) === d) return null;
  }
};
const posix = (p: string) => p.split(path.sep).join("/");
if (MODE === "ask") {
  const fi = argv.indexOf("--file");
  const args = argv.slice(1).filter((_, i) => fi < 0 || (i + 1 !== fi && i + 1 !== fi + 1));
  let port = +opt("port", "0"), shared: { text: string; rel: string; root: string; file: string } | undefined;
  if (fi >= 0) {
    const file = path.resolve(argv[fi + 1] ?? "");
    if (!fs.existsSync(file)) { console.error("gen2 ask: no file " + file); process.exit(1); }
    const root = gitRoot(file);
    if (!root) { console.error("gen2 ask: " + file + " is not in a git worktree"); process.exit(1); }
    const rel = posix(path.relative(path.join(root, "src"), file));
    shared = { text: fs.readFileSync(file, "utf8"), rel, root: posix(root), file };
  }
  port ||= 7311;
  const res = await fetch("http://127.0.0.1:" + port + "/prove", { method: "POST", timeout: false, body: JSON.stringify({ args, ...(shared ? { text: shared.text, rel: shared.rel, root: shared.root } : {}) }) }).catch((e) => null);
  if (!res) { console.error("gen2 ask: no server on port " + port + " (start one: bun tools/gen2/gen2.ts serve <file.bend>)"); process.exit(1); }
  const r: any = await res.json();
  if (r.stderr) process.stderr.write(r.stderr);
  if (r.stdout) process.stdout.write(r.stdout);
  if (shared && typeof r.write === "string") {
    // --write: the server returns the new text; it lands only if the file is still the text it read
    if (fs.readFileSync(shared.file, "utf8") === shared.text) { fs.writeFileSync(shared.file, r.write); console.error("[gen2] wrote " + shared.file); }
    else console.error("[gen2] --write skipped: " + shared.file + " changed while gen2 worked (ask again)");
  }
  process.exit(r.code);
}
// the arguments, before anything loads: a clear message and a non-zero exit, never a stack
if (!["prove", "batch", "bench", "serve"].includes(MODE)) {
  console.error("usage: bun tools/gen2/gen2.ts prove <file.bend> <def> [<def> ...] [options] | serve <file.bend> | ask <def> ... (see the header)");
  process.exit(2);
}
if (!FILE || !fs.existsSync(FILE) || !fs.statSync(FILE).isFile()) {
  console.error("[gen2] no such file: " + (FILE ?? "(none given)"));
  process.exit(2);
}
const B = (await import("./bend2.ts")).default;
// --wp steps bend-bootstrap's own machine (its Cir code): not part of bend-ver, so it is off here
const wpProve = (..._: any[]): any => ({ open: -1, why: "--wp is not available in bend-ver (it steps bend-bootstrap's machine)" });
if (WP) { console.error("[gen2] --wp is not available in bend-ver (it steps bend-bootstrap's machine)"); process.exit(1); }
const Ind = await import("./gen2_ind.ts");

// ---- load ----
const entry = fs.realpathSync(path.resolve(FILE ?? ""));
const TOP = path.dirname(entry) + "/";
const entryText = fs.readFileSync(entry, "utf8");
const entryNames = new Set([...entryText.matchAll(/^def\s+([A-Za-z_][\w.]*)\(/gm)].flatMap((m) => [m[1], m[1].replace(/^[^.]+\./, "")]));
const autoImports: { file: string; alias: string; ns: string; proofs: Set<string> }[] = [];
if (entryText.includes("?TODO")) {
  for (const name of fs.readdirSync(TOP).filter((n) => n.endsWith(".bend") && path.join(TOP, n) !== entry)) {
    const proofs = new Set([...fs.readFileSync(path.join(TOP, name), "utf8").matchAll(/^def\s+([A-Za-z_][\w.]*)\.proof\(/gm)]
      .map((m) => m[1]).filter((n) => entryNames.has(n)));
    if (proofs.size > 0) autoImports.push({ file: path.join(TOP, name), alias: "Gen2" + path.basename(name, ".bend").replace(/(^|_)([a-z])/g, (_, __, c) => c.toUpperCase()), ns: path.basename(name, ".bend"), proofs });
  }
}
const spanFile = (t: any, n = 0): B.File | undefined => {
  if (!t || n > 50) return undefined;
  if (t.s?.file) return t.s.file;
  if (t.$ === "All") return spanFile(t.A, n + 1) ?? spanFile(t.B(B.Var("_", 0)), n + 1);
  return undefined;
};
// a match that bend2 cannot elaborate: bend2 matches only the def's own pending binders, so a match on
// a computed value, or on a binder after a local statement, needs its own def (the parser's errors
// below). The block that holds it, in the text the parser read (line indexes = the file's): the
// statement's lines S..H (`match x:`, or a destructuring `pat = value`), then its block up to E
// (exclusive): the arms, or the rest of the local's block.
type Blk = { S: number; H: number; E: number; ind: string; kind: "match" | "local"; scrut: string; pat: string };
const SCRUT_ERR = /^a parameter or field scrutinee|can't be matched in this position/;
const DEF_LINE = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/;
const brackets = (l: string) => { let b = 0; for (const ch of l.replace(/#.*$/, "")) { if ("([{".includes(ch)) b++; else if (")]}".includes(ch)) b--; } return b; };
const blockAt = (str: string, beg: number): Blk | null => {
  const lines = str.split("\n");
  const L = str.slice(0, beg).split("\n").length - 1;
  let D = L;
  while (D >= 0 && !DEF_LINE.test(lines[D])) D--;
  if (D < 0) return null;
  const open: number[] = [];
  for (let i = D, b = 0; i <= L; i++) { open[i] = b; b += brackets(lines[i]); }
  let S = L;
  while (S > D && open[S] > 0) S--;
  if (S === D) return null;
  let H = S;
  for (let b = brackets(lines[S]); b > 0 && H + 1 < lines.length; ) b += brackets(lines[++H]);
  const head = lines.slice(S, H + 1).map((l) => l.replace(/#.*$/, "").trim()).join(" ");
  const m = /^match\s+(.*):$/.exec(head);
  const lm = m ? null : /^(.+?)\s+=\s+(.+)$/.exec(head);
  if (!m && !lm) return null;
  const ind = /^\s*/.exec(lines[S])![0];
  let E = H + 1;
  for (; E < lines.length; E++) {
    const t = lines[E].trim();
    if (t === "" || t.startsWith("#")) continue;
    const li = /^\s*/.exec(lines[E])![0].length;
    if (m ? li <= ind.length : li < ind.length) break;
  }
  while (E > H + 1 && (lines[E - 1].trim() === "" || lines[E - 1].trim().startsWith("#"))) E--;
  return { S, H, E, ind, kind: m ? "match" : "local", scrut: (m ? m[1] : lm![2]).trim(), pat: m ? "" : lm![1].trim() };
};
// text with the block's lines replaced by one hole (the line numbers kept)
const holeOut = (lines: string[], blk: Blk, hole: string): string[] =>
  [...lines.slice(0, blk.S), blk.ind + hole, ...Array(blk.E - blk.S - 1).fill(""), ...lines.slice(blk.E)];
// the entry's parse error of that kind: the book holds the entry with the block as ?TODO, so that every
// other def still works; each answer prints the error first, with the helper def that fixes it (scrutFix)
let parseErr: { err: B.Err; blk: Blk } | null = null;
// parse the entry's text into bk (its imports loaded): on a match error, parse it again with the block as
// ?TODO and set parseErr; fresh: a book with the imports only (parse_book may have added a part)
const parseEntry = (bk: B.Book, str: string, al: Record<string, string>, fresh: () => B.Book): B.Book => {
  parseErr = null;
  try {
    B.parse_book(bk, TOP, str, "", al);
    return bk;
  } catch (e: any) {
    const blk = e?.$ === "Err" && e.spn && SCRUT_ERR.test(String(e.exp)) ? blockAt(e.spn.file.str, e.spn.beg) : null;
    if (!blk) throw e;
    const nb = fresh();
    B.parse_book(nb, TOP, holeOut(str.split("\n"), blk, "?TODO").join("\n"), "", al);
    parseErr = { err: e, blk };
    return nb;
  }
};
const book = B.book_nil();
const seen = new Map<string, string | null>();
for (const imp of autoImports) await B.book_load(book, imp.file, imp.ns, seen, undefined, TOP);
let validErr: unknown = null;
// bend2 loads the entry's imports itself, under its own module names (so the entry's aliases, such as
// `import ./spec.bend as Spec` and `def Spec.law(..)`, resolve); a match error in the entry is parsed
// again with the block as ?TODO
let N0 = await (async () => {
  const n0 = book.order.length, tlds = { ...book.tlds }, ctrs = { ...book.ctrs };
  try {
    return await B.book_load(book, entry, "", seen, undefined, TOP); // the entry's first entry in book order
  } catch (e: any) {
    // a match error in the entry (its Parse holds the text and aliases): parse it again with the block
    // as ?TODO, on the book as it was before the entry
    const p = e?.$ === "Err" ? (e.spn?.file as B.Parse | undefined) : undefined;
    const blk = p && "book" in p && SCRUT_ERR.test(String(e.exp)) ? blockAt(p.str, e.spn.beg) : null;
    if (!blk) throw e;
    book.tlds = Object.assign(Object.create(null), tlds);
    book.ctrs = Object.assign(Object.create(null), ctrs);
    book.order.length = n0;
    B.parse_book(book, TOP, holeOut(p!.str.split("\n"), blk, "?TODO").join("\n"), "", p!.al);
    parseErr = { err: e, blk };
    return n0;
  }
})().catch((e: any) => {
  // the book cannot load: print bend2's error bounded (Bun's own print of an Err dumps the whole book)
  const f = e?.spn?.file;
  const line = e?.spn && f?.str ? f.str.slice(0, e.spn.beg).split("\n").length : 0;
  console.error("[gen2] cannot load " + FILE + ": " + (typeof e?.exp === "string" ? e.exp : "error") + (typeof e?.obs === "string" ? " (found " + e.obs + ")" : "") + (line ? "\n  at line " + line + (f.ns ? " of " + f.ns : "") + ": " + f.str.split("\n")[line - 1].trim().slice(0, 300) : ""));
  if (e?.$ !== "Err") console.error(String(e?.stack ?? e).slice(0, 2000));
  process.exit(1);
});
const tLoad = performance.now();
if (STREAM) console.error("[gen2] loaded book in " + Math.round(tLoad) + " ms");
if (flag("validate-book")) {
  try { B.book_valid(book, N0); } catch (e) { validErr = e; }
}
const tValid = performance.now();
if (STREAM) console.error("[gen2] " + (flag("validate-book") ? "validated book in " + Math.round(tValid - tLoad) + " ms" : "skipped whole-book validation"));
const RAW: Record<string, B.TLD> = book.tlds;
book.tlds = new Proxy(RAW, {
  get(t, k, r) {
    if (--fuel < 0) throw OOF;
    if ((++ticks & 4095) === 0) { const now = performance.now(); if (now > deadline || (stallWindow > 0 && now > lastWin + stallWindow)) throw TIMEOUT; }
    return Reflect.get(t, k, r);
  },
});
const ORDER = new Map<string, number>();
book.order.forEach((k, i) => ORDER.set(k, i));

// ---- source text of defs ----
type Src = { file: string; header: string; body: string; bodyLine: number };
const texts = new Map<string, string>();
const fileText = (f: string) => { let t = texts.get(f); if (t === undefined) { t = fs.readFileSync(f, "utf8"); texts.set(f, t); } return t; };
const fileLines = new Map<string, string[]>();
const defLines = new Map<string, Map<string, number>>();
const linesOf = (file: string) => {
  let lines = fileLines.get(file);
  if (!lines) { lines = fileText(file).split("\n"); fileLines.set(file, lines); }
  return lines;
};
const defLine = (file: string, name: string) => {
  let defs = defLines.get(file);
  if (!defs) {
    // exact names first, then the names less their first segment (D.alloc.post as alloc.post) only
    // where no def has that exact name (and.nf.st must not hide nf.st)
    defs = new Map();
    const found: [string, number][] = [];
    linesOf(file).forEach((line, i) => {
      const m = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/.exec(line);
      if (m) found.push([m[1], i]);
    });
    for (const [nm, i] of found) if (!defs.has(nm)) defs.set(nm, i);
    for (const [nm, i] of found) { const sf = nm.slice(nm.indexOf(".") + 1); if (!defs.has(sf)) defs.set(sf, i); }
    defLines.set(file, defs);
  }
  return defs.get(name) ?? -1;
};
const nsOf = (k: string) => (k.includes(":") ? k.slice(0, k.indexOf(":")) : "");
const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
const pathOf = (k: string) => {
  if ((ORDER.get(k) ?? -1) >= N0) return entry;
  return nsOf(k) === "" ? entry : path.resolve(TOP, nsOf(k) + ".bend");
};
const srcCache = new Map<string, Src | null>();
const fileExists = new Map<string, boolean>(); // cleared with srcCache
const defSrc = (k: string): Src | null => {
  if (srcCache.has(k)) return srcCache.get(k)!;
  let res: Src | null = null;
  const file = pathOf(k);
  let ex = fileExists.get(file);
  if (ex === undefined) { ex = fs.existsSync(file); fileExists.set(file, ex); }
  if (ex) {
    const lines = linesOf(file);
    const li = defLine(file, shortOf(k));
    if (li >= 0) {
      let depth = 0, he = li;
      for (; he < lines.length; he++) {
        const l = lines[he].replace(/#.*$/, "");
        for (const ch of l) { if ("([{".includes(ch)) depth++; else if (")]}".includes(ch)) depth--; }
        if (depth <= 0 && /:\s*$/.test(l)) break;
      }
      // the body: indented or blank lines, and any line inside an open bracket (a body may continue at
      // column 0 inside parentheses: alfr.fresh.at in heap_ops.bend)
      let be = he + 1, bd = 0;
      while (be < lines.length && (lines[be].startsWith(" ") || lines[be].trim() === "" || bd > 0)) {
        for (const ch of lines[be].replace(/#.*$/, "")) { if ("([{".includes(ch)) bd++; else if (")]}".includes(ch)) bd--; }
        be++;
      }
      while (be > he + 1 && (lines[be - 1].trim() === "" || lines[be - 1].trim().startsWith("#"))) be--;
      res = { file, header: lines.slice(li, he + 1).join("\n"), body: lines.slice(he + 1, be).join("\n"), bodyLine: he + 1 };
    }
  }
  srcCache.set(k, res);
  return res;
};

const sourceFiles = new Map<string, B.File>();
for (const k of book.order) {
  const t = RAW[k];
  if (t?.$ === "Def") {
    const f = spanFile(t.v) ?? spanFile(t.T);
    if (f) sourceFiles.set(k, f);
  }
}
for (const k of book.order.slice(N0)) {
  const file = sourceFiles.get(k);
  if (file) for (const imp of autoImports) file.al[imp.alias] = imp.ns;
}
const openBySource = new Map<string, Set<string>>();
const tempOpen = new Set<string>(); // --ind: temp defs being proven (gen2_ind.ts)
const isOpen = (k: string) => {
  if (IND && tempOpen.has(k)) return true;
  const source = sourceFiles.get(k)?.str;
  if (!source) return false;
  let names = openBySource.get(source);
  if (!names) {
    names = new Set();
    let current = "";
    for (const line of source.split("\n")) {
      const def = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/.exec(line);
      if (def) current = def[1];
      else if (current && line.includes("?TODO") && !line.trimStart().startsWith("#")) {
        names.add(current);
        names.add(current.slice(current.indexOf(".") + 1));
      }
    }
    openBySource.set(source, names);
  }
  return names.has(shortOf(k));
};

// the error of k's statement (bend2's term_check of its type, as book_valid does), or null if it checks;
// the book is loaded without validation, so a new helper's ill-typed statement would only show as a miss
const stmtError = (k: string, shown?: Set<string>): string | null => {
  const t = RAW[k];
  if (t?.$ !== "Def") return null;
  const old = fuel;
  fuel = FUEL_FINAL;
  try {
    B.term_check(book, { t: B.Ref(k), n: 0, def: k, qs: [], u: t.u }, t.T, B.None(), B.Typ(B.Qua(B.Lone())), B.ctx_nil(), 0);
    return null;
  } catch (e: any) {
    return e === OOF ? null : errText(e, flag("full-errors"), shown);
  } finally { fuel = old; }
};

// the file line of the first line of a text that checkDef parsed (errors show file line numbers)
const lineBase = new WeakMap<object, number>();
// checks <def> with the body text <body> (a def body, indented); throws bend2's Err on failure
// (header, file: of a def that is in no file yet, as scrutFix's helper)
const checkDef = (k: string, body: string, header = defSrc(k)!.header, file = sourceFiles.get(k)!) => {
  const def = RAW[k] as B.Def;
  const str = header + "\n" + body + "\n";
  const p: B.Parse = { book, dir: path.dirname(defSrc(k)?.file ?? entry) + "/", str, pos: str.indexOf("(") + 1, stk: [], frs: 0, ns: file.ns, al: file.al };
  const ds = defSrc(k);
  if (ds && header === ds.header) lineBase.set(p, ds.bodyLine - header.split("\n").length);
  const hols = book.hols;
  const tele = B.parse_tele(p, ")");
  p.pos = header.length;
  const vars = tele.map((c): B.PVar => ({ $: "PVar", k: c[1], i: c[2], q: B.Lone(), s: c[4] }));
  const v = B.term_higher(B.term_lower(B.term_higher(B.body_flatten(B.parse_body(p), vars, () => p.frs++))));
  B.parse_skip(p);
  book.hols = hols;
  if (p.pos < str.length) B.parse_fail(p, "the end of the body");
  B.def_check(book, k, { ...def, v });
};

// ---- terms ----
const lit = (k: "Nat" | "U32", v: number): LTerm => B.Lit(k, v);
const canon = (t: LTerm): LTerm => {
  switch (t.$) {
    case "Ctr": {
      const x = t.x.map(canon);
      if (t.k === "Zero" && x.length === 0) return lit("Nat", 0);
      if (t.k === "Succ" && x.length === 1 && x[0].$ === "Lit" && x[0].k === "Nat") return lit("Nat", (x[0].v as number) + 1);
      const c = B.Ctr<[LTerm]>(t.k, x);
      if (t.k === "U32") { const u = B.u32_from_term(c); if (u !== null) return lit("U32", u); }
      return c;
    }
    case "App": return B.App(canon(t.f), canon(t.x));
    case "Eql": return B.Eql(canon(t.a), canon(t.b), canon(t.T));
    case "ADT": return B.ADT(t.k, t.x.map(canon), undefined, t.r);
    case "All": return B.All<LTerm>(t.q, t.k, t.i, canon(t.A), canon(t.B as LTerm));
    case "Lam": return B.Lam<LTerm>(t.k, t.i, canon(t.f as LTerm), undefined, t.q);
    case "Ann": return canon(t.x);
    case "Var": return t.v !== undefined && t.i >= 0 ? B.Var(t.k, t.i) : t;
    case "Ref": { const a = RAW[t.k]; return a?.$ === "ADT" && a.n === 0 ? B.ADT(t.k, [], undefined, []) : t; } // U32 is <U32> once whnf'd
    default: return t;
  }
};
const lower = (h: HTerm, d: number): LTerm => canon(B.term_lower(h, d));

const key = (t: LTerm): string => {
  switch (t.$) {
    case "Var": return "$" + t.i;
    case "Ref": return "@" + t.k;
    case "App": return "(" + key(t.f) + " " + key(t.x) + ")";
    case "Ctr": return t.k + "{" + t.x.map(key).join(",") + "}";
    case "Lit": return "#" + t.k + String(t.v);
    case "Eql": return "{" + key(t.a) + "==" + key(t.b) + ":" + key(t.T) + "}";
    case "ADT": return "<" + t.k + " " + t.x.map(key).join(",") + "-" + t.r.join(",") + ">";
    case "All": return "A" + t.q.$[0] + t.i + "(" + key(t.A) + ")" + key(t.B as LTerm);
    case "Lam": return "L" + t.i + key(t.f as LTerm);
    default: return B.term_key(t);
  }
};
// node count, stopping past cap (iterative: a deep term cannot overflow the stack)
const size = (t0: LTerm, cap = 100000): number => {
  const st: LTerm[] = [t0];
  let n = 0;
  while (st.length && n <= cap) {
    const t = st.pop()!;
    n++;
    switch (t.$) {
      case "App": st.push(t.f, t.x); break;
      case "Ctr": case "ADT": st.push(...t.x); break;
      case "Eql": st.push(t.a, t.b); break;
      case "All": st.push(t.A, t.B as LTerm); break;
      case "Lam": st.push(t.f as LTerm); break;
    }
  }
  return n;
};
const unapply = (t: LTerm): [LTerm, LTerm[]] => B.term_unapply(t);
const hasMeta = (t: LTerm): boolean => {
  switch (t.$) {
    case "Var": return t.i >= META;
    case "App": return hasMeta(t.f) || hasMeta(t.x);
    case "Ctr": case "ADT": return t.x.some(hasMeta);
    case "Eql": return hasMeta(t.a) || hasMeta(t.b) || hasMeta(t.T);
    case "All": return hasMeta(t.A) || hasMeta(t.B as LTerm);
    case "Lam": return hasMeta(t.f as LTerm);
    default: return false;
  }
};
// every variable of t is below d or bound inside t (a binder's own level i: a predicate st2 => ..
// may fill a parameter Q)
const closedBelow = (t: LTerm, d: number, bound: number[] = []): boolean => {
  switch (t.$) {
    case "Var": return t.i < d || bound.includes(t.i);
    case "App": return closedBelow(t.f, d, bound) && closedBelow(t.x, d, bound);
    case "Ctr": case "ADT": return t.x.every((x) => closedBelow(x, d, bound));
    case "Eql": return closedBelow(t.a, d, bound) && closedBelow(t.b, d, bound) && closedBelow(t.T, d, bound);
    case "All": return closedBelow(t.A, d, bound) && closedBelow(t.B as LTerm, d, [...bound, t.i]);
    case "Lam": return closedBelow(t.f as LTerm, d, [...bound, t.i]);
    case "Let": case "Mat": case "Use": return false;
    default: return true;
  }
};
const replace = (t: LTerm, k: string, by: LTerm): LTerm => {
  if (key(t) === k) return by;
  switch (t.$) {
    case "App": return B.App(replace(t.f, k, by), replace(t.x, k, by));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map((x) => replace(x, k, by)));
    case "Eql": return B.Eql(replace(t.a, k, by), replace(t.b, k, by), t.T);
    case "ADT": return B.ADT(t.k, t.x.map((x) => replace(x, k, by)), undefined, t.r);
    default: return t;
  }
};
const subterms = (t: LTerm, out: Map<string, LTerm>) => {
  out.set(key(t), t);
  switch (t.$) {
    case "App": { const [h, xs] = unapply(t); if (h.$ !== "Ref") subterms(t.f, out); xs.forEach((x) => subterms(x, out)); break; }
    case "Ctr": case "ADT": t.x.forEach((x) => subterms(x, out)); break;
    case "Eql": subterms(t.a, out); subterms(t.b, out); break;
  }
};
const litStep = (t: LTerm): LTerm | null => (t.$ === "Lit" && (t.k === "Nat" || t.k === "U32") ? canonShallow(B.lit_step(t)) : null);
const canonShallow = (t: LTerm): LTerm => t;

// when set (diagnosis only), a constructor of the pattern against a context variable of the target is
// recorded here instead of failing: the match holds once that variable is split to that constructor
let clashes: [number, string][] | null = null;
const match = (p: LTerm, t: LTerm, sol: (LTerm | null)[], d: number): boolean => {
  if (clashes && p.$ === "Ctr" && t.$ === "Var" && t.i < META) { clashes.push([t.i, p.k]); return true; }
  if (p.$ === "Var" && p.i >= META) {
    const s = sol[p.i - META];
    if (s) return key(s) === key(t);
    if (!closedBelow(t, d)) return false;
    sol[p.i - META] = t;
    return true;
  }
  switch (p.$) {
    case "Var": return t.$ === "Var" && t.i === p.i;
    case "Ref": return t.$ === "Ref" && t.k === p.k;
    case "App": return t.$ === "App" && match(p.f, t.f, sol, d) && match(p.x, t.x, sol, d);
    case "Ctr": {
      if (t.$ === "Lit") { const s = litStep(t); if (!s) return false; t = s; }
      return t.$ === "Ctr" && t.k === p.k && t.x.length === p.x.length && p.x.every((x, i) => match(x, (t as any).x[i], sol, d));
    }
    case "Lit": {
      if (t.$ === "Lit") return t.k === p.k && t.v === p.v;
      if (t.$ === "Ctr") { const s = litStep(p); return s !== null && match(s, t, sol, d); }
      return false;
    }
    case "Eql": {
      if (t.$ !== "Eql" || !match(p.a, t.a, sol, d) || !match(p.b, t.b, sol, d)) return false;
      const s2 = sol.slice();
      if (match(p.T, t.T, s2, d)) for (let i = 0; i < sol.length; i++) sol[i] = s2[i];
      return true;
    }
    case "ADT": return t.$ === "ADT" && t.k === p.k && t.x.length === p.x.length && t.r.join() === p.r.join() && p.x.every((x, i) => match(x, (t as any).x[i], sol, d));
    case "All": return t.$ === "All" && t.q.$ === p.q.$ && match(p.A, t.A, sol, d) && match(p.B as LTerm, t.B as LTerm, sol, d);
    case "Lam": return t.$ === "Lam" && match(p.f as LTerm, t.f as LTerm, sol, d);
    case "Typ": return t.$ === "Typ" && match(p.g, t.g, sol, d);
    default: return key(p) === key(t);
  }
};

// ---- normal form ----
const wnf = (h: HTerm): HTerm | undefined => attempt(FUEL_NF, () => B.term_wnf(book, h));
const nfGo = (h: HTerm, d: number, b: { n: number }): LTerm => {
  b.n--;
  const w = wnf(h) ?? B.term_strip(h);
  switch (w.$) {
    case "App": {
      const [hd, xs] = B.term_unapply(w);
      const f = B.term_strip(hd);
      if (f.$ === "Ref") return xs.reduce<LTerm>((r, x) => B.App(r, nfArg(x, d, b)), B.Ref(f.k));
      return B.term_lower(w, d);
    }
    case "Ctr": return B.Ctr<[LTerm]>(w.k, w.x.map((x) => nfArg(x, d, b)));
    case "Eql": return B.Eql(nfArg(w.a, d, b), nfArg(w.b, d, b), B.term_lower(w.T, d));
    default: return B.term_lower(w, d);
  }
};
const nfArg = (x: HTerm, d: number, b: { n: number }): LTerm => {
  if (b.n <= 0) return B.term_lower(x, d);
  const s = B.term_strip(x);
  if (s.$ === "Ref") {
    const t = RAW[s.k];
    if (t?.$ === "Def" && t.n === 0 && t.v !== null) {
      const lb = { n: 24 };
      const r = nfGo(s, d, lb);
      return lb.n <= 0 ? B.Ref(s.k) : r;
    }
  }
  return nfGo(x, d, b);
};
const nf = (h: HTerm, d: number): LTerm => canon(nfGo(h, d, { n: NF_NODES }));

// ---- errors ----
// bend2's err_show prints every type in strong normal form (term_snf: unbounded, and a tree walk of
// shared cells), which overflowed the stack on machine runs and buried a mismatch under walls of
// Cr.Cir.eval terms. errText prints the same Err bounded: each term lowered with a node budget (the
// rest is "…"); for a mismatch, first the smallest subterms where expected and observed differ after
// weak normal forms, as term_compare walks them (each with its path); then the context, its types as
// stated (no normal form), a long one elided unless it names a variable of a difference.
const ERR_NODES = 400, CTX_CHARS = 400, MAX_DIFFS = 4;
const ELL = B.Ref("…") as LTerm;
const lowerCut = (h: HTerm, d: number, b: { n: number }): LTerm => {
  if (--b.n < 0) return ELL;
  const t = B.term_strip(h);
  const go = (x: HTerm, dd = d) => lowerCut(x, dd, b);
  switch (t.$) {
    case "All": { const x = B.Var(t.k, d); return B.All<LTerm>(t.q, t.k, d, go(t.A), go(t.B(x), d + 1)); }
    case "Lam": { const x = B.Var(t.k, d); return B.Lam<LTerm>(t.k, d, go(t.f(x), d + 1), undefined, t.q); }
    case "App": { const [f, xs] = B.term_unapply(t); return xs.reduce<LTerm>((r, x) => B.App(r, go(x)), go(f)); }
    case "ADT": return B.ADT(t.k, t.x.map((x) => go(x)), undefined, t.r);
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map((x) => go(x)));
    case "Eql": return B.Eql(go(t.a), go(t.b), go(t.T));
    case "Typ": return B.Typ(go(t.g));
    case "Mat": return B.Mat(t.k, go(t.h), go(t.m));
    case "Rwt": return B.Rwt(go(t.e), go(t.p), go(t.f));
    case "Let": case "Sub": return ELL;
    default: return t as LTerm;
  }
};
const clipTo = (s: string, n: number) => (s.length > n ? s.slice(0, n) + " … [" + (s.length - n) + " more chars]" : s);
// t (at depth d, its variables named by names) printed within ERR_NODES nodes; never throws
const showCut = (t: HTerm, d: number, names: string[], file: B.File | undefined, nodes = ERR_NODES): string => {
  try {
    return B.term_show(lowerCut(t, d, { n: nodes }), -1, names.slice(), file);
  } catch (e: any) {
    return "<not printable: " + String(e?.message ?? e).slice(0, 80) + ">";
  }
};
// the subterms where a and b differ (at most MAX_DIFFS): both in weak normal form; a pair of the same
// shape (constructor, stuck call of the same def, equation, type, binder) is entered, an equal pair
// (term_compare) skipped; a pair that differs at its head is a difference
type Diff = { path: string[]; a0: HTerm; b0: HTerm; a: HTerm; b: HTerm; d: number; names: string[] };
const diffsOf = (a0: HTerm, b0: HTerm, d: number, names: string[], path: string[], out: Diff[], top = false): void => {
  if (out.length >= MAX_DIFFS || path.length > 200) return;
  if (!top && attempt(FUEL_NF, () => B.term_compare("EQ", book, a0, b0, d)) === true) return;
  let a = wnf(a0) ?? B.term_strip(a0), b = wnf(b0) ?? B.term_strip(b0);
  if (a.$ === "Lit" && b.$ === "Ctr") a = B.lit_step(a);
  if (b.$ === "Lit" && a.$ === "Ctr") b = B.lit_step(b);
  const n0 = out.length;
  const sub = (x: HTerm, y: HTerm, step: string, dd = d, nn = names) => diffsOf(x, y, dd, nn, [...path, step], out);
  if (a.$ === "Lam" && b.$ === "Lam") {
    const x = B.Var(a.k, d);
    sub(a.f(x), b.f(x), "fun " + a.k, d + 1, [...names, a.k]);
  } else if (a.$ === "Ctr" && b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length) {
    a.x.forEach((x, i) => sub(x, b.x[i], shortOf(a.k) + "{.." + (i + 1) + "}"));
  } else if (a.$ === "ADT" && b.$ === "ADT" && a.k === b.k && a.x.length === b.x.length) {
    a.x.forEach((x, i) => sub(x, b.x[i], shortOf(a.k) + "<.." + (i + 1) + ">"));
  } else if (a.$ === "Eql" && b.$ === "Eql") {
    sub(a.a, b.a, "left of =="); sub(a.b, b.b, "right of =="); sub(a.T, b.T, "type of ==");
  } else if (a.$ === "All" && b.$ === "All" && a.q.$ === b.q.$) {
    const x = B.Var(a.k, d);
    sub(a.A, b.A, "type of " + a.k); sub(a.B(x), b.B(x), "after " + a.k, d + 1, [...names, a.k]);
  } else if (a.$ === "App" && b.$ === "App") {
    const [fa, xa] = B.term_unapply(a), [fb, xb] = B.term_unapply(b);
    const ha = B.term_strip(fa), hb = B.term_strip(fb);
    if (ha.$ === "Ref" && hb.$ === "Ref" && ha.k === hb.k && xa.length === xb.length) xa.forEach((x, i) => sub(x, xb[i], shortOf(ha.k) + "(.." + (i + 1) + ")"));
  }
  if (out.length === n0) out.push({ path, a0, b0, a, b, d, names });
};
// the variables named in t (lowered at depth d): a context entry that names one of a difference's
// variables is kept whole
const varsOf = (t: LTerm, names: string[], out: Set<string>) => {
  const st: LTerm[] = [t];
  while (st.length) {
    const x = st.pop()!;
    switch (x.$) {
      case "Var": if (x.i >= 0 && x.i < names.length) out.add(names[x.i]); break;
      case "App": st.push(x.f, x.x); break;
      case "Ctr": case "ADT": st.push(...x.x); break;
      case "Eql": st.push(x.a, x.b, x.T); break;
      case "All": st.push(x.A, x.B as LTerm); break;
      case "Lam": st.push(x.f as LTerm); break;
    }
  }
};
const errLocation = (err: B.Err): string => {
  const def = err.def === undefined ? "" : " " + B.name_show(err.spn?.file, err.def);
  if (err.spn === undefined) return def === "" ? "" : "\nLocation:" + def;
  const str = err.spn.file.str;
  const lns = str.split("\n");
  const pre = str.slice(0, err.spn.beg).split("\n");
  const at = pre.length, beg = Math.max(1, at - 1), end = Math.min(lns.length, at + 1), base = lineBase.get(err.spn.file) ?? 0, num = String(end + base).length;
  const lft = pre[at - 1];
  const car = " ".repeat(num) + " | " + lft.replace(/[^\t]/g, " ") + "^".repeat(Math.max(1, Math.min(err.spn.end - err.spn.beg, lns[at - 1].length - lft.length, 300 - lft.length)));
  const other = !lineBase.has(err.spn.file) && err.spn.file.ns ? " (in " + err.spn.file.ns + ".bend)" : "";
  return "\nLocation:" + def + other + "\n" + lns.slice(beg - 1, end).map((l, j) => String(base + beg + j).padStart(num) + (beg + j === at ? ">| " + clipTo(l, 300) + "\n" + car : " | " + clipTo(l, 300))).join("\n");
};
// bend2's Err as text, bounded (see above); full: no elision of context entries (still bounded)
const errText = (e: any, full = flag("full-errors"), shown?: Set<string>): string => {
  if (e?.$ !== "Err") return e === OOF ? "out of fuel (" + FUEL_FINAL + " def lookups): not decided" : String(e?.stack ?? e?.message ?? e).slice(0, 1500);
  const err = e as B.Err;
  const file = err.spn?.file;
  const anns = B.pmap_to_array(err.ctx).sort((x, y) => x[0] - y[0]);
  const names = B.ctx_scope(err.ctx);
  const d = names.length;
  const old = fuel;
  fuel = Infinity;
  try {
    const out: string[] = ["Error:"];
    const keep = new Set<string>();
    if (err.obs === undefined || typeof err.exp === "string" || typeof err.obs === "string" || err.obs.$ === "Hol") {
      const ex = (x: B.Expr) => (typeof x === "string" ? x : showCut(x, d, names, file));
      out.push(err.obs === undefined ? "- message  : " + ex(err.exp)
        : typeof err.obs !== "string" && err.obs.$ === "Hol" ? "- goal of ?" + err.obs.k + " : " + ex(err.exp)
        : "- expected : " + ex(err.exp) + "\n- observed : " + ex(err.obs));
    } else {
      const ds: Diff[] = [];
      diffsOf(err.exp, err.obs, d, names, [], ds, true);
      out.push("- expected : " + clipTo(showCut(err.exp, d, names, file), 1200), "- observed : " + clipTo(showCut(err.obs, d, names, file), 1200));
      if (ds.length !== 1 || ds[0]!.path.length > 0) out.push("- where they differ (" + ds.length + (ds.length >= MAX_DIFFS ? "+" : "") + "; each side in weak normal form, its arguments as the checker holds them):");
      if (ds.length !== 1 || ds[0]!.path.length > 0) ds.forEach((x, i) => {
        const at = x.path.length ? x.path.join(" > ") : "(the whole type)";
        const ea = attempt(FUEL_NF, () => nf(x.a, x.d)), ob = attempt(FUEL_NF, () => nf(x.b, x.d));
        for (const t of [ea, ob]) if (t) varsOf(t, x.names, keep);
        // as the checker holds it (Mc.M.redex), then its normal form if that reads differently
        const sh = (t: LTerm | undefined, h0: HTerm, h: HTerm) => {
          const raw = clipTo(showCut(h0, x.d, x.names, file), 800);
          const n = clipTo(t && size(t, ERR_NODES + 1) <= ERR_NODES ? B.term_show(t, -1, x.names.slice(), file) : showCut(h, x.d, x.names, file), 800);
          return n === raw ? raw : raw + "\n                = " + n;
        };
        out.push("  " + (i + 1) + ". at " + at + "\n     expected : " + sh(ea, x.a0, x.a) + "\n     observed : " + sh(ob, x.b0, x.b));
      });
    }
    if (anns.length) out.push("Context (types as stated" + (full ? "" : "; a type over " + CTX_CHARS + " chars that names no variable of a difference is cut; --full-errors shows all") + "):");
    // consecutive binders of one type share a line (r4 .. r62 : U32)
    const rows: [string[], string][] = [];
    for (const [i, a] of anns) {
      const T = showCut(a.T, i, names.slice(0, i), file, full ? 20000 : 2000);
      const long = !full && T.length > CTX_CHARS && ![...keep].some((v) => v !== a.k && new RegExp("(^|[^\\w.])" + v.replace(/[.$]/g, "\\$&") + "($|[^\\w.])").test(T));
      const shown = long ? T.slice(0, 160) + " … [cut: " + T.length + " chars]" : clipTo(T, full ? 20000 : 4000);
      const last = rows[rows.length - 1];
      if (last && last[1] === shown && !full) last[0].push(a.k);
      else rows.push([[a.k], shown]);
    }
    const label = (ks: string[]) => (ks.length > 4 ? ks[0] + ", " + ks[1] + ", …, " + ks[ks.length - 1] + " (" + ks.length + ")" : ks.join(", "));
    const wid = Math.max(0, ...rows.map(([ks]) => Math.min(24, label(ks).length)));
    // shown: context lines printed by an earlier error of the same --check (printed once)
    let same = 0;
    for (const [ks, T] of rows) { const id = label(ks) + " : " + T; if (shown?.has(id)) same++; else { shown?.add(id); out.push("- " + label(ks).padEnd(wid) + " : " + T); } }
    if (same) out.push("- (and " + same + " entries as in an error above)");
    return out.join("\n") + errLocation(err) + (err.nte ? "\n" + err.nte : "");
  } catch (x: any) {
    return "Error: " + (typeof err.exp === "string" ? err.exp : "(gen2 could not print it: " + String(x?.message ?? x).slice(0, 100) + ")") + errLocation(err);
  } finally { fuel = old; }
};
// program stepping: a closed call (no variable: Sh.body, Wk.body(Sh.part)) in the goal's spine (depth
// 1-3, through equation sides) unfolded ONE step to its head constructor (Cr.Cir.Stmt.seq{a, b}),
// so that the statement lemmas (Ok.seq, X.set, X.if1, ..) match it; the goal converts to the result,
// which nf misses (it evaluates exec(1n+f, ..) far too deep). At most 8 unfoldings of <= 2000 nodes.
const hasVar = (t: LTerm): boolean => {
  switch (t.$) {
    case "Var": return true;
    case "App": return hasVar(t.f) || hasVar(t.x);
    case "Ctr": case "ADT": return t.x.some(hasVar);
    case "Eql": return hasVar(t.a) || hasVar(t.b) || hasVar(t.T);
    case "Lam": case "All": case "Let": case "Mat": case "Use": return true;
    default: return false;
  }
};
const unfoldProg = (t: LTerm, env: B.Env, d: number, depth: number, b: { n: number }): LTerm => {
  if (depth > 3 || b.n <= 0) return t;
  if (t.$ === "Eql") {
    const a = unfoldProg(t.a, env, d, depth, b), c = unfoldProg(t.b, env, d, depth, b);
    return a === t.a && c === t.b ? t : B.Eql(a, c, t.T);
  }
  if (t.$ !== "App" && t.$ !== "Ref") return t;
  const [h, args] = unapply(t);
  if (h.$ !== "Ref") return t;
  if (depth > 0 && !hasVar(t)) {
    const w = wnf(B.term_higher(t, env));
    if (w && w.$ === "Ctr") {
      const l = attempt(FUEL_NF, () => lower(w, d));
      if (l && size(l, 2001) <= 2000) { b.n--; return l; }
    }
    return t;
  }
  let ch = false;
  const na = args.map((a) => { const x = unfoldProg(a, env, d, depth + 1, b); if (x !== a) ch = true; return x; });
  return ch ? na.reduce((f: LTerm, x) => B.App(f, x), h) : t;
};
const stepped = (raw: LTerm, env: B.Env, d: number): LTerm | null => {
  const v = attempt(FUEL_NF * 4, () => unfoldProg(raw, env, d, 0, { n: 8 }));
  return v && v !== raw ? v : null;
};
// the targets that lemmas are matched against: the goal as stated, stepped, and its normal form (last)
const goalTargets = (g: Goal, raw: LTerm): LTerm[] => {
  const out = [raw];
  const v = stepped(raw, g.env, g.d);
  if (v && key(v) !== key(raw)) out.push(v);
  const n = attempt(FUEL_NF * 2, () => nf(g.ty, g.d));
  if (n && !out.some((x) => key(x) === key(n))) out.push(n);
  return out;
};

const headKey = (t: LTerm): string => {
  switch (t.$) {
    case "App": { const [h] = unapply(t); return h.$ === "Ref" ? "R:" + h.k : h.$ === "Var" && h.i >= META ? "*" : "V"; }
    case "Ref": return "R:" + t.k;
    case "Ctr": return "C:" + t.k;
    case "Lit": return t.k === "Nat" ? (t.v === 0 ? "C:Zero" : "C:Succ") : "C:" + t.k;
    case "Var": return t.i >= META ? "*" : "V";
    case "ADT": return "A:" + t.k;
    case "Eql": return "E|" + headKey(t.a);
    case "All": return "P";
    default: return t.$;
  }
};

// strict parameter of a def: the one its body matches first
const strictMemo = new Map<string, number | null>();
const strictOf = (k: string): number | null => {
  if (strictMemo.has(k)) return strictMemo.get(k)!;
  let r: number | null = null;
  const t0 = RAW[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let t: HTerm = t0.v, j = 0;
    for (; j <= t0.n; j++) {
      t = B.term_strip(t);
      if (t.$ === "Lam") { t = t.f(B.Var("_", 1e7 + j)); continue; }
      if ((t.$ === "Mat" || t.$ === "Efq") && j < t0.n) r = j;
      break;
    }
  }
  strictMemo.set(k, r);
  return r;
};
// the parameters that a def's case tree matches (at any depth)
const matchedMemo = new Map<string, Set<number>>();
const matchedOf = (k: string): Set<number> => {
  let r = matchedMemo.get(k);
  if (r) return r;
  r = new Set();
  const t0 = RAW[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let budget = 400;
    const walk = (t: HTerm, q: number[]) => {
      if (--budget < 0) return;
      t = B.term_strip(t);
      if (t.$ === "Lam") { walk(t.f(B.Var("_", 1e7)), q.slice(1)); return; }
      if (t.$ === "Mat") {
        const b = q[0];
        if (b !== undefined && b >= 0) r!.add(b);
        const ctr = RAW[t.k] === undefined ? (book.ctrs as any)[t.k] : null;
        const nf = ctr ? ctr.n : 0;
        walk(t.h, [...new Array(nf).fill(-1), ...q.slice(1)]);
        walk(t.m, q);
      }
    };
    walk(t0.v, Array.from({ length: t0.n }, (_, i) => i));
  }
  matchedMemo.set(k, r);
  return r;
};
// subterms that block evaluation: the strict argument of a stuck call, when a variable or a stuck call
const blockers = (t: LTerm, out: LTerm[]) => {
  switch (t.$) {
    case "App": {
      const [h, xs] = unapply(t);
      if (h.$ === "Ref") {
        const j = strictOf(h.k);
        const blk = (a: LTerm) => a.$ === "Var" || (a.$ === "App" && unapply(a)[0].$ === "Ref");
        if (j !== null && j < xs.length && blk(xs[j])) out.push(xs[j]);
        // the strict argument is a constructor (a nested match reads another one): the other matched ones
        else { const ms = matchedOf(h.k); xs.forEach((a, i) => { if (ms.has(i) && blk(a)) out.push(a); }); }
      }
      xs.forEach((x) => blockers(x, out));
      break;
    }
    case "Ctr": case "ADT": t.x.forEach((x) => blockers(x, out)); break;
    case "Eql": blockers(t.a, out); blockers(t.b, out); break;
  }
};

// ---- lemma index ----
type Lemma = { k: string; order: number; n: number };
const applyIndex = new Map<string, Lemma[]>();
const rwIndex = new Map<string, { L: Lemma; side: 0 | 1 }[]>();
const wild: Lemma[] = [];
const isProp = (h: HTerm, n = 0): boolean => {
  const w = wnf(h);
  if (!w) return true;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": {
      const t = RAW[w.k];
      if (t?.$ !== "ADT") return false;
      if (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)) return true;
      // a pair of facts (P2(A, B), D.HSK(..) = P2(RtsK(..), P2(..))) is a fact: one constructor whose
      // type arguments are all facts
      // (Sigma<&2, &2, A, _ => B>: quantities skipped, a lambda judged by its body)
      return t.c.length === 1 && w.x.length > 0 && n < 20 && w.x.every((a: HTerm) => {
        const wa = wnf(a);
        if (!wa || wa.$ === "Qua" || wa.$ === "Qnt") return true;
        return wa.$ === "Lam" ? isProp((wa.f as B.HBody)(B.Var("_", 1e7 + n)), n + 1) : isProp(wa, n + 1);
      });
    }
    case "Typ": case "Qnt": case "Qua": return false;
    case "All": return n < 20 ? isProp(w.B(B.Var("_", 1e7 + n)), n + 1) : true;
    case "Var": return false;
    case "Ref": return false;
    default: return true;
  }
};
// a parameter that a hypothesis or a proof must give: a fact, or a type that still names other
// parameters of the callee (D.HSK(?dk, .., ?ps), @st2 -> AlQ(..) -> Q(st2)), not a type or a kind
const isPrem = (A: HTerm, d: number): boolean => {
  if (isProp(A)) return true;
  if (attempt(FUEL_NF, () => hasMeta(lower(A, d))) !== true) return false;
  const w = wnf(A);
  return !!w && w.$ !== "Typ" && w.$ !== "Qnt" && w.$ !== "Qua";
};
// a predicate type: a function (any arity) whose result is a kind (State -> Type)
const isPredType = (A: HTerm, n = 0): boolean => {
  const w = wnf(A);
  if (!w) return null;
  if (w.$ === "Typ") return n > 0;
  return w.$ === "All" && n < 12 && isPredType(w.B(B.Var("_", 1e7 + n)), n + 1);
};
const openMeta = (T: HTerm, n: number, sol: (HTerm | null)[] = []): { doms: { q: B.Quant; k: string; A: HTerm }[]; concl: HTerm } | null => {
  let t = T;
  const doms: { q: B.Quant; k: string; A: HTerm }[] = [];
  for (let j = 0; j < n; j++) {
    let s = B.term_strip(t);
    if (s.$ !== "All") { const w = wnf(t); if (!w || w.$ !== "All") return null; s = w; }
    doms.push({ q: s.q, k: s.k, A: s.A });
    t = s.B(sol[j] ?? B.Var("?" + j, META + j));
  }
  return { doms, concl: t };
};
const preds = new Map<string, Lemma[]>();
let tIndex = 0;
// what one def gives the index, memoized by its TLD object: serve's reload keeps the imports' objects,
// so only the entry's defs are indexed again (the lookups of the ~5000 imported defs cost most of a reload)
type IdxOf = { keys: string[]; wild: boolean; rw: [string, 0 | 1][]; pred: string | null };
const idxMemo = new WeakMap<B.TLD, IdxOf>();
const indexOf = (t: B.TLD): IdxOf => {
  let r = idxMemo.get(t);
  if (r) return r;
  r = { keys: [], wild: false, rw: [], pred: null };
  idxMemo.set(t, r);
  if (t.$ !== "Def" || t.x > 0) return r;
  if (!(t.v === null && t.b !== true) && !t.i) {
    const o = attempt(20000, () => openMeta(t.T, t.n));
    const c = o && attempt(20000, () => lower(o.concl, 0));
    if (o && c) {
      const hk = headKey(c);
      if (hk === "*") r.wild = t.n <= 4;
      else if (hk !== "V" && hk !== "Typ") {
        r.keys.push(hk);
        // also by the head of the conclusion's normal form (Le(a, b) is T(..) once unfolded)
        if (t.n > 0) {
          const cn = attempt(20000, () => nf(o.concl, 0));
          const nk = cn ? headKey(cn) : "*";
          if (nk !== hk && nk !== "*" && nk !== "V" && nk !== "E|*" && nk !== "E|V") r.keys.push(nk);
        }
        if (c.$ === "Eql") {
          for (const side of [0, 1] as const) {
            const sk = headKey(side === 0 ? c.a : c.b);
            if (sk.startsWith("R:") || (t.n === 0 && (sk.startsWith("C:") || sk.startsWith("A:")))) r.rw.push([sk, side]);
          }
          // also by the head of each side in normal form (a rewrite matches that form too)
          const cn = t.n > 0 ? attempt(20000, () => nf(o.concl, 0)) : null;
          if (cn && cn.$ === "Eql") for (const side of [0, 1] as const) {
            const sk = headKey(side === 0 ? cn.a : cn.b);
            if (sk.startsWith("R:") && !r.rw.some(([k2, s2]) => k2 === sk && s2 === side)) r.rw.push([sk, side]);
          }
        }
      }
    }
  }
  // a predicate on one datatype (P: T -> Type), to discriminate two constructors (`%e : P(_); Unit{}`)
  if (t.v !== null && t.n === 1) {
    const s0 = B.term_strip(t.T);
    if (s0.$ === "All") {
      const w = attempt(20000, () => wnf(s0.B(B.Var("_", 0))));
      if (w && w.$ === "Typ") r.pred = attempt(20000, () => key(lower(s0.A, 0))) ?? null;
    }
  }
  return r;
};
const buildIndex = () => {
  const tIndex0 = performance.now();
  applyIndex.clear(); rwIndex.clear(); wild.length = 0; preds.clear();
  const add = <V>(m: Map<string, V[]>, k: string, v: V) => { let a = m.get(k); if (!a) m.set(k, a = []); a.push(v); };
  for (const k of Object.keys(RAW)) {
    const t = RAW[k];
    if (!t || t.$ !== "Def" || isOpen(k)) continue;
    const r = indexOf(t);
    const L: Lemma = { k, order: ORDER.get(k) ?? -1, n: t.n };
    if (r.wild) wild.push(L);
    for (const hk of r.keys) add(applyIndex, hk, L);
    for (const [sk, side] of r.rw) add(rwIndex, sk, { L, side });
    if (r.pred !== null) add(preds, r.pred, { k, order: L.order, n: 1 });
  }
  for (const v of preds.values()) v.sort((a, b) => b.order - a.order);
  for (const v of applyIndex.values()) v.sort((a, b) => b.order - a.order);
  for (const v of rwIndex.values()) v.sort((a, b) => b.L.order - a.L.order);
  wild.sort((a, b) => b.order - a.order);
  tIndex = performance.now() - tIndex0;
};
buildIndex();
if (STREAM) console.error("[gen2] indexed book in " + Math.round(tIndex) + " ms");

// ---- proofs ----
type Pf =
  | { t: "tm"; s: string }
  | { t: "rw"; e: string; P: string; k: Pf }
  | { t: "mt"; x: string; arms: { pat: string; k: Pf }[] }
  | { t: "hole"; g: Goal }
  | { t: "app"; s: string; subs: Pf[] }; // a call whose open premises are subs (marked HOLE in s)
const HOLE = "\u0000";
const inline = (p: Pf): string => {
  switch (p.t) {
    case "tm": return p.s;
    case "app": { let i = 0; return p.s.replace(/\u0000/g, () => inline(p.subs[i++])); }
    case "rw": return "(%" + p.e + " : " + p.P + "; " + inline(p.k) + ")";
    case "hole": return "?TODO";
    case "mt": throw new Error("a match cannot be inlined");
  }
};
const flat = (p: Pf): string => (p.t === "rw" ? "%" + p.e + " : " + p.P + "; " + flat(p.k) : inline(p));
const render = (p: Pf, ind: string, out: string[]) => {
  switch (p.t) {
    case "tm": out.push(ind + p.s); break;
    case "app": out.push(ind + inline(p)); break;
    case "hole": out.push(ind + "?TODO"); break;
    case "rw": out.push(ind + "%" + p.e + " :"); out.push(ind + "  " + p.P); render(p.k, ind, out); break;
    case "mt":
      out.push(ind + "match " + p.x + ":");
      for (const a of p.arms) { out.push(ind + "  case " + a.pat + ":"); render(a.k, ind + "    ", out); }
      break;
  }
};
const holesOf = (p: Pf, out: Goal[] = []): Goal[] => {
  if (p.t === "hole") out.push(p.g);
  else if (p.t === "rw") holesOf(p.k, out);
  else if (p.t === "mt") p.arms.forEach((a) => holesOf(a.k, out));
  else if (p.t === "app") p.subs.forEach((a) => holesOf(a, out));
  return out;
};

// ---- goals ----
type Goal = {
  ctx: B.Ctx; d: number; ty: HTerm; lhs: B.LHS; qt: B.Quant; env: B.Env;
  names: string[]; ckey: string;
  pend: number; pnames: string[]; pmany: boolean[];
  split: boolean; path: string; lvl: number;
  hc: Map<number, LTerm[]>;
  weak?: boolean; // a skeleton hole equal to its goal but in one argument (a monotonicity step)
};
// what a goal gives the leaf tactics whatever its budget (iterative deepening asks again): per job, by goal key
type GoalInfo = { targets?: LTerm[]; hyp?: Callee[]; lem?: Callee[] };
type Job = { k: string; def: B.Def; order: number; file: B.File; short: string; tags: Map<string, number>; memo: Map<string, { pf: Pf | null; depth: number; rw: number }>; smemo: Map<string, Res>; gi: Map<string, GoalInfo>; closed: number; ih: boolean };
let job: Job;
// serve only: caches that live across asks (LRU). proofCache: a closed leaf goal (by goal key) -> its
// proof, reused only after the proof checks again at the new goal and names only defs that the new job
// may use (see reuseOk). answers: what an ask printed for a def, by the def, the options and the entry
// file's text up to the end of that def; a proven answer is checked again before it is reused.
const SERVE = MODE === "serve";
const proofCache = new Map<string, Pf>();
const lruGet = <V>(m: Map<string, V>, k: string): V | undefined => { const v = m.get(k); if (v !== undefined) { m.delete(k); m.set(k, v); } return v; };
const lruSet = <V>(m: Map<string, V>, k: string, v: V, cap: number) => { m.delete(k); m.set(k, v); if (m.size > cap) m.delete(m.keys().next().value!); };
type Res = { pf: Pf; holes: number; closed: number };
const tag = (t: string) => job.tags.set(t, (job.tags.get(t) ?? 0) + 1);
const tm = (s: string): Pf => ({ t: "tm", s });

// bend2 prints a call of a zero-parameter def (def Bytes() -> Data) as its bare name, which reads back
// as the def itself, not its value: add the "()" back, for the defs of the book that take none
const zeroArity = new Map<any, RegExp | null>();
const zeroFix = (s: string, file: any): string => {
  let re = zeroArity.get(file);
  if (re === undefined) {
    const names = Object.keys(RAW).filter((k) => { const d: any = RAW[k]; return d && d.$ === "Def" && d.n === 0 && d.v; })
      .map((k) => B.name_show(file, k)).filter((n) => /^[A-Za-z_][\w.]*$/.test(n));
    re = names.length ? new RegExp("(?<![\w.])(" + names.sort((a, b) => b.length - a.length).map((n) => n.replace(/\./g, "\.")).join("|") + ")(?![\w.(])", "g") : null;
    zeroArity.set(file, re);
  }
  return re ? s.replace(re, "$1()") : s;
};
const show = (t: LTerm, names: string[]): string => zeroFix(B.term_show(t, -1, names.slice(), job.file), job.file);
const ann = (g: Goal, i: number) => B.pmap_get(g.ctx, i);
const goalKey = (g: Goal) => g.ckey + "|-" + g.qt.$[0] + key(lower(g.ty, g.d));

const parseLow = (text: string, g: Goal): LTerm => {
  const p: B.Parse = { book, dir: "", str: text, pos: 0, stk: g.names.map((k, i) => [k, i] as [string, number]), frs: g.d, ns: job.file.ns, al: job.file.al };
  const hols = book.hols;
  const lt = B.parse_block(p);
  book.hols = hols;
  B.parse_skip(p);
  if (p.pos < text.length) B.parse_fail(p, "the end of the fragment");
  return lt;
};
const parseFrag = (text: string, g: Goal): HTerm => B.term_higher(parseLow(text, g), g.env);
// a cached proof may name only what this job's own search may name: defs before the target that are
// not open, and the target itself only as the induction hypothesis (below a split)
// (a span's file is the parser state, which holds the whole book: skip spans)
const refsOf = (t: any, out: Set<string>) => {
  if (t.$ === "Ref") out.add(t.k);
  for (const k in t) if (k !== "s" && t[k] && typeof t[k] === "object") refsOf(t[k], out);
};
const reuseOk = (g: Goal, text: string): boolean => {
  const rs = new Set<string>();
  if (!attempt(FUEL_NF, () => { refsOf(parseLow(text, g), rs); return true; })) return false;
  for (const r of rs) {
    if (r === job.k) { if (job.ih && g.split) continue; return false; }
    const t = RAW[r];
    if (!t) return false;
    if (t.$ === "Def" && ((ORDER.get(r) ?? Infinity) >= job.order || isOpen(r))) return false;
  }
  return true;
};
// does text check at g (bend2's term_check, plus the linearity of g's live binders)?
const tryText = (g: Goal, text: string): boolean =>
  attempt(FUEL_CHECK, () => {
    const c = B.term_check(book, g.lhs, parseFrag(text, g), g.qt, g.ty, g.ctx, g.d);
    if (g.qt.$ !== "None") {
      for (const [i, a] of B.pmap_to_array(g.ctx)) if (a.q.$ === "Lone" && B.pmap_get(c.us, i)?.$ === "Many") throw LIN;
    }
    return true;
  }) === true;

const intro = (g: Goal, name: string, many: boolean): Goal | null => {
  let t: HTerm | undefined = B.term_strip(g.ty);
  if (t.$ !== "All") t = wnf(g.ty);
  if (!t || t.$ !== "All") return null;
  const x: HTerm = B.Var(name, g.d);
  const lhs = g.lhs.n > 0 ? { ...g.lhs, t: B.term_apply(g.lhs.t, x), n: g.lhs.n - 1 } : g.lhs;
  let q = t.q;
  if (many && q.$ === "Lone") q = B.Many();
  const A = t.A;
  const Ak = attempt(FUEL_NF, () => key(lower(A, g.d))) ?? "?";
  return {
    ...g, ctx: B.ctx_bind(g.ctx, g.d, q, name, A), d: g.d + 1, ty: t.B(x), lhs, env: B.list_set(g.env, g.d, x),
    names: [...g.names, name], ckey: g.ckey + "|" + q.$[0] + name + ":" + Ak,
    pend: Math.max(0, g.pend - 1), pnames: g.pnames.slice(1), pmany: g.pmany.slice(1), hc: new Map(),
  };
};
const introAll = (g: Goal): Goal | null => {
  let c: Goal | null = g;
  while (c && c.pend > 0) c = intro(c, c.pnames[0], c.pmany[0]);
  return c;
};

const reserved = (nm: string) => {
  const q = job.file.ns === "" ? nm : job.file.ns + ":" + nm;
  return q in RAW || nm in RAW || nm === "_" || /^(def|type|law|match|case|do|return|for|exs|where|is|import|Type|Data|Kind|Quant)$/.test(nm);
};
const fresh = (base: string, used: Set<string>): string => {
  const b = base.replace(/[^A-Za-z0-9_]/g, "") || "x";
  for (let i = 0; ; i++) {
    const nm = i === 0 ? b : b + String(i);
    if (!used.has(nm) && !reserved(nm)) { used.add(nm); return nm; }
  }
};

// hypothesis types (raw and normal form), cached per goal context
const hypTargets = (g: Goal, i: number): LTerm[] => {
  let r = g.hc.get(i);
  if (!r) {
    const a = ann(g, i)!;
    const raw = lower(a.T, g.d);
    const n = attempt(FUEL_NF * 2, () => nf(a.T, g.d));
    r = n && key(n) !== key(raw) ? [raw, n] : [raw];
    g.hc.set(i, r);
  }
  return r;
};
const usable = (g: Goal, i: number, qt: B.Quant) => {
  const a = ann(g, i);
  return !!a && g.names[i] !== "_" && (qt.$ === "None" || a.q.$ !== "None");
};

// ---- leaf tactics ----
type Callee = { text: string; T: HTerm; n: number; kind: string };

// apply a callee whose conclusion matches one of targets; premises proven at depth - 1
type Applied = { args: string[]; doms: any[]; sol: (LTerm | null)[]; holes?: Goal[] };
const applyCallee = (g: Goal, c: Callee, targets: LTerm[], depth: number, rw: number, path: Set<string>, concl: ((o: LTerm) => LTerm | null) | null, accept: (a: Applied) => boolean, cnt?: { n: number; probe?: boolean; spec?: number }, holesOk = false): Applied | null => {
  const toH = (s: (LTerm | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
  const o = openMeta(c.T, c.n);
  if (!o) return null;
  const pc0 = attempt(FUEL_NF, () => lower(o.concl, g.d));
  if (!pc0) return null;
  const pc = concl ? concl(pc0) : pc0;
  if (!pc) return null;
  // the distinct solutions of the conclusion against the goal: raw pattern against each target, then
  // the normal form of the conclusion (metavariables stay stuck) against the normal form of the goal
  const sols: (LTerm | null)[][] = [];
  const seen = new Set<string>();
  const push = (p: LTerm, t: LTerm) => {
    const s2: (LTerm | null)[] = new Array(c.n).fill(null);
    if (!match(p, t, s2, g.d)) return;
    const k = s2.map((x) => (x ? key(x) : "_")).join(";");
    if (!seen.has(k)) { seen.add(k); sols.push(s2); }
  };
  for (const t of targets) push(pc, t);
  if (!concl && targets.length > 0) {
    const pn = nfPattern(c, o.concl, g.d);
    if (pn && key(pn) !== key(pc)) push(pn, targets[targets.length - 1]);
  } else if (concl && targets.length > 0 && sols.length === 0) {
    // a rewrite: the side of the conclusion in normal form too (Brk.char(Brk.of(c)) is Brk.char(Bool.pick(..))
    // in a goal's normal form), when the raw side matched nothing
    const pn = nfPattern(c, o.concl, g.d);
    const ps = pn ? concl(pn) : null;
    if (ps && key(ps) !== key(pc)) for (const t of targets) push(ps, t);
  }
  if (cnt && cnt.probe) { cnt.spec = sols.length ? specOf(pc) : -1; return null; }
  for (const s0 of sols) {
    if (cnt) cnt.n++;
    const r = complete(g, c, s0, toH, depth, rw, path, holesOk, concl !== null);
    if (r && accept(r)) return r;
  }
  return null;
};
// specificity of a pattern: its nodes that are not metavariables
const specOf = (t: LTerm): number => size(t) - metas(t);
const metas = (t: LTerm): number => {
  switch (t.$) {
    case "Var": return t.i >= META ? 1 : 0;
    case "App": return metas(t.f) + metas(t.x);
    case "Ctr": case "ADT": return t.x.reduce((a, x) => a + metas(x), 0);
    case "Eql": return metas(t.a) + metas(t.b);
    default: return 0;
  }
};
const complete = (g: Goal, c: Callee, s0: (LTerm | null)[], toH: (s: (LTerm | null)[]) => (HTerm | null)[], depth: number, rw: number, path: Set<string>, holesOk = false, refl = false): Applied | null => {
  let sol = s0.slice();
  let o2 = openMeta(c.T, c.n, toH(sol));
  if (!o2) return null;
  const prem: boolean[] = o2.doms.map((dm, j) => !sol[j] && isPrem(dm.A, g.d));
  const viaHyp: (string | null)[] = new Array(c.n).fill(null);
  // parameters not fixed by the conclusion: from premises that match hypotheses (raw, then normal forms)
  for (let iter = 0; iter < 3 && sol.some((s, j) => !s && !prem[j]); iter++) {
    let progress = false;
    for (let j = 0; j < c.n; j++) {
      if (!prem[j] || viaHyp[j]) continue;
      const Araw = attempt(FUEL_NF, () => lower(o2!.doms[j].A, g.d));
      if (!Araw || !hasMeta(Araw)) continue;
      const An = attempt(FUEL_NF, () => nf(o2!.doms[j].A, g.d));
      const pats = An && key(An) !== key(Araw) ? [Araw, An] : [Araw];
      const qt = B.quant_dem(o2.doms[j].q, g.qt);
      for (let i = g.d - 1; i >= 0 && !viaHyp[j]; i--) {
        if (!usable(g, i, qt)) continue;
        const hts = hypTargets(g, i);
        for (let pi = 0; pi < pats.length && !viaHyp[j]; pi++) {
          const ht = pi === 0 ? hts : [hts[hts.length - 1]];
          for (const t of ht) {
            const s2 = sol.slice();
            if (match(pats[pi], t, s2, g.d)) { sol = s2; viaHyp[j] = g.names[i]; progress = true; break; }
          }
        }
      }
    }
    if (!progress) break;
    o2 = openMeta(c.T, c.n, toH(sol));
    if (!o2) return null;
  }
  // (rewrites only) still open: a premise {a == x} or {x == a} whose x is an open parameter fixes x := a (the premise
  // then holds by {==}: L.len(t, p, v, List.length(t), {==}))
  if (refl && sol.some((s, j) => !s && !prem[j])) {
    for (let j = 0; j < c.n; j++) {
      if (!prem[j] || viaHyp[j]) continue;
      const A = attempt(FUEL_NF, () => lower(o2!.doms[j].A, g.d));
      if (!A || A.$ !== "Eql") continue;
      const isOpen = (t: LTerm) => t.$ === "Var" && t.i >= META && !sol[t.i - META] && !prem[t.i - META];
      const [x, a] = isOpen(A.b) && !hasMeta(A.a) ? [A.b, A.a] : isOpen(A.a) && !hasMeta(A.b) ? [A.a, A.b] : [null, null];
      if (!x || !a || !closedBelow(a, g.d)) continue;
      sol[(x as any).i - META] = a;
      const o3 = openMeta(c.T, c.n, toH(sol));
      if (!o3) return null;
      o2 = o3;
    }
  }
  if (sol.some((s, j) => !s && !prem[j])) {
    // still open: unify a premise with an indexed lemma's conclusion (le_trans's middle term from
    // the lemma that proves its first premise); at most 3 alternatives, each one completed
    // only at the top of a leaf (premise level 0) with depth for the premises: it is costly
    // a skeleton (holesOk: bestStep) leaves such a parameter as a hole for the agent (K.Ok.seq's
    // intermediate predicate: the invariant after the first statement is the agent's choice)
    // only a predicate may stay open: a number (a budget, K.Ok.wk's) is a guess, not a choice
    const predOnly = () => o2!.doms.every((dm, j) => sol[j] || prem[j] || isPredType(dm.A));
    if (depth < 2 || g.lvl > 0) return holesOk && predOnly() ? finish(g, c, sol, viaHyp, o2, depth, rw, path, holesOk) : null;
    for (const alt of forwardBinds(g, c, sol, prem, viaHyp, o2).slice(0, 2)) {
      const s2 = sol.slice();
      for (const [j, t] of alt) s2[j] = t;
      if (s2.some((x, j) => !x && !prem[j])) continue;
      const o3 = openMeta(c.T, c.n, toH(s2));
      if (!o3) continue;
      const r = finish(g, c, s2, viaHyp, o3, depth, rw, path, holesOk);
      if (r) { tag("forward"); return r; }
    }
    return holesOk && predOnly() ? finish(g, c, sol, viaHyp, o2, depth, rw, path, holesOk) : null;
  }
  return finish(g, c, sol, viaHyp, o2, depth, rw, path, holesOk);
};
const finish = (g: Goal, c: Callee, sol: (LTerm | null)[], viaHyp: (string | null)[], o2: { doms: { q: B.Quant; k: string; A: HTerm }[] }, depth: number, rw: number, path: Set<string>, holesOk: boolean): Applied | null => {
  const args: string[] = [];
  const holes: Goal[] = [];
  for (let j = 0; j < c.n; j++) {
    if (sol[j]) { args.push(show(sol[j]!, g.names)); continue; }
    if (viaHyp[j]) { args.push(viaHyp[j]!); continue; }
    const sg: Goal = { ...g, ty: o2.doms[j].A, qt: B.quant_dem(o2.doms[j].q, g.qt), lvl: g.lvl + 1, path: g.path + "#" + c.text + "." + j };
    const pf = leaf(sg, Math.max(0, depth - 1), rw, path);
    if (!pf && !holesOk) return null;
    if (!pf) { holes.push(sg); args.push(HOLE); continue; }
    args.push(inline(pf));
  }
  return { args, doms: o2.doms, sol, holes };
};
// two-sided first-order unification; metavariables >= META on both sides (the callee's below META2)
const META2 = 2 * META;
const shiftMetas = (t: LTerm): LTerm => {
  switch (t.$) {
    case "Var": return t.i >= META ? B.Var(t.k, t.i + META) : t;
    case "App": return B.App(shiftMetas(t.f), shiftMetas(t.x));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map(shiftMetas));
    case "Eql": return B.Eql(shiftMetas(t.a), shiftMetas(t.b), shiftMetas(t.T));
    case "ADT": return B.ADT(t.k, t.x.map(shiftMetas), undefined, t.r);
    default: return t;
  }
};
const deref = (t: LTerm, s: Map<number, LTerm>): LTerm => { while (t.$ === "Var" && t.i >= META && s.has(t.i)) t = s.get(t.i)!; return t; };
const resolve = (t: LTerm, s: Map<number, LTerm>, n = 0): LTerm => {
  t = deref(t, s);
  if (n > 200) return t;
  switch (t.$) {
    case "App": return B.App(resolve(t.f, s, n + 1), resolve(t.x, s, n + 1));
    case "Ctr": return B.Ctr<[LTerm]>(t.k, t.x.map((x) => resolve(x, s, n + 1)));
    case "Eql": return B.Eql(resolve(t.a, s, n + 1), resolve(t.b, s, n + 1), resolve(t.T, s, n + 1));
    case "ADT": return B.ADT(t.k, t.x.map((x) => resolve(x, s, n + 1)), undefined, t.r);
    default: return t;
  }
};
const occurs = (i: number, t: LTerm, s: Map<number, LTerm>): boolean => {
  t = deref(t, s);
  switch (t.$) {
    case "Var": return t.i === i;
    case "App": return occurs(i, t.f, s) || occurs(i, t.x, s);
    case "Ctr": case "ADT": return t.x.some((x) => occurs(i, x, s));
    case "Eql": return occurs(i, t.a, s) || occurs(i, t.b, s);
    default: return false;
  }
};
const unify = (a: LTerm, b: LTerm, s: Map<number, LTerm>, d: number): boolean => {
  a = deref(a, s); b = deref(b, s);
  if (a.$ === "Var" && b.$ === "Var" && a.i === b.i) return true;
  if (a.$ === "Var" && a.i >= META) { if (occurs(a.i, b, s)) return false; s.set(a.i, b); return true; }
  if (b.$ === "Var" && b.i >= META) { if (occurs(b.i, a, s)) return false; s.set(b.i, a); return true; }
  if (a.$ === "Lit" && b.$ === "Ctr") { const x = litStep(a); return !!x && unify(x, b, s, d); }
  if (b.$ === "Lit" && a.$ === "Ctr") { const x = litStep(b); return !!x && unify(a, x, s, d); }
  switch (a.$) {
    case "Var": return false;
    case "Ref": return b.$ === "Ref" && a.k === b.k;
    case "App": return b.$ === "App" && unify(a.f, b.f, s, d) && unify(a.x, b.x, s, d);
    case "Ctr": return b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length && a.x.every((x, i) => unify(x, (b as any).x[i], s, d));
    case "Lit": return b.$ === "Lit" && a.k === b.k && a.v === b.v;
    case "Eql": return b.$ === "Eql" && unify(a.a, b.a, s, d) && unify(a.b, b.b, s, d) && (unify(a.T, b.T, s, d) || true);
    case "ADT": return b.$ === "ADT" && a.k === b.k && a.x.length === b.x.length && a.x.every((x, i) => unify(x, (b as any).x[i], s, d));
    default: return key(a) === key(b);
  }
};
// bindings of the callee's open parameters that make one of its premises an instance of an indexed
// lemma's conclusion (ground values only)
const forwardBinds = (g: Goal, c: Callee, sol: (LTerm | null)[], prem: boolean[], viaHyp: (string | null)[], o2: { doms: { A: HTerm }[] }): [number, LTerm][][] => {
  const out: [number, LTerm][][] = [];
  const seen = new Set<string>();
  for (let j = 0; j < c.n && out.length < 3; j++) {
    if (!prem[j] || viaHyp[j]) continue;
    const A = attempt(FUEL_NF, () => lower(o2.doms[j].A, g.d));
    if (!A || !hasMeta(A)) continue;
    const open: number[] = [];
    for (let m = 0; m < c.n; m++) if (!sol[m] && !prem[m]) open.push(META + m);
    let looked = 0;
    for (const L of applyIndex.get(headKey(A)) ?? []) {
      if (out.length >= 3 || looked++ > 64) break;
      if (L.order >= job.order || L.k === job.k || L.k === shortKey(c)) continue;
      const o = attempt(FUEL_NF, () => openMeta((RAW[L.k] as B.Def).T, L.n));
      if (!o) continue;
      const P = attempt(FUEL_NF, () => shiftMetas(lower(o.concl, g.d)));
      if (!P) continue;
      const sb = new Map<number, LTerm>();
      if (!unify(P, A, sb, g.d)) continue;
      const alt: [number, LTerm][] = [];
      let ok = true;
      for (const m of open) {
        if (!sb.has(m)) continue;
        const v = resolve(B.Var("?", m), sb);
        if (hasMeta(v) || !closedBelow(v, g.d)) { ok = false; break; }
        alt.push([m - META, v]);
      }
      if (!ok || alt.length === 0) continue;
      const k = alt.map(([m, v]) => m + "=" + key(v)).join(";");
      if (seen.has(k)) continue;
      seen.add(k);
      out.push(alt);
    }
  }
  return out;
};
const shortKey = (c: Callee) => c.text;
const nfPat = new WeakMap<object, Map<number, LTerm | null>>();
const nfPattern = (c: Callee, concl: HTerm, d: number): LTerm | null => {
  let m = nfPat.get(c.T);
  if (!m) { m = new Map(); nfPat.set(c.T, m); }
  if (!m.has(d)) m.set(d, attempt(FUEL_NF, () => nf(concl, d)) ?? null);
  return m.get(d)!;
};
const callText = (c: Callee, args: string[]) => c.text + "(" + args.join(", ") + ")";

const lemmaCands = (g: Goal, targets: LTerm[]): Callee[] => {
  const seen = new Set<string>();
  const out: Callee[] = [];
  for (const t of targets) {
    const ks = t.$ === "Eql" ? [headKey(t), "E|*"] : [headKey(t)];
    for (const hk of ks) {
      for (const L of applyIndex.get(hk) ?? []) {
        if (L.order >= job.order || L.k === job.k || seen.has(L.k)) continue;
        seen.add(L.k);
        out.push({ text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" });
      }
    }
  }
  return out;
};
// hypotheses that are functions (through aliases): callees
const hypCallees = (g: Goal): Callee[] => {
  const out: Callee[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const a = ann(g, i)!;
    let t: HTerm = B.term_strip(a.T), k = 0;
    if (t.$ !== "All") t = wnf(a.T) ?? t;
    while (t.$ === "All" && k < 12) { const b: HTerm = t.B(B.Var("_", 1e7 + k)); t = B.term_strip(b); if (t.$ !== "All") t = wnf(b) ?? t; k++; }
    if (k > 0) out.push({ text: g.names[i], T: a.T, n: k, kind: "hyp" });
  }
  return out;
};
const ihCallee = (): Callee => ({ text: job.short, T: job.def.T, n: job.def.n, kind: "ih" });

const contradictory = (g: Goal): number[] => {
  const out: number[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, B.Lone())) continue;
    const ts = hypTargets(g, i);
    const n = ts[ts.length - 1];
    if (n.$ === "Eql") {
      const ha = headKey(n.a), hb = headKey(n.b);
      if (ha.startsWith("C:") && hb.startsWith("C:") && (ha !== hb || (n.a.$ === "Lit" && n.b.$ === "Lit" && n.a.v !== n.b.v))) out.push(i);
    }
  }
  return out;
};

const leaf = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  if (performance.now() > deadline) throw TIMEOUT;
  const gk = attempt(FUEL_NF, () => goalKey(g));
  if (gk === undefined) return null;
  if (path.has(gk)) return null;
  const ok = job.memo.get(gk);
  if (ok?.pf) return ok.pf;
  // a failure is memoized with its budget (depth, rewrites) and its candidate cap (level)
  const fk = gk + "#" + Math.min(g.lvl, CAPS.length - 1);
  const m = job.memo.get(fk);
  if (m && m.depth >= depth && m.rw >= rw) return null;
  if (SERVE) {
    const c = lruGet(proofCache, gk);
    if (c) {
      const s = flat(c);
      if (reuseOk(g, s) && tryText(g, s)) { tag("cache"); job.memo.set(gk, { pf: c, depth, rw }); return c; }
    }
  }
  const p2 = new Set(path);
  p2.add(gk);
  const r = leafGo(g, depth, rw, p2, gk);
  if (r && SERVE) lruSet(proofCache, gk, r, 50000);
  // progress: a goal of the original level closed (a premise or a rewrite side goal closing is not)
  // progress: a goal of the original level closed, or a premise closed by a lemma or a rewrite (not by a
  // closer: those keep coming in a search that goes nowhere, exec.alloc)
  if (r) { job.memo.set(gk, { pf: r, depth, rw }); if (g.lvl === 0 || r.t !== "tm") lastWin = performance.now(); }
  else job.memo.set(fk, { pf: null, depth: Math.max(depth, m?.depth ?? 0), rw: Math.max(rw, m?.rw ?? 0) });
  return r;
};

const leafGo = (g: Goal, depth: number, rw: number, path: Set<string>, gk: string): Pf | null => {
  const w = wnf(g.ty);
  if (!w) return null;
  // 1. closers
  if (w.$ === "Eql" && tryText(g, "{==}")) { tag("rfl"); return tm("{==}"); }
  if (w.$ === "ADT") {
    const t = RAW[w.k];
    if (t?.$ === "ADT" && t.c.length === 1 && t.c[0].n === 0) {
      const s = B.name_show(job.file, t.c[0].k) + "{}";
      if (tryText(g, s)) { tag("unit"); return tm(s); }
    }
  }
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const a = ann(g, i)!;
    if (attempt(FUEL_CHECK, () => B.term_compare("LE", book, a.T, g.ty, g.d)) && tryText(g, g.names[i])) { tag("hyp"); return tm(g.names[i]); }
  }
  if (g.path === "" && g.d === job.def.n) {
    for (const imp of autoImports) {
      if (!imp.proofs.has(job.short)) continue;
      if (isOpen(imp.ns + ":" + job.short + ".proof")) continue;
      const call = imp.alias + "." + job.short + ".proof(" + g.names.join(", ") + ")";
      if (tryText(g, call)) { tag("reuse"); return tm(call); }
    }
  }
  // 2. intro
  if (w.$ === "All") {
    const used = new Set(g.names);
    const x = fresh(w.k === "_" || w.k === "" ? "x" : w.k, used);
    const b = intro({ ...g, ty: w, pend: 1, pnames: [x], pmany: [false] }, x, false);
    if (!b) return null;
    const r = leaf(b, depth, rw, path);
    if (!r) return null;
    const s = x + " => " + inline(r);
    if (tryText(g, s)) { tag("intro"); return tm(s); }
    return null;
  }
  // 3. absurd
  const raw = lower(g.ty, g.d);
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const ts = hypTargets(g, i);
    const n = ts[ts.length - 1];
    if (n.$ === "ADT") {
      const t = RAW[n.k];
      if (t?.$ === "ADT" && t.c.length === 0) {
        const s = "Empty.absurd(" + show(raw, g.names) + ", " + g.names[i] + ")";
        if (tryText(g, s)) { tag("absurd"); return tm(s); }
      }
    }
  }
  const contra = contradictory(g);
  if (contra.length > 0 && w.$ === "ADT" && (RAW[w.k] as any)?.c?.length === 0) {
    for (const i of contra) {
      const ts = hypTargets(g, i);
      const E = ts[ts.length - 1] as Extract<LTerm, { $: "Eql" }>;
      const Tk = key(E.T);
      for (const L of (preds.get(Tk) ?? []).slice(0, MAX_CANDS)) {
        if (L.order >= job.order) continue;
        const P = B.name_show(job.file, L.k);
        for (const sym of [false, true]) {
          const [x, y] = sym ? [E.b, E.a] : [E.a, E.b];
          const e = sym ? "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + g.names[i] + ")" : g.names[i];
          const sub: Goal = { ...g, ty: B.App(B.Ref(L.k), B.term_higher(x, g.env)) };
          if (!tryText(g, "%" + e + " : " + P + "(_); ?TODO")) continue;
          const r = leaf(sub, 0, 0, path);
          if (r) { const pf: Pf = { t: "rw", e, P: P + "(_)", k: r }; if (tryText(g, flat(pf))) { tag("discriminate"); return pf; } }
          void y;
        }
      }
    }
  }
  if (contra.length > 0 && depth > 0) {
    for (const L of wild) {
      if (L.order >= job.order || L.k === job.k) continue;
      const c: Callee = { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" };
      const a = applyCallee(g, c, [raw], 1, 0, path, null, (a) => tryText(g, callText(c, a.args)));
      if (a) { tag("exfalso"); return tm(callText(c, a.args)); }
    }
  }
  if (IND) { const r = Ind.indLeaf(indApi(), g); if (r) { tag("ind"); return tm(r); } }
  if (depth === 0 && rw === 0) return null;
  let gi = job.gi.get(gk);
  if (!gi) { gi = {}; job.gi.set(gk, gi); }
  const targets = (gi.targets ??= goalTargets(g, raw));
  // 4. apply
  if (depth > 0) {
    const callees: Callee[] = [...(gi.hyp ??= hypCallees(g))];
    if (job.ih && g.split) callees.push(ihCallee());
    // lemmas: those whose conclusion matches, most specific first (a general lemma such as
    // weaken: Le(a, b) from Le(1+a, b) matches every goal of its head, and is tried last); the probe
    // stops before the premises, so the order depends on the goal only
    callees.push(...(gi.lem ??= lemmaCands(g, targets)
      .map((c) => { const pr = { n: 0, probe: true, spec: -1 }; applyCallee(g, c, targets, depth, rw, path, null, () => false, pr); return { c, spec: pr.spec! }; })
      .filter((x) => x.spec >= 0).sort((a, b) => b.spec - a.spec).map((x) => x.c)));
    const cap = CAPS[Math.min(g.lvl, CAPS.length - 1)];
    const tries = { n: 0 };
    for (const c of callees) {
      if (performance.now() > deadline) throw TIMEOUT;
      if (tries.n >= cap) break;
      const a = applyCallee(g, c, targets, depth, rw, path, null, (a) => tryText(g, callText(c, a.args)), tries);
      if (a) { tag("apply:" + c.kind); return tm(callText(c, a.args)); }
    }
  }
  // 5. rewrite
  if (rw > 0) {
    const r = rewrite(g, depth, rw, path);
    if (r) return r;
  }
  return null;
};

type RwCand = { base: LTerm; from: LTerm; to: LTerm; e: string; kind: string; score: number };
const rewrite = (g: Goal, depth: number, rw: number, path: Set<string>): Pf | null => {
  const N0 = attempt(FUEL_NF * 2, () => nf(g.ty, g.d + 1));
  const R = attempt(FUEL_NF, () => lower(g.ty, g.d + 1));
  const bases: LTerm[] = [];
  if (N0 && size(N0, 600) <= 600) bases.push(N0);
  if (R && size(R, 600) <= 600 && (!N0 || key(R) !== key(N0))) bases.push(R);
  const V = R && stepped(R, g.env, g.d + 1);
  if (V && size(V, 2400) <= 2400) bases.push(V);
  if (bases.length === 0) return null;
  const N = bases[0];
  const cands: RwCand[] = [];
  for (const base of bases) rwCands(g, base, base === R && bases.length > 1, depth, path, cands);
  return rwRun(g, cands, depth, rw, path);
};
const rwCands = (g: Goal, N: LTerm, isRaw: boolean, depth: number, path: Set<string>, cands: RwCand[]) => {
  const subs = new Map<string, LTerm>();
  subterms(N, subs);
  const blk: LTerm[] = [];
  blockers(N, blk);
  const blkKeys = new Set(blk.map(key));
  const okFrom = (t: LTerm) => t.$ === "Var" || t.$ === "App" || (t.$ === "Ctr" && t.x.length > 0);
  // hypotheses
  for (let i = g.d - 1; i >= 0; i--) {
    if (!usable(g, i, g.qt)) continue;
    const ts = hypTargets(g, i);
    for (const E of ts) {
      if (E.$ !== "Eql") continue;
      const ka = key(E.a), kb = key(E.b);
      if (ka === kb) continue;
      if (subs.has(kb) && okFrom(E.b)) cands.push({ base: N, from: E.b, to: E.a, e: g.names[i], kind: "rw:hyp", score: (blkKeys.has(kb) ? 0 : 1) + (isRaw ? 0.2 : 0) });
      if (subs.has(ka) && okFrom(E.a)) cands.push({ base: N, from: E.a, to: E.b, e: "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + g.names[i] + ")", kind: "rw:hyp", score: (blkKeys.has(ka) ? 0 : 1) + (isRaw ? 0.2 : 0) });
    }
  }
  // the induction hypothesis and lemmas, on the stuck calls of nf(goal)
  for (const [sk, s] of subs) {
    const hk = headKey(s);
    const h = s.$ === "App" ? unapply(s)[0] : s;
    if (h.$ !== "Ref" && !(s.$ !== "App" && rwIndex.has(hk))) continue;
    const entries: { c: Callee; side: 0 | 1; kind: string }[] = [];
    if (h.$ === "Ref" && job.ih && g.split) {
      const o = attempt(FUEL_NF, () => { const oo = openMeta(job.def.T, job.def.n); return oo ? lower(oo.concl, g.d + 1) : null; });
      if (o && o.$ === "Eql") for (const side of [0, 1] as const) if (headKey(side === 0 ? o.a : o.b) === "R:" + h.k) entries.push({ c: ihCallee(), side, kind: "rw:ih" });
    }
    for (const { L, side } of rwIndex.get(hk) ?? []) {
      if (L.order >= job.order || L.k === job.k) continue;
      entries.push({ c: { text: B.name_show(job.file, L.k), T: (RAW[L.k] as B.Def).T, n: L.n, kind: "lemma" }, side, kind: "rw:lemma" });
      if (entries.length > MAX_CANDS) break;
    }
    for (const { c, side, kind } of entries) {
      if (performance.now() > deadline) throw TIMEOUT;
      const gg: Goal = { ...g, d: g.d + 1 - 1 };
      const a = applyCallee(gg, c, [s], depth, 0, path, (o) => (o.$ === "Eql" ? (side === 0 ? o.a : o.b) : null), () => true);
      if (process.env.GEN2_TRACE && kind === "rw:ih") console.error("[trace] ih on " + show(s, [...g.names, "_"]).slice(0, 100) + " -> " + (a ? a.args.join(", ") : "no"));
      if (!a) continue;
      const o2 = openMeta(c.T, c.n, a.sol.map((x) => (x ? B.term_higher(x, g.env) : null)));
      if (!o2) continue;
      const E = attempt(FUEL_NF, () => lower(o2.concl, g.d + 1));
      if (!E || E.$ !== "Eql" || hasMeta(E)) continue;
      const call = callText(c, a.args);
      const to = side === 0 ? E.b : E.a;
      if (key(to) === sk) continue;
      const e = side === 0 ? "Equal.sym(" + show(E.T, g.names) + ", " + show(E.a, g.names) + ", " + show(E.b, g.names) + ", " + call + ")" : call;
      cands.push({ base: N, from: s, to, e, kind, score: (blkKeys.has(sk) ? 0 : 1) + (c.n === 0 ? -0.5 : kind === "rw:ih" ? 0 : 0.5) + (isRaw ? 0.2 : 0) });
    }
  }
};
const rwRun = (g: Goal, cands: RwCand[], depth: number, rw: number, path: Set<string>): Pf | null => {
  cands.sort((a, b) => a.score - b.score);
  const motiveNames = [...g.names, "_"];
  const later: { c: RwCand; P: string; sub: Goal; gk: string }[] = [];
  const seen = new Set<string>();
  for (const c of cands) {
    if (performance.now() > deadline) throw TIMEOUT;
    const fk = key(c.from);
    const Pt = replace(c.base, fk, B.Var("_", g.d));
    const Gp = replace(c.base, fk, c.to);
    const gpk = key(Gp);
    if (seen.has(gpk)) continue;
    seen.add(gpk);
    if (!closedBelow(Gp, g.d) && Gp.$ !== "Eql") { /* binders: keep */ }
    const P = show(Pt, motiveNames);
    if (process.env.GEN2_TRACE) console.error("[trace] rw " + c.kind + " " + c.e.slice(0, 120) + " : " + P.slice(0, 160));
    if (!tryText(g, "%" + c.e + " : " + P + "; ?TODO")) continue;
    const sub: Goal = { ...g, ty: B.term_higher(Gp, g.env) };
    if (tryText(sub, "{==}")) { tag(c.kind); tag("rfl"); return { t: "rw", e: c.e, P, k: tm("{==}") }; }
    later.push({ c, P, sub, gk: gpk });
  }
  for (const l of later.slice(0, BEAM)) {
    const r = leaf(l.sub, depth, rw - 1, path);
    if (r) {
      const pf: Pf = { t: "rw", e: l.c.e, P: l.P, k: r };
      if (tryText(g, flat(pf))) { tag(l.c.kind); return pf; }
    }
  }
  return null;
};

// ---- node tactics: split ----
const isData = (g: Goal, A: HTerm) => attempt(FUEL_NF, () => { B.term_check(book, g.lhs, A, B.None(), B.Typ(B.Qua(B.Many())), g.ctx, g.d); return true; }) === true;

const split = (n: Goal, j: number): { pat: string; node: Goal }[] | null => {
  let g: Goal | null = n;
  for (let i = 0; i < j && g; i++) g = intro(g, g.pnames[0], g.pmany[0]);
  if (!g) return null;
  const t = wnf(g.ty);
  if (!t || t.$ !== "All" || t.q.$ === "None") return null;
  const A = wnf(t.A);
  if (!A || A.$ !== "ADT") return null;
  const adt = attempt(FUEL_NF, () => B.book_adt(book, A, g!.ctx, job.k));
  if (!adt || adt.c.length === 0) return null;
  const sname = g.pnames[0];
  const used = new Set([...g.names, ...g.pnames]);
  const arms: { pat: string; node: Goal }[] = [];
  for (const ctr of adt.c) {
    const gg = g;
    const tel = attempt(FUEL_NF, () => B.tele_fill(book, ctr.T, A.x, gg.ctx, job.k));
    if (!tel) return null;
    const mk = (cur: HTerm, m: number, xs: HTerm[]): HTerm => {
      if (m === 0) return t.B(B.Ctr(ctr.k, xs));
      const c = B.tele_head(book, cur, gg.ctx, job.k);
      const dem = c.q.$ === "None" ? B.None() : c.q.$ === "Lone" ? t.q : B.quant_add(t.q, t.q);
      return B.All<B.HBody>(dem, c.k, c.i, c.A, (x: HTerm) => mk(c.B(x), m - 1, xs.concat([x])));
    };
    const goal = attempt(FUEL_NF, () => mk(tel, ctr.n, []));
    if (!goal) return null;
    const lhs = g.lhs.n > 0 ? { ...g.lhs, t: B.lhs_ext(g.lhs.t, ctr.k, ctr.n), n: g.lhs.n - 1 + ctr.n } : g.lhs;
    // field names and marks
    const fnames: string[] = [], fmany: boolean[] = [];
    const isNat = ctr.k === "Succ" || ctr.k === "Zero";
    let probe: Goal | null = { ...g, ty: goal, lhs, pend: ctr.n, pnames: [], pmany: [] };
    let cur: HTerm = goal;
    for (let f = 0; f < ctr.n; f++) {
      const c = wnf(cur) as any;
      if (!c || c.$ !== "All") return null;
      const base = isNat ? (sname.length <= 2 ? sname + "p" : "p") : c.k;
      const nm = fresh(base, used);
      const many = !isNat && c.q.$ === "Lone" && probe !== null && isData(probe, c.A);
      fnames.push(nm);
      fmany.push(many);
      probe = probe ? intro({ ...probe, pend: 1, pnames: [nm], pmany: [many] }, nm, many) : null;
      cur = c.B(B.Var(nm, g.d + f));
    }
    const node: Goal = {
      ...g, ty: goal, lhs, pend: ctr.n + g.pend - 1, pnames: [...fnames, ...g.pnames.slice(1)], pmany: [...fmany, ...g.pmany.slice(1)],
      split: true, path: n.path + "/" + shortOf(ctr.k), hc: new Map(),
    };
    const cn = B.name_show(job.file, ctr.k);
    const pat = isNat ? (ctr.k === "Zero" ? "0n" : "1n+" + fnames[0]) : cn + "{" + fnames.map((f, i) => (fmany[i] ? "+" : "") + f).join(", ") + "}";
    arms.push({ pat, node });
  }
  return arms;
};

const splitCands = (n: Goal, lg: Goal): number[] => {
  const out: number[] = [];
  const records: number[] = [];
  let record: Goal | null = n;
  for (let j = 0; j < n.pend && record; j++) {
    const t = wnf(record.ty);
    if (!t || t.$ !== "All") break;
    const A = wnf(t.A);
    if (A?.$ === "ADT" && t.q.$ !== "None") {
      const a = RAW[A.k];
      if (a?.$ === "ADT" && a.c.length === 1 && a.c[0].n > 0 &&
          !/^(U32|F32|Chr|Word)$/.test(A.k) && !/\b(?:WCon|WNil)$/.test(a.c[0].k)) records.push(j);
    }
    record = intro(record, record.pnames[0], record.pmany[0]);
  }
  out.push(...records.slice(-2).reverse());
  const add = (t: LTerm) => {
    if (t.$ !== "Var") return;
    const j = t.i - n.d;
    if (j >= 0 && j < n.pend && !out.includes(j)) out.push(j);
  };
  const N = attempt(FUEL_NF * 2, () => nf(lg.ty, lg.d));
  const blk: LTerm[] = [];
  if (N) blockers(N, blk);
  for (let i = lg.d - 1; i >= n.d; i--) {
    const h = hypTargets(lg, i);
    blockers(h[h.length - 1], blk);
  }
  for (let i = n.d - 1; i >= 0; i--) {
    const h = hypTargets(lg, i);
    blockers(h[h.length - 1], blk);
  }
  blk.forEach(add);
  if (IND) Ind.indSplits(indApi(), n, out);
  const depth = n.path.split("/").length - 1;
  return out.slice(0, depth >= 4 ? 1 : depth >= 2 ? 2 : MAX_SPLIT_CANDS);
};

const solve = (n: Goal, S: number, D: number, partial: boolean): Res => {
  if (performance.now() > deadline) throw TIMEOUT;
  const nk = (attempt(FUEL_NF, () => goalKey(n)) ?? Math.random()) + "#" + n.pnames.join(",") + "#" + S + "," + D + (partial ? "p" : "");
  const m = job.smemo.get(nk);
  if (m) return m;
  let r: Res;
  try {
    r = solveGo(n, S, D, partial);
  } catch (e) {
    // a partial pass keeps what it has: a goal reached past the deadline is a hole
    if (e !== TIMEOUT || !partial) throw e;
    return { pf: { t: "hole", g: introAll(n) ?? n }, holes: 1, closed: 0 };
  }
  job.smemo.set(nk, r);
  return r;
};
const solveGo = (n: Goal, S: number, D: number, partial: boolean): Res => {
  const lg = introAll(n);
  if (!lg) return { pf: { t: "hole", g: n }, holes: 1, closed: 0 };
  for (let dd = 0; dd <= D; dd++) {
    const lf = leaf(lg, dd, dd === 0 ? 1 : MAX_RW, new Set());
    if (lf) {
      if (STREAM) console.error("[gen2] closed " + (n.path || "/") + ": " + flat(lf).slice(0, 160));
      return { pf: lf, holes: 0, closed: 1 };
    }
  }
  let best: Res = { pf: { t: "hole", g: lg }, holes: 1, closed: 0 };
  if (S === 0 || n.pend === 0) return best;
  for (const j of splitCands(n, lg)) {
    const arms = split(n, j);
    if (!arms) continue;
    let holes = 0, closed = 0;
    const out: { pat: string; k: Pf }[] = [];
    let i = 0;
    for (; i < arms.length; i++) {
      const r = solve(arms[i].node, S - 1, D, partial);
      holes += r.holes; closed += r.closed;
      out.push({ pat: arms[i].pat, k: r.pf });
      if (!partial && r.holes > 0) break;
    }
    if (i < arms.length) continue;
    const pf: Pf = { t: "mt", x: n.pnames[j], arms: out };
    if (holes === 0) { tag("split"); return { pf, holes: 0, closed }; }
    if (holes < best.holes || (holes === best.holes && closed > best.closed)) best = { pf, holes, closed };
  }
  return best;
};

// ---- decomposition ----
// the best one-step skeleton for a leaf goal that the search does not close: an applied callee (most
// specific first) whose solved premises are filled and whose open premises are holes; fewest holes
// first, then the smallest holes; no hole may restate the goal
// the keys of a goal: as stated, and with the sides of an equation swapped
const goalKeys = (g: Goal): string[] => {
  const pre = g.ckey + "|-" + g.qt.$[0];
  const out: string[] = [];
  for (const t of [lower(g.ty, g.d), nf(g.ty, g.d)]) {
    out.push(pre + key(t));
    if (t.$ === "Eql") out.push(pre + key(B.Eql(t.b, t.a, t.T)), pre + "=" + key(t.a) + "|" + key(t.b), pre + "=" + key(t.b) + "|" + key(t.a));
  }
  return out;
};
const bestStep = (g: Goal, anc: Set<string> = new Set()): Pf | null => {
  const raw = lower(g.ty, g.d);
  const targets = goalTargets(g, raw);
  const gk = goalKey(g);
  const own = new Set(attempt(FUEL_NF, () => goalKeys(g)) ?? []);
  const callees: Callee[] = hypCallees(g);
  if (job.ih && g.split) callees.push(ihCallee());
  const lem = lemmaCands(g, targets).map((c) => { const pr = { n: 0, probe: true, spec: -1 }; applyCallee(g, c, targets, 1, 0, new Set(), null, () => false, pr); return { c, spec: pr.spec! }; });
  callees.push(...lem.filter((x) => x.spec >= 0).sort((a, b) => b.spec - a.spec).map((x) => x.c));
  // a weak hole (see below) can be a stronger claim than the goal, often false (K.Ok.wk at budget 1n
  // for Sh.body.ok): prefer steps with fewer weak holes, then fewer holes, then smaller ones
  let best: { pf: Pf; holes: number; size: number; same: number } | null = null;
  const tries = { n: 0 };
  // past the deadline, the best step found so far stands (a TIMEOUT used to discard it)
  try { for (const c of callees) {
    if (tries.n >= 24) break;
    // premises get closers only (depth 1, no rewrite): decompose searches each hole of the chosen step on
    // its own budget, so a deep search here only spent the budget before the right callee was tried
    applyCallee(g, c, targets, 1, 0, new Set([gk]), null, (a) => {
      const hs = a.holes ?? [];
      if (process.env.GEN2_TRACE) console.error("[trace] bestStep " + c.text + ": " + hs.length + " holes of " + c.n);
      if (hs.length === 0 || hs.length >= c.n) return false;
      if (hs.some((h) => (attempt(FUEL_NF, () => goalKeys(h)) ?? [gk]).some((k) => k === gk || anc.has(k) || own.has(k)))) { if (process.env.GEN2_TRACE) console.error("[trace]   restates the goal"); return false; }
      const s = callText(c, a.args.map((x) => (x === HOLE ? "?TODO" : x)));
      if (!tryText(g, s)) {
        if (process.env.GEN2_TRACE) { try { B.term_check(book, g.lhs, parseFrag(s, g), g.qt, g.ty, g.ctx, g.d); } catch (e: any) { console.error("[trace] bestStep " + c.text + " rejected: " + errText(e).slice(0, 600)); } }
        return false;
      }
      const sz = hs.reduce((acc, h) => acc + (attempt(FUEL_NF, () => size(lower(h.ty, h.d))) ?? 99), 0);
      // weak: the hole is the goal but in exactly one argument of the same head (K.Ok.wk's budget,
      // le_trans's middle term): it can be stronger than the goal; Ok.seq's first statement differs in
      // the program and the predicate, so it is not weak
      for (const h of hs) h.weak = attempt(FUEL_NF, () => {
        const [fa, xa] = unapply(lower(h.ty, h.d)), [fb, xb] = unapply(raw);
        return fa.$ === "Ref" && fb.$ === "Ref" && fa.k === fb.k && xa.length === xb.length && xa.filter((x, i) => key(x) !== key(xb[i])).length === 1;
      }) === true;
      const same = hs.filter((h) => h.weak).length;
      if (!best || same < best.same || (same === best.same && (hs.length < best.holes || (hs.length === best.holes && sz < best.size)))) {
        best = { pf: { t: "app", s: callText(c, a.args), subs: hs.map((h) => ({ t: "hole", g: h }) as Pf) }, holes: hs.length, size: sz, same };
      }
      return false;
    }, tries, true);
  } } catch (e) { if (e !== TIMEOUT || !best) throw e; }
  return best ? (best as any).pf : null;
};

// attack a leaf goal with its own budget; when it stays open, decompose it one step and recurse
const decompose = (g: Goal, level: number, until: number, anc: Set<string> = new Set()): Res => {
  const hole: Res = { pf: { t: "hole", g }, holes: 1, closed: 0 };
  if (performance.now() > until) return hole;
  deadline = Math.min(until, performance.now() + HOLE_BUDGET);
  try {
    for (let dd = 0; dd <= MAX_DEPTH + 1; dd++) {
      const r = leaf({ ...g, lvl: 0 }, dd, dd === 0 ? 1 : MAX_RW, new Set());
      if (r) { tag("decomp"); if (STREAM) console.error("[gen2] closed " + g.path + ": " + flat(r).slice(0, 160)); return { pf: r, holes: 0, closed: 1 }; }
    }
  } catch (e) { if (e !== TIMEOUT) throw e; }
  if (level >= MAX_DECOMP) return hole;
  deadline = Math.min(until, performance.now() + HOLE_BUDGET);
  let step: Pf | null = null;
  const anc2 = new Set([...anc, ...(attempt(FUEL_NF, () => goalKeys(g)) ?? [])]);
  try { step = bestStep({ ...g, lvl: 0 }, anc2); } catch (e) { if (e !== TIMEOUT) throw e; }
  if (!step || step.t !== "app") return hole;
  const subs: Pf[] = [];
  let holes = 0, closed = 1;
  for (const s of step.subs) {
    const r = decompose((s as any).g, level + 1, until, anc2);
    subs.push(r.pf); holes += r.holes; closed += r.closed;
  }
  return { pf: { t: "app", s: step.s, subs }, holes, closed };
};
const fillHoles = (p: Pf, f: (g: Goal) => Res, acc: { holes: number; closed: number }): Pf => {
  switch (p.t) {
    case "hole": { const r = f(p.g); acc.holes += r.holes; acc.closed += r.closed; return r.pf; }
    case "rw": return { ...p, k: fillHoles(p.k, f, acc) };
    case "mt": return { ...p, arms: p.arms.map((a) => ({ pat: a.pat, k: fillHoles(a.k, f, acc) })) };
    case "app": return { ...p, subs: p.subs.map((x) => fillHoles(x, f, acc)) };
    default: return p;
  }
};

// ---- guidance for a miss: why, a split that a lemma asks for, templates ----
// The lemmas whose conclusion matches a goal (most specific first), each with what blocks it: a premise
// that no hypothesis gives (a clash: it would, once a variable is split to a constructor), or a
// parameter that neither the goal nor a hypothesis fixes. A large goal that the search cannot close
// often needs one such lemma, after one split (D.alloc.post: al.fresh, once ps is Nil{}).
type Issue = { name: string; kind: "clash" | "open" | "unfixed" | "part"; text: string; clash?: [number, string][] };
// the parts of a hypothesis that is a nested pair of facts (D.HSK(..) = P2(RtsK(..), P2(..))): each
// with its path (1 = first, 2 = second) and type, at most 8 levels and 24 parts
const tupleParts = (g: Goal, i: number): { path: string; T: LTerm }[] => {
  const out: { path: string; T: LTerm }[] = [];
  const go = (h: HTerm, p: string) => {
    if (out.length >= 24) return;
    const w = p.length < 8 ? wnf(h) : undefined;
    const t = w?.$ === "ADT" ? RAW[w.k] : undefined;
    if (w?.$ === "ADT" && t?.$ === "ADT" && t.c.length === 1 && w.x.length === 4) {
      const second = wnf(w.x[3]);
      if (second?.$ === "Lam") { go(w.x[2], p + "1"); go((second.f as B.HBody)(B.Var("_", 1e7)), p + "2"); return; }
    }
    if (p.length > 0) { const T = attempt(FUEL_NF, () => lower(h, g.d)); if (T) out.push({ path: p, T }); }
  };
  const a = ann(g, i);
  if (a) attempt(FUEL_NF * 2, () => { go(a.T, ""); return true; });
  return out.length >= 2 ? out : [];
};
// the destructuring that names the part at path (2 then 1: (_, (x, _)) = h)
const partPat = (p: string): string => (p === "" ? "x" : p[0] === "1" ? "(" + partPat(p.slice(1)) + ", _)" : "(_, " + partPat(p.slice(1)) + ")");
const toHs = (g: Goal, s: (LTerm | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
const targetsOf = (g: Goal): LTerm[] => goalTargets(g, lower(g.ty, g.d));
const rankedLemmas = (g: Goal, targets: LTerm[]): Callee[] =>
  lemmaCands(g, targets).map((c) => { const pr = { n: 0, probe: true, spec: -1 }; applyCallee(g, c, targets, 1, 0, new Set(), null, () => false, pr); return { c, spec: pr.spec! }; })
    .filter((x) => x.spec >= 0).sort((a, b) => b.spec - a.spec).map((x) => x.c);
const conclSols = (g: Goal, c: Callee, targets: LTerm[]): (LTerm | null)[][] => {
  const o = openMeta(c.T, c.n);
  const pc = o && attempt(FUEL_NF, () => lower(o.concl, g.d));
  if (!o || !pc) return [];
  const out: (LTerm | null)[][] = [];
  const seen = new Set<string>();
  const push = (p: LTerm, t: LTerm) => {
    const s: (LTerm | null)[] = new Array(c.n).fill(null);
    if (!match(p, t, s, g.d)) return;
    const k = s.map((x) => (x ? key(x) : "_")).join(";");
    if (!seen.has(k)) { seen.add(k); out.push(s); }
  };
  for (const t of targets) push(pc, t);
  const pn = nfPattern(c, o.concl, g.d);
  if (pn && key(pn) !== key(pc)) push(pn, targets[targets.length - 1]);
  return out;
};
const issuesOf = (g: Goal, c: Callee, sol0: (LTerm | null)[]): Issue[] => {
  const sol = sol0.slice();
  const out: Issue[] = [];
  const o = openMeta(c.T, c.n, toHs(g, sol));
  if (!o) return out;
  for (let j = 0; j < c.n; j++) {
    const dm = o.doms[j];
    if (sol[j] || !isPrem(dm.A, g.d)) continue;
    const A = attempt(FUEL_NF, () => lower(dm.A, g.d));
    if (!A) continue;
    let ok = false, near: { cl: [number, string][]; h: string } | null = null;
    for (let i = g.d - 1; i >= 0 && !ok; i--) {
      if (!usable(g, i, B.quant_dem(dm.q, g.qt))) continue;
      for (const t of hypTargets(g, i)) {
        const s2 = sol.slice();
        if (match(A, t, s2, g.d)) { for (let m = 0; m < sol.length; m++) sol[m] = s2[m]; ok = true; break; }
        const cl: [number, string][] = [];
        clashes = cl;
        try { if (match(A, t, sol.slice(), g.d) && cl.length > 0 && (!near || cl.length < near.cl.length)) near = { cl, h: g.names[i] }; } finally { clashes = null; }
      }
    }
    if (ok) continue;
    if (near) { out.push({ name: dm.k, kind: "clash", text: near.h, clash: near.cl }); continue; }
    // a part of a tuple hypothesis that fits: the agent destructures that hypothesis once
    let part: string | null = null;
    for (let i = g.d - 1; i >= 0 && !part; i--) {
      if (!usable(g, i, B.quant_dem(dm.q, g.qt))) continue;
      for (const pt of tupleParts(g, i)) if (match(A, pt.T, sol.slice(), g.d)) { part = partPat(pt.path) + " = " + g.names[i]; break; }
    }
    if (part) { out.push({ name: dm.k, kind: "part", text: part }); continue; }
    else out.push({ name: dm.k, kind: "open", text: (attempt(FUEL_NF, () => show(A, g.names)) ?? "?").replace(/\?(\d+)\^\d+/g, (_, m) => "?" + (o.doms[+m]?.k ?? m)) });
  }
  const o2 = openMeta(c.T, c.n, toHs(g, sol));
  for (let j = 0; o2 && j < c.n; j++) if (!sol[j] && !isPrem(o2.doms[j].A, g.d)) out.push({ name: o2.doms[j].k, kind: "unfixed", text: "" });
  return out;
};
const clip = (s: string, n = 160) => (s.length > n ? s.slice(0, n) + " ..." : s);
const issueText = (g: Goal, is: Issue): string =>
  is.kind === "clash" ? "premise " + is.name + ": hypothesis " + is.text + " fits once " + is.clash!.map(([i, k]) => g.names[i] + " is " + B.name_show(job.file, k)).join(", ") + " (split)"
  : is.kind === "part" ? "premise " + is.name + ": a part of a hypothesis fits (x below): " + is.text
  : is.kind === "open" ? "premise " + is.name + " open: " + clip(is.text)
  : "parameter " + is.name + " fixed by neither the goal nor a hypothesis (give it)";
// the candidates whose conclusion matches the goal, each with what blocks it (at most max)
const matchLines = (g: Goal, targets: LTerm[], cands: Callee[], max: number): string[] => {
  // noise left out (S1's tally): a lemma whose equation is over another type than the goal's (the
  // matcher tolerates a type mismatch), and one with a type parameter that nothing fixes (Equal.cong's
  // A); the rest ranked by their number of issues
  const gT = targets[0]?.$ === "Eql" ? targets[0].T : null;
  const rows: { n: number; s: string }[] = [];
  for (const c of cands) {
    if (rows.length >= max * 3) break;
    const sols = conclSols(g, c, targets);
    if (sols.length === 0) continue;
    const o = attempt(FUEL_NF, () => openMeta(c.T, c.n, toHs(g, sols[0]!)));
    const cT = o ? attempt(FUEL_NF, () => lower(o.concl, g.d)) : undefined;
    if (gT && cT?.$ === "Eql" && !hasMeta(cT.T) && key(cT.T) !== key(gT) && attempt(FUEL_NF, () => B.term_compare("EQ", book, B.term_higher(cT.T, g.env), B.term_higher(gT, g.env), g.d)) !== true) continue;
    const is = issuesOf(g, c, sols[0]!);
    if (o && is.some((x) => x.kind === "unfixed" && wnf(o.doms.find((dm) => dm.k === x.name)?.A ?? B.Ref("?"))?.$ === "Typ")) continue;
    rows.push({ n: is.length, s: c.text + (c.kind === "hyp" ? " (hypothesis)" : "") + ": " + (is.length === 0 ? "every premise is a hypothesis or fixed (more --budget may close it)" : is.slice(0, 3).map((x) => issueText(g, x)).join("; ")) });
  }
  return rows.sort((a, b) => a.n - b.n).slice(0, max).map((r) => r.s);
};
// usable lemmas indexed under the goal's head that do not match it (a different argument shape), with
// their conclusions (at most max; names in skip are left out)
const nearMisses = (g: Goal, targets: LTerm[], skip: Set<string>, max: number): string[] => {
  const out: string[] = [];
  for (const t of targets) {
    // only a head that names a def or a constructor: a function goal (P) or a variable head is noise
    const hk = headKey(t);
    if (!/^(E\|)?(R|C|A):/.test(hk)) continue;
    for (const L of applyIndex.get(hk) ?? []) {
      const nm = B.name_show(job.file, L.k);
      if (out.length >= max || skip.has(nm) || L.order >= job.order || L.k === job.k) continue;
      skip.add(nm);
      out.push(nm + " : " + conclOf(L.k));
    }
  }
  return out;
};
const diagnose = (g: Goal, until: number): string => {
  const lines: string[] = [], near: string[] = [];
  const d0 = deadline;
  deadline = until;
  try {
    const targets = targetsOf(g);
    lines.push(...matchLines(g, targets, [...hypCallees(g), ...rankedLemmas(g, targets)].slice(0, 16), 4).map((l) => "#   " + l));
    if (lines.length === 0) near.push(...nearMisses(g, targets, new Set(), 3).map((l) => "#   " + l));
  } catch (e) { if (e !== TIMEOUT) throw e; } finally { deadline = d0; }
  return lines.length ? "# why: lemmas whose conclusion matches the goal, and what blocks each\n" + lines.join("\n") : "# why: no lemma's conclusion matches the goal (as stated or in normal form): it needs a new lemma or a split" + (near.length ? "; lemmas with its head that do not match (compare the arguments):\n" + near.join("\n") : "");
};
// whole-body mode: the first clash of the best lemmas names a root parameter and a constructor;
// split there, and decompose the arm that the lemma wants with a full budget (the others: leaf only)
const guidedSplit = (root: Goal, until: number, budget: number): Res | null => {
  const lg = introAll(root);
  if (!lg) return null;
  let pick: [number, string] | null = null;
  deadline = until;
  try {
    const targets = targetsOf(lg);
    for (const c of rankedLemmas(lg, targets).slice(0, 12)) {
      for (const s of conclSols(lg, c, targets)) {
        for (const is of issuesOf(lg, c, s)) {
          const cl = is.clash;
          if (is.kind === "clash" && cl!.length === 1 && cl![0][0] < root.pend) { pick = cl![0]; break; }
        }
        if (pick) break;
      }
      if (pick) break;
    }
  } catch (e) { if (e !== TIMEOUT) throw e; }
  if (!pick) return null;
  const arms = split(root, pick[0]);
  if (!arms) return null;
  const want = root.path + "/" + shortOf(pick[1]);
  const hb = HOLE_BUDGET;
  const out: { pat: string; k: Pf }[] = [];
  let holes = 0, closed = 0;
  try {
    for (const a of arms) {
      const al = introAll(a.node);
      let r: Res = { pf: { t: "hole", g: al ?? a.node }, holes: 1, closed: 0 };
      if (al) {
        HOLE_BUDGET = a.node.path === want ? Math.max(hb, budget / 2) : Math.min(hb, 300);
        r = decompose(al, a.node.path === want ? 0 : MAX_DECOMP, until);
      }
      out.push({ pat: a.pat, k: r.pf });
      holes += r.holes; closed += r.closed;
    }
  } finally { HOLE_BUDGET = hb; }
  tag("guided");
  return { pf: { t: "mt", x: root.pnames[pick[0]], arms: out }, holes, closed };
};
// proven defs of the entry file whose statements share the most names with the goal's (and its
// conclusion's head): their bodies are templates (D.inc.post is one call to inc.top: D.alloc.post
// likely wants an al.top built the same way)
const tinfo = new Map<string, { refs: Set<string>; head: string } | null>();
const typeInfo = (k: string) => {
  if (!tinfo.has(k)) {
    const t = RAW[k] as B.Def;
    const refs = new Set<string>();
    const o = attempt(FUEL_NF, () => openMeta(t.T, t.n));
    const ok = attempt(FUEL_NF, () => { refsOf(lower(t.T, 0), refs); return true; });
    tinfo.set(k, ok && o ? { refs, head: attempt(FUEL_NF, () => headKey(lower(o.concl, t.n))) ?? "*" } : null);
  }
  return tinfo.get(k)!;
};
const templates = (k: string, refs: Set<string>, head: string): string => {
  const sc: [number, string][] = [];
  for (const d of new Set(book.order.slice(N0))) {
    const t = RAW[d];
    if (d === k || d.includes("~") || t?.$ !== "Def" || t.v === null || isOpen(d) || !defSrc(d)) continue;
    const ti = typeInfo(d);
    if (!ti || ti.refs.size === 0) continue;
    let inter = 0;
    for (const r of ti.refs) if (refs.has(r)) inter++;
    sc.push([inter / (refs.size + ti.refs.size - inter) + (ti.head === head && head !== "*" ? 0.3 : 0), d]);
  }
  sc.sort((a, b) => b[0] - a[0]);
  const top = sc.filter(([s]) => s >= 0.25).slice(0, 3);
  if (top.length === 0) return "";
  return "# similar proven defs (templates):\n" + top.map(([, d]) => {
    const body = defSrc(d)!.body.split("\n").filter((l) => l.trim() !== "");
    return "#   " + B.name_show(job.file, d) + ":\n" + body.slice(0, 6).map((l) => "#   " + clip(l, 200)).join("\n") + (body.length > 6 ? "\n#     ... (" + body.length + " lines)" : "");
  }).join("\n");
};
const hintsFor = (k: string, g: Goal, whole: boolean): string => {
  const until = performance.now() + Math.max(300, BUDGET / 2);
  const ti = whole ? typeInfo(k) : null;
  const refs = ti?.refs ?? new Set<string>();
  if (!ti) attempt(FUEL_NF, () => { refsOf(lower(g.ty, g.d), refs); return true; });
  const head = ti?.head ?? attempt(FUEL_NF, () => headKey(lower(g.ty, g.d))) ?? "*";
  const legend = /<>|\[\]/.test(showGoal(g)) ? "# (printing: [] is Nil{}, a <> b is Con{a, b})\n" : "";
  return legend + diagnose(g, until) + "\n" + templates(k, refs, head);
};

// ---- helpers: each open hole as its own lemma (--helpers, --write) ----
// The helper's statement is exactly the hole's goal over the hole's whole context (same names, order
// and quantities), so it holds iff the hole does; the hole becomes a call of it. Each helper is then a
// job of its own (own budget, own cache) that the agent or gen2 attacks by name. Written helpers are
// checked by serve's reload (STATEMENT ERROR) like any changed statement.
const helperDef = (g: Goal): { params: string; goal: string; args: string } | null => {
  const names = g.names.slice(0, g.d);
  if (new Set(names).size !== names.length || names.some((x) => x === "_" || x === "")) return null;
  // a goal that still names an open parameter of its step (K.Ok.seq's predicate, a ?TODO) is not a
  // statement yet: the agent fills the parameter first
  if (attempt(FUEL_NF, () => hasMeta(lower(g.ty, g.d))) !== false) return null;
  const ps: string[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = ann(g, i);
    const T = a && attempt(FUEL_NF, () => show(lower(a.T, i), names.slice(0, i)));
    if (!a || T === undefined) return null;
    ps.push("  " + B.quant_show(a.q) + names[i] + ": " + T);
  }
  const goal = attempt(FUEL_NF, () => show(lower(g.ty, g.d), names));
  return goal === undefined ? null : { params: ps.join(",\n"), goal, args: names.join(", ") };
};
const helperName = (k: string, used: Set<string>, sfx = "h"): string => {
  const base = shortOf(k);
  const txt = fileText(defSrc(k)!.file);
  const taken = new Set(Object.keys(RAW).map(shortOf));
  for (let i = 1; ; i++) {
    const nm = base + "." + sfx + i;
    if (!used.has(nm) && !taken.has(nm) && !txt.includes("def " + nm + "(")) { used.add(nm); return nm; }
  }
};
// the holes of p (at most 6) as calls of new helpers; the rest stay ?TODO
const helperize = (k: string, p: Pf, used: Set<string>): { pf: Pf; defs: string[] } => {
  const defs: string[] = [];
  const pf = fillHoles(p, (g) => {
    const h = defs.length < 6 ? helperDef(g) : null;
    if (!h) return { pf: { t: "hole", g }, holes: 1, closed: 0 };
    const nm = helperName(k, used);
    defs.push("# gen2: an open subgoal of " + shortOf(k) + " (at " + (g.path || "/") + "), as its own lemma\ndef " + nm + "(\n" + h.params + ") ->\n  " + h.goal + ":\n  ?TODO\n");
    return { pf: tm(nm + "(" + h.args + ")"), holes: 0, closed: 0 };
  }, { holes: 0, closed: 0 });
  return { pf, defs };
};
// ---- a match bend2 cannot elaborate, as its own def (parseErr) ----
// The helper's statement is the goal at the match (bend2's goal of a hole put in place of the block,
// over its whole context). A computed scrutinee v becomes a parameter sc with an equation hsc: {sc == v}
// (so the helper holds iff the goal does), and v is generalized to sc in the goal and in the later
// context types; the helper's body is the block with sc matched. A binder scrutinee (a match after a
// local statement) stays the parameter it is. gen2 checks the helper's statement, its body and the call
// in the loaded book before it prints them, and says which of them fail.
const maxVar = (t: LTerm): number => {
  let m = -1;
  const st: LTerm[] = [t];
  while (st.length) {
    const x = st.pop()!;
    switch (x.$) {
      case "Var": if (x.i < META) m = Math.max(m, x.i); break;
      case "App": st.push(x.f, x.x); break;
      case "Ctr": case "ADT": st.push(...x.x); break;
      case "Eql": st.push(x.a, x.b, x.T); break;
      case "All": st.push(x.A, x.B as LTerm); break;
      case "Lam": st.push(x.f as LTerm); break;
    }
  }
  return m;
};
// text with every whole occurrence of expression e (not inside a longer name) replaced by x
const replaceExpr = (text: string, e: string, x: string): string => {
  if (e === "") return text;
  let out = "", i = 0;
  for (let j = text.indexOf(e); j >= 0; j = text.indexOf(e, i)) {
    const before = j > 0 ? text[j - 1] : " ", after = text[j + e.length] ?? " ";
    const ok = !/[\w.]/.test(before) && !(/[\w.]$/.test(e) && /[\w.(]/.test(after));
    out += text.slice(i, j) + (ok ? x : e);
    i = j + e.length;
  }
  return out + text.slice(i);
};
const scrutFix = (pe: { err: B.Err; blk: Blk }): string => {
  const { blk } = pe;
  const lines = linesOf(entry);
  const k = defOfLine(blk.S) ?? "";
  const ds = k ? defSrc(k) : null;
  if (!ds) return "# no helper: the def at line " + (blk.S + 1) + " is not in the loaded book";
  const bl = ds.body.split("\n");
  const off = blk.S - ds.bodyLine, end = blk.E - ds.bodyLine;
  if (off < 0 || end > bl.length) return "# no helper: the match is not inside the body of " + k;
  const inBody = (hole: string) => holeOut(bl, { ...blk, S: off, E: end }, hole).join("\n");
  const old = fuel;
  fuel = FUEL_FINAL;
  try {
    job = newJob(k);
    let err: any = null;
    try { checkDef(k, inBody("?gen2hole")); } catch (e) { err = e; }
    const g = holeGoal(k, err, "match");
    if (!g) return "# no helper: bend2 stops before the match: " + (err ? errText(err) : "no error");
    const names = g.names.slice(0, g.d);
    if (new Set(names).size !== names.length || names.some((x) => x === "_" || x === "")) return "# no helper: the context at the match has repeated or anonymous binders (" + names.join(", ") + "); name them";
    const used = new Set(names);
    const hn = helperName(k, new Set(), "m");
    // the block's lines re-indented to the helper's body (the block's own indentation -> 2 spaces)
    const re = (ls: string[]) => ls.map((l) => (l.startsWith(blk.ind) ? "  " + l.slice(blk.ind.length) : l.trim() === "" ? "" : "  " + l.trim()));
    const rest = re(lines.slice(blk.H + 1, blk.E));
    const isVar = blk.kind === "match" && used.has(blk.scrut);
    const pshow = (i: number) => B.quant_show(ann(g, i)!.q) + names[i] + ": " + show(lower(ann(g, i)!.T, i), names.slice(0, i));
    let params: string[], body: string[], callArgs: string[], goal = show(lower(g.ty, g.d), names);
    if (isVar) {
      params = names.map((_, i) => pshow(i));
      body = re(lines.slice(blk.S, blk.E));
      callArgs = names;
    } else {
      // a plain binder (`+x = v`) keeps its name as the parameter; a pattern or a match gets sc
      const plain = blk.kind === "local" && /^[+-]?[A-Za-z_]\w*$/.test(blk.pat) ? blk.pat.replace(/^[+-]/, "") : null;
      let sc = plain ?? "sc";
      for (let i = 2; used.has(sc) || reserved(sc); i++) sc = (plain ?? "sc") + i;
      let hsc = "h" + sc;
      for (let i = 2; used.has(hsc) || reserved(hsc); i++) hsc = "h" + sc + i;
      let v: HTerm, T: HTerm;
      try {
        v = parseFrag(blk.scrut, g);
        T = B.term_infer(book, g.lhs, v, B.None(), g.ctx, g.d).ty;
      } catch (e) { return "# no helper: the scrutinee " + blk.scrut + " does not check at the match:\n" + errText(e); }
      const vl = lower(v, g.d), Tl = lower(T, g.d);
      const vs = show(vl, names), Ts = show(Tl, names);
      const p = Math.max(maxVar(vl), maxVar(Tl)) + 1;
      const gen = (t: string) => replaceExpr(replaceExpr(t, blk.scrut, sc), vs, sc);
      params = names.map((_, i) => (i < p ? pshow(i) : gen(pshow(i))));
      params.splice(p, 0, (isData(g, T) ? "+" : "") + sc + ": " + Ts, hsc + ": {" + sc + " == " + vs + " : " + Ts + "}");
      goal = gen(goal);
      body = blk.kind === "match" ? ["  match " + sc + ":", ...rest] : plain ? rest : ["  " + blk.pat + " = " + sc, ...rest];
      callArgs = [...names.slice(0, p), blk.scrut, "{==}", ...names.slice(p)];
    }
    const head = "def " + hn + "(\n" + params.map((x) => "  " + x).join(",\n") + ") ->\n  " + goal + ":";
    const hbody = body.join("\n");
    const call = hn + "(" + callArgs.join(", ") + ")";
    // check it in the loaded book: the helper's statement, its body, and k with the call
    const file = sourceFiles.get(k)!;
    const n0 = book.order.length;
    const verdict: string[] = [];
    try {
      B.parse_book(book, TOP, head + "\n  ?TODO\n", file.ns, file.al);
      const hk = book.order[n0] ?? hn;
      const se = stmtError(hk);
      if (se) verdict.push("its statement does NOT check:\n" + se);
      else {
        try { checkDef(hk, hbody, head, file); verdict.push("its statement and body check"); } catch (e) { verdict.push("its statement checks, its body does NOT:\n" + errText(e)); }
        try { checkDef(k, inBody(call)); verdict.push(shortOf(k) + " with the call checks"); } catch (e) { verdict.push(shortOf(k) + " with the call does NOT check:\n" + errText(e)); }
      }
    } catch (e) {
      verdict.push("gen2 could not check it: " + errText(e));
    } finally {
      for (const x of book.order.slice(n0)) delete RAW[x];
      book.order.length = n0;
    }
    const what = blk.kind === "match" ? "match" : "destructuring";
    return "# FIX: give the " + what + " of " + blk.scrut + " its own def. gen2 checked it in its book: " + verdict.join("; ") + "\n" +
      "# 1. paste above `def " + shortOf(k) + "(`" + (isVar ? "" : " (the scrutinee is a parameter, with an equation: the helper holds iff the goal at the " + what + " does)") + ":\n" +
      "# the " + what + " of " + shortOf(k) + " (line " + (blk.S + 1) + "), as its own def\n" + head + "\n" + hbody + "\n" +
      "# 2. replace lines " + (blk.S + 1) + "-" + blk.E + " (the " + what + (blk.kind === "match" ? " and its arms" : " and the rest of its block") + ") with:\n" + blk.ind + call + "\n";
  } finally { fuel = old; }
};
// put body as k's body and defs above k's def (and its comment) in k's file; the file must still hold
// the body gen2 read
const writeBack = (k: string, ds: Src, body: string, defs: string[]): string => {
  const lines = (ds.file === entry && reqText !== undefined ? pendingWrite ?? reqText : fs.readFileSync(ds.file, "utf8")).split("\n");
  const n = ds.body.split("\n").length;
  if (lines.slice(ds.bodyLine, ds.bodyLine + n).join("\n") !== ds.body) return "[gen2] --write skipped: " + path.basename(ds.file) + " changed since gen2 read it (ask again)";
  lines.splice(ds.bodyLine, n, ...body.split("\n"));
  let at = defLine(ds.file, shortOf(k));
  while (at > 0 && lines[at - 1].startsWith("#")) at--;
  if (defs.length > 0) lines.splice(at, 0, ...defs.join("\n").split("\n"));
  if (ds.file === entry && reqText !== undefined) pendingWrite = lines.join("\n"); // the client writes it
  else fs.writeFileSync(ds.file, lines.join("\n"));
  return "[gen2] wrote " + path.basename(ds.file) + ": the body of " + shortOf(k) + (defs.length ? " and " + defs.length + " helper(s) above it" : "");
};

// ---- jobs ----
const rootGoal = (k: string): Goal => {
  const def = RAW[k] as B.Def;
  const qs = B.tele_unbind(book, def.T).doms.map((dm) => dm[0]);
  const pnames: string[] = [];
  let t = def.T;
  for (let j = 0; j < def.n; j++) { const s = B.term_strip(t) as any; pnames.push(s.k); t = s.B(B.Var(s.k, j)); }
  return {
    ctx: B.ctx_nil(), d: 0, ty: def.T, lhs: { t: B.Ref(k), n: def.n - def.x, def: k, qs, u: def.u }, qt: B.Lone(), env: null,
    names: [], ckey: "", pend: def.n, pnames, pmany: pnames.map(() => false), split: false, path: "", lvl: 0, hc: new Map(),
  };
};
const newJob = (k: string): Job => {
  const def = RAW[k] as B.Def;
  return { k, def, order: ORDER.get(k) ?? book.order.length, file: sourceFiles.get(k)!, short: shortOf(k), tags: new Map(), memo: new Map(), smemo: new Map(), gi: new Map(), closed: 0, ih: true };
};

type Outcome = { ok: boolean; text: string | null; partial: string | null; partialBody?: string; hints?: string; helpers?: { body: string; defs: string[] }; holes: number; closed: number; ms: number; tags: string[]; why?: string };

const showGoal = (g: Goal): string => {
  const clip = (s: string) => s.length > 2000 ? s.slice(0, 2000) + " ... [truncated]" : s;
  const lines: string[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = ann(g, i)!;
    lines.push("    " + B.quant_show(a.q) + g.names[i] + " : " + clip(show(lower(a.T, i), g.names.slice(0, i))));
  }
  // ?p<j>: the step's open parameter j (a predicate the agent chooses: the hole at path #<callee>.<j>)
  const raw = clip(show(lower(g.ty, g.d), g.names)).replace(/\?(\d+)\^\d+/g, "?p$1");
  const pred = attempt(FUEL_NF, () => isPredType(g.ty)) === true && /#[^#]*\.\d+$/.test(g.path)
    ? "  (a predicate to choose: write it here; the other holes of this step name it ?p" + g.path.slice(g.path.lastIndexOf(".") + 1) + ")\n" : "";
  return pred + "  goal : " + raw + "\n  context:\n" + lines.join("\n").replace(/\?(\d+)\^\d+/g, "?p$1");
};

// prove the whole body of k (its body forgotten)
const proveDef = (k: string, budget: number): Outcome => {
  job = newJob(k);
  const t0 = performance.now();
  deadline = t0 + budget;
  const root = rootGoal(k);
  let best: Res | null = null;
  let full: Pf | null = null;
  let why = "", stalled = false;
  lastWin = t0;
  stallWindow = Math.max(300, budget * 0.6);
  try {
    // a cost level that meets no goal the earlier levels did not meet (the memos do not grow) means the
    // search space is exhausted: deeper levels repeat it, so the search stops early (no progress possible)
    let seen = -1;
    outer: for (let cost = 1; cost <= MAX_SPLIT + MAX_DEPTH; cost++) {
      for (let S = Math.min(MAX_SPLIT, cost - 1); S >= 0; S--) {
        const D = Math.min(MAX_DEPTH, cost - S);
        if (D < 1 && cost > 1) continue;
        const r = solve(root, S, D, false);
        if (r.holes === 0) { full = r.pf; break outer; }
      }
      const size = job.memo.size + job.smemo.size + job.gi.size;
      if (cost >= 3 && size === seen) { why = "the search space is exhausted (no new goal at cost " + cost + ")"; break; }
      seen = size;
      // a quarter of the budget gone and not one subgoal closed anywhere: no progress, answer now
      if (performance.now() - t0 > budget / 4 && ![...job.memo.values()].some((m) => m.pf)) { why = "no subgoal closed in " + Math.round(performance.now() - t0) + " ms: stopped early"; stalled = true; break; }
    }
  } catch (e) {
    if (e !== TIMEOUT) throw e;
    why = performance.now() - lastWin > stallWindow && performance.now() < deadline ? "no subgoal closed for " + Math.round(stallWindow) + " ms: stopped early" : "time";
    if (why !== "time") stalled = true;
  }
  stallWindow = 0;
  if (!full && !stalled && (PARTIAL || DECOMP)) {
    deadline = performance.now() + Math.max(500, budget / 3);
    try { best = solve(root, Math.min(MAX_SPLIT, 3), Math.min(MAX_DEPTH, 2), true); } catch (e) { if (e !== TIMEOUT) throw e; }
    if (best && best.holes > 0 && DECOMP) {
      // each open subgoal with its own budget (HOLE_BUDGET), all of them within 2 x budget
      const until = performance.now() + 2 * budget;
      const acc = { holes: 0, closed: best.closed };
      const pf = fillHoles(best.pf, (g) => decompose(g, 0, until), acc);
      best = { pf, holes: acc.holes, closed: acc.closed };
      if (acc.holes === 0) { full = pf; tag("decomp"); }
    }
    // nothing closed: a split that the best lemmas ask for (their premise fits a hypothesis once a
    // parameter is a given constructor), with that arm decomposed on a full budget
    if (!full && DECOMP && (!best || best.closed === 0)) {
      const gs = guidedSplit(root, performance.now() + budget, budget);
      if (gs && gs.closed > 0) { best = gs; if (gs.holes === 0) full = gs.pf; }
    }
  }
  deadline = Infinity;
  const ms = performance.now() - t0;
  const tags = [...job.tags.keys()];
  if (full) {
    const out: string[] = [];
    render(full, "  ", out);
    const text = out.join("\n");
    const ok = attempt(FUEL_FINAL, () => { checkDef(k, text); return true; });
    if (ok) return { ok: true, text, partial: null, holes: 0, closed: 0, ms: performance.now() - t0, tags };
    if (DEBUG) {
      try { checkDef(k, text); } catch (e: any) { console.error("[gen2] final check failed for " + k + ":\n" + text + "\n" + errText(e)); }
    }
    why = "final check";
  }
  let partial: string | null = null;
  let partialBody: string | undefined;
  if (best && best.holes > 0) {
    const hs = holesOf(best.pf);
    // a hole that asks P -> P & B (B new facts from nothing: tot.wk's post left as Q(x) -> Q(x) & frame)
    // makes the skeleton a dead end: it is not shown as a partial (S1's tally: misleading)
    const deadEnd = (g: Goal): boolean => attempt(FUEL_NF, () => {
      let t = lower(g.ty, g.d);
      const doms = new Set<string>();
      for (let i = 0; i < 16 && t.$ === "All"; i++) { doms.add(key(t.A)); t = t.B as LTerm; }
      // the codomain as written: Pair(A, B) (Bend's A & B), or a Sigma
      const [h, xs] = unapply(t);
      let a: LTerm | undefined, b: LTerm | undefined;
      if (h.$ === "Ref" && shortOf(h.k) === "Pair" && xs.length >= 2) { a = xs[xs.length - 2]; b = xs[xs.length - 1]; }
      else if (t.$ === "ADT" && shortOf(t.k) === "Sigma" && t.x.length >= 4) { a = t.x[2]; const f = t.x[3]!; b = f.$ === "Lam" ? (f.f as LTerm) : f; }
      if (doms.size === 0 || !a || !b) return false;
      return (doms.has(key(a)) && !doms.has(key(b))) || (doms.has(key(b)) && !doms.has(key(a)));
    }) === true;
    if (hs.some(deadEnd)) {
      why = (why ? why + "; " : "") + "the best skeleton asks P -> P & (new facts) in a hole: a dead end, not shown";
      best = null;
    }
  }
  if (best && best.holes > 0) {
    const out: string[] = [];
    render(best.pf, "  ", out);
    if (best.closed > 0) partialBody = out.join("\n");
    const hs = holesOf(best.pf);
    const caution = (g: Goal) => (g.weak
      ? "  CAUTION: possible dead end: this hole is its goal with one argument changed (a monotonicity step such as K.Ok.wk), so it can be a STRONGER claim than the goal, and false; check that it is true before working on it (the theorem's statement is unchanged)\n" : "");
    partial = out.join("\n") + "\n" + hs.map((g, i) => "# hole " + (i + 1) + " at " + (g.path || "/") + "\n" + caution(g) + showGoal(g)).join("\n");
  }
  // for the agent: why the first open goal stays open, and proven defs to copy the shape of
  const g0 = (best && holesOf(best.pf)[0]) || introAll(root);
  const hints = MODE !== "bench" && g0 ? hintsFor(k, g0, true) : undefined;
  // --helpers: a skeleton (at least one step closed) with each hole a call of a new helper lemma (a
  // helper for the whole goal would only restate the def)
  let helpers: { body: string; defs: string[] } | undefined;
  if (HELPERS && best && best.holes > 0 && best.closed > 0) {
    const h = helperize(k, best.pf, new Set());
    const out: string[] = [];
    if (h.defs.length > 0 && attempt(FUEL_NF, () => { render(h.pf, "  ", out); return true; })) helpers = { body: out.join("\n"), defs: h.defs };
  }
  return { ok: false, text: null, partial, partialBody, hints, helpers, holes: best?.holes ?? 1, closed: best?.closed ?? 0, ms, tags, why };
};

// the goal of the hole ?gen2hole from bend2's error at it (null: the error is elsewhere, e.g. a
// mismatch before the hole, which must not be read as its goal)
const holeGoal = (k: string, err: any, path: string): Goal | null => {
  if (!err || err.$ !== "Err" || typeof err.exp === "string" || err.obs?.$ !== "Hol" || err.obs.k !== "gen2hole") return null;
  const arr = B.pmap_to_array(err.ctx as B.Ctx).sort((a, b) => a[0] - b[0]);
  const d = arr.length ? arr[arr.length - 1][0] + 1 : 0;
  const names: string[] = [];
  let env: B.Env = null;
  let ckey = "";
  for (let i = 0; i < d; i++) {
    const a = B.pmap_get(err.ctx as B.Ctx, i);
    names.push(a?.k ?? "_");
    env = B.list_set(env, i, B.Var(a?.k ?? "_", i));
    ckey += "|" + (a ? a.q.$[0] + a.k + ":" + (attempt(FUEL_NF, () => key(lower(a.T, i))) ?? "?") : "_");
  }
  return {
    ctx: err.ctx, d, ty: err.exp, lhs: { t: B.Ref(k), n: 0, def: k, qs: [], u: true }, qt: B.Lone(), env, names, ckey,
    pend: 0, pnames: [], pmany: [], split: true, path, lvl: 0, hc: new Map(),
  };
};
// ---- --wp: the Cir stepper (gen2_wp.ts) on a Tot goal ----
// The stepper's text is used only if bend2 checks it at the goal (its ?TODO leaves allowed); each leaf
// is then tried by the leaf tactics (a small budget), and the ones left are reported with their goal
// and the stepper's hint. Never throws.
// a routine law Tot(code_L, st_L, b_L, Q_L, H_L) instantiated at a call (code, st) of the goal g: its
// parameters fixed by matching code and st (raw, then the code's normal form), the others' types
// (premises: facts to find, or leaves), and b_L, Q_L, H_L
// the goal's environment, extended by the binders that --wp adds after the context (a matched state's
// fields, a page binder)
const envAt = (g: Goal, d: number): B.Env => { let e = g.env; for (let i = g.d; i < d; i++) e = B.list_set(e, i, B.Var("_", i)); return e; };
const wpInst = (g: Goal) => (law: string, code: LTerm, st: LTerm, b: LTerm, facts: { T: LTerm; pf: string }[], d: number) => attempt(FUEL_NF, () => {
  const t = RAW[law];
  if (t?.$ !== "Def") return null;
  const o = openMeta(t.T, t.n);
  if (!o) return null;
  const [, xs] = unapply(lower(o.concl, d));
  if (xs.length !== 5) return null;
  let sol: (LTerm | null)[] = new Array(t.n).fill(null);
  if (!match(xs[0]!, code, sol, d) || !match(xs[1]!, st, sol, d)) {
    sol = new Array(t.n).fill(null);
    const cn = nf(B.term_higher(code, envAt(g, d)), d);
    if (!match(xs[0]!, cn, sol, d) || !match(xs[1]!, st, sol, d)) return null;
  }
  // the law's budget as the goal's, when it matches (else tot.wk's premise b_L <= b stays)
  const sb = sol.slice();
  if (match(xs[2]!, b, sb, d)) sol = sb;
  return wpPrems(g, t, sol, facts, d);
}) ?? null;
// an equation law {lhs == ..} instantiated at a term (its parameters by the left side), as wpInst
const wpInstEq = (g: Goal) => (law: string, lhs: LTerm, facts: { T: LTerm; pf: string }[], d: number) => attempt(FUEL_NF, () => {
  const t = RAW[law];
  if (t?.$ !== "Def") return null;
  const o = openMeta(t.T, t.n);
  if (!o) return null;
  const c = lower(o.concl, d);
  if (c.$ !== "Eql") return null;
  const sol: (LTerm | null)[] = new Array(t.n).fill(null);
  return match(c.a, lhs, sol, d) ? wpPrems(g, t, sol, facts, d) : null;
}) ?? null;
// the equation laws (open ones too) by the head of their left side, "R:<def>": one pass over the book, on
// the first ask of --wp that needs it
let wpEqHeads: Map<string, string[]> | null = null;
const wpLawsOn = (head: string): string[] => {
  if (!wpEqHeads) {
    wpEqHeads = new Map();
    for (const k of Object.keys(RAW)) {
      const t = RAW[k];
      if (!t || t.$ !== "Def" || t.n === 0) continue;
      const c = attempt(FUEL_NF, () => { const o = openMeta(t.T, t.n); return o ? lower(o.concl, 0) : null; });
      if (!c || c.$ !== "Eql") continue;
      const hk = headKey(c.a);
      if (!hk.startsWith("R:")) continue;
      let a = wpEqHeads.get(hk);
      if (!a) wpEqHeads.set(hk, a = []);
      a.push(k);
    }
  }
  return wpEqHeads.get("R:" + head) ?? [];
};
// a law instantiated by its premises alone, once per fact that its first premise fits (at most max)
const wpInstPremAll = (g: Goal) => (law: string, facts: { T: LTerm; pf: string }[], d: number, max: number) => attempt(FUEL_NF, () => {
  const t = RAW[law];
  if (t?.$ !== "Def") return [];
  const o = openMeta(t.T, t.n);
  if (!o) return [];
  const j0 = o.doms.findIndex((dm) => isProp(dm.A));
  if (j0 < 0) return [];
  const P = lower(o.doms[j0]!.A, d);
  const out: NonNullable<ReturnType<typeof wpPrems>>[] = [];
  for (const f of facts) {
    if (out.length >= max) break;
    const sol: (LTerm | null)[] = new Array(t.n).fill(null);
    if (!match(P, f.T, sol, d)) continue;
    const r = wpPrems(g, t, sol, facts, d);
    if (r && r.sol.every((v, i) => v || r.pfs[i])) out.push(r);
  }
  return out;
}) ?? [];
// a law instantiated by its premises alone, as wpInst
const wpInstPrem = (g: Goal) => (law: string, facts: { T: LTerm; pf: string }[], d: number) => attempt(FUEL_NF, () => {
  const t = RAW[law];
  return t?.$ === "Def" ? wpPrems(g, t, new Array(t.n).fill(null), facts, d) : null;
}) ?? null;
// a law's premises: one that a fact of the context (or a conjunct of one) fits gives its parameters and its
// proof; the conclusion as instantiated
const wpPrems = (g: Goal, t: Extract<B.TLD, { $: "Def" }>, sol: (LTerm | null)[], facts: { T: LTerm; pf: string }[], d: number) => {
  const pfs: (string | null)[] = new Array(t.n).fill(null);
  for (let pass = 0; pass < 2; pass++) {
    const oi = openMeta(t.T, t.n, sol.map((x) => (x ? B.term_higher(x, envAt(g, d)) : null)));
    if (!oi) return null;
    oi.doms.forEach((dm, j) => {
      if (sol[j] || pfs[j] || !isProp(dm.A)) return;
      const P = attempt(FUEL_NF, () => lower(dm.A, d));
      if (!P) return;
      for (const f of facts) {
        const s2 = sol.slice();
        if (match(P, f.T, s2, d)) { for (let i = 0; i < sol.length; i++) sol[i] = s2[i] ?? null; pfs[j] = f.pf; return; }
      }
    });
  }
  const o2 = openMeta(t.T, t.n, sol.map((x) => (x ? B.term_higher(x, envAt(g, d)) : null)));
  if (!o2) return null;
  const T = lower(o2.concl, d);
  return {
    sol, pfs,
    doms: o2.doms.map((dm, j) => ({ k: dm.k, A: sol[j] ? null : attempt(FUEL_NF, () => lower(dm.A, d)) ?? null, fact: !sol[j] && isProp(dm.A) })),
    concl: unapply(T)[1], T,
  };
};
// verify: bend2's def check of k with the text in place (the error, or null); allowDst: a whole body
const wpGoal = (g: Goal, budget: number, verify: (t: string) => any, allowDst = false): { text: string; open: number; report: string } | null => {
  if (!WP) return null;
  const t0 = performance.now();
  // one stepping (dst: the proof matches the start state first), checked, its leaves tried
  const attemptWp = (dst: boolean, until: number): { text: string; open: number; report: string; why?: string; steps?: number } | null => {
    const r = wpProve({ RAW, show, lower, nf, wnf, attempt, key, deadline: performance.now() + (until - performance.now()) / 2, inst: wpInst(g), instEq: wpInstEq(g), instPrem: wpInstPrem(g), instPremAll: wpInstPremAll(g), lawsOn: wpLawsOn }, { ctx: g.ctx, d: g.d, ty: g.ty, names: g.names, self: job.k }, dst);
    if ("why" in r) return r.why === "not a Tot goal" ? null : { text: "", open: -1, report: "", why: r.why };
    const chk = verify;
    if (process.env.GEN2_WPDUMP) fs.writeFileSync(process.env.GEN2_WPDUMP + (dst ? ".dst" : ""), r.text);
    const e0 = chk(r.text);
    if (e0) return { text: "", open: -1, report: "", why: "the stepped proof does not check, so it is not used: " + (typeof e0 === "string" ? e0 : errText(e0).split("\n").slice(0, 8).join(" | ")).slice(0, 700) };
    let text = r.text;
    const report: string[] = [];
    let open = 0;
    for (let i = 0, pos = 0; i < r.leaves.length; i++) {
      const at = text.indexOf("?TODO", pos);
      if (at < 0) break;
      // past the budget: the leaf is reported with its hint only (each check of a large body costs ~1 s)
      const late = performance.now() > until;
      const marked = text.slice(0, at) + "?gen2hole" + text.slice(at + 5);
      const err = late ? null : chk(marked);
      const lg = typeof err === "object" ? holeGoal(job.k, err, "leaf" + (i + 1)) : null;
      let pf: Pf | null = null;
      if (lg && performance.now() < until) {
        deadline = Math.min(performance.now() + Math.max(100, budget / 8), until);
        try { for (let dd = 0; dd <= 2 && !pf; dd++) pf = leaf(lg, dd, dd === 0 ? 1 : MAX_RW, new Set()); } catch (x) { if (x !== TIMEOUT) throw x; }
        deadline = Infinity;
      }
      const fill = pf ? attempt(FUEL_NF, () => inline(pf!)) : undefined;
      if (fill !== undefined && chk(text.slice(0, at) + "(" + fill + ")" + text.slice(at + 5)) === null) {
        text = text.slice(0, at) + "(" + fill + ")" + text.slice(at + 5);
        pos = at + fill.length + 2;
        continue;
      }
      open++;
      const goal = lg ? attempt(FUEL_NF, () => show(lower(lg.ty, lg.d), lg.names)) ?? "?" : "?";
      report.push("# leaf " + open + " (the " + open + (open === 1 ? "st" : open === 2 ? "nd" : open === 3 ? "rd" : "th") + " ?TODO): " + r.leaves[i]!.hint + "\n#   goal: " + clipTo(goal, 400));
      pos = at + 5;
    }
    return { text, open, steps: r.steps, report: "# --wp: " + r.steps + " statements stepped, " + open + " leaf(s) open" + (dst ? " (the proof matches the start state)" : "") + ", " + Math.round(performance.now() - t0) + " ms" + (report.length ? "\n" + report.join("\n") : "") };
  };
  try {
    // the start state matched first, when it is a parameter: its accessors and facts compute, so it steps as
    // far as the plain run or further; the plain run when it cannot (its state is not a parameter, or its
    // text does not check)
    let w = allowDst ? attemptWp(true, t0 + budget * 0.75) : null;
    if (DEBUG && w) console.error("[gen2] --wp (the start state matched): " + (w.open < 0 ? w.why : w.report));
    if (!w || w.open < 0) {
      const w1 = attemptWp(false, t0 + budget);
      if (!w1) return null; // not a Tot goal
      if (!w || w1.open >= 0 || /not a parameter/.test(w.why ?? "")) w = w1;
    }
    if (!w) return null;
    if (w.open < 0) { console.error("[gen2] --wp: " + w.why); return null; }
    return w;
  } catch (e: any) {
    deadline = Infinity;
    if (e === TIMEOUT) return null;
    console.error("[gen2] --wp: internal: " + String(e?.message ?? e).slice(0, 200));
    return null;
  }
};
// the def check of k with a text placed in its body by place (the error, or null)
const wpVerify = (k: string, place: (t: string) => string) => (t: string): any => {
  const old = fuel;
  fuel = FUEL_FINAL;
  try { checkDef(k, place(t)); return null; } catch (e) { return e; } finally { fuel = old; }
};
// a whole body (?TODO) whose goal is a Tot: the stepped proof, printed as the body
const wpWhole = (k: string): number | null => {
  job = newJob(k);
  const g = introAll(rootGoal(k));
  const w = g ? wpGoal(g, BUDGET, wpVerify(k, (t) => t.split("\n").map((l) => "  " + l).join("\n")), true) : null;
  if (!w) return null;
  console.log(w.text.split("\n").map((l) => "  " + l).join("\n"));
  console.log(w.report);
  console.error("[gen2] " + shortOf(k) + ": --wp " + (w.open ? "partial, " + w.open + " leaf(s) open" : "proven"));
  return w.open;
};

// ---- --ind: induction schemes and helper lemmas (gen2_ind.ts) ----
// gen2_ind.ts sees gen2 through this object only. Temporary defs (helper lemmas while gen2 proves
// them) live in the book until dropTemps; a temp def enters the lemma index only with a proof body.
const temps: string[] = [];
let tempN = 0;
// a later temp gets a lower order (it is printed above, and is a lemma for the temps being proven)
const addTemp = (k: string, head: string, body: string, lemma: boolean, order?: number): string | null => {
  const file = sourceFiles.get(k), ds = defSrc(k);
  if (!file || !ds) return null;
  const n0 = book.order.length;
  try { B.parse_book(book, TOP, head + "\n" + body + "\n", file.ns, file.al); } catch { book.order.length = n0; return null; }
  const hk = book.order[n0];
  if (!hk || RAW[hk]?.$ !== "Def") { for (const x of book.order.slice(n0)) delete RAW[x]; book.order.length = n0; return null; }
  temps.push(hk);
  ORDER.set(hk, order ?? (ORDER.get(k) ?? n0) - 0.5 - (++tempN) * 1e-6);
  if (!lemma) tempOpen.add(hk);
  sourceFiles.set(hk, file);
  srcCache.set(hk, { file: ds.file, header: head, body, bodyLine: 0 });
  if (lemma) buildIndex();
  return hk;
};
const dropTemp = (hk: string) => {
  const i = temps.indexOf(hk);
  if (i < 0) return;
  temps.splice(i, 1);
  delete RAW[hk];
  const j = book.order.indexOf(hk);
  if (j >= 0) book.order.splice(j, 1);
  ORDER.delete(hk); sourceFiles.delete(hk); srcCache.delete(hk); strictMemo.delete(hk); matchedMemo.delete(hk); tempOpen.delete(hk);
};
const dropTemps = () => { const had = temps.length > 0; for (const hk of temps.slice()) dropTemp(hk); if (had) buildIndex(); };
// the whole-body search without its partial pass and decomposition: the proof text, or null
const proveQuick = (k: string, budget: number): string | null => {
  const d0 = DECOMP, p0 = PARTIAL, j0 = job, dl = deadline;
  DECOMP = false; PARTIAL = false;
  try { const o = proveDef(k, budget); return o.ok ? o.text : null; }
  catch (e) { if (e === TIMEOUT) return null; throw e; }
  finally { DECOMP = d0; PARTIAL = p0; job = j0; deadline = dl; }
};
// the leaf tactics (with the induction hypothesis of job k) on g within budget ms: a proof term, or null
const leafText = (k: string, g: Goal, budget: number): string | null => {
  const j0 = job, dl = deadline;
  job = newJob(k); job.ih = true;
  deadline = Math.min(dl, performance.now() + budget);
  try {
    let pf: Pf | null = null;
    for (let dd = 0; dd <= MAX_DEPTH && !pf; dd++) pf = leaf(g, dd, dd === 0 ? 1 : MAX_RW, new Set());
    return pf ? attempt(FUEL_NF, () => inline(pf!)) ?? null : null;
  } catch (e) { if (e === TIMEOUT) return null; throw e; }
  finally { job = j0; deadline = dl; }
};
// the def check of k with body (the error, or null)
const checkBody = (k: string, body: string): any => {
  const old = fuel;
  fuel = FUEL_FINAL;
  try { checkDef(k, body); return null; } catch (e) { return e ?? "error"; } finally { fuel = old; }
};
// the constructors of the datatype T at g (its type arguments filled): name, display name, field types (as
// text, the fields named by names)
const ctrFields = (g: Goal, T: HTerm, names: string[]): { k: string; show: string; types: string[] }[] | null => attempt(FUEL_NF, () => {
  const A = wnf(T);
  if (!A || A.$ !== "ADT") return null;
  const adt = B.book_adt(book, A, g.ctx, job.k);
  return adt.c.map((ctr) => {
    let cur = B.tele_fill(book, ctr.T, A.x, g.ctx, job.k);
    const types: string[] = [];
    for (let f = 0; f < ctr.n; f++) {
      const c = B.tele_head(book, cur, g.ctx, job.k);
      types.push(show(lower(c.A, g.d + f), [...g.names, ...names.slice(0, f)]));
      cur = c.B(B.Var(names[f] ?? "x" + f, g.d + f));
    }
    return { k: ctr.k, show: B.name_show(job.file, ctr.k), types };
  });
}) ?? null;
let indApiObj: any = null;
const indApi = (): any => indApiObj ??= {
  B, book, RAW, ORDER, show, lower, nf, wnf, key, attempt, unapply, blockers, strictOf, matchedOf, contradictory, hypTargets, usable, ann,
  tryText, holeGoal, rootGoal, introAll, intro, errText, defSrc, shortOf, fresh, reserved, helperName, isData,
  addTemp, dropTemp, dropTemps, proveQuick, leafText, checkBody, clipTo, ctrFields, stmtOk: (k: string) => stmtError(k) === null,
  FUEL_NF, FUEL_FINAL, TIMEOUT, META, matchT: match, openMeta, parseFrag,
  job: () => job, setJob: (j: Job) => { job = j; }, newJob, now: () => performance.now(),
  deadline: () => deadline, setDeadline: (t: number) => { deadline = t; },
  debug: () => DEBUG, budget: () => BUDGET, busy: () => SERVE && waiting > 1,
};
// a whole body that the search did not prove: the induction schemes of gen2_ind.ts; prints and returns
// the outcome when they prove it (a partial only if it closes more than o's), else null (o is printed)
const indWhole = (k: string, ds: Src, o: Outcome): { failed: boolean; body?: string; defs?: { head: string; body: string }[] } | null => {
  let r: ReturnType<typeof Ind.indProve> = null;
  const j0 = job;
  // a shared server answers one ask at a time: with asks waiting, the schemes get the budget only (no floor)
  try { r = Ind.indProve(indApi(), k, BUDGET, SERVE && waiting > 1 ? 0 : undefined); }
  catch (e: any) { console.error("[gen2] --ind: internal: " + String(e?.message ?? e).slice(0, 200)); r = null; }
  finally { dropTemps(); job = j0; deadline = Infinity; }
  if (!r) return null;
  if (r.open === 0) {
    if (r.helpers.length) console.log("# HELPERS (new, from gen2 --ind; each proven, and checked with the body below): paste them above `def " + shortOf(k) + "(`\n" + r.helpers.join("\n") + "\n# the body of " + shortOf(k) + ":");
    console.log(r.text);
    console.log(r.report);
    console.error("[gen2] " + shortOf(k) + ": proven by --ind in " + Math.round(r.ms) + " ms");
    if (WRITE) console.error(writeBack(k, ds, r.text, r.helpers));
    return { failed: false, body: r.text, defs: r.defs };
  }
  if (!PARTIAL || r.closed <= o.closed) return null;
  console.error("[gen2] " + shortOf(k) + ": no proof (" + Math.round(o.ms + r.ms) + " ms; --ind: a checked skeleton, " + r.open + " open)");
  console.log("# PARTIAL (--ind: " + r.open + " holes, " + r.closed + " subgoals closed; the skeleton checks): not a finished proof");
  if (r.helpers.length) console.log("# HELPERS it uses (new, proven):\n" + r.helpers.join("\n") + "\n# the body of " + shortOf(k) + ":");
  console.log(r.text);
  console.log(r.report);
  return { failed: true };
};

// prove the ?TODO holes of k's body, one by one (leaf tactics)
type HoleRes = { hole: number; ok: boolean; ms: number; text: string; partial?: string };
const proveHoles = (k: string, budget: number, log = true): { body: string; n: number; done: number; res: HoleRes[]; helpers: string[] } => {
  const res: HoleRes[] = [];
  const ds = defSrc(k)!;
  let body = ds.body;
  const n = (body.match(/\?TODO/g) ?? []).length;
  let done = 0, gone = 0; // gone: holes no longer ?TODO in body (filled, or a helper's call)
  const helpers: string[] = [], used = new Set<string>();
  for (let h = 0; h < n; h++) {
    if (ONLY_HOLE > 0 && h + 1 !== ONLY_HOLE) continue; // --hole N: that hole only (the others stay ?TODO)
    // find the next ?TODO not yet filled: mark it, read its goal from bend2's error
    let idx = -1;
    for (let c = 0, from = 0; c <= h - gone; c++) { idx = body.indexOf("?TODO", from); from = idx + 1; }
    const marked = body.slice(0, idx) + "?gen2hole" + body.slice(idx + 5);
    job = newJob(k);
    job.ih = true;
    let err: any = null;
    try { checkDef(k, marked); } catch (e) { err = e; }
    const g = holeGoal(k, err, "hole" + (h + 1));
    if (!g) {
      const why = "no goal (" + (err ? errText(err) : "checked") + ")";
      if (log) console.error("[gen2] hole " + (h + 1) + ": " + why);
      res.push({ hole: h + 1, ok: false, ms: 0, text: why });
      continue;
    }
    // --wp on a Tot hole alone on its line (its lets need a statement position)
    const ln = body.slice(body.lastIndexOf("\n", idx) + 1, idx);
    if (WP && /^\s*$/.test(ln) && /^[ \t]*(\n|$)/.test(body.slice(idx + 5))) {
      const w = wpGoal(g, budget, wpVerify(k, (t) => body.slice(0, idx) + t.split("\n").join("\n" + ln) + body.slice(idx + 5)), true);
      if (w) {
        body = body.slice(0, idx) + w.text.split("\n").join("\n" + ln) + body.slice(idx + 5);
        if (log) console.error("[gen2] hole " + (h + 1) + ": " + w.report);
        res.push({ hole: h + 1, ok: w.open === 0, ms: 0, text: w.report });
        gone += 1 - w.open;
        if (w.open === 0) done++;
        continue;
      }
    }
    const t0 = performance.now();
    deadline = t0 + budget;
    let pf: Pf | null = null;
    try {
      for (let dd = 0; dd <= MAX_DEPTH && !pf; dd++) pf = leaf(g, dd, dd === 0 ? 1 : MAX_RW, new Set());
    } catch (e) { if (e !== TIMEOUT) throw e; }
    deadline = Infinity;
    const ms = (performance.now() - t0).toFixed(0);
    if (!pf) {
      let partial = "";
      let dr: Res | null = null;
      if (DECOMP) {
        const r = dr = decompose(g, 0, performance.now() + budget);
        deadline = Infinity;
        if (r.closed > 0) {
          const out: string[] = [];
          render(r.pf, "", out);
          partial = "# PARTIAL (" + r.holes + " holes, " + r.closed + " subgoals closed): not a finished proof\n" + out.join("\n") + "\n" + holesOf(r.pf).map((hg, i) => "# subgoal " + (i + 1) + " at " + hg.path + "\n" + showGoal(hg)).join("\n");
        }
      }
      const text = "not found (" + ms + " ms)\n" + showGoal(g) + "\n" + hintsFor(k, g, false);
      if (log) console.error("[gen2] hole " + (h + 1) + ": " + text + (partial ? "\n" + partial : ""));
      res.push({ hole: h + 1, ok: false, ms: +ms, text, partial: partial || undefined });
      // --helpers: the hole (its decomposition if it closed a step) with each open goal a helper's call
      if (HELPERS) {
        const hz = helperize(k, dr && dr.closed > 0 ? dr.pf : { t: "hole", g }, used);
        if (hz.defs.length > 0) {
          const line = body.slice(body.lastIndexOf("\n", idx) + 1, idx);
          const ind = /^\s*$/.test(line) ? line : line.replace(/\S.*$/, "").replace(/$/, "  ");
          const out: string[] = [];
          if (attempt(FUEL_NF, () => { render(hz.pf, ind, out); return true; })) {
            body = body.slice(0, idx) + out.join("\n").slice(ind.length) + body.slice(idx + 5);
            helpers.push(...hz.defs);
            gone++;
            if (log) console.error("[gen2] hole " + (h + 1) + ": now " + hz.defs.length + " helper call(s)");
          }
        }
      }
      continue;
    }
    const line = body.slice(body.lastIndexOf("\n", idx) + 1, idx);
    const ind = /^\s*$/.test(line) ? line : line.replace(/\S.*$/, "").replace(/$/, "  ");
    const out: string[] = [];
    render(pf, ind, out);
    const text = out.join("\n").slice(ind.length);
    const nb = body.slice(0, idx) + text + body.slice(idx + 5);
    const ok = attempt(FUEL_FINAL, () => { checkDef(k, nb); return true; });
    if (!ok) {
      if (log) console.error("[gen2] hole " + (h + 1) + ": candidate failed the def check: " + flat(pf));
      res.push({ hole: h + 1, ok: false, ms: +ms, text: "candidate failed the def check: " + flat(pf) });
      continue;
    }
    body = nb;
    done++; gone++;
    if (log) console.error("[gen2] hole " + (h + 1) + ": filled (" + ms + " ms)");
    res.push({ hole: h + 1, ok: true, ms: +ms, text });
  }
  return { body, n: ONLY_HOLE > 0 ? Math.min(1, n) : n, done, res, helpers };
};

// ---- bench ----
// a proposition: an equation, Empty or Unit, a function to a proposition, or a stuck call of a def
// whose every case gives a proposition (Le(a, b) = T(..): Unit or Empty); a datatype with fields
// (Word(n), Nat, a state) is data, and its def is a function, not a lemma
const isPropType = (h: HTerm, n = 0): boolean => {
  if (n > 6) return false;
  const w = wnf(h);
  if (!w) return null;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": { const t = RAW[w.k]; return t?.$ === "ADT" && (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)); }
    case "All": return isPropType(w.B(B.Var("_", 1e7 + n)), n + 1);
    case "App": {
      const [hd] = B.term_unapply(w);
      const f = B.term_strip(hd);
      if (f.$ !== "Ref") return false;
      const t = RAW[f.k];
      if (t?.$ !== "Def" || t.v === null) return false;
      const leaves: HTerm[] = [];
      let budget = 64;
      const walk = (x: HTerm) => {
        if (--budget < 0) return;
        x = B.term_strip(x);
        if (x.$ === "Lam") { walk(x.f(B.Var("_", 1e7 + 50 + budget))); return; }
        if (x.$ === "Mat") { walk(x.h); walk(x.m); return; }
        if (x.$ === "Efq") return;
        leaves.push(x);
      };
      walk(t.v);
      return budget >= 0 && leaves.length > 0 && leaves.every((l) => isPropType(l, n + 1));
    }
    default: return false;
  }
};
const isLemma = (def: B.Def): boolean => {
  const o = attempt(20000, () => openMeta(def.T, def.n));
  return !!o && attempt(20000, () => isPropType(o.concl)) === true;
};
const bench = () => {
  const only = new RegExp(opt("only", ".*"));
  const max = +opt("max", "100000");
  const rows: any[] = [];
  const own = book.order.slice(N0).filter((k) => RAW[k]?.$ === "Def" && !(RAW[k] as B.Def).b);
  for (const k of own) {
    if (rows.length >= max) break;
    const def = RAW[k] as B.Def;
    if (!only.test(k) || def.v === null || def.x > 0 || def.i || !isLemma(def)) continue;
    const ds = defSrc(k);
    if (!ds || ds.body.includes("?TODO")) continue;
    const lines = ds.body.split("\n").filter((l) => l.trim() !== "" && !l.trim().startsWith("#")).length;
    RAW[k] = { ...def, v: null };
    let o: Outcome;
    try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
    // --ind: a miss gets the induction schemes too (its time added)
    if (IND && !o.ok) {
      RAW[k] = { ...def, v: null };
      const j0 = job;
      let r: ReturnType<typeof Ind.indProve> = null;
      try { r = Ind.indProve(indApi(), k, BUDGET); } catch (e: any) { if (e !== TIMEOUT) internal++; } finally { RAW[k] = def; dropTemps(); job = j0; deadline = Infinity; } // def back before the index is rebuilt
      if (r && r.open === 0) o = { ...o, ok: true, text: r.text, ms: o.ms + r.ms, tags: [...o.tags, "ind"] };
      else if (r) o = { ...o, ms: o.ms + r.ms };
    }
    const cls = lines <= 3 ? "S(1-3)" : lines <= 10 ? "M(4-10)" : "L(11+)";
    rows.push({ k, lines, cls, ok: o.ok, ms: Math.round(o.ms), tags: o.tags, holes: o.holes, closed: o.closed, why: o.why, proof: o.text, orig: ds.body });
    console.error((o.ok ? "OK  " : "--  ") + String(Math.round(o.ms)).padStart(6) + " ms  " + cls.padEnd(8) + " " + k + (o.ok ? "  [" + o.tags.join(" ") + "]" : o.why ? "  (" + o.why + ")" : ""));
  }
  const by = new Map<string, { n: number; ok: number; ms: number }>();
  for (const r of rows) { const b = by.get(r.cls) ?? { n: 0, ok: 0, ms: 0 }; b.n++; if (r.ok) b.ok++; b.ms += r.ms; by.set(r.cls, b); }
  const tot = rows.reduce((a, r) => a + r.ms, 0);
  const okn = rows.filter((r) => r.ok).length;
  console.log("file " + FILE + ": " + okn + "/" + rows.length + " re-proven, total " + (tot / 1000).toFixed(1) + " s" + (rows.length ? ", mean " + Math.round(tot / rows.length) + " ms" : "") + " (budget " + BUDGET + " ms; load " + Math.round(tLoad) + " ms, valid " + Math.round(tValid - tLoad) + " ms, index " + Math.round(tIndex) + " ms)");
  for (const c of ["S(1-3)", "M(4-10)", "L(11+)"]) { const b = by.get(c); if (b) console.log("  " + c.padEnd(8) + " " + b.ok + "/" + b.n + "  mean " + Math.round(b.ms / b.n) + " ms"); }
  const okMs = rows.filter((r) => r.ok).map((r) => r.ms).sort((a, b) => a - b);
  if (okMs.length) console.log("  hits: median " + okMs[okMs.length >> 1] + " ms, max " + okMs[okMs.length - 1] + " ms");
  const tg = new Map<string, number>();
  for (const r of rows) if (r.ok) for (const t of r.tags) tg.set(t, (tg.get(t) ?? 0) + 1);
  console.log("  tactics in hits: " + [...tg].sort((a, b) => b[1] - a[1]).map(([t, n]) => t + " " + n).join(", "));
  if (PARTIAL) {
    const fails = rows.filter((r) => !r.ok);
    console.log("  partial: " + fails.filter((r) => r.closed > 0).length + "/" + fails.length + " misses close some subgoal; " + fails.reduce((a, r) => a + r.closed, 0) + " subgoals closed, " + fails.reduce((a, r) => a + r.holes, 0) + " holes left");
  }
  if (internal) console.log("  internal errors: " + internal);
  const jf = opt("json", "");
  if (jf) fs.writeFileSync(jf, JSON.stringify(rows, null, 1));
};

// ---- batch ----
// every def of the book (not Base) with a ?TODO in its body: a whole ?TODO body is proven whole (splits),
// other holes one by one; writes DIR/report.txt (per hole: proof, or partial with its open subgoals)
// and DIR/gen2.patch (a unified diff, from the repository root, of proved bodies and,
// with --partial-patch, partial whole-body skeletons that still contain ?TODO)
const batch = () => {
  const only = new RegExp(opt("only", ".*"));
  const dir = path.resolve(opt("out", "gen2-out"));
  fs.mkdirSync(dir, { recursive: true });
  const todo = Object.keys(RAW).filter((k) => {
    const t = RAW[k];
    if (t.$ !== "Def" || t.b === true || !only.test(k)) return false;
    const ds = defSrc(k);
    return !!ds && /\?TODO/.test(ds.body);
  }).sort((a, b) => (ORDER.get(a) ?? 0) - (ORDER.get(b) ?? 0));
  const report: string[] = [];
  const newBody = new Map<string, string>();
  let holes = 0, proven = 0, partials = 0;
  const t0 = performance.now();
  for (const k of todo) {
    const ds = defSrc(k)!;
    const where = path.relative(TOP, ds.file) + ":" + (ds.bodyLine + 1);
    if (ds.body.trim() === "?TODO") {
      holes++;
      const def = RAW[k] as B.Def;
      RAW[k] = { ...def, v: null };
      let o: Outcome;
      try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
      if (o.ok) { proven++; newBody.set(k, o.text!); report.push("== " + shortOf(k) + " (" + where + "): PROVEN whole body in " + Math.round(o.ms) + " ms [" + o.tags.join(" ") + "]\n" + o.text); }
      else {
        if (o.partial) partials++;
        if (flag("partial-patch") && o.partialBody) {
          let err: any = null;
          try { checkDef(k, o.partialBody); } catch (e) { err = e; }
          if (!err || (err.$ === "Err" && typeof err.exp !== "string")) newBody.set(k, o.partialBody);
          else report.push("== " + shortOf(k) + ": partial skeleton failed the expected open-hole check: " + errText(err).slice(0, 2000));
        }
        report.push("== " + shortOf(k) + " (" + where + "): OPEN (" + Math.round(o.ms) + " ms)\n" + (o.partial ? "# PARTIAL (" + o.holes + " holes, " + o.closed + " subgoals closed): not a finished proof\n" + o.partial : "(no partial)"));
      }
      console.error("[gen2] " + (o.ok ? "PROVEN " : "open   ") + shortOf(k) + " (" + Math.round(o.ms) + " ms)");
      continue;
    }
    const r = proveHoles(k, BUDGET, false);
    holes += r.n;
    proven += r.done;
    if (r.done > 0) newBody.set(k, r.body);
    for (const h of r.res) {
      if (h.partial) partials++;
      report.push("== " + shortOf(k) + " (" + where + ") hole " + h.hole + ": " + (h.ok ? "PROVEN in " + h.ms + " ms\n" + h.text : "OPEN: " + h.text + (h.partial ? "\n" + h.partial : "")));
    }
    console.error("[gen2] " + r.done + "/" + r.n + " holes of " + shortOf(k));
  }
  // the patch: each file with its proven bodies replaced, diffed against the file
  let root = TOP;
  while (root !== "/" && !fs.existsSync(path.join(root, ".git"))) root = path.dirname(root);
  const byFile = new Map<string, [Src, string][]>();
  for (const [k, b] of newBody) { const ds = defSrc(k)!; if (!byFile.has(ds.file)) byFile.set(ds.file, []); byFile.get(ds.file)!.push([ds, b]); }
  let patch = "";
  for (const [file, edits] of byFile) {
    const lines = fileText(file).split("\n");
    edits.sort((a, b) => b[0].bodyLine - a[0].bodyLine);
    for (const [ds, b] of edits) lines.splice(ds.bodyLine, ds.body.split("\n").length, ...b.split("\n"));
    if (file === entry) for (const imp of autoImports) {
      if (!edits.some(([, body]) => body.includes(imp.alias + "."))) continue;
      const relative = path.relative(TOP, imp.file);
      const line = "import ./" + relative + " as " + imp.alias;
      if (!lines.includes(line)) lines.splice(lines.findLastIndex((l) => l.startsWith("import ")) + 1, 0, line);
    }
    const tmp = path.join(dir, "new-" + path.basename(file));
    fs.writeFileSync(tmp, lines.join("\n"));
    const rel = path.relative(root, file);
    const d = Bun.spawnSync(["diff", "-u", "--label", "a/" + rel, "--label", "b/" + rel, file, tmp]);
    patch += d.stdout.toString();
    fs.unlinkSync(tmp);
  }
  fs.writeFileSync(path.join(dir, "gen2.patch"), patch);
  const head = "gen2 batch " + FILE + ": " + proven + "/" + holes + " holes proven, " + partials + " partials, " + todo.length + " defs, " + ((performance.now() - t0) / 1000).toFixed(1) + " s (budget " + BUDGET + " ms per hole)";
  fs.writeFileSync(path.join(dir, "report.txt"), head + "\n\n" + report.join("\n\n") + "\n");
  console.log(head + "\nreport: " + path.join(dir, "report.txt") + "\npatch:  " + path.join(dir, "gen2.patch") + (flag("partial-patch") ? " (may contain open ?TODO goals)" : "") + " (apply from the repository root: git apply)");
};

// ---- queries: no search, answers from the loaded book (instead of grep over the files) ----
// --find RE: every def whose name (as the entry writes it, or its key) matches RE: its statement (in
// the entry's names), whether it is proven, and where it is. --lemmas: for the def's goal (a body that
// is ?TODO) or each ?TODO in its body, the lemmas and hypotheses whose conclusion matches the goal
// (as stated, stepped, or in normal form), each with what still blocks it; then the lemmas that share
// the goal's head but do not match, and the equations that can rewrite a call in the goal.
const MAX_FOUND = 40;
const statusOf = (k: string): string => {
  const t = RAW[k];
  if (t?.$ === "ADT") return "type";
  if (t?.$ !== "Def") return "?";
  if (t.v === null) return t.b ? "Base, no body" : "law: no body (a claim)";
  if (isOpen(k)) return "OPEN: has ?TODO";
  return t.b ? "Base" : "has a body";
};
const whereOf = (k: string): string => {
  const ds = defSrc(k);
  if (!ds) return nsOf(k) ? nsOf(k) + ".bend" : RAW[k]?.$ === "Def" && (RAW[k] as B.Def).b ? "base.bend" : "?";
  return path.relative(TOP, ds.file) + ":" + (defLine(ds.file, shortOf(k)) + 1);
};
const statementOf = (k: string, n = 600): string => {
  const t = RAW[k];
  if (!t) return "?";
  return clipTo(attempt(FUEL_NF, () => show(lower(t.T, 0), [])) ?? "?", n);
};
// k's conclusion over its parameters' names (a long parameter list is noise in a list of candidates)
const conclOf = (k: string, n = 300): string => {
  const t = RAW[k];
  if (t?.$ !== "Def") return statementOf(k, n);
  return clipTo(attempt(FUEL_NF, () => {
    const names: string[] = [];
    let T: HTerm = t.T;
    for (let j = 0; j < t.n; j++) { const s = B.term_strip(T); if (s.$ !== "All") break; names.push(s.k); T = s.B(B.Var(s.k, j)); }
    return "(" + names.length + " params) ... -> " + show(lower(T, names.length), names);
  }) ?? "?", n);
};
const runFind = (src: string) => {
  let re: RegExp;
  try { re = new RegExp(src); } catch (e: any) { console.log("# --find: not a regular expression: " + src); throw new Exit(1); }
  const hits: string[] = [];
  for (const k of new Set(book.order)) {
    if (k.includes("~") || !RAW[k]) continue;
    if (re.test(B.name_show(job.file, k)) || re.test(k)) hits.push(k);
  }
  // the entry's own defs first, then its imports (latest first), Base last
  const rank = (k: string) => ((ORDER.get(k) ?? 0) >= N0 ? 0 : (RAW[k] as B.Def).b ? 2 : 1);
  hits.sort((a, b) => rank(a) - rank(b) || (ORDER.get(b) ?? 0) - (ORDER.get(a) ?? 0));
  console.log("# --find " + src + ": " + hits.length + " defs" + (hits.length > MAX_FOUND ? " (the first " + MAX_FOUND + "; narrow the expression)" : ""));
  for (const k of hits.slice(0, MAX_FOUND)) console.log(B.name_show(job.file, k) + "  [" + statusOf(k) + "; " + whereOf(k) + "]\n  : " + statementOf(k, 1500));
  if (hits.length === 0) console.log("# (names match as the entry writes them, with an import's alias: U13.fs.zero; or as keys: moves_match:fs.zero)");
  // defs that match in .bend files the entry does not load (the entry's folder and its parent's): usable
  // only after an import, which the file's owner decides
  const loaded = new Set([...seen.keys()]);
  const out: string[] = [];
  const walk = (dir: string, depth: number) => {
    for (const ent of fs.readdirSync(dir, { withFileTypes: true })) {
      const f = path.join(dir, ent.name);
      if (ent.isDirectory() && depth > 0) walk(f, depth - 1);
      if (!ent.isFile() || !ent.name.endsWith(".bend") || loaded.has(fs.realpathSync(f))) continue;
      fileText(f).split("\n").forEach((l, i) => {
        const m = DEF_LINE.exec(l);
        if (m && out.length < 12 && re.test(m[1])) out.push("  " + m[1] + "  [" + path.relative(TOP, f) + ":" + (i + 1) + "]");
      });
    }
  };
  try { walk(path.resolve(TOP, ".."), 1); } catch (e) { /* an unreadable folder: no hint */ }
  if (out.length) console.log("# also in files the entry does not import (not usable without an import):\n" + out.join("\n"));
};
// the goals of k: its whole goal (parameters introduced) if its body is ?TODO, else each ?TODO's
const goalsOf = (k: string): { label: string; g: Goal }[] => {
  const ds = defSrc(k)!;
  if (ds.body.trim() === "?TODO") { job = newJob(k); const g = introAll(rootGoal(k)); return g ? [{ label: "the goal of " + shortOf(k), g }] : []; }
  const out: { label: string; g: Goal }[] = [];
  const n = (ds.body.match(/\?TODO/g) ?? []).length;
  for (let h = 0, from = 0; h < n; h++) {
    const idx = ds.body.indexOf("?TODO", from);
    from = idx + 1;
    if (ONLY_HOLE > 0 && h + 1 !== ONLY_HOLE) continue;
    job = newJob(k);
    let err: any = null;
    try { checkDef(k, ds.body.slice(0, idx) + "?gen2hole" + ds.body.slice(idx + 5)); } catch (e) { err = e; }
    const g = holeGoal(k, err, "hole" + (h + 1));
    const line = ds.bodyLine + ds.body.slice(0, idx).split("\n").length;
    out.push(...(g ? [{ label: "?TODO " + (h + 1) + " (line " + line + ")", g }] : []));
    if (!g) console.log("# ?TODO " + (h + 1) + " (line " + line + "): no goal: bend2 stops before it:\n" + (err ? errText(err) : "no error"));
  }
  return out;
};
const runLemmas = (k: string) => {
  const old = fuel;
  fuel = FUEL_FINAL;
  try {
    for (const { label, g } of goalsOf(k)) {
      console.log("# " + label + ": " + clipTo(attempt(FUEL_NF, () => show(lower(g.ty, g.d), g.names)) ?? "?", 600));
      const until = performance.now() + Math.max(500, BUDGET);
      const d0 = deadline;
      deadline = until;
      const lines: string[] = [];
      const near: string[] = [];
      try {
        const targets = targetsOf(g);
        lines.push(...matchLines(g, targets, [...hypCallees(g), ...rankedLemmas(g, targets)], 12).map((l) => "  " + l));
        near.push(...nearMisses(g, targets, new Set(lines.map((l) => l.trim().split(/[ :]/)[0]!)), 8).map((l) => "  " + l));
      } catch (e) { if (e !== TIMEOUT) throw e; } finally { deadline = d0; }
      // equations that rewrite a call that the goal (as stated, or its normal form) contains
      const rws: string[] = [];
      const heads = new Set<string>();
      for (const t of [lower(g.ty, g.d), attempt(FUEL_NF, () => nf(g.ty, g.d))]) if (t) { const m = new Map<string, LTerm>(); subterms(t, m); for (const s of m.values()) { const hk = headKey(s); if (hk.startsWith("R:")) heads.add(hk); } }
      for (const hk of heads) for (const { L, side } of rwIndex.get(hk) ?? []) {
        if (rws.length >= 8 || L.order >= job.order || L.k === job.k) continue;
        rws.push("  " + B.name_show(job.file, L.k) + " (" + (side === 0 ? "left to right" : "right to left") + ") : " + conclOf(L.k));
      }
      console.log(lines.length ? "# conclusion matches (" + lines.length + "; usable before " + shortOf(k) + "):\n" + lines.join("\n") : "# no lemma or hypothesis's conclusion matches it (as stated, stepped or in normal form)");
      if (near.length) console.log("# same head, no match (compare the arguments):\n" + near.join("\n"));
      if (rws.length) console.log("# equations on a call in the goal:\n" + rws.join("\n"));
    }
  } finally { fuel = old; }
};

// the def whose body holds line i of the entry (its key in the book)
const defOfLine = (i: number): string | null => {
  const lines = linesOf(entry);
  while (i >= 0 && !DEF_LINE.test(lines[i])) i--;
  if (i < 0) return null;
  const nm = DEF_LINE.exec(lines[i])![1];
  return [...new Set(book.order.slice(N0))].find((k) => RAW[k]?.$ === "Def" && defSrc(k) && defLine(entry, shortOf(k)) === i && (k === nm || shortOf(k) === nm || nm.endsWith("." + shortOf(k)))) ?? null;
};
// the entry's parse error with its fix (computed once per parse)
let parseFixed: { pe: object; text: string } | null = null;
const parseReport = (): string => {
  if (!parseErr) return "";
  if (parseFixed?.pe !== parseErr) parseFixed = { pe: parseErr, text: errText(parseErr.err) + "\n" + scrutFix(parseErr) };
  return "bend2 rejects the file (gen2 holds it with this block as ?TODO, so its other defs still work):\n" + parseFixed.text;
};

// ---- check: bend2's def check of the entry's defs in the loaded book (no bend2 process, no slot) ----
// each def (or each named one): its statement (stmtError), then its body as the file has it
// (checkDef); a ?TODO is counted, not an error (as bend2 --check-only). Not the gate: the kernel is.
const runCheck = (names: string[]) => {
  const own = [...new Set(book.order.slice(N0))].filter((k) => RAW[k]?.$ === "Def" && !k.includes("~"));
  const pick = names.length ? own.filter((k) => names.some((nm) => k === nm || shortOf(k) === nm || shortOf(k).endsWith("." + nm) || ("D." + shortOf(k)) === nm)) : own;
  let n = 0, bad = 0, todo = 0;
  const shownCtx = new Set<string>();
  const t0 = performance.now();
  const pk = parseErr && defOfLine(parseErr.blk.S);
  for (const k of pick) {
    const ds = defSrc(k);
    if (!ds) continue;
    n++;
    todo += (ds.body.match(/\?TODO/g) ?? []).length;
    let err: string | null = null;
    if (k === pk) err = parseReport();
    else {
      try {
        job = newJob(k);
        err = nsOf(k) === "" ? stmtError(k, shownCtx) : null;
        if (!err) {
          const old = fuel;
          fuel = FUEL_FINAL;
          try { checkDef(k, ds.body); } catch (e: any) { err = errText(e, flag("full-errors"), shownCtx); } finally { fuel = old; }
        } else err = "statement: " + err;
      } catch (e: any) {
        // gen2's own failure on this def (not bend2's verdict): an error, and the check goes on
        err = "gen2 could not check it: " + errText(e);
      }
    }
    if (err) { bad++; console.log("# ERROR in " + shortOf(k) + ":\n" + err); }
  }
  if (parseErr && !pick.includes(pk ?? "")) { bad++; console.log("# ERROR in " + path.basename(entry) + ":\n" + parseReport()); }
  console.log("# check " + path.basename(entry) + ": " + n + " defs, " + bad + " with errors, " + todo + " ?TODO (" + Math.round(performance.now() - t0) + " ms; bend2's checker in gen2's book; the gate stays the judge)");
  if (bad) throw new Exit(2);
};

// ---- prove ----
class Exit { constructor(readonly code: number) {} }
const runProve = () => {
  // the defs: the names after the file (options excluded), and with --only RE every def of the file
  // whose body is exactly ?TODO and whose name matches; the book is loaded once for all of them
  const names = argv.slice(2).filter((a, i, xs) => !a.startsWith("--") && !(i > 0 && xs[i - 1].startsWith("--") && !["--partial", "--stream", "--debug", "--whole", "--no-decomp", "--validate-book", "--fresh", "--helpers", "--write", "--check", "--lemmas", "--full-errors", "--wp", "--ind", "--no-ind"].includes(xs[i - 1])));
  if (flag("check")) { runCheck(names); return; }
  if (argv.includes("--find")) {
    job = newJob(book.order.slice(N0).find((k) => RAW[k]?.$ === "Def" && sourceFiles.has(k)) ?? book.order[book.order.length - 1]!);
    runFind(opt("find", ""));
    return;
  }
  if (parseErr) console.error("[gen2] " + path.basename(entry) + ": " + parseReport());
  const entryDefs = new Set(book.order.slice(N0));
  const own = (x: string) => entryDefs.has(x) && RAW[x].$ === "Def" && !(RAW[x] as B.Def).b;
  const ks: string[] = [];
  for (const nm of names) {
    const exact = Object.keys(RAW).filter((x) => own(x) && (shortOf(x) === nm || x === nm));
    const local = nm.includes(".") ? nm.slice(nm.indexOf(".") + 1) : nm;
    const suffix = exact.length ? [] : Object.keys(RAW).filter((x) => own(x) && (shortOf(x) === local || shortOf(x).endsWith("." + nm) || x.endsWith("." + nm)));
    const matches = exact.length ? exact : suffix;
    if (matches.length > 1) { console.error("gen2: ambiguous def " + nm + ": " + matches.map(shortOf).join(", ")); throw new Exit(1); }
    const k = matches[0];
    if (!k) { console.error("gen2: no def " + nm + " in " + FILE); { throw new Exit(1); }; }
    ks.push(k);
  }
  if (argv.includes("--only")) {
    const re = new RegExp(opt("only", ".*"));
    for (const k of book.order) if (own(k) && re.test(shortOf(k)) && !ks.includes(k) && defSrc(k)?.body.trim() === "?TODO") ks.push(k);
  }
  if (ks.length === 0) { console.error("gen2: no def to prove"); { throw new Exit(1); }; }
  if (flag("lemmas")) { for (const k of ks) { if (ks.length > 1) console.log("# " + shortOf(k)); runLemmas(k); } return; }
  let failed = 0;
  const optsKey = [BUDGET, MAX_SPLIT, MAX_DEPTH, MAX_RW, BEAM, FUEL_CHECK, HOLE_BUDGET, DECOMP, PARTIAL, STREAM, DEBUG, flag("whole"), HELPERS, ONLY_HOLE, IND, WP].join(",");
  for (const k of ks) {
    const ds = defSrc(k);
    if (!ds) { console.error("gen2: no source for " + k); failed++; continue; }
    if (ks.length > 1) console.log("# " + shortOf(k));
    const se = nsOf(k) === "" ? stmtError(k) : null;
    if (se) { console.log("# STATEMENT ERROR: the type of " + shortOf(k) + " does not check (no search; fix the statement):\n" + se); failed++; continue; }
    if (!SERVE) { failed += proveOne(k, ds).failed ? 1 : 0; continue; }
    const ak = k + "|" + optsKey + "|" + Bun.hash(linesOf(ds.file).slice(0, ds.bodyLine + ds.body.split("\n").length).join("\n"));
    const hit = flag("fresh") || WRITE ? undefined : lruGet(answers, ak);
    if (hit && (hit.body === undefined || recheck(k, hit.body, hit.defs))) {
      for (const [err, s] of hit.lines) (err ? console.error : console.log)(s);
      console.error("[gen2] " + shortOf(k) + ": cached answer (--fresh to search again)");
      if (hit.failed) failed++;
      continue;
    }
    const lines: [boolean, string][] = [];
    const ol = console.log, oe = console.error;
    console.log = (...a: any[]) => { lines.push([false, a.join(" ")]); ol(...a); };
    console.error = (...a: any[]) => { lines.push([true, a.join(" ")]); oe(...a); };
    let r: { failed: boolean; body?: string; defs?: { head: string; body: string }[] };
    try { r = proveOne(k, ds); } finally { console.log = ol; console.error = oe; }
    lruSet(answers, ak, { lines, ...r }, 2000);
    if (r.failed) failed++;
  }
  if (failed) throw new Exit(2);
};
// prove one def (its whole body, or the ?TODO holes in its body) and print the result; body: the
// proven body (no hole left), checked again before a cached answer is reused
const answers = new Map<string, { lines: [boolean, string][]; failed: boolean; body?: string; defs?: { head: string; body: string }[] }>();
// a cached proof checks again: its helpers (--ind) in the book as temps, each def-checked, then the body
const recheck = (k: string, body: string, defs?: { head: string; body: string }[]): boolean => {
  try {
    for (const d of defs ?? []) {
      const hk = addTemp(k, d.head, d.body, false);
      if (!hk || attempt(FUEL_FINAL, () => { checkDef(hk, d.body); return true; }) !== true) return false;
    }
    return attempt(FUEL_FINAL, () => { checkDef(k, body); return true; }) === true;
  } finally { dropTemps(); }
};
const proveOne = (k: string, ds: Src): { failed: boolean; body?: string; defs?: { head: string; body: string }[] } => {
  if (WP && ds.body.trim() === "?TODO") { const o = wpWhole(k); if (o !== null) return { failed: o > 0 }; }
  if (ds.body.trim() === "?TODO" || flag("whole")) {
    const def = RAW[k] as B.Def;
    RAW[k] = { ...def, v: null };
    let o: Outcome;
    try { o = proveDef(k, BUDGET); } finally { RAW[k] = def; }
    if (o.ok) {
      console.log(o.text);
      for (const imp of autoImports) if (o.text?.includes(imp.alias + ".")) console.error("[gen2] add import ./" + path.relative(TOP, imp.file) + " as " + imp.alias);
      console.error("[gen2] " + shortOf(k) + ": proven in " + Math.round(o.ms) + " ms [" + o.tags.join(" ") + "]");
      if (WRITE) console.error(writeBack(k, ds, o.text!, []));
      return { failed: false, body: o.text! };
    }
    if (IND) { const r = indWhole(k, ds, o); if (r) return r; }
    console.error("[gen2] " + shortOf(k) + ": no proof (" + Math.round(o.ms) + " ms" + (o.why ? ", " + o.why : "") + ")");
    console.log(o.partial ? "# PARTIAL (" + o.holes + " holes, " + o.closed + " subgoals closed): not a finished proof\n" + o.partial : "# NO PROOF");
    if (o.hints) console.log(o.hints);
    if (o.helpers) {
      console.log("# HELPERS: the skeleton with each hole a new lemma (statement = the hole's goal in its context); ask for each by name\n" + o.helpers.defs.join("\n") + "\n# the body of " + shortOf(k) + ":\n" + o.helpers.body);
      if (WRITE) console.error(writeBack(k, ds, o.helpers.body, o.helpers.defs));
    }
    return { failed: true };
  }
  const r = proveHoles(k, BUDGET);
  // the gate of every "done" claim: the whole body, as printed, through bend2's def check once more
  if (r.done > 0 && r.helpers.length === 0 && attempt(FUEL_FINAL, () => { checkDef(k, r.body); return true; }) !== true) {
    console.error("[gen2] " + shortOf(k) + ": the filled body fails bend2's def check: not printed (a gen2 bug; the holes stay open)");
    console.log(ds.body);
    return { failed: true };
  }
  if (r.helpers.length > 0) console.log("# HELPERS: each open hole as a new lemma (statement = the hole's goal in its context); ask for each by name\n" + r.helpers.join("\n") + "\n# the body of " + shortOf(k) + ":");
  console.log(r.body);
  console.error("[gen2] " + shortOf(k) + ": " + r.done + "/" + r.n + " holes filled" + (r.helpers.length ? ", " + r.helpers.length + " helper(s)" : ""));
  if (WRITE && r.body !== ds.body) console.error(writeBack(k, ds, r.body, r.helpers));
  return r.done < r.n ? { failed: true } : { failed: false, body: r.body };
};

// ---- serve: the book stays loaded between prove calls ----
// gen2.ts serve <file.bend> [--port 7311]; then `gen2.ts ask [--port N] <def> ... [options]` (the
// arguments of prove after the file). Before each call the entry is parsed again if its text changed:
// the text of the request (a shared ask: --file), else the entry file on disk; only its defs are
// re-parsed, on top of the loaded imports (an import that the text adds is loaded first).
const entryAl = (() => { for (const k of book.order.slice(N0)) { const f = sourceFiles.get(k); if (f) return f.al; } return {} as Record<string, string>; })();
let entryMtime = fs.statSync(entry).mtimeMs;
let entrySrc = entryText, srcFromReq = false;
// the text of the current shared ask (undefined: the file on disk), and what --write made of it
let reqText: string | undefined, pendingWrite: string | undefined;
const reloadEntry = (text?: string): string | null => {
  if (text === undefined) {
    const mt = fs.statSync(entry).mtimeMs;
    if (mt === entryMtime && !srcFromReq) return null;
    entryMtime = mt;
    text = fs.readFileSync(entry, "utf8");
  }
  if (text === entrySrc) { srcFromReq = reqText !== undefined; return null; }
  const t0 = performance.now();
  const lines = text.split("\n");
  for (let i = 0; i < lines.length; i++) { const l = lines[i].trim(); if (l === "" || l.startsWith("#")) continue; if (!/^import(\s|$)/.test(l)) break; lines[i] = ""; }
  const own = new Set(book.order.slice(N0));
  const oldHdr = new Map<string, string | undefined>();
  for (const k of own) oldHdr.set(k, defSrc(k)?.header);
  // an imported law that the entry fills (def D.alloc.post(..)) was filled in place and its key is in
  // the entry's order too: give the parser the law again, unfilled, or the fill is a duplicate name
  const imported = new Set(book.order.slice(0, N0));
  const ownCtrs = new Set<string>();
  for (const k of own) { const t = RAW[k]; if (t?.$ === "ADT") for (const c of t.c) ownCtrs.add(c.k); }
  const fresh = () => {
    const nb = B.book_nil();
    for (const k of Object.keys(RAW)) if (!own.has(k) && !k.includes("~")) nb.tlds[k] = RAW[k];
    for (const k of own) { const t = RAW[k]; if ((imported.has(k) || nsOf(k) !== "") && t?.$ === "Def") nb.tlds[k] = { ...t, v: null }; }
    for (const c of Object.keys(book.ctrs)) if (!ownCtrs.has(c)) nb.ctrs[c] = book.ctrs[c];
    nb.order = book.order.slice(0, N0);
    return nb;
  };
  // from here on the text is the source of the entry's defs (texts: also what --write edits)
  entrySrc = text; srcFromReq = reqText !== undefined;
  texts.set(entry, text); fileLines.delete(entry); defLines.delete(entry); srcCache.clear(); fileExists.clear();
  const nb = parseEntry(fresh(), lines.join("\n"), entryAl, fresh);
  if (flag("validate-book")) B.book_valid(nb, N0);
  for (const k of Object.keys(RAW)) delete RAW[k];
  Object.assign(RAW, nb.tlds);
  book.ctrs = nb.ctrs; book.order = nb.order; book.tmps = nb.tmps; book.hols = nb.hols;
  ORDER.clear(); book.order.forEach((k, i) => ORDER.set(k, i));
  sourceFiles.clear();
  openBySource.clear();
  for (const k of book.order) {
    const t = RAW[k];
    if (t?.$ === "Def") {
      const f = spanFile(t.v) ?? spanFile(t.T);
      if (f) sourceFiles.set(k, f);
    }
  }
  for (const k of book.order.slice(N0)) {
    const file = sourceFiles.get(k);
    if (file) for (const imp of autoImports) file.al[imp.alias] = imp.ns;
  }
  srcCache.clear(); fileExists.clear(); strictMemo.clear(); matchedMemo.clear(); tinfo.clear();
  buildIndex();
  // the statements that are new or changed (not law fills: their statement is the law's) must check
  const bad: string[] = [];
  for (const k of new Set(book.order.slice(N0))) {
    if (nsOf(k) !== "" || RAW[k]?.$ !== "Def" || oldHdr.get(k) === defSrc(k)?.header) continue;
    const e = stmtError(k);
    if (e) bad.push("[gen2] STATEMENT ERROR in " + shortOf(k) + " (its type does not check; fix it before asking):\n" + e);
  }
  return "[gen2] reloaded " + path.basename(entry) + " in " + Math.round(performance.now() - t0) + " ms" + (bad.length ? "\n" + bad.join("\n") : "");
};
// SHARED SERVERS: an import that the request's text adds is loaded into the book (after the other
// imports, before the entry's defs), with its alias; a removed import stays loaded (its alias still
// parses). Returns notes for the answer.
const IMPORT_LINE = /^import\s+(\S+)(?:\s+as\s+([A-Za-z_]\w*))?\s*(?:#.*)?$/;
const loadImports = async (text: string): Promise<string[]> => {
  const notes: string[] = [];
  for (const line of text.split("\n")) {
    const l = line.trim();
    if (l === "" || l.startsWith("#")) continue;
    if (!/^import(\s|$)/.test(l)) break;
    const m = IMPORT_LINE.exec(l);
    if (!m || !m[2] || !m[1].endsWith(".bend") || /^0x|@/.test(m[1])) continue;
    const got = path.resolve(TOP, m[1]);
    if (!fs.existsSync(got)) { notes.push("[gen2] the import " + m[1] + " does not exist in the server's tree"); continue; }
    const real = fs.realpathSync(got), ns = path.posix.relative(TOP, real).replace(/\.bend$/, "");
    if (entryAl[m[2]] === ns && seen.has(real)) continue;
    if (m[2] in entryAl && entryAl[m[2]] !== ns) { notes.push("[gen2] the alias " + m[2] + " names " + entryAl[m[2]] + " in the server's book, not " + ns + ": not loaded"); continue; }
    const n1 = book.order.length;
    await B.book_load(book, real, ns, seen, undefined, TOP);
    const added = book.order.slice(n1);
    book.order = [...book.order.slice(0, N0), ...added, ...book.order.slice(N0, n1)];
    N0 += added.length;
    ORDER.clear(); book.order.forEach((k, i) => ORDER.set(k, i));
    entryAl[m[2]] = ns;
    entrySrc = ""; // parse the entry again, on top of the new import
    notes.push("[gen2] loaded the new import " + m[1] + " as " + m[2] + " (" + added.length + " entries)");
  }
  return notes;
};
// the server's root (its worktree) and each loaded import's path in it, with a hash of the text that
// the server loaded; an ask from another worktree is told which of its imports differ (by stat; each
// result is kept 20 s per worktree, as the client's files are on /mnt/c)
const serverRoot = gitRoot(entry) ?? path.dirname(entry);
const importHash = new Map<string, number | bigint>();
const loadedImports = () => { for (const real of seen.keys()) if (real !== entry && !importHash.has(real) && real.startsWith(serverRoot + "/")) importHash.set(real, Bun.hash(fs.readFileSync(real, "utf8"))); };
loadedImports();
const statHash = new Map<string, { key: string; h: number | bigint }>();
const diffChecked = new Map<string, { at: number; notes: string[] }>();
const localPath = (p: string) => (process.platform !== "win32" && /^[A-Za-z]:\//.test(p) ? "/mnt/" + p[0].toLowerCase() + p.slice(2) : p);
const importDiffs = (clientRoot: string): string[] => {
  const root = localPath(clientRoot);
  const was = diffChecked.get(root);
  if (was && performance.now() - was.at < 20000) return was.notes;
  loadedImports();
  const notes: string[] = [];
  for (const [real, h] of importHash) {
    const rel = path.relative(serverRoot, real), f = path.join(root, rel);
    let st: fs.Stats | undefined;
    try { st = fs.statSync(f); } catch { notes.push(rel + " (missing in your worktree)"); continue; }
    const key = st.mtimeMs + ":" + st.size;
    let c = statHash.get(f);
    if (!c || c.key !== key) { c = { key, h: Bun.hash(fs.readFileSync(f, "utf8")) }; statHash.set(f, c); }
    if (c.h !== h) notes.push(rel);
  }
  diffChecked.set(root, { at: performance.now(), notes });
  return notes;
};
const entryRel = posix(path.relative(path.join(serverRoot, "src"), entry));
type Ask = { args: string[]; text?: string; rel?: string; root?: string };
let queue: Promise<unknown> = Promise.resolve(), waiting = 0;
const handle = async (body: Ask, tq: number, ahead: number) => {
  const out: string[] = [], err: string[] = [];
  const t0 = performance.now(), ticks0 = ticks;
  if (body.text !== undefined && body.rel !== entryRel)
    return { stdout: "", stderr: "[gen2] this server serves " + entryRel + ", not " + body.rel + " (one server per entry file)\n", code: 1 };
  const ol = console.log, oe = console.error;
  console.log = (...a: any[]) => { out.push(a.join(" ")); };
  console.error = (...a: any[]) => { err.push(a.join(" ")); };
  let code = 0;
  reqText = body.text; pendingWrite = undefined;
  try {
    if (body.text !== undefined) {
      for (const n of await loadImports(body.text)) err.push(n);
      const d = body.root ? importDiffs(body.root) : [];
      if (d.length) err.push("[gen2] NOTE: these imports differ between your worktree and the server's (answers use the server's copy; provers never edit imports: rebase on feature/redesign, or tell the orchestrator): " + d.join(", "));
    }
    const r = reloadEntry(body.text);
    if (r) err.push(r);
    argv.length = 0; argv.push("prove", FILE, ...body.args); readOpts();
    runProve();
  } catch (e: any) {
    if (e instanceof Exit) code = e.code;
    else { code = 1; err.push("[gen2] " + errText(e)); entryMtime = 0; entrySrc = ""; }
  } finally {
    console.log = ol; console.error = oe;
    deadline = Infinity;
  }
  err.push("[gen2] served in " + Math.round(performance.now() - t0) + " ms (" + (ticks - ticks0) + " def lookups" + (t0 - tq > 50 ? "; waited " + Math.round(t0 - tq) + " ms behind " + ahead + " ask(s)" : "") + ")");
  const write = pendingWrite;
  reqText = undefined; pendingWrite = undefined;
  // one line per ask in the server's log
  console.error("[ask] " + new Date().toISOString().slice(11, 19) + " " + (body.root ?? "(own file)") + " " + body.args.join(" ").slice(0, 120) + " -> " + code + ", " + Math.round(performance.now() - t0) + " ms" + (t0 - tq > 50 ? ", waited " + Math.round(t0 - tq) + " ms" : "") + (err.find((l) => l.startsWith("[gen2] reloaded"))?.replace(/^\[gen2\] reloaded \S+ in/, ", reload") ?? ""));
  return { stdout: out.length ? out.join("\n") + "\n" : "", stderr: err.join("\n") + "\n", code, ...(write !== undefined ? { write } : {}) };
};
const serve = () => {
  const port = +opt("port", "7311");
  Bun.serve({
    port, hostname: "127.0.0.1", idleTimeout: 0,
    async fetch(req) {
      const tq = performance.now();
      const body = (await req.json()) as Ask;
      // one ask at a time, in arrival order (the book is one shared state)
      const ahead = waiting++;
      const turn = queue.then(() => handle(body, tq, ahead));
      queue = turn.catch(() => {});
      try { return Response.json(await turn); } finally { waiting--; }
    },
  });
  console.error("[gen2] serving " + FILE + " on 127.0.0.1:" + port + " (book: " + book.order.length + " entries, load " + Math.round(tLoad) + " ms, valid " + Math.round(tValid - tLoad) + " ms); ask with: gen2.ts ask [--port " + port + "] <def> ... [options]");
};

// ---- main ----
if (validErr) { console.error(errText(validErr)); process.exit(1); }
if (MODE === "bench") {
  bench();
} else if (MODE === "batch") {
  batch();
} else if (MODE === "prove") {
  try { runProve(); } catch (e) { if (e instanceof Exit) process.exit(e.code); throw e; }
} else if (MODE === "serve") {
  serve();
} else {
  console.error("usage: bun gen2.ts prove <file.bend> <def> | batch <file.bend> | bench <file.bend> [options] (see the header)");
  process.exit(1);
}
