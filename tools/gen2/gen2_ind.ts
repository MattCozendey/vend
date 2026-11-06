// gen2_ind.ts: gen2's induction schemes and helper lemmas (--ind), a dev tool outside the trust like
// gen2.ts (copied from bend-bootstrap with it; see gen2.ts's ORIGIN). Every text it prints passed bend2's
// def check in gen2's book.
//
// WHAT (a whole body that gen2's own search did not prove; off unless --ind):
// * schemes: a skeleton TEXT with ?TODO arms, checked by bend2 (each arm's goal read from bend2's
//   error at a marked hole); each arm is closed by gen2's leaf tactics (with the induction
//   hypothesis), else by a helper lemma (below). Schemes, in order:
//   - enum: a Nat parameter bounded by a hypothesis {Nat.is_le(x, c) == True} (or is_lt), c <= 8:
//     every value and the rest (refuted by the hypothesis), jointly with the other parameters that
//     block the goal (a record such as Cir.Cell: its constructor);
//   - u32: the U32 parameters destructured (U32{w}); a goal over words of width 32n is the instance
//     at 32n of a helper over any width n (Equal.cong(Word(32n), U32, w => U32{w}, ..) for a U32
//     equation): the classic generalization before induction;
//   - word: a statement over n: Nat and words of width n: match n, then the words (WCon{h, t}),
//     then their head bits;
//   - nat: a Nat parameter that blocks the goal: 0n and 1n+p;
//   - fun: the case tree of a recursive def that the goal calls on parameters (functional
//     induction: List.get(xs, n) gives match xs n with its three cases);
//   - prem (pattern B): the premises of the conclusion (`-> {..} -> G`) introduced in each arm
//     (`+h => ?TODO`), alone, under a split on each enumeration parameter (Bool, Cmp) that a premise
//     or the conclusion blocks on, and under one joint split of all of them (prem:all);
//   - whole: the goal itself as one arm (its helpers are the point);
//   - rec: the record parameters (one constructor with fields) that a stuck call reads, opened (a
//     Root{p, d} that FileEp.decide matches); premises stay in the goal;
//   - blk: every parameter that the goal or a premise blocks on (enumerations, datatypes of at most 6
//     constructors) and every enumeration parameter, split jointly in parameter order.
//   rec and blk rank last: in the helper pass the best of them is tried after the two best schemes, so
//   a def that the others prove costs nothing more.
// * atoms step (the decide pattern; top level only): the stuck Bool/Cmp calls of an arm, on simple
//   arguments (FileEp.is_resource(rest)) or a whole side of a hypothesis (Cli.globs_read(Con{r, t})),
//   become parameters of a helper, each with its equation {g == call} (so the helper holds iff the arm
//   does); its hypotheses and goal are restated in folded normal form: bend2's weak normal form unfolds
//   wrapper defs (no match of their own) inside a stuck match, so each wrapper's pattern (its normal
//   form over metavariables) is folded back (refold). The atoms come first among the helper's
//   parameters (a later split on a context variable keeps binder order); blk then splits them.
// * arm split step: a variable that the goal, a hypothesis or a premise of a function goal blocks on,
//   also inside a constructor that a call matches (decide.here(Found{e, d}) reads e): `match v:` with
//   one ?TODO per constructor; then an intro step introduces a premise, alone on its line (a parameter
//   cannot be matched after a local statement, so splits come first).
// * leaf: a Bool clash in a hypothesis ({False == True}) closes any goal through Bool.pick as the motive.
// * pattern B step (hypGen): a hypothesis whose normal form holds a stuck call of an enumeration type
//   that is not a whole side of it (Expect.holds(e, k) inside Bool.when(..) == Done{s}) gives a helper
//   `(.., +g: Bool) -> {H[call := g]} -> G[call := g]`, proven by the schemes (prem), and the call
//   `helper(.., call)(h)` (variables named twice rebound above it when the hole is alone on its line).
// * a pair goal ({..} & {..}) becomes `(?TODO, ?TODO)`; clash and projection helpers take the type
//   variables of the equation (Result<.., A>) as erased parameters.
// * helpers for an arm that the leaf tactics do not close (depth <= MAX_DEPTH, each proven by the
//   same schemes before it is used; only proven helpers are printed): the arm's goal over its
//   context (true iff the arm is); the goal after the induction hypothesis rewrote it, with the
//   stuck calls common to both sides generalized to variables (U32.shrn(a, p) -> y); the goal with
//   those generalized directly. A generalization can be false: then its proof fails and nothing is
//   printed.
// * constructor steps for an arm (before the helpers; each leaves the arm's continuation as a new
//   ?TODO, worked on in further rounds): an equation of the context closed by a chain of at most two
//   equations (context facts, and instances of the induction hypothesis whose premises the context
//   gives: frame.fixed's seq); a clash C1{..} == C2{..} (a predicate helper); injectivity C{as} ==
//   C{bs} rewriting the goal's variable (a projection helper, Equal.cong); a goal variable equal to a
//   constructor value substituted; inversion of F(.., r, ..) == C{y} (r stuck; F any def that matches
//   r, e.g. Cir.exec.then, Cir.exec.if, Cir.exec.set): a helper in continuation style (bend2 destructures
//   only variables) for the one constructor of r that can give C, else a case split with one
//   continuation per constructor. Helpers print in dependency order (a def calls only defs above it).
// * leaf (inside gen2's search): a constructor clash in a hypothesis {None == Some{c}} closes any
//   goal, through a predicate def with type parameters (maybe.T(A, _)).
// * splits (inside gen2's search): a parameter of an enumeration type (Bool) that only a hypothesis
//   names is a split candidate (bool.case).
//
// BOUNDS: the caller's budget (each helper a slice), at most MAX_ARMS arms per skeleton, MAX_DEPTH
// nested helpers, MAX_HELPERS per def. Never throws past gen2's catch; an internal failure is one line.

import B from "./bend2.ts";

type HTerm = B.HTerm;
type LTerm = B.LTerm;

// ---- types ----
export type IndOut = { text: string; helpers: string[]; defs: { head: string; body: string }[]; open: number; closed: number; report: string; ms: number } | null;
type Api = any;
type Goal = any;
type Run = { A: Api; k: string; until: number; helpers: { order: number; text: string; head: string; body: string }[]; notes: string[]; used: Set<string>; nHelpers: number; failed: Set<string>; proven: Map<string, string>; cut: number; inverted: Set<string>; nFn: number };
type Fill = { body: string; open: number; closed: number; goals: string[] };
type Scheme = { name: string; body: string };

// ---- constants ----
const MAX_ARMS = 64;
const MAX_DEPTH = 3;
const MAX_HELPERS = 16;
const MAX_FN_HELPERS = 48; // written-out helpers (tests, projections, inversions) per def
const ENUM_MAX = 8;
const ARM_MS = 300;
const IND_FLOOR_MS = 2500; // the schemes get at least this (a def with helpers needs 0.5-2 s)
const MAX_HELPER_ARMS = 24;
const ROUNDS = 16; // leaf + step rounds after a constructor step left new holes // arms left after the leaf pass that may each get a helper
const NL = String.fromCharCode(10);
// which skeleton gets the helpers: the most specific split first (the functions' own recursion)
const SCHEME_RANK = ["enum", "u32+width", "word+split", "fun", "word", "nat", "u32", "prem:all", "prem", "whole", "rec", "blk"];
const ONLY = process.env.GEN2_IND_ONLY ? new RegExp(process.env.GEN2_IND_ONLY) : null; // debug: schemes by name

// ---- small helpers ----
const tele = (A: Api, k: string) => {
  // the parameters of def k: names, quantities, types (as text in k's file), and the conclusion's text
  const g0 = A.rootGoal(k);
  const g = A.introAll(g0);
  if (!g) return null;
  const ps: { name: string; q: string; ty: string; T: HTerm; i: number }[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = A.ann(g, i);
    const ty = A.attempt(A.FUEL_NF, () => A.show(A.lower(a.T, i), g.names.slice(0, i)));
    if (ty === undefined) return null;
    ps.push({ name: g.names[i], q: B.quant_show(a.q), ty, T: a.T, i });
  }
  return { g, ps };
};
const adtOf = (A: Api, g: Goal, T: HTerm): any => {
  const w = A.wnf(T);
  if (!w || w.$ !== "ADT") return null;
  const t = A.RAW[w.k];
  return t?.$ === "ADT" ? t : null;
};
const isWord = (ty: string) => /^Word\(/.test(ty);
const ctrPat = (A: Api, k: string, ctr: any, base: string, used: Set<string>): string => {
  const job = A.job();
  const cn = B.name_show(job.file, ctr.k);
  const fs: string[] = [];
  for (let i = 0; i < ctr.n; i++) fs.push(A.fresh(base + i, used));
  return cn + "{" + fs.join(", ") + "}";
};
const indent = (s: string, ind: string) => s.split("\n").map((l) => (l.trim() === "" ? l : ind + l)).join("\n");
// the cartesian product of case lists
const product = (xs: string[][]): string[][] => xs.reduce<string[][]>((acc, c) => acc.flatMap((a) => c.map((x) => [...a, x])), [[]]);
const matchText = (scruts: string[], cases: string[][], arm: (i: number) => string): string =>
  "match " + scruts.join(" ") + ":\n" + cases.map((c, i) => "  case " + c.join(" ") + ":\n" + indent(arm(i), "    ")).join("\n");
const freeVars = (t: LTerm, out: Set<number>) => {
  const st: LTerm[] = [t];
  while (st.length) {
    const x: any = st.pop();
    switch (x.$) {
      case "Var": if (x.i < (1 << 20)) out.add(x.i); break;
      case "App": st.push(x.f, x.x); break;
      case "Ctr": case "ADT": st.push(...x.x); break;
      case "Eql": st.push(x.a, x.b, x.T); break;
      case "All": st.push(x.A, x.B); break;
      case "Lam": st.push(x.f); break;
    }
  }
};

// t (a term at g) has an enumeration type: 2 to 4 constructors, none with fields (Bool, Cmp)
const enumTyped = (A: Api, g: Goal, t: LTerm): boolean => {
  const T = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, B.term_higher(t, g.env), B.None(), g.ctx, g.d).ty);
  const adt = T ? adtOf(A, g, T) : null;
  return !!adt && adt.c.length >= 2 && adt.c.length <= 4 && adt.c.every((c: any) => c.n === 0);
};

// ---- arms: fill the ?TODO of a skeleton ----
// the def check of k with body; for each ?TODO in order: its goal (the hole marked), the leaf tactics,
// then a helper; returns the body with the closed arms filled
const fillArms = (R: Run, k: string, body: string, depth: number, passes = [0, 1]): Fill | null => {
  const { A } = R;
  const e0 = A.checkBody(k, body);
  if (e0) { if (A.debug()) console.error("[gen2] --ind: skeleton of " + A.shortOf(k) + " does not check: " + A.errText(e0).split(NL).slice(0, 6).join(" | ")); return null; }
  const n = (body.match(/\?TODO/g) ?? []).length;
  if (n === 0) return { body, open: 0, closed: 0, goals: [] };
  if (n > MAX_ARMS) return null;
  let text = body, closed = 0;
  // pass 0: the leaf tactics on every arm; pass 1: a constructor step (a clash, injectivity, an inversion),
  // else a helper, for each arm left (when few are left); pass 2: the constructor step only. A step leaves a
  // new hole: the leaf pass and the step pass run again on it (at most ROUNDS times)
  let goals: string[] = [];
  const queue = passes.slice();
  let rounds = 0;
  while (queue.length) {
    const pass = queue.shift()!;
    const left = (text.match(/\?TODO/g) ?? []).length;
    if (left === 0 || (pass >= 1 && (depth >= MAX_DEPTH || left > MAX_HELPER_ARMS))) break;
    let stepped = false;
    goals = [];
    let pos = 0;
    for (let i = 0; i < left; i++) {
      if (A.busy && A.busy() && R.until > R.cut) R.until = R.cut; // others wait (shared server): the budget only
      const at = text.indexOf("?TODO", pos);
      if (at < 0) break;
      const err = A.checkBody(k, text.slice(0, at) + "?gen2hole" + text.slice(at + 5));
      const g = typeof err === "object" ? A.holeGoal(k, err, "ind" + (i + 1)) : null;
      let fill: string | null = null;
      // a fill checks at the hole's goal; one that calls k itself (the induction hypothesis: its descent is
      // checked only by the def check) checks in the whole body; the body is checked whole at the end
      const self = new RegExp("(?<![\\w.])" + B.name_show(A.job().file, k).replace(/\./g, "\\.") + "\\(");
      // a fill that the hole's own check refuses may still check in the whole body (a rebinding above the
      // hole, such as the whole+copy skeleton's `+k = k`, is not in the hole's context): try that too
      const whole = (f: string) => {
        const e = A.checkBody(k, text.slice(0, at) + f + text.slice(at + 5));
        if (e && A.debug()) console.error("[gen2] --ind: in the whole body: " + A.errText(e).split(NL).slice(0, 8).join(" | ").slice(0, 600));
        return e === null;
      };
      const fits = (f: string | null): f is string => f !== null && (g && !self.test(f) ? A.tryText(g, f) || whole(f) : whole(f));
      if (g && A.now() < R.until) {
        // the leaf tactics get a share of the time left (many arms: less each, so the steps still run)
        if (pass === 0) fill = A.leafText(k, g, Math.min(ARM_MS, Math.max(40, (R.until - A.now()) / (4 * left))));
        else {
          // a step needs the hole alone on its line (a statement position)
          const ls = text.lastIndexOf("\n", at) + 1, ind = text.slice(ls, at), alone = /^\s*$/.test(ind) && /^[ \t]*(\n|$)/.test(text.slice(at + 5));
          const caseAt = text.lastIndexOf("case ", at), arm = caseAt >= 0 ? text.slice(caseAt, text.indexOf(":", caseAt)) : "";
          // pattern B first when the hole is alone on its line (a call that names a variable twice can rebind
          // it above), else after the constructor steps
          const hyp = () => (depth < MAX_DEPTH ? A.attempt(A.FUEL_NF * 4, () => hypGen(R, k, g, depth, alone ? ind : "", fits)) ?? null : null);
          const hg0 = alone ? hyp() : null;
          // the decide pattern: the stuck Bool/Cmp calls of the arm as parameters of a helper, before a
          // constructor step splits a pair goal apart from the hypothesis that decides it
          const ag = hg0 || pass !== 1 ? null : A.attempt(A.FUEL_NF * 8, () => atomGen(R, k, g, depth, alone ? ind : "", fits)) ?? null;
          // a variable that the goal or a hypothesis blocks on: split it before a constructor step takes a
          // pair goal apart from the hypothesis that decides it
          const sp = hg0 || ag || pass !== 1 || !alone ? null : A.attempt(A.FUEL_NF * 4, () => armSplit(R, k, g, ind, fits)) ?? null;
          const it = hg0 || ag || sp || pass !== 1 || !alone ? null : A.attempt(A.FUEL_NF, () => introStep(R, g, ind, fits)) ?? null;
          const st = hg0 || ag || sp || it ? null : A.attempt(A.FUEL_NF * 4, () => ctorStep(R, k, g, alone ? ind : "", arm, fits)) ?? null;
          if (hg0 && fits(hg0)) fill = hg0;
          else if (ag) fill = ag;
          else if (sp) { fill = sp; stepped = true; }
          else if (it) { fill = it; stepped = true; }
          else if (st && fits(st)) { fill = st; if (st.includes("?TODO")) stepped = true; }
          else {
            const hg = alone ? null : hyp();
            if (hg && fits(hg)) fill = hg;
            else if (pass === 1) fill = armHelper(R, k, g, depth, fits, alone ? ind : null);
          }
        }
        if (!fits(fill)) fill = null;
      }
      if (pass >= 1 && A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " arm " + (i + 1) + ": " + (g ? (fill ? "closed" : "open") : "no goal: " + (err ? A.errText(err).split(NL).slice(0, 3).join(" | ") : "checks")));
      if (fill !== null) {
        text = text.slice(0, at) + fill + text.slice(at + 5);
        pos = at + (fill.includes("?TODO") ? fill.lastIndexOf("?TODO") + 5 : fill.length);
        if (!fill.includes("?TODO")) closed++;
        continue;
      }
      goals.push(g ? A.attempt(A.FUEL_NF, () => A.show(A.lower(g.ty, g.d), g.names)) ?? "?" : "?");
      pos = at + 5;
    }
    if (stepped && rounds++ < ROUNDS && A.now() < R.until) queue.unshift(0, pass);
  }
  return { body: text, open: (text.match(/\?TODO/g) ?? []).length, closed, goals };
};

// ---- helpers ----
// prove a new lemma (head: its `def name(..) -> concl:` text) for k's file: gen2's search, then the
// schemes; on success it stays in the book as a lemma and its text is kept for the output
const proveHelper = (R: Run, head: string, depth: number): string | null => {
  const { A } = R;
  const stmt = head.replace(/^def\s+[A-Za-z0-9_.]+\(/, "(");
  if (R.failed.has(stmt)) return null;
  const had = R.proven.get(stmt);
  if (had) return had;
  if (R.nHelpers >= MAX_HELPERS || A.now() > R.until) return null;
  const name = /^def\s+([A-Za-z0-9_.]+)\(/.exec(head)?.[1];
  if (!name) return null;
  const hk = A.addTemp(R.k, head, "  ?TODO", false);
  if (A.debug()) console.error("[gen2] --ind: helper " + (hk ? "" : "(does not parse) ") + head.replace(/\s+/g, " ").slice(0, 3000));
  if (!hk) return null;
  const order = A.ORDER.get(hk);
  if (A.attempt(A.FUEL_FINAL, () => A.stmtOk(hk)) !== true) { if (A.debug()) console.error("[gen2] --ind: its statement does not check"); A.dropTemp(hk); return null; }
  let body: string | null = null;
  const until0 = R.until;
  try {
    const rem = R.until - A.now();
    body = A.proveQuick(hk, Math.max(150, Math.min(A.budget() / 4, rem / 4)));
    if (!body) {
      R.until = A.now() + Math.max(200, (R.until - A.now()) / 2);
      const r = schemesProve(R, hk, depth + 1);
      if (r && r.open === 0) body = r.body;
    }
  } finally { A.dropTemp(hk); R.until = Math.min(until0, A.busy && A.busy() ? R.cut : Infinity); }
  if (!body) { R.failed.add(stmt); return null; }
  const hk2 = A.addTemp(R.k, head, body, true, order);
  if (!hk2 || A.checkBody(hk2, body) !== null) { if (hk2) A.dropTemp(hk2); return null; }
  R.nHelpers++;
  R.proven.set(stmt, name);
  R.helpers.push({ order, text: "# gen2 --ind: a helper lemma (proven)\n" + head + "\n" + body + "\n", head, body });
  return name;
};
const newName = (R: Run): string => R.A.helperName(R.k, R.used, "i");
// a statement over the context of g: the parameters that the goal (or a kept parameter's type) names
const ctxParams = (A: Api, g: Goal, goalT: LTerm, rename: (s: string) => string, skip: Set<number> = new Set()): { params: string[]; args: string[] } | null => {
  const need = new Set<number>();
  freeVars(goalT, need);
  for (let i = g.d - 1; i >= 0; i--) if (need.has(i)) { const a = A.ann(g, i); freeVars(A.lower(a.T, i), need); }
  // the facts (equations) of the context over those parameters stay premises (the statement is no stronger)
  for (let i = 0; i < g.d; i++) {
    if (need.has(i) || skip.has(i)) continue;
    const T = A.attempt(A.FUEL_NF, () => A.lower(A.ann(g, i).T, i));
    if (!T || T.$ !== "Eql") continue;
    const fv = new Set<number>();
    freeVars(T, fv);
    if ([...fv].every((v) => need.has(v))) need.add(i);
  }
  const names = g.names.slice(0, g.d);
  if (new Set(names).size !== names.length) return null;
  const params: string[] = [], args: string[] = [];
  for (let i = 0; i < g.d; i++) {
    if (!need.has(i) || skip.has(i)) continue;
    const a = A.ann(g, i);
    const T = A.attempt(A.FUEL_NF, () => A.show(A.lower(a.T, i), names.slice(0, i)));
    if (T === undefined || names[i] === "_") return null;
    params.push(B.quant_show(a.q) + names[i] + ": " + rename(T));
    args.push(names[i]);
  }
  return { params, args };
};
// an arm the leaf tactics did not close: a helper (its goal rewritten by the induction hypothesis,
// with the common stuck calls generalized; generalized directly; the arm's goal over its context)
const armHelper = (R: Run, k: string, g: Goal, depth: number, fits: (f: string | null) => boolean, ind: string | null = null): string | null => {
  const { A } = R;
  const raw = A.attempt(A.FUEL_NF, () => A.lower(g.ty, g.d));
  if (!raw || A.attempt(A.FUEL_NF, () => hasMetaOrHole(raw)) !== false) return null;
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(g.ty, g.d));
  const left = () => Math.min(ARM_MS, R.until - A.now());
  if (R.nHelpers > 0) { const lf = A.leafText(k, g, left()); if (fits(lf)) return lf; }
  // a call that the hole takes; a generalized call names a variable twice (k, and k inside
  // Expect.holds(e, k)), but a parameter is affine: with the hole alone on its line, rebind those
  // variables as reusable just above the call
  const tryCall = (text: string): string | null => {
    if (fits(text)) return text;
    if (ind === null) return null;
    const twice = g.names.filter((v: string) => v !== "_" && (text.match(new RegExp("(?<![\\w.])" + v.replace(/\./g, "\\.") + "(?![\\w.{])", "g")) ?? []).length > 1);
    const copied = twice.length ? twice.map((v: string) => "+" + v + " = " + v + NL + ind).join("") + text : null;
    return copied && fits(copied) ? copied : null;
  };
  const cands: { t: LTerm; rw?: IhRw }[] = [];
  if (N && N.$ === "Eql") {
    for (const [dir, useNf] of [[0, false], [1, false], [0, true], [1, true]] as [number, boolean][]) {
      const rw = A.attempt(A.FUEL_NF * 2, () => ihRewrite(A, k, g, N, dir, useNf));
      if (!rw) continue;
      // the rewritten goal is closed by computation
      const t = rw.t as any;
      if (t.$ === "Eql" && A.key(t.a) === A.key(t.b)) { const txt = "(%" + rw.e + " : " + rw.P + "; {==})"; if (fits(txt)) return txt; if (A.debug()) console.error("[gen2] --ind: the closed rewrite does not check: " + txt.slice(0, 400)); }
      cands.push({ t: rw.t, rw });
    }
    cands.push({ t: N });
    const seen = new Set<string>();
    for (const [c, enums] of cands.flatMap((c) => (c.rw ? [[c, false], [c, true]] : [[c, true], [c, false]]) as [{ t: LTerm; rw?: IhRw }, boolean][])) {
      if (A.now() > R.until) return null;
      const gen = A.attempt(A.FUEL_NF * 2, () => generalize(A, g, c.t, enums));
      if (A.debug()) console.error("[gen2] --ind: arm " + g.path + (c.rw ? " (IH rewritten)" : "") + (enums ? " enums" : "") + ": " + (gen ? gen.goal.slice(0, 200) : "no generalization"));
      if (!gen || seen.has(gen.goal)) continue;
      seen.add(gen.goal);
      const nm = proveHelper(R, "def " + newName(R) + "(" + gen.params.join(", ") + ") ->" + NL + "  " + gen.goal + ":", depth);
      if (!nm) continue;
      const call = nm + "(" + gen.args.join(", ") + ")";
      const text = c.rw ? "(%" + c.rw.e + " : " + c.rw.P + "; " + call + ")" : call;
      const took = tryCall(text);
      if (took) return took;
      if (A.debug()) console.error("[gen2] --ind: the arm does not take " + text.slice(0, 300));
      // the helper is a lemma now: the leaf tactics again (a rewrite by the IH, then the helper)
      const lf = A.leafText(k, g, left());
      if (fits(lf)) return lf;
    }
  }
  // the arm's goal over its context (true iff the arm is), when no instance of the induction
  // hypothesis occurs in it (another induction may prove it)
  const cp = ctxParams(A, g, raw, (s) => s);
  // as stated, or its normal form when shorter (the bits that a shift drops are gone)
  const goalText = A.attempt(A.FUEL_NF, () => { const a = A.show(raw, g.names), b = N ? A.show(N, g.names) : a; return b.length < a.length ? b : a; });
  if (cp && goalText !== undefined && cp.params.length > 0 && depth + 1 < MAX_DEPTH && cands.length <= 1) {
    const nm = proveHelper(R, "def " + newName(R) + "(" + cp.params.join(", ") + ") ->" + NL + "  " + goalText + ":", depth);
    if (nm) {
      const call = nm + "(" + cp.args.join(", ") + ")";
      if (fits(call)) return call;
    }
  }
  return null;
};
// N (an equation) with each instance of one side of k's conclusion (the induction hypothesis) replaced
// by the other side (dir 0: left to right); null if none occurs
type IhRw = { t: LTerm; P: string; e: string };
const ihRewrite = (A: Api, k: string, g: Goal, N: any, dir: number, useNf = false): IhRw | null => {
  const def = A.RAW[k];
  const o = A.openMeta(def.T, def.n);
  if (!o) return null;
  const c = A.lower(o.concl, 0);
  if (c.$ !== "Eql") return null;
  // the sides as stated, or their normal forms (St.nregs(St0(n, ..)) is List.length(List.replicate(..)))
  const cn = useNf ? A.nf(o.concl, 0) : c;
  if (A.debug() && useNf) console.error("[gen2] --ind: IH normal form " + A.show(cn, []).slice(0, 200));
  if (cn.$ !== "Eql" || (useNf && A.key(cn) === A.key(c))) return null;
  const [from, to] = dir === 0 ? [cn.a, cn.b] : [cn.b, cn.a];
  if (from.$ === "Var") return null;
  // the arm's own instance of k's parameters (its columns), from the goal as stated; an instance of the
  // hypothesis must descend: live parameters equal, left to right, until one is a strict subterm
  const raw = A.lower(g.ty, g.d);
  const cols: (LTerm | null)[] = new Array(def.n).fill(null);
  if (!A.matchT(c, raw, cols, g.d)) { if (A.debug()) console.error("[gen2] --ind: no columns for " + A.show(raw, g.names).slice(0, 200)); return null; }
  if (A.debug()) console.error("[gen2] --ind: columns " + cols.map((x) => (x ? A.show(x, g.names) + "/" + x.$ : "-")).join(", ").slice(0, 300));
  const live = o.doms.map((d: any) => d.q.$ !== "None");
  const sub = (a: LTerm, b: LTerm): boolean => strictSub(A, A.key(a), b);
  const descends = (sol: (LTerm | null)[]): boolean => {
    for (let j = 0; j < def.n; j++) {
      if (!live[j]) continue;
      const a = sol[j], b = cols[j];
      if (!a || !b) return false;
      if (A.key(a) === A.key(b)) continue;
      return sub(a, b) || (b.$ === "Lit" && b.k === "Nat" && a.$ === "Lit" && a.k === "Nat" && a.v < b.v);
    }
    return false;
  };
  let hit: { key: string; to: LTerm; sol: (LTerm | null)[] } | null = null;
  const inst = (t: LTerm, sol: (LTerm | null)[]): LTerm => {
    switch (t.$) {
      case "Var": return t.i >= A.META ? (sol[t.i - A.META] ?? t) : t;
      case "App": return { ...t, f: inst(t.f, sol), x: inst(t.x, sol) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map((x: LTerm) => inst(x, sol)) } as LTerm;
      case "Eql": return { ...t, a: inst(t.a, sol), b: inst(t.b, sol), T: inst(t.T, sol) } as LTerm;
      default: return t;
    }
  };
  // the first instance found is rewritten at each of its occurrences (one rewrite)
  const go = (t: LTerm, hole: boolean): LTerm => {
    if (hit && A.key(t) === hit.key) return hole ? (B.Ref("_") as LTerm) : hit.to;
    const sol: (LTerm | null)[] = new Array(def.n).fill(null);
    // a parameter that the side does not name stays the arm's own
    // a premise (a hypothesis of k) is the context's hypothesis of the same normal form
    const full = () => {
      for (let j = 0; j < sol.length; j++) {
        if (sol[j]) continue;
        const pA = A.attempt(A.FUEL_NF, () => { const T = inst(A.lower(o.doms[j].A, 0), sol); return hasMetaOrHole(T) ? null : A.key(A.nf(B.term_higher(T, g.env), g.d)); });
        if (pA) for (let i = g.d - 1; i >= 0 && !sol[j]; i--) {
          const a = A.ann(g, i);
          if (!a || g.names[i] === "_") continue;
          if (A.attempt(A.FUEL_NF, () => A.key(A.nf(a.T, g.d))) === pA) sol[j] = B.Var(g.names[i], i) as LTerm;
        }
        sol[j] ??= cols[j];
      }
      return true;
    };
    if (!hit && t.$ !== "Var" && A.matchT(from, t, sol, g.d) && full() && descends(sol) && sol.every((x) => x)) {
      const r = inst(to, sol);
      if (!A.attempt(A.FUEL_NF, () => hasMetaOrHole(r))) { hit = { key: A.key(t), to: r, sol }; return hole ? (B.Ref("_") as LTerm) : r; }
    }
    switch (t.$) {
      case "App": return { ...t, f: go(t.f, hole), x: go(t.x, hole) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map((x: LTerm) => go(x, hole)) } as LTerm;
      default: return t;
    }
  };
  const r = { ...N, a: go(N.a, false), b: go(N.b, false) } as LTerm;
  if (!hit) return null;
  const P = { ...N, a: go(N.a, true), b: go(N.b, true) } as LTerm;
  const h = hit as { key: string; to: LTerm; sol: (LTerm | null)[] };
  const call = B.name_show(A.job().file, k) + "(" + h.sol.map((x) => A.show(x!, g.names)).join(", ") + ")";
  const L = inst(c.a, h.sol), Rr = inst(c.b, h.sol);
  // (%e : P; t) has type P[b] for t : P[a] (e : {a == b}): P[b] is the goal, P[a] the rewritten goal
  const e = dir === 0 ? "Equal.sym(" + A.show(inst(c.T, h.sol), g.names) + ", " + A.show(L, g.names) + ", " + A.show(Rr, g.names) + ", " + call + ")" : call;
  return { t: r, P: A.show(P, g.names), e };
};
// a term whose key is ka occurs strictly inside b (any position)
const strictSubAny = (A: Api, ka: string, b: any): boolean => {
  const kids = (t: any): any[] => t.$ === "App" ? [t.f, t.x] : t.$ === "Ctr" || t.$ === "ADT" ? t.x : t.$ === "Eql" ? [t.a, t.b] : [];
  const st = kids(b);
  for (let n = 0; st.length && n < 5000; n++) { const x = st.pop(); if (A.key(x) === ka) return true; st.push(...kids(x)); }
  return false;
};
// a term whose key is ka is a strict subterm of b (Nat literals step: 2n has 1n inside)
const strictSub = (A: Api, ka: string, b: any): boolean => {
  const kids = (t: any): any[] => {
    if (t.$ === "Lit" && t.k === "Nat" && t.v > 0) return [B.Lit("Nat", t.v - 1)];
    return t.$ === "Ctr" ? t.x : [];
  };
  const st = kids(b);
  for (let n = 0; st.length && n < 2000; n++) { const x = st.pop(); if (A.key(x) === ka) return true; st.push(...kids(x)); }
  return false;
};
const hasMetaOrHole = (t: LTerm): boolean => {
  const st: any[] = [t];
  while (st.length) {
    const x = st.pop();
    if (!x || typeof x !== "object") continue;
    if (x.$ === "Var" && x.i >= (1 << 20)) return true;
    if (x.$ === "Hol") return true;
    for (const f of ["f", "x", "a", "b", "T", "A", "B"]) if (x[f] && typeof x[f] === "object" && !Array.isArray(x[f])) st.push(x[f]);
    if (Array.isArray(x.x)) st.push(...x.x);
  }
  return false;
};
// the stuck calls (a def applied, blocked on a variable) that occur on both sides of an equation,
// replaced by new parameters of their types
const generalize = (A: Api, g: Goal, N: any, enums = false): { params: string[]; args: string[]; goal: string } | null => {
  const seen = new Map<string, { t: LTerm; n: number }>();
  const walk = (t: LTerm, side: number) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") {
        const blk: LTerm[] = [];
        A.blockers(t, blk);
        const vars = new Set<number>();
        freeVars(t, vars);
        if (blk.length > 0 && vars.size > 0) {
          const kk = A.key(t);
          const e = seen.get(kk) ?? { t, n: 0 };
          e.n |= side;
          seen.set(kk, e);
        }
      }
      xs.forEach((x: LTerm) => walk(x, side));
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach((x: LTerm) => walk(x, side));
  };
  walk(N.a, 1); walk(N.b, 2);
  // maximal common subterms: drop one inside another common one
  const isEnum = (t: LTerm) => enumTyped(A, g, t);
  // common stuck calls become plain variables; with enums, a stuck call of an enumeration type (Cmp,
  // Bool) on one side becomes a variable with its equation (so the helper holds iff the goal does)
  const inside = (a: LTerm, b: LTerm) => a !== b && strictSubAny(A, A.key(a), b);
  const common0 = [...seen.values()].filter((e) => e.n === 3).map((e) => e.t);
  const common = common0.filter((a) => !common0.some((b) => inside(a, b))).slice(0, 4);
  const eqs0 = enums ? [...seen.values()].filter((e) => e.n !== 3 && isEnum(e.t)).map((e) => e.t) : [];
  const eqs = eqs0.filter((a) => !eqs0.some((b) => inside(b, a)) && !common.some((b) => inside(a, b) || inside(b, a))).slice(0, 2);
  if (enums && eqs.length === 0) return null;
  const gens = [...common, ...eqs];
  if (gens.length === 0) return null;
  const used = new Set<string>(g.names);
  const vs: { nm: string; ty: string; t: LTerm; eq?: string }[] = [];
  for (const t of gens) {
    const h = B.term_higher(t, g.env);
    const T = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, h, B.None(), g.ctx, g.d).ty);
    if (!T) return null;
    const ty = A.attempt(A.FUEL_NF, () => A.show(A.lower(T, g.d), g.names));
    if (ty === undefined) return null;
    vs.push({ nm: A.fresh("g", used), ty, t, eq: eqs.includes(t) ? A.fresh("hg", used) : undefined });
  }
  // the goal with each generalized call a variable (by key, from the largest)
  const repl = (t: LTerm): LTerm => {
    const kk = A.key(t);
    const v = vs.find((x) => A.key(x.t) === kk);
    if (v) return B.Ref(v.nm) as LTerm;
    switch (t.$) {
      case "App": return { ...t, f: repl(t.f), x: repl(t.x) } as LTerm;
      case "Ctr": case "ADT": return { ...t, x: (t as any).x.map(repl) } as LTerm;
      case "Eql": return { ...t, a: repl(t.a), b: repl(t.b), T: repl(t.T) } as LTerm;
      default: return t;
    }
  };
  const G = repl(N) as any;
  if (G.$ === "Eql" && A.key(G.a) === A.key(G.b)) return null;
  const goal = A.attempt(A.FUEL_NF, () => A.show(G, g.names));
  if (goal === undefined) return null;
  const cp = ctxParams(A, g, eqs.length ? (B.Eql(G, B.Ctr("Tuple", eqs) as LTerm, G) as LTerm) : G, (s) => s);
  if (!cp) return null;
  const shown = vs.map((v) => A.show(v.t, g.names));
  return {
    params: [...cp.params, ...vs.flatMap((v, i) => ["+" + v.nm + ": " + v.ty, ...(v.eq ? ["+" + v.eq + ": {" + v.nm + " == " + shown[i] + " : " + v.ty + "}"] : [])])],
    args: [...cp.args, ...vs.flatMap((v, i) => [shown[i], ...(v.eq ? ["{==}"] : [])])], goal,
  };
};

// ---- constructor steps for an arm: a clash, injectivity, inversion ----
// A hypothesis whose normal form is an equation with a constructor on a side:
// * C1{..} == C2{..}, two constructors: the arm is absurd (through a predicate helper is_C1 on the type);
// * C{as} == C{bs}: a part b that is a variable of the goal is rewritten by a (a projection helper with a
//   default, Equal.cong);
// * F(.., r, ..) == C{y}, F a def that matches r first and r stuck: when only one constructor K of r lets F
//   give C, an inversion helper: `(x0, .., (h1, h2)) = inv(.., r, h)` with h1: {r == K{xs}} and
//   h2: {F(.., K{xs}, ..) == C{y}} (Cir.exec.then(exec(f, a, st), ..) == next{st2} gives the middle state).
// The helpers are defs written out (not searched), checked in the book, printed above the body. A step
// returns the arm's text with a new ?TODO (its own line) where it continues.
const closedType = (t: LTerm) => { const fv = new Set<number>(); freeVars(t, fv); return fv.size === 0; };
const occurs = (t: LTerm, i: number) => { const fv = new Set<number>(); freeVars(t, fv); return fv.has(i); };
const substVar = (t: any, i: number): LTerm => {
  switch (t.$) {
    case "Var": return t.i === i ? (B.Ref("_") as LTerm) : t;
    case "App": return { ...t, f: substVar(t.f, i), x: substVar(t.x, i) };
    case "Ctr": case "ADT": return { ...t, x: t.x.map((x: LTerm) => substVar(x, i)) };
    case "Eql": return { ...t, a: substVar(t.a, i), b: substVar(t.b, i), T: substVar(t.T, i) };
    default: return t;
  }
};
// a def written out (a predicate, a projection, an inversion): checked, in the book, printed; its name
const fnHelper = (R: Run, head: string, body: string, why: string): string | null => {
  const { A } = R;
  const stmt = head.replace(/^def\s+[A-Za-z0-9_.]+\(/, "(") + body;
  const had = R.proven.get(stmt);
  if (had) return had;
  if (R.failed.has(stmt) || R.nFn >= MAX_FN_HELPERS) return null;
  const name = /^def\s+([A-Za-z0-9_.]+)\(/.exec(head)?.[1];
  const hk = name ? A.addTemp(R.k, head, body, true) : null;
  if (!hk || A.attempt(A.FUEL_FINAL, () => A.stmtOk(hk)) !== true || A.checkBody(hk, body) !== null) {
    if (A.debug()) console.error("[gen2] --ind: " + why + " helper does not check: " + head.replace(/\s+/g, " ").slice(0, hk ? 200 : 4000) + (hk ? " | " + String(A.errText(A.checkBody(hk, body) ?? "statement")).split(NL).slice(0, 4).join(" | ") : ""));
    if (hk) A.dropTemp(hk);
    R.failed.add(stmt);
    return null;
  }
  R.nFn++;
  R.proven.set(stmt, name!);
  R.helpers.push({ order: A.ORDER.get(hk), text: "# gen2 --ind: a helper (" + why + ")\n" + head + "\n" + body + "\n", head, body });
  return name!;
};
const fields = (n: number, base: string) => Array.from({ length: n }, (_, i) => base + i);
// the variables of a type at g (a type parameter such as A in Result<.., A>), as erased parameters of a
// helper and as the arguments of its calls; null when one is not a usable name
const typeVars = (A: Api, g: Goal, Tl: LTerm): { params: string[]; args: string[] } | null => {
  const fv = new Set<number>();
  freeVars(Tl, fv);
  const params: string[] = [], args: string[] = [];
  for (const i of [...fv].sort((a, b) => a - b)) {
    const a = A.ann(g, i);
    if (!a || g.names[i] === "_") return null;
    const T = A.attempt(A.FUEL_NF, () => A.show(A.lower(a.T, i), g.names.slice(0, i)));
    if (T === undefined) return null;
    params.push("-" + g.names[i] + ": " + T);
    args.push(g.names[i]);
  }
  return { params, args };
};
const callPre = (name: string, args: string[]) => name + "(" + args.map((a) => a + ", ").join("");
// is_C(z): Unit for the constructor C, Empty for the others
const predHelper = (R: Run, g: Goal, Tl: LTerm, ck: string): string | null => {
  const { A } = R;
  const T = A.show(Tl, g.names);
  const tv = typeVars(A, g, Tl);
  if (!tv) return null;
  const cs = A.ctrFields(g, B.term_higher(Tl, g.env), []);
  const c = cs?.find((x: any) => x.k === ck);
  if (!cs || !c || cs.length < 2) return null;
  const nm = A.helperName(R.k, R.used, "is_" + c.show.replace(/^.*\./, "").replace(/\W/g, "") + "_");
  const pat = c.show + "{" + fields(c.types.length, "f").join(", ") + "}";
  const name = fnHelper(R, "def " + nm + "(" + [...tv.params, "z: " + T].join(", ") + ") -> Type:", "  match z:\n    case " + pat + ":\n      Unit\n    case _:\n      Empty", "a constructor test");
  return name ? callPre(name, tv.args) : null;
};
// field j of constructor C, or d
const projHelper = (R: Run, g: Goal, Tl: LTerm, ck: string, j: number): { name: string; ty: string } | null => {
  const { A } = R;
  const T = A.show(Tl, g.names);
  const tv = typeVars(A, g, Tl);
  if (!tv) return null;
  const cs = A.ctrFields(g, B.term_higher(Tl, g.env), fields(16, "f"));
  const c = cs?.find((x: any) => x.k === ck);
  if (!c || j >= c.types.length) return null;
  const Ti = c.types[j];
  if (/\bf\d\b/.test(Ti)) return null; // a field type that names an earlier field
  const nm = A.helperName(R.k, R.used, c.show.replace(/^.*\./, "").replace(/\W/g, "") + "_" + j + "_");
  const pat = c.show + "{" + fields(c.types.length, "f").join(", ") + "}";
  const body = "  match z:\n    case " + pat + ":\n      f" + j + (cs.length > 1 ? "\n    case _:\n      d" : "");
  const name = fnHelper(R, "def " + nm + "(" + [...tv.params, "z: " + T, "d: " + Ti].join(", ") + ") -> " + Ti + ":", body, "a projection");
  return name ? { name: callPre(name, tv.args), ty: Ti } : null;
};
// an equation goal closed by a chain of at most two equations, each a context hypothesis or an instance of
// the induction hypothesis whose premises the context gives (frame.fixed's seq: the IH at the middle state,
// twice, joined by Equal.trans)
const instMeta = (A: Api, t: any, sol: (LTerm | null)[]): LTerm => {
  switch (t.$) {
    case "Var": return t.i >= A.META ? (sol[t.i - A.META] ?? t) : t;
    case "App": return { ...t, f: instMeta(A, t.f, sol), x: instMeta(A, t.x, sol) };
    case "Ctr": case "ADT": return { ...t, x: t.x.map((x: LTerm) => instMeta(A, x, sol)) };
    case "Eql": return { ...t, a: instMeta(A, t.a, sol), b: instMeta(A, t.b, sol), T: instMeta(A, t.T, sol) };
    case "Lam": return t;
    default: return t;
  }
};
const ihChain = (R: Run, k: string, g: Goal): string | null => {
  const { A } = R;
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(g.ty, g.d));
  if (!N || N.$ !== "Eql") return null;
  const def = A.RAW[k];
  const o = A.attempt(A.FUEL_NF, () => A.openMeta(def.T, def.n));
  const c = o ? A.lower(o.concl, 0) : null;
  type Eq = { a: LTerm; b: LTerm; T: string; text: string };
  const eqs: Eq[] = [];
  const nfKey = (t: LTerm) => A.attempt(A.FUEL_NF, () => A.key(A.nf(B.term_higher(t, g.env), g.d))) ?? A.key(t);
  // the context's equations
  for (let i = g.d - 1; i >= 0 && eqs.length < 24; i--) {
    if (!A.usable(g, i, B.Lone()) || g.names[i] === "_") continue;
    const T = A.attempt(A.FUEL_NF, () => A.lower(A.ann(g, i).T, i)) as any;
    if (T && T.$ === "Eql") eqs.push({ a: T.a, b: T.b, T: A.show(T.T, g.names), text: g.names[i] });
  }
  // instances of the induction hypothesis: a premise matched by a context fact, the other premises by facts of
  // the same normal form
  if (c && c.$ === "Eql" && o) {
    const prem = o.doms.map((d: any, j: number) => ({ j, T: A.attempt(A.FUEL_NF, () => A.lower(d.A, 0)) as any })).filter((p: any) => p.T && p.T.$ === "Eql");
    const own = new Set(A.introAll(A.rootGoal(k))?.names ?? []);
    for (const p of prem) for (let i = g.d - 1; i >= 0; i--) {
      if (!A.usable(g, i, B.Lone()) || g.names[i] === "_" || own.has(g.names[i])) continue;
      const hts = A.hypTargets(g, i);
      for (const ht of hts) {
        const sol: (LTerm | null)[] = new Array(def.n).fill(null);
        if (!A.matchT(p.T, ht, sol, g.d)) continue;
        sol[p.j] = B.Var(g.names[i], i) as LTerm;
        let ok = true;
        for (let j = 0; j < def.n && ok; j++) {
          if (sol[j]) continue;
          const pj = A.attempt(A.FUEL_NF, () => { const T = instMeta(A, A.lower(o.doms[j].A, 0), sol); return hasMetaOrHole(T) ? null : A.key(A.nf(B.term_higher(T, g.env), g.d)); });
          if (pj) for (let i2 = g.d - 1; i2 >= 0 && !sol[j]; i2--) {
            const a = A.ann(g, i2);
            if (a && g.names[i2] !== "_" && A.attempt(A.FUEL_NF, () => A.key(A.nf(a.T, g.d))) === pj) sol[j] = B.Var(g.names[i2], i2) as LTerm;
          }
          ok = !!sol[j];
        }
        if (!ok) continue;
        const ca = instMeta(A, c.a, sol), cb = instMeta(A, c.b, sol);
        if (hasMetaOrHole(ca) || hasMetaOrHole(cb)) continue;
        eqs.push({ a: ca, b: cb, T: A.show(instMeta(A, c.T, sol), g.names), text: B.name_show(A.job().file, k) + "(" + sol.map((x) => A.show(x!, g.names)).join(", ") + ")" });
        break;
      }
    }
  }
  if (eqs.length === 0) return null;
  const L = A.key(N.a), Rk = A.key(N.b);
  // each equation both ways, with the normal forms of its sides
  const dir: { from: string; to: string; fa: LTerm; tb: LTerm; T: string; text: string }[] = [];
  for (const e of eqs) {
    const ka = nfKey(e.a), kb = nfKey(e.b);
    dir.push({ from: ka, to: kb, fa: e.a, tb: e.b, T: e.T, text: e.text });
    dir.push({ from: kb, to: ka, fa: e.b, tb: e.a, T: e.T, text: "Equal.sym(" + e.T + ", " + A.show(e.a, g.names) + ", " + A.show(e.b, g.names) + ", " + e.text + ")" });
  }
  const goalT = A.show(N.T, g.names), Ls = A.show(N.a, g.names), Rs = A.show(N.b, g.names);
  for (const d of dir) if (d.from === L && d.to === Rk && A.tryText(g, d.text)) return d.text;
  for (const d1 of dir) {
    if (d1.from !== L) continue;
    for (const d2 of dir) {
      if (d2.from !== d1.to || d2.to !== Rk) continue;
      const t = "Equal.trans(" + goalT + ", " + Ls + ", " + A.show(d1.tb, g.names) + ", " + Rs + ", " + d1.text + ", " + d2.text + ")";
      if (A.tryText(g, t)) return t;
    }
  }
  return null;
};

const ctorStep = (R: Run, k: string, g: Goal, ind: string, arm = "", fits: (f: string | null) => boolean = () => true): string | null => {
  const { A } = R;
  const ch = A.attempt(A.FUEL_NF * 4, () => ihChain(R, k, g));
  if (ch && fits(ch)) return ch;
  const raw = A.lower(g.ty, g.d);
  const goalText = A.show(raw, g.names);
  const w = A.wnf(g.ty);
  // 0. a pair goal (a type with one constructor of two fields, such as {..} & {..}): one hole per part
  const pw = w && w.$ === "ADT" ? A.RAW[w.k] : null;
  if (pw && pw.c?.length === 1 && pw.c[0].n === 2 && fits("(?TODO, ?TODO)")) return "(?TODO, ?TODO)";
  const emptyGoal = !!w && w.$ === "ADT" && A.RAW[w.k]?.c?.length === 0;
  for (let i = g.d - 1; i >= 0; i--) {
    if (A.now() > R.until) return null;
    if (!A.usable(g, i, B.Lone()) || g.names[i] === "_") continue;
    const ts = A.hypTargets(g, i);
    const E = ts[ts.length - 1] as any;
    if (!E || E.$ !== "Eql" || hasMetaOrHole(E.T)) continue;
    const ca = E.a.$ === "Ctr" ? E.a : null, cb = E.b.$ === "Ctr" ? E.b : null;
    const T = A.show(E.T, g.names), h = g.names[i];
    const sym = "Equal.sym(" + T + ", " + A.show(E.a, g.names) + ", " + A.show(E.b, g.names) + ", " + h + ")";
    // 1. a clash: (%sym : is_Ca(_); Unit{}) : is_Ca(Cb) = Empty
    if (ca && cb && ca.k !== cb.k) {
      const P = predHelper(R, g, E.T, ca.k);
      if (!P) continue;
      const d = "(%" + sym + " : " + P + "_); Unit{})";
      const txt = emptyGoal ? d : "Empty.absurd(" + goalText + ", " + d + ")";
      if (A.tryText(g, txt)) return txt;
      continue;
    }
    // 2. injectivity: rewrite the goal's variable v (a part of one side) by the other side's part
    if (ca && cb && ca.k === cb.k) {
      for (let j = 0; j < ca.x.length; j++) {
        const a = ca.x[j], b = cb.x[j];
        if (A.key(a) === A.key(b)) continue;
        for (const [x, v, flip] of [[a, b, false], [b, a, true]] as [LTerm, LTerm, boolean][]) {
          if (v.$ !== "Var" || !occurs(raw, v.i) || occurs(x, v.i)) continue;
          const pj = projHelper(R, g, E.T, ca.k, j);
          if (!pj) continue;
          const [l, r, ev] = flip ? [E.b, E.a, sym] : [E.a, E.b, h];
          // eq : {x == v}; (%eq : G[v := _]; t) : G for t : G[v := x]
          const eq = "Equal.cong(" + T + ", " + pj.ty + ", z => " + pj.name + "z, " + A.show(x, g.names) + "), " + A.show(l, g.names) + ", " + A.show(r, g.names) + ", " + ev + ")";
          return "(%" + eq + " : " + A.show(substVar(raw, v.i), g.names) + "; ?TODO)";
        }
      }
      continue;
    }
    // 3. a variable of the goal equal to a constructor value: the goal at that value
    for (const [v, c, flip] of [[E.a, cb, false], [E.b, ca, true]] as [any, any, boolean][]) {
      if (!c || v.$ !== "Var" || !occurs(raw, v.i) || occurs(c, v.i)) continue;
      // e : {c == v}; (%e : G[v := _]; t) : G for t : G[v := c]
      const ev = flip ? h : sym;
      return "(%" + ev + " : " + A.show(substVar(raw, v.i), g.names) + "; ?TODO)";
    }
    // 4. inversion (each hypothesis once)
    const C = cb ?? ca, side = cb ? E.a : ca ? E.b : null;
    const ik = arm + "|" + h + "|" + A.show(E, g.names); // per arm, by names (a lambda binder level grows with the context)
    // only toward a constructor with fields (next{st2}): a Bool fact (.. == False{}) gives no part to read
    if (!C || C.x.length === 0 || !side || side.$ !== "App" || R.inverted.has(ik)) continue;
    const [hd, xs] = A.unapply(side);
    if (hd.$ !== "Ref") continue;
    // the strict argument, else the first matched one that is not a constructor yet (exec.set(r, Some{x}, st): st)
    const j0 = A.strictOf(hd.k), ms: Set<number> = A.matchedOf(hd.k);
    const js = [...(j0 === null ? [] : [j0]), ...[...ms].sort((a, b) => a - b)].filter((j) => j < xs.length && xs[j].$ !== "Ctr" && xs[j].$ !== "Lit");
    if (js.length === 0) continue;
    const inv = invHelper(R, g, side, xs[js[0]], C, !!cb, E.T, h, ind);
    if (inv) { R.inverted.add(ik); if (A.debug()) console.error("[gen2] --ind: inverted " + ik.slice(0, 160) + " (" + R.inverted.size + ")"); return inv; }
  }
  return null;
};
// pattern B: a hypothesis h whose normal form holds a stuck call c of an enumeration type (Bool, Cmp) that
// is no variable (Expect.holds(e, k) inside Bool.when(.., Expect.holds(e, k), ..) == Done{s}): a helper
// over the context with c a new parameter and h its premise, `(.., +g: Bool) -> {H[c := g]} -> G[c := g]`,
// proven by the schemes (a split on g with the premise introduced, then a clash or injectivity), called
// as `helper(.., c)(h)`
const hypGen = (R: Run, k: string, g: Goal, depth: number, ind: string, fits: (f: string | null) => boolean): string | null => {
  const { A } = R;
  const raw = A.lower(g.ty, g.d);
  if (A.attempt(A.FUEL_NF, () => hasMetaOrHole(raw)) !== false) return null;
  for (let i = g.d - 1; i >= 0; i--) {
    if (A.now() > R.until) return null;
    if (!A.usable(g, i, B.Lone()) || g.names[i] === "_") continue;
    const ts = A.hypTargets(g, i);
    const E = ts[ts.length - 1] as any;
    if (!E || E.$ !== "Eql" || hasMetaOrHole(E)) continue;
    // the stuck enumeration calls of E (outermost first), at most two tried
    const cs: LTerm[] = [];
    const walk = (t: any) => {
      if (cs.length >= 2 || !t || typeof t !== "object") return;
      if (t.$ === "App") {
        const [h, xs] = A.unapply(t);
        if (h.$ === "Ref") {
          const blk: LTerm[] = [];
          A.blockers(t, blk);
          const fv = new Set<number>();
          freeVars(t, fv);
          if (blk.length > 0 && fv.size > 0 && enumTyped(A, g, t) && !cs.some((c) => A.key(c) === A.key(t))) { cs.push(t); return; }
        }
        xs.forEach(walk);
      } else if (t.$ === "Ctr" || t.$ === "ADT") t.x.forEach(walk);
      else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
    };
    walk(E);
    // a call that is a whole side ({True == Char.is_eq(c, ..)}, a generalization's own equation) is a fact
    // about it already: nothing to generalize
    for (const c of cs.filter((c) => A.key(c) !== A.key(E.a) && A.key(c) !== A.key(E.b))) {
      if (A.now() > R.until) return null;
      const used = new Set<string>(g.names);
      const gv = A.fresh("g", used);
      const ck = A.key(c);
      const repl = (t: any): LTerm => {
        if (!t || typeof t !== "object") return t;
        if (A.key(t) === ck) return B.Ref(gv) as LTerm;
        switch (t.$) {
          case "App": return { ...t, f: repl(t.f), x: repl(t.x) };
          case "Ctr": case "ADT": return { ...t, x: t.x.map(repl) };
          case "Eql": return { ...t, a: repl(t.a), b: repl(t.b), T: repl(t.T) };
          default: return t;
        }
      };
      const Ty = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, B.term_higher(c, g.env), B.None(), g.ctx, g.d).ty);
      if (!Ty) continue;
      const tyText = A.attempt(A.FUEL_NF, () => A.show(A.lower(Ty, g.d), g.names));
      const He = repl(E), Gr = repl(raw);
      const hText = A.attempt(A.FUEL_NF, () => A.show(He, g.names)), gText = A.attempt(A.FUEL_NF, () => A.show(Gr, g.names));
      if (tyText === undefined || hText === undefined || gText === undefined) continue;
      const cp = ctxParams(A, g, B.Eql(Gr, He, Gr) as LTerm, (s) => s, new Set([i]));
      if (!cp) continue;
      const cText = A.show(c, g.names);
      const premise = hText.startsWith("{") ? hText : "{" + hText + "}";
      const nm = proveHelper(R, "def " + newName(R) + "(" + [...cp.params, "+" + gv + ": " + tyText].join(", ") + ") ->" + NL + "  " + premise + " -> " + gText + ":", depth);
      if (!nm) continue;
      const text = nm + "(" + [...cp.args, cText].join(", ") + ")(" + g.names[i] + ")";
      if (fits(text)) return text;
      // a variable named twice (k in the arguments and inside c) is affine: rebind it as reusable above
      if (ind) {
        const twice = g.names.filter((v: string) => v !== "_" && (text.match(new RegExp("(?<![\\w.])" + v.replace(/\./g, "\\.") + "(?![\\w.{])", "g")) ?? []).length > 1);
        const copied = twice.length ? twice.map((v: string) => "+" + v + " = " + v + NL + ind).join("") + text : null;
        if (copied && fits(copied)) return copied;
      }
      if (A.debug()) console.error("[gen2] --ind: the arm does not take " + text.slice(0, 300));
    }
  }
  return null;
};
// ---- atoms: stuck Bool/Cmp calls generalized as parameters (the decide pattern) ----
// a term that a call may take and still count as on its parameters: a variable, a literal, a
// constructor of such terms
const simpleArg = (t: any): boolean => !!t && (t.$ === "Var" || t.$ === "Lit" || t.$ === "Num" || ((t.$ === "Ctr" || t.$ === "ADT") && t.x.every(simpleArg)));
// Refolding. bend2's weak normal form unfolds a wrapper def (a def of an enumeration type with no match
// of its own, FileEp.is_resource(rest) = Bool.and(Glob.is_path(rest), ..)) inside a stuck match, so a
// hypothesis shows its body. A wrapper's pattern is the normal form of the wrapper applied to
// metavariables; a subterm that matches it is folded back into the call. Wrappers are looked for among
// the defs that the statement's calls name (three levels down).
type Wrap = { k: string; n: number; P: LTerm; head: string };
// def k returns an enumeration (Bool, Cmp)
const enumMemo = new Map<string, boolean>();
const enumDef = (A: Api, k: string): boolean => {
  if (enumMemo.has(k)) return enumMemo.get(k)!;
  const t = A.RAW[k];
  let r = false;
  if (t?.$ === "Def") {
    const o = A.attempt(A.FUEL_NF, () => A.openMeta(t.T, t.n));
    const w = o ? A.wnf(o.concl) : null;
    const at = w && w.$ === "ADT" ? A.RAW[w.k] : null;
    r = !!at && at.$ === "ADT" && at.c.length >= 2 && at.c.length <= 4 && at.c.every((c: any) => c.n === 0);
  }
  enumMemo.set(k, r);
  return r;
};
const wrapMemo = new Map<string, Wrap | null>();
let wrapBook: any = null;
const wrapOf = (A: Api, k: string): Wrap | null => {
  if (wrapBook !== A.book) { wrapMemo.clear(); wrapBook = A.book; }
  if (wrapMemo.has(k)) return wrapMemo.get(k)!;
  let r: Wrap | null = null;
  const t = A.RAW[k];
  if (t?.$ === "Def" && t.v && t.n >= 1 && t.n <= 4 && !isRecursive(A, k)) {
    r = A.attempt(A.FUEL_NF * 2, () => {
      let h: any = B.Ref(k);
      for (let j = 0; j < t.n; j++) h = B.App(h, B.Var("?" + j, A.META + j));
      const o = A.openMeta(t.T, t.n);
      const adt = o ? A.wnf(o.concl) : null;
      if (!adt || adt.$ !== "ADT") return null; // data (a Bool, a Maybe, ..): not a type or a proof
      const P = A.nf(h, 0);
      // a wrapper of another type folds only when no Bool/Cmp call is inside it (Uri.read: yes; Cli.watch,
      // whose body is a stuck Bool.when: no, the atoms are inside it)
      const at = A.RAW[adt.k];
      const isEnumTy = at?.$ === "ADT" && at.c.length >= 2 && at.c.length <= 4 && at.c.every((c: any) => c.n === 0);
      if (!isEnumTy) {
        const st: any[] = [P];
        for (let c = 0; st.length && c < 20000; c++) {
          const x = st.pop();
          if (!x || typeof x !== "object") continue;
          if (x.$ === "App") { const [hh] = A.unapply(x); if (hh.$ === "Ref" && enumDef(A, hh.k)) return null; }
          st.push(...termKids(x));
        }
      }
      const [ph] = A.unapply(P);
      if (ph.$ === "Ref" && ph.k === k) return null; // a match of its own: it stays a call anyway
      const seen = new Set<number>();
      const st: any[] = [P];
      for (let c = 0; st.length && c < 20000; c++) { const x = st.pop(); if (!x || typeof x !== "object") continue; if (x.$ === "Var") seen.add(x.i); else st.push(...termKids(x)); }
      for (let j = 0; j < t.n; j++) if (!seen.has(A.META + j)) return null;
      return { k, n: t.n, P, head: ph.$ === "Ref" ? ph.k : ph.$ };
    }) ?? null;
  }
  wrapMemo.set(k, r);
  return r;
};
// the defs that a term names, and the defs their bodies name, to the given depth (at most 200 defs)
const termKids = (x: any): any[] => {
  switch (x.$) {
    case "App": return [x.f, x.x];
    case "Ctr": case "ADT": return x.x;
    case "Eql": return [x.a, x.b, x.T];
    case "Lam": return [x.f];
    case "All": return [x.A, x.B];
    case "Mat": return [x.h, x.m];
    case "Let": case "Sub": return [];
    default: return Object.keys(x).filter((f) => f !== "s" && f !== "k" && f !== "q" && x[f] && typeof x[f] === "object" && typeof x[f].$ === "string").map((f) => x[f]);
  }
};
const namedDefs = (A: Api, t: any, out: Set<string>, depth: number) => {
  const st: any[] = [t];
  const found: string[] = [];
  for (let n = 0; st.length && n < 5000 && out.size < 200; n++) {
    const x = st.pop();
    if (!x || typeof x !== "object" || typeof x.$ !== "string") continue;
    if (x.$ === "Ref" && typeof x.k === "string" && A.RAW[x.k]?.$ === "Def" && !out.has(x.k)) { out.add(x.k); found.push(x.k); }
    st.push(...termKids(x));
  }
  if (depth <= 0) return;
  for (const k of found) {
    if (out.size >= 200) return;
    const d = A.RAW[k];
    if (d?.$ !== "Def" || !d.v) continue;
    const body = A.attempt(A.FUEL_NF, () => A.lower(d.v, 0));
    if (body) namedDefs(A, body, out, depth - 1);
  }
};
// t (a normal form at g) with the subterms that a wrapper pattern matches folded back, outermost first
const refold = (A: Api, g: Goal, t: any, ws: Wrap[], b: { n: number }): any => {
  if (!t || typeof t !== "object" || --b.n < 0) return t;
  if (t.$ === "App" || t.$ === "Ctr") {
    const [h] = t.$ === "App" ? A.unapply(t) : [t];
    const hk = h.$ === "Ref" ? h.k : h.$;
    for (const w of ws) {
      if (w.head !== hk) continue;
      const sol: (LTerm | null)[] = new Array(w.n).fill(null);
      if (A.matchT(w.P, t, sol, g.d) && sol.every((x) => x)) {
        return sol.reduce((r: any, x: any) => B.App(r, refold(A, g, x, ws, b)), B.Ref(w.k));
      }
    }
  }
  switch (t.$) {
    case "App": return { ...t, f: refold(A, g, t.f, ws, b), x: refold(A, g, t.x, ws, b) };
    case "Ctr": case "ADT": return { ...t, x: t.x.map((x: any) => refold(A, g, x, ws, b)) };
    case "Eql": return { ...t, a: refold(A, g, t.a, ws, b), b: refold(A, g, t.b, ws, b) };
    case "Lam": return { ...t, f: refold(A, g, t.f, ws, b) };
    default: return t;
  }
};
// the folded normal form of T (an HTerm at depth d of g): its normal form with the wrappers folded back
const foldNf = (A: Api, g: Goal, T: any, d: number, ws: Wrap[]): any => {
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(T, d));
  if (!N) return null;
  return A.attempt(A.FUEL_NF * 4, () => refold(A, g, N, ws, { n: 20000 })) ?? null;
};
// t with every subterm whose key is in m replaced by the variable m names (also under binders)
const replKeys = (A: Api, t: any, m: Map<string, string>): any => {
  if (!t || typeof t !== "object") return t;
  const v = m.get(A.key(t));
  if (v !== undefined) return B.Ref(v);
  switch (t.$) {
    case "App": return { ...t, f: replKeys(A, t.f, m), x: replKeys(A, t.x, m) };
    case "Ctr": case "ADT": return { ...t, x: t.x.map((x: any) => replKeys(A, x, m)) };
    case "Eql": return { ...t, a: replKeys(A, t.a, m), b: replKeys(A, t.b, m), T: replKeys(A, t.T, m) };
    case "Lam": return { ...t, f: replKeys(A, t.f, m) };
    default: return t;
  }
};
const hasKey = (A: Api, t: any, k: string): boolean => {
  if (!t || typeof t !== "object") return false;
  if (A.key(t) === k) return true;
  switch (t.$) {
    case "App": return hasKey(A, t.f, k) || hasKey(A, t.x, k);
    case "Ctr": case "ADT": return t.x.some((x: any) => hasKey(A, x, k));
    case "Eql": return hasKey(A, t.a, k) || hasKey(A, t.b, k);
    case "Lam": return hasKey(A, t.f, k);
    default: return false;
  }
};
// a first-order argument: a simple one, or a call of simple or first-order arguments (no binder), shallow
const plainArg = (t: any, n = 0): boolean => simpleArg(t) || (n < 3 && t?.$ === "App" && (() => { let h = t; const xs: any[] = []; while (h.$ === "App") { xs.push(h.x); h = h.f; } return h.$ === "Ref" && xs.every((x) => plainArg(x, n + 1)); })());
// the atoms of t: stuck calls of an enumeration type, on simple arguments or a whole side of a
// hypothesis (sides), also under binders; at most 4, in order of appearance
const atomsOf = (A: Api, g: Goal, t: any, sides: Set<string>, out: LTerm[]) => {
  if (!t || typeof t !== "object" || out.length >= 4) return;
  if (t.$ === "App") {
    const [h, xs] = A.unapply(t);
    if (h.$ === "Ref") {
      const kk = A.key(t);
      const fv = new Set<number>();
      freeVars(t, fv);
      const blk: LTerm[] = [];
      A.blockers(t, blk);
      const stuck = () => blk.length > 0 || (() => { const w = A.wnf(B.term_higher(t, g.env)); return !!w && w.$ !== "Ctr" && w.$ !== "Lit"; })();
      const ok = fv.size > 0 && [...fv].every((v) => v < g.d) && enumTyped(A, g, t);
      if (ok && xs.every(simpleArg) && stuck()) {
        if (!out.some((o) => A.key(o) === kk)) out.push(t);
        return;
      }
      // a whole side of a hypothesis (Maybe.is_some(Uri.read(root))) is an atom when no atom is inside it
      if (ok && sides.has(kk) && xs.every(plainArg) && stuck()) {
        const inner: LTerm[] = [];
        xs.forEach((x: any) => atomsOf(A, g, x, new Set(), inner));
        if (inner.length === 0) { if (!out.some((o) => A.key(o) === kk)) out.push(t); return; }
      }
    }
    xs.forEach((x: any) => atomsOf(A, g, x, sides, out));
  } else if (t.$ === "Ctr" || t.$ === "ADT") t.x.forEach((x: any) => atomsOf(A, g, x, sides, out));
  else if (t.$ === "Eql") { atomsOf(A, g, t.a, sides, out); atomsOf(A, g, t.b, sides, out); }
  else if (t.$ === "Lam") atomsOf(A, g, t.f, sides, out);
};
// an arm whose goal or hypotheses are stuck on Bool/Cmp calls of the statements (decide pattern): a
// helper over those calls as parameters, each with its equation (so the helper holds iff the arm
// does), its hypotheses and goal restated in folded form; the call `helper(.., call, {==}, ..)(h, ..)`
const atomGen = (R: Run, k: string, g: Goal, depth: number, ind: string, fits: (f: string | null) => boolean): string | null => {
  const { A } = R;
  if (depth > 0) return null; // inside a helper the atoms are parameters already: splits finish it
  const goal0 = A.attempt(A.FUEL_NF, () => A.lower(g.ty, g.d));
  if (!goal0 || A.attempt(A.FUEL_NF, () => hasMetaOrHole(goal0)) !== false) return null;
  // the wrappers that the goal and the hypotheses name
  const named = new Set<string>();
  const raws: any[] = [goal0];
  for (let i = 0; i < g.d; i++) { const T0 = A.attempt(A.FUEL_NF, () => A.lower(A.ann(g, i).T, i)); if (T0 && T0.$ === "Eql") raws.push(T0); }
  A.attempt(A.FUEL_NF * 4, () => { for (const r of raws) namedDefs(A, r, named, 2); });
  const tw = A.now();
  const ws = [...named].slice(0, 300).map((k2) => wrapOf(A, k2)).filter((w): w is Wrap => !!w).sort((x, y) => A.key(y.P).length - A.key(x.P).length);
  if (A.debug()) console.error("[gen2] --ind: atoms: " + named.size + " named defs, " + ws.length + " wrappers (" + ws.map((w) => A.shortOf(w.k)).join(", ").slice(0, 300) + ") in " + Math.round(A.now() - tw) + " ms");
  const G = foldNf(A, g, g.ty, g.d, ws);
  if (!G) return null;
  // the hypotheses: the equations of the context (usable), folded
  const hs: { i: number; T: any }[] = [];
  const sides = new Set<string>();
  for (let i = 0; i < g.d; i++) {
    if (g.names[i] === "_" || !A.usable(g, i, B.Lone())) continue;
    // a hypothesis as stated when one of its sides is itself an atom ({Cli.globs_read(Con{r, t}) == True}:
    // its normal form would unfold the call it is about), else its folded normal form
    const T0 = A.attempt(A.FUEL_NF, () => A.lower(A.ann(g, i).T, i));
    const rawAtom = !!T0 && T0.$ === "Eql" && [T0.a, T0.b].some((x: any) => x.$ === "App" && (() => { const [hh, xs] = A.unapply(x); return hh.$ === "Ref" && xs.every(simpleArg); })() && A.attempt(A.FUEL_NF, () => enumTyped(A, g, x)) === true);
    const T = rawAtom ? T0 : foldNf(A, g, A.ann(g, i).T, i, ws);
    if (!T || T.$ !== "Eql") continue;
    if (T.a.$ === "Var" || T.b.$ === "Var") continue; // a generalization's own equation {g == call}: not a source of atoms
    hs.push({ i, T });
    for (const s2 of [T.a, T.b]) if (s2.$ === "App") sides.add(A.key(s2));
  }
  const atoms: LTerm[] = [];
  A.attempt(A.FUEL_NF * 4, () => { for (const h of hs) atomsOf(A, g, h.T, sides, atoms); atomsOf(A, g, G, sides, atoms); });
  if (A.debug()) console.error("[gen2] --ind: atoms of " + g.path + ": " + atoms.map((t) => A.attempt(A.FUEL_NF, () => A.show(t, g.names))).join(", "));
  if (atoms.length === 0) return null;
  const used = new Set<string>(g.names);
  const vs = atoms.map((t) => ({ t, nm: A.fresh("g", used), eq: A.fresh("hg", used) }));
  const m = new Map(vs.map((v) => [A.key(v.t), v.nm] as [string, string]));
  const prem = hs.filter((h) => vs.some((v) => hasKey(A, h.T, A.key(v.t))));
  const Gr = replKeys(A, G, m);
  const shownAtoms = vs.map((v) => A.attempt(A.FUEL_NF, () => A.show(v.t, g.names)));
  const tys = vs.map((v) => { const Ty = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, B.term_higher(v.t, g.env), B.None(), g.ctx, g.d).ty); return Ty ? A.attempt(A.FUEL_NF, () => A.show(A.lower(Ty, g.d), g.names)) : undefined; });
  const gText = A.attempt(A.FUEL_NF, () => A.show(Gr, g.names));
  const pTexts = prem.map((h) => A.attempt(A.FUEL_NF, () => A.show(replKeys(A, h.T, m), g.names)));
  if (gText === undefined || shownAtoms.some((s) => s === undefined) || tys.some((s) => s === undefined) || pTexts.some((s) => s === undefined)) return null;
  // the parameters: what the restated goal and premises name, and the variables of the atoms (their equations)
  const all = B.Ctr("Tuple", [Gr, ...prem.map((h) => replKeys(A, h.T, m)), ...vs.map((v) => v.t)]) as LTerm;
  const cp = ctxParams(A, g, all, (s) => s, new Set(prem.map((h) => h.i)));
  if (!cp) return null;
  const brace = (s: string) => (s.startsWith("{") ? s : "{" + s + "}");
  // the atoms first (a split on them may then be followed by a split on a context variable: binders are
  // matched in order), then the context, then their equations
  const params = [...vs.map((v, j) => "+" + v.nm + ": " + tys[j]), ...cp.params, ...vs.map((v, j) => "+" + v.eq + ": {" + v.nm + " == " + shownAtoms[j] + " : " + tys[j] + "}")];
  const head = "def " + newName(R) + "(" + params.join(", ") + ") ->" + NL + "  " + [...pTexts.map((p) => brace(p!)), gText].join(" -> ") + ":";
  const nm = proveHelper(R, head, depth);
  if (!nm) return null;
  const call = nm + "(" + [...shownAtoms.map((a) => a!), ...cp.args, ...vs.map(() => "{==}")].join(", ") + ")" + (prem.length ? "(" + prem.map((h) => g.names[h.i]).join(", ") + ")" : "");
  if (fits(call)) return call;
  // a variable named twice (rest in the arguments and inside an atom) is affine: rebind it above
  if (ind) {
    const twice = g.names.filter((v: string) => v !== "_" && (call.match(new RegExp("(?<![\\w.])" + v.replace(/\./g, "\\.") + "(?![\\w.{])", "g")) ?? []).length > 1);
    const copied = twice.length ? twice.map((v: string) => "+" + v + " = " + v + NL + ind).join("") + call : null;
    if (copied && fits(copied)) return copied;
  }
  if (A.debug()) console.error("[gen2] --ind: the arm does not take " + call.slice(0, 300));
  return null;
};
// a function goal whose premise is a fact: introduce it, alone on its line (the steps then see it)
const introStep = (R: Run, g: Goal, ind: string, fits: (f: string | null) => boolean): string | null => {
  const { A } = R;
  if (!ind) return null;
  const w = A.wnf(g.ty);
  if (!w || w.$ !== "All") return null;
  const D = A.attempt(A.FUEL_NF, () => A.nf(w.A, g.d));
  if (!D || D.$ !== "Eql") return null;
  const nm = A.fresh("h", new Set<string>(g.names));
  const text = "+" + nm + " =>" + NL + ind + "  ?TODO";
  return fits(text) ? text : null;
};
// an arm stuck on a variable of a small datatype (a field of an outer pattern, as e in Found{e, d}): split it
const armSplit = (R: Run, k: string, g: Goal, ind: string, fits: (f: string | null) => boolean): string | null => {
  const { A } = R;
  if (!ind) return null;
  const terms: LTerm[] = [];
  // the premises of a function goal (`{H} -> G`) count as hypotheses: a split must come before their
  // introduction (a parameter cannot be matched after a local statement)
  let gg: Goal | null = g;
  for (let j = 0; j < 4 && gg; j++) {
    const w = A.wnf(gg.ty);
    if (!w || w.$ !== "All") break;
    const D = A.attempt(A.FUEL_NF * 2, () => A.nf(w.A, gg!.d));
    if (D && D.$ === "Eql") terms.push(D);
    gg = A.intro(gg, "_p" + j, false);
  }
  const N = gg ? A.attempt(A.FUEL_NF * 2, () => A.nf(gg!.ty, gg!.d)) : null;
  if (N) terms.push(N);
  for (let i = 0; i < g.d; i++) {
    if (!A.usable(g, i, B.Lone())) continue;
    const T = A.attempt(A.FUEL_NF * 2, () => A.nf(A.ann(g, i).T, i));
    if (T && T.$ === "Eql") terms.push(T);
  }
  const blk: LTerm[] = [];
  for (const t of terms) A.blockers(t, blk);
  // a variable inside a constructor that a call matches (decide.here(Found{e, d}) reads e): a nested match
  const inner = (t: any, depth: number) => {
    if (!t || typeof t !== "object" || depth > 6) return;
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") {
        const ms: Set<number> = A.matchedOf(h.k);
        const fieldVars = (a: any, n: number) => { if (n > 2 || !a) return; if (a.$ === "Ctr") a.x.forEach((x: any) => (x.$ === "Var" ? blk.push(x) : fieldVars(x, n + 1))); };
        xs.forEach((x: any, j: number) => { if (ms.has(j)) fieldVars(x, 0); });
      }
      xs.forEach((x: any) => inner(x, depth + 1));
    } else if (t.$ === "Ctr" || t.$ === "ADT") t.x.forEach((x: any) => inner(x, depth + 1));
    else if (t.$ === "Eql") { inner(t.a, depth + 1); inner(t.b, depth + 1); }
    else if (t.$ === "Lam") inner(t.f, depth + 1);
  };
  for (const t of terms) inner(t, 0);
  const seen = new Set<number>();
  for (const b of blk as any[]) {
    if (b.$ !== "Var" || b.i >= g.d || seen.has(b.i) || g.names[b.i] === "_") continue;
    seen.add(b.i);
    const adt = adtOf(A, g, A.ann(g, b.i).T);
    if (!adt || adt.c.length === 0 || adt.c.length > 6) continue;
    const tyName = A.attempt(A.FUEL_NF, () => A.show(A.lower(A.ann(g, b.i).T, b.i), g.names));
    if (!tyName || /^(U32|F32|Char|Nat|String|Word)/.test(tyName)) continue;
    const used = new Set<string>(g.names);
    const cases = adt.c.map((c: any) => (c.n === 0 ? B.name_show(A.job().file, c.k) + "{}" : ctrPat(A, "", c, g.names[b.i], used)));
    const text = "match " + g.names[b.i] + ":" + NL + cases.map((c: string) => ind + "  case " + c + ":" + NL + ind + "    ?TODO").join(NL);
    if (fits(text)) return text;
  }
  return null;
};
// the inversion helper for side == C (side's strict argument rr stuck) and its use in the arm
const invHelper = (R: Run, g: Goal, side: LTerm, rr: LTerm, C: any, cRight: boolean, Tl: LTerm, h: string, ind: string): string | null => {
  const { A } = R;
  const used = new Set<string>(g.names);
  const rv = A.fresh("r", used);
  const rkey = A.key(rr);
  const repl = (t: any): LTerm => {
    if (A.key(t) === rkey) return B.Ref(rv) as LTerm;
    switch (t.$) {
      case "App": return { ...t, f: repl(t.f), x: repl(t.x) };
      case "Ctr": case "ADT": return { ...t, x: t.x.map(repl) };
      default: return t;
    }
  };
  const G = repl(side), Ct = A.show(C, g.names), T = A.show(Tl, g.names);
  const Tr = A.attempt(A.FUEL_NF, () => B.term_infer(A.book, g.lhs, B.term_higher(rr, g.env), B.None(), g.ctx, g.d).ty);
  if (!Tr) return null;
  const Trl = A.lower(Tr, g.d);
  if (!closedType(Trl)) return null;
  const xsN = fields(16, A.fresh("x", used) + "_"), ysN = fields(16, A.fresh("y", used) + "_"); // Sigma binders, arm patterns
  const cs = A.ctrFields(g, Tr, xsN);
  // a record (one constructor) inverts only when r is a variable (its fields named); else two to six
  if (!cs || cs.length > 6 || (cs.length < 2 && rr.$ !== "Var")) return null;
  const cp = ctxParams(A, g, B.Eql(G, C, Tl) as LTerm, (s) => s);
  if (!cp) return null;
  const Gt = A.show(G, g.names);
  const hyp = cRight ? "{" + Gt + " == " + Ct + " : " + T + "}" : "{" + Ct + " == " + Gt + " : " + T + "}";
  const P = predHelper(R, g, Tl, C.k);
  if (!P) return null;
  const at = (s: string, pat: string) => s.replace(new RegExp("(?<![\\w.])" + rv + "(?![\\w.])", "g"), pat); // rv as a whole name
  for (const K of cs) {
    if (A.now() > R.until) return null;
    const xs = xsN.slice(0, K.types.length);
    const pat = K.show + "{" + xs.join(", ") + "}";
    const parts = "{" + rv + " == " + pat + " : " + A.show(Trl, g.names) + "} & " + at(hyp, pat);
    // inv(.., r, h, G, k) : G, with k : @x0: T0 -> .. -> @h1: {r == K{xs}} -> @h2: {F(.., K{xs}, ..) == C} -> G
    const hyp2 = at(hyp, pat), eqr = "{" + rv + " == " + pat + " : " + A.show(Trl, g.names) + "}";
    const kT = [...xs.map((x, i) => "@+" + x + ": " + K.types[i]), "@+h1: " + eqr, "@+h2: " + hyp2].join(" -> ") + " -> G";
    const nm = A.helperName(R.k, R.used, "inv");
    const head = "def " + nm + "(" + [...cp.params, "+" + rv + ": " + A.show(Trl, g.names), "+h: " + hyp, "-G: Type", "k: " + kT].join(", ") + ") -> G:";
    const arms = cs.map((K2: any) => {
      const ys = (K2.k === K.k ? xsN : ysN).slice(0, K2.types.length);
      const p2 = K2.show + "{" + ys.join(", ") + "}";
      if (K2.k === K.k) return "    case " + p2 + ":\n      k(" + [...xs, "{==}", "h"].join(", ") + ")";
      const ev = cRight ? "Equal.sym(" + T + ", " + at(Gt, p2) + ", " + Ct + ", h)" : "h";
      return "    case " + p2 + ":\n      Empty.absurd(G, (%" + ev + " : " + P + "_); Unit{}))";
    });
    const name = fnHelper(R, head, "  match " + rv + ":\n" + arms.join("\n"), "an inversion");
    if (!name) continue;
    const hs = [A.fresh("h", used), A.fresh("h", used)];
    const vs = xs.map((x, i) => A.fresh(K.show.replace(/^.*\./, "").replace(/\W/g, "").slice(0, 3) + i, used));
    return name + "(" + [...cp.args, A.show(rr, g.names), h, A.show(A.lower(g.ty, g.d), g.names)].join(", ") + ", " + [...vs, ...hs].join(" => ") + " => ?TODO)";
  }
  // no single constructor: a case split with one continuation per constructor (each with its equation and
  // h at that constructor); the impossible ones close by a clash later (exec.if.of(U32.is_zero(x), ..))
  if (cs.length > 3 || A.now() > R.until) return null;
  const nm = A.helperName(R.k, R.used, "case");
  const ks = cs.map((K: any, i: number) => {
    const xs = xsN.slice(0, K.types.length), pat = K.show + "{" + xs.join(", ") + "}";
    return "k" + i + ": " + [...xs.map((x: string, j: number) => "@+" + x + ": " + K.types[j]), "@+h1: {" + rv + " == " + pat + " : " + A.show(Trl, g.names) + "}", "@+h2: " + at(hyp, pat)].join(" -> ") + " -> G";
  });
  const head = "def " + nm + "(" + [...cp.params, "+" + rv + ": " + A.show(Trl, g.names), "+h: " + hyp, "-G: Type", ...ks].join(", ") + ") -> G:";
  const arms = cs.map((K: any, i: number) => {
    const xs = xsN.slice(0, K.types.length);
    return "    case " + K.show + "{" + xs.join(", ") + "}:\n      k" + i + "(" + [...xs, "{==}", "h"].join(", ") + ")";
  });
  const name = fnHelper(R, head, "  match " + rv + ":\n" + arms.join("\n"), "a case split");
  if (!name) return null;
  const conts = cs.map((K: any) => {
    const u = new Set(used);
    const vs = xsN.slice(0, K.types.length).map((_: string, i: number) => A.fresh(K.show.replace(/^.*\./, "").replace(/\W/g, "").slice(0, 3) + i, u));
    return [...vs, A.fresh("h", u), A.fresh("h", u)].join(" => ") + " => ?TODO";
  });
  return name + "(" + [...cp.args, A.show(rr, g.names), h, A.show(A.lower(g.ty, g.d), g.names), ...conts].join(", ") + ")";
};

// ---- schemes ----
const schemes = (R: Run, k: string): Scheme[] => {
  const { A } = R;
  const tl = tele(A, k);
  if (!tl) { if (A.debug()) console.error("[gen2] --ind: no parameters for " + A.shortOf(k)); return []; }
  const out: Scheme[] = [];
  const add = (name: string, body: string | null) => { if (body) out.push({ name, body: indent(body, "  ") }); };
  for (const s of [enumScheme, u32Scheme, wordScheme, natScheme, funScheme, recScheme, blkScheme, premScheme, wholeScheme]) {
    const r = A.attempt(A.FUEL_NF * 4, () => s(R, k, tl));
    if (A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " " + s.name + ": " + (r ? r.map((x: any) => x[0]).join(", ") : "none"));
    if (r) for (const [nm, b] of r) add(nm, b);
  }
  return out;
};
type Tele = { g: Goal; ps: { name: string; q: string; ty: string; T: HTerm; i: number }[] };
// the parameters that block the goal's normal form (strict arguments of stuck calls)
const blocking = (A: Api, tl: Tele): number[] => {
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const blk: LTerm[] = [];
  if (N) A.blockers(N, blk);
  const out: number[] = [];
  for (const b of blk) if (b.$ === "Var" && b.i < tl.ps.length && !out.includes(b.i)) out.push(b.i);
  return out.sort((a, b) => a - b);
};
// the parameters that a stuck call of the goal's normal form matches (any position its case tree reads)
const matchedParams = (A: Api, tl: Tele): number[] => {
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const out = new Set<number>(blocking(A, tl));
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") { const ms: Set<number> = A.matchedOf(h.k); xs.forEach((x: LTerm, j: number) => { if (ms.has(j) && x.$ === "Var" && x.i < tl.ps.length) out.add(x.i); }); }
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  if (N) walk(N);
  return [...out].filter((i) => tl.ps[i].q !== "-").sort((a, b) => a - b);
};
// the case list of parameter i: its constructors (fields named after it)
const casesOf = (A: Api, tl: Tele, i: number, used: Set<string>): string[] | null => {
  const p = tl.ps[i];
  if (p.ty === "Nat") return ["0n", "1n+" + A.fresh(p.name + "p", used)];
  const adt = adtOf(A, tl.g, p.T);
  if (!adt || adt.c.length === 0 || adt.c.length > 12 || /^(U32|F32|Char)$/.test(p.ty)) return null;
  return adt.c.map((c: any) => (c.n === 0 ? B.name_show(A.job().file, c.k) + "{}" : ctrPat(A, "", c, p.name, used)));
};
const enumScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const bound = new Map<number, number>();
  for (const p of tl.ps) {
    const m = /^\{Nat\.is_(le|lt)\(([A-Za-z_]\w*), (\d+)n\) == True\{\} : Bool\}$/.exec(p.ty);
    if (!m) continue;
    const i = tl.ps.findIndex((x) => x.name === m[2] && x.ty === "Nat");
    const c = +m[3] - (m[1] === "lt" ? 1 : 0);
    if (i >= 0 && c >= 0 && c <= ENUM_MAX) bound.set(i, Math.min(c, bound.get(i) ?? c));
  }
  if (bound.size === 0) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const idx = [...new Set([...bound.keys(), ...matchedParams(A, tl)])].sort((a, b) => a - b);
  const cases: string[][] = [];
  for (const i of idx) {
    if (bound.has(i)) cases.push([...Array.from({ length: bound.get(i)! + 1 }, (_, v) => v + "n"), (bound.get(i)! + 1) + "n+" + A.fresh(tl.ps[i].name + "p", used)]);
    else { const c = casesOf(A, tl, i, used); if (!c) return null; cases.push(c); }
  }
  const all = product(cases);
  if (all.length > MAX_ARMS) return null;
  return [["enum", matchText(idx.map((i) => tl.ps[i].name), all, () => "?TODO")]];
};
const u32Scheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  // the U32 parameters that a stuck call reads, or that a U32 operation takes
  const mp = new Set(matchedParams(A, tl));
  const N0 = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref" && /^U32\./.test(A.shortOf(h.k))) xs.forEach((x: LTerm) => { if (x.$ === "Var") mp.add(x.i); });
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  if (N0) walk(N0);
  const us = tl.ps.filter((p) => p.ty === "U32" && p.q !== "-" && mp.has(p.i));
  if (us.length === 0 || us.length > 4) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const ws = us.map((p) => A.fresh(p.name + "w", used));
  const skel = matchText(us.map((p) => p.name), [ws.map((w) => "U32{" + w + "}")], () => "?TODO");
  // the arm's goal: a statement over words of width 32n generalizes to width n
  const body = indent(skel, "  ");
  const err = A.checkBody(k, body.replace("?TODO", "?gen2hole"));
  const g = typeof err === "object" ? A.holeGoal(k, err, "u32") : null;
  if (!g) return [["u32", skel]];
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(g.ty, g.d));
  if (!N || N.$ !== "Eql") return [["u32", skel]];
  const lifted = liftWidth(R, g, N);
  return lifted ? [["u32+width", skel.replace("?TODO", lifted)], ["u32", skel]] : [["u32", skel]];
};
// a goal over words of width 32 (after U32{w} splits): the helper over width n, proven, and its call
const liftWidth = (R: Run, g: Goal, N: any): string | null => {
  const { A } = R;
  // a U32 side: U32{w} (its word w), or the literal 0 (Word.zero); a constant word of zeros is
  // Word.zero at any width
  const isU32 = (t: any) => (t.$ === "Ctr" && A.shortOf(t.k) === "U32" && t.x.length === 1) || (t.$ === "Lit" && t.k === "U32" && t.v === 0);
  const u32 = A.show(N.T, g.names) === "U32" && isU32(N.a) && isU32(N.b);
  const zeros = (n: number): string => (n === 0 ? "WNil{}" : "WCon{False{}, " + zeros(n - 1) + "}");
  const z32 = zeros(32);
  const side = (t: any) => (u32 ? (t.$ === "Lit" ? "Word.zero(32n)" : A.show(t.x[0], g.names)) : A.show(t, g.names)).split(z32).join("Word.zero(32n)");
  const L = u32 ? (N.a.$ === "Lit" ? N.b.x[0] : N.a.x[0]) : N.a, Rr = u32 ? (N.b.$ === "Lit" ? N.a.x[0] : N.b.x[0]) : N.b;
  const T = u32 ? "Word(32n)" : A.show(N.T, g.names);
  const ls = side(N.a), rs = side(N.b);
  if (!/\b32n\b/.test(ls + rs)) return null;
  const used = new Set<string>(g.names);
  const nv = A.fresh("n", used);
  const w = (s: string) => s.replace(/\b32n\b/g, nv).replace(/\b0n\b/g, "0n");
  const cp = ctxParams(A, g, B.Eql(L, Rr, N.T) as LTerm, w);
  if (!cp) return null;
  const nm = proveHelper(R, "def " + newName(R) + "(+" + nv + ": Nat, " + cp.params.join(", ") + ") ->\n  {" + w(ls) + " == " + w(rs) + " : " + w(T) + "}:", 0);
  if (!nm) return null;
  const call = nm + "(32n, " + cp.args.join(", ") + ")";
  return u32 ? "Equal.cong(Word(32n), U32, w => U32{w}, " + ls + ", " + rs + ", " + call + ")" : call;
};
// n: Nat and words of width n: match n; then the words with their head bits as nested patterns
// (WCon{False{}, t}: a pattern binder cannot be matched after a later parameter); as a second
// skeleton, also the other parameters that a stuck call matches
const wordScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const n = tl.ps.findIndex((p) => p.ty === "Nat" && p.q !== "-");
  if (n < 0) return null;
  const nm = tl.ps[n].name;
  const words = tl.ps.filter((p) => p.ty === "Word(" + nm + ")" && p.q !== "-");
  if (words.length === 0 || words.length > 4) return null;
  const out: [string, string][] = [];
  for (const extra of [false, true]) {
    const used = new Set(tl.ps.map((p) => p.name));
    const pv = A.fresh("p", used);
    const others = extra ? matchedParams(A, tl).filter((i) => i !== n && !words.some((w) => w.i === i)) : [];
    if (extra && others.length === 0) continue;
    const idx = [...words.map((w) => w.i), ...others].sort((a, b) => a - b);
    const cases: string[][] = [];
    for (const i of idx) {
      const p = tl.ps[i];
      if (words.some((w) => w.i === i)) { const t = A.fresh(p.name + "t", used); cases.push(["WCon{False{}, " + t + "}", "WCon{True{}, " + t + "}"]); }
      else { const c = casesOf(A, tl, i, used); if (!c) return null; cases.push(c); }
    }
    const all = product(cases);
    if (all.length > MAX_ARMS) continue;
    // at width 0 every word is WNil{}
    const zu = new Set(used);
    const zc = idx.map((i) => (words.some((w) => w.i === i) ? ["WNil{}"] : casesOf(A, tl, i, zu)));
    const zero = zc.every((c) => c) ? matchText(idx.map((i) => tl.ps[i].name), product(zc as string[][]), () => "?TODO") : "?TODO";
    const succ = matchText(idx.map((i) => tl.ps[i].name), all, () => "?TODO");
    out.push([extra ? "word+split" : "word", "match " + nm + ":" + NL + "  case 0n:" + NL + indent(zero, "    ") + NL + "  case 1n+" + pv + ":" + NL + indent(succ, "    ")]);
  }
  return out;
};
// the goal itself as one arm, when no scheme above applies: it lets the arm helpers run on a goal
// with no induction in it (a stuck Bool or Cmp call generalized to a variable, with its equation when
// it occurs on one side only; constructor steps on a hypothesis such as Done{x} == Done{s})
const wholeScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => [["whole", "?TODO"]];
// the premises of the conclusion of k (`-> {..} -> G`): their names (fresh) and goals, at most 4
const premises = (A: Api, tl: Tele): { names: string[]; goals: Goal[] } => {
  const used = new Set(tl.ps.map((p) => p.name));
  const names: string[] = [], goals: Goal[] = [];
  let g: Goal | null = tl.g;
  for (let j = 0; j < 4 && g; j++) {
    const w = A.wnf(g.ty);
    if (!w || w.$ !== "All") break;
    const nm = A.fresh(j === 0 ? "h" : "h" + j, used);
    g = A.intro(g, nm, false);
    if (!g) break;
    names.push(nm); goals.push(g);
  }
  return { names, goals };
};
// pattern B, on the side of the helper: the premises introduced in each arm (`h => ?TODO`), alone and
// under a split on each enumeration parameter (Bool, Cmp) that the normal form of a premise blocks on
const premScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const pr = premises(A, tl);
  // reusable binders: a step that uses h (injectivity) and the holes it leaves would count h twice
  const intro = pr.names.map((n) => "+" + n + " => ").join("") + "?TODO";
  const out: [string, string][] = pr.names.length ? [["whole+intro", intro]] : [];
  const last = pr.goals.length ? pr.goals[pr.goals.length - 1] : tl.g;
  const idx = new Set<number>();
  // an enumeration parameter that the conclusion blocks on (g of a generalized Char.is_eq(c, ..))
  for (const i of blocking(A, tl)) if (tl.ps[i].q !== "-" && enumTyped(A, tl.g, B.Var(tl.ps[i].name, i) as LTerm)) idx.add(i);
  for (let j = 0; j < pr.names.length; j++) {
    const a = A.ann(last, tl.ps.length + j);
    const N = a ? A.attempt(A.FUEL_NF * 2, () => A.nf(a.T, tl.ps.length + j)) : null;
    const blk: LTerm[] = [];
    if (N) A.blockers(N, blk);
    for (const b of blk) if (b.$ === "Var" && b.i < tl.ps.length && tl.ps[b.i].q !== "-" && enumTyped(A, tl.g, b)) idx.add(b.i);
  }
  const ids = [...idx].sort((a, b) => a - b).slice(0, 3);
  for (const i of ids.slice(0, 2)) {
    const used = new Set(tl.ps.map((p) => p.name));
    const cs = casesOf(A, tl, i, used);
    if (!cs) continue;
    out.push(["prem:" + tl.ps[i].name, matchText([tl.ps[i].name], cs.map((c) => [c]), () => intro)]);
  }
  // all of them jointly (nested Bool.pick(g, .., Bool.pick(g1, ..)): one arm per combination)
  if (ids.length >= 2) {
    const used = new Set(tl.ps.map((p) => p.name));
    const cs = ids.map((i) => casesOf(A, tl, i, used));
    if (cs.every((c) => c) && product(cs as string[][]).length <= 16) out.unshift(["prem:all", matchText(ids.map((i) => tl.ps[i].name), product(cs as string[][]), () => intro)]);
  }
  return out;
};
// the parameters that a stuck call reads, in the goal or in the type of a hypothesis parameter
const matchedAll = (A: Api, tl: Tele): number[] => {
  const out = new Set<number>(matchedParams(A, tl));
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      if (h.$ === "Ref") { const ms: Set<number> = A.matchedOf(h.k); xs.forEach((x: LTerm, j: number) => { if (ms.has(j) && x.$ === "Var" && x.i < tl.ps.length) out.add(x.i); }); }
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  for (const p of tl.ps) {
    const T = A.attempt(A.FUEL_NF * 2, () => A.nf(p.T, p.i));
    if (T && T.$ === "Eql") walk(T);
  }
  return [...out].filter((i) => tl.ps[i].q !== "-").sort((a, b) => a - b);
};
const isRecordTy = (A: Api, tl: Tele, i: number): boolean => {
  const p = tl.ps[i];
  if (/^(U32|F32|Char|Word|String)/.test(p.ty)) return false;
  const adt = adtOf(A, tl.g, p.T);
  return !!adt && adt.c.length === 1 && adt.c[0].n > 0;
};
// the decide pattern: the records (one constructor with fields) that a stuck call reads, opened, the
// premises introduced; the arm then gets its stuck Bool calls generalized (atomGen)
const recScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const recs = matchedAll(A, tl).filter((i) => isRecordTy(A, tl, i)).slice(0, 3);
  const pr = premises(A, tl);
  const intro = "?TODO"; // premises stay in the goal: an arm may still split a parameter, then introduce them
  if (recs.length === 0) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const cs = recs.map((i) => casesOf(A, tl, i, used));
  if (!cs.every((c) => c)) return null;
  return [["rec", matchText(recs.map((i) => tl.ps[i].name), product(cs as string[][]), () => intro)]];
};
// the parameters that the goal or a premise blocks on (enumerations, and datatypes of at most 6
// constructors), split jointly in parameter order, the premises introduced in each arm
const blkScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const pr = premises(A, tl);
  const intro = "?TODO"; // premises stay in the goal: an arm may still split a parameter, then introduce them
  const idx = new Set<number>(blocking(A, tl));
  const last = pr.goals.length ? pr.goals[pr.goals.length - 1] : tl.g;
  for (let j = 0; j < pr.names.length; j++) {
    const a = A.ann(last, tl.ps.length + j);
    const N = a ? A.attempt(A.FUEL_NF * 2, () => A.nf(a.T, tl.ps.length + j)) : null;
    const blk: LTerm[] = [];
    if (N) A.blockers(N, blk);
    for (const b of blk) if (b.$ === "Var" && b.i < tl.ps.length) idx.add(b.i);
  }
  for (const p of tl.ps) {
    const T = A.attempt(A.FUEL_NF * 2, () => A.nf(p.T, p.i));
    if (!T || T.$ !== "Eql" || T.a.$ === "Var" || T.b.$ === "Var") continue; // {g == call}: a generalization's equation
    const blk: LTerm[] = [];
    A.blockers(T, blk);
    for (const b of blk) if (b.$ === "Var" && b.i < p.i) idx.add(b.i);
  }
  // every enumeration parameter (a generalized Bool call: the point is to split them all at once)
  for (const p of tl.ps) if (p.q !== "-" && enumTyped(A, tl.g, B.Var(p.name, p.i) as LTerm)) idx.add(p.i);
  const ids = [...idx].filter((i) => {
    const p = tl.ps[i];
    if (p.q === "-" || /^(U32|F32|Char|Nat|String|Word)/.test(p.ty)) return false;
    const adt = adtOf(A, tl.g, p.T);
    return !!adt && adt.c.length >= 1 && adt.c.length <= 6;
  }).sort((a, b) => a - b).slice(0, 4);
  if (ids.length === 0) return null;
  const used = new Set(tl.ps.map((p) => p.name));
  const cs = ids.map((i) => casesOf(A, tl, i, used));
  if (!cs.every((c) => c) || product(cs as string[][]).length > MAX_ARMS) return null;
  return [["blk", matchText(ids.map((i) => tl.ps[i].name), product(cs as string[][]), () => intro)]];
};
const natScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const out: [string, string][] = [];
  for (const i of blocking(A, tl)) {
    const p = tl.ps[i];
    if (p.ty !== "Nat" || p.q === "-") continue;
    const used = new Set(tl.ps.map((x) => x.name));
    out.push(["nat:" + p.name, matchText([p.name], [["0n"], ["1n+" + A.fresh(p.name + "p", used)]], () => "?TODO")]);
    if (out.length >= 2) break;
  }
  return out;
};
// functional induction: a recursive def of the goal applied to parameters at the positions it
// matches: one skeleton with its matched parameters split jointly (their constructors)
const funScheme = (R: Run, k: string, tl: Tele): [string, string][] | null => {
  const { A } = R;
  const raw = A.lower(tl.g.ty, tl.g.d);
  const N = A.attempt(A.FUEL_NF * 2, () => A.nf(tl.g.ty, tl.g.d));
  const out: [string, string][] = [];
  const seen = new Set<string>();
  // the parameters that a call reads (its matched arguments), also through a recursive call in a
  // matched position (List.get(List.replicate(U32, n, 0), q) reads n and q)
  const reads = (t: LTerm, idx: number[], rec: { r: boolean }, n = 0) => {
    if (n > 6) return;
    if (t.$ === "Var") { if (t.i < tl.ps.length && tl.ps[t.i].q !== "-" && !idx.includes(t.i)) idx.push(t.i); return; }
    if (t.$ !== "App") return;
    const [h, xs] = A.unapply(t);
    if (h.$ !== "Ref") return;
    if (isRecursive(A, h.k)) rec.r = true;
    const ms: Set<number> = A.matchedOf(h.k);
    // a Nat argument of a recursive def is read too (a fuel: Cir.exec matches it only in its while case)
    xs.forEach((x: LTerm, j: number) => { if (ms.has(j) || (isRecursive(A, h.k) && x.$ === "Var" && x.i < tl.ps.length && tl.ps[x.i].ty === "Nat")) reads(x, idx, rec, n + 1); });
  };
  const walk = (t: LTerm) => {
    if (t.$ === "App") {
      const [h, xs] = A.unapply(t);
      const idx: number[] = [], rec = { r: false };
      reads(t, idx, rec);
      if (A.debug() && h.$ === "Ref") console.error("[gen2] --ind: fun " + A.shortOf(h.k) + " reads " + idx.join(",") + (rec.r ? " (recursive)" : ""));
      const kk = idx.slice().sort().join(",");
      if (h.$ === "Ref" && rec.r && idx.length >= 2 && idx.length <= 3 && !seen.has(kk)) {
        seen.add(kk);
        idx.sort((a, b) => a - b);
        const used = new Set(tl.ps.map((p) => p.name));
        const cs = idx.map((i) => casesOf(A, tl, i, used));
        if (cs.every((c) => c) && product(cs as string[][]).length <= MAX_ARMS)
          out.push(["fun:" + A.shortOf(h.k), matchText(idx.map((i) => tl.ps[i].name), product(cs as string[][]), () => "?TODO")]);
      }
      xs.forEach(walk);
    } else if (t.$ === "Ctr" || t.$ === "ADT") (t as any).x.forEach(walk);
    else if (t.$ === "Eql") { walk(t.a); walk(t.b); }
  };
  walk(raw);
  if (N) walk(N);
  for (const p of tl.ps) { const T = A.attempt(A.FUEL_NF, () => A.lower(p.T, p.i)); if (T && T.$ === "Eql") walk(T); }
  return out.slice(0, 2);
};
const recMemo = new Map<string, boolean>();
const isRecursive = (A: Api, k: string): boolean => {
  if (recMemo.has(k)) return recMemo.get(k)!;
  const t = A.RAW[k];
  let r = false;
  if (t?.$ === "Def" && t.v) {
    // the body (lowered) names k: a self-call
    const body = A.attempt(A.FUEL_NF, () => A.lower(t.v, 0));
    const st: any[] = body ? [body] : [];
    for (let n = 0; st.length && n < 20000 && !r; n++) {
      const x = st.pop();
      if (!x || typeof x !== "object") continue;
      if (x.$ === "Ref" && x.k === k) { r = true; break; }
      for (const f in x) if (f !== "s" && x[f] && typeof x[f] === "object") st.push(x[f]);
    }
  }
  recMemo.set(k, r);
  return r;
};

// ---- the schemes on def k: the first that closes every arm, else the best partial ----
const schemesProve = (R: Run, k: string, depth: number): Fill | null => {
  const { A } = R;
  // the leaf tactics on every scheme's arms first; then helpers for the arms left of the best two
  const tried: Fill[] = [];
  for (const s of schemes(R, k)) {
    if (A.now() > R.until) break;
    if (ONLY && depth === 0 && !ONLY.test(s.name)) continue;
    const r = fillArms(R, k, s.body, depth, [0]);
    if (A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " scheme " + s.name + ": " + (r ? r.open + " open, " + r.closed + " closed" : "does not check") + " (" + Math.round(R.until - A.now()) + " ms left)");
    if (!r) continue;
    if (r.open === 0) { if (A.checkBody(k, r.body) === null) { R.notes.push(A.shortOf(k) + ": scheme " + s.name); return r; } continue; }
    tried.push({ ...r, name: s.name } as any);
  }
  // the skeleton whose largest open arm is smallest (a split that made progress), then fewest open
  const rank = (f: any) => SCHEME_RANK.findIndex((r) => f.name.startsWith(r));
  tried.sort((a, b) => rank(a) - rank(b) || a.open - b.open || b.closed - a.closed);
  let best: Fill | null = tried[0] ?? null;
  // the best two by rank; then the best of the joint-split schemes (rec, blk) when neither of those is one:
  // they run only after the others failed, so a def that the others prove costs nothing more
  const cands = tried.slice(0, 2);
  const joint = tried.find((t: any) => /^(rec|blk)/.test(t.name));
  if (joint && !cands.includes(joint)) cands.push(joint);
  if (depth < MAX_DEPTH) for (const t of cands) {
    if (A.now() > R.until || t.open > MAX_HELPER_ARMS) break;
    // no arm closed: the split made no progress by the leaf tactics; the constructor steps only
    // (the whole goal as one arm closes nothing by itself: its helpers are the point)
    const r = fillArms(R, k, t.body, depth, [t.closed === 0 && !/^(whole|rec|blk)/.test(String((t as any).name)) ? 2 : 1]);
    if (A.debug()) console.error("[gen2] --ind: " + A.shortOf(k) + " scheme " + (t as any).name + " with helpers: " + (r ? r.open + " open" : "-"));
    if (!r) continue;
    const merged = { ...r, closed: r.closed + t.closed };
    if (r.open === 0 && A.checkBody(k, r.body) === null) { R.notes.push(A.shortOf(k) + ": scheme " + (t as any).name + " with helpers"); return merged; }
    if (!best || merged.closed - merged.open > best.closed - best.open) best = merged; // steps may add holes (a case split): progress = closed less open
  }
  return best;
};

// ---- entry points ----
// floor: the least time the schemes get (IND_FLOOR_MS; the caller lowers it when others wait)
export const indProve = (A: Api, k: string, budget: number, floor = IND_FLOOR_MS): IndOut => {
  const t0 = A.now();
  const R: Run = { A, k, until: t0 + Math.max(budget, floor), helpers: [], notes: [], used: new Set(), nHelpers: 0, failed: new Set(), proven: new Map(), cut: t0 + budget, inverted: new Set(), nFn: 0 };
  A.setJob(A.newJob(k));
  const r = schemesProve(R, k, 0);
  const ms = A.now() - t0;
  // what prints is what checks: the body whole (its arms were checked at their goals)
  if (!r || A.checkBody(k, r.body) !== null) return null;
  // only the helpers the body uses, directly or through another used helper
  const all = R.helpers.sort((a, b) => a.order - b.order);
  const nameOf = (h: { head: string }) => /^def\s+([A-Za-z0-9_.]+)\(/.exec(h.head)?.[1] ?? "";
  const uses = (text: string, nm: string) => new RegExp("(?<![\\w.])" + nm.replace(/\./g, "\\.") + "\\(").test(text);
  // printed in dependency order: a def calls only defs above it (the file check hides the bodies below; gen2's
  // def check sees every body, so it cannot catch a wrong order)
  const keep = new Set<string>();
  const sorted: typeof all = [];
  const visit = (text: string) => {
    for (const h of all) {
      const nm = nameOf(h);
      if (keep.has(nm) || !uses(text, nm)) continue;
      keep.add(nm);
      visit(h.head + "\n" + h.body);
      sorted.push(h);
    }
  };
  visit(r.body);
  const helpers = sorted.map((h) => h.text), defs = sorted.map((h) => ({ head: h.head, body: h.body }));
  const report = "# --ind: " + (r.open === 0 ? "proven" : r.open + " arm(s) open") + " (" + (R.notes.join("; ") || "skeleton") + (helpers.length ? ", " + helpers.length + " helper(s)" : "") + "), " + Math.round(ms) + " ms" +
    r.goals.map((g, i) => "\n# arm " + (i + 1) + " (the " + (i + 1) + ". ?TODO): goal " + A.clipTo(g, 400)).join("");
  return { text: r.body, helpers, defs, open: r.open, closed: r.closed, report, ms };
};

// a goal closed by a constructor clash in a hypothesis, through a predicate with type parameters
// (`%e : maybe.T(A, _); Unit{}`, under Empty.absurd when the goal is not Empty); the proof text or null
const predMemo = new Map<string, { k: string; n: number }[]>();
const predsOf = (A: Api, adt: string): { k: string; n: number }[] => {
  if (predMemo.size === 0) {
    for (const k of Object.keys(A.RAW)) {
      const t = A.RAW[k];
      if (t?.$ !== "Def" || !t.v || t.n < 2 || t.n > 4) continue;
      const o = A.attempt(20000, () => {
        let T: HTerm = t.T;
        let last: HTerm | null = null;
        for (let j = 0; j < t.n; j++) {
          const s = B.term_strip(T) as any;
          if (s.$ !== "All") return null;
          if (j < t.n - 1 && s.q.$ !== "None") return null;
          last = s.A;
          T = s.B(B.Var("_", 1e7 + j));
        }
        const w = B.term_strip(T) as any;
        const la = last ? (B.term_strip(last) as any) : null;
        return w && w.$ === "Typ" && la && la.$ === "ADT" ? la.k : null;
      });
      if (o) { let a = predMemo.get(o); if (!a) predMemo.set(o, a = []); a.push({ k, n: t.n }); }
    }
    if (predMemo.size === 0) predMemo.set("", []);
  }
  return predMemo.get(adt) ?? [];
};
export const indLeaf = (A: Api, g: Goal): string | null => {
  try { return indLeafGo(A, g); } catch (e) { if (e === A.TIMEOUT) throw e; return null; }
};
const indLeafGo = (A: Api, g: Goal): string | null => {
  const contra: number[] = A.contradictory(g);
  if (contra.length === 0) return null;
  const job = A.job();
  const w = A.wnf(g.ty);
  const empty = w && w.$ === "ADT" && A.RAW[w.k]?.c?.length === 0;
  const goal = A.attempt(A.FUEL_NF, () => A.show(A.lower(g.ty, g.d), g.names));
  if (goal === undefined) return null;
  for (const i of contra.slice(0, 2)) {
    const ts = A.hypTargets(g, i);
    const E = ts[ts.length - 1];
    const Tt = B.term_strip(E.T) as any;
    if (Tt.$ !== "ADT") continue;
    const targs = (Tt.x as LTerm[]).filter((x: any) => x.$ !== "Qua" && x.$ !== "Qnt").map((x) => A.show(x, g.names));
    // a Bool clash ({False == True}): Bool.pick as the motive, Empty at the right side, Unit at the left
    if (targs.length === 0 && A.shortOf(Tt.k) === "Bool" && (E as any).b?.$ === "Ctr") {
      const rightTrue = A.shortOf((E as any).b.k) === "True";
      const d = "(%" + g.names[i] + " : Bool.pick(Type, _, " + (rightTrue ? "Empty, Unit" : "Unit, Empty") + "); Unit{})";
      const s = empty ? d : "Empty.absurd(" + goal + ", " + d + ")";
      if (A.tryText(g, s)) return s;
      continue;
    }
    if (targs.length === 0) continue; // no type parameter: gen2's own absurd and ex-falso lemmas cover it
    for (const P of predsOf(A, Tt.k).slice(0, 8)) {
      if ((A.ORDER.get(P.k) ?? Infinity) >= job.order) continue;
      if (targs.length < P.n - 1) continue;
      const pn = B.name_show(job.file, P.k) + "(" + [...targs.slice(targs.length - (P.n - 1)), "_"].join(", ") + ")";
      for (const sym of [false, true]) {
        const e = sym ? "Equal.sym(" + A.show(E.T, g.names) + ", " + A.show(E.a, g.names) + ", " + A.show(E.b, g.names) + ", " + g.names[i] + ")" : g.names[i];
        const d = "(%" + e + " : " + pn + "; Unit{})";
        const s = empty ? d : "Empty.absurd(" + goal + ", " + d + ")";
        if (A.tryText(g, s)) return s;
      }
    }
  }
  return null;
};

// split candidates: a pending parameter of an enumeration type (constructors without fields) that the
// goal does not block on (bool.case's b: only its hypotheses name it), after the others
export const indSplits = (A: Api, n: Goal, out: number[]) => {
  try { indSplitsGo(A, n, out); } catch (e) { if (e === A.TIMEOUT) throw e; }
};
const indSplitsGo = (A: Api, n: Goal, out: number[]) => {
  let g: Goal | null = n;
  for (let j = 0; j < n.pend && g; j++) {
    const t = A.wnf(g.ty);
    if (!t || t.$ !== "All") break;
    if (t.q.$ !== "None" && !out.includes(j)) {
      const adt = adtOf(A, g, t.A);
      if (adt && adt.c.length >= 2 && adt.c.length <= 4 && adt.c.every((c: any) => c.n === 0)) out.push(j);
    }
    g = A.intro(g, g.pnames[0], g.pmany[0]);
  }
};
