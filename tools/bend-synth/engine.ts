// engine.ts: bend-synth's worker. It loads one Bend (bend.ts patched in memory, never on disk), keeps
// books warm, and searches for def bodies: proofs by proof-number search over an AND/OR tree of goals,
// programs by evidence-guided enumeration. Only synth.ts's supervisor talks to it (IPC); it never
// listens on a port and never writes a source file.
//
// THE ONE IDEA: the checker makes the goals. Bend's term_check reaches every ?TODO with its exact
// expected type, context, quantity and lhs (the descent columns); a hook (patch 1) records them. A
// tactic is a fragment of text with ?TODO in it, checked at its goal: the holes it leaves are its
// subgoals, exact by construction, and a recursive call is judged by the same descent rule as the def
// check. Nothing here rebuilds a context by hand. A def check of the target is ~0.1 ms, a local check
// less; a whole-book check (with Base) is ~25 ms, so nothing here checks the whole book in a loop.
//
// The rest is a port of what made gen3 strong, with each trick kept for its principle: goals keyed by
// a bounded normal form (cycles, transpositions), one fact list (hypotheses plus symmetry, injectivity,
// clash, forward steps), a lemma index by conclusion head, rewrites with printed motives, helpers that
// lift a goal over its context (splits inside holes, generalized stuck calls), fuel everywhere.
//
// Programs are not proofs: any value of a data type checks. So a data def is accepted only on
// evidence (the laws that name it and --spec examples, on small inputs), and a partial program is
// refuted early by evaluating it with its holes opaque: a clash that does not depend on a hole is a
// clash for every completion.

import * as fs from "node:fs";
import * as path from "node:path";
import { createHash } from "node:crypto";
import { pathToFileURL } from "node:url";

type Term = any;
let B: Term;

// ---- Bend: the patch, the surface ----
// The bridge object exists before bend.ts evaluates; the patched module reads it once at its top.
const BR: Term = ((globalThis as Term).__bendSynth = { f: Infinity, t: 0, out: () => {}, hole: null });
const PATCHES: Array<[string, string]> = [
  // 1. every ?TODO reached by a check reports its goal
  ['      if (tm.k === "TODO") {\n        return Check(tm, ty, uses_nil());',
    '      if (tm.k === "TODO") {\n        __B2.hole?.({ book, lhs, qt, ty, ctx, d, tm });\n        return Check(tm, ty, uses_nil());'],
  // 2. fuel: each unfolding of a def inside the machine, and 3. each check step
  ['      case "Ref": {\n        const tld = book.tlds[tm.k];',
    '      case "Ref": {\n        if (--__B2.f < 0 || (++__B2.t & 4095) === 0) __B2.out();\n        const tld = book.tlds[tm.k];'],
  ['export function term_check(book: Book, lhs: LHS, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Check {\n',
    'export function term_check(book: Book, lhs: LHS, tm: HTerm, qt: Quant, ty: HTerm, ctx: Ctx, d: number): Check {\n  if (--__B2.f < 0 || (++__B2.t & 4095) === 0) __B2.out();\n'],
  // 4. the parser state has one constructor: a new field in Bend changes this line, and the patch fails
  ['  const p: Parse = { book, dir, str: src, pos: 0, stk: [], idx: new Map(), frs: 0, ann: new Set(), ns, al };',
    '  const p: Parse = parse_new(book, dir, src, ns, al);'],
];
const PRELUDE = "const __B2 = (globalThis as any).__bendSynth;\n";
const EPILOGUE = "\nexport function parse_new(book: Book, dir: string, str: string, ns: string, al: Record<Name, Name>): Parse {\n"
  + "  return { book, dir, str, pos: 0, stk: [], idx: new Map(), frs: 0, ann: new Set(), ns, al };\n}\n";
const SURFACE = ["book_nil", "book_load", "book_adt", "book_valid", "def_check", "term_check", "term_infer", "term_wnf", "term_snf",
  "term_compare", "term_lower", "term_higher", "term_show", "term_key", "term_force", "term_strip", "term_unapply", "term_apply",
  "parse_new", "parse_push", "parse_block", "parse_body", "parse_tele", "parse_skip", "parse_fail", "parse_book", "body_flatten",
  "ctx_nil", "ctx_bind", "ctx_scope", "pmap_get", "pmap_to_array", "list_set", "quant_join", "quant_dem", "quant_add", "quant_show",
  "name_show", "lit_step", "term_descend", "u32_from_term", "lhs_ext", "tele_fill", "tele_head", "tele_unbind", "err_show", "Var", "Ref", "App", "Ctr",
  "ADT", "Lit", "Eql", "All", "Lam", "Hol", "Typ", "Qua", "None", "Lone", "Many"];

export const patchedSource = (dir: string): string => {
  let src = fs.readFileSync(path.join(dir, "bend.ts"), "utf8").replaceAll("\r\n", "\n");
  for (const [from, to] of PATCHES) {
    if (src.split(from).length !== 2) throw new Error("Bend drift: bend-synth expects exactly one\n" + from.slice(0, 160) + "\nin " + path.join(dir, "bend.ts"));
    src = src.replace(from, to);
  }
  return PRELUDE + src + EPILOGUE;
};
const loadBend = async (dir: string) => {
  const file = path.join(dir, "bend.ts");
  const real = fs.realpathSync(file).toLowerCase();
  const contents = patchedSource(dir);
  Bun.plugin({ name: "bend-synth", setup(b) {
    b.onLoad({ filter: /[\\/]bend\.ts$/ }, (a) => (fs.realpathSync(a.path).toLowerCase() === real ? { loader: "ts", contents } : undefined) as Term);
  } });
  B = await import(pathToFileURL(file).href);
  const missing = SURFACE.filter((k) => typeof B[k] !== "function");
  if (missing.length) throw new Error("Bend drift: bend.ts no longer exports " + missing.join(", "));
};

// ---- fuel, time, memory ----
class Stop { constructor(readonly why: string) {} }
const OOF = new Stop("out of fuel"), TIMEOUT = new Stop("out of time"), LIN = new Stop("a binder used beyond its quantity");
const FUEL_CHECK = 300000, FUEL_NF = 100000, FUEL_FINAL = 50000000, FUEL_PARTIAL = 5000000, FUEL_NFS = 40000, NF_NODES = 3000;
const META = 1 << 20, FRESH = 1e7;
let deadline = Infinity, jobDeadline = Infinity, memCap = Infinity, overMem = false;
BR.out = () => {
  if (BR.f < 0) throw OOF;
  if (performance.now() > deadline) throw TIMEOUT;
  // past the share: collect first (what counts is what is live), then stop
  if ((BR.t & 0xffff) === 0 && process.memoryUsage.rss() > memCap) { Bun.gc(true); if (process.memoryUsage.rss() > memCap) { overMem = true; throw TIMEOUT; } }
};
// f under at most n units, taken from the units left (limits nest); what it used is charged to the caller
const withFuel = <T>(n: number, f: () => T): T => {
  const old = BR.f, start = Math.min(n, old);
  BR.f = start;
  try { return f(); } finally { BR.f = old - Math.max(0, Math.min(start, start - BR.f)); }
};
// f with its own n units: a memo computed once per book must not depend on the caller's fuel
const withOwnFuel = <T>(n: number, f: () => T): T => {
  const old = BR.f;
  BR.f = n;
  try { return f(); } finally { BR.f = old; }
};
let lastErr: Term = null;
// f, or undefined when it runs out of fuel, overflows or Bend refuses (lastErr keeps why); time stops all
const attempt = <T>(n: number, f: () => T): T | undefined => {
  try { return withFuel(n, f); } catch (e) { if (e === TIMEOUT) throw e; lastErr = e; return undefined; }
};
const late = () => performance.now() > deadline || overMem;
// the worker's own memory, between steps (Bend's fuel ticks see only Bend's work): the caches go first;
// a slice still over its share stops with what it has, before the OS limit kills the worker
const memoryGuard = (): boolean => {
  if (!(memCap < Infinity) || process.memoryUsage.rss() < memCap * 0.8) return false;
  if (BK) BK.nfs.clear();
  if (S) S.facts.clear();
  nfObj = new WeakMap(); patMemo = new WeakMap(); smemo.clear(); nfHeld = 0; Bun.gc(true);
  if (process.memoryUsage.rss() < memCap * 0.9) return false;
  overMem = true;
  return true;
};

// ---- terms (lowered: de Bruijn levels) ----
let BK: Book;
const canon = (t: Term): Term => {
  switch (t.$) {
    case "Ctr": {
      const x = t.x.map(canon);
      if (t.k === "Zero" && x.length === 0) return B.Lit("Nat", 0);
      if (t.k === "Succ" && x.length === 1 && x[0].$ === "Lit" && x[0].k === "Nat") return B.Lit("Nat", x[0].v + 1);
      const c = B.Ctr(t.k, x);
      if (t.k === "U32") { const u = B.u32_from_term(c); if (u !== null) return B.Lit("U32", u); }
      return c;
    }
    case "App": return B.App(canon(t.f), canon(t.x));
    case "Eql": return B.Eql(canon(t.a), canon(t.b), canon(t.T));
    case "ADT": return B.ADT(t.k, t.x.map(canon), undefined, t.r);
    case "All": return B.All(t.q, t.k, t.i, canon(t.A), canon(t.B));
    case "Lam": return B.Lam(t.k, t.i, canon(t.f), undefined, t.q);
    case "Ann": return canon(t.x);
    case "Var": return t.v !== undefined && t.i >= 0 ? B.Var(t.k, t.i) : t;
    case "Ref": { const a = BK.raw[t.k]; return a?.$ === "ADT" && a.n === 0 ? B.ADT(t.k, [], undefined, []) : t; }
    default: return t;
  }
};
// term_lower with a node budget: a term is a graph, its tree can be exponential. cut: "…" past it
const BIG = new Stop("a term too large");
const lowerB = (h: Term, d: number, b: { n: number }, cut = false): Term => {
  if (--b.n < 0) { if (cut) return B.Ref("…"); throw BIG; }
  const t = B.term_force(h);
  const go = (x: Term, dd = d) => lowerB(x, dd, b, cut);
  if (cut && /^(Let|Sub|Mat|Rwt)$/.test(t.$)) return B.Ref("…");
  switch (t.$) {
    case "Let": { const xs = t.k.map((k: string, j: number) => B.Var(k, d + j)); return B.Let(t.k, xs.map((_: Term, j: number) => d + j), t.v.map((v: Term) => go(v)), go(t.f(xs), d + t.k.length), t.s, t.q); }
    case "Typ": return B.Typ(go(t.g), t.s);
    case "Min": return B.Min(go(t.a), go(t.b), t.s);
    case "All": return B.All(t.q, t.k, d, go(t.A), go(t.B(B.Var(t.k, d)), d + 1), t.s);
    case "Lam": return B.Lam(t.k, d, go(t.f(B.Var(t.k, d)), d + 1), t.s, t.q);
    case "App": return B.App(go(t.f), go(t.x), t.s);
    case "ADT": return B.ADT(t.k, t.x.map((x: Term) => go(x)), t.s, t.r);
    case "Ctr": return B.Ctr(t.k, t.x.map((x: Term) => go(x)), t.s);
    case "Mat": return B.Mat(t.k, go(t.h), go(t.m), t.s);
    case "Eql": return B.Eql(go(t.a), go(t.b), go(t.T), t.s);
    case "Rwt": return B.Rwt(go(t.e), go(t.p), go(t.f), t.s);
    case "Ann": return B.Ann(go(t.x), go(t.T), t.s);
    default: return t;
  }
};
const lower0 = (h: Term, d: number): Term => lowerB(h, d, { n: 20000 });
const lower = (h: Term, d: number): Term => canon(lower0(h, d));

// structural hashes (52 bits, memoized per node): keys never compare term strings
const hmemo = new WeakMap<object, number>();
const smemo = new Map<string, number>();
let ha = 0, hb = 0;
const tok = (x: number) => { ha = Math.imul(ha ^ x, 16777619); hb = Math.imul(hb ^ x, 0x5bd1e995) ^ (hb >>> 13); };
const tokH = (h: number) => { tok(h % 4294967296); tok(Math.floor(h / 4294967296)); };
const strH = (s: string): number => {
  let r = smemo.get(s);
  if (r === undefined) {
    let a = 2166136261;
    for (let i = 0; i < s.length; i++) a = Math.imul(a ^ s.charCodeAt(i), 16777619);
    r = a >>> 0;
    if (s.length <= 64) smemo.set(s, r);
  }
  return r;
};
const H = (t: Term): number => {
  const m = hmemo.get(t);
  if (m !== undefined) return m;
  const kids: number[] = [];
  let tag = 0, s = "";
  switch (t.$) {
    case "Var": tag = 1; kids.push(t.i); break;
    case "Ref": tag = 2; s = t.k; break;
    case "App": tag = 3; kids.push(H(t.f), H(t.x)); break;
    case "Ctr": tag = 4; s = t.k; for (const x of t.x) kids.push(H(x)); break;
    case "ADT": tag = 5; s = t.k + "-" + t.r.join(","); for (const x of t.x) kids.push(H(x)); break;
    case "Lit": tag = 6; s = t.k + ":" + String(t.v); break;
    case "Eql": tag = 7; kids.push(H(t.a), H(t.b), H(t.T)); break;
    case "All": tag = 8; s = t.q.$; kids.push(t.i, H(t.A), H(t.B)); break;
    case "Lam": tag = 9; kids.push(t.i, H(t.f)); break;
    default: tag = 10; s = B.term_key(t);
  }
  ha = 2166136261; hb = 0x9747b28c;
  tok(tag);
  if (s) tok(strH(s));
  for (const k of kids) tokH(k);
  const r = (ha >>> 0) * 1048576 + ((hb >>> 0) & 0xfffff);
  hmemo.set(t, r);
  return r;
};
const mixH = (...xs: number[]): number => { ha = 2166136261; hb = 0x9747b28c; for (const x of xs) tokH(x); return (ha >>> 0) * 1048576 + ((hb >>> 0) & 0xfffff); };
const NO_KIDS: Term[] = [];
const kidsT = (t: Term): Term[] => {
  switch (t.$) {
    case "App": return [t.f, t.x];
    case "Ctr": case "ADT": return t.x;
    case "Eql": return [t.a, t.b, t.T];
    case "All": return [t.A, t.B];
    case "Lam": return [t.f];
    case "Typ": return [t.g];
    default: return NO_KIDS;
  }
};
const some = (t0: Term, test: (t: Term) => boolean): boolean => {
  const st: Term[] = [t0];
  while (st.length) { const t = st.pop(); if (test(t)) return true; st.push(...kidsT(t)); }
  return false;
};
const size = (t0: Term, cap = 100000): number => { let n = 0; some(t0, () => ++n > cap); return n; };
const varsOf = (t0: Term, out: Set<number>) => { some(t0, (t) => { if (t.$ === "Var" && t.i < META) out.add(t.i); return false; }); return out; };
const hasMeta = (t0: Term): boolean => some(t0, (t) => t.$ === "Var" && t.i >= META);
const closedBelow = (t: Term, d: number, bound: number[] = []): boolean => {
  switch (t.$) {
    case "Var": return t.i < d || bound.includes(t.i);
    case "App": return closedBelow(t.f, d, bound) && closedBelow(t.x, d, bound);
    case "Ctr": case "ADT": return t.x.every((x: Term) => closedBelow(x, d, bound));
    case "Eql": return closedBelow(t.a, d, bound) && closedBelow(t.b, d, bound) && closedBelow(t.T, d, bound);
    case "All": return closedBelow(t.A, d, bound) && closedBelow(t.B, d, [...bound, t.i]);
    case "Lam": return closedBelow(t.f, d, [...bound, t.i]);
    case "Let": case "Mat": case "Use": return false;
    default: return true;
  }
};
// rewrite walks enter values (call arguments, equation sides, lambda bodies), never an equation's type
const replace = (t: Term, h: number, by: Term, at = -1, seen = { n: 0 }): Term => {
  if (H(t) === h) return at < 0 || seen.n++ === at ? by : t;
  const go = (x: Term) => replace(x, h, by, at, seen);
  switch (t.$) {
    case "App": { const f = go(t.f); return B.App(f, go(t.x)); }
    case "Ctr": return B.Ctr(t.k, t.x.map(go));
    case "Eql": { const a = go(t.a); return B.Eql(a, go(t.b), t.T); }
    case "ADT": return B.ADT(t.k, t.x.map(go), undefined, t.r);
    case "Lam": return B.Lam(t.k, t.i, go(t.f), undefined, t.q);
    default: return t;
  }
};
const occurrences = (t: Term, h: number): number => {
  if (H(t) === h) return 1;
  switch (t.$) {
    case "App": return occurrences(t.f, h) + occurrences(t.x, h);
    case "Ctr": case "ADT": return t.x.reduce((s: number, x: Term) => s + occurrences(x, h), 0);
    case "Eql": return occurrences(t.a, h) + occurrences(t.b, h);
    case "Lam": return occurrences(t.f, h);
    default: return 0;
  }
};
const contains = (t: Term, h: number): boolean => occurrences(t, h) > 0;
const subterms = (t: Term, out: Map<number, Term>, d = Infinity) => {
  if (!(d < Infinity) || closedBelow(t, d)) out.set(H(t), t);
  switch (t.$) {
    case "Lam": subterms(t.f, out, Math.min(d, t.i)); return;
    case "App": { const [h, xs] = B.term_unapply(t); if (h.$ !== "Ref") subterms(t.f, out, d); xs.forEach((x: Term) => subterms(x, out, d)); break; }
    case "Ctr": case "ADT": t.x.forEach((x: Term) => subterms(x, out, d)); break;
    case "Eql": subterms(t.a, out, d); subterms(t.b, out, d); break;
  }
};
const litStep = (t: Term): Term => (t.$ === "Lit" && (t.k === "Nat" || t.k === "U32") ? B.lit_step(t) : null);
// first-order matching of p (metavariables >= META) against t; sol filled in place
const match = (p: Term, t: Term, sol: (Term | null)[], d: number): boolean => {
  if (p.$ === "Var" && p.i >= META) {
    const s = sol[p.i - META];
    if (s) return H(s) === H(t);
    if (!closedBelow(t, d)) return false;
    sol[p.i - META] = t;
    return true;
  }
  switch (p.$) {
    case "Var": return t.$ === "Var" && t.i === p.i;
    case "Ref": return t.$ === "Ref" && t.k === p.k;
    case "App": return t.$ === "App" && match(p.f, t.f, sol, d) && match(p.x, t.x, sol, d);
    case "Ctr": {
      const u = t.$ === "Lit" ? litStep(t) : t;
      return !!u && u.$ === "Ctr" && u.k === p.k && u.x.length === p.x.length && p.x.every((x: Term, i: number) => match(x, u.x[i], sol, d));
    }
    case "Lit": {
      if (t.$ === "Lit") return t.k === p.k && t.v === p.v;
      const s = t.$ === "Ctr" ? litStep(p) : null;
      return s !== null && match(s, t, sol, d);
    }
    case "Eql": {
      if (t.$ !== "Eql" || !match(p.a, t.a, sol, d) || !match(p.b, t.b, sol, d)) return false;
      const s2 = sol.slice();
      if (match(p.T, t.T, s2, d)) for (let i = 0; i < sol.length; i++) sol[i] = s2[i];
      return true;
    }
    case "ADT": return t.$ === "ADT" && t.k === p.k && t.x.length === p.x.length && t.r.join() === p.r.join() && p.x.every((x: Term, i: number) => match(x, t.x[i], sol, d));
    case "All": return t.$ === "All" && t.q.$ === p.q.$ && match(p.A, t.A, sol, d) && match(p.B, t.B, sol, d);
    case "Lam": return t.$ === "Lam" && match(p.f, t.f, sol, d);
    case "Typ": return t.$ === "Typ" && match(p.g, t.g, sol, d);
    default: return H(p) === H(t);
  }
};
const headKey = (t: Term): string => {
  switch (t.$) {
    case "App": { const [h] = B.term_unapply(t); return h.$ === "Ref" ? "R:" + h.k : h.$ === "Var" && h.i >= META ? "*" : "V"; }
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

// ---- normal forms ----
// bounded strong normal form: stuck calls keep their arguments normalized, a closed constant unfolds only
// when tiny, past the node budget the raw term stays. atoms: a call that decides a branch (a def whose
// result is an enumeration, on small arguments) stays folded, so a goal reads as the source does
const wnf = (h: Term): Term => attempt(FUEL_NF, () => B.term_wnf(BK.book, h));
type NfBudget = { n: number; atoms: boolean };
const enumDef = (k: string): boolean => {
  let r = BK.enums.get(k);
  if (r === undefined) {
    const t = BK.raw[k];
    r = withOwnFuel(40000, () => {
      const o = t?.$ === "Def" && t.n > 0 ? attempt(20000, () => openMeta(t.T, t.n)) : null;
      const w = o && wnf(o.concl);
      const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
      return adt?.$ === "ADT" && adt.c.length >= 2 && adt.c.length <= 8 && adt.c.every((c: Term) => c.n === 0);
    }) === true;
    BK.enums.set(k, r);
  }
  return r;
};
const isAtom = (s: Term, d: number): boolean => {
  const [hd, xs] = B.term_unapply(s);
  const f = B.term_strip(hd);
  return f.$ === "Ref" && xs.length > 0 && enumDef(f.k) && xs.every((x: Term) => attempt(FUEL_NF, () => lowerB(x, d, { n: 16 })) !== undefined);
};
const wnfShared = (h: Term): Term => {
  if (BR.f <= 0) return undefined;
  try { return B.term_wnf(BK.book, h); } catch (e) { if (e === TIMEOUT) throw e; return undefined; }
};
const nfGo = (h: Term, d: number, b: NfBudget): Term => {
  b.n--;
  const s = B.term_strip(h);
  if (!(b.atoms && s.$ === "App" && isAtom(s, d))) return nfStep(h, s, d, b);
  const inner = nfStep(h, s, d, b);
  const decides = (t: Term) => { if (t === inner || t.$ !== "App") return false; const f = B.term_unapply(t)[0]; return f.$ === "Ref" && enumDef(f.k); };
  if (some(inner, decides)) return inner;
  const [hd, xs] = B.term_unapply(s);
  return xs.reduce((r: Term, x: Term) => B.App(r, nfArg(x, d, b)), B.Ref(B.term_strip(hd).k));
};
const nfStep = (h: Term, s: Term, d: number, b: NfBudget): Term => {
  const w = wnfShared(h) ?? s;
  switch (w.$) {
    case "App": {
      const [hd, xs] = B.term_unapply(w);
      const f = B.term_strip(hd);
      return f.$ === "Ref" ? xs.reduce((r: Term, x: Term) => B.App(r, nfArg(x, d, b)), B.Ref(f.k)) : lower0(w, d);
    }
    case "Ctr": return B.Ctr(w.k, w.x.map((x: Term) => nfArg(x, d, b)));
    case "Eql": return B.Eql(nfArg(w.a, d, b), nfArg(w.b, d, b), lower0(w.T, d));
    default: return lower0(w, d);
  }
};
const nfArg = (x: Term, d: number, b: NfBudget): Term => {
  if (b.n <= 0) return lower0(x, d);
  const s = B.term_strip(x);
  const t = s.$ === "Ref" ? BK.raw[s.k] : null;
  if (t?.$ === "Def" && t.n === 0 && t.v !== null) {
    const lb = { n: 24, atoms: b.atoms };
    const r = nfGo(s, d, lb);
    return lb.n <= 0 ? B.Ref(s.k) : r;
  }
  return nfGo(x, d, b);
};
let nfObj = new WeakMap<object, Map<number, Term>>();
let nfHeld = 0;
const nf = (h: Term, d: number, atoms = false, cap = FUEL_NFS): Term => {
  const sub = mixH(d, atoms ? 1 : 0, cap);
  const byObj = typeof h === "object" && h ? nfObj.get(h) : undefined;
  if (byObj?.has(sub)) return byObj.get(sub);
  const whole = BR.f >= cap;
  const raw = attempt(FUEL_NF, () => lower0(h, d));
  if (!raw) return undefined;
  const k = mixH(H(raw), d, atoms ? 1 : 0, cap);
  let r = BK.nfs.get(k);
  if (r === undefined && !BK.nfs.has(k)) {
    r = attempt(cap, () => canon(nfGo(h, d, { n: NF_NODES, atoms })));
    if (!whole) return r;
    // the cache is bounded by the terms it holds, not by how many
    nfHeld += r ? size(r, 20000) : 1;
    if (nfHeld > 1500000) { BK.nfs.clear(); nfHeld = 0; }
    BK.nfs.set(k, r);
  }
  if (whole && typeof h === "object" && h) { const m = byObj ?? new Map(); m.set(sub, r); if (!byObj) nfObj.set(h, m); }
  return r;
};
// the parameter a def's body matches first, and every parameter its case tree matches
const strictOf = (k: string): number | null => {
  if (BK.strict.has(k)) return BK.strict.get(k)!;
  let r: number | null = null;
  const t0 = BK.raw[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let t: Term = t0.v;
    for (let j = 0; j <= t0.n; j++) {
      t = B.term_strip(t);
      if (t.$ === "Lam") { t = t.f(B.Var("_", FRESH + j)); continue; }
      if ((t.$ === "Mat" || t.$ === "Efq") && j < t0.n) r = j;
      break;
    }
  }
  BK.strict.set(k, r);
  return r;
};
const matchedOf = (k: string): Set<number> => {
  let r = BK.matched.get(k);
  if (r) return r;
  const out = new Set<number>();
  const t0 = BK.raw[k];
  if (t0?.$ === "Def" && t0.v !== null) {
    let budget = 400;
    const walk = (t: Term, q: number[]) => {
      if (--budget < 0) return;
      t = B.term_strip(t);
      if (t.$ === "Lam") { walk(t.f(B.Var("_", FRESH)), q.slice(1)); return; }
      if (t.$ !== "Mat") return;
      if (q[0] !== undefined && q[0] >= 0) out.add(q[0]);
      const ctr = BK.raw[t.k] === undefined ? BK.book.ctrs[t.k] : null;
      walk(t.h, [...new Array(ctr ? ctr.n : 0).fill(-1), ...q.slice(1)]);
      walk(t.m, q);
    };
    try { withOwnFuel(20000, () => walk(t0.v, Array.from({ length: t0.n }, (_, i) => i))); } catch (e) { if (e === TIMEOUT) throw e; }
  }
  BK.matched.set(k, out);
  return out;
};
// what blocks evaluation: the strict argument of a stuck call, a variable or a stuck call there
const blockers = (t: Term, out: Term[]) => {
  switch (t.$) {
    case "App": {
      const [h, xs] = B.term_unapply(t);
      if (h.$ === "Ref") {
        const j = strictOf(h.k);
        const blk = (a: Term) => a.$ === "Var" || (a.$ === "App" && B.term_unapply(a)[0].$ === "Ref");
        const ms = j !== null && j < xs.length && blk(xs[j]) ? new Set([j]) : matchedOf(h.k);
        xs.forEach((a: Term, i: number) => {
          if (!ms.has(i)) return;
          if (blk(a)) out.push(a);
          else if (a.$ === "Ctr") for (const f of a.x) if (f.$ === "Var") out.push(f);
        });
      }
      xs.forEach((x: Term) => blockers(x, out));
      break;
    }
    case "Ctr": case "ADT": t.x.forEach((x: Term) => blockers(x, out)); break;
    case "Eql": blockers(t.a, out); blockers(t.b, out); break;
  }
};

// ---- propositions ----
// a fact: an equation, Empty or Unit, a one-constructor type of facts, a function to a fact
const isProp = (h: Term, n = 0): boolean => {
  const w = wnf(h);
  if (!w) return true;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": {
      const t = BK.raw[w.k];
      if (t?.$ !== "ADT") return false;
      if (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)) return true;
      // several constructors (Or<A, B>): a datatype of facts, judged by its parameters
      if (t.c.length > 1) return isPropType(w, n);
      return w.x.length > 0 && n < 20 && w.x.every((a: Term) => {
        const wa = wnf(a);
        if (!wa || wa.$ === "Qua" || wa.$ === "Qnt") return true;
        return wa.$ === "Lam" ? isProp(wa.f(B.Var("_", FRESH + n)), n + 1) : isProp(wa, n + 1);
      });
    }
    case "All": return n < 20 ? isProp(w.B(B.Var("_", FRESH + n)), n + 1) : true;
    // a stuck call of a predicate def (LE(a, b), Sorted.from(lo, xs)) is a proposition too
    case "App": case "Ref": return isPropType(w, n);
    default: return false;
  }
};
// also a stuck call of a def whose every case gives one (LE(a, b), Sorted.from(lo, xs)), or a datatype
// of facts (Or<A, B>, A & B). A predicate def is judged once, coinductively: inside its own analysis a
// recursive call (LE(a1, b1)) counts as a proposition, as a recursive type would
const predDefs = new Map<string, boolean | "pending">();
const isPropType = (h: Term, n = 0): boolean => {
  if (n > 12) return false;
  const w = wnf(h);
  if (!w) return false;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": {
      const t = BK.raw[w.k];
      if (t?.$ !== "ADT") return false;
      if (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)) return true;
      if (t.c.length > 4 || !w.x.length) return false;
      // a quantity parameter (Sigma<a, b, ..>) says nothing; a family parameter (x => P(x)) by its body
      let props = 0;
      for (const a of w.x) {
        const wa = wnf(a);
        if (!wa) return false;
        if (wa.$ === "Qua" || wa.$ === "Qnt" || wa.$ === "Min") continue;
        if (!(wa.$ === "Lam" ? isPropType(wa.f(B.Var("_", FRESH + 100 + n)), n + 1) : isPropType(a, n + 1))) return false;
        props++;
      }
      return props > 0;
    }
    case "All": return isPropType(w.B(B.Var("_", FRESH + n)), n + 1);
    case "Ref": case "App": {
      const f = B.term_strip(B.term_unapply(w)[0]);
      if (f.$ !== "Ref") return false;
      const t = BK.raw[f.k];
      if (t?.$ !== "Def" || t.v === null) return false;
      const memo = predDefs.get(f.k);
      if (memo !== undefined) return memo !== false;
      predDefs.set(f.k, "pending");
      const leaves: Term[] = [];
      let budget = 64;
      const walk = (x: Term) => {
        if (--budget < 0) return;
        x = B.term_strip(x);
        if (x.$ === "Lam") walk(x.f(B.Var("_", FRESH + 50 + budget)));
        else if (x.$ === "Mat") { walk(x.h); walk(x.m); }
        else if (x.$ !== "Efq") leaves.push(x);
      };
      // a verdict is kept only when it completes: running out of fuel is no answer
      try {
        walk(t.v);
        const r = budget >= 0 && leaves.length > 0 && leaves.every((l) => isPropType(l, n + 1));
        predDefs.set(f.k, r);
        return r;
      } catch (e) { predDefs.delete(f.k); throw e; }
    }
    default: return false;
  }
};
const isPrem = (A: Term, d: number): boolean => {
  if (isProp(A)) return true;
  if (attempt(FUEL_NF, () => hasMeta(lower(A, d))) !== true) return false;
  const w = wnf(A);
  return !!w && w.$ !== "Typ" && w.$ !== "Qnt" && w.$ !== "Qua";
};
type Dom = { q: Term; k: string; A: Term };
const asAll = (t: Term): Term => {
  const s = B.term_strip(t);
  if (s.$ === "All") return s;
  const w = wnf(t);
  return w?.$ === "All" ? w : null;
};
const arity = (T: Term, n: number): number => {
  let t = T, k = 0;
  for (; k < n + 8; k++) { const s = asAll(t); if (!s) break; t = s.B(B.Var("_", META + k)); }
  return Math.max(k, n);
};
const openMeta = (T: Term, n: number, sol: (Term | null)[] = []): { doms: Dom[]; concl: Term } | null => {
  let t = T;
  const doms: Dom[] = [];
  for (let j = 0; j < n; j++) {
    const s = asAll(t);
    if (!s) return null;
    doms.push({ q: s.q, k: s.k, A: s.A });
    t = s.B(sol[j] ?? B.Var("?" + j, META + j));
  }
  return { doms, concl: t };
};
// k's result is a sort (Type, Data, a kind): a type definition, not a program to search
const returnsSort = (k: string): boolean => {
  const t = BK.raw[k];
  const o = t?.$ === "Def" ? attempt(FUEL_NF, () => openMeta(t.T, t.n)) : null;
  const w = o && wnf(o.concl);
  return !!w && (w.$ === "Typ" || w.$ === "Qnt");
};
// k's result (after its parameters) is a proposition: proven, not synthesized
const isLemmaType = (k: string): boolean => {
  const t = BK.raw[k];
  const o = t?.$ === "Def" ? withOwnFuel(FUEL_NF * 2, () => attempt(FUEL_NF * 2, () => openMeta(t.T, t.n))) : null;
  return !!o && withOwnFuel(FUEL_NF * 4, () => attempt(FUEL_NF * 4, () => isPropType(o.concl) || (!!wnf(o.concl) && isProp(o.concl)))) === true;
};

// ---- books ----
type Lemma = { k: string; order: number; n: number; np: number; guarded: boolean };
type Src = { file: string; header: string; body: string; bodyLine: number };
type Book = {
  entry: string; top: string; book: Term; raw: Record<string, Term>; n0: number; order: Map<string, number>; files: Map<string, Term>;
  texts: Map<string, string>; src: Map<string, Src | null>; seen: string[]; stamp: string; hashes: Record<string, string>;
  nfs: Map<number, Term>; enums: Map<string, boolean>; strict: Map<string, number | null>; matched: Map<string, Set<number>>;
  apply: Map<string, Lemma[]>; rw: Map<string, { L: Lemma; side: 0 | 1 }[]>; fwd: Map<string, { L: Lemma; j: number }[]>;
  zero: Map<Term, RegExp | null>; hidden: Map<string, Term>; temps: string[];
};
const books = new Map<string, Book>();
let baseBook: Term = null;
const stampOf = (files: string[]) => files.map((f) => { try { const s = fs.statSync(f); return s.mtimeMs + ":" + s.size; } catch { return "-"; } }).join(",");
const DEF_LINE = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/;
const nsOf = (k: string) => (k.includes(":") ? k.slice(0, k.indexOf(":")) : "");
const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
const lineOf = (str: string, at: number) => str.slice(0, at).split("\n").length;
const todoAt = (body: string): number[] => {
  const out: number[] = [];
  let at = 0;
  for (const line of body.split("\n")) {
    const code = line.replace(/#.*$/, "");
    for (let i = code.indexOf("?TODO"); i >= 0; i = code.indexOf("?TODO", i + 1)) out.push(at + i);
    at += line.length + 1;
  }
  return out;
};
const sha = (s: string) => createHash("sha256").update(s).digest("hex").slice(0, 16);
const spanFile = (t: Term, n = 0): Term => {
  if (!t || typeof t !== "object" || n > 6) return undefined;
  if (t.s?.file) return t.s.file;
  for (const k of ["f", "x", "A", "h", "a"]) { const r = typeof t[k] === "object" ? spanFile(t[k], n + 1) : undefined; if (r) return r; }
  return undefined;
};
const loadBook = async (file: string): Promise<Book | string> => {
  if (!fs.existsSync(file) || !fs.statSync(file).isFile()) return "no such file: " + file;
  const entry = B.path_slash ? B.path_slash(fs.realpathSync(file)) : fs.realpathSync(file).replaceAll("\\", "/");
  const had = books.get(entry);
  if (had && stampOf(had.seen) === had.stamp) { books.delete(entry); books.set(entry, had); return had; }
  if (!baseBook) {
    baseBook = B.book_nil();
    await B.book_load(baseBook, B.BASE_BEND, "", new Map());
  }
  // Base once per worker: each book starts from a copy of its declarations (bend's own book_seed)
  const book = B.book_nil();
  for (const k of Object.keys(baseBook.tlds)) book.tlds[k] = { ...baseBook.tlds[k] };
  Object.assign(book.ctrs, baseBook.ctrs);
  for (const k of Object.keys(baseBook.tmps)) book.tmps[k] = new Map(baseBook.tmps[k]);
  book.order.push(...baseBook.order);
  const seen = new Map<string, string | null>([[B.BASE_BEND, ""]]);
  const top = entry.slice(0, entry.lastIndexOf("/") + 1);
  let n0: number;
  try { n0 = await B.book_load(book, entry, "", seen, undefined, top); } catch (e) { return "the file does not load:\n" + errText(e); }
  const raw: Record<string, Term> = book.tlds;
  const order = new Map<string, number>();
  book.order.forEach((k: string, i: number) => order.set(k, i));
  const files = new Map<string, Term>();
  for (const k of book.order) {
    const t = raw[k];
    const f = t?.$ === "Def" ? spanFile(t.v) ?? spanFile(t.T) : t?.$ === "ADT" ? spanFile(t.T) : undefined;
    if (f) files.set(k, f);
  }
  const deps = [...seen.keys()].filter((f) => f !== B.BASE_BEND);
  const texts = new Map<string, string>(), hashes: Record<string, string> = {};
  for (const f of deps) { try { const t = fs.readFileSync(f, "utf8"); texts.set(f, t); hashes[f] = sha(t); } catch { /* gone */ } }
  const L: Book = {
    entry, top, book, raw, n0, order, files, texts, src: new Map(), seen: deps, stamp: "", hashes,
    nfs: new Map(), enums: new Map(), strict: new Map(), matched: new Map(), apply: new Map(), rw: new Map(), fwd: new Map(),
    zero: new Map(), hidden: new Map(), temps: [],
  };
  L.stamp = stampOf(L.seen);
  BK = L;
  predDefs.clear();
  // a def with a ?TODO in its source is opaque: computing through a hole makes any two calls equal
  for (const k of book.order) if (raw[k]?.$ === "Def" && raw[k].v !== null && !raw[k].b && isOpen(k)) raw[k] = { ...raw[k], v: null };
  withOwnFuel(FUEL_FINAL, () => { try { buildIndex(); } catch (e) { if (e === TIMEOUT) throw e; } });
  books.set(entry, L);
  if (books.size > 3) books.delete(books.keys().next().value!);
  return L;
};
const fileOfDef = (k: string): string => ((BK.order.get(k) ?? -1) >= BK.n0 || nsOf(k) === "" ? BK.entry : BK.top + nsOf(k) + ".bend");
const fileText = (f: string): string => {
  let t = BK.texts.get(f);
  if (t === undefined) { t = fs.existsSync(f) ? fs.readFileSync(f, "utf8") : ""; BK.texts.set(f, t); }
  return t;
};
const brackets = (l: string) => { let b = 0; for (const ch of l.replace(/#.*$/, "")) { if ("([{".includes(ch)) b++; else if (")]}".includes(ch)) b--; } return b; };
const defLine = (lines: string[], name: string): number => {
  let alt = -1;
  for (let i = 0; i < lines.length; i++) {
    const m = DEF_LINE.exec(lines[i]);
    if (!m) continue;
    if (m[1] === name) return i;
    if (alt < 0 && m[1].slice(m[1].indexOf(".") + 1) === name) alt = i;
  }
  return alt;
};
const defSrc = (k: string): Src | null => {
  if (BK.src.has(k)) return BK.src.get(k)!;
  const file = fileOfDef(k);
  const lines = fileText(file).split("\n");
  const li = defLine(lines, shortOf(k));
  let res: Src | null = null;
  if (li >= 0) {
    let he = li;
    for (let depth = 0; he < lines.length; he++) {
      depth += brackets(lines[he]);
      if (depth <= 0 && /:\s*$/.test(lines[he].replace(/#.*$/, ""))) break;
    }
    let be = he + 1;
    for (let bd = 0; be < lines.length && (lines[be].startsWith(" ") || lines[be].trim() === "" || bd > 0); be++) bd += brackets(lines[be]);
    while (be > he + 1 && (lines[be - 1].trim() === "" || lines[be - 1].trim().startsWith("#"))) be--;
    res = { file, header: lines.slice(li, he + 1).join("\n"), body: lines.slice(he + 1, be).join("\n"), bodyLine: he + 1 };
  }
  BK.src.set(k, res);
  return res;
};
const openNames = new Map<string, Set<string>>();
const isOpen = (k: string): boolean => {
  const source = BK.files.get(k)?.str;
  if (!source) return false;
  let names = openNames.get(source);
  if (!names) {
    names = new Set();
    let current = "";
    for (const line of source.split("\n")) {
      const def = DEF_LINE.exec(line);
      if (def) current = def[1];
      else if (/^\S/.test(line)) current = "";
      else if (current && todoAt(line).length) { names.add(current); names.add(current.slice(current.indexOf(".") + 1)); }
    }
    openNames.set(source, names);
  }
  return names.has(shortOf(k));
};
const ownDefs = (): string[] => [...new Set<string>(BK.book.order.slice(BK.n0))].filter((k) => BK.raw[k]?.$ === "Def" && !k.includes("~") && !BK.raw[k].b);
const resolveDef = (nm: string): string | string[] => {
  const own = ownDefs();
  const exact = own.filter((x) => shortOf(x) === nm || x === nm);
  const local = nm.includes(".") ? nm.slice(nm.indexOf(".") + 1) : nm;
  const m = exact.length ? exact : own.filter((x) => shortOf(x) === local || shortOf(x).endsWith("." + nm));
  return m.length === 1 ? m[0] : m.map(shortOf);
};

// ---- the lemma index: by the head of each conclusion, of each equation side, of each premise ----
const buildIndex = () => {
  BK.apply = new Map(); BK.rw = new Map(); BK.fwd = new Map();
  for (const k of Object.keys(BK.raw)) { try { indexLemma(k); } catch (e) { if (e === TIMEOUT) throw e; } }
  sortIndex();
};
const indexLemma = (k: string) => {
  const add = <V>(m: Map<string, V[]>, key: string, v: V) => { let a = m.get(key); if (!a) m.set(key, a = []); a.push(v); };
  const t = BK.raw[k];
  if (t?.$ !== "Def" || (t.v === null && t.b !== true) || t.i || k.includes("~")) return;
  const L: Lemma = { k, order: BK.order.get(k) ?? -1, n: arity(t.T, t.n), np: t.n, guarded: false };
  const o = withOwnFuel(FUEL_NF * 2, () => attempt(FUEL_NF * 2, () => openMeta(t.T, L.n)));
  const c = o && attempt(20000, () => lower(o.concl, 0));
  if (!o || !c) return;
  L.guarded = withOwnFuel(FUEL_NF, () => o.doms.some((dm) => attempt(FUEL_NF / 4, () => isProp(dm.A)) === true));
  const hk = headKey(c);
  if (hk === "V" || hk === "*" || hk === "Typ") return;
  add(BK.apply, hk, L);
  const cn = t.n > 0 ? nf(o.concl, 0) : null;
  const nk = cn ? headKey(cn) : "*";
  if (nk !== hk && !/^(\*|V|E\|\*|E\|V)$/.test(nk)) add(BK.apply, nk, L);
  for (const e of [c, cn]) {
    if (e?.$ !== "Eql") continue;
    for (const side of [0, 1] as const) {
      const sk = headKey(side === 0 ? e.a : e.b);
      const ok = sk.startsWith("R:") || (t.n === 0 && (sk.startsWith("C:") || sk.startsWith("A:")));
      if (ok && !(BK.rw.get(sk) ?? []).some((x) => x.L.k === k && x.side === side)) add(BK.rw, sk, { L, side });
    }
  }
  if (t.x === 0) o.doms.forEach((dm, j) => {
    const P = attempt(20000, () => lower(dm.A, 0));
    const pk = P && headKey(P);
    // a premise with a head says which facts select the lemma; a bare {?a == ?b} says nothing
    if (pk && !/^(\*|V|E\|\*|E\|V)$/.test(pk) && hasMeta(P)) add(BK.fwd, pk, { L, j });
  });
};
// the head index is a fast path; a pattern whose head is a bare variable waits in the wildcard bucket
// of its kind ("E|*" for an equation, "*" otherwise), consulted by every lookup
const wildOf = (key: string) => (key.startsWith("E|") ? "E|*" : "*");
const bucket = <V>(m: Map<string, V[]>, key: string): V[] => {
  const w = wildOf(key);
  return w === key ? m.get(key) ?? [] : [...(m.get(key) ?? []), ...(m.get(w) ?? [])];
};
const sortIndex = () => {
  for (const v of BK.apply.values()) v.sort((a, b) => b.order - a.order);
  for (const v of BK.rw.values()) v.sort((a, b) => b.L.order - a.L.order);
  for (const v of BK.fwd.values()) v.sort((a, b) => b.L.order - a.L.order);
};
// a lemma a goal may call: above the goal's def in file order (Bend checks defs in order)
// a template lemma is usable anywhere: Bend instantiates it at closed ~ arguments (unification or a closed
// constant gives them; a step whose ~ argument is not closed is refused by Bend's own rule)
const usableLemma = (g: Goal, L: Lemma): boolean => L.order < g.own.order && L.k !== g.own.k && !BK.hidden.has(L.k);

// ---- printing, errors ----
const zeroFix = (s: string, file: Term): string => {
  let re = BK.zero.get(file);
  if (re === undefined) {
    const names = Object.keys(BK.raw).filter((k) => BK.raw[k]?.$ === "Def" && BK.raw[k].n === 0 && BK.raw[k].v)
      .map((k) => B.name_show(file, k)).filter((n: string) => /^[A-Za-z_][\w.]*$/.test(n));
    re = names.length ? new RegExp("(?<![\\w.])(" + names.sort((a, b) => b.length - a.length).map((n) => n.replace(/\./g, "\\.")).join("|") + ")(?![\\w.(])", "g") : null;
    BK.zero.set(file, re);
  }
  const t = re ? s.replace(re, "$1()") : s;
  // a template's constant prints as its name (comm3~op as op)
  return constNames.size && t.includes("~") ? t.replace(/(?<![\w.])([A-Za-z_][\w.]*)~([A-Za-z_]\w*)/g, (m, a: string, b: string) => constNames.get(a + "~" + b) ?? constNames.get(a.slice(a.indexOf(".") + 1) + "~" + b) ?? m) : t;
};
const clip = (s: string, n: number) => (s.length > n ? s.slice(0, n) + " … [" + (s.length - n) + " more chars]" : s);
const show = (t: Term, names: string[], file: Term): string => zeroFix(B.term_show(t, -1, names.slice(), file), file);
const showCut = (t: Term, d: number, names: string[], file: Term, nodes = 400): string => {
  try { return B.term_show(lowerB(t, d, { n: nodes }, true), -1, names.slice(), file); } catch (e) { return "<not printable: " + String((e as Error)?.message ?? e).slice(0, 80) + ">"; }
};
const errText = (e: Term): string => {
  if (e instanceof Stop) return "not decided: " + e.why;
  if (e?.$ !== "Err") return String(e?.message ?? e).slice(0, 1500);
  const file = e.spn?.file;
  const names: string[] = B.ctx_scope(e.ctx);
  const d = names.length;
  try {
    return withFuel(FUEL_FINAL, () => {
      const out: string[] = ["Error:"];
      const ex = (x: Term) => (typeof x === "string" ? x : clip(showCut(x, d, names, file), 1200));
      if (e.obs === undefined) out.push("- message  : " + ex(e.exp));
      else out.push("- expected : " + ex(e.exp), "- observed : " + ex(e.obs));
      for (const [i, a] of B.pmap_to_array(e.ctx).sort((x: Term, y: Term) => x[0] - y[0])) out.push("- " + a.k + " : " + clip(showCut(a.T, i, names.slice(0, i), file, 2000), 400));
      if (e.spn) {
        const at = lineOf(e.spn.file.str, e.spn.beg), lns = e.spn.file.str.split("\n");
        out.push("Location: " + (e.def ? B.name_show(file, e.def) : "") + "\n" + lns.slice(Math.max(0, at - 2), at + 1).map((l: string, j: number) => {
          const i = Math.max(0, at - 2) + j + 1;
          return String(i).padStart(5) + (i === at ? ">| " : " | ") + clip(l, 300);
        }).join("\n"));
      }
      return out.join("\n") + (e.nte ? "\n" + e.nte : "");
    });
  } catch {
    return "Error: " + (typeof e.exp === "string" ? e.exp : "(not printable within its budget)");
  }
};
const firstLine = (e: Term) => errText(e).split("\n").slice(0, 3).join(" ").slice(0, 300);

// ---- goals: what the checker reports at a ?TODO ----
type Raw = { book: Term; lhs: Term; qt: Term; ty: Term; ctx: Term; d: number; tm: Term };
let sink: Raw[] | null = null;
BR.hole = (h: Raw) => { if (sink) sink.push(h); };
// a def whose body is searched: the target, or a helper made by a lift (level: helpers above it)
// consts: a template's ~ parameters, which Bend makes constants (k~name, opaque, reusable), named as the
// header names them: in scope for every step's text, printed back by name, and hypotheses like any other
type Owner = { k: string; short: string; root: string; T: Term; n: number; x: number; order: number; file: Term; level: number; consts: { name: string; key: string }[] };
const constNames = new Map<string, string>(); // short key (comm3~op) -> its name (op)
// pend: binders the goal still has to bind, named pnames (a def's parameters, a case's fields): they can
// be split with descent (Bend refines lhs at a match on them); a goal with pend 0 is a leaf
type Goal = {
  own: Owner; book: Term; lhs: Term; qt: Term; ty: Term; ctx: Term; d: number; names: string[]; env: Term; ckey: number;
  pend: number; pnames: string[]; split: boolean; path: string; prefer?: string; // a lift's reason: split it first
};
const LD = (g: Goal) => g.d + 1; // a goal's terms are lowered one level below its context: `_` is level d
const sh = (g: Goal, t: Term): string => show(t, [...g.names, "_"], g.own.file);
const ann = (g: Goal, i: number): Term => B.pmap_get(g.ctx, i);
const qn = (q: Term): number => (q.$ === "None" ? 0 : q.$ === "Lone" ? 1 : 2);
const owner = (k: string, level = 0, root = shortOf(k)): Owner => {
  const t = BK.raw[k];
  const consts: { name: string; key: string }[] = [];
  if (t.x > 0) {
    const header = headerNames(k, t.n);
    let T: Term = t.T;
    for (let j = 0; j < t.x; j++) {
      const s = B.term_strip(T);
      if (s.$ !== "All") break;
      const key = k + "~" + s.k;
      consts.push({ name: header?.[j] ?? s.k, key });
      constNames.set(shortOf(key), header?.[j] ?? s.k);
      T = s.B(B.Ref(key));
    }
  }
  return { k, short: shortOf(k), root, T: t.T, n: t.n, x: t.x ?? 0, order: BK.order.get(k) ?? BK.book.order.length, file: BK.files.get(k), level, consts };
};
const goalOf = (h: Raw, own: Owner, pnames: string[], split: boolean, path: string): Goal => {
  const names = B.ctx_scope(h.ctx).slice(0, h.d);
  while (names.length < h.d) names.push("_");
  let env = null, ckey = 0;
  for (let i = 0; i < h.d; i++) {
    const a = B.pmap_get(h.ctx, i);
    env = B.list_set(env, i, B.Var(names[i], i));
    ckey = mixH(ckey, a ? qn(a.q) : 3, strH(names[i]), a ? attempt(FUEL_NF, () => H(lower(a.T, i))) ?? 0 : 0);
  }
  const pend = Math.min(pnames.length, h.lhs?.n ?? 0);
  return { own, book: h.book, lhs: h.lhs, qt: h.qt, ty: h.ty, ctx: h.ctx, d: h.d, names, env, ckey, pend, pnames: pnames.slice(0, pend), split, path };
};
let unkeyed = 0;
const goalKey = (g: Goal, N: Term): number =>
  attempt(FUEL_NF, () => mixH(g.ckey, qn(g.qt), g.pend, strH(g.pnames.join(",")), H(N ?? lower(g.ty, LD(g))))) ?? -++unkeyed;
const dirOf = (f: string) => f.slice(0, Math.max(f.lastIndexOf("/"), f.lastIndexOf("\\")) + 1);
const parserAt = (str: string, file: Term, names: string[], pos = 0, dir = BK.top, consts: { name: string }[] = []): Term => {
  const p = B.parse_new(BK.book, dir, str, file?.ns ?? "", file?.al ?? {});
  p.pos = pos;
  p.frs = names.length + consts.length;
  // consts first (outermost: a context name of the same spelling shadows them), at levels past the context
  consts.forEach((c, j) => B.parse_push(p, c.name, names.length + j));
  names.forEach((k, i) => { if (k !== "_") B.parse_push(p, k, i); });
  return p;
};
const withHols = <T>(f: () => T): T => { const h = BK.book.hols; try { return f(); } finally { BK.book.hols = h; } };
const parseAt = (g: Goal, text: string): { tm: Term; p: Term } => {
  const consts = g.own.consts ?? [];
  const p = parserAt(text, g.own.file, g.names, 0, BK.top, consts);
  let env = g.env;
  consts.forEach((c, j) => { env = B.list_set(env, g.names.length + j, B.Ref(c.key)); });
  const lt = withHols(() => {
    const t = B.parse_block(p);
    B.parse_skip(p);
    if (p.pos < text.length) B.parse_fail(p, "the end of the fragment");
    return t;
  });
  return { tm: B.term_higher(lt, env), p };
};
// text checked at g: its holes in text order (each with its exact goal), or a throw (Err or Stop). A
// binder of g's context used beyond its quantity fails here (Bend closes it outside the hole)
type Captured = { holes: Raw[]; us: Term };
const capture = (g: Goal, text: string): Captured => {
  const { tm, p } = parseAt(g, text);
  const saved = sink, mine: Raw[] = [];
  sink = mine;
  let c: Term;
  try { c = B.term_check(g.book, g.lhs, tm, g.qt, g.ty, g.ctx, g.d); } finally { sink = saved; }
  if (g.qt.$ !== "None") {
    for (const [i, a] of B.pmap_to_array(g.ctx)) {
      const u = B.pmap_get(c.us, i) ?? B.None();
      if (B.quant_join(u, a.q).$ !== a.q.$) throw LIN;
    }
  }
  const seen = new Set<number>();
  const holes = mine.filter((h) => h.tm.s?.file === p && !seen.has(h.tm.s.beg) && seen.add(h.tm.s.beg)).sort((a, b) => a.tm.s.beg - b.tm.s.beg);
  return { holes, us: c.us };
};
const tryCapture = (g: Goal, text: string, fuel = FUEL_CHECK): Captured | undefined => attempt(fuel, () => capture(g, text));
const tryText = (g: Goal, text: string): boolean => tryCapture(g, text) !== undefined;
// a body for def k (indented, under its header): its value and its holes (offsets into the body)
type Checked = { v: Term; holes: { raw: Raw; at: number }[] };
const checkDef = (k: string, body: string, header?: string): Checked => {
  const def = BK.raw[k], file = BK.files.get(k), ds = defSrc(k);
  const head = header ?? ds!.header;
  const str = head + "\n" + body + "\n";
  const p = parserAt(str, file, [], str.indexOf("(") + 1, dirOf(ds?.file ?? BK.entry));
  const v = withHols(() => {
    const tele = B.parse_tele(p, ")");
    p.pos = head.length;
    const vars = tele.map((c: Term) => ({ $: "PVar", k: c[1], i: c[2], q: B.Lone(), s: c[4] }));
    const b = B.body_flatten(B.parse_body(p), vars, () => p.frs++);
    B.parse_skip(p);
    if (p.pos < str.length) B.parse_fail(p, "the end of the body");
    return B.term_higher(b);
  });
  const saved = sink, mine: Raw[] = [];
  sink = mine;
  try { B.def_check(BK.book, k, { ...def, v }); } finally { sink = saved; }
  const seen = new Set<number>();
  const holes = mine.filter((h) => h.tm.s?.file === p && !seen.has(h.tm.s.beg) && seen.add(h.tm.s.beg))
    .sort((a, b) => a.tm.s.beg - b.tm.s.beg).map((raw) => ({ raw, at: raw.tm.s.beg - head.length - 1 }));
  return { v, holes };
};
const checkErr = (k: string, body: string, header?: string, cap = FUEL_FINAL): Term => {
  try { withFuel(cap, () => checkDef(k, body, header)); return null; } catch (e) { return e ?? "error"; }
};
const stmtErr = (k: string): Term => {
  const t = BK.raw[k];
  if (t?.$ !== "Def") return null;
  try {
    withFuel(FUEL_FINAL, () => B.term_check(BK.book, { t: B.Ref(k), n: 0, def: k, qs: [], u: t.u }, t.T, B.None(), B.Typ(B.Qua(B.Lone())), B.ctx_nil(), 0));
    return null;
  } catch (e) { return e === OOF ? null : e; }
};
const KEYWORD = /^(def|type|law|match|case|do|return|for|exs|where|is|import|Type|Data|Kind|Quant|if|else|with)$/;
const fresh = (g: Goal, base: string, used: Set<string>): string => {
  const b = base.replace(/[^A-Za-z0-9_]/g, "") || "x";
  for (let i = 0; ; i++) {
    const nm = i === 0 ? b : b + String(i);
    const q = (g.own.file?.ns ?? "") === "" ? nm : g.own.file.ns + ":" + nm;
    if (!used.has(nm) && !(q in BK.raw) && !(nm in BK.raw) && nm !== "_" && !KEYWORD.test(nm) && !/^\d/.test(nm)) { used.add(nm); return nm; }
  }
};
// the parameter names as k's header writes them (a law's fill renames them)
const headerNames = (k: string, n: number): string[] | null => {
  const ds = defSrc(k), file = BK.files.get(k);
  if (!ds || !file) return null;
  const p = parserAt(ds.header, file, [], ds.header.indexOf("(") + 1);
  const tele = attempt(FUEL_NF, () => withHols(() => B.parse_tele(p, ")")));
  return tele && tele.length === n ? tele.map((c: Term) => c[1]) : null;
};
// the root goal of def k: Bend's own def check reaches its body, a bare ?TODO, with every parameter
// pending (a template's ~ parameters are consumed first, as Bend does)
const rootGoal = (own: Owner): Goal | null => {
  const def = BK.raw[own.k];
  let v: Term = B.Hol("TODO");
  for (let j = 0; j < own.x; j++) { const inner = v; v = B.Lam("_", 0, () => inner); }
  const saved = sink, mine: Raw[] = [];
  sink = mine;
  try { attempt(FUEL_CHECK, () => B.def_check(BK.book, own.k, { ...def, v })); } finally { sink = saved; }
  const h = mine[0];
  if (!h) return null;
  const names = headerNames(own.k, def.n)?.slice(own.x) ?? [];
  let t = h.ty;
  for (let j = names.length; j < (h.lhs?.n ?? 0); j++) { const s = asAll(t); if (!s) break; names.push(s.k || "x" + j); t = s.B(B.Var(s.k, FRESH + j)); }
  return goalOf(h, own, names, false, "");
};
// the next pending binder bound by a lambda: +x (reusable) where Bend allows it, else x
const introOne = (g: Goal, reusable: boolean): { g: Goal; x: string; plus: boolean } | null => {
  const x = g.pnames[0];
  const t = asAll(g.ty);
  const tryPlus = reusable && t?.q.$ === "Lone";
  for (const mark of tryPlus ? ["+", ""] : [""]) {
    const r = tryCapture(g, mark + x + " => ?TODO");
    if (r?.holes.length === 1) return { g: goalOf(r.holes[0], g.own, g.pnames.slice(1), g.split, g.path), x, plus: mark === "+" };
  }
  return null;
};
type Bound = { x: string; plus: boolean };
const introAll = (g0: Goal): { g: Goal; xs: Bound[] } | null => {
  let g = g0;
  const xs: Bound[] = [];
  while (g.pend > 0) {
    const r = introOne(g, true);
    if (!r) return null;
    xs.push({ x: r.x, plus: r.plus });
    g = r.g;
  }
  return { g, xs };
};
const leafOf = (g: Goal): Goal => (g.pend > 0 ? introAll(g)?.g ?? g : g);
// a match on pending binder j: the first j bound, then a λ-match whose arms Bend types (refining lhs)
type ArmInfo = { ctr: string; label: string; fields: string[]; nat: boolean; g: Goal };
type Split = { pre: Bound[]; x: string; arms: ArmInfo[] };
const split = (g0: Goal, j: number): Split | null => {
  let g = g0;
  const pre: Bound[] = [];
  for (let i = 0; i < j; i++) { const r = introOne(g, true); if (!r) return null; pre.push({ x: r.x, plus: r.plus }); g = r.g; }
  const t = wnf(g.ty);
  if (!t || t.$ !== "All" || t.q.$ === "None") return null;
  const A = wnf(t.A);
  const adt = A?.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(g.book, A, g.ctx, g.own.k)) : null;
  if (!adt || adt.c.length === 0 || adt.c.length > 12) return null;
  const labels = adt.c.map((c: Term) => B.name_show(g.own.file, c.k));
  const r = tryCapture(g, "\\{" + labels.map((l: string) => l + ": ?TODO").join("; ") + "}");
  if (!r || r.holes.length !== adt.c.length) return null;
  const used = new Set([...g.names, ...g.pnames]);
  const sname = g.pnames[0];
  const arms = adt.c.map((c: Term, i: number): ArmInfo => {
    const h = r.holes[i];
    const isNat = c.k === "Succ" || c.k === "Zero";
    const fields: string[] = [];
    let cur = h.ty;
    for (let f = 0; f < c.n; f++) {
      const s = asAll(cur);
      const base = isNat ? (sname.length <= 2 ? sname + "p" : "p") : s?.k || "f" + f;
      fields.push(fresh(g, base, used));
      cur = s ? s.B(B.Var("_", FRESH + f)) : cur;
    }
    return { ctr: c.k, label: labels[i], fields, nat: isNat, g: goalOf(h, g.own, [...fields, ...g.pnames.slice(1)], true, g.path + "/" + shortOf(c.k)) };
  });
  return { pre, x: g.pnames[0], arms };
};
const isData = (g: Goal, A: Term) => attempt(FUEL_NF, () => { B.term_check(g.book, g.lhs, A, B.None(), B.Typ(B.Qua(B.Many())), g.ctx, g.d); return true; }) === true;
// the pending binders worth a split: those that block evaluation (in the goal or a hypothesis), then
// enumerations, then records (one arm: no branching)
const splitCands = (n: Goal, lg: Goal | null): number[] => {
  const out: number[] = [], records: number[] = [], enums: number[] = [], words = new Set<number>();
  let t: Term = n.ty;
  for (let j = 0; j < n.pend; j++) {
    const s = asAll(t);
    if (!s) break;
    const A = s.q.$ !== "None" ? wnf(s.A) : null;
    const a = A?.$ === "ADT" ? BK.raw[A.k] : null;
    const isWord = a?.$ === "ADT" && a.c.some((c: Term) => /(^|[.:])W(Con|Nil)$/.test(c.k));
    if (isWord && /(^|[/.])(U32|F32|WCon|WNil)(\/|$)/.test(n.path)) words.add(j);
    if (a?.$ === "ADT" && a.c.length === 1 && a.c[0].n > 0 && !/^(U32|F32|Chr|Word)$/.test(A.k) && !/\b(?:WCon|WNil)$/.test(a.c[0].k)) records.push(j);
    if (a?.$ === "ADT" && a.c.length >= 2 && a.c.length <= 4 && a.c.every((c: Term) => c.n === 0)) enums.push(j);
    t = s.B(B.Var(n.pnames[j] ?? "_", n.d + j));
  }
  const add = (j: number) => { if (j >= 0 && j < n.pend && !out.includes(j) && !words.has(j)) out.push(j); };
  if (lg) {
    const blk: Term[] = [];
    const N = nf(lg.ty, LD(lg), false, 8000);
    if (N) blockers(N, blk);
    for (let i = lg.d - 1; i >= 0; i--) { const a = ann(lg, i); const h = a && nf(a.T, LD(lg), false, 2000); if (h) blockers(h, blk); }
    let s = asAll(lg.ty);
    for (let k = 0; s && k < 8; k++, s = asAll(s.B(B.Var("_", FRESH + k)))) { const h = nf(s.A, LD(lg), false, 2000); if (h) blockers(h, blk); }
    blk.filter((x) => x.$ === "Var").forEach((x) => add(x.i - n.d));
  }
  enums.forEach(add);
  // a datatype binder no blocker names is still a candidate (structural recursion on it), last
  for (let j = 0; j < n.pend; j++) if (!records.includes(j)) add(j);
  const depth = n.path.split("/").length - 1;
  const branching = out.slice(0, depth >= 4 ? 1 : depth >= 2 ? 2 : 4);
  return [...branching, ...records.slice(-2).reverse().filter((j) => !branching.includes(j))];
};

// ---- facts: hypotheses, and what follows from one in one step ----
type Fact = { pf: string; T: Term; N: Term; q: Term; i: number; empty?: boolean; A?: Term; fwd?: boolean };
const symText = (g: Goal, E: Term, e: string) => "Equal.sym(" + sh(g, E.T) + ", " + sh(g, E.a) + ", " + sh(g, E.b) + ", " + e + ")";
const elim = (g: Goal, T: Term, arm: (k: string, fs: string[]) => string): string | null => {
  const w = wnf(B.term_higher(T, g.env));
  const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
  if (adt?.$ !== "ADT" || adt.c.length === 0 || adt.c.length > 12) return null;
  const used = new Set(g.names);
  const chain = adt.c.reduceRight((acc: string, c: Term) => {
    const fs = Array.from({ length: c.n }, (_, i) => fresh(g, "f" + i, used));
    return "\\{" + B.name_show(g.own.file, c.k) + ": " + fs.map((f) => f + " => ").join("") + arm(c.k, fs) + "; " + acc + "}";
  }, "\\{}");
  return "{" + chain + " : " + sh(g, T) + " -> Type}(_)";
};
const asCtr = (t: Term): Term => (t.$ === "Lit" ? litStep(t) : t);
const derive = (g: Goal, h: Fact, out: Fact[]) => {
  const E = h.N;
  if (E?.$ !== "Eql" || H(E.a) === H(E.b) || !BK.raw["Equal.sym"]) return;
  const [a, b, T] = [E.a, E.b, E.T];
  const sym = symText(g, E, h.pf);
  out.push({ pf: sym, T: B.Eql(b, a, T), N: B.Eql(b, a, T), q: h.q, i: -1 });
  const ca = asCtr(a), cb = asCtr(b);
  if (ca?.$ !== "Ctr" || cb?.$ !== "Ctr") return;
  if (ca.k !== cb.k) {
    const P = elim(g, T, (k) => (k === cb.k ? "Empty" : "Unit"));
    if (P) out.push({ pf: "{(%" + h.pf + " : " + P + "; Unit{}) : Empty}", T: E, N: E, q: h.q, i: -1, empty: true });
    return;
  }
  ca.x.forEach((x: Term, j: number) => {
    const y = cb.x[j];
    if (out.length > 48 || H(x) === H(y)) return;
    const F = attempt(FUEL_NF, () => lower(B.term_infer(g.book, g.lhs, B.term_higher(x, g.env), B.None(), g.ctx, g.d).ty, LD(g)));
    if (!F) return;
    const P = elim(g, T, (k, fs) => (k === ca.k ? "{" + fs[j] + " == " + sh(g, y) + " : " + sh(g, F) + "}" : "Unit"));
    if (P) out.push({ pf: "{(%" + sym + " : " + P + "; {==}) : {" + sh(g, x) + " == " + sh(g, y) + " : " + sh(g, F) + "}}", T: B.Eql(x, y, F), N: B.Eql(x, y, F), q: h.q, i: -1 });
  });
};
const factsOf = (g: Goal): Fact[] => {
  const k = mixH(g.ckey, g.d);
  let fs = S.facts.get(k);
  if (fs) return fs;
  fs = [];
  for (let i = g.d - 1; i >= 0; i--) {
    const a = ann(g, i);
    if (!a || g.names[i] === "_" || g.names.indexOf(g.names[i], i + 1) >= 0) continue; // shadowed: not nameable
    const T = attempt(FUEL_NF, () => lower(a.T, LD(g)));
    if (!T) continue;
    const f: Fact = { pf: g.names[i], T, N: nf(a.T, LD(g)) ?? T, q: a.q, i };
    fs.push(f);
    try { derive(g, f, fs); } catch (e) { if (e === TIMEOUT) throw e; }
  }
  // a template's constants that are facts (not functions): reusable, they spend no usage
  for (const c of g.own.consts ?? []) {
    const A = g.book.tlds[c.key]?.T;
    if (!A || asAll(A) || !isProp(A)) continue;
    const T = attempt(FUEL_NF, () => lower(A, LD(g)));
    if (T) fs.push({ pf: c.name, T, N: nf(A, LD(g)) ?? T, q: B.Many(), i: -1 });
  }
  S.facts.set(k, fs);
  for (const f of fs.filter((x) => x.i >= 0)) { try { forward(g, f, fs); } catch (e) { if (e === TIMEOUT) throw e; } }
  try { forwardLocal(g, fs); } catch (e) { if (e === TIMEOUT) throw e; }
  return fs;
};
const forward = (g: Goal, f: Fact, out: Fact[]) => {
  let made = out.filter((x) => x.fwd).length;
  const seen = new Set<string>();
  for (const t of f.N && H(f.N) !== H(f.T) ? [f.T, f.N] : [f.T]) {
    for (const { L, j } of bucket(BK.fwd, headKey(t)).slice(0, 24)) {
      if (made >= 16 || !usableLemma(g, L) || seen.has(L.k + "#" + j)) continue;
      seen.add(L.k + "#" + j);
      const c = lemmaCallee(g, L);
      const o = openMeta(c.T, c.n);
      const P = o && attempt(FUEL_NF, () => lower(o.doms[j].A, LD(g)));
      const sol: (Term | null)[] = new Array(c.n).fill(null);
      if (!P || !match(P, t, sol, g.d)) continue;
      const r = complete(g, c, sol, false);
      const o2 = r && r.holes === 0 ? openMeta(c.T, c.n, solH(g, r.sol)) : null;
      const E = o2 && attempt(FUEL_NF, () => lower(o2.concl, LD(g)));
      if (!E || hasMeta(E) || !isProp(o2!.concl) || out.some((x) => H(x.T) === H(E))) continue;
      const fact: Fact = { pf: callText(c, r!.args), T: E, N: nf(o2!.concl, LD(g)) ?? E, q: f.q, i: -1, fwd: true };
      out.push(fact);
      made++;
      try { derive(g, fact, out); } catch (e) { if (e === TIMEOUT) throw e; }
    }
  }
};
// the local rules forward: the induction hypothesis (under a split) and each function hypothesis, every
// parameter fixed by premises that facts fit, in either reading; the checker keeps what holds (a call
// that does not descend, read as stated, can descend read in normal form)
const forwardLocal = (g: Goal, out: Fact[]) => {
  const rules = [...(canRecurse(g) ? [ihCallee(g)] : []), ...hypCallees(g)].filter(guarded);
  let made = 0;
  for (const c of rules) {
    for (const nfFirst of [false, true]) {
      if (made >= 8) return;
      const r0 = complete(g, c, new Array(c.n).fill(null), false, nfFirst);
      const r = r0 && descends(g, c, r0.sol, r0.args) ? r0 : null;
      if (!r || r.holes) continue;
      const o2 = openMeta(c.T, c.n, solH(g, r.sol));
      const E = o2 && attempt(FUEL_NF, () => lower(o2.concl, LD(g)));
      if (!E || hasMeta(E) || out.some((x) => H(x.T) === H(E))) continue;
      const pf = callText(c, r.args);
      // checked at the goal's own quantity: an erased check would skip the descent rule
      if (!tryText({ ...g, ty: o2!.concl }, pf)) continue;
      const fact: Fact = { pf, T: E, N: nf(o2!.concl, LD(g)) ?? E, q: g.qt, i: -1, fwd: true };
      out.push(fact);
      made++;
      try { derive(g, fact, out); } catch (e) { if (e === TIMEOUT) throw e; }
    }
  }
};
const usable = (f: Fact, qt: Term) => qt.$ === "None" || f.q.$ !== "None";

// ---- proofs ----
const HOLE = "\u0000";
type Arm = ArmInfo & { k: Pf };
type Pf =
  | { t: "tm"; s: string; subs: Pf[] } // text; its i-th HOLE is subs[i]
  | { t: "rw"; e: Pf; P: string; k: Pf } // %e : P; k
  | { t: "lam"; x: string; k: Pf } // x => k at a function goal
  | { t: "intro"; xs: Bound[]; k: Pf } // the pending binders bound, then k
  | { t: "mt"; pre: Bound[]; x: string; arms: Arm[] } // match on a pending binder
  | { t: "def"; name: string; head: string; body: Pf; call: string } // a helper def, used by its call
  | { t: "body"; text: string; ats: number[]; subs: Pf[] } // a body with holes at offsets (a sketch, a def's own holes)
  | { t: "hole"; n: GNode };
const tm = (s: string, subs: Pf[] = []): Pf => ({ t: "tm", s, subs });
const lams = (xs: Bound[]) => xs.map((b) => (b.plus ? "+" : "") + b.x + " => ").join("");
// the λ-form: an expression that checks at the goal it proves (pending binders as lambdas)
const inline = (p: Pf): string => {
  switch (p.t) {
    case "tm": { let i = 0; return p.s.replace(/\u0000/g, () => inline(p.subs[i++])); }
    case "rw": return "(%" + inline(p.e) + " : " + p.P + "; " + inline(p.k) + ")";
    case "lam": return p.x + " => " + inline(p.k);
    case "intro": return lams(p.xs) + inline(p.k);
    case "mt": return lams(p.pre) + "\\{" + p.arms.map((a) => a.label + ": " + inline(a.k)).join("; ") + "}";
    case "def": return p.call;
    case "hole": return "?TODO";
    case "body": throw new Error("a body is not an expression");
  }
};
const flat = (p: Pf): string => (p.t === "rw" ? "%" + inline(p.e) + " : " + p.P + "; " + flat(p.k) : inline(p));
// the statement form: what a def body says (match statements on pending binders, rewrites on lines). A
// reusable binder's rebinding (+x = x) is a local statement, and Bend matches no binder after one: the
// rebindings wait for the first line that is not a match
const render = (p: Pf, ind: string, out: string[], plus: string[] = []) => {
  const flush = () => { for (const x of plus) out.push(ind + "+" + x + " = " + x); plus = []; };
  if (p.t === "intro") { render(p.k, ind, out, [...plus, ...p.xs.filter((b) => b.plus).map((b) => b.x)]); return; }
  if (p.t === "mt") {
    const keep = [...plus, ...p.pre.filter((b) => b.plus).map((b) => b.x)].filter((x) => x !== p.x);
    out.push(ind + "match " + p.x + ":");
    for (const a of p.arms) {
      const pat = a.nat ? (a.ctr === "Zero" ? "0n" : "1n+" + a.fields[0]) : a.label + "{" + a.fields.join(", ") + "}";
      out.push(ind + "  case " + pat + ":");
      render(a.k, ind + "    ", out, keep);
    }
    return;
  }
  flush();
  if (p.t === "rw") { out.push(ind + "%" + inline(p.e) + " :", ind + "  " + p.P); render(p.k, ind, out); }
  else if (p.t === "body") out.push(fillBody(p));
  else out.push(ind + inline(p));
};
// a body's holes filled from the last back (offsets stay valid); a hole alone on its line takes the
// statement form at its indentation, any other hole the λ-form in parentheses
const fillBody = (p: Extract<Pf, { t: "body" }>): string => {
  let body = p.text;
  const order = p.ats.map((at, i) => ({ at, i })).sort((a, b) => b.at - a.at);
  for (const { at, i } of order) {
    const sub = p.subs[i];
    if (sub.t === "hole") continue;
    const lineStart = body.lastIndexOf("\n", at - 1) + 1;
    const lineEnd = body.indexOf("\n", at) < 0 ? body.length : body.indexOf("\n", at);
    const before = body.slice(lineStart, at), after = body.slice(at + 5, lineEnd);
    if (/^\s*$/.test(before) && /^\s*(#.*)?$/.test(after)) {
      const out: string[] = [];
      render(sub, before, out);
      body = body.slice(0, lineStart) + out.join("\n") + body.slice(at + 5);
    } else body = body.slice(0, at) + "(" + inline(sub) + ")" + body.slice(at + 5);
  }
  return body;
};
const kidsOf = (p: Pf): Pf[] =>
  p.t === "tm" || p.t === "body" ? p.subs : p.t === "rw" ? [p.e, p.k] : p.t === "lam" || p.t === "intro" ? [p.k] : p.t === "mt" ? p.arms.map((a) => a.k) : p.t === "def" ? [p.body] : [];
const helpersOf = (p: Pf, out: Extract<Pf, { t: "def" }>[] = []): Extract<Pf, { t: "def" }>[] => {
  for (const k of kidsOf(p)) helpersOf(k, out);
  if (p.t === "def" && !out.includes(p)) out.push(p);
  return out;
};
const holesOf = (p: Pf, out: GNode[] = []): GNode[] => {
  if (p.t === "hole") out.push(p.n);
  for (const k of kidsOf(p)) holesOf(k, out);
  return out;
};
const bodyText = (p: Pf): string => { if (p.t === "body") return fillBody(p); const out: string[] = []; render(p, "  ", out); return out.join("\n"); };

// ---- the search: proof numbers over an AND/OR tree ----
// A goal (OR) is proven by any one alternative; an alternative (AND: one tactic step) by all its
// subgoals. pn estimates the work left to prove, dn to refute. Each step walks to the most-proving goal
// and expands it. An alternative's text is checked (and its subgoals made, by the checker) only when the
// search first reaches it; when its subgoals are proven it is checked whole once more at its goal.
const INF = 1e9, MAX_NODES = 60000, MAX_LV = 6, MAX_RW = 4, MAX_LEVEL = 2, MAX_HELPERS = 64; // nesting is capped per path (MAX_LEVEL); the count only bounds the book
type GNode = { g: Goal; key: number; up: Alt | null; alts: Alt[] | null; pn: number; dn: number; pf: Pf | null; lv: number; rws: number; raw?: Term; N?: Term; A?: Term; why?: string; heavy?: boolean; cost?: number };
type Alt = {
  up: GNode; tag: string; note: string; w: number; kids: GNode[]; pn: number; dn: number; pf: Pf | null; dead: boolean;
  probe: string | null; build: (ps: Pf[]) => Pf; open?: () => GNode[] | null; holes: number; why?: string; whole?: (pf: Pf) => boolean; fuel?: number; lazy?: () => string | null; quick?: boolean;
};
type Search = {
  root: GNode; proved: Map<number, Pf>; facts: Map<number, Fact[]>; nodes: number; helpers: number; tags: Map<string, number>;
  internal: number; cache: Map<number, string>; learned: (key: number, text: string) => void;
  starved: Set<Alt>; runMs: number; refuelMs: number;
};
let S: Search;
const newSearch = (root: GNode, cache = new Map<number, string>(), learned: (key: number, text: string) => void = () => {}): Search =>
  (S = { root, proved: new Map(), facts: new Map(), nodes: 0, helpers: 0, tags: new Map(), internal: 0, cache, learned, starved: new Set(), runMs: 0, refuelMs: 0 });
const tag = (t: string) => S.tags.set(t, (S.tags.get(t) ?? 0) + 1);
const mkNode = (g: Goal, up: Alt | null, lv: number, rws: number): GNode | null => {
  const N = g.pend === 0 ? nf(g.ty, LD(g)) : undefined;
  const key = goalKey(g, N);
  for (let a = up; a; a = a.up.up) if (a.up.key === key) return null; // restates an ancestor: a cycle
  // a node keeps its key, not its normal forms (a goal over a machine state is thousands of nodes):
  // they are recomputed (the cache usually has them) while the node is expanded, then let go
  return { g, key, up, alts: null, pn: 1, dn: 1, pf: null, lv, rws };
};
const mkAlt = (up: GNode, tagName: string, text: string | null, w: number, build: (ps: Pf[]) => Pf, note?: string): Alt => {
  const holes = text ? text.split(HOLE).length - 1 : 0;
  return { up, tag: tagName, note: note ?? text?.replace(/\u0000/g, "?") ?? tagName, w, kids: [], pn: w + 1 + holes * 0.5, dn: 1, pf: null, dead: false,
    probe: text === null ? null : text.replace(/\u0000/g, "?TODO"), build, holes };
};
const calcAlt = (a: Alt) => {
  if (a.pf) { a.pn = 0; a.dn = INF; return; }
  if (a.dead) { a.pn = INF; a.dn = 0; return; }
  if (unreached(a)) { a.pn = a.w + 1 + a.holes * 0.5; a.dn = 1; return; }
  let sum = 0, max = 0, dn = INF;
  for (const k of a.kids) { sum += k.pn; max = Math.max(max, k.pn); if (!k.pf) dn = Math.min(dn, k.dn); }
  // the hardest subgoal plus a fifth of the others: a split's arms are alike, not separate proofs
  a.pn = Math.min(a.w + max + 0.2 * (sum - max), INF);
  a.dn = dn;
};
const calcNode = (n: GNode) => {
  if (n.pf) { n.pn = 0; n.dn = INF; return; }
  if (!n.alts) { n.pn = 1; n.dn = 1; return; }
  let pn = INF, dn = 0;
  for (const a of n.alts) if (!a.dead) { pn = Math.min(pn, a.pn); dn = Math.min(INF, dn + a.dn); }
  n.pn = pn;
  n.dn = pn >= INF ? 0 : dn;
};
const setProof = (n: GNode, pf: Pf) => {
  n.pf = pf;
  if (n.g.pend === 0 && pf.t !== "def" && helpersOf(pf).length === 0) {
    S.proved.set(n.key, pf);
    if (n.g.own.level === 0) { try { S.learned(n.key, flat(pf)); } catch { /* a body is no lemma */ } }
  }
};
// every kid proven: the step whole, checked once more at its goal (subproofs may share a binder)
// the whole check needs what its parts needed: a proven goal keeps the fuel its proof took
const close = (a: Alt) => {
  const pf = a.build(a.kids.map((k) => k.pf!));
  const need = (a.fuel ?? 0) + a.kids.reduce((t, k) => t + (k.cost ?? 0), 0);
  const fuel = Math.max(FUEL_CHECK * 4, need * 1.5);
  let ok = true;
  if (a.whole) ok = a.whole(pf);
  // binding and case steps add nothing a re-check could refute (each part was checked at its own goal,
  // binder quantities included); the final def check sees the whole body anyway
  else if (a.kids.length && pf.t !== "def" && a.tag !== "intro" && a.tag !== "split") {
    const slice = deadline;
    if (fuel > FUEL_PARTIAL) deadline = Math.max(deadline, jobDeadline);
    try { ok = tryCapture(a.up.g, flat(pf), fuel) !== undefined; } finally { deadline = slice; }
  }
  if (!ok) { a.dead = true; a.why = lastErr ? firstLine(lastErr) : "the step does not check whole"; return; }
  a.pf = pf;
  tag(a.tag);
  if (!a.up.pf) { a.up.cost = need; setProof(a.up, pf); }
};
const unreached = (a: Alt) => a.probe !== null || a.open !== undefined || a.lazy !== undefined;
const update = (n0: GNode) => {
  for (let n: GNode | null = n0; n;) {
    calcNode(n);
    const a: Alt | null = n.up;
    if (!a) return;
    if (!a.pf && !a.dead) {
      if (n.pn >= INF) a.dead = true;
      else if (!unreached(a) && a.kids.every((k) => k.pf)) close(a);
    }
    calcAlt(a);
    n = a.up;
  }
};
const kidsFrom = (a: Alt, holes: Raw[]): GNode[] | null => {
  const g = a.up.g, out: GNode[] = [];
  const rw = a.tag.startsWith("rw") ? 1 : 0;
  for (const [i, h] of holes.entries()) {
    // a binder (x => ..) is no step of substance: it takes no depth
    const k = mkNode(goalOf(h, g.own, [], g.split, g.path + "#" + a.tag + i), a, a.up.lv + (a.tag === "intro" ? 0 : 1), a.up.rws + rw);
    if (!k) return null;
    out.push(k);
  }
  return out;
};
// BEND_SYNTH_STATS=1: per kind of step, how many reaches pass and fail, and their time (on stderr)
const STATS = !!process.env.BEND_SYNTH_STATS;
const stats = new Map<string, { ok: number; dead: number; ms: number }>();
const reach = (a: Alt) => {
  if (!STATS) return reach0(a);
  const t = performance.now();
  try { reach0(a); } finally {
    const k = a.tag.replace(/\d+$/, ""), r = stats.get(k) ?? { ok: 0, dead: 0, ms: 0 };
    if (a.dead) r.dead++; else r.ok++;
    r.ms += performance.now() - t;
    stats.set(k, r);
  }
};
const reach0 = (a: Alt) => {
  // a lazy step prints its text only now, when the search first reaches it
  if (a.lazy) {
    let t: string | null = null;
    try { t = a.lazy(); } catch (e) { if (e === TIMEOUT) throw e; }
    a.lazy = undefined;
    if (t === null) { a.dead = true; a.why = "the step does not print"; return; }
    a.probe = t.replace(/\u0000/g, "?TODO");
    a.holes = t.split(HOLE).length - 1;
  }
  if (a.open) {
    const ks = a.open();
    a.open = undefined;
    if (!ks) a.dead = true;
    else a.kids = ks;
  } else if (a.probe !== null) {
    // out of fuel is no refutation: the step stays, costlier, and is tried again with four times the fuel
    const fuel = a.fuel ?? FUEL_CHECK;
    // a step that earned more fuel than a slice is bounded by time: the job's own budget, not the slice
    const slice = deadline;
    if (fuel > FUEL_PARTIAL) deadline = Math.max(deadline, jobDeadline);
    let r: Captured | undefined;
    try { r = tryCapture(a.up.g, a.probe, fuel); } finally { deadline = slice; }
    if (process.env.BEND_SYNTH_TRACE && a.fuel) console.error("[refuel] " + a.tag + " " + clip(a.note, 60) + " fuel " + fuel + " -> " + (r ? "checks" : lastErr === OOF ? "out of fuel" : lastErr === TIMEOUT ? "time" : firstLine(lastErr)) + " at " + Math.round(performance.now()) + " ms");
    if (!r && lastErr === OOF) { a.fuel = fuel * 4; a.w += 1; a.why = "out of fuel at " + fuel; tag("refuel"); S.starved.add(a); return; }
    a.probe = null;
    if (!r) { a.dead = true; a.why = lastErr ? firstLine(lastErr) : "does not check"; return; }
    const ks = kidsFrom(a, r.holes);
    if (!ks) { a.dead = true; a.why = "a subgoal restates an ancestor"; return; }
    a.kids = ks;
  }
  if (!a.dead && a.kids.length === 0) close(a);
};
const bestAlt = (n: GNode): Alt | null => {
  let b: Alt | null = null;
  for (const a of n.alts ?? []) if (!a.dead && !a.pf && (!b || a.pn < b.pn || (a.pn === b.pn && a.w < b.w))) b = a;
  return b;
};
const bestKid = (a: Alt): GNode | null => {
  let b: GNode | null = null;
  for (const k of a.kids) if (!k.pf && (!b || k.dn < b.dn || (k.dn === b.dn && k.pn < b.pn))) b = k;
  return b;
};
const step = () => {
  let n = S.root;
  for (;;) {
    if (!n.alts) {
      try { expand(n); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; n.alts = []; n.why = String((e as Error)?.message ?? e).slice(0, 200); }
      update(n);
      return;
    }
    const a = bestAlt(n);
    if (!a) { update(n); return; }
    if (unreached(a)) {
      try { reach(a); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; a.dead = true; a.why = String((e as Error)?.message ?? e).slice(0, 200); }
      calcAlt(a);
      update(n);
      return;
    }
    const k = bestKid(a);
    if (!k) { update(n); return; }
    n = k;
  }
};
// the search until it proves the root, refutes it, or runs out; yields to the event loop every 100 ms
const run = async (until: number, progress: () => void) => {
  deadline = until;
  let yielded = performance.now(), reported = yielded;
  try {
    while (!S.root.pf && S.root.pn < INF && S.nodes < MAX_NODES && !late()) {
      // dovetailing: steps that only need more fuel get half the time, the shallowest and cheapest first, however
      // cheap the exploration looks (it cannot drown them, and they cannot take the search over)
      const t1 = performance.now();
      if (S.starved.size && S.refuelMs < 0.5 * S.runMs) refuelStep(); else step();
      S.runMs += performance.now() - t1;
      const now = performance.now();
      if (now - reported > 700) { reported = now; deadline = Infinity; try { progress(); } finally { deadline = until; } }
      if (now - yielded > 100) { if (memoryGuard()) break; deadline = Infinity; await Bun.sleep(0); deadline = until; yielded = performance.now(); }
    }
  } catch (e) {
    if (e !== TIMEOUT) throw e;
  } finally {
    deadline = Infinity;
    if (STATS) console.error("[stats] " + [...stats].sort((x, y) => y[1].ms - x[1].ms).map(([k, r]) => k + " ok " + r.ok + " dead " + r.dead + " " + Math.round(r.ms) + "ms").join(" | "));
    if (process.env.BEND_SYNTH_TRACE) console.error("[trace] " + S.nodes + " goals\n" + treeText(S.root, "", 0));
  }
};
// BEND_SYNTH_TRACE=1 (or a line cap): the explored tree (goals, their steps, why a step died), on stderr
const treeText = (n: GNode, ind: string, depth: number, out: string[] = []): string => {
  const cap = Number(process.env.BEND_SYNTH_TRACE) > 1 ? Number(process.env.BEND_SYNTH_TRACE) : 400;
  if (out.length > cap) return out.join("\n");
  out.push(ind + (n.pf ? "✓ " : n.pn >= INF ? "✗ " : "? ") + (n.g.path || "/") + " :: " + clip(attempt(FUEL_NF, () => sh(n.g, lower(n.g.ty, LD(n.g)))) ?? "?", 140) + (n.why ? "  !" + n.why : ""));
  if (depth > 12) return out.join("\n");
  for (const a of n.alts ?? []) {
    if (out.length > cap) break;
    out.push(ind + "  " + (a.pf ? "✓" : a.dead ? "✗" : "·") + " " + a.tag + " " + clip(a.note, 120) + (a.why ? "  !" + clip(a.why, 160) : ""));
    if (!a.dead || a.kids.length) for (const k of a.kids) treeText(k, ind + "    ", depth + 1, out);
  }
  return out.join("\n");
};
const moot = (a: Alt): boolean => { for (let n: GNode | null = a.up; n; n = n.up?.up ?? null) if (n.pf) return true; return false; };
const refuelStep = () => {
  let best: Alt | null = null;
  // a step nearer the root closes more: its fuel weighs four times less per level
  const cost = (a: Alt) => { let d = 0; for (let n: GNode | null = a.up; n?.up; n = n.up.up) d++; return (a.fuel ?? 0) * 4 ** d; };
  for (const a of S.starved) {
    if (a.dead || a.pf || !unreached(a) || moot(a)) { S.starved.delete(a); continue; }
    if (!best || cost(a) < cost(best)) best = a;
  }
  if (!best) return step();
  const t = performance.now();
  try { reach(best); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; best.dead = true; }
  finally { S.refuelMs += performance.now() - t; }
  if (!unreached(best)) S.starved.delete(best);
  calcAlt(best);
  update(best.up);
};
const expand = (n: GNode) => {
  S.nodes++;
  if (n.g.pend === 0) {
    const c = S.proved.get(n.key);
    if (c && tryText(n.g, flat(c))) { n.alts = []; setProof(n, c); tag("cache"); return; }
    const t = S.cache.get(n.key);
    if (t !== undefined && tryText(n.g, t)) { n.alts = []; setProof(n, tm(t)); tag("cache"); return; }
  }
  n.alts = n.g.pend > 0 ? nodeAlts(n) : leafAlts(n);
};
const partial = (n: GNode): { pf: Pf; holes: number; closed: number } => {
  if (n.pf) return { pf: n.pf, holes: 0, closed: 1 };
  const as = (n.alts ?? []).filter((a) => !a.dead && !unreached(a) && a.kids.length > 0);
  // the alternative with the most of its work done: fewest open, then most closed
  let best: { pf: Pf; holes: number; closed: number } | null = null;
  for (const a of as.sort((x, y) => x.pn - y.pn).slice(0, 4)) {
    const ps = a.kids.map(partial);
    const r = { pf: a.build(ps.map((p) => p.pf)), holes: ps.reduce((s, p) => s + p.holes, 0), closed: ps.reduce((s, p) => s + p.closed, 0) + 1 };
    if (!best || r.closed - r.holes > best.closed - best.holes) best = r;
  }
  return best ?? { pf: { t: "hole", n }, holes: 1, closed: 0 };
};

// ---- alternatives at a goal with pending binders: bind them, or split one ----
const nodeAlts = (n: GNode): Alt[] => {
  const alts: Alt[] = [];
  const all = introAll(n.g);
  if (all) {
    const a = mkAlt(n, "intro", null, n.g.prefer ? 1 : 0, (ps) => ({ t: "intro", xs: all.xs, k: ps[0] }), "bind " + n.g.pnames.join(", "));
    a.open = () => { const k = mkNode(all.g, a, n.lv, n.rws); return k ? [k] : null; };
    alts.push(a);
  }
  const cands = splitCands(n.g, all?.g ?? null);
  for (const j of cands) {
    const x = n.g.pnames[j];
    let info: Split | null = null;
    const a = mkAlt(n, "split", null, n.g.prefer === x ? 0 : 1, (ps) => ({ t: "mt", pre: info!.pre, x, arms: info!.arms.map((r, i) => ({ ...r, k: ps[i] })) }), "match " + x);
    a.open = () => {
      info = split(n.g, j);
      if (!info) return null;
      if (info.arms.length === 1) a.w = 0.5;
      const ks: GNode[] = [];
      for (const r of info.arms) { const k = mkNode(r.g, a, n.lv, n.rws); if (!k) return null; ks.push(k); }
      return ks;
    };
    alts.push(a);
  }
  return alts;
};

// ---- alternatives at a leaf goal ----
const targetsOf = (n: GNode): Term[] => {
  n.raw ??= attempt(FUEL_NF, () => lower(n.g.ty, LD(n.g)));
  n.N ??= nf(n.g.ty, LD(n.g));
  n.A ??= nf(n.g.ty, LD(n.g), true);
  const out: Term[] = [];
  for (const t of [n.raw, n.A, n.N]) if (t && !out.some((x) => H(x) === H(t))) out.push(t);
  return out;
};
// a goal one check closes: {==}, the unit, a fact, a fact of Empty
let starvedRefl = false;
// a goal below a heavy one specializes it: its reduction is as heavy (Bend shares no reduction between checks)
const heavyAbove = (n: GNode): boolean => { for (let x: GNode | null = n.up?.up ?? null; x; x = x.up?.up ?? null) if (x.heavy) return true; return false; };
const closer = (n: GNode, w: Term, skipRefl = false): Pf | null => {
  const g = n.g;
  if (w.$ === "Eql" && !skipRefl && tryText(g, "{==}")) return tm("{==}");
  starvedRefl = w.$ === "Eql" && (skipRefl || lastErr === OOF);
  const adt = w.$ === "ADT" ? BK.raw[w.k] : null;
  if (adt?.$ === "ADT" && adt.c.length === 1 && adt.c[0].n === 0) {
    const s = B.name_show(g.own.file, adt.c[0].k) + "{}";
    if (tryText(g, s)) return tm(s);
  }
  const ts = targetsOf(n);
  const hs = new Set(ts.map(H));
  for (const f of factsOf(g)) {
    if (!usable(f, g.qt)) continue;
    const fits = f.empty ? false : f.i >= 0 ? attempt(FUEL_CHECK, () => B.term_compare("LE", g.book, ann(g, f.i).T, g.ty, g.d)) === true : hs.has(H(f.T)) || hs.has(H(f.N));
    if (fits && tryText(g, f.pf)) return tm(f.pf);
    const isEmpty = f.empty || (f.N?.$ === "ADT" && BK.raw[f.N.k]?.c?.length === 0);
    if (!isEmpty) continue;
    const s = adt?.$ === "ADT" && adt.c.length === 0 ? f.pf : "Empty.absurd(" + sh(g, n.raw ?? ts[0]) + ", " + f.pf + ")";
    if (tryText(g, s)) return tm(s);
  }
  return null;
};
const leafAlts = (n: GNode): Alt[] => {
  const g = n.g;
  const w = wnf(g.ty);
  if (!w) return [];
  starvedRefl = false;
  const inherited = heavyAbove(n);
  const c = closer(n, w, inherited);
  if (c) { setProof(n, c); tag("close"); return []; }
  // {==} that ran out of fuel: a step of its own, deepened in the fuel share; under a heavy ancestor it
  // waits behind the ancestor's own step (which closes more)
  const refl = starvedRefl ? mkAlt(n, "refl", "{==}", inherited ? 3 : 0.5, () => tm("{==}")) : null;
  if (refl) {
    refl.fuel = FUEL_CHECK * 4;
    if (!inherited) {
      // heavy too: the goals this one only binds (an intro is the same goal with its binders open)
      n.heavy = true;
      for (let x: GNode = n; x.up?.tag === "intro"; x = x.up.up) x.up.up.heavy = true;
      S.starved.add(refl);
    }
  }
  if (w.$ === "All") {
    const x = fresh(g, w.k === "_" || w.k === "" ? "x" : w.k, new Set(g.names));
    return [mkAlt(n, "intro", x + " => " + HOLE, 0, (ps) => ({ t: "lam", x, k: ps[0] }))];
  }
  if (n.lv >= MAX_LV) return refl ? [refl] : [];
  const tactics = [() => applyAlts(n), () => ctorAlts(n, w), () => rewriteAlts(n), () => liftAlts(n)];
  const alts = tactics.flatMap((f) => { try { return f(); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; if (process.env.BEND_SYNTH_TRACE) console.error("[tactic error] " + ((e as Error)?.stack ?? (e instanceof Stop ? e.why : String(e))).slice(0, 400)); return []; } }).filter((a) => a !== null) as Alt[];
  if (refl) alts.push(refl);
  alts.sort((a, b) => a.w - b.w);
  // a step with no subgoal is checked now: the first that checks proves the goal
  // a heavy goal (even {==} ran out of fuel) re-reduces for every check: none is tried eagerly there
  for (const a of refl || inherited ? [] : [...alts.filter((x) => x.holes === 0 && !x.open && !x.lazy).slice(0, 24), ...alts.filter((x) => x.quick).slice(0, 8)]) {
    reach(a);
    if (n.pf) return [];
  }
  for (const a of alts) calcAlt(a);
  n.raw = n.N = n.A = undefined;
  return alts;
};
type Callee = { text: string; T: Term; n: number; np: number; kind: "hyp" | "ih" | "lemma"; guarded?: boolean; x?: number };
const guarded = (c: Callee): boolean => (c.guarded ??= attempt(FUEL_NF, () => openMeta(c.T, c.n)?.doms.some((dm) => isProp(dm.A))) === true);
const callText = (c: Callee, args: string[]) =>
  c.text + (c.np > 0 || args.length === 0 ? "(" + args.slice(0, c.np).map((a, i) => (i < (c.x ?? 0) ? "~" + a : a)).join(", ") + ")" : "") + args.slice(c.np).map((a) => "(" + a + ")").join("");
const lemmaCallee = (g: Goal, L: Lemma): Callee => ({ text: B.name_show(g.own.file, L.k), T: BK.raw[L.k].T, n: L.n, np: L.np, kind: "lemma", guarded: L.guarded, x: BK.raw[L.k].x ?? 0 });
// a self-call can descend only where a match refined the lhs: a constructor among its columns (Bend's
// own descent rule decides the rest). Whoever matched (a split here, a sketch, the user's code) counts
const canRecurse = (g: Goal): boolean => g.lhs?.u !== true && attempt(FUEL_NF, () =>
  B.term_unapply(B.term_strip(g.lhs.t))[1].some((c: Term) => { const x = B.term_strip(c); return x.$ === "Ctr" || x.$ === "Lit"; })) === true;
// Bend's own descent rule, before any check: a self-call's parameters against the lhs columns, read
// left to right, each unchanged until one shrinks; a parameter not fixed here leaves it to Bend
const descends = (g: Goal, c: Callee, sol: (Term | null)[], args: string[] = []): boolean => {
  if (c.kind !== "ih" || g.own.x > 0 || g.lhs?.u) return true;
  const cols = B.term_unapply(B.term_strip(g.lhs.t))[1];
  for (let j = 0; j < cols.length && j < c.np; j++) {
    const x = sol[j];
    // a fact's proof or a subgoal as the argument: unchanged only if it is the column's own variable
    if (!x) { const col = B.term_strip(cols[j]); if (col.$ === "Var" && args[j] === col.k) continue; return false; }
    const ord = attempt(FUEL_NF, () => B.term_descend(g.lhs.qs?.[j] ?? B.Lone(), B.term_higher(x, g.env), cols[j]));
    if (ord === undefined || ord === "LT") return true;
    if (ord !== "EQ") return false;
  }
  return false;
};
const ihCallee = (g: Goal): Callee => ({ text: B.name_show(g.own.file, g.own.k), T: g.own.T, n: arity(g.own.T, g.own.n), np: g.own.n, kind: "ih" });
const lemmaCands = (g: Goal, targets: Term[]): Callee[] => {
  const seen = new Set<string>(), out: Callee[] = [];
  for (const t of targets) {
    for (const hk of t.$ === "Eql" ? [headKey(t), "E|*"] : [headKey(t)]) {
      for (const L of BK.apply.get(hk) ?? []) {
        if (!usableLemma(g, L) || seen.has(L.k) || out.length >= 64) continue;
        seen.add(L.k);
        out.push(lemmaCallee(g, L));
      }
    }
  }
  return out;
};
const hypCallees = (g: Goal): Callee[] => {
  const out: Callee[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    const a = ann(g, i);
    if (!a || g.names[i] === "_" || g.names.indexOf(g.names[i], i + 1) >= 0 || (g.qt.$ !== "None" && a.q.$ === "None")) continue;
    let k = 0;
    for (let t = asAll(a.T); t && k < 12; t = asAll(t.B(B.Var("_", FRESH + k)))) k++;
    if (k > 0) out.push({ text: g.names[i], T: a.T, n: k, np: 0, kind: "hyp" });
  }
  for (const c of g.own.consts ?? []) {
    const T = g.book.tlds[c.key]?.T;
    let k = 0;
    if (T) for (let t = asAll(T); t && k < 12; t = asAll(t.B(B.Var("_", FRESH + k)))) k++;
    if (k > 0) out.push({ text: c.name, T, n: k, np: 0, kind: "hyp" });
  }
  return out;
};
// a rule's conclusion pattern belongs to the rule and the depth, not to the goal: opened, lowered (and
// normalized, when asked) once, then matched against every goal at that depth
let patMemo = new WeakMap<object, Map<number, { pc0: Term; concl: Term; pn?: Term | null }>>();
const patternOf = (c: Callee, d: number) => {
  let m = patMemo.get(c.T);
  if (!m) patMemo.set(c.T, (m = new Map()));
  const key = d * 64 + c.n;
  let p = m.get(key);
  if (!p) {
    const o = openMeta(c.T, c.n);
    const pc0 = o && attempt(FUEL_NF, () => lower(o.concl, d));
    if (!o || !pc0) return null; // out of fuel is not cached
    m.set(key, (p = { pc0, concl: o.concl }));
  }
  return p;
};
const conclSols = (g: Goal, c: Callee, targets: Term[], pick?: (e: Term) => Term | null): { sols: (Term | null)[][]; spec: number } => {
  const pat = patternOf(c, LD(g));
  const sols: (Term | null)[][] = [];
  if (!pat) return { sols, spec: 0 };
  const pc0 = pat.pc0;
  const seen = new Set<string>();
  const push = (p: Term | null, t: Term) => {
    if (!p) return;
    const s: (Term | null)[] = new Array(c.n).fill(null);
    if (!match(p, t, s, g.d)) return;
    const k = s.map((x) => (x ? String(H(x)) : "_")).join(";");
    if (!seen.has(k)) { seen.add(k); sols.push(s); }
  };
  const pc = pick ? pick(pc0) : pc0;
  const meta = (t: Term) => t.$ === "Var" && t.i >= META;
  // {?a == ?b} fits every equation: backward it says nothing (forward, its premises select it)
  if (pc?.$ === "Eql" && meta(pc.a) && meta(pc.b)) return { sols, spec: 0 };
  for (const t of targets) push(pc, t);
  if (sols.length === 0 && targets.length) {
    if (pat.pn === undefined) pat.pn = nf(pat.concl, LD(g)) ?? null;
    const pn = pat.pn;
    const ps = pn && (pick ? pick(pn) : pn);
    if (ps && H(ps) !== H(pc ?? pn)) for (const t of targets) push(ps, t);
  }
  return { sols, spec: pc ? size(pc) : 0 };
};
type Applied = { args: string[]; holes: number; sol: (Term | null)[] };
type Fill = { g: Goal; c: Callee; sol: (Term | null)[]; via: (string | null)[]; prem: boolean[]; o: { doms: Dom[]; concl: Term }; nfFirst?: boolean };
const solH = (g: Goal, s: (Term | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
const complete = (g: Goal, c: Callee, s0: (Term | null)[], refl: boolean, nfFirst = false): Applied | null => {
  const sol = s0.slice();
  const o = openMeta(c.T, c.n, solH(g, sol));
  if (!o) return null;
  const f: Fill = { g, c, sol, via: new Array(c.n).fill(null), prem: o.doms.map((dm, j) => !sol[j] && isPrem(dm.A, g.d)), o, nfFirst };
  if (!fitPremises(f) || (refl && !reflPremises(f)) || !closedConsts(f) || f.sol.some((s, j) => !s && !f.prem[j])) return null;
  return argsOf(f);
};
// a template's ~ arguments left open after unification: a closed constant of that type (a laws record,
// Spans.Span.laws()); a ~ argument is never a hole
const closedConsts = (f: Fill): boolean => {
  const { g, c } = f;
  for (let j = 0; j < (c.x ?? 0); j++) {
    if (f.sol[j] || f.via[j]) continue;
    const A = attempt(FUEL_NF, () => lower(f.o.doms[j].A, LD(g)));
    if (!A) return false;
    let found = false;
    for (const L of bucket(BK.apply, headKey(A)).slice(0, 48)) {
      if (L.np !== 0 || L.n !== 0 || !usableLemma(g, L)) continue;
      const T = attempt(FUEL_NF, () => lower(BK.raw[L.k].T, 0));
      const s2 = f.sol.slice();
      if (!T || !match(A, T, s2, g.d)) continue;
      s2.forEach((x, i) => { f.sol[i] = x; });
      f.sol[j] = B.Ref(L.k);
      f.prem[j] = false;
      found = true;
      break;
    }
    if (!found || !reopen(f)) return false;
  }
  return true;
};
const reopen = (f: Fill): boolean => { const o = openMeta(f.c.T, f.c.n, solH(f.g, f.sol)); if (o) f.o = o; return o !== null; };
const fitPremises = (f: Fill): boolean => {
  const { g } = f;
  const facts = factsOf(g);
  for (let round = 0; round < 3; round++) {
    let progress = false;
    for (let j = 0; j < f.c.n; j++) {
      if (!f.prem[j] || f.via[j]) continue;
      const dom = f.o.doms[j];
      const A = attempt(FUEL_NF, () => lower(dom.A, LD(g)));
      if (!A) continue;
      const qt = B.quant_dem(dom.q, g.qt);
      const fit = (p: Term) => facts.some((fa) => {
        if (fa.empty || !usable(fa, qt)) return false;
        // the fact read as stated, then in normal form (nfFirst: the other way round)
        const [r1, r2] = f.nfFirst ? [fa.N, fa.T] : [fa.T, fa.N];
        let s2 = f.sol.slice();
        if (!match(p, r1, s2, g.d) && !match(p, r2, (s2 = f.sol.slice()), g.d)) return false;
        s2.forEach((x, i) => { f.sol[i] = x; });
        f.via[j] = fa.pf;
        return true;
      });
      // a premise read as stated, or in normal form: the first that fits a fact wins (nfFirst: the other order)
      if (f.nfFirst) { const An = nf(dom.A, LD(g)); if ((An && fit(An)) || fit(A)) progress = true; }
      else { const An = fit(A) ? null : nf(dom.A, LD(g)); if (f.via[j] || (An && H(An) !== H(A) && fit(An))) progress = true; }
    }
    if (!progress) return true;
    if (!reopen(f)) return false;
  }
  return true;
};
const reflPremises = (f: Fill): boolean => {
  const open = (t: Term) => t.$ === "Var" && t.i >= META && !f.sol[t.i - META] && !f.prem[t.i - META];
  for (let j = 0; j < f.c.n; j++) {
    if (!f.prem[j] || f.via[j]) continue;
    const A = attempt(FUEL_NF, () => lower(f.o.doms[j].A, LD(f.g)));
    if (A?.$ !== "Eql") continue;
    const [x, v] = open(A.b) && !hasMeta(A.a) ? [A.b, A.a] : open(A.a) && !hasMeta(A.b) ? [A.a, A.b] : [null, null];
    if (!x || !closedBelow(v, f.g.d)) continue;
    f.sol[x.i - META] = v;
    if (!reopen(f)) return false;
  }
  return true;
};
// the call's arguments: a value, a fact's proof, or a HOLE for a premise (the checker gives its goal)
const argsOf = (f: Fill): Applied | null => {
  const { g, c } = f;
  const args: string[] = [];
  let holes = 0;
  for (let j = 0; j < c.n; j++) {
    const s = f.sol[j], v = f.via[j];
    if (s || v) { args.push(s ? sh(g, s) : v!); continue; }
    if (attempt(FUEL_NF, () => hasMeta(lower(f.o.doms[j].A, LD(g)))) !== false) return null;
    args.push(HOLE);
    holes++;
  }
  return { args, holes, sol: f.sol };
};
const applyAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  const targets = targetsOf(n);
  if (!targets.length) return [];
  const callees = [...hypCallees(g), ...(canRecurse(g) ? [ihCallee(g)] : []), ...lemmaCands(g, targets)];
  const swapped = BK.raw["Equal.sym"] ? targets.filter((t) => t.$ === "Eql").map((t) => B.Eql(t.b, t.a, t.T)) : [];
  const found: { c: Callee; r: Applied; spec: number; sym: Term | null }[] = [];
  for (const c of [...callees, ...lemmaCands(g, swapped).filter((x) => !callees.some((y) => y.text === x.text))]) {
    if (late()) throw TIMEOUT;
    for (const [ts, sym] of [[targets, null], [swapped, swapped[0] ?? null]] as [Term[], Term | null][]) {
      if (!ts.length) continue;
      const { sols, spec } = conclSols(g, c, ts);
      for (const s of sols.slice(0, 2)) {
        const r = complete(g, c, s, false);
        if (r && descends(g, c, r.sol, r.args)) found.push({ c, r, spec, sym });
      }
    }
    if (found.length >= 32) break;
  }
  found.sort((a, b) => (a.c.kind === "lemma" ? 1 : 0) - (b.c.kind === "lemma" ? 1 : 0) || b.spec - a.spec || (a.sym ? 1 : 0) - (b.sym ? 1 : 0));
  return found.map(({ c, r, sym }, i) => {
    const call = callText(c, r.args);
    const text = sym ? symText(g, sym, call) : call;
    return mkAlt(n, "apply:" + c.kind, text, 1 + i * 0.01 + r.holes * 0.1, (ps) => tm(text, ps));
  });
};
// a constructor of a datatype of facts (a pair, an Or): one subgoal per field, each a fact
const ctorAlts = (n: GNode, w: Term): (Alt | null)[] => {
  const g = n.g;
  const adt = w.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(g.book, w, g.ctx, g.own.k)) : null;
  if (!adt || adt.c.length === 0 || adt.c.length > 4 || (adt.c.length === 1 && adt.c[0].n === 0) || !isProp(g.ty)) return [];
  return adt.c.map((ctr: Term) => {
    const s = B.name_show(g.own.file, ctr.k) + "{" + Array(ctr.n).fill(HOLE).join(", ") + "}";
    const a = mkAlt(n, "ctor", s, 1 + ctr.n * 0.1, (ps) => tm(s, ps));
    // a field that is a witness (data) no search can give: the alternative dies at its first reach
    const open0 = a.probe!;
    a.probe = null;
    a.open = () => {
      const r = tryCapture(g, open0);
      if (!r || r.holes.some((h) => !isProp(h.ty))) return null;
      return kidsFrom(a, r.holes);
    };
    return a;
  });
};
type RwCand = { base: Term; from: Term; to: Term; e: () => string; ekey: string; holes: number; tag: string; score: number; blocker?: boolean };
const RW_NODES = 2000;
const rewriteAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  if (n.rws >= MAX_RW) return [];
  const bases: Term[] = [];
  for (const t of [nf(g.ty, LD(g)), nf(g.ty, LD(g), true), attempt(FUEL_NF, () => lower(g.ty, LD(g)))])
    if (t && size(t, RW_NODES) <= RW_NODES && !bases.some((x) => H(x) === H(t))) bases.push(t);
  const cands: RwCand[] = [];
  const hyps = hypRules(g);
  for (const [bi, base] of bases.entries()) rwCands(g, base, bi > 0, hyps, cands);
  cands.sort((a, b) => a.score - b.score);
  // a lemma rewrite should unstick evaluation: where a lemma rewrites a position the goal is stuck on, lemma
  // rewrites go nowhere else (facts, local and few, keep every position)
  if (cands.some((c) => c.tag === "rw:lemma" && c.blocker)) {
    const keep = cands.filter((c) => c.tag !== "rw:lemma" || c.blocker);
    cands.length = 0;
    cands.push(...keep);
  }
  const out: (Alt | null)[] = substAlts(n);
  const seen = new Set<number>();
  const counts = cands.map((c) => (contains(c.to, H(c.from)) ? 0 : occurrences(c.base, H(c.from))));
  const sites = [
    ...cands.filter((_, i) => counts[i] > 0).map((c) => ({ c, at: -1 })),
    ...cands.flatMap((c, i) => (counts[i] > 1 && counts[i] <= 4 ? Array.from({ length: counts[i] }, (_, at) => ({ c, at })) : [])),
  ];
  let open = 0;
  for (const { c, at } of sites) {
    if (open >= 16 && c.holes > 0) continue;
    const fh = H(c.from);
    // one candidate per (base, subterm, replacement, position, evidence): what fixes its result and its
    // justification (the checker may refuse one justification of a result and not another)
    const sk = mixH(H(c.base), fh, H(c.to), at + 1, strH(c.ekey));
    if (seen.has(sk)) continue;
    seen.add(sk);
    if (c.holes > 0 && open++ >= 16) continue;
    // nothing is printed or rebuilt until the search reaches the step (a goal over machine words is large)
    const m = c.holes;
    let P = "", e = "", done: string | null = null;
    const a = mkAlt(n, c.tag, null, 1 + c.score * 0.1 + m * 0.1,
      (ps) => ({ t: "rw", e: tm(e, ps.slice(0, m)), P, k: done !== null ? tm(done) : ps[m] }), "%" + c.ekey.replace(/^[01]/, "").replace(/\u0000/g, "?") + " (" + c.tag + ")");
    a.holes = m + 1;
    a.quick = m === 0;
    a.lazy = () => {
      e = c.e();
      P = show(replace(c.base, fh, B.Var("_", g.d), at), [...g.names, "_"], g.own.file);
      done = closingText(g, replace(c.base, fh, c.to, at));
      a.note = "%" + e.replace(/\u0000/g, "?") + " : " + clip(P, 160);
      return "%" + e + " : " + P + "; " + (done ?? HOLE);
    };
    out.push(a);
  }
  return out;
};
// subst, J in full: a hypothesis h : {v == x} with x a variable of the context abstracts the goal over the
// endpoint x and over the proof h itself (%E@h : P; ..): what an indexed constructor's equation field
// needs, where the goal names both the index and the proof (Num{n, h} : Expr<t> with h : {TNum == t})
const substAll = (t: Term, h: number, by: Term): Term => {
  if (H(t) === h) return by;
  const go = (x: Term) => substAll(x, h, by);
  switch (t.$) {
    case "App": return B.App(go(t.f), go(t.x));
    case "Ctr": return B.Ctr(t.k, t.x.map(go));
    case "ADT": return B.ADT(t.k, t.x.map(go), undefined, t.r);
    case "Eql": return B.Eql(go(t.a), go(t.b), go(t.T));
    case "Lam": return B.Lam(t.k, t.i, go(t.f), undefined, t.q);
    case "All": return B.All(t.q, t.k, t.i, go(t.A), go(t.B));
    case "Typ": return B.Typ(go(t.g));
    default: return t;
  }
};
const substAlts = (n: GNode): Alt[] => {
  const g = n.g, out: Alt[] = [];
  const raw = attempt(FUEL_NF, () => lower(g.ty, LD(g)));
  if (!raw) return out;
  for (const f of factsOf(g)) {
    if (f.i < 0 || out.length >= 4) continue;
    const E = f.T;
    if (E?.$ !== "Eql") continue;
    const x = E.b;
    if (x.$ !== "Var" || x.i >= g.d || x.i === f.i || contains(E.a, H(x)) || !contains(raw, H(x))) continue;
    const names = [...g.names, "_"];
    const En = fresh(g, "E", new Set(g.names));
    names[f.i] = En;
    const P = attempt(FUEL_NF, () => show(substAll(substAll(raw, H(x), B.Var("_", g.d)), H(B.Var(g.names[f.i], f.i)), B.Var(En, f.i)), names, g.own.file));
    if (!P) continue;
    out.push(mkAlt(n, "rw:subst", "%" + En + "@" + g.names[f.i] + " : " + P + "; " + HOLE, 0.8, (ps) => ({ t: "rw", e: tm(En + "@" + g.names[f.i]), P, k: ps[0] })));
  }
  return out;
};
const closingText = (g: Goal, G: Term): string | null => {
  if (G.$ === "Eql" && H(G.a) === H(G.b)) return "{==}";
  const h = H(G);
  return factsOf(g).find((f) => !f.empty && usable(f, g.qt) && (H(f.T) === h || H(f.N) === h))?.pf ?? null;
};
type RwSite = { base: Term; subs: Map<number, Term>; hyps: Map<string, RwRule[]>; score: (from: Term, base: number) => number; blk: (from: Term) => boolean };
const rwCands = (g: Goal, N: Term, isRaw: boolean, hyps: Map<string, RwRule[]>, cands: RwCand[]) => {
  const subs = new Map<number, Term>();
  subterms(N, subs);
  const blk: Term[] = [];
  blockers(N, blk);
  const blkKeys = new Set(blk.map(H));
  const site: RwSite = { base: N, subs, hyps, score: (from, base) => base + (blkKeys.has(H(from)) ? 0 : 1) + (isRaw ? 0.2 : 0), blk: (from) => blkKeys.has(H(from)) };
  for (const f of factsOf(g)) {
    if (!usable(f, g.qt)) continue;
    for (const E of f.N && f.N !== f.T ? [f.T, f.N] : [f.T]) {
      if (E?.$ !== "Eql" || H(E.a) === H(E.b) || !site.subs.has(H(E.b)) || !/^(Var|App|Ctr|Lit)$/.test(E.b.$)) continue;
      cands.push({ base: site.base, from: E.b, to: E.a, e: () => f.pf, ekey: f.pf, holes: 0, tag: "rw:fact", score: site.score(E.b, 0) });
    }
  }
  calleeRws(g, site, cands);
};
type RwRule = { c: Callee; side: 0 | 1; tag: string };
const hypRules = (g: Goal): Map<string, RwRule[]> => {
  const out = new Map<string, RwRule[]>();
  for (const c of hypCallees(g)) {
    const E = attempt(FUEL_NF, () => { const o = openMeta(c.T, c.n); return o ? lower(o.concl, LD(g)) : null; });
    if (E?.$ !== "Eql") continue;
    for (const side of [0, 1] as const) {
      const t = side === 0 ? E.a : E.b, hk = headKey(t);
      if (hk.startsWith("R:") || (hk === "V" && t.$ === "App")) out.set(hk, [...(out.get(hk) ?? []), { c, side, tag: "rw:hyp" }]);
    }
  }
  return out;
};
const calleeRws = (g: Goal, site: RwSite, cands: RwCand[]) => {
  const ih = canRecurse(g) ? ihCallee(g) : null;
  const ihEq = ih && attempt(FUEL_NF, () => { const o = openMeta(ih.T, ih.n); return o ? lower(o.concl, LD(g)) : null; });
  for (const s of site.subs.values()) {
    const hk = headKey(s);
    // local rules (hypotheses, the induction hypothesis) and lemmas, each by s's head and the wildcard
    const entries: RwRule[] = bucket(site.hyps, hk).slice();
    if (ih && ihEq?.$ === "Eql" && hk.startsWith("R:")) for (const side of [0, 1] as const) if (headKey(side === 0 ? ihEq.a : ihEq.b) === hk) entries.push({ c: ih, side, tag: "rw:ih" });
    for (const { L, side } of bucket(BK.rw, hk)) if (usableLemma(g, L) && entries.length <= 24) entries.push({ c: lemmaCallee(g, L), side, tag: "rw:lemma" });
    for (const en of entries) {
      if (late()) throw TIMEOUT;
      const { sols } = conclSols(g, en.c, [s], (o) => (o.$ === "Eql" ? (en.side === 0 ? o.a : o.b) : null));
      for (const s0 of sols.slice(0, 2)) {
        const r0 = complete(g, en.c, s0, true);
        const r = r0 && descends(g, en.c, r0.sol, r0.args) ? r0 : null;
        const o2 = r && openMeta(en.c.T, en.c.n, solH(g, r.sol));
        const E = o2 && attempt(FUEL_NF, () => lower(o2.concl, LD(g)));
        if (!r || E?.$ !== "Eql" || hasMeta(E)) continue;
        const to = en.side === 0 ? E.b : E.a;
        if (H(to) === H(s)) continue;
        const call = callText(en.c, r.args);
        if (en.side === 0 && !BK.raw["Equal.sym"]) continue;
        cands.push({ base: site.base, from: s, to, e: () => (en.side === 0 ? symText(g, E, call) : call), ekey: en.side + call, holes: r.holes, tag: en.tag,
          score: site.score(s, en.c.n === 0 ? -0.5 : en.c.kind === "lemma" ? 0.5 : 0), blocker: site.blk(s) });
      }
    }
  }
};

// ---- lift: the goal as a helper def over its context, so its parameters can be split with descent.
// With a stuck call t generalized: a parameter x, an equation hx: {x == t}, t replaced by x in the goal
// and the facts that name it; splitting x then decides the call (case analysis on a computed value) ----
const liftAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  if (g.own.level >= MAX_LEVEL || g.d === 0 || n.lv > 2) return [];
  const names = g.names;
  if (new Set(names).size !== names.length || names.some((x) => x === "_" || x === "" || !/^[A-Za-z_]\w*$/.test(x))) return [];
  const underNode = n.up?.tag === "intro" && n.up.up.g.pend > 0;
  const underLambda = n.up?.tag === "intro" && n.up.up.g.pend === 0;
  const out: (Alt | null)[] = underLambda ? [liftAlt(n, null)] : [];
  try {
    const blk: Term[] = [];
    targetsOf(n);
    if (n.A) blockers(n.A, blk);
    for (const f of factsOf(g)) {
      if (f.i < 0) continue;
      f.A ??= nf(ann(g, f.i).T, LD(g), true, 20000) ?? f.N;
      if (f.A) blockers(f.A, blk);
    }
    if (!underNode && !underLambda && blk.some((t) => t.$ === "Var" && t.i < g.d)) out.push(liftAlt(n, null));
    let cases = 0;
    for (const f of factsOf(g)) {
      if (cases >= 2 || f.i >= 0 || !f.fwd) continue;
      const w = wnf(B.term_higher(f.T, g.env));
      const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
      if (adt?.$ === "ADT" && adt.c.length >= 2 && adt.c.length <= 4) { out.push(liftAlt(n, null, f)); cases++; }
    }
    const seen = new Set<number>();
    const rank = new Map(blk.map((t) => [t, (t.$ === "App" && isAtom(B.term_higher(t, g.env), g.d) ? 0 : 1e6) + size(t, 1e5)]));
    let made = 0;
    for (const t of [...blk].sort((x, y) => rank.get(x)! - rank.get(y)!)) {
      if (made >= 3) break;
      if (t.$ !== "App" || seen.has(H(t)) || !closedBelow(t, g.d)) continue;
      seen.add(H(t));
      const T = attempt(FUEL_NF, () => B.term_infer(g.book, g.lhs, B.term_higher(t, g.env), B.None(), g.ctx, g.d).ty);
      const w = T && wnf(T);
      const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
      const Tl = adt?.$ === "ADT" && adt.c.length >= 2 && adt.c.length <= 8 ? attempt(FUEL_NF, () => lower(T, LD(g))) : undefined;
      if (Tl) { out.push(liftAlt(n, { t, T: Tl })); made++; }
    }
  } catch (e) { if (e === TIMEOUT) throw e; S.internal++; }
  return out;
};
const helperName = (own: Owner, sfx = ".g", used: Set<string> = new Set()): string => {
  const taken = new Set(Object.keys(BK.raw).map(shortOf));
  for (let i = 1; ; i++) {
    const nm = own.root + sfx + i;
    if (!taken.has(nm) && !used.has(nm) && !fileText(BK.entry).includes("def " + nm + "(")) return nm;
  }
};
const addTemp = (head: string, own: Owner): string | null => {
  const n0 = BK.book.order.length;
  try { withHols(() => B.parse_book(BK.book, BK.top, head + "\n  ?TODO\n", own.file?.ns ?? "", own.file?.al ?? {})); } catch { BK.book.order.length = n0; return null; }
  const hk = BK.book.order[n0];
  if (!hk || BK.raw[hk]?.$ !== "Def") { for (const k of BK.book.order.slice(n0)) delete BK.raw[k]; BK.book.order.length = n0; return null; }
  BK.temps.push(hk);
  BK.order.set(hk, own.order - 0.5 + BK.temps.length * 1e-6);
  BK.files.set(hk, own.file);
  BK.src.set(hk, { file: BK.entry, header: head, body: "  ?TODO", bodyLine: 0 });
  return hk;
};
const forget = (k: string) => { BK.strict.delete(k); BK.matched.delete(k); BK.enums.delete(k); };
const dropTemp = (hk: string) => {
  delete BK.raw[hk];
  const j = BK.book.order.indexOf(hk);
  if (j >= 0) BK.book.order.splice(j, 1);
  BK.order.delete(hk); BK.files.delete(hk); BK.src.delete(hk);
  forget(hk);
  const t = BK.temps.indexOf(hk);
  if (t >= 0) BK.temps.splice(t, 1);
};
const dropTemps = () => { for (const hk of [...BK.temps]) dropTemp(hk); };
const quantText = (g: Goal, i: number): string => B.quant_show(ann(g, i).q);
// fact: a derived fact of a sum type (an Or from the induction hypothesis) becomes a parameter, so the
// helper can split it: case analysis on a computed proof, as a generalized call is case analysis on a value
const liftAlt = (n: GNode, gen: { t: Term; T: Term } | null, fact?: Fact): Alt | null => {
  const g = n.g;
  const note = fact ? "a helper over the context and " + clip(fact.pf, 80) + ", to split it" : gen ? "a helper over the context, " + sh(g, gen.t) + " generalized" : "a helper over the context (its parameters can be split)";
  const a = mkAlt(n, fact ? "lift:case" : gen ? "lift:gen" : "lift", null, fact ? 2.5 : gen ? 3.5 : 3, (ps) => ps[0], note);
  a.open = () => {
    if (S.helpers >= MAX_HELPERS) { a.why = "the helper cap (" + MAX_HELPERS + ")"; return null; }
    const used = new Set([...g.names, ...(g.own.consts ?? []).map((c) => c.name)]);
    const x = gen ? fresh(g, "x", used) : "", hx = gen ? fresh(g, "h" + x, used) : "";
    const names = [...g.names, x];
    const th = gen ? H(gen.t) : 0;
    const xv = B.Var(x, g.d);
    const gen1 = (h: Term): { s: string; moved: boolean } | null => {
      const d = LD(g);
      const raw = attempt(FUEL_NF, () => lower(h, d));
      if (!raw) return null;
      if (!gen) return { s: show(raw, names, g.own.file), moved: false };
      const base = [raw, nf(h, d, true), nf(h, d)].find((m) => m && contains(m, th));
      return base ? { s: show(replace(base, th, xv), names, g.own.file), moved: true } : { s: show(raw, names, g.own.file), moved: false };
    };
    const first: string[] = [], later: string[] = [], argsFirst: string[] = [], argsLater: string[] = [];
    const movedIdx = new Set<number>();
    for (let i = 0; i < g.d; i++) {
      const r = gen1(ann(g, i).T);
      if (!r) return null;
      const p = quantText(g, i) + names[i] + ": " + r.s;
      if (r.moved) { movedIdx.add(i); later.push(p); argsLater.push(names[i]); } else { first.push(p); argsFirst.push(names[i]); }
    }
    const goal = gen1(g.ty);
    if (!goal || (gen && !goal.moved && movedIdx.size === 0)) return null;
    let params = first, args = argsFirst, pre = "", hname = "";
    if (gen) {
      for (let i = 0; i < g.d; i++) if (!movedIdx.has(i) && [...varsOf(lower(ann(g, i).T, i), new Set())].some((v) => movedIdx.has(v))) return null;
      if ([...varsOf(gen.t, new Set()), ...varsOf(gen.T, new Set())].some((v) => movedIdx.has(v))) return null;
      const ts = sh(g, gen.t), Ts = sh(g, gen.T);
      params = [...first, (isData(g, B.term_higher(gen.T, g.env)) ? "+" : "") + x + ": " + Ts, hx + ": {" + x + " == " + ts + " : " + Ts + "}", ...later];
      args = [...argsFirst, ts, "{==}", ...argsLater];
      const twice = [...varsOf(gen.t, new Set())].filter((v) => ann(g, v)?.q.$ === "Lone").map((v) => g.names[v]);
      pre = twice.map((v) => "+" + v + " = " + v + "; ").join("");
    }
    if (fact) {
      hname = fresh(g, "h", used);
      params = [...params, hname + ": " + sh(g, fact.T)];
      args = [...args, fact.pf];
      // a single-use binder the fact's proof names is also an argument: rebound reusable
      const twice = g.names.filter((v, i) => ann(g, i)?.q.$ === "Lone" && new RegExp("(?<![\\w.])" + v + "(?![\\w])").test(fact.pf));
      pre = twice.map((v) => "+" + v + " = " + v + "; ").join("");
    }
    // inside a template the helper is one too: the owner's ~ constants come first, by the same names (its
    // types already print them so), and the call passes them on (a constant is a closed ~ argument)
    const consts = g.own.consts ?? [];
    if (consts.length) {
      const cps: string[] = [];
      for (const c of consts) {
        const T = g.book.tlds[c.key]?.T;
        const Ts = T && attempt(FUEL_NF, () => show(lower(T, 0), [], g.own.file));
        if (!Ts) { a.why = "a ~ parameter's type does not print"; return null; }
        cps.push("~" + c.name + ": " + Ts);
      }
      params = [...cps, ...params];
      args = [...consts.map((c) => "~" + c.name), ...args];
    }
    const name = helperName(g.own);
    const head = "def " + name + "(\n  " + params.join(",\n  ") + ") ->\n  " + goal.s + ":";
    const hk = addTemp(head, g.own);
    if (!hk) { a.why = "the helper does not parse: " + clip(head.split("\n").join(" "), 300); return null; }
    const se = stmtErr(hk);
    if (se || !tryText(g, pre + name + "(" + args.join(", ") + ")")) { a.why = se ? "its statement does not check: " + firstLine(se) : "the call does not check: " + firstLine(lastErr); dropTemp(hk); return null; }
    S.helpers++;
    const call = pre + name + "(" + args.join(", ") + ")";
    a.build = (ps) => ({ t: "def", name, head, body: ps[0], call });
    const rg = rootGoal(owner(hk, g.own.level + 1, g.own.root));
    if (rg) rg.prefer = fact ? hname : gen ? x : undefined;
    const kid = rg && mkNode(rg, a, 0, 0);
    return kid ? [kid] : null;
  };
  return a;
};

// ---- evidence: what a data def must satisfy (laws that name it, --spec examples), on small inputs ----
type Inst = { law: string; vals: (Term | null)[] } | { ex: number };
type Example = { call: string; expect: string; a: Term; b: Term };
const MAX_VALS = 6, MAX_INSTS = 48, MAX_LEAVES = 14, MAX_COMBOS = 4000;
const valuesOf = (A: Term, depth: number, nest = 0): Term[] => {
  const w = nest > 8 ? null : wnf(A);
  if (!w) return [];
  if (w.$ === "Typ") return [B.ADT("Bool", [], undefined, [])];
  if (w.$ !== "ADT") return [];
  if (/(^|[.:])Nat$/.test(w.k)) return [0, 1, 2, 3].map((v) => B.Lit("Nat", v));
  if (/(^|[.:])U32$/.test(w.k)) return [0, 1, 2].map((v) => B.Lit("U32", v));
  const adt = attempt(FUEL_NF, () => B.book_adt(BK.book, w, B.ctx_nil(), undefined));
  if (!adt || adt.c.length === 0) return [];
  const out: Term[] = [];
  for (const ctr of [...adt.c].sort((a: Term, b: Term) => a.n - b.n)) {
    if (out.length >= MAX_VALS) break;
    if (ctr.n > 0 && depth <= 0) continue;
    const tel = attempt(FUEL_NF, () => B.tele_fill(BK.book, ctr.T, w.x, B.ctx_nil(), undefined));
    if (!tel) continue;
    let rows: { xs: Term[]; cur: Term }[] = [{ xs: [], cur: tel }];
    for (let f = 0; f < ctr.n && rows.length; f++) {
      const next: { xs: Term[]; cur: Term }[] = [];
      for (const r of rows) {
        const c = attempt(FUEL_NF, () => B.tele_head(BK.book, r.cur, B.ctx_nil(), undefined));
        if (!c) continue;
        const fw = wnf(c.A);
        for (const v of valuesOf(c.A, fw?.$ === "ADT" && fw.k === w.k ? depth - 1 : depth, nest + 1).slice(0, f === 0 ? 3 : 2)) {
          if (next.length >= MAX_VALS) break;
          next.push({ xs: [...r.xs, v], cur: c.B(B.term_higher(v, null)) });
        }
      }
      rows = next;
    }
    for (const r of rows) if (out.length < MAX_VALS && r.xs.length === ctr.n) out.push(B.Ctr(ctr.k, r.xs));
  }
  return out;
};
const refsOf = (T: Term): Set<string> => {
  const out = new Set<string>();
  const t = attempt(FUEL_NF, () => lower(T, 0));
  if (t) some(t, (x) => { if (x.$ === "Ref") out.add(x.k); else if (x.$ === "App") { const f = B.term_unapply(x)[0]; if (f.$ === "Ref") out.add(f.k); } return false; });
  return out;
};
const lawsOf = (k: string): string[] =>
  Object.keys(BK.raw).filter((l) => l !== k && BK.raw[l]?.$ === "Def" && !l.includes("~") && !BK.raw[l].b && refsOf(BK.raw[l].T).has(k) && isLemmaType(l));
const lawTerms = new Map<string, Term>();
const instancesOf = (l: string): Inst[] => {
  let rows: { vals: (Term | null)[]; t: Term }[] = [{ vals: [], t: BK.raw[l].T }];
  for (let i = 0; i < 12; i++) {
    const next: typeof rows = [];
    let done = false;
    for (const r of rows) {
      const s = asAll(r.t);
      if (!s) { done = true; next.push(r); continue; }
      if (isProp(s.A)) { next.push({ vals: [...r.vals, null], t: s.B(B.Var("h", FRESH + i)) }); continue; }
      for (const v of valuesOf(s.A, 2)) if (next.length < MAX_INSTS) next.push({ vals: [...r.vals, v], t: s.B(B.term_higher(v, null)) });
    }
    rows = next;
    if (done || rows.length === 0) break;
  }
  return rows.map((r) => ({ law: l, vals: r.vals }));
};
// do two closed terms evaluate to the same value? true, false, or null (stuck, a hole, out of fuel)
const sameValue = (a: Term, b: Term, depth = 0): boolean | null => {
  let x = wnf(a), y = wnf(b);
  if (!x || !y || x.$ === "Hol" || y.$ === "Hol") return null;
  if (depth === 0 && attempt(FUEL_NF, () => B.term_compare("EQ", BK.book, a, b, 0)) === true && !hasHole(a) && !hasHole(b)) return true;
  if (depth > 24) return null;
  if (x.$ === "Lit" && y.$ === "Lit") return x.k === y.k ? x.v === y.v : null;
  if (x.$ === "Lit") x = B.lit_step(x);
  if (y.$ === "Lit") y = B.lit_step(y);
  if (x.$ !== "Ctr" || y.$ !== "Ctr") return null;
  if (x.k !== y.k || x.x.length !== y.x.length) return false;
  let all: boolean | null = true;
  for (let i = 0; i < x.x.length; i++) {
    const r = sameValue(x.x[i], y.x[i], depth + 1);
    if (r === false) return false;
    if (r === null) all = null;
  }
  return all;
};
const hasHole = (t: Term): boolean => attempt(FUEL_NF, () => some(lowerB(t, 0, { n: 4000 }, true), (x) => x.$ === "Hol")) !== false;
const every = (rs: (boolean | null)[]): boolean | null => (rs.some((r) => r === false) ? false : rs.length && rs.every((r) => r === true) ? true : null);
const decide = (t: Term, depth: number): boolean | null => {
  const c = depth > 6 ? null : wnf(t);
  if (!c) return null;
  if (c.$ === "Eql") return sameValue(c.a, c.b);
  if (c.$ === "All") {
    if (isProp(c.A)) { const p = decide(c.A, depth + 1); return p === true ? decide(c.B(B.Var("h", FRESH + 400 + depth)), depth + 1) : null; }
    return every(valuesOf(c.A, 2).slice(0, 4).map((x) => decide(c.B(B.term_higher(x, null)), depth + 1)));
  }
  const adt = c.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(BK.book, c, B.ctx_nil(), undefined)) : null;
  if (adt?.c.length !== 1 || adt.c[0].n === 0) return null;
  const parts: (boolean | null)[] = [];
  let cur = attempt(FUEL_NF, () => B.tele_fill(BK.book, adt.c[0].T, c.x, B.ctx_nil(), undefined));
  for (let f = 0; cur && f < adt.c[0].n; f++) {
    const h = attempt(FUEL_NF, () => B.tele_head(BK.book, cur, B.ctx_nil(), undefined));
    if (!h) return null;
    parts.push(decide(h.A, depth + 1));
    cur = h.B(B.Var("p", FRESH + 500 + depth * 8 + f));
  }
  return every(parts);
};
let examples: Example[] = [];
const holds = (n: Inst): boolean | null => withFuel(FUEL_NFS * 8, () => {
  try {
    if ("ex" in n) { const e = examples[n.ex]; return sameValue(B.term_higher(e.a, null), B.term_higher(e.b, null)); }
    const L = lawTerms.get(n.law);
    if (!L) return null;
    let t = B.term_higher(L, null);
    for (let i = 0; i < n.vals.length; i++) {
      const s = asAll(t);
      if (!s) return null;
      if (n.vals[i] === null) {
        const p = wnf(s.A);
        if (p?.$ !== "Eql" || sameValue(p.a, p.b) !== true) return null;
        t = s.B(B.Var("h", FRESH + i));
      } else t = s.B(B.term_higher(n.vals[i], null));
    }
    return decide(t, 0);
  } catch (e) { if (e === TIMEOUT) throw e; return null; }
});
const instLabel = (n: Inst): string => ("ex" in n ? examples[n.ex].call + " == " + examples[n.ex].expect : shortOf(n.law) + "(" + n.vals.map((v) => (v ? B.term_show(v) : "_")).join(", ") + ")");
const parseExamples = (k: string, spec: { examples: { call: string; expect: string }[] } | undefined): Example[] | string => {
  const out: Example[] = [];
  const g0 = { own: owner(k), names: [] as string[], env: null } as unknown as Goal;
  for (const e of spec?.examples ?? []) {
    try {
      const a = B.term_lower(parseAt(g0, e.call).tm), b = B.term_lower(parseAt(g0, e.expect).tm);
      out.push({ call: e.call, expect: e.expect, a, b });
    } catch (x) { return "a --spec example does not parse: " + e.call + " == " + e.expect + "\n" + errText(x); }
  }
  return out;
};
const installed = new Map<string, Term>();
const resetNf = (k: string) => { forget(k); BK.nfs.clear(); nfObj = new WeakMap(); patMemo = new WeakMap(); nfHeld = 0; };
const install = (k: string, v: Term) => { if (!installed.has(k)) installed.set(k, BK.raw[k]); BK.raw[k] = { ...installed.get(k), v }; resetNf(k); };
const uninstall = (k: string) => { const d = installed.get(k); if (!d) return; BK.raw[k] = d; installed.delete(k); resetNf(k); };

// ---- synthesis: shapes (no match, a match on a parameter, and a match on its recursive field) times
// leaves per arm (small terms Bend types at the arm: variables, constructors, calls, the recursive call,
// whose descent Bend judges at the arm's own lhs). Each leaf is first tried alone, the other arms ?TODO:
// evidence that fails there fails for every completion, so the leaf goes. The rest combine, simplest
// first, until one passes every decided instance ----
type Shape = { label: string; arms: Goal[]; pf: (leaves: string[]) => Pf };
const shapesOf = (k: string, root: Goal): Shape[] => {
  const out: Shape[] = [];
  const all = introAll(root);
  if (all) out.push({ label: "no match", arms: [all.g], pf: (ls) => ({ t: "intro", xs: all.xs, k: tm(ls[0]) }) });
  for (let j = 0; j < root.pend; j++) {
    const sp = split(root, j);
    if (!sp || sp.arms.length > 6) continue;
    const leaves = sp.arms.map((a) => introAll(a.g));
    if (leaves.some((l) => !l)) continue;
    out.push({ label: "match " + sp.x, arms: leaves.map((l) => l!.g), pf: (ls) => ({ t: "mt", pre: sp.pre, x: sp.x, arms: sp.arms.map((a, i) => ({ ...a, k: { t: "intro", xs: leaves[i]!.xs, k: tm(ls[i]) } })) }) });
    // in each arm with a field of the scrutinee's own type (its recursion), that field matched too
    const scrT = (() => { let t = root.ty; for (let i = 0; i < j; i++) { const s = asAll(t); if (!s) return 0; t = s.B(B.Var("_", FRESH + i)); } const s = asAll(t); return s ? attempt(FUEL_NF, () => H(lower(s.A, 0))) ?? 0 : 0; })();
    const subs = sp.arms.map((a, ai) => {
      let t = a.g.ty;
      for (let f = 0; f < sp.arms[ai].fields.length; f++) {
        const s = asAll(t);
        if (!s) break;
        if (attempt(FUEL_NF, () => H(lower(s.A, 0))) === scrT) {
          const inner = split(a.g, f);
          if (inner && inner.arms.length <= 4) {
            const ls = inner.arms.map((b) => introAll(b.g));
            if (ls.every(Boolean)) return { inner, ls: ls as { g: Goal; xs: Bound[] }[] };
          }
        }
        t = s.B(B.Var("_", FRESH + f));
      }
      return null;
    });
    if (!subs.some(Boolean)) continue;
    const arms2: Goal[] = [];
    sp.arms.forEach((a, i) => { const s = subs[i]; if (s) arms2.push(...s.ls.map((l) => l.g)); else arms2.push(leaves[i]!.g); });
    out.push({
      label: "match " + sp.x + ", then its recursive field", arms: arms2,
      pf: (ls) => {
        let at = 0;
        return { t: "mt", pre: sp.pre, x: sp.x, arms: sp.arms.map((a, i): Arm => {
          const s = subs[i];
          if (!s) return { ...a, k: { t: "intro", xs: leaves[i]!.xs, k: tm(ls[at++]) } };
          return { ...a, k: { t: "mt", pre: s.inner.pre, x: s.inner.x, arms: s.inner.arms.map((b, bi) => ({ ...b, k: { t: "intro", xs: s.ls[bi].xs, k: tm(ls[at++]) } })) } };
        }) };
      },
    });
  }
  return out;
};
const callsByResult = (head: string, k: string): string[] => {
  const ord = BK.order.get(k) ?? Infinity;
  const out: string[] = [];
  for (const f of BK.book.order) {
    if (out.length >= 12) break;
    const t = BK.raw[f];
    if (f === k || t?.$ !== "Def" || t.n < 1 || t.n > 3 || (BK.order.get(f) ?? Infinity) >= ord || f.includes("~") || (t.v === null && !t.b) || t.i) continue;
    const o = attempt(20000, () => openMeta(t.T, t.n));
    const c = o && attempt(20000, () => lower(o.concl, t.n));
    if (c && headKey(c) === head && !isLemmaType(f)) out.push(f);
  }
  return out.reverse();
};
// small terms that check at g, one per normal form, ranked: variables and constructors, the recursive
// call and constructors around it, the entry's calls, Base's; shorter first
const leavesAt = (g: Goal, k: string): string[] => {
  // the target is opaque here: leaves are told apart by their normal forms, never through a candidate body
  uninstall(k);
  const found: { s: string; rank: number }[] = [], seen = new Set<string>(), values = new Set<number>();
  const add = (s: string, rank: number) => {
    if (seen.has(s) || found.length >= MAX_LEAVES * 4 || late()) return;
    seen.add(s);
    if (!tryText(g, s)) { if (process.env.BEND_SYNTH_TRACE && rank === 1) console.error("[leaf] " + s + " rejected: " + firstLine(lastErr)); return; }
    const v = attempt(FUEL_NF, () => { const t = parseAt(g, s).tm; return H(nf(t, LD(g)) ?? lower(t, LD(g))); });
    if (v !== undefined && values.has(v)) return;
    if (v !== undefined) values.add(v);
    found.push({ s, rank });
  };
  const vars = g.names.filter((x, i) => x !== "_" && ann(g, i)?.q.$ !== "None" && g.names.indexOf(x, i + 1) < 0);
  const w = wnf(g.ty);
  const adt = w?.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(g.book, w, g.ctx, g.own.k)) : null;
  const ctrs: { name: string; n: number }[] = (adt?.c ?? []).map((c: Term) => ({ name: B.name_show(g.own.file, c.k), n: c.n }));
  const ctrText = (name: string, args: string[]) => (/(^|\.)Succ$/.test(name) && args.length === 1 ? "1n+" + args[0] : name + "{" + args.join(", ") + "}");
  const atoms = [...(w?.$ === "ADT" && /(^|[.:])Nat$/.test(w.k) ? ["0n"] : []), ...vars, ...ctrs.filter((c) => c.n === 0).map((c) => c.name + "{}")];
  const combos = (m: number): string[][] => (m === 0 ? [[]] : combos(m - 1).flatMap((c) => atoms.map((a) => [...c, a])));
  atoms.forEach((a) => add(a, 0));
  for (const c of ctrs.filter((c) => c.n > 0 && c.n <= 2)) for (const args of combos(c.n).slice(0, 32)) add(ctrText(c.name, args), 0);
  const head = attempt(FUEL_NF, () => headKey(lower(g.ty, LD(g))));
  for (const f of [k, ...callsByResult(head ?? "", k)]) {
    const n = BK.raw[f]?.n ?? 0;
    if (n < 1 || n > 3) continue;
    const name = B.name_show(g.own.file, f), rank = f === k ? 1 : BK.raw[f].b ? 3 : 2;
    for (const args of combos(n).slice(0, 27)) {
      const call = name + "(" + args.join(", ") + ")";
      add(call, rank);
      if (found.some((x) => x.s === call)) for (const c of ctrs.filter((c) => c.n === 1)) add(ctrText(c.name, [call]), rank);
      // one more step: a call whose argument is a call (f(g(x))), only for the ranked-first callees
      if (rank <= 2) for (const c2 of found.filter((x) => x.rank === 1 && x.s !== call).slice(0, 2)) add(name + "(" + [c2.s, ...args.slice(1)].join(", ") + ")", rank + 1);
    }
  }
  return found.sort((a, b) => a.rank - b.rank || a.s.length - b.s.length).slice(0, MAX_LEAVES).map((x) => x.s);
};
function* combosOf(sizes: number[], max: number): Generator<number[]> {
  let made = 0;
  const total = sizes.reduce((s, n) => s + n - 1, 0);
  for (let sum = 0; sum <= total; sum++) {
    const go = function* (i: number, left: number, acc: number[]): Generator<number[]> {
      if (i === sizes.length) { if (left === 0) yield acc; return; }
      for (let r = 0; r <= Math.min(left, sizes[i] - 1); r++) yield* go(i + 1, left - r, [...acc, r]);
    };
    for (const c of go(0, sum, [])) { if (made++ >= max) return; yield c; }
  }
}
// a body for k under evidence: false if one decided instance fails, true if none fails and one holds
const judge = (k: string, body: string, insts: Inst[], holesOk: boolean): { v: Term; res: (boolean | null)[] } | null => {
  const r = attempt(FUEL_CHECK * 4, () => checkDef(k, body));
  if (!r || (!holesOk && r.holes.length)) return null;
  install(k, r.v);
  const res: (boolean | null)[] = [];
  for (const n of insts) { const x = holds(n); res.push(x); if (x === false) break; }
  if (process.env.BEND_SYNTH_TRACE) console.error("[judge] " + body.trim().split(/\n/).map((l) => l.trim()).join(" ; ") + "  =>  " + res.map((x) => (x === null ? "?" : x ? "+" : "-")).join(""));
  return { v: r.v, res };
};
type SynthState = { tried: number; pruned: number; shape: string; arms: { goal: Goal; leaves: string[] }[]; found?: Report };
// resumable: yields "time" when the slice ends mid-step (the step runs again), "tick" between steps
function* synthesize(k: string, own: Owner, ds: Src, insts: Inst[], laws: string[], st: SynthState, sketches: () => Shape[]): Generator<"time" | "tick", Report> {
  const step = function* <T>(f: () => T): Generator<"time", T> {
    for (;;) { try { return f(); } catch (e) { if (e !== TIMEOUT) throw e; yield "time"; } }
  };
  const root = yield* step(() => rootGoal(own));
  if (!root) return { status: "error", text: "# " + own.short + ": Bend gives no goal for its body (a template? write the ?TODO inside its body)" };
  const shapes = yield* step(() => shapesOf(k, root));
  const queue = [...shapes];
  const lawsText = laws.map(shortOf).join(", ") + (examples.length ? (laws.length ? " and " : "") + examples.length + " example(s)" : "");
  while (queue.length || sketches().length) {
    const sh = sketches().length ? sketches().shift()! : queue.shift()!;
    st.shape = sh.label;
    const leaves: string[][] = [];
    for (const g of sh.arms) leaves.push(yield* step(() => leavesAt(g, k)));
    st.arms = sh.arms.map((goal, i) => ({ goal, leaves: leaves[i] }));
    if (leaves.some((l) => l.length === 0)) continue;
    // each leaf alone, the other arms ?TODO: what fails there fails for every completion
    if (sh.arms.length > 1) for (let i = 0; i < sh.arms.length; i++) {
      const keep: string[] = [];
      for (const leaf of leaves[i]) {
        const body = bodyText(sh.pf(leaves.map((_, j) => (j === i ? leaf : "?TODO"))));
        const j = yield* step(() => judge(k, body, insts, true));
        if (!j || !j.res.includes(false)) keep.push(leaf); else st.pruned++;
        yield "tick";
      }
      leaves[i] = keep;
      st.arms[i].leaves = keep;
      if (keep.length === 0) break;
    }
    if (leaves.some((l) => l.length === 0)) continue;
    for (const pick of combosOf(leaves.map((l) => l.length), MAX_COMBOS)) {
      st.tried++;
      const body = bodyText(sh.pf(pick.map((r, i) => leaves[i][r])));
      const j = yield* step(() => judge(k, body, insts, false));
      yield "tick";
      if (!j || j.res.some((r) => r === false) || !j.res.some((r) => r === true)) continue;
      const n = j.res.filter((r) => r === true).length;
      const open = yield* step(() => undecided(k, j.v, sh, leaves, pick, insts));
      uninstall(k);
      const notes = open.map((o) => "# the evidence does not decide arm " + o.arm + ": " + o.alt + " also passes it");
      const head = "# " + own.short + ": SYNTHESIZED (" + st.tried + " bodies tried, " + st.pruned + " leaves refuted early): Bend accepts it, and it passes "
        + n + " decided instances of " + lawsText + ". Evidence, not a proof" + (laws.length ? ": prove the laws next" : "");
      if (open.length === sh.arms.length && sh.arms.length > 0) {
        return { status: "partial", text: "# " + own.short + ": the evidence (" + lawsText + ") does not pin a body down: this passes it, and so do bodies that answer differently (" + open.map((o) => o.alt).join("; ") + "). Add an example or a law.\n" + body, body };
      }
      const tidy = yield* step(() => trimPlus((x) => checkErr(k, x) === null, body));
      return { status: "synthesized", text: head + "\n" + tidy + (notes.length ? "\n" + notes.join("\n") : ""), body: tidy, edit: { file: ds.file, from: ds.header + "\n" + ds.body, to: ds.header + "\n" + tidy } };
    }
  }
  uninstall(k);
  const armText = st.arms.map((a, i) => "# arm " + (i + 1) + " (" + (a.goal.path || "/") + "): " + a.leaves.length + " leaves survive the evidence" + (a.leaves.length ? ": " + a.leaves.slice(0, 5).join(" | ") : "") + "\n" + goalLines(a.goal)).join("\n");
  return { status: "open", text: "# " + own.short + ": no body of the shapes tried passes " + lawsText + " (" + st.tried + " tried, " + st.pruned + " leaves refuted early). The last shape (" + st.shape + "):\n" + armText };
}
const undecided = (k: string, v: Term, sh: Shape, leaves: string[][], pick: number[], insts: Inst[]): { arm: string; alt: string }[] => {
  const inputs = inputsOf(k);
  const answers = (): (number | undefined)[] => inputs.map((xs) => {
    const call = xs.reduce((f: Term, x: Term) => B.App(f, B.term_higher(x, null)), B.Ref(k));
    const r = nf(call, 0, false, 200000);
    return r ? H(r) : undefined;
  });
  install(k, v);
  const mine = answers();
  const out: { arm: string; alt: string }[] = [];
  for (let i = 0; i < sh.arms.length && !late(); i++) {
    for (let r = 0; r < Math.min(leaves[i].length, 8); r++) {
      if (r === pick[i]) continue;
      const alt = pick.map((p, j) => leaves[j][j === i ? r : p]);
      const j = judge(k, bodyText(sh.pf(alt)), insts, false);
      if (!j || j.res.some((x) => x === false) || !j.res.some((x) => x === true)) continue;
      if (answers().some((a, q) => a !== undefined && mine[q] !== undefined && a !== mine[q])) { out.push({ arm: sh.arms[i].path || "/", alt: leaves[i][r] }); break; }
    }
  }
  install(k, v);
  return out;
};
const inputsOf = (k: string): Term[][] => {
  let rows: { xs: Term[]; t: Term }[] = [{ xs: [], t: BK.raw[k].T }];
  for (let j = 0; j < BK.raw[k].n; j++) {
    const next: typeof rows = [];
    for (const r of rows) {
      const s = asAll(r.t);
      if (!s) continue;
      for (const x of valuesOf(s.A, 2)) if (next.length < 16) next.push({ xs: [...r.xs, x], t: s.B(B.term_higher(x, null)) });
    }
    rows = next;
  }
  return rows.map((r) => r.xs);
};

// ---- answers ----
export type Report = {
  status: "proven" | "synthesized" | "partial" | "open" | "error" | "nothing" | "running"; text: string;
  body?: string; edit?: { file: string; from: string; to: string }; holes?: number; nodes?: number; ms?: number;
};
const HONEST = "# bend-synth is a helper, not the judge: PROVEN means Bend's checker accepted the text inside it; `bend <file> --check-only` decides.";
const goalLines = (g0: Goal): string => {
  const g = leafOf(g0);
  const ctx: string[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = ann(g, i);
    if (!a) continue;
    ctx.push("#   " + B.quant_show(a.q) + g.names[i] + " : " + clip(attempt(FUEL_NF, () => show(lower(a.T, i), g.names.slice(0, i), g.own.file)) ?? "?", 400));
  }
  return "# goal: " + clip(attempt(FUEL_NF, () => sh(g, lower(g.ty, LD(g)))) ?? "?", 2000) + (ctx.length ? "\n# context:\n" + ctx.join("\n") : "");
};
const triedLines = (n: GNode, max = 4): string => {
  const live = (n.alts ?? []).filter((a) => !a.dead && a.tag !== "intro").sort((a, b) => a.pn - b.pn).slice(0, max);
  const dead = (n.alts ?? []).filter((a) => a.dead && a.why && a.tag !== "intro").slice(0, 2);
  const needs = (a: Alt) => a.kids.filter((k) => !k.pf).slice(0, 2).map((k) => "\n#       needs: " + clip(attempt(FUEL_NF, () => sh(k.g, lower(k.g.ty, LD(k.g)))) ?? "?", 200)).join("");
  let s = "";
  if (live.length) s += "\n# tried (closest first):\n" + live.map((a) => "#   " + clip(a.note, 240) + (a.kids.length ? " (" + a.kids.filter((k) => !k.pf).length + " open)" + needs(a) : "")).join("\n");
  if (dead.length) s += "\n# rejected by Bend:\n" + dead.map((a) => "#   " + clip(a.note, 160) + "\n#     " + clip(a.why!, 240)).join("\n");
  return s || "\n# tried: no step applies (no lemma, fact or rewrite fits; it may need a lemma, a split or a helper)" + nearMisses(n);
};
const nearMisses = (n: GNode): string => {
  const t = n.raw ?? attempt(FUEL_NF, () => lower(n.g.ty, LD(n.g)));
  const hk = t && headKey(t);
  if (!hk || !/^(E\|)?(R|C|A):/.test(hk)) return "";
  const ls = (BK.apply.get(hk) ?? []).filter((L) => usableLemma(n.g, L)).slice(0, 3);
  return ls.length ? "\n# lemmas with the goal's head (compare their arguments):\n" + ls.map((L) => "#   " + B.name_show(n.g.own.file, L.k) + " : " + clip(attempt(FUEL_NF, () => { const o = openMeta(BK.raw[L.k].T, L.n); return o ? show(lower(o.concl, 0), [], n.g.own.file) : "?"; }) ?? "?", 240)).join("\n") : "";
};
const tagsOf = () => [...S.tags.entries()].sort((a, b) => b[1] - a[1]).map(([t]) => t).join(" ");
const secs = (ms: number) => (ms / 1000).toFixed(1) + " s";
type Printed = { head: string; body: string };
const printed = (hs: Extract<Pf, { t: "def" }>[]): Printed[] => hs.map((h) => ({ head: h.head, body: bodyText(h.body) }));
const defsText = (hs: Printed[]) => hs.map((h) => h.head + "\n" + h.body + "\n").join("\n");
const helperBlock = (hs: Printed[], k: string, proven: boolean): string =>
  hs.length ? "# helper defs (" + (proven ? "proven" : "some open") + "): paste them above `def " + shortOf(k) + "(`\n" + defsText(hs) + "# the body of " + shortOf(k) + ":\n" : "";
const editOf = (ds: Src, hs: Printed[], body: string) => ({ file: ds.file, from: ds.header + "\n" + ds.body, to: (hs.length ? defsText(hs) + "\n" : "") + ds.header + "\n" + body });
const PLUS_LINE = /^[ \t]*\+([A-Za-z_]\w*) = \1[ \t]*\n/gm;
const trimPlus = (checks: (body: string) => boolean, body: string): string => {
  const cuts = [...body.matchAll(PLUS_LINE)].map((m) => ({ at: m.index!, n: m[0].length })).sort((a, b) => b.at - a.at);
  if (!cuts.length) return body;
  // all at once first (one check); one by one only while a check is cheap (a heavy body costs its whole
  // reduction per check)
  const t0 = performance.now();
  const none = cuts.reduce((b, c) => b.slice(0, c.at) + b.slice(c.at + c.n), body);
  if (checks(none)) return none;
  if (performance.now() - t0 > 300) return body;
  let cur = body;
  for (const c of cuts.slice(0, 64)) {
    if (late()) break;
    const next = cur.slice(0, c.at) + cur.slice(c.at + c.n);
    if (checks(next)) cur = next;
  }
  return cur;
};
// a proof's helpers and body through Bend's def check once more: what prints is what checks
const finalErr = (k: string, pf: Pf, body: string, cap = FUEL_FINAL): Term => {
  for (const h of helpersOf(pf)) {
    const hk = BK.temps.find((t) => shortOf(t) === h.name);
    const e = hk ? checkErr(hk, bodyText(h.body), h.head, cap) : "the helper " + h.name + " is gone";
    if (e) return e;
  }
  try {
    const r = withFuel(cap, () => checkDef(k, body));
    return r.holes.length ? "the body still has " + r.holes.length + " ?TODO" : null;
  } catch (e) { return e ?? "error"; }
};
const provenText = (k: string, ds: Src, pf: Pf, ms: number): Report => {
  const name = shortOf(k), hs = helpersOf(pf);
  const body0 = bodyText(pf);
  const t0 = performance.now();
  const e = finalErr(k, pf, body0);
  const heavy = performance.now() - t0 > 1000; // a heavy body is not tidied (one check is its whole reduction)
  if (e instanceof Stop) return { status: "partial", text: "# " + name + ": a proof was found, but the re-check did not finish (" + errText(e) + "): unverified\n" + helperBlock(printed(hs), k, true) + body0, body: body0 };
  if (e) return { status: "partial", text: "# " + name + ": a proof was found, but its statement form fails Bend's def check (a bend-synth bug; its λ-form checked):\n" + body0 + "\n" + errText(e), body: body0 };
  const helpers = hs.map((h) => { const hk = BK.temps.find((t) => shortOf(t) === h.name); const b = bodyText(h.body); return { head: h.head, body: hk ? trimPlus((x) => checkErr(hk, x, h.head) === null, b) : b }; });
  const body = heavy ? body0 : trimPlus((x) => checkErr(k, x) === null, body0);
  return { status: "proven", text: "# " + name + ": PROVEN in " + Math.round(ms) + " ms [" + tagsOf() + "]\n" + helperBlock(helpers, k, true) + body, body, edit: editOf(ds, helpers, body), holes: 0 };
};
// each open hole as a lemma over its whole context (true iff the hole is); the hole becomes its call
const stubOf = (g: Goal, used: Set<string>): { head: string; call: string } | null => {
  const names = g.names;
  if (new Set(names).size !== names.length || names.some((x) => !/^[A-Za-z_]\w*$/.test(x))) return null;
  const pad = [...names, "_"];
  const types = names.map((_, i) => attempt(FUEL_NF, () => lower(ann(g, i).T, LD(g))));
  const goalT = attempt(FUEL_NF, () => lower(g.ty, LD(g)));
  if (types.some((x) => x === undefined) || goalT === undefined || hasMeta(goalT)) return null;
  const params = names.map((x, i) => quantText(g, i) + x + ": " + show(types[i], pad, g.own.file));
  const name = helperName(g.own, ".h", used);
  used.add(name);
  return { head: "def " + name + "(\n  " + params.join(",\n  ") + ") ->\n  " + sh(g, goalT) + ":", call: name + "(" + names.join(", ") + ")" };
};
const stubsText = (pf: Pf): string => {
  const used = new Set<string>(), out: string[] = [];
  for (const n of holesOf(pf).slice(0, 6)) {
    const st = attempt(FUEL_NF * 4, () => stubOf(leafOf(n.g), used));
    if (st) out.push(st.head + "\n  ?TODO\n# (then the hole is: " + st.call + ")");
  }
  return out.length ? "\n# each open hole as a lemma to prove by name (its goal over its context):\n" + out.join("\n") : "";
};
const openText = (k: string, ds: Src, root: GNode, head: string, helpers: boolean): Report => {
  const p = partial(root);
  if (p.closed === 0) {
    const leaf = root.alts?.find((a) => a.tag === "intro")?.kids[0] ?? root;
    return { status: "open", text: head + "; no step closed\n" + goalLines(leaf.g) + triedLines(leaf, 8) + templatesOf(k), holes: 1 };
  }
  const body = bodyText(p.pf);
  const e = finalErr(k, p.pf, body, FUEL_PARTIAL);
  const note = e instanceof Stop ? "; not checked (" + errText(e) + ")" : e && !/still has/.test(String(e)) ? "; it does NOT check: " + firstLine(e) : "";
  return {
    status: "partial", body, holes: p.holes,
    text: head + ": a partial (" + p.holes + " holes, " + p.closed + " steps closed). A structure, not a proof" + note + "\n" + helperBlock(printed(helpersOf(p.pf)), k, false) + body
      + "\n" + holesOf(p.pf).slice(0, 8).map((h, i) => "# hole " + (i + 1) + " at " + (h.g.path || "/") + " (in " + h.g.own.short + ")\n" + goalLines(h.g) + triedLines(h)).join("\n")
      + (helpers ? stubsText(p.pf) : "") + templatesOf(k),
    edit: e ? undefined : editOf(ds, printed(helpersOf(p.pf)), body),
  };
};
const templatesOf = (k: string): string => {
  const mine = refsOf(BK.raw[k].T);
  if (mine.size === 0) return "";
  const scored = ownDefs().filter((d) => d !== k && BK.raw[d].v !== null && !BK.hidden.has(d) && !BK.temps.includes(d)).map((d) => {
    const rs = refsOf(BK.raw[d].T);
    const both = [...rs].filter((r) => mine.has(r)).length;
    return { d, score: both / (rs.size + mine.size - both || 1) };
  }).filter((x) => x.score >= 0.25).sort((a, b) => b.score - a.score).slice(0, 3);
  if (scored.length === 0) return "";
  return "\n# similar proven defs (templates):\n" + scored.map(({ d }) => {
    const lines = (defSrc(d)?.body ?? "").split("\n").filter((l) => l.trim() !== "");
    return "#   " + shortOf(d) + ":\n" + lines.slice(0, 6).map((l) => "#   " + clip(l, 200)).join("\n") + (lines.length > 6 ? "\n#     ... (" + lines.length + " lines)" : "");
  }).join("\n");
};

// ---- sessions: a job's live search, kept across slices (a resume continues the same tree) ----
export type Task = {
  id: string; kind: "prove" | "goals" | "bench"; file: string; target: string; spec?: { examples: { call: string; expect: string }[] };
  helpers?: boolean; sliceMs: number; cache?: [string, string][]; submissions?: string[]; budgetMs?: number; regex?: string; verbose?: boolean; proofsOnly?: boolean;
};
export type FromWorker =
  | { t: "progress"; id: string; report: Report }
  | { t: "slice"; id: string; report: Report; done: boolean; spentMs: number; deps?: Record<string, string> }
  | { t: "lemma"; id: string; file: string; key: string; text: string }
  | { t: "row"; id: string; line: string }
  | { t: "ready"; pid: number } | { t: "fatal"; message: string };
type Session = {
  id: string; entry: string; stamp: string; k: string; own: Owner; ds: Src; kind: "proof" | "synth"; hide: boolean;
  search?: Search; gen?: Generator<"time" | "tick", Report>; synth?: SynthState; sketches: Shape[];
  subs: number; started: number; spent: number; last?: Report; final?: Report; t0: number;
};
const sessions = new Map<string, Session>();
// the session's own book is cleaned, and BK stays the book of the job that runs (an evicted session is
// often another file's)
const dropSession = (id: string) => {
  const s = sessions.get(id);
  if (!s) return;
  sessions.delete(id);
  const L = books.get(s.entry);
  if (!L) return;
  const cur = BK;
  BK = L;
  try { dropTemps(); BK.hidden.delete(s.k); } finally { BK = cur; }
};
let send: (m: FromWorker) => void = () => {};
const withHidden = <T>(s: Session, f: () => T): T => {
  // the target's own body never helps prove it: hidden while its search runs
  const def = BK.raw[s.k];
  if (!s.hide || def.v === null) return f();
  BK.raw[s.k] = { ...def, v: null };
  BK.hidden.set(s.k, def);
  resetNf(s.k);
  // a candidate installed meanwhile is dropped with the hiding: the def gets its own body back
  try { return f(); } finally { installed.delete(s.k); BK.raw[s.k] = def; BK.hidden.delete(s.k); resetNf(s.k); }
};
const holesRoot = (s: Session, body: string, label: string, root: GNode): Alt | string => {
  const r = attempt(FUEL_FINAL, () => checkDef(s.k, body));
  if (!r) return "the body does not check (a ?TODO checks at any goal; the error is elsewhere):\n" + errText(lastErr);
  const ats = r.holes.map((h) => h.at);
  const a = mkAlt(root, label, null, 0, (ps) => ({ t: "body", text: body, ats, subs: ps }), label);
  a.probe = null;
  a.whole = (pf) => { const b = fillBody(pf as Extract<Pf, { t: "body" }>); const c = attempt(FUEL_FINAL, () => checkDef(s.k, b)); return !!c && c.holes.length === 0; };
  for (const [i, h] of r.holes.slice(0, 16).entries()) {
    const k = mkNode(goalOf(h.raw, s.own, [], false, label + (i + 1)), a, 0, 0);
    if (k) a.kids.push(k);
  }
  return a;
};
const newSession = (t: Task, L: Book): Session | Report => {
  const r = resolveDef(t.target);
  if (typeof r !== "string") return { status: "error", text: "# " + t.target + ": " + (r.length ? "ambiguous: " + r.join(", ") : "no def of that name in " + path.basename(L.entry)) };
  const k = r, ds = defSrc(k);
  if (!ds) return { status: "error", text: "# " + t.target + ": no source text for it" };
  const se = nsOf(k) === "" ? stmtErr(k) : null;
  if (se) return { status: "error", text: "# " + shortOf(k) + ": its statement does not check; fix it first:\n" + errText(se) };
  const whole = ds.body.trim() === "?TODO", holes = todoAt(ds.body).length > 0;
  const bench = t.kind === "bench";
  if (!whole && !holes && !bench) return { status: "nothing", text: "# " + shortOf(k) + ": no ?TODO in its body (nothing to search; `bend " + path.basename(L.entry) + " --check-only` checks it)" };
  const own = owner(k);
  if (returnsSort(k)) return { status: "nothing", text: "# " + shortOf(k) + ": its result is a sort (a type definition): there is no program to search for it" };
  const kind = isLemmaType(k) ? "proof" : "synth";
  const s: Session = { id: t.id, entry: L.entry, stamp: L.stamp, k, own, ds: bench ? { ...ds, body: "  ?TODO" } : ds, kind, hide: bench, sketches: [], subs: 0, started: Date.now(), spent: 0, t0: performance.now() };
  return s;
};
const startSearch = (s: Session, t: Task): Report | null => {
  const cache = new Map<number, string>((t.cache ?? []).map(([k, v]) => [Number(k), v]));
  const learned = (key: number, text: string) => { if (!/\.(g|h)\d+\(/.test(text)) send({ t: "lemma", id: s.id, file: s.entry, key: String(key), text }); };
  if (s.kind === "proof") {
    if (s.ds.body.trim() === "?TODO") {
      const rg = rootGoal(s.own);
      if (!rg) return { status: "error", text: "# " + s.own.short + ": Bend gives no goal for its body (a template? write the ?TODO inside its body)" };
      const root = mkNode(rg, null, 0, 0)!;
      s.search = newSearch(root, cache, learned);
    } else {
      const rg = rootGoal(s.own);
      const root: GNode = { g: rg ?? ({ own: s.own, names: [], pend: 0, pnames: [], path: "" } as unknown as Goal), key: -1, up: null, alts: [], pn: 1, dn: 1, pf: null, lv: 0, rws: 0 };
      s.search = newSearch(root, cache, learned);
      const a = holesRoot(s, s.ds.body, "hole", root);
      if (typeof a === "string") return { status: "error", text: "# " + s.own.short + ": " + a };
      root.alts!.push(a);
      calcAlt(a); calcNode(root);
    }
    return null;
  }
  // synthesis: the laws that name it, the examples, each instance once
  const laws = lawsOf(s.k);
  lawTerms.clear();
  for (const l of laws) { const L = attempt(FUEL_NF, () => lower0(BK.raw[l].T, 0)); if (L) lawTerms.set(l, L); }
  const ex = parseExamples(s.k, t.spec);
  if (typeof ex === "string") return { status: "error", text: "# " + ex };
  examples = ex;
  const insts: Inst[] = [...ex.map((_, i) => ({ ex: i })), ...laws.filter((l) => lawTerms.has(l)).flatMap(instancesOf)];
  if (insts.length === 0) {
    const rg = rootGoal(s.own);
    return { status: "open", text: "# " + s.own.short + ": its type is data, so any value of it checks: nothing says which body is wanted. Add a law that names it, or --spec examples ({\"examples\": [{\"call\": \"f(2n)\", \"expect\": \"4n\"}]}).\n" + (rg ? goalLines(rg) : "") };
  }
  s.synth = { tried: 0, pruned: 0, shape: "", arms: [] };
  s.gen = synthesize(s.k, s.own, s.ds, insts, laws, s.synth, () => s.sketches);
  if (s.ds.body.trim() !== "?TODO") {
    // a body with holes: the holes are the arms (one shape, the body itself)
    const r = attempt(FUEL_FINAL, () => checkDef(s.k, s.ds.body));
    if (r && r.holes.length) {
      const ats = r.holes.map((h) => h.at), body = s.ds.body;
      s.sketches.push({ label: "the body's holes", arms: r.holes.map((h, i) => goalOf(h.raw, s.own, [], true, "hole" + (i + 1))), pf: (ls) => ({ t: "body", text: body, ats, subs: ls.map((l) => tm(l)) }) });
    }
  }
  return null;
};
const addSubmissions = (s: Session, t: Task): string[] => {
  const notes: string[] = [];
  for (const raw of (t.submissions ?? []).slice(s.subs)) {
    s.subs++;
    // a whole file: its body of the target; else the text is the body itself
    let body = raw;
    if (/^\s*(import|def|type|law)\b/m.test(raw) && DEF_LINE.test(raw.split("\n").find((l) => DEF_LINE.test(l)) ?? "")) {
      const lines = raw.split("\n"), li = defLine(lines, s.own.short);
      if (li < 0) { notes.push("# submission " + s.subs + ": no def " + s.own.short + " in it"); continue; }
      let he = li;
      for (let depth = 0; he < lines.length; he++) { depth += brackets(lines[he]); if (depth <= 0 && /:\s*$/.test(lines[he].replace(/#.*$/, ""))) break; }
      let be = he + 1;
      while (be < lines.length && (lines[be].startsWith(" ") || lines[be].trim() === "")) be++;
      body = lines.slice(he + 1, be).join("\n").replace(/\s+$/, "");
    }
    if (s.kind === "proof" && s.search) {
      const root = s.search.root;
      if (!root.alts) { try { expand(root); } catch (e) { if (e !== TIMEOUT) throw e; root.alts ??= []; } }
      const a = holesRoot(s, body, "sketch" + s.subs + ".", root);
      if (typeof a === "string") { notes.push("# submission " + s.subs + ": " + a); continue; }
      a.w = -1; // an agent's sketch goes first
      root.alts!.unshift(a);
      if (a.kids.length === 0) close(a);
      calcAlt(a); update(root);
      notes.push("# submission " + s.subs + ": " + a.kids.length + " holes added to the search");
    } else if (s.kind === "synth") {
      const r = attempt(FUEL_FINAL, () => checkDef(s.k, body));
      if (!r) { notes.push("# submission " + s.subs + ": it does not check: " + firstLine(lastErr)); continue; }
      const ats = r.holes.map((h) => h.at);
      s.sketches.push({ label: "submission " + s.subs, arms: r.holes.map((h, i) => goalOf(h.raw, s.own, [], true, "sketch" + (i + 1))), pf: (ls) => ({ t: "body", text: body, ats, subs: ls.map((l) => tm(l)) }) });
      notes.push("# submission " + s.subs + ": " + r.holes.length + " holes queued as a shape");
    }
  }
  return notes;
};
const reportOf = (s: Session, t: Task, final: boolean): Report => {
  const ms = performance.now() - s.t0;
  if (s.kind === "proof" && s.search) {
    S = s.search;
    const root = S.root;
    if (root.pf) return provenText(s.k, s.ds, root.pf, ms);
    const why = root.pn >= INF ? "every step failed" : S.nodes >= MAX_NODES ? "node cap" : overMem ? "memory share" : "time";
    const head = "# " + s.own.short + ": " + (final ? "OPEN" : "searching") + " after " + secs(ms) + " (" + S.nodes + " goals; stopped by " + why + (S.internal ? ", " + S.internal + " internal errors" : "") + ")";
    const r = openText(s.k, s.ds, root, head, !!t.helpers);
    r.nodes = S.nodes;
    return r;
  }
  if (s.synth) {
    const st = s.synth;
    return { status: "running", text: "# " + s.own.short + ": synthesizing (" + secs(ms) + ", shape: " + (st.shape || "-") + ", " + st.tried + " bodies tried, " + st.pruned + " leaves refuted early)\n"
      + st.arms.map((a, i) => "# arm " + (i + 1) + " (" + (a.goal.path || "/") + "): " + a.leaves.length + " leaves" + (a.leaves.length ? ": " + a.leaves.slice(0, 4).join(" | ") : "")).join("\n") };
  }
  return { status: "running", text: "# starting" };
};
type Done = (report: Report, fin: boolean, s?: Session) => void;
// one slice of a job: load (warm when unchanged), continue its session, report. The search stops itself
// at the slice's end and at the memory share; outside it (loading, starting, reporting) the memory share
// stops the slice, which ends open and not done: the worker sheds its caches, and the job goes on
const runSlice = async (t: Task): Promise<void> => {
  const t0 = performance.now();
  jobDeadline = t0 + Math.max(t.sliceMs, t.budgetMs ?? 0);
  let deps: Record<string, string> | undefined;
  const done: Done = (report, fin, s) => {
    send({ t: "slice", id: t.id, report: { ...report, ms: Math.round(performance.now() - (s?.t0 ?? t0)) }, done: fin, spentMs: Math.round(performance.now() - t0), deps });
    if (fin) dropSession(t.id);
  };
  try { await slice(t, t0 + Math.max(200, t.sliceMs), done, (L) => { deps = L.hashes; }); } catch (e) {
    if (e !== TIMEOUT) throw e;
    deadline = Infinity;
    const why = overMem ? "the worker's memory share (" + Math.round(memCap / 1048576) + " MiB; BEND_SYNTH_MEM_MB raises it)" : "time";
    done({ status: "open", text: HONEST + "\n# " + t.target + ": OPEN: this slice was stopped by " + why + " after " + secs(performance.now() - t0)
      + ", outside the search (loading the book, starting the search, or reporting). The worker drops its books and sessions; the job starts again in its next slice" }, false);
  }
};
const slice = async (t: Task, until: number, done: Done, loaded: (L: Book) => void): Promise<void> => {
  const L = await loadBook(t.file);
  if (typeof L === "string") return done({ status: "error", text: HONEST + "\n# " + L }, true);
  loaded(L);
  BK = L;
  let s = sessions.get(t.id);
  if (s && (s.stamp !== L.stamp || s.entry !== L.entry)) { dropSession(t.id); s = undefined; }
  if (!s) {
    const made = newSession(t, L);
    if (!("id" in made)) return done({ ...made, text: HONEST + "\n" + made.text }, true);
    s = made;
    sessions.set(t.id, s);
    if (sessions.size > 4) dropSession(sessions.keys().next().value!);
    const r = withHidden(s, () => startSearch(s!, t));
    if (r) return done({ ...r, text: HONEST + "\n" + r.text }, true, s);
    // hints first: the goals at once, before any search
    send({ t: "progress", id: t.id, report: { status: "running", text: HONEST + "\n" + withHidden(s, () => firstHints(s!)) } });
  }
  const sess = s;
  const notes = withHidden(sess, () => addSubmissions(sess, t));
  if (t.kind === "goals") return done({ status: "open", text: HONEST + "\n" + withHidden(sess, () => goalsText(sess)) }, true, sess);
  if (sess.kind === "proof") {
    S = sess.search!;
    await withHiddenAsync(sess, () => run(until, () => send({ t: "progress", id: t.id, report: reportOf(sess, t, false) })));
    const root = S.root;
    const fin = !!root.pf || root.pn >= INF || S.nodes >= MAX_NODES;
    const rep = withHidden(sess, () => { deadline = Infinity; return reportOf(sess, t, true); });
    return done({ ...rep, text: HONEST + "\n" + (notes.length ? notes.join("\n") + "\n" : "") + rep.text }, fin || rep.status === "proven", sess);
  }
  // synthesis
  deadline = until;
  let result: Report | undefined;
  let yielded = performance.now();
  try {
    for (;;) {
      if (late()) break;
      const r = withHidden(sess, () => sess.gen!.next());
      if (r.done) { result = r.value; break; }
      if (r.value === "time") break;
      if (performance.now() - yielded > 100) { if (memoryGuard()) break; deadline = Infinity; await Bun.sleep(0); deadline = until; yielded = performance.now(); }
    }
  } catch (e) {
    deadline = Infinity;
    uninstall(sess.k);
    return done({ status: "error", text: HONEST + "\n# internal error: " + String((e as Error)?.stack ?? e).slice(0, 800) }, true, sess);
  } finally { deadline = Infinity; }
  if (result) { uninstall(sess.k); return done({ ...result, text: HONEST + "\n" + (notes.length ? notes.join("\n") + "\n" : "") + result.text }, true, sess); }
  const rep = reportOf(sess, t, false);
  return done({ ...rep, text: HONEST + "\n" + (notes.length ? notes.join("\n") + "\n" : "") + rep.text }, false, sess);
};
const withHiddenAsync = async (s: Session, f: () => Promise<void>) => {
  const def = BK.raw[s.k];
  if (!s.hide || def.v === null) return f();
  BK.raw[s.k] = { ...def, v: null };
  BK.hidden.set(s.k, def);
  resetNf(s.k);
  try { await f(); } finally { BK.raw[s.k] = def; BK.hidden.delete(s.k); resetNf(s.k); }
};
const firstHints = (s: Session): string => {
  if (s.kind === "proof" && s.search) {
    const root = s.search.root;
    if (root.key === -1) return root.alts?.[0]?.kids.map((k, i) => "# hole " + (i + 1) + "\n" + goalLines(k.g)).join("\n") ?? "";
    return "# " + s.own.short + ": the goal\n" + goalLines(root.g);
  }
  const rg = rootGoal(s.own);
  return "# " + s.own.short + ": a program to synthesize\n" + (rg ? goalLines(rg) : "");
};
const goalsText = (s: Session): string => {
  const out: string[] = [];
  const nodes = s.kind === "proof" && s.search
    ? (s.search.root.key === -1 ? s.search.root.alts?.[0]?.kids ?? [] : [s.search.root])
    : [];
  if (!nodes.length) return firstHints(s);
  deadline = performance.now() + 3000;
  try {
    for (const [i, n0] of nodes.entries()) {
      S = s.search!;
      let n = n0;
      if (n.g.pend > 0) { const all = introAll(n.g); const k = all && mkNode(all.g, null, 0, 0); if (k) n = k; }
      try { n.alts = leafAlts(n); } catch (e) { if (e !== TIMEOUT) throw e; n.alts ??= []; }
      const nfa = n.A ?? nf(n.g.ty, LD(n.g), true);
      const derived = (S.facts.get(mixH(n.g.ckey, n.g.d)) ?? []).filter((f) => f.i < 0 && !f.pf.startsWith("Equal.sym(")).slice(0, 12);
      out.push("# " + (nodes.length > 1 ? "hole " + (i + 1) : s.own.short) + "\n" + goalLines(n.g)
        + (nfa ? "\n# in normal form: " + clip(sh(n.g, nfa), 2000) : "")
        + (derived.length ? "\n# facts derived from the context:\n" + derived.map((f) => "#   " + clip(f.pf, 200) + " : " + clip(attempt(FUEL_NF, () => sh(n.g, f.T)) ?? "?", 300)).join("\n") : "")
        + (n.pf ? "\n# closes by: " + inline(n.pf) : triedLines(n, 12)));
    }
  } finally { deadline = Infinity; dropTemps(); }
  return out.join("\n");
};
// bench: every proven lemma of a file (or a data def its laws name) searched again with its body hidden
const runBench = async (t: Task): Promise<void> => {
  const L = await loadBook(t.file);
  if (typeof L === "string") { send({ t: "row", id: t.id, line: "ERR " + L.split("\n")[0] }); return send({ t: "slice", id: t.id, report: { status: "error", text: L }, done: true, spentMs: 0 }); }
  BK = L;
  const re = new RegExp(t.regex || ".");
  const defs = ownDefs().filter((k) => re.test(shortOf(k)) && BK.raw[k].v !== null && !BK.raw[k].i && defSrc(k) && BK.order.get(k)! >= BK.n0
    && (BK.files.get(k)?.ns ?? "") === "" && todoAt(defSrc(k)!.body).length === 0);
  const tally = { proof: [0, 0], program: [0, 0] };
  let total = 0;
  for (const k of defs) {
    const isProof = isLemmaType(k);
    if (returnsSort(k) || (!isProof && (t.proofsOnly || lawsOf(k).length === 0))) continue;
    const kind = isProof ? "proof" : "program";
    tally[kind][1]++;
    const id = t.id + ":" + k;
    const t0 = performance.now();
    let last: Report | undefined;
    send = ((orig) => (m: FromWorker) => { if (m.t === "slice" && m.id === id) last = m.report; else if (m.t !== "progress" && m.t !== "lemma") orig(m); })(send);
    try { await runSlice({ id, kind: "bench", file: t.file, target: shortOf(k), sliceMs: t.budgetMs ?? 2000 }); } finally { send = rootSend; }
    dropSession(id);
    if (overMem) { BK.nfs.clear(); nfObj = new WeakMap(); nfHeld = 0; Bun.gc(true); overMem = false; }
    const ms = Math.round(performance.now() - t0);
    total += ms;
    const good = last?.status === "proven" || last?.status === "synthesized";
    if (good) tally[kind][0]++;
    send({ t: "row", id: t.id, line: (good ? "OK " : "-- ") + String(ms).padStart(6) + " ms  " + shortOf(k) + (isProof ? "" : "  [program]") + (good ? "" : "  (" + (last?.status ?? "?") + ")")
      + (t.verbose && last && !good ? "\n" + last.text.split("\n").filter((l) => !l.includes("helper, not the judge")).map((l) => "     " + l).join("\n") : "") });
    await Bun.sleep(0);
  }
  const [po, pn] = tally.proof, [go, gn] = tally.program;
  send({ t: "slice", id: t.id, report: { status: po + go === pn + gn ? "proven" : "partial",
    text: "# bench " + path.basename(L.entry) + ": " + po + " / " + pn + " proofs" + (gn ? ", " + go + " / " + gn + " programs (laws as evidence)" : "") + " found again in " + secs(total) }, done: true, spentMs: total });
};

// ---- the worker process ----
let rootSend: (m: FromWorker) => void = () => {};
// past the memory share: every book, session and memo goes, the current ones too (BK and S held the last
// job's book alive, so the next book loaded over the share again, and every job after it stopped)
const shed = () => {
  books.clear(); sessions.clear(); smemo.clear(); lawTerms.clear(); openNames.clear();
  examples = []; nfObj = new WeakMap(); patMemo = new WeakMap(); nfHeld = 0;
  BK = undefined as unknown as Book; S = undefined as unknown as Search;
  Bun.gc(true);
  overMem = false;
};
export const workerMain = async (bendDir: string) => {
  rootSend = send = (m) => { process.send?.(m); };
  try { await loadBend(bendDir); } catch (e) { send({ t: "fatal", message: String((e as Error)?.message ?? e) }); setTimeout(() => process.exit(1), 50); return; }
  const mb = Number(process.env.BEND_SYNTH_MEM_MB) || 0;
  // the share the search keeps to: well under the OS limit (a JS heap grows in steps, and a step past the
  // job object's limit is a crash, not an error)
  if (mb) memCap = mb * 0.7 * 1048576;
  const queue: Task[] = [];
  let busy = false;
  const pump = async () => {
    if (busy) return;
    busy = true;
    try {
      while (queue.length) {
        const t = queue.shift()!;
        try { if (t.kind === "bench") await runBench(t); else await runSlice(t); }
        catch (e) { send({ t: "slice", id: t.id, report: { status: "error", text: HONEST + "\n# internal error (please report it): " + String((e as Error)?.stack ?? (e instanceof Stop ? e.why : errText(e))).slice(0, 1500) }, done: true, spentMs: 0 }); dropSession(t.id); }
        finally {
          deadline = Infinity; BR.f = Infinity;
          for (const k of [...installed.keys()]) uninstall(k);
          if (overMem) shed();
        }
      }
    } finally { busy = false; }
  };
  process.on("message", (m: { t: "task"; task: Task } | { t: "drop"; id: string }) => {
    if (m.t === "drop") { dropSession(m.id); return; }
    queue.push(m.task);
    void pump();
  });
  process.on("disconnect", () => process.exit(0));
  send({ t: "ready", pid: process.pid });
};
// in-process use (tests, bench without a server): the same tasks, answered through a callback
export const local = async (bendDir: string) => {
  if (!B) await loadBend(bendDir);
  return {
    run: async (t: Task, on: (m: FromWorker) => void): Promise<Report> => {
      let out: Report | undefined;
      rootSend = send = (m) => { on(m); if (m.t === "slice" && m.id === t.id) out = m.report; };
      if (t.kind === "bench") await runBench(t); else await runSlice(t);
      return out!;
    },
    drop: dropSession,
  };
};

if (import.meta.main) {
  const [cmd, dir] = process.argv.slice(2);
  if (cmd === "worker") {
    const { contain } = await import("./synth.ts");
    const mb = Number(process.env.BEND_SYNTH_MEM_MB) || 768;
    try { await contain(mb); } catch (e) { process.send?.({ t: "fatal", message: String((e as Error)?.message ?? e) }); setTimeout(() => process.exit(1), 50); }
    await workerMain(dir);
  } else {
    console.error("engine.ts is bend-synth's worker; run synth.ts");
    process.exit(1);
  }
}
