// gen3.ts: a fast, anytime helper prover for Bend2 proof holes. One self-contained file; a dev tool
// OUTSIDE the trust (bend2 checks every candidate in gen3's own process; `bend <file> --check-only`
// is the judge of what gen3 prints).
//
// FOR AGENTS (gen3 prints the first line of this with every answer):
//   gen3 is a heuristic helper, not the judge. It can be wrong or misleading: a partial proof, a
//   hole's goal, a "tried" note. PROVEN means bend2 accepted the text inside gen3. Use common sense.
//
// RUN (from any folder; the file paths are yours, gen3 reads them from disk at each call):
//   bun tools/gen3/gen3.ts prove <file.bend> <def> [<def> ...] [--wait S] [--budget S] [--write]
//       a def whose body is ?TODO: a whole body (case splits, induction, helper lemmas). A body with
//       ?TODO holes: each hole. Prints the proof, or the best partial with each hole's goal.
//       --write puts a full proof into the file (only if that body did not change meanwhile).
//   bun tools/gen3/gen3.ts goals <file.bend> <def>     each hole's goal, context and candidate steps
//   bun tools/gen3/gen3.ts check <file.bend> [<def> ...]   bend2's def check, errors bounded
//   bun tools/gen3/gen3.ts find <file.bend> <regex>    defs whose name matches, with statements
//   bun tools/gen3/gen3.ts bench <file.bend> [<regex>]  re-prove each proven lemma (for gen3's authors)
//   bun tools/gen3/gen3.ts status | stop
//   Exit: 0 done, 2 something stays open, 3 still running (call again to resume), 1 error.
//
// DESIGN
// * start-or-resume: every call goes to one local server (started on first use; one per version of
//   this file: an edit to gen3.ts starts a fresh server, which stops the old one; a server exits after
//   10 idle minutes). A call starts a job, or attaches to the same job (same command, same file
//   texts) that another agent or an earlier call started. It returns after --wait seconds (default
//   10) with what the job has (a partial at worst); the job runs on to its --budget (default 60) and
//   the next call resumes it. So no call blocks for long, and shared worktrees share work.
// * crash containment, no frozen machine: the bend2 work runs in hidden worker processes at below
//   normal priority (one core left free; GEN3_WORKERS). Half of the RAM is split among them
//   (GEN3_MEM_MB): a worker at its share stops its search and answers; one that stays above restarts.
//   A worker that crashes or runs past its deadline (a check that fuel cannot bound) is killed and
//   replaced; the job reports what it had. The server never loads bend2.
// * one search, anytime: proof-number search over an AND/OR tree (goals OR tactics, a tactic AND its
//   subgoals). Every partial is the current best subtree, every subgoal gets effort in proportion to
//   how close it is to a proof, and no phase repeats another's work.
// * one move for every split: a goal can become a helper def (its context its parameters, optionally
//   with a stuck call generalized to a parameter x and an equation {x == call}), and a helper's
//   parameters can be split. That gives splits inside ?TODO holes, functional and enumeration
//   induction, deciding a stuck Bool call, and generalization.
// * one fact list: hypotheses plus facts derived from them (symmetry, constructor injectivity, a
//   constructor clash), each with its proof text. A clash or an injectivity is a rewrite whose motive
//   is an inline match eliminator {\{C: ..; \{}} : T -> Type}(_): no predicate or projection def.
// * one normal form, memoized: bounded (fuel shared by all its steps, a node budget), and in a second
//   variant with the calls that decide a branch kept folded (a def whose result is an enumeration,
//   on small arguments): bend2's weak normal form unfolds such a wrapper (FileEp.is_resource) inside
//   a stuck match, so each wrapper's unfolded body is folded back. Goals are keyed by their normal
//   form: a rewrite that changes nothing is a cycle.
// * bounded everywhere: fuel per check (a Proxy on the book counts def lookups; limits nest), a
//   deadline, caps on candidates per goal, lowering with a node budget (a term is a graph; its tree
//   can be exponential), term hashes instead of term strings (no quadratic keys).
//
// EXTEND: a tactic is a function that adds alternatives (Alt) to a goal in `leafAlts`; a closer goes
// in `closer`. Check a change with `bench` (parallel over the worker pool); find a slow spot with
// GEN3_PROF=<dir> (each worker writes a markdown CPU profile there after its first task).

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { spawn } from "node:child_process";

const HONEST = "# gen3: a heuristic helper, not the judge; its partials, goals and notes can be wrong or misleading. PROVEN = bend2 accepted it inside gen3; `bend <file> --check-only` decides.";

// ---- shared: the pinned bend2, the server's identity ----
// bend2 is the Bend that bend-lint pins (its package.json: bendWindows on Windows, else bendRelease),
// downloaded into bend-lint's cache by `bun install`; so gen3 checks with the same Bend as `bun run lint`.
const bendFile = (): string => {
  for (let d = import.meta.dir; ; d = path.dirname(d)) {
    const f = path.join(d, "node_modules", "bend-lint", "package.json");
    if (fs.existsSync(f)) {
      const pkg = JSON.parse(fs.readFileSync(f, "utf8"));
      const pin = process.platform === "win32" ? pkg.bendWindows : pkg.bendRelease;
      if (typeof pin !== "string" || !/^[\w.-]+\/[\w.-]+\/[\w.-]+$/.test(pin)) throw new Error("bend-lint's package.json pins no Bend");
      const cache = process.env.XDG_CACHE_HOME
        ?? (process.platform === "win32" ? (process.env.LOCALAPPDATA ?? path.join(os.homedir(), "AppData", "Local")) : path.join(os.homedir(), ".cache"));
      return path.join(cache, "bend-lint", ...pin.split("/"), "bend2", "bend.ts");
    }
    if (path.dirname(d) === d) throw new Error("bend-lint is not installed (run `bun install`)");
  }
};
const ID = BigInt.asUintN(48, BigInt(Bun.hash(fs.readFileSync(import.meta.path, "utf8") + "\0" + bendFile())));
const HOME = path.join(os.tmpdir(), "gen3");
const PORT = Number(process.env.GEN3_PORT) || 20000 + Number(ID % 20000n);
const LOG = path.join(HOME, ID.toString(36) + ".log");

// what a book read: a file's modification time and size (one stamp per list of files)
const stampOf = (files: string[]) => files.map((f) => { try { const s = fs.statSync(f); return s.mtimeMs + ":" + s.size; } catch { return "-"; } }).join(",");

type Args = { cmd: string; pos: string[]; opt: Map<string, string> };
const VALUED = new Set(["wait", "budget"]);
const parseArgs = (argv: string[]): Args => {
  const pos: string[] = [];
  const opt = new Map<string, string>();
  for (let i = 1; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith("--")) pos.push(a);
    else if (VALUED.has(a.slice(2))) opt.set(a.slice(2), argv[++i] ?? "");
    else opt.set(a.slice(2), "");
  }
  return { cmd: argv[0] ?? "help", pos, opt };
};
const num = (a: Args, k: string, d: number, max: number): number => {
  const v = Number(a.opt.get(k) ?? d);
  return Number.isFinite(v) && v > 0 ? Math.min(v, max) : d;
};

// what a call asks the server, and what the server streams back (one JSON object per line)
type Ask = { argv: string[]; cwd: string };
type Ev = { t: "out" | "err"; s: string } | { t: "edit"; file: string; from: string; to: string } | { t: "end"; code: number };
type Edit = Extract<Ev, { t: "edit" }>;

// ---- client ----
const USAGE = "usage: bun tools/gen3/gen3.ts prove <file.bend> <def>... [--wait S] [--budget S] [--write] | goals <file> <def> | check <file> [<def>...] | find <file> <regex> | bench <file> [<regex>] | status | stop";

const post = async (ask: Ask, wait: number): Promise<Response | null> => {
  try {
    return await fetch("http://127.0.0.1:" + PORT + "/run", { method: "POST", body: JSON.stringify(ask), signal: AbortSignal.timeout((wait + 30) * 1000) });
  } catch {
    return null;
  }
};
const hello = async (): Promise<string | null> => {
  try {
    const r = await fetch("http://127.0.0.1:" + PORT + "/hello", { signal: AbortSignal.timeout(1000) });
    return await r.text();
  } catch {
    return null;
  }
};
const startServer = async (): Promise<string | null> => {
  fs.mkdirSync(HOME, { recursive: true });
  const log = fs.openSync(LOG, "a");
  spawn(process.execPath, [import.meta.path, "serve"], { detached: true, stdio: ["ignore", log, log], windowsHide: true }).unref();
  for (let i = 0; i < 100; i++) {
    const h = await hello();
    if (h !== null) return h;
    await Bun.sleep(50);
  }
  return null;
};
const applyEdit = (e: Edit): string => {
  if (!fs.existsSync(e.file)) return "# gen3: --write skipped: " + e.file + " is gone";
  const text = fs.readFileSync(e.file, "utf8");
  const at = text.indexOf(e.from);
  if (at < 0 || text.indexOf(e.from, at + 1) >= 0) return "# gen3: --write skipped: " + e.file + " changed meanwhile (call again)";
  fs.writeFileSync(e.file, text.slice(0, at) + e.to + text.slice(at + e.from.length));
  return "# gen3: wrote " + e.file;
};
const client = async (a: Args): Promise<number> => {
  const ask: Ask = { argv: process.argv.slice(2), cwd: process.cwd() };
  const wait = num(a, "wait", 10, 300);
  let h = await hello();
  if (h === null) {
    if (a.cmd === "stop" || a.cmd === "status") { console.log("# gen3: no server is running"); return 0; }
    h = await startServer();
  }
  if (h !== String(ID)) {
    console.error("# gen3: port " + PORT + " answers, but not as this gen3 (" + (h ?? "no answer") + "); set GEN3_PORT to a free port. Server log: " + LOG);
    return 1;
  }
  const res = await post(ask, wait);
  if (!res?.ok || !res.body) { console.error("# gen3: the server did not answer (log: " + LOG + ")"); return 1; }
  let code = 1, rest = "";
  const take = (line: string) => {
    if (line.trim() === "") return;
    let e: Ev;
    try { e = JSON.parse(line) as Ev; } catch { console.error(line); return; }
    if (e.t === "out") console.log(e.s);
    else if (e.t === "err") console.error(e.s);
    else if (e.t === "edit") console.error(applyEdit(e));
    else code = e.code;
  };
  const dec = new TextDecoder();
  for await (const chunk of res.body) {
    const lines = (rest + dec.decode(chunk, { stream: true })).split("\n");
    rest = lines.pop() ?? "";
    lines.forEach(take);
  }
  take(rest);
  return code;
};

// ---- server ----
// Jobs by key (the command, its folder, a stamp of the files it reads); a worker process runs one job
// at a time; the server keeps each job's latest answer, so a later call (or another agent) resumes it.
type Task =
  | { t: "run"; id: number; args: Args; cwd: string; deadline: number }
  | { t: "lemmas"; id: number; file: string; only: string; budget: number; deadline: number }
  | { t: "reprove"; id: number; file: string; def: string; budget: number; deadline: number };
type Msg =
  | { id: number; t: "snap"; s: string; code: number; edits?: Edit[] }
  | { id: number; t: "files"; files: string[] }
  | { id: number; t: "lemmas"; names: string[] }
  | { id: number; t: "row"; s: string; ok: boolean; ms: number }
  | { id: number; t: "end" };
type Bench = { n: number; left: number; rows: string[]; ok: number; ms: number };
type Job = {
  id: number; key: string; task: Task; t0: number; snap: string; code: number; edits: Edit[]; done: boolean;
  subs: Set<(e: Ev) => void>; ask?: Ask; parent?: Job; bench?: Bench;
};
type Worker = { p: ReturnType<typeof Bun.spawn>; job: Job | null; entries: string[] };
const GB = 2 ** 30;
const POOL = Number(process.env.GEN3_WORKERS) || Math.max(1, Math.min(os.cpus().length - 1, Math.floor(os.totalmem() * 0.5 / (1.5 * GB))));
const MEM_MB = Number(process.env.GEN3_MEM_MB) || Math.floor(os.totalmem() * 0.5 / POOL / 2 ** 20);
const GRACE_MS = 5000;
const IDLE_MS = 10 * 60 * 1000;
const PORT_FILE = (id: string) => path.join(HOME, id + ".port");
const entryOf = (cwd: string, args: Args) => path.resolve(cwd, args.pos[0] ?? "");
const taskEntry = (t: Task) => (t.t === "run" ? entryOf(t.cwd, t.args) : t.file);
const taskMs = (t: Task) => (t.t === "run" ? num(t.args, "budget", 60, 600) * 1000 : t.t === "reprove" ? t.budget + 2000 : 30000);

const serve = async () => {
  const jobs = new Map<string, Job>();
  const byId = new Map<number, Job>();
  const queue: Job[] = [];
  const workers: Worker[] = [];
  const closures = new Map<string, string[]>(); // entry -> the files its book read (from the workers)
  let nextId = 1, lastAsk = Date.now();

  const emit = (j: Job, e: Ev) => { for (const f of j.subs) f(e); };
  const quit = () => {
    for (const w of workers) w.p.kill();
    try { fs.unlinkSync(PORT_FILE(ID.toString(36))); } catch { /* a newer server removed it */ }
    process.exit(0);
  };
  const finish = (j: Job) => {
    if (j.done) return;
    j.done = true;
    emit(j, { t: "end", code: j.code });
    const b = j.parent?.bench;
    if (b && --b.left === 0) benchDone(j.parent!);
  };
  const benchDone = (j: Job) => {
    const b = j.bench!;
    j.snap = HONEST + "\n" + b.rows.sort().join("\n") + "\n# bench: " + b.ok + "/" + b.n + " re-proven, " + (b.ms / 1000).toFixed(1) + " s of search (" + POOL + " workers, " + ((Date.now() - j.t0) / 1000).toFixed(1) + " s wall)";
    j.code = 0;
    finish(j);
  };
  // the key: the command (less --wait), its folder, and a stamp of every file its book read last time
  const keyOf = (ask: Ask, a: Args): string => {
    const argv = ask.argv.filter((x, i, xs) => x !== "--wait" && xs[i - 1] !== "--wait");
    const entry = entryOf(ask.cwd, a);
    return JSON.stringify(argv) + "\0" + ask.cwd + "\0" + stampOf(closures.get(entry) ?? [entry]);
  };
  const onMsg = (w: Worker, m: Msg) => {
    const j = byId.get(m.id);
    if (!j) return;
    switch (m.t) {
      case "snap": j.snap = m.s; j.code = m.code; j.edits = m.edits ?? []; break;
      case "files": {
        const entry = taskEntry(j.task);
        closures.set(entry, m.files);
        w.entries = [entry, ...w.entries.filter((e) => e !== entry)].slice(0, 3); // the worker keeps 3 books
        // the same call, asked again, resumes it: its key now stamps every file it reads
        if (j.ask && jobs.get(j.key) === j) { jobs.delete(j.key); j.key = keyOf(j.ask, parseArgs(j.ask.argv)); jobs.set(j.key, j); }
        break;
      }
      case "lemmas": fanOut(j, m.names); break;
      case "row": {
        const b = j.parent?.bench;
        if (b) { b.rows.push(m.s); if (m.ok) b.ok++; b.ms += m.ms; }
        break;
      }
      case "end": w.job = null; if (!j.bench) finish(j); pump(); break;
    }
  };
  const spawnWorker = (): Worker => {
    const w: Worker = { p: null as unknown as Worker["p"], job: null, entries: [] };
    // GEN3_PROF=<dir>: each worker writes a CPU profile (markdown) there after its first task
    const prof = process.env.GEN3_PROF ? ["--cpu-prof-md", "--cpu-prof-dir=" + process.env.GEN3_PROF] : [];
    w.p = Bun.spawn([process.execPath, ...prof, import.meta.path, "worker"], {
      stdio: ["ignore", "inherit", "inherit"],
      windowsHide: true,
      env: { ...process.env, GEN3_MEM_MB: String(MEM_MB) },
      ipc: (m: Msg) => onMsg(w, m),
      onExit: () => {
        workers.splice(workers.indexOf(w), 1);
        const j = w.job;
        if (j && !j.done && !j.bench) {
          emit(j, { t: "err", s: "# gen3: the worker stopped (a crash, or a check past its deadline); this answer is what the job had" });
          if (j.code === 3) j.code = 1;
          finish(j);
        }
        pump();
      },
    });
    try { os.setPriority(w.p.pid, os.constants.priority.PRIORITY_BELOW_NORMAL); } catch { /* not permitted: normal priority */ }
    workers.push(w);
    return w;
  };
  // a call's job before a bench's lemmas: an agent waits on it
  const pump = () => {
    while (queue.length) {
      const i = Math.max(0, queue.findIndex((j) => !j.parent));
      const entry = taskEntry(queue[i].task);
      let w = workers.find((x) => !x.job && x.entries.includes(entry)) ?? workers.find((x) => !x.job);
      if (!w && workers.length < POOL) w = spawnWorker();
      if (!w) return;
      const j = queue.splice(i, 1)[0];
      w.job = j;
      j.task.deadline = Date.now() + taskMs(j.task);
      w.p.send(j.task);
    }
  };
  // a worker past its task's deadline (plus grace) is stuck in a check that fuel does not bound
  setInterval(() => {
    for (const w of workers) if (w.job && Date.now() > w.job.task.deadline + GRACE_MS) w.p.kill();
    if (Date.now() - lastAsk > IDLE_MS && queue.length === 0 && workers.every((w) => !w.job)) quit();
  }, 500);

  const newJob = (key: string, task: Task, parent?: Job): Job => {
    const j: Job = { id: task.id, key, task, t0: Date.now(), snap: "", code: 3, edits: [], done: false, subs: new Set(), parent };
    jobs.set(key, j);
    byId.set(j.id, j);
    if (jobs.size > 400) for (const [k, x] of jobs) if (x.done) { jobs.delete(k); byId.delete(x.id); if (jobs.size <= 300) break; }
    return j;
  };
  const fanOut = (j: Job, names: string[]) => {
    if (j.task.t !== "lemmas") return;
    const { file, budget } = j.task;
    j.bench = { n: names.length, left: names.length, rows: [], ok: 0, ms: 0 };
    if (names.length === 0) benchDone(j);
    for (const def of names) {
      const id = nextId++;
      queue.push(newJob("bench\0" + id, { t: "reprove", id, file, def, budget, deadline: 0 }, j));
    }
    pump();
  };
  const startJob = (ask: Ask, a: Args): Job => {
    const id = nextId++;
    const j = a.cmd === "bench"
      ? newJob(keyOf(ask, a), { t: "lemmas", id, file: entryOf(ask.cwd, a), only: a.pos[1] ?? "", budget: num(a, "budget", 3, 60) * 1000, deadline: 0 })
      : newJob(keyOf(ask, a), { t: "run", id, args: a, cwd: ask.cwd, deadline: 0 });
    j.ask = ask;
    queue.push(j);
    pump();
    return j;
  };
  const statusText = () => {
    const rows = [...new Set(jobs.values())].filter((j) => !j.parent).slice(-20)
      .map((j) => (j.done ? "done " : "run  ") + Math.round((Date.now() - j.t0) / 1000) + " s  " + (j.task.t === "run" ? j.task.args.cmd + " " + j.task.args.pos.join(" ") : "bench " + j.task.file));
    return "# gen3 server " + ID.toString(36) + " on port " + PORT + ": " + workers.length + "/" + POOL + " workers (" + MEM_MB + " MB each, below normal priority), " + queue.length + " queued; log " + LOG + "\n" + rows.join("\n");
  };
  // a job's stream: its progress as it comes, then (when it ends, or after wait ms) its answer
  const stream = (head: Ev[], j: Job | null, wait: number, write: boolean): Response => {
    const enc = new TextEncoder();
    return new Response(new ReadableStream({
      start(c) {
        const send = (e: Ev) => { try { c.enqueue(enc.encode(JSON.stringify(e) + "\n")); } catch { /* the client left */ } };
        head.forEach(send);
        if (!j) { c.close(); return; }
        let timer: ReturnType<typeof setTimeout> | undefined;
        const end = (code: number) => {
          j.subs.delete(sub);
          clearTimeout(timer);
          send({ t: "out", s: j.snap || HONEST + "\n# gen3: nothing to show yet" });
          if (code === 3) send({ t: "err", s: "# gen3: still running (" + Math.round((Date.now() - j.t0) / 1000) + " s so far, up to its --budget); run the same command again to resume" });
          else if (write) j.edits.forEach(send);
          send({ t: "end", code });
          try { c.close(); } catch { /* the client left */ }
        };
        const sub = (e: Ev) => (e.t === "end" ? end(e.code) : send(e));
        if (j.done) { end(j.code); return; }
        j.subs.add(sub);
        timer = setTimeout(() => end(3), wait);
      },
    }), { headers: { "content-type": "application/x-ndjson" } });
  };
  const answer = (ask: Ask): Response => {
    lastAsk = Date.now();
    const a = parseArgs(ask.argv);
    if (a.cmd === "stop") { setTimeout(quit, 100); return stream([{ t: "out", s: "# gen3: server stopped" }, { t: "end", code: 0 }], null, 0, false); }
    if (a.cmd === "status") return stream([{ t: "out", s: statusText() }, { t: "end", code: 0 }], null, 0, false);
    if (!["prove", "goals", "check", "find", "bench"].includes(a.cmd) || a.pos.length === 0) return stream([{ t: "err", s: USAGE }, { t: "end", code: 1 }], null, 0, false);
    const had = jobs.get(keyOf(ask, a));
    const head: Ev[] = had ? [{ t: "err", s: "# gen3: resumed a job started " + Math.round((Date.now() - had.t0) / 1000) + " s ago" + (had.done ? " (finished)" : "") }] : [];
    return stream(head, had ?? startJob(ask, a), num(a, "wait", 10, 300) * 1000, a.opt.has("write"));
  };

  try {
    Bun.serve({
      port: PORT, hostname: "127.0.0.1", idleTimeout: 0,
      async fetch(req) {
        const u = new URL(req.url);
        if (u.pathname === "/hello") return new Response(String(ID));
        if (u.pathname !== "/run" || req.method !== "POST") return new Response("gen3", { status: 404 });
        try { return answer((await req.json()) as Ask); } catch (e) { return stream([{ t: "err", s: "# gen3: bad request: " + String(e) }, { t: "end", code: 1 }], null, 0, false); }
      },
    });
  } catch (e) {
    // another server of this version won the port: it serves
    console.error("[gen3] not serving: " + String(e));
    process.exit(0);
  }
  // one server at a time: ask the servers of older versions of this file to stop (a port that answers
  // as that version), and drop their files
  fs.mkdirSync(HOME, { recursive: true });
  for (const f of fs.readdirSync(HOME).filter((x) => x.endsWith(".port") && x !== ID.toString(36) + ".port")) {
    const id = f.slice(0, -5);
    const port = Number(fs.readFileSync(path.join(HOME, f), "utf8"));
    const h = await fetch("http://127.0.0.1:" + port + "/hello", { signal: AbortSignal.timeout(1000) }).then((r) => r.text()).catch(() => null);
    if (h !== null && BigInt(h).toString(36) === id) await fetch("http://127.0.0.1:" + port + "/run", { method: "POST", body: JSON.stringify({ argv: ["stop"], cwd: "" }) }).catch(() => null);
    for (const x of [f, id + ".log"]) try { fs.unlinkSync(path.join(HOME, x)); } catch { /* gone, or still open */ }
  }
  fs.writeFileSync(PORT_FILE(ID.toString(36)), String(PORT));
  console.error("[gen3] " + new Date().toISOString() + " serving " + ID.toString(36) + " on 127.0.0.1:" + PORT + " with up to " + POOL + " workers");
};

// ---- worker: bend2, loaded books ----
// bend2 (bend.ts) is imported at run time from bend-lint's cache, so its types are not visible here: a
// Term is one of its terms (higher-order, with closures in binders, or lowered: de Bruijn levels).
type Term = any;
let B: Term;

class Stop { constructor(readonly why: string) {} }
const FRESH = 1e7; // a level no context reaches: opens a binder whose variable does not matter
const OOF = new Stop("fuel"), TIMEOUT = new Stop("time"), LIN = new Stop("linearity");
const FUEL_CHECK = 300000, FUEL_NF = 100000, FUEL_FINAL = 50000000, NF_NODES = 3000, META = 1 << 20;
let fuel = Infinity, deadline = Infinity, ticks = 0;
// f under at most n def lookups, taken from the fuel left (limits nest: an inner call never gets more
// than its caller has); the lookups it used are charged to the caller
const withFuel = <T>(n: number, f: () => T): T => {
  const old = fuel, start = Math.min(n, old);
  fuel = start;
  try { return f(); } finally { fuel = old - Math.max(0, start - fuel); }
};
// f with its own n lookups, whatever the caller has left: a memo computed once per book (a "no" there
// must not mean "the caller was out of fuel")
const withOwnFuel = <T>(n: number, f: () => T): T => {
  const old = fuel;
  fuel = n;
  try { return f(); } finally { fuel = old; }
};
// withFuel, undefined when it runs out, hits a stack overflow or bend2 refuses; past the deadline it
// throws TIMEOUT (the search stops)
const attempt = <T>(n: number, f: () => T): T | undefined => {
  try { return withFuel(n, f); } catch (e) { if (e === TIMEOUT) throw e; return undefined; }
};
// past the deadline, or the worker over its memory share (a search stops either way)
const MEM_CAP = (Number(process.env.GEN3_MEM_MB) || 4096) * 2 ** 20;
let overMem = false;
const late = () => performance.now() > deadline || (deadline < Infinity && (overMem ||= process.memoryUsage.rss() > MEM_CAP));

type Src = { file: string; header: string; body: string; bodyLine: number };
type Lemma = { k: string; order: number; n: number; np: number }; // n binders in all, np of them parameters
type Loaded = {
  entry: string; top: string; book: Term; raw: Record<string, Term>; n0: number; order: Map<string, number>;
  files: Map<string, Term>; src: Map<string, Src | null>; texts: Map<string, string>; open: Map<string, Set<string>>;
  apply: Map<string, Lemma[]>; rw: Map<string, { L: Lemma; side: 0 | 1 }[]>; seen: string[]; stamp: string;
  zero: Map<Term, RegExp | null>; wraps: Map<string, Wrap[]> | null; nfs: Map<number, Term>; enums: Map<string, boolean>; strict: Map<string, number | null>; matched: Map<string, Set<number>>;
};
let BK: Loaded;
const books = new Map<string, Loaded>();

const lineOf = (str: string, at: number) => str.slice(0, at).split("\n").length;
// a load error, bounded (Bun's own print of a bend2 Err dumps the whole book)
const loadError = (e: Term): string => {
  const f = e?.spn?.file;
  const ln = e?.spn && f?.str ? lineOf(f.str, e.spn.beg) : 0;
  return "bend2 rejects the file: " + (typeof e?.exp === "string" ? e.exp : "an error") + (typeof e?.obs === "string" ? " (found " + e.obs + ")" : "")
    + (ln ? "\n  at line " + ln + (f.ns ? " of " + f.ns : "") + ": " + f.str.split("\n")[ln - 1].trim().slice(0, 300) : "")
    + (e?.$ === "Err" ? "" : "\n" + String(e?.stack ?? e).slice(0, 600));
};
const load = async (file: string): Promise<Loaded | string> => {
  if (!fs.existsSync(file) || !fs.statSync(file).isFile()) return "no such file: " + file;
  const entry = fs.realpathSync(file);
  const had = books.get(entry);
  if (had && stampOf(had.seen) === had.stamp) { books.delete(entry); books.set(entry, had); return had; }
  const book = B.book_nil(), seen = new Map<string, string | null>(), top = path.dirname(entry) + "/";
  let n0: number;
  try {
    n0 = await B.book_load(book, entry, "", seen, undefined, top);
  } catch (e) {
    return loadError(e);
  }
  const raw: Record<string, Term> = book.tlds;
  book.tlds = new Proxy(raw, {
    get(t, k, r) {
      if (--fuel < 0) throw OOF;
      if ((++ticks & 4095) === 0 && late()) throw TIMEOUT;
      return Reflect.get(t, k, r);
    },
  });
  const order = new Map<string, number>();
  book.order.forEach((k: string, i: number) => order.set(k, i));
  const files = new Map<string, Term>();
  for (const k of book.order) {
    const t = raw[k];
    const f = t?.$ === "Def" ? spanFile(t.v) ?? spanFile(t.T) : undefined;
    if (f) files.set(k, f);
  }
  const L: Loaded = {
    entry, top, book, raw, n0, order, files, src: new Map(), texts: new Map(), open: new Map(), apply: new Map(), rw: new Map(),
    seen: [...seen.keys()], stamp: "", zero: new Map(), wraps: null, nfs: new Map(), enums: new Map(), strict: new Map(), matched: new Map(),
  };
  L.stamp = stampOf(L.seen);
  for (const f of files.values()) L.texts.set(f.ns === "" ? entry : path.resolve(top, f.ns + ".bend"), f.str);
  BK = L;
  buildIndex();
  books.set(entry, L);
  if (books.size > 3) books.delete(books.keys().next().value!);
  return L;
};
const spanFile = (t: Term, n = 0): Term => {
  if (!t || n > 50) return undefined;
  if (t.s?.file) return t.s.file;
  if (t.$ === "All") return spanFile(t.A, n + 1) ?? spanFile(t.B(B.Var("_", 0)), n + 1);
  return undefined;
};

// ---- source text of defs ----
const DEF_LINE = /^(?:@unsafe\s+)?def\s+([A-Za-z0-9_.]+)\??\(/;
const nsOf = (k: string) => (k.includes(":") ? k.slice(0, k.indexOf(":")) : "");
const shortOf = (k: string) => (k.includes(":") ? k.slice(k.indexOf(":") + 1) : k);
// a file's text as the book parsed it (the disk may have changed since), else as the disk has it
const fileText = (f: string): string => {
  let t = BK.texts.get(f);
  if (t === undefined) { t = fs.existsSync(f) ? fs.readFileSync(f, "utf8") : ""; BK.texts.set(f, t); }
  return t;
};
// bend2's parser state at text str in the file of def k (its namespace and aliases), with names bound
const parserAt = (str: string, pos: number, file: Term, names: string[] = [], dir = "") =>
  ({ book: BK.book, dir, str, pos, stk: names.map((k, i) => [k, i]), frs: names.length, ns: file.ns, al: file.al });
// f parses: the book's hole counter comes back whatever happens (a failed parse must not keep holes)
const withHols = <T>(f: () => T): T => {
  const hols = BK.book.hols;
  try { return f(); } finally { BK.book.hols = hols; }
};
const brackets = (l: string) => { let b = 0; for (const ch of l.replace(/#.*$/, "")) { if ("([{".includes(ch)) b++; else if (")]}".includes(ch)) b--; } return b; };
// the line of def `name` in a file: its exact name first, then a name less its first segment
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
  const file = (BK.order.get(k) ?? -1) >= BK.n0 || nsOf(k) === "" ? BK.entry : path.resolve(BK.top, nsOf(k) + ".bend");
  const lines = fileText(file).split("\n");
  const li = defLine(lines, shortOf(k));
  let res: Src | null = null;
  if (li >= 0) {
    let he = li;
    for (let depth = 0; he < lines.length; he++) {
      depth += brackets(lines[he]);
      if (depth <= 0 && /:\s*$/.test(lines[he].replace(/#.*$/, ""))) break;
    }
    // the body: indented or blank lines, and any line inside an open bracket
    let be = he + 1;
    for (let bd = 0; be < lines.length && (lines[be].startsWith(" ") || lines[be].trim() === "" || bd > 0); be++) bd += brackets(lines[be]);
    while (be > he + 1 && (lines[be - 1].trim() === "" || lines[be - 1].trim().startsWith("#"))) be--;
    res = { file, header: lines.slice(li, he + 1).join("\n"), body: lines.slice(he + 1, be).join("\n"), bodyLine: he + 1 };
  }
  BK.src.set(k, res);
  return res;
};
// a def with a ?TODO in its source body is open: not a lemma
const isOpen = (k: string): boolean => {
  const source: string | undefined = BK.files.get(k)?.str;
  if (!source) return false;
  let names = BK.open.get(source);
  if (!names) {
    names = new Set();
    let current = "";
    for (const line of source.split("\n")) {
      const def = DEF_LINE.exec(line);
      if (def) current = def[1];
      else if (current && line.includes("?TODO") && !line.trimStart().startsWith("#")) { names.add(current); names.add(current.slice(current.indexOf(".") + 1)); }
    }
    BK.open.set(source, names);
  }
  return names.has(shortOf(k));
};
const ownDefs = (): string[] => [...new Set<string>(BK.book.order.slice(BK.n0))].filter((k) => BK.raw[k]?.$ === "Def" && !k.includes("~") && !BK.raw[k].b);
// a def name as an agent writes it (Spec.add_keeps, add_keeps, Keeps.at): exact, else a suffix
const resolveDef = (nm: string): string | string[] => {
  const own = ownDefs();
  const exact = own.filter((x) => shortOf(x) === nm || x === nm);
  const local = nm.includes(".") ? nm.slice(nm.indexOf(".") + 1) : nm;
  const m = exact.length ? exact : own.filter((x) => shortOf(x) === local || shortOf(x).endsWith("." + nm));
  return m.length === 1 ? m[0] : m.map(shortOf);
};

// ---- checking ----
// k with body text (a def body, indented two spaces): throws bend2's Err on failure
const checkDef = (k: string, body: string, header?: string) => {
  const def = BK.raw[k];
  const file = BK.files.get(k);
  const ds = defSrc(k);
  const head = header ?? ds!.header;
  const str = head + "\n" + body + "\n";
  const p = parserAt(str, str.indexOf("(") + 1, file, [], path.dirname(ds?.file ?? BK.entry) + "/");
  const v = withHols(() => {
    const tele = B.parse_tele(p, ")");
    p.pos = head.length;
    const vars = tele.map((c: Term) => ({ $: "PVar", k: c[1], i: c[2], q: B.Lone(), s: c[4] }));
    const body = B.term_higher(B.term_lower(B.term_higher(B.body_flatten(B.parse_body(p), vars, () => p.frs++))));
    B.parse_skip(p);
    if (p.pos < str.length) B.parse_fail(p, "the end of the body");
    return body;
  });
  B.def_check(BK.book, k, { ...def, v });
};
// k's def check with body: null, or bend2's error (a Stop: not decided, out of fuel or time)
const checkErr = (k: string, body: string, header?: string, cap = FUEL_FINAL): Term => {
  try { withFuel(cap, () => checkDef(k, body, header)); return null; } catch (e) { return e ?? "error"; }
};
// the error of k's statement, or null
const stmtErr = (k: string): Term => {
  const t = BK.raw[k];
  if (t?.$ !== "Def") return null;
  try {
    withFuel(FUEL_FINAL, () => B.term_check(BK.book, { t: B.Ref(k), n: 0, def: k, qs: [], u: t.u }, t.T, B.None(), B.Typ(B.Qua(B.Lone())), B.ctx_nil(), 0));
    return null;
  } catch (e) {
    return e === OOF ? null : e;
  }
};

// ---- terms ----
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
// bend2's term_lower with a node budget: a term is a graph (wnf shares every argument), and its tree
// can be exponentially larger; past the budget the lowering stops (BIG), so no lowering hangs. cut (to
// print an error): the rest is "…" instead, and so are the forms an error need not show
const LOWER_NODES = 20000;
const BIG = new Stop("size");
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
const lower0 = (h: Term, d: number): Term => lowerB(h, d, { n: LOWER_NODES });
const lower = (h: Term, d: number): Term => canon(lower0(h, d));

// a structural hash of a lowered term (52 bits; memoized per node): goal keys, dedupe and replace
// compare hashes, never term strings (a string key per subterm is quadratic in the term's size)
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
    if (s.length <= 64) smemo.set(s, r); // names, not term keys of any size
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

// the children of a lowered term (iterative walks: a deep term cannot overflow the stack)
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
// does some node of t pass test (stopping at the first)?
const some = (t0: Term, test: (t: Term) => boolean): boolean => {
  const st: Term[] = [t0];
  while (st.length) { const t = st.pop(); if (test(t)) return true; st.push(...kidsT(t)); }
  return false;
};
// node count, stopping past cap
const size = (t0: Term, cap = 100000): number => {
  let n = 0;
  some(t0, () => ++n > cap);
  return n;
};
// the variables (levels) of t, metavariables excluded
const varsOf = (t0: Term, out: Set<number>) => {
  some(t0, (t) => { if (t.$ === "Var" && t.i < META) out.add(t.i); return false; });
  return out;
};
const hasMeta = (t0: Term): boolean => some(t0, (t) => t.$ === "Var" && t.i >= META);
const contains = (t0: Term, h: number): boolean => some(t0, (t) => H(t) === h);
// every variable of t is below d or bound inside t
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
// the rewrite walks (replace, occurrences, subterms) enter terms, equation sides and lambda bodies,
// not an equation's type nor a binder's domain: a motive replaces only where a value is
// t with the occurrences of hash h replaced by `by`: every one (at < 0), or the at-th (left to right)
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
// the subterms of t a rewrite may target: not the head of a call; inside a lambda, only those that do
// not name its variable (d: the depth of t's context)
const subterms = (t: Term, out: Map<number, Term>, d = Infinity) => {
  if (!(d < Infinity) || closedBelow(t, d)) out.set(H(t), t);
  switch (t.$) {
    case "Lam": subterms(t.f, out, Math.min(d, t.i)); return;
    case "App": { const [h, xs] = B.term_unapply(t); if (h.$ !== "Ref") subterms(t.f, out, d); xs.forEach((x) => subterms(x, out, d)); break; }
    case "Ctr": case "ADT": t.x.forEach((x: Term) => subterms(x, out, d)); break;
    case "Eql": subterms(t.a, out, d); subterms(t.b, out, d); break;
  }
};
const litStep = (t: Term): Term => (t.$ === "Lit" && (t.k === "Nat" || t.k === "U32") ? B.lit_step(t) : null);
// first-order matching of pattern p (metavariables >= META) against t; sol is filled in place
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

// ---- normal forms ----
const wnf = (h: Term): Term => attempt(FUEL_NF, () => B.term_wnf(BK.book, h));
// a bounded strong normal form: a stuck call stays a call with its arguments normalized; a closed
// constant (a def with no parameter) unfolds only when its value is tiny; past the node budget the
// raw term stays. With atoms, a call that decides a branch stays folded: a def whose result is an
// enumeration (Bool, Cmp: constructors without fields), on small arguments; so the goal reads
// Bool.when(FileEp.is_resource(r), ..), not the stuck insides of is_resource's body
type NfBudget = { n: number; atoms: boolean };
const isAtom = (s: Term, d: number): boolean => {
  const [hd, xs] = B.term_unapply(s);
  const f = B.term_strip(hd);
  return f.$ === "Ref" && xs.length > 0 && enumDef(f.k) && xs.every((x) => attempt(FUEL_NF, () => lowerB(x, d, { n: 16 })) !== undefined);
};
const enumDef = (k: string): boolean => {
  let r = BK.enums.get(k);
  if (r === undefined) {
    const t = BK.raw[k];
    r = withOwnFuel(40000, () => {
      const o = t?.$ === "Def" && t.n > 0 ? attempt(20000, () => openMeta(t.T, t.n)) : null;
      const w = o && wnf(o.concl);
      const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
      return adt?.$ === "ADT" && adt.c.length >= 2 && adt.c.length <= 8 && adt.c.every((c: Term) => c.n === 0);
    });
    BK.enums.set(k, r);
  }
  return r;
};
const nfGo = (h: Term, d: number, b: NfBudget): Term => {
  b.n--;
  const s = B.term_strip(h);
  if (b.atoms && s.$ === "App" && isAtom(s, d)) { const [hd, xs] = B.term_unapply(s); return xs.reduce((r: Term, x: Term) => B.App(r, nfArg(x, d, b)), B.Ref(B.term_strip(hd).k)); }
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
// memoized per book by the lowered input (sibling goals share most hypotheses); a normal form that
// does not settle within FUEL_NFS lookups is not taken (undefined: the term as stated is used)
const FUEL_NFS = 40000;
// a weak normal form on the fuel left (inside nf: every step shares nf's fuel, so nf's cap holds)
const wnfShared = (h: Term): Term => {
  if (fuel <= 0) return undefined;
  try { return B.term_wnf(BK.book, h); } catch (e) { if (e === TIMEOUT) throw e; return undefined; }
};
const nfObj = new WeakMap<object, Map<number, Term>>(); // by the term object: no lowering on a hit
const nf = (h: Term, d: number, atoms = false, cap = FUEL_NFS): Term => {
  const sub = d * 4 + (atoms ? 1 : 0) + cap * 8;
  const byObj = typeof h === "object" && h ? nfObj.get(h) : undefined;
  if (byObj?.has(sub)) return byObj.get(sub);
  const r = nfKeyed(h, d, atoms, cap);
  if (typeof h === "object" && h) { const m = byObj ?? new Map(); m.set(sub, r); if (!byObj) nfObj.set(h, m); }
  return r;
};
const nfKeyed = (h: Term, d: number, atoms: boolean, cap: number): Term => {
  const raw = attempt(FUEL_NF, () => lower0(h, d));
  if (!raw) return undefined;
  const k = mixH(H(raw), d, atoms ? 1 : 0, cap);
  if (BK.nfs.has(k)) return BK.nfs.get(k);
  const r = attempt(cap, () => {
    const t = canon(nfGo(h, d, { n: NF_NODES, atoms }));
    return atoms ? refold(t, d, { n: 400 }) : t;
  });
  if (BK.nfs.size > 200000) BK.nfs.clear();
  BK.nfs.set(k, r);
  return r;
};
// bend2's weak normal form unfolds a wrapper (a def with no match of its own) while it reduces a match
// around it; refold puts each enumeration wrapper back: its unfolded body, over metavariables, matched
// against the subterms (innermost first)
type Wrap = { k: string; n: number; P: Term };
const wrapsOf = (): Map<string, Wrap[]> => {
  BK.wraps ??= withOwnFuel(5000000, buildWraps); // built once per book; a TIMEOUT leaves nothing cached
  return BK.wraps;
};
const buildWraps = (): Map<string, Wrap[]> => {
  let m = new Map<string, Wrap[]>();
  for (const k of Object.keys(BK.raw)) {
    const t = BK.raw[k];
    if (t?.$ !== "Def" || t.v === null || t.n === 0 || t.n > 6 || !enumDef(k) || strictOf(k) !== null) continue;
    const call = Array.from({ length: t.n }, (_, j) => B.Var("?" + j, META + j)).reduce((f: Term, x: Term) => B.App(f, x), B.Ref(k));
    const P = nf(call, 0);
    if (!P || P.$ !== "App" || headKey(P) === "R:" + k || size(P, 201) > 200) continue;
    const hk = headKey(P);
    m.set(hk, [...(m.get(hk) ?? []), { k, n: t.n, P }]);
  }
  // refold folds inner wrappers first, so each pattern holds its inner wrappers folded too (at depth
  // 2 * META, where its metavariables count as closed)
  for (let pass = 0; pass < 3; pass++) {
    const next = new Map<string, Wrap[]>();
    for (const w of [...m.values()].flat()) {
      const P = w.P.$ === "App" ? attempt(FUEL_NF, () => B.App(refold(w.P.f, 2 * META, { n: 400 }, m), refold(w.P.x, 2 * META, { n: 400 }, m))) ?? w.P : w.P;
      next.set(headKey(P), [...(next.get(headKey(P)) ?? []), { ...w, P }]);
    }
    m = next;
  }
  return m;
};
const refold = (t: Term, d: number, b: { n: number }, wraps = wrapsOf()): Term => {
  if (--b.n < 0) return t;
  const go = (x: Term) => refold(x, d, b, wraps);
  const u = t.$ === "App" ? B.App(go(t.f), go(t.x)) : t.$ === "Ctr" ? B.Ctr(t.k, t.x.map(go)) : t.$ === "Eql" ? B.Eql(go(t.a), go(t.b), t.T) : t;
  if (u.$ !== "App") return u;
  for (const w of wraps.get(headKey(u)) ?? []) {
    const sol: (Term | null)[] = new Array(w.n).fill(null);
    if (match(w.P, u, sol, d) && sol.every((x) => x)) return sol.reduce((f: Term, x) => B.App(f, x), B.Ref(w.k));
  }
  return u;
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
    walk(t0.v, Array.from({ length: t0.n }, (_, i) => i));
  }
  BK.matched.set(k, out);
  return out;
};
// the subterms that block evaluation: the strict argument of a stuck call, a variable or a stuck call
const blockers = (t: Term, out: Term[]) => {
  switch (t.$) {
    case "App": {
      const [h, xs] = B.term_unapply(t);
      if (h.$ === "Ref") {
        const j = strictOf(h.k);
        const blk = (a: Term) => a.$ === "Var" || (a.$ === "App" && B.term_unapply(a)[0].$ === "Ref");
        // the strict argument, else every matched one; a matched constructor's variable fields too (a
        // case tree that reads Core{Mount{..}, ..} is stuck on the Mount field)
        const ms = j !== null && j < xs.length && blk(xs[j]) ? new Set([j]) : matchedOf(h.k);
        xs.forEach((a, i) => {
          if (!ms.has(i)) return;
          if (blk(a)) out.push(a);
          else if (a.$ === "Ctr") for (const f of a.x) if (f.$ === "Var") out.push(f);
        });
      }
      xs.forEach((x) => blockers(x, out));
      break;
    }
    case "Ctr": case "ADT": t.x.forEach((x: Term) => blockers(x, out)); break;
    case "Eql": blockers(t.a, out); blockers(t.b, out); break;
  }
};

// ---- propositions and the lemma index ----
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
      return t.c.length === 1 && w.x.length > 0 && n < 20 && w.x.every((a: Term) => {
        const wa = wnf(a);
        if (!wa || wa.$ === "Qua" || wa.$ === "Qnt") return true;
        return wa.$ === "Lam" ? isProp(wa.f(B.Var("_", FRESH + n)), n + 1) : isProp(wa, n + 1);
      });
    }
    case "All": return n < 20 ? isProp(w.B(B.Var("_", FRESH + n)), n + 1) : true;
    default: return false;
  }
};
// a proposition for the bench: also a stuck call of a def whose every case gives one (Le(a, b))
const isPropType = (h: Term, n = 0): boolean => {
  if (n > 6) return false;
  const w = wnf(h);
  if (!w) return false;
  switch (w.$) {
    case "Eql": return true;
    case "ADT": { const t = BK.raw[w.k]; return t?.$ === "ADT" && (t.c.length === 0 || (t.c.length === 1 && t.c[0].n === 0)); }
    case "All": return isPropType(w.B(B.Var("_", FRESH + n)), n + 1);
    case "App": {
      const f = B.term_strip(B.term_unapply(w)[0]);
      const t = f.$ === "Ref" ? BK.raw[f.k] : null;
      if (t?.$ !== "Def" || t.v === null) return false;
      const leaves: Term[] = [];
      let budget = 64;
      const walk = (x: Term) => {
        if (--budget < 0) return;
        x = B.term_strip(x);
        if (x.$ === "Lam") walk(x.f(B.Var("_", FRESH + 50 + budget)));
        else if (x.$ === "Mat") { walk(x.h); walk(x.m); }
        else if (x.$ !== "Efq") leaves.push(x);
      };
      walk(t.v);
      return budget >= 0 && leaves.length > 0 && leaves.every((l) => isPropType(l, n + 1));
    }
    default: return false;
  }
};
// a parameter a hypothesis or a proof must give: a fact, or a type that still names other parameters
const isPrem = (A: Term, d: number): boolean => {
  if (isProp(A)) return true;
  if (attempt(FUEL_NF, () => hasMeta(lower(A, d))) !== true) return false;
  const w = wnf(A);
  return !!w && w.$ !== "Typ" && w.$ !== "Qnt" && w.$ !== "Qua";
};
type Dom = { q: Term; k: string; A: Term };
// t as a binder (@x: A -> B), as written or after a weak normal form; null when it is none
const asAll = (t: Term): Term => {
  const s = B.term_strip(t);
  if (s.$ === "All") return s;
  const w = wnf(t);
  return w?.$ === "All" ? w : null;
};
// T's binders: its n parameters, then up to 8 premises of its conclusion
const arity = (T: Term, n: number): number => {
  let t = T, k = 0;
  for (; k < n + 8; k++) {
    const s = asAll(t);
    if (!s) break;
    t = s.B(B.Var("_", META + k));
  }
  return Math.max(k, n);
};
// T's first n binders opened: parameter j is the metavariable META + j unless sol fixes it
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
// every def with a body (or Base's), filed by the head of its conclusion and, for an equation, of each
// side (as stated and in normal form); open defs are not lemmas
const buildIndex = () => {
  const add = <V>(m: Map<string, V[]>, k: string, v: V) => { let a = m.get(k); if (!a) m.set(k, a = []); a.push(v); };
  for (const k of Object.keys(BK.raw)) {
    const t = BK.raw[k];
    if (t?.$ !== "Def" || t.x > 0 || (t.v === null && t.b !== true) || t.i || isOpen(k)) continue;
    const L: Lemma = { k, order: BK.order.get(k) ?? -1, n: arity(t.T, t.n), np: t.n };
    const o = attempt(20000, () => openMeta(t.T, L.n));
    const c = o && attempt(20000, () => lower(o.concl, 0));
    if (!o || !c) continue;
    const hk = headKey(c);
    if (hk === "V" || hk === "*" || hk === "Typ") continue;
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
  }
  for (const v of BK.apply.values()) v.sort((a, b) => b.order - a.order);
  for (const v of BK.rw.values()) v.sort((a, b) => b.L.order - a.L.order);
};

// ---- printing ----
// bend2 prints a call of a zero-parameter def (def Bytes() -> Data) as its bare name, which reads back
// as the def itself: add the "()" back
const zeroFix = (s: string, file: Term): string => {
  let re = BK.zero.get(file);
  if (re === undefined) {
    const names = Object.keys(BK.raw).filter((k) => BK.raw[k]?.$ === "Def" && BK.raw[k].n === 0 && BK.raw[k].v)
      .map((k) => B.name_show(file, k)).filter((n: string) => /^[A-Za-z_][\w.]*$/.test(n));
    re = names.length ? new RegExp("(?<![\\w.])(" + names.sort((a, b) => b.length - a.length).map((n) => n.replace(/\./g, "\\.")).join("|") + ")(?![\\w.(])", "g") : null;
    BK.zero.set(file, re);
  }
  return re ? s.replace(re, "$1()") : s;
};
const clip = (s: string, n: number) => (s.length > n ? s.slice(0, n) + " … [" + (s.length - n) + " more chars]" : s);

// ---- goals ----
// a def whose body is being proven: the target, or a helper gen3 made (level: helpers above it)
type Owner = { k: string; short: string; root: string; T: Term; n: number; order: number; file: Term; level: number };
type Goal = {
  own: Owner; ctx: Term; d: number; ty: Term; lhs: Term; qt: Term; env: Term; names: string[]; ckey: number;
  pend: number; pnames: string[]; pmany: boolean[]; split: boolean; path: string;
};
const owner = (k: string, level = 0, root = shortOf(k)): Owner => {
  const t = BK.raw[k];
  return { k, short: shortOf(k), root, T: t.T, n: t.n, order: BK.order.get(k) ?? BK.book.order.length, file: BK.files.get(k), level };
};
const show = (t: Term, names: string[], file: Term): string => zeroFix(B.term_show(t, -1, names.slice(), file), file);
// a goal's terms are lowered one level below its context (LD), so that a rewrite's motive can bind
// `_` at level g.d; every term of a goal is lowered at LD and printed with the names [...names, "_"]
const LD = (g: Goal) => g.d + 1;
const sh = (g: Goal, t: Term): string => show(t, [...g.names, "_"], g.own.file);
const ann = (g: Goal, i: number): Term => B.pmap_get(g.ctx, i);
const qn = (q: Term): number => (q.$ === "None" ? 0 : q.$ === "Lone" ? 1 : 2);
// by the normal form (two goals that convert are one goal: a rewrite that changes nothing is a cycle)
const goalKey = (g: Goal, N: Term): number => attempt(FUEL_NF, () => mixH(g.ckey, qn(g.qt), H(N ?? lower(g.ty, LD(g))))) ?? Math.random();

const parseLow = (text: string, g: Goal): Term => {
  const p = parserAt(text, 0, g.own.file, g.names);
  return withHols(() => {
    const lt = B.parse_block(p);
    B.parse_skip(p);
    if (p.pos < text.length) B.parse_fail(p, "the end of the fragment");
    return lt;
  });
};
// does text check at g (bend2's term_check, plus the affinity of g's live binders)?
const tryText = (g: Goal, text: string): boolean =>
  attempt(FUEL_CHECK, () => {
    const c = B.term_check(BK.book, g.lhs, B.term_higher(parseLow(text, g), g.env), g.qt, g.ty, g.ctx, g.d);
    if (g.qt.$ !== "None") for (const [i, a] of B.pmap_to_array(g.ctx)) if (a.q.$ === "Lone" && B.pmap_get(c.us, i)?.$ === "Many") throw LIN;
    return true;
  }) === true;

const intro = (g: Goal, name: string, many: boolean): Goal | null => {
  const t = asAll(g.ty);
  if (!t) return null;
  const x = B.Var(name, g.d);
  const lhs = g.lhs.n > 0 ? { ...g.lhs, t: B.term_apply(g.lhs.t, x), n: g.lhs.n - 1 } : g.lhs;
  const q = many && t.q.$ === "Lone" ? B.Many() : t.q;
  const Ah = attempt(FUEL_NF, () => H(lower(t.A, g.d))) ?? 0;
  return {
    ...g, ctx: B.ctx_bind(g.ctx, g.d, q, name, t.A), d: g.d + 1, ty: t.B(x), lhs, env: B.list_set(g.env, g.d, x),
    names: [...g.names, name], ckey: mixH(g.ckey, qn(q), strH(name), Ah),
    pend: Math.max(0, g.pend - 1), pnames: g.pnames.slice(1), pmany: g.pmany.slice(1),
  };
};
const introAll = (g: Goal): Goal | null => {
  let c: Goal | null = g;
  while (c && c.pend > 0) c = intro(c, c.pnames[0], c.pmany[0]);
  return c;
};
const KEYWORD = /^(def|type|law|match|case|do|return|for|exs|where|is|import|Type|Data|Kind|Quant)$/;
const fresh = (g: Goal, base: string, used: Set<string>): string => {
  const b = base.replace(/[^A-Za-z0-9_]/g, "") || "x";
  for (let i = 0; ; i++) {
    const nm = i === 0 ? b : b + String(i);
    const q = g.own.file.ns === "" ? nm : g.own.file.ns + ":" + nm;
    if (!used.has(nm) && !(q in BK.raw) && !(nm in BK.raw) && nm !== "_" && !KEYWORD.test(nm)) { used.add(nm); return nm; }
  }
};
// the parameter names as k's header writes them (a law's fill renames them: def T.law(ty, t, k, v))
const headerNames = (k: string, n: number): string[] | null => {
  const ds = defSrc(k), file = BK.files.get(k);
  if (!ds || !file) return null;
  const p = parserAt(ds.header, ds.header.indexOf("(") + 1, file);
  const tele = attempt(FUEL_NF, () => withHols(() => B.parse_tele(p, ")")));
  return tele && tele.length === n ? tele.map((c: Term) => c[1]) : null;
};
const rootGoal = (own: Owner): Goal => {
  const def = BK.raw[own.k];
  const qs = B.tele_unbind(BK.book, def.T).doms.map((dm: Term) => dm[0]);
  const named = headerNames(own.k, def.n);
  const pnames: string[] = [];
  let t = def.T;
  for (let j = 0; j < def.n; j++) { const s = B.term_strip(t); pnames.push(named?.[j] ?? s.k); t = s.B(B.Var(pnames[j], j)); }
  return {
    own, ctx: B.ctx_nil(), d: 0, ty: def.T, lhs: { t: B.Ref(own.k), n: def.n - def.x, def: own.k, qs, u: def.u }, qt: B.Lone(), env: null,
    names: [], ckey: 0, pend: def.n, pnames, pmany: pnames.map(() => false), split: false, path: "",
  };
};
// the goal of the hole ?gen3hole, from bend2's error at it (null: the error is elsewhere)
const holeGoal = (own: Owner, err: Term, at: string): Goal | null => {
  if (!err || err.$ !== "Err" || typeof err.exp === "string" || err.obs?.$ !== "Hol" || err.obs.k !== "gen3hole") return null;
  const arr = B.pmap_to_array(err.ctx).sort((a: Term, b: Term) => a[0] - b[0]);
  const d = arr.length ? arr[arr.length - 1][0] + 1 : 0;
  const names: string[] = [];
  let env = null, ckey = 0;
  for (let i = 0; i < d; i++) {
    const a = B.pmap_get(err.ctx, i);
    names.push(a?.k ?? "_");
    env = B.list_set(env, i, B.Var(a?.k ?? "_", i));
    ckey = mixH(ckey, a ? qn(a.q) : 3, strH(a?.k ?? "_"), a ? attempt(FUEL_NF, () => H(lower(a.T, i))) ?? 0 : 0);
  }
  return {
    own, ctx: err.ctx, d, ty: err.exp, lhs: { t: B.Ref(own.k), n: 0, def: own.k, qs: [], u: true }, qt: B.Lone(), env, names, ckey,
    pend: 0, pnames: [], pmany: [], split: false, path: at, // no self-call: bend2 checks a hole's descent only in the whole body
  };
};
const isData = (g: Goal, A: Term) => attempt(FUEL_NF, () => { B.term_check(BK.book, g.lhs, A, B.None(), B.Typ(B.Qua(B.Many())), g.ctx, g.d); return true; }) === true;

// `match x:` on the j-th pending binder of n: one node per constructor (null: not a datatype)
type Arm = { pat: string; node: Goal };
const split = (n: Goal, j: number): Arm[] | null => {
  let g: Goal | null = n;
  for (let i = 0; i < j && g; i++) g = intro(g, g.pnames[0], g.pmany[0]);
  const t = g && wnf(g.ty);
  if (!g || !t || t.$ !== "All" || t.q.$ === "None") return null;
  const at = g;
  const A = wnf(t.A);
  const adt = A?.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(BK.book, A, at.ctx, at.own.k)) : null;
  if (!adt || adt.c.length === 0) return null;
  const used = new Set([...at.names, ...at.pnames]);
  const arms: Arm[] = [];
  for (const ctr of adt.c) {
    const arm = armOf(n, at, t, A, ctr, used);
    if (!arm) return null;
    arms.push(arm);
  }
  return arms;
};
// the arm of constructor ctr: the goal at ctr{fields} (fields named, reusable when they are Data)
const armOf = (n: Goal, at: Goal, t: Term, A: Term, ctr: Term, used: Set<string>): Arm | null => {
  const tel = attempt(FUEL_NF, () => B.tele_fill(BK.book, ctr.T, A.x, at.ctx, at.own.k));
  const mk = (cur: Term, m: number, xs: Term[]): Term => {
    if (m === 0) return t.B(B.Ctr(ctr.k, xs));
    const c = B.tele_head(BK.book, cur, at.ctx, at.own.k);
    const dem = c.q.$ === "None" ? B.None() : c.q.$ === "Lone" ? t.q : B.quant_add(t.q, t.q);
    return B.All(dem, c.k, c.i, c.A, (x: Term) => mk(c.B(x), m - 1, xs.concat([x])));
  };
  const goal = tel && attempt(FUEL_NF, () => mk(tel, ctr.n, []));
  if (!goal) return null;
  const lhs = at.lhs.n > 0 ? { ...at.lhs, t: B.lhs_ext(at.lhs.t, ctr.k, ctr.n), n: at.lhs.n - 1 + ctr.n } : at.lhs;
  const fnames: string[] = [], fmany: boolean[] = [];
  const isNat = ctr.k === "Succ" || ctr.k === "Zero";
  const sname = at.pnames[0];
  let probe: Goal | null = { ...at, ty: goal, lhs, pend: ctr.n, pnames: [], pmany: [] };
  let cur = goal;
  for (let f = 0; f < ctr.n; f++) {
    const c = wnf(cur);
    if (!c || c.$ !== "All") return null;
    const nm = fresh(at, isNat ? (sname.length <= 2 ? sname + "p" : "p") : c.k, used);
    const many = !isNat && c.q.$ === "Lone" && probe !== null && isData(probe, c.A);
    fnames.push(nm);
    fmany.push(many);
    probe = probe ? intro({ ...probe, pend: 1, pnames: [nm], pmany: [many] }, nm, many) : null;
    cur = c.B(B.Var(nm, at.d + f));
  }
  const node: Goal = {
    ...at, ty: goal, lhs, pend: ctr.n + at.pend - 1, pnames: [...fnames, ...at.pnames.slice(1)], pmany: [...fmany, ...at.pmany.slice(1)],
    split: true, path: n.path + "/" + shortOf(ctr.k),
  };
  const cn = B.name_show(at.own.file, ctr.k);
  return { pat: isNat ? (ctr.k === "Zero" ? "0n" : "1n+" + fnames[0]) : cn + "{" + fnames.map((f, i) => (fmany[i] ? "+" : "") + f).join(", ") + "}", node };
};
// the pending binders worth a split: those that block evaluation (in the goal or a hypothesis; a
// record that blocks early), then records the goal reads (at most 2), then enumerations (Bool, Cmp)
const splitCands = (n: Goal, lg: Goal | null): number[] => {
  const out: number[] = [], records: number[] = [], enums: number[] = [];
  let r: Goal | null = n;
  for (let j = 0; j < n.pend && r; j++) {
    const t = wnf(r.ty);
    if (!t || t.$ !== "All") break;
    const A = t.q.$ !== "None" ? wnf(t.A) : null;
    const a = A?.$ === "ADT" ? BK.raw[A.k] : null;
    if (a?.$ === "ADT" && a.c.length === 1 && a.c[0].n > 0 && !/^(U32|F32|Chr|Word)$/.test(A.k) && !/\b(?:WCon|WNil)$/.test(a.c[0].k)) records.push(j);
    if (a?.$ === "ADT" && a.c.length >= 2 && a.c.length <= 4 && a.c.every((c: Term) => c.n === 0)) enums.push(j);
    r = intro(r, r.pnames[0], r.pmany[0]);
  }
  const add = (j: number) => { if (j >= 0 && j < n.pend && !out.includes(j)) out.push(j); };
  if (lg) {
    const blk: Term[] = [];
    // the stuck structure is enough here: small budgets
    const N = nf(lg.ty, lg.d, false, 8000);
    if (N) blockers(N, blk);
    for (let i = lg.d - 1; i >= 0; i--) { const a = ann(lg, i); const h = a && nf(a.T, lg.d, false, 2000); if (h) blockers(h, blk); }
    const blocking = blk.filter((t) => t.$ === "Var").map((t) => t.i - n.d);
    // the first blocker, a record that blocks, the other blockers; then (below) the other records
    blocking.slice(0, 1).forEach(add);
    records.filter((j) => blocking.includes(j)).forEach(add);
    blocking.forEach(add);
  }
  records.slice(-2).reverse().forEach(add);
  enums.forEach(add);
  const depth = n.path.split("/").length - 1;
  return out.slice(0, depth >= 4 ? 1 : depth >= 2 ? 2 : 3);
};

// ---- facts: hypotheses, and what follows from one in one step ----
// a fact's proof text uses its hypothesis once; T is its type as stated, N in normal form; empty: a
// proof of Empty (a constructor clash)
type Fact = { pf: string; T: Term; N: Term; q: Term; i: number; empty?: boolean; A?: Term }; // A: N with deciding calls folded (lift)
// an inline match eliminator {\{C1: ..; \{C2: ..; \{}}} : T -> Type}: each constructor's fields bound
// by lambdas, its body from arm(ctor, field names)
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
  if (E?.$ !== "Eql" || H(E.a) === H(E.b)) return;
  const [a, b, T] = [E.a, E.b, E.T];
  const sym = symText(g, E, h.pf);
  out.push({ pf: sym, T: B.Eql(b, a, T), N: B.Eql(b, a, T), q: h.q, i: -1 });
  const ca = asCtr(a), cb = asCtr(b);
  if (ca?.$ !== "Ctr" || cb?.$ !== "Ctr") return;
  if (ca.k !== cb.k) {
    // a clash: the motive is Empty at b's constructor, Unit elsewhere
    const P = elim(g, T, (k) => (k === cb.k ? "Empty" : "Unit"));
    if (P) out.push({ pf: "(%" + h.pf + " : " + P + "; Unit{})", T: E, N: E, q: h.q, i: -1, empty: true });
    return;
  }
  // injectivity: field j of a equals field j of b
  ca.x.forEach((x: Term, j: number) => {
    const y = cb.x[j];
    if (out.length > 48 || H(x) === H(y)) return;
    const F = attempt(FUEL_NF, () => lower(B.term_infer(BK.book, g.lhs, B.term_higher(x, g.env), B.None(), g.ctx, g.d).ty, LD(g)));
    if (!F) return;
    const P = elim(g, T, (k, fs) => (k === ca.k ? "{" + fs[j] + " == " + sh(g, y) + " : " + sh(g, F) + "}" : "Unit"));
    if (P) out.push({ pf: "(%" + sym + " : " + P + "; {==})", T: B.Eql(x, y, F), N: B.Eql(x, y, F), q: h.q, i: -1 });
  });
};
const factsOf = (g: Goal): Fact[] => {
  const k = mixH(g.ckey, g.d);
  let fs = S.facts.get(k);
  if (fs) return fs;
  fs = [];
  for (let i = g.d - 1; i >= 0; i--) {
    const a = ann(g, i);
    if (!a || g.names[i] === "_") continue;
    const T = attempt(FUEL_NF, () => lower(a.T, LD(g)));
    if (!T) continue;
    const f: Fact = { pf: g.names[i], T, N: nf(a.T, LD(g), false, 20000) ?? T, q: a.q, i };
    fs.push(f);
    attempt(FUEL_NF, () => derive(g, f, fs!));
  }
  S.facts.set(k, fs);
  return fs;
};
const usable = (f: Fact, qt: Term) => qt.$ === "None" || f.q.$ !== "None";

// ---- proofs ----
const HOLE = "\u0000";
type Pf =
  | { t: "tm"; s: string; subs: Pf[] } // text; its i-th HOLE mark is subs[i]
  | { t: "rw"; e: Pf; P: string; k: Pf } // %e : P; k
  | { t: "lam"; x: string; k: Pf }
  | { t: "mt"; x: string; arms: { pat: string; k: Pf }[] }
  | { t: "def"; name: string; head: string; body: Pf; call: string } // a helper def, used through its call
  | { t: "hole"; n: GNode };
const tm = (s: string, subs: Pf[] = []): Pf => ({ t: "tm", s, subs });
const inline = (p: Pf): string => {
  switch (p.t) {
    case "tm": { let i = 0; return p.s.replace(/\u0000/g, () => inline(p.subs[i++])); }
    case "rw": return "(%" + inline(p.e) + " : " + p.P + "; " + inline(p.k) + ")";
    case "lam": return p.x + " => " + inline(p.k);
    case "def": return p.call;
    case "hole": return "?TODO";
    case "mt": throw new Error("a match is not an expression");
  }
};
const flat = (p: Pf): string => (p.t === "rw" ? "%" + inline(p.e) + " : " + p.P + "; " + flat(p.k) : inline(p));
const render = (p: Pf, ind: string, out: string[]) => {
  if (p.t === "rw") { out.push(ind + "%" + inline(p.e) + " :", ind + "  " + p.P); render(p.k, ind, out); }
  else if (p.t === "mt") for (const [i, a] of p.arms.entries()) { if (i === 0) out.push(ind + "match " + p.x + ":"); out.push(ind + "  case " + a.pat + ":"); render(a.k, ind + "    ", out); }
  else out.push(ind + inline(p));
};
const kidsOf = (p: Pf): Pf[] => (p.t === "tm" ? p.subs : p.t === "rw" ? [p.e, p.k] : p.t === "lam" ? [p.k] : p.t === "mt" ? p.arms.map((a) => a.k) : p.t === "def" ? [p.body] : []);
// the helper defs a proof uses, each after the helpers it calls (a def calls only defs above it)
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
const bodyText = (p: Pf): string => { const out: string[] = []; render(p, "  ", out); return out.join("\n"); };

// ---- the search: proof numbers over an AND/OR tree ----
// A goal node (OR) is proven by any one of its alternatives; an alternative (AND: one tactic step) by
// all of its subgoals. pn: an estimate of the work left to prove a node, dn: to refute it. The search
// expands the most-proving goal (follow the least pn at OR nodes, the least dn at AND nodes), then
// updates the numbers up to the root. An alternative is checked (its text with ?TODO subgoals) only
// when the search first reaches it, and again whole when its subgoals are proven.
const INF = 1e9, MAX_NODES = 60000, MAX_LV = 6, MAX_RW = 4;
type GNode = { g: Goal; key: number; up: Alt | null; alts: Alt[] | null; pn: number; dn: number; pf: Pf | null; lv: number; rws: number; raw?: Term; N?: Term; A?: Term };
type Alt = {
  up: GNode; tag: string; note: string; w: number; kids: GNode[]; pn: number; dn: number; pf: Pf | null; dead: boolean;
  probe: string | null; build: (ps: Pf[]) => Pf; open?: () => GNode[] | null; // open: kids made when first reached
};
type Search = { root: GNode; proved: Map<number, Pf>; facts: Map<number, Fact[]>; nodes: number; helpers: number; tags: Map<string, number>; internal: number };
let S: Search;
const newSearch = (root: GNode): Search => (S = { root, proved: new Map(), facts: new Map(), nodes: 0, helpers: 0, tags: new Map(), internal: 0 });
const tag = (t: string) => S.tags.set(t, (S.tags.get(t) ?? 0) + 1);

const mkNode = (g: Goal, up: Alt | null, lv: number, rws: number): GNode | null => {
  const N = g.pend === 0 ? nf(g.ty, LD(g)) : undefined;
  const key = goalKey(g, N);
  for (let a = up; a; a = a.up.up) if (a.up.key === key) return null; // a cycle: the goal restates an ancestor
  return { g, key, up, alts: null, pn: 1, dn: 1, pf: null, lv, rws, N };
};
// a step: its text with a HOLE mark per subgoal (its note shows ?, its probe checks ?TODO), or null
// for a step bend2 cannot check alone (a split, a helper: the final def check does)
const mkAlt = (up: GNode, tag: string, text: string | null, w: number, build: (ps: Pf[]) => Pf, note = text?.replace(/\u0000/g, "?") ?? tag): Alt =>
  ({ up, tag, note, w, kids: [], pn: w + 1, dn: 1, pf: null, dead: false, probe: text === null ? null : text.replace(/\u0000/g, "?TODO"), build });
// the proof of {b == a : T} from e : {a == b : T} (E: the equation that e proves)
const symText = (g: Goal, E: Term, e: string) => "Equal.sym(" + sh(g, E.T) + ", " + sh(g, E.a) + ", " + sh(g, E.b) + ", " + e + ")";
// kids from goals (null: a kid restates an ancestor, the alternative is useless)
const withKids = (a: Alt, gs: Goal[], lv: number, rws: number): Alt | null => {
  for (const g of gs) { const k = mkNode(g, a, lv, rws); if (!k) return null; a.kids.push(k); }
  return a;
};

const calcAlt = (a: Alt) => {
  if (a.pf) { a.pn = 0; a.dn = INF; return; }
  if (a.dead) { a.pn = INF; a.dn = 0; return; }
  // the hardest subgoal, plus a fifth of the others: a split's arms are alike, not separate proofs
  let sum = 0, max = 0, dn = unreached(a) ? 1 : INF;
  for (const k of a.kids) { sum += k.pn; max = Math.max(max, k.pn); if (!k.pf) dn = Math.min(dn, k.dn); }
  a.pn = Math.min(a.w + (a.open ? 1 : 0) + max + 0.2 * (sum - max), INF);
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
  if (n.g.pend === 0 && pf.t !== "def") S.proved.set(n.key, pf);
};
// every kid proven: the step whole, checked once more at its goal (subproofs may share a binder); a
// step without kids is its checked probe, a split or a helper is checked by bend2's final def check
const close = (a: Alt) => {
  const pf = a.build(a.kids.map((k) => k.pf!));
  if (!(a.kids.length === 0 || a.up.g.pend > 0 || pf.t === "def" || tryText(a.up.g, flat(pf)))) { a.dead = true; return; }
  a.pf = pf;
  tag(a.tag);
  if (!a.up.pf) setProof(a.up, pf);
};
// not yet reached: its text unchecked, or its kids not made yet
const unreached = (a: Alt) => a.probe !== null || a.open !== undefined;
// numbers from n up to the root
const update = (n0: GNode) => {
  for (let n: GNode | null = n0; n; ) {
    calcNode(n);
    const a: Alt | null = n.up;
    if (!a) return;
    if (!a.pf && !a.dead) {
      if (n.pn >= INF) a.dead = true;
      else if (!a.open && a.kids.every((k) => k.pf)) close(a);
    }
    calcAlt(a);
    n = a.up;
  }
};
// an alternative reached for the first time: its kids made (a helper) or its text checked
const reach = (a: Alt) => {
  if (a.open) {
    const ks = a.open();
    a.open = undefined;
    if (!ks) a.dead = true;
    else a.kids = ks;
  } else if (a.probe !== null) {
    if (!tryText(a.up.g, a.probe)) a.dead = true;
    a.probe = null;
    if (!a.dead && a.kids.length === 0) close(a);
  }
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
// one step: walk to the most-proving node and expand it (or reach the alternative on the way)
const step = () => {
  let n = S.root;
  for (;;) {
    if (!n.alts) {
      try { expand(n); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; n.alts = []; }
      update(n);
      return;
    }
    const a = bestAlt(n);
    if (!a) { update(n); return; }
    if (unreached(a)) {
      try { reach(a); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; a.dead = true; }
      calcAlt(a);
      update(n);
      return;
    }
    const k = bestKid(a);
    if (!k) { update(n); return; }
    n = k;
  }
};
// the search until it proves the root, refutes it, or runs out; every 200 ms it yields to the event
// loop (so the worker's progress messages leave the process), every second it reports progress
const run = async (until: number, progress: () => void) => {
  deadline = until;
  let yielded = performance.now(), reported = yielded;
  try {
    while (!S.root.pf && S.root.pn < INF && S.nodes < MAX_NODES && !late()) {
      step();
      const now = performance.now();
      if (now - reported > 1000) { reported = now; progress(); }
      if (now - yielded > 200) { deadline = Infinity; await Bun.sleep(0); deadline = until; yielded = performance.now(); }
    }
  } catch (e) {
    if (e !== TIMEOUT) throw e;
  } finally {
    deadline = Infinity;
  }
};
const expand = (n: GNode) => {
  S.nodes++;
  const c = n.g.pend === 0 ? S.proved.get(n.key) : undefined;
  if (c && tryText(n.g, flat(c))) { n.alts = []; setProof(n, c); tag("cache"); return; }
  n.alts = n.g.pend > 0 ? nodeAlts(n) : leafAlts(n);
};
// the best partial proof under n: an alternative counts when it was checked; fewest holes first, then
// most closed steps
const partial = (n: GNode): { pf: Pf; holes: number; closed: number } => {
  if (n.pf) return { pf: n.pf, holes: 0, closed: 1 };
  let best = { pf: { t: "hole", n } as Pf, holes: 1, closed: 0 };
  for (const a of n.alts ?? []) {
    if (a.dead || unreached(a) || a.kids.length === 0) continue;
    const ks = a.kids.map(partial);
    const holes = ks.reduce((s, k) => s + k.holes, 0), closed = ks.reduce((s, k) => s + k.closed, 0) + (a.tag === "intro" || a.tag.startsWith("lift") ? 0 : 1); // an intro or a lift alone proves nothing
    if (holes < best.holes || (holes === best.holes && closed > best.closed)) best = { pf: a.build(ks.map((k) => k.pf)), holes, closed };
  }
  return best;
};

// ---- node alternatives: a def body with pending binders ----
const nodeAlts = (n: GNode): Alt[] => {
  const alts: Alt[] = [];
  const lg = introAll(n.g);
  if (lg) { const a = withKids(mkAlt(n, "intro", null, 0, (ps) => ps[0], "introduce the parameters"), [lg], n.lv, n.rws); if (a) alts.push(a); }
  for (const j of splitCands(n.g, lg)) {
    const arms = split(n.g, j);
    if (!arms) continue;
    const x = n.g.pnames[j];
    const a = withKids(mkAlt(n, "split", null, 1, (ps) => ({ t: "mt", x, arms: arms.map((r, i) => ({ pat: r.pat, k: ps[i] })) }), "match " + x), arms.map((r) => r.node), n.lv, n.rws);
    if (a) alts.push(a);
  }
  return alts;
};

// ---- leaf alternatives: a goal in a context ----
const targetsOf = (n: GNode): Term[] => {
  n.raw ??= attempt(FUEL_NF, () => lower(n.g.ty, LD(n.g)));
  n.N ??= nf(n.g.ty, LD(n.g));
  n.A ??= nf(n.g.ty, LD(n.g), true);
  const out: Term[] = [];
  for (const t of [n.raw, n.A, n.N]) if (t && !out.some((x) => H(x) === H(t))) out.push(t);
  return out;
};
// a goal that one check closes: {==}, the unit, a fact, a fact of Empty
const closer = (n: GNode, w: Term): Pf | null => {
  const g = n.g;
  if (w.$ === "Eql" && tryText(g, "{==}")) return tm("{==}");
  const adt = w.$ === "ADT" ? BK.raw[w.k] : null;
  if (adt?.$ === "ADT" && adt.c.length === 1 && adt.c[0].n === 0) {
    const s = B.name_show(g.own.file, adt.c[0].k) + "{}";
    if (tryText(g, s)) return tm(s);
  }
  const ts = targetsOf(n);
  const hs = new Set(ts.map(H));
  const goalText = () => sh(g, n.raw ?? ts[0]);
  for (const f of factsOf(g)) {
    if (!usable(f, g.qt)) continue;
    const fits = f.empty ? false : f.i >= 0 ? attempt(FUEL_CHECK, () => B.term_compare("LE", BK.book, ann(g, f.i).T, g.ty, g.d)) === true : hs.has(H(f.T)) || hs.has(H(f.N));
    if (fits && tryText(g, f.pf)) return tm(f.pf);
    const isEmpty = f.empty || (f.N?.$ === "ADT" && BK.raw[f.N.k]?.c?.length === 0);
    if (!isEmpty) continue;
    const s = adt?.$ === "ADT" && adt.c.length === 0 ? f.pf : "Empty.absurd(" + goalText() + ", " + f.pf + ")";
    if (tryText(g, s)) return tm(s);
  }
  return null;
};
const leafAlts = (n: GNode): Alt[] => {
  const g = n.g;
  const w = wnf(g.ty);
  if (!w) return [];
  const c = closer(n, w);
  if (c) { setProof(n, c); tag("close"); return []; }
  if (w.$ === "All") {
    const x = fresh(g, w.k === "_" || w.k === "" ? "x" : w.k, new Set(g.names));
    const b = intro({ ...g, ty: w, pend: 1, pnames: [x], pmany: [false] }, x, false);
    const a = b && withKids(mkAlt(n, "intro", null, 0, (ps) => ({ t: "lam", x, k: ps[0] }), x + " =>"), [b], n.lv, n.rws);
    return a ? [a] : [];
  }
  if (n.lv >= MAX_LV) return [];
  // each tactic on its own: one that fails (a bend2 error, a term too large) costs only its own steps
  const tactics = [() => applyAlts(n), () => ctorAlts(n, w), () => rewriteAlts(n), () => liftAlts(n)];
  const alts = tactics.flatMap((f) => { try { return f(); } catch (e) { if (e === TIMEOUT) throw e; S.internal++; return []; } }).filter((a) => a !== null) as Alt[];
  alts.sort((a, b) => a.w - b.w);
  // a step with no subgoal is checked now: the first that checks proves the goal
  for (const a of alts.filter((x) => x.kids.length === 0 && !x.open).slice(0, 24)) {
    if (tryText(g, a.probe!)) { a.probe = null; close(a); if (n.pf) return []; }
    a.dead = true;
  }
  for (const a of alts) calcAlt(a);
  return alts;
};

// apply: a hypothesis, the induction hypothesis or a lemma whose conclusion matches the goal; its
// parameters from the match, its premises from facts, the rest subgoals
// a callee's binders: its np parameters, then the premises of its conclusion (f(a, b)(h))
type Callee = { text: string; T: Term; n: number; np: number; kind: "hyp" | "ih" | "lemma" };
const callText = (c: Callee, args: string[]) =>
  c.text + (c.np > 0 || args.length === 0 ? "(" + args.slice(0, c.np).join(", ") + ")" : "") + args.slice(c.np).map((a) => "(" + a + ")").join("");
const lemmaCallee = (g: Goal, L: Lemma): Callee => ({ text: B.name_show(g.own.file, L.k), T: BK.raw[L.k].T, n: L.n, np: L.np, kind: "lemma" });
const ihCallee = (g: Goal): Callee => ({ text: g.own.short, T: g.own.T, n: arity(g.own.T, g.own.n), np: g.own.n, kind: "ih" });
const lemmaCands = (g: Goal, targets: Term[]): Callee[] => {
  const seen = new Set<string>(), out: Callee[] = [];
  for (const t of targets) {
    for (const hk of t.$ === "Eql" ? [headKey(t), "E|*"] : [headKey(t)]) {
      for (const L of BK.apply.get(hk) ?? []) {
        if (L.order >= g.own.order || L.k === g.own.k || seen.has(L.k) || out.length >= 64) continue;
        seen.add(L.k);
        out.push(lemmaCallee(g, L));
      }
    }
  }
  return out;
};
// hypotheses that are functions (through aliases)
const hypCallees = (g: Goal): Callee[] => {
  const out: Callee[] = [];
  for (let i = g.d - 1; i >= 0; i--) {
    const a = ann(g, i);
    if (!a || g.names[i] === "_" || (g.qt.$ !== "None" && a.q.$ === "None")) continue;
    let k = 0;
    for (let t = asAll(a.T); t && k < 12; t = asAll(t.B(B.Var("_", FRESH + k)))) k++;
    if (k > 0) out.push({ text: g.names[i], T: a.T, n: k, np: 0, kind: "hyp" });
  }
  return out;
};
// the distinct solutions of c's conclusion (or one side of it: pick) against the targets
const conclSols = (g: Goal, c: Callee, targets: Term[], pick?: (e: Term) => Term | null): { sols: (Term | null)[][]; spec: number } => {
  const o = openMeta(c.T, c.n);
  const pc0 = o && attempt(FUEL_NF, () => lower(o.concl, LD(g)));
  const sols: (Term | null)[][] = [];
  if (!o || !pc0) return { sols, spec: 0 };
  const seen = new Set<string>();
  const push = (p: Term | null, t: Term) => {
    if (!p) return;
    const s: (Term | null)[] = new Array(c.n).fill(null);
    if (!match(p, t, s, g.d)) return;
    const k = s.map((x) => (x ? String(H(x)) : "_")).join(";");
    if (!seen.has(k)) { seen.add(k); sols.push(s); }
  };
  const pc = pick ? pick(pc0) : pc0;
  // {?a == ?b} fits every equation (Equal.sym): matching both orientations does its work
  const meta = (t: Term) => t.$ === "Var" && t.i >= META;
  if (pc?.$ === "Eql" && meta(pc.a) && meta(pc.b)) return { sols, spec: 0 };
  for (const t of targets) push(pc, t);
  if (sols.length === 0 && targets.length) {
    const pn = nf(o.concl, LD(g));
    const ps = pn && (pick ? pick(pn) : pn);
    if (ps && H(ps) !== H(pc ?? pn)) for (const t of targets) push(ps, t);
  }
  return { sols, spec: pc ? size(pc) : 0 };
};
type Applied = { args: string[]; kids: Goal[]; sol: (Term | null)[] };
// c's parameters: fixed by sol, by a fact that fits a premise (raw or normal form), else a premise
// left as a subgoal; null when a parameter that is not a premise stays open
type Fill = { g: Goal; c: Callee; sol: (Term | null)[]; via: (string | null)[]; prem: boolean[]; o: { doms: Dom[]; concl: Term } };
const complete = (g: Goal, c: Callee, s0: (Term | null)[], refl: boolean): Applied | null => {
  const sol = s0.slice();
  const o = openMeta(c.T, c.n, solH(g, sol));
  if (!o) return null;
  const f: Fill = { g, c, sol, via: new Array(c.n).fill(null), prem: o.doms.map((dm, j) => !sol[j] && isPrem(dm.A, g.d)), o };
  if (!fitPremises(f) || (refl && !reflPremises(f)) || f.sol.some((s, j) => !s && !f.prem[j])) return null;
  return argsOf(f);
};
const solH = (g: Goal, s: (Term | null)[]) => s.map((x) => (x ? B.term_higher(x, g.env) : null));
// c reopened at the current solution (false: it no longer opens)
const reopen = (f: Fill): boolean => {
  const o = openMeta(f.c.T, f.c.n, solH(f.g, f.sol));
  if (o) f.o = o;
  return o !== null;
};
// premises that a fact fits (each fit may fix parameters that later premises name: up to 3 rounds)
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
        const s2 = f.sol.slice();
        if (!match(p, fa.T, s2, g.d) && !match(p, fa.N, s2, g.d)) return false;
        s2.forEach((x, i) => { f.sol[i] = x; });
        f.via[j] = fa.pf;
        return true;
      });
      // the premise as stated first; its normal form only when that fits no fact
      const An = fit(A) ? null : nf(dom.A, LD(g));
      if (f.via[j] || (An && H(An) !== H(A) && fit(An))) progress = true;
    }
    if (!progress) return true;
    if (!reopen(f)) return false;
  }
  return true;
};
// a rewrite's premise {a == x} with x open fixes x := a (the premise then holds by {==})
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
// the call's arguments: a value, a fact's proof, or HOLE for a premise left as a subgoal
const argsOf = (f: Fill): Applied | null => {
  const { g, c } = f;
  const args: string[] = [], kids: Goal[] = [];
  for (let j = 0; j < c.n; j++) {
    const s = f.sol[j], v = f.via[j];
    if (s || v) { args.push(s ? sh(g, s) : v!); continue; }
    const A = f.o.doms[j].A;
    if (attempt(FUEL_NF, () => hasMeta(lower(A, LD(g)))) !== false) return null;
    kids.push({ ...g, ty: A, qt: B.quant_dem(f.o.doms[j].q, g.qt), path: g.path + "#" + c.text + "." + j });
    args.push(HOLE);
  }
  return { args, kids, sol: f.sol };
};
const applyAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  const targets = targetsOf(n);
  if (!targets.length) return [];
  const callees = [...hypCallees(g), ...(g.split ? [ihCallee(g)] : []), ...lemmaCands(g, targets)];
  // an equation goal {a == b} also takes a callee that proves {b == a}, through Equal.sym
  const swapped = targets.filter((t) => t.$ === "Eql").map((t) => B.Eql(t.b, t.a, t.T));
  const found: { c: Callee; r: Applied; spec: number; sym: Term | null }[] = [];
  for (const c of [...callees, ...lemmaCands(g, swapped).filter((x) => !callees.some((y) => y.text === x.text))]) {
    if (late()) throw TIMEOUT;
    for (const [ts, sym] of [[targets, null], [swapped, swapped[0] ?? null]] as [Term[], Term | null][]) {
      if (!ts.length) continue;
      const { sols, spec } = conclSols(g, c, ts);
      for (const s of sols.slice(0, 2)) {
        const r = complete(g, c, s, false);
        if (r) found.push({ c, r, spec, sym });
      }
    }
    if (found.length >= 32) break;
  }
  // most specific conclusion first: a general lemma (le_weaken) matches every goal of its head
  found.sort((a, b) => (a.c.kind === "lemma" ? 1 : 0) - (b.c.kind === "lemma" ? 1 : 0) || b.spec - a.spec || (a.sym ? 1 : 0) - (b.sym ? 1 : 0));
  return found.map(({ c, r, sym }, i) => {
    const call = callText(c, r.args);
    const text = sym ? symText(g, sym, call) : call;
    const a = mkAlt(n, "apply:" + c.kind, text, 1 + i * 0.01 + r.kids.length * 0.1, (ps) => tm(text, ps));
    return withKids(a, r.kids, n.lv + 1, n.rws);
  });
};
// a constructor of a goal that is a datatype of facts (a pair, an Or): one subgoal per field
const ctorAlts = (n: GNode, w: Term): (Alt | null)[] => {
  const g = n.g;
  const adt = w.$ === "ADT" ? attempt(FUEL_NF, () => B.book_adt(BK.book, w, g.ctx, g.own.k)) : null;
  if (!adt || adt.c.length === 0 || adt.c.length > 4 || (adt.c.length === 1 && adt.c[0].n === 0) || !isProp(g.ty)) return [];
  return adt.c.map((ctr: Term) => attempt(FUEL_NF, () => {
    let cur = B.tele_fill(BK.book, ctr.T, w.x, g.ctx, g.own.k);
    const kids: Goal[] = [];
    for (let f = 0; f < ctr.n; f++) {
      const c = B.tele_head(BK.book, cur, g.ctx, g.own.k);
      const A = lower(c.A, g.d + f);
      // a field that names an earlier one is a witness, not a fact: no subgoal can give it
      if ([...varsOf(A, new Set())].some((v) => v >= g.d) || !isProp(c.A)) return null;
      kids.push({ ...g, ty: c.A, qt: c.q.$ === "None" ? B.None() : g.qt, path: g.path + "/" + shortOf(ctr.k) + "." + f });
      cur = c.B(B.Var("_", g.d + f));
    }
    const s = B.name_show(g.own.file, ctr.k) + "{" + kids.map(() => HOLE).join(", ") + "}";
    return withKids(mkAlt(n, "ctor", s, 1 + kids.length * 0.1, (ps) => tm(s, ps)), kids, n.lv + 1, n.rws);
  }) ?? null);
};

// rewrite: `%e : P; ?` with an equation from a fact, the induction hypothesis or a lemma whose side
// matches a subterm of the goal (in normal form, or as stated); P is the goal with that subterm `_`
type RwCand = { base: Term; from: Term; to: Term; e: string; kids: Goal[]; tag: string; score: number };
const RW_NODES = 2000; // a larger goal is not rewritten (each candidate prints its motive)
const rewriteAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  if (n.rws >= MAX_RW) return [];
  // the normal form, the one with deciding calls folded, and the goal as stated (later ones score lower)
  const bases: Term[] = [];
  for (const t of [nf(g.ty, LD(g)), nf(g.ty, LD(g), true), attempt(FUEL_NF, () => lower(g.ty, LD(g)))])
    if (t && size(t, RW_NODES) <= RW_NODES && !bases.some((x) => H(x) === H(t))) bases.push(t);
  const cands: RwCand[] = [];
  for (const [bi, base] of bases.entries()) rwCands(g, base, bi > 0, cands);
  cands.sort((a, b) => a.score - b.score);
  const out: (Alt | null)[] = [];
  const seen = new Set<number>();
  // every candidate at all its occurrences first, then (2 to 4 occurrences) each occurrence alone
  const counts = cands.map((c) => (contains(c.to, H(c.from)) ? 0 : occurrences(c.base, H(c.from)))); // x to f(x): a loop
  const sites = [
    ...cands.filter((_, i) => counts[i] > 0).map((c) => ({ c, at: -1 })),
    ...cands.flatMap((c, i) => (counts[i] > 1 && counts[i] <= 4 ? Array.from({ length: counts[i] }, (_, at) => ({ c, at })) : [])),
  ];
  for (const { c, at } of sites) {
    if (out.length >= 16) break;
    const fh = H(c.from);
    const Gp = replace(c.base, fh, c.to, at);
    if (seen.has(H(Gp))) continue;
    seen.add(H(Gp));
    const P = show(replace(c.base, fh, B.Var("_", g.d), at), [...g.names, "_"], g.own.file);
    const sub: Goal = { ...g, ty: B.term_higher(Gp, g.env), path: g.path + "%" };
    const e = c.e;
    const build = (ps: Pf[]): Pf => ({ t: "rw", e: tm(e, ps.slice(1)), P, k: ps[0] });
    const a = mkAlt(n, c.tag, "%" + e + " : " + P + "; " + HOLE, 1.5 + c.score * 0.1 + c.kids.length * 0.1, build, "%" + e.replace(/\u0000/g, "?") + " : " + clip(P, 160));
    out.push(withKids(a, [sub, ...c.kids], n.lv + 1, n.rws + 1));
  }
  return out;
};
type RwSite = { base: Term; subs: Map<number, Term>; score: (from: Term, base: number) => number };
const rwCands = (g: Goal, N: Term, isRaw: boolean, cands: RwCand[]) => {
  const subs = new Map<number, Term>();
  subterms(N, subs);
  const blk: Term[] = [];
  blockers(N, blk);
  const blkKeys = new Set(blk.map(H));
  const site: RwSite = { base: N, subs, score: (from, base) => base + (blkKeys.has(H(from)) ? 0 : 1) + (isRaw ? 0.2 : 0) };
  factRws(g, site, cands);
  calleeRws(g, site, cands);
};
// facts: occurrences of an equation's right side become its left side (the motive's `_` there)
const factRws = (g: Goal, site: RwSite, cands: RwCand[]) => {
  for (const f of factsOf(g)) {
    if (!usable(f, g.qt)) continue;
    for (const E of f.N && f.N !== f.T ? [f.T, f.N] : [f.T]) {
      if (E?.$ !== "Eql" || H(E.a) === H(E.b) || !site.subs.has(H(E.b)) || !/^(Var|App|Ctr|Lit)$/.test(E.b.$)) continue;
      cands.push({ base: site.base, from: E.b, to: E.a, e: f.pf, kids: [], tag: "rw:fact", score: site.score(E.b, 0) });
    }
  }
};
// the induction hypothesis and lemmas whose equation side matches a stuck call of the base
const calleeRws = (g: Goal, site: RwSite, cands: RwCand[]) => {
  const ih = g.split ? ihCallee(g) : null;
  const ihEq = ih && attempt(FUEL_NF, () => { const o = openMeta(ih.T, ih.n); return o ? lower(o.concl, LD(g)) : null; });
  for (const s of site.subs.values()) {
    const hk = headKey(s);
    if (!hk.startsWith("R:") && !(s.$ !== "App" && BK.rw.has(hk))) continue;
    const entries: { c: Callee; side: 0 | 1; tag: string }[] = [];
    if (ih && ihEq?.$ === "Eql" && hk.startsWith("R:")) for (const side of [0, 1] as const) if (headKey(side === 0 ? ihEq.a : ihEq.b) === hk) entries.push({ c: ih, side, tag: "rw:ih" });
    for (const { L, side } of BK.rw.get(hk) ?? []) {
      if (L.order < g.own.order && L.k !== g.own.k && entries.length <= 24) entries.push({ c: lemmaCallee(g, L), side, tag: "rw:lemma" });
    }
    for (const en of entries) {
      if (late()) throw TIMEOUT;
      calleeRw(g, site, s, en, cands);
    }
  }
};
const calleeRw = (g: Goal, site: RwSite, s: Term, { c, side, tag: t }: { c: Callee; side: 0 | 1; tag: string }, cands: RwCand[]) => {
  const { sols } = conclSols(g, c, [s], (o) => (o.$ === "Eql" ? (side === 0 ? o.a : o.b) : null));
  for (const s0 of sols.slice(0, 2)) {
    const r = complete(g, c, s0, true);
    const o2 = r && openMeta(c.T, c.n, r.sol.map((x) => (x ? B.term_higher(x, g.env) : null)));
    const E = o2 && attempt(FUEL_NF, () => lower(o2.concl, LD(g)));
    if (!r || E?.$ !== "Eql" || hasMeta(E)) continue;
    const to = side === 0 ? E.b : E.a;
    if (H(to) === H(s)) continue;
    const call = callText(c, r.args);
    cands.push({ base: site.base, from: s, to, e: side === 0 ? symText(g, E, call) : call, kids: r.kids, tag: t, score: site.score(s, c.n === 0 ? -0.5 : t === "rw:ih" ? 0 : 0.5) });
  }
};

// lift: the goal as a helper def over its context (true iff the goal is), so that its parameters can
// be split (bend2 matches only a def's own parameters). With a stuck call t generalized: a parameter
// x, an equation hx: {x == t}, and t replaced by x in the goal and in the facts that name it (they
// move after x); splitting x then decides the call (the decide pattern, a generalized fuel).
const MAX_LEVEL = 2, MAX_HELPERS = 12;
const liftAlts = (n: GNode): (Alt | null)[] => {
  const g = n.g;
  if (g.own.level >= MAX_LEVEL || g.d === 0 || n.lv > 2) return [];
  const names = g.names;
  if (new Set(names).size !== names.length || names.some((x) => x === "_" || x === "" || !/^[A-Za-z_]\w*$/.test(x))) return [];
  const blk: Term[] = [];
  targetsOf(n);
  if (n.A) blockers(n.A, blk);
  for (const f of factsOf(g)) {
    if (f.i < 0) continue;
    f.A ??= nf(ann(g, f.i).T, LD(g), true, 20000) ?? f.N;
    if (f.A) blockers(f.A, blk);
  }
  const out: (Alt | null)[] = [];
  // a plain lift right under a node only repeats the node's own splits
  const underNode = n.up?.tag === "intro" && n.up.up.g.pend > 0;
  if (!underNode && blk.some((t) => t.$ === "Var" && t.i < g.d)) out.push(liftAlt(n, null));
  const seen = new Set<number>();
  // the deciding calls (atoms) first, innermost first
  const rank = new Map(blk.map((t) => [t, (t.$ === "App" && isAtom(B.term_higher(t, g.env), g.d) ? 0 : 1e6) + size(t, 1e5)]));
  blk.sort((x, y) => rank.get(x)! - rank.get(y)!);
  for (const t of blk) {
    if (out.length >= 3) break;
    if (t.$ !== "App" || seen.has(H(t)) || !closedBelow(t, g.d)) continue;
    seen.add(H(t));
    const T = attempt(FUEL_NF, () => B.term_infer(BK.book, g.lhs, B.term_higher(t, g.env), B.None(), g.ctx, g.d).ty);
    const w = T && wnf(T);
    const adt = w?.$ === "ADT" ? BK.raw[w.k] : null;
    if (adt?.$ !== "ADT" || adt.c.length < 2 || adt.c.length > 8) continue;
    out.push(liftAlt(n, { t, T: lower(T, LD(g)) }));
  }
  return out;
};
const liftAlt = (n: GNode, gen: { t: Term; T: Term } | null): Alt | null => {
  const g = n.g;
  const note = gen ? "a helper over the context, " + sh(g, gen.t) + " generalized" : "a helper over the context (its parameters can be split)";
  const a = mkAlt(n, gen ? "lift:gen" : "lift", null, gen ? 3.5 : 3, (ps) => ps[0], note);
  a.open = () => {
    if (S.helpers >= MAX_HELPERS) return null;
    const used = new Set(g.names);
    const x = gen ? fresh(g, "x", used) : "", hx = gen ? fresh(g, "h" + x, used) : "";
    const names = [...g.names, x]; // every type is lowered at LD(g), where level g.d is x
    const th = gen ? H(gen.t) : 0;
    const xv = B.Var(x, g.d);
    // a type with t replaced by x (raw if it names t, else its normal form if that does)
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
      const A = ann(g, i);
      const r = gen1(A.T);
      if (!r) return null;
      const p = B.quant_show(A.q) + names[i] + ": " + r.s;
      if (r.moved) { movedIdx.add(i); later.push(p); argsLater.push(names[i]); }
      else { first.push(p); argsFirst.push(names[i]); }
    }
    const goal = gen1(g.ty);
    if (!goal || (gen && !goal.moved && movedIdx.size === 0)) return null;
    let params = first, args = argsFirst, pre = "";
    if (gen) {
      // the parameters before x must not name a moved one; x's type must name no moved one
      for (let i = 0; i < g.d; i++) if (!movedIdx.has(i) && [...varsOf(lower(ann(g, i).T, i), new Set())].some((v) => movedIdx.has(v))) return null;
      if ([...varsOf(gen.t, new Set()), ...varsOf(gen.T, new Set())].some((v) => movedIdx.has(v))) return null;
      const ts = sh(g, gen.t), Ts = sh(g, gen.T);
      params = [...first, (isData(g, B.term_higher(gen.T, g.env)) ? "+" : "") + x + ": " + Ts, hx + ": {" + x + " == " + ts + " : " + Ts + "}", ...later];
      args = [...argsFirst, ts, "{==}", ...argsLater];
      // a variable that t names and that is also an argument is used twice: rebind it reusable
      const twice = [...varsOf(gen.t, new Set())].filter((v) => ann(g, v)?.q.$ === "Lone").map((v) => g.names[v]);
      pre = twice.map((v) => "+" + v + " = " + v + "; ").join("");
    }
    const name = helperName(g.own);
    const head = "def " + name + "(\n  " + params.join(",\n  ") + ") ->\n  " + goal.s + ":";
    const hk = addTemp(head, g.own);
    if (!hk) return null;
    const call = name + "(" + args.join(", ") + ")";
    if (stmtErr(hk) || !tryText(g, pre + call)) return null;
    S.helpers++;
    a.build = (ps) => ({ t: "def", name, head, body: ps[0], call: pre + call });
    const kid = mkNode(rootGoal(owner(hk, g.own.level + 1, g.own.root)), a, 0, 0);
    return kid ? [kid] : null;
  };
  return a;
};
// helpers live in the book while the task runs (parsed as `?TODO` bodies; not lemmas)
const temps: string[] = [];
const helperName = (own: Owner): string => {
  const taken = new Set(Object.keys(BK.raw).map(shortOf));
  for (let i = 1; ; i++) {
    const nm = own.root + ".g" + i;
    if (!taken.has(nm) && !fileText(BK.entry).includes("def " + nm + "(")) return nm;
  }
};
const addTemp = (head: string, own: Owner): string | null => {
  const n0 = BK.book.order.length;
  try { B.parse_book(BK.book, BK.top, head + "\n  ?TODO\n", own.file.ns, own.file.al); } catch { BK.book.order.length = n0; return null; }
  const hk = BK.book.order[n0];
  if (!hk || BK.raw[hk]?.$ !== "Def") { for (const k of BK.book.order.slice(n0)) delete BK.raw[k]; BK.book.order.length = n0; return null; }
  temps.push(hk);
  BK.order.set(hk, own.order - 0.5 + temps.length * 1e-6);
  BK.files.set(hk, own.file);
  BK.src.set(hk, { file: BK.entry, header: head, body: "  ?TODO", bodyLine: 0 });
  return hk;
};
// what the book's memos derived from def k (its body may have been forgotten while a search ran)
const forget = (k: string) => {
  BK.strict.delete(k); BK.matched.delete(k); BK.enums.delete(k);
  if (BK.wraps && [...BK.wraps.values()].some((ws) => ws.some((w) => w.k === k))) BK.wraps = null;
};
const dropTemps = () => {
  for (const hk of temps) {
    delete BK.raw[hk];
    const j = BK.book.order.indexOf(hk);
    if (j >= 0) BK.book.order.splice(j, 1);
    BK.order.delete(hk); BK.files.delete(hk); BK.src.delete(hk);
    forget(hk);
  }
  temps.length = 0;
};

// ---- bend2's errors, bounded ----
// bend2's err_show prints every type in strong normal form (unbounded: stack overflows and gigabytes
// of output on machine states); errText prints the same Err within node budgets: expected and
// observed, where they differ (both sides in weak normal form, same-shaped parts entered), the context
const ERR_NODES = 400, CTX_CHARS = 400;
const showCut = (t: Term, d: number, names: string[], file: Term, nodes = ERR_NODES): string => {
  try { return B.term_show(lowerB(t, d, { n: nodes }, true), -1, names.slice(), file); } catch (e) { return "<not printable: " + String((e as Error)?.message ?? e).slice(0, 80) + ">"; }
};
const diffs = (a0: Term, b0: Term, d: number, names: string[], at: string[], out: { at: string[]; a: Term; b: Term; d: number; names: string[] }[], top = false) => {
  if (out.length >= 4 || at.length > 200) return;
  if (!top && attempt(FUEL_NF, () => B.term_compare("EQ", BK.book, a0, b0, d)) === true) return;
  let a = wnf(a0) ?? B.term_strip(a0), b = wnf(b0) ?? B.term_strip(b0);
  if (a.$ === "Lit" && b.$ === "Ctr") a = B.lit_step(a);
  if (b.$ === "Lit" && a.$ === "Ctr") b = B.lit_step(b);
  const n0 = out.length;
  const sub = (x: Term, y: Term, s: string, dd = d, nn = names) => diffs(x, y, dd, nn, [...at, s], out);
  if (a.$ === "Ctr" && b.$ === "Ctr" && a.k === b.k && a.x.length === b.x.length) a.x.forEach((x: Term, i: number) => sub(x, b.x[i], shortOf(a.k) + "{.." + (i + 1) + "}"));
  else if (a.$ === "ADT" && b.$ === "ADT" && a.k === b.k && a.x.length === b.x.length) a.x.forEach((x: Term, i: number) => sub(x, b.x[i], shortOf(a.k) + "<.." + (i + 1) + ">"));
  else if (a.$ === "Eql" && b.$ === "Eql") { sub(a.a, b.a, "left of =="); sub(a.b, b.b, "right of =="); sub(a.T, b.T, "type of =="); }
  else if (a.$ === "All" && b.$ === "All" && a.q.$ === b.q.$) { const x = B.Var(a.k, d); sub(a.A, b.A, "type of " + a.k); sub(a.B(x), b.B(x), "after " + a.k, d + 1, [...names, a.k]); }
  else if (a.$ === "App" && b.$ === "App") {
    const [fa, xa] = B.term_unapply(a), [fb, xb] = B.term_unapply(b);
    const ha = B.term_strip(fa), hb = B.term_strip(fb);
    if (ha.$ === "Ref" && hb.$ === "Ref" && ha.k === hb.k && xa.length === xb.length) xa.forEach((x, i) => sub(x, xb[i], shortOf(ha.k) + "(.." + (i + 1) + ")"));
  }
  if (out.length === n0) out.push({ at, a, b, d, names });
};
const errLocation = (err: Term, base: number): string => {
  const def = err.def === undefined ? "" : " " + B.name_show(err.spn?.file, err.def);
  if (err.spn === undefined) return def === "" ? "" : "\nLocation:" + def;
  const lns = err.spn.file.str.split("\n");
  const at = lineOf(err.spn.file.str, err.spn.beg);
  return "\nLocation:" + def + (err.spn.file.ns && base === 0 ? " (in " + err.spn.file.ns + ".bend)" : "") + "\n"
    + lns.slice(Math.max(0, at - 2), Math.min(lns.length, at + 1)).map((l: string, j: number) => {
      const i = Math.max(0, at - 2) + j + 1;
      return String(base + i).padStart(5) + (i === at ? ">| " : " | ") + clip(l, 300);
    }).join("\n");
};
// base: the file line of the checked text's first line (0: the text is the file)
const errText = (e: Term, base = 0): string => {
  if (e instanceof Stop) return "not decided: out of " + (e === TIMEOUT ? "time" : e.why);
  if (e?.$ !== "Err") return String(e?.stack ?? e?.message ?? e).slice(0, 1500);
  const file = e.spn?.file;
  const names: string[] = B.ctx_scope(e.ctx);
  const d = names.length;
  const old = fuel;
  fuel = FUEL_FINAL;
  try {
    const out: string[] = ["Error:"];
    if (e.obs === undefined || typeof e.exp === "string" || typeof e.obs === "string" || e.obs.$ === "Hol") {
      const ex = (x: Term) => (typeof x === "string" ? x : showCut(x, d, names, file));
      out.push(e.obs === undefined ? "- message  : " + ex(e.exp) : typeof e.obs !== "string" && e.obs.$ === "Hol" ? "- goal of ?" + e.obs.k + " : " + ex(e.exp) : "- expected : " + ex(e.exp) + "\n- observed : " + ex(e.obs));
    } else {
      out.push("- expected : " + clip(showCut(e.exp, d, names, file), 1200), "- observed : " + clip(showCut(e.obs, d, names, file), 1200));
      const ds: { at: string[]; a: Term; b: Term; d: number; names: string[] }[] = [];
      diffs(e.exp, e.obs, d, names, [], ds, true);
      if (ds.length !== 1 || ds[0].at.length > 0) {
        out.push("- where they differ (each side in weak normal form):");
        ds.forEach((x, i) => out.push("  " + (i + 1) + ". at " + (x.at.join(" > ") || "(the whole type)") + "\n     expected : " + clip(showCut(x.a, x.d, x.names, file), 800) + "\n     observed : " + clip(showCut(x.b, x.d, x.names, file), 800)));
      }
    }
    const anns = B.pmap_to_array(e.ctx).sort((x: Term, y: Term) => x[0] - y[0]);
    if (anns.length) out.push("Context (types as stated; a type over " + CTX_CHARS + " chars is cut):");
    for (const [i, a] of anns) out.push("- " + a.k + " : " + clip(showCut(a.T, i, names.slice(0, i), file, 2000), CTX_CHARS));
    return out.join("\n") + errLocation(e, base) + (e.nte ? "\n" + e.nte : "");
  } catch (x) {
    return "Error: " + (typeof e.exp === "string" ? e.exp : "(gen3 could not print it: " + String((x as Error)?.message ?? x).slice(0, 100) + ")") + errLocation(e, base);
  } finally { fuel = old; }
};
const firstLine = (e: Term) => errText(e).split("\n").slice(0, 3).join(" ").slice(0, 300);

// ---- answers ----
const goalLines = (g0: Goal): string => {
  const g = g0.pend > 0 ? introAll(g0) ?? g0 : g0; // a def's root: its parameters introduced
  const ctx: string[] = [];
  for (let i = 0; i < g.d; i++) {
    const a = ann(g, i);
    ctx.push("#   " + B.quant_show(a.q) + g.names[i] + " : " + clip(attempt(FUEL_NF, () => show(lower(a.T, i), g.names.slice(0, i), g.own.file)) ?? "?", CTX_CHARS));
  }
  return "# goal: " + clip(attempt(FUEL_NF, () => sh(g, lower(g.ty, LD(g)))) ?? "?", 2000) + (ctx.length ? "\n# context:\n" + ctx.join("\n") : "");
};
// what the search tried at an open goal: its live steps, closest first
const triedLines = (n: GNode, max = 4): string => {
  const as = (n.alts ?? []).filter((a) => !a.dead && a.tag !== "intro").sort((a, b) => a.pn - b.pn).slice(0, max);
  return as.length ? "\n# tried (closest first; open subgoals in parentheses):\n" + as.map((a) => "#   " + clip(a.note, 240) + (a.kids.length ? " (" + a.kids.filter((k) => !k.pf).length + " open)" : "")).join("\n") : "\n# tried: no step applies (no lemma, fact or rewrite fits; it may need a new lemma or a split)";
};
const tagsOf = () => [...S.tags.entries()].sort((a, b) => b[1] - a[1]).map(([t]) => t).join(" ");
const secs = (ms: number) => (ms / 1000).toFixed(1) + " s";
type Helper = Extract<Pf, { t: "def" }>;
const defsText = (hs: Helper[]) => hs.map((h) => h.head + "\n" + bodyText(h.body) + "\n").join("\n");
const helperBlock = (hs: Helper[], k: string, proven: boolean): string =>
  hs.length ? "# helper defs (" + (proven ? "proven" : "some open") + "): paste them above `def " + shortOf(k) + "(`\n" + defsText(hs) + "# the body of " + shortOf(k) + ":\n" : "";
// --write: the def's text replaced by its helpers and its new body
const editOf = (ds: Src, hs: Helper[], body: string): Edit => ({ t: "edit", file: ds.file, from: ds.header + "\n" + ds.body, to: (hs.length ? defsText(hs) + "\n" : "") + ds.header + "\n" + body });
// a proof's helpers and body through bend2's def check once more (what prints is what checks); a
// partial's check gets less fuel (it only annotates a guess)
const FUEL_PARTIAL = 5000000;
const finalErr = (k: string, pf: Pf, body: string, cap = FUEL_FINAL): Term => {
  for (const h of helpersOf(pf)) {
    const hk = temps.find((t) => shortOf(t) === h.name);
    const e = hk ? checkErr(hk, bodyText(h.body), h.head, cap) : "the helper " + h.name + " is gone";
    if (e) return e;
  }
  return checkErr(k, body, undefined, cap);
};
type Result = { ok: boolean; text: string; edit?: Edit };
// the answer of a search, printed and checked before the hard deadline (a check out of time is "not
// decided"; printing out of time gives the fallback)
const settle = (hard: number, f: () => Result, fallback: () => string): Result => {
  deadline = hard;
  try { return f(); } catch (e) { if (e === TIMEOUT) return { ok: false, text: fallback() }; throw e; } finally { deadline = Infinity; }
};
// the ?TODO holes of a body (offsets), not those in comments
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
// each hole's goal, read from bend2's error at that hole marked
const holeGoals = (k: string, ds: Src, own: Owner): { at: number; g: Goal | null; err: Term }[] =>
  todoAt(ds.body).slice(0, MAX_HOLES).map((p, i) => {
    const err = checkErr(k, ds.body.slice(0, p) + "?gen3hole" + ds.body.slice(p + 5));
    return { at: p, g: holeGoal(own, err, "hole" + (i + 1)), err };
  });

// a whole body: the search from the def's root goal (its body forgotten while it runs)
const proveWhole = async (k: string, ds: Src, until: number, hard: number, progress: (s: string) => void): Promise<Result> => {
  const t0 = performance.now(), def = BK.raw[k], name = shortOf(k);
  BK.raw[k] = { ...def, v: null };
  try {
    const root = mkNode(rootGoal(owner(k)), null, 0, 0)!;
    newSearch(root);
    await run(until, () => {
      const p = partial(root);
      progress("# " + name + ": searching (" + secs(performance.now() - t0) + ", " + S.nodes + " goals): best partial " + p.holes + " holes, " + p.closed + " steps closed");
    });
    const ms = performance.now() - t0;
    const head = "# " + name + ": OPEN after " + secs(ms) + " (" + S.nodes + " goals searched" + (overMem ? ", stopped at the worker's memory share" : "") + (S.internal ? ", " + S.internal + " internal errors" : "") + ")";
    return settle(hard, () => (root.pf ? provenText(k, ds, root.pf, ms) : openText(k, root, head)), () => head + "; out of time while printing the answer");
  } finally {
    BK.raw[k] = def;
    forget(k);
    dropTemps();
  }
};
const provenText = (k: string, ds: Src, pf: Pf, ms: number): Result => {
  const name = shortOf(k), body = bodyText(pf), hs = helpersOf(pf);
  const e = finalErr(k, pf, body);
  if (e instanceof Stop) return { ok: false, text: "# " + name + ": a proof was found, but gen3's re-check did not finish (" + errText(e) + "): unverified\n" + helperBlock(hs, k, true) + body };
  if (e) return { ok: false, text: "# " + name + ": a proof was found but fails bend2's def check (a gen3 bug; please report it):\n" + body + "\n" + errText(e) };
  return { ok: true, text: "# " + name + ": PROVEN in " + Math.round(ms) + " ms [" + tagsOf() + "]\n" + helperBlock(hs, k, true) + body, edit: editOf(ds, hs, body) };
};
const openText = (k: string, root: GNode, head: string): Result => {
  const p = partial(root);
  if (p.closed === 0 || p.holes === 0) {
    const leaf = root.alts?.[0]?.kids[0];
    return { ok: false, text: head + "; no step closed\n" + (leaf ? goalLines(leaf.g) + triedLines(leaf) : goalLines(root.g)) };
  }
  const body = bodyText(p.pf);
  const e = finalErr(k, p.pf, body, FUEL_PARTIAL);
  const note = e instanceof Stop ? "; not checked (" + errText(e) + ")" : e ? "; it does NOT check in gen3: " + firstLine(e) : "";
  return {
    ok: false,
    text: head + ": a partial proof (" + p.holes + " holes, " + p.closed + " steps closed). A guess at a structure, not a proof" + note + "\n"
      + helperBlock(helpersOf(p.pf), k, false) + body + "\n" + holesOf(p.pf).map((h, i) => "# hole " + (i + 1) + " at " + (h.g.path || "/") + " (in " + h.g.own.short + ")\n" + goalLines(h.g) + triedLines(h)).join("\n"),
  };
};
// the ?TODO holes of a body: one search over all of them (a root whose one step needs every hole)
const MAX_HOLES = 16;
const proveHoles = async (k: string, ds: Src, until: number, hard: number, progress: (s: string) => void): Promise<Result> => {
  const t0 = performance.now(), name = shortOf(k), own = owner(k);
  const root: GNode = { g: rootGoal(own), key: -1, up: null, alts: null, pn: 1, dn: 1, pf: null, lv: 0, rws: 0 };
  newSearch(root);
  const all = mkAlt(root, "holes", null, 0, () => tm(""));
  root.alts = [all];
  const notes: string[] = [];
  const holes = holeGoals(k, ds, own).map((h, i) => {
    if (!h.g) notes.push("# hole " + (i + 1) + ": no goal (bend2 stops before it): " + (h.err ? firstLine(h.err) : "the body checks"));
    const n = h.g && mkNode(h.g, all, 0, 0);
    if (n) all.kids.push(n);
    return { at: h.at, n };
  });
  try {
    calcAlt(all);
    calcNode(root);
    await run(until, () => progress("# " + name + ": searching (" + secs(performance.now() - t0) + "): " + holes.filter((h) => h.n?.pf).length + "/" + holes.length + " holes closed"));
    return settle(hard, () => {
      // fill from the last hole back (the earlier offsets stay valid); a fill stays only if the body
      // checks with it (the other ?TODO holes check at any goal)
      let body = ds.body;
      const used: Pf[] = [];
      for (const [i, h] of [...holes.entries()].reverse()) {
        const pf = h.n?.pf;
        if (!pf) continue;
        const line = body.slice(body.lastIndexOf("\n", h.at) + 1, h.at);
        const out: string[] = [];
        if (/^\s*$/.test(line)) render(pf, line, out);
        const nb = body.slice(0, h.at) + (out.length ? out.join("\n").slice(line.length) : inline(pf)) + body.slice(h.at + 5);
        const e = finalErr(k, pf, nb);
        if (!e) { body = nb; used.push(pf); }
        else notes.push("# hole " + (i + 1) + ": a fill was found but " + (e instanceof Stop ? "its re-check did not finish: " + inline(pf) : "fails the def check (a gen3 bug): " + inline(pf)));
      }
      const hs = used.flatMap((p) => helpersOf(p));
      const open = holes.map((h, i) => (h.n && !h.n.pf ? "# hole " + (i + 1) + " (open)\n" + goalLines(h.n.g) + triedLines(h.n) : "")).filter(Boolean);
      const ok = used.length === holes.length && todoAt(body).length === 0;
      const text = "# " + name + ": " + used.length + "/" + holes.length + " holes filled in " + secs(performance.now() - t0) + (S.tags.size ? " [" + tagsOf() + "]" : "") + "\n"
        + helperBlock(hs, k, true) + body + (notes.length || open.length ? "\n" + [...notes, ...open].join("\n") : "");
      return { ok, text, edit: ok ? editOf(ds, hs, body) : undefined };
    }, () => "# " + name + ": out of time while filling the holes");
  } finally {
    dropTemps();
  }
};
const proveOne = async (k: string, until: number, hard: number, progress: (s: string) => void): Promise<Result> => {
  const ds = defSrc(k);
  const name = shortOf(k);
  if (!ds) return { ok: false, text: "# " + name + ": gen3 cannot find its source text" };
  const se = nsOf(k) === "" ? stmtErr(k) : null;
  if (se) return { ok: false, text: "# " + name + ": STATEMENT ERROR (its type does not check; fix it first):\n" + errText(se) };
  if (ds.body.trim() === "?TODO") return proveWhole(k, ds, until, hard, progress);
  if (todoAt(ds.body).length) return proveHoles(k, ds, until, hard, progress);
  return { ok: true, text: "# " + name + ": no ?TODO in its body (nothing to prove; `check` checks it)" };
};

// ---- commands (in a worker) ----
type Send = (m: Msg) => void;
type Snap = (s: string, code: number, edits?: Edit[]) => void;
const defsOf = (a: Args): { ks: string[]; bad: string[] } => {
  const ks: string[] = [], bad: string[] = [];
  for (const nm of a.pos.slice(1)) {
    const r = resolveDef(nm);
    if (typeof r === "string") ks.push(r);
    else bad.push("# " + nm + ": " + (r.length ? "ambiguous: " + r.join(", ") : "no def of that name in " + path.basename(BK.entry)));
  }
  return { ks, bad };
};
const proveCmd = async (a: Args, until: number, hard: number, snap: Snap) => {
  const { ks, bad } = defsOf(a);
  if (ks.length === 0) return snap(HONEST + "\n" + (bad.join("\n") || "# name a def to prove: " + USAGE), 1);
  const parts = ks.map((k) => "# " + shortOf(k) + ": searching");
  const edits: Edit[] = [];
  let code = bad.length ? 1 : 0;
  const publish = (c: number) => snap(HONEST + "\n" + [...bad, ...parts].join("\n\n"), c, edits);
  publish(3);
  for (const [i, k] of ks.entries()) {
    const left = ks.length - i, now = performance.now();
    const r = await proveOne(k, now + (until - now) / left, now + (hard - now) / left, (s) => { parts[i] = s; publish(3); });
    parts[i] = r.text;
    if (!r.ok) code = Math.max(code, 2);
    if (r.edit) edits.push(r.edit);
    publish(i === ks.length - 1 ? code : 3);
  }
};
const goalsCmd = (a: Args, snap: Snap) => {
  const { ks, bad } = defsOf(a);
  const out = [HONEST, ...bad];
  for (const k of ks) {
    const own = owner(k), ds = defSrc(k);
    if (!ds) continue;
    const gs = ds.body.trim() === "?TODO"
      ? [{ label: "the goal of " + own.short, g: introAll(rootGoal(own)) }]
      : holeGoals(k, ds, own).map((h, i) => ({ label: "?TODO " + (i + 1) + " of " + own.short + " (line " + (ds.bodyLine + lineOf(ds.body, h.at)) + ")", g: h.g }));
    if (gs.length === 0) out.push("# " + own.short + ": no ?TODO in its body");
    for (const { label, g } of gs) {
      if (!g) { out.push("# " + label + ": no goal (bend2 stops before it; run `check`)"); continue; }
      const n = mkNode(g, null, 0, 0)!;
      newSearch(n);
      deadline = performance.now() + 3000;
      try { n.alts = leafAlts(n); } catch (e) { if (e !== TIMEOUT) throw e; n.alts ??= []; } finally { deadline = Infinity; dropTemps(); }
      const nfa = n.A ?? nf(g.ty, LD(g), true);
      const nfText = nfa ? "\n# goal in normal form (deciding calls folded): " + clip(sh(g, nfa), 2000) : "";
      out.push("# " + label + "\n" + goalLines(g) + nfText + (n.pf ? "\n# closes by: " + inline(n.pf) : triedLines(n, 12)));
    }
  }
  snap(out.join("\n"), bad.length ? 1 : 0);
};
const checkCmd = (a: Args, snap: Snap) => {
  const { ks, bad } = a.pos.length > 1 ? defsOf(a) : { ks: ownDefs(), bad: [] };
  const out = [HONEST, ...bad];
  let errs = 0, todo = 0;
  const t0 = performance.now();
  for (const k of ks) {
    const ds = defSrc(k);
    if (!ds) continue;
    todo += todoAt(ds.body).length;
    const se = nsOf(k) === "" ? stmtErr(k) : null;
    const e = se ?? checkErr(k, ds.body);
    if (e) { errs++; out.push("# ERROR in " + shortOf(k) + (se ? " (its statement)" : "") + ":\n" + errText(e, se ? 0 : ds.bodyLine - ds.header.split("\n").length)); }
  }
  out.push("# check " + path.basename(BK.entry) + ": " + ks.length + " defs, " + errs + " with errors, " + todo + " ?TODO (" + Math.round(performance.now() - t0) + " ms; bend2's checker in gen3; `bend --check-only` is the judge)");
  snap(out.join("\n"), errs || bad.length ? 2 : 0);
};
const findCmd = (a: Args, snap: Snap) => {
  let re: RegExp;
  try { re = new RegExp(a.pos[1] ?? ""); } catch { return snap(HONEST + "\n# find: not a regular expression: " + a.pos[1], 1); }
  const file = BK.files.get(ownDefs()[0] ?? "") ?? { ns: "", al: {} };
  const hits = [...new Set<string>(BK.book.order)].filter((k) => !k.includes("~") && BK.raw[k] && (re.test(B.name_show(file, k)) || re.test(k)));
  const rank = (k: string) => ((BK.order.get(k) ?? 0) >= BK.n0 ? 0 : BK.raw[k].b ? 2 : 1);
  hits.sort((x, y) => rank(x) - rank(y) || (BK.order.get(y) ?? 0) - (BK.order.get(x) ?? 0));
  const status = (k: string) => { const t = BK.raw[k]; return t.$ === "ADT" ? "type" : t.v === null ? (t.b ? "Base" : "law: no proof") : isOpen(k) ? "OPEN: has ?TODO" : t.b ? "Base" : "has a body"; };
  const rows = hits.slice(0, 40).map((k) => B.name_show(file, k) + "  [" + status(k) + "]\n  : " + clip(attempt(FUEL_NF, () => show(lower(BK.raw[k].T, 0), [], file)) ?? "?", 1500));
  snap(HONEST + "\n# find " + a.pos[1] + ": " + hits.length + " defs" + (hits.length > 40 ? " (the first 40)" : "") + "\n" + rows.join("\n"), 0);
};
const isLemma = (k: string): boolean => {
  const t = BK.raw[k];
  if (t?.$ !== "Def" || t.v === null || t.x > 0 || t.i || isOpen(k)) return false;
  const o = attempt(20000, () => openMeta(t.T, t.n));
  return !!o && attempt(20000, () => isPropType(o.concl)) === true && !!defSrc(k);
};

const runTask = async (t: Task, send: Send) => {
  const snap: Snap = (s, code, edits) => send({ id: t.id, t: "snap", s, code, edits });
  const L = await load(taskEntry(t));
  if (typeof L === "string") {
    if (t.t === "reprove") send({ id: t.id, t: "row", s: "ERR  " + t.def + ": " + L.split("\n")[0], ok: false, ms: 0 });
    return snap(HONEST + "\n# " + L, 1);
  }
  BK = L;
  send({ id: t.id, t: "files", files: L.seen });
  // the search gets 85% of the time left; the rest prints and checks the answer (hard: 0.5 s spare)
  const left = t.deadline - Date.now(), now = performance.now();
  const until = now + 0.85 * left, hard = now + left - 500;
  if (t.t === "lemmas") {
    const only = new RegExp(t.only);
    return send({ id: t.id, t: "lemmas", names: ownDefs().filter((k) => only.test(shortOf(k)) && isLemma(k)) });
  }
  if (t.t === "reprove") {
    const ds = defSrc(t.def)!;
    const r = await proveWhole(t.def, { ...ds, body: "  ?TODO" }, now + t.budget, hard, () => {});
    const ms = Math.round(performance.now() - now);
    return send({ id: t.id, t: "row", s: (r.ok ? "OK " : "-- ") + String(ms).padStart(6) + " ms  " + shortOf(t.def) + (r.ok ? "  [" + tagsOf() + "]" : ""), ok: r.ok, ms });
  }
  switch (t.args.cmd) {
    case "prove": return proveCmd(t.args, until, hard, snap);
    case "goals": return goalsCmd(t.args, snap);
    case "check": return checkCmd(t.args, snap);
    case "find": return findCmd(t.args, snap);
  }
};
// one task at a time (the server sends one per worker); the task's end goes out before the worker
// exits over its memory share (the server then starts a fresh one)
const onTask = async (t: Task, send: Send) => {
  try {
    await runTask(t, send);
  } catch (e) {
    let why = "";
    try { why = e instanceof Stop ? e.why : errText(e); } catch { why = String(e).slice(0, 300); }
    send({ id: t.id, t: "snap", s: HONEST + "\n# gen3: internal error (please report it): " + why, code: 1 });
  } finally {
    fuel = Infinity; deadline = Infinity;
    send({ id: t.id, t: "end" });
    if (overMem || process.memoryUsage.rss() > MEM_CAP * 0.7) { books.clear(); smemo.clear(); Bun.gc(true); }
    overMem = false;
    if (process.memoryUsage.rss() > MEM_CAP || process.env.GEN3_PROF) setTimeout(() => process.exit(0), 100);
  }
};
const worker = async () => {
  const send: Send = (m) => process.send!(m);
  try {
    B = await import(bendFile());
  } catch (e) {
    console.error("[gen3 worker] cannot load bend2: " + String(e));
    process.exit(1);
  }
  // the server is gone (stopped, killed, replaced): so is this worker
  process.on("disconnect", () => process.exit(0));
  const parent = process.ppid;
  setInterval(() => { try { process.kill(parent, 0); } catch { process.exit(0); } }, 2000).unref();
  process.on("message", (t: Task) => void onTask(t, send));
};

// ---- main ----
const main = async () => {
  const a = parseArgs(process.argv.slice(2));
  if (a.cmd === "serve") return await serve();
  if (a.cmd === "worker") return worker();
  if (a.cmd === "help" || a.opt.has("help")) { console.log(HONEST + "\n" + USAGE); return process.exit(0); }
  process.exit(await client(a));
};
await main();
