#!/usr/bin/env bun
// synth.ts: bend-synth's command line and its supervisor. The supervisor never loads Bend: workers
// (engine.ts) do, each contained (a Windows job object with a memory limit, below-normal priority,
// a wall-clock watchdog). It schedules jobs in slices, so several callers share the workers fairly; a
// job keeps its live search in the worker that ran it last (a resume continues the same tree), and every
// goal a search proves is kept in SQLite: the next job that meets that goal (another def, a restart,
// another agent) checks the stored proof first.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { spawn } from "node:child_process";
import { createHash } from "node:crypto";
import type { FromWorker, Report, Task } from "./engine.ts";

const HERE = import.meta.dir;
const ENGINE = path.join(HERE, "engine.ts");
const sha = (s: string | Buffer) => createHash("sha256").update(s).digest("hex");
const VERSION = sha(fs.readFileSync(ENGINE) + "\0" + fs.readFileSync(import.meta.path)).slice(0, 16);
const STATE = path.resolve(process.env.BEND_SYNTH_STATE ?? path.join(os.tmpdir(), "bend-synth", sha(HERE).slice(0, 12)));
const ENDPOINT = path.join(STATE, "endpoint.json");
const SLICE_MS = 1500, IDLE_EXIT_MS = 10 * 60 * 1000, WORKER_IDLE_MS = 90 * 1000;
const WORKERS = Math.max(1, Math.min(4, Number(process.env.BEND_SYNTH_WORKERS) || 1));
const MEM_MB = Math.max(256, Math.min(4096, Number(process.env.BEND_SYNTH_MEM_MB) || Math.min(1024, Math.floor(os.totalmem() / 1048576 * 0.1))));

// ---- which Bend: --bend-path, $BEND_PATH, the nearest bend2/ (or a sibling bend/bend2/) above the
// file, this tool's own checkout. A repository root or its bend2 directory ----
const bendAt = (p: string): string | null => {
  for (const d of [p, path.join(p, "bend2")]) if (fs.existsSync(path.join(d, "bend.ts")) && fs.existsSync(path.join(d, "base.bend"))) return fs.realpathSync(d);
  return null;
};
export const bendDir = (given?: string, from?: string): string => {
  if (given) { const r = bendAt(path.resolve(given)); if (r) return r; throw new Error("no Bend at " + given + " (a repository root or its bend2 directory)"); }
  if (process.env.BEND_PATH) { const r = bendAt(path.resolve(process.env.BEND_PATH)); if (r) return r; throw new Error("no Bend at $BEND_PATH=" + process.env.BEND_PATH); }
  if (from) for (let d = path.resolve(from); ; d = path.dirname(d)) {
    const r = bendAt(path.join(d, "bend2")) ?? bendAt(path.join(d, "bend", "bend2"));
    if (r) return r;
    if (path.dirname(d) === d) break;
  }
  const own = bendAt(path.resolve(HERE, "..", ".."));
  if (own) return own;
  throw new Error("no Bend found: pass --bend-path PATH (a Bend repository or its bend2 directory)");
};
const bendHash = (dir: string) => sha(fs.readFileSync(path.join(dir, "bend.ts")) + "\0" + fs.readFileSync(path.join(dir, "base.bend"))).slice(0, 16);

// ---- containment ----
// A worker applies this to itself before it loads Bend: a failed Windows limit is a failed worker,
// never an unbounded one. Elsewhere the limit is the worker's own RSS check, plus the watchdog.
export async function contain(memoryMb: number): Promise<string> {
  try { os.setPriority(0, os.constants.priority.PRIORITY_BELOW_NORMAL); } catch { /* a hint */ }
  if (process.platform !== "win32") return "cooperative RSS limit " + memoryMb + " MiB; wall-clock watchdog";
  if (process.arch !== "x64" && process.arch !== "arm64") throw new Error("unsupported Windows ABI for memory containment");
  const { dlopen, ptr } = await import("bun:ffi");
  const lib = dlopen("kernel32.dll", {
    CreateJobObjectW: { args: ["ptr", "ptr"], returns: "ptr" },
    SetInformationJobObject: { args: ["ptr", "i32", "ptr", "u32"], returns: "i32" },
    AssignProcessToJobObject: { args: ["ptr", "ptr"], returns: "i32" },
    GetCurrentProcess: { args: [], returns: "ptr" },
    GetLastError: { args: [], returns: "u32" },
  });
  const k = lib.symbols, job = k.CreateJobObjectW(null, null);
  if (!job) throw new Error("CreateJobObjectW failed: " + k.GetLastError());
  // JOBOBJECT_EXTENDED_LIMIT_INFORMATION (Win64): LimitFlags at 16, ProcessMemoryLimit at 112, JobMemoryLimit at 120
  const info = new Uint8Array(144), view = new DataView(info.buffer);
  view.setUint32(16, 0x100 | 0x200, true);
  view.setBigUint64(112, BigInt(memoryMb) * 1048576n, true);
  view.setBigUint64(120, BigInt(memoryMb) * 1048576n, true);
  if (!k.SetInformationJobObject(job, 9, ptr(info), info.length) || !k.AssignProcessToJobObject(job, k.GetCurrentProcess())) {
    throw new Error("Windows refused the worker memory limit: " + k.GetLastError());
  }
  (globalThis as Record<string, unknown>).__bendSynthJob = { lib, job };
  return "Windows job memory limit " + memoryMb + " MiB";
}
// the supervisor's job object: Windows closes it when the supervisor dies, which kills its workers
const workerGroup = async (): Promise<((pid: number) => void) | undefined> => {
  if (process.platform !== "win32") return;
  const { dlopen, ptr } = await import("bun:ffi");
  const lib = dlopen("kernel32.dll", {
    CreateJobObjectW: { args: ["ptr", "ptr"], returns: "ptr" },
    SetInformationJobObject: { args: ["ptr", "i32", "ptr", "u32"], returns: "i32" },
    AssignProcessToJobObject: { args: ["ptr", "ptr"], returns: "i32" },
    OpenProcess: { args: ["u32", "i32", "u32"], returns: "ptr" },
    CloseHandle: { args: ["ptr"], returns: "i32" },
    GetLastError: { args: [], returns: "u32" },
  });
  const k = lib.symbols, job = k.CreateJobObjectW(null, null), info = new Uint8Array(144), view = new DataView(info.buffer);
  view.setUint32(16, 0x2000, true); // kill on job close
  if (!job || !k.SetInformationJobObject(job, 9, ptr(info), info.length)) throw new Error("could not make the Windows worker group: " + k.GetLastError());
  (globalThis as Record<string, unknown>).__bendSynthGroup = { lib, job };
  return (pid) => {
    const h = k.OpenProcess(0x101, 0, pid);
    const ok = h && k.AssignProcessToJobObject(job, h);
    if (h) k.CloseHandle(h);
    if (!ok) throw new Error("could not contain worker " + pid + ": " + k.GetLastError());
  };
};
const spawnWorker = (bend: string, ipc: (m: FromWorker) => void, onExit: (code: number | null) => void) => {
  fs.mkdirSync(STATE, { recursive: true });
  const logFile = path.join(STATE, "worker.log");
  const logStart = fs.existsSync(logFile) ? fs.statSync(logFile).size : 0;
  const log = fs.openSync(logFile, "a");
  const p = Bun.spawn([process.execPath, ENGINE, "worker", bend], {
    stdin: "ignore", stdout: log, stderr: log, windowsHide: true, ipc: (m: FromWorker) => ipc(m),
    env: { ...process.env, BEND_SYNTH_MEM_MB: String(MEM_MB), BEND_NO_TELEMETRY: "1" },
    onExit: (_p, code) => { try { fs.closeSync(log); } catch { /* closed */ } onExit(code); },
  });
  return Object.assign(p, { logStart });
};
// what this worker wrote to the shared log (not an older worker's lines)
const logTail = (from: number) => { try { const t = fs.readFileSync(path.join(STATE, "worker.log")).subarray(from).toString("utf8"); return t.slice(0, 1500) + (t.length > 1500 ? "\n…" : ""); } catch { return ""; } };

// ---- the store: jobs, their reports, and every goal a search proved ----
type Job = {
  id: string; key: string; file: string; target: string; kind: "prove" | "goals"; spec?: Task["spec"]; helpers: boolean;
  bend: string; bendHash: string; deps: Record<string, string>; status: string; budgetMs: number; spentMs: number;
  report: Report; submissions: string[]; created: number; updated: number; rev: number; done: boolean; queuedAt?: number;
};
const FINAL = new Set(["proven", "synthesized", "nothing", "error", "cancelled"]);
class Store {
  db: import("bun:sqlite").Database;
  constructor(file: string) {
    const { Database } = require("bun:sqlite") as typeof import("bun:sqlite");
    this.db = new Database(file, { create: true });
    this.db.exec(`PRAGMA journal_mode=WAL; PRAGMA synchronous=NORMAL;
      CREATE TABLE IF NOT EXISTS jobs(id TEXT PRIMARY KEY, key TEXT, json TEXT NOT NULL);
      CREATE INDEX IF NOT EXISTS jobs_key ON jobs(key);
      CREATE TABLE IF NOT EXISTS goals(file TEXT, key TEXT, text TEXT, at INTEGER, PRIMARY KEY(file, key));`);
  }
  save(j: Job) { j.updated = Date.now(); this.db.query("INSERT OR REPLACE INTO jobs VALUES(?,?,?)").run(j.id, j.key, JSON.stringify(j)); }
  get(id: string): Job | null { const r = this.db.query("SELECT json FROM jobs WHERE id=?").get(id) as { json: string } | null; return r ? JSON.parse(r.json) : null; }
  byKey(key: string): Job[] { return (this.db.query("SELECT json FROM jobs WHERE key=? ORDER BY rowid DESC LIMIT 4").all(key) as { json: string }[]).map((r) => JSON.parse(r.json)); }
  recent(): Job[] { return (this.db.query("SELECT json FROM jobs ORDER BY rowid DESC LIMIT 30").all() as { json: string }[]).map((r) => JSON.parse(r.json)); }
  learn(file: string, key: string, text: string) { this.db.query("INSERT OR REPLACE INTO goals VALUES(?,?,?,?)").run(file, key, text, Date.now()); }
  cache(file: string): [string, string][] { return (this.db.query("SELECT key, text FROM goals WHERE file=? ORDER BY at DESC LIMIT 4000").all(file) as { key: string; text: string }[]).map((r) => [r.key, r.text]); }
}

// ---- the supervisor ----
type Worker = { p: ReturnType<typeof spawnWorker>; bend: string; job: string | null; warm: string[]; ready: boolean; fatal?: string; timer?: ReturnType<typeof setTimeout>; idle?: ReturnType<typeof setTimeout> };
const alive = (pid: number) => { try { process.kill(pid, 0); return true; } catch { return false; } };
type Endpoint = { pid: number; port: number; token: string; version: string };
const endpoint = (): Endpoint | undefined => { try { const e = JSON.parse(fs.readFileSync(ENDPOINT, "utf8")); return alive(e.pid) ? e : undefined; } catch { return undefined; } };
// the files of a job (its own from the start, its imports after its first slice) that changed or are gone
const changed = (j: Job): string[] => Object.entries(j.deps).filter(([f, h]) => { try { return sha(fs.readFileSync(f, "utf8")).slice(0, 16) !== h; } catch { return true; } }).map(([f]) => f);

async function serve(): Promise<void> {
  fs.mkdirSync(STATE, { recursive: true });
  const lock = path.join(STATE, "server.lock");
  try { fs.writeFileSync(lock, String(process.pid), { flag: "wx" }); } catch {
    if (alive(Number(fs.readFileSync(lock, "utf8")))) return;
    fs.unlinkSync(lock);
    try { fs.writeFileSync(lock, String(process.pid), { flag: "wx" }); } catch { return; }
  }
  const store = new Store(path.join(STATE, "synth.sqlite"));
  const group = await workerGroup().catch(() => undefined);
  const live = new Map<string, Job>();
  for (const j of store.recent()) if (j.status === "queued" || j.status === "running") { j.status = "interrupted"; store.save(j); }
  const queue: string[] = [];
  const workers: Worker[] = [];
  let lastActive = Date.now(), failures = 0;
  const get = (id: string): Job => { const j = live.get(id) ?? store.get(id); if (!j) throw new Error("no job " + id); return j; };
  const save = (j: Job) => { j.rev++; if (FINAL.has(j.status) || !["queued", "running"].includes(j.status)) live.delete(j.id); else live.set(j.id, j); store.save(j); };
  const retire = (w: Worker) => { const i = workers.indexOf(w); if (i >= 0) workers.splice(i, 1); try { w.p.kill(); } catch { /* gone */ } };
  const onMsg = (w: Worker, m: FromWorker) => {
    if (m.t === "ready") { w.ready = true; failures = 0; pump(); return; }
    if (m.t === "fatal") { w.fatal = m.message; const j = w.job ? live.get(w.job) : undefined; if (j) { j.status = "error"; j.report = { status: "error", text: "# worker: " + m.message }; save(j); } w.job = null; retire(w); return; }
    if (m.t === "lemma") { store.learn(m.file, m.key, m.text); return; }
    const j = live.get(m.id);
    if (!j) return;
    if (m.t === "progress") { j.report = m.report; j.rev++; return; }
    if (m.t === "slice") {
      if (w.timer) clearTimeout(w.timer);
      w.job = null;
      w.warm = [m.id, ...w.warm.filter((x) => x !== m.id)].slice(0, 4);
      j.spentMs += m.spentMs;
      j.report = m.report;
      if (m.deps && Object.keys(m.deps).length) j.deps = m.deps;
      if (j.status === "cancelled") { save(j); pump(); return; }
      if (m.done) { j.done = true; j.status = m.report.status === "running" ? "open" : m.report.status; }
      else if (j.spentMs < j.budgetMs) { j.status = "queued"; j.queuedAt = Date.now(); queue.push(j.id); }
      else j.status = m.report.status === "running" ? "open" : m.report.status;
      save(j);
      w.idle = setTimeout(() => { if (!w.job) retire(w); }, WORKER_IDLE_MS);
      pump();
    }
  };
  const newWorker = (bend: string): Worker => {
    const w: Worker = { bend, job: null, warm: [], ready: false } as unknown as Worker;
    w.p = spawnWorker(bend, (m) => onMsg(w, m), (code) => {
      const i = workers.indexOf(w);
      if (i >= 0) workers.splice(i, 1);
      if (w.timer) clearTimeout(w.timer);
      const j = w.job ? live.get(w.job) : undefined;
      if (j && j.status === "running") { j.status = "interrupted"; j.report = { ...j.report, text: j.report.text + "\n# the worker stopped (exit " + code + "); resume continues from the proven goals" }; save(j); }
      // a worker that dies before it is ready (a broken Bend, a bad install): three in a row fail the queue
      if (!w.ready && ++failures >= 3) {
        for (const id of queue.splice(0)) {
          const q = live.get(id);
          if (q && q.bend === w.bend) { q.status = "error"; q.report = { status: "error", text: "# the worker does not start:\n" + (w.fatal ?? logTail(w.p.logStart)) }; save(q); }
        }
        failures = 0;
        return;
      }
      pump();
    });
    try { group?.(w.p.pid); } catch (e) { w.p.kill(); throw e; }
    workers.push(w);
    return w;
  };
  const pump = () => {
    for (let qi = 0; qi < queue.length;) {
      const j = live.get(queue[qi]);
      if (!j || j.status !== "queued") { queue.splice(qi, 1); continue; }
      const idle = workers.filter((w) => w.ready && !w.job && w.bend === j.bend);
      // a job's live tree is in the worker that ran it last: it waits for that worker up to a slice
      // (it finishes within one) rather than start cold elsewhere; other jobs take the idle workers
      const own = idle.find((x) => x.warm.includes(j.id));
      const ownBusy = !own && workers.some((x) => x.job && x.warm.includes(j.id));
      if (ownBusy && Date.now() - (j.queuedAt ?? 0) < SLICE_MS) { qi++; continue; }
      const w = own ?? idle[0];
      if (!w) {
        if (workers.length < WORKERS) { newWorker(j.bend); qi++; continue; }
        const other = workers.find((x) => x.ready && !x.job && x.bend !== j.bend);
        if (other) { retire(other); newWorker(j.bend); }
        qi++;
        continue;
      }
      queue.splice(qi, 1);
      // a job searches the text it was asked about: once its files change (an edit, a delete) it stops,
      // and `prove` again starts a job on the new text (the same text again attaches to this one)
      const gone = changed(j);
      if (gone.length) {
        j.status = "changed";
        j.report = { status: "open", text: "# " + j.target + ": stopped after " + (j.spentMs / 1000).toFixed(1) + " s: " + gone.map((f) => path.basename(f)).join(", ")
          + " changed (or " + (gone.length > 1 ? "are" : "is") + " gone) since the job began; `prove` again searches the new text" + (j.report.text === "# queued" ? "" : "\n# the last report, of the old text:\n" + j.report.text) };
        for (const x of workers) if (x.warm.includes(j.id) && !x.job) x.p.send({ t: "drop", id: j.id });
        save(j);
        continue;
      }
      if (w.idle) clearTimeout(w.idle);
      // another job's warm session in this worker is dropped when the worker's warm list overflows
      w.job = j.id;
      j.status = "running";
      const task: Task = { id: j.id, kind: j.kind, file: j.file, target: j.target, spec: j.spec, helpers: j.helpers,
        sliceMs: Math.max(200, Math.min(SLICE_MS, j.budgetMs - j.spentMs)), budgetMs: Math.max(200, j.budgetMs - j.spentMs), cache: w.warm.includes(j.id) ? [] : store.cache(j.file.replaceAll("\\", "/")), submissions: j.submissions };
      w.p.send({ t: "task", task });
      w.timer = setTimeout(() => { if (w.job === j.id) retire(w); }, Math.max(task.sliceMs, task.budgetMs ?? 0) + 20000); // a refueled step may use the job's budget
      lastActive = Date.now();
    }
  };
  const view = (j: Job) => ({ id: j.id, status: j.status, file: j.file, target: j.target, spentMs: j.spentMs, budgetMs: j.budgetMs, rev: j.rev, done: j.done, report: j.report });
  const enqueue = (j: Job, budgetMs: number) => {
    j.budgetMs = j.spentMs + budgetMs;
    j.status = "queued";
    j.queuedAt = Date.now();
    save(j);
    if (!queue.includes(j.id)) queue.push(j.id);
    pump();
  };
  const token = crypto.randomUUID();
  const server = Bun.serve({
    hostname: "127.0.0.1", port: 0, maxRequestBodySize: 4 * 1048576,
    async fetch(req) {
      if (req.headers.get("authorization") !== "Bearer " + token) return new Response("unauthorized", { status: 401 });
      try {
        const a = await req.json() as Record<string, unknown>;
        const cmd = String(a.cmd ?? "");
        lastActive = Date.now();
        if (cmd === "hello") return Response.json({ version: VERSION });
        if (cmd === "status") return Response.json({ workers: workers.map((w) => ({ pid: w.p.pid, bend: w.bend, job: w.job })), queued: queue.length, memoryMb: MEM_MB,
          jobs: store.recent().slice(0, 12).map((j) => ({ id: j.id, target: j.target, file: path.basename(j.file), status: live.get(j.id)?.status ?? j.status, spentMs: j.spentMs })) });
        if (cmd === "stop") { setTimeout(stop, 50); return Response.json({ stopped: true }); }
        if (cmd === "start") {
          const file = fs.realpathSync(String(a.file));
          const target = String(a.target ?? "");
          if (!/^[A-Za-z_][\w.]*$/.test(target)) throw new Error("name the def to search");
          const bend = bendDir(a.bendPath ? String(a.bendPath) : undefined, path.dirname(file));
          const kind = a.kind === "goals" ? "goals" : "prove";
          const spec = a.spec as Task["spec"];
          const bh = bendHash(bend), text = fs.readFileSync(file, "utf8");
          const key = sha(JSON.stringify([VERSION, bh, file, text, target, kind, spec ?? null, !!a.helpers])).slice(0, 24);
          const budget = Math.max(200, Math.min(600000, Number(a.budget ?? 30) * 1000));
          const had = store.byKey(key).map((j) => live.get(j.id) ?? j).find((j) => changed(j).length === 0 && j.status !== "cancelled");
          if (had) {
            // the same request attaches; a paused one continues with the budget this call brings
            if (!had.done && !FINAL.has(had.status) && !["queued", "running"].includes(had.status)) { live.set(had.id, had); enqueue(had, budget); }
            return Response.json(view(had));
          }
          const now = Date.now();
          const j: Job = { id: crypto.randomUUID().slice(0, 8), key, file, target, kind, spec, helpers: !!a.helpers, bend, bendHash: bh, deps: { [file]: sha(text).slice(0, 16) },
            status: "queued", budgetMs: budget, spentMs: 0, report: { status: "running", text: "# queued" }, submissions: [], created: now, updated: now, rev: 0, done: false };
          live.set(j.id, j);
          enqueue(j, budget);
          return Response.json(view(j));
        }
        const j = get(String(a.id));
        if (cmd === "view") {
          // a poll that has the current revision gets no report again
          const v = live.get(j.id) ?? j;
          return Response.json(a.rev !== undefined && Number(a.rev) === v.rev ? { ...view(v), report: undefined, same: true } : view(v));
        }
        if (cmd === "cancel") { j.status = "cancelled"; save(j); for (const w of workers) if (w.warm.includes(j.id) && !w.job) w.p.send({ t: "drop", id: j.id }); return Response.json(view(j)); }
        if (cmd === "resume" || cmd === "submit") {
          if (changed(j).length) throw new Error("the files changed since this job started: start a new job (prove again)");
          if (cmd === "submit") {
            const src = String(a.source ?? "");
            if (src.length > 262144) throw new Error("a submission is at most 256 KiB");
            if (!j.submissions.includes(src)) j.submissions.push(src);
            if (j.done) j.done = false; // a sketch reopens an exhausted search
          }
          if (FINAL.has(j.status) && j.status !== "cancelled" && cmd === "resume") return Response.json(view(j));
          live.set(j.id, j);
          if (!["queued", "running"].includes(j.status)) enqueue(j, Math.max(200, Math.min(600000, Number(a.budget ?? 30) * 1000)));
          else save(j);
          return Response.json(view(j));
        }
        throw new Error("unknown command " + cmd);
      } catch (e) { return Response.json({ error: e instanceof Error ? e.message : String(e) }, { status: 400 }); }
    },
  });
  const stop = () => {
    for (const w of workers) { try { w.p.kill(); } catch { /* gone */ } }
    try { if (Number(fs.readFileSync(lock, "utf8")) === process.pid) { fs.unlinkSync(lock); fs.unlinkSync(ENDPOINT); } } catch { /* gone */ }
    process.exit(0);
  };
  setInterval(() => { if (!live.size && !queue.length && Date.now() - lastActive > IDLE_EXIT_MS) stop(); }, 30000).unref();
  fs.writeFileSync(ENDPOINT, JSON.stringify({ pid: process.pid, port: server.port, token, version: VERSION } satisfies Endpoint));
  process.on("SIGINT", stop); process.on("SIGTERM", stop);
}

// ---- the client ----
class Transport extends Error {}
const request = async (e: Endpoint, a: Record<string, unknown>): Promise<Record<string, unknown>> => {
  let res: Response, out: Record<string, unknown>;
  try {
    res = await fetch("http://127.0.0.1:" + e.port, { method: "POST", headers: { authorization: "Bearer " + e.token }, body: JSON.stringify(a), signal: AbortSignal.timeout(a.cmd === "hello" ? 500 : 15000) });
    out = await res.json() as Record<string, unknown>;
  } catch (x) { throw new Transport(x instanceof Error ? x.message : String(x)); }
  if (!res.ok) throw new Error(String(out.error ?? "request failed"));
  return out;
};
const connect = async (start: boolean): Promise<Endpoint | undefined> => {
  const until = Date.now() + 8000;
  let launched = false;
  while (Date.now() < until) {
    const e = endpoint();
    if (e) {
      if (e.version !== VERSION) {
        // another version serves: stop it (its jobs and proven goals stay in the store)
        try { await request(e, { cmd: "stop" }); } catch { /* stopping */ }
        await Bun.sleep(300);
        continue;
      }
      try { await request(e, { cmd: "hello" }); return e; } catch { /* starting */ }
    } else if (!start) return undefined;
    else if (!launched) {
      fs.mkdirSync(STATE, { recursive: true });
      const log = fs.openSync(path.join(STATE, "server.log"), "a");
      const p = spawn(process.execPath, [import.meta.path, "serve"], { detached: true, windowsHide: true, stdio: ["ignore", log, log], env: process.env });
      p.unref(); fs.closeSync(log); launched = true;
    }
    await Bun.sleep(30);
  }
  throw new Transport("the supervisor did not start; see " + path.join(STATE, "server.log"));
};
const HELP = `bend-synth: proofs and programs for Bend's ?TODO holes, budgeted, resumable, shared by callers.

  bun tools/bend-synth/synth.ts prove FILE DEF [--budget S] [--wait S] [--spec F.json] [--helpers] [--write] [--json] [--bend-path P]
      DEF's body is ?TODO: a whole body. A body with ?TODO holes: each hole. A proposition is proven
      (Bend checks every step); a data def is synthesized from the laws that name it and --spec
      examples ({"examples": [{"call": "half(4n)", "expect": "2n"}]}): evidence, not a proof.
      Prints the proof, or the best partial with each open hole's goal, context and what was tried.
      --budget: search seconds in all (default 30); --wait: seconds this call waits (default 10); the job
      runs on in the background, and calling the same command again attaches to it (or resumes it).
      --write: put a proven or synthesized body into FILE (only if that def's text did not change).
      --helpers: also print each open hole as a lemma stub over its context.
  ... goals FILE DEF            each hole's goal, context, derived facts and the steps that apply
  ... show JOB | watch JOB [--wait S] | resume JOB [--budget S] | cancel JOB | export JOB
  ... submit JOB SKETCH.bend    an agent's sketch of DEF's body (or a file with DEF), its holes searched first
  ... bench FILE [REGEX] [--budget S] [--verbose] [--proofs]   every proven lemma (and program with laws) found again, its body hidden
  ... tally [--json]            every prove job of every checkout on this machine, by outcome: is the search used, and does it prove
  ... status | stop
Exit: 0 done (proven, synthesized, nothing to do), 2 open or partial, 3 still running, 1 error.
State (jobs, proven goals): ${STATE}. Workers: ${WORKERS} (BEND_SYNTH_WORKERS), ${MEM_MB} MiB each (BEND_SYNTH_MEM_MB).`;
const exitOf = (status: string) => (["proven", "synthesized", "nothing"].includes(status) ? 0 : ["queued", "running"].includes(status) ? 3 : status === "error" ? 1 : 2);
const applyEdit = (r: Report): string => {
  const e = r.edit;
  if (!e) return "# --write: nothing to write";
  const text = fs.readFileSync(e.file, "utf8");
  // a law's new def (no text to replace) goes at the end of the file
  if (e.from === "") { fs.writeFileSync(e.file, text.replace(/\s*$/, "\n\n") + e.to + "\n"); return "# --write: appended to " + e.file; }
  const n = text.split(e.from).length - 1;
  if (n !== 1) return "# --write: " + path.basename(e.file) + " changed meanwhile (the def's text is " + (n ? "not unique" : "gone") + "); nothing written";
  fs.writeFileSync(e.file, text.replace(e.from, () => e.to));
  return "# --write: written to " + e.file;
};
const parseArgs = (argv: string[]) => {
  const pos: string[] = [], opt = new Map<string, string>();
  const VALUED = new Set(["budget", "wait", "spec", "bend-path"]);
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (!a.startsWith("--")) { pos.push(a); continue; }
    const eq = a.indexOf("=");
    const k = eq > 0 ? a.slice(2, eq) : a.slice(2);
    if (eq > 0) opt.set(k, a.slice(eq + 1));
    else if (VALUED.has(k)) { if (argv[i + 1] === undefined) throw new Error(a + " needs a value"); opt.set(k, argv[++i]); }
    else opt.set(k, "");
  }
  return { pos, opt };
};
async function bench(file: string, regex: string, budgetS: number, bendPath?: string, verbose = false, proofsOnly = false): Promise<number> {
  const bend = bendDir(bendPath, path.dirname(path.resolve(file)));
  let code = 1, got = false;
  await new Promise<void>((resolve) => {
    const p = spawnWorker(bend, (m) => {
      if (m.t === "ready") p.send({ t: "task", task: { id: "bench", kind: "bench", file: fs.realpathSync(file), target: "", regex, verbose, proofsOnly, budgetMs: budgetS * 1000, sliceMs: budgetS * 1000 } satisfies Task });
      else if (m.t === "row") console.log(m.line);
      else if (m.t === "fatal") { console.error("bend-synth: " + m.message); p.kill(); }
      else if (m.t === "slice" && m.id === "bench") { got = true; console.log(m.report.text); code = m.report.status === "proven" ? 0 : 2; p.kill(); }
    }, (exit) => { if (!got) console.error("bend-synth: the worker stopped (exit " + exit + ")\n" + logTail(p.logStart)); resolve(); });
  });
  return code;
}
// every prove job in the stores of every checkout on this machine (each checkout keeps its own), by
// outcome; it reads the stores only, so it needs no supervisor
const tally = (json: boolean): number => {
  const { Database } = require("bun:sqlite") as typeof import("bun:sqlite");
  const root = path.dirname(STATE);
  const jobs: Record<string, number> = {}, defs: Record<string, Set<string>> = {};
  for (const d of fs.existsSync(root) ? fs.readdirSync(root) : []) {
    const f = path.join(root, d, "synth.sqlite");
    if (!fs.existsSync(f)) continue;
    const db = new Database(f, { readonly: true });
    try {
      for (const { json: t } of db.query("SELECT json FROM jobs").all() as { json: string }[]) {
        const j = JSON.parse(t) as Job;
        if (j.kind !== "prove") continue;
        jobs[j.status] = (jobs[j.status] ?? 0) + 1;
        (defs[j.status] ??= new Set()).add(j.file + " " + j.target);
      }
    } finally { db.close(); }
  }
  const rows = Object.entries(jobs).sort((a, b) => b[1] - a[1]).map(([status, n]) => ({ status, jobs: n, defs: defs[status].size }));
  if (json) { console.log(JSON.stringify(rows)); return 0; }
  const total = rows.reduce((t, r) => t + r.jobs, 0);
  console.log("prove jobs: " + total);
  for (const r of rows) console.log("  " + r.status + ": " + r.jobs + " jobs, " + r.defs + " defs");
  return 0;
};
async function main(argv: string[]): Promise<number> {
  const cmd = argv[0] ?? "help";
  if (cmd === "serve") { await serve(); return 0; }
  if (cmd === "help" || cmd === "--help" || cmd === "-h") { console.log(HELP); return 0; }
  const { pos, opt } = parseArgs(argv.slice(1));
  if (cmd === "bench") {
    if (!pos[0]) throw new Error("bench FILE [REGEX]");
    return bench(pos[0], pos[1] ?? "", Number(opt.get("budget") ?? 2), opt.get("bend-path"), opt.has("verbose"), opt.has("proofs"));
  }
  const json = opt.has("json");
  if (cmd === "tally") return tally(json);
  if (cmd === "stop") { const e = endpoint(); if (e) await request(e, { cmd: "stop" }).catch(() => {}); console.log(e ? "stopped" : "no supervisor is running"); return 0; }
  const e0 = await connect(cmd !== "status");
  if (!e0) { console.log(json ? JSON.stringify({ running: false }) : "no supervisor is running"); return 0; }
  let e = e0;
  const call = async (a: Record<string, unknown>) => {
    for (let retry = 0; ; retry++) {
      try { return await request(e, a); } catch (x) {
        if (!(x instanceof Transport) || retry >= 2) throw x;
        e = (await connect(true))!;
      }
    }
  };
  if (cmd === "status") { console.log(JSON.stringify(await call({ cmd }), null, json ? 0 : 2)); return 0; }
  let r: Record<string, unknown>;
  if (cmd === "prove" || cmd === "goals") {
    if (!pos[0] || !pos[1]) throw new Error(HELP);
    r = await call({ cmd: "start", file: path.resolve(pos[0]), target: pos[1], kind: cmd, budget: cmd === "goals" ? 3 : Number(opt.get("budget") ?? 30),
      spec: opt.has("spec") ? JSON.parse(fs.readFileSync(opt.get("spec")!, "utf8")) : undefined, helpers: opt.has("helpers"), bendPath: opt.get("bend-path") });
  } else if (["show", "watch", "resume", "cancel", "export", "submit"].includes(cmd)) {
    if (!pos[0]) throw new Error(cmd + " JOB");
    if (cmd === "submit") {
      if (!pos[1]) throw new Error("submit JOB SKETCH.bend");
      r = await call({ cmd, id: pos[0], source: fs.readFileSync(pos[1], "utf8"), budget: opt.get("budget") });
    } else r = await call({ cmd: cmd === "show" || cmd === "watch" || cmd === "export" ? "view" : cmd, id: pos[0], budget: opt.get("budget") });
  } else throw new Error("unknown command " + cmd + "\n" + HELP);
  // wait: until the job is done or --wait elapses (show and export do not wait)
  const waitS = cmd === "show" || cmd === "export" || cmd === "cancel" ? 0 : Number(opt.get("wait") ?? (cmd === "goals" ? 5 : 10));
  const until = Date.now() + waitS * 1000;
  let shown = -1;
  while (["queued", "running"].includes(String(r.status)) && Date.now() < until) {
    await Bun.sleep(Date.now() + 120 < until ? 120 : 20);
    const nr = await call({ cmd: "view", id: r.id, rev: r.rev });
    r = nr.same ? { ...nr, report: r.report } : nr;
    if (!json && process.stderr.isTTY && r.rev !== shown) { shown = Number(r.rev); process.stderr.write("\r" + String((r.report as Report).text.split("\n").find((l) => l.startsWith("# ") && !l.includes("helper, not the judge")) ?? "").slice(0, 110).padEnd(110)); }
  }
  if (!json && process.stderr.isTTY && shown >= 0) process.stderr.write("\r" + " ".repeat(110) + "\r");
  const rep = r.report as Report;
  if (cmd === "export") { process.stdout.write((rep.body ?? "") + "\n"); return rep.body ? 0 : 2; }
  if (json) console.log(JSON.stringify(r));
  else {
    console.log(rep.text);
    const st = String(r.status);
    if (["queued", "running"].includes(st)) console.log("# job " + r.id + ": still running (" + Math.round(Number(r.spentMs) / 100) / 10 + " s of " + Number(r.budgetMs) / 1000 + " s); the same command attaches to it");
    else if (!FINAL.has(st) && st !== "changed") console.log("# job " + r.id + ": " + st + " after " + Math.round(Number(r.spentMs) / 100) / 10 + " s; `resume " + r.id + "` continues it, `submit " + r.id + " sketch.bend` adds a sketch");
    if (opt.has("write") && (st === "proven" || st === "synthesized")) console.log(applyEdit(rep));
  }
  return exitOf(String(r.status));
}

if (import.meta.main) {
  main(process.argv.slice(2)).then((c) => { process.exitCode = c; }).catch((x) => { console.error("bend-synth: " + (x instanceof Error ? x.message : String(x))); process.exitCode = 1; });
}
