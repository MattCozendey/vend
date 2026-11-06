// build.ts: build the vend program while some laws are still open.
//
// USAGE
//   bun run build [--verbose] [--keep]
//
// Bend refuses to build a program that imports a law no def fills. Until every law is proven, this
// script builds from a copy of src/ in which the open laws are removed, so the binary it writes is
// NOT the proven program: it runs code whose laws are still claims. The banner says how many laws
// were removed (--verbose names them). The repo itself is never changed.
//
// STEPS
//   1. Copy src/ to a fresh folder in the OS temp folder.
//   2. Remove each open law: a `law N:` block of a file F that no def fills. A def fills it when it is
//      `def N(` in F, or `def A.N(` in a file that imports F as A. A law that declares an operation
//      (such as `law Tree.write:`) is filled by its impl and so stays. Then, until nothing changes:
//      a def that names a removed law (N in F, or A.N where F is imported as A) is removed too, and
//      if that def filled a law, the law is now open and is removed as well.
//   3. Make the copy's main.bend import every impl.bend, so every operation that a spec declares is
//      filled in the program.
//   4. Run `bend <copy>/main.bend -o <out>` with the `bend` on PATH. The out file is vend.exe
//      (vend on POSIX) in the user's data folder: %LOCALAPPDATA%\vend\bin on Windows, else
//      $XDG_DATA_HOME/vend/bin, else ~/.local/share/vend/bin.
//   5. Remove the copy, also on failure, unless --keep is given.
//
// Exit status: 0 when the binary is written; 1 with bend's message, or the reason, otherwise.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

type File = { rel: string; lines: string[] };

// a block: the lines from a top-level `law`/`def` line to the next top-level line
type Block = { kind: "law" | "def"; name: string; start: number; end: number };

const HEAD = /^(law|def) ([A-Za-z_][\w.]*)(?:[:(\s]|$)/;
const IMPORT = /^import (\.{1,2}\/[^\s]+) as (\w+)\s*$/;

function fail(msg: string): never {
  console.error(`build: ${msg}`);
  process.exit(1);
}

function readTree(root: string): File[] {
  const out: File[] = [];
  const walk = (dir: string): void => {
    for (const e of fs.readdirSync(dir, { withFileTypes: true })) {
      const p = path.join(dir, e.name);
      if (e.isDirectory()) walk(p);
      else if (e.name.endsWith(".bend")) {
        out.push({ rel: path.relative(root, p).split(path.sep).join("/"), lines: fs.readFileSync(p, "utf8").split("\n") });
      }
    }
  };
  walk(root);
  return out;
}

function blocks(f: File): Block[] {
  const out: Block[] = [];
  for (let i = 0; i < f.lines.length; i++) {
    const m = HEAD.exec(f.lines[i]);
    if (!m) continue;
    let j = i + 1;
    while (j < f.lines.length && (f.lines[j] === "" || /^\s/.test(f.lines[j]) || /^\)/.test(f.lines[j]))) j++;
    while (j > i + 1 && f.lines[j - 1] === "") j--;
    out.push({ kind: m[1] as "law" | "def", name: m[2], start: i, end: j });
  }
  return out;
}

// the aliases under which each file is imported: file -> [(importer, alias)]
function importers(files: File[]): Map<string, { by: string; alias: string }[]> {
  const out = new Map<string, { by: string; alias: string }[]>();
  for (const f of files) {
    for (const line of f.lines) {
      const m = IMPORT.exec(line);
      if (!m) continue;
      const target = path.posix.normalize(path.posix.join(path.posix.dirname(f.rel), m[1]));
      const list = out.get(target) ?? [];
      list.push({ by: f.rel, alias: m[2] });
      out.set(target, list);
    }
  }
  return out;
}

function escape(s: string): string {
  return s.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}

// remove open laws and the defs that rest on them; returns the removed laws as "file: name"
function strip(files: File[]): string[] {
  const byRel = new Map(files.map((f) => [f.rel, f]));
  const imps = importers(files);
  const removed = new Map<string, Set<string>>(); // file -> names of blocks to drop
  const drop = (rel: string, name: string): boolean => {
    const s = removed.get(rel) ?? new Set<string>();
    if (s.has(name)) return false;
    s.add(name);
    removed.set(rel, s);
    return true;
  };
  const dropped = (rel: string, name: string): boolean => removed.get(rel)?.has(name) ?? false;

  // the law that a def `name` in file `rel` fills, if any
  const fillsOf = (rel: string, name: string): { rel: string; name: string } | undefined => {
    const own = blocks(byRel.get(rel)!).find((b) => b.kind === "law" && b.name === name);
    if (own) return { rel, name };
    for (const [target, list] of imps) {
      for (const { by, alias } of list) {
        if (by !== rel || !name.startsWith(alias + ".")) continue;
        const law = name.slice(alias.length + 1);
        const t = byRel.get(target);
        if (t && blocks(t).some((b) => b.kind === "law" && b.name === law)) return { rel: target, name: law };
      }
    }
    return undefined;
  };

  const filled = new Set<string>();
  for (const f of files) {
    for (const b of blocks(f)) {
      if (b.kind !== "def") continue;
      const law = fillsOf(f.rel, b.name);
      if (law) filled.add(`${law.rel}\u0000${law.name}`);
    }
  }
  const openLaws: { rel: string; name: string }[] = [];
  for (const f of files) {
    for (const b of blocks(f)) {
      if (b.kind === "law" && !filled.has(`${f.rel}\u0000${b.name}`)) openLaws.push({ rel: f.rel, name: b.name });
    }
  }
  for (const l of openLaws) drop(l.rel, l.name);

  // a def that names a removed law goes too, and so does the law it fills
  let queue = [...openLaws];
  while (queue.length > 0) {
    const next: { rel: string; name: string }[] = [];
    for (const law of queue) {
      const refs: { rel: string; re: RegExp }[] = [
        { rel: law.rel, re: new RegExp(`(?<![\\w.])${escape(law.name)}(?![\\w])`) },
      ];
      for (const { by, alias } of imps.get(law.rel) ?? []) {
        refs.push({ rel: by, re: new RegExp(`(?<![\\w.])${escape(alias + "." + law.name)}(?![\\w])`) });
      }
      for (const { rel, re } of refs) {
        const f = byRel.get(rel)!;
        for (const b of blocks(f)) {
          if (b.kind !== "def" || dropped(rel, b.name)) continue;
          const body = f.lines.slice(b.start, b.end).filter((l) => !/^\s*#/.test(l)).join("\n");
          if (!re.test(body)) continue;
          drop(rel, b.name);
          const filledLaw = fillsOf(rel, b.name);
          if (filledLaw && drop(filledLaw.rel, filledLaw.name)) next.push(filledLaw);
        }
      }
    }
    queue = next;
  }

  const lawsOut: string[] = [];
  for (const f of files) {
    const names = removed.get(f.rel);
    if (!names) continue;
    const bs = blocks(f).filter((b) => names.has(b.name));
    for (const b of bs) if (b.kind === "law") lawsOut.push(`${f.rel}: ${b.name}`);
    for (const b of [...bs].sort((x, y) => y.start - x.start)) f.lines.splice(b.start, b.end - b.start);
  }
  return lawsOut.sort();
}

function outPath(): string {
  const exe = process.platform === "win32" ? "vend.exe" : "vend";
  if (process.platform === "win32") {
    const base = process.env.LOCALAPPDATA;
    if (!base) throw new Error("LOCALAPPDATA is not set");
    return path.join(base, "vend", "bin", exe);
  }
  const base = process.env.XDG_DATA_HOME || path.join(os.homedir(), ".local", "share");
  return path.join(base, "vend", "bin", exe);
}

function main(): void {
  const args = process.argv.slice(2);
  const verbose = args.includes("--verbose");
  const keep = args.includes("--keep");
  const unknown = args.filter((a) => a !== "--verbose" && a !== "--keep");
  if (unknown.length > 0) fail(`unknown argument ${unknown[0]}; usage: bun run build [--verbose] [--keep]`);

  const repo = path.resolve(import.meta.dir, "..");
  const src = path.join(repo, "src");
  if (!fs.existsSync(path.join(src, "main.bend"))) fail(`no src/main.bend under ${repo}`);
  const tmp = fs.mkdtempSync(path.join(os.tmpdir(), "vend-build-"));
  const copy = path.join(tmp, "src");
  let code = 1;
  try {
    fs.cpSync(src, copy, { recursive: true });
    const files = readTree(copy);
    const stripped = strip(files);
    const main = files.find((f) => f.rel === "main.bend")!;
    const impls = files.filter((f) => f.rel.endsWith("/impl.bend")).map((f) => f.rel);
    const at = main.lines.findIndex((l) => l.startsWith("import ")) + 1;
    main.lines.splice(at, 0, ...impls.map((rel, i) => `import ./${rel} as BuildImpl${i}`));
    for (const f of files) fs.writeFileSync(path.join(copy, ...f.rel.split("/")), f.lines.join("\n"));

    const out = outPath();
    fs.mkdirSync(path.dirname(out), { recursive: true });
    const t0 = performance.now();
    const r = Bun.spawnSync(["bend", path.join(copy, "main.bend"), "-o", out], { stdout: "pipe", stderr: "pipe" });
    const secs = ((performance.now() - t0) / 1000).toFixed(1);
    if (r.exitCode !== 0 || !fs.existsSync(out)) {
      process.stderr.write(r.stdout.toString() + r.stderr.toString());
      throw new Error(`bend could not build the program (${secs} s)${keep ? `; the copy is kept at ${copy}` : ""}`);
    }
    console.log(`built ${out} in ${secs} s`);
    console.log(
      `NOT the proven program: ${stripped.length} open law(s) were removed from the build copy` +
        (verbose ? ":" : " (--verbose names them)."),
    );
    if (verbose) for (const s of stripped) console.log(`  ${s}`);
    if (keep) console.log(`the build copy is kept at ${copy}`);
    code = 0;
  } catch (e) {
    console.error(`build: ${e instanceof Error ? e.message : String(e)}`);
  } finally {
    if (!keep) fs.rmSync(tmp, { recursive: true, force: true });
  }
  process.exit(code);
}

main();
