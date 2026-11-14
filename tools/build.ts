// build.ts: build the vend program.
//
// USAGE
//   bun run build [--out <path>]
//
// STEPS
//   1. Run `bend src/main.bend --check-only` with the `bend` on PATH, and stop unless it prints
//      ALL PROOFS CHECK: src/main.bend imports src/vend_node/impl.bend, which fills every law of
//      src/vend_node/spec.bend, so the program is built only when each of them is proven.
//   2. Run `bend src/main.bend -o <out>`. The out file is --out, else vend.exe (vend on POSIX) in
//      the user's data folder: %LOCALAPPDATA%\vend\bin on Windows, else $XDG_DATA_HOME/vend/bin,
//      else ~/.local/share/vend/bin.
//
// Exit status: 0 when the binary is written; 1 with bend's message, or the reason, otherwise.

import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

function fail(msg: string): never {
  console.error(`build: ${msg}`);
  process.exit(1);
}

function defaultOut(): string {
  const exe = process.platform === "win32" ? "vend.exe" : "vend";
  if (process.platform === "win32") {
    const base = process.env.LOCALAPPDATA;
    if (!base) fail("LOCALAPPDATA is not set; give --out");
    return path.join(base, "vend", "bin", exe);
  }
  const base = process.env.XDG_DATA_HOME || path.join(os.homedir(), ".local", "share");
  return path.join(base, "vend", "bin", exe);
}

function bend(args: string[]): { ok: boolean; text: string; secs: string } {
  const t0 = performance.now();
  const r = Bun.spawnSync(["bend", ...args], { stdout: "pipe", stderr: "pipe" });
  return { ok: r.exitCode === 0, text: r.stdout.toString() + r.stderr.toString(), secs: ((performance.now() - t0) / 1000).toFixed(1) };
}

function main(): void {
  const args = process.argv.slice(2);
  const at = args.indexOf("--out");
  if (args.length !== 0 && !(args.length === 2 && at === 0)) fail("usage: bun run build [--out <path>]");
  const out = path.resolve(at === 0 ? args[1] : defaultOut());

  const repo = path.resolve(import.meta.dir, "..");
  const entry = path.join(repo, "src", "main.bend");
  if (!fs.existsSync(entry)) fail(`no src/main.bend under ${repo}`);

  const check = bend([entry, "--check-only"]);
  if (!check.text.includes("ALL PROOFS CHECK")) {
    process.stderr.write(check.text);
    fail(`src/main.bend does not check (${check.secs} s)`);
  }
  console.log(`checked src/main.bend in ${check.secs} s: ALL PROOFS CHECK`);

  fs.mkdirSync(path.dirname(out), { recursive: true });
  const build = bend([entry, "-o", out]);
  if (!build.ok || !fs.existsSync(out)) {
    process.stderr.write(build.text);
    fail(`bend could not build the program (${build.secs} s)`);
  }
  console.log(`built ${out} in ${build.secs} s`);
}

main();
