// The bend2 that gen2 loads: the source of the Bend that bend-lint pins (package.json of bend-lint:
// bendWindows on Windows, else bendRelease), which bend-lint downloads into its cache on install. So
// gen2 checks with the same Bend as `bun run lint`, and the repo needs no other checkout.
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";

const fail = (msg: string): never => {
  console.error("[gen2] " + msg);
  process.exit(1);
};
// bend-lint's package: the nearest node_modules/bend-lint above this folder
let pkgFile = "";
for (let d = import.meta.dir; ; d = path.dirname(d)) {
  const f = path.join(d, "node_modules", "bend-lint", "package.json");
  if (fs.existsSync(f)) { pkgFile = f; break; }
  if (path.dirname(d) === d) fail("bend-lint is not installed (run `bun install`)");
}
const pkg = JSON.parse(fs.readFileSync(pkgFile, "utf8"));
const pin: string = process.platform === "win32" ? pkg.bendWindows : pkg.bendRelease;
if (typeof pin !== "string" || !/^[\w.-]+\/[\w.-]+\/[\w.-]+$/.test(pin)) fail("bend-lint's package.json pins no Bend");
// bend-lint's cache folder (as its src/linter/seam.ts computes it)
const cache = process.env.XDG_CACHE_HOME
  ?? (process.platform === "win32" ? (process.env.LOCALAPPDATA ?? path.join(os.homedir(), "AppData", "Local")) : path.join(os.homedir(), ".cache"));
const file = path.join(cache, "bend-lint", ...pin.split("/"), "bend2", "bend.ts");
if (!fs.existsSync(file)) fail("no bend2 at " + file + " (run `bun install`, or `bun run lint` once: bend-lint downloads Bend " + pin + ")");
const B: any = await import(file);
export default B;
