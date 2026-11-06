// File endpoint
// =============
//
// The JS lane of file_fx.c. Paths are the bytes of a List<U32>; a value
// past 255 or a NUL byte is EINVAL.

// the path bytes of xs as a Buffer, or null
function filefx_path(xs) {
  const b = io_unlist(xs);
  return b === null || b.includes(0) ? null : Buffer.from(b);
}

function filefx_unit(f) {
  try {
    f();
    return io_done({ $: CID(Unit) });
  } catch (e) {
    return io_fail(io_code(e));
  }
}

// What is at the path, without following a last link. NotFound only for
// ENOENT: the OS says no entry is there.
function filefx_probe(path) {
  const p = filefx_path(path);
  if (p === null) {
    return { $: CID(Failed), code: 22, text: "the path is not bytes" };
  }
  try {
    const st = require("fs").lstatSync(p);
    const entry = st.isFile() ? CID(KFile) : st.isDirectory() ? CID(KDir) : CID(KOther);
    return { $: CID(Found), entry: { $: entry }, device: Number(st.dev) >>> 0 };
  } catch (e) {
    if (e.code === "ENOENT") {
      return { $: CID(NotFound) };
    }
    return { $: CID(Failed), code: io_code(e) >>> 0, text: String(e.message) };
  }
}

// from over to, at once for every reader
function filefx_rename(from, to) {
  const a = filefx_path(from);
  const b = filefx_path(to);
  if (a === null || b === null) {
    return io_fail(22);
  }
  return filefx_unit(() => require("fs").renameSync(a, b));
}

// mkdir -p; the path must end as a directory
function filefx_make_dirs(path) {
  const p = filefx_path(path);
  if (p === null) {
    return io_fail(22);
  }
  return filefx_unit(() => {
    const fs = require("fs");
    fs.mkdirSync(p, { recursive: true });
    if (!fs.lstatSync(p).isDirectory()) {
      throw Object.assign(new Error("not a directory"), { code: "ENOTDIR", errno: 20 });
    }
  });
}

function filefx_remove(path) {
  const p = filefx_path(path);
  if (p === null) {
    return io_fail(22);
  }
  return filefx_unit(() => require("fs").unlinkSync(p));
}

// Watchers. The JS lane runs its loop without yielding to the host's event
// loop, so fs.watch callbacks never run here; a watcher polls instead. Each
// wait scans the tree below the root, without following links, and
// compares it with the last scan: an entry that appeared, left, or changed
// its kind, size, modification time or inode is touched, and a file or
// directory that left and appeared elsewhere with the same inode is a
// rename. A scan sees every name below a moved directory, so this lane
// never drops reports; a change that keeps the size and the modification
// time within one tick of the clock goes unseen. A scan costs time in the
// size of the tree. A watcher is carried in a File handle whose value is a
// negative id, so it never names a real descriptor: File.close on it only
// fails, and FileFx.unwatch releases it.
const filefx_watches = new Map();
let filefx_last = 0;

// the entries below the directory at base (a Buffer), keyed by the latin1
// of their path relative to the root, '/' between segments
function filefx_scan_into(base, rel, out) {
  const fs = require("fs");
  let names;
  try {
    // Bun loses the names when withFileTypes meets encoding "buffer", so
    // each entry is probed on its own below.
    names = fs.readdirSync(base, { encoding: "buffer" });
  } catch (e) {
    return;
  }
  for (const n of names) {
    const name = Buffer.isBuffer(n) ? n : Buffer.from(String(n));
    const r = rel.length === 0 ? name : Buffer.concat([rel, Buffer.from("/"), name]);
    const full = Buffer.concat([base, Buffer.from("/"), name]);
    let st;
    try {
      st = fs.lstatSync(full);
    } catch (e) {
      continue;
    }
    const dir = st.isDirectory();
    out.set(r.toString("latin1"), { dir, file: st.isFile(), size: Number(st.size), time: st.mtimeMs, ino: String(st.ino) });
    if (dir) {
      filefx_scan_into(full, r, out);
    }
  }
}

// the scan of the tree below root, or null when root is not a directory
function filefx_scan(root) {
  try {
    if (!require("fs").lstatSync(root).isDirectory()) {
      return null;
    }
  } catch (e) {
    return null;
  }
  const out = new Map();
  filefx_scan_into(root, Buffer.alloc(0), out);
  return out;
}

function filefx_raw(key) {
  const b = Buffer.from(key, "latin1");
  return io_list(b, b.length);
}

// the reports from scan a to scan b
function filefx_diff(a, b) {
  const gone = [];
  const came = [];
  const out = [];
  for (const [k, v] of a) {
    const w = b.get(k);
    if (w === undefined || w.dir !== v.dir) {
      gone.push([k, v]);
    } else if (w.size !== v.size || w.time !== v.time || w.ino !== v.ino) {
      out.push({ $: CID(RawTouched), path: filefx_raw(k) });
    }
  }
  for (const [k, w] of b) {
    const v = a.get(k);
    if (v === undefined || w.dir !== v.dir) {
      came.push([k, w]);
    }
  }
  for (const [k, v] of gone) {
    const i = came.findIndex(([, w]) => w.ino === v.ino && w.dir === v.dir && v.ino !== "0");
    if (i >= 0) {
      const [k2] = came[i];
      came.splice(i, 1);
      out.push({ $: CID(RawRenamed), from: filefx_raw(k), to: filefx_raw(k2) });
    } else {
      out.push({ $: CID(RawTouched), path: filefx_raw(k) });
    }
  }
  for (const [k] of came) {
    out.push({ $: CID(RawTouched), path: filefx_raw(k) });
  }
  return out;
}

function filefx_watch(root) {
  const p = filefx_path(root);
  if (p === null) {
    return io_fail(22);
  }
  const scan = filefx_scan(p);
  if (scan === null) {
    return io_fail(2);
  }
  filefx_last -= 1;
  filefx_watches.set(filefx_last, { root: p, scan, dead: false });
  return io_done(filefx_last);
}

function filefx_list(xs) {
  let l = { $: CID(Nil) };
  for (let i = xs.length - 1; i >= 0; i -= 1) {
    l = { $: CID(Con), head: xs[i], tail: l };
  }
  return l;
}

// every regular file below root, as its path relative to the root; links
// are not followed and are skipped
function filefx_list_files(root) {
  const p = filefx_path(root);
  if (p === null) {
    return io_fail(22);
  }
  const scan = filefx_scan(p);
  if (scan === null) {
    return io_fail(20);
  }
  const out = [];
  for (const [k, v] of scan) {
    if (v.file) {
      out.push(filefx_raw(k));
    }
  }
  return io_done(filefx_list(out));
}

// one look: the reports since the last scan, RawRootGone once when the
// root stopped being a directory, and nothing after that
function filefx_look(x) {
  if (x.dead) {
    return [];
  }
  const scan = filefx_scan(x.root);
  if (scan === null) {
    x.dead = true;
    return [{ $: CID(RawRootGone) }];
  }
  const out = filefx_diff(x.scan, scan);
  x.scan = scan;
  return out;
}

function filefx_next(w, ms, k) {
  const x = filefx_watches.get(w);
  if (x === undefined) {
    return io_tup(w, io_fail(9));
  }
  const at = performance.now() + Number(ms);
  const more = () => {
    const out = filefx_look(x);
    if (out.length > 0 || performance.now() >= at) {
      return io_tup(w, io_done(filefx_list(out)));
    }
    io_park_on(undefined, false, k, more, Math.min(at, performance.now() + 200));
    return undefined;
  };
  return more();
}

function filefx_unwatch(w) {
  filefx_watches.delete(w);
  return { $: CID(Unit) };
}

// the open file f flushed to the disk
function filefx_sync(f) {
  try {
    require("fs").fsyncSync(f);
    return io_tup(f, io_done({ $: CID(Unit) }));
  } catch (e) {
    return io_tup(f, io_fail(io_code(e)));
  }
}

// the lock file at path, held by this process: the JS lane has no flock, so
// it writes its pid there and takes over only a lock whose process is gone
function filefx_lock(path) {
  const p = filefx_path(path);
  if (p === null) {
    return io_fail(22);
  }
  const fs = require("fs");
  try {
    let fd;
    try {
      fd = fs.openSync(p, "wx");
    } catch (e) {
      if (e.code !== "EEXIST") {
        throw e;
      }
      const old = parseInt(fs.readFileSync(p, "utf8"), 10);
      let alive = false;
      if (old > 0 && old !== process.pid) {
        try {
          process.kill(old, 0);
          alive = true;
        } catch (k) {
          alive = k.code === "EPERM";
        }
      }
      if (alive) {
        return io_fail(16);
      }
      fd = fs.openSync(p, "w");
    }
    fs.writeSync(fd, String(process.pid));
    fs.fsyncSync(fd);
    return io_done(fd);
  } catch (e) {
    return io_fail(io_code(e));
  }
}

io_eff(CID(FileFx.probe), filefx_probe);
io_eff(CID(FileFx.rename), filefx_rename);
io_eff(CID(FileFx.make_dirs), filefx_make_dirs);
io_eff(CID(FileFx.remove), filefx_remove);
io_eff(CID(FileFx.watch), filefx_watch);
io_eff(CID(FileFx.next), filefx_next);
io_eff(CID(FileFx.unwatch), filefx_unwatch);
io_eff(CID(FileFx.list), filefx_list_files);
io_eff(CID(FileFx.sync), filefx_sync);
io_eff(CID(FileFx.lock), filefx_lock);
