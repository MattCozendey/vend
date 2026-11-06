// Standard input
// ==============
//
// The JS lane of stdin.c: every byte of standard input, read to its end;
// or the next line, with its line feed. The JS lane blocks while it reads,
// so a line read first writes out what the program printed before it.

function stdin_read_all() {
  try {
    const b = require("fs").readFileSync(0);
    return io_done(io_list(b, b.length));
  } catch (e) {
    return io_fail(io_code(e));
  }
}

io_eff(CID(Stdin.read_all), stdin_read_all);

let stdin_held = Buffer.alloc(0);
let stdin_ended = false;

function stdin_read_line() {
  if (typeof io_sync === "function") {
    io_sync();
  }
  const fs = require("fs");
  for (;;) {
    const at = stdin_held.indexOf(10);
    if (at >= 0 || stdin_ended) {
      const end = at >= 0 ? at + 1 : stdin_held.length;
      const line = stdin_held.subarray(0, end);
      stdin_held = stdin_held.subarray(end);
      return io_done(io_list(line, line.length));
    }
    const chunk = Buffer.alloc(65536);
    try {
      const n = fs.readSync(0, chunk, 0, chunk.length, null);
      if (n === 0) {
        stdin_ended = true;
      } else {
        stdin_held = Buffer.concat([stdin_held, chunk.subarray(0, n)]);
      }
    } catch (e) {
      if (e.code === "EOF") {
        stdin_ended = true;
      } else if (e.code !== "EAGAIN") {
        return io_fail(io_code(e));
      }
    }
  }
}

io_eff(CID(Stdin.read_line), stdin_read_line);
