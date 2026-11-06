// Standard input
// ==============
//
// The JS lane of stdin.c: every byte of standard input, read to its end.
// The JS lane blocks while it reads.

function stdin_read_all() {
  try {
    const b = require("fs").readFileSync(0);
    return io_done(io_list(b, b.length));
  } catch (e) {
    return io_fail(io_code(e));
  }
}

io_eff(CID(Stdin.read_all), stdin_read_all);
