// Standard input
// ==============
//
// Stdin.read_all: every byte of standard input, read to its end on an IO
// helper thread. Stdin.read_line: the bytes up to and with the next line
// feed, or the last bytes before the end; none at the end. On Windows the
// stream is put in binary mode first, so no CR LF is turned into LF and no
// Ctrl-Z ends it early.

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

static void stdin_read_call(IoWork* w) {
#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
#endif
  u64   cap = 65536, n = 0;
  char* b   = io_mem(malloc(cap));
  w->code   = 0;
  for (;;) {
    if (n == cap) {
      cap *= 2;
      b = io_mem(realloc(b, cap));
    }
    size_t got = fread(b + n, 1, cap - n, stdin);
    n += got;
    if (got == 0) {
      if (ferror(stdin)) {
        w->code = EIO;
      }
      break;
    }
  }
  w->text = b;
  w->size = n;
}

static void stdin_line_call(IoWork* w) {
#ifdef _WIN32
  _setmode(_fileno(stdin), _O_BINARY);
#endif
  u64   cap = 256, n = 0;
  char* b   = io_mem(malloc(cap));
  w->code   = 0;
  for (;;) {
    int c = fgetc(stdin);
    if (c == EOF) {
      if (ferror(stdin)) {
        w->code = EIO;
      }
      break;
    }
    if (n == cap) {
      cap *= 2;
      b = io_mem(realloc(b, cap));
    }
    b[n++] = (char)c;
    if (c == '\n') {
      break;
    }
  }
  w->text = b;
  w->size = n;
}

static Term stdin_read_pack(Env e, IoWork* w) {
  Term t = io_list(e, w->text, w->size);
  free(w->text);
  return io_res(e, w, t);
}

#ifdef CID(Stdin.read_all)

Term stdin_read_all_run(Env e, Term* f, IoWork* w) {
  w->text = NULL;
  w->size = 0;
  return io_work(w, stdin_read_call, stdin_read_pack);
}

static void __attribute__((constructor)) stdin_read_all_use(void) {
  io_eff(CID(Stdin.read_all), stdin_read_all_run);
}

#endif

#ifdef CID(Stdin.read_line)

Term stdin_read_line_run(Env e, Term* f, IoWork* w) {
  w->text = NULL;
  w->size = 0;
  return io_work(w, stdin_line_call, stdin_read_pack);
}

static void __attribute__((constructor)) stdin_read_line_use(void) {
  io_eff(CID(Stdin.read_line), stdin_read_line_run);
}

#endif
