// File endpoint
// =============
//
// Probes, the rename of a Put, and the watcher of a root. Every path is
// the bytes of a List<U32>; a value past 255 or a NUL byte is EINVAL. On
// Windows the binary's manifest makes the narrow APIs UTF-8.

#ifndef _WIN32
#include <dirent.h>
#include <sys/file.h>
#include <sys/stat.h>
#ifdef __linux__
#include <sys/inotify.h>
#endif
#endif

// The path at f, with its length; NULL when it is not bytes.
static char* fx_path(Env e, Term t, u64* len) {
  char* p = io_cbuf(e, t, len, CID(Con));
  if (p != NULL && io_nul(p, *len)) {
    free(p);
    return NULL;
  }
  return p;
}

#ifdef _WIN32
// A Win32 error as the errno the Bend side reads: ENOENT only when the OS
// says the name is not there.
static u32 fx_win_errno(DWORD err) {
  switch (err) {
    case ERROR_FILE_NOT_FOUND:
    case ERROR_PATH_NOT_FOUND:
      return ENOENT;
    case ERROR_ACCESS_DENIED:
    case ERROR_SHARING_VIOLATION:
    case ERROR_LOCK_VIOLATION:
      return EACCES;
    case ERROR_ALREADY_EXISTS:
    case ERROR_FILE_EXISTS:
      return EEXIST;
    case ERROR_DIRECTORY:
      return ENOTDIR;
    case ERROR_INVALID_NAME:
      return EINVAL;
    default:
      return EIO;
  }
}
#endif

// Probe
// -----

// w->size: 0 file, 1 directory, 2 other; w->made: the device.
static void fx_probe_call(IoWork* w) {
#ifdef _WIN32
  WIN32_FILE_ATTRIBUTE_DATA a;
  if (!GetFileAttributesExA(w->data, GetFileExInfoStandard, &a)) {
    w->code = fx_win_errno(GetLastError());
    return;
  }
  DWORD at = a.dwFileAttributes;
  w->code = 0;
  w->size = (at & FILE_ATTRIBUTE_REPARSE_POINT) ? 2
    : (at & FILE_ATTRIBUTE_DIRECTORY) ? 1 : 0;
  w->made = 0;
#else
  struct stat st;
  if (lstat(w->data, &st) != 0) {
    w->code = (u32)errno;
    return;
  }
  w->code = 0;
  w->size = S_ISREG(st.st_mode) ? 0 : S_ISDIR(st.st_mode) ? 1 : 2;
  w->made = (intptr_t)(uint32_t)st.st_dev;
#endif
}

static Term fx_probe_pack(Env e, IoWork* w) {
  free(w->data);
  if (w->code == ENOENT) {
    return term_pak(CID(NotFound), 0);
  }
  if (w->code != 0) {
    const char* t = strerror((int)w->code);
    return io_node(e, CID(Failed), (Term)w->code, io_str(e, t, strlen(t)));
  }
  u64 k = w->size == 0 ? CID(KFile) : w->size == 1 ? CID(KDir) : CID(KOther);
  // Entry's constructors have no fields, so its value packs the index of
  // its constructor (KFile 0, KDir 1, KOther 2) beside the id.
  return io_node(e, CID(Found), term_pak(k, w->size), (Term)(uint32_t)w->made);
}

#ifdef CID(FileFx.probe)

Term filefx_probe_run(Env e, Term* f, IoWork* w) {
  u64 n;
  w->data = fx_path(e, f[0], &n);
  if (w->data == NULL) {
    const char* t = "the path is not bytes";
    return io_node(e, CID(Failed), (Term)EINVAL, io_str(e, t, strlen(t)));
  }
  return io_work(w, fx_probe_call, fx_probe_pack);
}

static void __attribute__((constructor)) filefx_probe_use(void) {
  io_eff(CID(FileFx.probe), filefx_probe_run);
}

#endif

// Rename, directories, removal
// ----------------------------

static Term fx_unit_pack(Env e, IoWork* w) {
  free(w->data);
  free(w->text);
  return io_res(e, w, term_pak(CID(Unit), 0));
}

// w->data over w->text, at once for every reader.
static void fx_rename_call(IoWork* w) {
#ifdef _WIN32
  w->code = MoveFileExA(w->data, w->text,
    MOVEFILE_REPLACE_EXISTING | MOVEFILE_WRITE_THROUGH)
    ? 0 : fx_win_errno(GetLastError());
#else
  io_sys_end(w, rename(w->data, w->text));
#endif
}

// the path is a directory now
static int fx_is_dir(const char* p) {
#ifdef _WIN32
  DWORD at = GetFileAttributesA(p);
  return at != INVALID_FILE_ATTRIBUTES && (at & FILE_ATTRIBUTE_DIRECTORY)
    && !(at & FILE_ATTRIBUTE_REPARSE_POINT);
#else
  struct stat st;
  return lstat(p, &st) == 0 && S_ISDIR(st.st_mode);
#endif
}

// mkdir -p: every prefix that ends before a separator, then the path. A
// prefix that fails is fine when it is a directory (a drive, the root, one
// made meanwhile); the path itself must end as a directory.
static void fx_make_dirs_call(IoWork* w) {
  char* p = w->data;
  u64   n = w->size;
  for (u64 i = 1; i <= n; i += 1) {
    if (i < n && p[i] != '/' && p[i] != '\\') {
      continue;
    }
    char c = p[i];
    p[i] = 0;
#ifdef _WIN32
    int ok = CreateDirectoryA(p, NULL) || fx_is_dir(p);
#else
    int ok = mkdir(p, 0755) == 0 || fx_is_dir(p);
#endif
    if (!ok && i == n) {
#ifdef _WIN32
      w->code = fx_win_errno(GetLastError());
#else
      w->code = errno == EEXIST ? ENOTDIR : (u32)errno;
#endif
      p[i] = c;
      return;
    }
    p[i] = c;
  }
  w->code = fx_is_dir(p) ? 0 : ENOTDIR;
}

static void fx_remove_call(IoWork* w) {
#ifdef _WIN32
  w->code = DeleteFileA(w->data) ? 0 : fx_win_errno(GetLastError());
#else
  io_sys_end(w, unlink(w->data));
#endif
}

// the unit effect of call on one path (and a second one, at f[1], when two)
static Term fx_paths_start(Env e, Term* f, IoWork* w, int two, IoCall call) {
  u64 n = 0, m = 0;
  w->data = fx_path(e, f[0], &n);
  w->text = two ? fx_path(e, f[1], &m) : NULL;
  w->size = n;
  if (w->data == NULL || (two && w->text == NULL)) {
    w->code = EINVAL;
    return fx_unit_pack(e, w);
  }
  return io_work(w, call, fx_unit_pack);
}

#ifdef CID(FileFx.rename)

Term filefx_rename_run(Env e, Term* f, IoWork* w) {
  return fx_paths_start(e, f, w, 1, fx_rename_call);
}

static void __attribute__((constructor)) filefx_rename_use(void) {
  io_eff(CID(FileFx.rename), filefx_rename_run);
}

#endif

#ifdef CID(FileFx.make_dirs)

Term filefx_make_dirs_run(Env e, Term* f, IoWork* w) {
  return fx_paths_start(e, f, w, 0, fx_make_dirs_call);
}

static void __attribute__((constructor)) filefx_make_dirs_use(void) {
  io_eff(CID(FileFx.make_dirs), filefx_make_dirs_run);
}

#endif

#ifdef CID(FileFx.remove)

Term filefx_remove_run(Env e, Term* f, IoWork* w) {
  return fx_paths_start(e, f, w, 0, fx_remove_call);
}

static void __attribute__((constructor)) filefx_remove_use(void) {
  io_eff(CID(FileFx.remove), filefx_remove_run);
}

#endif

// the tree at p removed, depth levels deep at most: a link (a reparse
// point on Windows) is removed as the link itself, never followed
static u32 fx_rmtree(char* p, int depth) {
  if (depth <= 0) {
    return ELOOP;
  }
#ifdef _WIN32
  DWORD a = GetFileAttributesA(p);
  if (a == INVALID_FILE_ATTRIBUTES) {
    return fx_win_errno(GetLastError());
  }
  if (a & FILE_ATTRIBUTE_READONLY) {
    SetFileAttributesA(p, a & ~FILE_ATTRIBUTE_READONLY);
  }
  if ((a & FILE_ATTRIBUTE_REPARSE_POINT) || !(a & FILE_ATTRIBUTE_DIRECTORY)) {
    BOOL ok = (a & FILE_ATTRIBUTE_DIRECTORY) ? RemoveDirectoryA(p) : DeleteFileA(p);
    return ok ? 0 : fx_win_errno(GetLastError());
  }
  size_t n = strlen(p);
  char* pat = malloc(n + 3);
  if (pat == NULL) {
    return ENOMEM;
  }
  memcpy(pat, p, n);
  memcpy(pat + n, "\\*", 3);
  WIN32_FIND_DATAA fd;
  HANDLE h = FindFirstFileA(pat, &fd);
  free(pat);
  if (h != INVALID_HANDLE_VALUE) {
    do {
      if (strcmp(fd.cFileName, ".") == 0 || strcmp(fd.cFileName, "..") == 0) {
        continue;
      }
      size_t m = strlen(fd.cFileName);
      char* q = malloc(n + m + 2);
      if (q == NULL) {
        FindClose(h);
        return ENOMEM;
      }
      memcpy(q, p, n);
      q[n] = '\\';
      memcpy(q + n + 1, fd.cFileName, m + 1);
      u32 code = fx_rmtree(q, depth - 1);
      free(q);
      if (code != 0) {
        FindClose(h);
        return code;
      }
    } while (FindNextFileA(h, &fd));
    FindClose(h);
  }
  return RemoveDirectoryA(p) ? 0 : fx_win_errno(GetLastError());
#else
  struct stat st;
  if (lstat(p, &st) != 0) {
    return (u32)errno;
  }
  if (!S_ISDIR(st.st_mode)) {
    return unlink(p) == 0 ? 0 : (u32)errno;
  }
  DIR* dir = opendir(p);
  if (dir == NULL) {
    return (u32)errno;
  }
  size_t n = strlen(p);
  struct dirent* ent;
  while ((ent = readdir(dir)) != NULL) {
    if (strcmp(ent->d_name, ".") == 0 || strcmp(ent->d_name, "..") == 0) {
      continue;
    }
    size_t m = strlen(ent->d_name);
    char* q = malloc(n + m + 2);
    if (q == NULL) {
      closedir(dir);
      return ENOMEM;
    }
    memcpy(q, p, n);
    q[n] = '/';
    memcpy(q + n + 1, ent->d_name, m + 1);
    u32 code = fx_rmtree(q, depth - 1);
    free(q);
    if (code != 0) {
      closedir(dir);
      return code;
    }
  }
  closedir(dir);
  return rmdir(p) == 0 ? 0 : (u32)errno;
#endif
}

// the directory w->data removed with its tree; a link there is refused
static void fx_remove_tree_call(IoWork* w) {
#ifdef _WIN32
  DWORD a = GetFileAttributesA(w->data);
  if (a == INVALID_FILE_ATTRIBUTES) {
    w->code = fx_win_errno(GetLastError());
    return;
  }
  if ((a & FILE_ATTRIBUTE_REPARSE_POINT) || !(a & FILE_ATTRIBUTE_DIRECTORY)) {
    w->code = (a & FILE_ATTRIBUTE_REPARSE_POINT) ? ELOOP : ENOTDIR;
    return;
  }
#else
  struct stat st;
  if (lstat(w->data, &st) != 0) {
    w->code = (u32)errno;
    return;
  }
  if (!S_ISDIR(st.st_mode)) {
    w->code = S_ISLNK(st.st_mode) ? ELOOP : ENOTDIR;
    return;
  }
#endif
  w->code = fx_rmtree(w->data, 64);
}

#ifdef CID(FileFx.remove_tree)

Term filefx_remove_tree_run(Env e, Term* f, IoWork* w) {
  return fx_paths_start(e, f, w, 0, fx_remove_tree_call);
}

static void __attribute__((constructor)) filefx_remove_tree_use(void) {
  io_eff(CID(FileFx.remove_tree), filefx_remove_tree_run);
}

#endif

// Sync and lock
// -------------

// the descriptor w->hand flushed to the disk
static void fx_sync_call(IoWork* w) {
#ifdef _WIN32
  HANDLE h = (HANDLE)_get_osfhandle((int)w->hand);
  w->code = h != INVALID_HANDLE_VALUE && FlushFileBuffers(h)
    ? 0 : fx_win_errno(GetLastError());
#else
  io_sys_end(w, fsync((int)w->hand));
#endif
}

static Term fx_sync_pack(Env e, IoWork* w) {
  return io_tup(e, io_hand(w->hand), io_res(e, w, term_pak(CID(Unit), 0)));
}

#ifdef CID(FileFx.sync)

Term filefx_sync_run(Env e, Term* f, IoWork* w) {
  w->hand = (intptr_t)io_hand_v(f[0]);
  return io_work(w, fx_sync_call, fx_sync_pack);
}

static void __attribute__((constructor)) filefx_sync_use(void) {
  io_eff(CID(FileFx.sync), filefx_sync_run);
}

#endif

// the lock file w->data, held alone: w->hand its descriptor. The handle is
// never closed on purpose; the OS releases the lock when the process ends.
static void fx_lock_call(IoWork* w) {
#ifdef _WIN32
  HANDLE h = CreateFileA(w->data, GENERIC_READ | GENERIC_WRITE, 0, NULL,
    OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, NULL);
  if (h == INVALID_HANDLE_VALUE) {
    DWORD er = GetLastError();
    w->code = er == ERROR_SHARING_VIOLATION ? EBUSY : fx_win_errno(er);
    return;
  }
  int fd = _open_osfhandle((intptr_t)h, 0);
  if (fd < 0) {
    CloseHandle(h);
    w->code = EIO;
    return;
  }
  w->hand = fd;
#else
  int fd = open(w->data, O_RDWR | O_CREAT, 0644);
  if (fd < 0) {
    w->code = (u32)errno;
    return;
  }
  if (flock(fd, LOCK_EX | LOCK_NB) != 0) {
    w->code = errno == EWOULDBLOCK ? EBUSY : (u32)errno;
    close(fd);
    return;
  }
  w->hand = fd;
#endif
}

static Term fx_lock_pack(Env e, IoWork* w) {
  free(w->data);
  if (w->code == EBUSY) {
    return io_fail(e, EBUSY, "another vend holds the journal");
  }
  return io_res(e, w, io_hand(w->hand));
}

#ifdef CID(FileFx.lock)

Term filefx_lock_run(Env e, Term* f, IoWork* w) {
  u64 n;
  w->data = fx_path(e, f[0], &n);
  if (w->data == NULL) {
    w->code = EINVAL;
    return fx_lock_pack(e, w);
  }
  return io_work(w, fx_lock_call, fx_lock_pack);
}

static void __attribute__((constructor)) filefx_lock_use(void) {
  io_eff(CID(FileFx.lock), filefx_lock_run);
}

#endif

// Reports
// -------
// A wait collects reports into a byte buffer on the helper thread, and its
// pack turns them into Raw terms: a tag byte (0 touched, 1 renamed, 2
// dropped, 3 root gone), then each path as a u32 length and its bytes.

// lost: a directory left, moved or vanished, so the names below it changed
// without reports of their own; the batch then ends with one "dropped".
typedef struct {
  char* buf;
  u64   len;
  u64   cap;
  int   lost;
} FxOut;

static void fx_out_bytes(FxOut* o, const void* p, u64 n) {
  if (o->len + n > o->cap) {
    o->cap = (o->len + n) * 2 + 64;
    o->buf = io_mem(realloc(o->buf, o->cap));
  }
  memcpy(o->buf + o->len, p, n);
  o->len += n;
}

static void fx_out_path(FxOut* o, const char* p, u32 n) {
  fx_out_bytes(o, &n, sizeof n);
  fx_out_bytes(o, p, n);
}

static void fx_out_touched(FxOut* o, const char* p, u32 n) {
  char t = 0;
  fx_out_bytes(o, &t, 1);
  fx_out_path(o, p, n);
}

static void fx_out_renamed(FxOut* o, const char* a, u32 an, const char* b, u32 bn) {
  char t = 1;
  fx_out_bytes(o, &t, 1);
  fx_out_path(o, a, an);
  fx_out_path(o, b, bn);
}

static void fx_out_tag(FxOut* o, char t) {
  fx_out_bytes(o, &t, 1);
}

// the batch, closed: one "dropped" at its end when a directory changed
static void fx_out_end(FxOut* o, IoWork* w) {
  if (o->lost) {
    fx_out_tag(o, 2);
  }
  w->data = o->buf;
  w->size = o->len;
}

// the Raw terms of the buffer, in order
static Term fx_reports(Env e, const char* p, u64 n) {
  u64   cnt = 0, cap = 16, at = 0;
  Term* xs  = io_mem(malloc(cap * sizeof(Term)));
  while (at < n) {
    char t = p[at++];
    Term x;
    if (t == 0 || t == 1) {
      u32 an;
      memcpy(&an, p + at, sizeof an);
      Term a = io_list(e, p + at + sizeof an, an);
      at += sizeof an + an;
      if (t == 0) {
        x = io_box(e, CID(RawTouched), a);
      } else {
        u32 bn;
        memcpy(&bn, p + at, sizeof bn);
        Term b = io_list(e, p + at + sizeof bn, bn);
        at += sizeof bn + bn;
        x = io_node(e, CID(RawRenamed), a, b);
      }
    } else {
      x = term_pak(t == 2 ? CID(RawLost) : CID(RawRootGone), 0);
    }
    if (cnt == cap) {
      cap *= 2;
      xs = io_mem(realloc(xs, cap * sizeof(Term)));
    }
    xs[cnt++] = x;
  }
  Term list = term_pak(CID(Nil), 0);
  for (u64 i = cnt; i > 0; i -= 1) {
    list = io_node(e, CID(Con), xs[i - 1], list);
  }
  free(xs);
  return list;
}

// Watchers
// --------
// A watcher is an OS descriptor (an inotify fd on Linux, a directory handle
// made into a CRT fd on Windows) carried in a File handle: user handle
// types are WONTFIX, a File handle owns one descriptor on both lanes, and
// FileFx.unwatch releases it with the state kept for it below. Each
// watcher keeps that state in a list keyed by its descriptor; waits on one
// watcher are sequential, since its handle is affine.

typedef struct FxWatch FxWatch;

struct FxWatch {
  int      fd;
  char*    root;
  int      dead;
#ifdef _WIN32
  HANDLE     dir;
  OVERLAPPED ov;
  int        pending;
  DWORD*     note;
#else
  int*   wds;
  char** rels;
  u32    nwd;
  u32    cap;
#endif
  FxWatch* next;
};

static pthread_mutex_t fx_lock = PTHREAD_MUTEX_INITIALIZER;
static FxWatch*        fx_watches;

static FxWatch* fx_find(int fd) {
  pthread_mutex_lock(&fx_lock);
  FxWatch* x = fx_watches;
  while (x != NULL && x->fd != fd) {
    x = x->next;
  }
  pthread_mutex_unlock(&fx_lock);
  return x;
}

static void fx_keep(FxWatch* x) {
  pthread_mutex_lock(&fx_lock);
  x->next    = fx_watches;
  fx_watches = x;
  pthread_mutex_unlock(&fx_lock);
}

static void fx_drop(FxWatch* x) {
  pthread_mutex_lock(&fx_lock);
  FxWatch** at = &fx_watches;
  while (*at != NULL && *at != x) {
    at = &(*at)->next;
  }
  if (*at == x) {
    *at = x->next;
  }
  pthread_mutex_unlock(&fx_lock);
}

// the path a/b, or b when a is empty
static char* fx_join(const char* a, const char* b, u64 bn) {
  u64   an = strlen(a);
  char* p  = io_mem(malloc(an + bn + 2));
  u64   k  = 0;
  if (an > 0) {
    memcpy(p, a, an);
    p[an] = '/';
    k     = an + 1;
  }
  memcpy(p + k, b, bn);
  p[k + bn] = 0;
  return p;
}

// List
// ----
// Every regular file below a root, as its path relative to the root, '/'
// between segments, without following links: a link or reparse point is
// skipped, and so is a directory that cannot be read. The buffer holds each
// path as a u32 length and its bytes.

static void fx_list_tree(const char* root, const char* rel, FxOut* o) {
  char* full = rel[0] ? fx_join(root, rel, strlen(rel)) : strdup(root);
#ifdef _WIN32
  char*            pat = fx_join(full, "*", 1);
  WIN32_FIND_DATAA fd;
  HANDLE           h = FindFirstFileA(pat, &fd);
  free(pat);
  if (h != INVALID_HANDLE_VALUE) {
    do {
      const char* n = fd.cFileName;
      if (strcmp(n, ".") == 0 || strcmp(n, "..") == 0) {
        continue;
      }
      char* sub = fx_join(rel, n, strlen(n));
      DWORD at  = fd.dwFileAttributes;
      if (at & FILE_ATTRIBUTE_REPARSE_POINT) {
        // a link: skipped
      } else if (at & FILE_ATTRIBUTE_DIRECTORY) {
        fx_list_tree(root, sub, o);
      } else {
        fx_out_path(o, sub, (u32)strlen(sub));
      }
      free(sub);
    } while (FindNextFileA(h, &fd));
    FindClose(h);
  }
#else
  DIR* d = opendir(full);
  if (d != NULL) {
    struct dirent* en;
    while ((en = readdir(d)) != NULL) {
      if (strcmp(en->d_name, ".") == 0 || strcmp(en->d_name, "..") == 0) {
        continue;
      }
      char*       sub  = fx_join(rel, en->d_name, strlen(en->d_name));
      char*       path = fx_join(root, sub, strlen(sub));
      struct stat st;
      if (lstat(path, &st) == 0) {
        if (S_ISDIR(st.st_mode)) {
          fx_list_tree(root, sub, o);
        } else if (S_ISREG(st.st_mode)) {
          fx_out_path(o, sub, (u32)strlen(sub));
        }
      }
      free(path);
      free(sub);
    }
    closedir(d);
  }
#endif
  free(full);
}

// w->data: the root; the paths go to w->text, w->size bytes long.
static void fx_list_call(IoWork* w) {
  FxOut o = { 0 };
  if (fx_is_dir(w->data)) {
    w->code = 0;
    fx_list_tree(w->data, "", &o);
  } else {
    w->code = ENOTDIR;
  }
  w->text = o.buf;
  w->size = o.len;
}

static Term fx_list_pack(Env e, IoWork* w) {
  const char* p   = w->text;
  u64         n   = w->size, at = 0, cnt = 0, cap = 16;
  Term*       xs  = io_mem(malloc(cap * sizeof(Term)));
  while (at < n) {
    u32 an;
    memcpy(&an, p + at, sizeof an);
    Term a = io_list(e, p + at + sizeof an, an);
    at += sizeof an + an;
    if (cnt == cap) {
      cap *= 2;
      xs = io_mem(realloc(xs, cap * sizeof(Term)));
    }
    xs[cnt++] = a;
  }
  Term list = term_pak(CID(Nil), 0);
  for (u64 i = cnt; i > 0; i -= 1) {
    list = io_node(e, CID(Con), xs[i - 1], list);
  }
  free(xs);
  free(w->data);
  free(w->text);
  return io_res(e, w, list);
}

#ifdef CID(FileFx.list)

Term filefx_list_run(Env e, Term* f, IoWork* w) {
  u64 n;
  w->data = fx_path(e, f[0], &n);
  w->text = NULL;
  w->size = 0;
  if (w->data == NULL) {
    w->code = EINVAL;
    return fx_list_pack(e, w);
  }
  return io_work(w, fx_list_call, fx_list_pack);
}

static void __attribute__((constructor)) filefx_list_use(void) {
  io_eff(CID(FileFx.list), filefx_list_run);
}

#endif

#if defined(__linux__)

#define FX_MASK (IN_CREATE | IN_DELETE | IN_MODIFY | IN_CLOSE_WRITE \
  | IN_ATTRIB | IN_MOVED_FROM | IN_MOVED_TO | IN_DELETE_SELF | IN_MOVE_SELF \
  | IN_ONLYDIR | IN_DONT_FOLLOW)

static const char* fx_rel(FxWatch* x, int wd) {
  for (u32 i = 0; i < x->nwd; i += 1) {
    if (x->wds[i] == wd) {
      return x->rels[i];
    }
  }
  return NULL;
}

static void fx_forget(FxWatch* x, u32 i) {
  free(x->rels[i]);
  x->nwd    -= 1;
  x->wds[i]  = x->wds[x->nwd];
  x->rels[i] = x->rels[x->nwd];
}

// rel starts with the directory dir, or is it
static int fx_under(const char* rel, const char* dir) {
  u64 n = strlen(dir);
  return strncmp(rel, dir, n) == 0 && (rel[n] == 0 || rel[n] == '/');
}

// Watches the directory rel and every directory below it; reports each
// entry it finds when found, so creations that came before the watch are
// not lost.
static void fx_add_tree(FxWatch* x, const char* rel, FxOut* found) {
  char* full = rel[0] ? fx_join(x->root, rel, strlen(rel)) : strdup(x->root);
  int   wd   = inotify_add_watch(x->fd, full, FX_MASK);
  if (wd >= 0) {
    if (x->nwd == x->cap) {
      x->cap  = x->cap * 2 + 8;
      x->wds  = io_mem(realloc(x->wds, x->cap * sizeof(int)));
      x->rels = io_mem(realloc(x->rels, x->cap * sizeof(char*)));
    }
    x->wds[x->nwd]  = wd;
    x->rels[x->nwd] = strdup(rel);
    x->nwd         += 1;
    DIR* d = opendir(full);
    if (d != NULL) {
      struct dirent* en;
      while ((en = readdir(d)) != NULL) {
        if (strcmp(en->d_name, ".") == 0 || strcmp(en->d_name, "..") == 0) {
          continue;
        }
        char* sub = fx_join(rel, en->d_name, strlen(en->d_name));
        if (found != NULL) {
          fx_out_touched(found, sub, (u32)strlen(sub));
        }
        if (en->d_type == DT_DIR) {
          fx_add_tree(x, sub, found);
        }
        free(sub);
      }
      closedir(d);
    }
  }
  free(full);
}

// Moves every watch of the directory from to the directory to.
static void fx_move_tree(FxWatch* x, const char* from, const char* to) {
  u64 fn = strlen(from);
  for (u32 i = 0; i < x->nwd; i += 1) {
    if (fx_under(x->rels[i], from)) {
      char* rest = x->rels[i] + fn;
      char* re   = io_mem(malloc(strlen(to) + strlen(rest) + 1));
      strcpy(re, to);
      strcat(re, rest);
      free(x->rels[i]);
      x->rels[i] = re;
    }
  }
}

// Drops every watch of the directory dir and below.
static void fx_drop_tree(FxWatch* x, const char* dir) {
  for (u32 i = 0; i < x->nwd;) {
    if (fx_under(x->rels[i], dir)) {
      inotify_rm_watch(x->fd, x->wds[i]);
      fx_forget(x, i);
    } else {
      i += 1;
    }
  }
}

// One wait: up to ms for the first report, then everything queued. A
// rename pairs its two halves by cookie within the batch; a half without
// its pair is a touch (it left or entered the watched tree).
static void fx_next_call(IoWork* w) {
  FxWatch* x = (FxWatch*)w->made;
  FxOut    o = { 0 };
  w->code    = 0;
  if (x->dead) {
    w->data = NULL;
    w->size = 0;
    return;
  }
  struct pollfd pf = { .fd = x->fd, .events = POLLIN };
  int           r;
  do {
    r = poll(&pf, 1, (int)w->word);
  } while (r < 0 && errno == EINTR);
  if (r < 0) {
    w->code = (u32)errno;
    return;
  }
  char*    from  = NULL;
  uint32_t ck    = 0;
  int      fdir  = 0;
  char     buf[65536] __attribute__((aligned(__alignof__(struct inotify_event))));
  while (r > 0) {
    ssize_t n = read(x->fd, buf, sizeof buf);
    if (n <= 0) {
      break;
    }
    for (char* p = buf; p < buf + n;) {
      struct inotify_event* ev = (struct inotify_event*)p;
      p += sizeof *ev + ev->len;
      if (ev->mask & IN_Q_OVERFLOW) {
        fx_out_tag(&o, 2);
        continue;
      }
      const char* rel = fx_rel(x, ev->wd);
      if (rel == NULL) {
        continue;
      }
      int root = rel[0] == 0;
      if (ev->mask & (IN_DELETE_SELF | IN_MOVE_SELF | IN_UNMOUNT | IN_IGNORED)) {
        if (root) {
          fx_out_tag(&o, 3);
          x->dead = 1;
          break;
        }
        continue;
      }
      if (ev->len == 0) {
        continue;
      }
      u64   nn   = strlen(ev->name);
      char* path = fx_join(rel, ev->name, nn);
      int   dir  = (ev->mask & IN_ISDIR) != 0;
      if (from != NULL && !((ev->mask & IN_MOVED_TO) && ev->cookie == ck)) {
        fx_out_touched(&o, from, (u32)strlen(from));
        if (fdir) {
          fx_drop_tree(x, from);
          o.lost = 1;
        }
        free(from);
        from = NULL;
      }
      if (ev->mask & IN_MOVED_FROM) {
        from = path;
        ck   = ev->cookie;
        fdir = dir;
        continue;
      }
      if (ev->mask & IN_MOVED_TO) {
        if (from != NULL) {
          fx_out_renamed(&o, from, (u32)strlen(from), path, (u32)strlen(path));
          if (dir) {
            fx_move_tree(x, from, path);
            o.lost = 1;
          }
          free(from);
          from = NULL;
        } else {
          fx_out_touched(&o, path, (u32)strlen(path));
          if (dir) {
            fx_add_tree(x, path, &o);
          }
        }
        free(path);
        continue;
      }
      fx_out_touched(&o, path, (u32)strlen(path));
      if (dir && (ev->mask & IN_CREATE)) {
        fx_add_tree(x, path, &o);
      }
      free(path);
    }
    if (x->dead) {
      break;
    }
    struct pollfd more = { .fd = x->fd, .events = POLLIN };
    r = poll(&more, 1, 0);
  }
  if (from != NULL) {
    fx_out_touched(&o, from, (u32)strlen(from));
    if (fdir) {
      fx_drop_tree(x, from);
      o.lost = 1;
    }
    free(from);
  }
  fx_out_end(&o, w);
}

static void fx_watch_call(IoWork* w) {
  int fd = inotify_init1(IN_NONBLOCK | IN_CLOEXEC);
  if (fd < 0) {
    w->code = (u32)errno;
    return;
  }
  FxWatch* x = io_mem(calloc(1, sizeof *x));
  x->fd   = fd;
  x->root = w->data;
  w->data = NULL;
  fx_add_tree(x, "", NULL);
  if (x->nwd == 0) {
    w->code = (u32)errno;
    close(fd);
    free(x->root);
    free(x);
    return;
  }
  fx_keep(x);
  w->code = 0;
  w->hand = fd;
}

static void fx_unwatch(FxWatch* x) {
  for (u32 i = 0; i < x->nwd; i += 1) {
    free(x->rels[i]);
  }
  free(x->wds);
  free(x->rels);
  close(x->fd);
}

#elif defined(_WIN32)

#define FX_NOTE_BYTES 65536
#define FX_FILTER (FILE_NOTIFY_CHANGE_FILE_NAME | FILE_NOTIFY_CHANGE_DIR_NAME \
  | FILE_NOTIFY_CHANGE_SIZE | FILE_NOTIFY_CHANGE_LAST_WRITE \
  | FILE_NOTIFY_CHANGE_CREATION | FILE_NOTIFY_CHANGE_ATTRIBUTES)

// the UTF-8 of a UTF-16 name of n bytes, with '\' as '/'
static char* fx_utf8(const WCHAR* s, DWORD n, u32* len) {
  int   k = WideCharToMultiByte(CP_UTF8, 0, s, (int)(n / sizeof(WCHAR)), NULL, 0, NULL, NULL);
  char* p = io_mem(malloc((u64)k + 1));
  WideCharToMultiByte(CP_UTF8, 0, s, (int)(n / sizeof(WCHAR)), p, k, NULL, NULL);
  for (int i = 0; i < k; i += 1) {
    p[i] = p[i] == '\\' ? '/' : p[i];
  }
  p[k] = 0;
  *len = (u32)k;
  return p;
}

// Asks the OS for the next batch of changes.
static int fx_ask(FxWatch* x) {
  ResetEvent(x->ov.hEvent);
  x->pending = ReadDirectoryChangesW(x->dir, x->note, FX_NOTE_BYTES, TRUE,
    FX_FILTER, NULL, &x->ov, NULL);
  return x->pending;
}

// One batch that the OS finished: its reports into o.
static void fx_batch(FxWatch* x, FxOut* o) {
  DWORD got = 0;
  x->pending = 0;
  if (!GetOverlappedResult(x->dir, &x->ov, &got, FALSE)) {
    if (GetLastError() == ERROR_NOTIFY_ENUM_DIR) {
      o->lost = 1;
    } else {
      fx_out_tag(o, 3);
      x->dead = 1;
    }
    return;
  }
  if (got == 0) {
    o->lost = 1;
    return;
  }
  char* from = NULL;
  u32   fn   = 0;
  for (char* p = (char*)x->note;;) {
    FILE_NOTIFY_INFORMATION* fi = (FILE_NOTIFY_INFORMATION*)p;
    u32   n;
    char* path = fx_utf8(fi->FileName, fi->FileNameLength, &n);
    if (fi->Action == FILE_ACTION_RENAMED_OLD_NAME) {
      if (from != NULL) {
        fx_out_touched(o, from, fn);
        free(from);
        o->lost = 1;
      }
      from = path;
      fn   = n;
    } else if (fi->Action == FILE_ACTION_RENAMED_NEW_NAME && from != NULL) {
      fx_out_renamed(o, from, fn, path, n);
      char* full = fx_join(x->root, path, n);
      o->lost |= fx_is_dir(full);
      free(full);
      free(from);
      free(path);
      from = NULL;
    } else {
      // Windows does not say whether a removed name was a directory.
      o->lost |= fi->Action == FILE_ACTION_REMOVED;
      fx_out_touched(o, path, n);
      free(path);
    }
    if (fi->NextEntryOffset == 0) {
      break;
    }
    p += fi->NextEntryOffset;
  }
  if (from != NULL) {
    fx_out_touched(o, from, fn);
    free(from);
    o->lost = 1;
  }
}

// One wait: up to ms for a first batch, then every batch already done. An
// empty batch, or ERROR_NOTIFY_ENUM_DIR, means the OS dropped changes; a
// failed request means the root is gone.
static void fx_next_call(IoWork* w) {
  FxWatch* x = (FxWatch*)w->made;
  FxOut    o = { 0 };
  w->code    = 0;
  for (DWORD ms = w->word; !x->dead; ms = 0) {
    if (!x->pending && !fx_ask(x)) {
      fx_out_tag(&o, 3);
      x->dead = 1;
      break;
    }
    if (WaitForSingleObject(x->ov.hEvent, ms) != WAIT_OBJECT_0) {
      break;
    }
    fx_batch(x, &o);
  }
  fx_out_end(&o, w);
}

static void fx_watch_call(IoWork* w) {
  HANDLE h = CreateFileA(w->data, FILE_LIST_DIRECTORY,
    FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, NULL,
    OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OVERLAPPED, NULL);
  if (h == INVALID_HANDLE_VALUE) {
    w->code = fx_win_errno(GetLastError());
    return;
  }
  FxWatch* x = io_mem(calloc(1, sizeof *x));
  x->dir       = h;
  x->root      = w->data;
  w->data      = NULL;
  x->note      = io_mem(malloc(FX_NOTE_BYTES));
  x->ov.hEvent = CreateEventA(NULL, TRUE, FALSE, NULL);
  int fd       = _open_osfhandle((intptr_t)h, 0);
  if (x->ov.hEvent == NULL || fd < 0 || !fx_ask(x)) {
    w->code = fx_win_errno(GetLastError());
    if (x->ov.hEvent != NULL) {
      CloseHandle(x->ov.hEvent);
    }
    if (fd >= 0) {
      _close(fd);
    } else {
      CloseHandle(h);
    }
    free(x->note);
    free(x->root);
    free(x);
    return;
  }
  x->fd = fd;
  fx_keep(x);
  w->code = 0;
  w->hand = fd;
}

static void fx_unwatch(FxWatch* x) {
  if (x->pending) {
    DWORD got;
    CancelIoEx(x->dir, &x->ov);
    GetOverlappedResult(x->dir, &x->ov, &got, TRUE);
  }
  CloseHandle(x->ov.hEvent);
  free(x->note);
  _close(x->fd);
}

#else

// Watching is not supported on this OS yet: a watch fails with ENOSYS.
static void fx_next_call(IoWork* w) {
  w->code = ENOSYS;
}

static void fx_watch_call(IoWork* w) {
  w->code = ENOSYS;
}

static void fx_unwatch(FxWatch* x) {
}

#endif

static Term fx_watch_pack(Env e, IoWork* w) {
  free(w->data);
  if (w->code == ENOSYS) {
    return io_fail(e, ENOSYS, "watching is not supported on this OS yet");
  }
  return io_res(e, w, io_hand(w->hand));
}

static Term fx_next_pack(Env e, IoWork* w) {
  Term r = w->code ? io_fail(e, w->code, NULL)
    : io_done(e, fx_reports(e, w->data, w->size));
  free(w->data);
  return io_tup(e, io_hand(w->hand), r);
}

#ifdef CID(FileFx.watch)

Term filefx_watch_run(Env e, Term* f, IoWork* w) {
  u64 n;
  w->data = fx_path(e, f[0], &n);
  if (w->data == NULL) {
    w->code = EINVAL;
    return fx_watch_pack(e, w);
  }
  return io_work(w, fx_watch_call, fx_watch_pack);
}

static void __attribute__((constructor)) filefx_watch_use(void) {
  io_eff(CID(FileFx.watch), filefx_watch_run);
}

#endif

#ifdef CID(FileFx.next)

Term filefx_next_run(Env e, Term* f, IoWork* w) {
  w->hand  = (intptr_t)io_hand_v(f[0]);
  w->word  = (u32)f[1];
  w->data  = NULL;
  w->size  = 0;
  FxWatch* x = fx_find((int)w->hand);
  if (x == NULL) {
    w->code = EBADF;
    return fx_next_pack(e, w);
  }
  w->made = (intptr_t)x;
  return io_work(w, fx_next_call, fx_next_pack);
}

static void __attribute__((constructor)) filefx_next_use(void) {
  io_eff(CID(FileFx.next), filefx_next_run);
}

#endif

#ifdef CID(FileFx.unwatch)

Term filefx_unwatch_run(Env e, Term* f, IoWork* w) {
  FxWatch* x = fx_find((int)io_hand_v(f[0]));
  if (x != NULL) {
    fx_drop(x);
    fx_unwatch(x);
    free(x->root);
    free(x);
  }
  return term_pak(CID(Unit), 0);
}

static void __attribute__((constructor)) filefx_unwatch_use(void) {
  io_eff(CID(FileFx.unwatch), filefx_unwatch_run);
}

#endif
