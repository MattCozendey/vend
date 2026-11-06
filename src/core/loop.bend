import Base
import ../endpoints/file/impl.bend as FileImpl
import ../endpoints/file/spec.bend as File
import ../endpoints/spec.bend as Ep
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../journal/impl.bend as JournalImpl
import ../journal/spec.bend as Journal
import ../shared.bend as Shared
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text
import ./impl.bend as Impl
import ./spec.bend as Spec

# The loop: all of the core's IO, for the file endpoint. It reads the
# space of the root (or makes one), takes the user's journal (locked, its
# torn tail cut) and restores the core from it, watches the root, lists it
# and fetches every file it knows so that what changed while it was off
# gets versioned, then waits for reports. Each input goes through
# Spec.Core.step. The records of a step go to the journal, which is synced
# before anything else of that step happens; then each command goes to the
# endpoint, whose answer is the next input, and every other output goes to
# the front's report, so the loop prints nothing itself. Bend needs every
# loop to end: the loop counts down waits (each at most half a second), and
# the inputs of one wait count down a budget of steps.

# the most steps that the inputs of one wait may take
def Loop.budget() -> Nat:
  1000000n

# how long one wait lasts at most, in milliseconds
def Loop.wait_ms() -> U32:
  500

# the text of an error
def Loop.why(e: U32 & String) -> String:
  (c, t) = e
  t

# the inputs of the signals about the file at p
def Loop.about(+p: String, ss: List<&2, Ep.Signal>) -> List<&2, Spec.Input>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      Spec.Noticed{p, s} <> Loop.about(p, t)

# the inputs of signal s for every path of ps
def Loop.each(ps: List<&2, String>, +s: Ep.Signal) -> List<&2, Spec.Input>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Spec.Noticed{p, s} <> Loop.each(t, s)

# the paths of the files whose streams the core keeps
def Loop.known(c: Spec.Core) -> List<&2, String>:
  match c:
    case Spec.Core{m, s, h, l, ss, ms, ns}:
      Shared.Table.keys(Ep.Stream, ss)

# p is the space file of a directory below the root: it starts another
# space there
def Loop.is_nested(p: String) -> Bool:
  String.ends_with(p, String.append("/", Spec.Mount.space_file()))

# the input of signal s about the file at p, after a Nested input for the
# directory of p when p is the space file of another space
def Loop.noticed(+p: String, +s: Ep.Signal) -> List<&2, Spec.Input>:
  dir = String.take(p, Nat.sub(String.length(p), 1n+String.length(Spec.Mount.space_file())))
  Shared.Bool.when(
    List<&2, Spec.Input>,
    Loop.is_nested(p),
    u => [Spec.Nested{dir}, Spec.Noticed{p, s}],
    u => [Spec.Noticed{p, s}]
  )

# the inputs of the notices: AllOverflowed asks every known resource to
# fetch again (again: a hint for each), and AllLost makes every known
# resource unreachable
def Loop.inputs(
  ns: List<&2, File.Notice>,
  +known: List<&2, String>,
  +again: List<&2, Spec.Input>
) -> List<&2, Spec.Input>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{File.About{p, s}, t}:
      List.append(&2, Spec.Input, Loop.noticed(p, s), Loop.inputs(t, known, again))
    case Con{File.Moved{a, b}, t}:
      Spec.Moved{a, b} <> Loop.inputs(t, known, again)
    case Con{File.AllOverflowed{}, t}:
      List.append(&2, Spec.Input, again, Loop.inputs(t, known, again))
    case Con{File.AllLost{why}, t}:
      List.append(
        &2,
        Spec.Input,
        Loop.each(known, Ep.Reached{Ep.Unreachable{why}}),
        Loop.inputs(t, known, again)
      )

# some notice says that reports were lost
def Loop.overflowed(ns: List<&2, File.Notice>) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case Con{File.AllOverflowed{}, t}:
      True{}
    case Con{n, t}:
      Loop.overflowed(t)

# the paths below the root when reports were lost, so files that came
# without a report of their own (an unpaired rename, say) get fetched too;
# none otherwise
def Loop.relist(root: File.Root, lost: Bool) -> IO(List<&2, String>):
  match lost:
    case False{}:
      IO.pure(List<&2, String>, [])
    case True{}:
      FileImpl.FileEp.list(root)

# a hint for each path, so the core fetches what it tracks, with the
# Nested inputs of the space files of other spaces
def Loop.hints(ps: List<&2, String>) -> List<&2, Spec.Input>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      List.append(&2, Spec.Input, Loop.noticed(p, Ep.Hinted{}), Loop.hints(t))

# the inputs that carrying out the output o gives: a command goes to the
# endpoint and its answer comes back; anything else is reported
def Loop.carry(
  ~report: Spec.Output -> IO(Unit),
  root: File.Root,
  o: Spec.Output
) -> IO(List<&2, Spec.Input>):
  match o:
    case Spec.Command{+p, Ep.Fetch{}}:
      do IO<List<&2, Spec.Input>>:
        s: Ep.Signal <- FileImpl.FileEp.fetch(root, p)
        return [Spec.Noticed{p, s}]
    case Spec.Command{+p, Ep.Put{b, e}}:
      do IO<List<&2, Spec.Input>>:
        ss: List<&2, Ep.Signal> <- FileImpl.FileEp.put(root, p, b, e)
        return Loop.about(p, ss)
    case Spec.Logged{r}:
      IO.pure(List<&2, Spec.Input>, [])
    case x:
      do IO<List<&2, Spec.Input>>:
        report(x)
        return []

# the inputs that carrying out the outputs gives, in order
def Loop.carry_all(
  ~report: Spec.Output -> IO(Unit),
  +root: File.Root,
  os: List<&2, Spec.Output>
) -> IO(List<&2, Spec.Input>):
  match os:
    case Nil{}:
      IO.pure(List<&2, Spec.Input>, [])
    case Con{o, t}:
      do IO<List<&2, Spec.Input>>:
        a: List<&2, Spec.Input> <- Loop.carry(~report, root, o)
        b: List<&2, Spec.Input> <- Loop.carry_all(~report, root, t)
        return List.append(&2, Spec.Input, a, b)

# k of the core and the outputs of a step
def Loop.split(
  s: Spec.Stepped,
  k: Spec.Core -> List<&2, Spec.Output> -> IO(Drained)
) -> IO(Drained):
  match s:
    case Spec.Stepped{c, os}:
      k(c, os)

# The end of a drain: the core and the journal, or why the journal failed
# (then nothing after the failed write was carried out or reported).
type Drained is Type:
  Ran{core: Spec.Core, journal: File}
  Broke{why: String}

# the journal synced after its write, unless the write failed
def Loop.logged.sync(
  jw: File & Result<&1, &1, U32 & String, Unit>
) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  (j, w) = jw
  match w:
    case Fail{e}:
      IO.pure(File & Result<&1, &1, U32 & String, Unit>, (j, Fail{e}))
    case Done{u}:
      File.FileFx.sync(j)

# the journal j after the records rs: appended, then synced to the disk;
# nothing to do for no records
def Loop.log(
  j: File,
  rs: List<&2, Journal.Record>
) -> IO(File & Result<&1, &1, U32 & String, Unit>):
  match rs:
    case Nil{}:
      IO.pure(File & Result<&1, &1, U32 & String, Unit>, (j, Done{Unit{}}))
    case Con{r, t}:
      do IO<File & Result<&1, &1, U32 & String, Unit>>:
        jw: File
          & Result<
            &1,
            &1,
            U32 & String,
            Unit> <- File.write_bytes(j, Journal.Record.encode_all(Con{r, t}))
        Loop.logged.sync(jw)

# k of the journal once its records are on disk, or Broke
def Loop.logged(
  r: File & Result<&1, &1, U32 & String, Unit>,
  k: File -> IO(Drained)
) -> IO(Drained):
  (j, w) = r
  match w:
    case Fail{e}:
      IO.pure(Drained, Broke{Loop.why(e)})
    case Done{u}:
      k(j)

# the core after the inputs of queue, and the inputs their outputs give,
# in order; fuel bounds the steps. The records of each step are on disk
# before its other outputs are carried out.
def Loop.drain(
  ~report: Spec.Output -> IO(Unit),
  fuel: Nat,
  +root: File.Root,
  j: File,
  c: Spec.Core,
  queue: List<&2, Spec.Input>
) -> IO(Drained):
  match fuel:
    case 0n:
      IO.pure(Drained, Ran{c, j})
    case 1n+f:
      match queue:
        case Nil{}:
          IO.pure(Drained, Ran{c, j})
        case Con{i, t}:
          Loop.split(Spec.Core.step(c, i), c2 => +os => do IO<Drained>:
            jr: File & Result<&1, &1, U32 & String, Unit> <- Loop.log(j, Spec.Output.logged(os))
            Loop.logged(jr, j2 => do IO<Drained>:
            more: List<&2, Spec.Input> <- Loop.carry_all(~report, root, os)
            Loop.drain(~report, f, root, j2, c2, List.append(&2, Spec.Input, t, more))))

# k of the watcher and the notices of a wait, or the text of its failure
def Loop.waited(
  r: File & Result<&1, &1, U32 & String, List<&2, File.Notice>>,
  k: File -> List<&2, File.Notice> -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  (w, res) = r
  match res:
    case Fail{e}:
      do IO<Maybe<&2, String>>:
        FileImpl.FileEp.unwatch(w)
        return Some{Loop.why(e)}
    case Done{ns}:
      k(w, ns)

# the next waits after a drain, or the journal's failure
def Loop.drained(
  d: Drained,
  w: File,
  k: File -> File -> Spec.Core -> IO(Maybe<&2, String>)
) -> IO(Maybe<&2, String>):
  match d:
    case Ran{c, j}:
      k(w, j, c)
    case Broke{why}:
      do IO<Maybe<&2, String>>:
        FileImpl.FileEp.unwatch(w)
        return Some{"the journal could not be written: " ++ why}

# the waits of the watcher w, at most waits of them, with the core c and
# the journal j; None when the waits ran out, or the text of a failed wait
def Loop.go(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  w: File,
  j: File,
  +c: Spec.Core
) -> IO(Maybe<&2, String>):
  match waits:
    case 0n:
      do IO<Maybe<&2, String>>:
        FileImpl.FileEp.unwatch(w)
        return None{}
    case 1n+f:
      do IO<Maybe<&2, String>>:
        r: File
          & Result<
            &1,
            &1,
            U32 & String,
            List<&2, File.Notice>> <- FileImpl.FileEp.next(w, Loop.wait_ms())
        Loop.waited(r, w2 => +ns => do IO<Maybe<&2, String>>:
          listed: List<&2, String> <- Loop.relist(root, Loop.overflowed(ns))
          ins: List<&2, Spec.Input> = List.append(&2, Spec.Input, Loop.inputs(ns, Loop.known(c), Loop.each(Loop.known(c), Ep.Hinted{})), Loop.hints(listed))
          d: Drained <- Loop.drain(~report, Loop.budget(), root, j, c, ins)
          Loop.drained(d, w2, w3 => j2 => c2 => Loop.go(~report, f, root, w3, j2, c2)))

# the loop once the watcher of the root started: list the root, fetch what
# is listed and every file the restored core knows (so what changed or went
# away while the loop was off gets versioned), then wait
def Loop.started(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  j: File,
  +c: Spec.Core,
  wr: Result<&1, &1, U32 & String, File>
) -> IO(Maybe<&2, String>):
  match wr:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{Loop.why(e)})
    case Done{w}:
      do IO<Maybe<&2, String>>:
        ns: List<&2, String> <- FileImpl.FileEp.list(root)
        ins: List<
          &2,
          Spec.Input> = List.append(
          &2,
          Spec.Input,
          Loop.hints(ns),
          Loop.each(Loop.known(c), Ep.Hinted{})
        )
        d: Drained <- Loop.drain(~report, Loop.budget(), root, j, c, ins)
        Loop.drained(d, w, w2 => j2 => c2 => Loop.go(~report, waits, root, w2, j2, c2))

# The journal
# -----------
# One journal per user, in the user's data folder: %LOCALAPPDATA%\bend-ver
# on Windows, else $XDG_DATA_HOME/bend-ver, else $HOME/.local/share/bend-ver.
# A lock file there keeps a second loop out (the OS drops the lock with its
# process). The journal is read whole at start (so it stays below 4 GiB
# until compaction exists), and a torn tail is cut by writing the good part
# to a new file, syncing it, and renaming it over the journal.

# the folder named by an environment variable, with rest after it, when it
# is set and not empty
def Log.env(r: Result<&1, &1, U32 & String, String>, rest: String) -> Maybe<&2, String>:
  match r:
    case Fail{e}:
      None{}
    case Done{+v}:
      Shared.Bool.when(
        Maybe<&2, String>,
        String.is_empty(v),
        u => None{},
        u => Some{String.append(v, rest)}
      )

# the user's data folder for bend-ver, or None when no variable names one
def Log.dir() -> IO(Maybe<&2, String>):
  do IO<Maybe<&2, String>>:
    a: Result<&1, &1, U32 & String, String> <- IO.get_env("LOCALAPPDATA")
    b: Result<&1, &1, U32 & String, String> <- IO.get_env("XDG_DATA_HOME")
    h: Result<&1, &1, U32 & String, String> <- IO.get_env("HOME")
    first: Maybe<
      &2,
      String> = Maybe.or(&2, String, Log.env(a, "/bend-ver"), Log.env(b, "/bend-ver"))
    return Maybe.or(&2, String, first, Log.env(h, "/.local/share/bend-ver"))

# the bytes of a path in the folder d
def Log.path(d: String, name: String) -> Shared.Bytes():
  Text.Text.encode(String.concat([d, "/", name]))

# the bytes that a read gave, or why it gave none
def Log.got(g: FileImpl.Got) -> Result<&2, &2, String, Shared.Bytes()>:
  match g:
    case FileImpl.Read{b}:
      Done{b}
    case FileImpl.Moving{}:
      Fail{"the journal changed while it was read"}
    case FileImpl.Unreadable{why}:
      Fail{why}

# the bytes of the journal, empty when there is none yet, or why they
# cannot be read
def Log.bytes.of(
  p: Shared.Bytes(),
  probe: File.Probe
) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match probe:
    case File.NotFound{}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Done{[]})
    case _:
      do IO<Result<&2, &2, String, Shared.Bytes()>>:
        g: FileImpl.Got <- FileImpl.FileEp.read(p)
        return Log.got(g)

# the bytes of the journal at p
def Log.bytes(+p: Shared.Bytes()) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  do IO<Result<&2, &2, String, Shared.Bytes()>>:
    probe: File.Probe <- File.FileFx.probe(p)
    Log.bytes.of(p, probe)

# the result of a sync, after the file closes
def Log.closed(
  fs: File & Result<&1, &1, U32 & String, Unit>
) -> IO(Result<&1, &1, U32 & String, Unit>):
  (f, s) = fs
  do IO<Result<&1, &1, U32 & String, Unit>>:
    File.close(f)
    return s

# the result of a write that a sync and a close follow
def Log.flush(
  fw: File & Result<&1, &1, U32 & String, Unit>
) -> IO(Result<&1, &1, U32 & String, Unit>):
  (f, w) = fw
  match w:
    case Fail{e}:
      do IO<Result<&1, &1, U32 & String, Unit>>:
        File.close(f)
        return Fail{e}
    case Done{u}:
      do IO<Result<&1, &1, U32 & String, Unit>>:
        fs: File & Result<&1, &1, U32 & String, Unit> <- File.FileFx.sync(f)
        Log.closed(fs)

# None after a rename, or why it failed
def Log.renamed(r: Result<&1, &1, U32 & String, Unit>) -> Maybe<&2, String>:
  match r:
    case Done{u}:
      None{}
    case Fail{e}:
      Some{Loop.why(e)}

# the rename over the journal after the good part is on disk
def Log.cut.wrote(
  tmp: Shared.Bytes(),
  p: Shared.Bytes(),
  w: Result<&1, &1, U32 & String, Unit>
) -> IO(Maybe<&2, String>):
  match w:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{Loop.why(e)})
    case Done{u}:
      do IO<Maybe<&2, String>>:
        r: Result<&1, &1, U32 & String, Unit> <- File.FileFx.rename(tmp, p)
        return Log.renamed(r)

# the good part written to tmp and renamed over p, or why not
def Log.cut.opened(
  tmp: Shared.Bytes(),
  p: Shared.Bytes(),
  good: Shared.Bytes(),
  o: Result<&1, &1, U32 & String, File>
) -> IO(Maybe<&2, String>):
  match o:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{Loop.why(e)})
    case Done{f}:
      do IO<Maybe<&2, String>>:
        fw: File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, good)
        w: Result<&1, &1, U32 & String, Unit> <- Log.flush(fw)
        Log.cut.wrote(tmp, p, w)

# the journal at p cut to its first good bytes of b, when a torn tail
# follows them; None when nothing needed cutting or the cut worked
def Log.cut(+d: String, p: Shared.Bytes(), +b: Shared.Bytes(), +good: Nat) -> IO(Maybe<&2, String>):
  Shared.Bool.when(
    IO(Maybe<&2, String>),
    Nat.is_lt(good, List.length(&2, U32, b)),
    u => do IO<Maybe<&2, String>>:
      o: Result<&1, &1, U32 & String, File> <- File.open_bytes(Log.path(d, "journal.log.tmp"), "w")
      Log.cut.opened(Log.path(d, "journal.log.tmp"), p, List.take(&2, U32, b, good), o),
    u => IO.pure(Maybe<&2, String>, None{}))

# the loop once the journal is open for appends
def Loop.appending(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  +root: File.Root,
  c: Spec.Core,
  o: Result<&1, &1, U32 & String, File>
) -> IO(Maybe<&2, String>):
  match o:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{"the journal could not be opened: " ++ Loop.why(e)})
    case Done{j}:
      do IO<Maybe<&2, String>>:
        wr: Result<&1, &1, U32 & String, File> <- FileImpl.FileEp.watch(root)
        Loop.started(~report, waits, root, j, c, wr)

# the loop after the journal was read and its torn tail cut: the core
# restored from the records, the journal open for appends, then the watch
def Loop.restored(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  m: Spec.Mount,
  p: Shared.Bytes(),
  rs: List<&2, Journal.Record>,
  cut: Maybe<&2, String>
) -> IO(Maybe<&2, String>):
  match cut:
    case Some{why}:
      IO.pure(Maybe<&2, String>, Some{"the torn tail of the journal could not be cut: " ++ why})
    case None{}:
      do IO<Maybe<&2, String>>:
        o: Result<&1, &1, U32 & String, File> <- File.open_bytes(p, "a")
        Loop.appending(~report, waits, root, Spec.Core.restore(m, rs), o)

# the loop with what the reader found in the bytes b of the journal
def Loop.read.of(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  m: Spec.Mount,
  d: String,
  +p: Shared.Bytes(),
  b: Shared.Bytes(),
  rd: Journal.Read
) -> IO(Maybe<&2, String>):
  match rd:
    case Journal.Read{rs, good}:
      do IO<Maybe<&2, String>>:
        cut: Maybe<&2, String> <- Log.cut(d, p, b, good)
        Loop.restored(~report, waits, root, m, p, rs, cut)

# the loop once the bytes of the journal are read: its records, after the
# torn tail (if any) is cut
def Loop.read(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  m: Spec.Mount,
  d: String,
  p: Shared.Bytes(),
  r: Result<&2, &2, String, Shared.Bytes()>
) -> IO(Maybe<&2, String>):
  match r:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{"the journal could not be read: " ++ e})
    case Done{+b}:
      Loop.read.of(~report, waits, root, m, d, p, b, Journal.Journal.read(b))

# the loop once the lock on the journal is held (its handle stays open
# until the process ends, and with it the lock)
def Loop.locked(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  m: Spec.Mount,
  +d: String,
  lk: Result<&1, &1, U32 & String, File>
) -> IO(Maybe<&2, String>):
  match lk:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{"the journal is not free: " ++ Loop.why(e)})
    case Done{held}:
      +p = Log.path(d, "journal.log")
      do IO<Maybe<&2, String>>:
        r: Result<&2, &2, String, Shared.Bytes()> <- Log.bytes(p)
        Loop.read(~report, waits, root, m, d, p, r)

# the loop once the space is known: take the journal of the data folder
def Loop.opened(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  m: Spec.Mount,
  dir: Maybe<&2, String>
) -> IO(Maybe<&2, String>):
  match dir:
    case None{}:
      IO.pure(Maybe<&2, String>, Some{"no data folder: set LOCALAPPDATA, XDG_DATA_HOME or HOME"})
    case Some{+d}:
      do IO<Maybe<&2, String>>:
        made: Result<&1, &1, U32 & String, Unit> <- File.FileFx.make_dirs(Text.Text.encode(d))
        lk: Result<&1, &1, U32 & String, File> <- File.FileFx.lock(Log.path(d, "journal.lock"))
        Loop.locked(~report, waits, root, m, d, lk)

# The space file
# --------------
# The id of a space is the text of the file ".bend-ver" at its root. A root
# without one gets a new id: 16 random bytes as 32 lowercase hex
# characters, written there before anything else happens.

# the bytes of one random word, low byte first, or the text of its failure
def Loop.word(r: Result<&1, &1, U32 & String, U32>) -> Result<&2, &2, String, Shared.Bytes()>:
  match r:
    case Fail{e}:
      Fail{Loop.why(e)}
    case Done{+x}:
      Done{[(x .&. 255: U32), ((x >> 8n) .&. 255: U32), ((x >> 16n) .&. 255: U32), (x >> 24n: U32)]}

# a then b, or the first failure
def Loop.join(
  a: Result<&2, &2, String, Shared.Bytes()>,
  b: Result<&2, &2, String, Shared.Bytes()>
) -> Result<&2, &2, String, Shared.Bytes()>:
  match a b:
    case Done{x} Done{y}:
      Done{List.append(&2, U32, x, y)}
    case Fail{e} _:
      Fail{e}
    case _ Fail{e}:
      Fail{e}

# n random words as bytes, or the text of a failure
def Loop.random(n: Nat) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match n:
    case 0n:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Done{[]})
    case 1n+k:
      do IO<Result<&2, &2, String, Shared.Bytes()>>:
        r: Result<&1, &1, U32 & String, U32> <- IO.random_u32()
        rest: Result<&2, &2, String, Shared.Bytes()> <- Loop.random(k)
        return Loop.join(Loop.word(r), rest)

# the id that the put of a new space file left, or the text of what went
# wrong
def Loop.created(id: String, ss: List<&2, Ep.Signal>) -> Result<&2, &2, String, String>:
  match ss:
    case Con{Ep.Fetched{b, t}, r}:
      Done{id}
    case Con{Ep.Reached{Ep.Unreachable{why}}, r}:
      Fail{why}
    case Con{s, r}:
      Loop.created(id, r)
    case Nil{}:
      Fail{"the space file was not written"}

# a new space file at the root, with a random id
def Loop.create(
  root: File.Root,
  r: Result<&2, &2, String, Shared.Bytes()>
) -> IO(Result<&2, &2, String, String>):
  match r:
    case Fail{e}:
      IO.pure(Result<&2, &2, String, String>, Fail{e})
    case Done{bytes}:
      +id = Hash.Hash.hex(bytes)
      do IO<Result<&2, &2, String, String>>:
        ss: List<
          &2,
          Ep.Signal> <- FileImpl.FileEp.put(
          root,
          Spec.Mount.space_file(),
          Text.Text.encode(id),
          Ep.WasAbsent{}
        )
        return Loop.created(id, ss)

# the id of the text of a space file: trimmed, and not empty
def Loop.space.text(t: Maybe<&2, String>) -> Result<&2, &2, String, String>:
  match t:
    case None{}:
      Fail{"the space file is not UTF-8"}
    case Some{x}:
      +id = String.trim(x)
      Shared.Bool.when(
        Result<&2, &2, String, String>,
        String.is_empty(id),
        u => Fail{"the space file is empty"},
        u => Done{id}
      )

# the id that the fetched space file holds, trimmed of spaces and line
# ends, or a new one when the root has none
def Loop.space.of(root: File.Root, s: Ep.Signal) -> IO(Result<&2, &2, String, String>):
  match s:
    case Ep.Fetched{b, t}:
      IO.pure(Result<&2, &2, String, String>, Loop.space.text(Text.Text.decode(b)))
    case Ep.Reached{Ep.Absent{}}:
      do IO<Result<&2, &2, String, String>>:
        r: Result<&2, &2, String, Shared.Bytes()> <- Loop.random(4n)
        Loop.create(root, r)
    case Ep.Reached{Ep.Unreachable{why}}:
      IO.pure(Result<&2, &2, String, String>, Fail{why})
    case _:
      IO.pure(Result<&2, &2, String, String>, Fail{"the space file could not be read"})

# the space of the root: read from its space file, or made new
def Loop.space(+root: File.Root) -> IO(Result<&2, &2, String, String>):
  do IO<Result<&2, &2, String, String>>:
    s: Ep.Signal <- FileImpl.FileEp.fetch(root, Spec.Mount.space_file())
    Loop.space.of(root, s)

# the loop once the space is known, or the text of why it is not
def Loop.spaced(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  root: File.Root,
  uri: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  sp: Result<&2, &2, String, String>
) -> IO(Maybe<&2, String>):
  match sp:
    case Fail{e}:
      IO.pure(Maybe<&2, String>, Some{e})
    case Done{id}:
      do IO<Maybe<&2, String>>:
        dir: Maybe<&2, String> <- Log.dir()
        Loop.opened(~report, waits, root, Spec.Mount{id, line, uri, globs}, dir)

# the loop over the root at the OS path os
def Loop.rooted(
  ~report: Spec.Output -> IO(Unit),
  waits: Nat,
  uri: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  os: Maybe<&2, String>
) -> IO(Maybe<&2, String>):
  match os:
    case None{}:
      IO.pure(Maybe<&2, String>, Some{"not a local file URI"})
    case Some{path}:
      do IO<Maybe<&2, String>>:
        +r: File.Root <- FileImpl.FileEp.open(path)
        sp: Result<&2, &2, String, String> <- Loop.space(r)
        Loop.spaced(~report, waits, r, uri, line, globs, sp)

# the core loop over the files below the URI root that the globs select,
# on the line named line, for at most waits waits; None when the waits ran
# out, or the text of what stopped it. The space id comes from the space
# file at the root (made when missing). The watcher starts before the
# listing, so no change between them is lost.
def Loop.run(
  ~report: Spec.Output -> IO(Unit),
  +root: Shared.Uri,
  line: String,
  globs: List<&2, Glob.Rule>,
  waits: Nat
) -> IO(Maybe<&2, String>):
  Loop.rooted(~report, waits, root, line, globs, File.FileEp.root_of(root))
