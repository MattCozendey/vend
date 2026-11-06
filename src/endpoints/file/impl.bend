import Base
import ../../hash/spec.bend as Hash
import ../../shared.bend as Shared
import ../../views/text/impl.bend as TextImpl
import ../../views/text/spec.bend as Text
import ../spec.bend as Ep
import ./spec.bend as Spec

# The file endpoint's IO. Each operation probes before it acts, answers
# Unreachable for whatever it cannot tell, and never reads a path that
# names no resource.

# Opening
# -------

# the device of a root probe, when the root is a directory
def FileEp.device_of(p: Spec.Probe) -> Maybe<&2, U32>:
  match p:
    case Spec.Found{Spec.KDir{}, d}:
      Some{d}
    case _:
      None{}

# the endpoint at the OS path root. It notes the root's device when the
# root is a directory now, so a later mount over it is caught.
def FileEp.open(root: String) -> IO(Spec.Root):
  do IO<Spec.Root>:
    +path: Shared.Bytes() = Text.Text.encode(root)
    p: Spec.Probe <- Spec.FileFx.probe(path)
    return Spec.Root{path, FileEp.device_of(p)}

# Fetching
# --------

# the signal of a decision that is not ReadIt
def FileEp.unread(d: Spec.Decision) -> Ep.Signal:
  match d:
    case Spec.ReadIt{}:
      Ep.Reached{Ep.Unreachable{"a file to read was not read"}}
    case Spec.KnownAbsent{}:
      Ep.Reached{Ep.Absent{}}
    case Spec.CannotTell{why}:
      Ep.Reached{Ep.Unreachable{why}}

# What a read of a file gave. Read: all its bytes. Moving: its size changed
# while it was read, so read again. Unreadable: an error, with its text.
type Got is Data:
  Read{bytes: Shared.Bytes()}
  Moving{}
  Unreadable{why: String}

# the text of an error
def FileEp.why(e: U32 & String) -> Got:
  (c, t) = e
  Unreadable{t}

# the read of size bytes: Moving when there were not exactly size bytes
def FileEp.got(size: U32, r: Result<&1, &1, U32 & String, Shared.Bytes()>) -> Got:
  match r:
    case Fail{e}:
      FileEp.why(e)
    case Done{+b}:
      same = Nat.is_eq(List.length(&2, U32, b), U32.to_nat(size))
      Shared.Bool.when(Got, same, u => Read{b}, u => Moving{})

# the read of n bytes, after it closes the file
def FileEp.read.done(n: U32, fr: File & Result<&1, &1, U32 & String, Shared.Bytes()>) -> IO(Got):
  (f, r) = fr
  do IO<Got>:
    File.close(f)
    return FileEp.got(n, r)

# the bytes of the open file f: its size, then one byte more than that, so
# a file that grows while it is read shows as Moving
def FileEp.read.sized(f: File, s: Result<&1, &1, U32 & String, U32>) -> IO(Got):
  match s:
    case Fail{e}:
      do IO<Got>:
        File.close(f)
        return FileEp.why(e)
    case Done{+n}:
      do IO<Got>:
        fr: File & Result<&1, &1, U32 & String, Shared.Bytes()> <- File.read_bytes(f, (n + 1: U32))
        FileEp.read.done(n, fr)

# the read after File.size
def FileEp.read.size(fs: File & Result<&1, &1, U32 & String, U32>) -> IO(Got):
  (f, s) = fs
  FileEp.read.sized(f, s)

# the bytes of the file that opening gave
def FileEp.read.opened(o: Result<&1, &1, U32 & String, File>) -> IO(Got):
  match o:
    case Fail{e}:
      IO.pure(Got, FileEp.why(e))
    case Done{f}:
      do IO<Got>:
        fs: File & Result<&1, &1, U32 & String, U32> <- File.size(f)
        FileEp.read.size(fs)

# the bytes of the file at the OS path p
def FileEp.read(p: Shared.Bytes()) -> IO(Got):
  do IO<Got>:
    o: Result<&1, &1, U32 & String, File> <- File.open_bytes(p, "r")
    FileEp.read.opened(o)

# Sources
# -------
# A write may take its bytes from a file URI. Like a fetch, the read probes
# first, reads only a regular file, and says why it cannot when it cannot.

# the source after a read: its bytes, again() while the file moved, or why
def FileEp.source.got(
  g: Got,
  again: Unit -> IO(Result<&2, &2, String, Shared.Bytes()>)
) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match g:
    case Read{b}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Done{b})
    case Moving{}:
      again(Unit{})
    case Unreadable{why}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Fail{why})

# the bytes of the regular file at the OS path p, read again while it
# changes, at most fuel times
def FileEp.source.read(fuel: Nat, +p: Shared.Bytes()) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match fuel:
    case 0n:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Fail{"it kept changing while it was read"})
    case 1n+f:
      do IO<Result<&2, &2, String, Shared.Bytes()>>:
        g: Got <- FileEp.read(p)
        FileEp.source.got(g, u => FileEp.source.read(f, p))

# the bytes of the file at the OS path p after its probe decided d
def FileEp.source.decided(
  d: Spec.Decision,
  p: Shared.Bytes()
) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match d:
    case Spec.ReadIt{}:
      FileEp.source.read(4n, p)
    case Spec.KnownAbsent{}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Fail{"nothing is there"})
    case Spec.CannotTell{why}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Fail{why})

# the bytes of the file at the OS path, if the URI names a local file
def FileEp.source.at(m: Maybe<&2, String>) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  match m:
    case None{}:
      IO.pure(Result<&2, &2, String, Shared.Bytes()>, Fail{"it is not a local file URI"})
    case Some{path}:
      do IO<Result<&2, &2, String, Shared.Bytes()>>:
        +p: Shared.Bytes() = Text.Text.encode(path)
        here: Spec.Probe <- Spec.FileFx.probe(p)
        FileEp.source.decided(Spec.FileEp.decide.here(here), p)

# the bytes of the file that the file URI u names, or why they cannot be
# read
def FileEp.source(u: Shared.Uri) -> IO(Result<&2, &2, String, Shared.Bytes()>):
  FileEp.source.at(Spec.FileEp.root_of(u))

# the decision for rest: it probes the root, then rest's path
def FileEp.decide(+root: Spec.Root, +rest: String) -> IO(Spec.Decision):
  do IO<Spec.Decision>:
    +rp: Spec.Probe <- Spec.FileFx.probe(Spec.Root.path(root))
    here: Spec.Probe <- Spec.FileFx.probe(Spec.FileEp.path(Spec.Root.path(root), rest))
    return Spec.FileEp.decide(rest, root, rp, here)

# the signal of a read, or again() when the file moved
def FileEp.fetch.got(g: Got, again: Unit -> IO(Ep.Signal)) -> IO(Ep.Signal):
  match g:
    case Read{+b}:
      IO.pure(Ep.Signal, Ep.Fetched{b, Hash.Hash.blake3(b)})
    case Unreadable{why}:
      IO.pure(Ep.Signal, Ep.Reached{Ep.Unreachable{why}})
    case Moving{}:
      again(Unit{})

# the signal for rest after its probes: the content when a file is there;
# again() reads once more when the file moved meanwhile
def FileEp.fetch.decided(
  d: Spec.Decision,
  root: Spec.Root,
  rest: String,
  again: Unit -> IO(Ep.Signal)
) -> IO(Ep.Signal):
  match d:
    case Spec.ReadIt{}:
      do IO<Ep.Signal>:
        g: Got <- FileEp.read(Spec.FileEp.path(Spec.Root.path(root), rest))
        FileEp.fetch.got(g, again)
    case _:
      IO.pure(Ep.Signal, FileEp.unread(d))

# the signal for rest; fuel counts the reads left while the file moves
def FileEp.fetch.go(fuel: Nat, +root: Spec.Root, +rest: String) -> IO(Ep.Signal):
  match fuel:
    case 0n:
      IO.pure(Ep.Signal, Ep.Reached{Ep.Unreachable{"the file kept changing while it was read"}})
    case 1n+f:
      do IO<Ep.Signal>:
        d: Spec.Decision <- FileEp.decide(root, rest)
        FileEp.fetch.decided(d, root, rest, u => FileEp.fetch.go(f, root, rest))

# the fetch of rest when ok, the answer for a rest that names no resource
# when not
def FileEp.fetch.if(ok: Bool, root: Spec.Root, rest: String) -> IO(Ep.Signal):
  match ok:
    case False{}:
      IO.pure(Ep.Signal, Ep.Reached{Ep.Unreachable{String.append("not a file resource: ", rest)}})
    case True{}:
      FileEp.fetch.go(4n, root, rest)

# the answer to a Fetch of rest: Fetched with the content and its BLAKE3
# token, Reached Absent when the endpoint knows nothing is there, or
# Reached Unreachable with why. A rest that names no resource never touches
# the disk.
def FileEp.fetch(root: Spec.Root, +rest: String) -> IO(Ep.Signal):
  FileEp.fetch.if(Spec.FileEp.is_resource(rest), root, rest)

# Putting
# -------

# the text of a failed step, after what
def FileEp.failed(what: String, e: U32 & String) -> Ep.Signal:
  (c, t) = e
  Ep.Reached{Ep.Unreachable{String.concat([what, ": ", t])}}

# the signals after the rename of the temporary file tmp over p: the written
# content, whose token the core already knows; on failure tmp is removed
def FileEp.put.renamed(
  tmp: Shared.Bytes(),
  +bytes: Shared.Bytes(),
  r: Result<&1, &1, U32 & String, Unit>
) -> IO(List<&2, Ep.Signal>):
  match r:
    case Done{u}:
      IO.pure(List<&2, Ep.Signal>, [Ep.Fetched{bytes, Hash.Hash.blake3(bytes)}])
    case Fail{e}:
      do IO<List<&2, Ep.Signal>>:
        gone: Result<&1, &1, U32 & String, Unit> <- Spec.FileFx.remove(tmp)
        return [FileEp.failed("cannot replace the file", e)]

# the signals after the temporary file tmp was written and closed: on
# success, the rename over p
def FileEp.put.wrote(
  +tmp: Shared.Bytes(),
  p: Shared.Bytes(),
  bytes: Shared.Bytes(),
  w: Result<&1, &1, U32 & String, Unit>
) -> IO(List<&2, Ep.Signal>):
  match w:
    case Done{u}:
      do IO<List<&2, Ep.Signal>>:
        r: Result<&1, &1, U32 & String, Unit> <- Spec.FileFx.rename(tmp, p)
        FileEp.put.renamed(tmp, bytes, r)
    case Fail{e}:
      do IO<List<&2, Ep.Signal>>:
        gone: Result<&1, &1, U32 & String, Unit> <- Spec.FileFx.remove(tmp)
        return [FileEp.failed("cannot write the temporary file", e)]

# the write result after the temporary file closes
def FileEp.put.closed(
  fw: File & Result<&1, &1, U32 & String, Unit>
) -> IO(Result<&1, &1, U32 & String, Unit>):
  (f, w) = fw
  do IO<Result<&1, &1, U32 & String, Unit>>:
    File.close(f)
    return w

# the write result after the temporary file is flushed to the disk and
# closed, so the rename never puts a file whose bytes a power cut can lose
def FileEp.put.flushed(
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
        fs: File & Result<&1, &1, U32 & String, Unit> <- Spec.FileFx.sync(f)
        FileEp.put.closed(fs)

# the signals after the temporary file tmp was created ("x": only when no
# file is there): write bytes into it, then rename it over p
def FileEp.put.created(
  tmp: Shared.Bytes(),
  p: Shared.Bytes(),
  +bytes: Shared.Bytes(),
  o: Result<&1, &1, U32 & String, File>
) -> IO(List<&2, Ep.Signal>):
  match o:
    case Fail{e}:
      IO.pure(List<&2, Ep.Signal>, [FileEp.failed("cannot create the temporary file", e)])
    case Done{f}:
      do IO<List<&2, Ep.Signal>>:
        fw: File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, bytes)
        w: Result<&1, &1, U32 & String, Unit> <- FileEp.put.flushed(fw)
        FileEp.put.wrote(tmp, p, bytes, w)

# a number to keep temporary files apart, 0 when the OS gives none
def FileEp.nonce(r: Result<&1, &1, U32 & String, U32>) -> U32:
  match r:
    case Done{n}:
      n
    case Fail{e}:
      0

# the signals of the write itself: the temporary file next to rest's file,
# then the rename over it
def FileEp.put.write(
  +root: Spec.Root,
  +rest: String,
  bytes: Shared.Bytes()
) -> IO(List<&2, Ep.Signal>):
  do IO<List<&2, Ep.Signal>>:
    r: Result<&1, &1, U32 & String, U32> <- IO.random_u32()
    +tmp: Shared.Bytes() = Spec.FileEp.path(
      Spec.Root.path(root),
      Spec.FileEp.temp(rest, FileEp.nonce(r))
    )
    o: Result<&1, &1, U32 & String, File> <- File.open_bytes(tmp, "x")
    FileEp.put.created(tmp, Spec.FileEp.path(Spec.Root.path(root), rest), bytes, o)

# the signals after the directories above rest were made: on success, the
# write
def FileEp.put.dirs(
  root: Spec.Root,
  rest: String,
  bytes: Shared.Bytes(),
  m: Result<&1, &1, U32 & String, Unit>
) -> IO(List<&2, Ep.Signal>):
  match m:
    case Done{u}:
      FileEp.put.write(root, rest, bytes)
    case Fail{e}:
      IO.pure(List<&2, Ep.Signal>, [FileEp.failed("cannot make the directory", e)])

# the directory dir below the root made, with every missing one above it;
# nothing to make at the top, where top holds
def FileEp.put.mkdir(
  top: Bool,
  root: Spec.Root,
  dir: String
) -> IO(Result<&1, &1, U32 & String, Unit>):
  match top:
    case True{}:
      IO.pure(Result<&1, &1, U32 & String, Unit>, Done{Unit{}})
    case False{}:
      Spec.FileFx.make_dirs(Spec.FileEp.path(Spec.Root.path(root), dir))

# the signals of a write whose belief held: a file that is known absent may
# lack the directories above it, so they are made first
def FileEp.put.go(
  d: Spec.Decision,
  +root: Spec.Root,
  +rest: String,
  bytes: Shared.Bytes()
) -> IO(List<&2, Ep.Signal>):
  match d:
    case Spec.KnownAbsent{}:
      do IO<List<&2, Ep.Signal>>:
        +dir: String = Spec.FileEp.dir(rest)
        m: Result<&1, &1, U32 & String, Unit> <- FileEp.put.mkdir(String.is_empty(dir), root, dir)
        FileEp.put.dirs(root, rest, bytes, m)
    case _:
      FileEp.put.write(root, rest, bytes)

# the signals of a Put after reading the file that is there: the write
# when e holds for its content, else that content, so the core records what
# the disk holds; a file that moves while it is read refuses the write and
# asks for a fetch
def FileEp.put.read(
  g: Got,
  root: Spec.Root,
  rest: String,
  bytes: Shared.Bytes(),
  e: Ep.Expect
) -> IO(List<&2, Ep.Signal>):
  match g:
    case Read{+b}:
      +t = Hash.Hash.blake3(b)
      Shared.Bool.when(
        IO(List<&2, Ep.Signal>),
        Spec.FileEp.holds(e, Spec.ReadIt{}, Some{t}),
        u => FileEp.put.go(Spec.ReadIt{}, root, rest, bytes),
        u => IO.pure(List<&2, Ep.Signal>, [Ep.Fetched{b, t}])
      )
    case Moving{}:
      IO.pure(List<&2, Ep.Signal>, [Ep.Hinted{}])
    case Unreadable{why}:
      IO.pure(List<&2, Ep.Signal>, [Ep.Reached{Ep.Unreachable{why}}])

# the signals of a Put after rest's decision d: the write when e holds for
# what is there, else what is there
def FileEp.put.decided(
  d: Spec.Decision,
  +root: Spec.Root,
  +rest: String,
  bytes: Shared.Bytes(),
  e: Ep.Expect
) -> IO(List<&2, Ep.Signal>):
  match d:
    case Spec.ReadIt{}:
      do IO<List<&2, Ep.Signal>>:
        g: Got <- FileEp.read(Spec.FileEp.path(Spec.Root.path(root), rest))
        FileEp.put.read(g, root, rest, bytes, e)
    case Spec.KnownAbsent{}:
      Shared.Bool.when(
        IO(List<&2, Ep.Signal>),
        Spec.FileEp.holds(e, Spec.KnownAbsent{}, None{}),
        u => FileEp.put.go(Spec.KnownAbsent{}, root, rest, bytes),
        u => IO.pure(List<&2, Ep.Signal>, [Ep.Reached{Ep.Absent{}}])
      )
    case Spec.CannotTell{why}:
      IO.pure(List<&2, Ep.Signal>, [Ep.Reached{Ep.Unreachable{why}}])

# the signals of a Put of rest when ok, the answer for a rest that names no
# resource when not
def FileEp.put.if(
  ok: Bool,
  +root: Spec.Root,
  +rest: String,
  bytes: Shared.Bytes(),
  e: Ep.Expect
) -> IO(List<&2, Ep.Signal>):
  match ok:
    case False{}:
      IO.pure(
        List<&2, Ep.Signal>,
        [Ep.Reached{Ep.Unreachable{String.append("not a file resource: ", rest)}}]
      )
    case True{}:
      do IO<List<&2, Ep.Signal>>:
        d: Spec.Decision <- FileEp.decide(root, rest)
        FileEp.put.decided(d, root, rest, bytes, e)

# the answer to a Put of bytes that believes e. It checks e against the
# disk right before it writes: when e holds, it writes a temporary file
# next to rest's file and renames it over that file, and answers Fetched
# with the content (the core already recorded it, so it records nothing);
# when e does not hold, it writes nothing and answers what is there. An
# outside writer that lands between the check and the rename is
# overwritten, and nothing can tell afterwards; writes through the core are
# exact because the core orders them.
def FileEp.put(
  root: Spec.Root,
  +rest: String,
  bytes: Shared.Bytes(),
  e: Ep.Expect
) -> IO(List<&2, Ep.Signal>):
  FileEp.put.if(Spec.FileEp.is_resource(rest), root, rest, bytes, e)

# Listing
# -------

# rest, with the path m in front when there is one
def FileEp.names.put(m: Maybe<&2, String>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      rest
    case Some{n}:
      n <> rest

# the listed OS paths that name file resources, as resource paths
def FileEp.names(ps: List<&2, Shared.Bytes()>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      FileEp.names.put(Spec.FileEp.path_of(Text.Text.decode(p)), FileEp.names(t))

# the resource paths of a listing, or none when the root could not be
# listed
def FileEp.list.of(r: Result<&1, &1, U32 & String, List<&2, Shared.Bytes()>>) -> List<&2, String>:
  match r:
    case Fail{e}:
      []
    case Done{ps}:
      FileEp.names(ps)

# the paths of the file resources below the root now: none when the root
# cannot be listed
def FileEp.list(root: Spec.Root) -> IO(List<&2, String>):
  do IO<List<&2, String>>:
    r: Result<
      &1,
      &1,
      U32 & String,
      List<&2, Shared.Bytes()>> <- Spec.FileFx.list(Spec.Root.path(root))
    return FileEp.list.of(r)

# Watching
# --------

# r with each path read as UTF-8
def FileEp.report(r: Spec.Raw) -> Spec.Report:
  match r:
    case Spec.RawTouched{p}:
      Spec.Touched{Text.Text.decode(p)}
    case Spec.RawRenamed{a, b}:
      Spec.Renamed{Text.Text.decode(a), Text.Text.decode(b)}
    case Spec.RawLost{}:
      Spec.Dropped{}
    case Spec.RawRootGone{}:
      Spec.RootGone{}

# what the core hears of rs, in order
def FileEp.notices(rs: List<&2, Spec.Raw>) -> List<&2, Spec.Notice>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      List.append(&2, Spec.Notice, Spec.FileEp.notices(FileEp.report(r)), FileEp.notices(t))

# a watcher of the root and everything below it. After AllLost the watcher
# reports nothing more: the caller watches again once the root is back.
def FileEp.watch(root: Spec.Root) -> IO(Result<&1, &1, U32 & String, File>):
  Spec.FileFx.watch(Spec.Root.path(root))

# the notices of a wait
def FileEp.next.of(
  wr: File & Result<&1, &1, U32 & String, List<&2, Spec.Raw>>
) -> File
  & Result<&1, &1, U32 & String, List<&2, Spec.Notice>>:
  (w, r) = wr
  (
    w,
    Result.map(&1, &1, U32 & String, List<&2, Spec.Raw>, List<&2, Spec.Notice>, FileEp.notices, r)
  )

# what the watcher w reports, as notices for the core, waiting at most ms
# milliseconds for the first report
def FileEp.next(w: File, ms: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, Spec.Notice>>):
  do IO<File & Result<&1, &1, U32 & String, List<&2, Spec.Notice>>>:
    wr: File & Result<&1, &1, U32 & String, List<&2, Spec.Raw>> <- Spec.FileFx.next(w, ms)
    return FileEp.next.of(wr)

# the watcher w released
def FileEp.unwatch(w: File) -> IO(Unit):
  Spec.FileFx.unwatch(w)

def Spec.resource_needs_path(rest, h):
  rest = rest
  %Equal.sym(Bool, Spec.FileEp.is_resource(rest), False{}, h):
    {
      Shared.Bool.when(
        Maybe<&2, String>,
        _,
        u => Some{rest},
        u => None{}
      )
        == None{}: Maybe<&2, String>
    }
  {==}

# no False is True
def Bool.false_not_true(e: {False{} == True{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Empty, Unit)
  Unit{}

# what absent_only_when_known concludes, for conditions a and b and probe here
def Absent.Goal(a: Bool, b: Bool, here: Spec.Probe) -> Type:
  {a == True{}: Bool} & ({b == True{}: Bool} & {here == Spec.NotFound{}: Spec.Probe})

# absent_only_when_known with the two conditions of FileEp.decide as a and b
def Absent.only(
  a: Bool,
  b: Bool,
  here: Spec.Probe,
  x: String
) -> {
  Spec.Decision.is_absent(
    Shared.Bool.when(
      Spec.Decision,
      Bool.and(a, b),
      u => Spec.FileEp.decide.here(here),
      u => Spec.CannotTell{x}
    )
  )
    == True{}: Bool
} -> Absent.Goal(a, b, here):
  match a b here:
    case True{} True{} Spec.NotFound{}:
      h => ({==}, ({==}, {==}))
    case True{} True{} Spec.Found{Spec.KFile{}, d}:
      h => Empty.absurd(
        Absent.Goal(True{}, True{}, Spec.Found{Spec.KFile{}, d}),
        Bool.false_not_true(h)
      )
    case True{} True{} Spec.Found{Spec.KDir{}, d}:
      h => Empty.absurd(
        Absent.Goal(True{}, True{}, Spec.Found{Spec.KDir{}, d}),
        Bool.false_not_true(h)
      )
    case True{} True{} Spec.Found{Spec.KOther{}, d}:
      h => Empty.absurd(
        Absent.Goal(True{}, True{}, Spec.Found{Spec.KOther{}, d}),
        Bool.false_not_true(h)
      )
    case True{} True{} Spec.Failed{c, t}:
      h => Empty.absurd(Absent.Goal(True{}, True{}, Spec.Failed{c, t}), Bool.false_not_true(h))
    case True{} False{} p:
      h => Empty.absurd(Absent.Goal(True{}, False{}, p), Bool.false_not_true(h))
    case False{} bb p:
      h => Empty.absurd(Absent.Goal(False{}, bb, p), Bool.false_not_true(h))

def Spec.absent_only_when_known(rest, r, root, here, h):
  match r:
    case Spec.Root{pp, d}:
      +rest = rest
      +root = root
      bad = Shared.Bool.when(
        String,
        Spec.FileEp.is_resource(rest),
        u => Spec.FileEp.root_why(root),
        u => String.append("not a file resource: ", rest)
      )
      Absent.only(Spec.FileEp.is_resource(rest), Spec.FileEp.root_holds(d, root), here, bad)(h)

# what read_only_files concludes, for conditions a and b
def Read.Goal(a: Bool, b: Bool) -> Type:
  {a == True{}: Bool} & {b == True{}: Bool}

# read_only_files with the two conditions of FileEp.decide as a and b
def Read.only(
  a: Bool,
  b: Bool,
  here: Spec.Probe,
  x: String
) -> {
  Spec.Decision.is_read(
    Shared.Bool.when(
      Spec.Decision,
      Bool.and(a, b),
      u => Spec.FileEp.decide.here(here),
      u => Spec.CannotTell{x}
    )
  )
    == True{}: Bool
} -> Read.Goal(a, b):
  match a b:
    case True{} True{}:
      h => ({==}, {==})
    case True{} False{}:
      h => Empty.absurd(Read.Goal(True{}, False{}), Bool.false_not_true(h))
    case False{} bb:
      h => Empty.absurd(Read.Goal(False{}, bb), Bool.false_not_true(h))

def Spec.read_only_files(rest, r, root, here, h):
  match r:
    case Spec.Root{pp, d}:
      +rest = rest
      +root = root
      bad = Shared.Bool.when(
        String,
        Spec.FileEp.is_resource(rest),
        u => Spec.FileEp.root_why(root),
        u => String.append("not a file resource: ", rest)
      )
      Read.only(Spec.FileEp.is_resource(rest), Spec.FileEp.root_holds(d, root), here, bad)(h)

# no True is False
def Bool.true_not_false(e: {True{} == False{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Unit, Empty)
  Unit{}

# the decision of FileEp.decide with conditions a and b, a not holding
def NoRes.Goal(a: Bool, b: Bool, here: Spec.Probe, x: String) -> Type:
  {
    Bool.or(
      Spec.Decision.is_read(
        Shared.Bool.when(
          Spec.Decision,
          Bool.and(a, b),
          u => Spec.FileEp.decide.here(here),
          u => Spec.CannotTell{x}
        )
      ),
      Spec.Decision.is_absent(
        Shared.Bool.when(
          Spec.Decision,
          Bool.and(a, b),
          u => Spec.FileEp.decide.here(here),
          u => Spec.CannotTell{x}
        )
      )
    )
      == False{}: Bool
  }

# non_resource_cannot_tell with the two conditions of FileEp.decide as a and b
def NoRes.go(
  a: Bool,
  b: Bool,
  here: Spec.Probe,
  x: String
) -> {a == False{}: Bool} -> NoRes.Goal(a, b, here, x):
  match a:
    case False{}:
      h => {==}
    case True{}:
      h => Empty.absurd(NoRes.Goal(True{}, b, here, x), Bool.true_not_false(h))

def Spec.non_resource_cannot_tell(rest, r, root, here, h):
  match r:
    case Spec.Root{pp, d}:
      +rest = rest
      +root = root
      bad = Shared.Bool.when(
        String,
        Spec.FileEp.is_resource(rest),
        u => Spec.FileEp.root_why(root),
        u => String.append("not a file resource: ", rest)
      )
      NoRes.go(Spec.FileEp.is_resource(rest), Spec.FileEp.root_holds(d, root), here, bad)(h)

def Spec.absence_holds_only_known(d, t, h):
  match d:
    case Spec.ReadIt{}:
      h
    case Spec.KnownAbsent{}:
      {==}
    case Spec.CannotTell{reason}:
      h

# one step of Hints.append over an About hint, with b the answer of
# FileEp.is_resource for it
def Hints.app.at(
  b: Bool,
  -t: List<&2, Spec.Notice>,
  -ys: List<&2, Spec.Notice>,
  ih: {
    Spec.Notice.all_hints(t) == True{}: Bool
  } -> {
    Spec.Notice.all_hints(ys) == True{}: Bool
  } -> {Spec.Notice.all_hints(List.append(&2, Spec.Notice, t, ys)) == True{}: Bool}
) -> {
  List.all.if(u => Spec.Notice.all_hints(t), b) == True{}: Bool
} -> {
  Spec.Notice.all_hints(ys) == True{}: Bool
} -> {
  List.all.if(u => Spec.Notice.all_hints(List.append(&2, Spec.Notice, t, ys)), b) == True{}: Bool
}:
  match b:
    case False{}:
      hx => hy => Empty.absurd({False{} == True{}: Bool}, Bool.false_not_true(hx))
    case True{}:
      hx => hy => ih(hx, hy)

# appending keeps all_hints
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- the other use of ys is an erased argument of Hints.app.at
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- the unused names are premises of the proof's own type; a proof does not run
def Hints.append(
  xs: List<&2, Spec.Notice>,
  ys: List<&2, Spec.Notice>
) -> {
  Spec.Notice.all_hints(xs) == True{}: Bool
} -> {
  Spec.Notice.all_hints(ys) == True{}: Bool
} -> {Spec.Notice.all_hints(List.append(&2, Spec.Notice, xs, ys)) == True{}: Bool}:
  match xs:
    case Nil{}:
      _ => hy => hy
    case Con{Spec.About{r, Ep.Hinted{}}, t}:
      Hints.app.at(Spec.FileEp.is_resource(r), t, ys, Hints.append(t, ys))
    case Con{Spec.About{r, Ep.Reached{x}}, t}:
      hx => _ => Empty.absurd(
        {
          Spec.Notice.all_hints(
            List.append(&2, Spec.Notice, Con{Spec.About{r, Ep.Reached{x}}, t}, ys)
          )
            == True{}: Bool
        },
        Bool.false_not_true(hx)
      )
    case Con{Spec.About{r, Ep.Fetched{x, y}}, t}:
      hx => _ => Empty.absurd(
        {
          Spec.Notice.all_hints(
            List.append(&2, Spec.Notice, Con{Spec.About{r, Ep.Fetched{x, y}}, t}, ys)
          )
            == True{}: Bool
        },
        Bool.false_not_true(hx)
      )
    case Con{Spec.About{r, Ep.Overflowed{}}, t}:
      hx => _ => Empty.absurd(
        {
          Spec.Notice.all_hints(
            List.append(&2, Spec.Notice, Con{Spec.About{r, Ep.Overflowed{}}, t}, ys)
          )
            == True{}: Bool
        },
        Bool.false_not_true(hx)
      )
    case Con{Spec.Moved{x, y}, t}:
      Hints.append(t, ys)
    case Con{Spec.AllOverflowed{}, t}:
      Hints.append(t, ys)
    case Con{Spec.AllLost{w}, t}:
      Hints.append(t, ys)

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the hint of a resource r, with b the answer of FileEp.is_resource(r)
def Hints.of(
  r: String,
  b: Bool
) -> {
  Spec.FileEp.is_resource(r) == b: Bool
} -> {
  Spec.Notice.all_hints(
    Spec.FileEp.hint.of(Shared.Bool.when(Maybe<&2, String>, b, u => Some{r}, u => None{}))
  )
    == True{}: Bool
}:
  match b:
    case False{}:
      e => {==}
    case True{}:
      e =>
        %Equal.sym(Bool, Spec.FileEp.is_resource(r), True{}, e):
          {List.all.if(u => Spec.Notice.all_hints([]), _) == True{}: Bool}
        {==}

# the hint of a report path is a hint about a resource
def Hints.path(
  p: Maybe<&2, String>
) -> {Spec.Notice.all_hints(Spec.FileEp.hint(p)) == True{}: Bool}:
  match p:
    case None{}:
      {==}
    case Some{+r}:
      Hints.of(r, Spec.FileEp.is_resource(r), {==})

# the Moved notice of a rename is no About
def Hints.moved(
  x: Maybe<&2, String>,
  y: Maybe<&2, String>
) -> {Spec.Notice.all_hints(Spec.FileEp.moved(x, y)) == True{}: Bool}:
  match x y:
    case Some{a} Some{b}:
      {==}
    case Some{a} None{}:
      {==}
    case None{} Some{b}:
      {==}
    case None{} None{}:
      {==}

def Spec.notices_are_hints(e):
  match e:
    case Spec.Touched{p}:
      Hints.path(p)
    case Spec.Renamed{+a, +b}:
      m = Spec.FileEp.moved(Spec.FileEp.path_of(a), Spec.FileEp.path_of(b))
      rest = List.append(&2, Spec.Notice, Spec.FileEp.hint(a), Spec.FileEp.hint(b))
      inner = Hints.append(Spec.FileEp.hint(a), Spec.FileEp.hint(b), Hints.path(a), Hints.path(b))
      Hints.append(m, rest, Hints.moved(Spec.FileEp.path_of(a), Spec.FileEp.path_of(b)), inner)
    case Spec.Dropped{}:
      {==}
    case Spec.RootGone{}:
      {==}
