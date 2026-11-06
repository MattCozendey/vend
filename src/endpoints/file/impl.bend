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
        w: Result<&1, &1, U32 & String, Unit> <- FileEp.put.closed(fw)
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

# rest, with the name m in front when there is one
def FileEp.names.put(
  m: Maybe<&2, Shared.Name>,
  rest: List<&2, Shared.Name>
) -> List<&2, Shared.Name>:
  match m:
    case None{}:
      rest
    case Some{n}:
      n <> rest

# the names of the paths that name file resources
def FileEp.names(ps: List<&2, Shared.Bytes()>) -> List<&2, Shared.Name>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      FileEp.names.put(Spec.FileEp.name_of(Text.Text.decode(p)), FileEp.names(t))

# the names of a listing, or none when the root could not be listed
def FileEp.list.of(
  r: Result<&1, &1, U32 & String, List<&2, Shared.Bytes()>>
) -> List<&2, Shared.Name>:
  match r:
    case Fail{e}:
      []
    case Done{ps}:
      FileEp.names(ps)

# the names of the file resources below the root now: none when the root
# cannot be listed
def FileEp.list(root: Spec.Root) -> IO(List<&2, Shared.Name>):
  do IO<List<&2, Shared.Name>>:
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
