import Base
import ../../glob/spec.bend as Glob
import ../../shared.bend as Shared
import ../../views/text/spec.bend as Text
import ../spec.bend as Ep

# The file endpoint. It is opened with a root directory: the OS path of a
# mount's file URI, which may be missing, unmounted or unreadable at any
# time. A resource is a valid path (Glob.is_path) below that root, relative
# to it; nothing else is a file resource. The endpoint speaks in these
# relative paths; the core makes names from them with the mount's space,
# and OS paths live only in this endpoint.

# Resources
# ---------

# the mark in the names of the temporary files that a Put writes
def FileEp.temp_mark() -> String:
  ".bend-ver-"

# s is the name of a temporary file that a Put writes before its rename:
# it starts with '.', holds the mark, and ends with ".tmp"
def FileEp.is_temp(+s: String) -> Bool:
  dot = String.starts_with(s, ".")
  Bool.and(dot, Bool.and(String.contains(s, FileEp.temp_mark()), String.ends_with(s, ".tmp")))

# the last segment of rest
def FileEp.last(rest: String) -> String:
  Maybe.default(&2, String, List.last(&2, String, String.split(rest, '/')), "")

# rest names a file resource: a valid path whose last segment is not the
# name of a temporary file
def FileEp.is_resource(+rest: String) -> Bool:
  Bool.and(Glob.is_path(rest), Bool.not(FileEp.is_temp(FileEp.last(rest))))

# rest, when it names a file resource
def FileEp.resource(+rest: String) -> Maybe<&2, String>:
  Shared.Bool.when(Maybe<&2, String>, FileEp.is_resource(rest), u => Some{rest}, u => None{})

# The OS path of a file URI (RFC 8089): the scheme is "file", the authority
# is absent, empty or "localhost", and the path is the OS path; a path like
# "/C:/repo" names the Windows path "C:/repo". Percent-encoded characters
# are not decoded yet: a '%' is taken as itself.

# the authority a names this machine: none, empty or "localhost"
def FileEp.local(a: Maybe<&2, String>) -> Bool:
  match a:
    case None{}:
      True{}
    case Some{+x}:
      Bool.or(String.is_empty(x), String.eq(x, "localhost"))

# p starts with '/', a letter, then ':', as "/C:/repo" does
def FileEp.is_drive(p: String) -> Bool:
  match p:
    case SCon{s, SCon{c, SCon{k, t}}}:
      Bool.and(
        U32.is_eq(Char.to_u32(s), 47),
        Bool.and(Char.is_alpha(c), U32.is_eq(Char.to_u32(k), 58))
      )
    case _:
      False{}

# the OS path of the URI path p
def FileEp.os_path(+p: String) -> String:
  Shared.Bool.when(String, FileEp.is_drive(p), u => String.drop(p, 1n), u => p)

# the OS path of the file URI u, or None for a URI that is not a local
# file URI
def FileEp.root_of(u: Shared.Uri) -> Maybe<&2, String>:
  match u:
    case Shared.Uri{sc, a, p}:
      Shared.Bool.when(
        Maybe<&2, String>,
        Bool.and(String.eq(sc, "file"), FileEp.local(a)),
        v => Some{FileEp.os_path(p)},
        v => None{}
      )

# the OS path of rest below the root: the root, '/', then the UTF-8 of rest
def FileEp.path(root: Shared.Bytes(), rest: String) -> Shared.Bytes():
  List.append(&2, U32, root, 47 <> Text.Text.encode(rest))

# the segments of rest but the last, joined by '/': its directory below
# the root, "" at the top
def FileEp.dir(rest: String) -> String:
  +segs = String.split(rest, '/')
  String.join(List.take(&2, String, segs, Nat.sub(List.length(&2, String, segs), 1n)), "/")

# a rest that names no file resource is never a resource
law resource_needs_path:
  for rest: String
  for h: {FileEp.is_resource(rest) == False{}: Bool}
  {FileEp.resource(rest) == None{}: Maybe<&2, String>}

# Probes
# ------

# What the file system holds at a path. Other: a link, a device, a socket,
# or anything that is not a regular file or a directory. Links are not
# followed: a link is not the file it points to.
type Entry is Data:
  KFile{}
  KDir{}
  KOther{}

# What a probe of a path answers, without following a last link. Found:
# the kind, and the device it lives on (0 where the OS does not tell).
# NotFound: the OS says no entry is there (ENOENT): every directory above it
# could be searched, and one of them lacks the next name. Failed: any other
# error, with its code and text; it tells nothing about the entry.
type Probe is Data:
  Found{entry: Entry, device: U32}
  NotFound{}
  Failed{code: U32, text: String}

# the probe of the OS path p
def FileFx.probe(path: Shared.Bytes()) -> IO(Probe):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# An open file endpoint: the OS path of its root, and the device the root
# was on when it was opened, or None when the root was not there then.
type Root is Data:
  Root{path: Shared.Bytes(), device: Maybe<&2, U32>}

# the OS path of the root
def Root.path(r: Root) -> Shared.Bytes():
  match r:
    case Root{p, d}:
      p

# the device the root was on when the endpoint opened
def Root.device(r: Root) -> Maybe<&2, U32>:
  match r:
    case Root{p, d}:
      d

# What to do for a resource. ReadIt: a regular file is there. KnownAbsent:
# the endpoint knows nothing is there. CannotTell: anything else, with why.
type Decision is Data:
  ReadIt{}
  KnownAbsent{}
  CannotTell{reason: String}

# the root is still the directory it was: a directory, on the device it
# was on when the endpoint opened (any device when it was not there then)
def FileEp.root_holds(device: Maybe<&2, U32>, root: Probe) -> Bool:
  match device root:
    case Some{e} Found{KDir{}, d}:
      U32.is_eq(d, e)
    case None{} Found{KDir{}, d}:
      True{}
    case _ _:
      False{}

# why the root does not hold
def FileEp.root_why(root: Probe) -> String:
  match root:
    case Found{KDir{}, d}:
      "the root is on another device now (unmounted?)"
    case Found{k, d}:
      "the root is not a directory"
    case NotFound{}:
      "the root is missing"
    case Failed{c, t}:
      String.append("the root: ", t)

# the decision for the probe of a path whose root holds
def FileEp.decide.here(here: Probe) -> Decision:
  match here:
    case Found{KFile{}, d}:
      ReadIt{}
    case Found{KDir{}, d}:
      CannotTell{"a directory is there"}
    case Found{KOther{}, d}:
      CannotTell{"not a regular file (links are not followed)"}
    case NotFound{}:
      KnownAbsent{}
    case Failed{c, t}:
      CannotTell{t}

# the decision for rest, given the root and the probes of the root and of
# rest's path. Only a resource can be read or known absent, and only below a
# root that holds; every other case cannot tell, with its reason.
def FileEp.decide(+rest: String, r: Root, +root: Probe, here: Probe) -> Decision:
  match r:
    case Root{p, d}:
      d = d
      ok = Bool.and(FileEp.is_resource(rest), FileEp.root_holds(d, root))
      bad = Shared.Bool.when(
        String,
        FileEp.is_resource(rest),
        u => FileEp.root_why(root),
        u => String.append("not a file resource: ", rest)
      )
      Shared.Bool.when(Decision, ok, u => FileEp.decide.here(here), u => CannotTell{bad})

# the decision says nothing is there
def Decision.is_absent(d: Decision) -> Bool:
  match d:
    case KnownAbsent{}:
      True{}
    case _:
      False{}

# the decision says a file is there to read
def Decision.is_read(d: Decision) -> Bool:
  match d:
    case ReadIt{}:
      True{}
    case _:
      False{}

# never absent when unsure: known absent only when rest is a resource, the
# root holds, and the OS says no entry is there
law absent_only_when_known:
  for rest: String
  for r: Root
  for root: Probe
  for here: Probe
  for h: {Decision.is_absent(FileEp.decide(rest, r, root, here)) == True{}: Bool}
  {FileEp.is_resource(rest) == True{}: Bool} &
    ({FileEp.root_holds(Root.device(r), root) == True{}: Bool} & {here == NotFound{}: Probe})

# read only a resource below a root that holds, where a regular file is
law read_only_files:
  for rest: String
  for r: Root
  for root: Probe
  for here: Probe
  for h: {Decision.is_read(FileEp.decide(rest, r, root, here)) == True{}: Bool}
  {FileEp.is_resource(rest) == True{}: Bool} &
    {FileEp.root_holds(Root.device(r), root) == True{}: Bool}

# a rest that names no resource is never read and never known absent
law non_resource_cannot_tell:
  for rest: String
  for r: Root
  for root: Probe
  for here: Probe
  for h: {FileEp.is_resource(rest) == False{}: Bool}
  {
    Bool.or(
      Decision.is_read(FileEp.decide(rest, r, root, here)),
      Decision.is_absent(FileEp.decide(rest, r, root, here))
    )
      == False{}: Bool
  }

# Writes
# ------

# the rest of the temporary file that a Put of rest writes, with n to
# keep writers apart: in rest's directory, named "." + its last segment +
# the mark + n + ".tmp"
def FileEp.temp(+rest: String, n: U32) -> String:
  +dir = FileEp.dir(rest)
  +name = String.concat([".", FileEp.last(rest), FileEp.temp_mark(), U32.show(n), ".tmp"])
  Shared.Bool.when(String, String.is_empty(dir), u => name, u => String.concat([dir, "/", name]))

# the temporary file of a Put is never taken for a resource, so its reports
# and its name stay out of the history
law temp_is_temp:
  for rest: String
  for n: U32
  {FileEp.is_temp(FileEp.last(FileEp.temp(rest, n))) == True{}: Bool}

# the belief e holds on disk: present with that token, or known absent.
# Put checks it right before its rename; an outside writer that lands
# between that check and the rename is overwritten, and nothing can tell
# afterwards. Writes through the core are exact, because the core orders
# them before they reach the disk.
def FileEp.holds(e: Ep.Expect, d: Decision, token: Maybe<&2, Shared.Bytes()>) -> Bool:
  match e d token:
    case Ep.WasPresent{a} ReadIt{} Some{b}:
      Shared.Bytes.is_eq(a, b)
    case Ep.WasAbsent{} KnownAbsent{} _:
      True{}
    case _ _ _:
      False{}

# a belief in absence holds only when the endpoint knows nothing is there
law absence_holds_only_known:
  for d: Decision
  for t: Maybe<&2, Shared.Bytes()>
  for h: {FileEp.holds(Ep.WasAbsent{}, d, t) == True{}: Bool}
  {Decision.is_absent(d) == True{}: Bool}

# the write of a temporary file at path from, renamed over path to; the
# rename replaces to at once for every reader
def FileFx.rename(
  from: Shared.Bytes(),
  to: Shared.Bytes()
) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# the directory at path, with every missing directory above it
def FileFx.make_dirs(path: Shared.Bytes()) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# the file at path removed
def FileFx.remove(path: Shared.Bytes()) -> IO(Result<&1, &1, U32 & String, Unit>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# Listing
# -------

# every regular file below the root, each as its path relative to the root
# with '/' between segments, without following links (a link is skipped,
# as are directories that cannot be read); fails when root is not a
# directory now
def FileFx.list(root: Shared.Bytes()) -> IO(Result<&1, &1, U32 & String, List<&2, Shared.Bytes()>>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# Watching
# --------

# What the OS reports, with each path relative to the root, '/' between
# its segments, as bytes. RawTouched: something at path was created,
# written, changed or removed. RawRenamed: the OS paired a rename. RawLost:
# the OS dropped events. RawRootGone: the root itself went away.
type Raw is Data:
  RawTouched{path: Shared.Bytes()}
  RawRenamed{from: Shared.Bytes(), to: Shared.Bytes()}
  RawLost{}
  RawRootGone{}

# a watcher of the root and everything below it, carried in a File handle:
# the watcher is an OS descriptor, and FileFx.unwatch releases it
def FileFx.watch(root: Shared.Bytes()) -> IO(Result<&1, &1, U32 & String, File>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# what the watcher w reported, waiting at most ms milliseconds for the
# first report; an empty list after the wait
def FileFx.next(w: File, ms: U32) -> IO(File & Result<&1, &1, U32 & String, List<&2, Raw>>):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# the watcher w released
def FileFx.unwatch(w: File) -> IO(Unit):
  import "./effs/file_fx.c"
  import "./effs/file_fx.js"

# A report with each path read as UTF-8: None when its bytes are not UTF-8,
# which no resource name can hold.
type Report is Data:
  Touched{path: Maybe<&2, String>}
  Renamed{from: Maybe<&2, String>, to: Maybe<&2, String>}
  Dropped{}
  RootGone{}

# What the core hears from the endpoint. About: a signal for one resource.
# Moved: a rename that the OS paired, for the core's moved-from edges.
# AllOverflowed: reports were dropped, so every watched stream must fetch
# again. AllLost: the root went away, so every stream is unreachable.
type Notice is Data:
  About{path: String, signal: Ep.Signal}
  Moved{from: String, to: String}
  AllOverflowed{}
  AllLost{reason: String}

# a report path, when it names a file resource
def FileEp.path_of(p: Maybe<&2, String>) -> Maybe<&2, String>:
  match p:
    case None{}:
      None{}
    case Some{r}:
      FileEp.resource(r)

# a hint for the resource n, if any
def FileEp.hint.of(n: Maybe<&2, String>) -> List<&2, Notice>:
  match n:
    case None{}:
      []
    case Some{x}:
      [About{x, Ep.Hinted{}}]

# a hint for the resource at p, if any
def FileEp.hint(p: Maybe<&2, String>) -> List<&2, Notice>:
  FileEp.hint.of(FileEp.path_of(p))

# the Moved notice of a rename, when both ends name resources
def FileEp.moved(a: Maybe<&2, String>, b: Maybe<&2, String>) -> List<&2, Notice>:
  match a b:
    case Some{x} Some{y}:
      [Moved{x, y}]
    case _ _:
      []

# what the core hears of e. A report is a hint, never data: the core
# fetches to learn what is there, so a removal is a hint too, and the fetch
# tells Absent from Unreachable.
def FileEp.notices(e: Report) -> List<&2, Notice>:
  match e:
    case Touched{p}:
      FileEp.hint(p)
    case Renamed{+a, +b}:
      m = FileEp.moved(FileEp.path_of(a), FileEp.path_of(b))
      List.append(&2, Notice, m, List.append(&2, Notice, FileEp.hint(a), FileEp.hint(b)))
    case Dropped{}:
      [AllOverflowed{}]
    case RootGone{}:
      [AllLost{"the root went away"}]

# every About among ns carries a hint and names a file resource
def Notice.all_hints(ns: List<&2, Notice>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{About{r, Ep.Hinted{}}, t}:
      List.all.if(u => Notice.all_hints(t), FileEp.is_resource(r))
    case Con{About{n, s}, t}:
      False{}
    case Con{x, t}:
      Notice.all_hints(t)

# reports are hints only, and only about file resources
law notices_are_hints:
  for e: Report
  {Notice.all_hints(FileEp.notices(e)) == True{}: Bool}
