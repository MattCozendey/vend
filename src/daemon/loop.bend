import Base
import ../core/impl.bend as CoreImpl
import ../core/loop.bend as CoreLoop
import ../core/spec.bend as Core
import ../endpoints/file/impl.bend as FileImpl
import ../endpoints/file/spec.bend as File
import ../endpoints/spec.bend as Ep
import ../glob/impl.bend as GlobImpl
import ../glob/spec.bend as Glob
import ../hash/spec.bend as Hash
import ../history/spec.bend as History
import ../journal/impl.bend as J
import ../journal/spec.bend as Journal
import ../lines/spec.bend as Lines
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../shared/tables.bend as Tables
import ../shared/uris.bend as Uris
import ../store/spec.bend as Store
import ../views/shared.bend as Vs
import ../views/text/impl.bend as TextImpl
import ../views/text/spec.bend as Text
import ./impl.bend as Impl
import ./spec.bend as Spec
import ./views.bend as Views

# The daemon's IO. `start-or-resume` takes the journal (its lock keeps a
# second daemon out), restores the shared state from it, listens on a TCP
# port of 127.0.0.1, writes the port and a random token to the file
# "daemon" of the data folder, mounts again what the mounts file lists, and
# then serves in the foreground until a Stop. Three kinds of task run in
# one event loop: one watcher per mount (it waits on the OS for reports and
# sends them on), one acceptor (it waits for connections, reads one
# request from each, and sends it on), and the core task, the only one
# that touches the state: it takes one event at a time from its inbox, so
# requests and reports are ordered. A watcher and the acceptor poll a stop
# channel between waits, so a Stop ends them within half a second. Every
# loop counts down fuel, as Bend needs; the fuel is far beyond any run.

# The fuel of every loop: the largest Nat literal.
def Fuel.max() -> Nat:
  4294967295n

# The text of an error.
def Err.why(e: U32 & String) -> String:
  (c, t) = e
  t

# What the core task hears (its inbox). WatchHeard: reports of the
# watcher of the mount at uri. WatchLost: that watcher stopped, with why.
# ClientAsked: the bytes of a request, and the connection to answer on.
type Inbox is Type:
  WatchHeard{uri: String, notices: List<&2, File.Notice>}
  WatchLost{uri: String, why: String}
  ClientAsked{bytes: Octets.Bytes(), socket: Socket}

# A watched mount: its URI, its root, and the channel that stops its
# watcher.
type Watch is Data:
  Watch{uri: String, root: File.Root, stop: Chan(Unit)}

# the line of an author
def Report.author(a: History.Author) -> String:
  match a:
    case History.Agent{n}:
      n
    case History.Outside{}:
      "Outside"

# the line the daemon prints for an output; commands go to the endpoint and
# records to the journal, so neither reaches here
def Report.line(o: Core.Output) -> IO(Unit):
  match o:
    case Core.Recorded{n, x, a}:
      IO.print(
        String.concat(
          ["recorded ", Resources.Name.show(n), " ", Hash.Hash.hex(x), " by ", Report.author(a)]
        )
      )
    case Core.Refused{n, hs}:
      IO.print("refused " ++ Resources.Name.show(n))
    case Core.Failed{n, p}:
      IO.print("failed " ++ Resources.Name.show(n))
    case Core.Stopped{}:
      IO.pure(Unit, Unit{})
    case Core.Command{p, k}:
      IO.pure(Unit, Unit{})
    case Core.Logged{r}:
      IO.pure(Unit, Unit{})

# Wire
# ----
# A message on a connection is its length (LEB128), then its bytes.

# the bytes of the message, when acc holds all of it
def Wire.whole(m: Maybe<&2, J.Got<Nat>>) -> Maybe<&2, Octets.Bytes()>:
  match m:
    case Some{J.Got{+n, +r}}:
      Bools.Bool.when(
        Maybe<&2, Octets.Bytes()>,
        Nat.is_le(n, List.length(&2, U32, r)),
        u => Some{List.take(&2, U32, r, n)},
        u => None{}
      )
    case None{}:
      None{}

# the message read so far into acc, after one more read
def Wire.more(
  s: Socket & Poll<&1, &1, Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>, Unit>,
  acc: Octets.Bytes(),
  k: Socket -> Octets.Bytes() -> IO(Socket & Maybe<&2, Octets.Bytes()>)
) -> IO(Socket & Maybe<&2, Octets.Bytes()>):
  (sock, p) = s
  match p:
    case Ready{Done{Some{chunk}}}:
      k(sock, List.append(&2, U32, acc, chunk))
    case _:
      IO.pure(Socket & Maybe<&2, Octets.Bytes()>, (sock, None{}))

# the message when it is whole, else one more read and k
def Wire.read.at(
  m: Maybe<&2, Octets.Bytes()>,
  sock: Socket,
  acc: Octets.Bytes(),
  k: Socket -> Octets.Bytes() -> IO(Socket & Maybe<&2, Octets.Bytes()>)
) -> IO(Socket & Maybe<&2, Octets.Bytes()>):
  match m:
    case Some{b}:
      IO.pure(Socket & Maybe<&2, Octets.Bytes()>, (sock, Some{b}))
    case None{}:
      do IO<Socket & Maybe<&2, Octets.Bytes()>>:
        s: Socket
          & Poll<
            &1,
            &1,
            Result<&1, &1, U32 & String, Maybe<&1, List<&2, U32>>>,
            Unit> <- TCP.try_recv_bytes(sock, 65536, 2000)
        Wire.more(s, acc, k)

# the message on sock, read in chunks; None when it does not come whole
# within the reads that fuel allows (each waits at most 2 seconds)
def Wire.read.go(
  fuel: Nat,
  sock: Socket,
  +acc: Octets.Bytes()
) -> IO(Socket & Maybe<&2, Octets.Bytes()>):
  match fuel:
    case 0n:
      IO.pure(Socket & Maybe<&2, Octets.Bytes()>, (sock, None{}))
    case 1n+f:
      Wire.read.at(Wire.whole(J.Leb.read(acc)), sock, acc, s2 => a2 => Wire.read.go(f, s2, a2))

# the message on sock, within at most 64 reads
def Wire.read(sock: Socket) -> IO(Socket & Maybe<&2, Octets.Bytes()>):
  Wire.read.go(64n, sock, [])

# the socket closed after a send
def Wire.sent(r: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Unit):
  (sock, x) = r
  Socket.close(sock)

# the message b sent on sock, which then closes
def Wire.send(sock: Socket, b: Octets.Bytes()) -> IO(Unit):
  do IO<Unit>:
    r: Socket
      & Result<
        &1,
        &1,
        (U32 & String) & List<&2, U32>,
        Unit> <- TCP.send_bytes(sock, Store.Bytes.framed(b))
    Wire.sent(r)

# Watchers
# --------

# the reports ns sent on to the core task, when there are any
def Watcher.tell(inbox: Chan(Inbox), uri: String, ns: List<&2, File.Notice>) -> IO(Unit):
  match ns:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{n, t}:
      do IO<Unit>:
        r: Result<&1, &1, Inbox, Unit> <- Chan.send(Inbox, inbox, WatchHeard{uri, Con{n, t}})
        return Unit{}

# after a wait: the reports sent on and k; or the failure sent on and the
# watcher released
def Watcher.got(
  r: File & Result<&1, &1, U32 & String, List<&2, File.Notice>>,
  inbox: Chan(Inbox),
  uri: String,
  k: File -> IO(Unit)
) -> IO(Unit):
  (w, res) = r
  match res:
    case Fail{e}:
      do IO<Unit>:
        FileImpl.FileEp.unwatch(w)
        x: Result<&1, &1, Inbox, Unit> <- Chan.send(Inbox, inbox, WatchLost{uri, Err.why(e)})
        return Unit{}
    case Done{ns}:
      do IO<Unit>:
        Watcher.tell(inbox, uri, ns)
        k(w)

# the watcher released when its stop channel spoke (or closed), else k
def Watcher.polled(
  p: Poll<&1, &1, Maybe<&1, Unit>, Unit>,
  w: File,
  k: File -> IO(Unit)
) -> IO(Unit):
  match p:
    case Ready{m}:
      FileImpl.FileEp.unwatch(w)
    case Wait{u}:
      k(w)

# the watcher w of the mount at uri: wait at most half a second, send the
# reports on, and again, until stop speaks or fuel runs out
def Watcher.go(
  fuel: Nat,
  +uri: String,
  w: File,
  +inbox: Chan(Inbox),
  +stop: Chan(Unit)
) -> IO(Unit):
  match fuel:
    case 0n:
      FileImpl.FileEp.unwatch(w)
    case 1n+f:
      do IO<Unit>:
        p: Poll<&1, &1, Maybe<&1, Unit>, Unit> <- Chan.try_recv(Unit, stop, 0)
        Watcher.polled(p, w, w2 => do IO<Unit>:
          r: File & Result<&1, &1, U32 & String, List<&2, File.Notice>> <- FileImpl.FileEp.next(w2, 500)
          Watcher.got(r, inbox, uri, w3 => Watcher.go(f, uri, w3, inbox, stop)))

# Acceptor
# --------

# the request read from a connection sent on to the core task, or the
# connection closed when no whole request came
def Acceptor.read(r: Socket & Maybe<&2, Octets.Bytes()>, inbox: Chan(Inbox)) -> IO(Unit):
  (sock, m) = r
  match m:
    case None{}:
      Socket.close(sock)
    case Some{b}:
      do IO<Unit>:
        x: Result<&1, &1, Inbox, Unit> <- Chan.send(Inbox, inbox, ClientAsked{b, sock})
        return Unit{}

# after a wait for a connection: its request read and sent on, then k
def Acceptor.accepted(
  r: Listener & Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit>,
  inbox: Chan(Inbox),
  k: Listener -> IO(Unit)
) -> IO(Unit):
  (l, p) = r
  match p:
    case Ready{Done{sock}}:
      do IO<Unit>:
        m: Socket & Maybe<&2, Octets.Bytes()> <- Wire.read(sock)
        Acceptor.read(m, inbox)
        k(l)
    case Ready{Fail{e}}:
      k(l)
    case Wait{u}:
      k(l)

# the listener closed when the stop channel spoke (or closed), else k
def Acceptor.polled(
  p: Poll<&1, &1, Maybe<&1, Unit>, Unit>,
  l: Listener,
  k: Listener -> IO(Unit)
) -> IO(Unit):
  match p:
    case Ready{m}:
      Listener.close(l)
    case Wait{u}:
      k(l)

# the acceptor: wait at most half a second for a connection, read its one
# request, send it on, and again, until stop speaks or fuel runs out
def Acceptor.go(fuel: Nat, l: Listener, +inbox: Chan(Inbox), +stop: Chan(Unit)) -> IO(Unit):
  match fuel:
    case 0n:
      Listener.close(l)
    case 1n+f:
      do IO<Unit>:
        p: Poll<&1, &1, Maybe<&1, Unit>, Unit> <- Chan.try_recv(Unit, stop, 0)
        Acceptor.polled(p, l, l2 => do IO<Unit>:
          r: Listener & Poll<&1, &1, Result<&1, &1, U32 & String, Socket>, Unit> <- TCP.try_accept(l2, 500)
          Acceptor.accepted(r, inbox, l3 => Acceptor.go(f, l3, inbox, stop)))

# Files of the data folder
# ------------------------

# the bytes of a path in the data folder d
def Data.path(d: String, name: String) -> Octets.Bytes():
  CoreLoop.Log.path(d, name)

# the bytes b written whole to the file name of d: to a temporary file,
# synced, then renamed over it; None, or why it failed
def Data.write(+d: String, +name: String, b: Octets.Bytes()) -> IO(Maybe<&2, String>):
  +tmp = Data.path(d, String.append(name, ".tmp"))
  do IO<Maybe<&2, String>>:
    o: Result<&1, &1, U32 & String, File> <- File.open_bytes(tmp, "w")
    CoreLoop.Log.cut.opened(tmp, Data.path(d, name), b, o)

# the digit of a hex character, or None
def Hex.digit(c: Char) -> Maybe<&2, U32>:
  match c:
    case Chr{+x}:
      Bools.Bool.when(
        Maybe<&2, U32>,
        Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57)),
        u => Some{(x - 48: U32)},
        u => Bools.Bool.when(
          Maybe<&2, U32>,
          Bool.and(U32.is_ge(x, 97), U32.is_le(x, 102)),
          v => Some{(x - 87: U32)},
          v => None{}
        )
      )

# the byte of two hex digits
def Hex.byte(a: Maybe<&2, U32>, b: Maybe<&2, U32>) -> Maybe<&2, U32>:
  match a b:
    case Some{x} Some{y}:
      Some{((x << 4n) .|. y: U32)}
    case _ _:
      None{}

# x in front of the bytes m read
def Hex.cons(x: Maybe<&2, U32>, m: Maybe<&2, Octets.Bytes()>) -> Maybe<&2, Octets.Bytes()>:
  match x m:
    case Some{v} Some{r}:
      Some{v <> r}
    case _ _:
      None{}

# the bytes that lowercase hex text spells, or None
def Hex.bytes(s: String) -> Maybe<&2, Octets.Bytes()>:
  match s:
    case SNil{}:
      Some{[]}
    case SCon{a, SCon{b, t}}:
      Hex.cons(Hex.byte(Hex.digit(a), Hex.digit(b)), Hex.bytes(t))
    case _:
      None{}

# Where the daemon listens and its token, as the file "daemon" holds them:
# the port, a space, the token as hex.
type Door is Data:
  Door{port: U32, token: Octets.Bytes()}

# the text of a door
def Door.show(d: Door) -> String:
  match d:
    case Door{p, t}:
      String.concat([U32.show(p), " ", Hash.Hash.hex(t)])

# the door that two words spell
def Door.of(p: Maybe<&2, U32>, t: Maybe<&2, Octets.Bytes()>) -> Maybe<&2, Door>:
  match p t:
    case Some{x} Some{y}:
      Some{Door{x, y}}
    case _ _:
      None{}

# the door of the two words ws, or None
def Door.words(ws: List<&2, String>) -> Maybe<&2, Door>:
  match ws:
    case Con{p, Con{t, Nil{}}}:
      Door.of(U32.read(p), Hex.bytes(t))
    case _:
      None{}

# the door of the text of the file "daemon", or None
def Door.read(s: String) -> Maybe<&2, Door>:
  Door.words(String.split(String.trim(s), ' '))

# The core task
# -------------

# The state of the core task: the daemon, the watched mounts, the token,
# the data folder, its inbox, and the channel that stops the acceptor.
type Serve is Data:
  Serve{
    daemon: Spec.Daemon,
    watches: List<&2, Watch>,
    token: Octets.Bytes(),
    dir: String,
    inbox: Chan(Inbox),
    astop: Chan(Unit)
  }

# the daemon of st
def Serve.daemon(st: Serve) -> Spec.Daemon:
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      d

# the inbox of st
def Serve.inbox(st: Serve) -> Chan(Inbox):
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      ib

# st with the daemon d
def Serve.with(st: Serve, d: Spec.Daemon) -> Serve:
  match st:
    case Serve{d0, ws, tok, dir, ib, ast}:
      Serve{d, ws, tok, dir, ib, ast}

# the URI of a watch
def Watch.uri(w: Watch) -> String:
  match w:
    case Watch{u, r, sc}:
      u

# the root of the watched mount at uri, if there is one
def Watches.root(ws: List<&2, Watch>, +uri: String) -> Maybe<&2, File.Root>:
  match ws:
    case Nil{}:
      None{}
    case Con{Watch{u, r, sc}, t}:
      Bools.Bool.when(
        Maybe<&2, File.Root>,
        String.eq(u, uri),
        x => Some{r},
        x => Watches.root(t, uri)
      )

# ws without the watch of uri
def Watches.drop(ws: List<&2, Watch>, +uri: String) -> List<&2, Watch>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+w, +t}:
      Bools.Bool.when(
        List<&2, Watch>,
        String.eq(Watch.uri(w), uri),
        x => Watches.drop(t, uri),
        x => w <> Watches.drop(t, uri)
      )

# the watcher of each watch of ws told to stop: all of them, or those of uri
def Watches.stop(ws: List<&2, Watch>, +all: Bool, +uri: String) -> IO(Unit):
  match ws:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Watch{u, r, sc}, t}:
      do IO<Unit>:
        Bools.Bool.when(
          IO(Unit),
          Bool.or(all, String.eq(u, uri)),
          x => do IO<Unit>:
            e: Result<&1, &1, Unit, Unit> <- Chan.send(Unit, sc, Unit{})
            return Unit{},
          x => IO.pure(Unit, Unit{}))
        Watches.stop(t, all, uri)

# a line when the mounts file could not be written
def Serve.saved(e: Maybe<&2, String>) -> IO(Unit):
  match e:
    case None{}:
      IO.pure(Unit, Unit{})
    case Some{why}:
      IO.print("the mounts file could not be written: " ++ why)

# the mounts file written for the mounts of st
def Serve.save(st: Serve) -> IO(Unit):
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      do IO<Unit>:
        e: Maybe<
          &2,
          String> <- Data.write(dir, "mounts", Spec.Entries.encode(Spec.Daemon.entries(d)))
        Serve.saved(e)

# the daemon ended: every watcher and the acceptor told to stop, and the
# journal closed
def Serve.end(st: Serve, j: File, why: String) -> IO(Unit):
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      do IO<Unit>:
        Watches.stop(ws, True{}, "")
        e: Result<&1, &1, Unit, Unit> <- Chan.send(Unit, ast, Unit{})
        File.close(j)
        IO.print(why)

# after a drain of the mount whose glob texts are gs: k of the daemon with
# the result put back, or the daemon ended when the journal broke
def Serve.drained(
  dr: CoreLoop.Drained,
  +st: Serve,
  gs: List<&2, String>,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match dr:
    case CoreLoop.Ran{c, j}:
      k(Serve.with(st, Spec.Daemon.put(Serve.daemon(st), c, gs)), j)
    case CoreLoop.Broke{why}:
      match st:
        case Serve{d, ws, tok, dir, ib, ast}:
          do IO<Unit>:
            Watches.stop(ws, True{}, "")
            e: Result<&1, &1, Unit, Unit> <- Chan.send(Unit, ast, Unit{})
            IO.die(Unit, 1, "vend stopped: the journal could not be written: " ++ why)

# the inputs of the reports ns of a mount whose core is c, with the paths
# listed again when reports were lost
def Serve.inputs(
  ns: List<&2, File.Notice>,
  c: Core.Core,
  listed: List<&2, String>
) -> List<&2, Core.Input>:
  +known = CoreLoop.Loop.known(c)
  List.append(
    &2,
    Core.Input,
    CoreLoop.Loop.inputs(ns, known, CoreLoop.Loop.each(known, Ep.Hinted{})),
    CoreLoop.Loop.hints(listed)
  )

# the reports of the mount l, whose root is root, stepped through its core
def Serve.heard.at(
  lm: Maybe<&2, Spec.Local>,
  rm: Maybe<&2, File.Root>,
  +st: Serve,
  j: File,
  +ns: List<&2, File.Notice>,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match lm rm:
    case Some{+l} Some{+root}:
      +c = Spec.Daemon.core(Serve.daemon(st), l)
      do IO<Unit>:
        listed: List<&2, String> <- CoreLoop.Loop.relist(root, CoreLoop.Loop.overflowed(ns))
        dr: CoreLoop.Drained <- CoreLoop.Loop.drain(
          ~Report.line,
          CoreLoop.Loop.budget(),
          root,
          j,
          c,
          Serve.inputs(ns, c, listed)
        )
        Serve.drained(dr, st, Spec.Local.globs(l), k)
    case _ _:
      k(st, j)

# the reports of the watcher of the mount at uri
def Serve.heard(
  +st: Serve,
  j: File,
  +uri: String,
  ns: List<&2, File.Notice>,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      Serve.heard.at(Spec.Daemon.local(d, uri), Watches.root(ws, uri), st, j, ns, k)

# rest, with the rule m in front when there is one
def Rules.put(m: Maybe<&2, Glob.Rule>, rest: List<&2, Glob.Rule>) -> List<&2, Glob.Rule>:
  match m:
    case None{}:
      rest
    case Some{r}:
      r <> rest

# the rules that the glob texts read as; Cli checked them
def Rules.of(gs: List<&2, String>) -> List<&2, Glob.Rule>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{g, t}:
      Rules.put(Glob.Rule.read(g), Rules.of(t))

# st with one more watch
def Serve.watching(st: Serve, w: Watch) -> Serve:
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      Serve{d, w <> ws, tok, dir, ib, ast}

# the mount once its watcher started: the watcher spawned, the mount added
# with its streams primed from its line, the root listed and every listed
# and known file fetched; k gets Mounted with the space id
def Serve.mount.watched(
  wr: Result<&1, &1, U32 & String, File>,
  +id: String,
  +root: File.Root,
  +u: Uris.Uri,
  +st: Serve,
  j: File,
  +gs: List<&2, String>,
  ln: String,
  a: History.Author,
  k: Serve -> File -> Spec.Response -> IO(Unit)
) -> IO(Unit):
  match wr:
    case Fail{e}:
      k(st, j, Spec.Denied{Err.why(e)})
    case Done{w}:
      +uri = Uris.Uri.show(u)
      +l = {
        Spec.Local{
          Core.Mount{id, ln, u, Rules.of(gs), a},
          gs,
          Tables.Table.new(Ep.Stream),
          Tables.Table.new(Maybe<&2, Resources.Name>),
          []
        }: Spec.Local
      }
      +d1 = Spec.Daemon.mount(Serve.daemon(st), l)
      +c0 = CoreImpl.Replay.primed.core(Spec.Daemon.core(d1, l))
      do IO<Unit>:
        +stop: Chan(Unit) <- Chan.new(Unit, 1)
        IO.spawn(Unit, Watcher.go(Fuel.max(), uri, w, Serve.inbox(st), stop))
        ns: List<&2, String> <- FileImpl.FileEp.list(root)
        ins: List<
          &2,
          Core.Input> = List.append(
          &2,
          Core.Input,
          CoreLoop.Loop.hints(ns),
          CoreLoop.Loop.each(CoreLoop.Loop.known(c0), Ep.Hinted{})
        )
        dr: CoreLoop.Drained <- CoreLoop.Loop.drain(
          ~Report.line,
          CoreLoop.Loop.budget(),
          root,
          j,
          c0,
          ins
        )
        Serve.drained(dr, Serve.watching(
          Serve.with(st, d1),
          Watch{uri, root, stop}
        ), gs, +s2 => j2 => do IO<Unit>:
          Serve.save(s2)
          k(s2, j2, Spec.Mounted{id}))

# the mount once the space of its root is known
def Serve.mount.spaced(
  sp: Result<&2, &2, String, String>,
  +root: File.Root,
  u: Uris.Uri,
  st: Serve,
  j: File,
  gs: List<&2, String>,
  ln: String,
  a: History.Author,
  k: Serve -> File -> Spec.Response -> IO(Unit)
) -> IO(Unit):
  match sp:
    case Fail{e}:
      k(st, j, Spec.Denied{e})
    case Done{id}:
      do IO<Unit>:
        wr: Result<&1, &1, U32 & String, File> <- FileImpl.FileEp.watch(root)
        Serve.mount.watched(wr, id, root, u, st, j, gs, ln, a, k)

# the mount once the OS path of its root is known
def Serve.mount.os(
  mo: Maybe<&2, String>,
  u: Uris.Uri,
  st: Serve,
  j: File,
  gs: List<&2, String>,
  ln: String,
  a: History.Author,
  k: Serve -> File -> Spec.Response -> IO(Unit)
) -> IO(Unit):
  match mo:
    case None{}:
      k(st, j, Spec.Denied{"not a local file URI"})
    case Some{os}:
      do IO<Unit>:
        +root: File.Root <- FileImpl.FileEp.open(os)
        sp: Result<&2, &2, String, String> <- CoreLoop.Loop.space(root)
        Serve.mount.spaced(sp, root, u, st, j, gs, ln, a, k)

# the mount once its URI text is read
def Serve.mount.uri(
  mu: Maybe<&2, Uris.Uri>,
  utext: String,
  st: Serve,
  j: File,
  gs: List<&2, String>,
  ln: String,
  a: History.Author,
  k: Serve -> File -> Spec.Response -> IO(Unit)
) -> IO(Unit):
  match mu:
    case None{}:
      k(st, j, Spec.Denied{String.append("not a URI: ", utext)})
    case Some{+u}:
      Serve.mount.os(File.FileEp.root_of(u), u, st, j, gs, ln, a, k)

# the mount of the root at the URI text utext, on the line ln, versioning
# what the glob texts gs select, what it sees saved signed by a; k gets the
# response
def Serve.mount(
  st: Serve,
  j: File,
  +utext: String,
  gs: List<&2, String>,
  ln: String,
  a: History.Author,
  k: Serve -> File -> Spec.Response -> IO(Unit)
) -> IO(Unit):
  Serve.mount.uri(Uris.Uri.read(utext), utext, st, j, gs, ln, a, k)

# st without the mount at uri, its watcher told to stop and the mounts file
# written
def Serve.unmount(st: Serve, +uri: String) -> IO(Serve):
  match st:
    case Serve{d, +ws, tok, dir, ib, ast}:
      +st2 = {Serve{Spec.Daemon.unmount(d, uri), Watches.drop(ws, uri), tok, dir, ib, ast}: Serve}
      do IO<Serve>:
        Watches.stop(ws, False{}, uri)
        Serve.save(st2)
        return st2

# the line key of the mount l
def Local.line(l: Spec.Local) -> String:
  match l:
    case Spec.Local{Core.Mount{sp, ln, r, g, a}, gs, ss, ms, ns}:
      Lines.Line.key(sp, ln)

# the mounts of st
def Serve.mounts(st: Serve) -> List<&2, Spec.Local>:
  Spec.Daemon.mounts(Serve.daemon(st))

# the watches of st
def Serve.watches(st: Serve) -> List<&2, Watch>:
  match st:
    case Serve{d, ws, tok, dir, ib, ast}:
      ws

# the core c with the content of each carry of cs that it tracks believed at
# once: the line already holds it, so the answer to its Put shows no new
# version
def Carry.streams(cs: List<&2, Spec.Carry>, +c: Core.Core) -> Core.Core:
  match cs:
    case Nil{}:
      c
    case Con{Spec.Carry{+p, b}, +t}:
      +h = Hash.Hash.blake3(b)
      Bools.Bool.when(
        Core.Core,
        CoreImpl.Core.tracks(c, p),
        u => Carry.streams(
          t,
          CoreImpl.Core.set_stream(c, p, Ep.Stream{Ep.Present{h}, Some{h}, False{}, False{}})
        ),
        u => Carry.streams(t, c)
      )

# a Put of the content of each carry that the core c tracks, to the
# endpoint at root, with what c believes is there; the inputs of the
# answers
def Carry.puts(
  +root: File.Root,
  +c: Core.Core,
  cs: List<&2, Spec.Carry>
) -> IO(List<&2, Core.Input>):
  match cs:
    case Nil{}:
      IO.pure(List<&2, Core.Input>, [])
    case Con{Spec.Carry{+p, b}, +t}:
      Bools.Bool.when(
        IO(List<&2, Core.Input>),
        CoreImpl.Core.tracks(c, p),
        u => do IO<List<&2, Core.Input>>:
          ss: List<&2, Ep.Signal> <- FileImpl.FileEp.put(root, p, b, CoreImpl.Core.belief(Ep.Stream.last(Core.Core.stream(c, p))))
          rest: List<&2, Core.Input> <- Carry.puts(root, c, t)
          return List.append(&2, Core.Input, CoreLoop.Loop.about(p, ss), rest),
        u => Carry.puts(root, c, t))

# the carries written to the working copy of the mount l, whose root is
# found (none for a mount on another line)
def Serve.carry.at(
  +l: Spec.Local,
  rm: Maybe<&2, File.Root>,
  +cs: List<&2, Spec.Carry>,
  +st: Serve,
  j: File,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match rm:
    case None{}:
      k(st, j)
    case Some{+root}:
      +c = Spec.Daemon.core(Serve.daemon(st), l)
      do IO<Unit>:
        ins: List<&2, Core.Input> <- Carry.puts(root, c, cs)
        dr: CoreLoop.Drained <- CoreLoop.Loop.drain(
          ~Report.line,
          CoreLoop.Loop.budget(),
          root,
          j,
          Carry.streams(cs, c),
          ins
        )
        Serve.drained(dr, st, Spec.Local.globs(l), k)

# the root of the mount l, when it is on the line whose key is key
def Serve.carry.root(+l: Spec.Local, key: String, ws: List<&2, Watch>) -> Maybe<&2, File.Root>:
  Bools.Bool.when(
    Maybe<&2, File.Root>,
    String.eq(Local.line(l), key),
    u => Watches.root(ws, Spec.Local.uri(l)),
    u => None{}
  )

# the carries written to the working copy of every mount of ls on the line
# whose key is key
def Serve.carry(
  ls: List<&2, Spec.Local>,
  +key: String,
  +cs: List<&2, Spec.Carry>,
  +st: Serve,
  j: File,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match ls:
    case Nil{}:
      k(st, j)
    case Con{+l, t}:
      Serve.carry.at(
        l,
        Serve.carry.root(l, key, Serve.watches(st)),
        cs,
        st,
        j,
        s2 => j2 => Serve.carry(t, key, cs, s2, j2, k)
      )

# after the records of a command are logged: the content carried to the
# working copies of its line, then the answer; or the daemon ended when the
# journal broke
def Serve.logged(
  w: File & Result<&1, &1, U32 & String, Unit>,
  +st: Serve,
  sock: Socket,
  r: Spec.Response,
  key: String,
  cs: List<&2, Spec.Carry>,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  (j, res) = w
  match res:
    case Fail{e}:
      do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(Spec.Denied{"the journal could not be written"}))
        Serve.drained(CoreLoop.Broke{Err.why(e)}, st, [], k)
    case Done{u}:
      Serve.carry(Serve.mounts(st), key, cs, st, j, s2 => j2 => do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(r))
        k(s2, j2))

# what the daemon does about a handled command: its records appended and
# synced before anything else, and replayed into the daemon
def Serve.asked(
  h: Spec.Handled,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match h:
    case Spec.Handled{+rs, r, key, cs}:
      do IO<Unit>:
        w: File & Result<&1, &1, U32 & String, Unit> <- CoreLoop.Loop.log(j, rs)
        Serve.logged(
          w,
          Serve.with(st, Spec.Daemon.replay(Serve.daemon(st), rs)),
          sock,
          r,
          key,
          cs,
          k
        )

# the bytes of the resource at u through the endpoint e of its scheme
def Source.at(
  e: Maybe<&2, Resources.Endpoint>,
  u: Uris.Uri
) -> IO(Result<&2, &2, String, Octets.Bytes()>):
  match e:
    case None{}:
      IO.pure(Result<&2, &2, String, Octets.Bytes()>, Fail{"no endpoint serves its scheme"})
    case Some{Resources.FileEndpoint{}}:
      FileImpl.FileEp.source(u)

# the bytes of the resource at the URI m, through its endpoint, or why
# they cannot be had
def Source.fetch(m: Maybe<&2, Uris.Uri>) -> IO(Result<&2, &2, String, Octets.Bytes()>):
  match m:
    case None{}:
      IO.pure(Result<&2, &2, String, Octets.Bytes()>, Fail{"it is not a URI"})
    case Some{+u}:
      Source.at(Resources.Endpoint.of(u), u)

# the command c of the agent a handled with the fetched bytes, or refused
# with why the source could not be read
def Serve.fetched(
  r: Result<&2, &2, String, Octets.Bytes()>,
  t: String,
  a: String,
  c: Spec.Command,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match r:
    case Done{b}:
      Serve.asked(Spec.Daemon.handle(Serve.daemon(st), a, c, b), st, j, sock, k)
    case Fail{why}:
      do IO<Unit>:
        Wire.send(
          sock,
          Spec.Response.encode(
            Spec.Said{False{}, [String.concat(["refused: cannot read ", t, ": ", why])]}
          )
        )
        k(st, j)

# the command c of the agent a handled: with the bytes of its source when
# it names one (fetched first), else with the request's data b
def Serve.sourced(
  m: Maybe<&2, String>,
  a: String,
  c: Spec.Command,
  b: Octets.Bytes(),
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match m:
    case None{}:
      Serve.asked(Spec.Daemon.handle(Serve.daemon(st), a, c, b), st, j, sock, k)
    case Some{+t}:
      do IO<Unit>:
        r: Result<&2, &2, String, Octets.Bytes()> <- Source.fetch(Uris.Uri.read(t))
        Serve.fetched(r, t, a, c, st, j, sock, k)

# Checkouts
# ---------
# A checkout is a mount that the daemon makes at the root Daemon.plan
# gives, inside a mount the user made, with the agent as its author. Its
# folder gets the space file and the line's files; release unmounts it and
# removes that folder only (FileFx.remove_tree follows no link).

# the answer Said on sock, then k
def Serve.said(
  sock: Socket,
  ok: Bool,
  ls: List<&2, String>,
  st: Serve,
  j: File,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  do IO<Unit>:
    Wire.send(sock, Spec.Response.encode(Spec.Said{ok, ls}))
    k(st, j)

# the OS path of the root of a plan, as text ("?" when it is no local file)
def Checkout.os(p: Spec.Plan) -> String:
  Maybe.default(&2, String, File.FileEp.root_of(Spec.Plan.root(p)), "?")

# the checkout mounted: answered when its space file named its space
# (same), else unmounted and refused
def Serve.checkout.filled(
  same: Bool,
  p: Spec.Plan,
  uri: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match same:
    case True{}:
      Serve.said(sock, True{}, [String.append("checked out at ", Checkout.os(p))], st, j, k)
    case False{}:
      do IO<Unit>:
        s2: Serve <- Serve.unmount(st, uri)
        Serve.said(sock, False{}, ["refused: the checkout folder holds another space"], s2, j, k)

# the checkout after its mount answered r
def Serve.checkout.mounted(
  r: Spec.Response,
  +p: Spec.Plan,
  uri: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match r:
    case Spec.Mounted{id}:
      Serve.checkout.filled(String.eq(id, Spec.Plan.space(p)), p, uri, st, j, sock, k)
    case Spec.Denied{why}:
      Serve.said(sock, False{}, [String.append("refused: ", why)], st, j, k)
    case _:
      Serve.said(sock, False{}, ["refused: the checkout was not mounted"], st, j, k)

# each carry written to the folder at root, where nothing is yet
def Checkout.write(+root: File.Root, cs: List<&2, Spec.Carry>) -> IO(Unit):
  match cs:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{Spec.Carry{p, b}, t}:
      do IO<Unit>:
        ss: List<&2, Ep.Signal> <- FileImpl.FileEp.put(root, p, b, Ep.WasAbsent{})
        Checkout.write(root, t)

# the checkout of the mount m once its folder is made: the space file and
# the files of its line written, then the folder mounted with the agent as
# its author, following the globs gs of the user's mount; its streams start
# from the line, so what it finds there records nothing
def Serve.checkout.at(
  m: Core.Mount,
  gs: List<&2, String>,
  p: Spec.Plan,
  os: String,
  +uri: String,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match m:
    case Core.Mount{+sp, +ln, r, g, a}:
      +d = Serve.daemon(st)
      cs = Impl.Answer.files(d, Spec.Daemon.line_in(d, sp, ln))
      do IO<Unit>:
        +root: File.Root <- FileImpl.FileEp.open(os)
        put: List<
          &2,
          Ep.Signal> <- FileImpl.FileEp.put(
          root,
          Core.Mount.space_file(),
          Text.Text.encode(sp),
          Ep.WasAbsent{}
        )
        Checkout.write(root, cs)
        Serve.mount(
          st,
          j,
          uri,
          gs,
          ln,
          a,
          s2 => j2 => res => Serve.checkout.mounted(res, p, uri, s2, j2, sock, k)
        )

# the checkout once its folder is made, or refused when it could not be
def Serve.checkout.made(
  mk: Result<&1, &1, U32 & String, Unit>,
  +p: Spec.Plan,
  os: String,
  uri: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match mk:
    case Fail{e}:
      Serve.said(
        sock,
        False{},
        [String.append("refused: cannot make the checkout folder: ", Err.why(e))],
        st,
        j,
        k
      )
    case Done{x}:
      Serve.checkout.at(
        Spec.Plan.mount(p),
        Spec.Local.globs(Spec.Plan.base(p)),
        p,
        os,
        uri,
        st,
        j,
        sock,
        k
      )

# the checkout at the OS path os: answered at once when it is mounted
# already (there), else its folder made
def Serve.checkout.new(
  there: Bool,
  p: Spec.Plan,
  +os: String,
  uri: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match there:
    case True{}:
      Serve.said(sock, True{}, [String.append("checked out at ", os)], st, j, k)
    case False{}:
      do IO<Unit>:
        mk: Result<&1, &1, U32 & String, Unit> <- File.FileFx.make_dirs(Text.Text.encode(os))
        Serve.checkout.made(mk, p, os, uri, st, j, sock, k)

# the checkout at the OS path mo: answered at once when it is mounted
# already, else made
def Serve.checkout.os(
  mo: Maybe<&2, String>,
  +p: Spec.Plan,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match mo:
    case None{}:
      Serve.said(sock, False{}, ["refused: the mount is not a local file URI"], st, j, k)
    case Some{os}:
      +uri = Uris.Uri.show(Spec.Plan.root(p))
      there = Maybe.is_some(&2, Spec.Local, Spec.Daemon.local(Serve.daemon(st), uri))
      Serve.checkout.new(there, p, os, uri, st, j, sock, k)

# the checkout of the plan, or refused with why there is none
def Serve.checkout.planned(
  pr: Result<&2, &2, String, Spec.Plan>,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match pr:
    case Fail{why}:
      Serve.said(sock, False{}, [String.append("refused: ", why)], st, j, k)
    case Done{+p}:
      Serve.checkout.os(File.FileEp.root_of(Spec.Plan.root(p)), p, st, j, sock, k)

# the release once the checkout is unmounted: its folder removed
def Serve.release.removed(
  rm: Result<&1, &1, U32 & String, Unit>,
  os: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match rm:
    case Fail{e}:
      Serve.said(
        sock,
        False{},
        [String.concat(["released, but its folder could not be removed: ", os, ": ", Err.why(e)])],
        st,
        j,
        k
      )
    case Done{x}:
      Serve.said(sock, True{}, [String.append("released ", os)], st, j, k)

# the release of the checkout at the OS path os, at uri, when it is
# mounted (there): unmounted, then its folder removed; else refused
def Serve.release.there(
  there: Bool,
  +os: String,
  uri: String,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match there:
    case True{}:
      do IO<Unit>:
        s2: Serve <- Serve.unmount(st, uri)
        rm: Result<&1, &1, U32 & String, Unit> <- File.FileFx.remove_tree(Text.Text.encode(os))
        Serve.release.removed(rm, os, s2, j, sock, k)
    case False{}:
      Serve.said(sock, False{}, [String.append("refused: no checkout of yours at ", os)], st, j, k)

# the release of the checkout at the OS path mo, at uri: refused unless
# it is mounted
def Serve.release.os(
  mo: Maybe<&2, String>,
  +uri: String,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match mo:
    case None{}:
      Serve.said(sock, False{}, ["refused: the mount is not a local file URI"], st, j, k)
    case Some{os}:
      there = Maybe.is_some(&2, Spec.Local, Spec.Daemon.local(Serve.daemon(st), uri))
      Serve.release.there(there, os, uri, st, j, sock, k)

# the release of the plan, or refused with why there is none
def Serve.release.planned(
  pr: Result<&2, &2, String, Spec.Plan>,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match pr:
    case Fail{why}:
      Serve.said(sock, False{}, [String.append("refused: ", why)], st, j, k)
    case Done{p}:
      +r = Spec.Plan.root(p)
      Serve.release.os(File.FileEp.root_of(r), Uris.Uri.show(r), st, j, sock, k)

# Verifying
# ---------
# `verify <line>` runs each resource's verifier (its view names one, or
# none) on the line's files as a folder shows them: the agent's checkout of
# the line, else a mount the user made that shows the line. Each runs to
# its end (or its timeout) before the daemon serves the next event.

# the OS path of the agent's checkout of the plan, when it is mounted
def Verify.checkout(d: Spec.Daemon, pr: Result<&2, &2, String, Spec.Plan>) -> Maybe<&2, String>:
  match pr:
    case Fail{why}:
      None{}
    case Done{+p}:
      Bools.Bool.when(
        Maybe<&2, String>,
        Maybe.is_some(&2, Spec.Local, Spec.Daemon.local(d, Uris.Uri.show(Spec.Plan.root(p)))),
        u => File.FileEp.root_of(Spec.Plan.root(p)),
        u => None{}
      )

# the OS path of the first mount of ms that the user made on the line
# whose key is key
def Verify.mount(ms: List<&2, Spec.Local>, +key: String) -> Maybe<&2, String>:
  match ms:
    case Nil{}:
      None{}
    case Con{+l, t}:
      Bools.Bool.when(
        Maybe<&2, String>,
        List.all.if(
          u => String.eq(Local.line(l), key),
          Maybe.is_none(&2, String, Spec.Author.agent(Spec.Local.author(l)))
        ),
        u => File.FileEp.root_of(Spec.Local.root(l)),
        u => Verify.mount(t, key)
      )

# the OS path of a mount the user made that shows the line found
def Verify.mounted(d: Spec.Daemon, ml: Maybe<&2, Lines.Line>) -> Maybe<&2, String>:
  match ml:
    case None{}:
      None{}
    case Some{l}:
      Verify.mount(Spec.Daemon.mounts(d), Lines.Line.id(l))

# the folder that shows the line that t names to the agent a
def Verify.folder(+d: Spec.Daemon, a: String, +t: String) -> Maybe<&2, String>:
  Maybe.or(
    &2,
    String,
    Verify.checkout(d, Spec.Daemon.plan(d, a, t)),
    Verify.mounted(d, Spec.Daemon.line_ref(d, t))
  )

# the files of the line found, as carries
def Verify.carries(d: Spec.Daemon, ml: Maybe<&2, Lines.Line>) -> List<&2, Spec.Carry>:
  match ml:
    case None{}:
      []
    case Some{l}:
      Impl.Answer.files(d, l)

# xs, as the list Process.run takes
def Verify.args(xs: List<&2, String>) -> List<String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      x <> Verify.args(t)

# the first n lines of ls that are not blank
def Verify.first(n: Nat, ls: List<&2, String>) -> List<&2, String>:
  match n ls:
    case 0n _:
      []
    case _ Nil{}:
      []
    case 1n+(+m) Con{+x, +t}:
      Bools.Bool.when(
        List<&2, String>,
        String.is_empty(String.trim(x)),
        u => Verify.first(1n+m, t),
        u => x <> Verify.first(m, t)
      )

# the verdict of the run of prog on the resource at path: its first lines
def Verify.said(
  path: String,
  prog: String,
  r: Result<&1, &1, U32 & String, U32 & (String & String)>
) -> String:
  match r:
    case Fail{e}:
      String.concat([path, ": could not run ", prog, ": ", Err.why(e)])
    case Done{(st, (out, err))}:
      String.concat(
        [path, ": ", String.join(Verify.first(3n, String.lines(String.append(out, err))), " / ")]
      )

# the verdict for the resource at path in the folder os, by its verifier
def Verify.one(m: Maybe<&2, Vs.Verifier>, os: String, +path: String) -> IO(String):
  match m:
    case None{}:
      IO.pure(String, String.append(path, ": no verifier"))
    case Some{Vs.Verifier{+prog, bf, af}}:
      file = String.append(Spec.Checkout.dir(os), path)
      args = Verify.args(List.append(&2, String, bf, file <> af))
      do IO<String>:
        r: Result<
          &1,
          &1,
          U32 & String,
          U32 & (String & String)> <- Process.run(prog, args, "", 1048576, 300000)
        return Verify.said(path, prog, r)

# the verdict for each carry's resource in the folder os
def Verify.run(cs: List<&2, Spec.Carry>, +os: String) -> IO(List<&2, String>):
  match cs:
    case Nil{}:
      IO.pure(List<&2, String>, [])
    case Con{Spec.Carry{+p, b}, t}:
      do IO<List<&2, String>>:
        x: String <- Verify.one(Views.View.verifier(p), os, p)
        rest: List<&2, String> <- Verify.run(t, os)
        return x <> rest

# the verification of the files cs in the folder found, answered on sock
def Serve.verify(
  mf: Maybe<&2, String>,
  cs: List<&2, Spec.Carry>,
  st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match mf:
    case None{}:
      Serve.said(sock, False{}, ["no folder shows this line; check it out first"], st, j, k)
    case Some{os}:
      do IO<Unit>:
        ls: List<&2, String> <- Verify.run(cs, os)
        Serve.said(sock, True{}, ls, st, j, k)

# what the daemon does about the action a, answering on sock
def Serve.act(
  a: Spec.Action,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match a:
    case Spec.Reply{r}:
      do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(r))
        k(st, j)
    case Spec.DoMount{u, gs, ln}:
      Serve.mount(st, j, u, gs, ln, History.Outside{}, s2 => j2 => r => do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(r))
        k(s2, j2))
    case Spec.DoUnmount{u}:
      do IO<Unit>:
        s2: Serve <- Serve.unmount(st, u)
        Wire.send(sock, Spec.Response.encode(Spec.Unmounted{}))
        k(s2, j)
    case Spec.DoStop{}:
      do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(Spec.Stopping{}))
        Serve.end(st, j, "vend stopped")
    case Spec.DoAsk{a, +c, b}:
      Serve.sourced(Spec.Command.source(c), a, c, b, st, j, sock, k)
    case Spec.DoCheckout{a, t}:
      Serve.checkout.planned(Spec.Daemon.plan(Serve.daemon(st), a, t), st, j, sock, k)
    case Spec.DoRelease{a, t}:
      Serve.release.planned(Spec.Daemon.plan(Serve.daemon(st), a, t), st, j, sock, k)
    case Spec.DoVerify{a, +t}:
      +d = Serve.daemon(st)
      Serve.verify(
        Verify.folder(d, a, t),
        Verify.carries(d, Spec.Daemon.line_ref(d, t)),
        st,
        j,
        sock,
        k
      )

# the request in the bytes of a connection, decided and acted on
def Serve.request(
  m: Maybe<&2, Spec.Request>,
  +st: Serve,
  j: File,
  sock: Socket,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match m:
    case None{}:
      do IO<Unit>:
        Wire.send(sock, Spec.Response.encode(Spec.Denied{"not a request"}))
        k(st, j)
    case Some{r}:
      match st:
        case Serve{d, ws, tok, dir, ib, ast}:
          Serve.act(Spec.Daemon.decide(d, tok, r), st, j, sock, k)

# one event of the inbox, handled; k goes on with the next
def Serve.on(m: Maybe<&1, Inbox>, st: Serve, j: File, k: Serve -> File -> IO(Unit)) -> IO(Unit):
  match m:
    case None{}:
      Serve.end(st, j, "vend stopped: its inbox closed")
    case Some{WatchHeard{u, ns}}:
      Serve.heard(st, j, u, ns, k)
    case Some{WatchLost{u, why}}:
      do IO<Unit>:
        IO.print(String.concat(["watching ", u, " stopped: ", why]))
        k(st, j)
    case Some{ClientAsked{b, sock}}:
      Serve.request(Spec.Request.decode(b), st, j, sock, k)

# the core task: one event at a time, until a Stop or fuel runs out
def Serve.go(fuel: Nat, +st: Serve, j: File) -> IO(Unit):
  match fuel:
    case 0n:
      Serve.end(st, j, "vend stopped: its fuel ran out")
    case 1n+f:
      do IO<Unit>:
        m: Maybe<&1, Inbox> <- Chan.recv(Inbox, Serve.inbox(st))
        Serve.on(m, st, j, s2 => j2 => Serve.go(f, s2, j2))

# Start
# -----

# the daemon that the records of the journal rebuild: every content in the
# store, every node in the history, every line, mark, seen marker and fork;
# no mount yet
def Start.replayed(rs: List<&2, Journal.Record>) -> Spec.Daemon:
  Spec.Daemon.replay(
    Spec.Daemon{
      Store.Store.new(),
      History.History.new(),
      Tables.Table.new(Lines.Line),
      [],
      0n,
      Spec.Book.new()
    },
    rs
  )

# the entries that the bytes of the mounts file spell; none when it is
# missing or unreadable
def Start.entries(r: Result<&2, &2, String, Octets.Bytes()>) -> List<&2, Spec.Entry>:
  match r:
    case Fail{e}:
      []
    case Done{b}:
      Maybe.default(&2, List<&2, Spec.Entry>, Spec.Entries.decode(b), [])

# the line that a mount at start prints
def Start.said(u: String, r: Spec.Response) -> IO(Unit):
  match r:
    case Spec.Mounted{sp}:
      IO.print(String.concat(["mounted ", u, " (space ", sp, ")"]))
    case Spec.Denied{why}:
      IO.print(String.concat(["could not mount ", u, ": ", why]))
    case _:
      IO.pure(Unit, Unit{})

# who signs what a mount of the file sees saved: its agent, else Outside
def Start.author(m: Maybe<&2, String>) -> History.Author:
  match m:
    case None{}:
      History.Outside{}
    case Some{n}:
      History.Agent{n}

# the entries mounted again, in order, then k
def Start.remount(
  es: List<&2, Spec.Entry>,
  st: Serve,
  j: File,
  k: Serve -> File -> IO(Unit)
) -> IO(Unit):
  match es:
    case Nil{}:
      k(st, j)
    case Con{Spec.Entry{+u, ln, gs, ag}, t}:
      Serve.mount(st, j, u, gs, ln, Start.author(ag), s2 => j2 => r => do IO<Unit>:
        Start.said(u, r)
        Start.remount(t, s2, j2, k))

# A listener and its port, or why none could be had.
type Bound is Type:
  Bound{listener: Listener, port: U32}
  Unbound{why: String}

# a port of the dynamic range from a random word (49152 when there is none)
def Start.port(r: Result<&1, &1, U32 & String, U32>) -> U32:
  match r:
    case Fail{e}:
      49152
    case Done{x}:
      (49152 + (x % 16000): U32)

# the listener on port, or again() when it could not listen there
def Start.bound(
  r: Result<&1, &1, U32 & String, Listener>,
  port: U32,
  again: Unit -> IO(Bound)
) -> IO(Bound):
  match r:
    case Done{l}:
      IO.pure(Bound, Bound{l, port})
    case Fail{e}:
      again(Unit{})

# a listener on 127.0.0.1, at a random port of the dynamic range; tries
# counts the ports to try
def Start.listen(tries: Nat) -> IO(Bound):
  match tries:
    case 0n:
      IO.pure(Bound, Unbound{"no free port"})
    case 1n+n:
      do IO<Bound>:
        x: Result<&1, &1, U32 & String, U32> <- IO.random_u32()
        +port: U32 = Start.port(x)
        l: Result<&1, &1, U32 & String, Listener> <- TCP.listen("127.0.0.1", port)
        Start.bound(l, port, u => Start.listen(n))

# the daemon once it listens: the door written, the acceptor spawned, the
# mounts of the mounts file mounted again, then the core task
def Start.listening(
  b: Bound,
  j: File,
  rs: List<&2, Journal.Record>,
  +d: String,
  +tok: Octets.Bytes()
) -> IO(Unit):
  match b:
    case Unbound{why}:
      do IO<Unit>:
        File.close(j)
        IO.die(Unit, 1, "vend could not listen: " ++ why)
    case Bound{l, +port}:
      do IO<Unit>:
        +inbox: Chan(Inbox) <- Chan.new(Inbox, 4096)
        +astop: Chan(Unit) <- Chan.new(Unit, 1)
        e: Maybe<
          &2,
          String> <- Data.write(d, "daemon", Text.Text.encode(Door.show(Door{port, tok})))
        IO.spawn(Unit, Acceptor.go(Fuel.max(), l, inbox, astop))
        mb: Result<&2, &2, String, Octets.Bytes()> <- CoreLoop.Log.bytes(Data.path(d, "mounts"))
        IO.print(
          String.concat(
            ["vend is running on 127.0.0.1:", U32.show(port), "; `vend daemon stop` ends it"]
          )
        )
        Start.remount(
          Start.entries(mb),
          Serve{Start.replayed(rs), [], tok, d, inbox, astop},
          j,
          s2 => j2 => Serve.go(Fuel.max(), s2, j2)
        )

# the daemon once its token is drawn
def Start.token(
  t: Result<&2, &2, String, Octets.Bytes()>,
  j: File,
  rs: List<&2, Journal.Record>,
  d: String
) -> IO(Unit):
  match t:
    case Fail{e}:
      do IO<Unit>:
        File.close(j)
        IO.die(Unit, 1, "no random token: " ++ e)
    case Done{tok}:
      do IO<Unit>:
        b: Bound <- Start.listen(20n)
        Start.listening(b, j, rs, d, tok)

# the daemon once the journal is open for appends: the token drawn, then
# the listener
def Start.opened(
  o: Result<&1, &1, U32 & String, File>,
  rs: List<&2, Journal.Record>,
  d: String
) -> IO(Unit):
  match o:
    case Fail{e}:
      IO.die(Unit, 1, "the journal could not be opened: " ++ Err.why(e))
    case Done{j}:
      do IO<Unit>:
        t: Result<&2, &2, String, Octets.Bytes()> <- CoreLoop.Loop.random(4n)
        Start.token(t, j, rs, d)

# the daemon once the torn tail of the journal is cut
def Start.cut(cut: Maybe<&2, String>, rs: List<&2, Journal.Record>, +d: String) -> IO(Unit):
  match cut:
    case Some{why}:
      IO.die(Unit, 1, "the torn tail of the journal could not be cut: " ++ why)
    case None{}:
      do IO<Unit>:
        o: Result<&1, &1, U32 & String, File> <- File.open_bytes(Data.path(d, "journal.log"), "a")
        Start.opened(o, rs, d)

# the daemon with what the reader found in the bytes b of the journal
def Start.records(rd: Journal.Read, b: Octets.Bytes(), +d: String) -> IO(Unit):
  match rd:
    case Journal.Read{rs, good}:
      do IO<Unit>:
        cut: Maybe<&2, String> <- CoreLoop.Log.cut(d, Data.path(d, "journal.log"), b, good)
        Start.cut(cut, rs, d)

# the daemon once the bytes of the journal are read
def Start.read(r: Result<&2, &2, String, Octets.Bytes()>, d: String) -> IO(Unit):
  match r:
    case Fail{e}:
      IO.die(Unit, 1, "the journal could not be read: " ++ e)
    case Done{+b}:
      Start.records(Journal.Journal.read(b), b, d)

# the daemon once the lock of the journal is held (its handle stays open
# until the process ends, and with it the lock); a held lock means a
# daemon runs already
def Start.locked(lk: Result<&1, &1, U32 & String, File>, +d: String) -> IO(Unit):
  match lk:
    case Fail{e}:
      IO.die(Unit, 1, "vend is already running: " ++ Err.why(e))
    case Done{held}:
      do IO<Unit>:
        r: Result<&2, &2, String, Octets.Bytes()> <- CoreLoop.Log.bytes(Data.path(d, "journal.log"))
        Start.read(r, d)

# the daemon once the data folder is known
def Start.dir(m: Maybe<&2, String>) -> IO(Unit):
  match m:
    case None{}:
      IO.die(Unit, 1, "no data folder: set LOCALAPPDATA, XDG_DATA_HOME or HOME")
    case Some{+d}:
      do IO<Unit>:
        made: Result<&1, &1, U32 & String, Unit> <- File.FileFx.make_dirs(Text.Text.encode(d))
        lk: Result<&1, &1, U32 & String, File> <- File.FileFx.lock(Data.path(d, "journal.lock"))
        Start.locked(lk, d)

# `vend start-or-resume`: the only way the daemon starts. It runs in
# the foreground until a Stop.
def Daemon.start_or_resume() -> IO(Unit):
  do IO<Unit>:
    m: Maybe<&2, String> <- CoreLoop.Log.dir()
    Start.dir(m)

# The client
# ----------
# Every command but start-or-resume: read the door, connect, send one
# request, read the response. Client.request gives the response to a front;
# the CLI prints it, and exits with 1 for a refusal or when the daemon is
# down.

# the message for a daemon that does not run
def Client.down() -> String:
  "vend is not running; ask the user to run `vend start-or-resume`"

# What a request got: no daemon to answer it, or its answer, None when the
# daemon answered something that is not a response.
type Heard is Data:
  Unheard{}
  Heard{response: Maybe<&2, Spec.Response>}

# An answer as text: whether it is no refusal, and its lines.
type Shown is Data:
  Shown{ok: Bool, lines: List<&2, String>}

# the line of one mount in a status
def Client.info(i: Spec.Info) -> String:
  match i:
    case Spec.Info{u, ln, sp, n}:
      String.concat([u, " line ", ln, " space ", sp, " versions ", Nat.show(n)])

# the lines of the mounts in a status
def Client.infos(infos: List<&2, Spec.Info>) -> List<&2, String>:
  match infos:
    case Nil{}:
      Nil{}
    case Con{i, t}:
      Client.info(i) <> Client.infos(t)

# what a request got, as text
def Client.shown(h: Heard) -> Shown:
  match h:
    case Unheard{}:
      Shown{False{}, [Client.down()]}
    case Heard{None{}}:
      Shown{False{}, ["vend answered something that is not a response"]}
    case Heard{Some{Spec.StatusIs{Nil{}, c}}}:
      Shown{True{}, ["no mounts; clients " ++ Nat.show(c)]}
    case Heard{Some{Spec.StatusIs{Con{i, t}, c}}}:
      Shown{True{}, List.append(&2, String, Client.infos(Con{i, t}), ["clients " ++ Nat.show(c)])}
    case Heard{Some{Spec.Mounted{sp}}}:
      Shown{True{}, ["mounted (space " ++ sp ++ ")"]}
    case Heard{Some{Spec.Unmounted{}}}:
      Shown{True{}, ["unmounted"]}
    case Heard{Some{Spec.Stopping{}}}:
      Shown{True{}, ["stopping"]}
    case Heard{Some{Spec.Denied{why}}}:
      Shown{False{}, ["denied: " ++ why]}
    case Heard{Some{Spec.Said{ok, ls}}}:
      Shown{ok, ls}

# the lines printed, one after another
def Client.lines(ls: List<&2, String>) -> IO(Unit):
  match ls:
    case Nil{}:
      IO.pure(Unit, Unit{})
    case Con{l, t}:
      do IO<Unit>:
        IO.print(l)
        Client.lines(t)

# the answer printed; a refusal is the exit with 1
def Client.print(s: Shown) -> IO(Unit):
  match s:
    case Shown{True{}, ls}:
      Client.lines(ls)
    case Shown{False{}, ls}:
      IO.die(Unit, 1, String.join(ls, "\n"))

# the response read from the daemon; the connection closed
def Client.answered(r: Socket & Maybe<&2, Octets.Bytes()>) -> IO(Heard):
  (sock, m) = r
  match m:
    case None{}:
      do IO<Heard>:
        Socket.close(sock)
        return Unheard{}
    case Some{b}:
      do IO<Heard>:
        Socket.close(sock)
        return Heard{Spec.Response.decode(b)}

# the response read once the request is sent
def Client.sent(r: Socket & Result<&1, &1, (U32 & String) & List<&2, U32>, Unit>) -> IO(Heard):
  (sock, w) = r
  match w:
    case Fail{e}:
      do IO<Heard>:
        Socket.close(sock)
        return Unheard{}
    case Done{u}:
      do IO<Heard>:
        a: Socket & Maybe<&2, Octets.Bytes()> <- Wire.read(sock)
        Client.answered(a)

# the request sent once connected
def Client.connected(r: Result<&1, &1, U32 & String, Socket>, req: Spec.Request) -> IO(Heard):
  match r:
    case Fail{e}:
      IO.pure(Heard, Unheard{})
    case Done{sock}:
      do IO<Heard>:
        s: Socket
          & Result<
            &1,
            &1,
            (U32 & String) & List<&2, U32>,
            Unit> <- TCP.send_bytes(sock, Store.Bytes.framed(Spec.Request.encode(req)))
        Client.sent(s)

# the request with body b sent through the door, if the file names one
def Client.door(m: Maybe<&2, Door>, b: Spec.Body) -> IO(Heard):
  match m:
    case None{}:
      IO.pure(Heard, Unheard{})
    case Some{Door{port, tok}}:
      do IO<Heard>:
        r: Result<&1, &1, U32 & String, Socket> <- TCP.connect("127.0.0.1", port)
        Client.connected(r, Spec.Request{tok, b})

# the door of the text of the file, if it is text
def Client.text(m: Maybe<&2, String>) -> Maybe<&2, Door>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Door.read(s)

# the door that the bytes of the file "daemon" spell
def Client.read(r: Result<&2, &2, String, Octets.Bytes()>) -> Maybe<&2, Door>:
  match r:
    case Fail{e}:
      None{}
    case Done{bytes}:
      Client.text(Text.Text.decode(bytes))

# the request with body b, once the data folder is known
def Client.dir(m: Maybe<&2, String>, b: Spec.Body) -> IO(Heard):
  match m:
    case None{}:
      IO.pure(Heard, Unheard{})
    case Some{d}:
      do IO<Heard>:
        r: Result<&2, &2, String, Octets.Bytes()> <- CoreLoop.Log.bytes(Data.path(d, "daemon"))
        Client.door(Client.read(r), b)

# the request with body b sent to the daemon, and what it got; it never
# ends the program
def Client.request(b: Spec.Body) -> IO(Heard):
  do IO<Heard>:
    m: Maybe<&2, String> <- CoreLoop.Log.dir()
    Client.dir(m, b)

# the request with body b sent to the daemon, and its answer printed
def Client.ask(b: Spec.Body) -> IO(Unit):
  do IO<Unit>:
    h: Heard <- Client.request(b)
    Client.print(Client.shown(h))

# the agent named by VEND_AGENT, or "unnamed" when it is not set
def Client.agent() -> IO(String):
  do IO<String>:
    a: Result<&1, &1, U32 & String, String> <- IO.get_env("VEND_AGENT")
    return Maybe.default(&2, String, CoreLoop.Log.env(a, ""), "unnamed")

# the everyday command of the words ws sent to the daemon with the bytes
# b, signed with Client.agent
def Client.everyday(ws: List<&2, String>, b: Octets.Bytes()) -> IO(Unit):
  do IO<Unit>:
    a: String <- Client.agent()
    Client.ask(Spec.Ask{a, ws, b})
