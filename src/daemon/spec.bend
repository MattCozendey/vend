import Base
import ../core/spec.bend as Core
import ../endpoints/spec.bend as Ep
import ../history/spec.bend as History
import ../journal/spec.bend as Journal
import ../lines/spec.bend as Lines
import ../shared.bend as Shared
import ../store/spec.bend as Store
import ../views/text/spec.bend as Text

# The daemon: one per user and machine, serving every mount of every space.
# It keeps ONE store, ONE history and every line, plus what each mount
# needs on its own (its streams, pending moves and nested spaces). A step
# for one mount runs Core.step on a core made of the shared parts and that
# mount's own parts, then puts the result back: every law of Core.step
# holds for each mount, and the other mounts are not touched. Only
# `bend-ver start-or-resume` starts it; fronts talk to it with requests.

# State
# -----

# What one mount keeps on its own: the mount, the glob texts it was asked
# for (kept for the mounts file), its streams, pending moves, and the
# directories that start other spaces.
type Local is Data:
  Local{
    mount: Core.Mount,
    globs: List<&2, String>,
    streams: Shared.Table<Ep.Stream>,
    moves: Shared.Table<Maybe<&2, Shared.Name>>,
    nested: List<&2, String>
  }

# The daemon's state. lines: every line, by Line.key. mounts: one Local per
# mount, no URI twice. clients: the connections it holds open besides the
# request it answers (none yet, as every request comes on a connection of
# its own; a streaming `affects` will hold one).
type Daemon is Data:
  Daemon{
    store: Store.Store,
    history: History.History,
    lines: Shared.Table<Lines.Line>,
    mounts: List<&2, Local>,
    clients: Nat
  }

# the key of the line named ln of the space sp
def Line.key(sp: String, ln: String) -> String:
  String.concat([sp, ":", ln])

# the glob texts of l
def Local.globs(l: Local) -> List<&2, String>:
  match l:
    case Local{m, gs, ss, ms, ns}:
      gs

# the line name of a mount
def Local.line(l: Local) -> String:
  match l:
    case Local{Core.Mount{sp, ln, r, g}, gs, ss, ms, ns}:
      ln

# the text of the root of a mount, which names the mount in requests
def Local.uri(l: Local) -> String:
  match l:
    case Local{Core.Mount{sp, ln, r, g}, gs, ss, ms, ns}:
      Shared.Uri.show(r)

# the first local of ms whose URI is uri
def Local.find(ms: List<&2, Local>, +uri: String) -> Maybe<&2, Local>:
  match ms:
    case Nil{}:
      None{}
    case Con{+m, t}:
      Shared.Bool.when(
        Maybe<&2, Local>,
        String.eq(Local.uri(m), uri),
        u => Some{m},
        u => Local.find(t, uri)
      )

# ms without the locals whose URI is uri
def Local.drop(ms: List<&2, Local>, +uri: String) -> List<&2, Local>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+m, +t}:
      Shared.Bool.when(
        List<&2, Local>,
        String.eq(Local.uri(m), uri),
        u => Local.drop(t, uri),
        u => m <> Local.drop(t, uri)
      )

# the local of the mount at uri, if there is one
def Daemon.local(d: Daemon, uri: String) -> Maybe<&2, Local>:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Local.find(ms, uri)

# the line of the space sp named ln: as the daemon has it, else new
def Daemon.line(d: Daemon, +sp: String, +ln: String) -> Lines.Line:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Maybe.default(
        &2,
        Lines.Line,
        Shared.Table.get(Lines.Line, ls, Line.key(sp, ln)),
        Lines.Line.new(sp, ln)
      )

# Steps
# -----

# the core of the mount l: the shared store and history, the line of l,
# and the parts l keeps on its own
def Daemon.core(+d: Daemon, l: Local) -> Core.Core:
  match d l:
    case Daemon{s, h, ls, ms, cs} Local{Core.Mount{+sp, +ln, r, g}, gs, ss, mv, ns}:
      Core.Core{Core.Mount{sp, ln, r, g}, s, h, Daemon.line(d, sp, ln), ss, mv, ns}

# d with the result c of a step of the mount whose glob texts are gs: its
# store, history and line become the daemon's, and its own parts replace
# the local of its URI (first among the mounts)
def Daemon.put(d: Daemon, c: Core.Core, gs: List<&2, String>) -> Daemon:
  match d c:
    case Daemon{s, h, ls, ms, cs} Core.Core{Core.Mount{+sp, +ln, r, g}, s2, h2, l2, ss, mv, ns}:
      +l = {Local{Core.Mount{sp, ln, r, g}, gs, ss, mv, ns}: Local}
      Daemon{
        s2,
        h2,
        Shared.Table.set(Lines.Line, ls, Line.key(sp, ln), l2),
        l <> Local.drop(ms, Local.uri(l)),
        cs
      }

# The result of a step of one mount: the daemon after it, and the outputs
# of Core.step, in order.
type Stepped is Data:
  Stepped{daemon: Daemon, outputs: List<&2, Core.Output>}

# the result of the core step s of the mount whose glob texts are gs
def Daemon.stepped(d: Daemon, gs: List<&2, String>, s: Core.Stepped) -> Stepped:
  match s:
    case Core.Stepped{c, os}:
      Stepped{Daemon.put(d, c, gs), os}

# the daemon after the input i to the mount l, and the outputs
law Daemon.step:
  for d: Daemon
  for l: Local
  for i: Core.Input
  Stepped

# a step of a mount is exactly Core.step on the core of that mount: the
# same outputs, and its store, history, line and own parts put back
law step_is_core:
  for d: Daemon
  for l: Local
  for i: Core.Input
  {
    Daemon.step(
      d,
      l,
      i
    )
      == Daemon.stepped(d, Local.globs(l), Core.Core.step(Daemon.core(d, l), i)): Stepped
  }

# the daemon of a step
def Stepped.daemon(s: Stepped) -> Daemon:
  match s:
    case Stepped{d, os}:
      d

# d with the mount l added, when no mount has its URI
def Daemon.mount(d: Daemon, l: Local) -> Daemon:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Daemon{s, h, ls, l <> ms, cs}

# d without the mount at uri; its versions and lines stay
def Daemon.unmount(d: Daemon, uri: String) -> Daemon:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Daemon{s, h, ls, Local.drop(ms, uri), cs}

# a step of one mount leaves every other mount as it was
law step_frames:
  for d: Daemon
  for l: Local
  for i: Core.Input
  for uri: String
  for o: {String.eq(uri, Local.uri(l)) == False{}: Bool}
  {
    Daemon.local(
      Stepped.daemon(Daemon.step(d, l, i)),
      uri
    )
      == Daemon.local(d, uri): Maybe<&2, Local>
  }

# a step of one mount leaves every line of another space or name as it was
law step_frames_lines:
  for d: Daemon
  for l: Local
  for i: Core.Input
  for sp: String
  for ln: String
  for o: {
    String.eq(
      Line.key(sp, ln),
      Line.key(
        Core.Core.space(Daemon.core(d, l)),
        Lines.Line.name(Core.Core.line(Daemon.core(d, l)))
      )
    )
      == False{}: Bool
  }
  {Daemon.line(Stepped.daemon(Daemon.step(d, l, i)), sp, ln) == Daemon.line(d, sp, ln): Lines.Line}

# an unmount removes exactly that mount
law unmount_drops:
  for d: Daemon
  for uri: String
  {Daemon.local(Daemon.unmount(d, uri), uri) == None{}: Maybe<&2, Local>}

# an unmount leaves every other mount as it was
law unmount_frames:
  for d: Daemon
  for uri: String
  for other: String
  for o: {String.eq(other, uri) == False{}: Bool}
  {Daemon.local(Daemon.unmount(d, uri), other) == Daemon.local(d, other): Maybe<&2, Local>}

# Requests
# --------
# A front sends one request on a connection of its own and reads one
# response. Every request carries the daemon's token: a random 128-bit
# secret in a file of the user's data folder, so only that user's fronts
# can talk to it. New requests (log, show, diff, write, ...) come as new
# tags of Body and Response.

# What a front asks. Status: the mounts and clients. Mount: version the
# files below uri that the glob texts select, on the line named line.
# Unmount: stop versioning the mount at uri. Stop: end the daemon; without
# force it refuses while mounts are active or other clients are connected.
type Body is Data:
  Status{}
  Mount{uri: String, globs: List<&2, String>, line: String}
  Unmount{uri: String}
  Stop{force: Bool}

# A request: the token, then what it asks.
type Request is Data:
  Request{token: Shared.Bytes(), body: Body}

# One mount, as Status tells it: its root, line, space, and how many
# versions of its space the history holds.
type Info is Data:
  Info{uri: String, line: String, space: String, versions: Nat}

# What the daemon answers.
type Response is Data:
  StatusIs{mounts: List<&2, Info>, clients: Nat}
  Mounted{space: String}
  Unmounted{}
  Stopping{}
  Denied{why: String}

# each text framed as UTF-8, one after another
def Texts.encode.go(xs: List<&2, String>) -> Shared.Bytes():
  match xs:
    case Nil{}:
      []
    case Con{x, t}:
      List.append(&2, U32, Journal.Utf8.framed(x), Texts.encode.go(t))

# the bytes of the texts: their count, then each framed as UTF-8
def Texts.encode(xs: List<&2, String>) -> Shared.Bytes():
  +xs = xs
  List.append(&2, U32, Store.Leb.of(List.length(&2, String, xs)), Texts.encode.go(xs))

# the bytes of a Bool: 1 or 0
def Flag.encode(b: Bool) -> Shared.Bytes():
  match b:
    case False{}:
      [0]
    case True{}:
      [1]

# the bytes of what a request asks: a tag (0 Status, 1 Mount, 2 Unmount,
# 3 Stop), then its fields in order
def Body.encode(b: Body) -> Shared.Bytes():
  match b:
    case Status{}:
      [0]
    case Mount{u, gs, ln}:
      1
        <> List.append(
          &2,
          U32,
          Journal.Utf8.framed(u),
          List.append(&2, U32, Texts.encode(gs), Journal.Utf8.framed(ln))
        )
    case Unmount{u}:
      2 <> Journal.Utf8.framed(u)
    case Stop{f}:
      3 <> Flag.encode(f)

# the bytes of a request: the token, framed, then what it asks
def Request.encode(r: Request) -> Shared.Bytes():
  match r:
    case Request{t, b}:
      List.append(&2, U32, Store.Bytes.framed(t), Body.encode(b))

# the bytes of one mount's status
def Info.encode(i: Info) -> Shared.Bytes():
  match i:
    case Info{u, ln, sp, n}:
      List.append(
        &2,
        U32,
        Journal.Utf8.framed(u),
        List.append(
          &2,
          U32,
          Journal.Utf8.framed(ln),
          List.append(&2, U32, Journal.Utf8.framed(sp), Store.Leb.of(n))
        )
      )

# the bytes of the statuses, one after another
def Infos.encode.go(infos: List<&2, Info>) -> Shared.Bytes():
  match infos:
    case Nil{}:
      []
    case Con{i, t}:
      List.append(&2, U32, Info.encode(i), Infos.encode.go(t))

# the bytes of a response: a tag (0 StatusIs, 1 Mounted, 2 Unmounted,
# 3 Stopping, 4 Denied), then its fields in order
def Response.encode(r: Response) -> Shared.Bytes():
  match r:
    case StatusIs{+infos, n}:
      0
        <> List.append(
          &2,
          U32,
          Store.Leb.of(List.length(&2, Info, infos)),
          List.append(&2, U32, Infos.encode.go(infos), Store.Leb.of(n))
        )
    case Mounted{sp}:
      1 <> Journal.Utf8.framed(sp)
    case Unmounted{}:
      [2]
    case Stopping{}:
      [3]
    case Denied{why}:
      4 <> Journal.Utf8.framed(why)

# every text can be written as UTF-8
def Texts.ok(xs: List<&2, String>) -> Bool:
  List.all(~&2, ~String, ~Text.Text.ok, xs)

# every text of a request can be written as UTF-8
def Request.ok(r: Request) -> Bool:
  match r:
    case Request{t, Mount{u, gs, ln}}:
      Bool.and(Text.Text.ok(u), Bool.and(Texts.ok(gs), Text.Text.ok(ln)))
    case Request{t, Unmount{u}}:
      Text.Text.ok(u)
    case _:
      True{}

# every text of a status can be written as UTF-8
def Infos.ok(infos: List<&2, Info>) -> Bool:
  match infos:
    case Nil{}:
      True{}
    case Con{Info{u, ln, sp, n}, t}:
      List.all.if(x => Infos.ok(t), Texts.ok([u, ln, sp]))

# every text of a response can be written as UTF-8
def Response.ok(r: Response) -> Bool:
  match r:
    case StatusIs{infos, n}:
      Infos.ok(infos)
    case Mounted{sp}:
      Text.Text.ok(sp)
    case Denied{why}:
      Text.Text.ok(why)
    case _:
      True{}

# the request that bytes b spell, or None
law Request.decode:
  for b: Shared.Bytes()
  Maybe<&2, Request>

# the response that bytes b spell, or None
law Response.decode:
  for b: Shared.Bytes()
  Maybe<&2, Response>

# a request reads back from its bytes
law request_decode_after_encode:
  for r: Request
  for h: {Request.ok(r) == True{}: Bool}
  {Request.decode(Request.encode(r)) == Some{r}: Maybe<&2, Request>}

# a response reads back from its bytes
law response_decode_after_encode:
  for r: Response
  for h: {Response.ok(r) == True{}: Bool}
  {Response.decode(Response.encode(r)) == Some{r}: Maybe<&2, Response>}

# Answers
# -------

# What the daemon does about a request. Reply: answer at once. DoMount,
# DoUnmount: change the mounts (the loop does the IO: the root, its space
# file, the watcher, the mounts file), then answer. DoStop: answer
# Stopping, then end.
type Action is Data:
  Reply{response: Response}
  DoMount{uri: String, globs: List<&2, String>, line: String}
  DoUnmount{uri: String}
  DoStop{}

# the nodes of h, by the hex of their id
def Versions.nodes(h: History.History) -> Shared.Table<History.Node>:
  match h:
    case History.History{ns, ts}:
      ns

# the node m is a version of a resource of the space sp
def Versions.of_space(m: Maybe<&2, History.Node>, sp: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      String.eq(Shared.Name.space(History.Node.name(v)), sp)

# how many versions of the space sp the nodes ns hold, among the keys ks
def Versions.count(ks: List<&2, String>, +ns: Shared.Table<History.Node>, +sp: String) -> Nat:
  match ks:
    case Nil{}:
      0n
    case Con{k, t}:
      +rest = Versions.count(t, ns, sp)
      Shared.Bool.when(
        Nat,
        Versions.of_space(Shared.Table.get(History.Node, ns, k), sp),
        u => 1n+rest,
        u => rest
      )

# how many versions of the space sp the history holds
def Versions.of(h: History.History, sp: String) -> Nat:
  +ns = Versions.nodes(h)
  Versions.count(Shared.Table.keys(History.Node, ns), ns, sp)

# the status of each mount
def Daemon.infos.go(+h: History.History, ms: List<&2, Local>) -> List<&2, Info>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{Local{Core.Mount{+sp, ln, r, g}, gs, ss, mv, ns}, t}:
      Info{Shared.Uri.show(r), ln, sp, Versions.of(h, sp)} <> Daemon.infos.go(h, t)

# the status of each mount of d
def Daemon.infos(d: Daemon) -> List<&2, Info>:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Daemon.infos.go(h, ms)

# d has no mount and no other client: a Stop without force may end it
def Daemon.idle(d: Daemon) -> Bool:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Bool.and(List.is_empty(&2, Local, ms), Nat.is_eq(cs, 0n))

# the clients of d
def Daemon.clients(d: Daemon) -> Nat:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      cs

# the action ends the daemon
def Action.stops(a: Action) -> Bool:
  match a:
    case DoStop{}:
      True{}
    case _:
      False{}

# the action answers at once
def Action.is_reply(a: Action) -> Bool:
  match a:
    case Reply{r}:
      True{}
    case _:
      False{}

# the token of a request
def Request.token(r: Request) -> Shared.Bytes():
  match r:
    case Request{t, b}:
      t

# what to do about the request body b
def Daemon.decide.body(+d: Daemon, b: Body) -> Action:
  match b:
    case Status{}:
      Reply{StatusIs{Daemon.infos(d), Daemon.clients(d)}}
    case Mount{+u, gs, ln}:
      Shared.Bool.when(
        Action,
        Maybe.is_some(&2, Local, Daemon.local(d, u)),
        x => Reply{Denied{String.append("already mounted: ", u)}},
        x => DoMount{u, gs, ln}
      )
    case Unmount{+u}:
      Shared.Bool.when(
        Action,
        Maybe.is_some(&2, Local, Daemon.local(d, u)),
        x => DoUnmount{u},
        x => Reply{Denied{String.append("not mounted: ", u)}}
      )
    case Stop{f}:
      Shared.Bool.when(
        Action,
        Bool.or(f, Daemon.idle(d)),
        x => DoStop{},
        x => Reply{
          Denied{"mounts are active or other clients are connected: unmount them, or use --force"}
        }
      )

# what to do about the request r when the token of the daemon is tok: a
# request with another token is refused, whatever it asks
def Daemon.decide(d: Daemon, tok: Shared.Bytes(), r: Request) -> Action:
  match r:
    case Request{t, b}:
      Shared.Bool.when(
        Action,
        Shared.Bytes.is_eq(t, tok),
        x => Daemon.decide.body(d, b),
        x => Reply{Denied{"wrong token"}}
      )

# a request with another token is refused, and asks nothing of the daemon
law token_checked:
  for d: Daemon
  for tok: Shared.Bytes()
  for r: Request
  for h: {Shared.Bytes.is_eq(Request.token(r), tok) == False{}: Bool}
  {Daemon.decide(d, tok, r) == Reply{Denied{"wrong token"}}: Action}

# a Stop without force does not end the daemon while a mount is active or
# another client is connected
law stop_guarded:
  for d: Daemon
  for tok: Shared.Bytes()
  for h: {Daemon.idle(d) == False{}: Bool}
  {Action.stops(Daemon.decide(d, tok, Request{tok, Stop{False{}}})) == False{}: Bool}

# a Stop with force and the right token always ends the daemon
law stop_forced:
  for d: Daemon
  for tok: Shared.Bytes()
  {Daemon.decide(d, tok, Request{tok, Stop{True{}}}) == DoStop{}: Action}

# a Mount of a URI that is already mounted is refused at once
law mount_once:
  for d: Daemon
  for tok: Shared.Bytes()
  for u: String
  for gs: List<&2, String>
  for ln: String
  for h: {Maybe.is_some(&2, Local, Daemon.local(d, u)) == True{}: Bool}
  {Action.is_reply(Daemon.decide(d, tok, Request{tok, Mount{u, gs, ln}})) == True{}: Bool}

# The mounts file
# ---------------
# The mounts live in a file of the data folder, not in the journal: they
# are the setup of this machine (its paths), while the journal holds
# versions that other machines may join; and they change rarely, so the
# whole file is rewritten (to a temporary file, synced, then renamed over
# it) on each mount and unmount, which a power cut leaves whole.

# One mount as the file keeps it: the root, the line, the glob texts.
type Entry is Data:
  Entry{uri: String, line: String, globs: List<&2, String>}

# the entry of each mount
def Daemon.entries.go(ms: List<&2, Local>) -> List<&2, Entry>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      Entry{Local.uri(l), Local.line(l), Local.globs(l)} <> Daemon.entries.go(t)

# the entries of the mounts of d
def Daemon.entries(d: Daemon) -> List<&2, Entry>:
  match d:
    case Daemon{s, h, ls, ms, cs}:
      Daemon.entries.go(ms)

# the bytes of the entries, one after another
def Entries.encode(es: List<&2, Entry>) -> Shared.Bytes():
  match es:
    case Nil{}:
      []
    case Con{Entry{u, ln, gs}, t}:
      List.append(
        &2,
        U32,
        Journal.Utf8.framed(u),
        List.append(
          &2,
          U32,
          Journal.Utf8.framed(ln),
          List.append(&2, U32, Texts.encode(gs), Entries.encode(t))
        )
      )

# every text of the entries can be written as UTF-8
def Entries.ok(es: List<&2, Entry>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Entry{u, ln, gs}, t}:
      List.all.if(x => Entries.ok(t), Texts.ok(u <> ln <> gs))

# the entries that bytes b spell, or None
law Entries.decode:
  for b: Shared.Bytes()
  Maybe<&2, List<&2, Entry>>

# entries read back from their bytes
law entries_decode_after_encode:
  for es: List<&2, Entry>
  for h: {Entries.ok(es) == True{}: Bool}
  {Entries.decode(Entries.encode(es)) == Some{es}: Maybe<&2, List<&2, Entry>>}
