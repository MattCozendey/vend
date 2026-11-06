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

# Where a forked line came from: the key of the line it was forked from,
# the mark it was forked at (if any), and the line as it started.
type Origin is Data:
  Origin{from: String, mark: Maybe<&2, String>, at: Lines.Line}

# What the daemon keeps besides versions and lines, all rebuilt from the
# journal: every agent's seen markers, every mark (by Mark.key), and the
# origin of every forked line (by its key).
type Book is Data:
  Book{seen: Lines.SeenBook, marks: Shared.Table<Lines.Mark>, origins: Shared.Table<Origin>}

# a book with nothing in it
def Book.new() -> Book:
  Book{Lines.SeenBook.new(), Shared.Table.new(Lines.Mark), Shared.Table.new(Origin)}

# the key of the mark named name of the line whose key is line
def Mark.key(line: String, name: String) -> String:
  String.concat([line, "@", name])

# The daemon's state. lines: every line, by Lines.Line.key. mounts: one Local
# per mount, no URI twice. clients: the connections it holds open besides
# the request it answers (none yet, as every request comes on a connection
# of its own; a streaming `affects` will hold one). book: seen markers,
# marks and origins.
type Daemon is Data:
  Daemon{
    store: Store.Store,
    history: History.History,
    lines: Shared.Table<Lines.Line>,
    mounts: List<&2, Local>,
    clients: Nat,
    book: Book
  }

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
    case Daemon{s, h, ls, ms, cs, bk}:
      Local.find(ms, uri)

# the line of the space sp named ln: as the daemon has it, else new
def Daemon.line(d: Daemon, +sp: String, +ln: String) -> Lines.Line:
  match d:
    case Daemon{s, h, ls, ms, cs, bk}:
      Maybe.default(
        &2,
        Lines.Line,
        Shared.Table.get(Lines.Line, ls, Lines.Line.key(sp, ln)),
        Lines.Line.new(sp, ln)
      )

# Steps
# -----

# the core of the mount l: the shared store and history, the line of l,
# and the parts l keeps on its own
def Daemon.core(+d: Daemon, l: Local) -> Core.Core:
  match d l:
    case Daemon{s, h, ls, ms, cs, bk} Local{Core.Mount{+sp, +ln, r, g}, gs, ss, mv, ns}:
      Core.Core{Core.Mount{sp, ln, r, g}, s, h, Daemon.line(d, sp, ln), ss, mv, ns}

# d with the result c of a step of the mount whose glob texts are gs: its
# store, history and line become the daemon's, and its own parts replace
# the local of its URI (first among the mounts)
def Daemon.put(d: Daemon, c: Core.Core, gs: List<&2, String>) -> Daemon:
  match d c:
    case Daemon{s, h, ls, ms, cs, bk} Core.Core{Core.Mount{+sp, +ln, r, g}, s2, h2, l2, ss, mv, ns}:
      +l = {Local{Core.Mount{sp, ln, r, g}, gs, ss, mv, ns}: Local}
      Daemon{
        s2,
        h2,
        Shared.Table.set(Lines.Line, ls, Lines.Line.key(sp, ln), l2),
        l <> Local.drop(ms, Local.uri(l)),
        cs,
        bk
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
    case Daemon{s, h, ls, ms, cs, bk}:
      Daemon{s, h, ls, l <> ms, cs, bk}

# d without the mount at uri; its versions and lines stay
def Daemon.unmount(d: Daemon, uri: String) -> Daemon:
  match d:
    case Daemon{s, h, ls, ms, cs, bk}:
      Daemon{s, h, ls, Local.drop(ms, uri), cs, bk}

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
      Lines.Line.key(sp, ln),
      Lines.Line.key(
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
# Ask: one of the everyday commands, as its words (Command.read reads
# them), signed by the agent named agent (BEND_VER_AGENT; empty for none),
# with data: the bytes that a write writes, else none.
type Body is Data:
  Status{}
  Mount{uri: String, globs: List<&2, String>, line: String}
  Unmount{uri: String}
  Stop{force: Bool}
  Ask{agent: String, words: List<&2, String>, data: Shared.Bytes()}

# A request: the token, then what it asks.
type Request is Data:
  Request{token: Shared.Bytes(), body: Body}

# One mount, as Status tells it: its root, line, space, and how many
# versions of its space the history holds.
type Info is Data:
  Info{uri: String, line: String, space: String, versions: Nat}

# What the daemon answers. Said: the answer of an Ask, as lines of text;
# ok is False for a refusal (a stale write, a clash, a bad command), which a
# front reports as a failure.
type Response is Data:
  StatusIs{mounts: List<&2, Info>, clients: Nat}
  Mounted{space: String}
  Unmounted{}
  Stopping{}
  Denied{why: String}
  Said{ok: Bool, lines: List<&2, String>}

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
# 3 Stop, 4 Ask), then its fields in order
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
    case Ask{a, ws, b}:
      4
        <> List.append(
          &2,
          U32,
          Journal.Utf8.framed(a),
          List.append(&2, U32, Texts.encode(ws), Store.Bytes.framed(b))
        )

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
# 3 Stopping, 4 Denied, 5 Said), then its fields in order
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
    case Said{ok, ls}:
      5 <> List.append(&2, U32, Flag.encode(ok), Texts.encode(ls))

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
    case Request{t, Ask{a, ws, b}}:
      Bool.and(Text.Text.ok(a), Texts.ok(ws))
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
    case Said{ok, ls}:
      Texts.ok(ls)
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

# The book and the journal
# ------------------------
# Every change of the daemon's state that a power cut must not lose is a
# journal record, and the daemon's state is the records replayed in order:
# the loop keeps the records of a step, syncs them, and only then takes
# the state that Daemon.replay gives. So the state after a restart is the
# state before it.

# the line whose key is k, if the daemon has it
def Daemon.line_at(d: Daemon, k: String) -> Maybe<&2, Lines.Line>:
  match d:
    case Daemon{s, h, ls, ms, cs, bk}:
      Shared.Table.get(Lines.Line, ls, k)

# the mark named nm of the line whose key is k, if there is one
def Daemon.mark(d: Daemon, k: String, nm: String) -> Maybe<&2, Lines.Mark>:
  match d:
    case Daemon{s, h, ls, ms, cs, Book{sn, mk, og}}:
      Shared.Table.get(Lines.Mark, mk, Mark.key(k, nm))

# the seen marker of the agent a on the line whose key is k
def Daemon.seen(d: Daemon, a: String, k: String) -> Lines.Seen:
  match d:
    case Daemon{s, h, ls, ms, cs, Book{sn, mk, og}}:
      Lines.SeenBook.get(sn, a, k)

# where the line whose key is k came from, if it was forked
def Daemon.origin(d: Daemon, k: String) -> Maybe<&2, Origin>:
  match d:
    case Daemon{s, h, ls, ms, cs, Book{sn, mk, og}}:
      Shared.Table.get(Origin, og, k)

# the text after the cut, or the whole text t when there is none
def Key.after(c: Maybe<&2, Shared.Cut>, t: String) -> String:
  match c:
    case None{}:
      t
    case Some{Shared.Cut{b, a}}:
      a

# the text after the first ':' of a line key: the line's name
def Key.name(+k: String) -> String:
  Key.after(Shared.Text.cut(k, 58), k)

# the record names the mark nm of the line whose key is k
def Record.names_mark(r: Journal.Record, k: String, nm: String) -> Bool:
  match r:
    case Journal.Marked{ln, n, msg, a}:
      Bool.and(String.eq(ln, k), String.eq(n, nm))
    case _:
      False{}

# d after the record r. Kept: the content in the store, the node in the
# history, and the line it names (of the space of its node) moved, as a
# core replays it. Saw: the agent's marker on the line caught up with the
# line as it is now. Marked: the mark made of the line as it is now, unless
# that mark exists. Forked: the new line, following what its source line
# (or the source's mark) follows now, with its origin; unless it exists or
# its source does not. A record about a line the daemon does not have
# changes nothing.
law Daemon.apply:
  for d: Daemon
  for r: Journal.Record
  Daemon

# d after the records, in order
law Daemon.replay:
  for d: Daemon
  for rs: List<&2, Journal.Record>
  Daemon

# replaying no records changes nothing
law replay_nil:
  for d: Daemon
  {Daemon.replay(d, []) == d: Daemon}

# replaying records applies the first, then replays the rest
law replay_con:
  for d: Daemon
  for r: Journal.Record
  for rs: List<&2, Journal.Record>
  {Daemon.replay(d, Con{r, rs}) == Daemon.replay(Daemon.apply(d, r), rs): Daemon}

# a Saw catches the agent's marker up with the line as it is
law apply_saw:
  for d: Daemon
  for a: String
  for k: String
  for l: Lines.Line
  for h: {Daemon.line_at(d, k) == Some{l}: Maybe<&2, Lines.Line>}
  {
    Daemon.seen(
      Daemon.apply(d, Journal.Saw{a, k}),
      a,
      k
    )
      == Lines.Seen.update(Daemon.seen(d, a, k), l): Lines.Seen
  }

# a Marked keeps the mark of the line as it is when the mark is new
law apply_marked:
  for d: Daemon
  for k: String
  for nm: String
  for msg: String
  for a: History.Author
  for l: Lines.Line
  for h: {Daemon.line_at(d, k) == Some{l}: Maybe<&2, Lines.Line>}
  for n: {Daemon.mark(d, k, nm) == None{}: Maybe<&2, Lines.Mark>}
  {
    Daemon.mark(
      Daemon.apply(d, Journal.Marked{k, nm, msg, a}),
      k,
      nm
    )
      == Some{Lines.Mark.of(l, nm, msg, a)}: Maybe<&2, Lines.Mark>
  }

# a mark is fixed: no record but the one that makes it changes it, so a
# line that moves on leaves its marks where they were
law mark_fixed:
  for d: Daemon
  for r: Journal.Record
  for k: String
  for nm: String
  for o: {Record.names_mark(r, k, nm) == False{}: Bool}
  {Daemon.mark(Daemon.apply(d, r), k, nm) == Daemon.mark(d, k, nm): Maybe<&2, Lines.Mark>}

# a Forked from a line starts the new line where its source is now
law apply_forked:
  for d: Daemon
  for k: String
  for f: String
  for l: Lines.Line
  for h: {Daemon.line_at(d, f) == Some{l}: Maybe<&2, Lines.Line>}
  for n: {Daemon.line_at(d, k) == None{}: Maybe<&2, Lines.Line>}
  {
    Daemon.line_at(
      Daemon.apply(d, Journal.Forked{k, f, None{}}),
      k
    )
      == Some{Lines.Line.fork(l, Key.name(k))}: Maybe<&2, Lines.Line>
  }

# a Forked from a mark starts the new line where the mark is
law apply_forked_mark:
  for d: Daemon
  for k: String
  for f: String
  for m: String
  for mk: Lines.Mark
  for h: {Daemon.mark(d, f, m) == Some{mk}: Maybe<&2, Lines.Mark>}
  for n: {Daemon.line_at(d, k) == None{}: Maybe<&2, Lines.Line>}
  {
    Daemon.line_at(
      Daemon.apply(d, Journal.Forked{k, f, Some{m}}),
      k
    )
      == Some{Lines.Line.fork(Lines.Mark.at(mk), Key.name(k))}: Maybe<&2, Lines.Line>
  }

# Commands
# --------
# The everyday commands, as Ask carries them. Names are `<space>:<path>`;
# a line is named by its name, or by its key `<space>:<name>` when names
# alone are ambiguous; `<line>@<mark>` names a mark; a version is a prefix
# of a node id (in hex), or a line, whose head it then means.
#
#   lines                                   every line and how far it moved
#   log <name> [--line L] [--author A]      the versions of a resource
#   show <name> [<version>]                 the content of a version
#   diff <name> <a> <b>                     two versions, through the view
#   affects <line>                          what changed since the agent
#                                           looked, and who it affects
#   impact <line|line@mark>                 the changeset since the fork,
#                                           classified, and its radius
#   line new <name> --from <line|line@mark> a new line
#   write <name> --expect <ids|none> [--line L]   a version of the data
#   restore <name> <version> [--line L]     a version with an old content
#   mark <line> <name> -m <message>         a mark of the line as it is
#   merge <line|line@mark> into <line>      a merge, every resource or none
type Command is Data:
  LinesOf{}
  LogOf{name: Shared.Name, line: Maybe<&2, String>, author: Maybe<&2, String>}
  ShowOf{name: Shared.Name, version: Maybe<&2, String>}
  DiffOf{name: Shared.Name, a: String, b: String}
  AffectsOf{line: String}
  ImpactOf{target: String}
  LineNew{name: String, from: String}
  WriteTo{name: Shared.Name, line: String, expect: List<&2, String>}
  RestoreTo{name: Shared.Name, line: String, version: String}
  MarkMade{line: String, name: String, message: String}
  MergeOf{from: String, into: String}

# the usage of the everyday commands
def Command.usage() -> String:
  "usage: lines | log <name> [--line L] [--author A] | show <name> [<version>] | diff <name> <a> <b> | affects <line> | impact <line|line@mark> | line new <name> --from <line|line@mark> | write <name> --expect <ids|none> [--line L] | restore <name> <version> [--line L] | mark <line> <name> -m <message> | merge <line|line@mark> into <line>"

# the value after the option key in ws, if it is there
def Opts.get(ws: List<&2, String>, +key: String) -> Maybe<&2, String>:
  match ws:
    case Con{w, Con{+v, t}}:
      Shared.Bool.when(
        Maybe<&2, String>,
        String.eq(w, key),
        u => Some{v},
        u => Opts.get(Con{v, t}, key)
      )
    case _:
      None{}

# a line name is plain: not empty, with no ':' or '@'
def Line.plain(+n: String) -> Bool:
  List.all.if(
    u => List.all.if(v => Bool.not(Shared.Text.has(n, 64)), Bool.not(Shared.Text.has(n, 58))),
    Bool.not(String.is_empty(n))
  )

# the command k of the name m read from t, or a refusal when t is no name
def Command.named.of(
  m: Maybe<&2, Shared.Name>,
  t: String,
  k: Shared.Name -> Command
) -> Result<&2, &2, String, Command>:
  match m:
    case None{}:
      Fail{String.append("not a name <space>:<path>: ", t)}
    case Some{n}:
      Done{k(n)}

# the command of a name text and k, or a refusal when it is not a name
def Command.named(+t: String, k: Shared.Name -> Command) -> Result<&2, &2, String, Command>:
  Command.named.of(Shared.Name.read(t), t, k)

# the ids of an expect text: "none" for none, else prefixes split at ','
def Command.expect(+e: String) -> List<&2, String>:
  Shared.Bool.when(List<&2, String>, String.eq(e, "none"), u => [], u => String.split(e, ','))

# c when ok, else the usage
def Command.if(ok: Bool, c: Command) -> Result<&2, &2, String, Command>:
  match ok:
    case False{}:
      Fail{Command.usage()}
    case True{}:
      Done{c}

# the line option of t: --line L, else main
def Opts.line(t: List<&2, String>) -> String:
  Maybe.default(&2, String, Opts.get(t, "--line"), "main")

# Each command word has one reader below, for the words after it. Fewer
# words than the command needs, or a word in the wrong place, is the usage.

# lines
def Command.lines(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  Command.if(List.is_empty(&2, String, r), LinesOf{})

# log <name> [--line L] [--author A]
def Command.log(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, +t}:
      Command.named(a, n => LogOf{n, Opts.get(t, "--line"), Opts.get(t, "--author")})
    case Nil{}:
      Fail{Command.usage()}

# show <name> [<version>]
def Command.show(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, t}:
      Command.named(a, n => ShowOf{n, List.head(&2, String, t)})
    case Nil{}:
      Fail{Command.usage()}

# diff <name> <a> [<b>]; with no b, b is a
def Command.diff(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{+b, t}}:
      Command.named(a, n => DiffOf{n, b, Maybe.default(&2, String, List.head(&2, String, t), b)})
    case _:
      Fail{Command.usage()}

# affects <line>
def Command.affects(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, t}:
      Command.if(List.is_empty(&2, String, t), AffectsOf{a})
    case Nil{}:
      Fail{Command.usage()}

# impact <line|line@mark>
def Command.impact(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, t}:
      Command.if(List.is_empty(&2, String, t), ImpactOf{a})
    case Nil{}:
      Fail{Command.usage()}

# line new <name> --from <line|line@mark>
def Command.line(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{+b, t}}:
      line = {LineNew{b, Maybe.default(&2, String, Opts.get(t, "--from"), "main")}: Command}
      Shared.Bool.when(
        Result<&2, &2, String, Command>,
        String.eq(a, "new"),
        u => Command.if(Line.plain(b), line),
        u => Fail{Command.usage()}
      )
    case _:
      Fail{Command.usage()}

# write <name> --expect <ids|none> [--line L]
def Command.write(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{b, +t}}:
      e = Command.expect(Maybe.default(&2, String, Opts.get(b <> t, "--expect"), "none"))
      Command.named(a, n => WriteTo{n, Opts.line(t), e})
    case _:
      Fail{Command.usage()}

# restore <name> <version> [--line L]
def Command.restore(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{b, t}}:
      Command.named(a, n => RestoreTo{n, Opts.line(t), b})
    case _:
      Fail{Command.usage()}

# mark <line> <name> -m <message>
def Command.mark(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{+b, t}}:
      Command.if(Line.plain(b), MarkMade{a, b, Maybe.default(&2, String, Opts.get(t, "-m"), "")})
    case _:
      Fail{Command.usage()}

# merge <line|line@mark> into <line>
def Command.merge(r: List<&2, String>) -> Result<&2, &2, String, Command>:
  match r:
    case Con{a, Con{b, Con{c, t}}}:
      Command.if(String.eq(b, "into"), MergeOf{a, c})
    case _:
      Fail{Command.usage()}

# A command word and the reader of the words after it.
type Reader is Type:
  Reader{word: String, read: List<&2, String> -> Result<&2, &2, String, Command>}

# every command word with its reader
def Command.readers() -> List<&1, Reader>:
  [
    Reader{"lines", r => Command.lines(r)},
    Reader{"log", r => Command.log(r)},
    Reader{"show", r => Command.show(r)},
    Reader{"diff", r => Command.diff(r)},
    Reader{"affects", r => Command.affects(r)},
    Reader{"impact", r => Command.impact(r)},
    Reader{"line", r => Command.line(r)},
    Reader{"write", r => Command.write(r)},
    Reader{"restore", r => Command.restore(r)},
    Reader{"mark", r => Command.mark(r)},
    Reader{"merge", r => Command.merge(r)}
  ]

# the reader of rs for the word w reads r; no reader for w is the usage
def Command.of(
  rs: List<&1, Reader>,
  +w: String,
  +r: List<&2, String>
) -> Result<&2, &2, String, Command>:
  match rs:
    case Nil{}:
      Fail{Command.usage()}
    case Con{Reader{k, f}, t}:
      Shared.Bool.when(
        Result<&2, &2, String, Command>,
        String.eq(k, w),
        u => f(r),
        u => Command.of(t, w, r)
      )

# the command that the words ws spell, or the usage
def Command.read(ws: List<&2, String>) -> Result<&2, &2, String, Command>:
  match ws:
    case Nil{}:
      Fail{Command.usage()}
    case Con{w, r}:
      Command.of(Command.readers(), w, r)

# the command only reads: it keeps no record
def Command.reads(c: Command) -> Bool:
  match c:
    case LinesOf{}:
      True{}
    case LogOf{n, l, a}:
      True{}
    case ShowOf{n, v}:
      True{}
    case DiffOf{n, a, b}:
      True{}
    case ImpactOf{t}:
      True{}
    case _:
      False{}

# Answers to commands
# -------------------

# Content to put in the working copies of the mounts that follow a line:
# the file at path gets bytes. A write or a merge of a mounted line updates
# its files this way, and the mount's stream learns the bytes first, so
# the fetch that follows records nothing.
type Carry is Data:
  Carry{path: String, bytes: Shared.Bytes()}

# The result of a command: the records to keep (Daemon.replay of them is
# the daemon after it), the answer, and the content to carry to the
# working copies of the line whose key is line.
type Handled is Data:
  Handled{
    records: List<&2, Journal.Record>,
    response: Response,
    line: String,
    carries: List<&2, Carry>
  }

# the records of a result
def Handled.records(h: Handled) -> List<&2, Journal.Record>:
  match h:
    case Handled{rs, r, l, cs}:
      rs

# the result is not a refusal
def Handled.ok(h: Handled) -> Bool:
  match h:
    case Handled{rs, Said{ok, ls}, l, cs}:
      ok
    case _:
      True{}

# the line of the space sp named ln: as the daemon has it, else a new one
def Daemon.line_in(d: Daemon, +sp: String, +ln: String) -> Lines.Line:
  Maybe.default(&2, Lines.Line, Daemon.line_at(d, Lines.Line.key(sp, ln)), Lines.Line.new(sp, ln))

# the ids of the nodes of n whose hex starts with each prefix of ps, each
# matching exactly one node; None when a prefix matches none or several
law Daemon.ids:
  for d: Daemon
  for n: Shared.Name
  for ps: List<&2, String>
  Maybe<&2, List<&2, Shared.Bytes()>>

# the line that the text t names (a name, or a key `<space>:<name>`), when
# exactly one line has it
law Daemon.line_ref:
  for d: Daemon
  for t: String
  Maybe<&2, Lines.Line>

# the result of the command c of the agent a, with the data b, on d
law Daemon.handle:
  for d: Daemon
  for a: String
  for c: Command
  for b: Shared.Bytes()
  Handled

# a reading command keeps no record
law reads_record_nothing:
  for d: Daemon
  for a: String
  for c: Command
  for b: Shared.Bytes()
  for r: {Command.reads(c) == True{}: Bool}
  {Handled.records(Daemon.handle(d, a, c, b)) == []: List<&2, Journal.Record>}

# a write that did not see the heads of the line now is refused, and keeps
# nothing
law write_stale:
  for d: Daemon
  for a: String
  for n: Shared.Name
  for ln: String
  for ps: List<&2, String>
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for i: {Daemon.ids(d, n, ps) == Some{e}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for s: {
    History.Ids.is_eq(
      e,
      Lines.Line.heads(Daemon.line_in(d, Shared.Name.space(n), ln), n)
    )
      == False{}: Bool
  }
  {Handled.records(Daemon.handle(d, a, WriteTo{n, ln, ps}, b)) == []: List<&2, Journal.Record>} &
    {Handled.ok(Daemon.handle(d, a, WriteTo{n, ln, ps}, b)) == False{}: Bool}

# a write that saw the heads of the line now keeps exactly one version: the
# data, after those heads, signed by the agent
law write_kept:
  for d: Daemon
  for a: String
  for n: Shared.Name
  for ln: String
  for ps: List<&2, String>
  for b: Shared.Bytes()
  for e: List<&2, Shared.Bytes()>
  for i: {Daemon.ids(d, n, ps) == Some{e}: Maybe<&2, List<&2, Shared.Bytes()>>}
  for s: {
    History.Ids.is_eq(
      e,
      Lines.Line.heads(Daemon.line_in(d, Shared.Name.space(n), ln), n)
    )
      == True{}: Bool
  }
  {
    Handled.records(
      Daemon.handle(d, a, WriteTo{n, ln, ps}, b)
    )
      == [
        Journal.Kept{
          ln,
          Some{b},
          History.Node{
            n,
            Lines.Line.heads(Daemon.line_in(d, Shared.Name.space(n), ln), n),
            History.Has{Store.Tree.root(Core.Core.items(b))},
            None{},
            History.Agent{a}
          }
        }
      ]: List<&2, Journal.Record>
  }

# a merge is every resource or none: a merge that is refused (a clash, or
# a line it cannot name) keeps nothing, so no resource of the target moves
law merge_all_or_nothing:
  for d: Daemon
  for a: String
  for f: String
  for t: String
  for b: Shared.Bytes()
  for o: {Handled.ok(Daemon.handle(d, a, MergeOf{f, t}, b)) == False{}: Bool}
  {Handled.records(Daemon.handle(d, a, MergeOf{f, t}, b)) == []: List<&2, Journal.Record>}

# `affects` of a line catches the agent's marker up with it, and keeps
# nothing else
law affects_sees:
  for d: Daemon
  for a: String
  for t: String
  for b: Shared.Bytes()
  for l: Lines.Line
  for h: {Daemon.line_ref(d, t) == Some{l}: Maybe<&2, Lines.Line>}
  {
    Handled.records(
      Daemon.handle(d, a, AffectsOf{t}, b)
    )
      == [Journal.Saw{a, Lines.Line.id(l)}]: List<&2, Journal.Record>
  }

# Answers
# -------

# What the daemon does about a request. Reply: answer at once. DoMount,
# DoUnmount: change the mounts (the loop does the IO: the root, its space
# file, the watcher, the mounts file), then answer. DoStop: answer
# Stopping, then end. DoAsk: run the command c for the agent with data
# (Daemon.handle), keep its records, then answer.
type Action is Data:
  Reply{response: Response}
  DoMount{uri: String, globs: List<&2, String>, line: String}
  DoUnmount{uri: String}
  DoStop{}
  DoAsk{agent: String, command: Command, data: Shared.Bytes()}

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
    case Daemon{s, h, ls, ms, cs, bk}:
      Daemon.infos.go(h, ms)

# d has no mount and no other client: a Stop without force may end it
def Daemon.idle(d: Daemon) -> Bool:
  match d:
    case Daemon{s, h, ls, ms, cs, bk}:
      Bool.and(List.is_empty(&2, Local, ms), Nat.is_eq(cs, 0n))

# the clients of d
def Daemon.clients(d: Daemon) -> Nat:
  match d:
    case Daemon{s, h, ls, ms, cs, bk}:
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

# what to do about the words of an Ask: the command they spell, or a
# refusal with the usage
def Command.decided(r: Result<&2, &2, String, Command>, a: String, b: Shared.Bytes()) -> Action:
  match r:
    case Fail{u}:
      Reply{Said{False{}, [u]}}
    case Done{c}:
      DoAsk{a, c, b}

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
    case Ask{a, ws, b}:
      Command.decided(Command.read(ws), a, b)
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
    case Daemon{s, h, ls, ms, cs, bk}:
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
