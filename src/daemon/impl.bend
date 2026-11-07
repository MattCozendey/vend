import Base
import ../core/impl.bend as CoreImpl
import ../core/spec.bend as Core
import ../endpoints/spec.bend as Ep
import ../graph/spec.bend as Graph
import ../hash/spec.bend as Hash
import ../history/spec.bend as History
import ../impact/spec.bend as Impact
import ../journal/impl.bend as J
import ../journal/spec.bend as Journal
import ../lines/spec.bend as Lines
import ../shared/bools.bend as Bools
import ../shared/bytes.bend as Octets
import ../shared/resources.bend as Resources
import ../shared/tables.bend as Tables
import ../shared/texts.bend as Cuts
import ../shared/uris.bend as Uris
import ../store/spec.bend as Store
import ../views/bend/spec.bend as Bend
import ../views/shared.bend as Vs
import ../views/text/spec.bend as Text
import ./spec.bend as Spec
import ./views.bend as Views

def Spec.Daemon.step(d, l, i):
  +d = d
  +l = l
  Spec.Daemon.stepped(d, Spec.Local.globs(l), Core.Core.step(Spec.Daemon.core(d, l), i))

# Decoding
# --------
# Each reader takes what it needs from the front of the bytes and gives the
# rest, as the journal's readers do.

# n texts, framed as UTF-8, one after another
def Texts.read.go(n: Nat, b: Octets.Bytes()) -> Maybe<&2, J.Got<List<&2, String>>>:
  match n:
    case 0n:
      Some{J.Got{[], b}}
    case 1n+k:
      J.Got.then(
        String,
        List<&2, String>,
        J.Utf8.read(b),
        x => r => J.Got.then(
          List<&2, String>,
          List<&2, String>,
          Texts.read.go(k, r),
          xs => r2 => Some{J.Got{x <> xs, r2}}
        )
      )

# texts: their count, then each
def Texts.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<List<&2, String>>>:
  J.Got.then(Nat, List<&2, String>, J.Leb.read(b), n => r => Texts.read.go(n, r))

# the value of m when it read all of the bytes, else None
def Read.whole(-A: Data, m: Maybe<&2, J.Got<A>>) -> Maybe<&2, A>:
  match m:
    case Some{J.Got{v, Nil{}}}:
      Some{v}
    case _:
      None{}

# a Bool: 0 or 1
def Flag.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<Bool>>:
  match b:
    case Con{0, r}:
      Some{J.Got{False{}, r}}
    case Con{1, r}:
      Some{J.Got{True{}, r}}
    case _:
      None{}

# what a request asks, after its tag
def Body.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<Spec.Body>>:
  match b:
    case Con{0, r}:
      Some{J.Got{Spec.Status{}, r}}
    case Con{1, r}:
      J.Got.then(
        String,
        Spec.Body,
        J.Utf8.read(r),
        u => r2 => J.Got.then(
          List<&2, String>,
          Spec.Body,
          Texts.read(r2),
          gs => r3 => J.Got.then(
            String,
            Spec.Body,
            J.Utf8.read(r3),
            ln => r4 => Some{J.Got{Spec.Mount{u, gs, ln}, r4}}
          )
        )
      )
    case Con{2, r}:
      J.Got.then(String, Spec.Body, J.Utf8.read(r), u => r2 => Some{J.Got{Spec.Unmount{u}, r2}})
    case Con{3, r}:
      J.Got.then(Bool, Spec.Body, Flag.read(r), f => r2 => Some{J.Got{Spec.Stop{f}, r2}})
    case Con{4, r}:
      J.Got.then(
        String,
        Spec.Body,
        J.Utf8.read(r),
        a => r2 => J.Got.then(
          List<&2, String>,
          Spec.Body,
          Texts.read(r2),
          ws => r3 => J.Got.then(
            Octets.Bytes(),
            Spec.Body,
            J.Framed.read(r3),
            b => r4 => Some{J.Got{Spec.Ask{a, ws, b}, r4}}
          )
        )
      )
    case _:
      None{}

def Spec.Request.decode(b):
  Read.whole(
    Spec.Request,
    J.Got.then(
      Octets.Bytes(),
      Spec.Request,
      J.Framed.read(b),
      t => r => J.Got.then(
        Spec.Body,
        Spec.Request,
        Body.read(r),
        x => r2 => Some{J.Got{Spec.Request{t, x}, r2}}
      )
    )
  )

# one mount's status
def Info.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<Spec.Info>>:
  J.Got.then(
    String,
    Spec.Info,
    J.Utf8.read(b),
    u => r => J.Got.then(
      String,
      Spec.Info,
      J.Utf8.read(r),
      ln => r2 => J.Got.then(
        String,
        Spec.Info,
        J.Utf8.read(r2),
        sp => r3 => J.Got.then(
          Nat,
          Spec.Info,
          J.Leb.read(r3),
          n => r4 => Some{J.Got{Spec.Info{u, ln, sp, n}, r4}}
        )
      )
    )
  )

# n statuses, one after another
def Infos.read.go(n: Nat, b: Octets.Bytes()) -> Maybe<&2, J.Got<List<&2, Spec.Info>>>:
  match n:
    case 0n:
      Some{J.Got{[], b}}
    case 1n+k:
      J.Got.then(
        Spec.Info,
        List<&2, Spec.Info>,
        Info.read(b),
        x => r => J.Got.then(
          List<&2, Spec.Info>,
          List<&2, Spec.Info>,
          Infos.read.go(k, r),
          xs => r2 => Some{J.Got{x <> xs, r2}}
        )
      )

# a response, from its tag
def Response.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<Spec.Response>>:
  match b:
    case Con{0, r}:
      J.Got.then(
        Nat,
        Spec.Response,
        J.Leb.read(r),
        n => r2 => J.Got.then(
          List<&2, Spec.Info>,
          Spec.Response,
          Infos.read.go(n, r2),
          infos => r3 => J.Got.then(
            Nat,
            Spec.Response,
            J.Leb.read(r3),
            c => r4 => Some{J.Got{Spec.StatusIs{infos, c}, r4}}
          )
        )
      )
    case Con{1, r}:
      J.Got.then(
        String,
        Spec.Response,
        J.Utf8.read(r),
        sp => r2 => Some{J.Got{Spec.Mounted{sp}, r2}}
      )
    case Con{2, r}:
      Some{J.Got{Spec.Unmounted{}, r}}
    case Con{3, r}:
      Some{J.Got{Spec.Stopping{}, r}}
    case Con{4, r}:
      J.Got.then(
        String,
        Spec.Response,
        J.Utf8.read(r),
        why => r2 => Some{J.Got{Spec.Denied{why}, r2}}
      )
    case Con{5, r}:
      J.Got.then(
        Bool,
        Spec.Response,
        Flag.read(r),
        ok => r2 => J.Got.then(
          List<&2, String>,
          Spec.Response,
          Texts.read(r2),
          ls => r3 => Some{J.Got{Spec.Said{ok, ls}, r3}}
        )
      )
    case _:
      None{}

def Spec.Response.decode(b):
  Read.whole(Spec.Response, Response.read(b))

# the entry that m read in front of the entries that k reads from the rest
def Entries.read.one(
  m: Maybe<&2, J.Got<Spec.Entry>>,
  k: Octets.Bytes() -> Maybe<&2, List<&2, Spec.Entry>>
) -> Maybe<&2, List<&2, Spec.Entry>>:
  match m:
    case None{}:
      None{}
    case Some{J.Got{e, r}}:
      Maybe.map(&2, List<&2, Spec.Entry>, List<&2, Spec.Entry>, es => e <> es, k(r))

# the agent of an entry: 0, or 1 then its name
def Agent.read(b: Octets.Bytes()) -> Maybe<&2, J.Got<Maybe<&2, String>>>:
  match b:
    case Con{0, r}:
      Some{J.Got{None{}, r}}
    case Con{1, r}:
      J.Got.then(String, Maybe<&2, String>, J.Utf8.read(r), n => r2 => Some{J.Got{Some{n}, r2}})
    case _:
      None{}

# entries up to the end of the bytes; fuel counts the bytes left
def Entries.read.go(fuel: Nat, b: Octets.Bytes()) -> Maybe<&2, List<&2, Spec.Entry>>:
  match fuel b:
    case _ Nil{}:
      Some{[]}
    case 0n bs:
      None{}
    case 1n+f bs:
      Entries.read.one(
        J.Got.then(
          String,
          Spec.Entry,
          J.Utf8.read(bs),
          u => r => J.Got.then(
            String,
            Spec.Entry,
            J.Utf8.read(r),
            ln => r2 => J.Got.then(
              List<&2, String>,
              Spec.Entry,
              Texts.read(r2),
              gs => r3 => J.Got.then(
                Maybe<&2, String>,
                Spec.Entry,
                Agent.read(r3),
                ag => r4 => Some{J.Got{Spec.Entry{u, ln, gs, ag}, r4}}
              )
            )
          )
        ),
        r => Entries.read.go(f, r)
      )

def Spec.Entries.decode(b):
  +b = b
  Entries.read.go(List.length(&2, U32, b), b)

# The book and the journal
# ------------------------

# a mount that serves nothing: the core that replays a record for the
# shared store and history only
def Apply.nomount() -> Core.Mount:
  Core.Mount{"", "", Uris.Uri{"file", None{}, "/"}, [], History.Outside{}}

# d after the Kept record of the line named ln with content ct and node v
def Apply.kept(
  d: Spec.Daemon,
  +ln: String,
  ct: Maybe<&2, Octets.Bytes()>,
  +v: History.Node
) -> Spec.Daemon:
  match d:
    case Spec.Daemon{s, h, ls, ms, cs, bk}:
      +c = Core.Core.replay(
        Core.Core{
          Apply.nomount(),
          s,
          h,
          Lines.Line.new("", ""),
          Tables.Table.new(Ep.Stream),
          Tables.Table.new(Maybe<&2, Resources.Name>),
          []
        },
        [Journal.Kept{ln, ct, v}]
      )
      +h2 = Core.Core.history(c)
      +sp = Resources.Name.space(History.Node.name(v))
      +key = Lines.Line.key(sp, ln)
      +ls = ls
      l = Maybe.default(
        &2,
        Lines.Line,
        Tables.Table.get(Lines.Line, ls, key),
        Lines.Line.new(sp, ln)
      )
      Spec.Daemon{
        Core.Core.store(c),
        h2,
        Tables.Table.set(Lines.Line, ls, key, CoreImpl.Replay.advance(l, h2, ln, v)),
        ms,
        cs,
        bk
      }

# d after the agent a caught up with the line whose key is k, found as m
def Apply.saw(d: Spec.Daemon, a: String, m: Maybe<&2, Lines.Line>) -> Spec.Daemon:
  match d m:
    case k None{}:
      k
    case Spec.Daemon{s, h, ls, ms, cs, Spec.Book{sn, mk, og}} Some{l}:
      Spec.Daemon{s, h, ls, ms, cs, Spec.Book{Lines.SeenBook.update(sn, a, l), mk, og}}

# d after the mark nm of the line found as m, unless the mark exists
def Apply.marked(
  d: Spec.Daemon,
  m: Maybe<&2, Lines.Line>,
  +key: String,
  nm: String,
  msg: String,
  a: History.Author
) -> Spec.Daemon:
  match d m:
    case k None{}:
      k
    case Spec.Daemon{+s, +h, +ls, +ms, +cs, Spec.Book{+sn, +mk, +og}} Some{l}:
      Bools.Bool.when(
        Spec.Daemon,
        Maybe.is_some(&2, Lines.Mark, Tables.Table.get(Lines.Mark, mk, key)),
        u => Spec.Daemon{s, h, ls, ms, cs, Spec.Book{sn, mk, og}},
        u => Spec.Daemon{
          s,
          h,
          ls,
          ms,
          cs,
          Spec.Book{sn, Tables.Table.set(Lines.Mark, mk, key, Lines.Mark.of(l, nm, msg, a)), og}
        }
      )

# the line a fork starts from: the line whose key is f, or its mark
def Apply.source(d: Spec.Daemon, f: String, m: Maybe<&2, String>) -> Maybe<&2, Lines.Line>:
  match m:
    case None{}:
      Spec.Daemon.line_at(d, f)
    case Some{x}:
      Maybe.map(&2, Lines.Mark, Lines.Line, mk => Lines.Mark.at(mk), Spec.Daemon.mark(d, f, x))

# d after the line whose key is k forked from the source src, unless it
# exists
def Apply.forked(
  d: Spec.Daemon,
  src: Maybe<&2, Lines.Line>,
  +k: String,
  f: String,
  m: Maybe<&2, String>
) -> Spec.Daemon:
  match d src:
    case x None{}:
      x
    case Spec.Daemon{+s, +h, +ls, +ms, +cs, Spec.Book{+sn, +mk, +og}} Some{l}:
      +nl = Lines.Line.fork(l, Spec.Key.name(k))
      Bools.Bool.when(
        Spec.Daemon,
        Maybe.is_some(&2, Lines.Line, Tables.Table.get(Lines.Line, ls, k)),
        u => Spec.Daemon{s, h, ls, ms, cs, Spec.Book{sn, mk, og}},
        u => Spec.Daemon{
          s,
          h,
          Tables.Table.set(Lines.Line, ls, k, nl),
          ms,
          cs,
          Spec.Book{sn, mk, Tables.Table.set(Spec.Origin, og, k, Spec.Origin{f, m, nl})}
        }
      )

# d after the record r (Spec.Daemon.apply)
def Apply.one(+d: Spec.Daemon, r: Journal.Record) -> Spec.Daemon:
  match r:
    case Journal.Kept{ln, ct, v}:
      Apply.kept(d, ln, ct, v)
    case Journal.Saw{a, k}:
      Apply.saw(d, a, Spec.Daemon.line_at(d, k))
    case Journal.Marked{+k, +nm, msg, a}:
      Apply.marked(d, Spec.Daemon.line_at(d, k), Spec.Mark.key(k, nm), nm, msg, a)
    case Journal.Forked{k, +f, +m}:
      Apply.forked(d, Apply.source(d, f, m), k, f, m)

def Spec.Daemon.apply(d, r):
  Apply.one(d, r)

# d after the records, in order
def Apply.all(rs: List<&2, Journal.Record>, d: Spec.Daemon) -> Spec.Daemon:
  match rs:
    case Nil{}:
      d
    case Con{r, t}:
      Apply.all(t, Spec.Daemon.apply(d, r))

def Spec.Daemon.replay(d, rs):
  Apply.all(rs, d)

# References
# ----------

# the nodes of the history of d
def Ref.nodes(d: Spec.Daemon) -> Tables.Table<History.Node>:
  match d:
    case Spec.Daemon{s, h, ls, ms, cs, bk}:
      Spec.Versions.nodes(h)

# a and b are the same name
def Ref.same(a: Resources.Name, b: Resources.Name) -> Bool:
  String.eq(Resources.Name.show(a), Resources.Name.show(b))

# the id of the node found under a key, when it is a node of n
def Ref.of(m: Maybe<&2, History.Node>, n: Resources.Name) -> List<&2, Octets.Bytes()>:
  match m:
    case None{}:
      []
    case Some{+v}:
      Bools.Bool.when(
        List<&2, Octets.Bytes()>,
        Ref.same(History.Node.name(v), n),
        u => [History.Node.id(v)],
        u => []
      )

# the ids of the nodes of n among the keys ks whose hex starts with p
def Ref.matches(
  ks: List<&2, String>,
  +ns: Tables.Table<History.Node>,
  +n: Resources.Name,
  +p: String
) -> List<&2, Octets.Bytes()>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, t}:
      +rest = Ref.matches(t, ns, n, p)
      Bools.Bool.when(
        List<&2, Octets.Bytes()>,
        String.starts_with(k, p),
        u => List.append(
          &2,
          Octets.Bytes(),
          Ref.of(Tables.Table.get(History.Node, ns, k), n),
          rest
        ),
        u => rest
      )

# the one id of xs
def Ref.one(xs: List<&2, Octets.Bytes()>) -> Maybe<&2, Octets.Bytes()>:
  match xs:
    case Con{x, Nil{}}:
      Some{x}
    case _:
      None{}

# x before the ids of the rest, when both are found
def Ref.cons(
  m: Maybe<&2, Octets.Bytes()>,
  r: Maybe<&2, List<&2, Octets.Bytes()>>
) -> Maybe<&2, List<&2, Octets.Bytes()>>:
  match m r:
    case Some{x} Some{xs}:
      Some{x <> xs}
    case _ _:
      None{}

# the id of each prefix of ps among the keys ks of the nodes ns of n
def Ref.all(
  ps: List<&2, String>,
  +ks: List<&2, String>,
  +ns: Tables.Table<History.Node>,
  +n: Resources.Name
) -> Maybe<&2, List<&2, Octets.Bytes()>>:
  match ps:
    case Nil{}:
      Some{[]}
    case Con{p, t}:
      Ref.cons(Ref.one(Ref.matches(ks, ns, n, p)), Ref.all(t, ks, ns, n))

def Spec.Daemon.ids(d, n, ps):
  +ns = Ref.nodes(d)
  Ref.all(ps, Tables.Table.keys(History.Node, ns), ns, n)

# the keys among ks whose line name is t
def Ref.named(ks: List<&2, String>, +t: String) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, +r}:
      Bools.Bool.when(
        List<&2, String>,
        String.eq(Spec.Key.name(k), t),
        u => k <> Ref.named(r, t),
        u => Ref.named(r, t)
      )

# the line of the one key of ks
def Ref.line_of(d: Spec.Daemon, ks: List<&2, String>) -> Maybe<&2, Lines.Line>:
  match ks:
    case Con{k, Nil{}}:
      Spec.Daemon.line_at(d, k)
    case _:
      None{}

# the lines of d
def Ref.lines(d: Spec.Daemon) -> Tables.Table<Lines.Line>:
  match d:
    case Spec.Daemon{s, h, ls, ms, cs, bk}:
      ls

def Spec.Daemon.line_ref(d, t):
  +d = d
  +t = t
  Bools.Bool.when(
    Maybe<&2, Lines.Line>,
    Cuts.Text.has(t, 58),
    u => Spec.Daemon.line_at(d, t),
    u => Ref.line_of(d, Ref.named(Tables.Table.keys(Lines.Line, Ref.lines(d)), t))
  )

# What a reference to a line or a mark gives: its key, its mark (if any),
# and the line as it is (or was, for a mark).
type Source is Data:
  Source{key: String, mark: Maybe<&2, String>, at: Lines.Line}

# the source of the mark named m of the line found as l
def Ref.marked(d: Spec.Daemon, l: Maybe<&2, Lines.Line>, +m: String) -> Maybe<&2, Source>:
  match l:
    case None{}:
      None{}
    case Some{x}:
      +k = Lines.Line.id(x)
      Maybe.map(
        &2,
        Lines.Mark,
        Source,
        mk => Source{k, Some{m}, Lines.Mark.at(mk)},
        Spec.Daemon.mark(d, k, m)
      )

# the source of a line found as l
def Ref.lined(l: Maybe<&2, Lines.Line>) -> Maybe<&2, Source>:
  match l:
    case None{}:
      None{}
    case Some{+x}:
      Some{Source{Lines.Line.id(x), None{}, x}}

# the source that t names: `<line>@<mark>`, or a line
def Ref.source.of(+d: Spec.Daemon, c: Maybe<&2, Cuts.Cut>, t: String) -> Maybe<&2, Source>:
  match c:
    case None{}:
      Ref.lined(Spec.Daemon.line_ref(d, t))
    case Some{Cuts.Cut{b, a}}:
      Ref.marked(d, Spec.Daemon.line_ref(d, b), a)

# the source that t names
def Ref.source(d: Spec.Daemon, +t: String) -> Maybe<&2, Source>:
  Ref.source.of(d, Cuts.Text.cut(t, 64), t)

# Contents
# --------

# the history of d
def Ref.history(d: Spec.Daemon) -> History.History:
  match d:
    case Spec.Daemon{s, h, ls, ms, cs, bk}:
      h

# the store of d
def Ref.store(d: Spec.Daemon) -> Store.Store:
  match d:
    case Spec.Daemon{s, h, ls, ms, cs, bk}:
      s

# the bytes of the items the store read, if it could
def Content.bytes(m: Maybe<&2, List<&2, Octets.Bytes()>>) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{items}:
      Some{Some{CoreImpl.Replay.bytes(items)}}

# the content of the node found: Some{None} for a version that says gone
def Content.of(d: Spec.Daemon, m: Maybe<&2, History.Node>) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{History.Node{n, ps, History.Has{r}, f, a}}:
      Content.bytes(Store.Tree.read(Ref.store(d), r))
    case Some{History.Node{n, ps, History.Gone{}, f, a}}:
      Some{None{}}

# the content of the version x: None when the daemon lacks it, Some{None}
# for a version that says gone
def Content.at(+d: Spec.Daemon, x: Octets.Bytes()) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  Content.of(d, History.History.get(Ref.history(d), x))

# the id that the version text v names for n: a line's one head, else an
# id prefix
def Ref.version.of(
  l: Maybe<&2, Lines.Line>,
  d: Spec.Daemon,
  n: Resources.Name,
  v: String
) -> Maybe<&2, Octets.Bytes()>:
  match l:
    case Some{x}:
      Ref.one(Lines.Line.heads(x, n))
    case None{}:
      Maybe.default(
        &2,
        Maybe<&2, Octets.Bytes()>,
        Maybe.map(
          &2,
          List<&2, Octets.Bytes()>,
          Maybe<&2, Octets.Bytes()>,
          xs => Ref.one(xs),
          Spec.Daemon.ids(d, n, [v])
        ),
        None{}
      )

# the id that the version text v names for n
def Ref.version(+d: Spec.Daemon, n: Resources.Name, +v: String) -> Maybe<&2, Octets.Bytes()>:
  Ref.version.of(Spec.Daemon.line_ref(d, v), d, n, v)

# Showing
# -------

# the first 8 hex digits of an id
def Show.id(x: Octets.Bytes()) -> String:
  String.take(Hash.Hash.hex(x), 8n)

# the ids, short, one after another
def Show.ids(xs: List<&2, Octets.Bytes()>) -> String:
  match xs:
    case Nil{}:
      "none"
    case Con{x, Nil{}}:
      Show.id(x)
    case Con{x, t}:
      String.concat([Show.id(x), ",", Show.ids(t)])

# who an author is
def Show.author(a: History.Author) -> String:
  match a:
    case History.Agent{n}:
      n
    case History.Outside{}:
      "outside"

# a refusal
def Show.no(why: String) -> Spec.Handled:
  Spec.Handled{[], Spec.Said{False{}, [why]}, "", []}

# an answer that keeps nothing
def Show.yes(ls: List<&2, String>) -> Spec.Handled:
  Spec.Handled{[], Spec.Said{True{}, ls}, "", []}

# the lines of a text, or a note for bytes that are not text
def Show.text(m: Maybe<&2, String>, n: Nat) -> Spec.Handled:
  match m:
    case None{}:
      Show.yes([String.concat(["binary content, ", Nat.show(n), " bytes"])])
    case Some{s}:
      Show.yes(String.split(s, Chr{10}))

# the lines of a content
def Show.content(m: Maybe<&2, Maybe<&2, Octets.Bytes()>>) -> Spec.Handled:
  match m:
    case None{}:
      Show.no("no such version")
    case Some{None{}}:
      Show.yes(["(gone)"])
    case Some{Some{+b}}:
      Show.text(Text.Text.decode(b), List.length(&2, U32, b))

# The history, walked
# -------------------

# the parents of a node found, if any
def Dag.parents(m: Maybe<&2, History.Node>) -> List<&2, Octets.Bytes()>:
  match m:
    case None{}:
      []
    case Some{v}:
      History.Node.parents(v)

# the ids reachable from queue through parents, each once, in the order
# found; fuel bounds the steps
def Dag.walk(
  fuel: Nat,
  +h: History.History,
  queue: List<&2, Octets.Bytes()>,
  seen: List<&2, Octets.Bytes()>
) -> List<&2, Octets.Bytes()>:
  match fuel queue:
    case 0n q:
      List.reverse(&2, Octets.Bytes(), seen)
    case _ Nil{}:
      List.reverse(&2, Octets.Bytes(), seen)
    case 1n+(+f) Con{+x, +t}:
      +seen = seen
      Bools.Bool.when(
        List<&2, Octets.Bytes()>,
        History.Ids.has(seen, x),
        u => Dag.walk(f, h, t, seen),
        u => Dag.walk(
          f,
          h,
          List.append(&2, Octets.Bytes(), t, Dag.parents(History.History.get(h, x))),
          x <> seen
        )
      )

# fuel for a walk of h: more steps than nodes and parents
def Dag.fuel(h: History.History) -> Nat:
  +n = List.length(&2, String, Tables.Table.keys(History.Node, Spec.Versions.nodes(h)))
  Nat.add(Nat.mul(n, n), 2n)

# the ids reachable from xs
def Dag.reach(+h: History.History, xs: List<&2, Octets.Bytes()>) -> List<&2, Octets.Bytes()>:
  Dag.walk(Dag.fuel(h), h, xs, [])

# the first id of ys that xs also has
def Dag.first(
  ys: List<&2, Octets.Bytes()>,
  +xs: List<&2, Octets.Bytes()>
) -> Maybe<&2, Octets.Bytes()>:
  match ys:
    case Nil{}:
      None{}
    case Con{+y, t}:
      Bools.Bool.when(
        Maybe<&2, Octets.Bytes()>,
        History.Ids.has(xs, y),
        u => Some{y},
        u => Dag.first(t, xs)
      )

# the nearest common ancestor of a and b (each its own ancestor)
def Dag.base(
  +h: History.History,
  a: Octets.Bytes(),
  b: Octets.Bytes()
) -> Maybe<&2, Octets.Bytes()>:
  Dag.first(Dag.reach(h, [b]), Dag.reach(h, [a]))

# Answers
# -------

# the heads table of a line
def Answer.table(l: Lines.Line) -> Tables.Table<List<&2, Octets.Bytes()>>:
  match l:
    case Lines.Line{sp, nm, hs}:
      hs

# the space of a line
def Answer.space(l: Lines.Line) -> String:
  match l:
    case Lines.Line{sp, nm, hs}:
      sp

# the paths a line follows
def Answer.paths(l: Lines.Line) -> List<&2, String>:
  Tables.Table.keys(List<&2, Octets.Bytes()>, Answer.table(l))

# how many paths of ps the line l follows differently than at
def Answer.moved(
  ps: List<&2, String>,
  +l: Tables.Table<List<&2, Octets.Bytes()>>,
  +at: Tables.Table<List<&2, Octets.Bytes()>>
) -> Nat:
  match ps:
    case Nil{}:
      0n
    case Con{+p, t}:
      +rest = Answer.moved(t, l, at)
      Bools.Bool.when(
        Nat,
        History.Ids.is_eq(Lines.Heads.at(l, p), Lines.Heads.at(at, p)),
        u => rest,
        u => 1n+rest
      )

# the status of the line whose key is k
def Answer.line(k: String, l: Maybe<&2, Lines.Line>, o: Maybe<&2, Spec.Origin>) -> String:
  match l o:
    case Some{+x} None{}:
      String.concat(
        [k, "  ", Nat.show(List.length(&2, String, Answer.paths(x))), " resources  root line"]
      )
    case Some{+x} Some{Spec.Origin{f, m, at}}:
      String.concat(
        [
          k,
          "  ",
          Nat.show(List.length(&2, String, Answer.paths(x))),
          " resources  moved ",
          Nat.show(Answer.moved(Answer.paths(x), Answer.table(x), Answer.table(at))),
          " since its fork from ",
          f,
          Maybe.default(
            &2,
            String,
            Maybe.map(&2, String, String, mk => String.append("@", mk), m),
            ""
          )
        ]
      )
    case _ _:
      k

# the status of every line of ks
def Answer.lines(ks: List<&2, String>, +d: Spec.Daemon) -> List<&2, String>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{+k, t}:
      Answer.line(k, Spec.Daemon.line_at(d, k), Spec.Daemon.origin(d, k)) <> Answer.lines(t, d)

# the node is by the author named ma, when one is named ("outside" names
# writes from outside)
def Answer.by(v: History.Node, ma: Maybe<&2, String>) -> Bool:
  match ma:
    case None{}:
      True{}
    case Some{a}:
      String.eq(Show.author(History.Node.author(v)), a)

# what a node holds, in a word
def Answer.body(v: History.Node) -> String:
  match v:
    case History.Node{n, ps, History.Has{r}, f, a}:
      "content"
    case History.Node{n, ps, History.Gone{}, f, a}:
      "gone"

# the log line of the node found, if it is by the author asked for
def Answer.entry(
  m: Maybe<&2, History.Node>,
  x: Octets.Bytes(),
  ma: Maybe<&2, String>
) -> List<&2, String>:
  match m:
    case None{}:
      []
    case Some{+v}:
      line = String.concat(
        [
          Show.id(x),
          " by ",
          Show.author(History.Node.author(v)),
          " ",
          Answer.body(v),
          " after ",
          Show.ids(History.Node.parents(v))
        ]
      )
      Bools.Bool.when(List<&2, String>, Answer.by(v, ma), u => [line], u => [])

# the log lines of the ids xs
def Answer.entries(
  xs: List<&2, Octets.Bytes()>,
  +h: History.History,
  +ma: Maybe<&2, String>
) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      List.append(
        &2,
        String,
        Answer.entry(History.History.get(h, x), x, ma),
        Answer.entries(t, h, ma)
      )

# the heads a log starts from: those of the line named, else every tip
def Answer.starts(
  d: Spec.Daemon,
  n: Resources.Name,
  ml: Maybe<&2, String>
) -> List<&2, Octets.Bytes()>:
  match ml:
    case None{}:
      History.History.tips(Ref.history(d), n)
    case Some{t}:
      Maybe.default(
        &2,
        List<&2, Octets.Bytes()>,
        Maybe.map(
          &2,
          Lines.Line,
          List<&2, Octets.Bytes()>,
          l => Lines.Line.heads(l, n),
          Spec.Daemon.line_ref(d, t)
        ),
        []
      )

# the log of n
def Answer.log(
  +d: Spec.Daemon,
  +n: Resources.Name,
  ml: Maybe<&2, String>,
  ma: Maybe<&2, String>
) -> Spec.Handled:
  +h = Ref.history(d)
  +ls = Answer.entries(Dag.reach(h, Answer.starts(d, n, ml)), h, ma)
  Bools.Bool.when(
    Spec.Handled,
    List.is_empty(&2, String, ls),
    u => Show.yes([String.append("no versions of ", Resources.Name.show(n))]),
    u => Show.yes(ls)
  )

# the content of the version that m found
def Answer.content(
  d: Spec.Daemon,
  m: Maybe<&2, Octets.Bytes()>
) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Content.at(d, x)

# the content of the version text mv of n, or of n's one tip
def Answer.show(+d: Spec.Daemon, n: Resources.Name, mv: Maybe<&2, String>) -> Spec.Handled:
  match mv:
    case None{}:
      Show.content(Answer.content(d, Ref.one(History.History.tips(Ref.history(d), n))))
    case Some{v}:
      Show.content(Answer.content(d, Ref.version(d, n, v)))

# the diff of two contents found
def Answer.diff.of(
  path: String,
  x: Maybe<&2, Maybe<&2, Octets.Bytes()>>,
  y: Maybe<&2, Maybe<&2, Octets.Bytes()>>
) -> Spec.Handled:
  match x y:
    case Some{Some{a}} Some{Some{b}}:
      Show.yes(Views.View.diff(path, a, b))
    case Some{a} Some{b}:
      Show.yes(["one side is gone"])
    case _ _:
      Show.no("no such version")

# the diff of the versions a and b of n
def Answer.diff(+d: Spec.Daemon, +n: Resources.Name, a: String, b: String) -> Spec.Handled:
  Answer.diff.of(
    Resources.Name.path(n),
    Answer.content(d, Ref.version(d, n, a)),
    Answer.content(d, Ref.version(d, n, b))
  )

# the Bend document of a content, if it is UTF-8
def Answer.module(c: Maybe<&2, Maybe<&2, Octets.Bytes()>>) -> Maybe<&2, Bend.Module>:
  match c:
    case Some{Some{b}}:
      Maybe.map(&2, String, Bend.Module, s => Views.View.module(s), Text.Text.decode(b))
    case _:
      None{}

# the content of the one head of hs
def Answer.head(
  d: Spec.Daemon,
  hs: List<&2, Octets.Bytes()>
) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  Answer.content(d, Ref.one(hs))

# the import edges of the Bend resources at the paths ps of the line l
def Answer.edges(ps: List<&2, String>, +d: Spec.Daemon, +l: Lines.Line) -> List<&2, Graph.Edge>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      +n = {Resources.Name{Answer.space(l), p}: Resources.Name}
      +rest = Answer.edges(t, d, l)
      Bools.Bool.when(
        List<&2, Graph.Edge>,
        Views.View.is_bend(p),
        u => List.append(
          &2,
          Graph.Edge,
          Maybe.default(
            &2,
            List<&2, Graph.Edge>,
            Maybe.map(
              &2,
              Bend.Module,
              List<&2, Graph.Edge>,
              m => Bend.Bend.edges(n, m),
              Answer.module(Answer.head(d, Lines.Line.heads(l, n)))
            ),
            []
          ),
          rest
        ),
        u => rest
      )

# what changed between two documents, when both are Bend documents
def Answer.change(
  path: String,
  a: Maybe<&2, Bend.Module>,
  b: Maybe<&2, Bend.Module>
) -> Graph.Change:
  match a b:
    case Some{x} Some{y}:
      Bools.Bool.when(
        Graph.Change,
        Views.View.is_bend(path),
        u => Bend.Bend.changed(x, y),
        u => Graph.Content{}
      )
    case _ _:
      Graph.Content{}

# the text of a selection
def Answer.selection(s: Graph.Selection) -> String:
  match s:
    case Graph.Whole{}:
      "the whole resource"
    case Graph.Items{ks}:
      String.join(ks, ", ")

# the text of a change
def Answer.changed(c: Graph.Change) -> String:
  match c:
    case Graph.Content{}:
      "its content"
    case Graph.Keys{ks}:
      String.join(ks, ", ")

# the lines of the edges a change affects
def Answer.affected(es: List<&2, Graph.Edge>) -> List<&2, String>:
  match es:
    case Nil{}:
      Nil{}
    case Con{Graph.Edge{f, t, v, s, c}, r}:
      String.concat(
        ["  affects ", Resources.Name.show(f), ", which uses ", Answer.selection(s)]
      )
        <> Answer.affected(r)

# the seen heads of a marker
def Answer.seen(s: Lines.Seen) -> Tables.Table<List<&2, Octets.Bytes()>>:
  match s:
    case Lines.Seen{a, ln, hs}:
      hs

# the lines of each changed resource of ns, and what each change affects
def Answer.news(
  ns: List<&2, Resources.Name>,
  +d: Spec.Daemon,
  +l: Lines.Line,
  +seen: Tables.Table<List<&2, Octets.Bytes()>>,
  +es: List<&2, Graph.Edge>
) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, t}:
      +p = Resources.Name.path(n)
      +c = Answer.change(
        p,
        Answer.module(Answer.head(d, Lines.Heads.at(seen, p))),
        Answer.module(Answer.head(d, Lines.Line.heads(l, n)))
      )
      List.append(
        &2,
        String,
        String.concat(
          ["changed ", Resources.Name.show(n), ": ", Answer.changed(c)]
        )
          <> Answer.affected(Views.View.affected(es, n, c)),
        Answer.news(t, d, l, seen, es)
      )

# what is new on the line found for the agent a, and the record that
# catches the agent's marker up
def Answer.affects(
  +d: Spec.Daemon,
  +a: String,
  m: Maybe<&2, Lines.Line>,
  t: String
) -> Spec.Handled:
  match m:
    case None{}:
      Show.no(String.append("no such line: ", t))
    case Some{+l}:
      +k = Lines.Line.id(l)
      +s = Spec.Daemon.seen(d, a, k)
      +ns = Lines.Seen.unseen(s, l)
      es = Answer.edges(Answer.paths(l), d, l)
      ls = Bools.Bool.when(
        List<&2, String>,
        List.is_empty(&2, Resources.Name, ns),
        u => [String.append("nothing new on ", k)],
        u => Answer.news(ns, d, l, Answer.seen(s), es)
      )
      Spec.Handled{[Journal.Saw{a, k}], Spec.Said{True{}, ls}, "", []}

# the text of a class
def Answer.class(c: Impact.Class) -> String:
  match c:
    case Impact.ProofOnly{}:
      "proof only"
    case Impact.LawStatement{}:
      "law statement"
    case Impact.Covered{}:
      "covered"
    case Impact.Uncovered{}:
      "uncovered"
    case Impact.Added{}:
      "added"
    case Impact.Removed{}:
      "removed"

# One line of an impact's changeset, with the spot it names (if a key).
type Found is Data:
  Found{text: String, spot: Maybe<&2, Impact.Spot>}

# the found lines of the classified keys of the resource n at path
def Answer.classes(
  cs: List<&2, Impact.Classified>,
  +path: String,
  +n: Resources.Name
) -> List<&2, Found>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Impact.Classified{+k, c}, t}:
      Found{
        String.concat(["  ", path, " ", k, ": ", Answer.class(c)]),
        Some{Impact.Spot{n, k}}
      }
        <> Answer.classes(t, path, n)

# the texts of found lines
def Found.texts(fs: List<&2, Found>) -> List<&2, String>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Found{x, s}, t}:
      x <> Found.texts(t)

# the spots of found lines
def Found.spots(fs: List<&2, Found>) -> List<&2, Impact.Spot>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{Found{x, None{}}, t}:
      Found.spots(t)
    case Con{Found{x, Some{sp}}, t}:
      sp <> Found.spots(t)

# an empty document
def Answer.empty() -> Bend.Module:
  Bend.Module{[]}

# Answer.changes for one path p before rest: unchanged, a non-Bend change,
# or the classes of a Bend change
def Answer.changes.at(
  same: Bool,
  bend: Bool,
  +d: Spec.Daemon,
  +n: Resources.Name,
  p: String,
  at: Lines.Line,
  base: Lines.Line,
  rest: List<&2, Found>
) -> List<&2, Found>:
  match same bend:
    case True{} b:
      rest
    case False{} False{}:
      Found{String.concat(["  ", p, ": its content (no items)"]), None{}} <> rest
    case False{} True{}:
      old = Maybe.default(
        &2,
        Bend.Module,
        Answer.module(Answer.head(d, Lines.Line.heads(base, n))),
        Answer.empty()
      )
      new = Maybe.default(
        &2,
        Bend.Module,
        Answer.module(Answer.head(d, Lines.Line.heads(at, n))),
        Answer.empty()
      )
      List.append(&2, Found, Answer.classes(Impact.Impact.classes(n, old, new), p, n), rest)

# the found lines of the changed paths ps
def Answer.changes(
  ps: List<&2, String>,
  +d: Spec.Daemon,
  +sp: String,
  +at: Lines.Line,
  +base: Lines.Line
) -> List<&2, Found>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      +n = {Resources.Name{sp, p}: Resources.Name}
      same = History.Ids.is_eq(Lines.Line.heads(at, n), Lines.Line.heads(base, n))
      Answer.changes.at(
        same,
        Views.View.is_bend(p),
        d,
        n,
        p,
        at,
        base,
        Answer.changes(t, d, sp, at, base)
      )

# the Bend documents of the paths ps of the line l
def Answer.docs(ps: List<&2, String>, +d: Spec.Daemon, +l: Lines.Line) -> List<&2, Impact.Doc>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      +n = {Resources.Name{Answer.space(l), p}: Resources.Name}
      +rest = Answer.docs(t, d, l)
      Bools.Bool.when(
        List<&2, Impact.Doc>,
        Views.View.is_bend(p),
        u => Maybe.default(
          &2,
          List<&2, Impact.Doc>,
          Maybe.map(
            &2,
            Bend.Module,
            List<&2, Impact.Doc>,
            m => Impact.Doc{n, m} <> rest,
            Answer.module(Answer.head(d, Lines.Line.heads(l, n)))
          ),
          rest
        ),
        u => rest
      )

# the lines of d
def Answer.all_lines(ks: List<&2, String>, +d: Spec.Daemon) -> List<&2, Lines.Line>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, t}:
      List.append(
        &2,
        Lines.Line,
        Maybe.default(
          &2,
          List<&2, Lines.Line>,
          Maybe.map(&2, Lines.Line, List<&2, Lines.Line>, l => [l], Spec.Daemon.line_at(d, k)),
          []
        ),
        Answer.all_lines(t, d)
      )

# the names of spots
def Answer.spots(ss: List<&2, Impact.Spot>) -> String:
  match ss:
    case Nil{}:
      ""
    case Con{Impact.Spot{n, k}, t}:
      String.concat([" ", Resources.Name.path(n), ":", k, Answer.spots(t)])

# the names of resources
def Answer.names(ns: List<&2, Resources.Name>) -> String:
  match ns:
    case Nil{}:
      ""
    case Con{n, t}:
      String.concat([" ", Resources.Name.show(n), Answer.names(t)])

# the lines of the layers of a radius
def Answer.layers(l: Impact.Layers) -> List<&2, String>:
  match l:
    case Impact.Layers{st, pr, co, rs, ls, vs}:
      [
        String.append("statements:", Answer.spots(st)),
        String.append("proofs:", Answer.spots(pr)),
        String.append("code:", Answer.spots(co)),
        String.append("resources:", Answer.names(rs)),
        String.append("lines: ", String.join(ls, " "))
      ]

# the line an origin started as
def Answer.origin_at(o: Spec.Origin) -> Lines.Line:
  match o:
    case Spec.Origin{f, m, at}:
      at

# the impact of the source found: its changeset since its line's fork
# (all of it for a root line), classified, then its radius
def Answer.impact(+d: Spec.Daemon, m: Maybe<&2, Source>, t: String) -> Spec.Handled:
  match m:
    case None{}:
      Show.no(String.append("no such line or mark: ", t))
    case Some{Source{+k, mk, +at}}:
      +sp = Answer.space(at)
      base = Maybe.default(
        &2,
        Lines.Line,
        Maybe.map(&2, Spec.Origin, Lines.Line, o => Answer.origin_at(o), Spec.Daemon.origin(d, k)),
        Lines.Line.new(sp, "")
      )
      +fs = Answer.changes(Answer.paths(at), d, sp, at, base)
      docs = Answer.docs(Answer.paths(at), d, at)
      lay = Impact.Impact.layers(
        docs,
        Answer.all_lines(Tables.Table.keys(Lines.Line, Ref.lines(d)), d),
        Found.spots(fs)
      )
      Show.yes(
        List.append(
          &2,
          String,
          String.append("changes since the fork of ", k) <> Found.texts(fs),
          Answer.layers(lay)
        )
      )

# a new line named nm, forked from the source found
def Answer.fork(d: Spec.Daemon, m: Maybe<&2, Source>, nm: String, f: String) -> Spec.Handled:
  match m:
    case None{}:
      Show.no(String.append("no such line or mark: ", f))
    case Some{Source{k, mk, at}}:
      +nk = Lines.Line.key(Answer.space(at), nm)
      Bools.Bool.when(
        Spec.Handled,
        Maybe.is_some(&2, Lines.Line, Spec.Daemon.line_at(d, nk)),
        u => Show.no(String.append("the line exists: ", nk)),
        u => Spec.Handled{
          [Journal.Forked{nk, k, mk}],
          Spec.Said{True{}, [String.concat(["line ", nk, " from ", f])]},
          "",
          []
        }
      )

# a new version of n with the content b after the heads hs of the line l,
# by the agent a
def Answer.kept(
  a: String,
  +n: Resources.Name,
  ln: String,
  +l: Lines.Line,
  hs: List<&2, Octets.Bytes()>,
  +b: Octets.Bytes()
) -> Spec.Handled:
  +v = {
    History.Node{
      n,
      hs,
      History.Has{Store.Tree.root(Core.Core.items(b))},
      None{},
      History.Agent{a}
    }: History.Node
  }
  Spec.Handled{
    [Journal.Kept{ln, Some{b}, v}],
    Spec.Said{
      True{},
      [String.concat(["wrote ", Show.id(History.Node.id(v)), " on ", Lines.Line.id(l)])]
    },
    Lines.Line.id(l),
    [Spec.Carry{Resources.Name.path(n), b}]
  }

# a write of b to n after the ids found, on the line l
def Answer.write.ids(
  m: Maybe<&2, List<&2, Octets.Bytes()>>,
  a: String,
  +n: Resources.Name,
  ln: String,
  +l: Lines.Line,
  b: Octets.Bytes()
) -> Spec.Handled:
  match m:
    case None{}:
      Show.no("an expected version names no version of the resource, or several")
    case Some{e}:
      +hs = Lines.Line.heads(l, n)
      Bools.Bool.when(
        Spec.Handled,
        History.Ids.is_eq(e, hs),
        u => Answer.kept(a, n, ln, l, hs, b),
        u => Show.no(
          String.concat(
            ["refused: ", Lines.Line.id(l), " follows ", Show.ids(hs), " for ", Resources.Name.show(n)]
          )
        )
      )

# a write of b to n on the line named ln, after the versions ps
def Answer.write(
  +d: Spec.Daemon,
  a: String,
  +n: Resources.Name,
  +ln: String,
  ps: List<&2, String>,
  b: Octets.Bytes()
) -> Spec.Handled:
  Answer.write.ids(
    Spec.Daemon.ids(d, n, ps),
    a,
    n,
    ln,
    Spec.Daemon.line_in(d, Resources.Name.space(n), ln),
    b
  )

# a restore of the content found as a new version of n on the line named ln
def Answer.restore.of(
  d: Spec.Daemon,
  c: Maybe<&2, Maybe<&2, Octets.Bytes()>>,
  a: String,
  +n: Resources.Name,
  +ln: String
) -> Spec.Handled:
  match c:
    case Some{Some{b}}:
      +l = Spec.Daemon.line_in(d, Resources.Name.space(n), ln)
      Answer.kept(a, n, ln, l, Lines.Line.heads(l, n), b)
    case Some{None{}}:
      Show.no("that version says the resource is gone; there is no content to restore")
    case None{}:
      Show.no("no such version")

# a mark named nm of the line found
def Answer.mark(
  d: Spec.Daemon,
  m: Maybe<&2, Lines.Line>,
  a: String,
  +nm: String,
  msg: String,
  t: String
) -> Spec.Handled:
  match m:
    case None{}:
      Show.no(String.append("no such line: ", t))
    case Some{l}:
      +k = Lines.Line.id(l)
      Bools.Bool.when(
        Spec.Handled,
        Maybe.is_some(&2, Lines.Mark, Spec.Daemon.mark(d, k, nm)),
        u => Show.no(String.concat(["the mark exists: ", k, "@", nm])),
        u => Spec.Handled{
          [Journal.Marked{k, nm, msg, History.Agent{a}}],
          Spec.Said{True{}, [String.concat(["marked ", k, "@", nm])]},
          "",
          []
        }
      )

# Merges
# ------
# A merge takes every resource the source follows into the target line, by
# the view of each: a resource the target does not follow yet takes the
# source's version; one whose source head is already in the target's
# history is left; any other gets a merge node with both heads as parents
# and the three-way merge of the contents from their nearest common
# ancestor. It is every resource or none: one clash and nothing moves, so a
# line never holds half of a merge (whose resources may need each other),
# and after the clash is resolved the same merge can run again.

# The merge of one resource. Same: nothing to do. Take: keep the node, new
# (fresh) or the source's own, with the content to carry to working
# copies. Clash: why it cannot merge.
type Merged is Data:
  Same{}
  Take{node: History.Node, content: Maybe<&2, Octets.Bytes()>, fresh: Bool}
  Clash{why: String}

# the merge of the resource at path, with its outcome
type At is Data:
  At{path: String, merged: Merged}

# two contents are the same
def Answer.same(a: Maybe<&2, Octets.Bytes()>, b: Maybe<&2, Octets.Bytes()>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Octets.Bytes.is_eq(x, y)
    case _ _:
      False{}

# the merge of three present contents, by the view of path
def Answer.three.view(
  path: String,
  b: Maybe<&2, Octets.Bytes()>,
  x: Maybe<&2, Octets.Bytes()>,
  y: Maybe<&2, Octets.Bytes()>
) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  match b x y:
    case Some{bb} Some{xx} Some{yy}:
      Maybe.map(
        &2,
        Octets.Bytes(),
        Maybe<&2, Octets.Bytes()>,
        r => Some{r},
        Views.View.merge(path, bb, xx, yy)
      )
    case _ _ _:
      None{}

# the three-way merge of the target content x and the source content y
# from their base b; None for a clash
def Answer.three(
  path: String,
  +b: Maybe<&2, Octets.Bytes()>,
  +x: Maybe<&2, Octets.Bytes()>,
  +y: Maybe<&2, Octets.Bytes()>
) -> Maybe<&2, Maybe<&2, Octets.Bytes()>>:
  Bools.Bool.when(
    Maybe<&2, Maybe<&2, Octets.Bytes()>>,
    Answer.same(y, b),
    u => Some{x},
    u => Bools.Bool.when(
      Maybe<&2, Maybe<&2, Octets.Bytes()>>,
      Answer.same(x, b),
      v => Some{y},
      v => Bools.Bool.when(
        Maybe<&2, Maybe<&2, Octets.Bytes()>>,
        Answer.same(x, y),
        w => Some{x},
        w => Answer.three.view(path, b, x, y)
      )
    )
  )

# a content, or none when the version is missing
def Answer.flat(c: Maybe<&2, Maybe<&2, Octets.Bytes()>>) -> Maybe<&2, Octets.Bytes()>:
  match c:
    case None{}:
      None{}
    case Some{x}:
      x

# the content of the base found, if any
def Answer.base(d: Spec.Daemon, m: Maybe<&2, Octets.Bytes()>) -> Maybe<&2, Octets.Bytes()>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Answer.flat(Content.at(d, x))

# what a version holds, given its content
def Answer.holds(c: Maybe<&2, Octets.Bytes()>) -> History.Body:
  match c:
    case None{}:
      History.Gone{}
    case Some{b}:
      History.Has{Store.Tree.root(Core.Core.items(b))}

# the merge node of n after the target head t and the source head s, with
# the merged content found
def Answer.merge.node(
  r: Maybe<&2, Maybe<&2, Octets.Bytes()>>,
  a: String,
  n: Resources.Name,
  t: Octets.Bytes(),
  s: Octets.Bytes()
) -> Merged:
  match r:
    case None{}:
      Clash{
        String.concat([Resources.Name.show(n), ": both sides changed it, and their changes clash"])
      }
    case Some{+c}:
      Take{History.Node{n, [t, s], Answer.holds(c), None{}, History.Agent{a}}, c, True{}}

# the base m is the source head s: the target already has the source
def Answer.has(m: Maybe<&2, Octets.Bytes()>, s: Octets.Bytes()) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Octets.Bytes.is_eq(x, s)

# the merge of n from the source head s into the target head t
def Answer.merge.two(
  +d: Spec.Daemon,
  a: String,
  +n: Resources.Name,
  +s: Octets.Bytes(),
  +t: Octets.Bytes()
) -> Merged:
  h = Ref.history(d)
  +m = Dag.base(h, t, s)
  Bools.Bool.when(
    Merged,
    Answer.has(m, s),
    u => Same{},
    u => Answer.merge.node(
      Answer.three(
        Resources.Name.path(n),
        Answer.base(d, m),
        Answer.flat(Content.at(d, t)),
        Answer.flat(Content.at(d, s))
      ),
      a,
      n,
      t,
      s
    )
  )

# the node of the source for n, for a target that follows nothing of n yet
def Answer.merge.own(
  d: Spec.Daemon,
  m: Maybe<&2, History.Node>,
  s: Octets.Bytes(),
  n: Resources.Name
) -> Merged:
  match m:
    case None{}:
      Clash{String.append("a version is missing from the history: ", Resources.Name.show(n))}
    case Some{v}:
      Take{v, Answer.flat(Content.at(d, s)), False{}}

# the merge of n from the source heads fs into the target heads ts
def Answer.merge.one(
  +d: Spec.Daemon,
  a: String,
  n: Resources.Name,
  fs: List<&2, Octets.Bytes()>,
  ts: List<&2, Octets.Bytes()>
) -> Merged:
  match fs ts:
    case Nil{} _:
      Same{}
    case Con{+s, Nil{}} Nil{}:
      Answer.merge.own(d, History.History.get(Ref.history(d), s), s, n)
    case Con{+s, Nil{}} Con{+t, Nil{}}:
      Bools.Bool.when(
        Merged,
        Octets.Bytes.is_eq(s, t),
        u => Same{},
        u => Answer.merge.two(d, a, n, s, t)
      )
    case _ _:
      Clash{String.append("several heads: ", Resources.Name.show(n))}

# the merge of every path of ps from the line src into the line tgt
def Answer.merge.paths(
  ps: List<&2, String>,
  +d: Spec.Daemon,
  +a: String,
  +sp: String,
  +src: Lines.Line,
  +tgt: Lines.Line
) -> List<&2, At>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      +n = {Resources.Name{sp, p}: Resources.Name}
      At{
        p,
        Answer.merge.one(d, a, n, Lines.Line.heads(src, n), Lines.Line.heads(tgt, n))
      }
        <> Answer.merge.paths(t, d, a, sp, src, tgt)

# the clashes among the outcomes
def Answer.clashes(xs: List<&2, At>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{At{p, Clash{w}}, t}:
      w <> Answer.clashes(t)
    case Con{x, t}:
      Answer.clashes(t)

# the records of the outcomes, on the line named ln: a fresh node keeps its
# content; the source node of the source keeps none, as the store has it
def Answer.taken(xs: List<&2, At>, +ln: String) -> List<&2, Journal.Record>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{At{p, Take{v, c, True{}}}, t}:
      Journal.Kept{ln, c, v} <> Answer.taken(t, ln)
    case Con{At{p, Take{v, c, False{}}}, t}:
      Journal.Kept{ln, None{}, v} <> Answer.taken(t, ln)
    case Con{x, t}:
      Answer.taken(t, ln)

# the content to carry of the outcomes
def Answer.carried(xs: List<&2, At>) -> List<&2, Spec.Carry>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{At{p, Take{v, Some{b}, f}}, t}:
      Spec.Carry{p, b} <> Answer.carried(t)
    case Con{x, t}:
      Answer.carried(t)

# the lines of the outcomes
def Answer.merged(xs: List<&2, At>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{At{p, Take{v, c, f}}, t}:
      String.append("merged ", p) <> Answer.merged(t)
    case Con{x, t}:
      Answer.merged(t)

# the result of the outcomes of a merge into the line l: every resource,
# or none when one clashes
def Answer.merge.done(+xs: List<&2, At>, +l: Lines.Line) -> Spec.Handled:
  +cs = Answer.clashes(xs)
  +ms = Answer.merged(xs)
  Bools.Bool.when(
    Spec.Handled,
    List.is_empty(&2, String, cs),
    u => Spec.Handled{
      Answer.taken(xs, Lines.Line.name(l)),
      Spec.Said{
        True{},
        Bools.Bool.when(
          List<&2, String>,
          List.is_empty(&2, String, ms),
          v => ["nothing to merge"],
          v => ms
        )
      },
      Lines.Line.id(l),
      Answer.carried(xs)
    },
    u => Spec.Handled{[], Spec.Said{False{}, "nothing merged:" <> cs}, "", []}
  )

# the merge of the source found into the line found
def Answer.merge(
  d: Spec.Daemon,
  a: String,
  ms: Maybe<&2, Source>,
  mt: Maybe<&2, Lines.Line>,
  f: String,
  t: String
) -> Spec.Handled:
  match ms mt:
    case Some{Source{k, mk, +at}} Some{+l}:
      +sp = Answer.space(at)
      Bools.Bool.when(
        Spec.Handled,
        String.eq(sp, Answer.space(l)),
        u => Answer.merge.done(Answer.merge.paths(Answer.paths(at), d, a, sp, at, l), l),
        u => Show.no("the lines are of different spaces")
      )
    case _ _:
      Show.no(String.concat(["no such line or mark: ", f, " or ", t]))

# the carry of the content found for the file at path; none when it is
# gone, missing, or not one version
def Answer.file(m: Maybe<&2, Maybe<&2, Octets.Bytes()>>, path: String) -> List<&2, Spec.Carry>:
  match m:
    case Some{Some{b}}:
      [Spec.Carry{path, b}]
    case _:
      []

# the carry of each path of ps that the line l (of the space sp) follows
# with one version that has content
def Answer.files.go(
  ps: List<&2, String>,
  +d: Spec.Daemon,
  +l: Lines.Line,
  +sp: String
) -> List<&2, Spec.Carry>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      x = Ref.one(Lines.Line.heads(l, Resources.Name{sp, p}))
      List.append(
        &2,
        Spec.Carry,
        Answer.file(Answer.content(d, x), p),
        Answer.files.go(t, d, l, sp)
      )

# the files of the line l as it is now: each resource with one version
# that has content, with that content
def Answer.files(d: Spec.Daemon, +l: Lines.Line) -> List<&2, Spec.Carry>:
  Answer.files.go(Answer.paths(l), d, l, Answer.space(l))

# the Bend documents of the carries of the space sp
def Open.docs(cs: List<&2, Spec.Carry>, +sp: String) -> List<&2, Bend.Doc>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Spec.Carry{+p, b}, t}:
      List.append(&2, Bend.Doc, Views.View.doc(Resources.Name{sp, p}, p, b), Open.docs(t, sp))

# the line of an obligation of the resource at path
def Open.line(path: String, o: Vs.Obligation) -> String:
  match o:
    case Vs.Obligation{k, i, t}:
      String.concat([path, ": ", k, " ", i, ": ", t])

# the lines of the obligations os of the resource at path
def Open.lines.of(+path: String, os: List<&2, Vs.Obligation>) -> List<&2, String>:
  match os:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      Open.line(path, o) <> Open.lines.of(path, t)

# the lines of the open obligations of each carry, by its view, given ds,
# the line's Bend documents
def Open.lines(cs: List<&2, Spec.Carry>, +ds: List<&2, Bend.Doc>, +sp: String) -> List<&2, String>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{Spec.Carry{+p, b}, t}:
      List.append(
        &2,
        String,
        Open.lines.of(p, Views.View.obligations(ds, Resources.Name{sp, p}, p, b)),
        Open.lines(t, ds, sp)
      )

# the open obligations of the line found for the text t, grouped by
# resource
def Answer.open(d: Spec.Daemon, ml: Maybe<&2, Lines.Line>, t: String) -> Spec.Handled:
  match ml:
    case None{}:
      Show.no(String.append("no line named ", t))
    case Some{+l}:
      +sp = Answer.space(l)
      +cs = Answer.files(d, l)
      +ls = Open.lines(cs, Open.docs(cs, sp), sp)
      Show.yes(
        Bools.Bool.when(
          List<&2, String>,
          List.is_empty(&2, String, ls),
          u => [String.append("no open obligations on ", t)],
          u => ls
        )
      )

# the result of the command c of the agent a with the data b
def Answer.go(+d: Spec.Daemon, a: String, c: Spec.Command, b: Octets.Bytes()) -> Spec.Handled:
  match c:
    case Spec.LinesOf{}:
      Show.yes(Answer.lines(Tables.Table.keys(Lines.Line, Ref.lines(d)), d))
    case Spec.LogOf{n, ml, ma}:
      Answer.log(d, n, ml, ma)
    case Spec.ShowOf{n, mv}:
      Answer.show(d, n, mv)
    case Spec.DiffOf{n, x, y}:
      Answer.diff(d, n, x, y)
    case Spec.AffectsOf{+t}:
      Answer.affects(d, a, Spec.Daemon.line_ref(d, t), t)
    case Spec.ImpactOf{+t}:
      Answer.impact(d, Ref.source(d, t), t)
    case Spec.LineNew{nm, +f}:
      Answer.fork(d, Ref.source(d, f), nm, f)
    case Spec.WriteTo{n, ln, ps, f}:
      Answer.write(d, a, n, ln, ps, b)
    case Spec.RestoreTo{+n, ln, v}:
      Answer.restore.of(d, Answer.content(d, Ref.version(d, n, v)), a, n, ln)
    case Spec.MarkMade{+t, nm, msg}:
      Answer.mark(d, Spec.Daemon.line_ref(d, t), a, nm, msg, t)
    case Spec.MergeOf{+f, +t}:
      Answer.merge(d, a, Ref.source(d, f), Spec.Daemon.line_ref(d, t), f, t)
    case Spec.CheckoutOf{t}:
      Show.no("a checkout is made by the daemon's loop, not as a command")
    case Spec.ReleaseOf{t}:
      Show.no("a release is made by the daemon's loop, not as a command")
    case Spec.OpenOf{+t}:
      Answer.open(d, Spec.Daemon.line_ref(d, t), t)
    case Spec.VerifyOf{t}:
      Show.no("a verification is made by the daemon's loop, not as a command")

def Spec.Daemon.handle(d, a, c, b):
  Answer.go(d, a, c, b)

def Spec.affects_sees(d, a, t, b, l, h):
  +d = d
  +a = a
  +t = t
  +l = l
  %Equal.sym(Maybe<&2, Lines.Line>, Bools.Bool.when(Maybe<&2, Lines.Line>, Cuts.Text.has(t, 58), u => Spec.Daemon.line_at(d, t), u => Ref.line_of(d, Ref.named(Tables.Table.keys(Lines.Line, Ref.lines(d)), t))), Some{l}, h) :
    {Spec.Handled.records(Answer.affects(d, a, _, t)) == [Journal.Saw{a, Lines.Line.id(l)}] : List<&2, Journal.Record>}
  {==}

def Spec.apply_marked(d, k, nm, msg, a, l, h, n):
  match d:
    case Spec.Daemon{+store, +history, +lines, +mounts, +clients, +book}:
      match book:
        case Spec.Book{+seen, +marks, +origins}:
          +k = k
          +nm = nm
          +msg = msg
          +a = a
          +l = l
          %Equal.sym(Maybe<&2, Lines.Line>, Tables.Table.get(Lines.Line, lines, k), Some{l}, h) :
            {Spec.Daemon.mark(Apply.marked(Spec.Daemon{store, history, lines, mounts, clients, Spec.Book{seen, marks, origins}}, _, String.append(k, SCon{'@', String.append(nm, "")}), nm, msg, a), k, nm) == Some{Lines.Mark{Lines.Line.name(l), nm, msg, a, l}} : Maybe<&2, Lines.Mark>}
          %Equal.sym(Maybe<&2, Lines.Mark>, Tables.Table.get(Lines.Mark, marks, String.append(k, SCon{'@', String.append(nm, "")})), None{}, n) :
            {Spec.Daemon.mark(Bools.Bool.when(Spec.Daemon, Maybe.is_some(&2, Lines.Mark, _), u => Spec.Daemon{store, history, lines, mounts, clients, Spec.Book{seen, marks, origins}}, u => Spec.Daemon{store, history, lines, mounts, clients, Spec.Book{seen, Tables.Table.set(Lines.Mark, marks, String.append(k, SCon{'@', String.append(nm, "")}), Lines.Mark.of(l, nm, msg, a)), origins}}), k, nm) == Some{Lines.Mark{Lines.Line.name(l), nm, msg, a, l}} : Maybe<&2, Lines.Mark>}
          %Equal.sym(Maybe<&2, Lines.Mark>, Tables.Table.get(Lines.Mark, Tables.Table.set(Lines.Mark, marks, String.append(k, SCon{'@', String.append(nm, "")}), Lines.Mark.of(l, nm, msg, a)), String.append(k, SCon{'@', String.append(nm, "")})), Some{Lines.Mark.of(l, nm, msg, a)}, Tables.Table.get_after_set(Lines.Mark, marks, String.append(k, SCon{'@', String.append(nm, "")}), Lines.Mark.of(l, nm, msg, a))) :
            {_ == Some{Lines.Mark{Lines.Line.name(l), nm, msg, a, l}} : Maybe<&2, Lines.Mark>}
          {==}

def mount_once.g1(
  +d: Spec.Daemon,
  +tok: Octets.Bytes(),
  +u: String,
  +gs: List<&2, String>,
  +ln: String,
  +h: {Maybe.is_some(&2, Spec.Local, Spec.Daemon.local(d, u)) == True{} : Bool},
  +x: Bool,
  hx: {x == Octets.Bytes.is_eq(tok, tok) : Bool}) ->
  {Spec.Action.is_reply(Bools.Bool.when(Spec.Action, x, x => Spec.Daemon.decide.body(d, Spec.Mount{u, gs, ln}), x => Spec.Reply{Spec.Denied{"wrong token"}})) == True{} : Bool}:
  match x:
    case False{}:
      {==}
    case True{}:
      %Equal.sym(Bool, Maybe.is_some(&2, Spec.Local, Spec.Daemon.local(d, u)), True{}, h) :
        {Spec.Action.is_reply(Bools.Bool.when(Spec.Action, _, x => Spec.Reply{Spec.Denied{String.append("already mounted: ", u)}}, x => Spec.DoMount{u, gs, ln})) == True{} : Bool}
      {==}

def Spec.mount_once(d, tok, u, gs, ln, h):
  +tok = tok
  mount_once.g1(d, tok, u, gs, ln, h, Octets.Bytes.is_eq(tok, tok), {==})

def Spec.replay_con(d, r, rs):
  {==}

def Spec.replay_nil(d):
  {==}

def Spec.step_is_core(d, l, i):
  {==}

def Spec.token_checked(d, tok, r, h):
  match r:
    case Spec.Request{+token, +body}:
      %Equal.sym(Bool, Octets.Bytes.is_eq(token, tok), False{}, h) :
        {Bools.Bool.when(Spec.Action, _, x => Spec.Daemon.decide.body(d, body), x => Spec.Reply{Spec.Denied{"wrong token"}}) == Spec.Reply{Spec.Denied{"wrong token"}} : Spec.Action}
      {==}

def Spec.write_kept(d, a, n, ln, ps, f, b, e, i, s):
  +d = d
  +a = a
  +n = n
  +ln = ln
  +b = b
  +e = e
  %Equal.sym(Maybe<&2, List<&2, Octets.Bytes()>>, Ref.all(ps, Tables.Table.keys(History.Node, Ref.nodes(d)), Ref.nodes(d), n), Some{e}, i) :
    {Spec.Handled.records(Answer.write.ids(_, a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), b)) == [Journal.Kept{ln, Some{b}, History.Node{n, Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n), History.Has{Store.Tree.up(64n, Store.Node.refs(Store.Tree.leaves.of(Store.Chunk.split.go(List<&2, U32>, Store.Bytes.id, Core.Core.items(b), 0, [], 0n, 0n))))}, None{}, History.Agent{a}}}] : List<&2, Journal.Record>}
  %Equal.sym(Bool, History.Ids.is_eq(e, Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), True{}, s) :
    {Spec.Handled.records(Bools.Bool.when(Spec.Handled, _, u => Answer.kept(a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n), b), u => Show.no(String.concat(["refused: ", Lines.Line.id(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}})), " follows ", Show.ids(Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), " for ", Resources.Name.show(n)])))) == [Journal.Kept{ln, Some{b}, History.Node{n, Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n), History.Has{Store.Tree.up(64n, Store.Node.refs(Store.Tree.leaves.of(Store.Chunk.split.go(List<&2, U32>, Store.Bytes.id, Core.Core.items(b), 0, [], 0n, 0n))))}, None{}, History.Agent{a}}}] : List<&2, Journal.Record>}
  {==}

def Spec.write_stale(d, a, n, ln, ps, f, b, e, i, s):
  +d = d
  +a = a
  +n = n
  +ln = ln
  +ps = ps
  +b = b
  +e = e
  +i = i
  +s = s
  Tuple{(%Equal.sym(Maybe<&2, List<&2, Octets.Bytes()>>, Ref.all(ps, Tables.Table.keys(History.Node, Ref.nodes(d)), Ref.nodes(d), n), Some{e}, i) : {Spec.Handled.records(Answer.write.ids(_, a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), b)) == [] : List<&2, Journal.Record>}; (%Equal.sym(Bool, History.Ids.is_eq(e, Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), False{}, s) : {Spec.Handled.records(Bools.Bool.when(Spec.Handled, _, u => Answer.kept(a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n), b), u => Show.no(String.concat(["refused: ", Lines.Line.id(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}})), " follows ", Show.ids(Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), " for ", Resources.Name.show(n)])))) == [] : List<&2, Journal.Record>}; {==})), (%Equal.sym(Maybe<&2, List<&2, Octets.Bytes()>>, Ref.all(ps, Tables.Table.keys(History.Node, Ref.nodes(d)), Ref.nodes(d), n), Some{e}, i) : {Spec.Handled.ok(Answer.write.ids(_, a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), b)) == False{} : Bool}; (%Equal.sym(Bool, History.Ids.is_eq(e, Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), False{}, s) : {Spec.Handled.ok(Bools.Bool.when(Spec.Handled, _, u => Answer.kept(a, n, ln, Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n), b), u => Show.no(String.concat(["refused: ", Lines.Line.id(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}})), " follows ", Show.ids(Lines.Line.heads(Maybe.default(&2, Lines.Line, Spec.Daemon.line_at(d, String.append(Resources.Name.space(n), SCon{':', String.append(ln, "")})), Lines.Line{Resources.Name.space(n), ln, Tables.TNil{}}), n)), " for ", Resources.Name.show(n)])))) == False{} : Bool}; {==}))}

def Spec.apply_forked(d, k, f, l, h, n):
  match d:
    case Spec.Daemon{store, history, lines, mounts, clients, book}:
      match book:
        case Spec.Book{seen, marks, origins}:
          +k = k
          %Equal.sym(Maybe<&2, Lines.Line>, Tables.Table.get(Lines.Line, lines, f), Some{l}, h) :
            {Spec.Daemon.line_at(Apply.forked(Spec.Daemon{store, history, lines, mounts, clients, Spec.Book{seen, marks, origins}}, _, k, f, None{}), k) == Some{Lines.Line.fork(l, Spec.Key.after(Cuts.Text.cut(k, 58), k))} : Maybe<&2, Lines.Line>}
          %Equal.sym(Maybe<&2, Lines.Line>, Tables.Table.get(Lines.Line, lines, k), None{}, n) :
            {Spec.Daemon.line_at(Bools.Bool.when(Spec.Daemon, Maybe.is_some(&2, Lines.Line, _), u => Spec.Daemon{store, history, lines, mounts, clients, Spec.Book{seen, marks, origins}}, u => Spec.Daemon{store, history, Tables.Table.set(Lines.Line, lines, k, Lines.Line.fork(l, Spec.Key.name(k))), mounts, clients, Spec.Book{seen, marks, Tables.Table.set(Spec.Origin, origins, k, Spec.Origin{f, None{}, Lines.Line.fork(l, Spec.Key.name(k))})}}), k) == Some{Lines.Line.fork(l, Spec.Key.after(Cuts.Text.cut(k, 58), k))} : Maybe<&2, Lines.Line>}
          %Equal.sym(Maybe<&2, Lines.Line>, Tables.Table.get(Lines.Line, Tables.Table.set(Lines.Line, lines, k, Lines.Line.fork(l, Spec.Key.name(k))), k), Some{Lines.Line.fork(l, Spec.Key.name(k))}, Tables.Table.get_after_set(Lines.Line, lines, k, Lines.Line.fork(l, Spec.Key.name(k)))) :
            {_ == Some{Lines.Line.fork(l, Spec.Key.after(Cuts.Text.cut(k, 58), k))} : Maybe<&2, Lines.Line>}
          {==}

# Checkouts
# ---------

# the mounts of ms that the user made of the space sp
def Plan.bases(ms: List<&2, Spec.Local>, +sp: String) -> List<&2, Spec.Local>:
  match ms:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      +rest = Plan.bases(t, sp)
      Bools.Bool.when(
        List<&2, Spec.Local>,
        List.all.if(
          u => Maybe.is_none(&2, String, Spec.Author.agent(Spec.Local.author(l))),
          String.eq(Spec.Local.space(l), sp)
        ),
        u => l <> rest,
        u => rest
      )

# l, unless best comes before it in String order of their URIs
def Plan.better(+l: Spec.Local, best: Maybe<&2, Spec.Local>) -> Maybe<&2, Spec.Local>:
  match best:
    case None{}:
      Some{l}
    case Some{+b}:
      Bools.Bool.when(
        Maybe<&2, Spec.Local>,
        String.is_lt(Spec.Local.uri(b), Spec.Local.uri(l)),
        u => Some{b},
        u => Some{l}
      )

# the mount of ms whose URI comes first in String order, or best when it
# comes before all of them
def Plan.first(ms: List<&2, Spec.Local>, best: Maybe<&2, Spec.Local>) -> Maybe<&2, Spec.Local>:
  match ms:
    case Nil{}:
      best
    case Con{l, t}:
      Plan.first(t, Plan.better(l, best))

# the plan for the base m, or why there is none
def Plan.based(
  m: Maybe<&2, Spec.Local>,
  a: String,
  nm: String,
  sp: String
) -> Result<&2, &2, String, Spec.Plan>:
  match m:
    case None{}:
      Fail{
        String.concat(["no mount of the space ", sp, " on this machine: ask the user to mount it"])
      }
    case Some{b}:
      Done{Spec.Plan{b, a, nm}}

# the plan of the agent a for the line found for the text t
def Plan.of(
  d: Spec.Daemon,
  a: String,
  ml: Maybe<&2, Lines.Line>,
  t: String
) -> Result<&2, &2, String, Spec.Plan>:
  match ml:
    case None{}:
      Fail{String.append("no line named ", t)}
    case Some{Lines.Line{+sp, +nm, hs}}:
      Bools.Bool.when(
        Result<&2, &2, String, Spec.Plan>,
        Spec.Checkout.name_ok(nm),
        u => Plan.based(Plan.first(Plan.bases(Spec.Daemon.mounts(d), sp), None{}), a, nm, sp),
        u => Fail{String.append("the line's name cannot name a folder: ", nm)}
      )

def Spec.Daemon.plan(d, a, t):
  +d = d
  +a = a
  +t = t
  Bools.Bool.when(
    Result<&2, &2, String, Spec.Plan>,
    Spec.Checkout.name_ok(a),
    u => Plan.of(d, a, Spec.Daemon.line_ref(d, t), t),
    u => Fail{String.append("not a valid agent name for a checkout: ", a)}
  )
