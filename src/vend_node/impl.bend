import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./live.bend as Live
import ./node.bend as Nodes
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./shared/parts.bend as Parts
import ./spec.bend as Spec
import ./types.bend as Types
import ./work.bend as Works

# A Vend Node
# -----------
# This file fills the names of spec.bend and proves its laws. A node is its
# state (Nodes.Raw) with the proof that its facts are sound for its name
# (Facts.ok), so every node, however it came to be, never names itself a
# liar. The laws are those of the core, said of the facts of the node.

def Spec.VendNode():
  Sigma<&2, &2, Nodes.Raw, r => {Nodes.Raw.ok(r) == True{}: Bool}>

def Spec.Change():
  Types.Change

def Spec.Request.code(i, r):
  Coded.Named.code(i, r)

def Spec.Change.ballot(c):
  Facts.Change.ballot(c)

def Spec.Diff():
  Formats.Diff()

def Spec.Format.items(p, ws):
  Formats.Format.items(p, ws)

def Spec.Format.imports(p, ws, bs):
  Formats.Format.imports(p, ws, bs)

def Spec.Format.diff(p, a, b):
  Formats.Format.diff(p, a, b)

def Spec.Format.apply(p, a, x):
  Formats.Format.apply(p, a, x)

def Spec.Format.merge(p, base, ours, theirs):
  Formats.Format.merge(p, base, ours, theirs)

# What a node shows
# -----------------

# the state of the node n
def Node.raw(n: Spec.VendNode) -> Nodes.Raw:
  match n:
    case Tuple{r, ok}:
      r

# the facts of the node n
def Node.facts(n: Spec.VendNode) -> Facts.Facts():
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      fs

def Spec.VendNode.name(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      name

def Spec.VendNode.writers(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      ws

def Spec.VendNode.mounts(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Nodes.Mounts.addresses(ms)

def Spec.VendNode.stopped(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      st

def Spec.VendNode.holds(n, c):
  Facts.Facts.holds(Node.facts(n), c)

def Spec.VendNode.parts(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Parts.Parts.list(ps)

def Spec.VendNode.part(n, h):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Parts.Parts.get(ps, h)

def Spec.VendNode.read(n, c, k, p):
  Contents.Content.read(Node.facts(n), c, k, p)

def Spec.VendNode.view(n, w, b, p):
  Answers.View.at(Node.facts(n), w, b, p)

def Spec.VendNode.answer(n, q):
  Answers.Answer.of(Node.facts(n), q)

def Spec.VendNode.liars(n):
  Facts.Facts.liars(Node.facts(n))

# What a node does
# ----------------

# a node of the name name, that holds nothing yet
def Node.new(+name: String) -> Spec.VendNode:
  (Nodes.Raw{name, [], [], False{}, Facts.Facts.new(), Parts.Parts.new()}, Facts.Facts.new_ok(name))

# the node after it takes in the request r of the id i, with the words m to
# keep, when it may (go): it has not stopped, and the writer is connected
def Node.asks(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  st: Bool,
  +fs: Facts.Facts(),
  ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> Spec.VendNode:
  match go:
    case False{}:
      (Nodes.Raw{name, ws, ms, st, fs, ps}, ok)
    case True{}:
      (
        Nodes.Raw{name, ws, ms, st, Facts.Facts.ask(name, fs, i, r), Nodes.Kept.with(ps, Nodes.Request.content(r))},
        Facts.Facts.take_ok(name, fs, Types.Fact.Ask{Facts.Facts.asked(fs, i, r)})(ok)
      )

# the node after a work, unless it has stopped
def Node.works(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool}
) -> Spec.VendNode:
  match st:
    case True{}:
      (Nodes.Raw{name, ws, ms, True{}, fs, ps}, ok)
    case False{}:
      (Nodes.Raw{name, ws, ms, False{}, Works.Work.does(fs, name), ps}, Live.Work.does_ok(name, fs)(ok))

def Spec.VendNode.does(n, d):
  match n d:
    case Tuple{Nodes.Raw{name, +ws, ms, st, fs, ps}, ok} Spec.Deed.Connect{+w}:
      (Nodes.Raw{name, w <> Shared.List.remove(~String, ~String.eq, ws, w), ms, st, fs, ps}, ok)
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Spec.Deed.Leave{w}:
      (Nodes.Raw{name, Shared.List.remove(~String, ~String.eq, ws, w), ms, st, fs, ps}, ok)
    case Tuple{Nodes.Raw{name, +ws, ms, +st, fs, ps}, ok} Spec.Deed.Ask{+i, r}:
      Node.asks(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        ok,
        i,
        r,
        Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
      )
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, ps}, ok} Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      +gs = Facts.Facts.list(fs2)
      (
        Nodes.Raw{name, ws, ms, st, Facts.Facts.take_all(name, gs, fs), Parts.Parts.join(ps, ps2)},
        Facts.Facts.take_all_ok(name, gs, fs)(ok)
      )
    case Tuple{Nodes.Raw{+name, ws, ms, +st, fs, ps}, ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.asks(
        name,
        ws,
        Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
        st,
        fs,
        ps,
        ok,
        Nodes.Mount.id(name, a),
        Spec.Request.Write{b, p, Some{held}},
        Bool.not(st)
      )
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Spec.Deed.Unmount{a}:
      (Nodes.Raw{name, ws, Nodes.Mounts.remove(ms, a), st, fs, ps}, ok)
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Spec.Deed.Work{}:
      Node.works(name, ws, ms, st, fs, ps, ok)
    case Tuple{Nodes.Raw{+name, ws, +ms, st, +fs, ps}, ok} Spec.Deed.Drop{}:
      (Nodes.Raw{name, ws, ms, st, fs, Parts.Parts.only(ps, Nodes.Needs.of(fs, name, ms))}, ok)
    case Tuple{Nodes.Raw{name, +ws, +ms, st, fs, ps}, ok} Spec.Deed.Stop{f}:
      (
        Nodes.Raw{
          name,
          ws,
          ms,
          Bool.or(
            st,
            Bool.or(
              f,
              Bool.and(
                List.is_empty(&2, String, ws),
                List.is_empty(&2, String, Nodes.Mounts.addresses(ms))
              )
            )
          ),
          fs,
          ps
        },
        ok
      )
