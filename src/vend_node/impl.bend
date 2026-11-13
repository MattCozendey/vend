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

# Laws of formats and names
# -------------------------

def Spec.Request.code_names(i, r, j, s):
  Coded.Named.code_names(i, r, j, s)

def Spec.Format.items_whole(p, ws):
  Formats.Format.items_whole(p, ws)

def Spec.Format.apply_diff(p, a, b):
  Formats.Format.apply_diff(p, a, b)

def Spec.Format.merge_theirs(p, base, theirs):
  Formats.Format.merge_theirs(p, base, theirs)

def Spec.Format.merge_ours(p, base, ours):
  Formats.Format.merge_ours(p, base, ours)

def Spec.Format.merge_same(p, base, both):
  Formats.Format.merge_same(p, base, both)

# Laws of what a node holds
# -------------------------

# the facts of a node are sound for its name
def Node.ok(n: Spec.VendNode) -> {Facts.Facts.ok(Spec.VendNode.name(n), Node.facts(n)) == True{}: Bool}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      ok

def Spec.VendNode.never_lies(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Facts.Facts.ok_never(name, fs)(ok)

def Spec.VendNode.liars_are(n, v):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Facts.Facts.liars_are(fs, v)

def Spec.VendNode.liars_found(n, a, b, v, s, x, y):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Facts.Facts.liars_found(fs, a, b, v, s, x, y)

def Spec.VendNode.part_is(n, h, ws):
  match n:
    case Tuple{Nodes.Raw{name, ws2, ms, st, fs, ps}, ok}:
      Parts.Parts.part_is(ps, h, ws)

def Spec.VendNode.same_changes(n1, n2, q):
  match n1 n2:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
      h => Equal.cong(
        Facts.Facts(),
        Maybe<&2, Spec.Reply>,
        s => Answers.Answer.of(s, q),
        fs,
        fs2,
        Facts.Facts.same(fs, fs2)(h)
      )

def Spec.VendNode.reads_agree(n1, n2, c, k, p, x, y):
  match n1 n2:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
      h => hx => hy => Shared.Maybe.some_inj(
        Maybe<&2, List<&2, U32>>,
        x,
        y,
        Equal.trans(
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Some{x},
          Contents.Content.read(fs2, c, k, p),
          Some{y},
          Equal.trans(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            Some{x},
            Contents.Content.read(fs, c, k, p),
            Contents.Content.read(fs2, c, k, p),
            Equal.sym(Maybe<&2, Maybe<&2, List<&2, U32>>>, Contents.Content.read(fs, c, k, p), Some{x}, hx),
            Equal.cong(
              Facts.Facts(),
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              s => Contents.Content.read(s, c, k, p),
              fs,
              fs2,
              Facts.Facts.same(fs, fs2)(h)
            )
          ),
          hy
        )
      )

def Spec.VendNode.views_agree(n1, n2, w, b, p):
  match n1 n2:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok} Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
      h => Equal.cong(
        Facts.Facts(),
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        s => Answers.View.at(s, w, b, p),
        fs,
        fs2,
        Facts.Facts.same(fs, fs2)(h)
      )

# Laws of what a node is
# ----------------------

# a node that asks keeps its name
def Node.asks_name(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {Spec.VendNode.name(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)) == name: String}:
  match go:
    case False{}:
      {==}
    case True{}:
      {==}

# a node that works keeps its name
def Node.works_name(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool}
) -> {Spec.VendNode.name(Node.works(name, ws, ms, st, fs, ps, ok)) == name: String}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

def Spec.VendNode.name_stays(n, d):
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Ask{+i, +r}:
      Node.asks_name(
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
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.asks_name(
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
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Unmount{+a}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.works_name(name, ws, ms, st, fs, ps, ok)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      {==}

# every name of xs is in xs
def Node.within_refl(xs: List<&2, String>) -> {Shared.List.within(~String, ~String.eq, xs, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        List.contains(~String, ~String.eq, x <> r, x),
        Shared.List.within(~String, ~String.eq, r, x <> r)
      )(Lists.List.contains_head(~String, ~String.eq, ~Texts.String.laws(), x, r))(
        Lists.List.within_cons(~String, ~String.eq, r, x, r)(Node.within_refl(r))
      )

# two tests that hold both ways hold as one
def Node.same_refl.of(a: Bool) -> {a == True{}: Bool} -> {List.all.if(u => a, a) == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a list of names holds the same names as itself
def Node.same_refl(+xs: List<&2, String>) -> {Shared.List.same_set(~String, ~String.eq, xs, xs) == True{}: Bool}:
  Node.same_refl.of(Shared.List.within(~String, ~String.eq, xs, xs))(Node.within_refl(xs))

# equal lists of names hold the same names
def Node.same_of(+xs: List<&2, String>, +ys: List<&2, String>) -> {xs == ys: List<&2, String>} -> {
  Shared.List.same_set(~String, ~String.eq, xs, ys) == True{}: Bool
}:
  e =>
    %e: {Shared.List.same_set(~String, ~String.eq, xs, _) == True{}: Bool}
    Node.same_refl(xs)

# a node that asks keeps its writers
def Node.asks_writers(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {Spec.VendNode.writers(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)) == ws: List<&2, String>}:
  match go:
    case False{}:
      {==}
    case True{}:
      {==}

# a node that works keeps its writers
def Node.works_writers(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool}
) -> {Spec.VendNode.writers(Node.works(name, ws, ms, st, fs, ps, ok)) == ws: List<&2, String>}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

def Spec.VendNode.writers_are(n, d):
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      Node.same_refl(w <> Shared.List.remove(~String, ~String.eq, ws, w))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      Node.same_refl(Shared.List.remove(~String, ~String.eq, ws, w))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Ask{+i, +r}:
      Node.same_of(
        Spec.VendNode.writers(
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
        ),
        ws
      )(
        Node.asks_writers(
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
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      Node.same_refl(ws)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.same_of(
        Spec.VendNode.writers(
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
        ),
        ws
      )(
        Node.asks_writers(
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
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Unmount{+a}:
      Node.same_refl(ws)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.same_of(Spec.VendNode.writers(Node.works(name, ws, ms, st, fs, ps, ok)), ws)(
        Node.works_writers(name, ws, ms, st, fs, ps, ok)
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      Node.same_refl(ws)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      Node.same_refl(ws)

# a node that asks keeps its mounts
def Node.asks_mounts(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  Spec.VendNode.mounts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)) == Nodes.Mounts.addresses(ms): List<&2, String>
}:
  match go:
    case False{}:
      {==}
    case True{}:
      {==}

# a node that works keeps its mounts
def Node.works_mounts(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool}
) -> {
  Spec.VendNode.mounts(Node.works(name, ws, ms, st, fs, ps, ok)) == Nodes.Mounts.addresses(ms): List<&2, String>
}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

# the addresses of a kept resource before others are its address, kept, before theirs
def Node.remove_addresses.put(m: Nodes.Mounted, r: List<&2, Nodes.Mounted>, keep: Bool) -> {
  Nodes.Mounts.addresses(List.filter.put(Nodes.Mounted, m, r, keep))
    == List.filter.put(String, Nodes.Mounted.address(m), Nodes.Mounts.addresses(r), keep): List<&2, String>
}:
  match keep:
    case False{}:
      {==}
    case True{}:
      {==}

# the addresses of the resources but those at a are the addresses but a
def Node.remove_addresses(ms: List<&2, Nodes.Mounted>, +a: String) -> {
  Nodes.Mounts.addresses(Nodes.Mounts.remove(ms, a))
    == Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a): List<&2, String>
}:
  match ms:
    case Nil{}:
      {==}
    case Con{Nodes.Mounted{+x, +b, +p}, +rest}:
      Equal.trans(
        List<&2, String>,
        Nodes.Mounts.addresses(
          List.filter.put(Nodes.Mounted, Nodes.Mounted{x, b, p}, Nodes.Mounts.remove(rest, a), Bool.not(String.eq(x, a)))
        ),
        List.filter.put(String, x, Nodes.Mounts.addresses(Nodes.Mounts.remove(rest, a)), Bool.not(String.eq(x, a))),
        List.filter.put(
          String,
          x,
          Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(rest), a),
          Bool.not(String.eq(x, a))
        ),
        Node.remove_addresses.put(Nodes.Mounted{x, b, p}, Nodes.Mounts.remove(rest, a), Bool.not(String.eq(x, a))),
        Equal.cong(
          List<&2, String>,
          List<&2, String>,
          z => List.filter.put(String, x, z, Bool.not(String.eq(x, a))),
          Nodes.Mounts.addresses(Nodes.Mounts.remove(rest, a)),
          Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(rest), a),
          Node.remove_addresses(rest, a)
        )
      )

def Spec.VendNode.mounts_are(n, d):
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      Node.same_refl(Nodes.Mounts.addresses(ms))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      Node.same_refl(Nodes.Mounts.addresses(ms))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Ask{+i, +r}:
      Node.same_of(
        Spec.VendNode.mounts(
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
        ),
        Nodes.Mounts.addresses(ms)
      )(
        Node.asks_mounts(
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
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      Node.same_refl(Nodes.Mounts.addresses(ms))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.same_of(
        Spec.VendNode.mounts(
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
        ),
        a <> Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a)
      )(
        Equal.trans(
          List<&2, String>,
          Spec.VendNode.mounts(
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
          ),
          a <> Nodes.Mounts.addresses(Nodes.Mounts.remove(ms, a)),
          a <> Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a),
          Node.asks_mounts(
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
          ),
          Equal.cong(
            List<&2, String>,
            List<&2, String>,
            z => a <> z,
            Nodes.Mounts.addresses(Nodes.Mounts.remove(ms, a)),
            Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a),
            Node.remove_addresses(ms, a)
          )
        )
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Unmount{+a}:
      Node.same_of(
        Nodes.Mounts.addresses(Nodes.Mounts.remove(ms, a)),
        Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a)
      )(Node.remove_addresses(ms, a))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.same_of(Spec.VendNode.mounts(Node.works(name, ws, ms, st, fs, ps, ok)), Nodes.Mounts.addresses(ms))(
        Node.works_mounts(name, ws, ms, st, fs, ps, ok)
      )
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      Node.same_refl(Nodes.Mounts.addresses(ms))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      Node.same_refl(Nodes.Mounts.addresses(ms))

# a node that asks stops no more than it had
def Node.asks_stopped(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {Spec.VendNode.stopped(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)) == st: Bool}:
  match go:
    case False{}:
      {==}
    case True{}:
      {==}

# a node that works stops no more than it had
def Node.works_stopped(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Facts.Facts.ok(name, fs) == True{}: Bool}
) -> {Spec.VendNode.stopped(Node.works(name, ws, ms, st, fs, ps, ok)) == st: Bool}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

def Spec.VendNode.stops(n, d):
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Ask{+i, +r}:
      Node.asks_stopped(
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
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.asks_stopped(
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
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Unmount{+a}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.works_stopped(name, ws, ms, st, fs, ps, ok)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      {==}
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      {==}
