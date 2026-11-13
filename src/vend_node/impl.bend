import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ./affects.bend as Affects
import ./answers.bend as Answers
import ./codes.bend as Coded
import ./content.bend as Contents
import ./facts.bend as Facts
import ./forward.bend as Forward
import ./laws.bend as Laws
import ./lines.bend as Lines
import ./live.bend as Live
import ./mirror.bend as Mirror
import ./node.bend as Nodes
import ./owners.bend as Owners
import ./reads.bend as Reads
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./shared/parts.bend as Parts
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions
import ./work.bend as Works

# A Vend Node
# -----------
# This file fills the names of spec.bend and proves its laws. A node is its
# state (Nodes.Raw) with the proof that its facts are sound for its name
# (Facts.ok) and that its name is not reserved (Facts.Trust.reserved), so
# every node, however it came to be, never names itself a liar, and is never
# the one that another node names when its trust breaks. The laws are those
# of the core, said of the facts of the node.
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

# the facts fs of a node of the name name are sound for the name
def Node.sound(
  +name: String,
  +fs: Facts.Facts(),
  ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
) -> {Facts.Facts.ok(name, fs) == True{}: Bool}:
  Shared.Bool.and_true_left(Facts.Facts.ok(name, fs), Bool.not(Facts.Trust.reserved(name)))(ok)

# the name name of a node, whatever its facts fs, is not reserved
def Node.free(
  +name: String,
  +fs: Facts.Facts(),
  ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
) -> {Bool.not(Facts.Trust.reserved(name)) == True{}: Bool}:
  Shared.Bool.and_true_right(Facts.Facts.ok(name, fs), Bool.not(Facts.Trust.reserved(name)))(ok)

# facts fs that are sound for a name name that is not reserved can be those of
# a node of that name
def Node.join(
  +name: String,
  +fs: Facts.Facts(),
  sound: {Facts.Facts.ok(name, fs) == True{}: Bool},
  free: {Bool.not(Facts.Trust.reserved(name)) == True{}: Bool}
) -> {Nodes.Raw.sound(name, fs) == True{}: Bool}:
  Shared.Bool.and_both(Facts.Facts.ok(name, fs), Bool.not(Facts.Trust.reserved(name)))(sound)(free)

# a node of the name name keeps its proof when its facts go from fs to gs, if
# gs are sound for the name whenever fs are
def Node.resound(
  +name: String,
  +fs: Facts.Facts(),
  +gs: Facts.Facts(),
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  step: {Facts.Facts.ok(name, fs) == True{}: Bool} -> {Facts.Facts.ok(name, gs) == True{}: Bool}
) -> {Nodes.Raw.sound(name, gs) == True{}: Bool}:
  Node.join(name, gs, step(Node.sound(name, fs, ok)), Node.free(name, fs, ok))

# a node of the name name, that holds nothing yet, unless the name is
# reserved (b)
def Node.new.if(
  +name: String,
  b: Bool,
  e: {Facts.Trust.reserved(name) == b: Bool}
) -> Maybe<&2, Spec.VendNode>:
  match b e:
    case True{} e:
      None{}
    case False{} e:
      Some{
        (
          Nodes.Raw{name, [], [], False{}, Facts.Facts.new(), Parts.Parts.new()},
          Node.join(
            name,
            Facts.Facts.new(),
            Facts.Facts.new_ok(name),
            Equal.cong(Bool, Bool, Bool.not, Facts.Trust.reserved(name), False{}, e)
          )
        )
      }

# a node of the name name, that holds nothing yet; none if the name is
# reserved, as no node has such a name
def Node.new(+name: String) -> Maybe<&2, Spec.VendNode>:
  Node.new.if(name, Facts.Trust.reserved(name), {==})

# the node after it takes in the request r of the id i, with the words m to
# keep, when it may (go): it has not stopped, and the writer is connected
def Node.asks(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  st: Bool,
  +fs: Facts.Facts(),
  ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> Spec.VendNode:
  match go:
    case False{}:
      (Nodes.Raw{name, ws, ms, st, fs, ps}, ok)
    case True{}:
      (
        Nodes.Raw{
          name,
          ws,
          ms,
          st,
          Facts.Facts.ask(name, fs, i, r),
          Nodes.Kept.with(ps, Nodes.Request.content(r))
        },
        Node.resound(
          name,
          fs,
          Facts.Facts.ask(name, fs, i, r),
          ok,
          Facts.Facts.take_ok(name, fs, Types.Fact.Ask{Facts.Facts.asked(fs, i, r)})
        )
      )

# the node after a work, unless it has stopped
def Node.works(
  +name: String,
  ws: List<&2, String>,
  ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
) -> Spec.VendNode:
  match st:
    case True{}:
      (Nodes.Raw{name, ws, ms, True{}, fs, ps}, ok)
    case False{}:
      (
        Nodes.Raw{name, ws, ms, False{}, Works.Work.does(fs, name), ps},
        Node.resound(name, fs, Works.Work.does(fs, name), ok, Live.Work.does_ok(name, fs))
      )

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
    case Tuple{
      Nodes.Raw{+name, ws, ms, st, +fs, ps},
      ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
      +gs = Facts.Facts.list(fs2)
      (
        Nodes.Raw{name, ws, ms, st, Facts.Facts.take_all(name, gs, fs), Parts.Parts.join(ps, ps2)},
        Node.resound(
          name,
          fs,
          Facts.Facts.take_all(name, gs, fs),
          ok,
          Facts.Facts.take_all_ok(name, gs, fs)
        )
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
def Node.ok(
  n: Spec.VendNode
) -> {Facts.Facts.ok(Spec.VendNode.name(n), Node.facts(n)) == True{}: Bool}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}:
      Node.sound(name, fs, ok)

# the name of a node is not reserved: it is never the name under which a node
# says that its trust broke (Facts.Trust.voter), so no node is named a liar
# by the broken trust of another
def Node.name_free(
  n: Spec.VendNode
) -> {Facts.Trust.reserved(Spec.VendNode.name(n)) == False{}: Bool}:
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, fs, ps}, ok}:
      Shared.Bool.not_true(Facts.Trust.reserved(name))(Node.free(name, fs, ok))

def Spec.VendNode.never_lies(n):
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, ps}, ok}:
      Facts.Facts.ok_never(name, fs)(Node.sound(name, fs, ok))

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
    case Tuple{
      Nodes.Raw{name, ws, ms, st, fs, ps},
      ok
    } Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
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
    case Tuple{
      Nodes.Raw{name, ws, ms, st, fs, ps},
      ok
    } Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
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
            Equal.sym(
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              Contents.Content.read(fs, c, k, p),
              Some{x},
              hx
            ),
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
    case Tuple{
      Nodes.Raw{name, ws, ms, st, fs, ps},
      ok
    } Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}:
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
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
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
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
def Node.within_refl(
  xs: List<&2, String>
) -> {Shared.List.within(~String, ~String.eq, xs, xs) == True{}: Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        List.contains(~String, ~String.eq, x <> r, x),
        Shared.List.within(~String, ~String.eq, r, x <> r)
      )(
        Lists.List.contains_head(~String, ~String.eq, ~Texts.String.laws(), x, r)
      )(Lists.List.within_cons(~String, ~String.eq, r, x, r)(Node.within_refl(r)))

# two tests that hold both ways hold as one
def Node.same_refl.of(a: Bool) -> {a == True{}: Bool} -> {List.all.if(u => a, a) == True{}: Bool}:
  match a:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a list of names holds the same names as itself
def Node.same_refl(
  +xs: List<&2, String>
) -> {Shared.List.same_set(~String, ~String.eq, xs, xs) == True{}: Bool}:
  Node.same_refl.of(Shared.List.within(~String, ~String.eq, xs, xs))(Node.within_refl(xs))

# equal lists of names hold the same names
def Node.same_of(
  +xs: List<&2, String>,
  +ys: List<&2, String>
) -> {
  xs == ys: List<&2, String>
} -> {Shared.List.same_set(~String, ~String.eq, xs, ys) == True{}: Bool}:
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  Spec.VendNode.writers(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)) == ws: List<&2, String>
}:
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
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
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
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
      Node.same_of(
        Spec.VendNode.writers(Node.works(name, ws, ms, st, fs, ps, ok)),
        ws
      )(Node.works_writers(name, ws, ms, st, fs, ps, ok))
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  Spec.VendNode.mounts(
    Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go)
  )
    == Nodes.Mounts.addresses(ms): List<&2, String>
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
) -> {
  Spec.VendNode.mounts(
    Node.works(name, ws, ms, st, fs, ps, ok)
  )
    == Nodes.Mounts.addresses(ms): List<&2, String>
}:
  match st:
    case True{}:
      {==}
    case False{}:
      {==}

# the addresses of a kept resource before others are its address, kept, before theirs
def Node.remove_addresses.put(
  m: Nodes.Mounted,
  r: List<&2, Nodes.Mounted>,
  keep: Bool
) -> {
  Nodes.Mounts.addresses(
    List.filter.put(Nodes.Mounted, m, r, keep)
  )
    == List.filter.put(
      String,
      Nodes.Mounted.address(m),
      Nodes.Mounts.addresses(r),
      keep
    ): List<&2, String>
}:
  match keep:
    case False{}:
      {==}
    case True{}:
      {==}

# the addresses of the resources but those at a are the addresses but a
def Node.remove_addresses(
  ms: List<&2, Nodes.Mounted>,
  +a: String
) -> {
  Nodes.Mounts.addresses(
    Nodes.Mounts.remove(ms, a)
  )
    == Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(ms), a): List<&2, String>
}:
  match ms:
    case Nil{}:
      {==}
    case Con{Nodes.Mounted{+x, +b, +p}, +rest}:
      Equal.trans(
        List<&2, String>,
        Nodes.Mounts.addresses(
          List.filter.put(
            Nodes.Mounted,
            Nodes.Mounted{x, b, p},
            Nodes.Mounts.remove(rest, a),
            Bool.not(String.eq(x, a))
          )
        ),
        List.filter.put(
          String,
          x,
          Nodes.Mounts.addresses(Nodes.Mounts.remove(rest, a)),
          Bool.not(String.eq(x, a))
        ),
        List.filter.put(
          String,
          x,
          Shared.List.remove(~String, ~String.eq, Nodes.Mounts.addresses(rest), a),
          Bool.not(String.eq(x, a))
        ),
        Node.remove_addresses.put(
          Nodes.Mounted{x, b, p},
          Nodes.Mounts.remove(rest, a),
          Bool.not(String.eq(x, a))
        ),
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
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
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
      Node.same_of(
        Spec.VendNode.mounts(Node.works(name, ws, ms, st, fs, ps, ok)),
        Nodes.Mounts.addresses(ms)
      )(Node.works_mounts(name, ws, ms, st, fs, ps, ok))
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
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
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
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
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}:
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

# Laws of what a node does
# ------------------------

# the facts of a node that asks are wider
def Node.asks_wider(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  Facts.Facts.wider(
    fs,
    Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go))
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      Facts.Facts.wider_refl(fs)
    case True{}:
      Facts.Facts.take_wider(name, fs, Types.Fact.Ask{Facts.Facts.asked(fs, i, r)})

# the facts of a node that works are wider
def Node.works_wider(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool}
) -> {Facts.Facts.wider(fs, Node.facts(Node.works(name, ws, ms, st, fs, ps, ok))) == True{}: Bool}:
  match st:
    case True{}:
      Facts.Facts.wider_refl(fs)
    case False{}:
      Live.Work.does_wider(name, fs)

# the facts of a node are wider after any deed
def Node.does_wider(
  n: Spec.VendNode,
  d: Spec.Deed
) -> {Facts.Facts.wider(Node.facts(n), Node.facts(Spec.VendNode.does(n, d))) == True{}: Bool}:
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      Facts.Facts.wider_refl(fs)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      Facts.Facts.wider_refl(fs)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Ask{+i, +r}:
      Node.asks_wider(
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
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, +fs2, ps2}, ok2}}:
      Facts.Facts.take_all_wider(name, Facts.Facts.list(fs2), fs)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Mount{+a, +b, +p, +held}:
      Node.asks_wider(
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
      Facts.Facts.wider_refl(fs)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.works_wider(name, ws, ms, st, fs, ps, ok)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      Facts.Facts.wider_refl(fs)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      Facts.Facts.wider_refl(fs)

# a node holds after a deed each change that it held
def Node.keeps(
  +n: Spec.VendNode,
  +d: Spec.Deed,
  +c: Types.Change
) -> {
  Facts.Facts.holds(Node.facts(n), c) == True{}: Bool
} -> {Facts.Facts.holds(Node.facts(Spec.VendNode.does(n, d)), c) == True{}: Bool}:
  h => Facts.Facts.wider_holds(
    Node.facts(n),
    Node.facts(Spec.VendNode.does(n, d)),
    c
  )(Node.does_wider(n, d))(h)

def Spec.VendNode.keeps(n, d, c):
  Node.keeps(n, d, c)

def Spec.VendNode.sync_joins(n, m, c):
  match n m:
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Tuple{Nodes.Raw{name2, ws2, ms2, st2, +fs2, ps2}, ok2}:
      hn => hc => Facts.Facts.take_all_holds(name, fs2, fs, c)(hn)(hc)

# hashes that differ in the words of the parts differ in the words of the spec
def Node.distinct(hs: List<&2, Hashes.Hash>, d: Parts.Parts.Distinct(hs)) -> Spec.Distinct(hs):
  match hs d:
    case Nil{} u:
      Unit{}
    case Con{+h, +r} Tuple{e, rest}:
      (e, Node.distinct(r, rest))

# the parts ps are listed once, in the words of the spec
def Node.parts_once.of(
  +ps: Parts.Parts,
  p: Parts.Parts.Distinct(
    Parts.Parts.list(ps)
  )
    & (
      @h: Hashes.Hash -> {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          Parts.Parts.get(ps, h)
        )
          == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Parts.Parts.list(ps), h): Bool
      }
    )
) -> Spec.Distinct(
  Parts.Parts.list(ps)
)
  & (
    @h: Hashes.Hash -> {
      Maybe.is_some(
        &2,
        List<&2, U32>,
        Parts.Parts.get(ps, h)
      )
        == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, Parts.Parts.list(ps), h): Bool
    }
  ):
  match p:
    case Tuple{d, f}:
      (Node.distinct(Parts.Parts.list(ps), d), f)

def Spec.VendNode.parts_once(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      Node.parts_once.of(ps, Parts.Parts.once(ps))

# a node that has not stopped takes in what a connected writer asks
def Node.gate(
  st: Bool,
  c: Bool
) -> {st == False{}: Bool} -> {c == True{}: Bool} -> {Bool.and(Bool.not(st), c) == True{}: Bool}:
  match st:
    case True{}:
      hs => hc => Empty.absurd(
        {Bool.and(Bool.not(True{}), c) == True{}: Bool},
        Shared.Bool.true_ne_false(hs)
      )
    case False{}:
      hs => hc => hc

# a node that has not stopped may go
def Node.gate_not(st: Bool) -> {st == False{}: Bool} -> {Bool.not(st) == True{}: Bool}:
  match st:
    case True{}:
      hs => Empty.absurd({Bool.not(True{}) == True{}: Bool}, Shared.Bool.true_ne_false(hs))
    case False{}:
      hs => {==}

# what holds of the facts with a request holds of the facts of a node that
# takes it in
def Node.asks_at(
  -P: Facts.Facts() -> Type,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  go == True{}: Bool
} -> P(
  Facts.Facts.ask(name, fs, i, r)
) -> P(Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go))):
  match go:
    case False{}:
      h => p => Empty.absurd(
        P(Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, False{}))),
        Shared.Bool.false_ne_true(h)
      )
    case True{}:
      h => p => p

# what holds of the facts with a request, after a work, holds of the facts of
# a node that takes it in and works
def Node.asks_works_at(
  -P: Facts.Facts() -> Type,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: Facts.Facts(),
  +ps: Parts.Parts,
  +ok: {Nodes.Raw.sound(name, fs) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  st == False{}: Bool
} -> {
  go == True{}: Bool
} -> P(
  Works.Work.does(Facts.Facts.ask(name, fs, i, r), name)
) -> P(
  Node.facts(
    Spec.VendNode.does(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go), Spec.Deed.Work{})
  )
):
  match st go:
    case False{} True{}:
      hs => hg => p => p
    case True{} +go:
      hs => hg => p => Empty.absurd(
        P(
          Node.facts(
            Spec.VendNode.does(
              Node.asks(name, ws, ms, True{}, fs, ps, ok, i, r, go),
              Spec.Deed.Work{}
            )
          )
        ),
        Shared.Bool.true_ne_false(hs)
      )
    case +st False{}:
      hs => hg => p => Empty.absurd(
        P(
          Node.facts(
            Spec.VendNode.does(
              Node.asks(name, ws, ms, st, fs, ps, ok, i, r, False{}),
              Spec.Deed.Work{}
            )
          )
        ),
        Shared.Bool.false_ne_true(hg)
      )

# a connected writer that starts a store owned by the node alone gets it
def Node.starts(
  n: Spec.VendNode,
  +i: Ledgers.Id
) -> {
  Spec.VendNode.stopped(n) == False{}: Bool
} -> {
  List.contains(~String, ~String.eq, Spec.VendNode.writers(n), Spec.Id.writer(i)) == True{}: Bool
} -> Spec.Works(
  Spec.VendNode.does(n, Spec.Deed.Ask{i, Spec.Request.Start{[Spec.VendNode.name(n)]}}),
  m => {
    Spec.VendNode.answer(
      m,
      Spec.Question.Version{
        Ledgers.Line{
          Hashes.Sha.hash(Spec.Request.code(i, Spec.Request.Start{[Spec.VendNode.name(n)]})),
          None{}
        },
        0n
      }
    )
      == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
  }
):
  match n:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok}:
      hs => hw => (
        0n,
        Node.asks_at(
          s => {
            Answers.Answer.of(
              s,
              Spec.Question.Version{
                Ledgers.Line{
                  Hashes.Sha.hash(Spec.Request.code(i, Spec.Request.Start{[name]})),
                  None{}
                },
                0n
              }
            )
              == Some{Spec.Reply.Id{i}}: Maybe<&2, Spec.Reply>
          },
          name,
          ws,
          ms,
          st,
          fs,
          ps,
          ok,
          i,
          Spec.Request.Start{[name]},
          Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))
        )(
          Node.gate(st, List.contains(~String, ~String.eq, ws, Spec.Id.writer(i)))(hs)(hw)
        )(
          Equal.cong(
            Maybe<&2, Types.Entry>,
            Maybe<&2, Spec.Reply>,
            Answers.Reply.id,
            Lines.Line.at(
              Facts.Facts.ask(name, fs, i, Spec.Request.Start{[name]}),
              Ledgers.Line{Facts.Start.root(i, Spec.Request.Start{[name]}), None{}},
              0n
            ),
            Some{Lines.Entry.first(i, Spec.Request.Start{[name]}, 0n)},
            Versions.Line.started(name, fs, i, [name])
          )
        )
      )

def Spec.VendNode.starts(n, i):
  Node.starts(n, i)

# a writer reads its own write at once
def Node.reads_own(
  n: Spec.VendNode,
  +i: Ledgers.Id,
  +b: Ledgers.Line,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>
) -> {
  Spec.VendNode.stopped(n) == False{}: Bool
} -> {
  List.contains(~String, ~String.eq, Spec.VendNode.writers(n), Spec.Id.writer(i)) == True{}: Bool
} -> {
  Spec.VendNode.view(
    Spec.VendNode.does(n, Spec.Deed.Ask{i, Spec.Request.Write{b, p, ws}}),
    Spec.Id.writer(i),
    b,
    p
  )
    == Some{ws}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match n:
    case Tuple{Nodes.Raw{+name, +wrs, +ms, +st, +fs, +ps}, +ok}:
      hs => hw => Node.asks_at(
        s => {
          Answers.View.at(
            s,
            Spec.Id.writer(i),
            b,
            p
          )
            == Some{ws}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        name,
        wrs,
        ms,
        st,
        fs,
        ps,
        ok,
        i,
        Spec.Request.Write{b, p, ws},
        Bool.and(Bool.not(st), List.contains(~String, ~String.eq, wrs, Spec.Id.writer(i)))
      )(
        Node.gate(st, List.contains(~String, ~String.eq, wrs, Spec.Id.writer(i)))(hs)(hw)
      )(Live.View.reads_own(name, fs, i, b, p, ws))

def Spec.VendNode.reads_own(n, i, b, p, ws):
  Node.reads_own(n, i, b, p, ws)

# the node reads what a mounted resource held
def Node.mount_records(
  n: Spec.VendNode,
  +a: String,
  +b: Ledgers.Line,
  +p: String,
  +ws: List<&2, U32>
) -> {
  Spec.VendNode.stopped(n) == False{}: Bool
} -> {
  Spec.VendNode.view(
    Spec.VendNode.does(n, Spec.Deed.Mount{a, b, p, ws}),
    Spec.VendNode.name(n),
    b,
    p
  )
    == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match n:
    case Tuple{Nodes.Raw{+name, +wrs, +ms, +st, +fs, +ps}, +ok}:
      hs => Node.asks_at(
        s => {
          Answers.View.at(s, name, b, p) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        name,
        wrs,
        Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
        st,
        fs,
        ps,
        ok,
        Nodes.Mount.id(name, a),
        Spec.Request.Write{b, p, Some{ws}},
        Bool.not(st)
      )(
        Node.gate_not(st)(hs)
      )(Live.View.reads_own(name, fs, Nodes.Mount.id(name, a), b, p, Some{ws}))

def Spec.VendNode.mount_records(n, a, b, p, ws):
  Node.mount_records(n, a, b, p, ws)

# a node that alone decides writes a new request once it works
def Node.decides_alone(
  n: Spec.VendNode,
  +b: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +p: String,
  +ws: Maybe<&2, List<&2, U32>>
) -> {
  Spec.VendNode.stopped(n) == False{}: Bool
} -> {
  List.contains(~String, ~String.eq, Spec.VendNode.writers(n), Spec.Id.writer(i)) == True{}: Bool
} -> {
  Spec.VendNode.answer(
    n,
    Spec.Question.Count{b}
  )
    == Some{Spec.Reply.Number{k}}: Maybe<&2, Spec.Reply>
} -> {
  Spec.VendNode.answer(
    n,
    Spec.Question.Group{b, k}
  )
    == Some{Spec.Reply.Names{[Spec.VendNode.name(n)]}}: Maybe<&2, Spec.Reply>
} -> {
  Spec.VendNode.answer(n, Spec.Question.Status{b, i}) == None{}: Maybe<&2, Spec.Reply>
} -> Spec.Works(
  Spec.VendNode.does(n, Spec.Deed.Ask{i, Spec.Request.Write{b, p, ws}}),
  m => {
    Spec.VendNode.answer(
      m,
      Spec.Question.Status{b, i}
    )
      == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
  }
):
  match n:
    case Tuple{Nodes.Raw{+name, +wrs, +ms, +st, +fs, +ps}, +ok}:
      +hs => hw => h1 => h2 => h3 => (
        1n,
        (
          Spec.VendNode.does(
            Node.asks(
              name,
              wrs,
              ms,
              st,
              fs,
              ps,
              ok,
              i,
              Spec.Request.Write{b, p, ws},
              Bool.and(Bool.not(st), List.contains(~String, ~String.eq, wrs, Spec.Id.writer(i)))
            ),
            Spec.Deed.Work{}
          ),
          (
            {==},
            Node.asks_works_at(
              s => {
                Answers.Answer.of(
                  s,
                  Spec.Question.Status{b, i}
                )
                  == Some{Spec.Reply.Status{Spec.Status.Written{}}}: Maybe<&2, Spec.Reply>
              },
              name,
              wrs,
              ms,
              st,
              fs,
              ps,
              ok,
              i,
              Spec.Request.Write{b, p, ws},
              Bool.and(Bool.not(st), List.contains(~String, ~String.eq, wrs, Spec.Id.writer(i)))
            )(
              hs
            )(
              Node.gate(st, List.contains(~String, ~String.eq, wrs, Spec.Id.writer(i)))(hs)(hw)
            )(Live.Work.decides(name, fs, b, k, i, p, ws)(Node.sound(name, fs, ok))(h1)(h2)(h3))
          )
        )
      )

def Spec.VendNode.decides_alone(n, b, k, i, p, ws):
  Node.decides_alone(n, b, k, i, p, ws)

# Laws of the core, said of a node
# --------------------------------
def Spec.VendNode.answer_fits(n, q, r):
  Laws.Core.answer_fits(Node.facts(n), q, r)

def Spec.VendNode.counts_once(n, c, i, a, b):
  Laws.Core.counts_once(Node.facts(n), c, i, a, b)

def Spec.VendNode.written_made(n, c, i):
  Laws.Core.written_made(Node.facts(n), c, i)

def Spec.VendNode.mark_names(n, c, i, m, v):
  Laws.Core.mark_names(Node.facts(n), c, i, m, v)

def Spec.VendNode.merge_resolved(n, c, i, f, ps, p):
  Laws.Core.merge_resolved(Node.facts(n), c, i, f, ps, p)

def Spec.VendNode.majority_decides(n, c, k, os, gs):
  Laws.Core.majority_decides(Node.facts(n), c, k, os, gs)

def Spec.VendNode.branches_decided(n, r, b, x):
  Laws.Core.branches_decided(Node.facts(n), r, b, x)

# the parents of a version, in the words of the spec
def Node.parents_of(
  r: Spec.Request,
  -c: Ledgers.Line,
  -k: Nat,
  -ps: List<&2, Spec.Point>,
  m: Mirror.Request.Parents(r, c, k, ps)
) -> Spec.Request.Parents(r, c, k, ps):
  match r:
    case Spec.Request.Start{os}:
      m
    case Spec.Request.Write{b, p, w}:
      m
    case Spec.Request.Merge{f, x}:
      m
    case Spec.Request.Resolve{g, p, w}:
      m
    case Spec.Request.Mark{b, x, v}:
      m
    case Spec.Request.Move{b, t, v}:
      m
    case Spec.Request.Group{h, x, ms}:
      m
    case Spec.Request.Own{l, g}:
      m

# the law of the parents of the core, in the words of the spec
def Node.parents_are.of(
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -k: Nat,
  -i: Ledgers.Id,
  r: Spec.Request,
  -ps: List<&2, Spec.Point>,
  m: (
    {
      Spec.VendNode.answer(
        n,
        Spec.Question.Parents{c, 0n}
      )
        == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
    } -> {ps == []: List<&2, Spec.Point>}
  )
    & (
      Mirror.Made(
        Node.facts(n),
        c,
        1n+k,
        i,
        r
      ) -> {
        Spec.VendNode.answer(
          n,
          Spec.Question.Parents{c, 1n+k}
        )
          == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
      } -> Mirror.Request.Parents(r, c, k, ps)
    )
) -> (
  {
    Spec.VendNode.answer(
      n,
      Spec.Question.Parents{c, 0n}
    )
      == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
  } -> {ps == []: List<&2, Spec.Point>}
)
  & (
    Mirror.Made(
      Node.facts(n),
      c,
      1n+k,
      i,
      r
    ) -> {
      Spec.VendNode.answer(
        n,
        Spec.Question.Parents{c, 1n+k}
      )
        == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
    } -> Spec.Request.Parents(r, c, k, ps)
  ):
  match m:
    case Tuple{z, f}:
      (z, hm => he => Node.parents_of(r, c, k, ps, f(hm)(he)))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# the law of the parents of a node
def Node.parents_are(
  n: Spec.VendNode,
  +c: Ledgers.Line,
  +k: Nat,
  +i: Ledgers.Id,
  +r: Spec.Request,
  +ps: List<&2, Spec.Point>
) -> (
  {
    Spec.VendNode.answer(
      n,
      Spec.Question.Parents{c, 0n}
    )
      == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
  } -> {ps == []: List<&2, Spec.Point>}
)
  & (
    Mirror.Made(
      Node.facts(n),
      c,
      1n+k,
      i,
      r
    ) -> {
      Spec.VendNode.answer(
        n,
        Spec.Question.Parents{c, 1n+k}
      )
        == Some{Spec.Reply.Points{ps}}: Maybe<&2, Spec.Reply>
    } -> Spec.Request.Parents(r, c, k, ps)
  ):
  Node.parents_are.of(n, c, k, i, r, ps, Laws.Core.parents_are(Node.facts(n), c, k, i, r, ps))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.VendNode.parents_are(n, c, k, i, r, ps):
  Node.parents_are(n, c, k, i, r, ps)

def Spec.VendNode.group_nodes(n, s, g, k, ms, v):
  Owners.Core.group_nodes(Node.facts(n), s, g, k, ms, v)

def Spec.VendNode.group_nodes_only(n, s, g, k, ns, x):
  Owners.Core.group_nodes_only(Node.facts(n), s, g, k, ns, x)

def Spec.VendNode.members_decided(n, s, g, m, ms):
  Owners.Core.members_decided(Node.facts(n), s, g, m, ms)

def Spec.VendNode.groups_decided(n, s, g, m, y):
  Owners.Core.groups_decided(Node.facts(n), s, g, m, y)

def Spec.VendNode.owner_decided(n, c, k, g, m):
  Owners.Core.owner_decided(Node.facts(n), c, k, g, m)

def Spec.VendNode.group_of_era(n, c, k, gs):
  Owners.Core.group_of_era(Node.facts(n), c, k, gs)

def Spec.VendNode.eras_grow(n, c, a, b, x, y):
  Owners.Core.eras_grow(Node.facts(n), c, a, b, x, y)

def Spec.VendNode.write_writes(n, c, k, i, p, ws, q, x, y):
  Reads.Core.write_writes(Node.facts(n), c, k, i, p, ws, q, x, y)

# a chain of imports in the facts of a node is one at the node
def Node.imports_of(
  ps: List<&2, String>,
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -k: Nat,
  -bs: List<&2, String>,
  -a: String,
  -b: String,
  m: Mirror.Imports(Node.facts(n), c, k, bs, a, ps, b)
) -> Spec.Imports(n, c, k, bs, a, ps, b):
  match ps m:
    case Nil{} e:
      e
    case Con{q, rest} Tuple{ws, Tuple{e1, Tuple{e2, r}}}:
      (ws, (e1, (e2, Node.imports_of(rest, n, c, k, bs, q, b, r))))

# a chain of imports at a node is one in its facts
def Node.imports_to(
  ps: List<&2, String>,
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -k: Nat,
  -bs: List<&2, String>,
  -a: String,
  -b: String,
  m: Spec.Imports(n, c, k, bs, a, ps, b)
) -> Mirror.Imports(Node.facts(n), c, k, bs, a, ps, b):
  match ps m:
    case Nil{} e:
      e
    case Con{q, rest} Tuple{ws, Tuple{e1, Tuple{e2, r}}}:
      (ws, (e1, (e2, Node.imports_to(rest, n, c, k, bs, q, b, r))))

# a path reached in the facts of a node is reached at the node
def Node.reaches_of(
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -k: Nat,
  -bs: List<&2, String>,
  -us: List<&2, String>,
  -p: String,
  m: Mirror.Reaches(Node.facts(n), c, k, bs, us, p)
) -> Spec.Reaches(n, c, k, bs, us, p):
  match m:
    case Tuple{u, Tuple{e, Tuple{+ps, im}}}:
      (u, (e, (ps, Node.imports_of(ps, n, c, k, bs, u, p, im))))

# a path reached at a node is reached in its facts
def Node.reaches_to(
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -k: Nat,
  -bs: List<&2, String>,
  -us: List<&2, String>,
  -p: String,
  m: Spec.Reaches(n, c, k, bs, us, p)
) -> Mirror.Reaches(Node.facts(n), c, k, bs, us, p):
  match m:
    case Tuple{u, Tuple{e, Tuple{+ps, im}}}:
      (u, (e, (ps, Node.imports_to(ps, n, c, k, bs, u, p, im))))

# a path changed and reached in the facts of a node is so at the node
def Node.affects_only.of(
  -n: Spec.VendNode,
  -c: Ledgers.Line,
  -a: Nat,
  -b: Nat,
  -bs: List<&2, String>,
  -us: List<&2, String>,
  -p: String,
  m: Mirror.Changed(Node.facts(n), c, a, b, p) & Mirror.Reaches(Node.facts(n), c, b, bs, us, p)
) -> Spec.Changed(n, c, a, b, p)
  & Spec.Reaches(n, c, b, bs, us, p):
  match m:
    case Tuple{ch, rc}:
      (ch, Node.reaches_of(n, c, b, bs, us, p, rc))

def Spec.VendNode.affects_only(n, c, a, b, us, bs, ps, p):
  h => hin => Node.affects_only.of(
    n,
    c,
    a,
    b,
    bs,
    us,
    p,
    Affects.Core.affects_only(Node.facts(n), c, a, b, us, bs, ps, p)(h)(hin)
  )

def Spec.VendNode.affects_all(n, c, a, b, us, bs, ps, p):
  h => ch => rc => Affects.Core.affects_all(
    Node.facts(n),
    c,
    a,
    b,
    us,
    bs,
    ps,
    p
  )(h)(ch)(Node.reaches_to(n, c, b, bs, us, p, rc))

# a chain of parents in the facts of a node is one at the node
def Node.back_of(
  qs: List<&2, Spec.Point>,
  -n: Spec.VendNode,
  -a: Spec.Point,
  -c: Ledgers.Line,
  -k: Nat,
  m: Mirror.Back(Node.facts(n), a, qs, c, k)
) -> Spec.Back(n, a, qs, c, k):
  match qs m:
    case Nil{} e:
      e
    case Con{q, rest} Tuple{ps, Tuple{e1, Tuple{e2, r}}}:
      (ps, (e1, (e2, Node.back_of(rest, n, a, Spec.Point.line(q), Spec.Point.n(q), r))))

# a version before another in the facts of a node is before it at the node
def Node.before_of(
  -n: Spec.VendNode,
  -a: Spec.Point,
  -c: Ledgers.Line,
  -k: Nat,
  m: Mirror.Before(Node.facts(n), a, c, k)
) -> Spec.Before(n, a, c, k):
  match m:
    case Tuple{+qs, r}:
      (qs, Node.back_of(qs, n, a, c, k, r))

# the replies of a node only move forward, while it names no liar
def Node.answer_moves(
  +n: Spec.VendNode,
  +d: Spec.Deed,
  +q: Spec.Question,
  +a: Spec.Reply
) -> Spec.VendNode.Honest(
  Spec.VendNode.does(n, d)
) -> {
  Spec.VendNode.answer(n, q) == Some{a}: Maybe<&2, Spec.Reply>
} -> Exists(
  Spec.Reply,
  b => {
    Spec.VendNode.answer(Spec.VendNode.does(n, d), q) == Some{b}: Maybe<&2, Spec.Reply>
  }
    & Spec.Reply.Moves(q, a, b)
):
  hl => h => Forward.Core.answer_moves(
    Spec.VendNode.name(Spec.VendNode.does(n, d)),
    Node.facts(n),
    Node.facts(Spec.VendNode.does(n, d)),
    q,
    a
  )(Node.does_wider(n, d))(hl)(Node.ok(Spec.VendNode.does(n, d)))(h)

def Spec.VendNode.answer_moves_forward(n, d, q, a):
  Node.answer_moves(n, d, q, a)

# a read of a node never changes to other words, while it names no liar
def Node.read_stays(
  +n: Spec.VendNode,
  +d: Spec.Deed,
  +c: Ledgers.Line,
  +k: Nat,
  +p: String,
  +x: Maybe<&2, List<&2, U32>>
) -> Spec.VendNode.Honest(
  Spec.VendNode.does(n, d)
) -> {
  Spec.VendNode.read(n, c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {
  Spec.VendNode.read(
    Spec.VendNode.does(n, d),
    c,
    k,
    p
  )
    == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}
  | {
    Spec.VendNode.read(
      Spec.VendNode.does(n, d),
      c,
      k,
      p
    )
      == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }:
  hl => h => Reads.Core.read_stays(
    Spec.VendNode.name(Spec.VendNode.does(n, d)),
    Node.facts(n),
    Node.facts(Spec.VendNode.does(n, d)),
    c,
    k,
    p,
    x
  )(Node.does_wider(n, d))(hl)(Node.ok(Spec.VendNode.does(n, d)))(h)

def Spec.VendNode.read_stays(n, d, c, k, p, x):
  Node.read_stays(n, d, c, k, p, x)

def Spec.VendNode.move_equals(n, c, k, i, t, v, h, h2):
  Reads.Core.move_equals(Node.facts(n), c, k, i, t, v, h, h2)

# a version before two others in the facts of a node is before both at the node
def Node.base_shared.of(
  -n: Spec.VendNode,
  -a: Spec.Point,
  -c: Ledgers.Line,
  -k: Nat,
  -f: Ledgers.Line,
  -v: Nat,
  m: Mirror.Before(Node.facts(n), a, c, k) & Mirror.Before(Node.facts(n), a, f, v)
) -> Spec.Before(n, a, c, k)
  & Spec.Before(n, a, f, v):
  match m:
    case Tuple{x, y}:
      (Node.before_of(n, a, c, k, x), Node.before_of(n, a, f, v, y))

def Spec.VendNode.base_shared(n, c, k, i, f, v, a):
  hm => hp => hb => Node.base_shared.of(
    n,
    a,
    c,
    k,
    f,
    v,
    Reads.Core.base_shared(Node.facts(n), c, k, i, f, v, a)(hm)(hp)(hb)
  )

def Spec.VendNode.merge_merges(n, c, k, i, f, v, a, p, b, o, t):
  Reads.Core.merge_merges(Node.facts(n), c, k, i, f, v, a, p, b, o, t)
