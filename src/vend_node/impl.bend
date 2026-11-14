import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
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
import ./run/answers.bend as RAnswers
import ./run/facts.bend as RFacts
import ./run/known.bend as RKnown
import ./run/lines.bend as RLines
import ./run/parts.bend as RParts
import ./run/set.bend as Checks
import ./run/work.bend as RWorks
import ./shared/format.bend as Formats
import ./shared/lists.bend as Lists
import ./shared/parts.bend as Parts
import ./shared/set.bend as Sets
import ./spec.bend as Spec
import ./types.bend as Types
import ./versions.bend as Versions
import ./work.bend as Works

# A Vend Node
# -----------
# This file fills the names of spec.bend and proves its laws. A node is its
# state (Nodes.Raw), which is plain, with one proof: that the state passes
# the check of a node (Nodes.Raw.ok). The check says that its facts are a set
# and its parts a well formed map, that its facts are sound for its name
# (Facts.ok), and that its name is not reserved (Facts.Trust.reserved), so
# every node, however it came to be, never names itself a liar, and is never
# the one that another node names when its trust breaks. The code that runs
# (Nodes.Raw.does and what it calls, in run/) works on the plain state and
# builds no proof. The laws are those of the core, said of the facts of the
# node: the set that the map of its state is (Node.facts).
def Spec.VendNode():
  Sigma<&2, &2, Nodes.Raw, r => {Nodes.Raw.ok(r) == True{}: Bool}>

def Spec.Change():
  Types.Change

def Spec.Request.code(i, r):
  Coded.Named.code(i, r)

def Spec.Change.ballot(c):
  RFacts.Change.ballot(c)

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

# the map of the facts of the node n: what the code that runs holds
def Node.tree(n: Spec.VendNode) -> RFacts.Plain():
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      fs

# the map fs of a sound state passes the two checks of a set
def Node.set_ok(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  Bool.and(
    Crits.Crit.wf(~Types.Fact, fs, 0n),
    Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
  )
    == True{}: Bool
}:
  Shared.Bool.and_true_left(
    Bool.and(
      Crits.Crit.wf(~Types.Fact, fs, 0n),
      Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
    ),
    RParts.Parts.wf(ps)
  )(
    Shared.Bool.and_true_left(
      Nodes.Raw.set(fs, ps),
      Bool.and(RFacts.Facts.ok(name, fs), Bool.not(RFacts.Trust.reserved(name)))
    )(ok)
  )

# the map of the parts ps of a sound state is well formed
def Node.parts_wf(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {RParts.Parts.wf(ps) == True{}: Bool}:
  Shared.Bool.and_true_right(
    Bool.and(
      Crits.Crit.wf(~Types.Fact, fs, 0n),
      Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
    ),
    RParts.Parts.wf(ps)
  )(
    Shared.Bool.and_true_left(
      Nodes.Raw.set(fs, ps),
      Bool.and(RFacts.Facts.ok(name, fs), Bool.not(RFacts.Trust.reserved(name)))
    )(ok)
  )

# the proofs that the map fs of a sound state is a set, from the check that
# the state passes (ok)
def Node.checked(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> Sets.ValSet.Checked(~Types.Fact, ~Coded.Fact.words, fs):
  (
    Shared.Bool.and_true_left(
      Crits.Crit.wf(~Types.Fact, fs, 0n),
      Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
    )(Node.set_ok(name, fs, ps, ok)),
    Shared.Bool.and_true_right(
      Crits.Crit.wf(~Types.Fact, fs, 0n),
      Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, fs)
    )(Node.set_ok(name, fs, ps, ok))
  )

# the facts of a sound state of the name name and the map fs: the map, with
# the proofs that it is a set. Only the laws use it: the code that runs holds
# the map alone
def Node.set(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> Facts.Facts():
  (fs, Node.checked(name, fs, ps, ok))

# the facts of the node n
def Node.facts(n: Spec.VendNode) -> Facts.Facts():
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Node.set(name, fs, ps, ok)

def Spec.VendNode.name(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      name

def Spec.VendNode.writers(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      ws

def Spec.VendNode.mounts(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      Nodes.Mounts.addresses(ms)

def Spec.VendNode.stopped(n):
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      st

def Spec.VendNode.holds(n, c):
  Facts.Facts.holds(Node.facts(n), c)

# the parts of the node n: the map that its state holds, with the proof that
# it is well formed. Only the laws use it
def Node.kept(n: Spec.VendNode) -> Parts.Parts:
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Parts.Parts.of(ps, Node.parts_wf(name, fs, ps, ok))

def Spec.VendNode.parts(n):
  Parts.Parts.list(Node.kept(n))

def Spec.VendNode.part(n, h):
  Parts.Parts.get(Node.kept(n), h)

def Spec.VendNode.read(n, c, k, p):
  Contents.Content.read(Node.facts(n), c, k, p)

def Spec.VendNode.view(n, w, b, p):
  Answers.View.at(Node.facts(n), w, b, p)

def Spec.VendNode.answer(n, q):
  Answers.Answer.of(Node.facts(n), q)

def Spec.VendNode.liars(n):
  Facts.Facts.liars(Node.facts(n))

# What the code that runs shows
# -----------------------------
# What a node shows is said of its facts (a set, with its proofs), so that the
# laws of the core are laws of the node. The code that runs reads the same
# from the plain state (Nodes.Raw.answer, ...), and builds no proof.

# the map of the facts of a node is the map that its state holds
def Node.facts_tree(
  n: Spec.VendNode
) -> {Facts.Facts.crit(Node.facts(n)) == Nodes.Raw.facts(Node.raw(n)): RFacts.Plain()}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node holds a change when its state does
def Node.holds_runs(
  n: Spec.VendNode,
  c: Types.Change
) -> {Spec.VendNode.holds(n, c) == Nodes.Raw.holds(Node.raw(n), c): Bool}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node reads what its state reads
def Node.read_runs(
  n: Spec.VendNode,
  c: Ledgers.Line,
  k: Nat,
  p: String
) -> {
  Spec.VendNode.read(
    n,
    c,
    k,
    p
  )
    == Nodes.Raw.read(Node.raw(n), c, k, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node shows a writer what its state shows
def Node.view_runs(
  n: Spec.VendNode,
  w: String,
  b: Ledgers.Line,
  p: String
) -> {
  Spec.VendNode.view(
    n,
    w,
    b,
    p
  )
    == Nodes.Raw.view(Node.raw(n), w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node answers what its state answers
def Node.answer_runs(
  n: Spec.VendNode,
  q: Spec.Question
) -> {Spec.VendNode.answer(n, q) == Nodes.Raw.answer(Node.raw(n), q): Maybe<&2, Spec.Reply>}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node names the liars that its state names
def Node.liars_runs(
  n: Spec.VendNode
) -> {Spec.VendNode.liars(n) == Nodes.Raw.liars(Node.raw(n)): List<&2, String>}:
  match n:
    case Tuple{Nodes.Raw{name, ws, ms, st, fs, +ps}, ok}:
      {==}

# a node lists the parts that its state lists
def Node.parts_runs(
  n: Spec.VendNode
) -> {Spec.VendNode.parts(n) == Nodes.Raw.parts(Node.raw(n)): List<&2, Hashes.Hash>}:
  match n:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, RParts.Parts{+m}}, +ok}:
      Parts.Parts.list_runs(Node.kept(Tuple{Nodes.Raw{name, ws, ms, st, fs, RParts.Parts{m}}, ok}))

# a node holds the words of a hash that its state holds
def Node.part_runs(
  n: Spec.VendNode,
  +h: Hashes.Hash
) -> {Spec.VendNode.part(n, h) == Nodes.Raw.part(Node.raw(n), h): Maybe<&2, List<&2, U32>>}:
  match n:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, RParts.Parts{+m}}, +ok}:
      Parts.Parts.get_runs(
        Node.kept(Tuple{Nodes.Raw{name, ws, ms, st, fs, RParts.Parts{m}}, ok}),
        h
      )

# What a node does
# ----------------

# the facts of a sound state of the name name are sound for the name
def Node.sound(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {Facts.Facts.ok(name, Node.set(name, fs, ps, ok)) == True{}: Bool}:
  Shared.Bool.and_true_left(
    RFacts.Facts.ok(name, fs),
    Bool.not(RFacts.Trust.reserved(name))
  )(
    Shared.Bool.and_true_right(
      Nodes.Raw.set(fs, ps),
      Bool.and(RFacts.Facts.ok(name, fs), Bool.not(RFacts.Trust.reserved(name)))
    )(ok)
  )

# the name name of a node, whatever its facts fs, is not reserved
def Node.free(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {Bool.not(RFacts.Trust.reserved(name)) == True{}: Bool}:
  Shared.Bool.and_true_right(
    RFacts.Facts.ok(name, fs),
    Bool.not(RFacts.Trust.reserved(name))
  )(
    Shared.Bool.and_true_right(
      Nodes.Raw.set(fs, ps),
      Bool.and(RFacts.Facts.ok(name, fs), Bool.not(RFacts.Trust.reserved(name)))
    )(ok)
  )

# a map m that is the map of facts gs, sound for a name name that is not
# reserved, can be the map of a node of that name, with parts qs that are
# well formed: the proofs that m is a set are those of gs
def Node.join(
  +name: String,
  +m: RFacts.Plain(),
  +qs: RParts.Parts,
  +gs: Facts.Facts(),
  e: {Facts.Facts.crit(gs) == m: RFacts.Plain()},
  pw: {RParts.Parts.wf(qs) == True{}: Bool},
  sound: {Facts.Facts.ok(name, gs) == True{}: Bool},
  free: {Bool.not(RFacts.Trust.reserved(name)) == True{}: Bool}
) -> {Nodes.Raw.sound(name, m, qs) == True{}: Bool}:
  %e: {Nodes.Raw.sound(name, _, qs) == True{}: Bool}
  Shared.Bool.and_both(
    Nodes.Raw.set(Facts.Facts.crit(gs), qs),
    Bool.and(RFacts.Facts.ok(name, Facts.Facts.crit(gs)), Bool.not(RFacts.Trust.reserved(name)))
  )(
    Shared.Bool.and_both(
      Bool.and(
        Crits.Crit.wf(~Types.Fact, Facts.Facts.crit(gs), 0n),
        Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, Facts.Facts.crit(gs))
      ),
      RParts.Parts.wf(qs)
    )(
      Shared.Bool.and_both(
        Crits.Crit.wf(~Types.Fact, Facts.Facts.crit(gs), 0n),
        Checks.ValSet.ok(~Types.Fact, ~Coded.Fact.words, Facts.Facts.crit(gs))
      )(
        Sets.ValSet.wf(~Types.Fact, ~Coded.Fact.words, gs)
      )(Sets.ValSet.checked(~Types.Fact, ~Coded.Fact.words, gs))
    )(pw)
  )(
    Shared.Bool.and_both(
      RFacts.Facts.ok(name, Facts.Facts.crit(gs)),
      Bool.not(RFacts.Trust.reserved(name))
    )(sound)(free)
  )

# a node of the name name keeps its proof when its map goes from fs to m and
# its parts from ps to qs, if qs are well formed and m is the map of facts gs
# that are sound for the name whenever those of fs are
def Node.resound(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +gs: Facts.Facts(),
  +m: RFacts.Plain(),
  +qs: RParts.Parts,
  e: {Facts.Facts.crit(gs) == m: RFacts.Plain()},
  pw: {RParts.Parts.wf(qs) == True{}: Bool},
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  step: {
    Facts.Facts.ok(name, Node.set(name, fs, ps, ok)) == True{}: Bool
  } -> {Facts.Facts.ok(name, gs) == True{}: Bool}
) -> {Nodes.Raw.sound(name, m, qs) == True{}: Bool}:
  Node.join(name, m, qs, gs, e, pw, step(Node.sound(name, fs, ps, ok)), Node.free(name, fs, ps, ok))

# the parts ps with the words m, if any, are well formed
def Node.kept_wf(
  +ps: RParts.Parts,
  m: Maybe<&2, List<&2, U32>>
) -> {
  RParts.Parts.wf(ps) == True{}: Bool
} -> {RParts.Parts.wf(Nodes.Kept.with(ps, m)) == True{}: Bool}:
  match m:
    case None{}:
      w => w
    case Some{+ws}:
      w => Parts.Plain.put_wf(ps, ws)(w)

# sets of facts on one map are one set: the facts of a sound state are any
# facts gs whose map is its map
def Node.set_eq(
  +name: String,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  gs: Facts.Facts()
) -> {
  Facts.Facts.crit(gs) == fs: RFacts.Plain()
} -> {Node.set(name, fs, ps, ok) == gs: Facts.Facts()}:
  match gs:
    case Tuple{+m, +p}:
      e => Sets.ValSet.of_eq(
        ~Types.Fact,
        ~Coded.Fact.words,
        fs,
        m,
        Equal.sym(RFacts.Plain(), m, fs, e)
      )(Node.checked(name, fs, ps, ok))(p)

# the facts of a node are any facts gs whose map is the map of the node
def Node.facts_eq(
  n: Spec.VendNode,
  +gs: Facts.Facts()
) -> {Facts.Facts.crit(gs) == Node.tree(n): RFacts.Plain()} -> {Node.facts(n) == gs: Facts.Facts()}:
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      e => Node.set_eq(name, fs, ps, ok, gs)(e)

# a node of the name name, that holds nothing yet, unless the name is
# reserved (b)
def Node.new.if(
  +name: String,
  b: Bool,
  e: {RFacts.Trust.reserved(name) == b: Bool}
) -> Maybe<&2, Spec.VendNode>:
  match b e:
    case True{} e:
      None{}
    case False{} e:
      Some{
        (
          Nodes.Raw.new(name),
          Node.join(
            name,
            RFacts.Facts.new(),
            RParts.Parts.new(),
            Facts.Facts.new(),
            {==},
            Parts.Plain.new_wf(),
            Facts.Facts.new_ok(name),
            Equal.cong(Bool, Bool, Bool.not, RFacts.Trust.reserved(name), False{}, e)
          )
        )
      }

# a node of the name name, that holds nothing yet; none if the name is
# reserved, as no node has such a name
def Node.new(+name: String) -> Maybe<&2, Spec.VendNode>:
  Node.new.if(name, RFacts.Trust.reserved(name), {==})

# the deed d on plain states: the other node of a Sync is its state
def Node.act(d: Spec.Deed) -> Nodes.Act:
  match d:
    case Spec.Deed.Connect{w}:
      Nodes.Act.Connect{w}
    case Spec.Deed.Leave{w}:
      Nodes.Act.Leave{w}
    case Spec.Deed.Ask{i, r}:
      Nodes.Act.Ask{i, r}
    case Spec.Deed.Sync{Tuple{r, ok}}:
      Nodes.Act.Sync{r}
    case Spec.Deed.Mount{a, b, p, held}:
      Nodes.Act.Mount{a, b, p, held}
    case Spec.Deed.Unmount{a}:
      Nodes.Act.Unmount{a}
    case Spec.Deed.Work{}:
      Nodes.Act.Work{}
    case Spec.Deed.Drop{}:
      Nodes.Act.Drop{}
    case Spec.Deed.Stop{f}:
      Nodes.Act.Stop{f}

# a sound state stays sound when the node takes in a request: its map is the
# map of the facts that the laws build (Facts.Facts.ask_crit), which are a
# set and are sound
def Node.asks_sound(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {Nodes.Raw.ok(Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go)) == True{}: Bool}:
  match go:
    case False{}:
      ok
    case True{}:
      Node.resound(
        name,
        fs,
        ps,
        Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r),
        RFacts.Facts.ask(name, fs, i, r),
        Nodes.Kept.with(ps, Nodes.Request.content(r)),
        Facts.Facts.ask_crit(name, Node.set(name, fs, ps, ok), i, r),
        Node.kept_wf(ps, Nodes.Request.content(r))(Node.parts_wf(name, fs, ps, ok)),
        ok,
        Facts.Facts.take_ok(
          name,
          Node.set(name, fs, ps, ok),
          Types.Fact.Ask{Facts.Facts.asked(Node.set(name, fs, ps, ok), i, r)}
        )
      )

# a sound state stays sound when the node works
def Node.works_sound(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {Nodes.Raw.ok(Nodes.Raw.works(name, ws, ms, st, fs, ps)) == True{}: Bool}:
  match st:
    case True{}:
      ok
    case False{}:
      Node.resound(
        name,
        fs,
        ps,
        Works.Work.does(Node.set(name, fs, ps, ok), name),
        RWorks.Work.does(RKnown.Known.none(), fs, name),
        ps,
        Works.Work.does_crit(Node.set(name, fs, ps, ok), name),
        Node.parts_wf(name, fs, ps, ok),
        ok,
        Live.Work.does_ok(name, Node.set(name, fs, ps, ok))
      )

# a sound state stays sound after any deed: the proof that a node carries,
# which the code that runs (Nodes.Raw.does) never builds
def Node.does_sound(
  +r: Nodes.Raw,
  +d: Spec.Deed
) -> {
  Nodes.Raw.ok(r) == True{}: Bool
} -> {Nodes.Raw.ok(Nodes.Raw.does(r, Node.act(d))) == True{}: Bool}:
  match r d:
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Connect{+w}:
      ok => ok
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Leave{+w}:
      ok => ok
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Ask{+i, +q}:
      +ok => Node.asks_sound(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        i,
        q,
        Bool.and(Bool.not(st), List.contains(~String, ~String.eq, ws, Spec.Id.writer(i))),
        ok
      )
    case Nodes.Raw{
      +name,
      +ws,
      +ms,
      +st,
      +fs,
      +ps
    } Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, +fs2, +ps2}, ok2}}:
      +ok => Node.resound(
        name,
        fs,
        ps,
        Facts.Facts.take_all(name, RFacts.Facts.list(fs2), Node.set(name, fs, ps, ok)),
        RFacts.Facts.take_all(name, RFacts.Facts.list(fs2), fs),
        RParts.Parts.join(ps, ps2),
        Facts.Facts.take_all_crit(name, RFacts.Facts.list(fs2), Node.set(name, fs, ps, ok)),
        Parts.Plain.join_wf(ps, ps2)(Node.parts_wf(name, fs, ps, ok)),
        ok,
        Facts.Facts.take_all_ok(name, RFacts.Facts.list(fs2), Node.set(name, fs, ps, ok))
      )
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Mount{+a, +b, +p, +held}:
      +ok => Node.asks_sound(
        name,
        ws,
        Nodes.Mounted{a, b, p} <> Nodes.Mounts.remove(ms, a),
        st,
        fs,
        ps,
        Nodes.Mount.id(name, a),
        Spec.Request.Write{b, p, Some{held}},
        Bool.not(st),
        ok
      )
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Unmount{+a}:
      ok => ok
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Work{}:
      +ok => Node.works_sound(name, ws, ms, st, fs, ps, ok)
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Drop{}:
      +ok => Node.join(
        name,
        fs,
        RParts.Parts.only(ps, Nodes.Needs.of(RKnown.Known.none(), fs, name, ms)),
        Node.set(name, fs, ps, ok),
        {==},
        Parts.Plain.only_wf(ps, Nodes.Needs.of(RKnown.Known.none(), fs, name, ms)),
        Node.sound(name, fs, ps, ok),
        Node.free(name, fs, ps, ok)
      )
    case Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps} Spec.Deed.Stop{+f}:
      ok => ok

# the node n after the deed d: its state after the deed, with the proof that
# it is sound
def Node.does(n: Spec.VendNode, +d: Spec.Deed) -> Spec.VendNode:
  match n:
    case Tuple{+r, ok}:
      (Nodes.Raw.does(r, Node.act(d)), Node.does_sound(r, d)(ok))

def Spec.VendNode.does(n, d):
  Node.does(n, d)

# the code that runs works on plain states (Nodes.Raw.does) and builds no
# proof; this is the link that it relies on: the state of a node after a deed
# is what the plain code computes from its state
def Node.runs(
  n: Spec.VendNode,
  d: Spec.Deed
) -> {Node.raw(Spec.VendNode.does(n, d)) == Nodes.Raw.does(Node.raw(n), Node.act(d)): Nodes.Raw}:
  match n:
    case Tuple{r, ok}:
      {==}

# the node that takes in the request r of the id i when it may (go): the
# state Nodes.Raw.asks with its proof, as Spec.VendNode.does builds it; the
# laws of a node that asks are said of it
def Node.asks(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  +go: Bool
) -> Spec.VendNode:
  (
    Nodes.Raw.asks(name, ws, ms, st, fs, ps, i, r, go),
    Node.asks_sound(name, ws, ms, st, fs, ps, i, r, go, ok)
  )

# the node after a work, unless it has stopped: the state Nodes.Raw.works
# with its proof, as Spec.VendNode.does builds it
def Node.works(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> Spec.VendNode:
  (Nodes.Raw.works(name, ws, ms, st, fs, ps), Node.works_sound(name, ws, ms, st, fs, ps, ok))

# the facts of a node that takes a request in are the facts with the request
def Node.asks_facts(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  Facts.Facts.ask(
    name,
    Node.set(name, fs, ps, ok),
    i,
    r
  )
    == Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, True{})): Facts.Facts()
}:
  Equal.sym(
    Facts.Facts(),
    Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, True{})),
    Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r),
    Node.facts_eq(
      Node.asks(name, ws, ms, st, fs, ps, ok, i, r, True{}),
      Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r)
    )(Facts.Facts.ask_crit(name, Node.set(name, fs, ps, ok), i, r))
  )

# the facts of a node that works are the facts after a work
def Node.works_facts(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  Works.Work.does(
    Node.set(name, fs, ps, ok),
    name
  )
    == Node.facts(Node.works(name, ws, ms, False{}, fs, ps, ok)): Facts.Facts()
}:
  Equal.sym(
    Facts.Facts(),
    Node.facts(Node.works(name, ws, ms, False{}, fs, ps, ok)),
    Works.Work.does(Node.set(name, fs, ps, ok), name),
    Node.facts_eq(
      Node.works(name, ws, ms, False{}, fs, ps, ok),
      Works.Work.does(Node.set(name, fs, ps, ok), name)
    )(Works.Work.does_crit(Node.set(name, fs, ps, ok), name))
  )

# the facts of a node after a Sync are its facts after it takes in each fact
# of the other node
def Node.syncs_facts(
  n: Spec.VendNode,
  m: Spec.VendNode
) -> {
  Facts.Facts.take_all(
    Spec.VendNode.name(n),
    Facts.Facts.list(Node.facts(m)),
    Node.facts(n)
  )
    == Node.facts(Spec.VendNode.does(n, Spec.Deed.Sync{m})): Facts.Facts()
}:
  match n m:
    case Tuple{
      Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps},
      +ok
    } Tuple{Nodes.Raw{+name2, +ws2, +ms2, +st2, +fs2, +ps2}, +ok2}:
      Equal.sym(
        Facts.Facts(),
        Node.facts(
          Spec.VendNode.does(
            Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok},
            Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}
          )
        ),
        Facts.Facts.take_all(
          name,
          Facts.Facts.list(Node.set(name2, fs2, ps2, ok2)),
          Node.set(name, fs, ps, ok)
        ),
        Node.facts_eq(
          Spec.VendNode.does(
            Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok},
            Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}}
          ),
          Facts.Facts.take_all(
            name,
            Facts.Facts.list(Node.set(name2, fs2, ps2, ok2)),
            Node.set(name, fs, ps, ok)
          )
        )(
          Facts.Facts.take_all_crit(
            name,
            Facts.Facts.list(Node.set(name2, fs2, ps2, ok2)),
            Node.set(name, fs, ps, ok)
          )
        )
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
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Node.sound(name, fs, ps, ok)

# the name of a node is not reserved: it is never the name under which a node
# says that its trust broke (Facts.Trust.voter), so no node is named a liar
# by the broken trust of another
def Node.name_free(
  n: Spec.VendNode
) -> {RFacts.Trust.reserved(Spec.VendNode.name(n)) == False{}: Bool}:
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Shared.Bool.not_true(RFacts.Trust.reserved(name))(Node.free(name, fs, ps, ok))

def Spec.VendNode.never_lies(n):
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Facts.Facts.ok_never(name, Node.set(name, fs, ps, ok))(Node.sound(name, fs, ps, ok))

def Spec.VendNode.liars_are(n, v):
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Facts.Facts.liars_are(Node.set(name, fs, ps, ok), v)

def Spec.VendNode.liars_found(n, a, b, v, s, x, y):
  match n:
    case Tuple{Nodes.Raw{+name, ws, ms, st, +fs, +ps}, +ok}:
      Facts.Facts.liars_found(Node.set(name, fs, ps, ok), a, b, v, s, x, y)

def Spec.VendNode.part_is(n, h, ws):
  Parts.Parts.part_is(Node.kept(n), h, ws)

def Spec.VendNode.same_changes(n1, n2, q):
  match n1 n2:
    case Tuple{
      Nodes.Raw{+name, ws, ms, st, +fs, +ps},
      +ok
    } Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}:
      h => Equal.cong(
        Facts.Facts(),
        Maybe<&2, Spec.Reply>,
        s => Answers.Answer.of(s, q),
        Node.set(name, fs, ps, ok),
        Node.set(name2, fs2, ps2, ok2),
        Facts.Facts.same(Node.set(name, fs, ps, ok), Node.set(name2, fs2, ps2, ok2))(h)
      )

def Spec.VendNode.reads_agree(n1, n2, c, k, p, x, y):
  match n1 n2:
    case Tuple{
      Nodes.Raw{+name, ws, ms, st, +fs, +ps},
      +ok
    } Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}:
      h => hx => hy => Shared.Maybe.some_inj(
        Maybe<&2, List<&2, U32>>,
        x,
        y,
        Equal.trans(
          Maybe<&2, Maybe<&2, List<&2, U32>>>,
          Some{x},
          Contents.Content.read(Node.set(name2, fs2, ps2, ok2), c, k, p),
          Some{y},
          Equal.trans(
            Maybe<&2, Maybe<&2, List<&2, U32>>>,
            Some{x},
            Contents.Content.read(Node.set(name, fs, ps, ok), c, k, p),
            Contents.Content.read(Node.set(name2, fs2, ps2, ok2), c, k, p),
            Equal.sym(
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              Contents.Content.read(Node.set(name, fs, ps, ok), c, k, p),
              Some{x},
              hx
            ),
            Equal.cong(
              Facts.Facts(),
              Maybe<&2, Maybe<&2, List<&2, U32>>>,
              s => Contents.Content.read(s, c, k, p),
              Node.set(name, fs, ps, ok),
              Node.set(name2, fs2, ps2, ok2),
              Facts.Facts.same(Node.set(name, fs, ps, ok), Node.set(name2, fs2, ps2, ok2))(h)
            )
          ),
          hy
        )
      )

def Spec.VendNode.views_agree(n1, n2, w, b, p):
  match n1 n2:
    case Tuple{
      Nodes.Raw{+name, ws, ms, st, +fs, +ps},
      +ok
    } Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}:
      h => Equal.cong(
        Facts.Facts(),
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        s => Answers.View.at(s, w, b, p),
        Node.set(name, fs, ps, ok),
        Node.set(name2, fs2, ps2, ok2),
        Facts.Facts.same(Node.set(name, fs, ps, ok), Node.set(name2, fs2, ps2, ok2))(h)
      )

# Laws of what a node is
# ----------------------

# a node that asks keeps its name
def Node.asks_name(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
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
    } Spec.Deed.Sync{Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}}:
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
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
    } Spec.Deed.Sync{Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}}:
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
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
    } Spec.Deed.Sync{Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}}:
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
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
    } Spec.Deed.Sync{Tuple{Nodes.Raw{+name2, ws2, ms2, st2, +fs2, +ps2}, +ok2}}:
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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  Facts.Facts.wider(
    Node.set(name, fs, ps, ok),
    Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go))
  )
    == True{}: Bool
}:
  match go:
    case False{}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
    case True{}:
      %Node.asks_facts(
        name,
        ws,
        ms,
        st,
        fs,
        ps,
        ok,
        i,
        r
      ): {Facts.Facts.wider(Node.set(name, fs, ps, ok), _) == True{}: Bool}
      Facts.Facts.take_wider(
        name,
        Node.set(name, fs, ps, ok),
        Types.Fact.Ask{Facts.Facts.asked(Node.set(name, fs, ps, ok), i, r)}
      )

# the facts of a node that works are wider
def Node.works_wider(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool}
) -> {
  Facts.Facts.wider(
    Node.set(name, fs, ps, ok),
    Node.facts(Node.works(name, ws, ms, st, fs, ps, ok))
  )
    == True{}: Bool
}:
  match st:
    case True{}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
    case False{}:
      %Node.works_facts(
        name,
        ws,
        ms,
        fs,
        ps,
        ok
      ): {Facts.Facts.wider(Node.set(name, fs, ps, ok), _) == True{}: Bool}
      Live.Work.does_wider(name, Node.set(name, fs, ps, ok))

# the facts of a node are wider after any deed
def Node.does_wider(
  n: Spec.VendNode,
  d: Spec.Deed
) -> {Facts.Facts.wider(Node.facts(n), Node.facts(Spec.VendNode.does(n, d))) == True{}: Bool}:
  match n d:
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Connect{+w}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Leave{+w}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
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
    } Spec.Deed.Sync{Tuple{Nodes.Raw{+name2, +ws2, +ms2, +st2, +fs2, +ps2}, +ok2}}:
      %Node.syncs_facts(
        Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok},
        Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}
      ): {Facts.Facts.wider(Node.set(name, fs, ps, ok), _) == True{}: Bool}
      Facts.Facts.take_all_wider(
        name,
        Facts.Facts.list(Node.set(name2, fs2, ps2, ok2)),
        Node.set(name, fs, ps, ok)
      )
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
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Work{}:
      Node.works_wider(name, ws, ms, st, fs, ps, ok)
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Drop{}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))
    case Tuple{Nodes.Raw{+name, +ws, +ms, +st, +fs, +ps}, +ok} Spec.Deed.Stop{f}:
      Facts.Facts.wider_refl(Node.set(name, fs, ps, ok))

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
    } Tuple{Nodes.Raw{+name2, +ws2, +ms2, +st2, +fs2, +ps2}, +ok2}:
      hn => hc =>
        %Node.syncs_facts(
          Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok},
          Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}
        ): {Facts.Facts.holds(_, c) == True{}: Bool}
        Facts.Facts.take_all_holds(
          name,
          Node.set(name2, fs2, ps2, ok2),
          Node.set(name, fs, ps, ok),
          c
        )((
            %Equal.sym(Facts.Facts(), Facts.Facts.take_all(name, Facts.Facts.list(Node.set(name2, fs2, ps2, ok2)), Node.set(name, fs, ps, ok)), Node.facts(Spec.VendNode.does(Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}, Spec.Deed.Sync{Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2}})), Node.syncs_facts(Tuple{Nodes.Raw{name, ws, ms, st, fs, ps}, ok}, Tuple{Nodes.Raw{name2, ws2, ms2, st2, fs2, ps2}, ok2})): {Facts.Facts.liars(_) == []: List<&2, String>}
            hn))(hc)

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
    case Tuple{+r, +ok}:
      Node.parts_once.of(Node.kept(Tuple{r, ok}), Parts.Parts.once(Node.kept(Tuple{r, ok})))

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
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  go == True{}: Bool
} -> P(
  Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r)
) -> P(Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go))):
  match go:
    case False{}:
      h => p => Empty.absurd(
        P(Node.facts(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, False{}))),
        Shared.Bool.false_ne_true(h)
      )
    case True{}:
      h => p =>
        %Node.asks_facts(name, ws, ms, st, fs, ps, ok, i, r): P(_)
        p

# the facts of a node that takes a request in and works are the facts with the
# request, after a work
def Node.asks_works_facts(
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request
) -> {
  Works.Work.does(
    Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r),
    name
  )
    == Node.facts(
      Spec.VendNode.does(
        Node.asks(name, ws, ms, False{}, fs, ps, ok, i, r, True{}),
        Spec.Deed.Work{}
      )
    ): Facts.Facts()
}:
  Equal.sym(
    Facts.Facts(),
    Node.facts(
      Spec.VendNode.does(
        Node.asks(name, ws, ms, False{}, fs, ps, ok, i, r, True{}),
        Spec.Deed.Work{}
      )
    ),
    Works.Work.does(Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r), name),
    Node.facts_eq(
      Spec.VendNode.does(
        Node.asks(name, ws, ms, False{}, fs, ps, ok, i, r, True{}),
        Spec.Deed.Work{}
      ),
      Works.Work.does(Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r), name)
    )((
        %Facts.Facts.ask_crit(name, Node.set(name, fs, ps, ok), i, r): {Facts.Facts.crit(Works.Work.does(Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r), name)) == RWorks.Work.does(RKnown.Known.none(), _, name): RFacts.Plain()}
        Works.Work.does_crit(Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r), name)))
  )

# what holds of the facts with a request, after a work, holds of the facts of
# a node that takes it in and works
def Node.asks_works_at(
  -P: Facts.Facts() -> Type,
  +name: String,
  +ws: List<&2, String>,
  +ms: List<&2, Nodes.Mounted>,
  +st: Bool,
  +fs: RFacts.Plain(),
  +ps: RParts.Parts,
  +ok: {Nodes.Raw.sound(name, fs, ps) == True{}: Bool},
  +i: Ledgers.Id,
  +r: Spec.Request,
  go: Bool
) -> {
  st == False{}: Bool
} -> {
  go == True{}: Bool
} -> P(
  Works.Work.does(Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, r), name)
) -> P(
  Node.facts(
    Spec.VendNode.does(Node.asks(name, ws, ms, st, fs, ps, ok, i, r, go), Spec.Deed.Work{})
  )
):
  match st go:
    case False{} True{}:
      hs => hg => p =>
        %Node.asks_works_facts(name, ws, ms, fs, ps, ok, i, r): P(_)
        p
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
            RAnswers.Reply.id,
            Lines.Line.at(
              Facts.Facts.ask(name, Node.set(name, fs, ps, ok), i, Spec.Request.Start{[name]}),
              Ledgers.Line{RFacts.Start.root(i, Spec.Request.Start{[name]}), None{}},
              0n
            ),
            Some{RLines.Entry.first(i, Spec.Request.Start{[name]}, 0n)},
            Versions.Line.started(name, Node.set(name, fs, ps, ok), i, [name])
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
      )(Live.View.reads_own(name, Node.set(name, fs, ps, ok), i, b, p, ws))

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
      )(
        Live.View.reads_own(
          name,
          Node.set(name, fs, ps, ok),
          Nodes.Mount.id(name, a),
          b,
          p,
          Some{ws}
        )
      )

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
            )(
              Live.Work.decides(
                name,
                Node.set(name, fs, ps, ok),
                b,
                k,
                i,
                p,
                ws
              )(Node.sound(name, fs, ps, ok))(h1)(h2)(h3)
            )
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
