# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/formats.bend as Formats
import ../../shared/ledger.bend as Ledgers
import ../../shared/resources.bend as Resources
import ../../shared/rope.bend as Ropes
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/seal.bend as Seals
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/tree.bend as Trees
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../stepping.bend as Stepping
import ../voting.bend as Voting
import ../../shared/shared/store.bend as Stores
import ../../replica/impl.bend as Replicas

def Spec.Ask.same():
  Basics.Ask.laws()

# Owners
# ------

# owners that fit the nodes ns are ns
def Fits.same(
  +os: List<&2, String>,
  +ns: List<&2, String>
) -> {Judging.Own.fits(os, ns) == True{}: Bool} -> {os == ns: List<&2, String>}:
  e => Shared.Eq.sound(
    ~List<&2, String>,
    ~Ledgers.Owners.is_eq,
    Ledgers.Owners.laws(),
    os,
    ns
  )(
    Shared.List.all.if_rest(
      Bool.not(List.is_empty(&2, String, os)),
      u => Ledgers.Owners.is_eq(os, ns)
    )(e)
  )

# Takes.at once whether the node holds the groups is known (b)
def Takes.held(
  os: List<&2, String>,
  ns: List<&2, String>,
  b: Bool
) -> {
  Shared.Maybe.when(Bool, b, u => Some{Judging.Own.fits(os, ns)}) == Some{True{}}: Maybe<&2, Bool>
} -> {os == ns: List<&2, String>}:
  match b:
    case False{}:
      e => Empty.absurd({os == ns: List<&2, String>}, Shared.Maybe.none_ne_some(Bool, True{}, e))
    case True{}:
      e => Fits.same(os, ns)(Shared.Maybe.some_inj(Bool, Judging.Own.fits(os, ns), True{}, e))

# Own.takes_inside once whether the Own may name its version is known (m)
def Takes.at(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  g: String,
  os: List<&2, String>,
  m: Maybe<&2, Bool>
) -> {
  Maybe.bind(
    &2,
    Bool,
    Bool,
    m,
    k => Judging.Own.takes.at(s, h, g, os, k)
  )
    == Some{True{}}: Maybe<&2, Bool>
} -> {os == Judging.Group.nodes(s, h, g): List<&2, String>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {os == Judging.Group.nodes(s, h, g): List<&2, String>},
        Shared.Maybe.none_ne_some(Bool, True{}, e)
      )
    case Some{False{}}:
      e => Empty.absurd(
        {os == Judging.Group.nodes(s, h, g): List<&2, String>},
        Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e))
      )
    case Some{True{}}:
      Takes.held(os, Judging.Group.nodes(s, h, g), Judging.Groups.held(s, h))

def Spec.Own.takes_inside(s, r, l, g, at, os, h):
  Takes.at(s, Judging.Own.tree(s, l, at, h), g, os, Judging.Own.ok(s, r, l, at))

# Growth
# ------
# A node's ledger only grows: each operation keeps every entry that it held.

# the ledger of a node with a new ledger is that ledger
def Led.led(
  s: Replicas.Node<Basics.Ask>,
  l: Ledgers.State(Basics.Ask)
) -> {Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l)) == l: Ledgers.State(Basics.Ask)}:
  match s:
    case Replicas.Node{old, hs, ws, ks}:
      {==}

# a new head keeps the ledger
def Led.head(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head
) -> {
  Replicas.State.ledger(~Basics.Ask.machine(), 
    Sealing.State.head(s, c, h)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# new waiting requests keep the ledger
def Led.wait(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  Replicas.State.ledger(~Basics.Ask.machine(), 
    Sealing.Wait.set(s, c, qs)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a node grows to itself
def Grows.refl(s: Replicas.Node<Basics.Ask>) -> {Reading.Node.grows(s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(~Basics.Ask, ~Basics.Ask.is_eq, ~Basics.Ask.laws(), Replicas.State.ledger(~Basics.Ask.machine(), s))

# growth composes
def Grows.trans(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Replicas.Node<Basics.Ask>
) -> {
  Reading.Node.grows(a, b) == True{}: Bool
} -> {Reading.Node.grows(b, c) == True{}: Bool} -> {Reading.Node.grows(a, c) == True{}: Bool}:
  Ledgers.State.grows_trans(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    ~Basics.Ask.laws(),
    Replicas.State.ledger(~Basics.Ask.machine(), a),
    Replicas.State.ledger(~Basics.Ask.machine(), b),
    Replicas.State.ledger(~Basics.Ask.machine(), c)
  )

# a node with a new ledger grows when the ledger does
def Grows.led(
  s: Replicas.Node<Basics.Ask>,
  l: Ledgers.State(Basics.Ask),
  e: {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), l) == True{}: Bool
  }
) -> {Reading.Node.grows(s, Replicas.State.led(~Basics.Ask.machine(), s, l)) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Basics.Ask),
    Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l)),
    l,
    Led.led(s, l)
  ): {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), _) == True{}: Bool
  }
  e

# data only grows a node
def Grows.keep(
  +s: Replicas.Node<Basics.Ask>,
  +ds: List<&2, List<&2, U32>>
) -> {Reading.Node.grows(s, Replicas.State.keep(~Basics.Ask.machine(), s, ds)) == True{}: Bool}:
  Grows.led(
    s,
    Ledgers.State.put_datas(~Basics.Ask, ~Basics.Ask.is_eq, ds, Replicas.State.ledger(~Basics.Ask.machine(), s)),
    Ledgers.State.put_datas_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      ds,
      Replicas.State.ledger(~Basics.Ask.machine(), s)
    )
  )

# the work m, if any, is on a node that grew from s
def Work.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Work<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Replicas.Work{s2, h}}:
      Reading.Node.grows(s, s2)

# the node m, if any, grew from s
def State.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Node<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Reading.Node.grows(s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  s: Replicas.Node<Basics.Ask>,
  -s2: Replicas.Node<Basics.Ask>,
  b: Bool,
  g: {Reading.Node.grows(s, s2) == True{}: Bool}
) -> {State.after(s, Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{s2})) == True{}: Bool}:
  match b:
    case True{}:
      g
    case False{}:
      {==}

# data that a node puts and reads back only grows it
def Put.grows(
  +s: Replicas.Node<Basics.Ask>,
  +ds: List<&2, List<&2, U32>>
) -> {State.after(s, Replicas.State.put(~Basics.Ask.machine(), s, ds)) == True{}: Bool}:
  Put.grows.if(
    s,
    Replicas.State.keep(~Basics.Ask.machine(), s, ds),
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ds), ds),
    Grows.keep(s, ds)
  )

# a work on a node that grew
def Work.on.grows(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Work.after(s, Replicas.Work.on(~Basics.Ask.machine(), m, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a new subtree only grows a node
def Work.of.grows(
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Trees.Put>
) -> {Work.after(s, Replicas.Work.of(~Basics.Ask.machine(), s, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, +ws}}:
      Work.on.grows(s, Replicas.State.put(~Basics.Ask.machine(), s, ws), Some{h})(Put.grows(s, ws))

# a key set in a tree only grows a node
def Set.grows(
  +s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(s, Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, k, x)) == True{}: Bool}:
  Work.of.grows(s, Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x))

# the run m, if any, is on a node that grew from s
def Run.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Stepping.Run>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Stepping.Run{s2, t}}:
      Reading.Node.grows(s, s2)

# a run is on its own node
def After.self(r: Stepping.Run) -> {Run.after(Stepping.Run.state(r), Some{r}) == True{}: Bool}:
  match r:
    case Stepping.Run{s, t}:
      Grows.refl(s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Stepping.Run>,
  e1: {Reading.Node.grows(a, b) == True{}: Bool},
  e2: {Run.after(b, m) == True{}: Bool}
) -> {Run.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{s2, t}}:
      Grows.trans(a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  s: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Stepping.Run>,
  f: Stepping.Run -> Maybe<&2, Stepping.Run>,
  hm: {Run.after(s, m) == True{}: Bool},
  hf: @r: Stepping.Run -> {Run.after(Stepping.Run.state(r), f(r)) == True{}: Bool}
) -> {Run.after(s, Maybe.bind(&2, Stepping.Run, Stepping.Run, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{+s2, +t}}:
      After.trans(s, s2, f(Stepping.Run{s2, t}), hm, hf(Stepping.Run{s2, t}))

# one of two runs, each on a node that grew
def After.when(
  s: Replicas.Node<Basics.Ask>,
  +b: Bool,
  -mx: Maybe<&2, Stepping.Run>,
  -my: Maybe<&2, Stepping.Run>,
  hx: {Run.after(s, mx) == True{}: Bool},
  hy: {Run.after(s, my) == True{}: Bool}
) -> {Run.after(s, Shared.Bool.when(Maybe<&2, Stepping.Run>, b, u => mx, u => my)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a work on a node that grew from b is on one that grew from a, when b grew
# from a
def Work.after.trans(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  e1: {Reading.Node.grows(a, b) == True{}: Bool},
  e2: {Work.after(b, m) == True{}: Bool}
) -> {Work.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Work{s3, h}}:
      Grows.trans(a, b, s3)(e1)(e2)

# a key set in a work on a node that grew from s is on a node that grew from s
def Work.set.after(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {
  Work.after(
    s,
    Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Replicas.Work.set(~Basics.Ask.machine(), w, k, x))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{Replicas.Work{+s2, +h}}:
      e => Work.after.trans(
        s,
        s2,
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s2, h}, k, x),
        e,
        Set.grows(s2, h, k, x)
      )

# the node of the work w
def Work.state(w: Replicas.Work<Basics.Ask>) -> Replicas.Node<Basics.Ask>:
  match w:
    case Replicas.Work{s, h}:
      s

# a work is on its own node
def Grown.self(w: Replicas.Work<Basics.Ask>) -> {Work.after(Work.state(w), Some{w}) == True{}: Bool}:
  match w:
    case Replicas.Work{s, h}:
      Grows.refl(s)

# a work, then a work from it, is on a node that grew
def Grown.bind(
  s: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  f: Replicas.Work<Basics.Ask> -> Maybe<&2, Replicas.Work<Basics.Ask>>,
  hm: {Work.after(s, m) == True{}: Bool},
  hf: @w: Replicas.Work<Basics.Ask> -> {Work.after(Work.state(w), f(w)) == True{}: Bool}
) -> {Work.after(s, Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Work{+s2, +h}}:
      Work.after.trans(s, s2, f(Replicas.Work{s2, h}), hm, hf(Replicas.Work{s2, h}))

# a work from a value that the node reads is on a node that grew
def Grown.with(
  -A: Data,
  s: Replicas.Node<Basics.Ask>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Replicas.Work<Basics.Ask>>,
  hk: @a: A -> {Work.after(s, k(a)) == True{}: Bool}
) -> {Work.after(s, Maybe.bind(&2, A, Replicas.Work<Basics.Ask>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# one of two works, each on a node that grew
def Grown.when(
  s: Replicas.Node<Basics.Ask>,
  +b: Bool,
  -mx: Maybe<&2, Replicas.Work<Basics.Ask>>,
  -my: Maybe<&2, Replicas.Work<Basics.Ask>>,
  hx: {Work.after(s, mx) == True{}: Bool},
  hy: {Work.after(s, my) == True{}: Bool}
) -> {
  Work.after(s, Shared.Bool.when(Maybe<&2, Replicas.Work<Basics.Ask>>, b, u => mx, u => my)) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a key set in a work only grows its node
def Grown.set(
  w: Replicas.Work<Basics.Ask>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(Work.state(w), Replicas.Work.set(~Basics.Ask.machine(), w, k, x)) == True{}: Bool}:
  match w:
    case Replicas.Work{s, h}:
      Set.grows(s, h, k, x)

# words kept in a work only grow its node
def Grown.keep(
  w: Replicas.Work<Basics.Ask>,
  +ns: List<&2, List<&2, U32>>
) -> {Work.after(Work.state(w), Replicas.Work.keep(~Basics.Ask.machine(), w, ns)) == True{}: Bool}:
  match w:
    case Replicas.Work{+s, h}:
      Work.on.grows(s, Replicas.State.put(~Basics.Ask.machine(), s, ns), h)(Put.grows(s, ns))

# a place added to a version vector only grows a node
def Grown.vector.add(
  w: Replicas.Work<Basics.Ask>,
  +c: Ledgers.Chain,
  +p: Basics.Place
) -> {Work.after(Work.state(w), Judging.Vector.add(w, c, p)) == True{}: Bool}:
  match w:
    case Replicas.Work{+s, +h}:
      Grown.when(
        s,
        Basics.Place.covered(Basics.Node.vector(s, h, c), p),
        Some{Replicas.Work{s, h}},
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.vector(c), Basics.Place.code(p)),
        Grows.refl(s),
        Set.grows(s, h, Basics.Key.vector(c), Basics.Place.code(p))
      )

# an entry added to a version vector only grows a node
def Grown.vector.add.if(
  +w: Replicas.Work<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Place>
) -> {Work.after(Work.state(w), Judging.Vector.add.if(w, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grown.self(w)
    case Some{+p}:
      Grown.when(
        Work.state(w),
        Ledgers.Chain.is_eq(Basics.Place.chain(p), c),
        Some{w},
        Judging.Vector.add(w, Basics.Place.chain(p), p),
        Grown.self(w),
        Grown.vector.add(w, Basics.Place.chain(p), p)
      )

# the entries added to a version vector only grow a node
def Grown.vector.adds(
  +s: Replicas.Node<Basics.Ask>,
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Work.after(s, Judging.Vector.adds(bs, c, m)) == True{}: Bool}:
  match bs:
    case Nil{}:
      e => e
    case Con{+b, r}:
      e => Grown.vector.adds(
        s,
        r,
        c,
        Maybe.bind(
          &2,
          Replicas.Work<Basics.Ask>,
          Replicas.Work<Basics.Ask>,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b))
        )
      )(
        Grown.bind(
          s,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b)),
          e,
          +w => Grown.vector.add.if(w, c, Judging.Vector.entry(b))
        )
      )

# a version joined to a version vector only grows a node
def Grown.vector.joined(
  +s: Replicas.Node<Basics.Ask>,
  +s0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Work.after(s, Judging.Vector.joined(s0, c, v, m)) == True{}: Bool}:
  e => Grown.bind(
    s,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s0, Basics.Node.root_of(s0, Some{v})),
      c,
      m
    ),
    w => Judging.Vector.add.if(w, c, Basics.Node.place(s0, v)),
    Grown.vector.adds(
      s,
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s0, Basics.Node.root_of(s0, Some{v})),
      c,
      m
    )(e),
    +w => Grown.vector.add.if(w, c, Basics.Node.place(s0, v))
  )

# what a merge keeps of a resource only grows a node
def Grown.merge.put(
  +f: Ledgers.Id,
  +n: Resources.Name,
  +o: Maybe<&2, Ropes.Root>,
  p: Judging.Pick,
  +w: Replicas.Work<Basics.Ask>
) -> {Work.after(Work.state(w), Judging.Merge.put(f, n, o, p, w)) == True{}: Bool}:
  match p:
    case Judging.Pick.Take{m}:
      Grown.set(w, Basics.Key.res(n), Basics.Res.code(m))
    case Judging.Pick.Make{+x}:
      Grown.bind(
        Work.state(w),
        Replicas.Work.keep(~Basics.Ask.machine(), w, Ropes.Put.nodes(Basics.Bytes.rope(x))),
        w2 => Replicas.Work.set(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(n),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(x))})
        ),
        Grown.keep(w, Ropes.Put.nodes(Basics.Bytes.rope(x))),
        w2 => Grown.set(
          w2,
          Basics.Key.res(n),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(x))})
        )
      )
    case Judging.Pick.Clash{}:
      Grown.bind(
        Work.state(w),
        Replicas.Work.set(~Basics.Ask.machine(), w, Basics.Key.res(n), Basics.Res.code(o)),
        y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), Judging.Clash.code(f)),
        Grown.set(w, Basics.Key.res(n), Basics.Res.code(o)),
        y => Grown.set(y, Basics.Key.clash(n), Judging.Clash.code(f))
      )

# a resource merged only grows a node
def Grown.merge.one(
  s0: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  +w: Replicas.Work<Basics.Ask>
) -> {Work.after(Work.state(w), Judging.Merge.one(s0, f, n, b, o, t, w)) == True{}: Bool}:
  Grown.with(
    Judging.Pick,
    Work.state(w),
    Judging.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s0, b, o, t),
    p => Judging.Merge.put(f, n, o, p, w),
    p => Grown.merge.put(f, n, o, p, w)
  )

# the resources merged only grow a node
def Grown.merge.all(
  +s: Replicas.Node<Basics.Ask>,
  +s0: Replicas.Node<Basics.Ask>,
  +f: Ledgers.Id,
  ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Work.after(s, Judging.Merge.all(s0, f, ns, hb, ho, ht, m)) == True{}: Bool}:
  match ns:
    case Nil{}:
      e => e
    case Con{+n, r}:
      e => Grown.merge.all(
        s,
        s0,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(
          &2,
          Replicas.Work<Basics.Ask>,
          Replicas.Work<Basics.Ask>,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Work<Basics.Ask>,
            Basics.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Basics.Ask>,
              Basics.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Basics.Ask>,
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w)
              )
            )
          )
        )
      )(
        Grown.bind(
          s,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Work<Basics.Ask>,
            Basics.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Basics.Ask>,
              Basics.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Basics.Ask>,
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w)
              )
            )
          ),
          e,
          +w => Grown.with(
            Maybe<&2, Ropes.Root>,
            Work.state(w),
            Basics.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Basics.Ask>,
              Basics.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Basics.Ask>,
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w)
              )
            ),
            +b => Grown.with(
              Maybe<&2, Ropes.Root>,
              Work.state(w),
              Basics.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Basics.Ask>,
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w)
              ),
              +o => Grown.with(
                Maybe<&2, Ropes.Root>,
                Work.state(w),
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w),
                x => Grown.merge.one(s0, f, n, b, o, x, w)
              )
            )
          )
        )
      )

# the trees of a merge are on a node that grew
def Grown.merge.work(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> {Work.after(s, Judging.Merge.work(s, c, from, h)) == True{}: Bool}:
  Grown.vector.joined(
    s,
    s,
    c,
    from,
    Judging.Merge.all(
      s,
      from,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
      h,
      Basics.Node.root_of(s, Some{from}),
      Some{Replicas.Work{s, h}}
    )
  )(
    Grown.merge.all(
      s,
      s,
      from,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
      h,
      Basics.Node.root_of(s, Some{from}),
      Some{Replicas.Work{s, h}}
    )(Grows.refl(s))
  )

# the trees of a move are on a node that grew
def Grown.move.work(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +to: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> {Work.after(s, Judging.Move.work(s, c, to, h)) == True{}: Bool}:
  Grown.vector.joined(
    s,
    s,
    c,
    to,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Basics.Node.root_of(s, Some{to})}}
    )
  )(
    Grown.vector.adds(
      s,
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Basics.Node.root_of(s, Some{to})}}
    )(Grows.refl(s))
  )

# the trees of a resolve are on a node that grew
def Grown.resolve.work(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +m: Maybe<&2, Ropes.Root>
) -> {Work.after(s, Judging.Resolve.work(s, h, n, m)) == True{}: Bool}:
  Grown.bind(
    s,
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), []),
    Set.grows(s, h, Basics.Key.res(n), Basics.Res.code(m)),
    y => Grown.set(y, Basics.Key.clash(n), [])
  )

# the trees of a group are on a node that grew
def Grown.group.work(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  +ms: List<&2, Basics.Member>
) -> {Work.after(s, Judging.Group.work(s, h, g, ms)) == True{}: Bool}:
  Grown.bind(
    s,
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.group(g), Basics.Members.code(ms, [])),
    +w => Shared.Bool.when(
      Maybe<&2, Replicas.Work<Basics.Ask>>,
      List.contains(~String, ~String.eq, Judging.Group.names(s, h), g),
      u => Some{w},
      u => Replicas.Work.set(~Basics.Ask.machine(), 
        w,
        Basics.Key.groups(),
        Ledgers.Owners.code(g <> Judging.Group.names(s, h), [])
      )
    ),
    Set.grows(s, h, Basics.Key.group(g), Basics.Members.code(ms, [])),
    +w => Grown.when(
      Work.state(w),
      List.contains(~String, ~String.eq, Judging.Group.names(s, h), g),
      Some{w},
      Replicas.Work.set(~Basics.Ask.machine(), 
        w,
        Basics.Key.groups(),
        Ledgers.Owners.code(g <> Judging.Group.names(s, h), [])
      ),
      Grown.self(w),
      Grown.set(w, Basics.Key.groups(), Ledgers.Owners.code(g <> Judging.Group.names(s, h), []))
    )
  )

# the first tree of a branch is on a node that grew
def Grown.make.branch(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Ledgers.Id>
) -> {Work.after(s, Judging.Make.branch(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+v}:
      Grown.vector.joined(
        s,
        s,
        c,
        v,
        Some{Replicas.Work{s, Basics.Node.root_of(s, Some{v})}}
      )(Grows.refl(s))

# the first tip m of a branch, if any, is on a node that grew from s
def Made.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Judging.Made>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Judging.Made{t, s2}}:
      Reading.Node.grows(s, s2)

# a first tip on a work is on a node that grew
def Grown.made.put(
  s: Replicas.Node<Basics.Ask>,
  t: Replicas.Tip,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {Work.after(s, m) == True{}: Bool} -> {Made.after(s, Judging.Made.put(t, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Replicas.Work{s2, l}}:
      e => e

# the first tip of a new branch is on a node that grew
def Grown.make.first(
  +s: Replicas.Node<Basics.Ask>,
  start: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +os: List<&2, String>
) -> {
  Work.after(s, start) == True{}: Bool
} -> {Made.after(s, Judging.Make.first(start, os)) == True{}: Bool}:
  match start:
    case None{}:
      e => {==}
    case Some{Replicas.Work{+s2, +h}}:
      e =>
        +t = {Replicas.Tip{h, None{}, 0, os}: Replicas.Tip}
        Grown.made.put(
          s,
          t,
          Replicas.Work.keep(~Basics.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)])
        )(
          Work.after.trans(
            s,
            s2,
            Replicas.Work.keep(~Basics.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)]),
            e,
            Grown.keep(Replicas.Work{s2, h}, [Replicas.Tip.words(t)])
          )
        )

# the verdict m, if any, holds a node that grew from s
def Verdict.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Verdict<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Replicas.Verdict.Stale{}}:
      True{}
    case Some{Replicas.Verdict.Taken{Replicas.Work{s2, h}}}:
      Reading.Node.grows(s, s2)

# a verdict that takes a work holds its node
def Verdict.take(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {Work.after(s, m) == True{}: Bool} -> {Verdict.after(s, Replicas.Work.take(~Basics.Ask.machine(), m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Replicas.Work{s2, h}}:
      e => e

# a verdict after a verdict holds a node that grew
def Verdict.then(
  s: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  hk: {Verdict.after(s, k(Unit{})) == True{}: Bool}
) -> {Verdict.after(s, Judging.Judge.then(m, k)) == True{}: Bool}:
  match m:
    case Some{True{}}:
      hk
    case Some{False{}}:
      {==}
    case None{}:
      {==}

# a verdict under a condition holds a node that grew
def Verdict.when(
  s: Replicas.Node<Basics.Ask>,
  +b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  hk: {Verdict.after(s, k(Unit{})) == True{}: Bool}
) -> {Verdict.after(s, Judging.Judge.when(b, k)) == True{}: Bool}:
  match b:
    case True{}:
      hk
    case False{}:
      {==}

# a verdict on whole trees holds a node that grew
def Verdict.whole(
  s: Replicas.Node<Basics.Ask>,
  +b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  hk: {Verdict.after(s, k(Unit{})) == True{}: Bool}
) -> {Verdict.after(s, Judging.Judge.whole(b, k)) == True{}: Bool}:
  match b:
    case True{}:
      hk
    case False{}:
      {==}

# a verdict from a value that the node reads holds a node that grew
def Verdict.with(
  -A: Data,
  s: Replicas.Node<Basics.Ask>,
  +ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  hk: @a: A -> {Verdict.after(s, k(a)) == True{}: Bool}
) -> {Verdict.after(s, Maybe.bind(&2, A, Replicas.Verdict<Basics.Ask>, ma, k)) == True{}: Bool}:
  match ma:
    case None{}:
      {==}
    case Some{a}:
      hk(a)

# the verdict on a write holds a node that grew
def Verdict.write(
  +s: Replicas.Node<Basics.Ask>,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Basics.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> {Verdict.after(s, Judging.Judge.write(s, n, base, c, h)) == True{}: Bool}:
  Verdict.then(
    s,
    Judging.Judge.ready_maybe(s, base),
    u => Judging.Judge.then(
      Judging.Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Verdict<Basics.Ask>,
        Basics.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Basics.Res.find(s, Basics.Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Judging.Content.find(s, n, c),
            m => Judging.Judge.when(
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )
            )
          )
        )
      )
    ),
    Verdict.then(
      s,
      Judging.Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Verdict<Basics.Ask>,
        Basics.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Basics.Res.find(s, Basics.Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Judging.Content.find(s, n, c),
            m => Judging.Judge.when(
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )
            )
          )
        )
      ),
      Verdict.with(
        Maybe<&2, Ropes.Root>,
        s,
        Basics.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Basics.Res.find(s, Basics.Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Judging.Content.find(s, n, c),
            m => Judging.Judge.when(
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )
            )
          )
        ),
        +a => Verdict.with(
          Maybe<&2, Ropes.Root>,
          s,
          Basics.Res.find(s, Basics.Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Judging.Content.find(s, n, c),
            m => Judging.Judge.when(
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )
            )
          ),
          +b => Verdict.with(
            Maybe<&2, Ropes.Root>,
            s,
            Judging.Content.find(s, n, c),
            m => Judging.Judge.when(
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )
            ),
            +m => Verdict.when(
              s,
              Basics.Roots.same(a, b),
              x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              ),
              Verdict.take(
                s,
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )(Set.grows(s, h, Basics.Key.res(n), Basics.Res.code(m)))
            )
          )
        )
      )
    )
  )

# the verdict on a resolve holds a node that grew
def Verdict.resolve(
  +s: Replicas.Node<Basics.Ask>,
  r: Ledgers.Id,
  b: String,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Basics.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> {Verdict.after(s, Judging.Judge.resolve(s, r, b, k, n, c, h)) == True{}: Bool}:
  Verdict.then(
    s,
    Judging.Judge.ready(s, k),
    u => Judging.Judge.then(
      Judging.Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Replicas.Verdict<Basics.Ask>,
        Judging.Clash.find(s, h, n, Judging.Merge.from_on(Replicas.Node.asked(~Basics.Ask.machine(), s, k), r, b)),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Judging.Content.find(s, n, c),
          m => Judging.Judge.when(open, x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m)))
        )
      )
    ),
    Verdict.then(
      s,
      Judging.Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Replicas.Verdict<Basics.Ask>,
        Judging.Clash.find(s, h, n, Judging.Merge.from_on(Replicas.Node.asked(~Basics.Ask.machine(), s, k), r, b)),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Judging.Content.find(s, n, c),
          m => Judging.Judge.when(open, x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m)))
        )
      ),
      Verdict.with(
        Bool,
        s,
        Judging.Clash.find(s, h, n, Judging.Merge.from_on(Replicas.Node.asked(~Basics.Ask.machine(), s, k), r, b)),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Judging.Content.find(s, n, c),
          m => Judging.Judge.when(open, x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m)))
        ),
        +open => Verdict.with(
          Maybe<&2, Ropes.Root>,
          s,
          Judging.Content.find(s, n, c),
          m => Judging.Judge.when(open, x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m))),
          +m => Verdict.when(
            s,
            open,
            x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m)),
            Verdict.take(s, Judging.Resolve.work(s, h, n, m))(Grown.resolve.work(s, h, n, m))
          )
        )
      )
    )
  )

# the verdict on an Own holds a node that grew
def Verdict.own(
  +s: Replicas.Node<Basics.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> {Verdict.after(s, Judging.Own.change(s, r, l, g, at, os, h)) == True{}: Bool}:
  Verdict.then(
    s,
    Judging.Own.takes(s, r, l, g, at, os, h),
    u => Replicas.Work.take(~Basics.Ask.machine(), 
      Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.owner(), Codes.Code.text(g, []))
    ),
    Verdict.take(
      s,
      Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.owner(), Codes.Code.text(g, []))
    )(Set.grows(s, h, Basics.Key.owner(), Codes.Code.text(g, [])))
  )

# the verdict on a change holds a node that grew from the node that judged it
def Verdict.change(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Basics.Change,
  +h: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>
) -> {Verdict.after(s, Judging.Judge.change(s, r, l, c, h, os)) == True{}: Bool}:
  match l c:
    case None{} Basics.Change.Group{+g, +ms}:
      Verdict.when(
        s,
        Bool.not(Judging.Group.loops.any(s, h, g, ms)),
        u => Replicas.Work.take(~Basics.Ask.machine(), Judging.Group.work(s, h, g, ms)),
        Verdict.take(s, Judging.Group.work(s, h, g, ms))(Grown.group.work(s, h, g, ms))
      )
    case None{} Basics.Change.Key{+n, +k}:
      Verdict.take(
        s,
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.seal(n), Hashes.Hash.code(k, []))
      )(Set.grows(s, h, Basics.Key.seal(n), Hashes.Hash.code(k, [])))
    case +w Basics.Change.Own{g, at, os2}:
      Verdict.own(s, r, w, g, at, os2, h)
    case Some{b} Basics.Change.Write{n, base, c2}:
      Verdict.write(s, n, base, c2, h)
    case Some{+b} Basics.Change.Resolve{k, n, c2}:
      Verdict.resolve(s, r, b, k, n, c2, h)
    case Some{+b} Basics.Change.Merge{+from}:
      Verdict.then(
        s,
        Judging.Judge.ready(s, from),
        u => Judging.Judge.whole(
          Judging.Whole.both(s, h, Basics.Node.root_of(s, Some{from})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h))
        ),
        Verdict.whole(
          s,
          Judging.Whole.both(s, h, Basics.Node.root_of(s, Some{from})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)),
          Verdict.take(
            s,
            Judging.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)
          )(Grown.merge.work(s, Replicas.Line.chain(r, Some{b}), from, h))
        )
      )
    case Some{+b} Basics.Change.Move{+to}:
      Verdict.then(
        s,
        Judging.Judge.ready(s, to),
        u => Judging.Judge.whole(
          Judging.Whole.both(s, h, Basics.Node.root_of(s, Some{to})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h))
        ),
        Verdict.whole(
          s,
          Judging.Whole.both(s, h, Basics.Node.root_of(s, Some{to})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)),
          Verdict.take(
            s,
            Judging.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)
          )(Grown.move.work(s, Replicas.Line.chain(r, Some{b}), to, h))
        )
      )
    case None{} Basics.Change.Write{n, base, c2}:
      {==}
    case None{} Basics.Change.Resolve{k, n, c2}:
      {==}
    case None{} Basics.Change.Merge{from}:
      {==}
    case None{} Basics.Change.Move{to}:
      {==}
    case None{} Basics.Change.Mark{m, d}:
      {==}
    case None{} Basics.Change.Branch{b, at}:
      {==}
    case Some{b} Basics.Change.Group{g, ms}:
      {==}
    case Some{b} Basics.Change.Key{n, k}:
      {==}
    case Some{b} Basics.Change.Mark{m, d}:
      {==}
    case Some{b} Basics.Change.Branch{b2, at}:
      {==}

# the run of a new log is on a node that grew
def Run.logged.grows(
  s: Replicas.Node<Basics.Ask>,
  t: Replicas.Tip,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  e: {Work.after(s, m) == True{}: Bool}
) -> {Run.after(s, Stepping.Run.logged(t, m)) == True{}: Bool}:
  match t m:
    case x None{}:
      {==}
    case Replicas.Tip{c, old, n, os} Some{Replicas.Work{s2, l}}:
      e

# Add.grows once the value m of the key is known
def Add.at.grows(
  r: Stepping.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.add.at(r, k, x, m)) == True{}: Bool}:
  match r m:
    case Stepping.Run{+s, +t} None{}:
      Run.logged.grows(
        s,
        t,
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, Replicas.Tip.log(t)}, k, x),
        Set.grows(s, Replicas.Tip.log(t), k, x)
      )
    case y Some{old}:
      {==}

# a new key in a run's log only grows its node
def Add.grows(
  +r: Stepping.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.add(r, k, x)) == True{}: Bool}:
  Add.at.grows(
    r,
    k,
    x,
    Replicas.Node.get(~Basics.Ask.machine(), Stepping.Run.state(r), Replicas.Tip.log(Stepping.Run.tip(r)), k)
  )

# a run one version on is on its own node
def Next.grows(
  r: Stepping.Run,
  own: Maybe<&2, List<&2, String>>
) -> {Run.after(Stepping.Run.state(r), Some{Stepping.Run.next(r, own)}) == True{}: Bool}:
  match r:
    case Stepping.Run{s, t}:
      Grows.refl(s)

# a refused request only grows a run's node
def Stale.grows(
  r: Stepping.Run,
  i: Ledgers.Id
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.stale(r, i)) == True{}: Bool}:
  Add.grows(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.taken(r, i, own)) == True{}: Bool}:
  +n = Replicas.Tip.count(Stepping.Run.tip(r))
  After.bind(
    Stepping.Run.state(r),
    Stepping.Run.add(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Stepping.Run,
      Stepping.Run,
      Stepping.Run.add(
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Stepping.Run.tip(r1))})
      ),
      r2 => Some{Stepping.Run.next(r2, own)}
    ),
    Add.grows(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
    +r1 => After.bind(
      Stepping.Run.state(r1),
      Stepping.Run.add(
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Stepping.Run.tip(r1))})
      ),
      r2 => Some{Stepping.Run.next(r2, own)},
      Add.grows(
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Stepping.Run.tip(r1))})
      ),
      r2 => Next.grows(r2, own)
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Replicas.Verdict<Basics.Ask>>
) -> {
  Verdict.after(Stepping.Run.state(r), m) == True{}: Bool
} -> {Run.after(Stepping.Run.state(r), Stepping.Step.judged(r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Replicas.Verdict.Stale{}}:
      g => Stale.grows(r, i)
    case Some{Replicas.Verdict.Taken{Replicas.Work{+s2, +h}}}:
      g => After.trans(
        Stepping.Run.state(r),
        s2,
        Stepping.Step.taken(Stepping.Run.over(r, s2, h), i, own),
        g,
        Taken.grows(Stepping.Run.over(r, s2, h), i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Replicas.Version>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.marked(r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(
        Stepping.Run.state(r),
        Stepping.Run.add(r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(x), [])),
        r2 => Stepping.Step.taken(r2, i, None{}),
        Add.grows(r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(x), [])),
        r2 => Taken.grows(r2, i, None{})
      )

# a request for a mark only grows a run's node
def Mark.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +m: String
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.mark(r, i, m)) == True{}: Bool}:
  +s = Stepping.Run.state(r)
  +t = Stepping.Run.tip(r)
  +n = Replicas.Tip.count(t)
  After.when(
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Replicas.Line.mark(~Basics.Ask.machine(), s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Stepping.Step.marked(r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Stepping.Step.stale(r, i),
    Marked.grows(r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Stale.grows(r, i)
  )

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Judging.Made>
) -> {
  Made.after(Stepping.Run.state(r), m) == True{}: Bool
} -> {Run.after(Stepping.Run.state(r), Stepping.Branch.made(r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Judging.Made{+t, +s2}}:
      g =>
        +r1 = {Stepping.Run.over(r, s2, Replicas.Tip.content(Stepping.Run.tip(r))): Stepping.Run}
        After.trans(
          Stepping.Run.state(r),
          s2,
          Maybe.bind(
            &2,
            Stepping.Run,
            Stepping.Run,
            Stepping.Run.add(r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Stepping.Step.taken(r2, i, None{})
          ),
          g,
          After.bind(
            s2,
            Stepping.Run.add(r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Stepping.Step.taken(r2, i, None{}),
            Add.grows(r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Taken.grows(r2, i, None{})
          )
        )

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> {Run.after(Stepping.Run.state(r), Stepping.Branch.ready(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{False{}}:
      Stale.grows(r, i)
    case Some{True{}}:
      After.when(
        Stepping.Run.state(r),
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Stepping.Run.state(r),
          Basics.Node.root_of(Stepping.Run.state(r), at)
        ),
        Stepping.Branch.made(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Stepping.Run.tip(r))
          )
        ),
        None{},
        Branch.made.grows(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Stepping.Run.tip(r))
          )
        )(
          Grown.make.first(
            Stepping.Run.state(r),
            Judging.Make.branch(Stepping.Run.state(r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Stepping.Run.tip(r))
          )(Grown.make.branch(Stepping.Run.state(r), Replicas.Line.chain(st, Some{b}), at))
        ),
        {==}
      )

# a request for a branch only grows a run's node
def Branch.new.grows(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Branch.new(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Some{x}}:
      Stale.grows(r, i)
    case Some{None{}}:
      Branch.ready.grows(r, i, st, b, at, Judging.Judge.ready_maybe(Stepping.Run.state(r), at))

# On.grows once it is known how the line takes the change (w)
def On.of.grows(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.on.of(r, i, st, l, ch, w)) == True{}: Bool}:
  match w:
    case Stepping.Route.Mark{a}:
      Mark.grows(r, i, a)
    case Stepping.Route.Branch{+a, b}:
      Branch.new.grows(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(~Basics.Ask.machine(), 
          Stepping.Run.state(r),
          Replicas.Tip.log(Stepping.Run.tip(r)),
          Replicas.Log.start(a)
        )
      )
    case Stepping.Route.Judge{}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          l,
          ch,
          Replicas.Tip.content(Stepping.Run.tip(r)),
          Replicas.Tip.owners(Stepping.Run.tip(r))
        )
      )(
        Verdict.change(
          Stepping.Run.state(r),
          st,
          l,
          ch,
          Replicas.Tip.content(Stepping.Run.tip(r)),
          Replicas.Tip.owners(Stepping.Run.tip(r))
        )
      )

# a change of a line only grows a run's node
def On.grows(
  r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  On.of.grows(r, i, st, l, ch, Stepping.Route.of(l, ch))

# a request only grows a run's node
def Change.grows(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Basics.Ask
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.change(r, c, i, q)) == True{}: Bool}:
  match q:
    case Basics.Ask.Start{os}:
      Stale.grows(r, i)
    case Basics.Ask.On{+st, +l, ch}:
      After.when(
        Stepping.Run.state(r),
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Stepping.Step.stale(r, i),
        On.grows(r, i, st, l, ch),
        Stale.grows(r, i)
      )

# a request that the node holds or not only grows a run's node
def Asked.grows(
  r: Stepping.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.asked(r, c, i, a)) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{Ledgers.Asked{t, q}}:
      Change.grows(r, c, i, q)

# a request that the log holds or not only grows a run's node
def Fresh.grows(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +o: Maybe<&2, Replicas.Out>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.fresh(r, c, i, o)) == True{}: Bool}:
  match o:
    case Some{x}:
      After.self(r)
    case None{}:
      Asked.grows(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Stepping.Run.state(r), i))

# one request of a step only grows a run's node
def One.grows(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.one(r, c, i)) == True{}: Bool}:
  Fresh.grows(r, c, i, Replicas.Line.out(~Basics.Ask.machine(), Stepping.Run.state(r), Stepping.Run.tip(r), i))

# the requests of a step only grow a run's node
def All.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Stepping.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Run.after(s, Stepping.Step.all(c, qs, m)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.grows(
        s,
        c,
        rest,
        Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, i))
      )(After.bind(s, m, r => Stepping.Step.one(r, c, i), h, r => One.grows(r, c, i)))

# a step only grows a node: its run is on a node that keeps every entry
def Run.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  qs: List<&2, Ledgers.Id>
) -> {Run.after(s, Stepping.Step.run(s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Stepping.Run{s, t}})(Grows.refl(s))

# the run of picked requests, with one more request or not
def Add.run(
  b: Bool,
  i: Ledgers.Id,
  p: Stepping.Picked
) -> {Stepping.Picked.run(Stepping.Picked.add(b, i, p)) == Stepping.Picked.run(p): Stepping.Run}:
  match p:
    case Stepping.Picked{r, qs}:
      {==}

# the run m, if any, else r, is on a node that grew from that of r
def Default.run.grows(
  r: Stepping.Run,
  m: Maybe<&2, Stepping.Run>
) -> {
  Run.after(Stepping.Run.state(r), m) == True{}: Bool
} -> {
  Reading.Node.grows(
    Stepping.Run.state(r),
    Stepping.Run.state(Maybe.default(&2, Stepping.Run, m, r))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(Stepping.Run.state(r))
    case Some{Stepping.Run{s2, t}}:
      e => e

# the run of the requests that can run is on a node that grew
def Some.grows(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Stepping.Run
) -> {
  Run.after(
    Stepping.Run.state(r),
    Some{Stepping.Picked.run(Stepping.Step.some(c, qs, r))}
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      After.self(r)
    case Con{+i, +rest}:
      +m = Stepping.Step.one(r, c, i)
      +r2 = Maybe.default(&2, Stepping.Run, m, r)
      %Equal.sym(
        Stepping.Run,
        Stepping.Picked.run(
          Stepping.Picked.add(
            Maybe.is_some(&2, Stepping.Run, m),
            i,
            Stepping.Step.some(c, rest, r2)
          )
        ),
        Stepping.Picked.run(Stepping.Step.some(c, rest, r2)),
        Add.run(Maybe.is_some(&2, Stepping.Run, m), i, Stepping.Step.some(c, rest, r2))
      ): {Run.after(Stepping.Run.state(r), Some{_}) == True{}: Bool}
      After.trans(
        Stepping.Run.state(r),
        Stepping.Run.state(r2),
        Some{Stepping.Picked.run(Stepping.Step.some(c, rest, r2))},
        Default.run.grows(r, m)(One.grows(r, c, i)),
        Some.grows(c, rest, r2)
      )

# a run that is kept when b holds is on a node that grew, when it is
def Fit.when.grows(
  -s: Replicas.Node<Basics.Ask>,
  b: Bool,
  -r: Stepping.Run,
  e: {Run.after(s, Some{r}) == True{}: Bool}
) -> {Run.after(s, Shared.Maybe.when(Stepping.Run, b, u => Some{r})) == True{}: Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# a run that fits a tip is on a node that grew, when the run is
def Plan.fit.grows(
  -s: Replicas.Node<Basics.Ask>,
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Stepping.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Run.after(s, Sealing.Plan.fit(after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Stepping.Run{s2, t2}}:
      e => Fit.when.grows(
        s,
        Sealing.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        Stepping.Run{s2, t2},
        e
      )

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  -s: Replicas.Node<Basics.Ask>,
  b: Bool,
  -x: Sealing.Plan,
  -y: Sealing.Plan,
  hx: {Run.after(s, Sealing.Plan.run(x)) == True{}: Bool},
  hy: {Run.after(s, Sealing.Plan.run(y)) == True{}: Bool}
) -> {
  Run.after(s, Sealing.Plan.run(Shared.Bool.when(Sealing.Plan, b, u => x, u => y))) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the run of the plan of an owner that proposes freely is on a node that grew
def Plan.own.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  t: Replicas.Tip,
  -from: List<&2, String>
) -> {Run.after(s, Sealing.Plan.run(Sealing.Plan.own(s, c, t, from))) == True{}: Bool}:
  Some.grows(c, Sealing.Cast.mine(s, Sealing.Wait.of(s, c)), Stepping.Run{s, t})

# the run of the plan for a step that another ballot names is on a node that
# grew
def Plan.copy.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  -from: List<&2, String>
) -> {Run.after(s, Sealing.Plan.run(Sealing.Plan.copy(s, c, t, th, m, from))) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Plan.when.grows(
        s,
        List.all.if(u => Sealing.Cast.all_mine(s, qs), Sealing.Root.same(before, th)),
        Sealing.Plan{qs, Sealing.Plan.fit(after, Stepping.Step.run(s, c, t, qs)), from},
        Sealing.Plan{[], None{}, []},
        Plan.fit.grows(s, after, Stepping.Step.run(s, c, t, qs))(Run.grows(s, c, t, qs)),
        {==}
      )

# the run of the plan of the proposer of a later round is on a node that grew
def Plan.later.grows(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Run.after(s, Sealing.Plan.run(Voting.Plan.later(s, c, w, t, th, os, from, m))) == True{}: Bool
}:
  match m:
    case None{}:
      Plan.when.grows(
        s,
        Voting.Owners.major(os, from),
        Sealing.Plan.own(s, c, t, from),
        Sealing.Plan{[], None{}, []},
        Plan.own.grows(s, c, t, from),
        {==}
      )
    case Some{Ledgers.Last{r, v}}:
      Plan.when.grows(
        s,
        Voting.Owners.major(os, from),
        Sealing.Plan.copy(s, c, t, th, Some{v}, from),
        Sealing.Plan{[], None{}, []},
        Plan.copy.grows(s, c, t, th, Some{v}, from),
        {==}
      )

# the run of the plan of the proposer is on a node that grew
def Plan.lead.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> {Run.after(s, Sealing.Plan.run(Voting.Plan.lead(s, c, w, t, th, os))) == True{}: Bool}:
  Plan.when.grows(
    s,
    Nat.is_eq(Voting.Where.round(w), 0n),
    Sealing.Plan.own(s, c, t, []),
    Voting.Plan.later(
      s,
      c,
      w,
      t,
      th,
      os,
      Voting.Passes.of(s, w, os),
      Voting.Passes.last(s, w, Voting.Passes.of(s, w, os))
    ),
    Plan.own.grows(s, c, t, []),
    Plan.later.grows(
      s,
      c,
      w,
      t,
      th,
      os,
      Voting.Passes.of(s, w, os),
      Voting.Passes.last(s, w, Voting.Passes.of(s, w, os))
    )
  )

# the run of the plan of another owner is on a node that grew
def Plan.follow.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> {Run.after(s, Sealing.Plan.run(Voting.Plan.follow(s, c, w, t, th, os, m))) == True{}: Bool}:
  match m:
    case Some{Ledgers.Act.Vote{+v, from}}:
      Plan.when.grows(
        s,
        Voting.Vote.allowed(s, w, os, v, from),
        Sealing.Plan.copy(s, c, t, th, Some{v}, from),
        Sealing.Plan{[], None{}, []},
        Plan.copy.grows(s, c, t, th, Some{v}, from),
        {==}
      )
    case Some{Ledgers.Act.Pass{l}}:
      {==}
    case None{}:
      {==}

# the run of what a node casts for is on a node that grew
def Plan.of.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Replicas.Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> {Run.after(s, Sealing.Plan.run(Voting.Plan.of(n, s, c, w, t, th, os, turn))) == True{}: Bool}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Plan.when.grows(
        s,
        String.eq(p, n),
        Voting.Plan.lead(s, c, w, t, th, os),
        Voting.Plan.follow(s, c, w, t, th, os, Voting.Cast.act(s, w, p)),
        Plan.lead.grows(s, c, w, t, th, os),
        Plan.follow.grows(s, c, w, t, th, os, Voting.Cast.act(s, w, p))
      )

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  x: Replicas.Node<Basics.Ask>,
  e: {Replicas.State.ledger(~Basics.Ask.machine(), x) == Replicas.State.ledger(~Basics.Ask.machine(), b): Ledgers.State(Basics.Ask)},
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {Reading.Node.grows(a, x) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Basics.Ask),
    Replicas.State.ledger(~Basics.Ask.machine(), x),
    Replicas.State.ledger(~Basics.Ask.machine(), b),
    e
  ): {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), a), _) == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  s: Replicas.Node<Basics.Ask>,
  b: Bool,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: {Reading.Node.grows(s, x) == True{}: Bool},
  hy: {Reading.Node.grows(s, y) == True{}: Bool}
) -> {Reading.Node.grows(s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a moved head keeps the ledger
def Led.moved(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  qs: List<&2, Ledgers.Id>
) -> {
  Replicas.State.ledger(~Basics.Ask.machine(), 
    Sealing.State.moved(s, c, h, qs)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  Replicas.State.ledger(~Basics.Ask.machine(), 
    Sealing.State.wait(s, c, i)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a node with the ledger of a node that grew from it grew
def Grows.back(
  s: Replicas.Node<Basics.Ask>,
  s3: Replicas.Node<Basics.Ask>,
  g: {Reading.Node.grows(s, s3) == True{}: Bool}
) -> {Reading.Node.grows(s, Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))) == True{}: Bool}:
  Grows.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3), g)

# new keys keep the ledger
def Led.keyed(
  s: Replicas.Node<Basics.Ask>,
  ks: Replicas.Keys
) -> {
  Replicas.State.ledger(~Basics.Ask.machine(), 
    Replicas.State.keyed(~Basics.Ask.machine(), s, ks)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, old}:
      {==}

# a ballot that a node accepts only grows it
def Accept.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Replicas.Keychain>
) -> {State.after(s, Sealing.Seal.accept.at(s, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Put.grows.if(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), 
          Replicas.State.led(~Basics.Ask.machine(), 
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Sealing.Keys.saw(
            Sealing.Keys.set(
              Replicas.State.keys(~Basics.Ask.machine(), s),
              Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
              Sealing.Keychain.next(c, b)
            ),
            Sealing.Ballot.at(b)
          )
        ),
        Sealing.Seal.fits(c, b),
        Grows.to(
          s,
          Replicas.State.led(~Basics.Ask.machine(), 
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Replicas.State.keyed(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Sealing.Keys.saw(
              Sealing.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
                Sealing.Keychain.next(c, b)
              ),
              Sealing.Ballot.at(b)
            )
          ),
          Led.keyed(
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Sealing.Keys.saw(
              Sealing.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
                Sealing.Keychain.next(c, b)
              ),
              Sealing.Ballot.at(b)
            )
          ),
          Grows.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b),
            Ledgers.State.add_grows(
              ~Basics.Ask,
              ~Basics.Ask.is_eq,
              ~Basics.Ask.laws(),
              Replicas.State.ledger(~Basics.Ask.machine(), s),
              Ledgers.Slot.of(b),
              Ledgers.Entry.Vote{b}
            )
          )
        )
      )

# the node m, if any, else s, grew from s when m did
def Default.grows(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Maybe.default(&2, Replicas.Node<Basics.Ask>, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{s2}:
      e => e

# a sealed ballot only grows a node
def Cast.seal.grows(
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Replicas.Keychain>
) -> {Reading.Node.grows(s, Sealing.Cast.seal(s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Replicas.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Sealing.Seal.secret(Sealing.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)), Sealing.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Sealing.Seal.secret(
            Sealing.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)),
            Sealing.Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.grows(
        s,
        Sealing.Seal.accept(s, b)
      )(
        Accept.at.grows(
          s,
          b,
          Sealing.Seal.chain(s, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )

# a ballot on a node that grew from a, which grew from s, only grows s
def Cast.vote.grows(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +w: Ledgers.Where,
  +n: String,
  +a0: Ledgers.Act,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Cast.vote(s, m, w, n, a0)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.trans(
          s,
          s4,
          Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(Cast.seal.grows(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n)))

# a vote only grows a node
def Cast.put.grows(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Stepping.Run>,
  s: Replicas.Node<Basics.Ask>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Cast.put(n, w, th, qs, from, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Stepping.Run{+s2, +t2}}:
      e => Cast.vote.grows(
        s,
        s2,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from},
        e
      )(Put.grows(s2, [Replicas.Tip.words(t2)]))

# a pass only grows a node
def Pass.to.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {Reading.Node.grows(s, Voting.Pass.to(n, s, w, os)) == True{}: Bool}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Grows.when(
        s,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        Sealing.Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Voting.Last.below(n, s, c, h, r)},
          Sealing.Seal.chain(s, Sealing.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.grows(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Voting.Last.below(n, s, c, h, r)},
          Sealing.Seal.chain(s, Sealing.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        Grows.refl(s)
      )

# a node that joins a round only grows a node
def Round.join.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {Reading.Node.grows(s, Voting.Round.join(n, s, c, h, os)) == True{}: Bool}:
  +top = Sealing.Round.seen(s, c, h)
  k = top
  Grows.when(
    s,
    Nat.is_lt(Voting.Round.mine(n, s, c, h, k), top),
    Voting.Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.grows(n, s, Ledgers.Where{c, h, top}, os),
    Grows.refl(s)
  )

# a ballot in the node's round only grows a node
def Cast.round.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Replicas.Tip
) -> {Reading.Node.grows(s, Voting.Cast.round(n, s, c, next, th, t)) == True{}: Bool}:
  +os = Replicas.Tip.owners(t)
  +r = Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Voting.Plan.of(
    n,
    s,
    c,
    w,
    t,
    th,
    os,
    Sealing.Owners.turn(os, U32.add(next, U32.from_nat(r)))
  )
  Grows.when(
    s,
    Sealing.Cast.may(n, s, w, t, Sealing.Plan.asks(p)),
    Sealing.Cast.put(n, w, th, Sealing.Plan.asks(p), Sealing.Plan.from(p), Sealing.Plan.run(p), s),
    s,
    Cast.put.grows(
      n,
      w,
      th,
      Sealing.Plan.asks(p),
      Sealing.Plan.from(p),
      Sealing.Plan.run(p),
      s
    )(
      Plan.of.grows(n, s, c, w, t, th, os, Sealing.Owners.turn(os, U32.add(next, U32.from_nat(r))))
    ),
    Grows.refl(s)
  )

# Node.cast only grows a node, at the head h whose tip is m
def Cast.at.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {Reading.Node.grows(s, Voting.Cast.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, +next, +th} Some{+t}:
      +s1 = Voting.Round.join(n, s, c, next, Replicas.Tip.owners(t))
      Grows.trans(
        s,
        s1,
        Voting.Cast.round(n, s1, c, next, th, t)
      )(
        Round.join.grows(n, s, c, next, Replicas.Tip.owners(t))
      )(Cast.round.grows(n, s1, c, next, th, t))
    case Replicas.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, at the head h whose tip is m
def Pass.at.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {Reading.Node.grows(s, Voting.Pass.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{t}:
      Pass.to.grows(
        n,
        s,
        Ledgers.Where{c, next, 1n+Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))},
        Replicas.Tip.owners(t)
      )
    case Replicas.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, once the head m is known
def Pass.head.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Voting.Pass.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Pass.at.grows(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# Node.cast only grows a node, once the head m is known
def Cast.head.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Voting.Cast.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Cast.at.grows(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# a node's ballot only grows it
def Cast.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.cast(n, s, c)) == True{}: Bool}:
  Cast.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  +qs: List<&2, Ledgers.Id>,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Reading.Node.grows(s, Voting.Advance.moved(s, m, c, h, qs)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.to(
          s,
          x,
          Sealing.State.moved(x, c, h, qs),
          Led.moved(x, c, h, qs),
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )

# a checked step only grows a node
def Advance.ran.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Voting.Advance.ran(s, c, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Stepping.Run{+s2, +t2}}:
      e =>
        +hd = {Replicas.Head{r, b, U32.inc(next), Some{Replicas.Tip.hash(t2)}}: Replicas.Head}
        Grows.when(
          s,
          Sealing.Root.same(after, Some{Replicas.Tip.hash(t2)}),
          Voting.Advance.moved(s, Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]), c, hd, qs),
          s,
          Advance.moved.grows(
            s,
            s2,
            Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
            c,
            hd,
            qs,
            e
          )(Put.grows(s2, [Replicas.Tip.words(t2)])),
          Grows.refl(s)
        )

# Node.advance only grows a node, once the decided step m is known
def Advance.step.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Reading.Node.grows(s, Voting.Advance.step(s, c, h, t, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Grows.when(
        s,
        Sealing.Root.same(before, th),
        Voting.Advance.ran(s, c, r, b, next, after, qs, Stepping.Step.run(s, c, t, qs)),
        s,
        Advance.ran.grows(
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Stepping.Step.run(s, c, t, qs)
        )(Run.grows(s, c, t, qs)),
        Grows.refl(s)
      )
    case Replicas.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {Reading.Node.grows(s, Voting.Advance.at(s, c, h, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+t}:
      Advance.step.grows(
        s,
        c,
        h,
        t,
        Voting.Height.decide(
          s,
          c,
          Sealing.Head.next(h),
          Replicas.Tip.owners(t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )

# Node.advance only grows a node, once the head m is known
def Advance.head.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Voting.Advance.head(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# Advances.grows once the head m is known
def Advances.at.grows(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Voting.Advances.at(f, s, c, m)) == True{}: Bool}:
  match f m:
    case 0n x:
      Grows.refl(s)
    case 1n+p None{}:
      Grows.refl(s)
    case 1n+(+p) Some{+h}:
      +s1 = Voting.Advance.at(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
      +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
      Grows.when(
        s,
        Voting.Heads.level(Some{h}, m1),
        s1,
        Voting.Advances.at(p, s1, c, m1),
        Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h)),
        Grows.trans(
          s,
          s1,
          Voting.Advances.at(p, s1, c, m1)
        )(Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h)))(Advances.at.grows(p, s1, c, m1))
      )

# a head that moves over each decided step only grows a node
def Advances.grows(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.advances(f, s, c)) == True{}: Bool}:
  Advances.at.grows(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# what a node does at a head only grows it
def Step.head.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Step.head(n, s, c)) == True{}: Bool}:
  +s1 = Voting.Node.advances(4294967295n, s, c)
  +s2 = Voting.Node.cast(n, s1, c)
  +s3 = Voting.Node.advances(4294967295n, s2, c)
  Grows.trans(
    s,
    s1,
    s3
  )(
    Advances.grows(4294967295n, s, c)
  )(Grows.trans(s1, s2, s3)(Cast.grows(n, s1, c))(Advances.grows(4294967295n, s2, c)))

# a line that opens only grows a node, once its head m is known
def Open.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Sealing.Open.at(s, c, m)) == True{}: Bool}:
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Replicas.Head{
          r,
          Some{b},
          0,
          Sealing.Branch.first(s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
        }: Replicas.Head
      }
      Grows.to(s, s, Sealing.State.head(s, c, hd), Led.head(s, c, hd), Grows.refl(s))
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      Grows.refl(s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      Grows.refl(s)
    case None{}:
      Grows.refl(s)

# what a node does on a line only grows it
def Step.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.step(n, s, c)) == True{}: Bool}:
  +s1 = Sealing.Node.open(s, c)
  Grows.trans(
    s,
    s1,
    Voting.Step.head(n, s1, c)
  )(Open.at.grows(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.head.grows(n, s1, c))

# a pass to the next round only grows a node
def Pass.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.pass(n, s, c)) == True{}: Bool}:
  +s1 = Voting.Pass.head(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Grows.trans(
    s,
    s1,
    Voting.Node.step(n, s1, c)
  )(Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.grows(n, s1, c))

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Sealing.First.at(s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      Grows.refl(s)
    case Some{Replicas.Head{r, b, n, None{}}}:
      Grows.to(s, s, Sealing.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))
    case None{}:
      Grows.to(s, s, Sealing.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Start.head(s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.trans(
          s,
          x,
          Sealing.State.first(x, c, h)
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(First.at.grows(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c)))

# the first keys of a store are on a node that grew
def Firsts.after(
  +s: Replicas.Node<Basics.Ask>,
  os: List<&2, Basics.Owner>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Work.after(s, Sealing.Seal.firsts(os, m)) == True{}: Bool}:
  match os:
    case Nil{}:
      e => e
    case Con{Basics.Owner{+n, +k}, r}:
      e => Firsts.after(
        s,
        r,
        Maybe.bind(
          &2,
          Replicas.Work<Basics.Ask>,
          Replicas.Work<Basics.Ask>,
          m,
          w => Replicas.Work.set(~Basics.Ask.machine(), w, Basics.Key.seal(n), Hashes.Hash.code(k, []))
        )
      )(Work.set.after(s, m, Basics.Key.seal(n), Hashes.Hash.code(k, []))(e))

# Start.grows once the content m of the store is known
def Start.with.grows(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Start.with(s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Replicas.Work{+s2, +c}}:
      e =>
        +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
        Start.head.grows(
          s,
          s2,
          Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Replicas.Tip.words(t)]))

# a store that starts only grows a node
def Start.grows(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Basics.Owner>
) -> {Reading.Node.grows(s, Sealing.Node.start(s, i, os)) == True{}: Bool}:
  Start.with.grows(
    s,
    i,
    Basics.Owner.names(os),
    Sealing.Seal.firsts(os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Grows.refl(s)))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Sealing.Follow.new(s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(s)
    case None{}:
      Grows.to(
        s,
        s,
        Sealing.State.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
        Led.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
        Grows.refl(s)
      )

# a new request only grows a node
def Arrive.grows(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> {Reading.Node.grows(s, Sealing.Node.arrive(s, i, q)) == True{}: Bool}:
  match q:
    case Basics.Ask.Start{os}:
      Start.grows(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Sealing.Node.follow(s, r, l)
      Grows.to(
        s,
        s1,
        Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
        Led.waits(s1, Replicas.Line.chain(r, l), i),
        Follow.new.grows(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))
      )

# a new request only grows a node
def Ask.new.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> {Reading.Node.grows(s, Voting.Node.ask.new(n, s, e, q)) == True{}: Bool}:
  +i = Replicas.Envelope.of(e)
  +c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Replicas.State.ledger(~Basics.Ask.machine(), s),
    i,
    Replicas.Envelope.time(e),
    q
  )
  +s0 = Replicas.State.led(~Basics.Ask.machine(), s, l0)
  +s1 = Sealing.Node.arrive(s0, i, q)
  Grows.trans(
    s,
    s0,
    Voting.Node.step(n, s1, c)
  )(
    Grows.led(
      s,
      l0,
      Ledgers.State.add_grows(
        ~Basics.Ask,
        ~Basics.Ask.is_eq,
        ~Basics.Ask.laws(),
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        Ledgers.Slot.ask(i),
        Ledgers.Entry.Ask{i, Replicas.Envelope.time(e), q}
      )
    )
  )(Grows.trans(s0, s1, Voting.Node.step(n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c)))

# Node.ask_grows once the cell m of the request's ID is known
def Ask.at.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {Reading.Node.grows(s, Voting.Node.ask.at(n, s, e, q, m)) == True{}: Bool}:
  match m:
    case Some{x}:
      Grows.refl(s)
    case None{}:
      Grows.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Voting.Node.ask.new(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )(
        Grows.to(
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Grows.refl(s)
        )
      )(
        Ask.new.grows(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )

# a node that takes in a request only grows
def Ask.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask
) -> {Reading.Node.grows(s, Voting.Node.ask(n, s, e, q)) == True{}: Bool}:
  Ask.at.grows(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e)))
  )

# the new requests among cells only grow a node
def Take.asks.grows(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>
) -> {Reading.Node.grows(s, Voting.Take.asks(cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(
        Replicas.Node<Basics.Ask>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Sealing.Node.arrive(s, i, q),
        u => s
      )
      Grows.trans(
        s,
        s1,
        Voting.Take.asks(rest, old, s1)
      )(
        Grows.when(
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          Sealing.Node.arrive(s, i, q),
          s,
          Arrive.grows(s, i, q),
          Grows.refl(s)
        )
      )(Take.asks.grows(rest, old, s1))
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(rest, old, s)

# the ballots that a chain leads to only grow a node, when each one more does
def Follow.step.grows(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  k: Replicas.Node<Basics.Ask> -> Replicas.Node<Basics.Ask>,
  ih: @s2: Replicas.Node<Basics.Ask> -> {Reading.Node.grows(s2, k(s2)) == True{}: Bool}
) -> {
  State.after(s, m) == True{}: Bool
} -> {
  Reading.Node.grows(
    s,
    Maybe.default(
      &2,
      Replicas.Node<Basics.Ask>,
      Maybe.bind(&2, Replicas.Node<Basics.Ask>, Replicas.Node<Basics.Ask>, m, s2 => Some{k(s2)}),
      s
    )
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s2}:
      e => Grows.trans(s, s2, k(s2))(e)(ih(s2))

# the ballots that a chain leads to only grow a node
def Follow.grows(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {Reading.Node.grows(s, Sealing.Sealed.follow(f, s, p, r, n, mb)) == True{}: Bool}:
  match f mb:
    case 0n x:
      Grows.refl(s)
    case 1n+g None{}:
      Grows.refl(s)
    case 1n+(+g) Some{+b}:
      Follow.step.grows(
        s,
        Sealing.Seal.accept(s, b),
        +s2 => Sealing.Sealed.follow(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n)),
        +s2 => Follow.grows(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n))
      )(
        Accept.at.grows(
          s,
          b,
          Sealing.Seal.chain(s, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to only grow a node
def Each.grows(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {Reading.Node.grows(s, Sealing.Sealed.each(f, bs, p, s)) == True{}: Bool}:
  match bs:
    case Nil{}:
      Grows.refl(s)
    case Con{+b, +rest}:
      +s1 = Sealing.Sealed.follow(
        f,
        s,
        p,
        Sealing.Ballot.store(b),
        Sealing.Ballot.node(b),
        Sealing.Pending.next(s, p, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
      )
      Grows.trans(
        s,
        s1,
        Sealing.Sealed.each(f, rest, p, s1)
      )(
        Follow.grows(
          f,
          s,
          p,
          Sealing.Ballot.store(b),
          Sealing.Ballot.node(b),
          Sealing.Pending.next(s, p, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )(Each.grows(f, rest, p, s1))

# a node that takes in what another node sent only grows
def Take.grows(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {Reading.Node.grows(s, Voting.Node.take(s, t)) == True{}: Bool}:
  +sent = Voting.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Grows.trans(
    s,
    s1,
    Sealing.Sealed.take(bs, s2)
  )(
    Grows.led(
      s,
      l1,
      Ledgers.State.take_grows(
        ~Basics.Ask,
        ~Basics.Ask.is_eq,
        ~Basics.Ask.laws(),
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        sent
      )
    )
  )(
    Grows.trans(
      s1,
      s2,
      Sealing.Sealed.take(bs, s2)
    )(
      Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
    )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2))
  )

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {
  Reading.Node.grows(
    Replicas.State.led(~Basics.Ask.machine(), 
      s,
      Ledgers.State.take(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        Voting.Take.clean(
          Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
          Ledgers.State.empty(~Basics.Ask)
        )
      )
    ),
    Voting.Node.take(s, t)
  )
    == True{}: Bool
}:
  +sent = Voting.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Grows.trans(
    s1,
    s2,
    Sealing.Sealed.take(bs, s2)
  )(
    Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2))

# Node.fetch for the data ws itself
def Fetch.take(
  +b: Replicas.Node<Basics.Ask>,
  +ws: List<&2, U32>
) -> {
  Ledgers.State.get(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), b),
    Ledgers.Slot.data(Hashes.Sha.hash(ws))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
} -> {
  Ledgers.State.data(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), 
      Voting.Node.take(
        b,
        Ledgers.State.put_data(~Basics.Ask, ~Basics.Ask.is_eq, Ledgers.State.empty(~Basics.Ask), ws)
      )
    ),
    Hashes.Sha.hash(ws)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  +t = Ledgers.State.put_data(~Basics.Ask, ~Basics.Ask.is_eq, Ledgers.State.empty(~Basics.Ask), ws)
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), b), t)
  e =>
    Ledgers.State.data_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), b, l1)),
      Replicas.State.ledger(~Basics.Ask.machine(), Voting.Node.take(b, t)),
      Hashes.Sha.hash(ws),
      ws
    )(Take.tail(b, t))(
      %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), b, l1)), l1, Led.led(b, l1)): {Ledgers.State.data(~Basics.Ask, _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
      Ledgers.State.take_data(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), b), ws)(e))

def Spec.Node.fetch(a, b, h, ws):
  +ea => eb =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Ledgers.State.data(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), h),
      Some{ws},
      ea
    ): {
      Ledgers.State.data(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), 
          Voting.Node.take(b, Voting.Serve.put(_, Ledgers.State.empty(~Basics.Ask)))
        ),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Ledgers.State.data_hash(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      h,
      ws
    )(
      ea
    ): {
      Ledgers.State.data(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), 
          Voting.Node.take(
            b,
            Ledgers.State.put_data(
              ~Basics.Ask,
              ~Basics.Ask.is_eq,
              Ledgers.State.empty(~Basics.Ask),
              ws
            )
          )
        ),
        _
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    Fetch.take(b, ws)(
      %Equal.sym(Hashes.Hash, Hashes.Sha.hash(ws), h, Ledgers.State.data_hash(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), h, ws)(ea)): {Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), b), Ledgers.Slot.data(_)) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
      eb)

# what a node does on each of some lines only grows it
def Steps.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> {Reading.Node.grows(s, Voting.Node.steps(n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{+c, +rest}:
      +s1 = Voting.Node.step(n, s, c)
      Grows.trans(
        s,
        s1,
        Voting.Node.steps(n, rest, s1)
      )(Step.grows(n, s, c))(Steps.grows(n, rest, s1))

# an adoption only grows a node, once the request m is known
def Adopt.ask.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Reading.Request>
) -> {Reading.Node.grows(s, Reading.Adopt.ask(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Reading.Request{e, q}}:
      Ask.grows(n, s, e, q)

# an adoption only grows a node, once the head m of the line is known
def Adopt.head.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> {Reading.Node.grows(s, Reading.Adopt.head(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.grows(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line only grows a node
def Adopt.at.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> {Reading.Node.grows(s, Reading.Adopt.at(n, s, c)) == True{}: Bool}:
  Adopt.head.grows(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> {Reading.Node.grows(s, Reading.Adopt.maybe(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{c}:
      Adopt.at.grows(n, s, c)

# the adoption of each of some lines only grows a node
def Adopts.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> {Reading.Node.grows(s, Reading.Node.adopts(n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{+c, +rest}:
      Grows.trans(
        s,
        Reading.Adopt.at(n, s, c),
        Reading.Node.adopts(n, rest, Reading.Adopt.at(n, s, c))
      )(Adopt.at.grows(n, s, c))(Adopts.grows(n, rest, Reading.Adopt.at(n, s, c)))

# more rounds of a sync, grows
def More.grows(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {Reading.Node.grows(s, Reading.Sync.more(f, n, cs, k, bs, pd, s)) == True{}: Bool}:
  match f:
    case 0n:
      Grows.refl(s)
    case 1n+(+p):
      Grows.when(
        s,
        Reading.Lines.level(cs, s, Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))),
        Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
        Reading.Sync.more(
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
        ),
        Grows.trans(
          s,
          Sealing.Sealed.each(k, bs, pd, s),
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
        )(Each.grows(k, bs, pd, s))(Steps.grows(n, cs, Sealing.Sealed.each(k, bs, pd, s))),
        Grows.trans(
          s,
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
          Reading.Sync.more(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          )
        )(
          Grows.trans(
            s,
            Sealing.Sealed.each(k, bs, pd, s),
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          )(Each.grows(k, bs, pd, s))(Steps.grows(n, cs, Sealing.Sealed.each(k, bs, pd, s)))
        )(
          More.grows(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          )
        )
      )

# a sync only grows a node
def Sync.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {Reading.Node.grows(s, Reading.Node.sync(n, s, t)) == True{}: Bool}:
  +s1 = Voting.Node.take(s, t)
  +cs = Voting.Sync.lines(s, s1, t)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Voting.Node.steps(n, cs, s1)
  +s3 = Reading.Sync.more(
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Sealing.Pending.of(bs),
    s2
  )
  Grows.trans(
    s,
    s1,
    Reading.Node.adopts(n, cs, s3)
  )(
    Take.grows(s, t)
  )(
    Grows.trans(
      s1,
      s2,
      Reading.Node.adopts(n, cs, s3)
    )(
      Steps.grows(n, cs, s1)
    )(
      Grows.trans(
        s2,
        s3,
        Reading.Node.adopts(n, cs, s3)
      )(
        More.grows(
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Sealing.Pending.of(bs),
          s2
        )
      )(Adopts.grows(n, cs, s3))
    )
  )
