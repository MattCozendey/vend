# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/missed_fork@hint -- this file holds only proofs: a proof does not run
import Base
import ../../shared.bend as Shared
import ../replica/impl.bend as Replicas
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/quorum.bend as Quorums
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/store.bend as Stores
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ./judging.bend as Judging
import ./reading.bend as Reading
import ./spec.bend as Spec
import ./stepping.bend as Stepping

# The proofs of the core's laws.

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
    Replicas.State.head(~Basics.Ask.machine(), s, c, h)
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
    Replicas.Wait.set(~Basics.Ask.machine(), s, c, qs)
  )
    == Replicas.State.ledger(~Basics.Ask.machine(), s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a node grows to itself
def Grows.refl(s: Replicas.Node<Basics.Ask>) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(~Basics.Ask, ~Basics.Ask.is_eq, ~Basics.Ask.laws(), Replicas.State.ledger(~Basics.Ask.machine(), s))

# growth composes
def Grows.trans(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Replicas.Node<Basics.Ask>
) -> {
  Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), b, c) == True{}: Bool} -> {Replicas.Node.grows(~Basics.Ask.machine(), a, c) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.State.led(~Basics.Ask.machine(), s, l)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.State.keep(~Basics.Ask.machine(), s, ds)) == True{}: Bool}:
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
      Replicas.Node.grows(~Basics.Ask.machine(), s, s2)

# the node m, if any, grew from s
def State.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Node<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Replicas.Node.grows(~Basics.Ask.machine(), s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  s: Replicas.Node<Basics.Ask>,
  -s2: Replicas.Node<Basics.Ask>,
  b: Bool,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, s2) == True{}: Bool}
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
def Run.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Run<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Replicas.Run{s2, t}}:
      Replicas.Node.grows(~Basics.Ask.machine(), s, s2)

# a run is on its own node
def After.self(r: Replicas.Run<Basics.Ask>) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Some{r}) == True{}: Bool}:
  match r:
    case Replicas.Run{s, t}:
      Grows.refl(s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  e1: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  e2: {Run.after(b, m) == True{}: Bool}
) -> {Run.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Run{s2, t}}:
      Grows.trans(a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  s: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  f: Replicas.Run<Basics.Ask> -> Maybe<&2, Replicas.Run<Basics.Ask>>,
  hm: {Run.after(s, m) == True{}: Bool},
  hf: @r: Replicas.Run<Basics.Ask> -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), f(r)) == True{}: Bool}
) -> {Run.after(s, Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Run{+s2, +t}}:
      After.trans(s, s2, f(Replicas.Run{s2, t}), hm, hf(Replicas.Run{s2, t}))

# one of two runs, each on a node that grew
def After.when(
  s: Replicas.Node<Basics.Ask>,
  +b: Bool,
  -mx: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -my: Maybe<&2, Replicas.Run<Basics.Ask>>,
  hx: {Run.after(s, mx) == True{}: Bool},
  hy: {Run.after(s, my) == True{}: Bool}
) -> {Run.after(s, Shared.Bool.when(Maybe<&2, Replicas.Run<Basics.Ask>>, b, u => mx, u => my)) == True{}: Bool}:
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
  e1: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
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
def Made.after(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Made<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Replicas.Made{t, s2}}:
      Replicas.Node.grows(~Basics.Ask.machine(), s, s2)

# a first tip on a work is on a node that grew
def Grown.made.put(
  s: Replicas.Node<Basics.Ask>,
  t: Replicas.Tip,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {Work.after(s, m) == True{}: Bool} -> {Made.after(s, Replicas.Made.put(~Basics.Ask.machine(), t, m)) == True{}: Bool}:
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
      Replicas.Node.grows(~Basics.Ask.machine(), s, s2)

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
) -> {Run.after(s, Replicas.Run.logged(~Basics.Ask.machine(), t, m)) == True{}: Bool}:
  match t m:
    case x None{}:
      {==}
    case Replicas.Tip{c, old, n, os} Some{Replicas.Work{s2, l}}:
      e

# Add.grows once the value m of the key is known
def Add.at.grows(
  r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Run.add.at(~Basics.Ask.machine(), r, k, x, m)) == True{}: Bool}:
  match r m:
    case Replicas.Run{+s, +t} None{}:
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
  +r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Run.add(~Basics.Ask.machine(), r, k, x)) == True{}: Bool}:
  Add.at.grows(
    r,
    k,
    x,
    Replicas.Node.get(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)), k)
  )

# a run one version on is on its own node
def Next.grows(
  r: Replicas.Run<Basics.Ask>,
  own: Maybe<&2, List<&2, String>>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Some{Replicas.Run.next(~Basics.Ask.machine(), r, own)}) == True{}: Bool}:
  match r:
    case Replicas.Run{s, t}:
      Grows.refl(s)

# a refused request only grows a run's node
def Stale.grows(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.stale(~Basics.Ask.machine(), r, i)) == True{}: Bool}:
  Add.grows(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.taken(~Basics.Ask.machine(), r, i, own)) == True{}: Bool}:
  +n = Replicas.Tip.count(Replicas.Run.tip(~Basics.Ask.machine(), r))
  After.bind(
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Replicas.Run<Basics.Ask>,
      Replicas.Run<Basics.Ask>,
      Replicas.Run.add(~Basics.Ask.machine(), 
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
      ),
      r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)}
    ),
    Add.grows(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
    +r1 => After.bind(
      Replicas.Run.state(~Basics.Ask.machine(), r1),
      Replicas.Run.add(~Basics.Ask.machine(), 
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
      ),
      r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)},
      Add.grows(
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
      ),
      r2 => Next.grows(r2, own)
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Replicas.Verdict<Basics.Ask>>
) -> {
  Verdict.after(Replicas.Run.state(~Basics.Ask.machine(), r), m) == True{}: Bool
} -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.judged(~Basics.Ask.machine(), r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Replicas.Verdict.Stale{}}:
      g => Stale.grows(r, i)
    case Some{Replicas.Verdict.Taken{Replicas.Work{+s2, +h}}}:
      g => After.trans(
        Replicas.Run.state(~Basics.Ask.machine(), r),
        s2,
        Replicas.Step.taken(~Basics.Ask.machine(), Replicas.Run.over(~Basics.Ask.machine(), r, s2, h), i, own),
        g,
        Taken.grows(Replicas.Run.over(~Basics.Ask.machine(), r, s2, h), i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Replicas.Version>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(x), [])),
        r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{}),
        Add.grows(r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(x), [])),
        r2 => Taken.grows(r2, i, None{})
      )

# a request for a mark only grows a run's node
def Mark.grows(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +m: String
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.mark(~Basics.Ask.machine(), r, i, m)) == True{}: Bool}:
  +s = Replicas.Run.state(~Basics.Ask.machine(), r)
  +t = Replicas.Run.tip(~Basics.Ask.machine(), r)
  +n = Replicas.Tip.count(t)
  After.when(
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Replicas.Line.mark(~Basics.Ask.machine(), s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Replicas.Step.stale(~Basics.Ask.machine(), r, i),
    Marked.grows(r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Stale.grows(r, i)
  )

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Replicas.Made<Basics.Ask>>
) -> {
  Made.after(Replicas.Run.state(~Basics.Ask.machine(), r), m) == True{}: Bool
} -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Branch.made(~Basics.Ask.machine(), r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      g => {==}
    case Some{Replicas.Made{+t, +s2}}:
      g =>
        +r1 = {Replicas.Run.over(~Basics.Ask.machine(), r, s2, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r))): Replicas.Run<Basics.Ask>}
        After.trans(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          s2,
          Maybe.bind(
            &2,
            Replicas.Run<Basics.Ask>,
            Replicas.Run<Basics.Ask>,
            Replicas.Run.add(~Basics.Ask.machine(), r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{})
          ),
          g,
          After.bind(
            s2,
            Replicas.Run.add(~Basics.Ask.machine(), r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{}),
            Add.grows(r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
            r2 => Taken.grows(r2, i, None{})
          )
        )

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Branch.ready(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{False{}}:
      Stale.grows(r, i)
    case Some{True{}}:
      After.when(
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Basics.Node.root_of(Replicas.Run.state(~Basics.Ask.machine(), r), at)
        ),
        Replicas.Branch.made(~Basics.Ask.machine(), 
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        ),
        None{},
        Branch.made.grows(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        )(
          Grown.make.first(
            Replicas.Run.state(~Basics.Ask.machine(), r),
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )(Grown.make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at))
        ),
        {==}
      )

# a request for a branch only grows a run's node
def Branch.new.grows(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Branch.new(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Some{x}}:
      Stale.grows(r, i)
    case Some{None{}}:
      Branch.ready.grows(r, i, st, b, at, Judging.Judge.ready_maybe(Replicas.Run.state(~Basics.Ask.machine(), r), at))

# On.grows once it is known how the line takes the change (w)
def On.of.grows(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.on.of(r, i, st, l, ch, w)) == True{}: Bool}:
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
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Log.start(a)
        )
      )
    case Stepping.Route.Judge{}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
        )
      )(
        Verdict.change(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
        )
      )

# a change of a line only grows a run's node
def On.grows(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  On.of.grows(r, i, st, l, ch, Stepping.Route.of(l, ch))

# a request only grows a run's node
def Change.grows(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Basics.Ask
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.change(r, c, i, q)) == True{}: Bool}:
  match q:
    case Basics.Ask.Start{os}:
      Stale.grows(r, i)
    case Basics.Ask.On{+st, +l, ch}:
      After.when(
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        On.grows(r, i, st, l, ch),
        Stale.grows(r, i)
      )

# a request that the node holds or not only grows a run's node
def Asked.grows(
  r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.asked(~Stepping.Ask.kernel(), r, c, i, a)) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{Ledgers.Asked{t, q}}:
      Change.grows(r, c, i, q)

# a request that the log holds or not only grows a run's node
def Fresh.grows(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +o: Maybe<&2, Replicas.Out>
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.fresh(~Stepping.Ask.kernel(), r, c, i, o)) == True{}: Bool}:
  match o:
    case Some{x}:
      After.self(r)
    case None{}:
      Asked.grows(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), i))

# one request of a step only grows a run's node
def One.grows(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i)) == True{}: Bool}:
  Fresh.grows(r, c, i, Replicas.Line.out(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Run.tip(~Basics.Ask.machine(), r), i))

# the requests of a step only grow a run's node
def All.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Run.after(s, Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.grows(
        s,
        c,
        rest,
        Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i))
      )(After.bind(s, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i), h, r => One.grows(r, c, i)))

# a step only grows a node: its run is on a node that keeps every entry
def Run.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  qs: List<&2, Ledgers.Id>
) -> {Run.after(s, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Replicas.Run{s, t}})(Grows.refl(s))

# the run of picked requests, with one more request or not
def Add.run(
  b: Bool,
  i: Ledgers.Id,
  p: Replicas.Picked<Basics.Ask>
) -> {Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Picked.add(~Basics.Ask.machine(), b, i, p)) == Replicas.Picked.run(~Basics.Ask.machine(), p): Replicas.Run<Basics.Ask>}:
  match p:
    case Replicas.Picked{r, qs}:
      {==}

# the run m, if any, else r, is on a node that grew from that of r
def Default.run.grows(
  r: Replicas.Run<Basics.Ask>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> {
  Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), m) == True{}: Bool
} -> {
  Replicas.Node.grows(~Basics.Ask.machine(), 
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Replicas.Run.state(~Basics.Ask.machine(), Maybe.default(&2, Replicas.Run<Basics.Ask>, m, r))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(Replicas.Run.state(~Basics.Ask.machine(), r))
    case Some{Replicas.Run{s2, t}}:
      e => e

# the run of the requests that can run is on a node that grew
def Some.grows(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Replicas.Run<Basics.Ask>
) -> {
  Run.after(
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Some{Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Step.some(~Stepping.Ask.kernel(), c, qs, r))}
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      After.self(r)
    case Con{+i, +rest}:
      +m = Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i)
      +r2 = Maybe.default(&2, Replicas.Run<Basics.Ask>, m, r)
      %Equal.sym(
        Replicas.Run<Basics.Ask>,
        Replicas.Picked.run(~Basics.Ask.machine(), 
          Replicas.Picked.add(~Basics.Ask.machine(), 
            Maybe.is_some(&2, Replicas.Run<Basics.Ask>, m),
            i,
            Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2)
          )
        ),
        Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2)),
        Add.run(Maybe.is_some(&2, Replicas.Run<Basics.Ask>, m), i, Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2))
      ): {Run.after(Replicas.Run.state(~Basics.Ask.machine(), r), Some{_}) == True{}: Bool}
      After.trans(
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Replicas.Run.state(~Basics.Ask.machine(), r2),
        Some{Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2))},
        Default.run.grows(r, m)(One.grows(r, c, i)),
        Some.grows(c, rest, r2)
      )

# a run that is kept when b holds is on a node that grew, when it is
def Fit.when.grows(
  -s: Replicas.Node<Basics.Ask>,
  b: Bool,
  -r: Replicas.Run<Basics.Ask>,
  e: {Run.after(s, Some{r}) == True{}: Bool}
) -> {Run.after(s, Shared.Maybe.when(Replicas.Run<Basics.Ask>, b, u => Some{r})) == True{}: Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# a run that fits a tip is on a node that grew, when the run is
def Plan.fit.grows(
  -s: Replicas.Node<Basics.Ask>,
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Run.after(s, Replicas.Plan.fit(~Basics.Ask.machine(), after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Replicas.Run{s2, t2}}:
      e => Fit.when.grows(
        s,
        Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        Replicas.Run{s2, t2},
        e
      )

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  -s: Replicas.Node<Basics.Ask>,
  b: Bool,
  -x: Replicas.Plan<Basics.Ask>,
  -y: Replicas.Plan<Basics.Ask>,
  hx: {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), x)) == True{}: Bool},
  hy: {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), y)) == True{}: Bool}
) -> {
  Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Shared.Bool.when(Replicas.Plan<Basics.Ask>, b, u => x, u => y))) == True{}: Bool
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
) -> {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.own(~Stepping.Ask.kernel(), s, c, t, from))) == True{}: Bool}:
  Some.grows(c, Replicas.Cast.mine(~Stepping.Ask.kernel(), s, Replicas.Wait.of(~Basics.Ask.machine(), s, c)), Replicas.Run{s, t})

# the run of the plan for a step that another ballot names is on a node that
# grew
def Plan.copy.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  -from: List<&2, String>
) -> {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.copy(~Stepping.Ask.kernel(), s, c, t, th, m, from))) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Plan.when.grows(
        s,
        List.all.if(u => Replicas.Cast.all_mine(~Stepping.Ask.kernel(), s, qs), Replicas.Root.same(before, th)),
        Replicas.Plan{qs, Replicas.Plan.fit(~Basics.Ask.machine(), after, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)), from},
        Replicas.Plan{[], None{}, []},
        Plan.fit.grows(s, after, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs))(Run.grows(s, c, t, qs)),
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
  Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.later(~Stepping.Ask.kernel(), s, c, w, t, th, os, from, m))) == True{}: Bool
}:
  match m:
    case None{}:
      Plan.when.grows(
        s,
        Replicas.Owners.major(os, from),
        Replicas.Plan.own(~Stepping.Ask.kernel(), s, c, t, from),
        Replicas.Plan{[], None{}, []},
        Plan.own.grows(s, c, t, from),
        {==}
      )
    case Some{Ledgers.Last{r, v}}:
      Plan.when.grows(
        s,
        Replicas.Owners.major(os, from),
        Replicas.Plan.copy(~Stepping.Ask.kernel(), s, c, t, th, Some{v}, from),
        Replicas.Plan{[], None{}, []},
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
) -> {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.lead(~Stepping.Ask.kernel(), s, c, w, t, th, os))) == True{}: Bool}:
  Plan.when.grows(
    s,
    Nat.is_eq(Replicas.Where.round(w), 0n),
    Replicas.Plan.own(~Stepping.Ask.kernel(), s, c, t, []),
    Replicas.Plan.later(~Stepping.Ask.kernel(), 
      s,
      c,
      w,
      t,
      th,
      os,
      Replicas.Passes.of(~Basics.Ask.machine(), s, w, os),
      Replicas.Passes.last(~Basics.Ask.machine(), s, w, Replicas.Passes.of(~Basics.Ask.machine(), s, w, os))
    ),
    Plan.own.grows(s, c, t, []),
    Plan.later.grows(
      s,
      c,
      w,
      t,
      th,
      os,
      Replicas.Passes.of(~Basics.Ask.machine(), s, w, os),
      Replicas.Passes.last(~Basics.Ask.machine(), s, w, Replicas.Passes.of(~Basics.Ask.machine(), s, w, os))
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
) -> {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.follow(~Stepping.Ask.kernel(), s, c, w, t, th, os, m))) == True{}: Bool}:
  match m:
    case Some{Ledgers.Act.Vote{+v, from}}:
      Plan.when.grows(
        s,
        Replicas.Vote.allowed(~Basics.Ask.machine(), s, w, os, v, from),
        Replicas.Plan.copy(~Stepping.Ask.kernel(), s, c, t, th, Some{v}, from),
        Replicas.Plan{[], None{}, []},
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
) -> {Run.after(s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.of(~Stepping.Ask.kernel(), n, s, c, w, t, th, os, turn))) == True{}: Bool}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Plan.when.grows(
        s,
        String.eq(p, n),
        Replicas.Plan.lead(~Stepping.Ask.kernel(), s, c, w, t, th, os),
        Replicas.Plan.follow(~Stepping.Ask.kernel(), s, c, w, t, th, os, Replicas.Cast.act(~Basics.Ask.machine(), s, w, p)),
        Plan.lead.grows(s, c, w, t, th, os),
        Plan.follow.grows(s, c, w, t, th, os, Replicas.Cast.act(~Basics.Ask.machine(), s, w, p))
      )

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  x: Replicas.Node<Basics.Ask>,
  e: {Replicas.State.ledger(~Basics.Ask.machine(), x) == Replicas.State.ledger(~Basics.Ask.machine(), b): Ledgers.State(Basics.Ask)},
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {Replicas.Node.grows(~Basics.Ask.machine(), a, x) == True{}: Bool}:
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
  hx: {Replicas.Node.grows(~Basics.Ask.machine(), s, x) == True{}: Bool},
  hy: {Replicas.Node.grows(~Basics.Ask.machine(), s, y) == True{}: Bool}
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)) == True{}: Bool}:
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
    Replicas.State.moved(~Basics.Ask.machine(), s, c, h, qs)
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
    Replicas.State.wait(~Basics.Ask.machine(), s, c, i)
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
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, s3) == True{}: Bool}
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))) == True{}: Bool}:
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
) -> {State.after(s, Replicas.Seal.accept.at(~Basics.Ask.machine(), s, b, m)) == True{}: Bool}:
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
          Replicas.Keys.saw(
            Replicas.Keys.set(
              Replicas.State.keys(~Basics.Ask.machine(), s),
              Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
              Replicas.Keychain.next(c, b)
            ),
            Replicas.Ballot.at(b)
          )
        ),
        Replicas.Seal.fits(c, b),
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
            Replicas.Keys.saw(
              Replicas.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                Replicas.Keychain.next(c, b)
              ),
              Replicas.Ballot.at(b)
            )
          ),
          Led.keyed(
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Replicas.Keys.saw(
              Replicas.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                Replicas.Keychain.next(c, b)
              ),
              Replicas.Ballot.at(b)
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
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Maybe.default(&2, Replicas.Node<Basics.Ask>, m, s)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.seal(~Stepping.Ask.kernel(), s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Replicas.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Replicas.Seal.secret(Replicas.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)), Replicas.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Replicas.Seal.secret(
            Replicas.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)),
            Replicas.Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.grows(
        s,
        Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b)
      )(
        Accept.at.grows(
          s,
          b,
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
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
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.vote(~Stepping.Ask.kernel(), s, m, w, n, a0)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.trans(
          s,
          s4,
          Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(Cast.seal.grows(s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)))

# a vote only grows a node
def Cast.put.grows(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  s: Replicas.Node<Basics.Ask>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, qs, from, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Replicas.Run{+s2, +t2}}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Pass.to(~Stepping.Ask.kernel(), n, s, w, os)) == True{}: Bool}:
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
        Replicas.Cast.seal(~Stepping.Ask.kernel(), 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Replicas.Last.below(~Basics.Ask.machine(), n, s, c, h, r)},
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.grows(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Replicas.Last.below(~Basics.Ask.machine(), n, s, c, h, r)},
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Where.store(Ledgers.Where{c, h, r}), n)
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Round.join(~Stepping.Ask.kernel(), n, s, c, h, os)) == True{}: Bool}:
  +top = Replicas.Round.seen(~Basics.Ask.machine(), s, c, h)
  k = top
  Grows.when(
    s,
    Nat.is_lt(Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, h, k), top),
    Replicas.Pass.to(~Stepping.Ask.kernel(), n, s, Ledgers.Where{c, h, top}, os),
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.round(~Stepping.Ask.kernel(), n, s, c, next, th, t)) == True{}: Bool}:
  +os = Replicas.Tip.owners(t)
  +r = Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, next, Replicas.Round.seen(~Basics.Ask.machine(), s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Replicas.Plan.of(~Stepping.Ask.kernel(), 
    n,
    s,
    c,
    w,
    t,
    th,
    os,
    Replicas.Owners.turn(os, U32.add(next, U32.from_nat(r)))
  )
  Grows.when(
    s,
    Replicas.Cast.may(~Basics.Ask.machine(), n, s, w, t, Replicas.Plan.asks(~Basics.Ask.machine(), p)),
    Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, Replicas.Plan.asks(~Basics.Ask.machine(), p), Replicas.Plan.from(~Basics.Ask.machine(), p), Replicas.Plan.run(~Basics.Ask.machine(), p), s),
    s,
    Cast.put.grows(
      n,
      w,
      th,
      Replicas.Plan.asks(~Basics.Ask.machine(), p),
      Replicas.Plan.from(~Basics.Ask.machine(), p),
      Replicas.Plan.run(~Basics.Ask.machine(), p),
      s
    )(
      Plan.of.grows(n, s, c, w, t, th, os, Replicas.Owners.turn(os, U32.add(next, U32.from_nat(r))))
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.at(~Stepping.Ask.kernel(), n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, +next, +th} Some{+t}:
      +s1 = Replicas.Round.join(~Stepping.Ask.kernel(), n, s, c, next, Replicas.Tip.owners(t))
      Grows.trans(
        s,
        s1,
        Replicas.Cast.round(~Stepping.Ask.kernel(), n, s1, c, next, th, t)
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Pass.at(~Stepping.Ask.kernel(), n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{t}:
      Pass.to.grows(
        n,
        s,
        Ledgers.Where{c, next, 1n+Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, next, Replicas.Round.seen(~Basics.Ask.machine(), s, c, next))},
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.head(~Stepping.Ask.kernel(), n, s, c, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  Cast.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  +qs: List<&2, Ledgers.Id>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.moved(~Basics.Ask.machine(), s, m, c, h, qs)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.to(
          s,
          x,
          Replicas.State.moved(~Basics.Ask.machine(), x, c, h, qs),
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
  m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Replicas.Run{+s2, +t2}}:
      e =>
        +hd = {Replicas.Head{r, b, U32.inc(next), Some{Replicas.Tip.hash(t2)}}: Replicas.Head}
        Grows.when(
          s,
          Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}),
          Replicas.Advance.moved(~Basics.Ask.machine(), s, Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]), c, hd, qs),
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.step(~Stepping.Ask.kernel(), s, c, h, t, m)) == True{}: Bool}:
  match h m:
    case Replicas.Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Grows.when(
        s,
        Replicas.Root.same(before, th),
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, b, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Advance.ran.grows(
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+t}:
      Advance.step.grows(
        s,
        c,
        h,
        t,
        Replicas.Height.decide(~Basics.Ask.machine(), 
          s,
          c,
          Replicas.Head.next(h),
          Replicas.Tip.owners(t),
          Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
        )
      )

# Node.advance only grows a node, once the head m is known
def Advance.head.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.head(~Stepping.Ask.kernel(), s, c, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advances.at(~Stepping.Ask.kernel(), f, s, c, m)) == True{}: Bool}:
  match f m:
    case 0n x:
      Grows.refl(s)
    case 1n+p None{}:
      Grows.refl(s)
    case 1n+(+p) Some{+h}:
      +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
      +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
      Grows.when(
        s,
        Replicas.Heads.level(Some{h}, m1),
        s1,
        Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
        Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h)),
        Grows.trans(
          s,
          s1,
          Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1)
        )(Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h)))(Advances.at.grows(p, s1, c, m1))
      )

# a head that moves over each decided step only grows a node
def Advances.grows(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.advances(~Stepping.Ask.kernel(), f, s, c)) == True{}: Bool}:
  Advances.at.grows(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# what a node does at a head only grows it
def Step.head.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Step.head(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  +s1 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s, c)
  +s2 = Replicas.Node.cast(~Stepping.Ask.kernel(), n, s1, c)
  +s3 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s2, c)
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Open.at(~Basics.Ask.machine(), s, c, m)) == True{}: Bool}:
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Replicas.Head{
          r,
          Some{b},
          0,
          Replicas.Branch.first(~Basics.Ask.machine(), s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
        }: Replicas.Head
      }
      Grows.to(s, s, Replicas.State.head(~Basics.Ask.machine(), s, c, hd), Led.head(s, c, hd), Grows.refl(s))
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  +s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Grows.trans(
    s,
    s1,
    Replicas.Step.head(~Stepping.Ask.kernel(), n, s1, c)
  )(Open.at.grows(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.head.grows(n, s1, c))

# a pass to the next round only grows a node
def Pass.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  +s1 = Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Grows.trans(
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
  )(Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.grows(n, s1, c))

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.First.at(~Basics.Ask.machine(), s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      Grows.refl(s)
    case Some{Replicas.Head{r, b, n, None{}}}:
      Grows.to(s, s, Replicas.State.head(~Basics.Ask.machine(), s, c, h), Led.head(s, c, h), Grows.refl(s))
    case None{}:
      Grows.to(s, s, Replicas.State.head(~Basics.Ask.machine(), s, c, h), Led.head(s, c, h), Grows.refl(s))

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Start.head(~Basics.Ask.machine(), s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Grows.trans(
          s,
          x,
          Replicas.State.first(~Basics.Ask.machine(), x, c, h)
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(First.at.grows(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c)))

# the first keys of a store are on a node that grew
def Firsts.after(
  +s: Replicas.Node<Basics.Ask>,
  os: List<&2, Replicas.Owner>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Work.after(s, Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, m)) == True{}: Bool}:
  match os:
    case Nil{}:
      e => e
    case Con{Replicas.Owner{+n, +k}, r}:
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
} -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Start.with(~Basics.Ask.machine(), s, i, os, m)) == True{}: Bool}:
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
  +os: List<&2, Replicas.Owner>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.start(~Stepping.Ask.kernel(), s, i, os)) == True{}: Bool}:
  Start.with.grows(
    s,
    i,
    Replicas.Owner.names(os),
    Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Grows.refl(s)))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Follow.new(~Basics.Ask.machine(), s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(s)
    case None{}:
      Grows.to(
        s,
        s,
        Replicas.State.head(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
        Led.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
        Grows.refl(s)
      )

# a new request only grows a node
def Arrive.grows(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q)) == True{}: Bool}:
  match q:
    case Basics.Ask.Start{os}:
      Start.grows(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Replicas.Node.follow(~Basics.Ask.machine(), s, r, l)
      Grows.to(
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Led.waits(s1, Replicas.Line.chain(r, l), i),
        Follow.new.grows(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))
      )

# a new request only grows a node
def Ask.new.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.ask.new(~Stepping.Ask.kernel(), n, s, e, q)) == True{}: Bool}:
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
  +s1 = Replicas.Node.arrive(~Stepping.Ask.kernel(), s0, i, q)
  Grows.trans(
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
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
  )(Grows.trans(s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c)))

# Node.ask_grows once the cell m of the request's ID is known
def Ask.at.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.ask.at(~Stepping.Ask.kernel(), n, s, e, q, m)) == True{}: Bool}:
  match m:
    case Some{x}:
      Grows.refl(s)
    case None{}:
      Grows.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Replicas.Node.ask.new(~Stepping.Ask.kernel(), 
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )(
        Grows.to(
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Grows.refl(s)
        )
      )(
        Ask.new.grows(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Take.asks(~Stepping.Ask.kernel(), cs, old, s)) == True{}: Bool}:
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
        u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
        u => s
      )
      Grows.trans(
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1)
      )(
        Grows.when(
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
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
  ih: @s2: Replicas.Node<Basics.Ask> -> {Replicas.Node.grows(~Basics.Ask.machine(), s2, k(s2)) == True{}: Bool}
) -> {
  State.after(s, m) == True{}: Bool
} -> {
  Replicas.Node.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Sealed.follow(~Stepping.Ask.kernel(), f, s, p, r, n, mb)) == True{}: Bool}:
  match f mb:
    case 0n x:
      Grows.refl(s)
    case 1n+g None{}:
      Grows.refl(s)
    case 1n+(+g) Some{+b}:
      Follow.step.grows(
        s,
        Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b),
        +s2 => Replicas.Sealed.follow(~Stepping.Ask.kernel(), g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n)),
        +s2 => Follow.grows(g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n))
      )(
        Accept.at.grows(
          s,
          b,
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to only grow a node
def Each.grows(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Sealed.each(~Stepping.Ask.kernel(), f, bs, p, s)) == True{}: Bool}:
  match bs:
    case Nil{}:
      Grows.refl(s)
    case Con{+b, +rest}:
      +s1 = Replicas.Sealed.follow(~Stepping.Ask.kernel(), 
        f,
        s,
        p,
        Replicas.Ballot.store(b),
        Replicas.Ballot.node(b),
        Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
      )
      Grows.trans(
        s,
        s1,
        Replicas.Sealed.each(~Stepping.Ask.kernel(), f, rest, p, s1)
      )(
        Follow.grows(
          f,
          s,
          p,
          Replicas.Ballot.store(b),
          Replicas.Ballot.node(b),
          Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        )
      )(Each.grows(f, rest, p, s1))

# a node that takes in what another node sent only grows
def Take.grows(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.take(~Stepping.Ask.kernel(), s, t)) == True{}: Bool}:
  +sent = Replicas.Take.clean(~Basics.Ask.machine(), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Replicas.Take.asks(~Stepping.Ask.kernel(), cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Grows.trans(
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
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
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
    )(
      Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
    )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2))
  )

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {
  Replicas.Node.grows(~Basics.Ask.machine(), 
    Replicas.State.led(~Basics.Ask.machine(), 
      s,
      Ledgers.State.take(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        Replicas.Take.clean(~Basics.Ask.machine(), 
          Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
          Ledgers.State.empty(~Basics.Ask)
        )
      )
    ),
    Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  )
    == True{}: Bool
}:
  +sent = Replicas.Take.clean(~Basics.Ask.machine(), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Replicas.Take.asks(~Stepping.Ask.kernel(), cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Grows.trans(
    s1,
    s2,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
  )(
    Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2))

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
      Replicas.Node.take(~Stepping.Ask.kernel(), 
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
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.take(~Stepping.Ask.kernel(), b, t)),
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
          Replicas.Node.take(~Stepping.Ask.kernel(), b, Replicas.Serve.put(~Basics.Ask.machine(), _, Ledgers.State.empty(~Basics.Ask)))
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
          Replicas.Node.take(~Stepping.Ask.kernel(), 
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{+c, +rest}:
      +s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Grows.trans(
        s,
        s1,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1)
      )(Step.grows(n, s, c))(Steps.grows(n, rest, s1))

# an adoption only grows a node, once the request m is known
def Adopt.ask.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Reading.Request>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Adopt.ask(n, s, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Adopt.head(n, s, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Adopt.at(n, s, c)) == True{}: Bool}:
  Adopt.head.grows(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Adopt.maybe(n, s, m)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Node.adopts(n, cs, s)) == True{}: Bool}:
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Sync.more(f, n, cs, k, bs, pd, s)) == True{}: Bool}:
  match f:
    case 0n:
      Grows.refl(s)
    case 1n+(+p):
      Grows.when(
        s,
        Reading.Lines.level(cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Reading.Sync.more(
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Grows.trans(
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        )(Each.grows(k, bs, pd, s))(Steps.grows(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        Grows.trans(
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Reading.Sync.more(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )
        )(
          Grows.trans(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )(Each.grows(k, bs, pd, s))(Steps.grows(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)))
        )(
          More.grows(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )
        )
      )

# a sync only grows a node
def Sync.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Reading.Node.sync(n, s, t)) == True{}: Bool}:
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  +s3 = Reading.Sync.more(
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
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
          Replicas.Pending.of(bs),
          s2
        )
      )(Adopts.grows(n, cs, s3))
    )
  )

# Asks
# ----

# a slot that holds a cell holds one in a node that grew
def Slot.held_kept(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +k: List<&2, Bool>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), k)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), b), k)
  )
    == True{}: Bool
}:
  Cells.Cell.keeps_some(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), k),
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), b), k)
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Replicas.State.ledger(~Basics.Ask.machine(), b),
      k
    )(g)
  )

# a node that took in a new request of e holds its slot
def Ask.held.new(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask,
  +em: {
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.ask.new(~Stepping.Ask.kernel(), n, s, e, q)),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  +i = Replicas.Envelope.of(e)
  +c = Basics.Ask.chain(i, q)
  +k = Ledgers.Slot.ask(i)
  +en = {Ledgers.Entry.Ask{i, Replicas.Envelope.time(e), q}: Ledgers.Entry<Basics.Ask>}
  +l0 = Ledgers.State.put(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), k, en)
  +s0 = Replicas.State.led(~Basics.Ask.machine(), s, l0)
  +s1 = Replicas.Node.arrive(~Stepping.Ask.kernel(), s0, i, q)
  %Equal.sym(
    Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), k),
    None{},
    em
  ): {
    Maybe.is_some(
      &2,
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), 
          Replicas.Node.step(~Stepping.Ask.kernel(), 
            n,
            Replicas.Node.arrive(~Stepping.Ask.kernel(), 
              Replicas.State.led(~Basics.Ask.machine(), 
                s,
                Ledgers.State.add.of(
                  ~Basics.Ask,
                  ~Basics.Ask.is_eq,
                  Replicas.State.ledger(~Basics.Ask.machine(), s),
                  k,
                  en,
                  _
                )
              ),
              i,
              q
            ),
            c
          )
        ),
        k
      )
    )
      == True{}: Bool
  }
  Slot.held_kept(
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    k,
    Grows.trans(
      s0,
      s1,
      Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
    )(Arrive.grows(s0, i, q))(Step.grows(n, s1, c))
  )(
    %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), s0), l0, Led.led(s, l0)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, Ledgers.State.get(~Basics.Ask, _, k)) == True{}: Bool}
    %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, l0, k), Some{Cells.One{en}}, Ledgers.State.put_get(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), k, en)(em)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _) == True{}: Bool}
    {==})

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  em: {
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )
      == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.ask.at(~Stepping.Ask.kernel(), n, s, e, q, m)),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
        Ledgers.State.get(
          ~Basics.Ask,
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          Ledgers.Slot.ask(Replicas.Envelope.of(e))
        ),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _) == True{}: Bool}
      {==}
    case None{}:
      Ask.held.new(
        n,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        e,
        q,
        (
          %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))), Replicas.State.ledger(~Basics.Ask.machine(), s), Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))): {Ledgers.State.get(~Basics.Ask, _, Ledgers.Slot.ask(Replicas.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
          em)
      )

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  m: String,
  s: Replicas.Node<Basics.Ask>,
  e: Replicas.Envelope,
  q: Basics.Ask,
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, c) == True{}: Bool
} -> {Replicas.Node.ask.at(~Stepping.Ask.kernel(), m, s, e, q, c) == s: Replicas.Node<Basics.Ask>}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Replicas.Node.ask.at(~Stepping.Ask.kernel(), m, s, e, q, None{}) == s: Replicas.Node<Basics.Ask>},
        Shared.Bool.false_ne_true(h)
      )

def Spec.Node.ask_once(n, m, s, e, q, e2, q2):
  h =>
    +a = Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q)
    Ask.once.at(
      m,
      a,
      e2,
      q2,
      Ledgers.State.get(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), a),
        Ledgers.Slot.ask(Replicas.Envelope.of(e2))
      )
    )(
      %Equal.sym(Ledgers.Id, Replicas.Envelope.of(e2), Replicas.Envelope.of(e), h): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), a), Ledgers.Slot.ask(_))) == True{}: Bool}
      Ask.held.at(n, s, e, q, Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e))), {==}))

# Logs
# ----
# A log only gains keys: a key that a log holds, other than the owners and the
# count, holds the same value after any step.

# a read of a tree stays in a node that grew
def Get.grows(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Replicas.Node.get(~Basics.Ask.machine(), a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Node.get(~Basics.Ask.machine(), b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Equal.trans(
    Maybe<&2, List<&2, U32>>,
    Replicas.Node.get(~Basics.Ask.machine(), b, h, k),
    Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), b, h, k),
    Some{v},
    Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), b, h, k),
    Trees.Tree.get_grows(
      ~Replicas.Node<Basics.Ask>,
      ~Replicas.Store.fetch(~Basics.Ask.machine()),
      ~Replicas.Node.grows(~Basics.Ask.machine()),
      ~(
        x => y => hh => w => Ledgers.State.data_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~Basics.Ask.laws(),
          Replicas.State.ledger(~Basics.Ask.machine(), x),
          Replicas.State.ledger(~Basics.Ask.machine(), y),
          hh,
          w
        )
      ),
      a,
      b,
      h,
      k,
      v
    )(
      g
    )(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), a, h, k),
        Replicas.Node.get(~Basics.Ask.machine(), a, h, k),
        Some{v},
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), a, h, k),
          Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), a, h, k),
          Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), a, h, k)
        ),
        e
      )
    )
  )

# Set.kept once whether the node holds the new nodes is known (b)
def Set.kept.if(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  v: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), ws) == b: Bool
  },
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>},
  em: {Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  k2,
  v,
  Replicas.Work.on(~Basics.Ask.machine(), Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{Replicas.State.keep(~Basics.Ask.machine(), s, ws)}), Some{hh})
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +sk = Replicas.State.keep(~Basics.Ask.machine(), s, ws)
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Replicas.Node.get(~Basics.Ask.machine(), sk, Some{hh}, k2),
        Replicas.Node.get(~Basics.Ask.machine(), sk, h, k2),
        Some{v},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), sk, Some{hh}, k2),
          Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, Some{hh}, k2),
          Replicas.Node.get(~Basics.Ask.machine(), sk, h, k2),
          Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, Some{hh}, k2),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, Some{hh}, k2),
            Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, h, k2),
            Replicas.Node.get(~Basics.Ask.machine(), sk, h, k2),
            Trees.Tree.get_other(
              ~Replicas.Node<Basics.Ask>,
              ~Replicas.Store.fetch(~Basics.Ask.machine()),
              ~Replicas.Node.grows(~Basics.Ask.machine()),
              ~(
                p => q => g => w => Ledgers.State.data_grows(
                  ~Basics.Ask,
                  ~Basics.Ask.is_eq,
                  ~Basics.Ask.laws(),
                  Replicas.State.ledger(~Basics.Ask.machine(), p),
                  Replicas.State.ledger(~Basics.Ask.machine(), q),
                  g,
                  w
                )
              ),
              s,
              sk,
              h,
              k,
              x,
              Trees.Put{hh, ws},
              k2
            )(
              Grows.keep(s, ws)
            )(
              hne
            )(
              Equal.trans(
                Maybe<&2, Trees.Put>,
                Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
                Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
                Some{Trees.Put{hh, ws}},
                Equal.sym(
                  Maybe<&2, Trees.Put>,
                  Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
                  Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
                  Trees.Tree.set_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x)
                ),
                em
              )
            )(eb),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Replicas.Node.get(~Basics.Ask.machine(), sk, h, k2),
              Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, h, k2),
              Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, h, k2)
            )
          )
        ),
        Get.grows(s, sk, h, k2, v, Grows.keep(s, ws))(hget)
      )

# Set.kept once the new subtree m is known
def Set.kept.of(
  +s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  em: {Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == m: Maybe<&2, Trees.Put>},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k2, v, Replicas.Work.of(~Basics.Ask.machine(), s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, +ws}}:
      Set.kept.if(
        s,
        h,
        k,
        x,
        k2,
        v,
        hh,
        ws,
        Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), ws),
        {==},
        hne,
        hget,
        em
      )

# a key set in a tree keeps the value of each other key
def Set.kept(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k2, v, Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, k, x)):
  Set.kept.of(s, h, k, x, k2, v, Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x), {==}, hne, hget)

# that the log of the run m, if any, reads the key k2 as v
def Run.Keeps(k2: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Replicas.Run<Basics.Ask>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Replicas.Run{s2, t2}}:
      {Replicas.Node.get(~Basics.Ask.machine(), s2, Replicas.Tip.log(t2), k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# the run of a new log that keeps a key keeps it
def Run.logged.keeps(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  t: Replicas.Tip,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k2, v, m) -> Run.Keeps(k2, v, Replicas.Run.logged(~Basics.Ask.machine(), t, m)):
  match t m:
    case x None{}:
      w => Unit{}
    case Replicas.Tip{c, old, n, os} Some{Replicas.Work{s2, l}}:
      w => w

# a key that a tree does not hold is not a key that it holds, once whether
# they are the same is known (b)
def Keys.differ.if(
  s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == b: Bool},
  e1: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k) == None{}: Maybe<&2, List<&2, U32>>},
  e2: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Replicas.Node.get(~Basics.Ask.machine(), s, h, k),
            Some{v},
            Equal.sym(Maybe<&2, List<&2, U32>>, Replicas.Node.get(~Basics.Ask.machine(), s, h, k), None{}, e1),
            (
              %Equal.sym(List<&2, U32>, k, k2, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)): {Replicas.Node.get(~Basics.Ask.machine(), s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2)
          )
        )
      )

# Add.kept when the log does not hold the new key
def Add.new.kept(
  +s: Replicas.Node<Basics.Ask>,
  +t: Replicas.Tip,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == None{}: Maybe<&2, List<&2, U32>>},
  +hr: {Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(
  k2,
  v,
  Replicas.Run.logged(~Basics.Ask.machine(), t, Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, Replicas.Tip.log(t)}, k, x))
):
  Run.logged.keeps(
    k2,
    v,
    t,
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, Replicas.Tip.log(t)}, k, x)
  )(
    Set.kept(
      s,
      Replicas.Tip.log(t),
      k,
      x,
      k2,
      v,
      Keys.differ.if(
        s,
        Replicas.Tip.log(t),
        k,
        k2,
        v,
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
        {==},
        em,
        hr
      ),
      hr
    )
  )

# Add.kept once the value m of the new key is known
def Add.at.kept(
  r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Replicas.Node.get(~Basics.Ask.machine(), 
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
    k
  )
    == m: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Run.add.at(~Basics.Ask.machine(), r, k, x, m)):
  match r m:
    case Replicas.Run{+s, +t} None{}:
      em => hr => Add.new.kept(s, t, k, x, k2, v, em, hr)
    case y Some{old}:
      em => hr => Unit{}

# a new key in a run's log keeps the value of each key that the log holds
def Add.kept(
  +r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Run.add(~Basics.Ask.machine(), r, k, x)):
  Add.at.kept(
    r,
    k,
    x,
    k2,
    v,
    Replicas.Node.get(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)), k)
  )({==})

# a run, then a run from it that keeps a key, keeps it
def Keeps.bind(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -f: Replicas.Run<Basics.Ask> -> Maybe<&2, Replicas.Run<Basics.Ask>>
) -> Run.Keeps(
  k2,
  v,
  m
) -> (
  @r: Replicas.Run<Basics.Ask> -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, f(r))
) -> Run.Keeps(k2, v, Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{r}:
      hm => hf => hf(r)(hm)

# one of two runs, each of which keeps a key that the run r keeps
def Keeps.when(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Replicas.Run<Basics.Ask>,
  b: Bool,
  -mx: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -my: Maybe<&2, Replicas.Run<Basics.Ask>>,
  hx: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, mx),
  hy: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, my)
) -> Run.Keeps(
  k2,
  v,
  Some{r}
) -> Run.Keeps(k2, v, Shared.Bool.when(Maybe<&2, Replicas.Run<Basics.Ask>>, b, u => mx, u => my)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a run one version on keeps each key of its log
def Next.kept(
  r: Replicas.Run<Basics.Ask>,
  -own: Maybe<&2, List<&2, String>>,
  -k2: List<&2, U32>,
  -v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Some{Replicas.Run.next(~Basics.Ask.machine(), r, own)}):
  match r:
    case Replicas.Run{s, Replicas.Tip{c, l, n, os}}:
      hr => hr

# a taken request keeps each key of a run's log
def Taken.kept(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.taken(~Basics.Ask.machine(), r, i, own)):
  +n = Replicas.Tip.count(Replicas.Run.tip(~Basics.Ask.machine(), r))
  hr => Keeps.bind(
    k2,
    v,
    Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Replicas.Run<Basics.Ask>,
      Replicas.Run<Basics.Ask>,
      Replicas.Run.add(~Basics.Ask.machine(), 
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
      ),
      r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)}
    )
  )(
    Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n}), k2, v)(hr)
  )(
    +r1 => h1 => Keeps.bind(
      k2,
      v,
      Replicas.Run.add(~Basics.Ask.machine(), 
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
      ),
      r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)}
    )(
      Add.kept(
        r1,
        Replicas.Log.version(n),
        Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))}),
        k2,
        v
      )(h1)
    )(r2 => h2 => Next.kept(r2, own, k2, v)(h2))
  )

# a run over a node that grew keeps each key of its log
def Over.kept(
  r: Replicas.Run<Basics.Ask>,
  s2: Replicas.Node<Basics.Ask>,
  -h: Maybe<&2, Hashes.Hash>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), s2) == True{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Some{Replicas.Run.over(~Basics.Ask.machine(), r, s2, h)}):
  match r:
    case Replicas.Run{s, Replicas.Tip{c, l, n, os}}:
      hr => Get.grows(s, s2, l, k2, v, g)(hr)

# a judged request keeps each key of a run's log, other than the owners and
# the count
def Judged.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Verdict.after(Replicas.Run.state(~Basics.Ask.machine(), r), m) == True{}: Bool
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.judged(~Basics.Ask.machine(), r, i, own, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Replicas.Verdict.Stale{}}:
      g => hr => Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)(hr)
    case Some{Replicas.Verdict.Taken{Replicas.Work{+s2, h}}}:
      g => hr => Taken.kept(
        Replicas.Run.over(~Basics.Ask.machine(), r, s2, h),
        i,
        own,
        k2,
        v
      )(Over.kept(r, s2, h, k2, v, g)(hr))

# a mark on a version keeps each key of a run's log, other than the owners
# and the count
def Marked.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +m: String,
  x: Maybe<&2, Replicas.Version>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, x)):
  match x:
    case None{}:
      hr => Unit{}
    case Some{+y}:
      hr => Keeps.bind(
        k2,
        v,
        Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(y), [])),
        r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{})
      )(
        Add.kept(r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(y), []), k2, v)(hr)
      )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v)(h2))

# a request for a mark keeps each key of a run's log, other than the owners
# and the count
def Mark.kept(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +m: String,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.mark(~Basics.Ask.machine(), r, i, m)):
  +s = Replicas.Run.state(~Basics.Ask.machine(), r)
  +t = Replicas.Run.tip(~Basics.Ask.machine(), r)
  +n = Replicas.Tip.count(t)
  Keeps.when(
    k2,
    v,
    r,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Replicas.Line.mark(~Basics.Ask.machine(), s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Replicas.Step.stale(~Basics.Ask.machine(), r, i),
    Marked.kept(r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1)), k2, v),
    Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
  )

# the first tip of a new branch keeps each key of a run's log, other than the
# owners and the count
def Branch.made.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Replicas.Made<Basics.Ask>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> {
  Made.after(Replicas.Run.state(~Basics.Ask.machine(), r), m) == True{}: Bool
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Branch.made(~Basics.Ask.machine(), r, i, b, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Replicas.Made{+t, +s2}}:
      g => hr =>
        +r1 = {Replicas.Run.over(~Basics.Ask.machine(), r, s2, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r))): Replicas.Run<Basics.Ask>}
        Keeps.bind(
          k2,
          v,
          Replicas.Run.add(~Basics.Ask.machine(), r1, Replicas.Log.start(b), Hashes.Hash.code(Replicas.Tip.hash(t), [])),
          r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{})
        )(
          Add.kept(
            r1,
            Replicas.Log.start(b),
            Hashes.Hash.code(Replicas.Tip.hash(t), []),
            k2,
            v
          )(Over.kept(r, s2, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)), k2, v, g)(hr))
        )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v)(h2))

# a request for a branch keeps each key of a run's log, other than the owners
# and the count, once it is known whether its version is one
def Branch.ready.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Branch.ready(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{False{}}:
      Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
    case Some{True{}}:
      Keeps.when(
        k2,
        v,
        r,
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Basics.Node.root_of(Replicas.Run.state(~Basics.Ask.machine(), r), at)
        ),
        Replicas.Branch.made(~Basics.Ask.machine(), 
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        ),
        None{},
        Branch.made.kept(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          ),
          k2,
          v
        )(
          Grown.make.first(
            Replicas.Run.state(~Basics.Ask.machine(), r),
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )(Grown.make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at))
        ),
        hr => Unit{}
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count
def Branch.new.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Branch.new(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Some{x}}:
      Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
    case Some{None{}}:
      Branch.ready.kept(
        r,
        i,
        st,
        b,
        at,
        Judging.Judge.ready_maybe(Replicas.Run.state(~Basics.Ask.machine(), r), at),
        k2,
        v
      )

# On.kept once it is known how the line takes the change (w)
def On.of.kept(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.on.of(r, i, st, l, ch, w)):
  match w:
    case Stepping.Route.Mark{a}:
      hr => Mark.kept(r, i, a, k2, v)(hr)
    case Stepping.Route.Branch{+a, b}:
      Branch.new.kept(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(~Basics.Ask.machine(), 
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Log.start(a)
        ),
        k2,
        v
      )
    case Stepping.Route.Judge{}:
      hr => Judged.kept(
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
        ),
        k2,
        v
      )(
        Verdict.change(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
        )
      )(hr)

# a change of a line keeps each key of a run's log, other than the owners and
# the count
def On.kept(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.on(r, i, st, l, ch)):
  On.of.kept(r, i, st, l, ch, Stepping.Route.of(l, ch), k2, v)

# a request keeps each key of a run's log, other than the owners and the count
def Change.kept(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Basics.Ask,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.change(r, c, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      hr => Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)(hr)
    case Basics.Ask.On{+st, +l, ch}:
      Keeps.when(
        k2,
        v,
        r,
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        On.kept(r, i, st, l, ch, k2, v),
        Add.kept(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
      )

# a request that the node holds or not keeps each key of a run's log
def Asked.kept(
  r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.asked(~Stepping.Ask.kernel(), r, c, i, a)):
  match a:
    case None{}:
      hr => Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.kept(r, c, i, q, k2, v)

# a request that the log holds or not keeps each key of a run's log
def Fresh.kept(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Replicas.Out>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Replicas.Step.fresh(~Stepping.Ask.kernel(), r, c, i, o)):
  match o:
    case Some{x}:
      hr => hr
    case None{}:
      Asked.kept(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), i), k2, v)

# the requests of a step keep each key of a run's log, other than the owners
# and the count
def All.kept(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Run.Keeps(k2, v, m) -> Run.Keeps(k2, v, Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m)):
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.kept(
        c,
        rest,
        Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i)),
        k2,
        v
      )(
        Keeps.bind(
          k2,
          v,
          m,
          r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i)
        )(
          h
        )(
          +r => hr => Fresh.kept(
            r,
            c,
            i,
            Replicas.Line.out(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Run.tip(~Basics.Ask.machine(), r), i),
            k2,
            v
          )(hr)
        )
      )

# a log only gains keys: a key that the log of a tip holds, other than the
# owners and the count, holds the same value after a step
def Run.kept(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)):
  match t:
    case Replicas.Tip{c0, l, n, os}:
      h => All.kept(c, qs, Some{Replicas.Run{s, Replicas.Tip{c0, l, n, os}}}, k2, v)(h)

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +x: Hashes.Hash,
  -t: Replicas.Tip,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Replicas.Tip.at(~Basics.Ask.machine(), a, x) == Some{t}: Maybe<&2, Replicas.Tip>
} -> {Replicas.Tip.at(~Basics.Ask.machine(), b, x) == Some{t}: Maybe<&2, Replicas.Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Replicas.Tip,
    Replicas.Store.fetch(~Basics.Ask.machine(), a, x),
    Replicas.Store.fetch(~Basics.Ask.machine(), b, x),
    ws => Replicas.Tip.read(ws),
    ws => Replicas.Tip.read(ws),
    t,
    w => Ledgers.State.data_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Replicas.State.ledger(~Basics.Ask.machine(), b),
      x,
      w
    )(g),
    w => e => e
  )

# the tip of a head, in a node that grew
def Head.tip.grows(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  h: Replicas.Head,
  -t: Replicas.Tip,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Replicas.Head.tip(~Basics.Ask.machine(), a, h) == Some{t}: Maybe<&2, Replicas.Tip>
} -> {Replicas.Head.tip(~Basics.Ask.machine(), b, h) == Some{t}: Maybe<&2, Replicas.Tip>}:
  match h:
    case Replicas.Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Replicas.Tip,
        th,
        th,
        x => Replicas.Tip.at(~Basics.Ask.machine(), a, x),
        x => Replicas.Tip.at(~Basics.Ask.machine(), b, x),
        t,
        x => e => e,
        +x => Tip.at.grows(a, b, x, t, g)
      )

# what the log of a head holds, in a node that grew
def Head.get.grows(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +h: Replicas.Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Replicas.Head.get(~Basics.Ask.machine(), a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Replicas.Tip,
    List<&2, U32>,
    Replicas.Head.tip(~Basics.Ask.machine(), a, h),
    Replicas.Head.tip(~Basics.Ask.machine(), b, h),
    t => Replicas.Node.get(~Basics.Ask.machine(), a, Replicas.Tip.log(t), k),
    t => Replicas.Node.get(~Basics.Ask.machine(), b, Replicas.Tip.log(t), k),
    v,
    t => Head.tip.grows(a, b, h, t, g),
    t => Get.grows(a, b, Replicas.Tip.log(t), k, v, g)
  )

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  eh: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Replicas.Node.head_of(~Basics.Ask.machine(), b, c): Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Line.get(~Basics.Ask.machine(), b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Replicas.Head,
    List<&2, U32>,
    Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
    Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
    h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k),
    h => Replicas.Head.get(~Basics.Ask.machine(), b, h, k),
    v,
    h => e => Equal.trans(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
      Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
      Some{h},
      Equal.sym(Maybe<&2, Replicas.Head>, Replicas.Node.head_of(~Basics.Ask.machine(), a, c), Replicas.Node.head_of(~Basics.Ask.machine(), b, c), eh),
      e
    ),
    +h => Head.get.grows(a, b, h, k, v, g)
  )

# a node keeps its own logs
def Kept.refl(-s: Replicas.Node<Basics.Ask>) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, s):
  c => k => v => e => e

# keeping composes
def Kept.trans(
  -a: Replicas.Node<Basics.Ask>,
  -b: Replicas.Node<Basics.Ask>,
  -d: Replicas.Node<Basics.Ask>,
  h1: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b),
  h2: Replicas.Node.Keeps(~Basics.Ask.machine(), b, d)
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), a, d):
  +c => +k => +v => e => h2(c)(k)(v)(h1(c)(k)(v)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: Replicas.Node.Keeps(~Basics.Ask.machine(), s, x),
  hy: Replicas.Node.Keeps(~Basics.Ask.machine(), s, y)
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b): Tries.Trie<Replicas.Head>}
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), a, b):
  +c => k => v => Line.same(
    a,
    b,
    c,
    k,
    v,
    g,
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  s: Replicas.Node<Basics.Ask>,
  l: Ledgers.State(Basics.Ask)
) -> {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l)): Tries.Trie<Replicas.Head>}:
  match s:
    case Replicas.Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Wait.set(~Basics.Ask.machine(), s, c, qs)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), 
    Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
    c2
  )
    == Bool.pick(
      Maybe<&2, Replicas.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
    ): Maybe<&2, Replicas.Head>
}:
  match b0:
    case Replicas.Node{l, hs, ws, ks}:
      Tries.Trie.get_set(Replicas.Head, hs, Ledgers.Chain.key(c), hd, Ledgers.Chain.key(c2))

# a pick, once what it picks by is known
def Pick.of(
  -A: Data,
  b: Bool,
  -p: Bool,
  -x: A,
  -y: A,
  eb: {p == b: Bool}
) -> {Bool.pick(A, p, x, y) == Bool.pick(A, b, x, y): A}:
  %eb: {Bool.pick(A, p, x, y) == Bool.pick(A, _, x, y): A}
  {==}

# what a line holds, once its head m is known
def Line.get.of(
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Replicas.Head>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == m: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    List<&2, U32>,
    m,
    h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {
      Maybe.bind(
        &2,
        Replicas.Head,
        List<&2, U32>,
        _,
        h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  +a: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +hd: Replicas.Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  cov: {
    Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Head.get(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Line.get(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Replicas.Head>,
          Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
          Some{hd},
          Equal.trans(
            Maybe<&2, Replicas.Head>,
            Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
            Bool.pick(
              Maybe<&2, Replicas.Head>,
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
            ),
            Some{hd},
            Head.of_set(b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Replicas.Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Replicas.Head,
            List<&2, U32>,
            _,
            h => Replicas.Head.get(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Replicas.Line.get(~Basics.Ask.machine(), a, c, k),
            Replicas.Line.get(~Basics.Ask.machine(), a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Replicas.Head,
                List<&2, U32>,
                Tries.Trie.get(Replicas.Head, Replicas.State.heads(~Basics.Ask.machine(), a), kk),
                h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
              ),
              Ledgers.Chain.key(c),
              Ledgers.Chain.key(c2),
              Equal.sym(
                List<&2, Bool>,
                Ledgers.Chain.key(c2),
                Ledgers.Chain.key(c),
                Shared.List.is_eq_sound(
                  ~Bool,
                  ~Shared.Bool.is_eq,
                  ~Shared.Bool.laws(),
                  Ledgers.Chain.key(c2),
                  Ledgers.Chain.key(c)
                )(ebs)
              )
            ),
            e
          )
        )
    case False{}:
      Line.same(
        a,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        c2,
        k,
        v,
        Grows.to(
          a,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Led.head(b0, c, hd),
          g
        ),
        Equal.trans(
          Maybe<&2, Replicas.Head>,
          Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
          Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
          Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
          Equal.cong(
            Tries.Trie<Replicas.Head>,
            Maybe<&2, Replicas.Head>,
            hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c2)),
            Replicas.State.heads(~Basics.Ask.machine(), a),
            Replicas.State.heads(~Basics.Ask.machine(), b0),
            eh
          ),
          Equal.sym(
            Maybe<&2, Replicas.Head>,
            Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
            Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
            Equal.trans(
              Maybe<&2, Replicas.Head>,
              Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
              Bool.pick(
                Maybe<&2, Replicas.Head>,
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
              ),
              Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
              Head.of_set(b0, c, hd, c2),
              Pick.of(
                Maybe<&2, Replicas.Head>,
                False{},
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
                ebs
              )
            )
          )
        )
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  hd: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Head.get(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), a, Replicas.State.head(~Basics.Ask.machine(), b0, c, hd)):
  +c2 => +k => +v => Head.put.kept.if(
    a,
    b0,
    c,
    hd,
    c2,
    k,
    v,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    cover(k)(v)
  )

# one of two nodes, each with the heads of s
def Heads.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), x): Tries.Trie<Replicas.Head>},
  hy: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), y): Tries.Trie<Replicas.Head>}
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)): Tries.Trie<Replicas.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  s: Replicas.Node<Basics.Ask>,
  ks: Replicas.Keys
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.State.keyed(~Basics.Ask.machine(), s, ks)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Node<Basics.Ask>>) -> Tries.Trie<Replicas.Head>:
  match m:
    case None{}:
      Replicas.State.heads(~Basics.Ask.machine(), s)
    case Some{s2}:
      Replicas.State.heads(~Basics.Ask.machine(), s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  hx: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), x): Tries.Trie<Replicas.Head>}
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Heads.of(s, Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{x})): Tries.Trie<Replicas.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  +s: Replicas.Node<Basics.Ask>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Replicas.Keychain>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, Replicas.Seal.accept.at(~Basics.Ask.machine(), s, b, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(
        Replicas.Seal.fits(c, b),
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), 
          Replicas.State.led(~Basics.Ask.machine(), 
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Replicas.Keys.saw(
            Replicas.Keys.set(
              Replicas.State.keys(~Basics.Ask.machine(), s),
              Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
              Replicas.Keychain.next(c, b)
            ),
            Replicas.Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<Replicas.Head>,
          Replicas.State.heads(~Basics.Ask.machine(), s),
          Replicas.State.heads(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            )
          ),
          Replicas.State.heads(~Basics.Ask.machine(), 
            Replicas.State.keyed(~Basics.Ask.machine(), 
              Replicas.State.led(~Basics.Ask.machine(), 
                s,
                Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
              ),
              Replicas.Keys.saw(
                Replicas.Keys.set(
                  Replicas.State.keys(~Basics.Ask.machine(), s),
                  Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                  Replicas.Keychain.next(c, b)
                ),
                Replicas.Ballot.at(b)
              )
            )
          ),
          Heads.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Heads.keyed(
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Replicas.Keys.saw(
              Replicas.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                Replicas.Keychain.next(c, b)
              ),
              Replicas.Ballot.at(b)
            )
          )
        )
      )

# the node m, if any, else s, has the heads of s when m has
def Default.heads(
  -s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, m): Tries.Trie<Replicas.Head>
} -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Maybe.default(&2, Replicas.Node<Basics.Ask>, m, s)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Replicas.Keychain>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.seal(~Stepping.Ask.kernel(), s, w, n, a0, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Replicas.Seal.secret(Replicas.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)), Replicas.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Replicas.Seal.secret(
            Replicas.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)),
            Replicas.Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.heads(
        s,
        Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b)
      )(
        Accept.at.heads(
          s,
          b,
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        )
      )

# a ballot keeps the heads
def Cast.vote.heads(
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.vote(~Stepping.Ask.kernel(), s, m, w, n, a0)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
      Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s4),
        Replicas.State.heads(~Basics.Ask.machine(), 
          Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
        ),
        Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
        Cast.seal.heads(s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  -s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  -k: Replicas.Node<Basics.Ask> -> Replicas.Node<Basics.Ask>,
  ih: @s2: Replicas.Node<Basics.Ask> -> {
    Replicas.State.heads(~Basics.Ask.machine(), s2) == Replicas.State.heads(~Basics.Ask.machine(), k(s2)): Tries.Trie<Replicas.Head>
  }
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, m): Tries.Trie<Replicas.Head>
} -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), 
      Maybe.default(
        &2,
        Replicas.Node<Basics.Ask>,
        Maybe.bind(&2, Replicas.Node<Basics.Ask>, Replicas.Node<Basics.Ask>, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s2),
        Replicas.State.heads(~Basics.Ask.machine(), k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Sealed.follow(~Stepping.Ask.kernel(), f, s, p, r, n, mb)): Tries.Trie<Replicas.Head>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.heads(
        s,
        Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b),
        +s2 => Replicas.Sealed.follow(~Stepping.Ask.kernel(), g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n)),
        +s2 => Follow.heads(g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n))
      )(
        Accept.at.heads(
          s,
          b,
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the heads
def Each.heads(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Sealed.each(~Stepping.Ask.kernel(), f, bs, p, s)): Tries.Trie<Replicas.Head>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Replicas.Sealed.follow(~Stepping.Ask.kernel(), 
        f,
        s,
        p,
        Replicas.Ballot.store(b),
        Replicas.Ballot.node(b),
        Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s1),
        Replicas.State.heads(~Basics.Ask.machine(), Replicas.Sealed.each(~Stepping.Ask.kernel(), f, rest, p, s1)),
        Follow.heads(
          f,
          s,
          p,
          Replicas.Ballot.store(b),
          Replicas.Ballot.node(b),
          Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        ),
        Each.heads(f, rest, p, s1)
      )

# a vote keeps the heads
def Cast.put.heads(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  s: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, qs, from, m, s)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Run{s2, +t2}}:
      Cast.vote.heads(
        s,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Pass.to(~Stepping.Ask.kernel(), n, s, w, os)): Tries.Trie<Replicas.Head>
}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        s,
        Replicas.Cast.seal(~Stepping.Ask.kernel(), 
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Replicas.Last.below(~Basics.Ask.machine(), n, s, c, h, r)},
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.heads(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Replicas.Last.below(~Basics.Ask.machine(), n, s, c, h, r)},
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        {==}
      )

# a node that joins a round keeps the heads
def Round.join.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Round.join(~Stepping.Ask.kernel(), n, s, c, h, os)): Tries.Trie<Replicas.Head>
}:
  +top = Replicas.Round.seen(~Basics.Ask.machine(), s, c, h)
  k = top
  Heads.when(
    Nat.is_lt(Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, h, k), top),
    s,
    Replicas.Pass.to(~Stepping.Ask.kernel(), n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.heads(n, s, Ledgers.Where{c, h, top}, os),
    {==}
  )

# a ballot in the node's round keeps the heads
def Cast.round.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Replicas.Tip
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.round(~Stepping.Ask.kernel(), n, s, c, next, th, t)): Tries.Trie<Replicas.Head>
}:
  +os = Replicas.Tip.owners(t)
  +r = Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, next, Replicas.Round.seen(~Basics.Ask.machine(), s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Replicas.Plan.of(~Stepping.Ask.kernel(), 
    n,
    s,
    c,
    w,
    t,
    th,
    os,
    Replicas.Owners.turn(os, U32.add(next, U32.from_nat(r)))
  )
  Heads.when(
    Replicas.Cast.may(~Basics.Ask.machine(), n, s, w, t, Replicas.Plan.asks(~Basics.Ask.machine(), p)),
    s,
    Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, Replicas.Plan.asks(~Basics.Ask.machine(), p), Replicas.Plan.from(~Basics.Ask.machine(), p), Replicas.Plan.run(~Basics.Ask.machine(), p), s),
    s,
    Cast.put.heads(n, w, th, Replicas.Plan.asks(~Basics.Ask.machine(), p), Replicas.Plan.from(~Basics.Ask.machine(), p), Replicas.Plan.run(~Basics.Ask.machine(), p), s),
    {==}
  )

# Node.cast keeps the heads, at the head h whose tip is m
def Cast.at.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.at(~Stepping.Ask.kernel(), n, s, c, h, m)): Tries.Trie<Replicas.Head>
}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{+t}:
      s1 = Replicas.Round.join(~Stepping.Ask.kernel(), n, s, c, next, Replicas.Tip.owners(t))
      Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s1),
        Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.round(~Stepping.Ask.kernel(), n, s1, c, next, th, t)),
        Round.join.heads(n, s, c, next, Replicas.Tip.owners(t)),
        Cast.round.heads(n, s1, c, next, th, t)
      )
    case Replicas.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Pass.at(~Stepping.Ask.kernel(), n, s, c, h, m)): Tries.Trie<Replicas.Head>
}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{t}:
      Pass.to.heads(
        n,
        s,
        Ledgers.Where{c, next, 1n+Replicas.Round.mine(~Basics.Ask.machine(), n, s, c, next, Replicas.Round.seen(~Basics.Ask.machine(), s, c, next))},
        Replicas.Tip.owners(t)
      )
    case Replicas.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.Cast.head(~Stepping.Ask.kernel(), n, s, c, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# a node's ballot keeps its logs
def Cast.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c)):
  Kept.same(
    s,
    Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c),
    Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  )

# the words of a tip read as the tip
def Tip.round(
  t: Replicas.Tip
) -> {Replicas.Tip.read(Replicas.Tip.words(t)) == Some{t}: Maybe<&2, Replicas.Tip>}:
  match t:
    case Replicas.Tip{+c, +l, +n, +os}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Replicas.Tip>>,
        Codes.Code.four.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Replicas.Tip,
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(U32, Codes.Code.token.codec()),
          ~Codes.Codec.dec(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec())),
          x => y => z => w => Replicas.Tip{x, y, z, w},
          Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(c)(
            Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(l)(
              Codes.Codec.enc(U32, Codes.Code.token.codec())(n)(Codes.Codec.enc(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec()))(os)([]))
            )
          )
        ),
        Some{Codes.Read{Replicas.Tip{c, l, n, os}, []}},
        Codes.Code.four_read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Replicas.Tip,
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.token.codec(),
          ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
          x => y => z => w => Replicas.Tip{x, y, z, w},
          c,
          l,
          n,
          os,
          []
        )
      ): {Replicas.Read.whole(Replicas.Tip, _) == Some{Replicas.Tip{c, l, n, os}}: Maybe<&2, Replicas.Tip>}
      {==}

# Put.holds once whether the node holds the data is known (b)
def Put.holds.if(
  -s2: Replicas.Node<Basics.Ask>,
  -ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>,
  b: Bool,
  eb: {
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s2, ds), ds) == b: Bool
  }
) -> {
  Shared.Maybe.when(
    Replicas.Node<Basics.Ask>,
    b,
    u => Some{Replicas.State.keep(~Basics.Ask.machine(), s2, ds)}
  )
    == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Node<Basics.Ask>, s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Replicas.Node<Basics.Ask>,
          Replicas.State.keep(~Basics.Ask.machine(), s2, ds),
          s3,
          e
        ): {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  s2: Replicas.Node<Basics.Ask>,
  +ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.put(~Basics.Ask.machine(), s2, ds) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool}:
  Put.holds.if(
    s2,
    ds,
    s3,
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  s2: Replicas.Node<Basics.Ask>,
  ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>,
  e: {Replicas.State.put(~Basics.Ask.machine(), s2, ds) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>}
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s2, s3) == True{}: Bool}:
  %e: {State.after(s2, _) == True{}: Bool}
  Put.grows(s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  s2: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  +s3: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Replicas.Store.fetch(~Basics.Ask.machine(), s3, Hashes.Sha.hash(Replicas.Tip.words(t2))),
      Some{Replicas.Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Replicas.Store.fetch(~Basics.Ask.machine(), s3, Hashes.Sha.hash(Replicas.Tip.words(t2))),
        Some{Replicas.Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Stores.Store.has(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, Replicas.Tip.words(t2)),
          u => Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, [])
        )(Put.holds(s2, [Replicas.Tip.words(t2)], s3)(e))
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Replicas.Tip,
        _,
        ws => Replicas.Tip.read(ws)
      )
        == Some{t2}: Maybe<&2, Replicas.Tip>
    }
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  -s: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Replicas.Head,
  -t: Replicas.Tip,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, U32>,
        _,
        t1 => Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    Line.get.of(s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  +s3: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Replicas.Node.grows(~Basics.Ask.machine(), s3, b) == True{}: Bool},
  e3: {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>},
  v3: {Replicas.Node.get(~Basics.Ask.machine(), s3, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Replicas.Head.get(~Basics.Ask.machine(), 
    b,
    Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}},
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Replicas.Tip>,
    Replicas.Tip.at(~Basics.Ask.machine(), b, Replicas.Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(s3, b, Replicas.Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      _,
      t1 => Replicas.Node.get(~Basics.Ask.machine(), b, Replicas.Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  Get.grows(s3, b, Replicas.Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  +s: Replicas.Node<Basics.Ask>,
  +s3: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  t: Replicas.Tip,
  g3: {Replicas.Node.grows(~Basics.Ask.machine(), s, s3) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>},
  e3: {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Node.get(~Basics.Ask.machine(), s3, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), 
  s,
  Replicas.State.moved(~Basics.Ask.machine(), 
    Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
    c,
    Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}},
    qs
  )
):
  +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +ws = Replicas.Wait.left(
    Replicas.Wait.of(~Basics.Ask.machine(), x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Replicas.Wait.set(~Basics.Ask.machine(), x, c, ws)
  +hd = {Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}}: Replicas.Head}
  Head.put.kept(
    s,
    b0,
    c,
    hd,
    Grows.to(s, x, b0, Led.wait(x, c, ws), Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Replicas.Head>,
      Replicas.State.heads(~Basics.Ask.machine(), s),
      Replicas.State.heads(~Basics.Ask.machine(), x),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
      Heads.wait(x, c, ws)
    ),
    +k => +v => e => Moved.cover(
      s3,
      Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
      t2,
      k,
      v,
      r,
      br,
      nx,
      Grows.to(
        s3,
        s3,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        Equal.trans(
          Ledgers.State(Basics.Ask),
          Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd)),
          Replicas.State.ledger(~Basics.Ask.machine(), b0),
          Replicas.State.ledger(~Basics.Ask.machine(), s3),
          Led.head(b0, c, hd),
          Equal.trans(
            Ledgers.State(Basics.Ask),
            Replicas.State.ledger(~Basics.Ask.machine(), b0),
            Replicas.State.ledger(~Basics.Ask.machine(), x),
            Replicas.State.ledger(~Basics.Ask.machine(), s3),
            Led.wait(x, c, ws),
            Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          )
        ),
        Grows.refl(s3)
      ),
      e3,
      kk(k)(v)(Line.read.at(s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  +s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  t: Replicas.Tip,
  g2: {Replicas.Node.grows(~Basics.Ask.machine(), s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Node.get(~Basics.Ask.machine(), s2, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]) == m: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), 
  s,
  Replicas.Advance.moved(~Basics.Ask.machine(), s, m, c, Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}}, qs)
):
  match m:
    case None{}:
      e2 => Kept.refl(s)
    case Some{+s3}:
      +e2 => Moved.kept(
        s,
        s3,
        c,
        r,
        br,
        nx,
        t2,
        qs,
        h,
        t,
        Grows.trans(s, s2, s3)(g2)(Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(s2, t2, s3)(e2),
        +k => +v => e => Get.grows(
          s2,
          s3,
          Replicas.Tip.log(t2),
          k,
          v,
          Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)
        )(kk(k)(v)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  h: Replicas.Head,
  t: Replicas.Tip,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
) -> {
  Run.after(s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Run.Keeps(k, v, m)
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(s)
    case Some{Replicas.Run{+s2, +t2}}:
      ga => rk => Kept.when(
        Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        s,
        Replicas.Advance.moved(~Basics.Ask.machine(), 
          s,
          Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
          c,
          Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(
          s,
          s2,
          Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
          c,
          r,
          br,
          U32.inc(next),
          t2,
          qs,
          h,
          t,
          ga,
          em,
          et,
          rk
        )({==}),
        Kept.refl(s)
      )

# Node.advance keeps the logs, once the decided step m is known
def Advance.step.kept(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Advance.step(~Stepping.Ask.kernel(), s, c, h, t, m)):
  match h m:
    case Replicas.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, after}}:
      +em => +et => Kept.when(
        Replicas.Root.same(before, th),
        s,
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Advance.ran.kept(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs),
          Replicas.Head{r, br, next, th},
          t,
          em,
          et
        )(
          Run.grows(s, c, t, qs)
        )(+k => +v => Run.kept(s, c, t, qs, k, v)),
        Kept.refl(s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => Kept.refl(s)

# Node.advance keeps the logs, at the head h whose tip is m
def Advance.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, m)):
  match m:
    case None{}:
      em => et => Kept.refl(s)
    case Some{+t}:
      em => et => Advance.step.kept(
        s,
        c,
        h,
        t,
        Replicas.Height.decide(~Basics.Ask.machine(), 
          s,
          c,
          Replicas.Head.next(h),
          Replicas.Tip.owners(t),
          Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
        )
      )(em)(et)

# Advances.kept once the head m is known
def Advances.at.kept(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Advances.at(~Stepping.Ask.kernel(), f, s, c, m)):
  match f m:
    case 0n x:
      em => Kept.refl(s)
    case 1n+p None{}:
      em => Kept.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Kept.when(
          Replicas.Heads.level(Some{h}, m1),
          s,
          s1,
          Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
          Advance.at.kept(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Kept.trans(
            s,
            s1,
            Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
            Advance.at.kept(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
            Advances.at.kept(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step keeps the logs
def Advances.kept(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.advances(~Stepping.Ask.kernel(), f, s, c)):
  Advances.at.kept(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Step.head(~Stepping.Ask.kernel(), n, s, c)):
  +s1 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s, c)
  +s2 = Replicas.Node.cast(~Stepping.Ask.kernel(), n, s1, c)
  s3 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s2, c)
  Kept.trans(
    s,
    s1,
    s3,
    Advances.kept(4294967295n, s, c),
    Kept.trans(s1, s2, s3, Cast.kept(n, s1, c), Advances.kept(4294967295n, s2, c))
  )

# a line with no head holds nothing
def Cover.none(
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -b: Replicas.Node<Basics.Ask>,
  -hd: Replicas.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == None{}: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -b: Replicas.Node<Basics.Ask>,
  -hd: Replicas.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Some{Replicas.Head{r, br, n, None{}}}: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(a, c, k, v, Some{Replicas.Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Open.at(~Basics.Ask.machine(), s, c, m)):
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Replicas.Head{
            r,
            Some{b},
            0,
            Replicas.Branch.first(~Basics.Ask.machine(), s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
          }: Replicas.Head
        }
        Head.put.kept(
          s,
          s,
          c,
          hd,
          Grows.refl(s),
          {==},
          k => v => Cover.wait(
            s,
            c,
            Replicas.State.head(~Basics.Ask.machine(), s, c, hd),
            hd,
            k,
            v,
            r,
            Some{b},
            n,
            em
          )
        )
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      em => Kept.refl(s)
    case None{}:
      em => Kept.refl(s)

# what a node does on a line keeps the logs
def Step.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)):
  s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Kept.trans(
    s,
    s1,
    Replicas.Step.head(~Stepping.Ask.kernel(), n, s1, c),
    Open.at.kept(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c)):
  +s1 = Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Kept.trans(
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Kept.same(
      s,
      s1,
      Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      Pass.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
    ),
    Step.kept(n, s1, c)
  )

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.First.at(~Basics.Ask.machine(), s, c, h, m)):
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Replicas.Head{r, b, n, None{}}}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        k => v => Cover.wait(s, c, Replicas.State.head(~Basics.Ask.machine(), s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        k => v => Cover.none(s, c, Replicas.State.head(~Basics.Ask.machine(), s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Start.head(~Basics.Ask.machine(), s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Kept.trans(
          s,
          x,
          Replicas.State.first(~Basics.Ask.machine(), x, c, h),
          Kept.same(
            s,
            x,
            Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          ),
          First.at.kept(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c))({==})
        )

# Start.kept once the content m of the store is known
def Start.with.kept(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Start.with(~Basics.Ask.machine(), s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{Replicas.Work{+s2, +c}}:
      e =>
        +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
        Start.head.kept(
          s,
          s2,
          Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Replicas.Tip.words(t)]))

# a store that starts keeps the logs
def Start.kept(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Replicas.Owner>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.start(~Stepping.Ask.kernel(), s, i, os)):
  Start.with.kept(
    s,
    i,
    Replicas.Owner.names(os),
    Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Grows.refl(s)))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Follow.new(~Basics.Ask.machine(), s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(s)
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        Replicas.Line.chain(r, l),
        Replicas.Head{r, l, 0, None{}},
        Grows.refl(s),
        {==},
        k => v => Cover.none(
          s,
          Replicas.Line.chain(r, l),
          Replicas.State.head(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
          Replicas.Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.State.wait(~Basics.Ask.machine(), s, c, i)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a new request keeps the logs
def Arrive.kept(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      Start.kept(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Replicas.Node.follow(~Basics.Ask.machine(), s, r, l)
      Kept.trans(
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Follow.new.kept(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Kept.same(
          s1,
          Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
          Grows.to(
            s1,
            s1,
            Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Led.waits(s1, Replicas.Line.chain(r, l), i),
            Grows.refl(s1)
          ),
          Heads.waits(s1, Replicas.Line.chain(r, l), i)
        )
      )

# a new request keeps the logs
def Ask.new.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.ask.new(~Stepping.Ask.kernel(), n, s, e, q)):
  +i = Replicas.Envelope.of(e)
  c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Replicas.State.ledger(~Basics.Ask.machine(), s),
    i,
    Replicas.Envelope.time(e),
    q
  )
  +s0 = Replicas.State.led(~Basics.Ask.machine(), s, l0)
  s1 = Replicas.Node.arrive(~Stepping.Ask.kernel(), s0, i, q)
  Kept.trans(
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Kept.same(
      s,
      s0,
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
      ),
      Heads.led(s, l0)
    ),
    Kept.trans(s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c), Arrive.kept(s0, i, q), Step.kept(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.ask.at(~Stepping.Ask.kernel(), n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(s)
    case None{}:
      Kept.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Replicas.Node.ask.new(~Stepping.Ask.kernel(), 
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        ),
        Kept.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Grows.refl(s)
          ),
          Heads.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
        ),
        Ask.new.kept(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask keeps the logs
def Ask.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q)):
  Ask.at.kept(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e)))
  )

# the new requests among cells keep the logs
def Take.asks.kept(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Take.asks(~Stepping.Ask.kernel(), cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Replicas.Node<Basics.Ask>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
        u => s
      )
      Kept.trans(
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1),
        Kept.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
          s,
          Arrive.kept(s, i, q),
          Kept.refl(s)
        ),
        Take.asks.kept(rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.kept(rest, old, s)

# Node.take keeps the logs
def Take.kept(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.take(~Stepping.Ask.kernel(), s, t)):
  +sent = Replicas.Take.clean(~Basics.Ask.machine(), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Replicas.Take.asks(~Stepping.Ask.kernel(), cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Kept.trans(
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
    Kept.same(
      s,
      s1,
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
      ),
      Heads.led(s, l1)
    ),
    Kept.trans(
      s1,
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Take.asks.kept(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
      Kept.same(
        s2,
        Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
        Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2),
        Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines keeps the logs
def Steps.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Kept.trans(s, s1, Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1), Step.kept(n, s, c), Steps.kept(n, rest, s1))

# an adoption keeps the logs, once the request m is known
def Adopt.ask.kept(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Reading.Request>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Reading.Request{e, q}}:
      Ask.kept(n, s, e, q)

# an adoption keeps the logs, once the head m of the line is known
def Adopt.head.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.kept(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Adopt.at(n, s, c)):
  Adopt.head.kept(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Adopt.at.kept(n, s, c)

# the adoption of each of some lines keeps the logs
def Adopts.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      Kept.trans(
        s,
        Reading.Adopt.at(n, s, c),
        Reading.Node.adopts(n, rest, Reading.Adopt.at(n, s, c)),
        Adopt.at.kept(n, s, c),
        Adopts.kept(n, rest, Reading.Adopt.at(n, s, c))
      )

# more rounds of a sync, kept
def More.kept(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Sync.more(f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Kept.refl(s)
    case 1n+(p):
      Kept.when(
        Reading.Lines.level(cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        s,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Reading.Sync.more(
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Kept.trans(
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Kept.same(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Each.grows(k, bs, pd, s),
            Each.heads(k, bs, pd, s)
          ),
          Steps.kept(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Kept.trans(
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Reading.Sync.more(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          Kept.trans(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
            Kept.same(
              s,
              Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
              Each.grows(k, bs, pd, s),
              Each.heads(k, bs, pd, s)
            ),
            Steps.kept(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          More.kept(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )
        )
      )

# a sync keeps the logs
def Sync.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Reading.Node.sync(n, s, t)):
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  s3 = Reading.Sync.more(
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
    s2
  )
  Kept.trans(
    s,
    s1,
    Reading.Node.adopts(n, cs, s3),
    Take.kept(s, t),
    Kept.trans(
      s1,
      s2,
      Reading.Node.adopts(n, cs, s3),
      Steps.kept(n, cs, s1),
      Kept.trans(
        s2,
        s3,
        Reading.Node.adopts(n, cs, s3),
        More.kept(
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Replicas.Pending.of(bs),
          s2
        ),
        Adopts.kept(n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node only grows it
def Consent.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Consent.at(~Stepping.Ask.kernel(), n, s, i, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+c}:
      Grows.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )(
        Grows.to(
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Grows.refl(s)
        )
      )(
        Step.grows(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          c
        )
      )

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Consent.at(~Stepping.Ask.kernel(), n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Kept.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Kept.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Grows.refl(s)
          ),
          Heads.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.kept(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Spec.Deed
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Spec.Node.does(n, s, ev)) == True{}: Bool}:
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Grows.trans(
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Reading.Adopt.at(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
      )(
        Ask.grows(n, s, e, q)
      )(
        Adopt.at.grows(
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
        )
      )
    case Spec.Deed.Take{t}:
      Take.grows(s, t)
    case Spec.Deed.Sync{t}:
      Sync.grows(n, s, t)
    case Spec.Deed.Keep{b}:
      Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b)))
    case Spec.Deed.Consent{+i}:
      Grows.trans(
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Reading.Adopt.maybe(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )(
        Consent.grows(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )(Adopt.maybe.grows(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)))
    case Spec.Deed.Pass{+c}:
      Grows.trans(
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Reading.Adopt.at(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )(Pass.grows(n, s, c))(Adopt.at.grows(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c))

def Spec.Node.after_grows(n, evs, s):
  match evs:
    case Nil{}:
      Grows.refl(s)
    case Con{+ev, +rest}:
      +s1 = Spec.Node.does(n, s, ev)
      Grows.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1)
      )(Does.grows(n, s, ev))(Spec.Node.after_grows(n, rest, s1))

# what a node does keeps the logs
def Does.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Spec.Deed
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Kept.trans(
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Reading.Adopt.at(
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
        ),
        Ask.kept(n, s, e, q),
        Adopt.at.kept(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
      )
    case Spec.Deed.Take{t}:
      Take.kept(s, t)
    case Spec.Deed.Sync{t}:
      Sync.kept(n, s, t)
    case Spec.Deed.Keep{+b}:
      Kept.same(
        s,
        Basics.Node.keep(s, b),
        Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b))),
        Heads.led(
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Basics.Bytes.rope(b)),
            Replicas.State.ledger(~Basics.Ask.machine(), s)
          )
        )
      )
    case Spec.Deed.Consent{+i}:
      Kept.trans(
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Reading.Adopt.maybe(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Consent.kept(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Adopt.maybe.kept(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )
    case Spec.Deed.Pass{+c}:
      Kept.trans(
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Reading.Adopt.at(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c),
        Pass.kept(n, s, c),
        Adopt.at.kept(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )
    case Spec.Deed.Pass{c}:
      Pass.kept(n, s, c)

def Spec.Node.after_keeps(n, evs, s):
  match evs:
    case Nil{}:
      Kept.refl(s)
    case Con{+ev, rest}:
      s1 = Spec.Node.does(n, s, ev)
      Kept.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1),
        Does.kept(n, s, ev),
        Spec.Node.after_keeps(n, rest, s1)
      )

# Moves
# -----
# A move sets only keys of the version vector, so each resource of its target
# reads the same after it (Spec.Move.reads).

# the key of a resource is not the key of a line in the version vector
def Vector.apart(
  c: Ledgers.Chain,
  n: Resources.Name
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.vector(c), Basics.Key.res(n)) == False{}: Bool
}:
  {==}

# Vector.add keeps a resource, once it is known whether the vector covers the
# place (b)
def Vector.add.reads.if(
  s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  +c: Ledgers.Chain,
  p: Basics.Place,
  +n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: {Replicas.Node.get(~Basics.Ask.machine(), s, h, Basics.Key.res(n)) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Replicas.Work<Basics.Ask>>,
    b,
    u => Some{Replicas.Work{s, h}},
    u => Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.vector(c), Basics.Place.code(p))
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Set.kept(
        s,
        h,
        Basics.Key.vector(c),
        Basics.Place.code(p),
        Basics.Key.res(n),
        v,
        Vector.apart(c, n),
        hget
      )

# a new entry of the version vector keeps a resource
def Vector.add.reads(
  w: Replicas.Work<Basics.Ask>,
  +c: Ledgers.Chain,
  +p: Basics.Place,
  n: Resources.Name,
  v: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Vector.add(w, c, p)):
  match w:
    case Replicas.Work{+s, +h}:
      hget => Vector.add.reads.if(
        s,
        h,
        c,
        p,
        n,
        v,
        Basics.Place.covered(Basics.Node.vector(s, h, c), p),
        hget
      )

# Vector.add.if keeps a resource, once it is known whether the place is of
# the line (b)
def Vector.add.if.reads.at(
  w: Replicas.Work<Basics.Ask>,
  +p: Basics.Place,
  n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Some{w})
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Replicas.Work<Basics.Ask>>,
    b,
    u => Some{w},
    u => Judging.Vector.add(w, Basics.Place.chain(p), p)
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Vector.add.reads(w, Basics.Place.chain(p), p, n, v)(hget)

# an entry of the version vector, if any, keeps a resource
def Vector.add.if.reads(
  w: Replicas.Work<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Place>,
  n: Resources.Name,
  v: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Vector.add.if(w, c, m)):
  match m:
    case None{}:
      hget => hget
    case Some{+p}:
      hget => Vector.add.if.reads.at(
        w,
        p,
        n,
        v,
        Ledgers.Chain.is_eq(Basics.Place.chain(p), c),
        hget
      )

# a work that reads a key, after a step that keeps the read
def Reads.bind(
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  -f: Replicas.Work<Basics.Ask> -> Maybe<&2, Replicas.Work<Basics.Ask>>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  k,
  v,
  m
) -> (
  @w: Replicas.Work<Basics.Ask> -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, Some{w}) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, f(w))
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{w}:
      hm => hf => hf(w)(hm)

# the entries of some bindings keep a resource
def Vector.adds.reads(
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  m
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Vector.adds(bs, c, m)):
  match bs:
    case Nil{}:
      hm => hm
    case Con{+b, r}:
      hm => Vector.adds.reads(
        r,
        c,
        Maybe.bind(
          &2,
          Replicas.Work<Basics.Ask>,
          Replicas.Work<Basics.Ask>,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b))
        ),
        n,
        v
      )(
        Reads.bind(
          Basics.Key.res(n),
          v,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b))
        )(hm)(+w => hw => Vector.add.if.reads(w, c, Judging.Vector.entry(b), n, v)(hw))
      )

# the version vector of a version, joined in, keeps a resource
def Vector.joined.reads(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  m
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Vector.joined(s, c, x, m)):
  hm => Reads.bind(
    Basics.Key.res(n),
    v,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, Basics.Node.root_of(s, Some{x})),
      c,
      m
    ),
    w => Judging.Vector.add.if(w, c, Basics.Node.place(s, x))
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, Basics.Node.root_of(s, Some{x})),
      c,
      m,
      n,
      v
    )(hm)
  )(+w => hw => Vector.add.if.reads(w, c, Basics.Node.place(s, x), n, v)(hw))

def Spec.Move.reads(s, c, to, h, n, v):
  hget => Vector.joined.reads(
    s,
    c,
    to,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Basics.Node.root_of(s, Some{to})}}
    ),
    n,
    v
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Basics.Node.root_of(s, Some{to})}},
      n,
      v
    )(hget)
  )

# Whole merges
# ------------
# A merge sets the key of each resource that it merges. A set of another key
# keeps what a key reads, so what the merge of one resource takes is what the
# whole merge gives for it (Spec.Merge.keeps).

# the words after the first one
def Words.rest(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{w, r}:
      r

# the text that a read gave, "" without one
def Read.text(m: Maybe<&2, Codes.Read<String>>) -> String:
  match m:
    case Some{Codes.Read{t, r}}:
      t
    case None{}:
      ""

# texts with the same code are the same
def Text.same(
  t1: String,
  t2: String,
  e: {Codes.Code.text(t1, []) == Codes.Code.text(t2, []): List<&2, U32>}
) -> {t1 == t2: String}:
  Equal.trans(
    String,
    t1,
    Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
    t2,
    Equal.sym(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      t1,
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t1, [])),
        Some{Codes.Read{t1, []}},
        Codes.Code.text_read(t1, [])
      )
    ),
    Equal.trans(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      Read.text(Codes.Code.text.read(Codes.Code.text(t2, []))),
      t2,
      Equal.cong(
        List<&2, U32>,
        String,
        ws => Read.text(Codes.Code.text.read(ws)),
        Codes.Code.text(t1, []),
        Codes.Code.text(t2, []),
        e
      ),
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t2, [])),
        Some{Codes.Read{t2, []}},
        Codes.Code.text_read(t2, [])
      )
    )
  )

# Res.apart once it is known whether the keys are the same (b)
def Res.apart.at(
  +t1: String,
  +t2: String,
  +b: Bool,
  eb: {
    Shared.List.is_eq(
      ~U32,
      ~U32.is_eq,
      Basics.Key.res(Resources.Name{t1}),
      Basics.Key.res(Resources.Name{t2})
    )
      == b: Bool
  },
  hf: {String.eq(t1, t2) == False{}: Bool}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            String.eq(t1, t2),
            True{},
            Equal.sym(Bool, String.eq(t1, t2), False{}, hf),
            Equal.trans(
              Bool,
              String.eq(t1, t2),
              String.eq(t2, t2),
              True{},
              Equal.cong(
                String,
                Bool,
                z => String.eq(z, t2),
                t1,
                t2,
                Text.same(
                  t1,
                  t2,
                  Equal.cong(
                    List<&2, U32>,
                    List<&2, U32>,
                    Words.rest,
                    Basics.Key.res(Resources.Name{t1}),
                    Basics.Key.res(Resources.Name{t2}),
                    Shared.List.is_eq_sound(
                      ~U32,
                      ~U32.is_eq,
                      ~Shared.U32.laws(),
                      Basics.Key.res(Resources.Name{t1}),
                      Basics.Key.res(Resources.Name{t2})
                    )(eb)
                  )
                )
              ),
              Texts.String.eq_refl(t2)
            )
          )
        )
      )

# resources that are not the same have keys that are not the same
def Res.apart(
  +m: Resources.Name,
  +n: Resources.Name
) -> {
  Resources.Name.is_eq(m, n) == False{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      hf => Res.apart.at(
        t1,
        t2,
        Shared.List.is_eq(
          ~U32,
          ~U32.is_eq,
          Basics.Key.res(Resources.Name{t1}),
          Basics.Key.res(Resources.Name{t2})
        ),
        {==},
        hf
      )

# resources that are the same are equal
def Name.sound(
  +m: Resources.Name,
  +n: Resources.Name
) -> {Resources.Name.is_eq(m, n) == True{}: Bool} -> {m == n: Resources.Name}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      e => Equal.cong(
        String,
        Resources.Name,
        z => Resources.Name{z},
        t1,
        t2,
        Texts.String.eq_sound(t1, t2)(e)
      )

# the key of a clash is not the key of a resource
def Clash.apart(
  m: Resources.Name,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.clash(m), Basics.Key.res(n)) == False{}: Bool}:
  {==}

# a work that reads a key, after a read that gives the next step
def Reads.with(
  -A: Data,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  +ma: Maybe<&2, A>,
  -f: A -> Maybe<&2, Replicas.Work<Basics.Ask>>
) -> (
  @a: A -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, f(a))
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, Maybe.bind(&2, A, Replicas.Work<Basics.Ask>, ma, f)):
  match ma:
    case None{}:
      hf => Unit{}
    case Some{a}:
      hf => hf(a)

# a set of another key keeps what a work reads
def Set.kept.work(
  +w: Replicas.Work<Basics.Ask>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k2, v, Some{w}) -> Replicas.Work.Reads(~Basics.Ask.machine(), k2, v, Replicas.Work.set(~Basics.Ask.machine(), w, k, x)):
  match w:
    case Replicas.Work{s, h}:
      hget => Set.kept(s, h, k, x, k2, v, hne, hget)

# Keep.reads once it is known whether the node holds the new data (b)
def Keep.reads.if(
  +s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +b: Bool,
  hget: {Replicas.Node.get(~Basics.Ask.machine(), s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  k,
  v,
  Replicas.Work.on(~Basics.Ask.machine(), Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{Replicas.State.keep(~Basics.Ask.machine(), s, ns)}), h)
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Get.grows(s, Replicas.State.keep(~Basics.Ask.machine(), s, ns), h, k, v, Grows.keep(s, ns))(hget)

# new data keeps what a work reads
def Keep.reads(
  +w: Replicas.Work<Basics.Ask>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, Some{w}) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, v, Replicas.Work.keep(~Basics.Ask.machine(), w, ns)):
  match w:
    case Replicas.Work{s, h}:
      hget => Keep.reads.if(s, h, ns, k, v, Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ns), ns), hget)

# Set.read once it is known whether the node holds the new nodes (b)
def Set.read.if(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  +b: Bool,
  eb: {
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), ws) == b: Bool
  },
  em: {Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  k,
  x,
  Replicas.Work.on(~Basics.Ask.machine(), Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{Replicas.State.keep(~Basics.Ask.machine(), s, ws)}), Some{hh})
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Replicas.Node.get(~Basics.Ask.machine(), Replicas.State.keep(~Basics.Ask.machine(), s, ws), Some{hh}, k),
        Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), Some{hh}, k),
        Some{x},
        Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), Some{hh}, k),
        Trees.Tree.get_set(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          s,
          Replicas.State.keep(~Basics.Ask.machine(), s, ws),
          h,
          k,
          x,
          Trees.Put{hh, ws}
        )(
          Equal.trans(
            Maybe<&2, Trees.Put>,
            Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
            Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
            Some{Trees.Put{hh, ws}},
            Equal.sym(
              Maybe<&2, Trees.Put>,
              Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
              Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
              Trees.Tree.set_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x)
            ),
            em
          )
        )(eb)
      )

# Set.read once the new subtree m is known
def Set.read.of(
  +s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  +m: Maybe<&2, Trees.Put>,
  em: {Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == m: Maybe<&2, Trees.Put>}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, x, Replicas.Work.of(~Basics.Ask.machine(), s, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, ws}}:
      Set.read.if(
        s,
        h,
        k,
        x,
        hh,
        ws,
        Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s, ws), ws),
        {==},
        em
      )

# a key that a work sets, it reads
def Set.read(
  +w: Replicas.Work<Basics.Ask>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Replicas.Work.Reads(~Basics.Ask.machine(), k, x, Replicas.Work.set(~Basics.Ask.machine(), w, k, x)):
  match w:
    case Replicas.Work{s, h}:
      Set.read.of(s, h, k, x, Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x), {==})

# the merge of one resource m, of the trees hb (base), ho (ours) and ht
# (theirs), on the work w: one step of Spec.Merge.all
def Merge.step(
  +s: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  w: Replicas.Work<Basics.Ask>
) -> Maybe<&2, Replicas.Work<Basics.Ask>>:
  Maybe.bind(
    &2,
    Maybe<&2, Ropes.Root>,
    Replicas.Work<Basics.Ask>,
    Basics.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Basics.Ask>,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Basics.Ask>,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )

# what the merge of another resource puts keeps what a work reads for n
def Merge.put.other(
  f: Ledgers.Id,
  +m: Resources.Name,
  +n: Resources.Name,
  +o2: Maybe<&2, Ropes.Root>,
  +p: Judging.Pick,
  +w: Replicas.Work<Basics.Ask>,
  +v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Judging.Merge.put(f, m, o2, p, w)):
  match p:
    case Judging.Pick.Take{mm}:
      Set.kept.work(w, Basics.Key.res(m), Basics.Res.code(mm), Basics.Key.res(n), v, hne)
    case Judging.Pick.Make{y}:
      hget => Reads.bind(
        Basics.Key.res(n),
        v,
        Replicas.Work.keep(~Basics.Ask.machine(), w, Ropes.Put.nodes(Basics.Bytes.rope(y))),
        w2 => Replicas.Work.set(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(y))})
        )
      )(
        Keep.reads(w, Ropes.Put.nodes(Basics.Bytes.rope(y)), Basics.Key.res(n), v)(hget)
      )(
        w2 => hw => Set.kept.work(
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(y))}),
          Basics.Key.res(n),
          v,
          hne
        )(hw)
      )
    case Judging.Pick.Clash{}:
      hget => Reads.bind(
        Basics.Key.res(n),
        v,
        Replicas.Work.set(~Basics.Ask.machine(), w, Basics.Key.res(m), Basics.Res.code(o2)),
        y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(m), Judging.Clash.code(f))
      )(
        Set.kept.work(w, Basics.Key.res(m), Basics.Res.code(o2), Basics.Key.res(n), v, hne)(hget)
      )(
        y => hy => Set.kept.work(
          y,
          Basics.Key.clash(m),
          Judging.Clash.code(f),
          Basics.Key.res(n),
          v,
          Clash.apart(m, n)
        )(hy)
      )

# the merge of another resource keeps what a work reads for n
def Merge.step.other(
  +s: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  n: Resources.Name,
  w: Replicas.Work<Basics.Ask>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), v, Merge.step(s, f, hb, ho, ht, m, w)):
  hget => Reads.with(
    Maybe<&2, Ropes.Root>,
    Basics.Key.res(n),
    v,
    Basics.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Basics.Ask>,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Basics.Ask>,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )(
    b => Reads.with(
      Maybe<&2, Ropes.Root>,
      Basics.Key.res(n),
      v,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Basics.Ask>,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )(
      +o => Reads.with(
        Maybe<&2, Ropes.Root>,
        Basics.Key.res(n),
        v,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )(
        x => Reads.with(
          Judging.Pick,
          Basics.Key.res(n),
          v,
          Judging.Pick.merge(Formats.Format.of(Resources.Name.path(m)), s, b, o, x),
          p => Judging.Merge.put(f, m, o, p, w)
        )(p => Merge.put.other(f, m, n, o, p, w, v, hne)(hget))
      )
    )
  )

# the merge of the resource n gives what its pick takes
def Merge.step.same(
  s: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  w: Replicas.Work<Basics.Ask>,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(x), Merge.step(s, f, hb, ho, ht, n, w)):
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, hb, n),
    Some{b},
    eb
  ): Replicas.Work.Reads(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Basics.Ask>,
      _,
      b1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Basics.Ask>,
        Basics.Res.find(s, ho, n),
        o1 => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Work<Basics.Ask>,
          Basics.Res.find(s, ht, n),
          x1 => Judging.Merge.one(s, f, n, b1, o1, x1, w)
        )
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, ho, n),
    Some{o},
    eo
  ): Replicas.Work.Reads(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Basics.Ask>,
      _,
      o1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Basics.Ask>,
        Basics.Res.find(s, ht, n),
        x1 => Judging.Merge.one(s, f, n, b, o1, x1, w)
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, ht, n),
    Some{t},
    et
  ): Replicas.Work.Reads(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Basics.Ask>,
      _,
      x1 => Judging.Merge.one(s, f, n, b, o, x1, w)
    )
  )
  %Equal.sym(
    Maybe<&2, Judging.Pick>,
    Judging.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    Some{Judging.Pick.Take{x}},
    ep
  ): Replicas.Work.Reads(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(&2, Judging.Pick, Replicas.Work<Basics.Ask>, _, p => Judging.Merge.put(f, n, o, p, w))
  )
  Set.read(w, Basics.Key.res(n), Basics.Res.code(x))

# Merge.step.same on the work m, if any
def Merge.step.takes(
  s: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, n, w))
):
  match m:
    case None{}:
      Unit{}
    case Some{w}:
      Merge.step.same(s, f, hb, ho, ht, n, b, o, t, x, w, eb, eo, et, ep)

# one step of a merge keeps what the work reads for n, once it is known
# whether the step is of n (same)
def Merge.step.keeps(
  s: Replicas.Node<Basics.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m1: Resources.Name,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool}
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  m
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
):
  match same:
    case True{}:
      hm =>
        %Equal.sym(
          Resources.Name,
          m1,
          n,
          Name.sound(m1, n)(es)
        ): Replicas.Work.Reads(~Basics.Ask.machine(), 
          Basics.Key.res(n),
          Basics.Res.code(x),
          Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, _, w))
        )
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep)
    case False{}:
      hm => Reads.bind(
        Basics.Key.res(n),
        Basics.Res.code(x),
        m,
        w => Merge.step(s, f, hb, ho, ht, m1, w)
      )(
        hm
      )(
        w => hw => Merge.step.other(
          s,
          f,
          hb,
          ho,
          ht,
          m1,
          n,
          w,
          Basics.Res.code(x),
          Res.apart(m1, n)(es)
        )(hw)
      )

# the merge of more resources keeps what the work reads for n
def Merge.all.keeps(
  +s: Replicas.Node<Basics.Ask>,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  m
) -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(s, f, ns, hb, ho, ht, m)
):
  match ns:
    case Nil{}:
      hm => hm
    case Con{m1, r}:
      hm => Merge.all.keeps(
        s,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep
      )(
        Merge.step.keeps(
          s,
          f,
          hb,
          ho,
          ht,
          m1,
          m,
          n,
          b,
          o,
          t,
          x,
          eb,
          eo,
          et,
          ep,
          Resources.Name.is_eq(m1, n),
          {==}
        )(hm)
      )

# Merge.all.takes at the first resource m1, once it is known whether it is n
def Merge.all.takes.at(
  +s: Replicas.Node<Basics.Ask>,
  +f: Ledgers.Id,
  +m1: Resources.Name,
  r: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool},
  ih: {
    List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n) == True{}: Bool
  } -> Replicas.Work.Reads(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(x),
    Judging.Merge.all(
      s,
      f,
      r,
      hb,
      ho,
      ht,
      Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
    )
  )
) -> {
  List.any.if(
    u => List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n),
    same
  )
    == True{}: Bool
} -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(
    s,
    f,
    r,
    hb,
    ho,
    ht,
    Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
  )
):
  match same:
    case True{}:
      e => Merge.all.keeps(
        s,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep
      )(
        %Equal.sym(Resources.Name, m1, n, Name.sound(m1, n)(es)): Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(x), Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, _, w)))
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep))
    case False{}:
      e => ih(e)

# a merge of the resources ns, with n among them, gives what the pick of n
# takes
def Merge.all.takes(
  +s: Replicas.Node<Basics.Ask>,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n) == True{}: Bool
} -> Replicas.Work.Reads(~Basics.Ask.machine(), 
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(s, f, ns, hb, ho, ht, m)
):
  match ns:
    case Nil{}:
      e => Empty.absurd(
        Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(x), m),
        Shared.Bool.false_ne_true(e)
      )
    case Con{m1, r}:
      Merge.all.takes.at(
        s,
        f,
        m1,
        r,
        hb,
        ho,
        ht,
        m,
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep,
        Resources.Name.is_eq(m1, n),
        {==},
        Merge.all.takes(
          s,
          f,
          r,
          hb,
          ho,
          ht,
          Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
          n,
          b,
          o,
          t,
          x,
          eb,
          eo,
          et,
          ep
        )
      )

def Spec.Merge.keeps(s, c, from, h, n, b, o, t, x):
  ec => eb => eo => et => ep => Vector.joined.reads(
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
    ),
    n,
    Basics.Res.code(x)
  )(
    Merge.all.takes(
      s,
      from,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
      h,
      Basics.Node.root_of(s, Some{from}),
      Some{Replicas.Work{s, h}},
      n,
      b,
      o,
      t,
      x,
      eb,
      eo,
      et,
      ep
    )(ec)
  )

def Spec.Resolve.reads(s, h, n, m):
  Reads.bind(
    Basics.Key.res(n),
    Basics.Res.code(m),
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), [])
  )(
    Set.read(Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
  )(
    y => hy => Set.kept.work(
      y,
      Basics.Key.clash(n),
      [],
      Basics.Key.res(n),
      Basics.Res.code(m),
      Clash.apart(n, n)
    )(hy)
  )

def Spec.Resolve.shuts(s, h, n, m):
  Reads.with(
    Replicas.Work<Basics.Ask>,
    Basics.Key.clash(n),
    [],
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), [])
  )(y => Set.read(y, Basics.Key.clash(n), []))

# the code of a count is not empty
def Count.full(
  n: Nat,
  r: List<&2, U32>
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, [], Codes.Code.count(n, r)) == False{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Spec.Clash.shut(s, h, n, f):
  match f:
    case Ledgers.Id{w, q}:
      e =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), s, h, Basics.Key.clash(n)),
          Some{[]},
          e
        ): {
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            _,
            Some{Judging.Clash.code(Ledgers.Id{w, q})}
          )
            == False{}: Bool
        }
        Count.full(
          Codes.Code.length(w),
          Codes.Code.chars(w, Codes.Code.count(Codes.Code.length(q), Codes.Code.chars(q, [])))
        )

# Outcomes
# --------
# A step gives each of its requests an outcome (Spec.Step.run_outs), and only
# the requests of a step leave the requests that wait (Spec.Wait.left_keeps).

# Add.reads once the value m of the key in the log is known
def Add.reads.at(
  r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Run.Keeps(k, x, Replicas.Run.add.at(~Basics.Ask.machine(), r, k, x, m)):
  match r m:
    case Replicas.Run{+s, +t} None{}:
      Run.logged.keeps(
        k,
        x,
        t,
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, Replicas.Tip.log(t)}, k, x)
      )(Set.read(Replicas.Work{s, Replicas.Tip.log(t)}, k, x))
    case y Some{old}:
      Unit{}

# a new key of the log of a run reads back
def Add.reads(
  +r: Replicas.Run<Basics.Ask>,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Run.Keeps(k, x, Replicas.Run.add(~Basics.Ask.machine(), r, k, x)):
  Add.reads.at(
    r,
    k,
    x,
    Replicas.Node.get(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)), k)
  )

# a log that reads the outcome key of i as v holds an outcome of i
def Outs.of(
  i: Ledgers.Id,
  v: List<&2, U32>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> Run.Keeps(Replicas.Log.out(i), v, m) -> Replicas.Run.Outs(~Basics.Ask.machine(), m, i):
  match m:
    case None{}:
      h => Unit{}
    case Some{Replicas.Run{s, t}}:
      h =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), Replicas.Log.out(i)),
          Some{v},
          h
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# each run that f gives has an outcome of i: so has the run after a step
def Outs.all(
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -f: Replicas.Run<Basics.Ask> -> Maybe<&2, Replicas.Run<Basics.Ask>>,
  -i: Ledgers.Id,
  hf: @r: Replicas.Run<Basics.Ask> -> Replicas.Run.Outs(~Basics.Ask.machine(), f(r), i)
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, f), i):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      hf(r)

# one of two runs, each with an outcome of i
def Outs.when(
  +b: Bool,
  -mx: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -my: Maybe<&2, Replicas.Run<Basics.Ask>>,
  -i: Ledgers.Id,
  hx: Replicas.Run.Outs(~Basics.Ask.machine(), mx, i),
  hy: Replicas.Run.Outs(~Basics.Ask.machine(), my, i)
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Shared.Bool.when(Maybe<&2, Replicas.Run<Basics.Ask>>, b, u => mx, u => my), i):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that is refused as stale has an outcome
def Stale.outs(+r: Replicas.Run<Basics.Ask>, +i: Ledgers.Id) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.stale(~Basics.Ask.machine(), r, i), i):
  Outs.of(
    i,
    Replicas.Out.words(Replicas.Out.Stale{}),
    Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}))
  )(Add.reads(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{})))

# a request that is taken has an outcome
def Taken.outs(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.taken(~Basics.Ask.machine(), r, i, own), i):
  +n = Replicas.Tip.count(Replicas.Run.tip(~Basics.Ask.machine(), r))
  Outs.of(
    i,
    Replicas.Out.words(Replicas.Out.Taken{n}),
    Replicas.Step.taken(~Basics.Ask.machine(), r, i, own)
  )(
    Keeps.bind(
      Replicas.Log.out(i),
      Replicas.Out.words(Replicas.Out.Taken{n}),
      Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n})),
      +r1 => Maybe.bind(
        &2,
        Replicas.Run<Basics.Ask>,
        Replicas.Run<Basics.Ask>,
        Replicas.Run.add(~Basics.Ask.machine(), 
          r1,
          Replicas.Log.version(n),
          Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
        ),
        r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)}
      )
    )(
      Add.reads(r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Taken{n}))
    )(
      +r1 => h1 => Keeps.bind(
        Replicas.Log.out(i),
        Replicas.Out.words(Replicas.Out.Taken{n}),
        Replicas.Run.add(~Basics.Ask.machine(), 
          r1,
          Replicas.Log.version(n),
          Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))})
        ),
        r2 => Some{Replicas.Run.next(~Basics.Ask.machine(), r2, own)}
      )(
        Add.kept(
          r1,
          Replicas.Log.version(n),
          Replicas.Version.words(Replicas.Version{i, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r1))}),
          Replicas.Log.out(i),
          Replicas.Out.words(Replicas.Out.Taken{n})
        )(h1)
      )(
        r2 => h2 => Next.kept(
          r2,
          own,
          Replicas.Log.out(i),
          Replicas.Out.words(Replicas.Out.Taken{n})
        )(h2)
      )
    )
  )

# a judged request has an outcome
def Judged.outs(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Replicas.Verdict<Basics.Ask>>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.judged(~Basics.Ask.machine(), r, i, own, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Replicas.Verdict.Stale{}}:
      Stale.outs(r, i)
    case Some{Replicas.Verdict.Taken{Replicas.Work{s2, h}}}:
      Taken.outs(Replicas.Run.over(~Basics.Ask.machine(), r, s2, h), i, own)

# a mark on a version has an outcome
def Marked.outs(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  m: String,
  +v: Maybe<&2, Replicas.Version>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, v), i):
  match v:
    case None{}:
      Unit{}
    case Some{x}:
      Outs.all(
        Replicas.Run.add(~Basics.Ask.machine(), r, Replicas.Log.mark(m), Ledgers.Id.code(Replicas.Version.id(x), [])),
        r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{}),
        i,
        r2 => Taken.outs(r2, i, None{})
      )

# a request for a mark has an outcome
def Mark.outs(
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  +m: String
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.mark(~Basics.Ask.machine(), r, i, m), i):
  +s = Replicas.Run.state(~Basics.Ask.machine(), r)
  +t = Replicas.Run.tip(~Basics.Ask.machine(), r)
  +n = Replicas.Tip.count(t)
  Outs.when(
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Replicas.Line.mark(~Basics.Ask.machine(), s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Replicas.Step.marked(~Basics.Ask.machine(), r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Replicas.Step.stale(~Basics.Ask.machine(), r, i),
    i,
    Marked.outs(r, i, m, Replicas.Line.version(~Basics.Ask.machine(), s, t, U32.sub(n, 1))),
    Stale.outs(r, i)
  )

# the first tip of a new branch has an outcome
def Branch.made.outs(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  b: String,
  +m: Maybe<&2, Replicas.Made<Basics.Ask>>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Branch.made(~Basics.Ask.machine(), r, i, b, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Replicas.Made{t, s2}}:
      Outs.all(
        Replicas.Run.add(~Basics.Ask.machine(), 
          Replicas.Run.over(~Basics.Ask.machine(), r, s2, Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r))),
          Replicas.Log.start(b),
          Hashes.Hash.code(Replicas.Tip.hash(t), [])
        ),
        r2 => Replicas.Step.taken(~Basics.Ask.machine(), r2, i, None{}),
        i,
        r2 => Taken.outs(r2, i, None{})
      )

# a request for a branch has an outcome, once it is known whether its version
# is one
def Branch.ready.outs(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  +m: Maybe<&2, Bool>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Stepping.Branch.ready(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{False{}}:
      Stale.outs(r, i)
    case Some{True{}}:
      Outs.when(
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Basics.Node.root_of(Replicas.Run.state(~Basics.Ask.machine(), r), at)
        ),
        Replicas.Branch.made(~Basics.Ask.machine(), 
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        ),
        None{},
        i,
        Branch.made.outs(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Line.chain(st, Some{b}), at),
            Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
          )
        ),
        Unit{}
      )

# a request for a branch has an outcome
def Branch.new.outs(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Stepping.Branch.new(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Stale.outs(r, i)
    case Some{None{}}:
      Branch.ready.outs(r, i, st, b, at, Judging.Judge.ready_maybe(Replicas.Run.state(~Basics.Ask.machine(), r), at))

# On.outs once it is known how the line takes the change (w)
def On.of.outs(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Stepping.Step.on.of(r, i, st, l, ch, w), i):
  match w:
    case Stepping.Route.Mark{a}:
      Mark.outs(r, i, a)
    case Stepping.Route.Branch{+a, b}:
      Branch.new.outs(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(~Basics.Ask.machine(), 
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Log.start(a)
        )
      )
    case Stepping.Route.Judge{}:
      Judged.outs(
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(
          Replicas.Run.state(~Basics.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Basics.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Basics.Ask.machine(), r))
        )
      )

# a change of a line has an outcome
def On.outs(
  r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Stepping.Step.on(r, i, st, l, ch), i):
  On.of.outs(r, i, st, l, ch, Stepping.Route.of(l, ch))

# a request of a run has an outcome
def Change.outs(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Basics.Ask
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Stepping.Step.change(r, c, i, q), i):
  match q:
    case Basics.Ask.Start{os}:
      Stale.outs(r, i)
    case Basics.Ask.On{st, l, ch}:
      Outs.when(
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        i,
        On.outs(r, i, st, l, ch),
        Stale.outs(r, i)
      )

# a request that the node holds or not, of a run, has an outcome
def Asked.outs(
  r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.asked(~Stepping.Ask.kernel(), r, c, i, a), i):
  match a:
    case None{}:
      Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.outs(r, c, i, q)

# a run whose log reads the outcome key of i has an outcome of i
def Outs.self(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  ws: List<&2, U32>
) -> {
  Replicas.Node.get(~Basics.Ask.machine(), 
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
    Replicas.Log.out(i)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
} -> Replicas.Run.Outs(~Basics.Ask.machine(), Some{r}, i):
  match r:
    case Replicas.Run{s, t}:
      eg =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), Replicas.Log.out(i)),
          Some{ws},
          eg
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# One.outs once the outcome o that the words ws read as is known
def One.outs.read(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  ws: List<&2, U32>,
  +o: Maybe<&2, Replicas.Out>,
  eg: {
    Replicas.Node.get(~Basics.Ask.machine(), 
      Replicas.Run.state(~Basics.Ask.machine(), r),
      Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
      Replicas.Log.out(i)
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.fresh(~Stepping.Ask.kernel(), r, c, i, o), i):
  match o:
    case Some{x}:
      Outs.self(r, i, ws)(eg)
    case None{}:
      Asked.outs(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), i))

# One.outs once what the log holds for the request is known (g)
def One.outs.at(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Replicas.Node.get(~Basics.Ask.machine(), 
      Replicas.Run.state(~Basics.Ask.machine(), r),
      Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
      Replicas.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> Replicas.Run.Outs(~Basics.Ask.machine(), 
  Replicas.Step.fresh(~Stepping.Ask.kernel(), 
    r,
    c,
    i,
    Maybe.bind(&2, List<&2, U32>, Replicas.Out, g, ws => Replicas.Out.read(ws))
  ),
  i
):
  match g:
    case None{}:
      Asked.outs(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), i))
    case Some{+ws}:
      One.outs.read(r, c, i, ws, Replicas.Out.read(ws), eg)

# a request has an outcome after its step
def One.outs(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i), i):
  One.outs.at(
    r,
    c,
    i,
    Replicas.Node.get(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)), Replicas.Log.out(i)),
    {==}
  )

# no run gives no run
def All.none(
  c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>
) -> {Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, None{}) == None{}: Maybe<&2, Replicas.Run<Basics.Ask>>}:
  match qs:
    case Nil{}:
      {==}
    case Con{i, rest}:
      All.none(c, rest)

# a run reads what its log holds
def Keeps.self(
  +r: Replicas.Run<Basics.Ask>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Replicas.Node.get(~Basics.Ask.machine(), 
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k, v, Some{r}):
  match r:
    case Replicas.Run{s, t}:
      e => e

# Outs.kept once what the log of the run holds for the request is known (g)
def Outs.kept.at(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +r: Replicas.Run<Basics.Ask>,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Replicas.Node.get(~Basics.Ask.machine(), 
      Replicas.Run.state(~Basics.Ask.machine(), r),
      Replicas.Tip.log(Replicas.Run.tip(~Basics.Ask.machine(), r)),
      Replicas.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> {
  Maybe.is_some(&2, List<&2, U32>, g) == True{}: Bool
} -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, Some{r}), i):
  match g:
    case None{}:
      h => Empty.absurd(
        Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, Some{r}), i),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+v}:
      h => Outs.of(
        i,
        v,
        Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, Some{r})
      )(
        All.kept(
          c,
          qs,
          Some{r},
          Replicas.Log.out(i),
          v
        )(Keeps.self(r, Replicas.Log.out(i), v)(eg))
      )

# an outcome that a run has, it has after more requests
def Outs.kept(
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  +i: Ledgers.Id
) -> Replicas.Run.Outs(~Basics.Ask.machine(), m, i) -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m), i):
  match m:
    case None{}:
      h =>
        %Equal.sym(
          Maybe<&2, Replicas.Run<Basics.Ask>>,
          Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, None{}),
          None{},
          All.none(c, qs)
        ): Replicas.Run.Outs(~Basics.Ask.machine(), _, i)
        Unit{}
    case Some{Replicas.Run{s, t}}:
      h => Outs.kept.at(
        c,
        qs,
        Replicas.Run{s, t},
        i,
        Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), Replicas.Log.out(i)),
        {==}
      )(h)

# All.outs at the first request j, once it is known whether it is i
def All.outs.at(
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  +i: Ledgers.Id,
  +same: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i) == True{}: Bool
  } -> Replicas.Run.Outs(~Basics.Ask.machine(), 
    Replicas.Step.all(~Stepping.Ask.kernel(), 
      c,
      rest,
      Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, j))
    ),
    i
  )
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i), same) == True{}: Bool
} -> Replicas.Run.Outs(~Basics.Ask.machine(), 
  Replicas.Step.all(~Stepping.Ask.kernel(), 
    c,
    rest,
    Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, j))
  ),
  i
):
  match same:
    case True{}:
      e => Outs.kept(
        c,
        rest,
        Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, j)),
        i
      )(
        %Equal.sym(Ledgers.Id, j, i, Ledgers.Id.is_eq_sound(j, i)(es)): Replicas.Run.Outs(~Basics.Ask.machine(), Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, _)), i)
        Outs.all(m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i), i, r => One.outs(r, c, i)))
    case False{}:
      e => ih(e)

# each request of a step has an outcome after it
def All.outs(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool
} -> Replicas.Run.Outs(~Basics.Ask.machine(), Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m), i):
  match qs:
    case Nil{}:
      e => Empty.absurd(Replicas.Run.Outs(~Basics.Ask.machine(), m, i), Shared.Bool.false_ne_true(e))
    case Con{j, rest}:
      All.outs.at(
        c,
        j,
        rest,
        m,
        i,
        Ledgers.Id.is_eq(j, i),
        {==},
        All.outs(
          c,
          rest,
          Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, j)),
          i
        )
      )

def Spec.Step.run_outs(s, c, t, qs, i):
  All.outs(c, qs, Some{Replicas.Run{s, t}}, i)

# Wait.left_keeps at the first request j, once it is known whether it is i
# (same) and whether a step ran it (d)
def Left.keeps.at(
  j: Ledgers.Id,
  ks: List<&2, Ledgers.Id>,
  rs: List<&2, Ledgers.Id>,
  done: Tries.Trie<Unit>,
  i: Ledgers.Id,
  +same: Bool,
  +d: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ed: {Tries.Trie.has(Unit, done, Ledgers.Id.key(j)) == d: Bool},
  hd: {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i) == True{}: Bool
  } -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool}
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i), same) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    List.filter.put(Ledgers.Id, j, ks, Bool.not(d)),
    i
  )
    == True{}: Bool
}:
  match same d:
    case True{} False{}:
      e =>
        %Equal.sym(
          Bool,
          Ledgers.Id.is_eq(j, i),
          True{},
          es
        ): {
          List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i), _) == True{}: Bool
        }
        {==}
    case True{} True{}:
      e => Empty.absurd(
        {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Tries.Trie.has(Unit, done, Ledgers.Id.key(i)),
            True{},
            Equal.sym(Bool, Tries.Trie.has(Unit, done, Ledgers.Id.key(i)), False{}, hd),
            (
              %Ledgers.Id.is_eq_sound(j, i)(es): {Tries.Trie.has(Unit, done, Ledgers.Id.key(_)) == True{}: Bool}
              ed)
          )
        )
      )
    case False{} False{}:
      e => Shared.List.contains_cons(~Ledgers.Id, ~Ledgers.Id.is_eq, j, ks, i)(ih(e))
    case False{} True{}:
      e => ih(e)

def Spec.Wait.left_keeps(ws, done, i):
  match ws:
    case Nil{}:
      e => hd => e
    case Con{j, rs}:
      e => +hd => Left.keeps.at(
        j,
        Replicas.Wait.left(rs, done),
        rs,
        done,
        i,
        Ledgers.Id.is_eq(j, i),
        Tries.Trie.has(Unit, done, Ledgers.Id.key(j)),
        {==},
        {==},
        hd,
        e2 => Spec.Wait.left_keeps(rs, done, i)(e2)(hd)
      )(e)

# Plan.follow_allowed once it is known whether the rules allow the vote (b)
def Follow.allowed.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  v: Ledgers.Vote,
  from: List<&2, String>,
  b: Bool
) -> {
  Maybe.is_some(
    &2,
    Replicas.Run<Basics.Ask>,
    Replicas.Plan.run(~Basics.Ask.machine(), 
      Shared.Bool.when(
        Replicas.Plan<Basics.Ask>,
        b,
        u => Replicas.Plan.copy(~Stepping.Ask.kernel(), s, c, t, th, Some{v}, from),
        u => Replicas.Plan{[], None{}, []}
      )
    )
  )
    == True{}: Bool
} -> {b == True{}: Bool}:
  match b:
    case True{}:
      e => {==}
    case False{}:
      e => e

def Spec.Plan.follow_allowed(s, c, w, t, th, os, v, from):
  Follow.allowed.at(s, c, t, th, v, from, Replicas.Vote.allowed(~Basics.Ask.machine(), s, w, os, v, from))

# Agreement
# ---------

# a step that the owners decided at a place in a, they decided in a node that
# grew, with the owners that it reads
def Decide.up(
  +a: Replicas.Node<Basics.Ask>,
  +u: Replicas.Node<Basics.Ask>,
  +t: Replicas.Tip,
  +w: Ledgers.Where,
  v: Ledgers.Vote,
  +g: {Replicas.Node.grows(~Basics.Ask.machine(), a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), a),
    w,
    Replicas.Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), u),
    w,
    Replicas.Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  e =>
    Ledgers.State.decide_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Replicas.State.ledger(~Basics.Ask.machine(), u),
      w,
      Replicas.Tip.owners(t),
      v
    )(g)(e)

# Scan.elim at a round, once what it decides is known (m)
def Scan.elim.at(
  -R: Type,
  -s: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -n: U32,
  -os: List<&2, String>,
  -p: Nat,
  -v: Ledgers.Vote,
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {
    Replicas.Height.decide(~Basics.Ask.machine(), s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> (
    @q: Nat -> {
      Ledgers.State.decide(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), s),
        Ledgers.Where{c, n, q},
        os
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
    } -> R
  ) -> R
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), s),
    Ledgers.Where{c, n, r},
    os
  )
    == m: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Vote.first(
    m,
    u => Replicas.Height.decide(~Basics.Ask.machine(), s, c, n, os, p)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => rec(e)(f)
    case Some{x}:
      em => e => f => f(
        r
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Vote>,
          Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, n, r}, os),
          Some{x},
          Some{v},
          em,
          e
        )
      )

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  -R: Type,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Replicas.Height.decide(~Basics.Ask.machine(), s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match k:
    case 0n:
      e => f => f(0n)(e)
    case 1n+(+p):
      Scan.elim.at(
        R,
        s,
        c,
        n,
        os,
        p,
        v,
        1n+p,
        Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, n, 1n+p}, os),
        Scan.elim(R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Replicas.Head) -> {Replicas.Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Replicas.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +h: Replicas.Head,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Ledgers.Vote,
    Replicas.Head.tip(~Basics.Ask.machine(), s, h),
    t => Replicas.Height.decide(~Basics.Ask.machine(), s, c, Replicas.Head.next(h), Replicas.Tip.owners(t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(+s: Replicas.Node<Basics.Ask>, +c: Ledgers.Chain, +h: Replicas.Head) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(s, c, h, Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h)))

# the head h after the step m: one height up, at the tip that the step names
# (no step, or one that names no tip: h)
def Head.step(h: Replicas.Head, m: Maybe<&2, Ledgers.Vote>) -> Replicas.Head:
  match h m:
    case Replicas.Head{r, b, n, th} Some{Ledgers.Vote{before, qs, Some{x}}}:
      Replicas.Head{r, b, U32.inc(n), Some{x}}
    case x y:
      x

# that the head of the line c in the node s2, when it is not at the height of
# h, is x
def Moves(s2: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h: Replicas.Head, x: Replicas.Head) -> Type:
  {
    Replicas.Heads.level(Some{h}, Replicas.Node.head_of(~Basics.Ask.machine(), s2, c)) == False{}: Bool
  } -> {Replicas.Node.head_of(~Basics.Ask.machine(), s2, c) == Some{x}: Maybe<&2, Replicas.Head>}

# a node whose head is h did not move it
def Moves.stay(
  -s: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  h: Replicas.Head,
  -x: Replicas.Head,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>}
) -> Moves(s, c, h, x):
  hl => Empty.absurd(
    {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{x}: Maybe<&2, Replicas.Head>},
    Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Replicas.Heads.level(Some{h}, Some{h}),
        True{},
        Equal.trans(
          Bool,
          False{},
          Replicas.Heads.level(Some{h}, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
          Replicas.Heads.level(Some{h}, Some{h}),
          Equal.sym(Bool, Replicas.Heads.level(Some{h}, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)), False{}, hl),
          Equal.cong(
            Maybe<&2, Replicas.Head>,
            Bool,
            m => Replicas.Heads.level(Some{h}, m),
            Replicas.Node.head_of(~Basics.Ask.machine(), s, c),
            Some{h},
            em
          )
        ),
        Level.refl(h)
      )
    )
  )

# one of two nodes, each with its head moved to x or not at all
def Moves.when(
  b: Bool,
  -sx: Replicas.Node<Basics.Ask>,
  -sy: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -h: Replicas.Head,
  -x: Replicas.Head,
  hx: Moves(sx, c, h, x),
  hy: Moves(sy, c, h, x)
) -> Moves(Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => sx, u => sy), c, h, x):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of a line, after it is set
def Head.at_set(
  b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  hd: Replicas.Head
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c) == Some{hd}: Maybe<&2, Replicas.Head>}:
  Equal.trans(
    Maybe<&2, Replicas.Head>,
    Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c),
    Bool.pick(
      Maybe<&2, Replicas.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c)
    ),
    Some{hd},
    Head.of_set(b0, c, hd, c),
    Pick.of(
      Maybe<&2, Replicas.Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c),
      Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
    )
  )

# Advance.moved moves the head to hd, or not at all
def Advance.moved.moves(
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  hd: Replicas.Head,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  -x: Replicas.Head,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ex: {hd == x: Replicas.Head}
) -> Moves(Replicas.Advance.moved(~Basics.Ask.machine(), s, m, c, hd, qs), c, h, x):
  match m:
    case None{}:
      Moves.stay(s, c, h, x, em)
    case Some{+s3}:
      hl =>
        %ex: {
          Replicas.Node.head_of(~Basics.Ask.machine(), 
            Replicas.State.moved(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)), c, hd, qs),
            c
          )
            == Some{_}: Maybe<&2, Replicas.Head>
        }
        Head.at_set(
          Replicas.Wait.set(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
            c,
            Replicas.Wait.left(
              Replicas.Wait.of(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)), c),
              Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
            )
          ),
          c,
          hd
        )

# Advance.ran.moves once whether the run gives the tip that the step names is
# known (bq)
def Advance.ran.moves.if(
  s: Replicas.Node<Basics.Ask>,
  s2: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  -x: Replicas.Head,
  bq: Bool,
  ebq: {Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}) == bq: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ex: {
    Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}) == True{}: Bool
  } -> {Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}} == x: Replicas.Head}
) -> Moves(
  Shared.Bool.when(
    Replicas.Node<Basics.Ask>,
    bq,
    u => Replicas.Advance.moved(~Basics.Ask.machine(), 
      s,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      c,
      Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
      qs
    ),
    u => s
  ),
  c,
  h,
  x
):
  match bq:
    case True{}:
      Advance.moved.moves(
        s,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
        c,
        Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
        qs,
        h,
        x,
        em,
        ex(ebq)
      )
    case False{}:
      Moves.stay(s, c, h, x, em)

# a checked step moves the head to the tip that the step names, or not at all
def Advance.ran.moves(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  h: Replicas.Head,
  -x: Replicas.Head,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ex: @t2: Replicas.Tip -> {
    Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}) == True{}: Bool
  } -> {Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}} == x: Replicas.Head}
) -> Moves(Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, m), c, h, x):
  match m:
    case None{}:
      Moves.stay(s, c, h, x, em)
    case Some{Replicas.Run{s2, +t2}}:
      Advance.ran.moves.if(
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        after,
        qs,
        h,
        x,
        Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        {==},
        em,
        ex(t2)
      )

# Node.advance moves the head by the decided step m, or not at all
def Advance.step.moves(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> Moves(Replicas.Advance.step(~Stepping.Ask.kernel(), s, c, h, t, m), c, h, Head.step(h, m)):
  match h m:
    case Replicas.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(
        Replicas.Root.same(before, th),
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        c,
        Replicas.Head{r, br, next, th},
        Head.step(Replicas.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
        Advance.ran.moves(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs),
          Replicas.Head{r, br, next, th},
          Head.step(Replicas.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(Maybe<&2, Hashes.Hash>, after, Some{Replicas.Tip.hash(t2)}, Shared.Maybe.is_eq_sound(~Hashes.Hash, ~Hashes.Hash.is_eq, x => y => Hashes.Hash.is_eq_sound(x, y), after, Some{Replicas.Tip.hash(t2)})(er)): {Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}} == Head.step(Replicas.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Replicas.Head}
            {==}),
        Moves.stay(
          s,
          c,
          Replicas.Head{r, br, next, th},
          Head.step(Replicas.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em
        )
      )
    case Replicas.Head{+r, +br, +next, +th} None{}:
      em => Moves.stay(s, c, Replicas.Head{r, br, next, th}, Replicas.Head{r, br, next, th}, em)

# Node.advance moves the head by the step decided at the head h, whose tip is
# m, or not at all
def Advance.at.moves(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
} -> Moves(Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, m), c, h, Head.step(h, Advance.vote(s, c, h))):
  match m:
    case None{}:
      em => et => Moves.stay(s, c, h, Head.step(h, Advance.vote(s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.vote(s, c, h),
          Replicas.Height.decide(~Basics.Ask.machine(), 
            s,
            c,
            Replicas.Head.next(h),
            Replicas.Tip.owners(t),
            Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
          ),
          Equal.cong(
            Maybe<&2, Replicas.Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Replicas.Tip,
              Ledgers.Vote,
              mt,
              t1 => Replicas.Height.decide(~Basics.Ask.machine(), 
                s,
                c,
                Replicas.Head.next(h),
                Replicas.Tip.owners(t1),
                Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
              )
            ),
            Replicas.Head.tip(~Basics.Ask.machine(), s, h),
            Some{t},
            et
          )
        ): Moves(
          Replicas.Advance.step(~Stepping.Ask.kernel(), 
            s,
            c,
            h,
            t,
            Replicas.Height.decide(~Basics.Ask.machine(), 
              s,
              c,
              Replicas.Head.next(h),
              Replicas.Tip.owners(t),
              Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
            )
          ),
          c,
          h,
          Head.step(h, _)
        )
        Advance.step.moves(
          s,
          c,
          h,
          t,
          Replicas.Height.decide(~Basics.Ask.machine(), 
            s,
            c,
            Replicas.Head.next(h),
            Replicas.Tip.owners(t),
            Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
          )
        )(em)

# a head moves only to the tip that the owners in its tip decided next
def Advance.decided(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +h: Replicas.Head
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Heads.level(Some{h}, Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.Node.advance(~Stepping.Ask.kernel(), s, c), c)) == False{}: Bool
} -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), 
    Replicas.Node.advance(~Stepping.Ask.kernel(), s, c),
    c
  )
    == Some{Head.step(h, Advance.vote(s, c, h))}: Maybe<&2, Replicas.Head>
}:
  +em =>
    %Equal.sym(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), s, c),
      Some{h},
      em
    ): Moves(Replicas.Advance.head(~Stepping.Ask.kernel(), s, c, _), c, h, Head.step(h, Advance.vote(s, c, h)))
    Advance.at.moves(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  -R: Type,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
} -> {
  Maybe.bind(
    &2,
    Replicas.Tip,
    Ledgers.Vote,
    m,
    t => Replicas.Height.decide(~Basics.Ask.machine(), s, c, Replicas.Head.next(h), Replicas.Tip.owners(t), k)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Replicas.Tip -> @q: Nat -> {
    Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(h), q},
      Replicas.Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Vote, v, e))
    case Some{+t}:
      em => e => f => Scan.elim(
        R,
        s,
        c,
        Replicas.Head.next(h),
        Replicas.Tip.owners(t),
        k,
        v
      )(e)(q => d => f(t)(q)(em)(d))

# a step that a node found at a head is decided at the head's tip, in some
# round
def Found.elim(
  -R: Type,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +h: Replicas.Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Advance.found(s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Replicas.Tip -> @q: Nat -> {
    Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(h), q},
      Replicas.Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  Found.elim.at(R, s, c, h, k, v, Replicas.Head.tip(~Basics.Ask.machine(), s, h))({==})

# Writes
# ------

# the value of a resource reads back
def Res.round(
  m: Maybe<&2, Ropes.Root>
) -> {Basics.Res.read(Basics.Res.code(m)) == m: Maybe<&2, Ropes.Root>}:
  %Equal.sym(
    Maybe<&2, Codes.Read<Maybe<&2, Ropes.Root>>>,
    Codes.Code.maybe.read(
      ~Ropes.Root,
      ~Ropes.Root.code.read,
      Codes.Code.maybe(~Ropes.Root, ~Ropes.Root.code, m, [])
    ),
    Some{Codes.Read{m, []}},
    Codes.Code.maybe_read(
      ~Ropes.Root,
      ~Ropes.Root.code,
      ~Ropes.Root.code.read,
      x => r => Ropes.Root.code_read(x, r),
      m,
      []
    )
  ): {Basics.Res.of.read(_) == m: Maybe<&2, Ropes.Root>}
  {==}

# the verdict m takes
def Verdict.took(m: Maybe<&2, Replicas.Verdict<Basics.Ask>>) -> Bool:
  match m:
    case Some{Replicas.Verdict.Taken{Replicas.Work{s2, h}}}:
      True{}
    case x:
      False{}

# the tree of the verdict m
def Took.root(m: Maybe<&2, Replicas.Verdict<Basics.Ask>>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Replicas.Verdict.Taken{Replicas.Work{s2, h}}}:
      h
    case x:
      None{}

# the node of the verdict m, or d when it takes nothing
def Took.node(m: Maybe<&2, Replicas.Verdict<Basics.Ask>>, d: Replicas.Node<Basics.Ask>) -> Replicas.Node<Basics.Ask>:
  match m:
    case Some{Replicas.Verdict.Taken{Replicas.Work{s2, h}}}:
      s2
    case x:
      d

# a verdict that takes, after a verdict, is the verdict of what comes next
def Then.took(
  m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Replicas.Node<Basics.Ask>
) -> {
  Judging.Judge.then(m, k) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
} -> {k(Unit{}) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>}:
  match m:
    case Some{True{}}:
      e => e
    case Some{False{}}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Replicas.Verdict<Basics.Ask>>,
            Bool,
            v => Verdict.took(v),
            Judging.Judge.refuse(),
            Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
            e
          )
        )
      )
    case None{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>},
        Shared.Maybe.none_ne_some(Replicas.Verdict<Basics.Ask>, Replicas.Verdict.Taken{Replicas.Work{s3, h2}}, e)
      )

# a verdict that takes, under a condition, is the verdict of what comes next
def When.took(
  b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Replicas.Node<Basics.Ask>
) -> {
  Judging.Judge.when(b, k) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
} -> {k(Unit{}) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Replicas.Verdict<Basics.Ask>>,
            Bool,
            v => Verdict.took(v),
            Judging.Judge.refuse(),
            Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
            e
          )
        )
      )

# Set.reads once the node m2 that the put of the new subtree gives is known
def Set.reads.put(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  ws: List<&2, List<&2, U32>>,
  m2: Maybe<&2, Replicas.Node<Basics.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Replicas.Node<Basics.Ask>,
  hp: @y: Replicas.Node<Basics.Ask> -> {
    m2 == Some{y}: Maybe<&2, Replicas.Node<Basics.Ask>>
  } -> {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), y, ws) == True{}: Bool}
) -> {
  Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>
} -> {
  Replicas.Work.take(~Basics.Ask.machine(), 
    Replicas.Work.on(~Basics.Ask.machine(), m2, Some{hh})
  )
    == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
} -> {Replicas.Node.get(~Basics.Ask.machine(), s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m2:
    case None{}:
      es => e => Empty.absurd(
        {Replicas.Node.get(~Basics.Ask.machine(), s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Replicas.Verdict<Basics.Ask>, Replicas.Verdict.Taken{Replicas.Work{s3, h2}}, e)
      )
    case Some{+sk}:
      es => +e =>
        %Equal.cong(
          Maybe<&2, Replicas.Verdict<Basics.Ask>>,
          Replicas.Node<Basics.Ask>,
          v => Took.node(v, s3),
          Some{Replicas.Verdict.Taken{Replicas.Work{sk, Some{hh}}}},
          Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
          e
        ): {Replicas.Node.get(~Basics.Ask.machine(), _, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.cong(
          Maybe<&2, Replicas.Verdict<Basics.Ask>>,
          Maybe<&2, Hashes.Hash>,
          v => Took.root(v),
          Some{Replicas.Verdict.Taken{Replicas.Work{sk, Some{hh}}}},
          Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
          e
        ): {Replicas.Node.get(~Basics.Ask.machine(), sk, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Basics.Ask.machine(), sk, Some{hh}, k),
          Trees.Tree.get.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, Some{hh}, k),
          Some{x},
          Trees.Tree.get_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), sk, Some{hh}, k),
          Trees.Tree.get_set(
            ~Replicas.Node<Basics.Ask>,
            ~Replicas.Store.fetch(~Basics.Ask.machine()),
            s,
            sk,
            h,
            k,
            x,
            Trees.Put{hh, ws}
          )(
            Equal.trans(
              Maybe<&2, Trees.Put>,
              Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
              Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
              Some{Trees.Put{hh, ws}},
              Equal.sym(
                Maybe<&2, Trees.Put>,
                Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x),
                Trees.Tree.set.plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x),
                Trees.Tree.set_plain(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h, k, x)
              ),
              es
            )
          )(hp(sk)({==}))
        )

# a key set in a tree, when the verdict takes the new tree, reads back in a
# node that holds the new nodes
def Set.reads(
  +s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Replicas.Node<Basics.Ask>
) -> {
  Replicas.Node.set(~Basics.Ask.machine(), s, h, k, x) == m: Maybe<&2, Trees.Put>
} -> {
  Replicas.Work.take(~Basics.Ask.machine(), 
    Replicas.Work.of(~Basics.Ask.machine(), s, m)
  )
    == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
} -> {Replicas.Node.get(~Basics.Ask.machine(), s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      es => e => Empty.absurd(
        {Replicas.Node.get(~Basics.Ask.machine(), s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Replicas.Verdict<Basics.Ask>, Replicas.Verdict.Taken{Replicas.Work{s3, h2}}, e)
      )
    case Some{Trees.Put{hh, +ws}}:
      Set.reads.put(
        s,
        h,
        k,
        x,
        hh,
        ws,
        Replicas.State.put(~Basics.Ask.machine(), s, ws),
        h2,
        s3,
        y => ey => Put.holds(s, ws, y)(ey)
      )

# a verdict that takes, after a read, is the verdict of what comes next
def With.took(
  -A: Data,
  ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  -kk: Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Replicas.Node<Basics.Ask>
) -> (
  @a: A -> {
    k(a) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
  } -> {kk == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>}
) -> {
  Maybe.bind(
    &2,
    A,
    Replicas.Verdict<Basics.Ask>,
    ma,
    k
  )
    == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>
} -> {kk == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>}:
  match ma:
    case None{}:
      hk => e => Empty.absurd(
        {kk == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>},
        Shared.Maybe.none_ne_some(Replicas.Verdict<Basics.Ask>, Replicas.Verdict.Taken{Replicas.Work{s3, h2}}, e)
      )
    case Some{a}:
      hk => e => hk(a)(e)

def Spec.Judge.write_reads(s, n, base, c, h, h2, s3, m):
  e => ec =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Replicas.Node.get(~Basics.Ask.machine(), s3, h2, Basics.Key.res(n)),
      Some{Basics.Res.code(m)},
      Set.reads(s, h, Basics.Key.res(n), Basics.Res.code(m), Replicas.Node.set(~Basics.Ask.machine(), s, h, Basics.Key.res(n), Basics.Res.code(m)), h2, s3)(
        {==}
      )(
        With.took(
          Maybe<&2, Ropes.Root>,
          Basics.Res.find(s, h, n),
          a1 => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Basics.Res.find(s, Basics.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Basics.Ask>,
              Judging.Content.find(s, n, c),
              m1 => Judging.Judge.when(
                Basics.Roots.same(a1, b1),
                x => Replicas.Work.take(~Basics.Ask.machine(), 
                  Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))
                )
              )
            )
          ),
          Replicas.Work.take(~Basics.Ask.machine(), 
            Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
          ),
          h2,
          s3
        )(
          +a => With.took(
            Maybe<&2, Ropes.Root>,
            Basics.Res.find(s, Basics.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Basics.Ask>,
              Judging.Content.find(s, n, c),
              m1 => Judging.Judge.when(
                Basics.Roots.same(a, b1),
                x => Replicas.Work.take(~Basics.Ask.machine(), 
                  Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))
                )
              )
            ),
            Replicas.Work.take(~Basics.Ask.machine(), 
              Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
            ),
            h2,
            s3
          )(
            +b => ex => When.took(Basics.Roots.same(a, b), x => Replicas.Work.take(~Basics.Ask.machine(), 
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              ), h2, s3)(
              %ec: {Maybe.bind(&2, Maybe<&2, Ropes.Root>, Replicas.Verdict<Basics.Ask>, _, m1 => Judging.Judge.when(Basics.Roots.same(a, b), x => Replicas.Work.take(~Basics.Ask.machine(), Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))))) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Basics.Ask>>}
              ex)
          )
        )(
          Then.took(Judging.Judge.content(s, c), w => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Basics.Ask>,
              Basics.Res.find(s, h, n),
              a1 => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Verdict<Basics.Ask>,
                Basics.Res.find(s, Basics.Node.root_of(s, base), n),
                b1 => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Replicas.Verdict<Basics.Ask>,
                  Judging.Content.find(s, n, c),
                  m1 => Judging.Judge.when(
                    Basics.Roots.same(a1, b1),
                    x => Replicas.Work.take(~Basics.Ask.machine(), 
                      Replicas.Work.set(~Basics.Ask.machine(), 
                        Replicas.Work{s, h},
                        Basics.Key.res(n),
                        Basics.Res.code(m1)
                      )
                    )
                  )
                )
              )
            ), h2, s3)(
            Then.took(Judging.Judge.ready_maybe(s, base), u => Judging.Judge.then(
                Judging.Judge.content(s, c),
                w => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Replicas.Verdict<Basics.Ask>,
                  Basics.Res.find(s, h, n),
                  a1 => Maybe.bind(
                    &2,
                    Maybe<&2, Ropes.Root>,
                    Replicas.Verdict<Basics.Ask>,
                    Basics.Res.find(s, Basics.Node.root_of(s, base), n),
                    b1 => Maybe.bind(
                      &2,
                      Maybe<&2, Ropes.Root>,
                      Replicas.Verdict<Basics.Ask>,
                      Judging.Content.find(s, n, c),
                      m1 => Judging.Judge.when(
                        Basics.Roots.same(a1, b1),
                        x => Replicas.Work.take(~Basics.Ask.machine(), 
                          Replicas.Work.set(~Basics.Ask.machine(), 
                            Replicas.Work{s, h},
                            Basics.Key.res(n),
                            Basics.Res.code(m1)
                          )
                        )
                      )
                    )
                  )
                )
              ), h2, s3)(e)
          )
        )
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Ropes.Root,
        _,
        ws => Basics.Res.read(ws)
      )
        == m: Maybe<&2, Ropes.Root>
    }
    Res.round(m)

# Merges
# ------
def Spec.Pick.merge_theirs(f, s, b, o, t):
  e =>
    %Equal.sym(
      Bool,
      Basics.Roots.same(o, b),
      True{},
      e
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        _,
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), Basics.Roots.same(t, b)),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{t}}: Maybe<&2, Judging.Pick>
    }
    {==}

def Spec.Pick.merge_ours(f, s, b, o, t):
  e1 => e2 =>
    %Equal.sym(
      Bool,
      Basics.Roots.same(o, b),
      False{},
      e1
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        _,
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), Basics.Roots.same(t, b)),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>
    }
    %Equal.sym(
      Bool,
      Basics.Roots.same(t, b),
      True{},
      e2
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        False{},
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), _),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>
    }
    {==}

# Seals
# -----

# Seal.accept_fits once whether the ballot fits is known (f)
def Accept.fits.if(
  f: Bool,
  -x: Replicas.Node<Basics.Ask>,
  -s2: Replicas.Node<Basics.Ask>
) -> {
  Shared.Maybe.when(Replicas.Node<Basics.Ask>, f, u => Some{x}) == Some{s2}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Replicas.Node<Basics.Ask>, s2, e))

def Spec.Seal.accept_fits(s, b, c, s2):
  ec => ea => Accept.fits.if(
    Replicas.Seal.fits(c, b),
    Replicas.State.keyed(~Basics.Ask.machine(), 
      Replicas.State.led(~Basics.Ask.machine(), 
        s,
        Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
      ),
      Replicas.Keys.saw(
        Replicas.Keys.set(
          Replicas.State.keys(~Basics.Ask.machine(), s),
          Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
          Replicas.Keychain.next(c, b)
        ),
        Replicas.Ballot.at(b)
      )
    ),
    s2
  )(
    %ec: {Replicas.Seal.accept.at(~Basics.Ask.machine(), s, b, _) == Some{s2}: Maybe<&2, Replicas.Node<Basics.Ask>>}
    ea)

# a place is the same as itself
def Prev.refl(m: Maybe<&2, Ledgers.Where>) -> {Replicas.Prev.same(m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Ledgers.Where.code(w, []))

def Spec.Seal.fits_own(seed, x, last, k, n, f):
  Shared.List.all.if_both(
    Replicas.Prev.same(last, last),
    u => Ledgers.Ballot.sealed(Seals.Seal.public(seed), Ledgers.Ballot.make(seed, x, last, k))
  )(Prev.refl(last))(Ledgers.Ballot.sealed_make(seed, x, last, k))

# a head that no step moves is at its own height
def Level.none(
  x: Replicas.Head
) -> {Replicas.Heads.level(Some{x}, Some{Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Replicas.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# that the rounds of each height of the line c decide one step in s
def Line.One(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> Type:
  @x: Replicas.Head -> @t: Replicas.Tip -> {
    Replicas.Head.tip(~Basics.Ask.machine(), s, x) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> Replicas.Height.One(~Basics.Ask.machine(), s, c, Replicas.Head.next(x), Replicas.Tip.owners(t))

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(k: Nat, s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(p, s, c) & Line.One(s, c)

# Histories
# ---------

# In.grows once the tip m of the head in a is known
def In.grows.at(
  +a: Replicas.Node<Basics.Ask>,
  +u: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +x: Replicas.Head,
  r: Nat,
  v: Ledgers.Vote,
  m: Maybe<&2, Replicas.Tip>,
  +g: {Replicas.Node.grows(~Basics.Ask.machine(), a, u) == True{}: Bool}
) -> {
  Replicas.Head.tip(~Basics.Ask.machine(), a, x) == m: Maybe<&2, Replicas.Tip>
} -> {
  Maybe.bind(
    &2,
    Replicas.Tip,
    Ledgers.Vote,
    m,
    t => Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Ledgers.Where{c, Replicas.Head.next(x), r},
      Replicas.Tip.owners(t)
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{t}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Replicas.Tip>,
          Replicas.Head.tip(~Basics.Ask.machine(), u, x),
          Some{t},
          Head.tip.grows(a, u, x, t, g)(em)
        ): {
          Maybe.bind(
            &2,
            Replicas.Tip,
            Ledgers.Vote,
            _,
            t1 => Ledgers.State.decide(
              ~Basics.Ask,
              Replicas.State.ledger(~Basics.Ask.machine(), u),
              Ledgers.Where{c, Replicas.Head.next(x), r},
              Replicas.Tip.owners(t1)
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        Decide.up(a, u, t, Ledgers.Where{c, Replicas.Head.next(x), r}, v, g)(e)

# a step that the owners decided at a head in a round, in a, they decided in
# a node that grew
def In.grows(
  +a: Replicas.Node<Basics.Ask>,
  u: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +x: Replicas.Head,
  r: Nat,
  v: Ledgers.Vote,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, u) == True{}: Bool}
) -> {
  Replicas.Advance.in(~Basics.Ask.machine(), a, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  In.grows.at(a, u, c, x, r, v, Replicas.Head.tip(~Basics.Ask.machine(), a, x), g)({==})

# Moved.grows once the step va that a holds at the head is known
def Moved.grows.at(
  a: Replicas.Node<Basics.Ask>,
  u: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  x: Replicas.Head,
  -y: Replicas.Head,
  r: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, u) == True{}: Bool}
) -> {
  Replicas.Advance.in(~Basics.Ask.machine(), a, c, x, r) == va: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Head.moved(x, va) == Some{y}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.moved(x, Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r)) == Some{y}: Maybe<&2, Replicas.Head>}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Replicas.Head.moved(x, Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r)) == Some{y}: Maybe<&2, Replicas.Head>},
        Shared.Maybe.none_ne_some(Replicas.Head, y, e)
      )
    case Some{v}:
      ea => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r),
          Some{v},
          In.grows(a, u, c, x, r, v, g)(ea)
        ): {Replicas.Head.moved(x, _) == Some{y}: Maybe<&2, Replicas.Head>}
        e

# a head that a decided step moves in a, it moves the same in a node that grew
def Moved.grows(
  +a: Replicas.Node<Basics.Ask>,
  u: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +x: Replicas.Head,
  -y: Replicas.Head,
  +r: Nat,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, u) == True{}: Bool}
) -> {
  Replicas.Head.moved(x, Replicas.Advance.in(~Basics.Ask.machine(), a, c, x, r)) == Some{y}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.moved(x, Replicas.Advance.in(~Basics.Ask.machine(), u, c, x, r)) == Some{y}: Maybe<&2, Replicas.Head>}:
  Moved.grows.at(a, u, c, x, y, r, Replicas.Advance.in(~Basics.Ask.machine(), a, c, x, r), g)({==})

def Spec.Line.at_grows(rs, a, u, c, h, x):
  match rs:
    case Nil{}:
      g => e => e
    case Con{r, +rest}:
      +g => Shared.Maybe.bind_kept(
        Replicas.Head,
        Replicas.Head,
        Replicas.Line.at(~Basics.Ask.machine(), rest, a, c, h),
        Replicas.Line.at(~Basics.Ask.machine(), rest, u, c, h),
        +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), a, c, z, r)),
        +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z, r)),
        x,
        +z => Spec.Line.at_grows(rest, a, u, c, h, z)(g),
        +z => Moved.grows(a, u, c, z, x, r, g)
      )

# Step.same once what the two rounds decide is known (w1, w2)
def Step.same.at(
  u: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  z: Replicas.Head,
  r1: Nat,
  r2: Nat,
  t: Replicas.Tip,
  -x: Replicas.Head,
  -y: Replicas.Head,
  w1: Maybe<&2, Ledgers.Vote>,
  w2: Maybe<&2, Ledgers.Vote>,
  one: Replicas.Height.One(~Basics.Ask.machine(), u, c, Replicas.Head.next(z), Replicas.Tip.owners(t))
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), u),
    Ledgers.Where{c, Replicas.Head.next(z), r1},
    Replicas.Tip.owners(t)
  )
    == w1: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Replicas.State.ledger(~Basics.Ask.machine(), u),
    Ledgers.Where{c, Replicas.Head.next(z), r2},
    Replicas.Tip.owners(t)
  )
    == w2: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Head.moved(z, w1) == Some{x}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.moved(z, w2) == Some{y}: Maybe<&2, Replicas.Head>} -> {x == y: Replicas.Head}:
  match w1 w2:
    case None{} b:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Replicas.Head},
        Shared.Maybe.none_ne_some(Replicas.Head, x, k1)
      )
    case Some{v1} None{}:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Replicas.Head},
        Shared.Maybe.none_ne_some(Replicas.Head, y, k2)
      )
    case Some{+v1} Some{v2}:
      e1 => e2 => k1 => k2 => Shared.Maybe.some_inj(
        Replicas.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Replicas.Head>,
          Some{x},
          Replicas.Head.moved(z, Some{v1}),
          Some{y},
          Equal.sym(Maybe<&2, Replicas.Head>, Replicas.Head.moved(z, Some{v1}), Some{x}, k1),
          Equal.trans(
            Maybe<&2, Replicas.Head>,
            Replicas.Head.moved(z, Some{v1}),
            Replicas.Head.moved(z, Some{v2}),
            Some{y},
            Equal.cong(
              Ledgers.Vote,
              Maybe<&2, Replicas.Head>,
              v => Replicas.Head.moved(z, Some{v}),
              v1,
              v2,
              one(r1)(r2)(v1)(v2)(e1)(e2)
            ),
            k2
          )
        )
      )

# the steps of two rounds at one head move it the same, once the tip m of
# the head is known
def Step.same(
  +u: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +z: Replicas.Head,
  +r1: Nat,
  +r2: Nat,
  -x: Replicas.Head,
  -y: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>,
  one: Line.One(u, c)
) -> {
  Replicas.Head.tip(~Basics.Ask.machine(), u, z) == m: Maybe<&2, Replicas.Tip>
} -> {
  Replicas.Head.moved(
    z,
    Maybe.bind(
      &2,
      Replicas.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), u),
        Ledgers.Where{c, Replicas.Head.next(z), r1},
        Replicas.Tip.owners(t)
      )
    )
  )
    == Some{x}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.moved(
    z,
    Maybe.bind(
      &2,
      Replicas.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Basics.Ask,
        Replicas.State.ledger(~Basics.Ask.machine(), u),
        Ledgers.Where{c, Replicas.Head.next(z), r2},
        Replicas.Tip.owners(t)
      )
    )
  )
    == Some{y}: Maybe<&2, Replicas.Head>
} -> {x == y: Replicas.Head}:
  match m:
    case None{}:
      em => k1 => k2 => Empty.absurd(
        {x == y: Replicas.Head},
        Shared.Maybe.none_ne_some(Replicas.Head, x, k1)
      )
    case Some{+t}:
      em => k1 => k2 =>
        Step.same.at(
          u,
          c,
          z,
          r1,
          r2,
          t,
          x,
          y,
          Ledgers.State.decide(
            ~Basics.Ask,
            Replicas.State.ledger(~Basics.Ask.machine(), u),
            Ledgers.Where{c, Replicas.Head.next(z), r1},
            Replicas.Tip.owners(t)
          ),
          Ledgers.State.decide(
            ~Basics.Ask,
            Replicas.State.ledger(~Basics.Ask.machine(), u),
            Ledgers.Where{c, Replicas.Head.next(z), r2},
            Replicas.Tip.owners(t)
          ),
          one(z)(t)(em)
        )({==})({==})(k1)(k2)

# At.same for one more step of each history, once the heads before are known
def At.same.step(
  +u: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r1: Nat,
  r2: Nat,
  -x: Replicas.Head,
  -y: Replicas.Head,
  m1: Maybe<&2, Replicas.Head>,
  m2: Maybe<&2, Replicas.Head>,
  one: Line.One(u, c),
  ih: @z1: Replicas.Head -> @z2: Replicas.Head -> {
    m1 == Some{z1}: Maybe<&2, Replicas.Head>
  } -> {m2 == Some{z2}: Maybe<&2, Replicas.Head>} -> {z1 == z2: Replicas.Head}
) -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    Replicas.Head,
    m1,
    +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z, r1))
  )
    == Some{x}: Maybe<&2, Replicas.Head>
} -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    Replicas.Head,
    m2,
    +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z, r2))
  )
    == Some{y}: Maybe<&2, Replicas.Head>
} -> {x == y: Replicas.Head}:
  match m1 m2:
    case None{} b:
      k1 => k2 => Empty.absurd({x == y: Replicas.Head}, Shared.Maybe.none_ne_some(Replicas.Head, x, k1))
    case Some{z1} None{}:
      k1 => k2 => Empty.absurd({x == y: Replicas.Head}, Shared.Maybe.none_ne_some(Replicas.Head, y, k2))
    case Some{+z1} Some{z2}:
      k1 => k2 =>
        Step.same(
          u,
          c,
          z1,
          r1,
          r2,
          x,
          y,
          Replicas.Head.tip(~Basics.Ask.machine(), u, z1),
          one
        )(
          {==}
        )(
          k1
        )(
          Equal.trans(
            Maybe<&2, Replicas.Head>,
            Replicas.Head.moved(z1, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z1, r2)),
            Replicas.Head.moved(z2, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z2, r2)),
            Some{y},
            Equal.cong(
              Replicas.Head,
              Maybe<&2, Replicas.Head>,
              +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), u, c, z, r2)),
              z1,
              z2,
              ih(z1)(z2)({==})({==})
            ),
            k2
          )
        )

# At.same for one more step of each history, with the witness of each step
def At.same.con(
  +u: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  r1: Nat,
  r2: Nat,
  t1: List<&2, Nat>,
  t2: List<&2, Nat>,
  -x: Replicas.Head,
  -y: Replicas.Head,
  ones: Line.Ones(List.length(&2, Nat, t1), u, c) & Line.One(u, c),
  ih: @z1: Replicas.Head -> @z2: Replicas.Head -> Line.Ones(
    List.length(&2, Nat, t1),
    u,
    c
  ) -> {
    Replicas.Line.at(~Basics.Ask.machine(), t1, u, c, h) == Some{z1}: Maybe<&2, Replicas.Head>
  } -> {Replicas.Line.at(~Basics.Ask.machine(), t2, u, c, h) == Some{z2}: Maybe<&2, Replicas.Head>} -> {z1 == z2: Replicas.Head}
) -> {
  Replicas.Line.at(~Basics.Ask.machine(), r1 <> t1, u, c, h) == Some{x}: Maybe<&2, Replicas.Head>
} -> {Replicas.Line.at(~Basics.Ask.machine(), r2 <> t2, u, c, h) == Some{y}: Maybe<&2, Replicas.Head>} -> {x == y: Replicas.Head}:
  match ones:
    case Tuple{rest, one}:
      At.same.step(
        u,
        c,
        r1,
        r2,
        x,
        y,
        Replicas.Line.at(~Basics.Ask.machine(), t1, u, c, h),
        Replicas.Line.at(~Basics.Ask.machine(), t2, u, c, h),
        one,
        z1 => z2 => ih(z1)(z2)(rest)
      )

# in one node, the same number of decided steps from one head give one head,
# whatever the round of each step
def At.same(
  rs1: List<&2, Nat>,
  rs2: List<&2, Nat>,
  +u: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  x: Replicas.Head,
  y: Replicas.Head
) -> Line.Ones(List.length(&2, Nat, rs1), u, c)
  -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
  -> {Replicas.Line.at(~Basics.Ask.machine(), rs1, u, c, h) == Some{x}: Maybe<&2, Replicas.Head>}
  -> {Replicas.Line.at(~Basics.Ask.machine(), rs2, u, c, h) == Some{y}: Maybe<&2, Replicas.Head>}
  -> {x == y: Replicas.Head}:
  match rs1 rs2:
    case Nil{} Nil{}:
      ones => el => e1 => e2 => Shared.Maybe.some_inj(
        Replicas.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Replicas.Head>,
          Some{x},
          Some{h},
          Some{y},
          Equal.sym(Maybe<&2, Replicas.Head>, Some{h}, Some{x}, e1),
          e2
        )
      )
    case Nil{} Con{r2, t2}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Replicas.Head},
        Shared.Nat.zero_ne_succ(List.length(&2, Nat, t2), el)
      )
    case Con{r1, t1} Nil{}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Replicas.Head},
        Shared.Nat.zero_ne_succ(
          List.length(&2, Nat, t1),
          Equal.sym(Nat, 1n+List.length(&2, Nat, t1), 0n, el)
        )
      )
    case Con{+r1, +t1} Con{r2, +t2}:
      ones => el =>
        At.same.con(
          u,
          c,
          h,
          r1,
          r2,
          t1,
          t2,
          x,
          y,
          ones,
          z1 => z2 => rest => At.same(
            t1,
            t2,
            u,
            c,
            h,
            z1,
            z2
          )(rest)(Shared.Nat.succ_inj(List.length(&2, Nat, t1), List.length(&2, Nat, t2), el))
        )

# a step that changes the height of a head moves it one height up
def Moved.step(
  h: Replicas.Head,
  v: Ledgers.Vote
) -> {
  Replicas.Heads.level(Some{h}, Some{Head.step(h, Some{v})}) == False{}: Bool
} -> {
  Replicas.Head.moved(h, Some{v}) == Some{Head.step(h, Some{v})}: Maybe<&2, Replicas.Head>
}:
  match h v:
    case Replicas.Head{r, b, n, th} Ledgers.Vote{before, qs, Some{y}}:
      e => {==}
    case Replicas.Head{r, b, n, th} Ledgers.Vote{before, qs, None{}}:
      e => Empty.absurd(
        {None{} == Some{Replicas.Head{r, b, n, th}}: Maybe<&2, Replicas.Head>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Replicas.Heads.level(Some{Replicas.Head{r, b, n, th}}, Some{Replicas.Head{r, b, n, th}}),
            True{},
            Equal.sym(
              Bool,
              Replicas.Heads.level(Some{Replicas.Head{r, b, n, th}}, Some{Replicas.Head{r, b, n, th}}),
              False{},
              e
            ),
            Level.refl(Replicas.Head{r, b, n, th})
          )
        )
      )

# Node.advance_at once the step m that the node found at the head is known
def Advance.at.one(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Advance.vote(s, c, h) == m: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Heads.level(Some{h}, Some{Head.step(h, m)}) == False{}: Bool
} -> Exists(
  Nat,
  q => {Replicas.Line.at(~Basics.Ask.machine(), [q], s, c, h) == Some{Head.step(h, m)}: Maybe<&2, Replicas.Head>}
):
  match m:
    case None{}:
      em => hl => Empty.absurd(
        Exists(
          Nat,
          q => {
            Replicas.Line.at(~Basics.Ask.machine(), 
              [q],
              s,
              c,
              h
            )
              == Some{Head.step(h, None{})}: Maybe<&2, Replicas.Head>
          }
        ),
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Replicas.Heads.level(Some{h}, Some{Head.step(h, None{})}),
            True{},
            Equal.sym(
              Bool,
              Replicas.Heads.level(Some{h}, Some{Head.step(h, None{})}),
              False{},
              hl
            ),
            Level.none(h)
          )
        )
      )
    case Some{v}:
      em => hl =>
        Found.elim(
          Exists(
            Nat,
            q => {
              Replicas.Line.at(~Basics.Ask.machine(), 
                [q],
                s,
                c,
                h
              )
                == Some{Head.step(h, Some{v})}: Maybe<&2, Replicas.Head>
            }
          ),
          s,
          c,
          h,
          Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h)),
          v
        )(em)(t => q => et => d => Tuple{q, (
              %Equal.sym(Maybe<&2, Replicas.Tip>, Replicas.Head.tip(~Basics.Ask.machine(), s, h), Some{t}, et): {Replicas.Head.moved(h, Maybe.bind(&2, Replicas.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, Replicas.Head.next(h), q}, Replicas.Tip.owners(t1)))) == Some{Head.step(h, Some{v})}: Maybe<&2, Replicas.Head>}
              %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, Replicas.Head.next(h), q}, Replicas.Tip.owners(t)), Some{v}, d): {Replicas.Head.moved(h, _) == Some{Head.step(h, Some{v})}: Maybe<&2, Replicas.Head>}
              Moved.step(h, v)(hl))})

def Spec.Node.advance_at(s, c, h):
  +eh => +hl =>
    %Equal.sym(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.Node.advance(~Stepping.Ask.kernel(), s, c), c),
      Some{Head.step(h, Advance.vote(s, c, h))},
      Advance.decided(s, c, h)(eh)(hl)
    ): Exists(Nat, q => {Replicas.Line.at(~Basics.Ask.machine(), [q], s, c, h) == _: Maybe<&2, Replicas.Head>})
    Advance.at.one(s, c, h, Advance.vote(s, c, h))({==})(
      %Advance.decided(s, c, h)(eh)(hl): {Replicas.Heads.level(Some{h}, _) == False{}: Bool}
      hl)

def Spec.Node.read_draft(s, w, r, b, n, c):
  e =>
    %Equal.sym(
      Maybe<&2, Basics.Content>,
      Reading.Node.draft(s, w, r, b, n),
      Some{c},
      e
    ): {
      Reading.Read.of(
        s,
        n,
        _,
        Basics.Point.Head{r, b}
      )
        == Basics.Root.bytes(s, Judging.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }
    {==}

# Rounds
# ------
# Two rounds of one height decide the same step (Spec.Rounds.one). A majority
# cast the step v1 in the round r1. A vote of a later round names a majority
# that passed to it; one of them cast v1 in r1 (two majorities share a node),
# and its pass names a vote of r1 or later. So the vote is the last vote of a
# round from r1 on, which is v1 by the same argument, by induction on the
# round.

# the ballots of the owners os in the round r of the height h of the line c
def Round.ballots(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  os: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Ledgers.Vote>>>:
  Ledgers.Bucket.ballots(
    ~Basics.Ask,
    Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
    os
  )

# the node o cast for the step v in the round r, as a count of ballots reads it
def Round.hit(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h: U32, r: Nat, o: String, v: Ledgers.Vote) -> Bool:
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(
      ~Basics.Ask,
      Ledgers.State.get(
        ~Basics.Ask,
        Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      )
    ),
    v
  )

# a cell that counts for the step v holds a vote for v
def Hit.step(
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  v: Ledgers.Vote
) -> {
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(~Basics.Ask, m),
    v
  )
    == True{}: Bool
} -> {Replicas.Cast.step(~Basics.Ask.machine(), m) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.Many{}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Ask{i, t, q}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{Cells.One{Ledgers.Entry.Data{ws}}}:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Pass{p}}, l}}}
    }:
      e => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(e))
    case Some{
      Cells.One{
        Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, Ledgers.Act.Vote{x, from}}, l}}
      }
    }:
      e => Equal.cong(
        Ledgers.Vote,
        Maybe<&2, Ledgers.Vote>,
        y => Some{y},
        x,
        v,
        Ledgers.Vote.is_eq_sound(x, v)(e)
      )

# a node that counts for the step v in a round cast v there
def Hit.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +o: String,
  v: Ledgers.Vote
) -> {
  Round.hit(s, c, h, r, o, v) == True{}: Bool
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, o) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Slot.bucket(c, h, r),
      Ledgers.Slot.ballot(o)
    ): {Replicas.Cast.step(~Basics.Ask.machine(), _) == Some{v}: Maybe<&2, Ledgers.Vote>}
    Hit.step(
      Ledgers.State.get(
        ~Basics.Ask,
        Ledgers.State.under(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      ),
      v
    )(e)

# a vote moved to an equal round
def Cast.moved(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  a: Nat,
  b: Nat,
  v: Ledgers.Vote,
  e: {a == b: Nat}
) -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, a}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, b}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  k =>
    %e: {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, _}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}
    k

# o when it is a hit, else rest
def Voter.if(+hit: Bool, o: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      rest

# the first node of os that cast for the step v in the round r, if any did
def Round.voter(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> Maybe<&2, String>:
  match os:
    case Nil{}:
      None{}
    case Con{+o, rest}:
      Voter.if(Round.hit(s, c, h, r, o, v), o, Round.voter(s, c, h, r, rest, v))

# no hit and no voter in the rest, when there is no voter
def Voter.if_hit(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {hit == False{}: Bool}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => {==}

def Voter.if_rest(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>
) -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>} -> {rest == None{}: Maybe<&2, String>}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {rest == None{}: Maybe<&2, String>},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => e

# Voter.cast once the hit of the first node is known
def Voter.cast.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  rest: Maybe<&2, String>,
  v: Ledgers.Vote,
  p: String,
  +hit: Bool,
  eh: {Round.hit(s, c, h, r, o, v) == hit: Bool},
  ih: {
    rest == Some{p}: Maybe<&2, String>
  } -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voter.if(hit, o, rest) == Some{p}: Maybe<&2, String>
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match hit:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          String,
          o,
          p,
          e
        ): {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Hit.cast(s, c, h, r, o, v)(eh)
    case False{}:
      e => ih(e)

# the voter cast for the step
def Voter.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote,
  +p: String
) -> {
  Round.voter(s, c, h, r, os, v) == Some{p}: Maybe<&2, String>
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match os:
    case Nil{}:
      e => Empty.absurd(
        {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(String, p, e)
      )
    case Con{+o, +rest}:
      Voter.cast.at(
        s,
        c,
        h,
        r,
        o,
        Round.voter(s, c, h, r, rest, v),
        v,
        p,
        Round.hit(s, c, h, r, o, v),
        {==},
        Voter.cast(s, c, h, r, rest, v, p)
      )

# Voter.yes once the hit of the first node is known
def Voter.yes.at(
  +hit: Bool,
  o: String,
  rest: Maybe<&2, String>,
  y: Nat,
  ih: {rest == None{}: Maybe<&2, String>} -> {y == 0n: Nat}
) -> {
  Voter.if(hit, o, rest) == None{}: Maybe<&2, String>
} -> {Shared.Nat.add_if(hit, y) == 0n: Nat}:
  match hit:
    case True{}:
      e => Empty.absurd(
        {1n+y == 0n: Nat},
        Shared.Maybe.none_ne_some(String, o, Equal.sym(Maybe<&2, String>, Some{o}, None{}, e))
      )
    case False{}:
      e => ih(e)

# with no voter, no ballot is for the step
def Voter.yes(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Round.voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>
} -> {
  Quorums.Quorum.yes(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == 0n: Nat
}:
  match os:
    case Nil{}:
      e => {==}
    case Con{o, rest}:
      Voter.yes.at(
        Round.hit(s, c, h, r, o, v),
        o,
        Round.voter(s, c, h, r, rest, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        Voter.yes(s, c, h, r, rest, v)
      )

# nothing is less than a number that is zero
def Lt.none(n: Nat, y: Nat, e: {y == 0n: Nat}) -> {Nat.is_lt(n, y) == True{}: Bool} -> Empty:
  k =>
    Shared.Nat.lt_zero(n)(
      %e: {Nat.is_lt(n, _) == True{}: Bool}
      k)

# a step with a majority has a voter
def Has.voter(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Round.voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>} -> Empty:
  hh => e =>
    Lt.none(
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Voter.yes(s, c, h, r, os, v)(e)
    )(hh)

# Sub.count for a first owner o and a first node f, once it is known whether
# they are the same (b)
def Sub.count.at(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  o: String,
  rest: List<&2, String>,
  +f: String,
  +fs: List<&2, String>,
  +v: Ledgers.Vote,
  b: Bool,
  eb: {String.eq(f, o) == b: Bool},
  ih1: {
    Replicas.Owners.sub(rest, fs) == True{}: Bool
  } -> {
    Round.voter(s, c, h, r, fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
      == True{}: Bool
  },
  ih2: {
    Replicas.Owners.sub(rest, f <> fs) == True{}: Bool
  } -> {
    Round.voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      1n+List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
      == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Bool,
    b,
    u => Replicas.Owners.sub(rest, fs),
    u => Replicas.Owners.sub(rest, f <> fs)
  )
    == True{}: Bool
} -> {
  Round.voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    1n+List.length(&2, String, fs),
    Shared.Nat.add_if(
      Bool.not(Round.hit(s, c, h, r, o, v)),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      es => +ev =>
        %Texts.String.eq_sound(
          f,
          o
        )(
          eb
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(Round.hit(s, c, h, r, _, v)),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        %Equal.sym(
          Bool,
          Round.hit(s, c, h, r, f, v),
          False{},
          Voter.if_hit(Round.hit(s, c, h, r, f, v), f, Round.voter(s, c, h, r, fs, v))(ev)
        ): {
          Nat.is_le(
            1n+List.length(&2, String, fs),
            Shared.Nat.add_if(
              Bool.not(_),
              Quorums.Quorum.no(
                ~Ledgers.Vote,
                ~Ledgers.Vote.is_eq,
                Round.ballots(s, c, h, r, rest),
                v
              )
            )
          )
            == True{}: Bool
        }
        ih1(es)(Voter.if_rest(Round.hit(s, c, h, r, f, v), f, Round.voter(s, c, h, r, fs, v))(ev))
    case False{}:
      es => ev =>
        Shared.Nat.le_add_if(
          Bool.not(Round.hit(s, c, h, r, o, v)),
          1n+List.length(&2, String, fs),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
        )(ih2(es)(ev))

# nodes that are some of the owners, none of which cast for the step v, are
# at most the ballots that are not for v
def Sub.count(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Replicas.Owners.sub(os, from) == True{}: Bool
} -> {
  Round.voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    List.length(&2, String, from),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
  )
    == True{}: Bool
}:
  match os from:
    case Nil{} Nil{}:
      es => ev => {==}
    case Nil{} Con{f, fs}:
      es => ev => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.false_ne_true(es))
    case Con{o, rest} Nil{}:
      es => ev => Shared.Nat.le_zero(
        Quorums.Quorum.no(
          ~Ledgers.Vote,
          ~Ledgers.Vote.is_eq,
          Round.ballots(s, c, h, r, o <> rest),
          v
        )
      )
    case Con{+o, +rest} Con{+f, +fs}:
      Sub.count.at(
        s,
        c,
        h,
        r,
        o,
        rest,
        f,
        fs,
        v,
        String.eq(f, o),
        {==},
        Sub.count(s, c, h, r, rest, fs, v),
        Sub.count(s, c, h, r, rest, f <> fs, v)
      )

# Count.total once the hit of the first node is known
def Count.total.at(
  hit: Bool,
  y: Nat,
  n: Nat,
  l: Nat,
  ih: {Nat.add(y, n) == l: Nat}
) -> {Nat.add(Shared.Nat.add_if(hit, y), Shared.Nat.add_if(Bool.not(hit), n)) == 1n+l: Nat}:
  match hit:
    case True{}:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
    case False{}:
      Equal.trans(
        Nat,
        Nat.add(y, 1n+n),
        1n+Nat.add(y, n),
        1n+l,
        Shared.Nat.add_succ(y, n),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(y, n), l, ih)
      )

# each owner's ballot is for the step v, or is not
def Count.total(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Nat.add(
    Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
    Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
  )
    == List.length(&2, String, os): Nat
}:
  match os:
    case Nil{}:
      {==}
    case Con{o, +rest}:
      Count.total.at(
        Round.hit(s, c, h, r, o, v),
        Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v),
        List.length(&2, String, rest),
        Count.total(s, c, h, r, rest, v)
      )

# a number is at most a number equal to it
def Le.same(a: Nat, b: Nat, e: {a == b: Nat}) -> {Nat.is_le(a, b) == True{}: Bool}:
  %e: {Nat.is_le(a, _) == True{}: Bool}
  Shared.Nat.le_refl(a)

# two majorities share a node: nodes that are a majority of the owners, none
# of which cast for the step v, leave v no majority
def Major.meets(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r, os),
    v
  )
    == True{}: Bool
} -> {Replicas.Owners.sub(os, from) == True{}: Bool}
  -> {Replicas.Owners.major(os, from) == True{}: Bool}
  -> {Round.voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>}
  -> Empty:
  hh => es => em => ev =>
    Shared.Nat.pigeon(
      List.length(&2, String, from),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      List.length(&2, String, os)
    )(
      Sub.count(s, c, h, r, os, from, v)(es)(ev)
    )(
      hh
    )(
      Le.same(
        Nat.add(
          Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v)
        ),
        List.length(&2, String, os),
        Count.total(s, c, h, r, os, v)
      )
    )(em)

# the round of a last vote, 0 without one
def Last.round(m: Maybe<&2, Ledgers.Last>) -> Nat:
  match m:
    case Some{Ledgers.Last{r, v}}:
      r
    case None{}:
      0n

# the step of a last vote, d without one
def Last.step(d: Ledgers.Vote, m: Maybe<&2, Ledgers.Last>) -> Ledgers.Vote:
  match m:
    case Some{Ledgers.Last{r, v}}:
      v
    case None{}:
      d

# the last vote m is of the round r1 or of a later one
def Last.from(m: Maybe<&2, Ledgers.Last>, r1: Nat) -> Bool:
  match m:
    case Some{Ledgers.Last{r, v}}:
      Nat.is_le(r1, r)
    case None{}:
      False{}

# Mine.le for one round
def Mine.le.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Nat.is_le(r, k) == True{}: Bool}
) -> {
  Replicas.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, k) == True{}: Bool}:
  match m:
    case Some{y}:
      e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Nat.is_le(_, k) == True{}: Bool}
        Shared.Nat.le_refl(k)
    case None{}:
      e => ih(e)

# the last vote of a node up to the round p is of a round up to p
def Mine.le(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, p) == True{}: Bool}:
  match p:
    case 0n:
      Mine.le.or(
        0n,
        Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 0n}, q),
        None{},
        r,
        x,
        e => Empty.absurd(
          {Nat.is_le(r, 0n) == True{}: Bool},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.le.or(
        1n+j,
        Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 1n+j}, q),
        Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, j),
        r,
        x,
        e => Shared.Nat.le_succ(r, j)(Mine.le(s, c, h, q, j, r, x)(e))
      )

# Mine.cast for one round
def Mine.cast.or(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  em: {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q) == m: Maybe<&2, Ledgers.Vote>},
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
) -> {
  Replicas.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case Some{y}:
      +e =>
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Nat,
          Last.round,
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, _}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Ledgers.Vote,
          Last.step(y),
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q) == Some{_}: Maybe<&2, Ledgers.Vote>}
        em
    case None{}:
      e => ih(e)

# the last vote of a node is a vote that it cast
def Mine.cast(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match p:
    case 0n:
      Mine.cast.or(
        s,
        c,
        h,
        q,
        0n,
        Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 0n}, q),
        {==},
        None{},
        r,
        x,
        e => Empty.absurd(
          {Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>},
          Shared.Maybe.none_ne_some(Ledgers.Last, Ledgers.Last{r, x}, e)
        )
      )
    case 1n+(+j):
      Mine.cast.or(
        s,
        c,
        h,
        q,
        1n+j,
        Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 1n+j}, q),
        {==},
        Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, j),
        r,
        x,
        Mine.cast(s, c, h, q, j, r, x)
      )

# Cast.apart once it is known whether the rounds are the same (b)
def Cast.apart.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote,
  b: Bool,
  eb: {Nat.is_eq(r1, k) == b: Bool}
) -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {b == False{}: Bool}:
  match b:
    case True{}:
      e1 => en => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          Ledgers.Vote,
          v1,
          Equal.trans(
            Maybe<&2, Ledgers.Vote>,
            None{},
            Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q),
            Some{v1},
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q),
              None{},
              en
            ),
            Cast.moved(s, c, h, q, r1, k, v1, Shared.Nat.is_eq_sound(r1, k)(eb))(e1)
          )
        )
      )
    case False{}:
      e1 => en => {==}

# a round with a vote of a node is not a round without one
def Cast.apart(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote
) -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
} -> {Nat.is_eq(r1, k) == False{}: Bool}:
  e1 => en => Cast.apart.at(s, c, h, q, r1, k, v1, Nat.is_eq(r1, k), {==})(e1)(en)

# Mine.from for one round
def Mine.from.or(
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rest: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Nat.is_le(r1, k) == True{}: Bool
} -> (
  {m == None{}: Maybe<&2, Ledgers.Vote>} -> {Last.from(rest, r1) == True{}: Bool}
) -> {Last.from(Replicas.Last.or(k, m, u => rest), r1) == True{}: Bool}:
  match m:
    case Some{y}:
      hk => ih => hk
    case None{}:
      hk => ih => ih({==})

# a node that cast in the round r1 has a last vote of r1 or later, up to any
# round from r1 on
def Mine.from(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Nat.is_le(r1, p) == True{}: Bool
} -> {Last.from(Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, p), r1) == True{}: Bool}:
  match p:
    case 0n:
      +e1 => +le =>
        Mine.from.or(
          0n,
          Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 0n}, q),
          None{},
          r1
        )(
          le
        )(
          en => Empty.absurd(
            {False{} == True{}: Bool},
            Shared.Maybe.none_ne_some(
              Ledgers.Vote,
              v1,
              Equal.trans(
                Maybe<&2, Ledgers.Vote>,
                None{},
                Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 0n}, q),
                Some{v1},
                Equal.sym(
                  Maybe<&2, Ledgers.Vote>,
                  Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 0n}, q),
                  None{},
                  en
                ),
                Cast.moved(s, c, h, q, r1, 0n, v1, Shared.Nat.le_zero_eq(r1)(le))(e1)
              )
            )
          )
        )
    case 1n+(+j):
      +e1 => +le =>
        Mine.from.or(
          1n+j,
          Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, 1n+j}, q),
          Replicas.Last.mine(~Basics.Ask.machine(), q, s, c, h, j),
          r1
        )(
          le
        )(
          en => Mine.from(
            s,
            c,
            h,
            q,
            j,
            r1,
            v1
          )(e1)(Shared.Nat.le_step(r1, j)(le)(Cast.apart(s, c, h, q, r1, 1n+j, v1)(e1)(en)))
        )

# Newer.left once it is known whether the round of a is less than that of b
def Newer.left.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, ra) == False{}: Bool}:
  match b:
    case True{}:
      e => Shared.Nat.nle_trans(r1, ra, rb)(e)(Shared.Nat.lt_weak(ra, rb)(eb))
    case False{}:
      e => e

# when the newer of two last votes is before the round r1, so is the first
def Newer.left(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Last.from(Replicas.Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(a, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => {==}
    case Some{x} None{}:
      e => e
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.left.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# Newer.right once it is known whether the round of a is less than that of b
def Newer.right.at(
  +ra: Nat,
  va: Ledgers.Vote,
  +rb: Nat,
  vb: Ledgers.Vote,
  r1: Nat,
  b: Bool,
  eb: {Nat.is_lt(ra, rb) == b: Bool}
) -> {
  Last.from(
    Shared.Bool.when(
      Maybe<&2, Ledgers.Last>,
      b,
      u => Some{Ledgers.Last{rb, vb}},
      u => Some{Ledgers.Last{ra, va}}
    ),
    r1
  )
    == False{}: Bool
} -> {Nat.is_le(r1, rb) == False{}: Bool}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Shared.Nat.nle_trans(r1, rb, ra)(e)(Shared.Nat.nlt_le(ra, rb)(eb))

# when the newer of two last votes is before the round r1, so is the second
def Newer.right(
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  r1: Nat
) -> {
  Last.from(Replicas.Last.newer(a, b), r1) == False{}: Bool
} -> {Last.from(b, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => e
    case Some{x} None{}:
      e => {==}
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.right.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# the rule that the passes that a vote names allow it, at the head hd whose tip is tp
def Rules.allow(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Replicas.Rounds.Allow(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd), Replicas.Tip.owners(tp)):
  Shared.Pair.first(
    Replicas.Rounds.Allow(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd), Replicas.Tip.owners(tp)),
    Replicas.Rounds.Last(~Basics.Ask.machine(), 
      s,
      c,
      Replicas.Head.next(hd)
    )
      & Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
    rules(hd)(tp)(ok)
  )

# the rule that a pass names the last vote of its node below its round, at the head hd whose tip is tp
def Rules.last(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Replicas.Rounds.Last(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)):
  Shared.Pair.first(
    Replicas.Rounds.Last(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
    Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
    Shared.Pair.second(
      Replicas.Rounds.Allow(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd), Replicas.Tip.owners(tp)),
      Replicas.Rounds.Last(~Basics.Ask.machine(), 
        s,
        c,
        Replicas.Head.next(hd)
      )
        & Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# the rule that the votes of one round are for one step, at the head hd whose tip is tp
def Rules.same(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>}
) -> Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)):
  Shared.Pair.second(
    Replicas.Rounds.Last(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
    Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
    Shared.Pair.second(
      Replicas.Rounds.Allow(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd), Replicas.Tip.owners(tp)),
      Replicas.Rounds.Last(~Basics.Ask.machine(), 
        s,
        c,
        Replicas.Head.next(hd)
      )
        & Replicas.Rounds.Same(~Basics.Ask.machine(), s, c, Replicas.Head.next(hd)),
      rules(hd)(tp)(ok)
    )
  )

# Pass.miss for a first node o, once its hit in the round r1 (hit) and its
# pass (m) are known
def Pass.miss.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  +o: String,
  rest: Maybe<&2, String>,
  hit: Bool,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> {Round.hit(s, c, Replicas.Head.next(hd), r1, o, v1) == hit: Bool}
  -> {
    Ledgers.State.passed(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
      o
    )
      == m: Maybe<&2, Maybe<&2, Ledgers.Last>>
  }
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, m) == True{}: Bool}
  -> {Last.from(Replicas.Passed.last(m), r1) == False{}: Bool}
  -> {rest == None{}: Maybe<&2, String>}
  -> {Voter.if(hit, o, rest) == None{}: Maybe<&2, String>}:
  match hit m:
    case False{} y:
      eh => em => le => es => ef => ih => ih
    case True{} None{}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(es)
      )
    case True{} Some{l}:
      eh => em => le => es => ef => ih => Empty.absurd(
        {Some{o} == None{}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(Equal.trans(
            Bool,
            False{},
            Last.from(l, r1),
            True{},
            Equal.sym(Bool, Last.from(l, r1), False{}, ef),
            %Equal.sym(Maybe<&2, Ledgers.Last>, l, Replicas.Last.mine(~Basics.Ask.machine(), o, s, c, Replicas.Head.next(hd), p), Rules.last(~s, ~c, ~rules, hd, tp, ok)(1n+p)(o)(l)(em)): {Last.from(_, r1) == True{}: Bool}
            Mine.from(s, c, Replicas.Head.next(hd), o, p, r1, v1)(Hit.cast(s, c, Replicas.Head.next(hd), r1, o, v1)(eh))(le)))
      )

# when the passes of the nodes from to the round 1 + p name no vote of the
# round r1 or later, none of them cast in r1
def Pass.miss(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  from: List<&2, String>
) -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from) == True{}: Bool}
  -> {
    Last.from(
      Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
      r1
    )
      == False{}: Bool
  }
  -> {Round.voter(s, c, Replicas.Head.next(hd), r1, from, v1) == None{}: Maybe<&2, String>}:
  match from:
    case Nil{}:
      le => ea => ef => {==}
    case Con{+o, +rest}:
      +le => +ea => +ef =>
        Pass.miss.at(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          p,
          r1,
          v1,
          o,
          Round.voter(s, c, Replicas.Head.next(hd), r1, rest, v1),
          Round.hit(s, c, Replicas.Head.next(hd), r1, o, v1),
          Ledgers.State.passed(
            ~Basics.Ask,
            Replicas.State.ledger(~Basics.Ask.machine(), s),
            Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
            o
          )
        )(
          {==}
        )(
          {==}
        )(
          le
        )(
          Shared.List.all.if_hit(
            Maybe.is_some(
              &2,
              Maybe<&2, Ledgers.Last>,
              Ledgers.State.passed(
                ~Basics.Ask,
                Replicas.State.ledger(~Basics.Ask.machine(), s),
                Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
                o
              )
            ),
            u => Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, rest)
          )(ea)
        )(
          Newer.left(
            Replicas.Passed.last(
              Ledgers.State.passed(
                ~Basics.Ask,
                Replicas.State.ledger(~Basics.Ask.machine(), s),
                Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
                o
              )
            ),
            Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, rest),
            r1
          )(ef)
        )(
          Pass.miss(
            ~s,
            ~c,
            ~rules,
            hd,
            tp,
            ok,
            p,
            r1,
            v1,
            rest
          )(
            le
          )(
            Shared.List.all.if_rest(
              Maybe.is_some(
                &2,
                Maybe<&2, Ledgers.Last>,
                Ledgers.State.passed(
                  ~Basics.Ask,
                  Replicas.State.ledger(~Basics.Ask.machine(), s),
                  Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
                  o
                )
              ),
              u => Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, rest)
            )(ea)
          )(
            Newer.right(
              Replicas.Passed.last(
                Ledgers.State.passed(
                  ~Basics.Ask,
                  Replicas.State.ledger(~Basics.Ask.machine(), s),
                  Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
                  o
                )
              ),
              Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, rest),
              r1
            )(ef)
          )
        )

# the case of a choice by b
def When.elim(
  -R: Type,
  x: Bool,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>,
  l: Ledgers.Last
) -> {
  Shared.Bool.when(Maybe<&2, Ledgers.Last>, x, u => b, u => a) == Some{l}: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> R
) -> ({a == Some{l}: Maybe<&2, Ledgers.Last>} -> R) -> R:
  match x:
    case True{}:
      e => f => g => f(e)
    case False{}:
      e => f => g => g(e)

# that the pass of some node to the place w names the last vote l
def Named(-R: Type, s: Replicas.Node<Basics.Ask>, w: Ledgers.Where, l: Ledgers.Last) -> Type:
  (
    @q: String -> {
      Replicas.Passed.last(
        Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, q)
      )
        == Some{l}: Maybe<&2, Ledgers.Last>
    } -> R
  ) -> R

# Last.elim for a first node o, once what it named (a) and what the rest
# named (b) are known
def Last.elim.at(
  -R: Type,
  s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  o: String,
  l: Ledgers.Last,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {
  Replicas.Passed.last(
    Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)
  )
    == a: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l)
) -> {Replicas.Last.newer(a, b) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
  match a b:
    case None{} y:
      ea => ih => e => ih(e)
    case Some{x} None{}:
      ea => ih => e => k => k(
        o
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          Replicas.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
          Some{x},
          Some{l},
          ea,
          e
        )
      )
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      ea => ih => e =>
        When.elim(
          Named(R, s, w, l),
          Nat.is_lt(ra, rb),
          Some{Ledgers.Last{ra, va}},
          Some{Ledgers.Last{rb, vb}},
          l
        )(
          e
        )(
          ih
        )(
          e2 => k => k(
            o
          )(
            Equal.trans(
              Maybe<&2, Ledgers.Last>,
              Replicas.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
              Some{Ledgers.Last{ra, va}},
              Some{l},
              ea,
              e2
            )
          )
        )

# the last vote of the highest round that passes name is named by one of them
def Last.elim(
  -R: Type,
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  from: List<&2, String>,
  +l: Ledgers.Last
) -> {Replicas.Passes.last(~Basics.Ask.machine(), s, w, from) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
  match from:
    case Nil{}:
      e => k => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Last, l, e))
    case Con{+o, +rest}:
      Last.elim.at(
        R,
        s,
        w,
        o,
        l,
        Replicas.Passed.last(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), w, o)),
        Replicas.Passes.last(~Basics.Ask.machine(), s, w, rest)
      )({==})(Last.elim(R, s, w, rest, l))

# a pass that names a last vote is held
def Passed.some(
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  l: Ledgers.Last
) -> {
  Replicas.Passed.last(m) == Some{l}: Maybe<&2, Ledgers.Last>
} -> {m == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {None{} == Some{Some{l}}: Maybe<&2, Maybe<&2, Ledgers.Last>>},
        Shared.Maybe.none_ne_some(Ledgers.Last, l, e)
      )
    case Some{x}:
      e => Equal.cong(
        Maybe<&2, Ledgers.Last>,
        Maybe<&2, Maybe<&2, Ledgers.Last>>,
        y => Some{y},
        x,
        Some{l},
        e
      )

# the parts of the rule of a later round
def Later.all(a: Bool, b: Bool, c: Bool, d: Bool) -> Bool:
  List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => d, c), b), a)

def Later.all.a(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => e

def Later.all.b(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {b == True{}: Bool}:
  match a b:
    case True{} True{}:
      e => {==}
    case True{} False{}:
      e => e
    case False{} y:
      e => Empty.absurd({y == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.c(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {c == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => {==}
    case True{} True{} False{}:
      e => e
    case True{} False{} z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))

def Later.all.d(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {Later.all(a, b, c, d) == True{}: Bool} -> {d == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => e
    case True{} True{} False{}:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case True{} False{} z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({d == True{}: Bool}, Shared.Bool.false_ne_true(e))

# that each vote of a round from r1 on, below the round j, is for the step v1
def Rounds.Below(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: U32,
  r1: Nat,
  v1: Ledgers.Vote,
  j: Nat
) -> Type:
  @rm: Nat -> @qm: String -> @vm: Ledgers.Vote -> {
    Nat.is_lt(rm, j) == True{}: Bool
  } -> {
    Nat.is_le(r1, rm) == True{}: Bool
  } -> {
    Replicas.Cast.of(~Basics.Ask.machine(), s, Ledgers.Where{c, h, rm}, qm) == Some{vm}: Maybe<&2, Ledgers.Vote>
  } -> {vm == v1: Ledgers.Vote}

# Rounds.last once the node qw that named the last vote is known, with its
# last vote
def Rounds.named(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  j: Nat,
  +rm: Nat,
  +vm: Ledgers.Vote,
  +qw: String,
  +em: {
    Replicas.Last.mine(~Basics.Ask.machine(), 
      qw,
      s,
      c,
      Replicas.Head.next(hd),
      p
    )
      == Some{Ledgers.Last{rm, vm}}: Maybe<&2, Ledgers.Last>
  },
  lt: {Nat.is_lt(p, j) == True{}: Bool},
  le: {Nat.is_le(r1, rm) == True{}: Bool},
  ih: Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, j)
) -> {vm == v1: Ledgers.Vote}:
  ih(
    rm
  )(
    qw
  )(
    vm
  )(
    Shared.Nat.le_lt(rm, p, j)(Mine.le(s, c, Replicas.Head.next(hd), qw, p, rm, vm)(em))(lt)
  )(le)(Mine.cast(s, c, Replicas.Head.next(hd), qw, p, rm, vm)(em))

# Rounds.round once the last vote m that the passes name is known: it is of
# the round r1 or later, and the vote x is for its step
def Rounds.last(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  x: Ledgers.Vote,
  j: Nat,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {
  Replicas.Passes.last(~Basics.Ask.machine(), 
    s,
    Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
    from
  )
    == m: Maybe<&2, Ledgers.Last>
}
  -> {Last.from(m, r1) == True{}: Bool}
  -> {Replicas.Last.is(m, x) == True{}: Bool}
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => ef => ei => lt => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(ef)
      )
    case Some{Ledgers.Last{+rm, +vm}}:
      em => ef => ei => lt => ih =>
        Last.elim(
          {x == v1: Ledgers.Vote},
          s,
          Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
          from,
          Ledgers.Last{rm, vm}
        )(em)(
          +qw => ew =>
            %Ledgers.Vote.is_eq_sound(vm, x)(ei): {_ == v1: Ledgers.Vote}
            Rounds.named(~s, ~c, ~rules, hd, tp, ok, r1, v1, p, j, rm, vm, qw, Equal.sym(Maybe<&2, Ledgers.Last>, Some{Ledgers.Last{rm, vm}}, Replicas.Last.mine(~Basics.Ask.machine(), qw, s, c, Replicas.Head.next(hd), p), Rules.last(~s, ~c, ~rules, hd, tp, ok)(1n+p)(qw)(Some{Ledgers.Last{rm, vm}})(Passed.some(Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, qw), Ledgers.Last{rm, vm})(ew))), lt, ef, ih))

# Rounds.round once it is known whether the passes name a vote of the round
# r1 or later (f)
def Rounds.pick(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +p: Nat,
  +x: Ledgers.Vote,
  j: Nat,
  +from: List<&2, String>,
  f: Bool
) -> {
  Last.from(
    Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
    r1
  )
    == f: Bool
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, j)
  -> {
    Later.all(
      Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
      Replicas.Owners.sub(Replicas.Tip.owners(tp), from),
      Replicas.Owners.major(Replicas.Tip.owners(tp), from),
      Replicas.Last.is(Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from), x)
    )
      == True{}: Bool
  }
  -> {x == v1: Ledgers.Vote}:
  match f:
    case False{}:
      ef => hh => lt => le => ih => +al =>
        Empty.absurd(
          {x == v1: Ledgers.Vote},
          Major.meets(
            s,
            c,
            Replicas.Head.next(hd),
            r1,
            Replicas.Tip.owners(tp),
            from,
            v1
          )(
            hh
          )(
            Later.all.b(
              Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
              Replicas.Owners.sub(Replicas.Tip.owners(tp), from),
              Replicas.Owners.major(Replicas.Tip.owners(tp), from),
              Replicas.Last.is(
                Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Later.all.c(
              Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
              Replicas.Owners.sub(Replicas.Tip.owners(tp), from),
              Replicas.Owners.major(Replicas.Tip.owners(tp), from),
              Replicas.Last.is(
                Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
                x
              )
            )(al)
          )(
            Pass.miss(
              ~s,
              ~c,
              ~rules,
              hd,
              tp,
              ok,
              p,
              r1,
              v1,
              from
            )(
              le
            )(
              Later.all.a(
                Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
                Replicas.Owners.sub(Replicas.Tip.owners(tp), from),
                Replicas.Owners.major(Replicas.Tip.owners(tp), from),
                Replicas.Last.is(
                  Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
                  x
                )
              )(al)
            )(ef)
          )
        )
    case True{}:
      ef => hh => lt => le => ih => al =>
        Rounds.last(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          from,
          Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from)
        )(
          {==}
        )(
          ef
        )(
          Later.all.d(
            Replicas.Passed.all(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
            Replicas.Owners.sub(Replicas.Tip.owners(tp), from),
            Replicas.Owners.major(Replicas.Tip.owners(tp), from),
            Replicas.Last.is(
              Replicas.Passes.last(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, from),
              x
            )
          )(al)
        )(lt)(ih)

# Rounds.same at the round r1 itself, once a voter m of the step v1 is known
def Rounds.base(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  q: String,
  x: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(
    s,
    c,
    Replicas.Head.next(hd),
    r1,
    Replicas.Tip.owners(tp),
    v1
  )
    == m: Maybe<&2, String>
}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Replicas.Cast.of(~Basics.Ask.machine(), 
      s,
      Ledgers.Where{c, Replicas.Head.next(hd), r1},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => hh => e => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Has.voter(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp), v1)(hh)(em)
      )
    case Some{+o}:
      em => hh => e => Rules.same(
        ~s,
        ~c,
        ~rules,
        hd,
        tp,
        ok
      )(
        r1
      )(
        q
      )(
        o
      )(x)(v1)(e)(Voter.cast(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp), v1, o)(em))

# Rounds.same in a round after r1
def Rounds.step(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  v1: Ledgers.Vote,
  r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat
) -> {Nat.is_eq(r1, r) == False{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Replicas.Cast.of(~Basics.Ask.machine(), 
      s,
      Ledgers.Where{c, Replicas.Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match r:
    case 0n:
      ne => hh => lt => le => e => ih => Empty.absurd(
        {x == v1: Ledgers.Vote},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_eq(r1, 0n),
            True{},
            Equal.sym(Bool, Nat.is_eq(r1, 0n), False{}, ne),
            Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), r1, 0n, Shared.Nat.le_zero_eq(r1)(le))
          )
        )
      )
    case 1n+(+p):
      ne => hh => lt => le => e => ih =>
        Rounds.pick(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          p,
          x,
          j,
          Replicas.Cast.from(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, q),
          Last.from(
            Replicas.Passes.last(~Basics.Ask.machine(), 
              s,
              Ledgers.Where{c, Replicas.Head.next(hd), 1n+p},
              Replicas.Cast.from(~Basics.Ask.machine(), s, Ledgers.Where{c, Replicas.Head.next(hd), 1n+p}, q)
            ),
            r1
          )
        )(
          {==}
        )(
          hh
        )(
          lt
        )(
          Shared.Nat.le_step(r1, p)(le)(ne)
        )(ih)(Rules.allow(~s, ~c, ~rules, hd, tp, ok)(1n+p)(q)(x)(e))

# Rounds.same once it is known whether the round is r1 (b)
def Rounds.same.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +v1: Ledgers.Vote,
  +r: Nat,
  +q: String,
  +x: Ledgers.Vote,
  j: Nat,
  b: Bool
) -> {Nat.is_eq(r1, r) == b: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {
    Replicas.Cast.of(~Basics.Ask.machine(), 
      s,
      Ledgers.Where{c, Replicas.Head.next(hd), r},
      q
    )
      == Some{x}: Maybe<&2, Ledgers.Vote>
  }
  -> Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match b:
    case True{}:
      eb => hh => lt => le => e => ih =>
        Rounds.base(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          q,
          x,
          Round.voter(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp), v1)
        )(
          {==}
        )(
          hh
        )(
          Cast.moved(
            s,
            c,
            Replicas.Head.next(hd),
            q,
            r,
            r1,
            x,
            Equal.sym(Nat, r1, r, Shared.Nat.is_eq_sound(r1, r)(eb))
          )(e)
        )
    case False{}:
      eb => hh => lt => le => e => ih =>
        Rounds.step(~s, ~c, ~rules, hd, tp, ok, r1, v1, r, q, x, j)(eb)(hh)(lt)(le)(e)(ih)

# each vote of a round from r1 on, below the round k, is for the step that a
# majority cast in r1
def Rounds.same(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  +ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
    v1
  )
    == True{}: Bool
} -> Rounds.Below(s, c, Replicas.Head.next(hd), r1, v1, k):
  match k:
    case 0n:
      hh => rm => qm => vm => lt => le => e => Empty.absurd(
        {vm == v1: Ledgers.Vote},
        Shared.Nat.lt_zero(rm)(lt)
      )
    case 1n+(+j):
      +hh => +rm => qm => vm => lt => le => e =>
        Rounds.same.at(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r1,
          v1,
          rm,
          qm,
          vm,
          j,
          Nat.is_eq(r1, rm)
        )({==})(hh)(lt)(le)(e)(Rounds.same(~s, ~c, ~rules, hd, tp, ok, j, r1, v1)(hh))

# Rounds.later once a voter m of the step v2 in the round r2 is known
def Rounds.later.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {
  Round.voter(
    s,
    c,
    Replicas.Head.next(hd),
    r2,
    Replicas.Tip.owners(tp),
    v2
  )
    == m: Maybe<&2, String>
}
  -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
      v1
    )
      == True{}: Bool
  }
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, Replicas.Head.next(hd), r2, Replicas.Tip.owners(tp)),
      v2
    )
      == True{}: Bool
  }
  -> {v2 == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => le => h1 => h2 => Empty.absurd(
        {v2 == v1: Ledgers.Vote},
        Has.voter(s, c, Replicas.Head.next(hd), r2, Replicas.Tip.owners(tp), v2)(h2)(em)
      )
    case Some{+o}:
      em => le => h1 => h2 =>
        Rounds.same(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          1n+r2,
          r1,
          v1
        )(
          h1
        )(
          r2
        )(
          o
        )(
          v2
        )(
          Shared.Nat.lt_succ(r2)
        )(le)(Voter.cast(s, c, Replicas.Head.next(hd), r2, Replicas.Tip.owners(tp), v2, o)(em))

# a round decides what an earlier round of its height decided
def Rounds.later(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  +hd: Replicas.Head,
  +tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +r2: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote
) -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(hd), r1},
      Replicas.Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(hd), r2},
      Replicas.Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v2 == v1: Ledgers.Vote}:
  le => d1 => d2 =>
    Rounds.later.at(
      ~s,
      ~c,
      ~rules,
      hd,
      tp,
      ok,
      r1,
      r2,
      v1,
      v2,
      Round.voter(s, c, Replicas.Head.next(hd), r2, Replicas.Tip.owners(tp), v2)
    )(
      {==}
    )(
      le
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, Replicas.Head.next(hd), r1, Replicas.Tip.owners(tp)),
        v1
      )(d1)
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, Replicas.Head.next(hd), r2, Replicas.Tip.owners(tp)),
        v2
      )(d2)
    )

# Rounds.one once it is known whether r1 is at most r2 (b)
def Rounds.one.at(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  hd: Replicas.Head,
  tp: Replicas.Tip,
  ok: {Replicas.Head.tip(~Basics.Ask.machine(), s, hd) == Some{tp}: Maybe<&2, Replicas.Tip>},
  +r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  v2: Ledgers.Vote,
  b: Bool
) -> {Nat.is_le(r1, r2) == b: Bool}
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(hd), r1},
      Replicas.Tip.owners(tp)
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Ledgers.Where{c, Replicas.Head.next(hd), r2},
      Replicas.Tip.owners(tp)
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v1 == v2: Ledgers.Vote}:
  match b:
    case True{}:
      eb => d1 => d2 => Equal.sym(
        Ledgers.Vote,
        v2,
        v1,
        Rounds.later(~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2)(eb)(d1)(d2)
      )
    case False{}:
      eb => d1 => d2 =>
        Rounds.later(
          ~s,
          ~c,
          ~rules,
          hd,
          tp,
          ok,
          r2,
          r1,
          v2,
          v1
        )(Shared.Nat.nle_le(r1, r2)(eb))(d2)(d1)

# the rounds of a height decide one step, when the ballots follow the rules
# of rounds: a later round can only decide what an earlier round decided
def Rounds.one(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c)
) -> Line.One(s, c):
  +hd => +tp => +ok => +r1 => +r2 => v1 => v2 => d1 => d2 =>
    Rounds.one.at(~s, ~c, ~rules, hd, tp, ok, r1, r2, v1, v2, Nat.is_le(r1, r2))({==})(d1)(d2)

# the rounds of each of k heights decide one step, when the ballots follow the
# rules of rounds
def Rounds.ones(
  ~s: Replicas.Node<Basics.Ask>,
  ~c: Ledgers.Chain,
  ~rules: Replicas.Rounds.Rules(~Basics.Ask.machine(), s, c),
  k: Nat
) -> Line.Ones(k, s, c):
  match k:
    case 0n:
      Unit{}
    case 1n+p:
      (Rounds.ones(~s, ~c, ~rules, p), Rounds.one(~s, ~c, ~rules))

def Spec.Line.at_agrees(u, c, rules, rs1, rs2, a, b, h, x, y):
  ga => gb => el => ea => eb =>
    At.same(
      rs1,
      rs2,
      u,
      c,
      h,
      x,
      y
    )(
      Rounds.ones(~u, ~c, ~rules, List.length(&2, Nat, rs1))
    )(
      el
    )(
      Spec.Line.at_grows(rs1, a, u, c, h, x)(ga)(ea)
    )(Spec.Line.at_grows(rs2, b, u, c, h, y)(gb)(eb))

def Spec.Cast.put_keeps(n, w, th, qs, from, s2, t2, s, s3):
  +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Replicas.Node<Basics.Ask>>,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      Some{s3},
      e
    ): {Replicas.Node.grows(~Basics.Ask.machine(), s2, Replicas.Cast.vote(~Stepping.Ask.kernel(), s, _, w, n, a0)) == True{}: Bool}
    Grows.trans(
      s2,
      s4,
      Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
    )(
      Grows.to(
        s2,
        s3,
        s4,
        Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
        Put.grew(s2, [Replicas.Tip.words(t2)], s3, e)
      )
    )(Cast.seal.grows(s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)))

def Spec.Cast.put_tip(n, w, th, qs, from, s2, t2, s, s3):
  +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Replicas.Node<Basics.Ask>>,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      Some{s3},
      e
    ): {
      Replicas.Tip.at(~Basics.Ask.machine(), 
        Replicas.Cast.vote(~Stepping.Ask.kernel(), s, _, w, n, a0),
        Replicas.Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Replicas.Tip>
    }
    Tip.at.grows(
      s3,
      Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)),
      Replicas.Tip.hash(t2),
      t2,
      Grows.trans(
        s3,
        s4,
        Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
      )(
        Grows.to(
          s3,
          s3,
          s4,
          Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
          Grows.refl(s3)
        )
      )(Cast.seal.grows(s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)))
    )(Tip.put.at(s2, t2, s3)(e))

# lines with the same key have the same key
def Key.same(
  c2: Ledgers.Chain,
  c: Ledgers.Chain
) -> {
  Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool
} -> {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}:
  Shared.List.is_eq_sound(
    ~Bool,
    ~Shared.Bool.is_eq,
    ~Shared.Bool.laws(),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c)
  )

def Spec.Node.affects_used(s, b):
  +g = Reading.Seen.of(s, b)
  Shared.List.keep_holds(
    ~Reading.Touch,
    ~Reading.Seen,
    ~Reading.Touch.holds,
    Reading.Affects.cands(s, b, g),
    g
  )

# Finality
# --------
# What a node knows of a line stays, whatever the node does next.

# an outcome that a line holds, it holds in a node that keeps its logs
def Chain.out.kept(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  -o: Replicas.Out,
  hk: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Replicas.Chain.out(~Basics.Ask.machine(), a, c, i) == Some{o}: Maybe<&2, Replicas.Out>
} -> {Replicas.Chain.out(~Basics.Ask.machine(), b, c, i) == Some{o}: Maybe<&2, Replicas.Out>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Replicas.Out,
    Replicas.Line.get(~Basics.Ask.machine(), a, c, Replicas.Log.out(i)),
    Replicas.Line.get(~Basics.Ask.machine(), b, c, Replicas.Log.out(i)),
    ws => Replicas.Out.read(ws),
    ws => Replicas.Out.read(ws),
    o,
    w => hk(c)(Replicas.Log.out(i))(w),
    w => e => e
  )

# the version of a number that a line holds, it holds in a node that keeps
# its logs
def Chain.version.kept(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +n: U32,
  -x: Replicas.Version,
  hk: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Replicas.Chain.version(~Basics.Ask.machine(), a, c, n) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Replicas.Chain.version(~Basics.Ask.machine(), b, c, n) == Some{x}: Maybe<&2, Replicas.Version>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Replicas.Version,
    Replicas.Line.get(~Basics.Ask.machine(), a, c, Replicas.Log.version(n)),
    Replicas.Line.get(~Basics.Ask.machine(), b, c, Replicas.Log.version(n)),
    ws => Replicas.Version.read(ws),
    ws => Replicas.Version.read(ws),
    x,
    w => hk(c)(Replicas.Log.version(n))(w),
    w => e => e
  )

# a mark that a line holds, it holds in a node that keeps its logs
def Chain.mark.kept(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +m: String,
  -v: Ledgers.Id,
  hk: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Replicas.Chain.mark(~Basics.Ask.machine(), a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Replicas.Chain.mark(~Basics.Ask.machine(), b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Ledgers.Id,
    Replicas.Line.get(~Basics.Ask.machine(), a, c, Replicas.Log.mark(m)),
    Replicas.Line.get(~Basics.Ask.machine(), b, c, Replicas.Log.mark(m)),
    ws => Replicas.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    ws => Replicas.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    v,
    w => hk(c)(Replicas.Log.mark(m))(w),
    w => e => e
  )

# the line of a request that a node holds, a node that grew holds
def Chain.of.kept(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  -c: Ledgers.Chain,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool}
) -> {
  Replicas.Node.chain_of(~Basics.Ask.machine(), a, i) == Some{c}: Maybe<&2, Ledgers.Chain>
} -> {Replicas.Node.chain_of(~Basics.Ask.machine(), b, i) == Some{c}: Maybe<&2, Ledgers.Chain>}:
  Shared.Maybe.bind_kept(
    Ledgers.Asked<Basics.Ask>,
    Ledgers.Chain,
    Replicas.Node.asked(~Basics.Ask.machine(), a, i),
    Replicas.Node.asked(~Basics.Ask.machine(), b, i),
    x => Some{Basics.Ask.chain(i, Replicas.Asked.ask(~Basics.Ask.machine(), x))},
    x => Some{Basics.Ask.chain(i, Replicas.Asked.ask(~Basics.Ask.machine(), x))},
    c,
    x => Ledgers.State.read_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      ~Ledgers.Asked<Basics.Ask>,
      m => Ledgers.Asked.of(~Basics.Ask, m),
      {==},
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Replicas.State.ledger(~Basics.Ask.machine(), b),
      Ledgers.Slot.ask(i),
      x
    )(g),
    x => e => e
  )

# an outcome that a node knows, a node that grew and keeps its logs knows
def Out.kept(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  -o: Replicas.Out,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  hk: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Basics.Node.out(a, i) == Some{o}: Maybe<&2, Replicas.Out>
} -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Replicas.Out>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Replicas.Out,
    Replicas.Node.chain_of(~Basics.Ask.machine(), a, i),
    Replicas.Node.chain_of(~Basics.Ask.machine(), b, i),
    c => Replicas.Chain.out(~Basics.Ask.machine(), a, c, i),
    c => Replicas.Chain.out(~Basics.Ask.machine(), b, c, i),
    o,
    c => Chain.of.kept(a, b, i, c, g),
    +c => Chain.out.kept(a, b, c, i, o, hk)
  )

# the version of an outcome, in a node that keeps the logs
def Out.on.kept(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  o: Replicas.Out,
  -x: Replicas.Version,
  hk: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Basics.Out.on(a, c, o) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Basics.Out.on(b, c, o) == Some{x}: Maybe<&2, Replicas.Version>}:
  match o:
    case Replicas.Out.Stale{}:
      e => e
    case Replicas.Out.Taken{n}:
      Chain.version.kept(a, b, c, n, x, hk)

# the version that a request made on a line, in a node that keeps the logs
def Chain.made.kept(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  -x: Replicas.Version,
  hk1: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b),
  hk2: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Basics.Chain.made(a, c, v) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Basics.Chain.made(b, c, v) == Some{x}: Maybe<&2, Replicas.Version>}:
  Shared.Maybe.bind_kept(
    Replicas.Out,
    Replicas.Version,
    Replicas.Chain.out(~Basics.Ask.machine(), a, c, v),
    Replicas.Chain.out(~Basics.Ask.machine(), b, c, v),
    o => Basics.Out.on(a, c, o),
    o => Basics.Out.on(b, c, o),
    x,
    o => Chain.out.kept(a, b, c, v, o, hk1),
    o => Out.on.kept(a, b, c, o, x, hk2)
  )

# the version that a request made, in a node that grew and keeps the logs
def Made.kept(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +v: Ledgers.Id,
  -x: Replicas.Version,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  hk1: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b),
  hk2: Replicas.Node.Keeps(~Basics.Ask.machine(), a, b)
) -> {
  Basics.Node.made(a, v) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Basics.Node.made(b, v) == Some{x}: Maybe<&2, Replicas.Version>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Replicas.Version,
    Replicas.Node.chain_of(~Basics.Ask.machine(), a, v),
    Replicas.Node.chain_of(~Basics.Ask.machine(), b, v),
    +c => Basics.Chain.made(a, c, v),
    +c => Basics.Chain.made(b, c, v),
    x,
    c => Chain.of.kept(a, b, v, c, g),
    +c => Chain.made.kept(a, b, c, v, x, hk1, hk2)
  )

def Spec.Node.out_final(n, evs, s, i, o):
  Out.kept(
    s,
    Spec.Node.after(n, evs, s),
    i,
    o,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Node.made_final(n, evs, s, v, x):
  Made.kept(
    s,
    Spec.Node.after(n, evs, s),
    v,
    x,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Chain.version_final(n, evs, s, c, k, x):
  Chain.version.kept(s, Spec.Node.after(n, evs, s), c, k, x, Spec.Node.after_keeps(n, evs, s))

def Spec.Chain.mark_final(n, evs, s, c, m, v):
  Chain.mark.kept(s, Spec.Node.after(n, evs, s), c, m, v, Spec.Node.after_keeps(n, evs, s))

def Spec.Chain.start_final(n, evs, s, r, b, v):
  Spec.Node.after_keeps(n, evs, s)(Ledgers.Chain{r, None{}})(Replicas.Log.start(b))(v)

# the answer b may come after the answer a, if there is an a
def Follows.opt(ma: Maybe<&2, Reading.Answer>, mb: Maybe<&2, Reading.Answer>) -> Bool:
  match ma:
    case None{}:
      True{}
    case Some{x}:
      Reading.Answer.follows(x, mb)

# Written or Conflicted may come after Written or Conflicted
def Left.follows(
  ba: Bool,
  bb: Bool,
  i: Ledgers.Id,
  k: Ledgers.Id
) -> {
  Reading.Answer.follows(
    Shared.Bool.when(
      Reading.Answer,
      ba,
      u => Reading.Answer.Written{i},
      u => Reading.Answer.Conflicted{k}
    ),
    Some{
      Shared.Bool.when(
        Reading.Answer,
        bb,
        u => Reading.Answer.Written{i},
        u => Reading.Answer.Conflicted{k}
      )
    }
  )
    == True{}: Bool
}:
  match ba bb:
    case True{} True{}:
      Ledgers.Id.is_eq_refl(i)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Ledgers.Id.is_eq_refl(k)

# the answer to a taken change may come after the answer to it
def Taken.follows(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> {
  Reading.Answer.follows(
    Reading.Answer.taken(a, i, q),
    Some{Reading.Answer.taken(b, i, q)}
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Branch{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Group{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Own{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Write{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Resolve{+k, y, z}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(a, k)),
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(b, k)),
        i,
        k
      )
    case Basics.Ask.On{st, l, Basics.Change.Merge{f}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(a, i)),
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(b, i)),
        i,
        i
      )
    case Basics.Ask.On{st, l, Basics.Change.Move{x}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Mark{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Key{x, y}}:
      Ledgers.Id.is_eq_refl(i)

# Asked.follows once the outcome oa of the request is known
def Of.follows(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  q: Basics.Ask,
  oa: Maybe<&2, Replicas.Out>
) -> {
  Basics.Node.out(a, i) == oa: Maybe<&2, Replicas.Out>
} -> (
  @o: Replicas.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Reading.Answer.follows(
    Reading.Answer.of(a, i, q, Basics.Node.out(a, i)),
    Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Basics.Node.out(a, i),
          None{},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Replicas.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Basics.Node.out(a, i),
          Some{Replicas.Out.Stale{}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Basics.Node.out(b, i),
          Some{Replicas.Out.Stale{}},
          ho(Replicas.Out.Stale{})(eo)
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, Some{Replicas.Out.Stale{}}),
            Some{Reading.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        {==}
    case Some{Replicas.Out.Taken{k}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Basics.Node.out(a, i),
          Some{Replicas.Out.Taken{k}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Basics.Node.out(b, i),
          Some{Replicas.Out.Taken{k}},
          ho(Replicas.Out.Taken{k})(eo)
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, Some{Replicas.Out.Taken{k}}),
            Some{Reading.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        Taken.follows(a, b, i, q)

# the answer to a request that a node holds may come after the answer to it
def Asked.follows(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask,
  ho: @o: Replicas.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Reading.Answer.follows(
    Reading.Answer.asked(a, i, q),
    Some{Reading.Answer.asked(b, i, q)}
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, ch}:
      Of.follows(a, b, i, Basics.Ask.On{st, l, ch}, Basics.Node.out(a, i))({==})(ho)

# Held.follows once whether the held change is the one asked is known (bq)
def Held.follows.if(
  bq: Bool,
  -x: Reading.Answer,
  -y: Reading.Answer,
  h: {Reading.Answer.follows(x, Some{y}) == True{}: Bool}
) -> {
  Reading.Answer.follows(
    Shared.Bool.when(Reading.Answer, bq, u => x, u => Reading.Answer.Refused{}),
    Some{Shared.Bool.when(Reading.Answer, bq, u => y, u => Reading.Answer.Refused{})}
  )
    == True{}: Bool
}:
  match bq:
    case True{}:
      h
    case False{}:
      {==}

# the answer of a node that holds the same cell may come after the answer
def Held.follows(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  ho: @o: Replicas.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Follows.opt(Reading.Answer.held(a, i, q, m), Reading.Answer.held(b, i, q, m)) == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Held.follows.if(
        Basics.Ask.is_eq(q2, q),
        Reading.Answer.asked(a, i, q2),
        Reading.Answer.asked(b, i, q2),
        Asked.follows(a, b, i, q2, ho)
      )
    case Some{Cells.One{Ledgers.Entry.Vote{v}}}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Data{d}}}:
      {==}
    case Some{Cells.Many{}}:
      {==}

# a cell that is kept is the same cell
def Cell.kept.eq(
  c: Cells.Cell<Ledgers.Entry<Basics.Ask>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    Some{c},
    mb
  )
    == True{}: Bool
} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}:
  match c mb:
    case Cells.One{x} y:
      Cells.Cell.keeps_value(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
        ~Ledgers.Entry.laws(~Basics.Ask, ~Basics.Ask.is_eq, ~Basics.Ask.laws()),
        x,
        y
      )
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{y}}:
      h => Empty.absurd(
        {
          Some{Cells.One{y}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )

# Node.answer_follows once the cell ma of the request's ID is known
def Answer.follows.at(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  q: Basics.Ask,
  -x: Reading.Answer,
  ma: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  ho: @o: Replicas.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    ma,
    mb
  )
    == True{}: Bool
} -> {
  Reading.Answer.held(a, i, q, ma) == Some{x}: Maybe<&2, Reading.Answer>
} -> {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, mb)) == True{}: Bool}:
  match ma:
    case None{}:
      ek => e => Empty.absurd(
        {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, mb)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Reading.Answer, x, e)
      )
    case Some{+c}:
      ek => e =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
          mb,
          Some{c},
          Cell.kept.eq(c, mb)(ek)
        ): {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, _)) == True{}: Bool}
        %e: {Follows.opt(_, Reading.Answer.held(b, i, q, Some{c})) == True{}: Bool}
        Held.follows(a, b, i, q, Some{c}, ho)

def Spec.Node.answer_follows(n, evs, s, e, q, x):
  Answer.follows.at(
    s,
    Spec.Node.after(n, evs, s),
    Replicas.Envelope.of(e),
    q,
    x,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e))),
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    ),
    o => Out.kept(
      s,
      Spec.Node.after(n, evs, s),
      Replicas.Envelope.of(e),
      o,
      Spec.Node.after_grows(n, evs, s),
      Spec.Node.after_keeps(n, evs, s)
    )
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      Replicas.State.ledger(~Basics.Ask.machine(), Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )(Spec.Node.after_grows(n, evs, s))
  )

# Drafts
# ------

# one of two drafts that are there
def When.some(
  b: Bool,
  -x: Maybe<&2, Reading.Draft>,
  -y: Maybe<&2, Reading.Draft>,
  hx: {Maybe.is_some(&2, Reading.Draft, x) == True{}: Bool},
  hy: {Maybe.is_some(&2, Reading.Draft, y) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Shared.Bool.when(Maybe<&2, Reading.Draft>, b, u => x, u => y)
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a draft that is there stays, with a write or not
def Draft.with.some(
  -found: Maybe<&2, Reading.Draft>,
  -k: List<&2, Bool>,
  m: Maybe<&2, Basics.Content>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Reading.Draft, Reading.Draft.with(found, k, m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{c}:
      h => {==}

# a draft that is there stays, after one more request
def Draft.of.some(
  w: String,
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  -found: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, i, a, found)) == True{}: Bool}:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      +h => When.some(
        String.eq(w2, w),
        Reading.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        ),
        found,
        Draft.with.some(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        )(h),
        h
      )
    case Ledgers.Id{w2, q2} None{}:
      h => h

# a draft that is there stays, after more requests
def Last.some(
  +s: Replicas.Node<Basics.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  found: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {
  Maybe.is_some(&2, Reading.Draft, Reading.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool
}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => Last.some(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found)
      )(Draft.of.some(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found)(h))

# a write of the writer w to the resource gives a draft
def Draft.of.hit(
  w: String,
  -r: Ledgers.Id,
  -b: String,
  -n: Resources.Name,
  -q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  -found: Maybe<&2, Reading.Draft>,
  ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>}
) -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Reading.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, Some{Ledgers.Asked{t, q}}, found)
  )
    == True{}: Bool
}:
  %Equal.sym(
    Bool,
    String.eq(w, w),
    True{},
    Texts.String.eq_refl(w)
  ): {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Shared.Bool.when(
        Maybe<&2, Reading.Draft>,
        _,
        u => Reading.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        ),
        u => found
      )
    )
      == True{}: Bool
  }
  %Equal.sym(
    Maybe<&2, Basics.Content>,
    Reading.Draft.content(r, b, n, q),
    Some{c},
    ec
  ): {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Reading.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), _)
    )
      == True{}: Bool
  }
  {==}

# Last.hit once whether the first request is the one looked for is known (bh)
def Last.hit.if(
  +s: Replicas.Node<Basics.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  +i: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  found: Maybe<&2, Reading.Draft>,
  q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  bh: Bool,
  ebh: {Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}) == bh: Bool},
  ea: {
    Replicas.Node.asked(~Basics.Ask.machine(), 
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Basics.Ask>>
  },
  ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}) == True{}: Bool
  } -> {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Reading.Draft.last(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found)
      )
    )
      == True{}: Bool
  }
) -> {
  List.any.if(
    u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}),
    bh
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Reading.Draft.last(
      s,
      w,
      r,
      b,
      n,
      rest,
      Reading.Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found)
    )
  )
    == True{}: Bool
}:
  match bh:
    case False{}:
      h => ih(h)
    case True{}:
      h => Last.some(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found)
      )(
        %Equal.sym(Ledgers.Id, i, Ledgers.Id{w, q2}, Ledgers.Id.is_eq_sound(i, Ledgers.Id{w, q2})(ebh)): {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, _, Replicas.Node.asked(~Basics.Ask.machine(), s, _), found)) == True{}: Bool}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Basics.Ask>>, Replicas.Node.asked(~Basics.Ask.machine(), s, Ledgers.Id{w, q2}), Some{Ledgers.Asked{t, q}}, ea): {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, _, found)) == True{}: Bool}
        Draft.of.hit(w, r, b, n, q2, t, q, c, found, ec))

# a write of the writer w among requests gives a draft
def Last.hit(
  +s: Replicas.Node<Basics.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  +found: Maybe<&2, Reading.Draft>,
  +q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  +ea: {
    Replicas.Node.asked(~Basics.Ask.machine(), 
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Basics.Ask>>
  },
  +ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>}
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, Ledgers.Id{w, q2}) == True{}: Bool
} -> {
  Maybe.is_some(&2, Reading.Draft, Reading.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool
}:
  match qs:
    case Nil{}:
      h => Empty.absurd(
        {Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+i, +rest}:
      Last.hit.if(
        s,
        w,
        r,
        b,
        n,
        i,
        rest,
        found,
        q2,
        t,
        q,
        c,
        Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}),
        {==},
        ea,
        ec,
        Last.hit(
          s,
          w,
          r,
          b,
          n,
          rest,
          Reading.Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found),
          q2,
          t,
          q,
          c,
          ea,
          ec
        )
      )

# the content of a draft that is there is there
def What.some(
  m: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, m) == True{}: Bool
} -> {Maybe.is_some(&2, Basics.Content, Reading.Draft.what(m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{Reading.Draft{k, c}}:
      h => {==}

def Spec.Node.draft_some(s, w, r, b, n, q2, t, q, c):
  hc => ea => ec => What.some(
    Reading.Draft.last(s, w, r, b, n, Replicas.Wait.of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})), None{})
  )(
    Last.hit(
      s,
      w,
      r,
      b,
      n,
      Replicas.Wait.of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      None{},
      q2,
      t,
      q,
      c,
      ea,
      ec
    )(hc)
  )

# Paths
# -----
# Every head is on the decided chain. A node sets a head in four places: a
# step that it checked (Advance.moved), and three that set only a head with no
# tip (Open.at, First.at, Follow.new). So a head that is some decided steps
# from a head with a tip stays so, one more step at a time, whatever the node
# does (Spec.Node.after_on).

# a head one height up has a tip
def Up.held(
  z: Replicas.Head,
  y: Hashes.Hash
) -> {Replicas.Head.held(Some{Replicas.Head.up(z, y)}) == True{}: Bool}:
  match z:
    case Replicas.Head{r, b, n, th}:
      {==}

# Moved.held once the tip m that the step names is known
def Moved.held.at(
  z: Replicas.Head,
  m: Maybe<&2, Hashes.Hash>,
  -h: Replicas.Head
) -> {
  Maybe.bind(
    &2,
    Hashes.Hash,
    Replicas.Head,
    m,
    y => Some{Replicas.Head.up(z, y)}
  )
    == Some{h}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Replicas.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Head, h, e)
      )
    case Some{y}:
      e =>
        %e: {Replicas.Head.held(_) == True{}: Bool}
        Up.held(z, y)

# a head that a step moved has a tip
def Moved.held(
  z: Replicas.Head,
  va: Maybe<&2, Ledgers.Vote>,
  -h: Replicas.Head
) -> {
  Replicas.Head.moved(z, va) == Some{h}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.held(Some{h}) == True{}: Bool}:
  Moved.held.at(z, Replicas.Vote.tip(va), h)

# Held.at for one more step, once the head m before it is known
def Held.at.step(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Nat,
  -h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    Replicas.Head,
    m,
    +x => Replicas.Head.moved(x, Replicas.Advance.in(~Basics.Ask.machine(), s, c, x, r))
  )
    == Some{h}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Replicas.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Head, h, e)
      )
    case Some{+z}:
      e => Moved.held(z, Replicas.Advance.in(~Basics.Ask.machine(), s, c, z, r), h)(e)

# a head that is some decided steps from a head with a tip has a tip
def Held.at(
  rs: List<&2, Nat>,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h0: Replicas.Head,
  -h: Replicas.Head
) -> {
  Replicas.Head.held(Some{h0}) == True{}: Bool
} -> {
  Replicas.Line.at(~Basics.Ask.machine(), rs, s, c, h0) == Some{h}: Maybe<&2, Replicas.Head>
} -> {Replicas.Head.held(Some{h}) == True{}: Bool}:
  match rs:
    case Nil{}:
      t0 => e =>
        %e: {Replicas.Head.held(_) == True{}: Bool}
        t0
    case Con{r, rest}:
      t0 => e => Held.at.step(s, c, r, h, Replicas.Line.at(~Basics.Ask.machine(), rest, s, c, h0))(e)

# a node is on its own paths
def Path.refl(-s: Replicas.Node<Basics.Ask>) -> Replicas.Node.On(~Basics.Ask.machine(), s, s):
  c => h0 => t0 => ra => ra

# paths compose
def Path.trans(
  -a: Replicas.Node<Basics.Ask>,
  -b: Replicas.Node<Basics.Ask>,
  -d: Replicas.Node<Basics.Ask>,
  h1: Replicas.Node.On(~Basics.Ask.machine(), a, b),
  h2: Replicas.Node.On(~Basics.Ask.machine(), b, d)
) -> Replicas.Node.On(~Basics.Ask.machine(), a, d):
  +c => +h0 => +t0 => ra => h2(c)(h0)(t0)(h1(c)(h0)(t0)(ra))

# one of two nodes, each on the paths of s
def Path.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: Replicas.Node.On(~Basics.Ask.machine(), s, x),
  hy: Replicas.Node.On(~Basics.Ask.machine(), s, y)
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a line whose head is the same in a node that grew is where it was
def Reach.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h0: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  eh: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Replicas.Node.head_of(~Basics.Ask.machine(), b, c): Maybe<&2, Replicas.Head>},
  ra: Replicas.Line.Reach(~Basics.Ask.machine(), a, c, h0)
) -> Replicas.Line.Reach(~Basics.Ask.machine(), b, c, h0):
  match ra:
    case Tuple{+rs, Tuple{+h, Tuple{e1, e2}}}:
      Tuple{
        rs,
        Tuple{
          h,
          Tuple{
            Equal.trans(
              Maybe<&2, Replicas.Head>,
              Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
              Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
              Some{h},
              Equal.sym(
                Maybe<&2, Replicas.Head>,
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
                eh
              ),
              e1
            ),
            Spec.Line.at_grows(rs, a, b, c, h0, h)(g)(e2)
          }
        }
      }

# a node that grew, with the same heads, is on the paths
def Path.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b): Tries.Trie<Replicas.Head>}
) -> Replicas.Node.On(~Basics.Ask.machine(), a, b):
  +c => +h0 => t0 => ra => Reach.same(
    a,
    b,
    c,
    h0,
    g,
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b),
      eh
    ),
    ra
  )

# the head of another line, after the head of the line c is set
def Head.other(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain,
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == False{}: Bool}
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), 
    a,
    c2
  )
    == Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2): Maybe<&2, Replicas.Head>
}:
  Equal.trans(
    Maybe<&2, Replicas.Head>,
    Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
    Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
    Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c2)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      eh
    ),
    Equal.sym(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
      Equal.trans(
        Maybe<&2, Replicas.Head>,
        Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
        Bool.pick(
          Maybe<&2, Replicas.Head>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
        ),
        Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
        Head.of_set(b0, c, hd, c2),
        Pick.of(
          Maybe<&2, Replicas.Head>,
          False{},
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
          ebs
        )
      )
    )
  )

# the head of a line with the key of the line c, after the head of c is set
def Head.this(
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool}
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2) == Some{hd}: Maybe<&2, Replicas.Head>}:
  Equal.trans(
    Maybe<&2, Replicas.Head>,
    Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2),
    Bool.pick(
      Maybe<&2, Replicas.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
    ),
    Some{hd},
    Head.of_set(b0, c, hd, c2),
    Pick.of(
      Maybe<&2, Replicas.Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
      ebs
    )
  )

# lines with the same key have the same head
def Head.keyed(
  a: Replicas.Node<Basics.Ask>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), a, c2) == Replicas.Node.head_of(~Basics.Ask.machine(), a, c): Maybe<&2, Replicas.Head>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Replicas.Head>,
    kk => Tries.Trie.get(Replicas.Head, Replicas.State.heads(~Basics.Ask.machine(), a), kk),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# lines with the same key have the same decided steps
def In.key(
  s: Replicas.Node<Basics.Ask>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  x: Replicas.Head,
  r: Nat,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Replicas.Advance.in(~Basics.Ask.machine(), s, c2, x, r) == Replicas.Advance.in(~Basics.Ask.machine(), s, c, x, r): Maybe<&2, Ledgers.Vote>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Ledgers.Vote>,
    kk => Maybe.bind(
      &2,
      Replicas.Tip,
      Ledgers.Vote,
      Replicas.Head.tip(~Basics.Ask.machine(), s, x),
      t => Ledgers.Bucket.decide(
        ~Basics.Ask,
        Ledgers.State.under(
          ~Basics.Ask,
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          List.append(
            &2,
            Bool,
            List.append(&2, Bool, False{} <> True{} <> kk, Ledgers.Word.key(Replicas.Head.next(x))),
            Ledgers.Round.key(r, [False{}])
          )
        ),
        Replicas.Tip.owners(t)
      )
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# no line with the key of c is some decided steps from a head with a tip, when
# the head of c has no tip
def Path.set.no(
  +a: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  nh: {Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool},
  t0: {Replicas.Head.held(Some{h0}) == True{}: Bool},
  ra: Replicas.Line.Reach(~Basics.Ask.machine(), a, c2, h0)
) -> Empty:
  match ra:
    case Tuple{rs, Tuple{h, Tuple{e1, e2}}}:
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)),
          True{},
          Equal.sym(Bool, Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)), False{}, nh),
          Equal.trans(
            Bool,
            Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)),
            Replicas.Head.held(Some{h}),
            True{},
            Equal.cong(
              Maybe<&2, Replicas.Head>,
              Bool,
              Replicas.Head.held,
              Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
              Some{h},
              Equal.trans(
                Maybe<&2, Replicas.Head>,
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
                Some{h},
                Equal.sym(
                  Maybe<&2, Replicas.Head>,
                  Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
                  Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                  Head.keyed(a, c2, c, ek)
                ),
                e1
              )
            ),
            Held.at(rs, a, c2, h0, h)(t0)(e2)
          )
        )
      )

# Path.set for the line c2, once it is known whether it has the key of c (bs)
def Path.set.if(
  +a: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +hd: Replicas.Head,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  bs: Bool,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  nh: {Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool},
  t0: {Replicas.Head.held(Some{h0}) == True{}: Bool},
  ra: Replicas.Line.Reach(~Basics.Ask.machine(), a, c2, h0)
) -> Replicas.Line.Reach(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Empty.absurd(
        Replicas.Line.Reach(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2, h0),
        Path.set.no(a, c, c2, h0, Key.same(c2, c)(ebs), nh, t0, ra)
      )
    case False{}:
      Reach.same(
        a,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        c2,
        h0,
        Grows.to(
          a,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Led.head(b0, c, hd),
          g
        ),
        Head.other(a, b0, c, hd, c2, eh, ebs),
        ra
      )

# a node b0 with a new head hd of the line c is on the paths of a, when b0
# grew from a with the same heads, and the head of c in a has no tip
def Path.set(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  hd: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  nh: {Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool}
) -> Replicas.Node.On(~Basics.Ask.machine(), a, Replicas.State.head(~Basics.Ask.machine(), b0, c, hd)):
  +c2 => +h0 => t0 => ra => Path.set.if(
    a,
    b0,
    c,
    hd,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    nh,
    t0,
    ra
  )

# Path.moved for a line with the key of c: one more decided step
def Path.moved.yes(
  +s: Replicas.Node<Basics.Ask>,
  +n: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  hd: Replicas.Head,
  +q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  +ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  +gn: {Replicas.Node.grows(~Basics.Ask.machine(), s, n) == True{}: Bool},
  en: {Replicas.Node.head_of(~Basics.Ask.machine(), n, c2) == Some{hd}: Maybe<&2, Replicas.Head>},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Replicas.Advance.in(~Basics.Ask.machine(), s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Replicas.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>},
  ra: Replicas.Line.Reach(~Basics.Ask.machine(), s, c2, h0)
) -> Replicas.Line.Reach(~Basics.Ask.machine(), n, c2, h0):
  match ra:
    case Tuple{+rs, Tuple{h2, Tuple{e1, e2}}}:
      Tuple{
        q <> rs,
        Tuple{
          hd,
          Tuple{
            en,
            Equal.trans(
              Maybe<&2, Replicas.Head>,
              Replicas.Line.at(~Basics.Ask.machine(), q <> rs, n, c2, h0),
              Replicas.Head.moved(h2, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h2, q)),
              Some{hd},
              Equal.cong(
                Maybe<&2, Replicas.Head>,
                Maybe<&2, Replicas.Head>,
                m => Maybe.bind(
                  &2,
                  Replicas.Head,
                  Replicas.Head,
                  m,
                  +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, z, q))
                ),
                Replicas.Line.at(~Basics.Ask.machine(), rs, n, c2, h0),
                Some{h2},
                Spec.Line.at_grows(rs, s, n, c2, h0, h2)(gn)(e2)
              ),
              Equal.trans(
                Maybe<&2, Replicas.Head>,
                Replicas.Head.moved(h2, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h2, q)),
                Replicas.Head.moved(h, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h, q)),
                Some{hd},
                Equal.cong(
                  Replicas.Head,
                  Maybe<&2, Replicas.Head>,
                  +z => Replicas.Head.moved(z, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, z, q)),
                  h2,
                  h,
                  Shared.Maybe.some_inj(
                    Replicas.Head,
                    h2,
                    h,
                    Equal.trans(
                      Maybe<&2, Replicas.Head>,
                      Some{h2},
                      Replicas.Node.head_of(~Basics.Ask.machine(), s, c2),
                      Some{h},
                      Equal.sym(Maybe<&2, Replicas.Head>, Replicas.Node.head_of(~Basics.Ask.machine(), s, c2), Some{h2}, e1),
                      Equal.trans(
                        Maybe<&2, Replicas.Head>,
                        Replicas.Node.head_of(~Basics.Ask.machine(), s, c2),
                        Replicas.Node.head_of(~Basics.Ask.machine(), s, c),
                        Some{h},
                        Head.keyed(s, c2, c, ek),
                        em
                      )
                    )
                  )
                ),
                Equal.trans(
                  Maybe<&2, Replicas.Head>,
                  Replicas.Head.moved(h, Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h, q)),
                  Replicas.Head.moved(h, Some{v}),
                  Some{hd},
                  Equal.cong(
                    Maybe<&2, Ledgers.Vote>,
                    Maybe<&2, Replicas.Head>,
                    w => Replicas.Head.moved(h, w),
                    Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h, q),
                    Some{v},
                    Equal.trans(
                      Maybe<&2, Ledgers.Vote>,
                      Replicas.Advance.in(~Basics.Ask.machine(), n, c2, h, q),
                      Replicas.Advance.in(~Basics.Ask.machine(), n, c, h, q),
                      Some{v},
                      In.key(n, c2, c, h, q, ek),
                      In.grows(s, n, c, h, q, v, gn)(ein)
                    )
                  ),
                  emv
                )
              )
            )
          }
        }
      }

# Path.moved for the line c2, once it is known whether it has the key of c
def Path.moved.if(
  +s: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +hd: Replicas.Head,
  q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Replicas.Advance.in(~Basics.Ask.machine(), s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Replicas.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>},
  ra: Replicas.Line.Reach(~Basics.Ask.machine(), s, c2, h0)
) -> Replicas.Line.Reach(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Path.moved.yes(
        s,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        c,
        h,
        hd,
        q,
        v,
        c2,
        h0,
        Key.same(c2, c)(ebs),
        Grows.to(
          s,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Led.head(b0, c, hd),
          g
        ),
        Head.this(b0, c, hd, c2, ebs),
        em,
        ein,
        emv,
        ra
      )
    case False{}:
      Reach.same(
        s,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        c2,
        h0,
        Grows.to(
          s,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Led.head(b0, c, hd),
          g
        ),
        Head.other(s, b0, c, hd, c2, eh, ebs),
        ra
      )

# a head moved over the step v that the owners decided at it, in the round
# q, is one more decided step on its path
def Path.moved(
  +s: Replicas.Node<Basics.Ask>,
  +s3: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  hd: Replicas.Head,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g3: {Replicas.Node.grows(~Basics.Ask.machine(), s, s3) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Replicas.Advance.in(~Basics.Ask.machine(), s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Replicas.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>}
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.State.moved(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)), c, hd, qs)):
  +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +ws = Replicas.Wait.left(
    Replicas.Wait.of(~Basics.Ask.machine(), x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Replicas.Wait.set(~Basics.Ask.machine(), x, c, ws)
  +c2 => +h0 => t0 => ra => Path.moved.if(
    s,
    b0,
    c,
    h,
    hd,
    q,
    v,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    Grows.to(s, x, b0, Led.wait(x, c, ws), Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Replicas.Head>,
      Replicas.State.heads(~Basics.Ask.machine(), s),
      Replicas.State.heads(~Basics.Ask.machine(), x),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
      Heads.wait(x, c, ws)
    ),
    em,
    ein,
    emv,
    ra
  )

# Advance.moved is on the paths, once the node m that the put gives is known
def Advance.moved.path(
  +s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  hd: Replicas.Head,
  t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g2: {Replicas.Node.grows(~Basics.Ask.machine(), s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Replicas.Advance.in(~Basics.Ask.machine(), s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Replicas.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]) == m: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advance.moved(~Basics.Ask.machine(), s, m, c, hd, qs)):
  match m:
    case None{}:
      e2 => Path.refl(s)
    case Some{+s3}:
      e2 => Path.moved(
        s,
        s3,
        c,
        h,
        hd,
        qs,
        q,
        v,
        Grows.trans(
          s,
          s2,
          s3
        )(g2)(Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)),
        em,
        ein,
        emv
      )

# Advance.ran is on the paths, once it is known whether the run gives the tip
# that the step names (bq)
def Advance.ran.path.if(
  s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  c: Ledgers.Chain,
  +r: Ledgers.Id,
  +br: Maybe<&2, String>,
  +next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  +qs: List<&2, Ledgers.Id>,
  q: Nat,
  bq: Bool,
  ebq: {Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}) == bq: Bool},
  g2: {Replicas.Node.grows(~Basics.Ask.machine(), s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{Replicas.Head{r, br, next, th}}: Maybe<&2, Replicas.Head>},
  ein: {
    Replicas.Advance.in(~Basics.Ask.machine(), 
      s,
      c,
      Replicas.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> Replicas.Node.On(~Basics.Ask.machine(), 
  s,
  Shared.Bool.when(
    Replicas.Node<Basics.Ask>,
    bq,
    u => Replicas.Advance.moved(~Basics.Ask.machine(), 
      s,
      Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
      c,
      Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
      qs
    ),
    u => s
  )
):
  match bq:
    case True{}:
      Advance.moved.path(
        s,
        s2,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
        c,
        Replicas.Head{r, br, next, th},
        Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
        t2,
        qs,
        q,
        Ledgers.Vote{before, qs, after},
        g2,
        em,
        ein,
        Equal.cong(
          Maybe<&2, Hashes.Hash>,
          Maybe<&2, Replicas.Head>,
          a => Maybe.bind(
            &2,
            Hashes.Hash,
            Replicas.Head,
            a,
            y => Some{Replicas.Head.up(Replicas.Head{r, br, next, th}, y)}
          ),
          after,
          Some{Replicas.Tip.hash(t2)},
          Shared.Maybe.is_eq_sound(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Hashes.Hash.is_eq_sound,
            after,
            Some{Replicas.Tip.hash(t2)}
          )(ebq)
        )
      )({==})
    case False{}:
      Path.refl(s)

# a checked step is on the paths
def Advance.ran.path(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  q: Nat,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{Replicas.Head{r, br, next, th}}: Maybe<&2, Replicas.Head>},
  ein: {
    Replicas.Advance.in(~Basics.Ask.machine(), 
      s,
      c,
      Replicas.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> {
  Run.after(s, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => Path.refl(s)
    case Some{Replicas.Run{s2, +t2}}:
      ga => Advance.ran.path.if(
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        th,
        before,
        after,
        qs,
        q,
        Replicas.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        {==},
        ga,
        em,
        ein
      )

# Node.advance is on the paths, once the decided step m is known
def Advance.step.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>}
  -> {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
  -> {
    Replicas.Height.decide(~Basics.Ask.machine(), 
      s,
      c,
      Replicas.Head.next(h),
      Replicas.Tip.owners(t),
      Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
    )
      == m: Maybe<&2, Ledgers.Vote>
  }
  -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advance.step(~Stepping.Ask.kernel(), s, c, h, t, m)):
  match h m:
    case Replicas.Head{r, br, +next, +th} Some{Ledgers.Vote{+before, +qs, after}}:
      em => et => ed => Path.when(
        Replicas.Root.same(before, th),
        s,
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Scan.elim(
          Replicas.Node.On(~Basics.Ask.machine(), 
            s,
            Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs))
          ),
          s,
          c,
          next,
          Replicas.Tip.owners(t),
          Replicas.Round.seen(~Basics.Ask.machine(), s, c, next),
          Ledgers.Vote{before, qs, after}
        )(
          ed
        )(
          q => d => Advance.ran.path(
            s,
            c,
            r,
            br,
            next,
            th,
            before,
            after,
            qs,
            Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs),
            q,
            em,
            (
              %Equal.sym(Maybe<&2, Replicas.Tip>, Replicas.Head.tip(~Basics.Ask.machine(), s, Replicas.Head{r, br, next, th}), Some{t}, et): {Maybe.bind(&2, Replicas.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, next, q}, Replicas.Tip.owners(t1))) == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>}
              d)
          )(Run.grows(s, c, t, qs))
        ),
        Path.refl(s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => ed => Path.refl(s)

# Node.advance is on the paths, at the head h whose tip is m
def Advance.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, m)):
  match m:
    case None{}:
      em => et => Path.refl(s)
    case Some{+t}:
      em => et => Advance.step.path(
        s,
        c,
        h,
        t,
        Replicas.Height.decide(~Basics.Ask.machine(), 
          s,
          c,
          Replicas.Head.next(h),
          Replicas.Tip.owners(t),
          Replicas.Round.seen(~Basics.Ask.machine(), s, c, Replicas.Head.next(h))
        )
      )(em)(et)({==})

# a node's ballot keeps its logs
def Cast.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c)):
  Path.same(
    s,
    Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c),
    Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  )

# Advances.kept once the head m is known
def Advances.at.path(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advances.at(~Stepping.Ask.kernel(), f, s, c, m)):
  match f m:
    case 0n x:
      em => Path.refl(s)
    case 1n+p None{}:
      em => Path.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Path.when(
          Replicas.Heads.level(Some{h}, m1),
          s,
          s1,
          Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
          Advance.at.path(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Path.trans(
            s,
            s1,
            Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
            Advance.at.path(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
            Advances.at.path(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step is on the paths
def Advances.path(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.advances(~Stepping.Ask.kernel(), f, s, c)):
  Advances.at.path(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==})

# what a node does at a head is on the paths
def Step.head.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Step.head(~Stepping.Ask.kernel(), n, s, c)):
  +s1 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s, c)
  +s2 = Replicas.Node.cast(~Stepping.Ask.kernel(), n, s1, c)
  s3 = Replicas.Node.advances(~Stepping.Ask.kernel(), 4294967295n, s2, c)
  Path.trans(
    s,
    s1,
    s3,
    Advances.path(4294967295n, s, c),
    Path.trans(s1, s2, s3, Cast.path(n, s1, c), Advances.path(4294967295n, s2, c))
  )

# a head with no tip is not held
def Held.not(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>}
) -> {Replicas.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), s, c)) == Replicas.Head.held(m): Bool}:
  Equal.cong(Maybe<&2, Replicas.Head>, Bool, Replicas.Head.held, Replicas.Node.head_of(~Basics.Ask.machine(), s, c), m, em)

# a branch that opens is on the paths, once the head m of the line is known
def Open.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Open.at(~Basics.Ask.machine(), s, c, m)):
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        Replicas.Head{
          r,
          Some{b},
          0,
          Replicas.Branch.first(~Basics.Ask.machine(), s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
        },
        Grows.refl(s),
        {==},
        Held.not(s, c, Some{Replicas.Head{r, Some{b}, n, None{}}}, em)
      )
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      em => Path.refl(s)
    case None{}:
      em => Path.refl(s)

# what a node does on a line is on the paths
def Step.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)):
  s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Path.trans(
    s,
    s1,
    Replicas.Step.head(~Stepping.Ask.kernel(), n, s1, c),
    Open.at.path(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==}),
    Step.head.path(n, s1, c)
  )

# a pass to the next round is on the paths
def Pass.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c)):
  +s1 = Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Path.trans(
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Path.same(
      s,
      s1,
      Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      Pass.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
    ),
    Step.path(n, s1, c)
  )

# a first head is on the paths, once the head m of the line is known
def First.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.First.at(~Basics.Ask.machine(), s, c, h, m)):
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Replicas.Head{+r, +b, +n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        Held.not(s, c, Some{Replicas.Head{r, b, n, None{}}}, em)
      )
    case None{}:
      em => Path.set(s, s, c, h, Grows.refl(s), {==}, Held.not(s, c, None{}, em))

# a first head on a node that grew from a, which grew from s, is on the paths
def Start.head.path(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Start.head(~Basics.Ask.machine(), s, m, c, h)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Path.trans(
          s,
          x,
          Replicas.State.first(~Basics.Ask.machine(), x, c, h),
          Path.same(
            s,
            x,
            Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          ),
          First.at.path(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c))({==})
        )

# Start.path once the content m of the store is known
def Start.with.path(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Work.after(s, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Start.with(~Basics.Ask.machine(), s, i, os, m)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{Replicas.Work{+s2, +c}}:
      e =>
        +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
        Start.head.path(
          s,
          s2,
          Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Replicas.Tip.words(t)]))

# a store that starts is on the paths
def Start.path(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Replicas.Owner>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.start(~Stepping.Ask.kernel(), s, i, os)):
  Start.with.path(
    s,
    i,
    Replicas.Owner.names(os),
    Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Grows.refl(s)))

# a line that a node starts to follow is on the paths
def Follow.new.path(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)) == m: Maybe<&2, Replicas.Head>
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Follow.new(~Basics.Ask.machine(), s, r, l, m)):
  match m:
    case Some{h}:
      em => Path.refl(s)
    case None{}:
      em => Path.set(
        s,
        s,
        Replicas.Line.chain(r, l),
        Replicas.Head{r, l, 0, None{}},
        Grows.refl(s),
        {==},
        Held.not(s, Replicas.Line.chain(r, l), None{}, em)
      )

# a new request is on the paths
def Arrive.path(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      Start.path(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Replicas.Node.follow(~Basics.Ask.machine(), s, r, l)
      Path.trans(
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Follow.new.path(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Path.same(
          s1,
          Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
          Grows.to(
            s1,
            s1,
            Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Led.waits(s1, Replicas.Line.chain(r, l), i),
            Grows.refl(s1)
          ),
          Heads.waits(s1, Replicas.Line.chain(r, l), i)
        )
      )

# a new request is on the paths
def Ask.new.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.ask.new(~Stepping.Ask.kernel(), n, s, e, q)):
  +i = Replicas.Envelope.of(e)
  c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Replicas.State.ledger(~Basics.Ask.machine(), s),
    i,
    Replicas.Envelope.time(e),
    q
  )
  +s0 = Replicas.State.led(~Basics.Ask.machine(), s, l0)
  s1 = Replicas.Node.arrive(~Stepping.Ask.kernel(), s0, i, q)
  Path.trans(
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Path.same(
      s,
      s0,
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
      ),
      Heads.led(s, l0)
    ),
    Path.trans(s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c), Arrive.path(s0, i, q), Step.path(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.ask.at(~Stepping.Ask.kernel(), n, s, e, q, m)):
  match m:
    case Some{x}:
      Path.refl(s)
    case None{}:
      Path.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Replicas.Node.ask.new(~Stepping.Ask.kernel(), 
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        ),
        Path.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Grows.refl(s)
          ),
          Heads.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
        ),
        Ask.new.path(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask is on the paths
def Ask.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q)):
  Ask.at.path(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e)))
  )

# the new requests among cells are on the paths
def Take.asks.path(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Take.asks(~Stepping.Ask.kernel(), cs, old, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Replicas.Node<Basics.Ask>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
        u => s
      )
      Path.trans(
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1),
        Path.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
          s,
          Arrive.path(s, i, q),
          Path.refl(s)
        ),
        Take.asks.path(rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.path(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.path(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.path(rest, old, s)

# Node.take is on the paths
def Take.path(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.take(~Stepping.Ask.kernel(), s, t)):
  +sent = Replicas.Take.clean(~Basics.Ask.machine(), 
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Replicas.Take.asks(~Stepping.Ask.kernel(), cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Path.trans(
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
    Path.same(
      s,
      s1,
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
      ),
      Heads.led(s, l1)
    ),
    Path.trans(
      s1,
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Take.asks.path(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
      Path.same(
        s2,
        Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
        Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2),
        Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines is on the paths
def Steps.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Path.trans(s, s1, Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1), Step.path(n, s, c), Steps.path(n, rest, s1))

# an adoption is on the paths, once the request m is known
def Adopt.ask.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Reading.Request>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Reading.Request{e, q}}:
      Ask.path(n, s, e, q)

# an adoption is on the paths, once the head m of the line is known
def Adopt.head.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.path(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line is on the paths
def Adopt.at.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Adopt.at(n, s, c)):
  Adopt.head.path(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, is on the paths
def Adopt.maybe.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Adopt.at.path(n, s, c)

# the adoption of each of some lines is on the paths
def Adopts.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      Path.trans(
        s,
        Reading.Adopt.at(n, s, c),
        Reading.Node.adopts(n, rest, Reading.Adopt.at(n, s, c)),
        Adopt.at.path(n, s, c),
        Adopts.path(n, rest, Reading.Adopt.at(n, s, c))
      )

# more rounds of a sync, path
def More.path(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Sync.more(f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Path.refl(s)
    case 1n+(p):
      Path.when(
        Reading.Lines.level(cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        s,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Reading.Sync.more(
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Path.trans(
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Path.same(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Each.grows(k, bs, pd, s),
            Each.heads(k, bs, pd, s)
          ),
          Steps.path(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Path.trans(
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Reading.Sync.more(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          Path.trans(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
            Path.same(
              s,
              Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
              Each.grows(k, bs, pd, s),
              Each.heads(k, bs, pd, s)
            ),
            Steps.path(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          More.path(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )
        )
      )

# a sync is on the paths
def Sync.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Reading.Node.sync(n, s, t)):
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  s3 = Reading.Sync.more(
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
    s2
  )
  Path.trans(
    s,
    s1,
    Reading.Node.adopts(n, cs, s3),
    Take.path(s, t),
    Path.trans(
      s1,
      s2,
      Reading.Node.adopts(n, cs, s3),
      Steps.path(n, cs, s1),
      Path.trans(
        s2,
        s3,
        Reading.Node.adopts(n, cs, s3),
        More.path(
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Replicas.Pending.of(bs),
          s2
        ),
        Adopts.path(n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node is on the paths
def Consent.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Consent.at(~Stepping.Ask.kernel(), n, s, i, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Path.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Path.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Led.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Grows.refl(s)
          ),
          Heads.keyed(s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.path(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does is on the paths
def Does.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Spec.Deed
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Path.trans(
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Reading.Adopt.at(
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
        ),
        Ask.path(n, s, e, q),
        Adopt.at.path(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
      )
    case Spec.Deed.Take{t}:
      Take.path(s, t)
    case Spec.Deed.Sync{t}:
      Sync.path(n, s, t)
    case Spec.Deed.Keep{+b}:
      Path.same(
        s,
        Basics.Node.keep(s, b),
        Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b))),
        Heads.led(
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Basics.Bytes.rope(b)),
            Replicas.State.ledger(~Basics.Ask.machine(), s)
          )
        )
      )
    case Spec.Deed.Consent{+i}:
      Path.trans(
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Reading.Adopt.maybe(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Consent.path(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Adopt.maybe.path(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )
    case Spec.Deed.Pass{+c}:
      Path.trans(
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Reading.Adopt.at(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c),
        Pass.path(n, s, c),
        Adopt.at.path(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )
    case Spec.Deed.Pass{c}:
      Pass.path(n, s, c)

def Spec.Node.after_on(n, evs, s):
  match evs:
    case Nil{}:
      Path.refl(s)
    case Con{+ev, rest}:
      s1 = Spec.Node.does(n, s, ev)
      Path.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1),
        Does.path(n, s, ev),
        Spec.Node.after_on(n, rest, s1)
      )

# Waits
# -----
# A request that a node takes in waits on its line: a pending write goes with
# its writer to another node (Spec.Node.take_waits).

# a new ledger keeps the waiting requests
def Waiting.led(
  s: Replicas.Node<Basics.Ask>,
  l: Ledgers.State(Basics.Ask)
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Replicas.Node{old, hs, ws, ks}:
      {==}

# new keys keep the waiting requests
def Waiting.keyed(
  s: Replicas.Node<Basics.Ask>,
  ks: Replicas.Keys
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.State.keyed(~Basics.Ask.machine(), s, ks)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Replicas.Node{l, hs, ws, old}:
      {==}

# the waiting requests of the node m, if any, else of s
def Waiting.of(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Node<Basics.Ask>>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match m:
    case None{}:
      Replicas.State.waiting(~Basics.Ask.machine(), s)
    case Some{s2}:
      Replicas.State.waiting(~Basics.Ask.machine(), s2)

# a node that is kept when b holds has the waiting requests of s, when it has
def Waiting.some.if(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  hx: {Replicas.State.waiting(~Basics.Ask.machine(), s) == Replicas.State.waiting(~Basics.Ask.machine(), x): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Waiting.of(
      s,
      Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{x})
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the waiting requests
def Accept.at.waiting(
  +s: Replicas.Node<Basics.Ask>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Replicas.Keychain>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Waiting.of(s, Replicas.Seal.accept.at(~Basics.Ask.machine(), s, b, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Waiting.some.if(
        Replicas.Seal.fits(c, b),
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), 
          Replicas.State.led(~Basics.Ask.machine(), 
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Replicas.Keys.saw(
            Replicas.Keys.set(
              Replicas.State.keys(~Basics.Ask.machine(), s),
              Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
              Replicas.Keychain.next(c, b)
            ),
            Replicas.Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<List<&2, Ledgers.Id>>,
          Replicas.State.waiting(~Basics.Ask.machine(), s),
          Replicas.State.waiting(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            )
          ),
          Replicas.State.waiting(~Basics.Ask.machine(), 
            Replicas.State.keyed(~Basics.Ask.machine(), 
              Replicas.State.led(~Basics.Ask.machine(), 
                s,
                Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
              ),
              Replicas.Keys.saw(
                Replicas.Keys.set(
                  Replicas.State.keys(~Basics.Ask.machine(), s),
                  Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                  Replicas.Keychain.next(c, b)
                ),
                Replicas.Ballot.at(b)
              )
            )
          ),
          Waiting.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Waiting.keyed(
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Replicas.Keys.saw(
              Replicas.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Replicas.Seal.slot(Replicas.Ballot.store(b), Replicas.Ballot.node(b)),
                Replicas.Keychain.next(c, b)
              ),
              Replicas.Ballot.at(b)
            )
          )
        )
      )

# the ballots that a chain leads to keep the waiting requests, when each one more does
def Follow.step.waiting(
  -s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  -k: Replicas.Node<Basics.Ask> -> Replicas.Node<Basics.Ask>,
  ih: @s2: Replicas.Node<Basics.Ask> -> {
    Replicas.State.waiting(~Basics.Ask.machine(), s2) == Replicas.State.waiting(~Basics.Ask.machine(), k(s2)): Tries.Trie<List<&2, Ledgers.Id>>
  }
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), s) == Waiting.of(s, m): Tries.Trie<List<&2, Ledgers.Id>>
} -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), 
      Maybe.default(
        &2,
        Replicas.Node<Basics.Ask>,
        Maybe.bind(&2, Replicas.Node<Basics.Ask>, Replicas.Node<Basics.Ask>, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Replicas.State.waiting(~Basics.Ask.machine(), s),
        Replicas.State.waiting(~Basics.Ask.machine(), s2),
        Replicas.State.waiting(~Basics.Ask.machine(), k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the waiting requests
def Follow.waiting(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), 
      Replicas.Sealed.follow(~Stepping.Ask.kernel(), f, s, p, r, n, mb)
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.waiting(
        s,
        Replicas.Seal.accept(~Stepping.Ask.kernel(), s, b),
        +s2 => Replicas.Sealed.follow(~Stepping.Ask.kernel(), g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n)),
        +s2 => Follow.waiting(g, s2, p, r, n, Replicas.Pending.next(~Stepping.Ask.kernel(), s2, p, r, n))
      )(
        Accept.at.waiting(
          s,
          b,
          Replicas.Seal.chain(~Stepping.Ask.kernel(), s, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the waiting requests
def Each.waiting(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.Sealed.each(~Stepping.Ask.kernel(), f, bs, p, s)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Replicas.Sealed.follow(~Stepping.Ask.kernel(), 
        f,
        s,
        p,
        Replicas.Ballot.store(b),
        Replicas.Ballot.node(b),
        Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Replicas.State.waiting(~Basics.Ask.machine(), s),
        Replicas.State.waiting(~Basics.Ask.machine(), s1),
        Replicas.State.waiting(~Basics.Ask.machine(), Replicas.Sealed.each(~Stepping.Ask.kernel(), f, rest, p, s1)),
        Follow.waiting(
          f,
          s,
          p,
          Replicas.Ballot.store(b),
          Replicas.Ballot.node(b),
          Replicas.Pending.next(~Stepping.Ask.kernel(), s, p, Replicas.Ballot.store(b), Replicas.Ballot.node(b))
        ),
        Each.waiting(f, rest, p, s1)
      )

# a new head keeps the waiting requests
def Waiting.head(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.State.head(~Basics.Ask.machine(), s, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a first head keeps the waiting requests
def First.at.waiting(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  +m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.First.at(~Basics.Ask.machine(), s, c, h, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      {==}
    case Some{Replicas.Head{r, b, n, None{}}}:
      Waiting.head(s, c, h)
    case None{}:
      Waiting.head(s, c, h)

# the first head of a store keeps the waiting requests
def Start.head.waiting(
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.Start.head(~Basics.Ask.machine(), s, m, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+s2}:
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Replicas.State.waiting(~Basics.Ask.machine(), s),
        Replicas.State.waiting(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s2))),
        Replicas.State.waiting(~Basics.Ask.machine(), 
          Replicas.State.first(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s2)), c, h)
        ),
        Waiting.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s2)),
        First.at.waiting(
          Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s2)),
          c,
          h,
          Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s2)), c)
        )
      )

# a store that starts keeps the waiting requests, once its content m is known
def Start.with.waiting(
  s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.Start.with(~Basics.Ask.machine(), s, i, os, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Work{s2, +c}}:
      Start.head.waiting(
        s,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(Replicas.Tip{c, None{}, 0, os})]),
        Ledgers.Chain{i, None{}},
        Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(Replicas.Tip{c, None{}, 0, os})}}
      )

# a line that a node starts to follow keeps the waiting requests
def Follow.new.waiting(
  s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.waiting(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.waiting(~Basics.Ask.machine(), Replicas.Follow.new(~Basics.Ask.machine(), s, r, l, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{h}:
      {==}
    case None{}:
      Waiting.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}})

# nodes with the same waiting requests have the same ones on each line
def Wait.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  e: {Replicas.State.waiting(~Basics.Ask.machine(), a) == Replicas.State.waiting(~Basics.Ask.machine(), b): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {Replicas.Wait.of(~Basics.Ask.machine(), a, c) == Replicas.Wait.of(~Basics.Ask.machine(), b, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    Tries.Trie<List<&2, Ledgers.Id>>,
    List<&2, Ledgers.Id>,
    ws => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c)),
      []
    ),
    Replicas.State.waiting(~Basics.Ask.machine(), a),
    Replicas.State.waiting(~Basics.Ask.machine(), b),
    e
  )

# lines with the same key have the same waiting requests
def Wait.keyed(
  s: Replicas.Node<Basics.Ask>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Replicas.Wait.of(~Basics.Ask.machine(), s, c2) == Replicas.Wait.of(~Basics.Ask.machine(), s, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    List<&2, Bool>,
    List<&2, Ledgers.Id>,
    kk => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, Replicas.State.waiting(~Basics.Ask.machine(), s), kk),
      []
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# the default of a pick is the pick of the defaults
def Wait.pick(
  +b: Bool,
  v: List<&2, Ledgers.Id>,
  m: Maybe<&2, List<&2, Ledgers.Id>>
) -> {
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Bool.pick(Maybe<&2, List<&2, Ledgers.Id>>, b, Some{v}, m),
    []
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      v,
      Maybe.default(&2, List<&2, Ledgers.Id>, m, [])
    ): List<&2, Ledgers.Id>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the requests that wait on a line, after some requests wait on the line c
def Wait.set.of(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +r: List<&2, Ledgers.Id>,
  +c2: Ledgers.Chain
) -> {
  Replicas.Wait.of(~Basics.Ask.machine(), 
    Replicas.Wait.set(~Basics.Ask.machine(), s, c, x <> r),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      x <> r,
      Replicas.Wait.of(~Basics.Ask.machine(), s, c2)
    ): List<&2, Ledgers.Id>
}:
  match s:
    case Replicas.Node{l, hs, +ws, ks}:
      %Equal.sym(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Tries.Trie.get(
          List<&2, Ledgers.Id>,
          Tries.Trie.set(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c), x <> r),
          Ledgers.Chain.key(c2)
        ),
        Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{x <> r},
          Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
        ),
        Tries.Trie.get_set(
          List<&2, Ledgers.Id>,
          ws,
          Ledgers.Chain.key(c),
          x <> r,
          Ledgers.Chain.key(c2)
        )
      ): {
        Maybe.default(
          &2,
          List<&2, Ledgers.Id>,
          _,
          []
        )
          == Bool.pick(
            List<&2, Ledgers.Id>,
            Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
            x <> r,
            Maybe.default(
              &2,
              List<&2, Ledgers.Id>,
              Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2)),
              []
            )
          ): List<&2, Ledgers.Id>
      }
      Wait.pick(
        Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
        x <> r,
        Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
      )

# Wait.wait for any requests ys that waited on the line c
def Wait.wait.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain,
  +ys: List<&2, Ledgers.Id>
) -> {
  Replicas.Wait.of(~Basics.Ask.machine(), 
    Replicas.Wait.set(~Basics.Ask.machine(), s, c, List.append(&2, Ledgers.Id, ys, [j])),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, ys, [j]),
      Replicas.Wait.of(~Basics.Ask.machine(), s, c2)
    ): List<&2, Ledgers.Id>
}:
  match ys:
    case Nil{}:
      Wait.set.of(s, c, j, [], c2)
    case Con{x, r}:
      Wait.set.of(s, c, x, List.append(&2, Ledgers.Id, r, [j]), c2)

# the requests that wait on a line, after one more waits on the line c
def Wait.wait(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain
) -> {
  Replicas.Wait.of(~Basics.Ask.machine(), 
    Replicas.State.wait(~Basics.Ask.machine(), s, c, j),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j]),
      Replicas.Wait.of(~Basics.Ask.machine(), s, c2)
    ): List<&2, Ledgers.Id>
}:
  Wait.wait.at(s, c, j, c2, Replicas.Wait.of(~Basics.Ask.machine(), s, c))

# Wait.keeps once it is known whether the line has the key of c (b)
def Wait.keeps.if(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  +b: Bool,
  eb: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == b: Bool},
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      List.append(&2, Ledgers.Id, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j]),
      Replicas.Wait.of(~Basics.Ask.machine(), s, c2)
    ),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_left(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j], i, (
          %Wait.keyed(s, c2, c, Key.same(c2, c)(eb)): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))
    case False{}:
      h

# a request that waits on a line waits there after one more waits on a line
def Wait.keeps(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.State.wait(~Basics.Ask.machine(), s, c, j), c2),
    i
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.State.wait(~Basics.Ask.machine(), s, c, j), c2),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j]),
      Replicas.Wait.of(~Basics.Ask.machine(), s, c2)
    ),
    Wait.wait(s, c, j, c2)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
  Wait.keeps.if(
    s,
    c,
    j,
    c2,
    i,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    h
  )

# a list of one is a member of itself
def Contains.one(
  j: Ledgers.Id
) -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [j], j) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Ledgers.Id.is_eq(j, j),
    True{},
    Ledgers.Id.is_eq_refl(j)
  ): {List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [], j), _) == True{}: Bool}
  {==}

# a request waits on its line once it waits there
def Wait.adds(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +j: Ledgers.Id
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.State.wait(~Basics.Ask.machine(), s, c, j), c),
    j
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.State.wait(~Basics.Ask.machine(), s, c, j), c),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j]),
      Replicas.Wait.of(~Basics.Ask.machine(), s, c)
    ),
    Wait.wait(s, c, j, c)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, j) == True{}: Bool}
  %Equal.sym(
    Bool,
    Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
    True{},
    Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
  ): {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Bool.pick(
        List<&2, Ledgers.Id>,
        _,
        List.append(&2, Ledgers.Id, Replicas.Wait.of(~Basics.Ask.machine(), s, c), [j]),
        Replicas.Wait.of(~Basics.Ask.machine(), s, c)
      ),
      j
    )
      == True{}: Bool
  }
  Shared.List.contains_right(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), s, c),
    [j],
    j,
    Contains.one(j)
  )

# a request that waits on a line waits there after a request arrives
def Arrive.waits(
  +s: Replicas.Node<Basics.Ask>,
  +j: Ledgers.Id,
  +q: Basics.Ask,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.Node.arrive(~Stepping.Ask.kernel(), s, j, q), c2),
    i
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      %Wait.same(
        s,
        Replicas.Node.start(~Stepping.Ask.kernel(), s, j, os),
        c2,
        Start.with.waiting(
          s,
          j,
          Replicas.Owner.names(os),
          Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Basics.Ask.On{r, l, ch}:
      Wait.keeps(Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), Replicas.Line.chain(r, l), j, c2, i, (
          %Wait.same(s, Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), c2, Follow.new.waiting(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

# one of two nodes, on each of which the request i waits on the line c2
def Contains.when(
  +b: Bool,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  -c2: Ledgers.Chain,
  -i: Ledgers.Id,
  hx: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), x, c2), i) == True{}: Bool},
  hy: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), y, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y), c2),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that waits on a line waits there after more requests arrive
def Take.asks.waits(
  +cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>,
  +c2: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), s, c2), i) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), Replicas.Take.asks(~Stepping.Ask.kernel(), cs, old, s), c2),
    i
  )
    == True{}: Bool
}:
  match cs:
    case Nil{}:
      h => h
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      +h => Take.asks.waits(
        rest,
        old,
        Shared.Bool.when(
          Replicas.Node<Basics.Ask>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, j, q),
          u => s
        ),
        c2,
        i
      )(
        Contains.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, j, q),
          s,
          c2,
          i,
          Arrive.waits(s, j, q, c2, i, h),
          h
        )
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.waits(rest, old, s, c2, i)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.waits(rest, old, s, c2, i)
    case Con{Cells.Many{}, rest}:
      Take.asks.waits(rest, old, s, c2, i)

# a new request among the cells that a node takes in waits on its line
def Take.asks.adds(
  +pre: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  post: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  time: String,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  ch: Basics.Change
) -> {
  Ledgers.State.get(
    ~Basics.Ask,
    old,
    Ledgers.Slot.ask(i)
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Replicas.Wait.of(~Basics.Ask.machine(), 
      Replicas.Take.asks(~Stepping.Ask.kernel(), 
        List.append(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          pre,
          Cells.One{Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}} <> post
        ),
        old,
        s
      ),
      Replicas.Line.chain(r, l)
    ),
    i
  )
    == True{}: Bool
}:
  match pre:
    case Nil{}:
      e => Take.asks.waits(
        post,
        old,
        Shared.Bool.when(
          Replicas.Node<Basics.Ask>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, Basics.Ask.On{r, l, ch}),
          u => s
        ),
        Replicas.Line.chain(r, l),
        i
      )(
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i)), None{}, e): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Replicas.Wait.of(~Basics.Ask.machine(), Shared.Bool.when(Replicas.Node<Basics.Ask>, Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _), u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, Basics.Ask.On{r, l, ch}), u => s), Replicas.Line.chain(r, l)), i) == True{}: Bool}
        Wait.adds(Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), Replicas.Line.chain(r, l), i))
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      e => Take.asks.adds(
        rest,
        post,
        old,
        Shared.Bool.when(
          Replicas.Node<Basics.Ask>,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Replicas.Node.arrive(~Stepping.Ask.kernel(), s, j, q),
          u => s
        ),
        i,
        time,
        r,
        l,
        ch
      )(e)
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)
    case Con{Cells.Many{}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)

def Spec.Node.take_holds(s, t, k, e):
  +sent = Replicas.Node.reads(~Basics.Ask.machine(), t)
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  es => eb =>
    Ledgers.State.one_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l1)),
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.take(~Stepping.Ask.kernel(), s, t)),
      k,
      e
    )(Take.tail(s, t))(
      %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l1)), l1, Led.led(s, l1)): {Ledgers.State.get(~Basics.Ask, _, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
      Equal.trans(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, l1, k), Ledgers.State.get(~Basics.Ask, sent, k), Some{Cells.One{e}}, Ledgers.State.take_get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent, k)(eb), es))

def Spec.Node.take_waits(s, t, i, time, r, l, ch):
  +sent = Replicas.Node.reads(~Basics.Ask.machine(), t)
  l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Replicas.Take.asks(~Stepping.Ask.kernel(), cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  cell = {
    Cells.One{
      Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}
    }: Cells.Cell<Ledgers.Entry<Basics.Ask>>
  }
  es => eb =>
    %Wait.same(
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Replicas.Line.chain(r, l),
      Each.waiting(List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
    ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
    %Equal.sym(
      List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
      cs,
      List.append(
        &2,
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        Tries.Trie.before(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
        cell <> Tries.Trie.after(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i))
      ),
      Tries.Trie.values_around(
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        sent,
        Ledgers.Slot.ask(i),
        cell
      )(es)
    ): {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Replicas.Wait.of(~Basics.Ask.machine(), Replicas.Take.asks(~Stepping.Ask.kernel(), _, Replicas.State.ledger(~Basics.Ask.machine(), s), s1), Replicas.Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }
    Take.asks.adds(
      Tries.Trie.before(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
      Tries.Trie.after(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
      Replicas.State.ledger(~Basics.Ask.machine(), s),
      s1,
      i,
      time,
      r,
      l,
      ch
    )(eb)
