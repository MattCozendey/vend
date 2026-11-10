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

# a place added to a version vector only grows a node
def Grown.vector.add(
  w: Replicas.Work<Basics.Ask>,
  +c: Ledgers.Chain,
  +p: Replicas.Place
) -> {Replicas.Work.after(~Basics.Ask.machine(), Replicas.Work.state(~Basics.Ask.machine(), w), Judging.Vector.add(w, c, p)) == True{}: Bool}:
  match w:
    case Replicas.Work{+s, +h}:
      Replicas.Grown.when(~Basics.Ask.machine(), 
        s,
        Replicas.Place.covered(Basics.Node.vector(s, h, c), p),
        Some{Replicas.Work{s, h}},
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.vector(c), Replicas.Place.code(p)),
        Replicas.Grows.refl(~Basics.Ask.machine(), s),
        Replicas.Set.grows(~Basics.Ask.machine(), s, h, Basics.Key.vector(c), Replicas.Place.code(p))
      )

# an entry added to a version vector only grows a node
def Grown.vector.add.if(
  +w: Replicas.Work<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Place>
) -> {Replicas.Work.after(~Basics.Ask.machine(), Replicas.Work.state(~Basics.Ask.machine(), w), Judging.Vector.add.if(w, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grown.self(~Basics.Ask.machine(), w)
    case Some{+p}:
      Replicas.Grown.when(~Basics.Ask.machine(), 
        Replicas.Work.state(~Basics.Ask.machine(), w),
        Ledgers.Chain.is_eq(Replicas.Place.chain(p), c),
        Some{w},
        Judging.Vector.add(w, Replicas.Place.chain(p), p),
        Replicas.Grown.self(~Basics.Ask.machine(), w),
        Grown.vector.add(w, Replicas.Place.chain(p), p)
      )

# the entries added to a version vector only grow a node
def Grown.vector.adds(
  +s: Replicas.Node<Basics.Ask>,
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Replicas.Work.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Vector.adds(bs, c, m)) == True{}: Bool}:
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
        Replicas.Grown.bind(~Basics.Ask.machine(), 
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
  Replicas.Work.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Vector.joined(s0, c, v, m)) == True{}: Bool}:
  e => Replicas.Grown.bind(~Basics.Ask.machine(), 
    s,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s0, Replicas.Node.root_of(~Basics.Ask.machine(), s0, Some{v})),
      c,
      m
    ),
    w => Judging.Vector.add.if(w, c, Replicas.Node.place(~Basics.Ask.machine(), s0, v)),
    Grown.vector.adds(
      s,
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s0, Replicas.Node.root_of(~Basics.Ask.machine(), s0, Some{v})),
      c,
      m
    )(e),
    +w => Grown.vector.add.if(w, c, Replicas.Node.place(~Basics.Ask.machine(), s0, v))
  )

# what a merge keeps of a resource only grows a node
def Grown.merge.put(
  +f: Ledgers.Id,
  +n: Resources.Name,
  +o: Maybe<&2, Ropes.Root>,
  p: Judging.Pick,
  +w: Replicas.Work<Basics.Ask>
) -> {Replicas.Work.after(~Basics.Ask.machine(), Replicas.Work.state(~Basics.Ask.machine(), w), Judging.Merge.put(f, n, o, p, w)) == True{}: Bool}:
  match p:
    case Judging.Pick.Take{m}:
      Replicas.Grown.set(~Basics.Ask.machine(), w, Basics.Key.res(n), Basics.Res.code(m))
    case Judging.Pick.Make{+x}:
      Replicas.Grown.bind(~Basics.Ask.machine(), 
        Replicas.Work.state(~Basics.Ask.machine(), w),
        Replicas.Work.keep(~Basics.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(x))),
        w2 => Replicas.Work.set(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(n),
          Basics.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(x))})
        ),
        Replicas.Grown.keep(~Basics.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(x))),
        w2 => Replicas.Grown.set(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(n),
          Basics.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(x))})
        )
      )
    case Judging.Pick.Clash{}:
      Replicas.Grown.bind(~Basics.Ask.machine(), 
        Replicas.Work.state(~Basics.Ask.machine(), w),
        Replicas.Work.set(~Basics.Ask.machine(), w, Basics.Key.res(n), Basics.Res.code(o)),
        y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), Judging.Clash.code(f)),
        Replicas.Grown.set(~Basics.Ask.machine(), w, Basics.Key.res(n), Basics.Res.code(o)),
        y => Replicas.Grown.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), Judging.Clash.code(f))
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
) -> {Replicas.Work.after(~Basics.Ask.machine(), Replicas.Work.state(~Basics.Ask.machine(), w), Judging.Merge.one(s0, f, n, b, o, t, w)) == True{}: Bool}:
  Replicas.Grown.with(~Basics.Ask.machine(), 
    Judging.Pick,
    Replicas.Work.state(~Basics.Ask.machine(), w),
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
  Replicas.Work.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Merge.all(s0, f, ns, hb, ho, ht, m)) == True{}: Bool}:
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
        Replicas.Grown.bind(~Basics.Ask.machine(), 
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
          +w => Replicas.Grown.with(~Basics.Ask.machine(), 
            Maybe<&2, Ropes.Root>,
            Replicas.Work.state(~Basics.Ask.machine(), w),
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
            +b => Replicas.Grown.with(~Basics.Ask.machine(), 
              Maybe<&2, Ropes.Root>,
              Replicas.Work.state(~Basics.Ask.machine(), w),
              Basics.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Basics.Ask>,
                Basics.Res.find(s0, ht, n),
                x => Judging.Merge.one(s0, f, n, b, o, x, w)
              ),
              +o => Replicas.Grown.with(~Basics.Ask.machine(), 
                Maybe<&2, Ropes.Root>,
                Replicas.Work.state(~Basics.Ask.machine(), w),
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
) -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Merge.work(s, c, from, h)) == True{}: Bool}:
  Grown.vector.joined(
    s,
    s,
    c,
    from,
    Judging.Merge.all(
      s,
      from,
      Judging.Merge.names(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Judging.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    )
  )(
    Grown.merge.all(
      s,
      s,
      from,
      Judging.Merge.names(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Judging.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    )(Replicas.Grows.refl(~Basics.Ask.machine(), s))
  )

# the trees of a move are on a node that grew
def Grown.move.work(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +to: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Move.work(s, c, to, h)) == True{}: Bool}:
  Grown.vector.joined(
    s,
    s,
    c,
    to,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})}}
    )
  )(
    Grown.vector.adds(
      s,
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})}}
    )(Replicas.Grows.refl(~Basics.Ask.machine(), s))
  )

# the trees of a resolve are on a node that grew
def Grown.resolve.work(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +m: Maybe<&2, Ropes.Root>
) -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Resolve.work(s, h, n, m)) == True{}: Bool}:
  Replicas.Grown.bind(~Basics.Ask.machine(), 
    s,
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), []),
    Replicas.Set.grows(~Basics.Ask.machine(), s, h, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Grown.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), [])
  )

# the trees of a group are on a node that grew
def Grown.group.work(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  +ms: List<&2, Basics.Member>
) -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Group.work(s, h, g, ms)) == True{}: Bool}:
  Replicas.Grown.bind(~Basics.Ask.machine(), 
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
    Replicas.Set.grows(~Basics.Ask.machine(), s, h, Basics.Key.group(g), Basics.Members.code(ms, [])),
    +w => Replicas.Grown.when(~Basics.Ask.machine(), 
      Replicas.Work.state(~Basics.Ask.machine(), w),
      List.contains(~String, ~String.eq, Judging.Group.names(s, h), g),
      Some{w},
      Replicas.Work.set(~Basics.Ask.machine(), 
        w,
        Basics.Key.groups(),
        Ledgers.Owners.code(g <> Judging.Group.names(s, h), [])
      ),
      Replicas.Grown.self(~Basics.Ask.machine(), w),
      Replicas.Grown.set(~Basics.Ask.machine(), w, Basics.Key.groups(), Ledgers.Owners.code(g <> Judging.Group.names(s, h), []))
    )
  )

# the first tree of a branch is on a node that grew
def Grown.make.branch(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Ledgers.Id>
) -> {Replicas.Work.after(~Basics.Ask.machine(), s, Judging.Make.branch(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{+v}:
      Grown.vector.joined(
        s,
        s,
        c,
        v,
        Some{Replicas.Work{s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{v})}}
      )(Replicas.Grows.refl(~Basics.Ask.machine(), s))

# the first tip of a new branch is on a node that grew
def Grown.make.first(
  +s: Replicas.Node<Basics.Ask>,
  start: Maybe<&2, Replicas.Work<Basics.Ask>>,
  +os: List<&2, String>
) -> {
  Replicas.Work.after(~Basics.Ask.machine(), s, start) == True{}: Bool
} -> {Replicas.Made.after(~Basics.Ask.machine(), s, Judging.Make.first(start, os)) == True{}: Bool}:
  match start:
    case None{}:
      e => {==}
    case Some{Replicas.Work{+s2, +h}}:
      e =>
        +t = {Replicas.Tip{h, None{}, 0, os}: Replicas.Tip}
        Replicas.Grown.made.put(~Basics.Ask.machine(), 
          s,
          t,
          Replicas.Work.keep(~Basics.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)])
        )(
          Replicas.Work.after.trans(~Basics.Ask.machine(), 
            s,
            s2,
            Replicas.Work.keep(~Basics.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)]),
            e,
            Replicas.Grown.keep(~Basics.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)])
          )
        )

# a verdict after a verdict holds a node that grew
def Verdict.then(
  s: Replicas.Node<Basics.Ask>,
  +m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Basics.Ask>>,
  hk: {Replicas.Verdict.after(~Basics.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.then(m, k)) == True{}: Bool}:
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
  hk: {Replicas.Verdict.after(~Basics.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.when(b, k)) == True{}: Bool}:
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
  hk: {Replicas.Verdict.after(~Basics.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.whole(b, k)) == True{}: Bool}:
  match b:
    case True{}:
      hk
    case False{}:
      {==}

# the verdict on a write holds a node that grew
def Verdict.write(
  +s: Replicas.Node<Basics.Ask>,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Basics.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.write(s, n, base, c, h)) == True{}: Bool}:
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
          Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
          Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
      Replicas.Verdict.with(~Basics.Ask.machine(), 
        Maybe<&2, Ropes.Root>,
        s,
        Basics.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Basics.Ask>,
          Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
        +a => Replicas.Verdict.with(~Basics.Ask.machine(), 
          Maybe<&2, Ropes.Root>,
          s,
          Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
          +b => Replicas.Verdict.with(~Basics.Ask.machine(), 
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
              Replicas.Verdict.take(~Basics.Ask.machine(), 
                s,
                Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              )(Replicas.Set.grows(~Basics.Ask.machine(), s, h, Basics.Key.res(n), Basics.Res.code(m)))
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
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.resolve(s, r, b, k, n, c, h)) == True{}: Bool}:
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
      Replicas.Verdict.with(~Basics.Ask.machine(), 
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
        +open => Replicas.Verdict.with(~Basics.Ask.machine(), 
          Maybe<&2, Ropes.Root>,
          s,
          Judging.Content.find(s, n, c),
          m => Judging.Judge.when(open, x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m))),
          +m => Verdict.when(
            s,
            open,
            x => Replicas.Work.take(~Basics.Ask.machine(), Judging.Resolve.work(s, h, n, m)),
            Replicas.Verdict.take(~Basics.Ask.machine(), s, Judging.Resolve.work(s, h, n, m))(Grown.resolve.work(s, h, n, m))
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
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Own.change(s, r, l, g, at, os, h)) == True{}: Bool}:
  Verdict.then(
    s,
    Judging.Own.takes(s, r, l, g, at, os, h),
    u => Replicas.Work.take(~Basics.Ask.machine(), 
      Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.owner(), Codes.Code.text(g, []))
    ),
    Replicas.Verdict.take(~Basics.Ask.machine(), 
      s,
      Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.owner(), Codes.Code.text(g, []))
    )(Replicas.Set.grows(~Basics.Ask.machine(), s, h, Basics.Key.owner(), Codes.Code.text(g, [])))
  )

# the verdict on a change holds a node that grew from the node that judged it
def Verdict.change(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Basics.Change,
  +h: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>
) -> {Replicas.Verdict.after(~Basics.Ask.machine(), s, Judging.Judge.change(s, r, l, c, h, os)) == True{}: Bool}:
  match l c:
    case None{} Basics.Change.Group{+g, +ms}:
      Verdict.when(
        s,
        Bool.not(Judging.Group.loops.any(s, h, g, ms)),
        u => Replicas.Work.take(~Basics.Ask.machine(), Judging.Group.work(s, h, g, ms)),
        Replicas.Verdict.take(~Basics.Ask.machine(), s, Judging.Group.work(s, h, g, ms))(Grown.group.work(s, h, g, ms))
      )
    case None{} Basics.Change.Key{+n, +k}:
      Replicas.Verdict.take(~Basics.Ask.machine(), 
        s,
        Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Replicas.Machine.seal(Basics.Ask.machine())(n), Hashes.Hash.code(k, []))
      )(Replicas.Set.grows(~Basics.Ask.machine(), s, h, Replicas.Machine.seal(Basics.Ask.machine())(n), Hashes.Hash.code(k, [])))
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
          Judging.Whole.both(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h))
        ),
        Verdict.whole(
          s,
          Judging.Whole.both(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)),
          Replicas.Verdict.take(~Basics.Ask.machine(), 
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
          Judging.Whole.both(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h))
        ),
        Verdict.whole(
          s,
          Judging.Whole.both(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})),
          v => Replicas.Work.take(~Basics.Ask.machine(), Judging.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)),
          Replicas.Verdict.take(~Basics.Ask.machine(), 
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

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Replicas.Run<Basics.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Branch.ready(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{False{}}:
      Replicas.Stale.grows(~Basics.Ask.machine(), r, i)
    case Some{True{}}:
      Replicas.After.when(~Basics.Ask.machine(), 
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Node.root_of(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), at)
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
        Replicas.Branch.made.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Branch.new(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Some{x}}:
      Replicas.Stale.grows(~Basics.Ask.machine(), r, i)
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.on.of(r, i, st, l, ch, w)) == True{}: Bool}:
  match w:
    case Stepping.Route.Mark{a}:
      Replicas.Mark.grows(~Basics.Ask.machine(), r, i, a)
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
      Replicas.Judged.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  On.of.grows(r, i, st, l, ch, Stepping.Route.of(l, ch))

# a request only grows a run's node
def Change.grows(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Basics.Ask
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Stepping.Step.change(r, c, i, q)) == True{}: Bool}:
  match q:
    case Basics.Ask.Start{os}:
      Replicas.Stale.grows(~Basics.Ask.machine(), r, i)
    case Basics.Ask.On{+st, +l, ch}:
      Replicas.After.when(~Basics.Ask.machine(), 
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        On.grows(r, i, st, l, ch),
        Replicas.Stale.grows(~Basics.Ask.machine(), r, i)
      )

# a request that the node holds or not only grows a run's node
def Asked.grows(
  r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.asked(~Stepping.Ask.kernel(), r, c, i, a)) == True{}: Bool}:
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.fresh(~Stepping.Ask.kernel(), r, c, i, o)) == True{}: Bool}:
  match o:
    case Some{x}:
      Replicas.After.self(~Basics.Ask.machine(), r)
    case None{}:
      Asked.grows(r, c, i, Replicas.Node.asked(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), i))

# one request of a step only grows a run's node
def One.grows(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i)) == True{}: Bool}:
  Fresh.grows(r, c, i, Replicas.Line.out(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Replicas.Run.tip(~Basics.Ask.machine(), r), i))

# the requests of a step only grow a run's node
def All.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Replicas.Run<Basics.Ask>>
) -> {
  Replicas.Run.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.grows(
        s,
        c,
        rest,
        Maybe.bind(&2, Replicas.Run<Basics.Ask>, Replicas.Run<Basics.Ask>, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i))
      )(Replicas.After.bind(~Basics.Ask.machine(), s, m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i), h, r => One.grows(r, c, i)))

# a step only grows a node: its run is on a node that keeps every entry
def Run.grows(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  qs: List<&2, Ledgers.Id>
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Replicas.Run{s, t}})(Replicas.Grows.refl(~Basics.Ask.machine(), s))

# the run of the requests that can run is on a node that grew
def Some.grows(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Replicas.Run<Basics.Ask>
) -> {
  Replicas.Run.after(~Basics.Ask.machine(), 
    Replicas.Run.state(~Basics.Ask.machine(), r),
    Some{Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Step.some(~Stepping.Ask.kernel(), c, qs, r))}
  )
    == True{}: Bool
}:
  match qs:
    case Nil{}:
      Replicas.After.self(~Basics.Ask.machine(), r)
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
        Replicas.Add.run(~Basics.Ask.machine(), Maybe.is_some(&2, Replicas.Run<Basics.Ask>, m), i, Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2))
      ): {Replicas.Run.after(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), Some{_}) == True{}: Bool}
      Replicas.After.trans(~Basics.Ask.machine(), 
        Replicas.Run.state(~Basics.Ask.machine(), r),
        Replicas.Run.state(~Basics.Ask.machine(), r2),
        Some{Replicas.Picked.run(~Basics.Ask.machine(), Replicas.Step.some(~Stepping.Ask.kernel(), c, rest, r2))},
        Replicas.Default.run.grows(~Basics.Ask.machine(), r, m)(One.grows(r, c, i)),
        Some.grows(c, rest, r2)
      )

# the run of the plan of an owner that proposes freely is on a node that grew
def Plan.own.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  t: Replicas.Tip,
  -from: List<&2, String>
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.own(~Stepping.Ask.kernel(), s, c, t, from))) == True{}: Bool}:
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.copy(~Stepping.Ask.kernel(), s, c, t, th, m, from))) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Replicas.Plan.when.grows(~Basics.Ask.machine(), 
        s,
        List.all.if(u => Replicas.Cast.all_mine(~Stepping.Ask.kernel(), s, qs), Replicas.Root.same(before, th)),
        Replicas.Plan{qs, Replicas.Plan.fit(~Basics.Ask.machine(), after, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)), from},
        Replicas.Plan{[], None{}, []},
        Replicas.Plan.fit.grows(~Basics.Ask.machine(), s, after, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs))(Run.grows(s, c, t, qs)),
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
  Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.later(~Stepping.Ask.kernel(), s, c, w, t, th, os, from, m))) == True{}: Bool
}:
  match m:
    case None{}:
      Replicas.Plan.when.grows(~Basics.Ask.machine(), 
        s,
        Replicas.Owners.major(os, from),
        Replicas.Plan.own(~Stepping.Ask.kernel(), s, c, t, from),
        Replicas.Plan{[], None{}, []},
        Plan.own.grows(s, c, t, from),
        {==}
      )
    case Some{Ledgers.Last{r, v}}:
      Replicas.Plan.when.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.lead(~Stepping.Ask.kernel(), s, c, w, t, th, os))) == True{}: Bool}:
  Replicas.Plan.when.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.follow(~Stepping.Ask.kernel(), s, c, w, t, th, os, m))) == True{}: Bool}:
  match m:
    case Some{Ledgers.Act.Vote{+v, from}}:
      Replicas.Plan.when.grows(~Basics.Ask.machine(), 
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
) -> {Replicas.Run.after(~Basics.Ask.machine(), s, Replicas.Plan.run(~Basics.Ask.machine(), Replicas.Plan.of(~Stepping.Ask.kernel(), n, s, c, w, t, th, os, turn))) == True{}: Bool}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Replicas.Plan.when.grows(~Basics.Ask.machine(), 
        s,
        String.eq(p, n),
        Replicas.Plan.lead(~Stepping.Ask.kernel(), s, c, w, t, th, os),
        Replicas.Plan.follow(~Stepping.Ask.kernel(), s, c, w, t, th, os, Replicas.Cast.act(~Basics.Ask.machine(), s, w, p)),
        Plan.lead.grows(s, c, w, t, th, os),
        Plan.follow.grows(s, c, w, t, th, os, Replicas.Cast.act(~Basics.Ask.machine(), s, w, p))
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
  Replicas.Grows.when(~Basics.Ask.machine(), 
    s,
    Replicas.Cast.may(~Basics.Ask.machine(), n, s, w, t, Replicas.Plan.asks(~Basics.Ask.machine(), p)),
    Replicas.Cast.put(~Stepping.Ask.kernel(), n, w, th, Replicas.Plan.asks(~Basics.Ask.machine(), p), Replicas.Plan.from(~Basics.Ask.machine(), p), Replicas.Plan.run(~Basics.Ask.machine(), p), s),
    s,
    Replicas.Cast.put.grows(~Stepping.Ask.kernel(), 
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
    Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Cast.round(~Stepping.Ask.kernel(), n, s1, c, next, th, t)
      )(
        Replicas.Round.join.grows(~Stepping.Ask.kernel(), n, s, c, next, Replicas.Tip.owners(t))
      )(Cast.round.grows(n, s1, c, next, th, t))
    case Replicas.Head{r, b, next, th} None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)

# Node.cast only grows a node, once the head m is known
def Cast.head.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Cast.head(~Stepping.Ask.kernel(), n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{+h}:
      Cast.at.grows(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# a node's ballot only grows it
def Cast.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  Cast.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

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
      Replicas.Grows.when(~Basics.Ask.machine(), 
        s,
        Replicas.Root.same(before, th),
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, b, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Replicas.Advance.ran.grows(~Basics.Ask.machine(), 
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)
        )(Run.grows(s, c, t, qs)),
        Replicas.Grows.refl(~Basics.Ask.machine(), s)
      )
    case Replicas.Head{r, b, next, th} None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case 1n+p None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case 1n+(+p) Some{+h}:
      +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
      +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
      Replicas.Grows.when(~Basics.Ask.machine(), 
        s,
        Replicas.Heads.level(Some{h}, m1),
        s1,
        Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
        Advance.at.grows(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h)),
        Replicas.Grows.trans(~Basics.Ask.machine(), 
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
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s1,
    s3
  )(
    Advances.grows(4294967295n, s, c)
  )(Replicas.Grows.trans(~Basics.Ask.machine(), s1, s2, s3)(Cast.grows(n, s1, c))(Advances.grows(4294967295n, s2, c)))

# what a node does on a line only grows it
def Step.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  +s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Step.head(~Stepping.Ask.kernel(), n, s1, c)
  )(Replicas.Open.at.grows(~Basics.Ask.machine(), s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.head.grows(n, s1, c))

# a pass to the next round only grows a node
def Pass.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  +s1 = Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
  )(Replicas.Pass.head.grows(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)))(Step.grows(n, s1, c))

# the first keys of a store are on a node that grew
def Firsts.after(
  +s: Replicas.Node<Basics.Ask>,
  os: List<&2, Replicas.Owner>,
  +m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> {
  Replicas.Work.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Basics.Ask.machine(), s, Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, m)) == True{}: Bool}:
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
          w => Replicas.Work.set(~Basics.Ask.machine(), w, Replicas.Machine.seal(Basics.Ask.machine())(n), Hashes.Hash.code(k, []))
        )
      )(Replicas.Work.set.after(~Basics.Ask.machine(), s, m, Replicas.Machine.seal(Basics.Ask.machine())(n), Hashes.Hash.code(k, []))(e))

# a store that starts only grows a node
def Start.grows(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Replicas.Owner>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.start(~Stepping.Ask.kernel(), s, i, os)) == True{}: Bool}:
  Replicas.Start.with.grows(~Basics.Ask.machine(), 
    s,
    i,
    Replicas.Owner.names(os),
    Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Replicas.Grows.refl(~Basics.Ask.machine(), s)))

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
      Replicas.Grows.to(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Replicas.Led.waits(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Replicas.Follow.new.grows(~Basics.Ask.machine(), s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))
      )

# a new request only grows a node
def Ask.new.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.ask.new(~Stepping.Ask.kernel(), n, s, e, q)) == True{}: Bool}:
  +i = Replicas.Envelope.of(e)
  +c = Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(q))
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
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
  )(
    Replicas.Grows.led(~Basics.Ask.machine(), 
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
  )(Replicas.Grows.trans(~Basics.Ask.machine(), s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c)))

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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case None{}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Replicas.Node.ask.new(~Stepping.Ask.kernel(), 
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )(
        Replicas.Grows.to(~Basics.Ask.machine(), 
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1)
      )(
        Replicas.Grows.when(~Basics.Ask.machine(), 
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
          s,
          Arrive.grows(s, i, q),
          Replicas.Grows.refl(~Basics.Ask.machine(), s)
        )
      )(Take.asks.grows(rest, old, s1))
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(rest, old, s)

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
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
  )(
    Replicas.Grows.led(~Basics.Ask.machine(), 
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
    Replicas.Grows.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
    )(
      Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
    )(Replicas.Each.grows(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2))
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
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s1,
    s2,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2)
  )(
    Take.asks.grows(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  )(Replicas.Each.grows(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2))

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
      %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), b, l1)), l1, Replicas.Led.led(~Basics.Ask.machine(), b, l1)): {Ledgers.State.data(~Basics.Ask, _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Con{+c, +rest}:
      +s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1)
      )(Step.grows(n, s, c))(Steps.grows(n, rest, s1))

# an adoption only grows a node, once the request m is known
def Adopt.ask.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Request<Basics.Ask>>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Adopt.ask(~Stepping.Ask.kernel(), n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Request{e, q}}:
      Ask.grows(n, s, e, q)

# an adoption only grows a node, once the head m of the line is known
def Adopt.head.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Adopt.head(~Stepping.Ask.kernel(), n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.grows(n, s, Replicas.Kernel.follow(Stepping.Ask.kernel())(s)(r)(b))

# the adoption of a line only grows a node
def Adopt.at.grows(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)) == True{}: Bool}:
  Adopt.head.grows(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{c}:
      Adopt.at.grows(n, s, c)

# the adoption of each of some lines only grows a node
def Adopts.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Con{+c, +rest}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c))
      )(Adopt.at.grows(n, s, c))(Adopts.grows(n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)))

# more rounds of a sync, grows
def More.grows(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Sync.more(~Stepping.Ask.kernel(), f, n, cs, k, bs, pd, s)) == True{}: Bool}:
  match f:
    case 0n:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case 1n+(+p):
      Replicas.Grows.when(~Basics.Ask.machine(), 
        s,
        Replicas.Lines.level(~Basics.Ask.machine(), cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Replicas.Sync.more(~Stepping.Ask.kernel(), 
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Replicas.Grows.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        )(Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s))(Steps.grows(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        Replicas.Grows.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Replicas.Sync.more(~Stepping.Ask.kernel(), 
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )
        )(
          Replicas.Grows.trans(~Basics.Ask.machine(), 
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          )(Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s))(Steps.grows(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)))
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
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.sync(~Stepping.Ask.kernel(), n, s, t)) == True{}: Bool}:
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  +s3 = Replicas.Sync.more(~Stepping.Ask.kernel(), 
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
    s2
  )
  Replicas.Grows.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3)
  )(
    Take.grows(s, t)
  )(
    Replicas.Grows.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3)
    )(
      Steps.grows(n, cs, s1)
    )(
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s2,
        s3,
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3)
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
  +c = Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(q))
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
  Replicas.Slot.held_kept(~Basics.Ask.machine(), 
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    k,
    Replicas.Grows.trans(~Basics.Ask.machine(), 
      s0,
      s1,
      Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c)
    )(Arrive.grows(s0, i, q))(Step.grows(n, s1, c))
  )(
    %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), s0), l0, Replicas.Led.led(~Basics.Ask.machine(), s, l0)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, Ledgers.State.get(~Basics.Ask, _, k)) == True{}: Bool}
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
          %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))), Replicas.State.ledger(~Basics.Ask.machine(), s), Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))): {Ledgers.State.get(~Basics.Ask, _, Ledgers.Slot.ask(Replicas.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
          em)
      )

def Spec.Node.ask_once(n, m, s, e, q, e2, q2):
  h =>
    +a = Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q)
    Replicas.Ask.once.at(~Stepping.Ask.kernel(), 
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Stepping.Branch.ready(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{False{}}:
      Replicas.Add.kept(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
    case Some{True{}}:
      Replicas.Keeps.when(~Basics.Ask.machine(), 
        k2,
        v,
        r,
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Node.root_of(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), at)
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
        Replicas.Branch.made.kept(~Basics.Ask.machine(), 
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Stepping.Branch.new(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Some{x}}:
      Replicas.Add.kept(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Stepping.Step.on.of(r, i, st, l, ch, w)):
  match w:
    case Stepping.Route.Mark{a}:
      hr => Replicas.Mark.kept(~Basics.Ask.machine(), r, i, a, k2, v)(hr)
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
      hr => Replicas.Judged.kept(~Basics.Ask.machine(), 
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Stepping.Step.on(r, i, st, l, ch)):
  On.of.kept(r, i, st, l, ch, Stepping.Route.of(l, ch), k2, v)

# a request keeps each key of a run's log, other than the owners and the count
def Change.kept(
  +r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Basics.Ask,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Stepping.Step.change(r, c, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      hr => Replicas.Add.kept(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)(hr)
    case Basics.Ask.On{+st, +l, ch}:
      Replicas.Keeps.when(~Basics.Ask.machine(), 
        k2,
        v,
        r,
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        On.kept(r, i, st, l, ch, k2, v),
        Replicas.Add.kept(~Basics.Ask.machine(), r, Replicas.Log.out(i), Replicas.Out.words(Replicas.Out.Stale{}), k2, v)
      )

# a request that the node holds or not keeps each key of a run's log
def Asked.kept(
  r: Replicas.Run<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Replicas.Step.asked(~Stepping.Ask.kernel(), r, c, i, a)):
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Some{r}) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Replicas.Step.fresh(~Stepping.Ask.kernel(), r, c, i, o)):
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
) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, m) -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Replicas.Step.all(~Stepping.Ask.kernel(), c, qs, m)):
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
        Replicas.Keeps.bind(~Basics.Ask.machine(), 
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
} -> Replicas.Run.Keeps(~Basics.Ask.machine(), k2, v, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)):
  match t:
    case Replicas.Tip{c0, l, n, os}:
      h => All.kept(c, qs, Some{Replicas.Run{s, Replicas.Tip{c0, l, n, os}}}, k2, v)(h)

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# a node's ballot keeps its logs
def Cast.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c)):
  Replicas.Kept.same(~Basics.Ask.machine(), 
    s,
    Replicas.Node.cast(~Stepping.Ask.kernel(), n, s, c),
    Cast.grows(n, s, c),
    Replicas.Cast.head.heads(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
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
      +em => +et => Replicas.Kept.when(~Basics.Ask.machine(), 
        Replicas.Root.same(before, th),
        s,
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Replicas.Advance.ran.kept(~Basics.Ask.machine(), 
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
        Replicas.Kept.refl(~Basics.Ask.machine(), s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => Replicas.Kept.refl(~Basics.Ask.machine(), s)

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
      em => et => Replicas.Kept.refl(~Basics.Ask.machine(), s)
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
      em => Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case 1n+p None{}:
      em => Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Replicas.Kept.when(~Basics.Ask.machine(), 
          Replicas.Heads.level(Some{h}, m1),
          s,
          s1,
          Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
          Advance.at.kept(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Replicas.Kept.trans(~Basics.Ask.machine(), 
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
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s1,
    s3,
    Advances.kept(4294967295n, s, c),
    Replicas.Kept.trans(~Basics.Ask.machine(), s1, s2, s3, Cast.kept(n, s1, c), Advances.kept(4294967295n, s2, c))
  )

# what a node does on a line keeps the logs
def Step.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)):
  s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Step.head(~Stepping.Ask.kernel(), n, s1, c),
    Replicas.Open.at.kept(~Basics.Ask.machine(), s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c)):
  +s1 = Replicas.Pass.head(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Replicas.Kept.same(~Basics.Ask.machine(), 
      s,
      s1,
      Replicas.Pass.head.grows(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      Replicas.Pass.head.heads(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
    ),
    Step.kept(n, s1, c)
  )

# a store that starts keeps the logs
def Start.kept(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Replicas.Owner>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.start(~Stepping.Ask.kernel(), s, i, os)):
  Replicas.Start.with.kept(~Basics.Ask.machine(), 
    s,
    i,
    Replicas.Owner.names(os),
    Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Replicas.Grows.refl(~Basics.Ask.machine(), s)))

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
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Replicas.Follow.new.kept(~Basics.Ask.machine(), s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Replicas.Kept.same(~Basics.Ask.machine(), 
          s1,
          Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s1,
            s1,
            Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Replicas.Led.waits(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Replicas.Grows.refl(~Basics.Ask.machine(), s1)
          ),
          Replicas.Heads.waits(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i)
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
  c = Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(q))
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
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Replicas.Kept.same(~Basics.Ask.machine(), 
      s,
      s0,
      Replicas.Grows.led(~Basics.Ask.machine(), 
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
      Replicas.Heads.led(~Basics.Ask.machine(), s, l0)
    ),
    Replicas.Kept.trans(~Basics.Ask.machine(), s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c), Arrive.kept(s0, i, q), Step.kept(n, s1, c))
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
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case None{}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Replicas.Node.ask.new(~Stepping.Ask.kernel(), 
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        ),
        Replicas.Kept.same(~Basics.Ask.machine(), 
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Replicas.Grows.refl(~Basics.Ask.machine(), s)
          ),
          Replicas.Heads.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
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
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
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
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1),
        Replicas.Kept.when(~Basics.Ask.machine(), 
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
          s,
          Arrive.kept(s, i, q),
          Replicas.Kept.refl(~Basics.Ask.machine(), s)
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
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
    Replicas.Kept.same(~Basics.Ask.machine(), 
      s,
      s1,
      Replicas.Grows.led(~Basics.Ask.machine(), 
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
      Replicas.Heads.led(~Basics.Ask.machine(), s, l1)
    ),
    Replicas.Kept.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Take.asks.kept(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
      Replicas.Kept.same(~Basics.Ask.machine(), 
        s2,
        Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
        Replicas.Each.grows(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2),
        Replicas.Each.heads(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
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
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Con{+c, rest}:
      s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Replicas.Kept.trans(~Basics.Ask.machine(), s, s1, Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1), Step.kept(n, s, c), Steps.kept(n, rest, s1))

# an adoption keeps the logs, once the request m is known
def Adopt.ask.kept(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Request<Basics.Ask>>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Adopt.ask(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Request{e, q}}:
      Ask.kept(n, s, e, q)

# an adoption keeps the logs, once the head m of the line is known
def Adopt.head.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Adopt.head(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.kept(n, s, Replicas.Kernel.follow(Stepping.Ask.kernel())(s)(r)(b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)):
  Adopt.head.kept(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Some{c}:
      Adopt.at.kept(n, s, c)

# the adoption of each of some lines keeps the logs
def Adopts.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s)):
  match cs:
    case Nil{}:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Con{+c, rest}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)),
        Adopt.at.kept(n, s, c),
        Adopts.kept(n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c))
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
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Sync.more(~Stepping.Ask.kernel(), f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case 1n+(p):
      Replicas.Kept.when(~Basics.Ask.machine(), 
        Replicas.Lines.level(~Basics.Ask.machine(), cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        s,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Replicas.Sync.more(~Stepping.Ask.kernel(), 
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Replicas.Kept.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Replicas.Kept.same(~Basics.Ask.machine(), 
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Each.heads(~Stepping.Ask.kernel(), k, bs, pd, s)
          ),
          Steps.kept(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Replicas.Kept.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Replicas.Sync.more(~Stepping.Ask.kernel(), 
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          Replicas.Kept.trans(~Basics.Ask.machine(), 
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
            Replicas.Kept.same(~Basics.Ask.machine(), 
              s,
              Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
              Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s),
              Replicas.Each.heads(~Stepping.Ask.kernel(), k, bs, pd, s)
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
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.sync(~Stepping.Ask.kernel(), n, s, t)):
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  s3 = Replicas.Sync.more(~Stepping.Ask.kernel(), 
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
    s2
  )
  Replicas.Kept.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
    Take.kept(s, t),
    Replicas.Kept.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
      Steps.kept(n, cs, s1),
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s2,
        s3,
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
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
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Some{+c}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )(
        Replicas.Grows.to(~Basics.Ask.machine(), 
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Replicas.Grows.refl(~Basics.Ask.machine(), s)
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
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Some{c}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Replicas.Kept.same(~Basics.Ask.machine(), 
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Replicas.Grows.refl(~Basics.Ask.machine(), s)
          ),
          Replicas.Heads.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.kept(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Replicas.Deed<Basics.Ask>
) -> {Replicas.Node.grows(~Basics.Ask.machine(), s, Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)) == True{}: Bool}:
  match ev:
    case Replicas.Deed.Ask{+e, +q}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q)))
      )(
        Ask.grows(n, s, e, q)
      )(
        Adopt.at.grows(
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q))
        )
      )
    case Replicas.Deed.Take{t}:
      Take.grows(s, t)
    case Replicas.Deed.Sync{t}:
      Sync.grows(n, s, t)
    case Replicas.Deed.Keep{b}:
      Replicas.Grows.keep(~Basics.Ask.machine(), s, Ropes.Put.nodes(Replicas.Bytes.rope(b)))
    case Replicas.Deed.Consent{+i}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )(
        Consent.grows(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )(Adopt.maybe.grows(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)))
    case Replicas.Deed.Pass{+c}:
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )(Pass.grows(n, s, c))(Adopt.at.grows(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c))

def Spec.Node.after_grows(n, evs, s):
  match evs:
    case Nil{}:
      Replicas.Grows.refl(~Basics.Ask.machine(), s)
    case Con{+ev, +rest}:
      +s1 = Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Node.after(~Stepping.Ask.kernel(), n, rest, s1)
      )(Does.grows(n, s, ev))(Spec.Node.after_grows(n, rest, s1))

# what a node does keeps the logs
def Does.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Replicas.Deed<Basics.Ask>
) -> Replicas.Node.Keeps(~Basics.Ask.machine(), s, Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)):
  match ev:
    case Replicas.Deed.Ask{+e, +q}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), 
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q))
        ),
        Ask.kept(n, s, e, q),
        Adopt.at.kept(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q)))
      )
    case Replicas.Deed.Take{t}:
      Take.kept(s, t)
    case Replicas.Deed.Sync{t}:
      Sync.kept(n, s, t)
    case Replicas.Deed.Keep{+b}:
      Replicas.Kept.same(~Basics.Ask.machine(), 
        s,
        Replicas.Node.keep(~Basics.Ask.machine(), s, b),
        Replicas.Grows.keep(~Basics.Ask.machine(), s, Ropes.Put.nodes(Replicas.Bytes.rope(b))),
        Replicas.Heads.led(~Basics.Ask.machine(), 
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Replicas.Bytes.rope(b)),
            Replicas.State.ledger(~Basics.Ask.machine(), s)
          )
        )
      )
    case Replicas.Deed.Consent{+i}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Consent.kept(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Adopt.maybe.kept(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )
    case Replicas.Deed.Pass{+c}:
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c),
        Pass.kept(n, s, c),
        Adopt.at.kept(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )
    case Replicas.Deed.Pass{c}:
      Pass.kept(n, s, c)

def Spec.Node.after_keeps(n, evs, s):
  match evs:
    case Nil{}:
      Replicas.Kept.refl(~Basics.Ask.machine(), s)
    case Con{+ev, rest}:
      s1 = Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)
      Replicas.Kept.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Node.after(~Stepping.Ask.kernel(), n, rest, s1),
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
  p: Replicas.Place,
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
    u => Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.vector(c), Replicas.Place.code(p))
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Replicas.Set.kept(~Basics.Ask.machine(), 
        s,
        h,
        Basics.Key.vector(c),
        Replicas.Place.code(p),
        Basics.Key.res(n),
        v,
        Vector.apart(c, n),
        hget
      )

# a new entry of the version vector keeps a resource
def Vector.add.reads(
  w: Replicas.Work<Basics.Ask>,
  +c: Ledgers.Chain,
  +p: Replicas.Place,
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
        Replicas.Place.covered(Basics.Node.vector(s, h, c), p),
        hget
      )

# Vector.add.if keeps a resource, once it is known whether the place is of
# the line (b)
def Vector.add.if.reads.at(
  w: Replicas.Work<Basics.Ask>,
  +p: Replicas.Place,
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
    u => Judging.Vector.add(w, Replicas.Place.chain(p), p)
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Vector.add.reads(w, Replicas.Place.chain(p), p, n, v)(hget)

# an entry of the version vector, if any, keeps a resource
def Vector.add.if.reads(
  w: Replicas.Work<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Place>,
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
        Ledgers.Chain.is_eq(Replicas.Place.chain(p), c),
        hget
      )

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
        Replicas.Reads.bind(~Basics.Ask.machine(), 
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
  hm => Replicas.Reads.bind(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    v,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{x})),
      c,
      m
    ),
    w => Judging.Vector.add.if(w, c, Replicas.Node.place(~Basics.Ask.machine(), s, x))
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{x})),
      c,
      m,
      n,
      v
    )(hm)
  )(+w => hw => Vector.add.if.reads(w, c, Replicas.Node.place(~Basics.Ask.machine(), s, x), n, v)(hw))

def Spec.Move.reads(s, c, to, h, n, v):
  hget => Vector.joined.reads(
    s,
    c,
    to,
    Judging.Vector.adds(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})}}
    ),
    n,
    v
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{to})}},
      n,
      v
    )(hget)
  )

# Whole merges
# ------------
# A merge sets the key of each resource that it merges. A set of another key
# keeps what a key reads, so what the merge of one resource takes is what the
# whole merge gives for it (Spec.Merge.keeps).

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
                Replicas.Text.same(
                  t1,
                  t2,
                  Equal.cong(
                    List<&2, U32>,
                    List<&2, U32>,
                    Replicas.Words.rest,
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

# the key of a clash is not the key of a resource
def Clash.apart(
  m: Resources.Name,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.clash(m), Basics.Key.res(n)) == False{}: Bool}:
  {==}

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
      Replicas.Set.kept.work(~Basics.Ask.machine(), w, Basics.Key.res(m), Basics.Res.code(mm), Basics.Key.res(n), v, hne)
    case Judging.Pick.Make{y}:
      hget => Replicas.Reads.bind(~Basics.Ask.machine(), 
        Basics.Key.res(n),
        v,
        Replicas.Work.keep(~Basics.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(y))),
        w2 => Replicas.Work.set(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(y))})
        )
      )(
        Replicas.Keep.reads(~Basics.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(y)), Basics.Key.res(n), v)(hget)
      )(
        w2 => hw => Replicas.Set.kept.work(~Basics.Ask.machine(), 
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(y))}),
          Basics.Key.res(n),
          v,
          hne
        )(hw)
      )
    case Judging.Pick.Clash{}:
      hget => Replicas.Reads.bind(~Basics.Ask.machine(), 
        Basics.Key.res(n),
        v,
        Replicas.Work.set(~Basics.Ask.machine(), w, Basics.Key.res(m), Basics.Res.code(o2)),
        y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(m), Judging.Clash.code(f))
      )(
        Replicas.Set.kept.work(~Basics.Ask.machine(), w, Basics.Key.res(m), Basics.Res.code(o2), Basics.Key.res(n), v, hne)(hget)
      )(
        y => hy => Replicas.Set.kept.work(~Basics.Ask.machine(), 
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
  hget => Replicas.Reads.with(~Basics.Ask.machine(), 
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
    b => Replicas.Reads.with(~Basics.Ask.machine(), 
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
      +o => Replicas.Reads.with(~Basics.Ask.machine(), 
        Maybe<&2, Ropes.Root>,
        Basics.Key.res(n),
        v,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )(
        x => Replicas.Reads.with(~Basics.Ask.machine(), 
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
  Replicas.Set.read(~Basics.Ask.machine(), w, Basics.Key.res(n), Basics.Res.code(x))

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
          Replicas.Name.sound(m1, n)(es)
        ): Replicas.Work.Reads(~Basics.Ask.machine(), 
          Basics.Key.res(n),
          Basics.Res.code(x),
          Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, _, w))
        )
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep)
    case False{}:
      hm => Replicas.Reads.bind(~Basics.Ask.machine(), 
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
        %Equal.sym(Resources.Name, m1, n, Replicas.Name.sound(m1, n)(es)): Replicas.Work.Reads(~Basics.Ask.machine(), Basics.Key.res(n), Basics.Res.code(x), Maybe.bind(&2, Replicas.Work<Basics.Ask>, Replicas.Work<Basics.Ask>, m, w => Merge.step(s, f, hb, ho, ht, _, w)))
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
      Judging.Merge.names(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Judging.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    ),
    n,
    Basics.Res.code(x)
  )(
    Merge.all.takes(
      s,
      from,
      Judging.Merge.names(s, h, Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Judging.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Basics.Ask.machine(), s, Some{from}),
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
  Replicas.Reads.bind(~Basics.Ask.machine(), 
    Basics.Key.res(n),
    Basics.Res.code(m),
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), [])
  )(
    Replicas.Set.read(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
  )(
    y => hy => Replicas.Set.kept.work(~Basics.Ask.machine(), 
      y,
      Basics.Key.clash(n),
      [],
      Basics.Key.res(n),
      Basics.Res.code(m),
      Clash.apart(n, n)
    )(hy)
  )

def Spec.Resolve.shuts(s, h, n, m):
  Replicas.Reads.with(~Basics.Ask.machine(), 
    Replicas.Work<Basics.Ask>,
    Basics.Key.clash(n),
    [],
    Replicas.Work.set(~Basics.Ask.machine(), Replicas.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Replicas.Work.set(~Basics.Ask.machine(), y, Basics.Key.clash(n), [])
  )(y => Replicas.Set.read(~Basics.Ask.machine(), y, Basics.Key.clash(n), []))

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
        Replicas.Count.full(
          Codes.Code.length(w),
          Codes.Code.chars(w, Codes.Code.count(Codes.Code.length(q), Codes.Code.chars(q, [])))
        )

# Outcomes
# --------
# A step gives each of its requests an outcome (Spec.Step.run_outs), and only
# the requests of a step leave the requests that wait (Spec.Wait.left_keeps).

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
      Replicas.Stale.outs(~Basics.Ask.machine(), r, i)
    case Some{True{}}:
      Replicas.Outs.when(~Basics.Ask.machine(), 
        Trees.Tree.whole(
          ~Replicas.Node<Basics.Ask>,
          ~Replicas.Store.fetch(~Basics.Ask.machine()),
          Replicas.Run.state(~Basics.Ask.machine(), r),
          Replicas.Node.root_of(~Basics.Ask.machine(), Replicas.Run.state(~Basics.Ask.machine(), r), at)
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
        Replicas.Branch.made.outs(~Basics.Ask.machine(), 
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
      Replicas.Stale.outs(~Basics.Ask.machine(), r, i)
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
      Replicas.Mark.outs(~Basics.Ask.machine(), r, i, a)
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
      Replicas.Judged.outs(~Basics.Ask.machine(), 
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
      Replicas.Stale.outs(~Basics.Ask.machine(), r, i)
    case Basics.Ask.On{st, l, ch}:
      Replicas.Outs.when(~Basics.Ask.machine(), 
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Basics.Ask.machine(), r, i),
        i,
        On.outs(r, i, st, l, ch),
        Replicas.Stale.outs(~Basics.Ask.machine(), r, i)
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
      Replicas.Outs.self(~Basics.Ask.machine(), r, i, ws)(eg)
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
      h => Replicas.Outs.of(~Basics.Ask.machine(), 
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
        )(Replicas.Keeps.self(~Basics.Ask.machine(), r, Replicas.Log.out(i), v)(eg))
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
          Replicas.All.none(~Stepping.Ask.kernel(), c, qs)
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
        Replicas.Outs.all(~Basics.Ask.machine(), m, r => Replicas.Step.one(~Stepping.Ask.kernel(), r, c, i), i, r => One.outs(r, c, i)))
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

def Spec.Wait.left_keeps(ws, done, i):
  match ws:
    case Nil{}:
      e => hd => e
    case Con{j, rs}:
      e => +hd => Replicas.Left.keeps.at(
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

def Spec.Plan.follow_allowed(s, c, w, t, th, os, v, from):
  Replicas.Follow.allowed.at(~Stepping.Ask.kernel(), s, c, t, th, v, from, Replicas.Vote.allowed(~Basics.Ask.machine(), s, w, os, v, from))

# Agreement
# ---------

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
            v => Replicas.Verdict.took(~Basics.Ask.machine(), v),
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
            v => Replicas.Verdict.took(~Basics.Ask.machine(), v),
            Judging.Judge.refuse(),
            Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
            e
          )
        )
      )

def Spec.Judge.write_reads(s, n, base, c, h, h2, s3, m):
  e => ec =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Replicas.Node.get(~Basics.Ask.machine(), s3, h2, Basics.Key.res(n)),
      Some{Basics.Res.code(m)},
      Replicas.Set.reads(~Basics.Ask.machine(), s, h, Basics.Key.res(n), Basics.Res.code(m), Replicas.Node.set(~Basics.Ask.machine(), s, h, Basics.Key.res(n), Basics.Res.code(m)), h2, s3)(
        {==}
      )(
        Replicas.With.took(~Basics.Ask.machine(), 
          Maybe<&2, Ropes.Root>,
          Basics.Res.find(s, h, n),
          a1 => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Basics.Ask>,
            Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
          +a => Replicas.With.took(~Basics.Ask.machine(), 
            Maybe<&2, Ropes.Root>,
            Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
                Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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
                    Basics.Res.find(s, Replicas.Node.root_of(~Basics.Ask.machine(), s, base), n),
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

def Spec.Seal.accept_fits(s, b, c, s2):
  ec => ea => Replicas.Accept.fits.if(~Basics.Ask.machine(), 
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

def Spec.Seal.fits_own(seed, x, last, k, n, f):
  Shared.List.all.if_both(
    Replicas.Prev.same(last, last),
    u => Ledgers.Ballot.sealed(Seals.Seal.public(seed), Ledgers.Ballot.make(seed, x, last, k))
  )(Replicas.Prev.refl(last))(Ledgers.Ballot.sealed_make(seed, x, last, k))

# Histories
# ---------

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
        +z => Replicas.Moved.grows(~Basics.Ask.machine(), a, u, c, z, x, r, g)
      )

def Spec.Node.advance_at(s, c, h):
  +eh => +hl =>
    %Equal.sym(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), Replicas.Node.advance(~Stepping.Ask.kernel(), s, c), c),
      Some{Replicas.Head.step(h, Replicas.Advance.vote(~Basics.Ask.machine(), s, c, h))},
      Replicas.Advance.decided(~Stepping.Ask.kernel(), s, c, h)(eh)(hl)
    ): Exists(Nat, q => {Replicas.Line.at(~Basics.Ask.machine(), [q], s, c, h) == _: Maybe<&2, Replicas.Head>})
    Replicas.Advance.at.one(~Basics.Ask.machine(), s, c, h, Replicas.Advance.vote(~Basics.Ask.machine(), s, c, h))({==})(
      %Replicas.Advance.decided(~Stepping.Ask.kernel(), s, c, h)(eh)(hl): {Replicas.Heads.level(Some{h}, _) == False{}: Bool}
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
        == Replicas.Root.bytes(~Basics.Ask.machine(), s, Judging.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
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

def Spec.Line.at_agrees(u, c, rules, rs1, rs2, a, b, h, x, y):
  ga => gb => el => ea => eb =>
    Replicas.At.same(~Basics.Ask.machine(), 
      rs1,
      rs2,
      u,
      c,
      h,
      x,
      y
    )(
      Replicas.Rounds.ones(~Basics.Ask.machine(), ~u, ~c, ~rules, List.length(&2, Nat, rs1))
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
    Replicas.Grows.trans(~Basics.Ask.machine(), 
      s2,
      s4,
      Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
    )(
      Replicas.Grows.to(~Basics.Ask.machine(), 
        s2,
        s3,
        s4,
        Replicas.Led.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
        Replicas.Put.grew(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)], s3, e)
      )
    )(Replicas.Cast.seal.grows(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)))

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
    Replicas.Tip.at.grows(~Basics.Ask.machine(), 
      s3,
      Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)),
      Replicas.Tip.hash(t2),
      t2,
      Replicas.Grows.trans(~Basics.Ask.machine(), 
        s3,
        s4,
        Replicas.Cast.seal(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n))
      )(
        Replicas.Grows.to(~Basics.Ask.machine(), 
          s3,
          s3,
          s4,
          Replicas.Led.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
          Replicas.Grows.refl(~Basics.Ask.machine(), s3)
        )
      )(Replicas.Cast.seal.grows(~Stepping.Ask.kernel(), s4, w, n, a0, Replicas.Seal.chain(~Stepping.Ask.kernel(), s4, Replicas.Where.store(w), n)))
    )(Replicas.Tip.put.at(~Basics.Ask.machine(), s2, t2, s3)(e))

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
    x => Some{Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(Replicas.Asked.ask(~Basics.Ask.machine(), x)))},
    x => Some{Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(Replicas.Asked.ask(~Basics.Ask.machine(), x)))},
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
  Replicas.Node.out(~Basics.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
} -> {Replicas.Node.out(~Basics.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Replicas.Out,
    Replicas.Node.chain_of(~Basics.Ask.machine(), a, i),
    Replicas.Node.chain_of(~Basics.Ask.machine(), b, i),
    c => Replicas.Chain.out(~Basics.Ask.machine(), a, c, i),
    c => Replicas.Chain.out(~Basics.Ask.machine(), b, c, i),
    o,
    c => Chain.of.kept(a, b, i, c, g),
    +c => Replicas.Chain.out.kept(~Basics.Ask.machine(), a, b, c, i, o, hk)
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
  Replicas.Out.on(~Basics.Ask.machine(), a, c, o) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Replicas.Out.on(~Basics.Ask.machine(), b, c, o) == Some{x}: Maybe<&2, Replicas.Version>}:
  match o:
    case Replicas.Out.Stale{}:
      e => e
    case Replicas.Out.Taken{n}:
      Replicas.Chain.version.kept(~Basics.Ask.machine(), a, b, c, n, x, hk)

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
  Replicas.Chain.made(~Basics.Ask.machine(), a, c, v) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Replicas.Chain.made(~Basics.Ask.machine(), b, c, v) == Some{x}: Maybe<&2, Replicas.Version>}:
  Shared.Maybe.bind_kept(
    Replicas.Out,
    Replicas.Version,
    Replicas.Chain.out(~Basics.Ask.machine(), a, c, v),
    Replicas.Chain.out(~Basics.Ask.machine(), b, c, v),
    o => Replicas.Out.on(~Basics.Ask.machine(), a, c, o),
    o => Replicas.Out.on(~Basics.Ask.machine(), b, c, o),
    x,
    o => Replicas.Chain.out.kept(~Basics.Ask.machine(), a, b, c, v, o, hk1),
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
  Replicas.Node.made(~Basics.Ask.machine(), a, v) == Some{x}: Maybe<&2, Replicas.Version>
} -> {Replicas.Node.made(~Basics.Ask.machine(), b, v) == Some{x}: Maybe<&2, Replicas.Version>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Replicas.Version,
    Replicas.Node.chain_of(~Basics.Ask.machine(), a, v),
    Replicas.Node.chain_of(~Basics.Ask.machine(), b, v),
    +c => Replicas.Chain.made(~Basics.Ask.machine(), a, c, v),
    +c => Replicas.Chain.made(~Basics.Ask.machine(), b, c, v),
    x,
    c => Chain.of.kept(a, b, v, c, g),
    +c => Chain.made.kept(a, b, c, v, x, hk1, hk2)
  )

def Spec.Node.out_final(n, evs, s, i, o):
  Out.kept(
    s,
    Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s),
    i,
    o,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Node.made_final(n, evs, s, v, x):
  Made.kept(
    s,
    Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s),
    v,
    x,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Chain.version_final(n, evs, s, c, k, x):
  Replicas.Chain.version.kept(~Basics.Ask.machine(), s, Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s), c, k, x, Spec.Node.after_keeps(n, evs, s))

def Spec.Chain.mark_final(n, evs, s, c, m, v):
  Replicas.Chain.mark.kept(~Basics.Ask.machine(), s, Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s), c, m, v, Spec.Node.after_keeps(n, evs, s))

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
  Replicas.Node.out(~Basics.Ask.machine(), a, i) == oa: Maybe<&2, Replicas.Out>
} -> (
  @o: Replicas.Out -> {
    Replicas.Node.out(~Basics.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Basics.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Reading.Answer.follows(
    Reading.Answer.of(a, i, q, Replicas.Node.out(~Basics.Ask.machine(), a, i)),
    Some{Reading.Answer.of(b, i, q, Replicas.Node.out(~Basics.Ask.machine(), b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Basics.Ask.machine(), a, i),
          None{},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Replicas.Node.out(~Basics.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Replicas.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Basics.Ask.machine(), a, i),
          Some{Replicas.Out.Stale{}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Replicas.Node.out(~Basics.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Basics.Ask.machine(), b, i),
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
          Replicas.Node.out(~Basics.Ask.machine(), a, i),
          Some{Replicas.Out.Taken{k}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Replicas.Node.out(~Basics.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Basics.Ask.machine(), b, i),
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
    Replicas.Node.out(~Basics.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Basics.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
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
      Of.follows(a, b, i, Basics.Ask.On{st, l, ch}, Replicas.Node.out(~Basics.Ask.machine(), a, i))({==})(ho)

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
    Replicas.Node.out(~Basics.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Basics.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
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
    Replicas.Node.out(~Basics.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Basics.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
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
          Replicas.Cell.kept.eq(~Basics.Ask.machine(), c, mb)(ek)
        ): {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, _)) == True{}: Bool}
        %e: {Follows.opt(_, Reading.Answer.held(b, i, q, Some{c})) == True{}: Bool}
        Held.follows(a, b, i, q, Some{c}, ho)

def Spec.Node.answer_follows(n, evs, s, e, q, x):
  Answer.follows.at(
    s,
    Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s),
    Replicas.Envelope.of(e),
    q,
    x,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e))),
    Ledgers.State.get(
      ~Basics.Ask,
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s)),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    ),
    o => Out.kept(
      s,
      Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s),
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
      Replicas.State.ledger(~Basics.Ask.machine(), Replicas.Node.after(~Stepping.Ask.kernel(), n, evs, s)),
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
        Replicas.Path.set.no(~Basics.Ask.machine(), a, c, c2, h0, Replicas.Key.same(c2, c)(ebs), nh, t0, ra)
      )
    case False{}:
      Reach.same(
        a,
        Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
        c2,
        h0,
        Replicas.Grows.to(~Basics.Ask.machine(), 
          a,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Replicas.Led.head(~Basics.Ask.machine(), b0, c, hd),
          g
        ),
        Replicas.Head.other(~Basics.Ask.machine(), a, b0, c, hd, c2, eh, ebs),
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
                        Replicas.Head.keyed(~Basics.Ask.machine(), s, c2, c, ek),
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
                      Replicas.In.key(~Basics.Ask.machine(), n, c2, c, h, q, ek),
                      Replicas.In.grows(~Basics.Ask.machine(), s, n, c, h, q, v, gn)(ein)
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
        Replicas.Key.same(c2, c)(ebs),
        Replicas.Grows.to(~Basics.Ask.machine(), 
          s,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Replicas.Led.head(~Basics.Ask.machine(), b0, c, hd),
          g
        ),
        Replicas.Head.this(~Basics.Ask.machine(), b0, c, hd, c2, ebs),
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
        Replicas.Grows.to(~Basics.Ask.machine(), 
          s,
          b0,
          Replicas.State.head(~Basics.Ask.machine(), b0, c, hd),
          Replicas.Led.head(~Basics.Ask.machine(), b0, c, hd),
          g
        ),
        Replicas.Head.other(~Basics.Ask.machine(), s, b0, c, hd, c2, eh, ebs),
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
    Replicas.Grows.to(~Basics.Ask.machine(), s, x, b0, Replicas.Led.wait(~Basics.Ask.machine(), x, c, ws), Replicas.Grows.back(~Basics.Ask.machine(), s, s3, g3)),
    Equal.trans(
      Tries.Trie<Replicas.Head>,
      Replicas.State.heads(~Basics.Ask.machine(), s),
      Replicas.State.heads(~Basics.Ask.machine(), x),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      Replicas.Heads.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
      Replicas.Heads.wait(~Basics.Ask.machine(), x, c, ws)
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
      e2 => Replicas.Path.refl(~Basics.Ask.machine(), s)
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
        Replicas.Grows.trans(~Basics.Ask.machine(), 
          s,
          s2,
          s3
        )(g2)(Replicas.Put.grew(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)], s3, e2)),
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
      Replicas.Path.refl(~Basics.Ask.machine(), s)

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
  Replicas.Run.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => Replicas.Path.refl(~Basics.Ask.machine(), s)
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
      em => et => ed => Replicas.Path.when(~Basics.Ask.machine(), 
        Replicas.Root.same(before, th),
        s,
        Replicas.Advance.ran(~Basics.Ask.machine(), s, c, r, br, next, after, qs, Replicas.Step.run(~Stepping.Ask.kernel(), s, c, t, qs)),
        s,
        Replicas.Scan.elim(~Basics.Ask.machine(), 
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
        Replicas.Path.refl(~Basics.Ask.machine(), s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => ed => Replicas.Path.refl(~Basics.Ask.machine(), s)

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
      em => et => Replicas.Path.refl(~Basics.Ask.machine(), s)
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
    Replicas.Cast.head.heads(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
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
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case 1n+p None{}:
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Replicas.Advance.at(~Stepping.Ask.kernel(), s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Replicas.Path.when(~Basics.Ask.machine(), 
          Replicas.Heads.level(Some{h}, m1),
          s,
          s1,
          Replicas.Advances.at(~Stepping.Ask.kernel(), p, s1, c, m1),
          Advance.at.path(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Replicas.Path.trans(~Basics.Ask.machine(), 
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
  Replicas.Path.trans(~Basics.Ask.machine(), 
    s,
    s1,
    s3,
    Advances.path(4294967295n, s, c),
    Replicas.Path.trans(~Basics.Ask.machine(), s1, s2, s3, Cast.path(n, s1, c), Advances.path(4294967295n, s2, c))
  )

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
        Replicas.Grows.refl(~Basics.Ask.machine(), s),
        {==},
        Replicas.Held.not(~Basics.Ask.machine(), s, c, Some{Replicas.Head{r, Some{b}, n, None{}}}, em)
      )
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case None{}:
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)

# what a node does on a line is on the paths
def Step.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)):
  s1 = Replicas.Node.open(~Basics.Ask.machine(), s, c)
  Replicas.Path.trans(~Basics.Ask.machine(), 
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
  Replicas.Path.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Path.same(
      s,
      s1,
      Replicas.Pass.head.grows(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      Replicas.Pass.head.heads(~Stepping.Ask.kernel(), n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
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
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Head{+r, +b, +n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        h,
        Replicas.Grows.refl(~Basics.Ask.machine(), s),
        {==},
        Replicas.Held.not(~Basics.Ask.machine(), s, c, Some{Replicas.Head{r, b, n, None{}}}, em)
      )
    case None{}:
      em => Path.set(s, s, c, h, Replicas.Grows.refl(~Basics.Ask.machine(), s), {==}, Replicas.Held.not(~Basics.Ask.machine(), s, c, None{}, em))

# a first head on a node that grew from a, which grew from s, is on the paths
def Start.head.path(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  g: {Replicas.Node.grows(~Basics.Ask.machine(), s, a) == True{}: Bool}
) -> {
  Replicas.State.after(~Basics.Ask.machine(), a, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Start.head(~Basics.Ask.machine(), s, m, c, h)):
  match m:
    case None{}:
      e => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Replicas.Path.trans(~Basics.Ask.machine(), 
          s,
          x,
          Replicas.State.first(~Basics.Ask.machine(), x, c, h),
          Path.same(
            s,
            x,
            Replicas.Grows.back(~Basics.Ask.machine(), s, s3, Replicas.Grows.trans(~Basics.Ask.machine(), s, a, s3)(g)(e)),
            Replicas.Heads.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
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
  Replicas.Work.after(~Basics.Ask.machine(), s, m) == True{}: Bool
} -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Start.with(~Basics.Ask.machine(), s, i, os, m)):
  match m:
    case None{}:
      e => Replicas.Path.refl(~Basics.Ask.machine(), s)
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
        )(Replicas.Put.grows(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t)]))

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
  )(Firsts.after(s, os, Some{Replicas.Work{s, None{}}})(Replicas.Grows.refl(~Basics.Ask.machine(), s)))

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
      em => Replicas.Path.refl(~Basics.Ask.machine(), s)
    case None{}:
      em => Path.set(
        s,
        s,
        Replicas.Line.chain(r, l),
        Replicas.Head{r, l, 0, None{}},
        Replicas.Grows.refl(~Basics.Ask.machine(), s),
        {==},
        Replicas.Held.not(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l), None{}, em)
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
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
        Follow.new.path(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Path.same(
          s1,
          Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s1,
            s1,
            Replicas.State.wait(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Replicas.Led.waits(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i),
            Replicas.Grows.refl(~Basics.Ask.machine(), s1)
          ),
          Replicas.Heads.waits(~Basics.Ask.machine(), s1, Replicas.Line.chain(r, l), i)
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
  c = Replicas.Arrival.chain(i, Replicas.Machine.arrival(Basics.Ask.machine())(q))
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
  Replicas.Path.trans(~Basics.Ask.machine(), 
    s,
    s0,
    Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c),
    Path.same(
      s,
      s0,
      Replicas.Grows.led(~Basics.Ask.machine(), 
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
      Replicas.Heads.led(~Basics.Ask.machine(), s, l0)
    ),
    Replicas.Path.trans(~Basics.Ask.machine(), s0, s1, Replicas.Node.step(~Stepping.Ask.kernel(), n, s1, c), Arrive.path(s0, i, q), Step.path(n, s1, c))
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
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case None{}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
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
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            Replicas.Grows.refl(~Basics.Ask.machine(), s)
          ),
          Replicas.Heads.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
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
      Replicas.Path.refl(~Basics.Ask.machine(), s)
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
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Take.asks(~Stepping.Ask.kernel(), rest, old, s1),
        Replicas.Path.when(~Basics.Ask.machine(), 
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Replicas.Node.arrive(~Stepping.Ask.kernel(), s, i, q),
          s,
          Arrive.path(s, i, q),
          Replicas.Path.refl(~Basics.Ask.machine(), s)
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
  Replicas.Path.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
    Path.same(
      s,
      s1,
      Replicas.Grows.led(~Basics.Ask.machine(), 
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
      Replicas.Heads.led(~Basics.Ask.machine(), s, l1)
    ),
    Replicas.Path.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Take.asks.path(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
      Path.same(
        s2,
        Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
        Replicas.Each.grows(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2),
        Replicas.Each.heads(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
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
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Con{+c, rest}:
      s1 = Replicas.Node.step(~Stepping.Ask.kernel(), n, s, c)
      Replicas.Path.trans(~Basics.Ask.machine(), s, s1, Replicas.Node.steps(~Stepping.Ask.kernel(), n, rest, s1), Step.path(n, s, c), Steps.path(n, rest, s1))

# an adoption is on the paths, once the request m is known
def Adopt.ask.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Request<Basics.Ask>>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Adopt.ask(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Request{e, q}}:
      Ask.path(n, s, e, q)

# an adoption is on the paths, once the head m of the line is known
def Adopt.head.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Adopt.head(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.path(n, s, Replicas.Kernel.follow(Stepping.Ask.kernel())(s)(r)(b))

# the adoption of a line is on the paths
def Adopt.at.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)):
  Adopt.head.path(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, is on the paths
def Adopt.maybe.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, s, m)):
  match m:
    case None{}:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{c}:
      Adopt.at.path(n, s, c)

# the adoption of each of some lines is on the paths
def Adopts.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s)):
  match cs:
    case Nil{}:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Con{+c, rest}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c)),
        Adopt.at.path(n, s, c),
        Adopts.path(n, rest, Replicas.Adopt.at(~Stepping.Ask.kernel(), n, s, c))
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
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Sync.more(~Stepping.Ask.kernel(), f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case 1n+(p):
      Replicas.Path.when(~Basics.Ask.machine(), 
        Replicas.Lines.level(~Basics.Ask.machine(), cs, s, Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))),
        s,
        Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
        Replicas.Sync.more(~Stepping.Ask.kernel(), 
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Replicas.Path.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Path.same(
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Each.heads(~Stepping.Ask.kernel(), k, bs, pd, s)
          ),
          Steps.path(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
        ),
        Replicas.Path.trans(~Basics.Ask.machine(), 
          s,
          Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
          Replicas.Sync.more(~Stepping.Ask.kernel(), 
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
          ),
          Replicas.Path.trans(~Basics.Ask.machine(), 
            s,
            Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
            Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s)),
            Path.same(
              s,
              Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s),
              Replicas.Each.grows(~Stepping.Ask.kernel(), k, bs, pd, s),
              Replicas.Each.heads(~Stepping.Ask.kernel(), k, bs, pd, s)
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
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.sync(~Stepping.Ask.kernel(), n, s, t)):
  +s1 = Replicas.Node.take(~Stepping.Ask.kernel(), s, t)
  +cs = Replicas.Sync.lines(~Basics.Ask.machine(), s, s1, t)
  +bs = Replicas.Ballots.of(~Basics.Ask.machine(), 
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Replicas.Node.steps(~Stepping.Ask.kernel(), n, cs, s1)
  s3 = Replicas.Sync.more(~Stepping.Ask.kernel(), 
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Replicas.Pending.of(bs),
    s2
  )
  Replicas.Path.trans(~Basics.Ask.machine(), 
    s,
    s1,
    Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
    Take.path(s, t),
    Replicas.Path.trans(~Basics.Ask.machine(), 
      s1,
      s2,
      Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
      Steps.path(n, cs, s1),
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s2,
        s3,
        Replicas.Node.adopts(~Stepping.Ask.kernel(), n, cs, s3),
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
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Some{c}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Replicas.Node.step(~Stepping.Ask.kernel(), n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Path.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          Replicas.Grows.to(~Basics.Ask.machine(), 
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Replicas.Led.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            Replicas.Grows.refl(~Basics.Ask.machine(), s)
          ),
          Replicas.Heads.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.path(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Replicas.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does is on the paths
def Does.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Replicas.Deed<Basics.Ask>
) -> Replicas.Node.On(~Basics.Ask.machine(), s, Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)):
  match ev:
    case Replicas.Deed.Ask{+e, +q}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), 
          n,
          Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q),
          Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q))
        ),
        Ask.path(n, s, e, q),
        Adopt.at.path(n, Replicas.Node.ask(~Stepping.Ask.kernel(), n, s, e, q), Replicas.Arrival.chain(Replicas.Envelope.of(e), Replicas.Machine.arrival(Basics.Ask.machine())(q)))
      )
    case Replicas.Deed.Take{t}:
      Take.path(s, t)
    case Replicas.Deed.Sync{t}:
      Sync.path(n, s, t)
    case Replicas.Deed.Keep{+b}:
      Path.same(
        s,
        Replicas.Node.keep(~Basics.Ask.machine(), s, b),
        Replicas.Grows.keep(~Basics.Ask.machine(), s, Ropes.Put.nodes(Replicas.Bytes.rope(b))),
        Replicas.Heads.led(~Basics.Ask.machine(), 
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Replicas.Bytes.rope(b)),
            Replicas.State.ledger(~Basics.Ask.machine(), s)
          )
        )
      )
    case Replicas.Deed.Consent{+i}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i),
        Replicas.Adopt.maybe(~Stepping.Ask.kernel(), n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Consent.path(n, s, i, Replicas.Node.chain_of(~Basics.Ask.machine(), s, i)),
        Adopt.maybe.path(n, Replicas.Node.consent(~Stepping.Ask.kernel(), n, s, i), Replicas.Node.chain_of(~Basics.Ask.machine(), s, i))
      )
    case Replicas.Deed.Pass{+c}:
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c),
        Replicas.Adopt.at(~Stepping.Ask.kernel(), n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c),
        Pass.path(n, s, c),
        Adopt.at.path(n, Replicas.Node.pass(~Stepping.Ask.kernel(), n, s, c), c)
      )
    case Replicas.Deed.Pass{c}:
      Pass.path(n, s, c)

def Spec.Node.after_on(n, evs, s):
  match evs:
    case Nil{}:
      Replicas.Path.refl(~Basics.Ask.machine(), s)
    case Con{+ev, rest}:
      s1 = Replicas.Node.does(~Stepping.Ask.kernel(), n, s, ev)
      Replicas.Path.trans(~Basics.Ask.machine(), 
        s,
        s1,
        Replicas.Node.after(~Stepping.Ask.kernel(), n, rest, s1),
        Does.path(n, s, ev),
        Spec.Node.after_on(n, rest, s1)
      )

# Waits
# -----
# A request that a node takes in waits on its line: a pending write goes with
# its writer to another node (Spec.Node.take_waits).

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
      %Replicas.Wait.same(~Basics.Ask.machine(), 
        s,
        Replicas.Node.start(~Stepping.Ask.kernel(), s, j, os),
        c2,
        Replicas.Start.with.waiting(~Basics.Ask.machine(), 
          s,
          j,
          Replicas.Owner.names(os),
          Replicas.Seal.firsts(~Stepping.Ask.kernel(), os, Some{Replicas.Work{s, None{}}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Basics.Ask.On{r, l, ch}:
      Replicas.Wait.keeps(~Basics.Ask.machine(), Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), Replicas.Line.chain(r, l), j, c2, i, (
          %Replicas.Wait.same(~Basics.Ask.machine(), s, Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), c2, Replicas.Follow.new.waiting(~Basics.Ask.machine(), s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

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
        Replicas.Contains.when(~Basics.Ask.machine(), 
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
        Replicas.Wait.adds(~Basics.Ask.machine(), Replicas.Node.follow(~Basics.Ask.machine(), s, r, l), Replicas.Line.chain(r, l), i))
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
      %Equal.sym(Ledgers.State(Basics.Ask), Replicas.State.ledger(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l1)), l1, Replicas.Led.led(~Basics.Ask.machine(), s, l1)): {Ledgers.State.get(~Basics.Ask, _, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
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
    %Replicas.Wait.same(~Basics.Ask.machine(), 
      s2,
      Replicas.Sealed.take(~Stepping.Ask.kernel(), bs, s2),
      Replicas.Line.chain(r, l),
      Replicas.Each.waiting(~Stepping.Ask.kernel(), List.length(&2, Ledgers.Ballot, bs), bs, Replicas.Pending.of(bs), s2)
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
