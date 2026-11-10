import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./spec.bend as Spec

# The proofs of the core's laws.

# Codes
# -----

# a member reads back
def Member.code_read(
  x: Spec.Member,
  r: List<&2, U32>
) -> {
  Spec.Member.code.read(
    Spec.Member.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Member>>
}:
  match x:
    case Spec.Member.Node{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.Node{a},
        n,
        r
      )
    case Spec.Member.Group{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.Group{a},
        n,
        r
      )

# the code of members
def Member.codec() -> Codes.Codec(Spec.Member):
  (Spec.Member.code, (Spec.Member.code.read, x => r => Member.code_read(x, r)))

# a content reads back
def Content.code_read(
  x: Spec.Content,
  r: List<&2, U32>
) -> {
  Spec.Content.code.read(
    Spec.Content.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Content>>
}:
  match x:
    case Spec.Content.Root{b}:
      Codes.Code.one_read(
        ~Ropes.Root,
        ~Spec.Content,
        ~Ropes.Root.codec(),
        a => Spec.Content.Root{a},
        b,
        r
      )
    case Spec.Content.Of{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Content,
        ~Ledgers.Id.codec(),
        a => Spec.Content.Of{a},
        v,
        r
      )

# the code of contents
def Content.codec() -> Codes.Codec(Spec.Content):
  (Spec.Content.code, (Spec.Content.code.read, x => r => Content.code_read(x, r)))

# a change reads back
def Change.code_read(
  x: Spec.Change,
  r: List<&2, U32>
) -> {
  Spec.Change.code.read(
    Spec.Change.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Change>>
}:
  match x:
    case Spec.Change.Branch{n, at}:
      Codes.Code.two_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        a => b => Spec.Change.Branch{a, b},
        n,
        at,
        r
      )
    case Spec.Change.Group{g, ms}:
      Codes.Code.two_read(
        ~String,
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => b => Spec.Change.Group{a, b},
        g,
        ms,
        r
      )
    case Spec.Change.Own{g, at, os}:
      Codes.Code.three_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => b => c => Spec.Change.Own{a, b, c},
        g,
        at,
        os,
        r
      )
    case Spec.Change.Write{n, base, c}:
      Codes.Code.three_read(
        ~Resources.Name,
        ~Maybe<&2, Ledgers.Id>,
        ~Spec.Content,
        ~Spec.Change,
        ~Resources.Name.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Content.codec(),
        a => b => c => Spec.Change.Write{a, b, c},
        n,
        base,
        c,
        r
      )
    case Spec.Change.Resolve{k, n, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Resources.Name,
        ~Spec.Content,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        ~Resources.Name.codec(),
        ~Content.codec(),
        a => b => c => Spec.Change.Resolve{a, b, c},
        k,
        n,
        c,
        r
      )
    case Spec.Change.Merge{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        a => Spec.Change.Merge{a},
        v,
        r
      )
    case Spec.Change.Move{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        a => Spec.Change.Move{a},
        v,
        r
      )
    case Spec.Change.Mark{m, n}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Spec.Change.Mark{a, b},
        m,
        n,
        r
      )

# the code of changes
def Change.codec() -> Codes.Codec(Spec.Change):
  (Spec.Change.code, (Spec.Change.code.read, x => r => Change.code_read(x, r)))

# a request reads back
def Ask.code_read(
  x: Spec.Ask,
  r: List<&2, U32>
) -> {
  Spec.Ask.code.read(Spec.Ask.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
}:
  match x:
    case Spec.Ask.Start{os}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Ask,
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => Spec.Ask.Start{a},
        os,
        r
      )
    case Spec.Ask.On{st, l, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Maybe<&2, String>,
        ~Spec.Change,
        ~Spec.Ask,
        ~Ledgers.Id.codec(),
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        ~Change.codec(),
        a => b => c => Spec.Ask.On{a, b, c},
        st,
        l,
        c,
        r
      )

# the code of requests
def Ask.codec() -> Codes.Codec(Spec.Ask):
  (Spec.Ask.code, (Spec.Ask.code.read, x => r => Ask.code_read(x, r)))

# the laws of Spec.Ask.is_eq: two requests are the same exactly when their codes
# are
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.is_eq):
  Codes.Code.eq_laws(~Spec.Ask, ~Ask.codec())

def Spec.Ask.same():
  Ask.laws()

# Owners
# ------

# owners that fit the nodes ns are ns
def Fits.same(
  +os: List<&2, String>,
  +ns: List<&2, String>
) -> {Spec.Own.fits(os, ns) == True{}: Bool} -> {os == ns: List<&2, String>}:
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

# Own.takes_inside for a branch, once whether its step is the store's is known
# (m)
def Takes.at(
  +os: List<&2, String>,
  +ns: List<&2, String>,
  m: Maybe<&2, Bool>
) -> {
  Maybe.bind(
    &2,
    Bool,
    Bool,
    m,
    k => Some{List.all.if(u => Spec.Own.fits(os, ns), k)}
  )
    == Some{True{}}: Maybe<&2, Bool>
} -> {os == ns: List<&2, String>}:
  match m:
    case None{}:
      e => Empty.absurd({os == ns: List<&2, String>}, Shared.Maybe.none_ne_some(Bool, True{}, e))
    case Some{k}:
      e => Fits.same(os, ns)(
        Shared.List.all.if_rest(
          k,
          u => Spec.Own.fits(os, ns)
        )(
          Shared.Maybe.some_inj(
            Bool,
            List.all.if(u => Spec.Own.fits(os, ns), k),
            True{},
            e
          )
        )
      )

def Spec.Own.takes_inside(s, r, l, g, at, os, h):
  Takes.at(os, Spec.Group.nodes(s, Spec.Own.tree(s, l, at, h), g), Spec.Own.ok(s, r, l, at))
# Growth
# ------
# A node's ledger only grows: each operation keeps every entry that it held.

# the ledger of a node with a new ledger is that ledger
def Led.led(
  s: Spec.State(),
  l: Ledgers.State(Spec.Ask)
) -> {Spec.State.ledger(Spec.State.led(s, l)) == l: Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{old, hs, ws}:
      {==}

# a new head keeps the ledger
def Led.head(
  s: Spec.State(),
  h: Spec.Head
) -> {Spec.State.ledger(Spec.State.head(s, h)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws}:
      {==}

# new waiting requests keep the ledger
def Led.wait(
  s: Spec.State(),
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {Spec.State.ledger(Spec.Wait.set(s, c, qs)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws}:
      {==}

# a node grows to itself
def Grows.refl(s: Spec.State()) -> {Spec.Node.grows(s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), Spec.State.ledger(s))

# growth composes
def Grows.trans(
  a: Spec.State(),
  b: Spec.State(),
  c: Spec.State()
) -> {
  Spec.Node.grows(a, b) == True{}: Bool
} -> {Spec.Node.grows(b, c) == True{}: Bool} -> {Spec.Node.grows(a, c) == True{}: Bool}:
  Ledgers.State.grows_trans(
    ~Spec.Ask,
    ~Spec.Ask.is_eq,
    ~Ask.laws(),
    Spec.State.ledger(a),
    Spec.State.ledger(b),
    Spec.State.ledger(c)
  )

# a node with a new ledger grows when the ledger does
def Grows.led(
  s: Spec.State(),
  l: Ledgers.State(Spec.Ask),
  e: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), l) == True{}: Bool}
) -> {Spec.Node.grows(s, Spec.State.led(s, l)) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Spec.Ask),
    Spec.State.ledger(Spec.State.led(s, l)),
    l,
    Led.led(s, l)
  ): {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), _) == True{}: Bool}
  e

# data only grows a node
def Grows.keep(
  +s: Spec.State(),
  +ds: List<&2, List<&2, U32>>
) -> {Spec.Node.grows(s, Spec.State.keep(s, ds)) == True{}: Bool}:
  Grows.led(
    s,
    Ledgers.State.put_datas(~Spec.Ask, ~Spec.Ask.is_eq, ds, Spec.State.ledger(s)),
    Ledgers.State.put_datas_grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), ds, Spec.State.ledger(s))
  )

# the work m, if any, is on a node that grew from s
def Work.after(s: Spec.State(), m: Maybe<&2, Spec.Work>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Spec.Work{s2, h, ns}}:
      Spec.Node.grows(s, s2)

# a new subtree only grows a node
def Work.of.grows(
  +s: Spec.State(),
  +ns: List<&2, List<&2, U32>>,
  +m: Maybe<&2, Trees.Put>
) -> {Work.after(s, Spec.Work.of(s, ns, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, ws}}:
      Grows.keep(s, ws)

# a key set in a tree only grows a node
def Set.grows(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {Work.after(s, Spec.Work.set(Spec.Work{s, h, ns}, k, x)) == True{}: Bool}:
  Work.of.grows(s, ns, Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x))

# the run m, if any, is on a node that grew from s
def Run.after(s: Spec.State(), m: Maybe<&2, Spec.Run>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Spec.Run{s2, t, ns}}:
      Spec.Node.grows(s, s2)

# a run is on its own node
def After.self(r: Spec.Run) -> {Run.after(Spec.Run.state(r), Some{r}) == True{}: Bool}:
  match r:
    case Spec.Run{s, t, ns}:
      Grows.refl(s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  +a: Spec.State(),
  +b: Spec.State(),
  +m: Maybe<&2, Spec.Run>,
  +e1: {Spec.Node.grows(a, b) == True{}: Bool},
  +e2: {Run.after(b, m) == True{}: Bool}
) -> {Run.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{s2, t, ns}}:
      Grows.trans(a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  +s: Spec.State(),
  +m: Maybe<&2, Spec.Run>,
  f: Spec.Run -> Maybe<&2, Spec.Run>,
  +hm: {Run.after(s, m) == True{}: Bool},
  hf: @r: Spec.Run -> {Run.after(Spec.Run.state(r), f(r)) == True{}: Bool}
) -> {Run.after(s, Maybe.bind(&2, Spec.Run, Spec.Run, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{+s2, +t, +ns}}:
      After.trans(s, s2, f(Spec.Run{s2, t, ns}), hm, hf(Spec.Run{s2, t, ns}))

# one of two runs, each on a node that grew
def After.when(
  +s: Spec.State(),
  +b: Bool,
  -mx: Maybe<&2, Spec.Run>,
  -my: Maybe<&2, Spec.Run>,
  +hx: {Run.after(s, mx) == True{}: Bool},
  +hy: {Run.after(s, my) == True{}: Bool}
) -> {Run.after(s, Shared.Bool.when(Maybe<&2, Spec.Run>, b, u => mx, u => my)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the run of a new log is on a node that grew
def Run.of.grows(
  +s: Spec.State(),
  +c: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  +e: {Work.after(s, m) == True{}: Bool}
) -> {Run.after(s, Spec.Run.of(c, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Work{s2, l, ns}}:
      e

# a key set in a run's log only grows its node
def Log.grows(
  +r: Spec.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {Run.after(Spec.Run.state(r), Spec.Run.log(r, k, x)) == True{}: Bool}:
  match r:
    case Spec.Run{+s, Spec.Tip{c, +l}, +ns}:
      Run.of.grows(
        s,
        c,
        Spec.Work.set(Spec.Work{s, l, ns}, k, x),
        Set.grows(s, l, ns, k, x)
      )

# new content only grows a run's node
def Content.grows(
  +r: Spec.Run,
  +h: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> {
  Spec.Node.grows(Spec.Run.state(r), Spec.Run.state(Spec.Run.content(r, h, ds))) == True{}: Bool
}:
  match r:
    case Spec.Run{s, Spec.Tip{c, l}, ns}:
      Grows.keep(s, ds)

# new owners only grow a run's node
def Owners.grows(
  +r: Spec.Run,
  +m: Maybe<&2, List<&2, String>>
) -> {Run.after(Spec.Run.state(r), Spec.Run.owners(r, m)) == True{}: Bool}:
  match m:
    case None{}:
      After.self(r)
    case Some{os}:
      Log.grows(r, Spec.Log.owners(), Ledgers.Owners.code(os, []))

# a refused request only grows a run's node
def Stale.grows(
  +r: Spec.Run,
  +i: Ledgers.Id
) -> {Run.after(Spec.Run.state(r), Spec.Step.stale(r, i)) == True{}: Bool}:
  Log.grows(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(Spec.Run.state(r), Spec.Step.taken(r, i, own)) == True{}: Bool}:
  +n = Spec.Line.count(Spec.Run.state(r), Spec.Run.tip(r))
  After.bind(
    Spec.Run.state(r),
    Spec.Run.log(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Spec.Run,
      Spec.Run,
      Spec.Run.log(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))})
      ),
      +r2 => Maybe.bind(
        &2,
        Spec.Run,
        Spec.Run,
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own)
      )
    ),
    Log.grows(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n})),
    +r1 => After.bind(
      Spec.Run.state(r1),
      Spec.Run.log(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))})
      ),
      +r2 => Maybe.bind(
        &2,
        Spec.Run,
        Spec.Run,
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own)
      ),
      Log.grows(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))})
      ),
      +r2 => After.bind(
        Spec.Run.state(r2),
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own),
        Log.grows(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Owners.grows(r3, own)
      )
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Spec.Verdict>
) -> {Run.after(Spec.Run.state(r), Spec.Step.judged(r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Verdict{False{}, h, ds}}:
      Stale.grows(r, i)
    case Some{Spec.Verdict{True{}, +h, +ds}}:
      After.trans(
        Spec.Run.state(r),
        Spec.Run.state(Spec.Run.content(r, h, ds)),
        Spec.Step.taken(Spec.Run.content(r, h, ds), i, own),
        Content.grows(r, h, ds),
        Taken.grows(Spec.Run.content(r, h, ds), i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Spec.Version>
) -> {Run.after(Spec.Run.state(r), Spec.Step.marked(r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(
        Spec.Run.state(r),
        Spec.Run.log(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(x), [])),
        r2 => Spec.Step.taken(r2, i, None{}),
        Log.grows(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(x), [])),
        r2 => Taken.grows(r2, i, None{})
      )

# a request for a mark only grows a run's node
def Mark.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +m: String
) -> {Run.after(Spec.Run.state(r), Spec.Step.mark(r, i, m)) == True{}: Bool}:
  +s = Spec.Run.state(r)
  +t = Spec.Run.tip(r)
  +n = Spec.Line.count(s, t)
  After.when(
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Spec.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Spec.Step.marked(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1))),
    Spec.Step.stale(r, i),
    Marked.grows(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1))),
    Stale.grows(r, i)
  )

# a change of a line only grows a run's node
def On.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Spec.Change
) -> {Run.after(Spec.Run.state(r), Spec.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  match l ch:
    case None{} Spec.Change.Branch{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Branch{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Branch{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Group{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Group{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Group{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Own{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Own{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Own{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Write{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Write{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Write{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Resolve{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Resolve{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Resolve{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Merge{a}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Merge{a}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Merge{a},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Move{a}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Move{a}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Move{a},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case None{} Spec.Change.Mark{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Mark{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Mark{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Branch{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Branch{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Branch{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Group{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Group{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Group{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Own{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Own{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Own{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Write{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Write{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Write{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Resolve{a, b, c}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Resolve{a, b, c}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Resolve{a, b, c},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Merge{a}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Merge{a}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Merge{a},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Move{a}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Move{a}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Move{a},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Mark{a, b}:
      Mark.grows(r, i, a)

# a request only grows a run's node
def Change.grows(
  +r: Spec.Run,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Spec.Ask
) -> {Run.after(Spec.Run.state(r), Spec.Step.change(r, c, i, q)) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
      Stale.grows(r, i)
    case Spec.Ask.On{+st, +l, +ch}:
      After.when(
        Spec.Run.state(r),
        Ledgers.Chain.is_eq(Spec.Line.chain(st, l), c),
        Spec.Step.on(r, i, st, l, ch),
        Spec.Step.stale(r, i),
        On.grows(r, i, st, l, ch),
        Stale.grows(r, i)
      )

# a request that the node holds or not only grows a run's node
def Asked.grows(
  +r: Spec.Run,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Spec.Ask>>
) -> {Run.after(Spec.Run.state(r), Spec.Step.asked(r, c, i, a)) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{Ledgers.Asked{t, q}}:
      Change.grows(r, c, i, q)

# a request that the log holds or not only grows a run's node
def Fresh.grows(
  +r: Spec.Run,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  +o: Maybe<&2, Spec.Out>
) -> {Run.after(Spec.Run.state(r), Spec.Step.fresh(r, c, i, o)) == True{}: Bool}:
  match o:
    case Some{x}:
      After.self(r)
    case None{}:
      Asked.grows(r, c, i, Spec.Node.asked(Spec.Run.state(r), i))

# one request of a step only grows a run's node
def One.grows(
  +r: Spec.Run,
  +c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {Run.after(Spec.Run.state(r), Spec.Step.one(r, c, i)) == True{}: Bool}:
  Fresh.grows(r, c, i, Spec.Line.out(Spec.Run.state(r), Spec.Run.tip(r), i))

# the requests of a step only grow a run's node
def All.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Spec.Run>
) -> {Run.after(s, m) == True{}: Bool} -> {Run.after(s, Spec.Step.all(c, qs, m)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.grows(
        s,
        c,
        rest,
        Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, i))
      )(After.bind(s, m, r => Spec.Step.one(r, c, i), h, r => One.grows(r, c, i)))

# a step only grows a node: its run is on a node that keeps every entry
def Run.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +t: Spec.Tip,
  +qs: List<&2, Ledgers.Id>
) -> {Run.after(s, Spec.Step.run(s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Spec.Run{s, t, []}})(Grows.refl(s))

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  +a: Spec.State(),
  +b: Spec.State(),
  +x: Spec.State(),
  e: {Spec.State.ledger(x) == Spec.State.ledger(b): Ledgers.State(Spec.Ask)},
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Node.grows(a, x) == True{}: Bool}:
  %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(x), Spec.State.ledger(b), e): {
    Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(a), _) == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  +s: Spec.State(),
  b: Bool,
  -x: Spec.State(),
  -y: Spec.State(),
  hx: {Spec.Node.grows(s, x) == True{}: Bool},
  hy: {Spec.Node.grows(s, y) == True{}: Bool}
) -> {Spec.Node.grows(s, Shared.Bool.when(Spec.State(), b, u => x, u => y)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a moved head keeps the ledger
def Led.moved(
  s: Spec.State(),
  h: Spec.Head,
  qs: List<&2, Ledgers.Id>
) -> {Spec.State.ledger(Spec.State.moved(s, h, qs)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  s: Spec.State(),
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {Spec.State.ledger(Spec.State.wait(s, c, i)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws}:
      {==}

# a ballot only grows a node
def Cast.put.grows(
  +n: String,
  +w: Ledgers.Where,
  +th: Maybe<&2, Hashes.Hash>,
  +qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  +s: Spec.State()
) -> {Run.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Cast.put(n, w, th, qs, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Run{+s2, +t2, ns}}:
      e =>
        +s3 = Spec.State.keep(s2, [Spec.Tip.words(t2)])
        +l4 = Ledgers.State.cast(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          Spec.State.ledger(s3),
          w,
          n,
          Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}
        )
        Grows.trans(s, s2, Spec.State.led(s3, l4))(e)(
          Grows.trans(s2, s3, Spec.State.led(s3, l4))(
            Grows.keep(s2, [Spec.Tip.words(t2)])
          )(
            Grows.led(
              s3,
              l4,
              Ledgers.State.add_grows(
                ~Spec.Ask,
                ~Spec.Ask.is_eq,
                ~Ask.laws(),
                Spec.State.ledger(s3),
                Ledgers.Slot.vote(w, n),
                Ledgers.Entry.Vote{Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}}
              )
            )
          )
        )

# Node.cast only grows a node, at the head h whose tip is m
def Cast.at.grows(
  +n: String,
  +s: Spec.State(),
  h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.grows(s, Spec.Cast.at(n, s, h, m)) == True{}: Bool}:
  match h m:
    case Spec.Head{+r, +b, +next, +th} Some{+t}:
      +c = Spec.Line.chain(r, b)
      +qs = Spec.Wait.of(s, c)
      Grows.when(
        s,
        Spec.Cast.may(n, s, Ledgers.Where{c, next}, t, qs),
        Spec.Cast.put(n, Ledgers.Where{c, next}, th, qs, Spec.Step.run(s, c, t, qs), s),
        s,
        Cast.put.grows(
          n,
          Ledgers.Where{c, next},
          th,
          qs,
          Spec.Step.run(s, c, t, qs),
          s
        )(Run.grows(s, c, t, qs)),
        Grows.refl(s)
      )
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# a node's ballot only grows it
def Cast.grows(
  +n: String,
  +s: Spec.State(),
  +h: Spec.Head
) -> {Spec.Node.grows(s, Spec.Node.cast(n, s, h)) == True{}: Bool}:
  Cast.at.grows(n, s, h, Spec.Head.tip(s, h))

# a checked step only grows a node
def Advance.ran.grows(
  +s: Spec.State(),
  +r: Ledgers.Id,
  +b: Maybe<&2, String>,
  +next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  +qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Advance.ran(s, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Run{+s2, +t2, ns}}:
      e =>
        +s3 = Spec.State.keep(s2, [Spec.Tip.words(t2)])
        +hd = {Spec.Head{r, b, U32.inc(next), Some{Spec.Tip.hash(t2)}}: Spec.Head}
        Grows.when(
          s,
          Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
          Spec.State.moved(s3, hd, qs),
          s,
          Grows.to(
            s,
            s3,
            Spec.State.moved(s3, hd, qs),
            Led.moved(s3, hd, qs),
            Grows.trans(s, s2, s3)(e)(Grows.keep(s2, [Spec.Tip.words(t2)]))
          ),
          Grows.refl(s)
        )

# Node.advance only grows a node, once the decided step m is known
def Advance.step.grows(
  +s: Spec.State(),
  h: Spec.Head,
  +t: Spec.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Node.grows(s, Spec.Advance.step(s, h, t, m)) == True{}: Bool}:
  match h m:
    case Spec.Head{+r, +b, +next, +th} Some{Ledgers.Vote{+before, +qs, +after}}:
      Grows.when(
        s,
        Spec.Root.same(before, th),
        Spec.Advance.ran(
          s,
          r,
          b,
          next,
          after,
          qs,
          Spec.Step.run(s, Spec.Line.chain(r, b), t, qs)
        ),
        s,
        Advance.ran.grows(
          s,
          r,
          b,
          next,
          after,
          qs,
          Spec.Step.run(s, Spec.Line.chain(r, b), t, qs)
        )(Run.grows(s, Spec.Line.chain(r, b), t, qs)),
        Grows.refl(s)
      )
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  +s: Spec.State(),
  +h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.grows(s, Spec.Advance.at(s, h, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+t}:
      Advance.step.grows(
        s,
        h,
        t,
        Ledgers.State.decide(
          ~Spec.Ask,
          Spec.State.ledger(s),
          Ledgers.Where{Spec.Head.chain(h), Spec.Head.next(h)},
          Spec.Line.owners(s, t)
        )
      )

# a head that moves only grows a node
def Advance.grows(
  +s: Spec.State(),
  +h: Spec.Head
) -> {Spec.Node.grows(s, Spec.Node.advance(s, h)) == True{}: Bool}:
  Advance.at.grows(s, h, Spec.Head.tip(s, h))

# a head that moves over each decided step only grows a node
def Advances.grows(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Node.advances(f, s, c, m)) == True{}: Bool}:
  match f m:
    case 0n x:
      Grows.refl(s)
    case 1n+p None{}:
      Grows.refl(s)
    case 1n+(+p) Some{+h}:
      +s1 = Spec.Node.advance(s, h)
      +m1 = Spec.Node.head_of(s1, c)
      Grows.when(
        s,
        Spec.Head.is_at(m1, Spec.Head.next(h)),
        s1,
        Spec.Node.advances(p, s1, c, m1),
        Advance.grows(s, h),
        Grows.trans(s, s1, Spec.Node.advances(p, s1, c, m1))(Advance.grows(s, h))(
          Advances.grows(p, s1, c, m1)
        )
      )

# a ballot at a head, if any, only grows a node
def Step.cast.grows(
  +n: String,
  +s: Spec.State(),
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Step.cast(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{h}:
      Cast.grows(n, s, h)

# what a node does at a head only grows it
def Step.head.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Step.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      +s1 = Spec.Node.advances(4294967295n, s, c, Some{h})
      +s2 = Spec.Step.cast(n, s1, Spec.Node.head_of(s1, c))
      +s3 = Spec.Node.advances(4294967295n, s2, c, Spec.Node.head_of(s2, c))
      Grows.trans(s, s1, s3)(
        Advances.grows(4294967295n, s, c, Some{h})
      )(
        Grows.trans(s1, s2, s3)(
          Step.cast.grows(n, s1, Spec.Node.head_of(s1, c))
        )(Advances.grows(4294967295n, s2, c, Spec.Node.head_of(s2, c)))
      )

# a line that opens only grows a node
def Opened.grows(
  +s: Spec.State(),
  h: Spec.Head
) -> {Spec.Node.grows(s, Spec.Node.opened(s, h)) == True{}: Bool}:
  match h:
    case Spec.Head{+r, Some{+b}, n, None{}}:
      +hd = {
        Spec.Head{
          r,
          Some{b},
          0,
          Spec.Branch.first(s, b, Spec.Node.tip(s, Ledgers.Chain{r, None{}}))
        }: Spec.Head
      }
      Grows.to(s, s, Spec.State.head(s, hd), Led.head(s, hd), Grows.refl(s))
    case Spec.Head{r, Some{b}, n, Some{t}}:
      Grows.refl(s)
    case Spec.Head{r, None{}, n, t}:
      Grows.refl(s)

# what a node does on a line only grows it
def Step.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Node.step(n, s, c, h)) == True{}: Bool}:
  match h:
    case None{}:
      Grows.refl(s)
    case Some{+x}:
      +s1 = Spec.Node.opened(s, x)
      Grows.trans(s, s1, Spec.Step.head(n, s1, c, Spec.Node.head_of(s1, c)))(
        Opened.grows(s, x)
      )(Step.head.grows(n, s1, c, Spec.Node.head_of(s1, c)))

# the first tip of a store only grows a node
def Start.put.grows(
  +s: Spec.State(),
  +i: Ledgers.Id,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Start.put(s, i, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Work{+s2, +l, ns}}:
      e =>
        +t = {Spec.Tip{None{}, l}: Spec.Tip}
        +s3 = Spec.State.keep(s2, [Spec.Tip.words(t)])
        +hd = {Spec.Head{i, None{}, 0, Some{Spec.Tip.hash(t)}}: Spec.Head}
        Grows.to(
          s,
          s3,
          Spec.State.head(s3, hd),
          Led.head(s3, hd),
          Grows.trans(s, s2, s3)(e)(Grows.keep(s2, [Spec.Tip.words(t)]))
        )

# a store that starts only grows a node
def Start.grows(
  +s: Spec.State(),
  +i: Ledgers.Id,
  +os: List<&2, String>
) -> {Spec.Node.grows(s, Spec.Node.start(s, i, os)) == True{}: Bool}:
  Start.put.grows(
    s,
    i,
    Spec.Log.first(Spec.Work{s, None{}, []}, os)
  )(Set.grows(s, None{}, [], Spec.Log.owners(), Ledgers.Owners.code(os, [])))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  +s: Spec.State(),
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Follow.new(s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(s)
    case None{}:
      Grows.to(
        s,
        s,
        Spec.State.head(s, Spec.Head{r, l, 0, None{}}),
        Led.head(s, Spec.Head{r, l, 0, None{}}),
        Grows.refl(s)
      )

# a new request only grows a node
def Arrive.grows(
  +s: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> {Spec.Node.grows(s, Spec.Node.arrive(s, i, q)) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{+os}:
      Start.grows(s, i, os)
    case Spec.Ask.On{+r, +l, c}:
      +s1 = Spec.Node.follow(s, r, l)
      Grows.to(
        s,
        s1,
        Spec.State.wait(s1, Spec.Line.chain(r, l), i),
        Led.waits(s1, Spec.Line.chain(r, l), i),
        Follow.new.grows(s, r, l, Spec.Node.head_of(s, Spec.Line.chain(r, l)))
      )

# Node.ask_grows once the cell m of the request's ID is known
def Ask.at.grows(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {Spec.Node.grows(s, Spec.Node.ask.at(n, s, e, q, m)) == True{}: Bool}:
  match m:
    case Some{x}:
      Grows.refl(s)
    case None{}:
      +i = Spec.Envelope.of(e)
      +c = Spec.Ask.chain(i, q)
      +l0 = Ledgers.State.ask(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        Spec.State.ledger(s),
        i,
        Spec.Envelope.time(e),
        q
      )
      +s0 = Spec.State.led(s, l0)
      +s1 = Spec.Node.arrive(s0, i, q)
      Grows.trans(s, s0, Spec.Node.step(n, s1, c, Spec.Node.head_of(s1, c)))(
        Grows.led(
          s,
          l0,
          Ledgers.State.add_grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            Spec.State.ledger(s),
            Ledgers.Slot.ask(i),
            Ledgers.Entry.Ask{i, Spec.Envelope.time(e), q}
          )
        )
      )(
        Grows.trans(s0, s1, Spec.Node.step(n, s1, c, Spec.Node.head_of(s1, c)))(
          Arrive.grows(s0, i, q)
        )(Step.grows(n, s1, c, Spec.Node.head_of(s1, c)))
      )

def Spec.Node.ask_grows(n, s, e, q):
  Ask.at.grows(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )

# the new requests among cells only grow a node
def Take.asks.grows(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Take.asks(cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Spec.Node.arrive(s, i, q)
      Grows.trans(s, s1, Spec.Take.asks(rest, s1))(Arrive.grows(s, i, q))(
        Take.asks.grows(rest, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(rest, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(rest, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(rest, s)

def Spec.Node.take_grows(s, t):
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), t)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
  )
  Grows.trans(s, s1, Spec.Take.asks(cs, s1))(
    Grows.led(
      s,
      l1,
      Ledgers.State.take_grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), Spec.State.ledger(s), t)
    )
  )(Take.asks.grows(cs, s1))

# what a node does on each of its lines only grows it
def Steps.grows(
  +n: String,
  hs: List<&2, Spec.Head>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Node.steps(n, hs, s)) == True{}: Bool}:
  match hs:
    case Nil{}:
      Grows.refl(s)
    case Con{+h, +rest}:
      +s1 = Spec.Node.step(n, s, Spec.Head.chain(h), Some{h})
      Grows.trans(s, s1, Spec.Node.steps(n, rest, s1))(
        Step.grows(n, s, Spec.Head.chain(h), Some{h})
      )(Steps.grows(n, rest, s1))

def Spec.Node.sync_grows(n, s, t):
  +s1 = Spec.Node.take(s, t)
  +hs = Tries.Trie.values(Spec.Head, Spec.State.heads(s1))
  Grows.trans(s, s1, Spec.Node.steps(n, hs, s1))(Spec.Node.take_grows(s, t))(Steps.grows(n, hs, s1))

# Asks
# ----

# a slot that holds a cell holds one in a node that grew
def Slot.held_kept(
  +a: Spec.State(),
  +b: Spec.State(),
  +k: List<&2, Bool>,
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(a), k)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(b), k)
  )
    == True{}: Bool
}:
  Cells.Cell.keeps_some(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(a), k),
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(b), k)
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      ~Cells.Cell.keeps(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
      ~Cells.Cell.none_kept(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
      Spec.State.ledger(a),
      Spec.State.ledger(b),
      k
    )(g)
  )

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +em: {
    Ledgers.State.get(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )
      == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(
      ~Spec.Ask,
      Spec.State.ledger(Spec.Node.ask.at(n, s, e, q, m)),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
        Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
      {==}
    case None{}:
      +i = Spec.Envelope.of(e)
      +c = Spec.Ask.chain(i, q)
      +k = Ledgers.Slot.ask(i)
      +en = {Ledgers.Entry.Ask{i, Spec.Envelope.time(e), q}: Ledgers.Entry<Spec.Ask>}
      +l0 = Ledgers.State.put(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), k, en)
      +s0 = Spec.State.led(s, l0)
      +s1 = Spec.Node.arrive(s0, i, q)
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
        Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), k),
        None{},
        em
      ): {
        Maybe.is_some(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(
            ~Spec.Ask,
            Spec.State.ledger(
              Spec.Node.step(
                n,
                Spec.Node.arrive(
                  Spec.State.led(
                    s,
                    Ledgers.State.add.of(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), k, en, _)
                  ),
                  i,
                  q
                ),
                c,
                Spec.Node.head_of(
                  Spec.Node.arrive(
                    Spec.State.led(
                      s,
                      Ledgers.State.add.of(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), k, en, _)
                    ),
                    i,
                    q
                  ),
                  c
                )
              )
            ),
            k
          )
        )
          == True{}: Bool
      }
      Slot.held_kept(
        s0,
        Spec.Node.step(n, s1, c, Spec.Node.head_of(s1, c)),
        k,
        Grows.trans(s0, s1, Spec.Node.step(n, s1, c, Spec.Node.head_of(s1, c)))(
          Arrive.grows(s0, i, q)
        )(Step.grows(n, s1, c, Spec.Node.head_of(s1, c)))
      )(
        %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(s0), l0, Led.led(s, l0)): {
          Maybe.is_some(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, _, k)
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, l0, k),
          Some{Cells.One{en}},
          Ledgers.State.put_get(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), k, en)(em)
        ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
        {==}
      )

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  m: String,
  s: Spec.State(),
  e: Spec.Envelope,
  q: Spec.Ask,
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, c) == True{}: Bool
} -> {Spec.Node.ask.at(m, s, e, q, c) == s: Spec.State()}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Spec.Node.ask.at(m, s, e, q, None{}) == s: Spec.State()},
        Shared.Bool.false_ne_true(h)
      )

def Spec.Node.ask_once(n, m, s, e, q, e2, q2):
  h =>
    +a = Spec.Node.ask(n, s, e, q)
    Ask.once.at(
      m,
      a,
      e2,
      q2,
      Ledgers.State.get(~Spec.Ask, Spec.State.ledger(a), Ledgers.Slot.ask(Spec.Envelope.of(e2)))
    )(
      %Equal.sym(Ledgers.Id, Spec.Envelope.of(e2), Spec.Envelope.of(e), h): {
        Maybe.is_some(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(~Spec.Ask, Spec.State.ledger(a), Ledgers.Slot.ask(_))
        )
          == True{}: Bool
      }
      Ask.held.at(
        n,
        s,
        e,
        q,
        Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))),
        {==}
      )
    )
