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
