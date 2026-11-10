import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
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
    case Spec.Change.Key{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Spec.Change.Key{a, b},
        n,
        k,
        r
      )

# the code of changes
def Change.codec() -> Codes.Codec(Spec.Change):
  (Spec.Change.code, (Spec.Change.code.read, x => r => Change.code_read(x, r)))

# a first owner reads back
def Owner.code_read(
  x: Spec.Owner,
  r: List<&2, U32>
) -> {
  Spec.Owner.code.read(Spec.Owner.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Owner>>
}:
  match x:
    case Spec.Owner{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Spec.Owner,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Spec.Owner{a, b},
        n,
        k,
        r
      )

# the code of first owners
def Owner.codec() -> Codes.Codec(Spec.Owner):
  (Spec.Owner.code, (Spec.Owner.code.read, x => r => Owner.code_read(x, r)))

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
        ~List<&2, Spec.Owner>,
        ~Spec.Ask,
        ~Codes.Code.list.codec(~Spec.Owner, ~Owner.codec()),
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

# Takes.at once whether the node holds the groups is known (b)
def Takes.held(
  os: List<&2, String>,
  ns: List<&2, String>,
  b: Bool
) -> {
  Shared.Maybe.when(Bool, b, u => Some{Spec.Own.fits(os, ns)}) == Some{True{}}: Maybe<&2, Bool>
} -> {os == ns: List<&2, String>}:
  match b:
    case False{}:
      e => Empty.absurd({os == ns: List<&2, String>}, Shared.Maybe.none_ne_some(Bool, True{}, e))
    case True{}:
      e => Fits.same(os, ns)(Shared.Maybe.some_inj(Bool, Spec.Own.fits(os, ns), True{}, e))

# Own.takes_inside once whether the Own may name its version is known (m)
def Takes.at(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  g: String,
  os: List<&2, String>,
  m: Maybe<&2, Bool>
) -> {
  Maybe.bind(&2, Bool, Bool, m, k => Spec.Own.takes.at(s, h, g, os, k)) == Some{True{}}: Maybe<&2, Bool>
} -> {os == Spec.Group.nodes(s, h, g): List<&2, String>}:
  match m:
    case None{}:
      e => Empty.absurd(
        {os == Spec.Group.nodes(s, h, g): List<&2, String>},
        Shared.Maybe.none_ne_some(Bool, True{}, e)
      )
    case Some{False{}}:
      e => Empty.absurd(
        {os == Spec.Group.nodes(s, h, g): List<&2, String>},
        Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e))
      )
    case Some{True{}}:
      Takes.held(os, Spec.Group.nodes(s, h, g), Spec.Groups.held(s, h))

def Spec.Own.takes_inside(s, r, l, g, at, os, h):
  Takes.at(s, Spec.Own.tree(s, l, at, h), g, os, Spec.Own.ok(s, r, l, at))

# Growth
# ------
# A node's ledger only grows: each operation keeps every entry that it held.

# Trees
# -----
# The node's read and write of a tree are the tree's own (Trees.Tree.get,
# Trees.Tree.set); they look at the root node before they make the path.

# a read below no node gives nothing
def Go.none(
  s: Spec.State(),
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {Trees.Tree.get.go(~Spec.State(), ~Spec.Store.fetch, s, p, k, None{}) == None{}: Maybe<&2, List<&2, U32>>}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a read below an empty node gives nothing
def Go.empty(
  s: Spec.State(),
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {
  Trees.Tree.get.go(~Spec.State(), ~Spec.Store.fetch, s, p, k, Some{Trees.Node.Empty{}}) == None{}: Maybe<&2, List<&2, U32>>
}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# Get.is once the root node m is known
def Get.at.is(
  s: Spec.State(),
  +k: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {
  Spec.Node.get.at(s, k, m)
    == Trees.Tree.get.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, m): Maybe<&2, List<&2, U32>>
}:
  match m:
    case None{}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, None{}),
        None{},
        Go.none(s, Trees.Tree.path(k), k)
      )
    case Some{Trees.Node.Empty{}}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, Some{Trees.Node.Empty{}}),
        None{},
        Go.empty(s, Trees.Tree.path(k), k)
      )
    case Some{Trees.Node.Leaf{a, b}}:
      {==}
    case Some{Trees.Node.Branch{ks}}:
      {==}

# the node's read of a tree is the tree's read
def Get.is(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> {Spec.Node.get(s, h, k) == Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, s, h, k): Maybe<&2, List<&2, U32>>}:
  Get.at.is(s, k, Trees.Tree.part(~Spec.State(), ~Spec.Store.fetch, s, h))

# a look below no node lacks it
def Look.go.none(
  s: Spec.State(),
  p: List<&2, Nat>,
  k: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {Trees.Tree.look.go(~Spec.State(), ~Spec.Store.fetch, s, p, k, h, None{}) == Trees.Look.missing(h): Trees.Look}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# a look below an empty node finds nothing
def Look.go.empty(
  s: Spec.State(),
  p: List<&2, Nat>,
  k: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {Trees.Tree.look.go(~Spec.State(), ~Spec.Store.fetch, s, p, k, h, Some{Trees.Node.Empty{}}) == Trees.Look.Absent{}: Trees.Look}:
  match p:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

# Look.is once the root node m is known
def Look.at.is(
  s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {Spec.Node.look.at(s, h, k, m) == Trees.Tree.look.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, h, m): Trees.Look}:
  match m:
    case None{}:
      Equal.sym(
        Trees.Look,
        Trees.Tree.look.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, h, None{}),
        Trees.Look.missing(h),
        Look.go.none(s, Trees.Tree.path(k), k, h)
      )
    case Some{Trees.Node.Empty{}}:
      Equal.sym(
        Trees.Look,
        Trees.Tree.look.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), k, h, Some{Trees.Node.Empty{}}),
        Trees.Look.Absent{},
        Look.go.empty(s, Trees.Tree.path(k), k, h)
      )
    case Some{Trees.Node.Leaf{a, b}}:
      {==}
    case Some{Trees.Node.Branch{ks}}:
      {==}

# the node's look at a tree is the tree's look
def Look.is(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> {Spec.Node.look(s, h, k) == Trees.Tree.look(~Spec.State(), ~Spec.Store.fetch, s, h, k): Trees.Look}:
  Look.at.is(s, h, k, Trees.Tree.part(~Spec.State(), ~Spec.Store.fetch, s, h))

# a write below no node gives nothing
def Set.go.none(
  s: Spec.State(),
  p: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  x: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {Trees.Tree.set.go(~Spec.State(), ~Spec.Store.fetch, s, p, d, k, x, h, None{}) == None{}: Maybe<&2, Trees.Put>}:
  match p:
    case Nil{}:
      {==}
    case Con{y, r}:
      {==}

# Set.is once the root node m is known
def Set.at.is(
  s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {
  Spec.Node.set.at(s, h, k, x, m)
    == Trees.Tree.set.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), 0n, k, x, h, m): Maybe<&2, Trees.Put>
}:
  match m:
    case None{}:
      Equal.sym(
        Maybe<&2, Trees.Put>,
        Trees.Tree.set.go(~Spec.State(), ~Spec.Store.fetch, s, Trees.Tree.path(k), 0n, k, x, h, None{}),
        None{},
        Set.go.none(s, Trees.Tree.path(k), 0n, k, x, h)
      )
    case Some{n}:
      {==}

# the node's write of a tree is the tree's write
def Set.is(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Spec.Node.set(s, h, k, x) == Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x): Maybe<&2, Trees.Put>}:
  Set.at.is(s, h, k, x, Trees.Tree.part(~Spec.State(), ~Spec.Store.fetch, s, h))

# the ledger of a node with a new ledger is that ledger
def Led.led(
  s: Spec.State(),
  l: Ledgers.State(Spec.Ask)
) -> {Spec.State.ledger(Spec.State.led(s, l)) == l: Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{old, hs, ws, ks}:
      {==}

# a new head keeps the ledger
def Led.head(
  s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head
) -> {Spec.State.ledger(Spec.State.head(s, c, h)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# new waiting requests keep the ledger
def Led.wait(
  s: Spec.State(),
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {Spec.State.ledger(Spec.Wait.set(s, c, qs)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
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

# the node m, if any, grew from s
def State.after(s: Spec.State(), m: Maybe<&2, Spec.State()>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Spec.Node.grows(s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  s: Spec.State(),
  -s2: Spec.State(),
  b: Bool,
  g: {Spec.Node.grows(s, s2) == True{}: Bool}
) -> {State.after(s, Shared.Maybe.when(Spec.State(), b, u => Some{s2})) == True{}: Bool}:
  match b:
    case True{}:
      g
    case False{}:
      {==}

# data that a node puts and reads back only grows it
def Put.grows(
  +s: Spec.State(),
  +ds: List<&2, List<&2, U32>>
) -> {State.after(s, Spec.State.put(s, ds)) == True{}: Bool}:
  Put.grows.if(
    s,
    Spec.State.keep(s, ds),
    Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ds), ds),
    Grows.keep(s, ds)
  )

# a work on a node that grew
def Work.put.grows(
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  h: Maybe<&2, Hashes.Hash>,
  ws: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> {State.after(s, m) == True{}: Bool} -> {Work.after(s, Spec.Work.put(m, h, ws, ns)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a new subtree only grows a node
def Work.of.grows(
  +s: Spec.State(),
  ns: List<&2, List<&2, U32>>,
  m: Maybe<&2, Trees.Put>
) -> {Work.after(s, Spec.Work.of(s, ns, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, +ws}}:
      Work.put.grows(s, Spec.State.put(s, ws), Some{h}, ws, ns)(Put.grows(s, ws))

# a key set in a tree only grows a node
def Set.grows(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(s, Spec.Work.set(Spec.Work{s, h, ns}, k, x)) == True{}: Bool}:
  Work.of.grows(s, ns, Spec.Node.set(s, h, k, x))

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
  a: Spec.State(),
  b: Spec.State(),
  +m: Maybe<&2, Spec.Run>,
  e1: {Spec.Node.grows(a, b) == True{}: Bool},
  e2: {Run.after(b, m) == True{}: Bool}
) -> {Run.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{s2, t, ns}}:
      Grows.trans(a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  s: Spec.State(),
  +m: Maybe<&2, Spec.Run>,
  f: Spec.Run -> Maybe<&2, Spec.Run>,
  hm: {Run.after(s, m) == True{}: Bool},
  hf: @r: Spec.Run -> {Run.after(Spec.Run.state(r), f(r)) == True{}: Bool}
) -> {Run.after(s, Maybe.bind(&2, Spec.Run, Spec.Run, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{+s2, +t, +ns}}:
      After.trans(s, s2, f(Spec.Run{s2, t, ns}), hm, hf(Spec.Run{s2, t, ns}))

# one of two runs, each on a node that grew
def After.when(
  s: Spec.State(),
  +b: Bool,
  -mx: Maybe<&2, Spec.Run>,
  -my: Maybe<&2, Spec.Run>,
  hx: {Run.after(s, mx) == True{}: Bool},
  hy: {Run.after(s, my) == True{}: Bool}
) -> {Run.after(s, Shared.Bool.when(Maybe<&2, Spec.Run>, b, u => mx, u => my)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the run of a new log is on a node that grew
def Run.of.grows(
  s: Spec.State(),
  c: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  e: {Work.after(s, m) == True{}: Bool}
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

# a run on a node that grew
def Run.put.grows(
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  t: Spec.Tip,
  ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> {State.after(s, m) == True{}: Bool} -> {Run.after(s, Spec.Run.put(m, t, ds, ns)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# new content only grows a run's node
def Content.grows(
  r: Spec.Run,
  h: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> {Run.after(Spec.Run.state(r), Spec.Run.content(r, h, ds)) == True{}: Bool}:
  match r:
    case Spec.Run{+s, Spec.Tip{c, l}, ns}:
      Run.put.grows(s, Spec.State.put(s, ds), Spec.Tip{h, l}, ds, ns)(Put.grows(s, ds))

# Add.grows once the value m of the key is known
def Add.at.grows(
  r: Spec.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(Spec.Run.state(r), Spec.Run.add.at(r, k, x, m)) == True{}: Bool}:
  match m:
    case None{}:
      Log.grows(r, k, x)
    case Some{old}:
      {==}

# a new key in a run's log only grows its node
def Add.grows(
  +r: Spec.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> {Run.after(Spec.Run.state(r), Spec.Run.add(r, k, x)) == True{}: Bool}:
  Add.at.grows(r, k, x, Spec.Node.get(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), k))

# new owners only grow a run's node
def Owners.grows(
  r: Spec.Run,
  +m: Maybe<&2, List<&2, String>>
) -> {Run.after(Spec.Run.state(r), Spec.Run.owners(r, m)) == True{}: Bool}:
  match m:
    case None{}:
      After.self(r)
    case Some{os}:
      Log.grows(r, Spec.Log.owners(), Ledgers.Owners.code(os, []))

# a refused request only grows a run's node
def Stale.grows(
  r: Spec.Run,
  i: Ledgers.Id
) -> {Run.after(Spec.Run.state(r), Spec.Step.stale(r, i)) == True{}: Bool}:
  Add.grows(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(Spec.Run.state(r), Spec.Step.taken(r, i, own)) == True{}: Bool}:
  +n = Spec.Line.count(Spec.Run.state(r), Spec.Run.tip(r))
  After.bind(
    Spec.Run.state(r),
    Spec.Run.add(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Spec.Run,
      Spec.Run,
      Spec.Run.add(
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
    Add.grows(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n})),
    +r1 => After.bind(
      Spec.Run.state(r1),
      Spec.Run.add(
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
      Add.grows(
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
      After.bind(
        Spec.Run.state(r),
        Spec.Run.content(r, h, ds),
        r2 => Spec.Step.taken(r2, i, own),
        Content.grows(r, h, ds),
        r2 => Taken.grows(r2, i, own)
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
        Spec.Run.add(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(x), [])),
        r2 => Spec.Step.taken(r2, i, None{}),
        Add.grows(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(x), [])),
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
  i: Ledgers.Id,
  st: Ledgers.Id,
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
    case None{} Spec.Change.Key{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Key{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Key{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )
    case Some{x} Spec.Change.Key{a, b}:
      Judged.grows(
        r,
        i,
        Spec.Change.owners(Spec.Change.Key{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Key{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        )
      )

# a request only grows a run's node
def Change.grows(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Spec.Ask
) -> {Run.after(Spec.Run.state(r), Spec.Step.change(r, c, i, q)) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
      Stale.grows(r, i)
    case Spec.Ask.On{+st, +l, ch}:
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
  r: Spec.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
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
  c: Ledgers.Chain,
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
  c: Ledgers.Chain,
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
  c: Ledgers.Chain,
  t: Spec.Tip,
  qs: List<&2, Ledgers.Id>
) -> {Run.after(s, Spec.Step.run(s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Spec.Run{s, t, []}})(Grows.refl(s))

# the run of picked requests, with one more request or not
def Add.run(
  b: Bool,
  i: Ledgers.Id,
  p: Spec.Picked
) -> {Spec.Picked.run(Spec.Picked.add(b, i, p)) == Spec.Picked.run(p): Spec.Run}:
  match p:
    case Spec.Picked{r, qs}:
      {==}

# the run m, if any, else r, is on a node that grew from that of r
def Default.run.grows(
  r: Spec.Run,
  m: Maybe<&2, Spec.Run>
) -> {Run.after(Spec.Run.state(r), m) == True{}: Bool} -> {
  Spec.Node.grows(Spec.Run.state(r), Spec.Run.state(Maybe.default(&2, Spec.Run, m, r))) == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(Spec.Run.state(r))
    case Some{Spec.Run{s2, t, ns}}:
      e => e

# the run of the requests that can run is on a node that grew
def Some.grows(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +r: Spec.Run
) -> {Run.after(Spec.Run.state(r), Some{Spec.Picked.run(Spec.Step.some(c, qs, r))}) == True{}: Bool}:
  match qs:
    case Nil{}:
      After.self(r)
    case Con{+i, +rest}:
      +m = Spec.Step.one(r, c, i)
      +r2 = Maybe.default(&2, Spec.Run, m, r)
      %Equal.sym(
        Spec.Run,
        Spec.Picked.run(Spec.Picked.add(Maybe.is_some(&2, Spec.Run, m), i, Spec.Step.some(c, rest, r2))),
        Spec.Picked.run(Spec.Step.some(c, rest, r2)),
        Add.run(Maybe.is_some(&2, Spec.Run, m), i, Spec.Step.some(c, rest, r2))
      ): {Run.after(Spec.Run.state(r), Some{_}) == True{}: Bool}
      After.trans(
        Spec.Run.state(r),
        Spec.Run.state(r2),
        Some{Spec.Picked.run(Spec.Step.some(c, rest, r2))},
        Default.run.grows(r, m)(One.grows(r, c, i)),
        Some.grows(c, rest, r2)
      )

# a run that is kept when b holds is on a node that grew, when it is
def Fit.when.grows(
  -s: Spec.State(),
  b: Bool,
  -r: Spec.Run,
  e: {Run.after(s, Some{r}) == True{}: Bool}
) -> {Run.after(s, Shared.Maybe.when(Spec.Run, b, u => Some{r})) == True{}: Bool}:
  match b:
    case True{}:
      e
    case False{}:
      {==}

# a run that fits a tip is on a node that grew, when the run is
def Plan.fit.grows(
  -s: Spec.State(),
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Spec.Run>
) -> {Run.after(s, m) == True{}: Bool} -> {Run.after(s, Spec.Plan.fit(after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Spec.Run{s2, +t2, ns}}:
      e => Fit.when.grows(
        s,
        Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
        Spec.Run{s2, t2, ns},
        e
      )

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  -s: Spec.State(),
  b: Bool,
  -x: Spec.Plan,
  -y: Spec.Plan,
  hx: {Run.after(s, Spec.Plan.run(x)) == True{}: Bool},
  hy: {Run.after(s, Spec.Plan.run(y)) == True{}: Bool}
) -> {Run.after(s, Spec.Plan.run(Shared.Bool.when(Spec.Plan, b, u => x, u => y))) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the run of the plan of the owner whose turn it is is on a node that grew
def Plan.own.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  t: Spec.Tip
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.own(s, c, t))) == True{}: Bool}:
  Some.grows(c, Spec.Cast.mine(s, Spec.Wait.of(s, c)), Spec.Run{s, t, []})

# the run of the plan of another owner is on a node that grew
def Plan.copy.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.copy(s, c, t, th, m))) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, +after}}:
      Plan.when.grows(
        s,
        List.all.if(u => Spec.Cast.all_mine(s, qs), Spec.Root.same(before, th)),
        Spec.Plan{qs, Spec.Plan.fit(after, Spec.Step.run(s, c, t, qs))},
        Spec.Plan{[], None{}},
        Plan.fit.grows(s, after, Spec.Step.run(s, c, t, qs))(Run.grows(s, c, t, qs)),
        {==}
      )

# the run of what a node casts for is on a node that grew
def Plan.of.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Spec.Tip,
  +th: Maybe<&2, Hashes.Hash>,
  turn: Maybe<&2, String>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.of(n, s, c, w, t, th, turn))) == True{}: Bool}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Plan.when.grows(
        s,
        String.eq(p, n),
        Spec.Plan.own(s, c, t),
        Spec.Plan.copy(s, c, t, th, Spec.Cast.of(s, w, p)),
        Plan.own.grows(s, c, t),
        Plan.copy.grows(s, c, t, th, Spec.Cast.of(s, w, p))
      )

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  a: Spec.State(),
  b: Spec.State(),
  x: Spec.State(),
  e: {Spec.State.ledger(x) == Spec.State.ledger(b): Ledgers.State(Spec.Ask)},
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Node.grows(a, x) == True{}: Bool}:
  %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(x), Spec.State.ledger(b), e): {
    Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(a), _) == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  s: Spec.State(),
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
  c: Ledgers.Chain,
  h: Spec.Head,
  qs: List<&2, Ledgers.Id>
) -> {Spec.State.ledger(Spec.State.moved(s, c, h, qs)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  s: Spec.State(),
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {Spec.State.ledger(Spec.State.wait(s, c, i)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# a node with the ledger of a node that grew from it grew
def Grows.back(
  s: Spec.State(),
  s3: Spec.State(),
  g: {Spec.Node.grows(s, s3) == True{}: Bool}
) -> {Spec.Node.grows(s, Spec.State.led(s, Spec.State.ledger(s3))) == True{}: Bool}:
  Grows.led(s, Spec.State.ledger(s3), g)

# new keys keep the ledger
def Led.keyed(
  s: Spec.State(),
  ks: Spec.Keys
) -> {Spec.State.ledger(Spec.State.keyed(s, ks)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)}:
  match s:
    case Spec.Node{l, hs, ws, old}:
      {==}

# a ballot that a node accepts only grows it
def Accept.at.grows(
  +s: Spec.State(),
  +b: Ledgers.Ballot,
  m: Maybe<&2, Spec.Chained>
) -> {State.after(s, Spec.Seal.accept.at(s, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Put.grows.if(
        s,
        Spec.State.keyed(
        Spec.State.led(
          s,
          Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
        ),
        Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b))
      ),
        Spec.Seal.fits(c, b),
        Grows.to(
          s,
          Spec.State.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)),
          Spec.State.keyed(
        Spec.State.led(
          s,
          Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
        ),
        Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b))
      ),
          Led.keyed(Spec.State.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)), Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b))),
          Grows.led(
            s,
            Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b),
            Ledgers.State.add_grows(
              ~Spec.Ask,
              ~Spec.Ask.is_eq,
              ~Ask.laws(),
              Spec.State.ledger(s),
              Ledgers.Slot.of(b),
              Ledgers.Entry.Vote{b}
            )
          )
        )
      )

# the node m, if any, else s, grew from s when m did
def Default.grows(
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>
) -> {State.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Maybe.default(&2, Spec.State(), m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{s2}:
      e => e

# a sealed ballot only grows a node
def Cast.seal.grows(
  +s: Spec.State(),
  +w: Ledgers.Where,
  n: String,
  v: Ledgers.Vote,
  m: Maybe<&2, Spec.Chained>
) -> {Spec.Node.grows(s, Spec.Cast.seal(s, w, n, v, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Spec.Chained{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), j),
        Ledgers.Signed{w, n, Ledgers.Act.Vote{v, []}},
        last,
        Seals.Seal.public(
          Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), U32.inc(j))
        )
      )
      Default.grows(s, Spec.Seal.accept(s, b))(
        Accept.at.grows(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b)))
      )

# a ballot on a node that grew from a, which grew from s, only grows s
def Cast.vote.grows(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +w: Ledgers.Where,
  +n: String,
  +v: Ledgers.Vote,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {State.after(a, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Cast.vote(s, m, w, n, v)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +s4 = Spec.State.led(s, Spec.State.ledger(s3))
        Grows.trans(s, s4, Spec.Cast.seal(s4, w, n, v, Spec.Seal.chain(s4, Spec.Where.store(w), n)))(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(Cast.seal.grows(s4, w, n, v, Spec.Seal.chain(s4, Spec.Where.store(w), n)))

# a ballot only grows a node
def Cast.put.grows(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  s: Spec.State()
) -> {Run.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Cast.put(n, w, th, qs, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Run{+s2, +t2, ns}}:
      e => Cast.vote.grows(
        s,
        s2,
        Spec.State.put(s2, [Spec.Tip.words(t2)]),
        w,
        n,
        Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}},
        e
      )(Put.grows(s2, [Spec.Tip.words(t2)]))

# Node.cast only grows a node, at the head h whose tip is m
def Cast.at.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.grows(s, Spec.Cast.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Spec.Head{r, b, +next, +th} Some{+t}:
      +p = Spec.Plan.of(n, s, c, Ledgers.Where{c, next, 0}, t, th, Spec.Owners.turn(Spec.Line.owners(s, t), next))
      +qs = Spec.Plan.asks(p)
      Grows.when(
        s,
        Spec.Cast.may(n, s, Ledgers.Where{c, next, 0}, t, qs),
        Spec.Cast.put(n, Ledgers.Where{c, next, 0}, th, qs, Spec.Plan.run(p), s),
        s,
        Cast.put.grows(
          n,
          Ledgers.Where{c, next, 0},
          th,
          qs,
          Spec.Plan.run(p),
          s
        )(
          Plan.of.grows(
            n,
            s,
            c,
            Ledgers.Where{c, next, 0},
            t,
            th,
            Spec.Owners.turn(Spec.Line.owners(s, t), next)
          )
        ),
        Grows.refl(s)
      )
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.cast only grows a node, once the head m is known
def Cast.head.grows(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Cast.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Cast.at.grows(n, s, c, h, Spec.Head.tip(s, h))

# a node's ballot only grows it
def Cast.grows(
  n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Node.cast(n, s, c)) == True{}: Bool}:
  Cast.head.grows(n, s, c, Spec.Node.head_of(s, c))

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  +h: Spec.Head,
  +qs: List<&2, Ledgers.Id>,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {State.after(a, m) == True{}: Bool} -> {
  Spec.Node.grows(s, Spec.Advance.moved(s, m, c, h, qs)) == True{}: Bool
}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Spec.State.led(s, Spec.State.ledger(s3))
        Grows.to(
          s,
          x,
          Spec.State.moved(x, c, h, qs),
          Led.moved(x, c, h, qs),
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )

# a checked step only grows a node
def Advance.ran.grows(
  +s: Spec.State(),
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Advance.ran(s, c, r, b, next, after, qs, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Run{+s2, +t2, ns}}:
      e =>
        +hd = {Spec.Head{r, b, U32.inc(next), Some{Spec.Tip.hash(t2)}}: Spec.Head}
        Grows.when(
          s,
          Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
          Spec.Advance.moved(s, Spec.State.put(s2, [Spec.Tip.words(t2)]), c, hd, qs),
          s,
          Advance.moved.grows(
            s,
            s2,
            Spec.State.put(s2, [Spec.Tip.words(t2)]),
            c,
            hd,
            qs,
            e
          )(Put.grows(s2, [Spec.Tip.words(t2)])),
          Grows.refl(s)
        )

# Node.advance only grows a node, once the decided step m is known
def Advance.step.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  +t: Spec.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Node.grows(s, Spec.Advance.step(s, c, h, t, m)) == True{}: Bool}:
  match h m:
    case Spec.Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Grows.when(
        s,
        Spec.Root.same(before, th),
        Spec.Advance.ran(s, c, r, b, next, after, qs, Spec.Step.run(s, c, t, qs)),
        s,
        Advance.ran.grows(
          s,
          c,
          r,
          b,
          next,
          after,
          qs,
          Spec.Step.run(s, c, t, qs)
        )(Run.grows(s, c, t, qs)),
        Grows.refl(s)
      )
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.grows(s, Spec.Advance.at(s, c, h, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+t}:
      Advance.step.grows(
        s,
        c,
        h,
        t,
        Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h))))
      )

# Node.advance only grows a node, once the head m is known
def Advance.head.grows(
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Advance.head(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Advance.at.grows(s, c, h, Spec.Head.tip(s, h))

# a head that moves only grows a node
def Advance.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Node.advance(s, c)) == True{}: Bool}:
  Advance.head.grows(s, c, Spec.Node.head_of(s, c))

# Advances.grows once the head m is known
def Advances.at.grows(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Advances.at(f, s, c, m)) == True{}: Bool}:
  match f m:
    case 0n x:
      Grows.refl(s)
    case 1n+p None{}:
      Grows.refl(s)
    case 1n+(+p) Some{+h}:
      +s1 = Spec.Advance.at(s, c, h, Spec.Head.tip(s, h))
      +m1 = Spec.Node.head_of(s1, c)
      Grows.when(
        s,
        Spec.Heads.level(Some{h}, m1),
        s1,
        Spec.Advances.at(p, s1, c, m1),
        Advance.at.grows(s, c, h, Spec.Head.tip(s, h)),
        Grows.trans(s, s1, Spec.Advances.at(p, s1, c, m1))(
          Advance.at.grows(s, c, h, Spec.Head.tip(s, h))
        )(Advances.at.grows(p, s1, c, m1))
      )

# a head that moves over each decided step only grows a node
def Advances.grows(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Node.advances(f, s, c)) == True{}: Bool}:
  Advances.at.grows(f, s, c, Spec.Node.head_of(s, c))

# what a node does at a head only grows it
def Step.head.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Step.head(n, s, c)) == True{}: Bool}:
  +s1 = Spec.Node.advances(4294967295n, s, c)
  +s2 = Spec.Node.cast(n, s1, c)
  +s3 = Spec.Node.advances(4294967295n, s2, c)
  Grows.trans(s, s1, s3)(Advances.grows(4294967295n, s, c))(
    Grows.trans(s1, s2, s3)(Cast.grows(n, s1, c))(Advances.grows(4294967295n, s2, c))
  )

# a line that opens only grows a node, once its head m is known
def Open.at.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Open.at(s, c, m)) == True{}: Bool}:
  match m:
    case Some{Spec.Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Spec.Head{
          r,
          Some{b},
          0,
          Spec.Branch.first(s, b, Spec.Node.tip(s, Ledgers.Chain{r, None{}}))
        }: Spec.Head
      }
      Grows.to(s, s, Spec.State.head(s, c, hd), Led.head(s, c, hd), Grows.refl(s))
    case Some{Spec.Head{r, Some{b}, n, Some{t}}}:
      Grows.refl(s)
    case Some{Spec.Head{r, None{}, n, t}}:
      Grows.refl(s)
    case None{}:
      Grows.refl(s)

# what a node does on a line only grows it
def Step.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Node.step(n, s, c)) == True{}: Bool}:
  +s1 = Spec.Node.open(s, c)
  Grows.trans(s, s1, Spec.Step.head(n, s1, c))(
    Open.at.grows(s, c, Spec.Node.head_of(s, c))
  )(Step.head.grows(n, s1, c))

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.First.at(s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Spec.Head{r, b, n, Some{t}}}:
      Grows.refl(s)
    case Some{Spec.Head{r, b, n, None{}}}:
      Grows.to(s, s, Spec.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))
    case None{}:
      Grows.to(s, s, Spec.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  +h: Spec.Head,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {State.after(a, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Start.head(s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Spec.State.led(s, Spec.State.ledger(s3))
        Grows.trans(s, x, Spec.State.first(x, c, h))(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(First.at.grows(x, c, h, Spec.Node.head_of(x, c)))

# a work on a node that grew from b is on one that grew from a, when b grew
# from a
def Work.after.trans(
  a: Spec.State(),
  b: Spec.State(),
  m: Maybe<&2, Spec.Work>,
  e1: {Spec.Node.grows(a, b) == True{}: Bool},
  e2: {Work.after(b, m) == True{}: Bool}
) -> {Work.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Work{s3, h, ns}}:
      Grows.trans(a, b, s3)(e1)(e2)

# a key set in a work on a node that grew from s is on a node that grew from s
def Work.set.after(
  s: Spec.State(),
  m: Maybe<&2, Spec.Work>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {Work.after(s, m) == True{}: Bool} -> {
  Work.after(s, Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Spec.Work.set(w, k, x))) == True{}: Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{Spec.Work{+s2, +h, +ns}}:
      e => Work.after.trans(
        s,
        s2,
        Spec.Work.set(Spec.Work{s2, h, ns}, k, x),
        e,
        Set.grows(s2, h, ns, k, x)
      )

# the first keys of a store are on a node that grew
def Firsts.after(
  +s: Spec.State(),
  os: List<&2, Spec.Owner>,
  +m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> {Work.after(s, Spec.Seal.firsts(os, m)) == True{}: Bool}:
  match os:
    case Nil{}:
      e => e
    case Con{Spec.Owner{+n, +k}, r}:
      e => Firsts.after(
        s,
        r,
        Maybe.bind(
          &2,
          Spec.Work,
          Spec.Work,
          m,
          w => Spec.Work.set(w, Spec.Key.seal(n), Hashes.Hash.code(k, []))
        )
      )(Work.set.after(s, m, Spec.Key.seal(n), Hashes.Hash.code(k, []))(e))

# the first log of a line is on a node that grew
def Log.first.after(
  s: Spec.State(),
  w: Spec.Work,
  +os: List<&2, String>
) -> {Work.after(s, Some{w}) == True{}: Bool} -> {Work.after(s, Spec.Log.first(w, os)) == True{}: Bool}:
  match w:
    case Spec.Work{+s2, h, +ns}:
      e => Work.after.trans(
        s,
        s2,
        Spec.Work.set(Spec.Work{s2, None{}, ns}, Spec.Log.owners(), Ledgers.Owners.code(os, [])),
        e,
        Set.grows(s2, None{}, ns, Spec.Log.owners(), Ledgers.Owners.code(os, []))
      )

# the first tip of a store only grows a node
def Start.put.grows(
  s: Spec.State(),
  +i: Ledgers.Id,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Start.put(s, i, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Spec.Work{+s2, l, ns}}:
      e =>
        +t = {Spec.Tip{c, l}: Spec.Tip}
        Start.head.grows(
          s,
          s2,
          Spec.State.put(s2, [Spec.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Spec.Head{i, None{}, 0, Some{Spec.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Spec.Tip.words(t)]))

# Start.grows once the content m of the store is known
def Start.with.grows(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Spec.Start.with(s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+w}:
      e => Start.put.grows(s, i, Spec.Work.root(w), Spec.Log.first(w, os))(Log.first.after(s, w, os)(e))

# a store that starts only grows a node
def Start.grows(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, Spec.Owner>
) -> {Spec.Node.grows(s, Spec.Node.start(s, i, os)) == True{}: Bool}:
  Start.with.grows(
    s,
    i,
    Spec.Owner.names(os),
    Spec.Seal.firsts(os, Some{Spec.Work{s, None{}, []}})
  )(Firsts.after(s, os, Some{Spec.Work{s, None{}, []}})(Grows.refl(s)))

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
        Spec.State.head(s, Spec.Line.chain(r, l), Spec.Head{r, l, 0, None{}}),
        Led.head(s, Spec.Line.chain(r, l), Spec.Head{r, l, 0, None{}}),
        Grows.refl(s)
      )

# a new request only grows a node
def Arrive.grows(
  +s: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> {Spec.Node.grows(s, Spec.Node.arrive(s, i, q)) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
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

# a new request only grows a node
def Ask.new.grows(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask
) -> {Spec.Node.grows(s, Spec.Node.ask.new(n, s, e, q)) == True{}: Bool}:
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
  Grows.trans(s, s0, Spec.Node.step(n, s1, c))(
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
    Grows.trans(s0, s1, Spec.Node.step(n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c))
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
      Grows.trans(s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), Spec.Node.ask.new(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), e, q))(
        Grows.to(s, s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), Grows.refl(s))
      )(Ask.new.grows(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), e, q))

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
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Take.asks(cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(Spec.State(), Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))), u => Spec.Node.arrive(s, i, q), u => s)
      Grows.trans(s, s1, Spec.Take.asks(rest, old, s1))(
        Grows.when(s, Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))), Spec.Node.arrive(s, i, q), s, Arrive.grows(s, i, q), Grows.refl(s))
      )(Take.asks.grows(rest, old, s1))
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.grows(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.grows(rest, old, s)

# the ballots that a chain leads to only grow a node, when each one more does
def Follow.step.grows(
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  k: Spec.State() -> Spec.State(),
  ih: @s2: Spec.State() -> {Spec.Node.grows(s2, k(s2)) == True{}: Bool}
) -> {State.after(s, m) == True{}: Bool} -> {Spec.Node.grows(s, Maybe.default(&2, Spec.State(), Maybe.bind(&2, Spec.State(), Spec.State(), m, s2 => Some{k(s2)}), s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s2}:
      e => Grows.trans(s, s2, k(s2))(e)(ih(s2))

# the ballots that a chain leads to only grow a node
def Follow.grows(
  f: Nat,
  +s: Spec.State(),
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {Spec.Node.grows(s, Spec.Sealed.follow(f, s, p, r, n, mb)) == True{}: Bool}:
  match f mb:
    case 0n x:
      Grows.refl(s)
    case 1n+g None{}:
      Grows.refl(s)
    case 1n+(+g) Some{+b}:
      Follow.step.grows(
        s,
        Spec.Seal.accept(s, b),
        +s2 => Spec.Sealed.follow(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n)),
        +s2 => Follow.grows(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n))
      )(Accept.at.grows(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b))))

# the ballots that the chains of some ballots lead to only grow a node
def Each.grows(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Sealed.each(f, bs, p, s)) == True{}: Bool}:
  match bs:
    case Nil{}:
      Grows.refl(s)
    case Con{+b, +rest}:
      +s1 = Spec.Sealed.follow(
        f,
        s,
        p,
        Spec.Ballot.store(b),
        Spec.Ballot.node(b),
        Spec.Pending.next(s, p, Spec.Ballot.store(b), Spec.Ballot.node(b))
      )
      Grows.trans(s, s1, Spec.Sealed.each(f, rest, p, s1))(
        Follow.grows(
          f,
          s,
          p,
          Spec.Ballot.store(b),
          Spec.Ballot.node(b),
          Spec.Pending.next(s, p, Spec.Ballot.store(b), Spec.Ballot.node(b))
        )
      )(Each.grows(f, rest, p, s1))

def Spec.Node.take_grows(s, t):
  +sent = Spec.Take.clean(Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t), Ledgers.State.empty(~Spec.Ask))
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s)))
  )
  Grows.trans(s, s1, Spec.Sealed.take(bs, s2))(
    Grows.led(
      s,
      l1,
      Ledgers.State.take_grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), Spec.State.ledger(s), sent)
    )
  )(
    Grows.trans(s1, s2, Spec.Sealed.take(bs, s2))(Take.asks.grows(cs, Spec.State.ledger(s), s1))(
      Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2)
    )
  )

# what a node does on each of some lines only grows it
def Steps.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Node.steps(n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{+c, +rest}:
      +s1 = Spec.Node.step(n, s, c)
      Grows.trans(s, s1, Spec.Node.steps(n, rest, s1))(Step.grows(n, s, c))(Steps.grows(n, rest, s1))

def Spec.Node.sync_grows(n, s, t):
  +s1 = Spec.Node.take(s, t)
  +cs = Spec.Sync.lines(s, s1, t)
  Grows.trans(s, s1, Spec.Node.steps(n, cs, s1))(Spec.Node.take_grows(s, t))(Steps.grows(n, cs, s1))

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

# a node that took in a new request of e holds its slot
def Ask.held.new(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  +em: {Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, Spec.State.ledger(Spec.Node.ask.new(n, s, e, q)), Ledgers.Slot.ask(Spec.Envelope.of(e)))) == True{}: Bool
}:
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
    Spec.Node.step(n, s1, c),
    k,
    Grows.trans(s0, s1, Spec.Node.step(n, s1, c))(
      Arrive.grows(s0, i, q)
    )(Step.grows(n, s1, c))
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

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  em: {Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))) == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, Spec.State.ledger(Spec.Node.ask.at(n, s, e, q, m)), Ledgers.Slot.ask(Spec.Envelope.of(e)))) == True{}: Bool
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
      Ask.held.new(
        n,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        e,
        q,
        (
          %Equal.sym(
            Ledgers.State(Spec.Ask),
            Spec.State.ledger(Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))),
            Spec.State.ledger(s),
            Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))
          ): {Ledgers.State.get(~Spec.Ask, _, Ledgers.Slot.ask(Spec.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
          em
        )
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

# Logs
# ----
# A log only gains keys: a key that a log holds, other than the owners and the
# count, holds the same value after any step.

# a read of a tree stays in a node that grew
def Get.grows(
  +a: Spec.State(),
  +b: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {
  Spec.Node.get(a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Node.get(b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Equal.trans(
    Maybe<&2, List<&2, U32>>,
    Spec.Node.get(b, h, k),
    Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, b, h, k),
    Some{v},
    Get.is(b, h, k),
    Trees.Tree.get_grows(
      ~Spec.State(),
      ~Spec.Store.fetch,
      ~Spec.Node.grows,
      ~(
        x => y => hh => w => Ledgers.State.data_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          Spec.State.ledger(x),
          Spec.State.ledger(y),
          hh,
          w
        )
      ),
      a,
      b,
      h,
      k,
      v
    )(g)(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, a, h, k),
        Spec.Node.get(a, h, k),
        Some{v},
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(a, h, k),
          Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, a, h, k),
          Get.is(a, h, k)
        ),
        e
      )
    )
  )

# that the work m, if any, reads the key k2 as v
def Work.Keeps(k2: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Spec.Work>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Spec.Work{s2, h2, ns2}}:
      {Spec.Node.get(s2, h2, k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# Set.kept once whether the node holds the new nodes is known (b)
def Set.kept.if(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  v: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ws), ws) == b: Bool},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Spec.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>},
  em: {Spec.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Work.Keeps(
  k2,
  v,
  Spec.Work.put(
    Shared.Maybe.when(Spec.State(), b, u => Some{Spec.State.keep(s, ws)}),
    Some{hh},
    ws,
    ns
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +sk = Spec.State.keep(s, ws)
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Spec.Node.get(sk, Some{hh}, k2),
        Spec.Node.get(sk, h, k2),
        Some{v},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(sk, Some{hh}, k2),
          Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, sk, Some{hh}, k2),
          Spec.Node.get(sk, h, k2),
          Get.is(sk, Some{hh}, k2),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, sk, Some{hh}, k2),
            Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, sk, h, k2),
            Spec.Node.get(sk, h, k2),
            Trees.Tree.get_other(
              ~Spec.State(),
              ~Spec.Store.fetch,
              ~Spec.Node.grows,
              ~(
                p => q => g => w => Ledgers.State.data_grows(
                  ~Spec.Ask,
                  ~Spec.Ask.is_eq,
                  ~Ask.laws(),
                  Spec.State.ledger(p),
                  Spec.State.ledger(q),
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
            )(Grows.keep(s, ws))(hne)(
              Equal.trans(
                Maybe<&2, Trees.Put>,
                Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x),
                Spec.Node.set(s, h, k, x),
                Some{Trees.Put{hh, ws}},
                Equal.sym(
                  Maybe<&2, Trees.Put>,
                  Spec.Node.set(s, h, k, x),
                  Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x),
                  Set.is(s, h, k, x)
                ),
                em
              )
            )(eb),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Spec.Node.get(sk, h, k2),
              Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, sk, h, k2),
              Get.is(sk, h, k2)
            )
          )
        ),
        Get.grows(s, sk, h, k2, v, Grows.keep(s, ws))(hget)
      )

# Set.kept once the new subtree m is known
def Set.kept.of(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  em: {Spec.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Spec.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Keeps(k2, v, Spec.Work.of(s, ns, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, +ws}}:
      Set.kept.if(
        s,
        h,
        ns,
        k,
        x,
        k2,
        v,
        hh,
        ws,
        Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ws), ws),
        {==},
        hne,
        hget,
        em
      )

# a key set in a tree keeps the value of each other key
def Set.kept(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Spec.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Work.Keeps(k2, v, Spec.Work.set(Spec.Work{s, h, ns}, k, x)):
  Set.kept.of(
    s,
    h,
    ns,
    k,
    x,
    k2,
    v,
    Spec.Node.set(s, h, k, x),
    {==},
    hne,
    hget
  )

# that the log of the run m, if any, reads the key k2 as v
def Run.Keeps(k2: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Spec.Run>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Spec.Run{s2, t2, ns}}:
      {Spec.Node.get(s2, Spec.Tip.log(t2), k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# the run of a new log that keeps a key keeps it
def Run.of.keeps(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Spec.Work>
) -> Work.Keeps(k2, v, m) -> Run.Keeps(k2, v, Spec.Run.of(c, m)):
  match m:
    case None{}:
      w => Unit{}
    case Some{Spec.Work{s2, l, ns}}:
      w => w

# a key set in a run's log keeps the value of each other key
def Log.kept(
  r: Spec.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Run.log(r, k, x)):
  match r:
    case Spec.Run{+s, Spec.Tip{c, +l}, +ns}:
      hr => Run.of.keeps(
        k2,
        v,
        c,
        Spec.Work.set(Spec.Work{s, l, ns}, k, x)
      )(Set.kept(s, l, ns, k, x, k2, v, hne, hr))

# a key that a tree does not hold is not a key that it holds, once whether
# they are the same is known (b)
def Keys.differ.if(
  s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == b: Bool},
  e1: {Spec.Node.get(s, h, k) == None{}: Maybe<&2, List<&2, U32>>},
  e2: {Spec.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
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
            Spec.Node.get(s, h, k),
            Some{v},
            Equal.sym(Maybe<&2, List<&2, U32>>, Spec.Node.get(s, h, k), None{}, e1),
            (
              %Equal.sym(
                List<&2, U32>,
                k,
                k2,
                Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)
              ): {Spec.Node.get(s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2
            )
          )
        )
      )

# Add.kept when the log does not hold the new key
def Add.new.kept(
  +s: Spec.State(),
  c: Maybe<&2, Hashes.Hash>,
  +l: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Spec.Node.get(s, l, k) == None{}: Maybe<&2, List<&2, U32>>},
  +hr: {Spec.Node.get(s, l, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(k2, v, Spec.Run.log(Spec.Run{s, Spec.Tip{c, l}, ns}, k, x)):
  Log.kept(
    Spec.Run{s, Spec.Tip{c, l}, ns},
    k,
    x,
    k2,
    v,
    Keys.differ.if(
      s,
      l,
      k,
      k2,
      v,
      Shared.List.is_eq(~U32, ~U32.is_eq, k, k2),
      {==},
      em,
      hr
    )
  )(hr)

# Add.kept once the value m of the new key is known
def Add.at.kept(
  r: Spec.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Spec.Node.get(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), k) == m: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Run.add.at(r, k, x, m)):
  match r m:
    case Spec.Run{s, Spec.Tip{c, l}, ns} Some{old}:
      em => hr => Unit{}
    case Spec.Run{+s, Spec.Tip{+c, +l}, +ns} None{}:
      em => hr => Add.new.kept(s, c, l, ns, k, x, k2, v, em, hr)

# a new key in a run's log keeps the value of each key that the log holds
def Add.kept(
  +r: Spec.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Run.add(r, k, x)):
  Add.at.kept(
    r,
    k,
    x,
    k2,
    v,
    Spec.Node.get(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), k)
  )({==})

# Content.kept once whether the node holds the new nodes is known (b)
def Content.kept.if(
  +s: Spec.State(),
  l: Maybe<&2, Hashes.Hash>,
  h: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  hr: {Spec.Node.get(s, l, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(
  k2,
  v,
  Spec.Run.put(
    Shared.Maybe.when(Spec.State(), b, u => Some{Spec.State.keep(s, ds)}),
    Spec.Tip{h, l},
    ds,
    ns
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Get.grows(s, Spec.State.keep(s, ds), l, k2, v, Grows.keep(s, ds))(hr)

# new content keeps each key of a run's log
def Content.kept(
  r: Spec.Run,
  h: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Run.content(r, h, ds)):
  match r:
    case Spec.Run{+s, Spec.Tip{c, l}, ns}:
      hr => Content.kept.if(
        s,
        l,
        h,
        ds,
        ns,
        k2,
        v,
        Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ds), ds),
        hr
      )

# a run, then a run from it that keeps a key, keeps it
def Keeps.bind(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Spec.Run>,
  -f: Spec.Run -> Maybe<&2, Spec.Run>
) -> Run.Keeps(
  k2,
  v,
  m
) -> (@r: Spec.Run -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, f(r))) -> Run.Keeps(
  k2,
  v,
  Maybe.bind(&2, Spec.Run, Spec.Run, m, f)
):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{r}:
      hm => hf => hf(r)(hm)

# one of two runs, each of which keeps a key that the run r keeps
def Keeps.when(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Spec.Run,
  b: Bool,
  -mx: Maybe<&2, Spec.Run>,
  -my: Maybe<&2, Spec.Run>,
  hx: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, mx),
  hy: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, my)
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Shared.Bool.when(Maybe<&2, Spec.Run>, b, u => mx, u => my)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new owners keep each other key of a run's log
def Owners.kept(
  r: Spec.Run,
  m: Maybe<&2, List<&2, String>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Run.owners(r, m)):
  match m:
    case None{}:
      hr => hr
    case Some{os}:
      hr => Log.kept(r, Spec.Log.owners(), Ledgers.Owners.code(os, []), k2, v, n0)(hr)

# a taken request keeps each key of a run's log, other than the owners and
# the count
def Taken.kept(
  +r: Spec.Run,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.taken(r, i, own)):
  +n = Spec.Line.count(Spec.Run.state(r), Spec.Run.tip(r))
  hr => Keeps.bind(
    k2,
    v,
    Spec.Run.add(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Spec.Run,
      Spec.Run,
      Spec.Run.add(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))})
      ),
      r2 => Maybe.bind(
        &2,
        Spec.Run,
        Spec.Run,
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own)
      )
    )
  )(
    Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n}), k2, v)(hr)
  )(
    +r1 => h1 => Keeps.bind(
      k2,
      v,
      Spec.Run.add(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))})
      ),
      r2 => Maybe.bind(
        &2,
        Spec.Run,
        Spec.Run,
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own)
      )
    )(
      Add.kept(
        r1,
        Spec.Log.version(n),
        Spec.Version.words(Spec.Version{i, Spec.Tip.content(Spec.Run.tip(r1))}),
        k2,
        v
      )(h1)
    )(
      +r2 => h2 => Keeps.bind(
        k2,
        v,
        Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
        r3 => Spec.Run.owners(r3, own)
      )(
        Log.kept(r2, Spec.Log.count(), [U32.inc(n)], k2, v, n1)(h2)
      )(r3 => h3 => Owners.kept(r3, own, k2, v, n0)(h3))
    )
  )

# a judged request keeps each key of a run's log, other than the owners and
# the count
def Judged.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Spec.Verdict>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.judged(r, i, own, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Spec.Verdict{False{}, h, ds}}:
      hr => Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)(hr)
    case Some{Spec.Verdict{True{}, +h, +ds}}:
      hr => Keeps.bind(
        k2,
        v,
        Spec.Run.content(r, h, ds),
        r2 => Spec.Step.taken(r2, i, own)
      )(Content.kept(r, h, ds, k2, v)(hr))(r2 => h2 => Taken.kept(r2, i, own, k2, v, n0, n1)(h2))

# a mark on a version keeps each key of a run's log, other than the owners
# and the count
def Marked.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  +m: String,
  x: Maybe<&2, Spec.Version>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.marked(r, i, m, x)):
  match x:
    case None{}:
      hr => Unit{}
    case Some{+y}:
      hr => Keeps.bind(
        k2,
        v,
        Spec.Run.add(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(y), [])),
        r2 => Spec.Step.taken(r2, i, None{})
      )(
        Add.kept(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(y), []), k2, v)(hr)
      )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v, n0, n1)(h2))

# a request for a mark keeps each key of a run's log, other than the owners
# and the count
def Mark.kept(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +m: String,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.mark(r, i, m)):
  +s = Spec.Run.state(r)
  +t = Spec.Run.tip(r)
  +n = Spec.Line.count(s, t)
  Keeps.when(
    k2,
    v,
    r,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Spec.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Spec.Step.marked(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1))),
    Spec.Step.stale(r, i),
    Marked.kept(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1)), k2, v, n0, n1),
    Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)
  )

# a change of a line keeps each key of a run's log, other than the owners and
# the count
def On.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  ch: Spec.Change,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.on(r, i, st, l, ch)):
  match l ch:
    case None{} Spec.Change.Branch{+a, +b}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Group{+a, +b}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Own{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Write{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Resolve{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Merge{+a}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Move{+a}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case None{} Spec.Change.Mark{+a, +b}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{x} Spec.Change.Branch{+a, +b}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Group{+a, +b}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Own{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Write{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Resolve{+a, +b, +c}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Merge{+a}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Move{+a}:
      hr => Judged.kept(
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
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Mark{a, b}:
      hr => Mark.kept(r, i, a, k2, v, n0, n1)(hr)
    case None{} Spec.Change.Key{+a, +b}:
      hr => Judged.kept(
        r,
        i,
        Spec.Change.owners(Spec.Change.Key{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          None{},
          Spec.Change.Key{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        ),
        k2,
        v,
        n0,
        n1
      )(hr)
    case Some{+x} Spec.Change.Key{+a, +b}:
      hr => Judged.kept(
        r,
        i,
        Spec.Change.owners(Spec.Change.Key{a, b}),
        Spec.Judge.change(
          Spec.Run.state(r),
          st,
          Some{x},
          Spec.Change.Key{a, b},
          Spec.Tip.content(Spec.Run.tip(r)),
          Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
        ),
        k2,
        v,
        n0,
        n1
      )(hr)

# a request keeps each key of a run's log, other than the owners and the count
def Change.kept(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Spec.Ask,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.change(r, c, i, q)):
  match q:
    case Spec.Ask.Start{os}:
      hr => Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)(hr)
    case Spec.Ask.On{+st, +l, ch}:
      Keeps.when(
        k2,
        v,
        r,
        Ledgers.Chain.is_eq(Spec.Line.chain(st, l), c),
        Spec.Step.on(r, i, st, l, ch),
        Spec.Step.stale(r, i),
        On.kept(r, i, st, l, ch, k2, v, n0, n1),
        Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)
      )

# a request that the node holds or not keeps each key of a run's log
def Asked.kept(
  r: Spec.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Spec.Ask>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.asked(r, c, i, a)):
  match a:
    case None{}:
      hr => Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.kept(r, c, i, q, k2, v, n0, n1)

# a request that the log holds or not keeps each key of a run's log
def Fresh.kept(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Spec.Out>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Step.fresh(r, c, i, o)):
  match o:
    case Some{x}:
      hr => hr
    case None{}:
      Asked.kept(r, c, i, Spec.Node.asked(Spec.Run.state(r), i), k2, v, n0, n1)

# the requests of a step keep each key of a run's log, other than the owners
# and the count
def All.kept(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Spec.Run>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  +n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  +n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, m) -> Run.Keeps(k2, v, Spec.Step.all(c, qs, m)):
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.kept(
        c,
        rest,
        Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, i)),
        k2,
        v,
        n0,
        n1
      )(
        Keeps.bind(
          k2,
          v,
          m,
          r => Spec.Step.one(r, c, i)
        )(
          h
        )(
          +r => hr => Fresh.kept(
            r,
            c,
            i,
            Spec.Line.out(Spec.Run.state(r), Spec.Run.tip(r), i),
            k2,
            v,
            n0,
            n1
          )(hr)
        )
      )

# a log only gains keys: a key that the log of a tip holds, other than the
# owners and the count, holds the same value after a step
def Run.kept(
  s: Spec.State(),
  c: Ledgers.Chain,
  t: Spec.Tip,
  qs: List<&2, Ledgers.Id>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> {
  Spec.Node.get(s, Spec.Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Spec.Step.run(s, c, t, qs)):
  match t:
    case Spec.Tip{c0, l}:
      h => All.kept(c, qs, Some{Spec.Run{s, Spec.Tip{c0, l}, []}}, k2, v, n0, n1)(h)

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  +a: Spec.State(),
  b: Spec.State(),
  +x: Hashes.Hash,
  -t: Spec.Tip,
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Tip.at(a, x) == Some{t}: Maybe<&2, Spec.Tip>} -> {Spec.Tip.at(b, x) == Some{t}: Maybe<&2, Spec.Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Spec.Tip,
    Spec.Store.fetch(a, x),
    Spec.Store.fetch(b, x),
    ws => Spec.Tip.read(ws),
    ws => Spec.Tip.read(ws),
    t,
w => Ledgers.State.data_grows(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      Spec.State.ledger(a),
      Spec.State.ledger(b),
      x,
      w
    )(g),
w => e => e
)

# the tip of a head, in a node that grew
def Head.tip.grows(
  a: Spec.State(),
  b: Spec.State(),
  h: Spec.Head,
  -t: Spec.Tip,
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Head.tip(a, h) == Some{t}: Maybe<&2, Spec.Tip>} -> {
  Spec.Head.tip(b, h) == Some{t}: Maybe<&2, Spec.Tip>
}:
  match h:
    case Spec.Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Spec.Tip,
        th,
        th,
        x => Spec.Tip.at(a, x),
        x => Spec.Tip.at(b, x),
        t,
x => e => e,
+x => Tip.at.grows(a, b, x, t, g)
)

# what the log of a head holds, in a node that grew
def Head.get.grows(
  +a: Spec.State(),
  +b: Spec.State(),
  +h: Spec.Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Head.get(a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Head.get(b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Spec.Tip,
    List<&2, U32>,
    Spec.Head.tip(a, h),
    Spec.Head.tip(b, h),
    t => Spec.Node.get(a, Spec.Tip.log(t), k),
    t => Spec.Node.get(b, Spec.Tip.log(t), k),
    v,
t => Head.tip.grows(a, b, h, t, g),
t => Get.grows(a, b, Spec.Tip.log(t), k, v, g)
)

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  +a: Spec.State(),
  b: Spec.State(),
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  eh: {Spec.Node.head_of(a, c) == Spec.Node.head_of(b, c): Maybe<&2, Spec.Head>}
) -> {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Line.get(b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Spec.Head,
    List<&2, U32>,
    Spec.Node.head_of(a, c),
    Spec.Node.head_of(b, c),
    h => Spec.Head.get(a, h, k),
    h => Spec.Head.get(b, h, k),
    v,
h => e => Equal.trans(
      Maybe<&2, Spec.Head>,
      Spec.Node.head_of(b, c),
      Spec.Node.head_of(a, c),
      Some{h},
      Equal.sym(Maybe<&2, Spec.Head>, Spec.Node.head_of(a, c), Spec.Node.head_of(b, c), eh),
      e
    ),
+h => Head.get.grows(a, b, h, k, v, g)
)

# a node keeps its own logs
def Kept.refl(-s: Spec.State()) -> Spec.Node.Keeps(s, s):
  c => k => v => n0 => n1 => e => e

# keeping composes
def Kept.trans(
  -a: Spec.State(),
  -b: Spec.State(),
  -d: Spec.State(),
  h1: Spec.Node.Keeps(a, b),
  h2: Spec.Node.Keeps(b, d)
) -> Spec.Node.Keeps(a, d):
  +c => +k => +v => +n0 => +n1 => e => h2(c)(k)(v)(n0)(n1)(h1(c)(k)(v)(n0)(n1)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  b: Bool,
  -s: Spec.State(),
  -x: Spec.State(),
  -y: Spec.State(),
  hx: Spec.Node.Keeps(s, x),
  hy: Spec.Node.Keeps(s, y)
) -> Spec.Node.Keeps(s, Shared.Bool.when(Spec.State(), b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  a: Spec.State(),
  b: Spec.State(),
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b): Tries.Trie<Spec.Head>}
) -> Spec.Node.Keeps(a, b):
  +c => k => v => n0 => n1 => Line.same(
    a,
    b,
    c,
    k,
    v,
    g,
    Equal.cong(
      Tries.Trie<Spec.Head>,
      Maybe<&2, Spec.Head>,
      hs => Tries.Trie.get(Spec.Head, hs, Ledgers.Chain.key(c)),
      Spec.State.heads(a),
      Spec.State.heads(b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  s: Spec.State(),
  l: Ledgers.State(Spec.Ask)
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.State.led(s, l)): Tries.Trie<Spec.Head>}:
  match s:
    case Spec.Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  s: Spec.State(),
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Wait.set(s, c, qs)): Tries.Trie<Spec.Head>}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  b0: Spec.State(),
  c: Ledgers.Chain,
  hd: Spec.Head,
  c2: Ledgers.Chain
) -> {
  Spec.Node.head_of(Spec.State.head(b0, c, hd), c2)
    == Bool.pick(
      Maybe<&2, Spec.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Spec.Node.head_of(b0, c2)
    ): Maybe<&2, Spec.Head>
}:
  match b0:
    case Spec.Node{l, hs, ws, ks}:
      Tries.Trie.get_set(Spec.Head, hs, Ledgers.Chain.key(c), hd, Ledgers.Chain.key(c2))

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
  -a: Spec.State(),
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Spec.Head>,
  em: {Spec.Node.head_of(a, c) == m: Maybe<&2, Spec.Head>}
) -> {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {
  Maybe.bind(&2, Spec.Head, List<&2, U32>, m, h => Spec.Head.get(a, h, k)) == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {Maybe.bind(&2, Spec.Head, List<&2, U32>, _, h => Spec.Head.get(a, h, k)) == Some{v}: Maybe<&2, List<&2, U32>>}
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  +a: Spec.State(),
  +b0: Spec.State(),
  +c: Ledgers.Chain,
  +hd: Spec.Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Spec.Node.grows(a, b0) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  cov: {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Head.get(Spec.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {Spec.Line.get(a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Line.get(Spec.State.head(b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Spec.Head>,
          Spec.Node.head_of(Spec.State.head(b0, c, hd), c2),
          Some{hd},
          Equal.trans(
            Maybe<&2, Spec.Head>,
            Spec.Node.head_of(Spec.State.head(b0, c, hd), c2),
            Bool.pick(
              Maybe<&2, Spec.Head>,
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Spec.Node.head_of(b0, c2)
            ),
            Some{hd},
            Head.of_set(b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Spec.Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Spec.Node.head_of(b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Spec.Head,
            List<&2, U32>,
            _,
            h => Spec.Head.get(Spec.State.head(b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Spec.Line.get(a, c, k),
            Spec.Line.get(a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Spec.Head,
                List<&2, U32>,
                Tries.Trie.get(Spec.Head, Spec.State.heads(a), kk),
                h => Spec.Head.get(a, h, k)
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
        Spec.State.head(b0, c, hd),
        c2,
        k,
        v,
        Grows.to(a, b0, Spec.State.head(b0, c, hd), Led.head(b0, c, hd), g),
        Equal.trans(
          Maybe<&2, Spec.Head>,
          Spec.Node.head_of(a, c2),
          Spec.Node.head_of(b0, c2),
          Spec.Node.head_of(Spec.State.head(b0, c, hd), c2),
          Equal.cong(
            Tries.Trie<Spec.Head>,
            Maybe<&2, Spec.Head>,
            hs => Tries.Trie.get(Spec.Head, hs, Ledgers.Chain.key(c2)),
            Spec.State.heads(a),
            Spec.State.heads(b0),
            eh
          ),
          Equal.sym(
            Maybe<&2, Spec.Head>,
            Spec.Node.head_of(Spec.State.head(b0, c, hd), c2),
            Spec.Node.head_of(b0, c2),
            Equal.trans(
              Maybe<&2, Spec.Head>,
              Spec.Node.head_of(Spec.State.head(b0, c, hd), c2),
              Bool.pick(
                Maybe<&2, Spec.Head>,
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Spec.Node.head_of(b0, c2)
              ),
              Spec.Node.head_of(b0, c2),
              Head.of_set(b0, c, hd, c2),
              Pick.of(
                Maybe<&2, Spec.Head>,
                False{},
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Spec.Node.head_of(b0, c2),
                ebs
              )
            )
          )
        )
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  a: Spec.State(),
  b0: Spec.State(),
  +c: Ledgers.Chain,
  hd: Spec.Head,
  g: {Spec.Node.grows(a, b0) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  cover: @k: List<&2, U32> -> @v: List<&2, U32> -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool} -> {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Head.get(Spec.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(a, Spec.State.head(b0, c, hd)):
  +c2 => +k => +v => n0 => n1 => Head.put.kept.if(
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
    cover(k)(v)(n0)(n1)
  )

# one of two nodes, each with the heads of s
def Heads.when(
  b: Bool,
  -s: Spec.State(),
  -x: Spec.State(),
  -y: Spec.State(),
  hx: {Spec.State.heads(s) == Spec.State.heads(x): Tries.Trie<Spec.Head>},
  hy: {Spec.State.heads(s) == Spec.State.heads(y): Tries.Trie<Spec.Head>}
) -> {Spec.State.heads(s) == Spec.State.heads(Shared.Bool.when(Spec.State(), b, u => x, u => y)): Tries.Trie<Spec.Head>}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  s: Spec.State(),
  ks: Spec.Keys
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.State.keyed(s, ks)): Tries.Trie<Spec.Head>}:
  match s:
    case Spec.Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(s: Spec.State(), m: Maybe<&2, Spec.State()>) -> Tries.Trie<Spec.Head>:
  match m:
    case None{}:
      Spec.State.heads(s)
    case Some{s2}:
      Spec.State.heads(s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  b: Bool,
  -s: Spec.State(),
  -x: Spec.State(),
  hx: {Spec.State.heads(s) == Spec.State.heads(x): Tries.Trie<Spec.Head>}
) -> {Spec.State.heads(s) == Heads.of(s, Shared.Maybe.when(Spec.State(), b, u => Some{x})): Tries.Trie<Spec.Head>}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  +s: Spec.State(),
  +b: Ledgers.Ballot,
  m: Maybe<&2, Spec.Chained>
) -> {Spec.State.heads(s) == Heads.of(s, Spec.Seal.accept.at(s, b, m)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(
        Spec.Seal.fits(c, b),
        s,
        Spec.State.keyed(
        Spec.State.led(
          s,
          Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
        ),
        Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b))
      ),
        Equal.trans(
          Tries.Trie<Spec.Head>,
          Spec.State.heads(s),
          Spec.State.heads(Spec.State.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b))),
          Spec.State.heads(Spec.State.keyed(
        Spec.State.led(
          s,
          Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
        ),
        Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b))
      )),
          Heads.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)),
          Heads.keyed(Spec.State.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)), Spec.Keys.saw(Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ), Spec.Ballot.at(b)))
        )
      )

# the node m, if any, else s, has the heads of s when m has
def Default.heads(
  -s: Spec.State(),
  m: Maybe<&2, Spec.State()>
) -> {Spec.State.heads(s) == Heads.of(s, m): Tries.Trie<Spec.Head>} -> {Spec.State.heads(s) == Spec.State.heads(Maybe.default(&2, Spec.State(), m, s)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  +s: Spec.State(),
  +w: Ledgers.Where,
  n: String,
  v: Ledgers.Vote,
  m: Maybe<&2, Spec.Chained>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Cast.seal(s, w, n, v, m)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Chained{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), j),
        Ledgers.Signed{w, n, Ledgers.Act.Vote{v, []}},
        last,
        Seals.Seal.public(
          Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), U32.inc(j))
        )
      )
      Default.heads(s, Spec.Seal.accept(s, b))(
        Accept.at.heads(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b)))
      )

# a ballot keeps the heads
def Cast.vote.heads(
  +s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +w: Ledgers.Where,
  +n: String,
  v: Ledgers.Vote
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Cast.vote(s, m, w, n, v)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = Spec.State.led(s, Spec.State.ledger(s3))
      Equal.trans(
        Tries.Trie<Spec.Head>,
        Spec.State.heads(s),
        Spec.State.heads(s4),
        Spec.State.heads(Spec.Cast.seal(s4, w, n, v, Spec.Seal.chain(s4, Spec.Where.store(w), n))),
        Heads.led(s, Spec.State.ledger(s3)),
        Cast.seal.heads(s4, w, n, v, Spec.Seal.chain(s4, Spec.Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  -s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  -k: Spec.State() -> Spec.State(),
  ih: @s2: Spec.State() -> {Spec.State.heads(s2) == Spec.State.heads(k(s2)): Tries.Trie<Spec.Head>}
) -> {Spec.State.heads(s) == Heads.of(s, m): Tries.Trie<Spec.Head>} -> {Spec.State.heads(s) == Spec.State.heads(Maybe.default(&2, Spec.State(), Maybe.bind(&2, Spec.State(), Spec.State(), m, s2 => Some{k(s2)}), s)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(Tries.Trie<Spec.Head>, Spec.State.heads(s), Spec.State.heads(s2), Spec.State.heads(k(s2)), e, ih(s2))

# the ballots that a chain leads to keep the heads
def Follow.heads(
  f: Nat,
  +s: Spec.State(),
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Sealed.follow(f, s, p, r, n, mb)): Tries.Trie<Spec.Head>}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.heads(
        s,
        Spec.Seal.accept(s, b),
        +s2 => Spec.Sealed.follow(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n)),
        +s2 => Follow.heads(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n))
      )(Accept.at.heads(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b))))

# the ballots that the chains of some ballots lead to keep the heads
def Each.heads(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Spec.State()
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Sealed.each(f, bs, p, s)): Tries.Trie<Spec.Head>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Spec.Sealed.follow(
        f,
        s,
        p,
        Spec.Ballot.store(b),
        Spec.Ballot.node(b),
        Spec.Pending.next(s, p, Spec.Ballot.store(b), Spec.Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<Spec.Head>,
        Spec.State.heads(s),
        Spec.State.heads(s1),
        Spec.State.heads(Spec.Sealed.each(f, rest, p, s1)),
        Follow.heads(
          f,
          s,
          p,
          Spec.Ballot.store(b),
          Spec.Ballot.node(b),
          Spec.Pending.next(s, p, Spec.Ballot.store(b), Spec.Ballot.node(b))
        ),
        Each.heads(f, rest, p, s1)
      )

# a ballot for a run keeps the heads
def Cast.put.heads(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  s: Spec.State()
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Cast.put(n, w, th, qs, m, s)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{s2, +t2, ns}}:
      Cast.vote.heads(
        s,
        Spec.State.put(s2, [Spec.Tip.words(t2)]),
        w,
        n,
        Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}
      )

# Node.cast keeps the heads, at the head h whose tip is m
def Cast.at.heads(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Cast.at(n, s, c, h, m)): Tries.Trie<Spec.Head>}:
  match h m:
    case Spec.Head{r, b, +next, +th} Some{+t}:
      +p = Spec.Plan.of(n, s, c, Ledgers.Where{c, next, 0}, t, th, Spec.Owners.turn(Spec.Line.owners(s, t), next))
      +qs = Spec.Plan.asks(p)
      Heads.when(
        Spec.Cast.may(n, s, Ledgers.Where{c, next, 0}, t, qs),
        s,
        Spec.Cast.put(n, Ledgers.Where{c, next, 0}, th, qs, Spec.Plan.run(p), s),
        s,
        Cast.put.heads(n, Ledgers.Where{c, next, 0}, th, qs, Spec.Plan.run(p), s),
        {==}
      )
    case Spec.Head{r, b, next, th} None{}:
      {==}

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Cast.head(n, s, c, m)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(n, s, c, h, Spec.Head.tip(s, h))

# a node's ballot keeps its logs
def Cast.kept(+n: String, +s: Spec.State(), +c: Ledgers.Chain) -> Spec.Node.Keeps(s, Spec.Node.cast(n, s, c)):
  Kept.same(
    s,
    Spec.Node.cast(n, s, c),
    Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Spec.Node.head_of(s, c))
  )

# the words of a tip read as the tip
def Tip.round(t: Spec.Tip) -> {Spec.Tip.read(Spec.Tip.words(t)) == Some{t}: Maybe<&2, Spec.Tip>}:
  match t:
    case Spec.Tip{c, l}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Spec.Tip>>,
        Codes.Code.two.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~Spec.Tip,
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          x => y => Spec.Tip{x, y},
          Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(c)(
            Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(l)([])
          )
        ),
        Some{Codes.Read{Spec.Tip{c, l}, []}},
        Codes.Code.two_read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~Spec.Tip,
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          x => y => Spec.Tip{x, y},
          c,
          l,
          []
        )
      ): {Spec.Read.whole(Spec.Tip, _) == Some{Spec.Tip{c, l}}: Maybe<&2, Spec.Tip>}
      {==}

# Put.holds once whether the node holds the data is known (b)
def Put.holds.if(
  -s2: Spec.State(),
  -ds: List<&2, List<&2, U32>>,
  -s3: Spec.State(),
  b: Bool,
  eb: {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s2, ds), ds) == b: Bool}
) -> {
  Shared.Maybe.when(Spec.State(), b, u => Some{Spec.State.keep(s2, ds)}) == Some{s3}: Maybe<&2, Spec.State()>
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.State(), s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(Spec.State(), Spec.State.keep(s2, ds), s3, e): {
          Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, _, ds) == True{}: Bool
        }
        eb

# a node that a put gives holds the data
def Put.holds(
  s2: Spec.State(),
  +ds: List<&2, List<&2, U32>>,
  -s3: Spec.State()
) -> {Spec.State.put(s2, ds) == Some{s3}: Maybe<&2, Spec.State()>} -> {
  Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool
}:
  Put.holds.if(
    s2,
    ds,
    s3,
    Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  s2: Spec.State(),
  ds: List<&2, List<&2, U32>>,
  -s3: Spec.State(),
  e: {Spec.State.put(s2, ds) == Some{s3}: Maybe<&2, Spec.State()>}
) -> {Spec.Node.grows(s2, s3) == True{}: Bool}:
  %e: {State.after(s2, _) == True{}: Bool}
  Put.grows(s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  s2: Spec.State(),
  +t2: Spec.Tip,
  +s3: Spec.State()
) -> {Spec.State.put(s2, [Spec.Tip.words(t2)]) == Some{s3}: Maybe<&2, Spec.State()>} -> {
  Spec.Tip.at(s3, Spec.Tip.hash(t2)) == Some{t2}: Maybe<&2, Spec.Tip>
}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Spec.Store.fetch(s3, Hashes.Sha.hash(Spec.Tip.words(t2))),
      Some{Spec.Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Spec.Store.fetch(s3, Hashes.Sha.hash(Spec.Tip.words(t2))),
        Some{Spec.Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Trees.Tree.has(~Spec.State(), ~Spec.Store.fetch, s3, Spec.Tip.words(t2)),
          u => Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, [])
        )(Put.holds(s2, [Spec.Tip.words(t2)], s3)(e))
      )
    ): {Maybe.bind(&2, List<&2, U32>, Spec.Tip, _, ws => Spec.Tip.read(ws)) == Some{t2}: Maybe<&2, Spec.Tip>}
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  -s: Spec.State(),
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Spec.Head,
  -t: Spec.Tip,
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  et: {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>}
) -> {Spec.Line.get(s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {Maybe.bind(&2, Spec.Tip, List<&2, U32>, _, t1 => Spec.Node.get(s, Spec.Tip.log(t1), k)) == Some{v}: Maybe<&2, List<&2, U32>>}
    Line.get.of(s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  +s3: Spec.State(),
  +b: Spec.State(),
  +t2: Spec.Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Spec.Node.grows(s3, b) == True{}: Bool},
  e3: {Spec.Tip.at(s3, Spec.Tip.hash(t2)) == Some{t2}: Maybe<&2, Spec.Tip>},
  v3: {Spec.Node.get(s3, Spec.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {Spec.Head.get(b, Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}}, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  %Equal.sym(
    Maybe<&2, Spec.Tip>,
    Spec.Tip.at(b, Spec.Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(s3, b, Spec.Tip.hash(t2), t2, g)(e3)
  ): {Maybe.bind(&2, Spec.Tip, List<&2, U32>, _, t1 => Spec.Node.get(b, Spec.Tip.log(t1), k)) == Some{v}: Maybe<&2, List<&2, U32>>}
  Get.grows(s3, b, Spec.Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  +s: Spec.State(),
  +s3: Spec.State(),
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Spec.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Spec.Head,
  t: Spec.Tip,
  g3: {Spec.Node.grows(s, s3) == True{}: Bool},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  et: {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>},
  e3: {Spec.Tip.at(s3, Spec.Tip.hash(t2)) == Some{t2}: Maybe<&2, Spec.Tip>},
  kk: @k: List<&2, U32> -> @v: List<&2, U32> -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool} -> {Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Node.get(s3, Spec.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(s, Spec.State.moved(Spec.State.led(s, Spec.State.ledger(s3)), c, Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}}, qs)):
  +x = Spec.State.led(s, Spec.State.ledger(s3))
  +ws = Spec.Wait.left(
    Spec.Wait.of(x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Spec.Wait.set(x, c, ws)
  +hd = {Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}}: Spec.Head}
  Head.put.kept(
    s,
    b0,
    c,
    hd,
    Grows.to(s, x, b0, Led.wait(x, c, ws), Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Spec.Head>,
      Spec.State.heads(s),
      Spec.State.heads(x),
      Spec.State.heads(b0),
      Heads.led(s, Spec.State.ledger(s3)),
      Heads.wait(x, c, ws)
    ),
    +k => +v => n0 => n1 => e => Moved.cover(
      s3,
      Spec.State.head(b0, c, hd),
      t2,
      k,
      v,
      r,
      br,
      nx,
      Grows.to(
        s3,
        s3,
        Spec.State.head(b0, c, hd),
        Equal.trans(
          Ledgers.State(Spec.Ask),
          Spec.State.ledger(Spec.State.head(b0, c, hd)),
          Spec.State.ledger(b0),
          Spec.State.ledger(s3),
          Led.head(b0, c, hd),
          Equal.trans(
            Ledgers.State(Spec.Ask),
            Spec.State.ledger(b0),
            Spec.State.ledger(x),
            Spec.State.ledger(s3),
            Led.wait(x, c, ws),
            Led.led(s, Spec.State.ledger(s3))
          )
        ),
        Grows.refl(s3)
      ),
      e3,
      kk(k)(v)(n0)(n1)(Line.read.at(s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  +s: Spec.State(),
  +s2: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Spec.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Spec.Head,
  t: Spec.Tip,
  g2: {Spec.Node.grows(s, s2) == True{}: Bool},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  et: {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>},
  kk: @k: List<&2, U32> -> @v: List<&2, U32> -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool} -> {Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Node.get(s2, Spec.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {Spec.State.put(s2, [Spec.Tip.words(t2)]) == m: Maybe<&2, Spec.State()>} -> Spec.Node.Keeps(
  s,
  Spec.Advance.moved(s, m, c, Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}}, qs)
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
        Grows.trans(s, s2, s3)(g2)(Put.grew(s2, [Spec.Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(s2, t2, s3)(e2),
        +k => +v => n0 => n1 => e => Get.grows(
          s2,
          s3,
          Spec.Tip.log(t2),
          k,
          v,
          Put.grew(s2, [Spec.Tip.words(t2)], s3, e2)
        )(kk(k)(v)(n0)(n1)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  s: Spec.State(),
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  h: Spec.Head,
  t: Spec.Tip,
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  et: {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>}
) -> {Run.after(s, m) == True{}: Bool} -> (@k: List<&2, U32> -> @v: List<&2, U32> -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool} -> {Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>} -> Run.Keeps(
  k,
  v,
  m
)) -> Spec.Node.Keeps(s, Spec.Advance.ran(s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(s)
    case Some{Spec.Run{+s2, +t2, ns}}:
      ga => rk => Kept.when(
        Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
        s,
        Spec.Advance.moved(
          s,
          Spec.State.put(s2, [Spec.Tip.words(t2)]),
          c,
          Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(
          s,
          s2,
          Spec.State.put(s2, [Spec.Tip.words(t2)]),
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  +t: Spec.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>} -> {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>} -> Spec.Node.Keeps(s, Spec.Advance.step(s, c, h, t, m)):
  match h m:
    case Spec.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, after}}:
      +em => +et => Kept.when(
        Spec.Root.same(before, th),
        s,
        Spec.Advance.ran(s, c, r, br, next, after, qs, Spec.Step.run(s, c, t, qs)),
        s,
        Advance.ran.kept(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Spec.Step.run(s, c, t, qs),
          Spec.Head{r, br, next, th},
          t,
          em,
          et
        )(Run.grows(s, c, t, qs))(+k => +v => +n0 => +n1 => Run.kept(s, c, t, qs, k, v, n0, n1)),
        Kept.refl(s)
      )
    case Spec.Head{r, br, next, th} None{}:
      em => et => Kept.refl(s)

# Node.advance keeps the logs, at the head h whose tip is m
def Advance.at.kept(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>} -> {Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>} -> Spec.Node.Keeps(s, Spec.Advance.at(s, c, h, m)):
  match m:
    case None{}:
      em => et => Kept.refl(s)
    case Some{+t}:
      em => et => Advance.step.kept(
        s,
        c,
        h,
        t,
        Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h))))
      )(em)(et)

# Node.advance keeps the logs, once the head m is known
def Advance.head.kept(
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>} -> Spec.Node.Keeps(s, Spec.Advance.head(s, c, m)):
  match m:
    case None{}:
      em => Kept.refl(s)
    case Some{+h}:
      em => Advance.at.kept(s, c, h, Spec.Head.tip(s, h))(em)({==})

# Advances.kept once the head m is known
def Advances.at.kept(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>} -> Spec.Node.Keeps(s, Spec.Advances.at(f, s, c, m)):
  match f m:
    case 0n x:
      em => Kept.refl(s)
    case 1n+p None{}:
      em => Kept.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Spec.Advance.at(s, c, h, Spec.Head.tip(s, h))
        +m1 = Spec.Node.head_of(s1, c)
        Kept.when(
          Spec.Heads.level(Some{h}, m1),
          s,
          s1,
          Spec.Advances.at(p, s1, c, m1),
          Advance.at.kept(s, c, h, Spec.Head.tip(s, h))(em)({==}),
          Kept.trans(
            s,
            s1,
            Spec.Advances.at(p, s1, c, m1),
            Advance.at.kept(s, c, h, Spec.Head.tip(s, h))(em)({==}),
            Advances.at.kept(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step keeps the logs
def Advances.kept(f: Nat, +s: Spec.State(), +c: Ledgers.Chain) -> Spec.Node.Keeps(s, Spec.Node.advances(f, s, c)):
  Advances.at.kept(f, s, c, Spec.Node.head_of(s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(+n: String, +s: Spec.State(), +c: Ledgers.Chain) -> Spec.Node.Keeps(s, Spec.Step.head(n, s, c)):
  +s1 = Spec.Node.advances(4294967295n, s, c)
  +s2 = Spec.Node.cast(n, s1, c)
  s3 = Spec.Node.advances(4294967295n, s2, c)
  Kept.trans(
    s,
    s1,
    s3,
    Advances.kept(4294967295n, s, c),
    Kept.trans(s1, s2, s3, Cast.kept(n, s1, c), Advances.kept(4294967295n, s2, c))
  )

# a line with no head holds nothing
def Cover.none(
  -a: Spec.State(),
  -c: Ledgers.Chain,
  -b: Spec.State(),
  -hd: Spec.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Spec.Node.head_of(a, c) == None{}: Maybe<&2, Spec.Head>}
) -> {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  -a: Spec.State(),
  -c: Ledgers.Chain,
  -b: Spec.State(),
  -hd: Spec.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Spec.Node.head_of(a, c) == Some{Spec.Head{r, br, n, None{}}}: Maybe<&2, Spec.Head>}
) -> {Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>} -> {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(a, c, k, v, Some{Spec.Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>} -> Spec.Node.Keeps(s, Spec.Open.at(s, c, m)):
  match m:
    case Some{Spec.Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Spec.Head{
            r,
            Some{b},
            0,
            Spec.Branch.first(s, b, Spec.Node.tip(s, Ledgers.Chain{r, None{}}))
          }: Spec.Head
        }
        Head.put.kept(
          s,
          s,
          c,
          hd,
          Grows.refl(s),
          {==},
          k => v => n0 => n1 => Cover.wait(s, c, Spec.State.head(s, c, hd), hd, k, v, r, Some{b}, n, em)
        )
    case Some{Spec.Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Spec.Head{r, None{}, n, t}}:
      em => Kept.refl(s)
    case None{}:
      em => Kept.refl(s)

# what a node does on a line keeps the logs
def Step.kept(n: String, +s: Spec.State(), +c: Ledgers.Chain) -> Spec.Node.Keeps(s, Spec.Node.step(n, s, c)):
  s1 = Spec.Node.open(s, c)
  Kept.trans(
    s,
    s1,
    Spec.Step.head(n, s1, c),
    Open.at.kept(s, c, Spec.Node.head_of(s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  +s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>} -> Spec.Node.Keeps(s, Spec.First.at(s, c, h, m)):
  match m:
    case Some{Spec.Head{r, b, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Spec.Head{r, b, n, None{}}}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.wait(s, c, Spec.State.head(s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.none(s, c, Spec.State.head(s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  h: Spec.Head,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {State.after(a, m) == True{}: Bool} -> Spec.Node.Keeps(s, Spec.Start.head(s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+s3}:
      e =>
        +x = Spec.State.led(s, Spec.State.ledger(s3))
        Kept.trans(
          s,
          x,
          Spec.State.first(x, c, h),
          Kept.same(
            s,
            x,
            Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Spec.State.ledger(s3))
          ),
          First.at.kept(x, c, h, Spec.Node.head_of(x, c))({==})
        )

# the first tip of a store keeps the logs
def Start.put.kept(
  s: Spec.State(),
  +i: Ledgers.Id,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> Spec.Node.Keeps(s, Spec.Start.put(s, i, c, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{Spec.Work{+s2, l, ns}}:
      e =>
        +t = {Spec.Tip{c, l}: Spec.Tip}
        Start.head.kept(
          s,
          s2,
          Spec.State.put(s2, [Spec.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Spec.Head{i, None{}, 0, Some{Spec.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Spec.Tip.words(t)]))

# Start.kept once the content m of the store is known
def Start.with.kept(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> Spec.Node.Keeps(s, Spec.Start.with(s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+w}:
      e => Start.put.kept(s, i, Spec.Work.root(w), Spec.Log.first(w, os))(Log.first.after(s, w, os)(e))

# a store that starts keeps the logs
def Start.kept(+s: Spec.State(), i: Ledgers.Id, +os: List<&2, Spec.Owner>) -> Spec.Node.Keeps(
  s,
  Spec.Node.start(s, i, os)
):
  Start.with.kept(
    s,
    i,
    Spec.Owner.names(os),
    Spec.Seal.firsts(os, Some{Spec.Work{s, None{}, []}})
  )(Firsts.after(s, os, Some{Spec.Work{s, None{}, []}})(Grows.refl(s)))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  +s: Spec.State(),
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, Spec.Line.chain(r, l)) == m: Maybe<&2, Spec.Head>} -> Spec.Node.Keeps(s, Spec.Follow.new(s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(s)
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        Spec.Line.chain(r, l),
        Spec.Head{r, l, 0, None{}},
        Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.none(
          s,
          Spec.Line.chain(r, l),
          Spec.State.head(s, Spec.Line.chain(r, l), Spec.Head{r, l, 0, None{}}),
          Spec.Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  s: Spec.State(),
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.State.wait(s, c, i)): Tries.Trie<Spec.Head>}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# a new request keeps the logs
def Arrive.kept(+s: Spec.State(), +i: Ledgers.Id, q: Spec.Ask) -> Spec.Node.Keeps(s, Spec.Node.arrive(s, i, q)):
  match q:
    case Spec.Ask.Start{os}:
      Start.kept(s, i, os)
    case Spec.Ask.On{+r, +l, c}:
      +s1 = Spec.Node.follow(s, r, l)
      Kept.trans(
        s,
        s1,
        Spec.State.wait(s1, Spec.Line.chain(r, l), i),
        Follow.new.kept(s, r, l, Spec.Node.head_of(s, Spec.Line.chain(r, l)))({==}),
        Kept.same(
          s1,
          Spec.State.wait(s1, Spec.Line.chain(r, l), i),
          Grows.to(
            s1,
            s1,
            Spec.State.wait(s1, Spec.Line.chain(r, l), i),
            Led.waits(s1, Spec.Line.chain(r, l), i),
            Grows.refl(s1)
          ),
          Heads.waits(s1, Spec.Line.chain(r, l), i)
        )
      )

# a new request keeps the logs
def Ask.new.kept(+n: String, +s: Spec.State(), +e: Spec.Envelope, +q: Spec.Ask) -> Spec.Node.Keeps(
  s,
  Spec.Node.ask.new(n, s, e, q)
):
  +i = Spec.Envelope.of(e)
  c = Spec.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Spec.Ask,
    ~Spec.Ask.is_eq,
    Spec.State.ledger(s),
    i,
    Spec.Envelope.time(e),
    q
  )
  +s0 = Spec.State.led(s, l0)
  s1 = Spec.Node.arrive(s0, i, q)
  Kept.trans(
    s,
    s0,
    Spec.Node.step(n, s1, c),
    Kept.same(
      s,
      s0,
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
      ),
      Heads.led(s, l0)
    ),
    Kept.trans(s0, s1, Spec.Node.step(n, s1, c), Arrive.kept(s0, i, q), Step.kept(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.kept(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> Spec.Node.Keeps(s, Spec.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(s)
    case None{}:
      Kept.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        Spec.Node.ask.new(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), e, q),
        Kept.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          Grows.to(s, s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), Grows.refl(s)),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))
        ),
        Ask.new.kept(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))), e, q)
      )

# Node.ask keeps the logs
def Ask.kept(n: String, +s: Spec.State(), +e: Spec.Envelope, q: Spec.Ask) -> Spec.Node.Keeps(
  s,
  Spec.Node.ask(n, s, e, q)
):
  Ask.at.kept(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )

# the new requests among cells keep the logs
def Take.asks.kept(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State()
) -> Spec.Node.Keeps(s, Spec.Take.asks(cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(Spec.State(), Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))), u => Spec.Node.arrive(s, i, q), u => s)
      Kept.trans(
        s,
        s1,
        Spec.Take.asks(rest, old, s1),
        Kept.when(Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))), s, Spec.Node.arrive(s, i, q), s, Arrive.kept(s, i, q), Kept.refl(s)),
        Take.asks.kept(rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.kept(rest, old, s)

# Node.take keeps the logs
def Take.kept(+s: Spec.State(), +t: Ledgers.State(Spec.Ask)) -> Spec.Node.Keeps(s, Spec.Node.take(s, t)):
  +sent = Spec.Take.clean(Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t), Ledgers.State.empty(~Spec.Ask))
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s)))
  )
  Kept.trans(
    s,
    s1,
    Spec.Sealed.take(bs, s2),
    Kept.same(
      s,
      s1,
      Grows.led(
        s,
        l1,
        Ledgers.State.take_grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), Spec.State.ledger(s), sent)
      ),
      Heads.led(s, l1)
    ),
    Kept.trans(
      s1,
      s2,
      Spec.Sealed.take(bs, s2),
      Take.asks.kept(cs, Spec.State.ledger(s), s1),
      Kept.same(
        s2,
        Spec.Sealed.take(bs, s2),
        Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2),
        Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines keeps the logs
def Steps.kept(+n: String, cs: List<&2, Ledgers.Chain>, +s: Spec.State()) -> Spec.Node.Keeps(
  s,
  Spec.Node.steps(n, cs, s)
):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      s1 = Spec.Node.step(n, s, c)
      Kept.trans(s, s1, Spec.Node.steps(n, rest, s1), Step.kept(n, s, c), Steps.kept(n, rest, s1))

# Node.sync keeps the logs
def Sync.kept(n: String, +s: Spec.State(), +t: Ledgers.State(Spec.Ask)) -> Spec.Node.Keeps(
  s,
  Spec.Node.sync(n, s, t)
):
  +s1 = Spec.Node.take(s, t)
  cs = Spec.Sync.lines(s, s1, t)
  Kept.trans(s, s1, Spec.Node.steps(n, cs, s1), Take.kept(s, t), Steps.kept(n, cs, s1))

# a request that a writer asks again at a node only grows it
def Consent.grows(
  +n: String,
  +s: Spec.State(),
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> {Spec.Node.grows(s, Spec.Consent.at(n, s, i, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+c}:
      Grows.trans(s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), Spec.Node.step(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c))(
        Grows.to(s, s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), Grows.refl(s))
      )(Step.grows(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c))

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  +n: String,
  +s: Spec.State(),
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Spec.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{+c}:
      Kept.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
        Spec.Node.step(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c),
        Kept.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
          Grows.to(s, s, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), Grows.refl(s)),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i))
        ),
        Step.kept(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  n: String,
  +s: Spec.State(),
  ev: Spec.Deed
) -> {Spec.Node.grows(s, Spec.Node.does(n, s, ev)) == True{}: Bool}:
  match ev:
    case Spec.Deed.Ask{e, q}:
      Spec.Node.ask_grows(n, s, e, q)
    case Spec.Deed.Take{t}:
      Spec.Node.take_grows(s, t)
    case Spec.Deed.Sync{t}:
      Spec.Node.sync_grows(n, s, t)
    case Spec.Deed.Keep{b}:
      Grows.keep(s, Ropes.Put.nodes(Spec.Bytes.rope(b)))
    case Spec.Deed.Consent{+i}:
      Consent.grows(n, s, i, Spec.Node.chain_of(s, i))

def Spec.Node.after_grows(n, evs, s):
  match evs:
    case Nil{}:
      Grows.refl(s)
    case Con{+ev, +rest}:
      +s1 = Spec.Node.does(n, s, ev)
      Grows.trans(s, s1, Spec.Node.after(n, rest, s1))(Does.grows(n, s, ev))(
        Spec.Node.after_grows(n, rest, s1)
      )

# what a node does keeps the logs
def Does.kept(n: String, +s: Spec.State(), ev: Spec.Deed) -> Spec.Node.Keeps(s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{e, q}:
      Ask.kept(n, s, e, q)
    case Spec.Deed.Take{t}:
      Take.kept(s, t)
    case Spec.Deed.Sync{t}:
      Sync.kept(n, s, t)
    case Spec.Deed.Keep{+b}:
      Kept.same(
        s,
        Spec.Node.keep(s, b),
        Grows.keep(s, Ropes.Put.nodes(Spec.Bytes.rope(b))),
        Heads.led(
          s,
          Ledgers.State.put_datas(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            Ropes.Put.nodes(Spec.Bytes.rope(b)),
            Spec.State.ledger(s)
          )
        )
      )
    case Spec.Deed.Consent{+i}:
      Consent.kept(n, s, i, Spec.Node.chain_of(s, i))

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

# Finality
# --------
# What a node knows of a line stays, whatever the node does next.

# an outcome that a line holds, it holds in a node that keeps its logs
def Chain.out.kept(
  a: Spec.State(),
  b: Spec.State(),
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  -o: Spec.Out,
  hk: Spec.Node.Keeps(a, b)
) -> {Spec.Chain.out(a, c, i) == Some{o}: Maybe<&2, Spec.Out>} -> {
  Spec.Chain.out(b, c, i) == Some{o}: Maybe<&2, Spec.Out>
}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Spec.Out,
    Spec.Line.get(a, c, Spec.Log.out(i)),
    Spec.Line.get(b, c, Spec.Log.out(i)),
    ws => Spec.Out.read(ws),
    ws => Spec.Out.read(ws),
    o,
w => hk(c)(Spec.Log.out(i))(w)({==})({==}),
w => e => e
)

# the version of a number that a line holds, it holds in a node that keeps
# its logs
def Chain.version.kept(
  a: Spec.State(),
  b: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  -x: Spec.Version,
  hk: Spec.Node.Keeps(a, b)
) -> {Spec.Chain.version(a, c, n) == Some{x}: Maybe<&2, Spec.Version>} -> {
  Spec.Chain.version(b, c, n) == Some{x}: Maybe<&2, Spec.Version>
}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Spec.Version,
    Spec.Line.get(a, c, Spec.Log.version(n)),
    Spec.Line.get(b, c, Spec.Log.version(n)),
    ws => Spec.Version.read(ws),
    ws => Spec.Version.read(ws),
    x,
w => hk(c)(Spec.Log.version(n))(w)({==})({==}),
w => e => e
)

# a mark that a line holds, it holds in a node that keeps its logs
def Chain.mark.kept(
  a: Spec.State(),
  b: Spec.State(),
  +c: Ledgers.Chain,
  +m: String,
  -v: Ledgers.Id,
  hk: Spec.Node.Keeps(a, b)
) -> {Spec.Chain.mark(a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>} -> {
  Spec.Chain.mark(b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Ledgers.Id,
    Spec.Line.get(a, c, Spec.Log.mark(m)),
    Spec.Line.get(b, c, Spec.Log.mark(m)),
    ws => Spec.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    ws => Spec.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    v,
w => hk(c)(Spec.Log.mark(m))(w)({==})({==}),
w => e => e
)

# the line of a request that a node holds, a node that grew holds
def Chain.of.kept(
  +a: Spec.State(),
  b: Spec.State(),
  +i: Ledgers.Id,
  -c: Ledgers.Chain,
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Node.chain_of(a, i) == Some{c}: Maybe<&2, Ledgers.Chain>} -> {
  Spec.Node.chain_of(b, i) == Some{c}: Maybe<&2, Ledgers.Chain>
}:
  Shared.Maybe.bind_kept(
    Ledgers.Asked<Spec.Ask>,
    Ledgers.Chain,
    Spec.Node.asked(a, i),
    Spec.Node.asked(b, i),
    x => Some{Spec.Ask.chain(i, Spec.Asked.ask(x))},
    x => Some{Spec.Ask.chain(i, Spec.Asked.ask(x))},
    c,
x => Ledgers.State.read_grows(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Ledgers.Asked<Spec.Ask>,
      m => Ledgers.Asked.of(~Spec.Ask, m),
      {==},
      Spec.State.ledger(a),
      Spec.State.ledger(b),
      Ledgers.Slot.ask(i),
      x
    )(g),
x => e => e
)

# an outcome that a node knows, a node that grew and keeps its logs knows
def Out.kept(
  +a: Spec.State(),
  +b: Spec.State(),
  +i: Ledgers.Id,
  -o: Spec.Out,
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  hk: Spec.Node.Keeps(a, b)
) -> {Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>} -> {
  Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>
}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Spec.Out,
    Spec.Node.chain_of(a, i),
    Spec.Node.chain_of(b, i),
    c => Spec.Chain.out(a, c, i),
    c => Spec.Chain.out(b, c, i),
    o,
c => Chain.of.kept(a, b, i, c, g),
+c => Chain.out.kept(a, b, c, i, o, hk)
)

# the version of an outcome, in a node that keeps the logs
def Out.on.kept(
  a: Spec.State(),
  b: Spec.State(),
  c: Ledgers.Chain,
  o: Spec.Out,
  -x: Spec.Version,
  hk: Spec.Node.Keeps(a, b)
) -> {Spec.Out.on(a, c, o) == Some{x}: Maybe<&2, Spec.Version>} -> {
  Spec.Out.on(b, c, o) == Some{x}: Maybe<&2, Spec.Version>
}:
  match o:
    case Spec.Out.Stale{}:
      e => e
    case Spec.Out.Taken{n}:
      Chain.version.kept(a, b, c, n, x, hk)

# the version that a request made on a line, in a node that keeps the logs
def Chain.made.kept(
  +a: Spec.State(),
  +b: Spec.State(),
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  -x: Spec.Version,
  hk1: Spec.Node.Keeps(a, b),
  hk2: Spec.Node.Keeps(a, b)
) -> {Spec.Chain.made(a, c, v) == Some{x}: Maybe<&2, Spec.Version>} -> {
  Spec.Chain.made(b, c, v) == Some{x}: Maybe<&2, Spec.Version>
}:
  Shared.Maybe.bind_kept(
    Spec.Out,
    Spec.Version,
    Spec.Chain.out(a, c, v),
    Spec.Chain.out(b, c, v),
    o => Spec.Out.on(a, c, o),
    o => Spec.Out.on(b, c, o),
    x,
o => Chain.out.kept(a, b, c, v, o, hk1),
o => Out.on.kept(a, b, c, o, x, hk2)
)

# the version that a request made, in a node that grew and keeps the logs
def Made.kept(
  +a: Spec.State(),
  +b: Spec.State(),
  +v: Ledgers.Id,
  -x: Spec.Version,
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  hk1: Spec.Node.Keeps(a, b),
  hk2: Spec.Node.Keeps(a, b)
) -> {Spec.Node.made(a, v) == Some{x}: Maybe<&2, Spec.Version>} -> {
  Spec.Node.made(b, v) == Some{x}: Maybe<&2, Spec.Version>
}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Spec.Version,
    Spec.Node.chain_of(a, v),
    Spec.Node.chain_of(b, v),
    +c => Spec.Chain.made(a, c, v),
    +c => Spec.Chain.made(b, c, v),
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

# the answer b may come after the answer a, if there is an a
def Follows.opt(ma: Maybe<&2, Spec.Answer>, mb: Maybe<&2, Spec.Answer>) -> Bool:
  match ma:
    case None{}:
      True{}
    case Some{x}:
      Spec.Answer.follows(x, mb)

# Written or Conflicted may come after Written or Conflicted
def Left.follows(
  ba: Bool,
  bb: Bool,
  i: Ledgers.Id,
  k: Ledgers.Id
) -> {
  Spec.Answer.follows(
    Shared.Bool.when(Spec.Answer, ba, u => Spec.Answer.Written{i}, u => Spec.Answer.Conflicted{k}),
    Some{
      Shared.Bool.when(Spec.Answer, bb, u => Spec.Answer.Written{i}, u => Spec.Answer.Conflicted{k})
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
  a: Spec.State(),
  b: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> {Spec.Answer.follows(Spec.Answer.taken(a, i, q), Some{Spec.Answer.taken(b, i, q)}) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Branch{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Group{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Own{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Write{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Resolve{+k, y, z}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(a, k)),
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(b, k)),
        i,
        k
      )
    case Spec.Ask.On{st, l, Spec.Change.Merge{f}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(a, i)),
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(b, i)),
        i,
        i
      )
    case Spec.Ask.On{st, l, Spec.Change.Move{x}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Mark{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, Spec.Change.Key{x, y}}:
      Ledgers.Id.is_eq_refl(i)

# Asked.follows once the outcome oa of the request is known
def Of.follows(
  a: Spec.State(),
  b: Spec.State(),
  i: Ledgers.Id,
  q: Spec.Ask,
  oa: Maybe<&2, Spec.Out>
) -> {Spec.Node.out(a, i) == oa: Maybe<&2, Spec.Out>} -> (@o: Spec.Out -> {
  Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
} -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}) -> {
  Spec.Answer.follows(
    Spec.Answer.of(a, i, q, Spec.Node.out(a, i)),
    Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(Maybe<&2, Spec.Out>, Spec.Node.out(a, i), None{}, eo): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, _),
            Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Spec.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(Maybe<&2, Spec.Out>, Spec.Node.out(a, i), Some{Spec.Out.Stale{}}, eo): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, _),
            Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Spec.Out>,
          Spec.Node.out(b, i),
          Some{Spec.Out.Stale{}},
          ho(Spec.Out.Stale{})(eo)
        ): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, Some{Spec.Out.Stale{}}),
            Some{Spec.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        {==}
    case Some{Spec.Out.Taken{k}}:
      +eo => ho =>
        %Equal.sym(Maybe<&2, Spec.Out>, Spec.Node.out(a, i), Some{Spec.Out.Taken{k}}, eo): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, _),
            Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Spec.Out>,
          Spec.Node.out(b, i),
          Some{Spec.Out.Taken{k}},
          ho(Spec.Out.Taken{k})(eo)
        ): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, Some{Spec.Out.Taken{k}}),
            Some{Spec.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        Taken.follows(a, b, i, q)

# the answer to a request that a node holds may come after the answer to it
def Asked.follows(
  +a: Spec.State(),
  b: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask,
  ho: @o: Spec.Out -> {Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>} -> {
    Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>
  }
) -> {Spec.Answer.follows(Spec.Answer.asked(a, i, q), Some{Spec.Answer.asked(b, i, q)}) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Spec.Ask.On{st, l, ch}:
      Of.follows(a, b, i, Spec.Ask.On{st, l, ch}, Spec.Node.out(a, i))({==})(ho)

# Held.follows once whether the held change is the one asked is known (bq)
def Held.follows.if(
  bq: Bool,
  -x: Spec.Answer,
  -y: Spec.Answer,
  h: {Spec.Answer.follows(x, Some{y}) == True{}: Bool}
) -> {
  Spec.Answer.follows(
    Shared.Bool.when(Spec.Answer, bq, u => x, u => Spec.Answer.Refused{}),
    Some{Shared.Bool.when(Spec.Answer, bq, u => y, u => Spec.Answer.Refused{})}
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
  a: Spec.State(),
  b: Spec.State(),
  i: Ledgers.Id,
  q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  ho: @o: Spec.Out -> {Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>} -> {
    Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>
  }
) -> {Follows.opt(Spec.Answer.held(a, i, q, m), Spec.Answer.held(b, i, q, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Held.follows.if(
        Spec.Ask.is_eq(q2, q),
        Spec.Answer.asked(a, i, q2),
        Spec.Answer.asked(b, i, q2),
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
  c: Cells.Cell<Ledgers.Entry<Spec.Ask>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {Cells.Cell.keeps(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq), Some{c}, mb) == True{}: Bool} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}:
  match c mb:
    case Cells.One{x} y:
      Cells.Cell.keeps_value(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
        ~Ledgers.Entry.laws(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws()),
        x,
        y
      )
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{y}}:
      h => Empty.absurd(
        {Some{Cells.One{y}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd({None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}, Shared.Bool.false_ne_true(h))

# Node.answer_follows once the cell ma of the request's ID is known
def Answer.follows.at(
  a: Spec.State(),
  b: Spec.State(),
  i: Ledgers.Id,
  q: Spec.Ask,
  -x: Spec.Answer,
  ma: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  ho: @o: Spec.Out -> {Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>} -> {
    Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>
  }
) -> {Cells.Cell.keeps(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq), ma, mb) == True{}: Bool} -> {
  Spec.Answer.held(a, i, q, ma) == Some{x}: Maybe<&2, Spec.Answer>
} -> {Spec.Answer.follows(x, Spec.Answer.held(b, i, q, mb)) == True{}: Bool}:
  match ma:
    case None{}:
      ek => e => Empty.absurd(
        {Spec.Answer.follows(x, Spec.Answer.held(b, i, q, mb)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Answer, x, e)
      )
    case Some{+c}:
      ek => e =>
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, mb, Some{c}, Cell.kept.eq(c, mb)(ek)): {
          Spec.Answer.follows(x, Spec.Answer.held(b, i, q, _)) == True{}: Bool
        }
        %e: {Follows.opt(_, Spec.Answer.held(b, i, q, Some{c})) == True{}: Bool}
        Held.follows(a, b, i, q, Some{c}, ho)

def Spec.Node.answer_follows(n, evs, s, e, q, x):
  Answer.follows.at(
    s,
    Spec.Node.after(n, evs, s),
    Spec.Envelope.of(e),
    q,
    x,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))),
    Ledgers.State.get(
      ~Spec.Ask,
      Spec.State.ledger(Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    ),
    o => Out.kept(
      s,
      Spec.Node.after(n, evs, s),
      Spec.Envelope.of(e),
      o,
      Spec.Node.after_grows(n, evs, s),
      Spec.Node.after_keeps(n, evs, s)
    )
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      ~Cells.Cell.keeps(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
      ~Cells.Cell.none_kept(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
      Spec.State.ledger(s),
      Spec.State.ledger(Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )(Spec.Node.after_grows(n, evs, s))
  )

# Drafts
# ------

# one of two drafts that are there
def When.some(
  b: Bool,
  -x: Maybe<&2, Spec.Draft>,
  -y: Maybe<&2, Spec.Draft>,
  hx: {Maybe.is_some(&2, Spec.Draft, x) == True{}: Bool},
  hy: {Maybe.is_some(&2, Spec.Draft, y) == True{}: Bool}
) -> {Maybe.is_some(&2, Spec.Draft, Shared.Bool.when(Maybe<&2, Spec.Draft>, b, u => x, u => y)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a draft that is there stays, with a write or not
def Draft.with.some(
  -found: Maybe<&2, Spec.Draft>,
  -k: List<&2, Bool>,
  m: Maybe<&2, Spec.Content>
) -> {Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.with(found, k, m)) == True{}: Bool}:
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
  a: Maybe<&2, Ledgers.Asked<Spec.Ask>>,
  -found: Maybe<&2, Spec.Draft>
) -> {Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, i, a, found)) == True{}: Bool}:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      +h => When.some(
        String.eq(w2, w),
        Spec.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), Spec.Draft.content(r, b, n, q)),
        found,
        Draft.with.some(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), Spec.Draft.content(r, b, n, q))(h),
        h
      )
    case Ledgers.Id{w2, q2} None{}:
      h => h

# a draft that is there stays, after more requests
def Last.some(
  +s: Spec.State(),
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  found: Maybe<&2, Spec.Draft>
) -> {Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool}:
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
        Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found)
      )(Draft.of.some(w, r, b, n, i, Spec.Node.asked(s, i), found)(h))

# a write of the writer w to the resource gives a draft
def Draft.of.hit(
  w: String,
  -r: Ledgers.Id,
  -b: String,
  -n: Resources.Name,
  -q2: String,
  -t: String,
  -q: Spec.Ask,
  -c: Spec.Content,
  -found: Maybe<&2, Spec.Draft>,
  ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Spec.Content>}
) -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, Some{Ledgers.Asked{t, q}}, found)) == True{}: Bool}:
  %Equal.sym(Bool, String.eq(w, w), True{}, Texts.String.eq_refl(w)): {
    Maybe.is_some(
      &2,
      Spec.Draft,
      Shared.Bool.when(
        Maybe<&2, Spec.Draft>,
        _,
        u => Spec.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), Spec.Draft.content(r, b, n, q)),
        u => found
      )
    )
      == True{}: Bool
  }
  %Equal.sym(Maybe<&2, Spec.Content>, Spec.Draft.content(r, b, n, q), Some{c}, ec): {
    Maybe.is_some(&2, Spec.Draft, Spec.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), _)) == True{}: Bool
  }
  {==}

# Last.hit once whether the first request is the one looked for is known (bh)
def Last.hit.if(
  +s: Spec.State(),
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  +i: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  found: Maybe<&2, Spec.Draft>,
  q2: String,
  -t: String,
  -q: Spec.Ask,
  -c: Spec.Content,
  bh: Bool,
  ebh: {Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}) == bh: Bool},
  ea: {Spec.Node.asked(s, Ledgers.Id{w, q2}) == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Spec.Ask>>},
  ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Spec.Content>},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}) == True{}: Bool
  } -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.last(s, w, r, b, n, rest, Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found))) == True{}: Bool}
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}), bh) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.last(s, w, r, b, n, rest, Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found))) == True{}: Bool}:
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
        Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found)
      )(
        %Equal.sym(
          Ledgers.Id,
          i,
          Ledgers.Id{w, q2},
          Ledgers.Id.is_eq_sound(i, Ledgers.Id{w, q2})(ebh)
        ): {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, _, Spec.Node.asked(s, _), found)) == True{}: Bool}
        %Equal.sym(
          Maybe<&2, Ledgers.Asked<Spec.Ask>>,
          Spec.Node.asked(s, Ledgers.Id{w, q2}),
          Some{Ledgers.Asked{t, q}},
          ea
        ): {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, _, found)) == True{}: Bool}
        Draft.of.hit(w, r, b, n, q2, t, q, c, found, ec)
      )

# a write of the writer w among requests gives a draft
def Last.hit(
  +s: Spec.State(),
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  +found: Maybe<&2, Spec.Draft>,
  +q2: String,
  -t: String,
  -q: Spec.Ask,
  -c: Spec.Content,
  +ea: {Spec.Node.asked(s, Ledgers.Id{w, q2}) == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Spec.Ask>>},
  +ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Spec.Content>}
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, Ledgers.Id{w, q2}) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => Empty.absurd(
        {Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool},
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
          Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found),
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
  m: Maybe<&2, Spec.Draft>
) -> {Maybe.is_some(&2, Spec.Draft, m) == True{}: Bool} -> {Maybe.is_some(&2, Spec.Content, Spec.Draft.what(m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{Spec.Draft{k, c}}:
      h => {==}

def Spec.Node.draft_some(s, w, r, b, n, q2, t, q, c):
  hc => ea => ec => What.some(
    Spec.Draft.last(s, w, r, b, n, Spec.Wait.of(s, Spec.Line.chain(r, Some{b})), None{})
  )(
    Last.hit(
      s,
      w,
      r,
      b,
      n,
      Spec.Wait.of(s, Spec.Line.chain(r, Some{b})),
      None{},
      q2,
      t,
      q,
      c,
      ea,
      ec
    )(hc)
  )

# Agreement
# ---------

# no owners decide nothing
def Decide.none(
  l: Ledgers.State(Spec.Ask),
  w: Ledgers.Where
) -> {Ledgers.State.decide(~Spec.Ask, l, w, []) == None{}: Maybe<&2, Ledgers.Vote>}:
  match w:
    case Ledgers.Where{c, h, z}:
      {==}

# Owners.up once what the log holds under the owners' key is known (m)
def Owners.up.at(
  a: Spec.State(),
  u: Spec.State(),
  t: Spec.Tip,
  w: Ledgers.Where,
  -v: Ledgers.Vote,
  m: Maybe<&2, List<&2, U32>>,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {Spec.Node.get(a, Spec.Tip.log(t), Spec.Log.owners()) == m: Maybe<&2, List<&2, U32>>} -> {
  Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, Maybe.default(&2, List<&2, String>, Maybe.bind(&2, List<&2, U32>, List<&2, String>, m, ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))), [])) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Maybe.default(&2, List<&2, String>, Maybe.bind(&2, List<&2, U32>, List<&2, String>, m, ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))), []) == Spec.Line.owners(u, t): List<&2, String>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {[] == Spec.Line.owners(u, t): List<&2, String>},
        Shared.Maybe.none_ne_some(
          Ledgers.Vote,
          v,
          Equal.trans(
            Maybe<&2, Ledgers.Vote>,
            None{},
            Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, []),
            Some{v},
            Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, []), None{}, Decide.none(Spec.State.ledger(a), w)),
            e
          )
        )
      )
    case Some{ws}:
      em => e =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(u, Spec.Tip.log(t), Spec.Log.owners()),
          Some{ws},
          Get.grows(a, u, Spec.Tip.log(t), Spec.Log.owners(), ws, g)(em)
        ): {Maybe.default(&2, List<&2, String>, Maybe.bind(&2, List<&2, U32>, List<&2, String>, Some{ws}, ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))), []) == Maybe.default(&2, List<&2, String>, Maybe.bind(&2, List<&2, U32>, List<&2, String>, _, ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))), []): List<&2, String>}
        {==}

# owners that decide a step are the owners in any node that grew
def Owners.up(
  +a: Spec.State(),
  u: Spec.State(),
  +t: Spec.Tip,
  w: Ledgers.Where,
  -v: Ledgers.Vote,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, Spec.Line.owners(a, t)) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Line.owners(a, t) == Spec.Line.owners(u, t): List<&2, String>
}:
  Owners.up.at(a, u, t, w, v, Spec.Node.get(a, Spec.Tip.log(t), Spec.Log.owners()), g)({==})

# a step that the owners decided at a place in a, they decided in a node that
# grew, with the owners that it reads
def Decide.up(
  +a: Spec.State(),
  +u: Spec.State(),
  +t: Spec.Tip,
  +w: Ledgers.Where,
  +v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, Spec.Line.owners(a, t)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), w, Spec.Line.owners(u, t)) == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  +e =>
    %Owners.up(a, u, t, w, v, g)(e): {
      Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), w, _) == Some{v}: Maybe<&2, Ledgers.Vote>
    }
    Ledgers.State.decide_grows(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      Spec.State.ledger(a),
      Spec.State.ledger(u),
      w,
      Spec.Line.owners(a, t),
      v
    )(g)(e)

# Scan.elim at a round, once what it decides is known (m)
def Scan.elim.at(
  -R: Type,
  -s: Spec.State(),
  -c: Ledgers.Chain,
  -n: U32,
  -os: List<&2, String>,
  -p: Nat,
  -v: Ledgers.Vote,
  +r: U32,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {Spec.Height.decide(s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>} -> (@q: U32 -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, q}, os) == Some{v}: Maybe<&2, Ledgers.Vote>} -> R) -> R
) -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, r}, os) == m: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Vote.first(m, u => Spec.Height.decide(s, c, n, os, p)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (@q: U32 -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, q}, os) == Some{v}: Maybe<&2, Ledgers.Vote>} -> R) -> R:
  match m:
    case None{}:
      em => e => f => rec(e)(f)
    case Some{x}:
      em => e => f => f(r)(Equal.trans(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, r}, os), Some{x}, Some{v}, em, e))

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  -R: Type,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {Spec.Height.decide(s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> (@q: U32 -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, q}, os) == Some{v}: Maybe<&2, Ledgers.Vote>} -> R) -> R:
  match k:
    case 0n:
      e => f => f(0)(e)
    case 1n+(+p):
      Scan.elim.at(
        R,
        s,
        c,
        n,
        os,
        p,
        v,
        U32.from_nat(1n+p),
        Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, U32.from_nat(1n+p)}, os),
        Scan.elim(R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Spec.Head) -> {Spec.Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Spec.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# that the head of the line c in the node s2, when it is not at the height of
# h, is x
def Moves(s2: Spec.State(), c: Ledgers.Chain, h: Spec.Head, x: Spec.Head) -> Type:
  {Spec.Heads.level(Some{h}, Spec.Node.head_of(s2, c)) == False{}: Bool} -> {Spec.Node.head_of(s2, c) == Some{x}: Maybe<&2, Spec.Head>}

# a node whose head is h did not move it
def Stay(
  -s: Spec.State(),
  -c: Ledgers.Chain,
  h: Spec.Head,
  -x: Spec.Head,
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>}
) -> Moves(s, c, h, x):
  hl => Empty.absurd(
    {Spec.Node.head_of(s, c) == Some{x}: Maybe<&2, Spec.Head>},
    Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Spec.Heads.level(Some{h}, Some{h}),
        True{},
        Equal.trans(
          Bool,
          False{},
          Spec.Heads.level(Some{h}, Spec.Node.head_of(s, c)),
          Spec.Heads.level(Some{h}, Some{h}),
          Equal.sym(Bool, Spec.Heads.level(Some{h}, Spec.Node.head_of(s, c)), False{}, hl),
          Equal.cong(
            Maybe<&2, Spec.Head>,
            Bool,
            m => Spec.Heads.level(Some{h}, m),
            Spec.Node.head_of(s, c),
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
  -sx: Spec.State(),
  -sy: Spec.State(),
  -c: Ledgers.Chain,
  -h: Spec.Head,
  -x: Spec.Head,
  hx: Moves(sx, c, h, x),
  hy: Moves(sy, c, h, x)
) -> Moves(Shared.Bool.when(Spec.State(), b, u => sx, u => sy), c, h, x):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of a line, after it is set
def Head.at_set(
  b0: Spec.State(),
  +c: Ledgers.Chain,
  hd: Spec.Head
) -> {Spec.Node.head_of(Spec.State.head(b0, c, hd), c) == Some{hd}: Maybe<&2, Spec.Head>}:
  Equal.trans(
    Maybe<&2, Spec.Head>,
    Spec.Node.head_of(Spec.State.head(b0, c, hd), c),
    Bool.pick(
      Maybe<&2, Spec.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Spec.Node.head_of(b0, c)
    ),
    Some{hd},
    Head.of_set(b0, c, hd, c),
    Pick.of(
      Maybe<&2, Spec.Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Spec.Node.head_of(b0, c),
      Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
    )
  )

# Advance.moved moves the head to hd, or not at all
def Advance.moved.moves(
  +s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  hd: Spec.Head,
  qs: List<&2, Ledgers.Id>,
  h: Spec.Head,
  -x: Spec.Head,
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ex: {hd == x: Spec.Head}
) -> Moves(Spec.Advance.moved(s, m, c, hd, qs), c, h, x):
  match m:
    case None{}:
      Stay(s, c, h, x, em)
    case Some{+s3}:
      hl =>
        %ex: {
          Spec.Node.head_of(
            Spec.State.moved(Spec.State.led(s, Spec.State.ledger(s3)), c, hd, qs),
            c
          )
            == Some{_}: Maybe<&2, Spec.Head>
        }
        Head.at_set(
          Spec.Wait.set(
            Spec.State.led(s, Spec.State.ledger(s3)),
            c,
            Spec.Wait.left(
              Spec.Wait.of(Spec.State.led(s, Spec.State.ledger(s3)), c),
              Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
            )
          ),
          c,
          hd
        )

# Advance.ran.moves once whether the run gives the tip that the step names is
# known (bq)
def Advance.ran.moves.if(
  s: Spec.State(),
  s2: Spec.State(),
  +t2: Spec.Tip,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  h: Spec.Head,
  -x: Spec.Head,
  bq: Bool,
  ebq: {Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == bq: Bool},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ex: {Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == True{}: Bool} -> {
    Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}} == x: Spec.Head
  }
) -> Moves(
  Shared.Bool.when(
    Spec.State(),
    bq,
    u => Spec.Advance.moved(
      s,
      Spec.State.put(s2, [Spec.Tip.words(t2)]),
      c,
      Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}},
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
        Spec.State.put(s2, [Spec.Tip.words(t2)]),
        c,
        Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}},
        qs,
        h,
        x,
        em,
        ex(ebq)
      )
    case False{}:
      Stay(s, c, h, x, em)

# a checked step moves the head to the tip that the step names, or not at all
def Advance.ran.moves(
  s: Spec.State(),
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  h: Spec.Head,
  -x: Spec.Head,
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ex: @t2: Spec.Tip -> {Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == True{}: Bool} -> {
    Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}} == x: Spec.Head
  }
) -> Moves(Spec.Advance.ran(s, c, r, br, next, after, qs, m), c, h, x):
  match m:
    case None{}:
      Stay(s, c, h, x, em)
    case Some{Spec.Run{s2, +t2, ns}}:
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
        Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
        {==},
        em,
        ex(t2)
      )

# Node.advance moves the head by the decided step m, or not at all
def Advance.step.moves(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  t: Spec.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>} -> Moves(Spec.Advance.step(s, c, h, t, m), c, h, Spec.Head.step(h, m)):
  match h m:
    case Spec.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(
        Spec.Root.same(before, th),
        Spec.Advance.ran(s, c, r, br, next, after, qs, Spec.Step.run(s, c, t, qs)),
        s,
        c,
        Spec.Head{r, br, next, th},
        Spec.Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
        Advance.ran.moves(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Spec.Step.run(s, c, t, qs),
          Spec.Head{r, br, next, th},
          Spec.Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(
              Maybe<&2, Hashes.Hash>,
              after,
              Some{Spec.Tip.hash(t2)},
              Shared.Maybe.is_eq_sound(
                ~Hashes.Hash,
                ~Hashes.Hash.is_eq,
                x => y => Hashes.Hash.is_eq_sound(x, y),
                after,
                Some{Spec.Tip.hash(t2)}
              )(er)
            ): {
              Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}}
                == Spec.Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Spec.Head
            }
            {==}
        ),
        Stay(
          s,
          c,
          Spec.Head{r, br, next, th},
          Spec.Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em
        )
      )
    case Spec.Head{+r, +br, +next, +th} None{}:
      em => Stay(s, c, Spec.Head{r, br, next, th}, Spec.Head{r, br, next, th}, em)

# Node.advance moves the head by the step decided at the head h, whose tip is
# m, or not at all
def Advance.at.moves(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>} -> {Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>} -> Moves(
  Spec.Advance.at(s, c, h, m),
  c,
  h,
  Spec.Head.step(h, Spec.Advance.vote(s, c, h))
):
  match m:
    case None{}:
      em => et => Stay(s, c, h, Spec.Head.step(h, Spec.Advance.vote(s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Spec.Advance.vote(s, c, h),
          Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h)))),
          Equal.cong(
            Maybe<&2, Spec.Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Spec.Tip,
              Ledgers.Vote,
              mt,
              t1 => Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t1), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h))))
            ),
            Spec.Head.tip(s, h),
            Some{t},
            et
          )
        ): Moves(
          Spec.Advance.step(
            s,
            c,
            h,
            t,
            Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h))))
          ),
          c,
          h,
          Spec.Head.step(h, _)
        )
        Advance.step.moves(
          s,
          c,
          h,
          t,
          Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), U32.to_nat(Spec.Round.seen(s, c, Spec.Head.next(h))))
        )(em)

def Spec.Node.advance_decided(s, c, h):
  +em =>
    %Equal.sym(Maybe<&2, Spec.Head>, Spec.Node.head_of(s, c), Some{h}, em): Moves(
      Spec.Advance.head(s, c, _),
      c,
      h,
      Spec.Head.step(h, Spec.Advance.vote(s, c, h))
    )
    Advance.at.moves(s, c, h, Spec.Head.tip(s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  -R: Type,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>} -> {
  Maybe.bind(&2, Spec.Tip, Ledgers.Vote, m, t => Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), k)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (@t: Spec.Tip -> @q: U32 -> {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>} -> {
  Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, Spec.Head.next(h), q}, Spec.Line.owners(s, t)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> R) -> R:
  match m:
    case None{}:
      em => e => f => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Vote, v, e))
    case Some{+t}:
      em => e => f => Scan.elim(R, s, c, Spec.Head.next(h), Spec.Line.owners(s, t), k, v)(e)(q => d => f(t)(q)(em)(d))

# a step that a node found at a head is decided at the head's tip, in some
# round
def Found.elim(
  -R: Type,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {Spec.Advance.found(s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> (@t: Spec.Tip -> @q: U32 -> {
  Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>
} -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, Spec.Head.next(h), q}, Spec.Line.owners(s, t)) == Some{v}: Maybe<&2, Ledgers.Vote>} -> R) -> R:
  Found.elim.at(R, s, c, h, k, v, Spec.Head.tip(s, h))({==})

# the steps that two nodes found at one head are the same, when their ledgers
# do not clash and the rounds of the height decide one step
def Agree.votes(
  +a: Spec.State(),
  +b: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  ka: Nat,
  kb: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  +ga: {Spec.Node.grows(a, u) == True{}: Bool},
  +gb: {Spec.Node.grows(b, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Advance.found(a, c, h, ka) == Some{v1}: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Advance.found(b, c, h, kb) == Some{v2}: Maybe<&2, Ledgers.Vote>
} -> {v1 == v2: Ledgers.Vote}:
  ea => eb => Found.elim({v1 == v2: Ledgers.Vote}, a, c, h, ka, v1)(ea)(
    +t => +q => +et => ed => Found.elim({v1 == v2: Ledgers.Vote}, b, c, h, kb, v2)(eb)(
      +tb => +q2 => etb => edb => one(h)(t)(Head.tip.grows(a, u, h, t, ga)(et))(q)(q2)(v1)(v2)(
        Decide.up(a, u, t, Ledgers.Where{c, Spec.Head.next(h), q}, v1, ga)(ed)
      )(
        %Equal.sym(
          Spec.Tip,
          t,
          tb,
          Shared.Maybe.some_inj(
            Spec.Tip,
            t,
            tb,
            Equal.trans(
              Maybe<&2, Spec.Tip>,
              Some{t},
              Spec.Head.tip(u, h),
              Some{tb},
              Equal.sym(Maybe<&2, Spec.Tip>, Spec.Head.tip(u, h), Some{t}, Head.tip.grows(a, u, h, t, ga)(et)),
              Head.tip.grows(b, u, h, tb, gb)(etb)
            )
          )
        ): {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, Spec.Head.next(h), q2}, Spec.Line.owners(u, _)) == Some{v2}: Maybe<&2, Ledgers.Vote>}
        Decide.up(b, u, tb, Ledgers.Where{c, Spec.Head.next(h), q2}, v2, gb)(edb)
      )
    )
  )

# two nodes whose ledgers do not clash, at the same head, step it the same
def Agree.steps(
  +a: Spec.State(),
  +b: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  va: Maybe<&2, Ledgers.Vote>,
  vb: Maybe<&2, Ledgers.Vote>,
  ga: {Spec.Node.grows(a, u) == True{}: Bool},
  gb: {Spec.Node.grows(b, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Advance.vote(a, c, h) == va: Maybe<&2, Ledgers.Vote>} -> {Spec.Advance.vote(b, c, h) == vb: Maybe<&2, Ledgers.Vote>} -> {Spec.Heads.level(Some{h}, Some{Spec.Head.step(h, va)}) == False{}: Bool} -> {Spec.Heads.level(Some{h}, Some{Spec.Head.step(h, vb)}) == False{}: Bool} -> {
  Spec.Head.step(h, va) == Spec.Head.step(h, vb): Spec.Head
}:
  match h va vb:
    case Spec.Head{+r, +br, +n, +th} Some{+v1} Some{+v2}:
      ea => eb => ma => mb => Equal.cong(
        Ledgers.Vote,
        Spec.Head,
        v => Spec.Head.step(Spec.Head{r, br, n, th}, Some{v}),
        v1,
        v2,
        Agree.votes(
          a,
          b,
          u,
          c,
          Spec.Head{r, br, n, th},
          U32.to_nat(Spec.Round.seen(a, c, n)),
          U32.to_nat(Spec.Round.seen(b, c, n)),
          v1,
          v2,
          ga,
          gb,
          one
        )(ea)(eb)
      )
    case Spec.Head{r, br, +n, th} None{} y:
      ea => eb => ma => mb => Empty.absurd(
        {Spec.Head{r, br, n, th} == Spec.Head.step(Spec.Head{r, br, n, th}, y): Spec.Head},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            U32.is_eq(n, n),
            True{},
            Equal.sym(Bool, U32.is_eq(n, n), False{}, ma),
            Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)
          )
        )
      )
    case Spec.Head{r, br, +n, th} Some{v1} None{}:
      ea => eb => ma => mb => Empty.absurd(
        {
          Spec.Head.step(Spec.Head{r, br, n, th}, Some{v1}) == Spec.Head{r, br, n, th}: Spec.Head
        },
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            U32.is_eq(n, n),
            True{},
            Equal.sym(Bool, U32.is_eq(n, n), False{}, mb),
            Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)
          )
        )
      )

def Spec.Node.advance_agrees(a, b, u, c, h):
  ga => gb => one => +ea => +eb => +la => +lb => Equal.trans(
    Maybe<&2, Spec.Head>,
    Spec.Node.head_of(Spec.Node.advance(a, c), c),
    Some{Spec.Head.step(h, Spec.Advance.vote(a, c, h))},
    Spec.Node.head_of(Spec.Node.advance(b, c), c),
    Spec.Node.advance_decided(a, c, h)(ea)(la),
    Equal.trans(
      Maybe<&2, Spec.Head>,
      Some{Spec.Head.step(h, Spec.Advance.vote(a, c, h))},
      Some{Spec.Head.step(h, Spec.Advance.vote(b, c, h))},
      Spec.Node.head_of(Spec.Node.advance(b, c), c),
      Equal.cong(
        Spec.Head,
        Maybe<&2, Spec.Head>,
        x => Some{x},
        Spec.Head.step(h, Spec.Advance.vote(a, c, h)),
        Spec.Head.step(h, Spec.Advance.vote(b, c, h)),
        Agree.steps(
          a,
          b,
          u,
          c,
          h,
          Spec.Advance.vote(a, c, h),
          Spec.Advance.vote(b, c, h),
          ga,
          gb,
          one
        )({==})({==})(
          %Spec.Node.advance_decided(a, c, h)(ea)(la): {Spec.Heads.level(Some{h}, _) == False{}: Bool}
          la
        )(
          %Spec.Node.advance_decided(b, c, h)(eb)(lb): {Spec.Heads.level(Some{h}, _) == False{}: Bool}
          lb
        )
      ),
      Equal.sym(
        Maybe<&2, Spec.Head>,
        Spec.Node.head_of(Spec.Node.advance(b, c), c),
        Some{Spec.Head.step(h, Spec.Advance.vote(b, c, h))},
        Spec.Node.advance_decided(b, c, h)(eb)(lb)
      )
    )
  )

# Writes
# ------

# the value of a resource reads back
def Res.round(m: Maybe<&2, Ropes.Root>) -> {Spec.Res.read(Spec.Res.code(m)) == m: Maybe<&2, Ropes.Root>}:
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
  ): {Spec.Res.of.read(_) == m: Maybe<&2, Ropes.Root>}
  {==}

# the verdict m takes
def Took(m: Maybe<&2, Spec.Verdict>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{Spec.Verdict{t, h, ds}}:
      t

# the tree of the verdict m
def Took.root(m: Maybe<&2, Spec.Verdict>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{Spec.Verdict{t, h, ds}}:
      h

# the new nodes of the verdict m
def Took.nodes(m: Maybe<&2, Spec.Verdict>) -> List<&2, List<&2, U32>>:
  match m:
    case None{}:
      []
    case Some{Spec.Verdict{t, h, ds}}:
      ds

# a verdict that takes, after a verdict, is the verdict of what comes next
def Then.took(
  m: Maybe<&2, Bool>,
  -h: Maybe<&2, Hashes.Hash>,
  -k: Unit -> Maybe<&2, Spec.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>
) -> {Spec.Judge.then(m, h, k) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>} -> {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}:
  match m:
    case Some{True{}}:
      e => e
    case Some{False{}}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Spec.Verdict>, Bool, v => Took(v), Spec.Judge.refuse(h), Some{Spec.Verdict{True{}, h2, ds}}, e)
        )
      )
    case None{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Maybe.none_ne_some(Spec.Verdict, Spec.Verdict{True{}, h2, ds}, e)
      )

# a verdict that takes, under a condition, is the verdict of what comes next
def When.took(
  b: Bool,
  -h: Maybe<&2, Hashes.Hash>,
  -k: Unit -> Maybe<&2, Spec.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>
) -> {Spec.Judge.when(b, h, k) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>} -> {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(Maybe<&2, Spec.Verdict>, Bool, v => Took(v), Spec.Judge.refuse(h), Some{Spec.Verdict{True{}, h2, ds}}, e)
        )
      )

# Set.reads once the node m2 that the put of the new subtree gives is known
def Set.reads.put(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  m2: Maybe<&2, Spec.State()>,
  -h2: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>,
  +s3: Spec.State()
) -> {Spec.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>} -> {
  Spec.Work.take(Spec.Work.put(m2, Some{hh}, ws, [])) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool} -> {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m2:
    case None{}:
      es => e => hd => Empty.absurd(
        {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Spec.Verdict, Spec.Verdict{True{}, h2, ds}, e)
      )
    case Some{sk}:
      es => +e => hd =>
        %Equal.cong(
          Maybe<&2, Spec.Verdict>,
          Maybe<&2, Hashes.Hash>,
          v => Took.root(v),
          Some{Spec.Verdict{True{}, Some{hh}, List.append(&2, List<&2, U32>, ws, [])}},
          Some{Spec.Verdict{True{}, h2, ds}},
          e
        ): {Spec.Node.get(s3, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(s3, Some{hh}, k),
          Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, s3, Some{hh}, k),
          Some{x},
          Get.is(s3, Some{hh}, k),
          Trees.Tree.get_set(
            ~Spec.State(),
            ~Spec.Store.fetch,
            s,
            s3,
            h,
            k,
            x,
            Trees.Put{hh, ws}
          )(
            Equal.trans(
              Maybe<&2, Trees.Put>,
              Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x),
              Spec.Node.set(s, h, k, x),
              Some{Trees.Put{hh, ws}},
              Equal.sym(
                Maybe<&2, Trees.Put>,
                Spec.Node.set(s, h, k, x),
                Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x),
                Set.is(s, h, k, x)
              ),
              es
            )
          )(
            %Shared.List.append_nil(List<&2, U32>, ws): {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, _) == True{}: Bool}
            %Equal.sym(
              List<&2, List<&2, U32>>,
              List.append(&2, List<&2, U32>, ws, []),
              ds,
              Equal.cong(
                Maybe<&2, Spec.Verdict>,
                List<&2, List<&2, U32>>,
                v => Took.nodes(v),
                Some{Spec.Verdict{True{}, Some{hh}, List.append(&2, List<&2, U32>, ws, [])}},
                Some{Spec.Verdict{True{}, h2, ds}},
                e
              )
            ): {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, _) == True{}: Bool}
            hd
          )
        )

# a key set in a tree, when the verdict takes the new tree, reads back in a
# node that holds the new nodes
def Set.reads(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  -h2: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>,
  s3: Spec.State()
) -> {Spec.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>} -> {
  Spec.Work.take(Spec.Work.of(s, [], m)) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool} -> {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      es => e => hd => Empty.absurd(
        {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Spec.Verdict, Spec.Verdict{True{}, h2, ds}, e)
      )
    case Some{Trees.Put{hh, +ws}}:
      Set.reads.put(s, h, k, x, hh, ws, Spec.State.put(s, ws), h2, ds, s3)

# a verdict that takes, after a read, is the verdict of what comes next
def With.took(
  -A: Data,
  ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Spec.Verdict>,
  -kk: Maybe<&2, Spec.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>
) -> (@a: A -> {k(a) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>} -> {kk == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}) -> {
  Maybe.bind(&2, A, Spec.Verdict, ma, k) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {kk == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}:
  match ma:
    case None{}:
      hk => e => Empty.absurd(
        {kk == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Maybe.none_ne_some(Spec.Verdict, Spec.Verdict{True{}, h2, ds}, e)
      )
    case Some{a}:
      hk => e => hk(a)(e)

def Spec.Judge.write_reads(s, n, base, c, h, h2, ds, s3, m):
  e => ep => ec =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Spec.Node.get(s3, h2, Spec.Key.res(n)),
      Some{Spec.Res.code(m)},
      Set.reads(
        s,
        h,
        Spec.Key.res(n),
        Spec.Res.code(m),
        Spec.Node.set(s, h, Spec.Key.res(n), Spec.Res.code(m)),
        h2,
        ds,
        s3
      )({==})(
        With.took(
          Maybe<&2, Ropes.Root>,
          Spec.Res.find(s, h, n),
          a1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Res.find(s, Spec.Node.root_of(s, base), n), b1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Content.find(s, n, c), m1 => Spec.Judge.when(Spec.Roots.same(a1, b1), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1)))))),
          Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))),
          h2,
          ds
        )(
          +a => With.took(
            Maybe<&2, Ropes.Root>,
            Spec.Res.find(s, Spec.Node.root_of(s, base), n),
            b1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Content.find(s, n, c), m1 => Spec.Judge.when(Spec.Roots.same(a, b1), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))))),
            Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))),
            h2,
            ds
          )(
            +b => ex => When.took(
              Spec.Roots.same(a, b),
              h,
              x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))),
              h2,
              ds
            )(
              %ec: {
                Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, _, m1 => Spec.Judge.when(Spec.Roots.same(a, b), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))))) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
              }
              ex
            )
          )
        )(
          Then.took(
            Spec.Judge.content(s, c),
            h,
            w => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Res.find(s, h, n), a1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Res.find(s, Spec.Node.root_of(s, base), n), b1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Content.find(s, n, c), m1 => Spec.Judge.when(Spec.Roots.same(a1, b1), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))))))),
            h2,
            ds
          )(
            Then.took(
              Spec.Judge.ready_maybe(s, base),
              h,
              u => Spec.Judge.then(Spec.Judge.content(s, c), h, w => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Res.find(s, h, n), a1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Res.find(s, Spec.Node.root_of(s, base), n), b1 => Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, Spec.Content.find(s, n, c), m1 => Spec.Judge.when(Spec.Roots.same(a1, b1), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1)))))))),
              h2,
              ds
            )(e)
          )
        )
      )(Put.holds(s, ds, s3)(ep))
    ): {Maybe.bind(&2, List<&2, U32>, Ropes.Root, _, ws => Spec.Res.read(ws)) == m: Maybe<&2, Ropes.Root>}
    Res.round(m)

# Merges
# ------

def Spec.Pick.merge_theirs(f, s, b, o, t):
  e =>
    %Equal.sym(Bool, Spec.Roots.same(o, b), True{}, e): {
      Shared.Bool.when(
      Maybe<&2, Spec.Pick>,
      _,
      u => Some{Spec.Pick.Take{t}},
      u => Shared.Bool.when(
        Maybe<&2, Spec.Pick>,
        List.any.if(v => Spec.Roots.same(o, t), Spec.Roots.same(t, b)),
        w => Some{Spec.Pick.Take{o}},
        w => Spec.Pick.both(f, s, b, o, t)
      )
    )
        == Some{Spec.Pick.Take{t}}: Maybe<&2, Spec.Pick>
    }
    {==}

def Spec.Pick.merge_ours(f, s, b, o, t):
  e1 => e2 =>
    %Equal.sym(Bool, Spec.Roots.same(o, b), False{}, e1): {
      Shared.Bool.when(
      Maybe<&2, Spec.Pick>,
      _,
      u => Some{Spec.Pick.Take{t}},
      u => Shared.Bool.when(
        Maybe<&2, Spec.Pick>,
        List.any.if(v => Spec.Roots.same(o, t), Spec.Roots.same(t, b)),
        w => Some{Spec.Pick.Take{o}},
        w => Spec.Pick.both(f, s, b, o, t)
      )
    )
        == Some{Spec.Pick.Take{o}}: Maybe<&2, Spec.Pick>
    }
    %Equal.sym(Bool, Spec.Roots.same(t, b), True{}, e2): {
      Shared.Bool.when(
      Maybe<&2, Spec.Pick>,
      False{},
      u => Some{Spec.Pick.Take{t}},
      u => Shared.Bool.when(
        Maybe<&2, Spec.Pick>,
        List.any.if(v => Spec.Roots.same(o, t), _),
        w => Some{Spec.Pick.Take{o}},
        w => Spec.Pick.both(f, s, b, o, t)
      )
    )
        == Some{Spec.Pick.Take{o}}: Maybe<&2, Spec.Pick>
    }
    {==}

# Seals
# -----

# Seal.accept_fits once whether the ballot fits is known (f)
def Accept.fits.if(
  f: Bool,
  -x: Spec.State(),
  -s2: Spec.State()
) -> {Shared.Maybe.when(Spec.State(), f, u => Some{x}) == Some{s2}: Maybe<&2, Spec.State()>} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Spec.State(), s2, e))

def Spec.Seal.accept_fits(s, b, c, s2):
  ec => ea => Accept.fits.if(
    Spec.Seal.fits(c, b),
    Spec.State.keyed(
      Spec.State.led(
        s,
        Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
      ),
      Spec.Keys.saw(Spec.Keys.set(
        Spec.State.keys(s),
        Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
        Spec.Chained.next(c, b)
      ), Spec.Ballot.at(b))
    ),
    s2
  )(
    %ec: {Spec.Seal.accept.at(s, b, _) == Some{s2}: Maybe<&2, Spec.State()>}
    ea
  )

# a place is the same as itself
def Prev.refl(m: Maybe<&2, Ledgers.Where>) -> {Spec.Prev.same(m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Ledgers.Where.code(w, []))

def Spec.Seal.fits_own(seed, x, last, k, n, f):
  Shared.List.all.if_both(
    Spec.Prev.same(last, last),
    u => Ledgers.Ballot.sealed(Seals.Seal.public(seed), Ledgers.Ballot.make(seed, x, last, k))
  )(Prev.refl(last))(Ledgers.Ballot.sealed_make(seed, x, last, k))

# a head that no step moves is at its own height
def Level.none(
  x: Spec.Head
) -> {Spec.Heads.level(Some{x}, Some{Spec.Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Spec.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# Histories
# ---------

# a step, or the step that rest gives, is there when rest gives one
def First.some(
  m: Maybe<&2, Ledgers.Vote>,
  -rest: Unit -> Maybe<&2, Ledgers.Vote>,
  h: {Maybe.is_some(&2, Ledgers.Vote, rest(Unit{})) == True{}: Bool}
) -> {Maybe.is_some(&2, Ledgers.Vote, Spec.Vote.first(m, rest)) == True{}: Bool}:
  match m:
    case Some{x}:
      {==}
    case None{}:
      h

# Scan.some at a round, once what the round decides in a is known (m)
def Scan.some.at(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  +p: Nat,
  -v: Ledgers.Vote,
  +r: U32,
  m: Maybe<&2, Ledgers.Vote>,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  ih: {Spec.Height.decide(a, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {Maybe.is_some(&2, Ledgers.Vote, Spec.Height.decide(u, c, n, os, p)) == True{}: Bool}
) -> {Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), Ledgers.Where{c, n, r}, os) == m: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Vote.first(m, w => Spec.Height.decide(a, c, n, os, p)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Maybe.is_some(&2, Ledgers.Vote, Spec.Vote.first(Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, n, r}, os), w => Spec.Height.decide(u, c, n, os, p))) == True{}: Bool}:
  match m:
    case None{}:
      em => e => First.some(Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, n, r}, os), w => Spec.Height.decide(u, c, n, os, p), ih(e))
    case Some{+x}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, n, r}, os),
          Some{x},
          Ledgers.State.decide_grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            Spec.State.ledger(a),
            Spec.State.ledger(u),
            Ledgers.Where{c, n, r},
            os,
            x
          )(g)(em)
        ): {Maybe.is_some(&2, Ledgers.Vote, Spec.Vote.first(_, w => Spec.Height.decide(u, c, n, os, p))) == True{}: Bool}
        {==}

# a height that decides a step in a, in a round up to k, decides one in a
# node that grew, in a round up to k
def Scan.some(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  +v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {Spec.Height.decide(a, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {Maybe.is_some(&2, Ledgers.Vote, Spec.Height.decide(u, c, n, os, k)) == True{}: Bool}:
  match k:
    case 0n:
      e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, n, 0}, os),
          Some{v},
          Ledgers.State.decide_grows(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        ~Ask.laws(),
        Spec.State.ledger(a),
        Spec.State.ledger(u),
        Ledgers.Where{c, n, 0},
        os,
        v
      )(g)(e)
        ): {Maybe.is_some(&2, Ledgers.Vote, _) == True{}: Bool}
        {==}
    case 1n+(+p):
      Scan.some.at(
        a,
        u,
        c,
        n,
        os,
        p,
        v,
        U32.from_nat(1n+p),
        Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), Ledgers.Where{c, n, U32.from_nat(1n+p)}, os),
        g,
        Scan.some(a, u, c, n, os, p, v, g)
      )({==})

# Scan.up once what the height decides in u is known (m)
def Scan.up.at(
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  +k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Height.decide(u, c, n, os, k) == m: Maybe<&2, Ledgers.Vote>} -> {Maybe.is_some(&2, Ledgers.Vote, m) == True{}: Bool} -> (@q: U32 -> @w: Ledgers.Vote -> {
  Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(u), Ledgers.Where{c, n, q}, os) == Some{w}: Maybe<&2, Ledgers.Vote>
} -> {w == v: Ledgers.Vote}) -> {m == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => hs => f => Empty.absurd({None{} == Some{v}: Maybe<&2, Ledgers.Vote>}, Shared.Bool.false_ne_true(hs))
    case Some{+w}:
      em => hs => f => Equal.cong(
        Ledgers.Vote,
        Maybe<&2, Ledgers.Vote>,
        x => Some{x},
        w,
        v,
        Scan.elim({w == v: Ledgers.Vote}, u, c, n, os, k, w)(em)(q => d => f(q)(w)(d))
      )

# a step that a height decides in a, in a round up to k, it decides in a
# node that grew, when the rounds of the height decide one step there
def Scan.up(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  +k: Nat,
  +v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  one: Spec.Height.One(u, c, n, os)
) -> {Spec.Height.decide(a, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {Spec.Height.decide(u, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  +e => Scan.elim({Spec.Height.decide(u, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>}, a, c, n, os, k, v)(e)(
    +q0 => d0 => Scan.up.at(u, c, n, os, k, v, Spec.Height.decide(u, c, n, os, k))({==})(
      Scan.some(a, u, c, n, os, k, v, g)(e)
    )(
      q => w => d => one(q)(q0)(w)(v)(d)(
        Ledgers.State.decide_grows(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        ~Ask.laws(),
        Spec.State.ledger(a),
        Spec.State.ledger(u),
        Ledgers.Where{c, n, q0},
        os,
        v
      )(g)(d0)
      )
    )
  )

# the owners that decide a step that a found at a head are the owners in a
# node that grew
def Owners.same(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  +t: Spec.Tip,
  k: Nat,
  +v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {Spec.Height.decide(a, c, Spec.Head.next(h), Spec.Line.owners(a, t), k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Line.owners(a, t) == Spec.Line.owners(u, t): List<&2, String>
}:
  e => Scan.elim(
    {Spec.Line.owners(a, t) == Spec.Line.owners(u, t): List<&2, String>},
    a,
    c,
    Spec.Head.next(h),
    Spec.Line.owners(a, t),
    k,
    v
  )(e)(q => d => Owners.up(a, u, t, Ledgers.Where{c, Spec.Head.next(h), q}, v, g)(d))

# Found.up once the tip m of the head in a is known
def Found.up.at(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  +k: Nat,
  +v: Ledgers.Vote,
  m: Maybe<&2, Spec.Tip>,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Head.tip(a, h) == m: Maybe<&2, Spec.Tip>} -> {
  Maybe.bind(&2, Spec.Tip, Ledgers.Vote, m, t => Spec.Height.decide(a, c, Spec.Head.next(h), Spec.Line.owners(a, t), k)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Advance.found(u, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Spec.Advance.found(u, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{+t}:
      +em => +e =>
        %Equal.sym(Maybe<&2, Spec.Tip>, Spec.Head.tip(u, h), Some{t}, Head.tip.grows(a, u, h, t, g)(em)): {
          Maybe.bind(
            &2,
            Spec.Tip,
            Ledgers.Vote,
            _,
            t1 => Spec.Height.decide(u, c, Spec.Head.next(h), Spec.Line.owners(u, t1), k)
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        %Owners.same(a, u, c, h, t, k, v, g)(e): {Spec.Height.decide(u, c, Spec.Head.next(h), _, k) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Scan.up(
          a,
          u,
          c,
          Spec.Head.next(h),
          Spec.Line.owners(a, t),
          k,
          v,
          g,
          (
            %Equal.sym(
              List<&2, String>,
              Spec.Line.owners(a, t),
              Spec.Line.owners(u, t),
              Owners.same(a, u, c, h, t, k, v, g)(e)
            ): Spec.Height.One(u, c, Spec.Head.next(h), _)
            one(h)(t)(Head.tip.grows(a, u, h, t, g)(em))
          )
        )(e)

# a step that a node found at a head, a node that grew finds there, when the
# rounds of the height decide one step in it
def Found.up(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  +k: Nat,
  +v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Advance.found(a, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>} -> {
  Spec.Advance.found(u, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  Found.up.at(a, u, c, h, k, v, Spec.Head.tip(a, h), g, one)({==})

# Moved.up once the step va that a found at the head is known
def Moved.up.at(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +x: Spec.Head,
  -y: Spec.Head,
  +k: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Advance.found(a, c, x, k) == va: Maybe<&2, Ledgers.Vote>} -> {Spec.Head.moved(x, va) == Some{y}: Maybe<&2, Spec.Head>} -> {
  Spec.Head.moved(x, Spec.Advance.found(u, c, x, k)) == Some{y}: Maybe<&2, Spec.Head>
}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Spec.Head.moved(x, Spec.Advance.found(u, c, x, k)) == Some{y}: Maybe<&2, Spec.Head>},
        Shared.Maybe.none_ne_some(
          Spec.Head,
          y,
          (
            %Level.none(x): {
              Shared.Maybe.when(Spec.Head, Bool.not(_), u1 => Some{Spec.Head.step(x, None{})})
                == Some{y}: Maybe<&2, Spec.Head>
            }
            e
          )
        )
      )
    case Some{+v}:
      ea => e =>
        %Equal.sym(Maybe<&2, Ledgers.Vote>, Spec.Advance.found(u, c, x, k), Some{v}, Found.up(a, u, c, x, k, v, g, one)(ea)): {
          Spec.Head.moved(x, _) == Some{y}: Maybe<&2, Spec.Head>
        }
        e

# a head that a step moves in a, it moves the same in a node that grew
def Moved.up(
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +x: Spec.Head,
  -y: Spec.Head,
  +k: Nat,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  one: Spec.Line.One(u, c)
) -> {Spec.Head.moved(x, Spec.Advance.found(a, c, x, k)) == Some{y}: Maybe<&2, Spec.Head>} -> {
  Spec.Head.moved(x, Spec.Advance.found(u, c, x, k)) == Some{y}: Maybe<&2, Spec.Head>
}:
  Moved.up.at(a, u, c, x, y, k, Spec.Advance.found(a, c, x, k), g, one)({==})

# Line.at_grows for one more step, with the witness of each step
def At.step.grows(
  +p: Nat,
  +a: Spec.State(),
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  +n: Nat,
  -x: Spec.Head,
  +g: {Spec.Node.grows(a, u) == True{}: Bool},
  ones: Spec.Line.Ones(p, u, c) & Spec.Line.One(u, c),
  ih: @z: Spec.Head -> Spec.Line.Ones(p, u, c) -> {Spec.Line.at(p, a, c, h, n) == Some{z}: Maybe<&2, Spec.Head>} -> {
    Spec.Line.at(p, u, c, h, n) == Some{z}: Maybe<&2, Spec.Head>
  }
) -> {Spec.Line.at(1n+p, a, c, h, n) == Some{x}: Maybe<&2, Spec.Head>} -> {
  Spec.Line.at(1n+p, u, c, h, n) == Some{x}: Maybe<&2, Spec.Head>
}:
  match ones:
    case Tuple{rest, one}:
      Shared.Maybe.bind_kept(
        Spec.Head,
        Spec.Head,
        Spec.Line.at(p, a, c, h, n),
        Spec.Line.at(p, u, c, h, n),
        +z => Spec.Head.moved(z, Spec.Advance.found(a, c, z, n)),
        +z => Spec.Head.moved(z, Spec.Advance.found(u, c, z, n)),
        x,
        z => ih(z)(rest),
        +z => Moved.up(a, u, c, z, x, n, g, one)
      )

def Spec.Line.at_grows(k, a, u, c, h, n, x):
  match k:
    case 0n:
      g => ones => e => e
    case 1n+(+p):
      +g => ones => At.step.grows(
        p,
        a,
        u,
        c,
        h,
        n,
        x,
        g,
        ones,
        +z => Spec.Line.at_grows(p, a, u, c, h, n, z)(g)
      )

def Spec.Line.at_agrees(k, a, b, u, c, h, n, x, y):
  ga => gb => ones1 => ones2 => ea => eb => Shared.Maybe.some_inj(
    Spec.Head,
    x,
    y,
    Equal.trans(
      Maybe<&2, Spec.Head>,
      Some{x},
      Spec.Line.at(k, u, c, h, n),
      Some{y},
      Equal.sym(
        Maybe<&2, Spec.Head>,
        Spec.Line.at(k, u, c, h, n),
        Some{x},
        Spec.Line.at_grows(k, a, u, c, h, n, x)(ga)(ones1)(ea)
      ),
      Spec.Line.at_grows(k, b, u, c, h, n, y)(gb)(ones2)(eb)
    )
  )

def Spec.Node.read_draft(s, w, r, b, n, c):
  e =>
    %Equal.sym(Maybe<&2, Spec.Content>, Spec.Node.draft(s, w, r, b, n), Some{c}, e): {
      Spec.Read.of(s, n, _, Spec.Point.Head{r, b})
        == Spec.Root.bytes(s, Spec.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }
    {==}
