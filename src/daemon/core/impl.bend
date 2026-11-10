# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/missed_fork@hint -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../shared.bend as Shared
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
  Spec.Owner.code.read(
    Spec.Owner.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Owner>>
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
  Maybe.bind(
    &2,
    Bool,
    Bool,
    m,
    k => Spec.Own.takes.at(s, h, g, os, k)
  )
    == Some{True{}}: Maybe<&2, Bool>
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
) -> {
  Trees.Tree.get.go(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    p,
    k,
    None{}
  )
    == None{}: Maybe<&2, List<&2, U32>>
}:
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
  Trees.Tree.get.go(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    p,
    k,
    Some{Trees.Node.Empty{}}
  )
    == None{}: Maybe<&2, List<&2, U32>>
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
  Spec.Node.get.at(
    s,
    k,
    m
  )
    == Trees.Tree.get.go(
      ~Spec.State(),
      ~Spec.Store.fetch,
      s,
      Trees.Tree.path(k),
      k,
      m
    ): Maybe<&2, List<&2, U32>>
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
        Trees.Tree.get.go(
          ~Spec.State(),
          ~Spec.Store.fetch,
          s,
          Trees.Tree.path(k),
          k,
          Some{Trees.Node.Empty{}}
        ),
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
) -> {
  Spec.Node.get(
    s,
    h,
    k
  )
    == Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, s, h, k): Maybe<&2, List<&2, U32>>
}:
  Get.at.is(s, k, Trees.Tree.part(~Spec.State(), ~Spec.Store.fetch, s, h))

# a look below no node lacks it
def Look.go.none(
  s: Spec.State(),
  p: List<&2, Nat>,
  k: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  Trees.Tree.look.go(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    p,
    k,
    h,
    None{}
  )
    == Trees.Look.missing(h): Trees.Look
}:
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
) -> {
  Trees.Tree.look.go(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    p,
    k,
    h,
    Some{Trees.Node.Empty{}}
  )
    == Trees.Look.Absent{}: Trees.Look
}:
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
) -> {
  Spec.Node.look.at(
    s,
    h,
    k,
    m
  )
    == Trees.Tree.look.go(
      ~Spec.State(),
      ~Spec.Store.fetch,
      s,
      Trees.Tree.path(k),
      k,
      h,
      m
    ): Trees.Look
}:
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
        Trees.Tree.look.go(
          ~Spec.State(),
          ~Spec.Store.fetch,
          s,
          Trees.Tree.path(k),
          k,
          h,
          Some{Trees.Node.Empty{}}
        ),
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
) -> {
  Spec.Node.look(s, h, k) == Trees.Tree.look(~Spec.State(), ~Spec.Store.fetch, s, h, k): Trees.Look
}:
  Look.at.is(s, h, k, Trees.Tree.part(~Spec.State(), ~Spec.Store.fetch, s, h))

# a write below no node gives nothing
def Set.go.none(
  s: Spec.State(),
  p: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  x: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  Trees.Tree.set.go(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    p,
    d,
    k,
    x,
    h,
    None{}
  )
    == None{}: Maybe<&2, Trees.Put>
}:
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
  Spec.Node.set.at(
    s,
    h,
    k,
    x,
    m
  )
    == Trees.Tree.set.go(
      ~Spec.State(),
      ~Spec.Store.fetch,
      s,
      Trees.Tree.path(k),
      0n,
      k,
      x,
      h,
      m
    ): Maybe<&2, Trees.Put>
}:
  match m:
    case None{}:
      Equal.sym(
        Maybe<&2, Trees.Put>,
        Trees.Tree.set.go(
          ~Spec.State(),
          ~Spec.Store.fetch,
          s,
          Trees.Tree.path(k),
          0n,
          k,
          x,
          h,
          None{}
        ),
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
) -> {
  Spec.Node.set(
    s,
    h,
    k,
    x
  )
    == Trees.Tree.set(~Spec.State(), ~Spec.Store.fetch, s, h, k, x): Maybe<&2, Trees.Put>
}:
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
) -> {
  State.after(s, m) == True{}: Bool
} -> {Work.after(s, Spec.Work.put(m, h, ws, ns)) == True{}: Bool}:
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
      Run.of.grows(s, c, Spec.Work.set(Spec.Work{s, l, ns}, k, x), Set.grows(s, l, ns, k, x))

# a run on a node that grew
def Run.put.grows(
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  t: Spec.Tip,
  ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Run.after(s, Spec.Run.put(m, t, ds, ns)) == True{}: Bool}:
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

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Spec.Made>
) -> {Run.after(Spec.Run.state(r), Spec.Branch.made(r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Made{+t, +ds}}:
      After.bind(
        Spec.Run.state(r),
        Spec.Run.content(r, Spec.Tip.content(Spec.Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Spec.Run,
          Spec.Run,
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{})
        ),
        Content.grows(r, Spec.Tip.content(Spec.Run.tip(r)), ds),
        +r1 => After.bind(
          Spec.Run.state(r1),
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{}),
          Add.grows(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Taken.grows(r2, i, None{})
        )
      )

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> {Run.after(Spec.Run.state(r), Spec.Branch.ready(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{False{}}:
      Stale.grows(r, i)
    case Some{True{}}:
      After.when(
        Spec.Run.state(r),
        Trees.Tree.whole(
          ~Spec.State(),
          ~Spec.Store.fetch,
          Spec.Run.state(r),
          Spec.Node.root_of(Spec.Run.state(r), at)
        ),
        Spec.Branch.made(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          )
        ),
        None{},
        Branch.made.grows(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          )
        ),
        {==}
      )

# a request for a branch only grows a run's node
def Branch.new.grows(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {Run.after(Spec.Run.state(r), Spec.Branch.new(r, i, st, b, at, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Some{x}}:
      Stale.grows(r, i)
    case Some{None{}}:
      Branch.ready.grows(r, i, st, b, at, Spec.Judge.ready_maybe(Spec.Run.state(r), at))

# a change of a line only grows a run's node
def On.grows(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Spec.Change
) -> {Run.after(Spec.Run.state(r), Spec.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  match l ch:
    case None{} Spec.Change.Branch{+a, b}:
      Branch.new.grows(
        r,
        i,
        st,
        a,
        b,
        Spec.Node.find(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), Spec.Log.start(a))
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
) -> {
  Run.after(Spec.Run.state(r), m) == True{}: Bool
} -> {
  Spec.Node.grows(
    Spec.Run.state(r),
    Spec.Run.state(Maybe.default(&2, Spec.Run, m, r))
  )
    == True{}: Bool
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
) -> {
  Run.after(Spec.Run.state(r), Some{Spec.Picked.run(Spec.Step.some(c, qs, r))}) == True{}: Bool
}:
  match qs:
    case Nil{}:
      After.self(r)
    case Con{+i, +rest}:
      +m = Spec.Step.one(r, c, i)
      +r2 = Maybe.default(&2, Spec.Run, m, r)
      %Equal.sym(
        Spec.Run,
        Spec.Picked.run(
          Spec.Picked.add(Maybe.is_some(&2, Spec.Run, m), i, Spec.Step.some(c, rest, r2))
        ),
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
    case Some{Spec.Run{s2, t2, ns}}:
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

# the run of the plan of an owner that proposes freely is on a node that grew
def Plan.own.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  t: Spec.Tip,
  -from: List<&2, String>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.own(s, c, t, from))) == True{}: Bool}:
  Some.grows(c, Spec.Cast.mine(s, Spec.Wait.of(s, c)), Spec.Run{s, t, []})

# the run of the plan for a step that another ballot names is on a node that
# grew
def Plan.copy.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  -from: List<&2, String>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.copy(s, c, t, th, m, from))) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Plan.when.grows(
        s,
        List.all.if(u => Spec.Cast.all_mine(s, qs), Spec.Root.same(before, th)),
        Spec.Plan{qs, Spec.Plan.fit(after, Spec.Step.run(s, c, t, qs)), from},
        Spec.Plan{[], None{}, []},
        Plan.fit.grows(s, after, Spec.Step.run(s, c, t, qs))(Run.grows(s, c, t, qs)),
        {==}
      )

# the run of the plan of the proposer of a later round is on a node that grew
def Plan.later.grows(
  s: Spec.State(),
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.later(s, c, w, t, th, os, from, m))) == True{}: Bool}:
  match m:
    case None{}:
      Plan.when.grows(
        s,
        Spec.Major(os, from),
        Spec.Plan.own(s, c, t, from),
        Spec.Plan{[], None{}, []},
        Plan.own.grows(s, c, t, from),
        {==}
      )
    case Some{Ledgers.Last{r, v}}:
      Plan.when.grows(
        s,
        Spec.Major(os, from),
        Spec.Plan.copy(s, c, t, th, Some{v}, from),
        Spec.Plan{[], None{}, []},
        Plan.copy.grows(s, c, t, th, Some{v}, from),
        {==}
      )

# the run of the plan of the proposer is on a node that grew
def Plan.lead.grows(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.lead(s, c, w, t, th, os))) == True{}: Bool}:
  Plan.when.grows(
    s,
    Nat.is_eq(Spec.Where.round(w), 0n),
    Spec.Plan.own(s, c, t, []),
    Spec.Plan.later(
      s,
      c,
      w,
      t,
      th,
      os,
      Spec.Passes.of(s, w, os),
      Spec.Passes.last(s, w, Spec.Passes.of(s, w, os))
    ),
    Plan.own.grows(s, c, t, []),
    Plan.later.grows(
      s,
      c,
      w,
      t,
      th,
      os,
      Spec.Passes.of(s, w, os),
      Spec.Passes.last(s, w, Spec.Passes.of(s, w, os))
    )
  )

# the run of the plan of another owner is on a node that grew
def Plan.follow.grows(
  +s: Spec.State(),
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.follow(s, c, w, t, th, os, m))) == True{}: Bool}:
  match m:
    case Some{Ledgers.Act.Vote{+v, from}}:
      Plan.when.grows(
        s,
        Spec.Allowed(s, w, os, v, from),
        Spec.Plan.copy(s, c, t, th, Some{v}, from),
        Spec.Plan{[], None{}, []},
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Spec.Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> {Run.after(s, Spec.Plan.run(Spec.Plan.of(n, s, c, w, t, th, os, turn))) == True{}: Bool}:
  match turn:
    case None{}:
      {==}
    case Some{+p}:
      Plan.when.grows(
        s,
        String.eq(p, n),
        Spec.Plan.lead(s, c, w, t, th, os),
        Spec.Plan.follow(s, c, w, t, th, os, Spec.Cast.act(s, w, p)),
        Plan.lead.grows(s, c, w, t, th, os),
        Plan.follow.grows(s, c, w, t, th, os, Spec.Cast.act(s, w, p))
      )

# a node with the ledger of a node that grew from a grew from a
def Grows.to(
  a: Spec.State(),
  b: Spec.State(),
  x: Spec.State(),
  e: {Spec.State.ledger(x) == Spec.State.ledger(b): Ledgers.State(Spec.Ask)},
  g: {Spec.Node.grows(a, b) == True{}: Bool}
) -> {Spec.Node.grows(a, x) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Spec.Ask),
    Spec.State.ledger(x),
    Spec.State.ledger(b),
    e
  ): {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(a), _) == True{}: Bool}
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
) -> {
  Spec.State.ledger(Spec.State.moved(s, c, h, qs)) == Spec.State.ledger(s): Ledgers.State(Spec.Ask)
}:
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
          Spec.Keys.saw(
            Spec.Keys.set(
              Spec.State.keys(s),
              Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
              Spec.Chained.next(c, b)
            ),
            Spec.Ballot.at(b)
          )
        ),
        Spec.Seal.fits(c, b),
        Grows.to(
          s,
          Spec.State.led(
            s,
            Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
          ),
          Spec.State.keyed(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            ),
            Spec.Keys.saw(
              Spec.Keys.set(
                Spec.State.keys(s),
                Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                Spec.Chained.next(c, b)
              ),
              Spec.Ballot.at(b)
            )
          ),
          Led.keyed(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            ),
            Spec.Keys.saw(
              Spec.Keys.set(
                Spec.State.keys(s),
                Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                Spec.Chained.next(c, b)
              ),
              Spec.Ballot.at(b)
            )
          ),
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
) -> {
  State.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Maybe.default(&2, Spec.State(), m, s)) == True{}: Bool}:
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
  a0: Ledgers.Act,
  m: Maybe<&2, Spec.Chained>
) -> {Spec.Node.grows(s, Spec.Cast.seal(s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Spec.Chained{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), U32.inc(j))
        )
      )
      Default.grows(
        s,
        Spec.Seal.accept(s, b)
      )(Accept.at.grows(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b))))

# a ballot on a node that grew from a, which grew from s, only grows s
def Cast.vote.grows(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +w: Ledgers.Where,
  +n: String,
  +a0: Ledgers.Act,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Cast.vote(s, m, w, n, a0)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +s4 = Spec.State.led(s, Spec.State.ledger(s3))
        Grows.trans(
          s,
          s4,
          Spec.Cast.seal(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n))
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(Cast.seal.grows(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n)))

# a vote only grows a node
def Cast.put.grows(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Spec.Run>,
  s: Spec.State()
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Cast.put(n, w, th, qs, from, m, s)) == True{}: Bool}:
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
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}, from},
        e
      )(Put.grows(s2, [Spec.Tip.words(t2)]))

# a pass only grows a node
def Pass.to.grows(
  +n: String,
  +s: Spec.State(),
  w: Ledgers.Where,
  os: List<&2, String>
) -> {Spec.Node.grows(s, Spec.Pass.to(n, s, w, os)) == True{}: Bool}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Grows.when(
        s,
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        Spec.Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Spec.Last.below(n, s, c, h, r)},
          Spec.Seal.chain(s, Spec.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.grows(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Spec.Last.below(n, s, c, h, r)},
          Spec.Seal.chain(s, Spec.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        Grows.refl(s)
      )

# a node that joins a round only grows a node
def Round.join.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {Spec.Node.grows(s, Spec.Round.join(n, s, c, h, os)) == True{}: Bool}:
  +top = Spec.Round.seen(s, c, h)
  k = top
  Grows.when(
    s,
    Nat.is_lt(Spec.Round.mine(n, s, c, h, k), top),
    Spec.Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.grows(n, s, Ledgers.Where{c, h, top}, os),
    Grows.refl(s)
  )

# a ballot in the node's round only grows a node
def Cast.round.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Spec.Tip
) -> {Spec.Node.grows(s, Spec.Cast.round(n, s, c, next, th, t)) == True{}: Bool}:
  +os = Spec.Line.owners(s, t)
  +r = Spec.Round.mine(n, s, c, next, Spec.Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Spec.Plan.of(n, s, c, w, t, th, os, Spec.Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Grows.when(
    s,
    Spec.Cast.may(n, s, w, t, Spec.Plan.asks(p)),
    Spec.Cast.put(n, w, th, Spec.Plan.asks(p), Spec.Plan.from(p), Spec.Plan.run(p), s),
    s,
    Cast.put.grows(
      n,
      w,
      th,
      Spec.Plan.asks(p),
      Spec.Plan.from(p),
      Spec.Plan.run(p),
      s
    )(Plan.of.grows(n, s, c, w, t, th, os, Spec.Owners.turn(os, U32.add(next, U32.from_nat(r))))),
    Grows.refl(s)
  )

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
      +s1 = Spec.Round.join(n, s, c, next, Spec.Line.owners(s, t))
      Grows.trans(
        s,
        s1,
        Spec.Cast.round(n, s1, c, next, th, t)
      )(
        Round.join.grows(n, s, c, next, Spec.Line.owners(s, t))
      )(Cast.round.grows(n, s1, c, next, th, t))
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, at the head h whose tip is m
def Pass.at.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.Node.grows(s, Spec.Pass.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Spec.Head{r, b, +next, th} Some{t}:
      Pass.to.grows(
        n,
        s,
        Ledgers.Where{c, next, 1n+Spec.Round.mine(n, s, c, next, Spec.Round.seen(s, c, next))},
        Spec.Line.owners(s, t)
      )
    case Spec.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, once the head m is known
def Pass.head.grows(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Pass.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Pass.at.grows(n, s, c, h, Spec.Head.tip(s, h))

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
) -> {
  State.after(a, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Advance.moved(s, m, c, h, qs)) == True{}: Bool}:
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
        Spec.Height.decide(
          s,
          c,
          Spec.Head.next(h),
          Spec.Line.owners(s, t),
          Spec.Round.seen(s, c, Spec.Head.next(h))
        )
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
        Grows.trans(
          s,
          s1,
          Spec.Advances.at(p, s1, c, m1)
        )(Advance.at.grows(s, c, h, Spec.Head.tip(s, h)))(Advances.at.grows(p, s1, c, m1))
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
  Grows.trans(
    s,
    s1,
    s3
  )(
    Advances.grows(4294967295n, s, c)
  )(Grows.trans(s1, s2, s3)(Cast.grows(n, s1, c))(Advances.grows(4294967295n, s2, c)))

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
  Grows.trans(
    s,
    s1,
    Spec.Step.head(n, s1, c)
  )(Open.at.grows(s, c, Spec.Node.head_of(s, c)))(Step.head.grows(n, s1, c))

# a pass to the next round only grows a node
def Pass.grows(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Node.pass(n, s, c)) == True{}: Bool}:
  +s1 = Spec.Pass.head(n, s, c, Spec.Node.head_of(s, c))
  Grows.trans(
    s,
    s1,
    Spec.Node.step(n, s1, c)
  )(Pass.head.grows(n, s, c, Spec.Node.head_of(s, c)))(Step.grows(n, s1, c))

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
) -> {
  State.after(a, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Start.head(s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Spec.State.led(s, Spec.State.ledger(s3))
        Grows.trans(
          s,
          x,
          Spec.State.first(x, c, h)
        )(
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
) -> {
  Work.after(s, m) == True{}: Bool
} -> {
  Work.after(
    s,
    Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Spec.Work.set(w, k, x))
  )
    == True{}: Bool
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
) -> {
  Work.after(s, Some{w}) == True{}: Bool
} -> {Work.after(s, Spec.Log.first(w, os)) == True{}: Bool}:
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
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Start.put(s, i, c, m)) == True{}: Bool}:
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
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Spec.Node.grows(s, Spec.Start.with(s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+w}:
      e => Start.put.grows(
        s,
        i,
        Spec.Work.root(w),
        Spec.Log.first(w, os)
      )(Log.first.after(s, w, os)(e))

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
  Grows.trans(
    s,
    s0,
    Spec.Node.step(n, s1, c)
  )(
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
  )(Grows.trans(s0, s1, Spec.Node.step(n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c)))

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
      Grows.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        Spec.Node.ask.new(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        )
      )(
        Grows.to(
          s,
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          Grows.refl(s)
        )
      )(
        Ask.new.grows(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        )
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
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Take.asks(cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(
        Spec.State(),
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Spec.Node.arrive(s, i, q),
        u => s
      )
      Grows.trans(
        s,
        s1,
        Spec.Take.asks(rest, old, s1)
      )(
        Grows.when(
          s,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
          ),
          Spec.Node.arrive(s, i, q),
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
  s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  k: Spec.State() -> Spec.State(),
  ih: @s2: Spec.State() -> {Spec.Node.grows(s2, k(s2)) == True{}: Bool}
) -> {
  State.after(s, m) == True{}: Bool
} -> {
  Spec.Node.grows(
    s,
    Maybe.default(
      &2,
      Spec.State(),
      Maybe.bind(&2, Spec.State(), Spec.State(), m, s2 => Some{k(s2)}),
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
      Grows.trans(
        s,
        s1,
        Spec.Sealed.each(f, rest, p, s1)
      )(
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
  +sent = Spec.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t),
    Ledgers.State.empty(~Spec.Ask)
  )
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  Grows.trans(
    s,
    s1,
    Spec.Sealed.take(bs, s2)
  )(
    Grows.led(
      s,
      l1,
      Ledgers.State.take_grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), Spec.State.ledger(s), sent)
    )
  )(
    Grows.trans(
      s1,
      s2,
      Spec.Sealed.take(bs, s2)
    )(
      Take.asks.grows(cs, Spec.State.ledger(s), s1)
    )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2))
  )

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  +s: Spec.State(),
  +t: Ledgers.State(Spec.Ask)
) -> {
  Spec.Node.grows(
    Spec.State.led(
      s,
      Ledgers.State.take(
        ~Spec.Ask,
        Spec.State.ledger(s),
        Spec.Take.clean(
          Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t),
          Ledgers.State.empty(~Spec.Ask)
        )
      )
    ),
    Spec.Node.take(s, t)
  )
    == True{}: Bool
}:
  +sent = Spec.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t),
    Ledgers.State.empty(~Spec.Ask)
  )
  l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  Grows.trans(
    s1,
    s2,
    Spec.Sealed.take(bs, s2)
  )(
    Take.asks.grows(cs, Spec.State.ledger(s), s1)
  )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2))

# Node.fetch for the data ws itself
def Fetch.take(
  +b: Spec.State(),
  +ws: List<&2, U32>
) -> {
  Ledgers.State.get(
    ~Spec.Ask,
    Spec.State.ledger(b),
    Ledgers.Slot.data(Hashes.Sha.hash(ws))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
} -> {
  Ledgers.State.data(
    ~Spec.Ask,
    Spec.State.ledger(
      Spec.Node.take(
        b,
        Ledgers.State.put_data(~Spec.Ask, ~Spec.Ask.is_eq, Ledgers.State.empty(~Spec.Ask), ws)
      )
    ),
    Hashes.Sha.hash(ws)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  +t = Ledgers.State.put_data(~Spec.Ask, ~Spec.Ask.is_eq, Ledgers.State.empty(~Spec.Ask), ws)
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(b), t)
  e =>
    Ledgers.State.data_grows(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      Spec.State.ledger(Spec.State.led(b, l1)),
      Spec.State.ledger(Spec.Node.take(b, t)),
      Hashes.Sha.hash(ws),
      ws
    )(Take.tail(b, t))(
      %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(Spec.State.led(b, l1)), l1, Led.led(b, l1)): {Ledgers.State.data(~Spec.Ask, _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
      Ledgers.State.take_data(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(b), ws)(e))

def Spec.Node.fetch(a, b, h, ws):
  +ea => eb =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Ledgers.State.data(~Spec.Ask, Spec.State.ledger(a), h),
      Some{ws},
      ea
    ): {
      Ledgers.State.data(
        ~Spec.Ask,
        Spec.State.ledger(Spec.Node.take(b, Spec.Serve.put(_, Ledgers.State.empty(~Spec.Ask)))),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Ledgers.State.data_hash(
      ~Spec.Ask,
      Spec.State.ledger(a),
      h,
      ws
    )(
      ea
    ): {
      Ledgers.State.data(
        ~Spec.Ask,
        Spec.State.ledger(
          Spec.Node.take(
            b,
            Ledgers.State.put_data(~Spec.Ask, ~Spec.Ask.is_eq, Ledgers.State.empty(~Spec.Ask), ws)
          )
        ),
        _
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    Fetch.take(b, ws)(
      %Equal.sym(Hashes.Hash, Hashes.Sha.hash(ws), h, Ledgers.State.data_hash(~Spec.Ask, Spec.State.ledger(a), h, ws)(ea)): {Ledgers.State.get(~Spec.Ask, Spec.State.ledger(b), Ledgers.Slot.data(_)) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
      eb)

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
      Grows.trans(
        s,
        s1,
        Spec.Node.steps(n, rest, s1)
      )(Step.grows(n, s, c))(Steps.grows(n, rest, s1))

# an adoption only grows a node, once the request m is known
def Adopt.ask.grows(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Spec.Request>
) -> {Spec.Node.grows(s, Spec.Adopt.ask(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Spec.Request{e, q}}:
      Spec.Node.ask_grows(n, s, e, q)

# an adoption only grows a node, once the head m of the line is known
def Adopt.head.grows(
  n: String,
  +s: Spec.State(),
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.grows(s, Spec.Adopt.head(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Spec.Head{r, b, next, t}}:
      Adopt.ask.grows(n, s, Spec.Node.adoption(s, r, b))

# the adoption of a line only grows a node
def Adopt.at.grows(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain
) -> {Spec.Node.grows(s, Spec.Adopt.at(n, s, c)) == True{}: Bool}:
  Adopt.head.grows(n, s, Spec.Node.head_of(s, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Ledgers.Chain>
) -> {Spec.Node.grows(s, Spec.Adopt.maybe(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{c}:
      Adopt.at.grows(n, s, c)

# the adoption of each of some lines only grows a node
def Adopts.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Node.adopts(n, cs, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{+c, +rest}:
      Grows.trans(
        s,
        Spec.Adopt.at(n, s, c),
        Spec.Node.adopts(n, rest, Spec.Adopt.at(n, s, c))
      )(Adopt.at.grows(n, s, c))(Adopts.grows(n, rest, Spec.Adopt.at(n, s, c)))

# more rounds of a sync, grows
def More.grows(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +bs: List<&2, Ledgers.Ballot>,
  +s: Spec.State()
) -> {Spec.Node.grows(s, Spec.Sync.more(f, n, cs, bs, s)) == True{}: Bool}:
  match f:
    case 0n:
      Grows.refl(s)
    case 1n+(+p):
      Grows.when(s, Spec.Lines.level(cs, s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Grows.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)))(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s))(Steps.grows(n, cs, Spec.Sealed.take(bs, s))), Grows.trans(s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))))(Grows.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)))(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s))(Steps.grows(n, cs, Spec.Sealed.take(bs, s))))(More.grows(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)))))

def Spec.Node.sync_grows(n, s, t):
  +s1 = Spec.Node.take(s, t)
  +cs = Spec.Sync.lines(s, s1, t)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  +s2 = Spec.Node.steps(n, cs, s1)
  +s3 = Spec.Sync.more(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2)
  Grows.trans(s, s1, Spec.Node.adopts(n, cs, s3))(Spec.Node.take_grows(s, t))(Grows.trans(s1, s2, Spec.Node.adopts(n, cs, s3))(Steps.grows(n, cs, s1))(Grows.trans(s2, s3, Spec.Node.adopts(n, cs, s3))(More.grows(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2))(Adopts.grows(n, cs, s3))))

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
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)
      ),
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
  +em: {
    Ledgers.State.get(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(
      ~Spec.Ask,
      Spec.State.ledger(Spec.Node.ask.new(n, s, e, q)),
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )
  )
    == True{}: Bool
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
    Grows.trans(s0, s1, Spec.Node.step(n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c))
  )(
    %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(s0), l0, Led.led(s, l0)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, _, k)) == True{}: Bool}
    %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, Ledgers.State.get(~Spec.Ask, l0, k), Some{Cells.One{en}}, Ledgers.State.put_get(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), k, en)(em)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
    {==})

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  em: {
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
      Ask.held.new(
        n,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        e,
        q,
        (
          %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))), Spec.State.ledger(s), Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))): {Ledgers.State.get(~Spec.Ask, _, Ledgers.Slot.ask(Spec.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
          em)
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
      %Equal.sym(Ledgers.Id, Spec.Envelope.of(e2), Spec.Envelope.of(e), h): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, Ledgers.State.get(~Spec.Ask, Spec.State.ledger(a), Ledgers.Slot.ask(_))) == True{}: Bool}
      Ask.held.at(n, s, e, q, Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e))), {==}))

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
    )(
      g
    )(
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
) -> Spec.Work.Reads(
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
            )(
              Grows.keep(s, ws)
            )(
              hne
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
) -> Spec.Work.Reads(k2, v, Spec.Work.of(s, ns, m)):
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
) -> Spec.Work.Reads(k2, v, Spec.Work.set(Spec.Work{s, h, ns}, k, x)):
  Set.kept.of(s, h, ns, k, x, k2, v, Spec.Node.set(s, h, k, x), {==}, hne, hget)

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
) -> Spec.Work.Reads(k2, v, m) -> Run.Keeps(k2, v, Spec.Run.of(c, m)):
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
              %Equal.sym(List<&2, U32>, k, k2, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)): {Spec.Node.get(s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2)
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
    Keys.differ.if(s, l, k, k2, v, Shared.List.is_eq(~U32, ~U32.is_eq, k, k2), {==}, em, hr)
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
) -> (
  @r: Spec.Run -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, f(r))
) -> Run.Keeps(k2, v, Maybe.bind(&2, Spec.Run, Spec.Run, m, f)):
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
) -> Run.Keeps(
  k2,
  v,
  Some{r}
) -> Run.Keeps(k2, v, Shared.Bool.when(Maybe<&2, Spec.Run>, b, u => mx, u => my)):
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

# the first tip of a new branch keeps each key of a run's log, other than the
# owners and the count
def Branch.made.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Spec.Made>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Branch.made(r, i, b, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Spec.Made{+t, +ds}}:
      hr => Keeps.bind(
        k2,
        v,
        Spec.Run.content(r, Spec.Tip.content(Spec.Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Spec.Run,
          Spec.Run,
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{})
        )
      )(
        Content.kept(r, Spec.Tip.content(Spec.Run.tip(r)), ds, k2, v)(hr)
      )(
        +r1 => h1 => Keeps.bind(
          k2,
          v,
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{})
        )(
          Add.kept(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), []), k2, v)(h1)
        )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v, n0, n1)(h2))
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count, once it is known whether its version is one
def Branch.ready.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Branch.ready(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{False{}}:
      Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)
    case Some{True{}}:
      Keeps.when(
        k2,
        v,
        r,
        Trees.Tree.whole(
          ~Spec.State(),
          ~Spec.Store.fetch,
          Spec.Run.state(r),
          Spec.Node.root_of(Spec.Run.state(r), at)
        ),
        Spec.Branch.made(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          )
        ),
        None{},
        Branch.made.kept(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          ),
          k2,
          v,
          n0,
          n1
        ),
        hr => Unit{}
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count
def Branch.new.kept(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Spec.Branch.new(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Some{x}}:
      Add.kept(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}), k2, v)
    case Some{None{}}:
      Branch.ready.kept(
        r,
        i,
        st,
        b,
        at,
        Spec.Judge.ready_maybe(Spec.Run.state(r), at),
        k2,
        v,
        n0,
        n1
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
    case None{} Spec.Change.Branch{+a, b}:
      Branch.new.kept(
        r,
        i,
        st,
        a,
        b,
        Spec.Node.find(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), Spec.Log.start(a)),
        k2,
        v,
        n0,
        n1
      )
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
) -> {
  Spec.Tip.at(a, x) == Some{t}: Maybe<&2, Spec.Tip>
} -> {Spec.Tip.at(b, x) == Some{t}: Maybe<&2, Spec.Tip>}:
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
) -> {
  Spec.Head.tip(a, h) == Some{t}: Maybe<&2, Spec.Tip>
} -> {Spec.Head.tip(b, h) == Some{t}: Maybe<&2, Spec.Tip>}:
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
) -> {
  Spec.Head.get(a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Head.get(b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
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
) -> {
  Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Line.get(b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
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
  Spec.Node.head_of(
    Spec.State.head(b0, c, hd),
    c2
  )
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
) -> {
  Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Spec.Head,
    List<&2, U32>,
    m,
    h => Spec.Head.get(a, h, k)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {
      Maybe.bind(
        &2,
        Spec.Head,
        List<&2, U32>,
        _,
        h => Spec.Head.get(a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
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
  cov: {
    Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Spec.Head.get(Spec.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Spec.Line.get(a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Line.get(Spec.State.head(b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
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
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool
  } -> {
    Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Spec.Head.get(Spec.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
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
) -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(Shared.Bool.when(Spec.State(), b, u => x, u => y)): Tries.Trie<Spec.Head>
}:
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
) -> {
  Spec.State.heads(
    s
  )
    == Heads.of(s, Shared.Maybe.when(Spec.State(), b, u => Some{x})): Tries.Trie<Spec.Head>
}:
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
          Spec.Keys.saw(
            Spec.Keys.set(
              Spec.State.keys(s),
              Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
              Spec.Chained.next(c, b)
            ),
            Spec.Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<Spec.Head>,
          Spec.State.heads(s),
          Spec.State.heads(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            )
          ),
          Spec.State.heads(
            Spec.State.keyed(
              Spec.State.led(
                s,
                Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
              ),
              Spec.Keys.saw(
                Spec.Keys.set(
                  Spec.State.keys(s),
                  Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                  Spec.Chained.next(c, b)
                ),
                Spec.Ballot.at(b)
              )
            )
          ),
          Heads.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)),
          Heads.keyed(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            ),
            Spec.Keys.saw(
              Spec.Keys.set(
                Spec.State.keys(s),
                Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                Spec.Chained.next(c, b)
              ),
              Spec.Ballot.at(b)
            )
          )
        )
      )

# the node m, if any, else s, has the heads of s when m has
def Default.heads(
  -s: Spec.State(),
  m: Maybe<&2, Spec.State()>
) -> {
  Spec.State.heads(s) == Heads.of(s, m): Tries.Trie<Spec.Head>
} -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(Maybe.default(&2, Spec.State(), m, s)): Tries.Trie<Spec.Head>
}:
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
  a0: Ledgers.Act,
  m: Maybe<&2, Spec.Chained>
) -> {
  Spec.State.heads(s) == Spec.State.heads(Spec.Cast.seal(s, w, n, a0, m)): Tries.Trie<Spec.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Chained{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Spec.Seal.secret(Spec.Keys.seed(Spec.State.keys(s)), Spec.Where.store(w), U32.inc(j))
        )
      )
      Default.heads(
        s,
        Spec.Seal.accept(s, b)
      )(Accept.at.heads(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b))))

# a ballot keeps the heads
def Cast.vote.heads(
  +s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  Spec.State.heads(s) == Spec.State.heads(Spec.Cast.vote(s, m, w, n, a0)): Tries.Trie<Spec.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = Spec.State.led(s, Spec.State.ledger(s3))
      Equal.trans(
        Tries.Trie<Spec.Head>,
        Spec.State.heads(s),
        Spec.State.heads(s4),
        Spec.State.heads(Spec.Cast.seal(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n))),
        Heads.led(s, Spec.State.ledger(s3)),
        Cast.seal.heads(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  -s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  -k: Spec.State() -> Spec.State(),
  ih: @s2: Spec.State() -> {Spec.State.heads(s2) == Spec.State.heads(k(s2)): Tries.Trie<Spec.Head>}
) -> {
  Spec.State.heads(s) == Heads.of(s, m): Tries.Trie<Spec.Head>
} -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(
      Maybe.default(
        &2,
        Spec.State(),
        Maybe.bind(&2, Spec.State(), Spec.State(), m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<Spec.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<Spec.Head>,
        Spec.State.heads(s),
        Spec.State.heads(s2),
        Spec.State.heads(k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  f: Nat,
  +s: Spec.State(),
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(Spec.Sealed.follow(f, s, p, r, n, mb)): Tries.Trie<Spec.Head>
}:
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
) -> {
  Spec.State.heads(s) == Spec.State.heads(Spec.Sealed.each(f, bs, p, s)): Tries.Trie<Spec.Head>
}:
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

# a vote keeps the heads
def Cast.put.heads(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Spec.Run>,
  s: Spec.State()
) -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(Spec.Cast.put(n, w, th, qs, from, m, s)): Tries.Trie<Spec.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Run{s2, +t2, ns}}:
      Cast.vote.heads(
        s,
        Spec.State.put(s2, [Spec.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  +n: String,
  +s: Spec.State(),
  w: Ledgers.Where,
  os: List<&2, String>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Pass.to(n, s, w, os)): Tries.Trie<Spec.Head>}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        s,
        Spec.Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Spec.Last.below(n, s, c, h, r)},
          Spec.Seal.chain(s, Spec.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.heads(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Spec.Last.below(n, s, c, h, r)},
          Spec.Seal.chain(s, Spec.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        {==}
      )

# a node that joins a round keeps the heads
def Round.join.heads(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  Spec.State.heads(s) == Spec.State.heads(Spec.Round.join(n, s, c, h, os)): Tries.Trie<Spec.Head>
}:
  +top = Spec.Round.seen(s, c, h)
  k = top
  Heads.when(
    Nat.is_lt(Spec.Round.mine(n, s, c, h, k), top),
    s,
    Spec.Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.heads(n, s, Ledgers.Where{c, h, top}, os),
    {==}
  )

# a ballot in the node's round keeps the heads
def Cast.round.heads(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Spec.Tip
) -> {
  Spec.State.heads(
    s
  )
    == Spec.State.heads(Spec.Cast.round(n, s, c, next, th, t)): Tries.Trie<Spec.Head>
}:
  +os = Spec.Line.owners(s, t)
  +r = Spec.Round.mine(n, s, c, next, Spec.Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Spec.Plan.of(n, s, c, w, t, th, os, Spec.Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Heads.when(
    Spec.Cast.may(n, s, w, t, Spec.Plan.asks(p)),
    s,
    Spec.Cast.put(n, w, th, Spec.Plan.asks(p), Spec.Plan.from(p), Spec.Plan.run(p), s),
    s,
    Cast.put.heads(n, w, th, Spec.Plan.asks(p), Spec.Plan.from(p), Spec.Plan.run(p), s),
    {==}
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
    case Spec.Head{r, b, +next, th} Some{+t}:
      s1 = Spec.Round.join(n, s, c, next, Spec.Line.owners(s, t))
      Equal.trans(
        Tries.Trie<Spec.Head>,
        Spec.State.heads(s),
        Spec.State.heads(s1),
        Spec.State.heads(Spec.Cast.round(n, s1, c, next, th, t)),
        Round.join.heads(n, s, c, next, Spec.Line.owners(s, t)),
        Cast.round.heads(n, s1, c, next, th, t)
      )
    case Spec.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Pass.at(n, s, c, h, m)): Tries.Trie<Spec.Head>}:
  match h m:
    case Spec.Head{r, b, +next, th} Some{t}:
      Pass.to.heads(
        n,
        s,
        Ledgers.Where{c, next, 1n+Spec.Round.mine(n, s, c, next, Spec.Round.seen(s, c, next))},
        Spec.Line.owners(s, t)
      )
    case Spec.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.State.heads(s) == Spec.State.heads(Spec.Pass.head(n, s, c, m)): Tries.Trie<Spec.Head>}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(n, s, c, h, Spec.Head.tip(s, h))

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
def Cast.kept(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Node.cast(n, s, c)):
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
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          x => y => Spec.Tip{x, y},
          Codes.Codec.enc(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          )(
            c
          )(
            Codes.Codec.enc(
              Maybe<&2, Hashes.Hash>,
              Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
            )(l)([])
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
  Shared.Maybe.when(
    Spec.State(),
    b,
    u => Some{Spec.State.keep(s2, ds)}
  )
    == Some{s3}: Maybe<&2, Spec.State()>
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.State(), s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Spec.State(),
          Spec.State.keep(s2, ds),
          s3,
          e
        ): {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  s2: Spec.State(),
  +ds: List<&2, List<&2, U32>>,
  -s3: Spec.State()
) -> {
  Spec.State.put(s2, ds) == Some{s3}: Maybe<&2, Spec.State()>
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool}:
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
) -> {
  Spec.State.put(s2, [Spec.Tip.words(t2)]) == Some{s3}: Maybe<&2, Spec.State()>
} -> {Spec.Tip.at(s3, Spec.Tip.hash(t2)) == Some{t2}: Maybe<&2, Spec.Tip>}:
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
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Spec.Tip,
        _,
        ws => Spec.Tip.read(ws)
      )
        == Some{t2}: Maybe<&2, Spec.Tip>
    }
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
) -> {
  Spec.Line.get(s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Spec.Tip,
        List<&2, U32>,
        _,
        t1 => Spec.Node.get(s, Spec.Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
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
) -> {
  Spec.Head.get(
    b,
    Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}},
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Spec.Tip>,
    Spec.Tip.at(b, Spec.Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(s3, b, Spec.Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Spec.Tip,
      List<&2, U32>,
      _,
      t1 => Spec.Node.get(b, Spec.Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
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
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool
  } -> {
    Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Spec.Node.get(s3, Spec.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(
  s,
  Spec.State.moved(
    Spec.State.led(s, Spec.State.ledger(s3)),
    c,
    Spec.Head{r, br, nx, Some{Spec.Tip.hash(t2)}},
    qs
  )
):
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
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool
  } -> {
    Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Spec.Node.get(s2, Spec.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Spec.State.put(s2, [Spec.Tip.words(t2)]) == m: Maybe<&2, Spec.State()>
} -> Spec.Node.Keeps(
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
) -> {
  Run.after(s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Log.count(), k) == False{}: Bool
  } -> {
    Spec.Node.get(s, Spec.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> Run.Keeps(k, v, m)
) -> Spec.Node.Keeps(s, Spec.Advance.ran(s, c, r, br, next, after, qs, m)):
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
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> {
  Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>
} -> Spec.Node.Keeps(s, Spec.Advance.step(s, c, h, t, m)):
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
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> {
  Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>
} -> Spec.Node.Keeps(s, Spec.Advance.at(s, c, h, m)):
  match m:
    case None{}:
      em => et => Kept.refl(s)
    case Some{+t}:
      em => et => Advance.step.kept(
        s,
        c,
        h,
        t,
        Spec.Height.decide(
          s,
          c,
          Spec.Head.next(h),
          Spec.Line.owners(s, t),
          Spec.Round.seen(s, c, Spec.Head.next(h))
        )
      )(em)(et)

# Advances.kept once the head m is known
def Advances.at.kept(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {
  Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.Keeps(s, Spec.Advances.at(f, s, c, m)):
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
def Advances.kept(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Node.advances(f, s, c)):
  Advances.at.kept(f, s, c, Spec.Node.head_of(s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Step.head(n, s, c)):
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
) -> {
  Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
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
) -> {
  Spec.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Spec.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
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
) -> {
  Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.Keeps(s, Spec.Open.at(s, c, m)):
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
          k => v => n0 => n1 => Cover.wait(
            s,
            c,
            Spec.State.head(s, c, hd),
            hd,
            k,
            v,
            r,
            Some{b},
            n,
            em
          )
        )
    case Some{Spec.Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Spec.Head{r, None{}, n, t}}:
      em => Kept.refl(s)
    case None{}:
      em => Kept.refl(s)

# what a node does on a line keeps the logs
def Step.kept(
  n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Node.step(n, s, c)):
  s1 = Spec.Node.open(s, c)
  Kept.trans(
    s,
    s1,
    Spec.Step.head(n, s1, c),
    Open.at.kept(s, c, Spec.Node.head_of(s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Node.pass(n, s, c)):
  +s1 = Spec.Pass.head(n, s, c, Spec.Node.head_of(s, c))
  Kept.trans(
    s,
    s1,
    Spec.Node.step(n, s1, c),
    Kept.same(
      s,
      s1,
      Pass.head.grows(n, s, c, Spec.Node.head_of(s, c)),
      Pass.head.heads(n, s, c, Spec.Node.head_of(s, c))
    ),
    Step.kept(n, s1, c)
  )

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  +s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Head>
) -> {
  Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.Keeps(s, Spec.First.at(s, c, h, m)):
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
      e => Start.put.kept(
        s,
        i,
        Spec.Work.root(w),
        Spec.Log.first(w, os)
      )(Log.first.after(s, w, os)(e))

# a store that starts keeps the logs
def Start.kept(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, Spec.Owner>
) -> Spec.Node.Keeps(s, Spec.Node.start(s, i, os)):
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
) -> {
  Spec.Node.head_of(s, Spec.Line.chain(r, l)) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.Keeps(s, Spec.Follow.new(s, r, l, m)):
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
def Arrive.kept(
  +s: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> Spec.Node.Keeps(s, Spec.Node.arrive(s, i, q)):
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
def Ask.new.kept(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask
) -> Spec.Node.Keeps(s, Spec.Node.ask.new(n, s, e, q)):
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
  q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> Spec.Node.Keeps(s, Spec.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(s)
    case None{}:
      Kept.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        Spec.Node.ask.new(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        ),
        Kept.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          Grows.to(
            s,
            s,
            Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
            Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
            Grows.refl(s)
          ),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))
        ),
        Ask.new.kept(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask keeps the logs
def Ask.kept(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  q: Spec.Ask
) -> Spec.Node.Keeps(s, Spec.Node.ask(n, s, e, q)):
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
      s1 = Shared.Bool.when(
        Spec.State(),
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Spec.Node.arrive(s, i, q),
        u => s
      )
      Kept.trans(
        s,
        s1,
        Spec.Take.asks(rest, old, s1),
        Kept.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Spec.Node.arrive(s, i, q),
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
  +s: Spec.State(),
  +t: Ledgers.State(Spec.Ask)
) -> Spec.Node.Keeps(s, Spec.Node.take(s, t)):
  +sent = Spec.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t),
    Ledgers.State.empty(~Spec.Ask)
  )
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
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
        Ledgers.State.take_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          Spec.State.ledger(s),
          sent
        )
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
def Steps.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> Spec.Node.Keeps(s, Spec.Node.steps(n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      s1 = Spec.Node.step(n, s, c)
      Kept.trans(s, s1, Spec.Node.steps(n, rest, s1), Step.kept(n, s, c), Steps.kept(n, rest, s1))

# an adoption keeps the logs, once the request m is known
def Adopt.ask.kept(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Spec.Request>
) -> Spec.Node.Keeps(s, Spec.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Spec.Request{e, q}}:
      Ask.kept(n, s, e, q)

# an adoption keeps the logs, once the head m of the line is known
def Adopt.head.kept(
  n: String,
  +s: Spec.State(),
  m: Maybe<&2, Spec.Head>
) -> Spec.Node.Keeps(s, Spec.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Spec.Head{r, b, next, t}}:
      Adopt.ask.kept(n, s, Spec.Node.adoption(s, r, b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Spec.Adopt.at(n, s, c)):
  Adopt.head.kept(n, s, Spec.Node.head_of(s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Spec.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Adopt.at.kept(n, s, c)

# the adoption of each of some lines keeps the logs
def Adopts.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> Spec.Node.Keeps(s, Spec.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      Kept.trans(
        s,
        Spec.Adopt.at(n, s, c),
        Spec.Node.adopts(n, rest, Spec.Adopt.at(n, s, c)),
        Adopt.at.kept(n, s, c),
        Adopts.kept(n, rest, Spec.Adopt.at(n, s, c))
      )

# more rounds of a sync, kept
def More.kept(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +bs: List<&2, Ledgers.Ballot>,
  +s: Spec.State()
) -> Spec.Node.Keeps(s, Spec.Sync.more(f, n, cs, bs, s)):
  match f:
    case 0n:
      Kept.refl(s)
    case 1n+(+p):
      Kept.when(Spec.Lines.level(cs, s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Kept.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Kept.same(s, Spec.Sealed.take(bs, s), Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s), Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s)), Steps.kept(n, cs, Spec.Sealed.take(bs, s))), Kept.trans(s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Kept.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Kept.same(s, Spec.Sealed.take(bs, s), Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s), Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s)), Steps.kept(n, cs, Spec.Sealed.take(bs, s))), More.kept(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)))))

# a sync keeps the logs
def Sync.kept(
  +n: String,
  +s: Spec.State(),
  +t: Ledgers.State(Spec.Ask)
) -> Spec.Node.Keeps(s, Spec.Node.sync(n, s, t)):
  +s1 = Spec.Node.take(s, t)
  +cs = Spec.Sync.lines(s, s1, t)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  +s2 = Spec.Node.steps(n, cs, s1)
  +s3 = Spec.Sync.more(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2)
  Kept.trans(s, s1, Spec.Node.adopts(n, cs, s3), Take.kept(s, t), Kept.trans(s1, s2, Spec.Node.adopts(n, cs, s3), Steps.kept(n, cs, s1), Kept.trans(s2, s3, Spec.Node.adopts(n, cs, s3), More.kept(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2), Adopts.kept(n, cs, s3))))

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
      Grows.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
        Spec.Node.step(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c)
      )(
        Grows.to(
          s,
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
          Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
          Grows.refl(s)
        )
      )(Step.grows(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c))

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  n: String,
  +s: Spec.State(),
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Spec.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Kept.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
        Spec.Node.step(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c),
        Kept.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
          Grows.to(
            s,
            s,
            Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
            Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
            Grows.refl(s)
          ),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i))
        ),
        Step.kept(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  +n: String,
  +s: Spec.State(),
  ev: Spec.Deed
) -> {Spec.Node.grows(s, Spec.Node.does(n, s, ev)) == True{}: Bool}:
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Grows.trans(
        s,
        Spec.Node.ask(n, s, e, q),
        Spec.Adopt.at(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q))
      )(
        Spec.Node.ask_grows(n, s, e, q)
      )(Adopt.at.grows(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q)))
    case Spec.Deed.Take{t}:
      Spec.Node.take_grows(s, t)
    case Spec.Deed.Sync{t}:
      Spec.Node.sync_grows(n, s, t)
    case Spec.Deed.Keep{b}:
      Grows.keep(s, Ropes.Put.nodes(Spec.Bytes.rope(b)))
    case Spec.Deed.Consent{+i}:
      Grows.trans(
        s,
        Spec.Node.consent(n, s, i),
        Spec.Adopt.maybe(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i))
      )(
        Consent.grows(n, s, i, Spec.Node.chain_of(s, i))
      )(Adopt.maybe.grows(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i)))
    case Spec.Deed.Pass{+c}:
      Grows.trans(
        s,
        Spec.Node.pass(n, s, c),
        Spec.Adopt.at(n, Spec.Node.pass(n, s, c), c)
      )(Pass.grows(n, s, c))(Adopt.at.grows(n, Spec.Node.pass(n, s, c), c))

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
  +s: Spec.State(),
  ev: Spec.Deed
) -> Spec.Node.Keeps(s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Kept.trans(
        s,
        Spec.Node.ask(n, s, e, q),
        Spec.Adopt.at(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q)),
        Ask.kept(n, s, e, q),
        Adopt.at.kept(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q))
      )
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
      Kept.trans(
        s,
        Spec.Node.consent(n, s, i),
        Spec.Adopt.maybe(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i)),
        Consent.kept(n, s, i, Spec.Node.chain_of(s, i)),
        Adopt.maybe.kept(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i))
      )
    case Spec.Deed.Pass{+c}:
      Kept.trans(
        s,
        Spec.Node.pass(n, s, c),
        Spec.Adopt.at(n, Spec.Node.pass(n, s, c), c),
        Pass.kept(n, s, c),
        Adopt.at.kept(n, Spec.Node.pass(n, s, c), c)
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
) -> {
  Spec.Chain.out(a, c, i) == Some{o}: Maybe<&2, Spec.Out>
} -> {Spec.Chain.out(b, c, i) == Some{o}: Maybe<&2, Spec.Out>}:
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
) -> {
  Spec.Chain.version(a, c, n) == Some{x}: Maybe<&2, Spec.Version>
} -> {Spec.Chain.version(b, c, n) == Some{x}: Maybe<&2, Spec.Version>}:
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
) -> {
  Spec.Chain.mark(a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Spec.Chain.mark(b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
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
) -> {
  Spec.Node.chain_of(a, i) == Some{c}: Maybe<&2, Ledgers.Chain>
} -> {Spec.Node.chain_of(b, i) == Some{c}: Maybe<&2, Ledgers.Chain>}:
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
) -> {
  Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
} -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}:
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
) -> {
  Spec.Out.on(a, c, o) == Some{x}: Maybe<&2, Spec.Version>
} -> {Spec.Out.on(b, c, o) == Some{x}: Maybe<&2, Spec.Version>}:
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
) -> {
  Spec.Chain.made(a, c, v) == Some{x}: Maybe<&2, Spec.Version>
} -> {Spec.Chain.made(b, c, v) == Some{x}: Maybe<&2, Spec.Version>}:
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
) -> {
  Spec.Node.made(a, v) == Some{x}: Maybe<&2, Spec.Version>
} -> {Spec.Node.made(b, v) == Some{x}: Maybe<&2, Spec.Version>}:
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

def Spec.Chain.start_final(n, evs, s, r, b, v):
  Spec.Node.after_keeps(n, evs, s)(Ledgers.Chain{r, None{}})(Spec.Log.start(b))(v)({==})({==})

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
) -> {
  Spec.Answer.follows(Spec.Answer.taken(a, i, q), Some{Spec.Answer.taken(b, i, q)}) == True{}: Bool
}:
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
) -> {
  Spec.Node.out(a, i) == oa: Maybe<&2, Spec.Out>
} -> (
  @o: Spec.Out -> {
    Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
  } -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}
) -> {
  Spec.Answer.follows(
    Spec.Answer.of(a, i, q, Spec.Node.out(a, i)),
    Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(
          Maybe<&2, Spec.Out>,
          Spec.Node.out(a, i),
          None{},
          eo
        ): {
          Spec.Answer.follows(
            Spec.Answer.of(a, i, q, _),
            Some{Spec.Answer.of(b, i, q, Spec.Node.out(b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Spec.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Spec.Out>,
          Spec.Node.out(a, i),
          Some{Spec.Out.Stale{}},
          eo
        ): {
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
        %Equal.sym(
          Maybe<&2, Spec.Out>,
          Spec.Node.out(a, i),
          Some{Spec.Out.Taken{k}},
          eo
        ): {
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
  ho: @o: Spec.Out -> {
    Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
  } -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}
) -> {
  Spec.Answer.follows(Spec.Answer.asked(a, i, q), Some{Spec.Answer.asked(b, i, q)}) == True{}: Bool
}:
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
  ho: @o: Spec.Out -> {
    Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
  } -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}
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
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    Some{c},
    mb
  )
    == True{}: Bool
} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}:
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
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )

# Node.answer_follows once the cell ma of the request's ID is known
def Answer.follows.at(
  a: Spec.State(),
  b: Spec.State(),
  i: Ledgers.Id,
  q: Spec.Ask,
  -x: Spec.Answer,
  ma: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  ho: @o: Spec.Out -> {
    Spec.Node.out(a, i) == Some{o}: Maybe<&2, Spec.Out>
  } -> {Spec.Node.out(b, i) == Some{o}: Maybe<&2, Spec.Out>}
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    ma,
    mb
  )
    == True{}: Bool
} -> {
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
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          mb,
          Some{c},
          Cell.kept.eq(c, mb)(ek)
        ): {Spec.Answer.follows(x, Spec.Answer.held(b, i, q, _)) == True{}: Bool}
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
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)
      ),
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
) -> {
  Maybe.is_some(
    &2,
    Spec.Draft,
    Shared.Bool.when(Maybe<&2, Spec.Draft>, b, u => x, u => y)
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
  -found: Maybe<&2, Spec.Draft>,
  -k: List<&2, Bool>,
  m: Maybe<&2, Spec.Content>
) -> {
  Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.with(found, k, m)) == True{}: Bool}:
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
) -> {
  Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, i, a, found)) == True{}: Bool}:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      +h => When.some(
        String.eq(w2, w),
        Spec.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Spec.Draft.content(r, b, n, q)
        ),
        found,
        Draft.with.some(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Spec.Draft.content(r, b, n, q)
        )(h),
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
) -> {
  Maybe.is_some(&2, Spec.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Draft, Spec.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool}:
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
) -> {
  Maybe.is_some(
    &2,
    Spec.Draft,
    Spec.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, Some{Ledgers.Asked{t, q}}, found)
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
      Spec.Draft,
      Shared.Bool.when(
        Maybe<&2, Spec.Draft>,
        _,
        u => Spec.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Spec.Draft.content(r, b, n, q)
        ),
        u => found
      )
    )
      == True{}: Bool
  }
  %Equal.sym(
    Maybe<&2, Spec.Content>,
    Spec.Draft.content(r, b, n, q),
    Some{c},
    ec
  ): {
    Maybe.is_some(
      &2,
      Spec.Draft,
      Spec.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), _)
    )
      == True{}: Bool
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
  ea: {
    Spec.Node.asked(
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Spec.Ask>>
  },
  ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Spec.Content>},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}) == True{}: Bool
  } -> {
    Maybe.is_some(
      &2,
      Spec.Draft,
      Spec.Draft.last(
        s,
        w,
        r,
        b,
        n,
        rest,
        Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found)
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
    Spec.Draft,
    Spec.Draft.last(s, w, r, b, n, rest, Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found))
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
        Spec.Draft.of(w, r, b, n, i, Spec.Node.asked(s, i), found)
      )(
        %Equal.sym(Ledgers.Id, i, Ledgers.Id{w, q2}, Ledgers.Id.is_eq_sound(i, Ledgers.Id{w, q2})(ebh)): {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, _, Spec.Node.asked(s, _), found)) == True{}: Bool}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Spec.Node.asked(s, Ledgers.Id{w, q2}), Some{Ledgers.Asked{t, q}}, ea): {Maybe.is_some(&2, Spec.Draft, Spec.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, _, found)) == True{}: Bool}
        Draft.of.hit(w, r, b, n, q2, t, q, c, found, ec))

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
  +ea: {
    Spec.Node.asked(
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Spec.Ask>>
  },
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
) -> {
  Maybe.is_some(&2, Spec.Draft, m) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Content, Spec.Draft.what(m)) == True{}: Bool}:
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
) -> {
  Spec.Node.get(a, Spec.Tip.log(t), Spec.Log.owners()) == m: Maybe<&2, List<&2, U32>>
} -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(a),
    w,
    Maybe.default(
      &2,
      List<&2, String>,
      Maybe.bind(
        &2,
        List<&2, U32>,
        List<&2, String>,
        m,
        ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
      ),
      []
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, String>,
      m,
      ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
    ),
    []
  )
    == Spec.Line.owners(u, t): List<&2, String>
}:
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
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(a), w, []),
              None{},
              Decide.none(Spec.State.ledger(a), w)
            ),
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
        ): {
          Maybe.default(
            &2,
            List<&2, String>,
            Maybe.bind(
              &2,
              List<&2, U32>,
              List<&2, String>,
              Some{ws},
              ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
            ),
            []
          )
            == Maybe.default(
              &2,
              List<&2, String>,
              Maybe.bind(
                &2,
                List<&2, U32>,
                List<&2, String>,
                _,
                ws => Spec.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
              ),
              []
            ): List<&2, String>
        }
        {==}

# owners that decide a step are the owners in any node that grew
def Owners.up(
  +a: Spec.State(),
  u: Spec.State(),
  +t: Spec.Tip,
  w: Ledgers.Where,
  -v: Ledgers.Vote,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(a),
    w,
    Spec.Line.owners(a, t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Line.owners(a, t) == Spec.Line.owners(u, t): List<&2, String>}:
  Owners.up.at(a, u, t, w, v, Spec.Node.get(a, Spec.Tip.log(t), Spec.Log.owners()), g)({==})

# a step that the owners decided at a place in a, they decided in a node that
# grew, with the owners that it reads
def Decide.up(
  +a: Spec.State(),
  +u: Spec.State(),
  +t: Spec.Tip,
  +w: Ledgers.Where,
  v: Ledgers.Vote,
  +g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(a),
    w,
    Spec.Line.owners(a, t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(u),
    w,
    Spec.Line.owners(u, t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  +e =>
    %Owners.up(
      a,
      u,
      t,
      w,
      v,
      g
    )(
      e
    ): {
      Ledgers.State.decide(
        ~Spec.Ask,
        Spec.State.ledger(u),
        w,
        _
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
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
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {
    Spec.Height.decide(s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> (
    @q: Nat -> {
      Ledgers.State.decide(
        ~Spec.Ask,
        Spec.State.ledger(s),
        Ledgers.Where{c, n, q},
        os
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
    } -> R
  ) -> R
) -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(s),
    Ledgers.Where{c, n, r},
    os
  )
    == m: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Vote.first(m, u => Spec.Height.decide(s, c, n, os, p)) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
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
          Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, r}, os),
          Some{x},
          Some{v},
          em,
          e
        )
      )

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  -R: Type,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Spec.Height.decide(s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
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
        Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, n, 1n+p}, os),
        Scan.elim(R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Spec.Head) -> {Spec.Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Spec.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(
  +s: Spec.State(),
  c: Ledgers.Chain,
  +h: Spec.Head,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Spec.Tip,
    Ledgers.Vote,
    Spec.Head.tip(s, h),
    t => Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(+s: Spec.State(), +c: Ledgers.Chain, +h: Spec.Head) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(s, c, h, Spec.Round.seen(s, c, Spec.Head.next(h)))

# the head h after the step m: one height up, at the tip that the step names
# (no step, or one that names no tip: h)
def Head.step(h: Spec.Head, m: Maybe<&2, Ledgers.Vote>) -> Spec.Head:
  match h m:
    case Spec.Head{r, b, n, th} Some{Ledgers.Vote{before, qs, Some{x}}}:
      Spec.Head{r, b, U32.inc(n), Some{x}}
    case x y:
      x

# that the head of the line c in the node s2, when it is not at the height of
# h, is x
def Moves(s2: Spec.State(), c: Ledgers.Chain, h: Spec.Head, x: Spec.Head) -> Type:
  {
    Spec.Heads.level(Some{h}, Spec.Node.head_of(s2, c)) == False{}: Bool
  } -> {Spec.Node.head_of(s2, c) == Some{x}: Maybe<&2, Spec.Head>}

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
  ex: {
    Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == True{}: Bool
  } -> {Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}} == x: Spec.Head}
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
  ex: @t2: Spec.Tip -> {
    Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == True{}: Bool
  } -> {Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}} == x: Spec.Head}
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
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> Moves(Spec.Advance.step(s, c, h, t, m), c, h, Head.step(h, m)):
  match h m:
    case Spec.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(
        Spec.Root.same(before, th),
        Spec.Advance.ran(s, c, r, br, next, after, qs, Spec.Step.run(s, c, t, qs)),
        s,
        c,
        Spec.Head{r, br, next, th},
        Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
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
          Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(Maybe<&2, Hashes.Hash>, after, Some{Spec.Tip.hash(t2)}, Shared.Maybe.is_eq_sound(~Hashes.Hash, ~Hashes.Hash.is_eq, x => y => Hashes.Hash.is_eq_sound(x, y), after, Some{Spec.Tip.hash(t2)})(er)): {Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}} == Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Spec.Head}
            {==}),
        Stay(
          s,
          c,
          Spec.Head{r, br, next, th},
          Head.step(Spec.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
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
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> {
  Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>
} -> Moves(Spec.Advance.at(s, c, h, m), c, h, Head.step(h, Advance.vote(s, c, h))):
  match m:
    case None{}:
      em => et => Stay(s, c, h, Head.step(h, Advance.vote(s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.vote(s, c, h),
          Spec.Height.decide(
            s,
            c,
            Spec.Head.next(h),
            Spec.Line.owners(s, t),
            Spec.Round.seen(s, c, Spec.Head.next(h))
          ),
          Equal.cong(
            Maybe<&2, Spec.Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Spec.Tip,
              Ledgers.Vote,
              mt,
              t1 => Spec.Height.decide(
                s,
                c,
                Spec.Head.next(h),
                Spec.Line.owners(s, t1),
                Spec.Round.seen(s, c, Spec.Head.next(h))
              )
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
            Spec.Height.decide(
              s,
              c,
              Spec.Head.next(h),
              Spec.Line.owners(s, t),
              Spec.Round.seen(s, c, Spec.Head.next(h))
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
          Spec.Height.decide(
            s,
            c,
            Spec.Head.next(h),
            Spec.Line.owners(s, t),
            Spec.Round.seen(s, c, Spec.Head.next(h))
          )
        )(em)

# a head moves only to the tip that the owners in its tip decided next
def Advance.decided(
  +s: Spec.State(),
  c: Ledgers.Chain,
  +h: Spec.Head
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> {
  Spec.Heads.level(Some{h}, Spec.Node.head_of(Spec.Node.advance(s, c), c)) == False{}: Bool
} -> {
  Spec.Node.head_of(
    Spec.Node.advance(s, c),
    c
  )
    == Some{Head.step(h, Advance.vote(s, c, h))}: Maybe<&2, Spec.Head>
}:
  +em =>
    %Equal.sym(
      Maybe<&2, Spec.Head>,
      Spec.Node.head_of(s, c),
      Some{h},
      em
    ): Moves(Spec.Advance.head(s, c, _), c, h, Head.step(h, Advance.vote(s, c, h)))
    Advance.at.moves(s, c, h, Spec.Head.tip(s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  -R: Type,
  +s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Spec.Tip>
) -> {
  Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>
} -> {
  Maybe.bind(
    &2,
    Spec.Tip,
    Ledgers.Vote,
    m,
    t => Spec.Height.decide(s, c, Spec.Head.next(h), Spec.Line.owners(s, t), k)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Spec.Tip -> @q: Nat -> {
    Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>
  } -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, Spec.Head.next(h), q},
      Spec.Line.owners(s, t)
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
        Spec.Head.next(h),
        Spec.Line.owners(s, t),
        k,
        v
      )(e)(q => d => f(t)(q)(em)(d))

# a step that a node found at a head is decided at the head's tip, in some
# round
def Found.elim(
  -R: Type,
  +s: Spec.State(),
  c: Ledgers.Chain,
  +h: Spec.Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Advance.found(s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Spec.Tip -> @q: Nat -> {
    Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>
  } -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, Spec.Head.next(h), q},
      Spec.Line.owners(s, t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  Found.elim.at(R, s, c, h, k, v, Spec.Head.tip(s, h))({==})

# Writes
# ------

# the value of a resource reads back
def Res.round(
  m: Maybe<&2, Ropes.Root>
) -> {Spec.Res.read(Spec.Res.code(m)) == m: Maybe<&2, Ropes.Root>}:
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
) -> {
  Spec.Judge.then(m, h, k) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}:
  match m:
    case Some{True{}}:
      e => e
    case Some{False{}}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Spec.Verdict>,
            Bool,
            v => Took(v),
            Spec.Judge.refuse(h),
            Some{Spec.Verdict{True{}, h2, ds}},
            e
          )
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
) -> {
  Spec.Judge.when(b, h, k) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Spec.Verdict>,
            Bool,
            v => Took(v),
            Spec.Judge.refuse(h),
            Some{Spec.Verdict{True{}, h2, ds}},
            e
          )
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
) -> {
  Spec.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>
} -> {
  Spec.Work.take(
    Spec.Work.put(m2, Some{hh}, ws, [])
  )
    == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {
  Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool
} -> {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
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
            %Equal.sym(List<&2, List<&2, U32>>, List.append(&2, List<&2, U32>, ws, []), ds, Equal.cong(Maybe<&2, Spec.Verdict>, List<&2, List<&2, U32>>, v => Took.nodes(v), Some{Spec.Verdict{True{}, Some{hh}, List.append(&2, List<&2, U32>, ws, [])}}, Some{Spec.Verdict{True{}, h2, ds}}, e)): {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, _) == True{}: Bool}
            hd)
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
) -> {
  Spec.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>
} -> {
  Spec.Work.take(
    Spec.Work.of(s, [], m)
  )
    == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
} -> {
  Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s3, ds) == True{}: Bool
} -> {Spec.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
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
) -> (
  @a: A -> {
    k(a) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
  } -> {kk == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}
) -> {
  Maybe.bind(
    &2,
    A,
    Spec.Verdict,
    ma,
    k
  )
    == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>
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
      )(
        {==}
      )(
        With.took(
          Maybe<&2, Ropes.Root>,
          Spec.Res.find(s, h, n),
          a1 => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Spec.Verdict,
            Spec.Res.find(s, Spec.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Spec.Verdict,
              Spec.Content.find(s, n, c),
              m1 => Spec.Judge.when(
                Spec.Roots.same(a1, b1),
                h,
                x => Spec.Work.take(
                  Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))
                )
              )
            )
          ),
          Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))),
          h2,
          ds
        )(
          +a => With.took(
            Maybe<&2, Ropes.Root>,
            Spec.Res.find(s, Spec.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Spec.Verdict,
              Spec.Content.find(s, n, c),
              m1 => Spec.Judge.when(
                Spec.Roots.same(a, b1),
                h,
                x => Spec.Work.take(
                  Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))
                )
              )
            ),
            Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))),
            h2,
            ds
          )(
            +b => ex => When.took(
              Spec.Roots.same(a, b),
              h,
              x => Spec.Work.take(
                Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))
              ),
              h2,
              ds
            )(
              %ec: {Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Verdict, _, m1 => Spec.Judge.when(Spec.Roots.same(a, b), h, x => Spec.Work.take(Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))))) == Some{Spec.Verdict{True{}, h2, ds}}: Maybe<&2, Spec.Verdict>}
              ex)
          )
        )(
          Then.took(
            Spec.Judge.content(s, c),
            h,
            w => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Spec.Verdict,
              Spec.Res.find(s, h, n),
              a1 => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Spec.Verdict,
                Spec.Res.find(s, Spec.Node.root_of(s, base), n),
                b1 => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Spec.Verdict,
                  Spec.Content.find(s, n, c),
                  m1 => Spec.Judge.when(
                    Spec.Roots.same(a1, b1),
                    h,
                    x => Spec.Work.take(
                      Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))
                    )
                  )
                )
              )
            ),
            h2,
            ds
          )(
            Then.took(
              Spec.Judge.ready_maybe(s, base),
              h,
              u => Spec.Judge.then(
                Spec.Judge.content(s, c),
                h,
                w => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Spec.Verdict,
                  Spec.Res.find(s, h, n),
                  a1 => Maybe.bind(
                    &2,
                    Maybe<&2, Ropes.Root>,
                    Spec.Verdict,
                    Spec.Res.find(s, Spec.Node.root_of(s, base), n),
                    b1 => Maybe.bind(
                      &2,
                      Maybe<&2, Ropes.Root>,
                      Spec.Verdict,
                      Spec.Content.find(s, n, c),
                      m1 => Spec.Judge.when(
                        Spec.Roots.same(a1, b1),
                        h,
                        x => Spec.Work.take(
                          Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m1))
                        )
                      )
                    )
                  )
                )
              ),
              h2,
              ds
            )(e)
          )
        )
      )(Put.holds(s, ds, s3)(ep))
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Ropes.Root,
        _,
        ws => Spec.Res.read(ws)
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
      Spec.Roots.same(o, b),
      True{},
      e
    ): {
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
    %Equal.sym(
      Bool,
      Spec.Roots.same(o, b),
      False{},
      e1
    ): {
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
    %Equal.sym(
      Bool,
      Spec.Roots.same(t, b),
      True{},
      e2
    ): {
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
) -> {
  Shared.Maybe.when(Spec.State(), f, u => Some{x}) == Some{s2}: Maybe<&2, Spec.State()>
} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Spec.State(), s2, e))

def Spec.Seal.accept_fits(s, b, c, s2):
  ec => ea => Accept.fits.if(
    Spec.Seal.fits(c, b),
    Spec.State.keyed(
      Spec.State.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)),
      Spec.Keys.saw(
        Spec.Keys.set(
          Spec.State.keys(s),
          Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
          Spec.Chained.next(c, b)
        ),
        Spec.Ballot.at(b)
      )
    ),
    s2
  )(
    %ec: {Spec.Seal.accept.at(s, b, _) == Some{s2}: Maybe<&2, Spec.State()>}
    ea)

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
) -> {Spec.Heads.level(Some{x}, Some{Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Spec.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# Histories
# ---------

# In.grows once the tip m of the head in a is known
def In.grows.at(
  +a: Spec.State(),
  +u: Spec.State(),
  c: Ledgers.Chain,
  +x: Spec.Head,
  r: Nat,
  v: Ledgers.Vote,
  m: Maybe<&2, Spec.Tip>,
  +g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Head.tip(a, x) == m: Maybe<&2, Spec.Tip>
} -> {
  Maybe.bind(
    &2,
    Spec.Tip,
    Ledgers.Vote,
    m,
    t => Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(a),
      Ledgers.Where{c, Spec.Head.next(x), r},
      Spec.Line.owners(a, t)
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{t}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Spec.Tip>,
          Spec.Head.tip(u, x),
          Some{t},
          Head.tip.grows(a, u, x, t, g)(em)
        ): {
          Maybe.bind(
            &2,
            Spec.Tip,
            Ledgers.Vote,
            _,
            t1 => Ledgers.State.decide(
              ~Spec.Ask,
              Spec.State.ledger(u),
              Ledgers.Where{c, Spec.Head.next(x), r},
              Spec.Line.owners(u, t1)
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        Decide.up(a, u, t, Ledgers.Where{c, Spec.Head.next(x), r}, v, g)(e)

# a step that the owners decided at a head in a round, in a, they decided in
# a node that grew
def In.grows(
  +a: Spec.State(),
  u: Spec.State(),
  c: Ledgers.Chain,
  +x: Spec.Head,
  r: Nat,
  v: Ledgers.Vote,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Advance.in(a, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  In.grows.at(a, u, c, x, r, v, Spec.Head.tip(a, x), g)({==})

# Moved.grows once the step va that a holds at the head is known
def Moved.grows.at(
  a: Spec.State(),
  u: Spec.State(),
  c: Ledgers.Chain,
  x: Spec.Head,
  -y: Spec.Head,
  r: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Advance.in(a, c, x, r) == va: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Head.moved(x, va) == Some{y}: Maybe<&2, Spec.Head>
} -> {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Spec.Head>}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Spec.Head>},
        Shared.Maybe.none_ne_some(Spec.Head, y, e)
      )
    case Some{v}:
      ea => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Spec.Advance.in(u, c, x, r),
          Some{v},
          In.grows(a, u, c, x, r, v, g)(ea)
        ): {Spec.Head.moved(x, _) == Some{y}: Maybe<&2, Spec.Head>}
        e

# a head that a decided step moves in a, it moves the same in a node that grew
def Moved.grows(
  +a: Spec.State(),
  u: Spec.State(),
  +c: Ledgers.Chain,
  +x: Spec.Head,
  -y: Spec.Head,
  +r: Nat,
  g: {Spec.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Head.moved(x, Spec.Advance.in(a, c, x, r)) == Some{y}: Maybe<&2, Spec.Head>
} -> {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Spec.Head>}:
  Moved.grows.at(a, u, c, x, y, r, Spec.Advance.in(a, c, x, r), g)({==})

def Spec.Line.at_grows(rs, a, u, c, h, x):
  match rs:
    case Nil{}:
      g => e => e
    case Con{r, +rest}:
      +g => Shared.Maybe.bind_kept(
        Spec.Head,
        Spec.Head,
        Spec.Line.at(rest, a, c, h),
        Spec.Line.at(rest, u, c, h),
        +z => Spec.Head.moved(z, Spec.Advance.in(a, c, z, r)),
        +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r)),
        x,
        +z => Spec.Line.at_grows(rest, a, u, c, h, z)(g),
        +z => Moved.grows(a, u, c, z, x, r, g)
      )

# Step.same once what the two rounds decide is known (w1, w2)
def Step.same.at(
  u: Spec.State(),
  c: Ledgers.Chain,
  z: Spec.Head,
  r1: Nat,
  r2: Nat,
  t: Spec.Tip,
  -x: Spec.Head,
  -y: Spec.Head,
  w1: Maybe<&2, Ledgers.Vote>,
  w2: Maybe<&2, Ledgers.Vote>,
  one: Spec.Height.One(u, c, Spec.Head.next(z), Spec.Line.owners(u, t))
) -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(u),
    Ledgers.Where{c, Spec.Head.next(z), r1},
    Spec.Line.owners(u, t)
  )
    == w1: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Spec.Ask,
    Spec.State.ledger(u),
    Ledgers.Where{c, Spec.Head.next(z), r2},
    Spec.Line.owners(u, t)
  )
    == w2: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Head.moved(z, w1) == Some{x}: Maybe<&2, Spec.Head>
} -> {Spec.Head.moved(z, w2) == Some{y}: Maybe<&2, Spec.Head>} -> {x == y: Spec.Head}:
  match w1 w2:
    case None{} b:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Spec.Head},
        Shared.Maybe.none_ne_some(Spec.Head, x, k1)
      )
    case Some{v1} None{}:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Spec.Head},
        Shared.Maybe.none_ne_some(Spec.Head, y, k2)
      )
    case Some{+v1} Some{v2}:
      e1 => e2 => k1 => k2 => Shared.Maybe.some_inj(
        Spec.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Spec.Head>,
          Some{x},
          Spec.Head.moved(z, Some{v1}),
          Some{y},
          Equal.sym(Maybe<&2, Spec.Head>, Spec.Head.moved(z, Some{v1}), Some{x}, k1),
          Equal.trans(
            Maybe<&2, Spec.Head>,
            Spec.Head.moved(z, Some{v1}),
            Spec.Head.moved(z, Some{v2}),
            Some{y},
            Equal.cong(
              Ledgers.Vote,
              Maybe<&2, Spec.Head>,
              v => Spec.Head.moved(z, Some{v}),
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
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +z: Spec.Head,
  +r1: Nat,
  +r2: Nat,
  -x: Spec.Head,
  -y: Spec.Head,
  m: Maybe<&2, Spec.Tip>,
  one: Spec.Line.One(u, c)
) -> {
  Spec.Head.tip(u, z) == m: Maybe<&2, Spec.Tip>
} -> {
  Spec.Head.moved(
    z,
    Maybe.bind(
      &2,
      Spec.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Spec.Ask,
        Spec.State.ledger(u),
        Ledgers.Where{c, Spec.Head.next(z), r1},
        Spec.Line.owners(u, t)
      )
    )
  )
    == Some{x}: Maybe<&2, Spec.Head>
} -> {
  Spec.Head.moved(
    z,
    Maybe.bind(
      &2,
      Spec.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Spec.Ask,
        Spec.State.ledger(u),
        Ledgers.Where{c, Spec.Head.next(z), r2},
        Spec.Line.owners(u, t)
      )
    )
  )
    == Some{y}: Maybe<&2, Spec.Head>
} -> {x == y: Spec.Head}:
  match m:
    case None{}:
      em => k1 => k2 => Empty.absurd(
        {x == y: Spec.Head},
        Shared.Maybe.none_ne_some(Spec.Head, x, k1)
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
            ~Spec.Ask,
            Spec.State.ledger(u),
            Ledgers.Where{c, Spec.Head.next(z), r1},
            Spec.Line.owners(u, t)
          ),
          Ledgers.State.decide(
            ~Spec.Ask,
            Spec.State.ledger(u),
            Ledgers.Where{c, Spec.Head.next(z), r2},
            Spec.Line.owners(u, t)
          ),
          one(z)(t)(em)
        )({==})({==})(k1)(k2)

# At.same for one more step of each history, once the heads before are known
def At.same.step(
  +u: Spec.State(),
  c: Ledgers.Chain,
  r1: Nat,
  r2: Nat,
  -x: Spec.Head,
  -y: Spec.Head,
  m1: Maybe<&2, Spec.Head>,
  m2: Maybe<&2, Spec.Head>,
  one: Spec.Line.One(u, c),
  ih: @z1: Spec.Head -> @z2: Spec.Head -> {
    m1 == Some{z1}: Maybe<&2, Spec.Head>
  } -> {m2 == Some{z2}: Maybe<&2, Spec.Head>} -> {z1 == z2: Spec.Head}
) -> {
  Maybe.bind(
    &2,
    Spec.Head,
    Spec.Head,
    m1,
    +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r1))
  )
    == Some{x}: Maybe<&2, Spec.Head>
} -> {
  Maybe.bind(
    &2,
    Spec.Head,
    Spec.Head,
    m2,
    +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r2))
  )
    == Some{y}: Maybe<&2, Spec.Head>
} -> {x == y: Spec.Head}:
  match m1 m2:
    case None{} b:
      k1 => k2 => Empty.absurd({x == y: Spec.Head}, Shared.Maybe.none_ne_some(Spec.Head, x, k1))
    case Some{z1} None{}:
      k1 => k2 => Empty.absurd({x == y: Spec.Head}, Shared.Maybe.none_ne_some(Spec.Head, y, k2))
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
          Spec.Head.tip(u, z1),
          one
        )(
          {==}
        )(
          k1
        )(
          Equal.trans(
            Maybe<&2, Spec.Head>,
            Spec.Head.moved(z1, Spec.Advance.in(u, c, z1, r2)),
            Spec.Head.moved(z2, Spec.Advance.in(u, c, z2, r2)),
            Some{y},
            Equal.cong(
              Spec.Head,
              Maybe<&2, Spec.Head>,
              +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r2)),
              z1,
              z2,
              ih(z1)(z2)({==})({==})
            ),
            k2
          )
        )

# At.same for one more step of each history, with the witness of each step
def At.same.con(
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  r1: Nat,
  r2: Nat,
  t1: List<&2, Nat>,
  t2: List<&2, Nat>,
  -x: Spec.Head,
  -y: Spec.Head,
  ones: Spec.Line.Ones(List.length(&2, Nat, t1), u, c) & Spec.Line.One(u, c),
  ih: @z1: Spec.Head -> @z2: Spec.Head -> Spec.Line.Ones(
    List.length(&2, Nat, t1),
    u,
    c
  ) -> {
    Spec.Line.at(t1, u, c, h) == Some{z1}: Maybe<&2, Spec.Head>
  } -> {Spec.Line.at(t2, u, c, h) == Some{z2}: Maybe<&2, Spec.Head>} -> {z1 == z2: Spec.Head}
) -> {
  Spec.Line.at(r1 <> t1, u, c, h) == Some{x}: Maybe<&2, Spec.Head>
} -> {Spec.Line.at(r2 <> t2, u, c, h) == Some{y}: Maybe<&2, Spec.Head>} -> {x == y: Spec.Head}:
  match ones:
    case Tuple{rest, one}:
      At.same.step(
        u,
        c,
        r1,
        r2,
        x,
        y,
        Spec.Line.at(t1, u, c, h),
        Spec.Line.at(t2, u, c, h),
        one,
        z1 => z2 => ih(z1)(z2)(rest)
      )

# in one node, the same number of decided steps from one head give one head,
# whatever the round of each step
def At.same(
  rs1: List<&2, Nat>,
  rs2: List<&2, Nat>,
  +u: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  x: Spec.Head,
  y: Spec.Head
) -> Spec.Line.Ones(List.length(&2, Nat, rs1), u, c)
  -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
  -> {Spec.Line.at(rs1, u, c, h) == Some{x}: Maybe<&2, Spec.Head>}
  -> {Spec.Line.at(rs2, u, c, h) == Some{y}: Maybe<&2, Spec.Head>}
  -> {x == y: Spec.Head}:
  match rs1 rs2:
    case Nil{} Nil{}:
      ones => el => e1 => e2 => Shared.Maybe.some_inj(
        Spec.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Spec.Head>,
          Some{x},
          Some{h},
          Some{y},
          Equal.sym(Maybe<&2, Spec.Head>, Some{h}, Some{x}, e1),
          e2
        )
      )
    case Nil{} Con{r2, t2}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Spec.Head},
        Shared.Nat.zero_ne_succ(List.length(&2, Nat, t2), el)
      )
    case Con{r1, t1} Nil{}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Spec.Head},
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

def Spec.Line.at_agrees(rs1, rs2, a, b, u, c, h, x, y):
  ga => gb => ones => el => ea => eb =>
    At.same(
      rs1,
      rs2,
      u,
      c,
      h,
      x,
      y
    )(
      ones
    )(
      el
    )(
      Spec.Line.at_grows(rs1, a, u, c, h, x)(ga)(ea)
    )(Spec.Line.at_grows(rs2, b, u, c, h, y)(gb)(eb))

# a step that changes the height of a head moves it one height up
def Moved.step(
  h: Spec.Head,
  v: Ledgers.Vote
) -> {
  Spec.Heads.level(Some{h}, Some{Head.step(h, Some{v})}) == False{}: Bool
} -> {Spec.Head.moved(h, Some{v}) == Some{Head.step(h, Some{v})}: Maybe<&2, Spec.Head>}:
  match h v:
    case Spec.Head{r, b, n, th} Ledgers.Vote{before, qs, Some{y}}:
      e => {==}
    case Spec.Head{r, b, n, th} Ledgers.Vote{before, qs, None{}}:
      e => Empty.absurd(
        {None{} == Some{Spec.Head{r, b, n, th}}: Maybe<&2, Spec.Head>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Spec.Heads.level(Some{Spec.Head{r, b, n, th}}, Some{Spec.Head{r, b, n, th}}),
            True{},
            Equal.sym(
              Bool,
              Spec.Heads.level(Some{Spec.Head{r, b, n, th}}, Some{Spec.Head{r, b, n, th}}),
              False{},
              e
            ),
            Level.refl(Spec.Head{r, b, n, th})
          )
        )
      )

# Node.advance_at once the step m that the node found at the head is known
def Advance.at.one(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Advance.vote(s, c, h) == m: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Heads.level(Some{h}, Some{Head.step(h, m)}) == False{}: Bool
} -> Exists(Nat, q => {Spec.Line.at([q], s, c, h) == Some{Head.step(h, m)}: Maybe<&2, Spec.Head>}):
  match m:
    case None{}:
      em => hl => Empty.absurd(
        Exists(
          Nat,
          q => {Spec.Line.at([q], s, c, h) == Some{Head.step(h, None{})}: Maybe<&2, Spec.Head>}
        ),
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Spec.Heads.level(Some{h}, Some{Head.step(h, None{})}),
            True{},
            Equal.sym(Bool, Spec.Heads.level(Some{h}, Some{Head.step(h, None{})}), False{}, hl),
            Level.none(h)
          )
        )
      )
    case Some{v}:
      em => hl =>
        Found.elim(
          Exists(
            Nat,
            q => {Spec.Line.at([q], s, c, h) == Some{Head.step(h, Some{v})}: Maybe<&2, Spec.Head>}
          ),
          s,
          c,
          h,
          Spec.Round.seen(s, c, Spec.Head.next(h)),
          v
        )(em)(t => q => et => d => Tuple{q, (
              %Equal.sym(Maybe<&2, Spec.Tip>, Spec.Head.tip(s, h), Some{t}, et): {Spec.Head.moved(h, Maybe.bind(&2, Spec.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, Spec.Head.next(h), q}, Spec.Line.owners(s, t1)))) == Some{Head.step(h, Some{v})}: Maybe<&2, Spec.Head>}
              %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, Spec.Head.next(h), q}, Spec.Line.owners(s, t)), Some{v}, d): {Spec.Head.moved(h, _) == Some{Head.step(h, Some{v})}: Maybe<&2, Spec.Head>}
              Moved.step(h, v)(hl))})

def Spec.Node.advance_at(s, c, h):
  +eh => +hl =>
    %Equal.sym(
      Maybe<&2, Spec.Head>,
      Spec.Node.head_of(Spec.Node.advance(s, c), c),
      Some{Head.step(h, Advance.vote(s, c, h))},
      Advance.decided(s, c, h)(eh)(hl)
    ): Exists(Nat, q => {Spec.Line.at([q], s, c, h) == _: Maybe<&2, Spec.Head>})
    Advance.at.one(s, c, h, Advance.vote(s, c, h))({==})(
      %Advance.decided(s, c, h)(eh)(hl): {Spec.Heads.level(Some{h}, _) == False{}: Bool}
      hl)

def Spec.Node.read_draft(s, w, r, b, n, c):
  e =>
    %Equal.sym(
      Maybe<&2, Spec.Content>,
      Spec.Node.draft(s, w, r, b, n),
      Some{c},
      e
    ): {
      Spec.Read.of(
        s,
        n,
        _,
        Spec.Point.Head{r, b}
      )
        == Spec.Root.bytes(s, Spec.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
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
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  os: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Ledgers.Vote>>>:
  Ledgers.Bucket.ballots(
    ~Spec.Ask,
    Ledgers.State.under(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.bucket(c, h, r)),
    os
  )

# the node o cast for the step v in the round r, as a count of ballots reads it
def Hit(s: Spec.State(), c: Ledgers.Chain, h: U32, r: Nat, o: String, v: Ledgers.Vote) -> Bool:
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(
      ~Spec.Ask,
      Ledgers.State.get(
        ~Spec.Ask,
        Ledgers.State.under(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      )
    ),
    v
  )

# a cell that counts for the step v holds a vote for v
def Hit.step(
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  v: Ledgers.Vote
) -> {
  Quorums.Quorum.hit(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Ledgers.Entry.ballot(~Spec.Ask, m),
    v
  )
    == True{}: Bool
} -> {Spec.Cast.step(m) == Some{v}: Maybe<&2, Ledgers.Vote>}:
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +o: String,
  v: Ledgers.Vote
) -> {
  Hit(s, c, h, r, o, v) == True{}: Bool
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, o) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Spec.State.ledger(s),
      Ledgers.Slot.bucket(c, h, r),
      Ledgers.Slot.ballot(o)
    ): {Spec.Cast.step(_) == Some{v}: Maybe<&2, Ledgers.Vote>}
    Hit.step(
      Ledgers.State.get(
        ~Spec.Ask,
        Ledgers.State.under(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.bucket(c, h, r)),
        Ledgers.Slot.ballot(o)
      ),
      v
    )(e)

# a vote moved to an equal round
def Cast.moved(
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  q: String,
  a: Nat,
  b: Nat,
  v: Ledgers.Vote,
  e: {a == b: Nat}
) -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, a}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, b}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  k =>
    %e: {Spec.Cast.of(s, Ledgers.Where{c, h, _}, q) == Some{v}: Maybe<&2, Ledgers.Vote>}
    k

# o when it is a hit, else rest
def Voter.if(+hit: Bool, o: String, rest: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{o}
    case False{}:
      rest

# the first node of os that cast for the step v in the round r, if any did
def Voter(
  +s: Spec.State(),
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
      Voter.if(Hit(s, c, h, r, o, v), o, Voter(s, c, h, r, rest, v))

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
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  r: Nat,
  o: String,
  rest: Maybe<&2, String>,
  v: Ledgers.Vote,
  p: String,
  +hit: Bool,
  eh: {Hit(s, c, h, r, o, v) == hit: Bool},
  ih: {
    rest == Some{p}: Maybe<&2, String>
  } -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}
) -> {
  Voter.if(hit, o, rest) == Some{p}: Maybe<&2, String>
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match hit:
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          String,
          o,
          p,
          e
        ): {Spec.Cast.of(s, Ledgers.Where{c, h, r}, _) == Some{v}: Maybe<&2, Ledgers.Vote>}
        Hit.cast(s, c, h, r, o, v)(eh)
    case False{}:
      e => ih(e)

# the voter cast for the step
def Voter.cast(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote,
  +p: String
) -> {
  Voter(s, c, h, r, os, v) == Some{p}: Maybe<&2, String>
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match os:
    case Nil{}:
      e => Empty.absurd(
        {Spec.Cast.of(s, Ledgers.Where{c, h, r}, p) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(String, p, e)
      )
    case Con{+o, +rest}:
      Voter.cast.at(
        s,
        c,
        h,
        r,
        o,
        Voter(s, c, h, r, rest, v),
        v,
        p,
        Hit(s, c, h, r, o, v),
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  +os: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>
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
        Hit(s, c, h, r, o, v),
        o,
        Voter(s, c, h, r, rest, v),
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
  +s: Spec.State(),
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
} -> {Voter(s, c, h, r, os, v) == None{}: Maybe<&2, String>} -> Empty:
  hh => e =>
    Lt.none(
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Quorums.Quorum.yes(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, os), v),
      Voter.yes(s, c, h, r, os, v)(e)
    )(hh)

# Sub.count for a first owner o and a first node f, once it is known whether
# they are the same (b)
def Sub.count.at(
  +s: Spec.State(),
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
    Spec.Owners.sub(rest, fs) == True{}: Bool
  } -> {
    Voter(s, c, h, r, fs, v) == None{}: Maybe<&2, String>
  } -> {
    Nat.is_le(
      List.length(&2, String, fs),
      Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
    )
      == True{}: Bool
  },
  ih2: {
    Spec.Owners.sub(rest, f <> fs) == True{}: Bool
  } -> {
    Voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
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
    u => Spec.Owners.sub(rest, fs),
    u => Spec.Owners.sub(rest, f <> fs)
  )
    == True{}: Bool
} -> {
  Voter(s, c, h, r, f <> fs, v) == None{}: Maybe<&2, String>
} -> {
  Nat.is_le(
    1n+List.length(&2, String, fs),
    Shared.Nat.add_if(
      Bool.not(Hit(s, c, h, r, o, v)),
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
              Bool.not(Hit(s, c, h, r, _, v)),
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
          Hit(s, c, h, r, f, v),
          False{},
          Voter.if_hit(Hit(s, c, h, r, f, v), f, Voter(s, c, h, r, fs, v))(ev)
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
        ih1(es)(Voter.if_rest(Hit(s, c, h, r, f, v), f, Voter(s, c, h, r, fs, v))(ev))
    case False{}:
      es => ev =>
        Shared.Nat.le_add_if(
          Bool.not(Hit(s, c, h, r, o, v)),
          1n+List.length(&2, String, fs),
          Quorums.Quorum.no(~Ledgers.Vote, ~Ledgers.Vote.is_eq, Round.ballots(s, c, h, r, rest), v)
        )(ih2(es)(ev))

# nodes that are some of the owners, none of which cast for the step v, are
# at most the ballots that are not for v
def Sub.count(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +r: Nat,
  os: List<&2, String>,
  from: List<&2, String>,
  +v: Ledgers.Vote
) -> {
  Spec.Owners.sub(os, from) == True{}: Bool
} -> {
  Voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>
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
  +s: Spec.State(),
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
        Hit(s, c, h, r, o, v),
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
  +s: Spec.State(),
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
} -> {Spec.Owners.sub(os, from) == True{}: Bool}
  -> {Spec.Major(os, from) == True{}: Bool}
  -> {Voter(s, c, h, r, from, v) == None{}: Maybe<&2, String>}
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
  Spec.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Spec.Last.mine(q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Nat.is_le(r, p) == True{}: Bool}:
  match p:
    case 0n:
      Mine.le.or(
        0n,
        Spec.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
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
        Spec.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
        Spec.Last.mine(q, s, c, h, j),
        r,
        x,
        e => Shared.Nat.le_succ(r, j)(Mine.le(s, c, h, q, j, r, x)(e))
      )

# Mine.cast for one round
def Mine.cast.or(
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  q: String,
  k: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  em: {Spec.Cast.of(s, Ledgers.Where{c, h, k}, q) == m: Maybe<&2, Ledgers.Vote>},
  rest: Maybe<&2, Ledgers.Last>,
  r: Nat,
  x: Ledgers.Vote,
  ih: {
    rest == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
  } -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
) -> {
  Spec.Last.or(k, m, u => rest) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
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
        ): {Spec.Cast.of(s, Ledgers.Where{c, h, _}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
        %Equal.cong(
          Maybe<&2, Ledgers.Last>,
          Ledgers.Vote,
          Last.step(y),
          Some{Ledgers.Last{k, y}},
          Some{Ledgers.Last{r, x}},
          e
        ): {Spec.Cast.of(s, Ledgers.Where{c, h, k}, q) == Some{_}: Maybe<&2, Ledgers.Vote>}
        em
    case None{}:
      e => ih(e)

# the last vote of a node is a vote that it cast
def Mine.cast(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r: Nat,
  +x: Ledgers.Vote
) -> {
  Spec.Last.mine(q, s, c, h, p) == Some{Ledgers.Last{r, x}}: Maybe<&2, Ledgers.Last>
} -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}:
  match p:
    case 0n:
      Mine.cast.or(
        s,
        c,
        h,
        q,
        0n,
        Spec.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
        {==},
        None{},
        r,
        x,
        e => Empty.absurd(
          {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>},
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
        Spec.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
        {==},
        Spec.Last.mine(q, s, c, h, j),
        r,
        x,
        Mine.cast(s, c, h, q, j, r, x)
      )

# Cast.apart once it is known whether the rounds are the same (b)
def Cast.apart.at(
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote,
  b: Bool,
  eb: {Nat.is_eq(r1, k) == b: Bool}
) -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
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
            Spec.Cast.of(s, Ledgers.Where{c, h, k}, q),
            Some{v1},
            Equal.sym(
              Maybe<&2, Ledgers.Vote>,
              Spec.Cast.of(s, Ledgers.Where{c, h, k}, q),
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
  s: Spec.State(),
  c: Ledgers.Chain,
  h: U32,
  q: String,
  +r1: Nat,
  +k: Nat,
  v1: Ledgers.Vote
) -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, k}, q) == None{}: Maybe<&2, Ledgers.Vote>
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
) -> {Last.from(Spec.Last.or(k, m, u => rest), r1) == True{}: Bool}:
  match m:
    case Some{y}:
      hk => ih => hk
    case None{}:
      hk => ih => ih({==})

# a node that cast in the round r1 has a last vote of r1 or later, up to any
# round from r1 on
def Mine.from(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: U32,
  +q: String,
  p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Spec.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{v1}: Maybe<&2, Ledgers.Vote>
} -> {
  Nat.is_le(r1, p) == True{}: Bool
} -> {Last.from(Spec.Last.mine(q, s, c, h, p), r1) == True{}: Bool}:
  match p:
    case 0n:
      +e1 => +le =>
        Mine.from.or(
          0n,
          Spec.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
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
                Spec.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
                Some{v1},
                Equal.sym(
                  Maybe<&2, Ledgers.Vote>,
                  Spec.Cast.of(s, Ledgers.Where{c, h, 0n}, q),
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
          Spec.Cast.of(s, Ledgers.Where{c, h, 1n+j}, q),
          Spec.Last.mine(q, s, c, h, j),
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
) -> {Last.from(Spec.Last.newer(a, b), r1) == False{}: Bool} -> {Last.from(a, r1) == False{}: Bool}:
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
) -> {Last.from(Spec.Last.newer(a, b), r1) == False{}: Bool} -> {Last.from(b, r1) == False{}: Bool}:
  match a b:
    case None{} y:
      e => e
    case Some{x} None{}:
      e => {==}
    case Some{Ledgers.Last{+ra, va}} Some{Ledgers.Last{+rb, vb}}:
      Newer.right.at(ra, va, rb, vb, r1, Nat.is_lt(ra, rb), {==})

# Pass.miss for a first node o, once its hit in the round r1 (hit) and its
# pass (m) are known
def Pass.miss.at(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~fb: Spec.Rounds.Last(s, c, h),
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  +o: String,
  rest: Maybe<&2, String>,
  hit: Bool,
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>
) -> {Hit(s, c, h, r1, o, v1) == hit: Bool}
  -> {
    Ledgers.State.passed(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, h, 1n+p},
      o
    )
      == m: Maybe<&2, Maybe<&2, Ledgers.Last>>
  }
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, m) == True{}: Bool}
  -> {Last.from(Spec.Passed.last(m), r1) == False{}: Bool}
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
            %Equal.sym(Maybe<&2, Ledgers.Last>, l, Spec.Last.mine(o, s, c, h, p), fb(1n+p)(o)(l)(em)): {Last.from(_, r1) == True{}: Bool}
            Mine.from(s, c, h, o, p, r1, v1)(Hit.cast(s, c, h, r1, o, v1)(eh))(le)))
      )

# when the passes of the nodes from to the round 1 + p name no vote of the
# round r1 or later, none of them cast in r1
def Pass.miss(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~fb: Spec.Rounds.Last(s, c, h),
  +p: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote,
  from: List<&2, String>
) -> {Nat.is_le(r1, p) == True{}: Bool}
  -> {Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from) == True{}: Bool}
  -> {Last.from(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), r1) == False{}: Bool}
  -> {Voter(s, c, h, r1, from, v1) == None{}: Maybe<&2, String>}:
  match from:
    case Nil{}:
      le => ea => ef => {==}
    case Con{+o, +rest}:
      +le => +ea => +ef =>
        Pass.miss.at(
          ~s,
          ~c,
          ~h,
          ~fb,
          p,
          r1,
          v1,
          o,
          Voter(s, c, h, r1, rest, v1),
          Hit(s, c, h, r1, o, v1),
          Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, o)
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
              Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, o)
            ),
            u => Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, rest)
          )(ea)
        )(
          Newer.left(
            Spec.Passed.last(
              Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, o)
            ),
            Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, rest),
            r1
          )(ef)
        )(
          Pass.miss(
            ~s,
            ~c,
            ~h,
            ~fb,
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
                Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, o)
              ),
              u => Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, rest)
            )(ea)
          )(
            Newer.right(
              Spec.Passed.last(
                Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, o)
              ),
              Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, rest),
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
def Named(-R: Type, s: Spec.State(), w: Ledgers.Where, l: Ledgers.Last) -> Type:
  (
    @q: String -> {
      Spec.Passed.last(
        Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), w, q)
      )
        == Some{l}: Maybe<&2, Ledgers.Last>
    } -> R
  ) -> R

# Last.elim for a first node o, once what it named (a) and what the rest
# named (b) are known
def Last.elim.at(
  -R: Type,
  s: Spec.State(),
  w: Ledgers.Where,
  o: String,
  l: Ledgers.Last,
  a: Maybe<&2, Ledgers.Last>,
  b: Maybe<&2, Ledgers.Last>
) -> {
  Spec.Passed.last(
    Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), w, o)
  )
    == a: Maybe<&2, Ledgers.Last>
} -> (
  {b == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l)
) -> {Spec.Last.newer(a, b) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
  match a b:
    case None{} y:
      ea => ih => e => ih(e)
    case Some{x} None{}:
      ea => ih => e => k => k(
        o
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Last>,
          Spec.Passed.last(Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), w, o)),
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
              Spec.Passed.last(Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), w, o)),
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
  +s: Spec.State(),
  +w: Ledgers.Where,
  from: List<&2, String>,
  +l: Ledgers.Last
) -> {Spec.Passes.last(s, w, from) == Some{l}: Maybe<&2, Ledgers.Last>} -> Named(R, s, w, l):
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
        Spec.Passed.last(Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), w, o)),
        Spec.Passes.last(s, w, rest)
      )({==})(Last.elim(R, s, w, rest, l))

# a pass that names a last vote is held
def Passed.some(
  m: Maybe<&2, Maybe<&2, Ledgers.Last>>,
  l: Ledgers.Last
) -> {
  Spec.Passed.last(m) == Some{l}: Maybe<&2, Ledgers.Last>
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
def All4(a: Bool, b: Bool, c: Bool, d: Bool) -> Bool:
  List.all.if(u2 => List.all.if(u3 => List.all.if(u4 => d, c), b), a)

def All4.a(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {All4(a, b, c, d) == True{}: Bool} -> {a == True{}: Bool}:
  match a:
    case True{}:
      e => {==}
    case False{}:
      e => e

def All4.b(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {All4(a, b, c, d) == True{}: Bool} -> {b == True{}: Bool}:
  match a b:
    case True{} True{}:
      e => {==}
    case True{} False{}:
      e => e
    case False{} y:
      e => Empty.absurd({y == True{}: Bool}, Shared.Bool.false_ne_true(e))

def All4.c(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {All4(a, b, c, d) == True{}: Bool} -> {c == True{}: Bool}:
  match a b c:
    case True{} True{} True{}:
      e => {==}
    case True{} True{} False{}:
      e => e
    case True{} False{} z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))
    case False{} y z:
      e => Empty.absurd({z == True{}: Bool}, Shared.Bool.false_ne_true(e))

def All4.d(
  a: Bool,
  b: Bool,
  c: Bool,
  d: Bool
) -> {All4(a, b, c, d) == True{}: Bool} -> {d == True{}: Bool}:
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
  s: Spec.State(),
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
    Spec.Cast.of(s, Ledgers.Where{c, h, rm}, qm) == Some{vm}: Maybe<&2, Ledgers.Vote>
  } -> {vm == v1: Ledgers.Vote}

# Rounds.last once the node qw that named the last vote is known, with its
# last vote
def Rounds.named(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  j: Nat,
  +rm: Nat,
  +vm: Ledgers.Vote,
  +qw: String,
  +em: {Spec.Last.mine(qw, s, c, h, p) == Some{Ledgers.Last{rm, vm}}: Maybe<&2, Ledgers.Last>},
  lt: {Nat.is_lt(p, j) == True{}: Bool},
  le: {Nat.is_le(r1, rm) == True{}: Bool},
  ih: Rounds.Below(s, c, h, r1, v1, j)
) -> {vm == v1: Ledgers.Vote}:
  ih(
    rm
  )(
    qw
  )(
    vm
  )(
    Shared.Nat.le_lt(rm, p, j)(Mine.le(s, c, h, qw, p, rm, vm)(em))(lt)
  )(le)(Mine.cast(s, c, h, qw, p, rm, vm)(em))

# Rounds.round once the last vote m that the passes name is known: it is of
# the round r1 or later, and the vote x is for its step
def Rounds.last(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~fb: Spec.Rounds.Last(s, c, h),
  r1: Nat,
  v1: Ledgers.Vote,
  +p: Nat,
  x: Ledgers.Vote,
  j: Nat,
  from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> {Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from) == m: Maybe<&2, Ledgers.Last>}
  -> {Last.from(m, r1) == True{}: Bool}
  -> {Spec.Last.is(m, x) == True{}: Bool}
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> Rounds.Below(s, c, h, r1, v1, j)
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
          Ledgers.Where{c, h, 1n+p},
          from,
          Ledgers.Last{rm, vm}
        )(em)(
          +qw => ew =>
            %Ledgers.Vote.is_eq_sound(vm, x)(ei): {_ == v1: Ledgers.Vote}
            Rounds.named(~s, ~c, ~h, r1, v1, p, j, rm, vm, qw, Equal.sym(Maybe<&2, Ledgers.Last>, Some{Ledgers.Last{rm, vm}}, Spec.Last.mine(qw, s, c, h, p), fb(1n+p)(qw)(Some{Ledgers.Last{rm, vm}})(Passed.some(Ledgers.State.passed(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, h, 1n+p}, qw), Ledgers.Last{rm, vm})(ew))), lt, ef, ih))

# Rounds.round once it is known whether the passes name a vote of the round
# r1 or later (f)
def Rounds.pick(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fb: Spec.Rounds.Last(s, c, h),
  +r1: Nat,
  +v1: Ledgers.Vote,
  +p: Nat,
  +x: Ledgers.Vote,
  j: Nat,
  +from: List<&2, String>,
  f: Bool
) -> {Last.from(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), r1) == f: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, h, r1, os),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(p, j) == True{}: Bool}
  -> {Nat.is_le(r1, p) == True{}: Bool}
  -> Rounds.Below(s, c, h, r1, v1, j)
  -> {
    All4(
      Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from),
      Spec.Owners.sub(os, from),
      Spec.Major(os, from),
      Spec.Last.is(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), x)
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
            h,
            r1,
            os,
            from,
            v1
          )(
            hh
          )(
            All4.b(
              Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from),
              Spec.Owners.sub(os, from),
              Spec.Major(os, from),
              Spec.Last.is(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), x)
            )(al)
          )(
            All4.c(
              Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from),
              Spec.Owners.sub(os, from),
              Spec.Major(os, from),
              Spec.Last.is(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), x)
            )(al)
          )(
            Pass.miss(
              ~s,
              ~c,
              ~h,
              ~fb,
              p,
              r1,
              v1,
              from
            )(
              le
            )(
              All4.a(
                Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from),
                Spec.Owners.sub(os, from),
                Spec.Major(os, from),
                Spec.Last.is(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), x)
              )(al)
            )(ef)
          )
        )
    case True{}:
      ef => hh => lt => le => ih => al =>
        Rounds.last(
          ~s,
          ~c,
          ~h,
          ~fb,
          r1,
          v1,
          p,
          x,
          j,
          from,
          Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from)
        )(
          {==}
        )(
          ef
        )(
          All4.d(
            Spec.Passed.all(s, Ledgers.Where{c, h, 1n+p}, from),
            Spec.Owners.sub(os, from),
            Spec.Major(os, from),
            Spec.Last.is(Spec.Passes.last(s, Ledgers.Where{c, h, 1n+p}, from), x)
          )(al)
        )(lt)(ih)

# Rounds.same at the round r1 itself, once a voter m of the step v1 is known
def Rounds.base(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fc: Spec.Rounds.Same(s, c, h),
  +r1: Nat,
  +v1: Ledgers.Vote,
  q: String,
  x: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {Voter(s, c, h, r1, os, v1) == m: Maybe<&2, String>}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, h, r1, os),
      v1
    )
      == True{}: Bool
  }
  -> {Spec.Cast.of(s, Ledgers.Where{c, h, r1}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> {x == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => hh => e => Empty.absurd({x == v1: Ledgers.Vote}, Has.voter(s, c, h, r1, os, v1)(hh)(em))
    case Some{+o}:
      em => hh => e => fc(r1)(q)(o)(x)(v1)(e)(Voter.cast(s, c, h, r1, os, v1, o)(em))

# Rounds.same in a round after r1
def Rounds.step(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
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
      Round.ballots(s, c, h, r1, os),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> Rounds.Below(s, c, h, r1, v1, j)
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
          ~h,
          ~os,
          ~fb,
          r1,
          v1,
          p,
          x,
          j,
          Spec.Cast.from(s, Ledgers.Where{c, h, 1n+p}, q),
          Last.from(
            Spec.Passes.last(
              s,
              Ledgers.Where{c, h, 1n+p},
              Spec.Cast.from(s, Ledgers.Where{c, h, 1n+p}, q)
            ),
            r1
          )
        )({==})(hh)(lt)(Shared.Nat.le_step(r1, p)(le)(ne))(ih)(fa(1n+p)(q)(x)(e))

# Rounds.same once it is known whether the round is r1 (b)
def Rounds.same.at(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
  ~fc: Spec.Rounds.Same(s, c, h),
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
      Round.ballots(s, c, h, r1, os),
      v1
    )
      == True{}: Bool
  }
  -> {Nat.is_lt(r, 1n+j) == True{}: Bool}
  -> {Nat.is_le(r1, r) == True{}: Bool}
  -> {Spec.Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{x}: Maybe<&2, Ledgers.Vote>}
  -> Rounds.Below(s, c, h, r1, v1, j)
  -> {x == v1: Ledgers.Vote}:
  match b:
    case True{}:
      eb => hh => lt => le => e => ih =>
        Rounds.base(
          ~s,
          ~c,
          ~h,
          ~os,
          ~fc,
          r1,
          v1,
          q,
          x,
          Voter(s, c, h, r1, os, v1)
        )(
          {==}
        )(
          hh
        )(
          Cast.moved(
            s,
            c,
            h,
            q,
            r,
            r1,
            x,
            Equal.sym(Nat, r1, r, Shared.Nat.is_eq_sound(r1, r)(eb))
          )(e)
        )
    case False{}:
      eb => hh => lt => le => e => ih =>
        Rounds.step(~s, ~c, ~h, ~os, ~fa, ~fb, r1, v1, r, q, x, j)(eb)(hh)(lt)(le)(e)(ih)

# each vote of a round from r1 on, below the round k, is for the step that a
# majority cast in r1
def Rounds.same(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
  ~fc: Spec.Rounds.Same(s, c, h),
  k: Nat,
  +r1: Nat,
  +v1: Ledgers.Vote
) -> {
  Quorums.Quorum.has(
    ~Ledgers.Vote,
    ~Ledgers.Vote.is_eq,
    Round.ballots(s, c, h, r1, os),
    v1
  )
    == True{}: Bool
} -> Rounds.Below(s, c, h, r1, v1, k):
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
          ~h,
          ~os,
          ~fa,
          ~fb,
          ~fc,
          r1,
          v1,
          rm,
          qm,
          vm,
          j,
          Nat.is_eq(r1, rm)
        )({==})(hh)(lt)(le)(e)(Rounds.same(~s, ~c, ~h, ~os, ~fa, ~fb, ~fc, j, r1, v1)(hh))

# Rounds.later once a voter m of the step v2 in the round r2 is known
def Rounds.later.at(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
  ~fc: Spec.Rounds.Same(s, c, h),
  r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  +v2: Ledgers.Vote,
  m: Maybe<&2, String>
) -> {Voter(s, c, h, r2, os, v2) == m: Maybe<&2, String>}
  -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, h, r1, os),
      v1
    )
      == True{}: Bool
  }
  -> {
    Quorums.Quorum.has(
      ~Ledgers.Vote,
      ~Ledgers.Vote.is_eq,
      Round.ballots(s, c, h, r2, os),
      v2
    )
      == True{}: Bool
  }
  -> {v2 == v1: Ledgers.Vote}:
  match m:
    case None{}:
      em => le => h1 => h2 => Empty.absurd(
        {v2 == v1: Ledgers.Vote},
        Has.voter(s, c, h, r2, os, v2)(h2)(em)
      )
    case Some{+o}:
      em => le => h1 => h2 =>
        Rounds.same(
          ~s,
          ~c,
          ~h,
          ~os,
          ~fa,
          ~fb,
          ~fc,
          1n+r2,
          r1,
          v1
        )(h1)(r2)(o)(v2)(Shared.Nat.lt_succ(r2))(le)(Voter.cast(s, c, h, r2, os, v2, o)(em))

# a round decides what an earlier round of its height decided
def Rounds.later(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
  ~fc: Spec.Rounds.Same(s, c, h),
  +r1: Nat,
  +r2: Nat,
  +v1: Ledgers.Vote,
  +v2: Ledgers.Vote
) -> {Nat.is_le(r1, r2) == True{}: Bool}
  -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, h, r1},
      os
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, h, r2},
      os
    )
      == Some{v2}: Maybe<&2, Ledgers.Vote>
  }
  -> {v2 == v1: Ledgers.Vote}:
  le => d1 => d2 =>
    Rounds.later.at(
      ~s,
      ~c,
      ~h,
      ~os,
      ~fa,
      ~fb,
      ~fc,
      r1,
      r2,
      v1,
      v2,
      Voter(s, c, h, r2, os, v2)
    )(
      {==}
    )(
      le
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, h, r1, os),
        v1
      )(d1)
    )(
      Quorums.Quorum.major_has(
        ~Ledgers.Vote,
        ~Ledgers.Vote.is_eq,
        ~Ledgers.Vote.laws(),
        Round.ballots(s, c, h, r2, os),
        v2
      )(d2)
    )

# Rounds.one once it is known whether r1 is at most r2 (b)
def Rounds.one.at(
  ~s: Spec.State(),
  ~c: Ledgers.Chain,
  ~h: U32,
  ~os: List<&2, String>,
  ~fa: Spec.Rounds.Allow(s, c, h, os),
  ~fb: Spec.Rounds.Last(s, c, h),
  ~fc: Spec.Rounds.Same(s, c, h),
  +r1: Nat,
  +r2: Nat,
  v1: Ledgers.Vote,
  v2: Ledgers.Vote,
  b: Bool
) -> {Nat.is_le(r1, r2) == b: Bool}
  -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, h, r1},
      os
    )
      == Some{v1}: Maybe<&2, Ledgers.Vote>
  }
  -> {
    Ledgers.State.decide(
      ~Spec.Ask,
      Spec.State.ledger(s),
      Ledgers.Where{c, h, r2},
      os
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
        Rounds.later(~s, ~c, ~h, ~os, ~fa, ~fb, ~fc, r1, r2, v1, v2)(eb)(d1)(d2)
      )
    case False{}:
      eb => d1 => d2 =>
        Rounds.later(
          ~s,
          ~c,
          ~h,
          ~os,
          ~fa,
          ~fb,
          ~fc,
          r2,
          r1,
          v2,
          v1
        )(Shared.Nat.nle_le(r1, r2)(eb))(d2)(d1)

def Spec.Rounds.one(s, c, h, os, fa, fb, fc):
  +r1 => +r2 => v1 => v2 => d1 => d2 =>
    Rounds.one.at(~s, ~c, ~h, ~os, ~fa, ~fb, ~fc, r1, r2, v1, v2, Nat.is_le(r1, r2))({==})(d1)(d2)

def Spec.Cast.put_keeps(n, w, th, qs, from, s2, t2, ns, s, s3):
  +s4 = Spec.State.led(s, Spec.State.ledger(s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Spec.State()>,
      Spec.State.put(s2, [Spec.Tip.words(t2)]),
      Some{s3},
      e
    ): {Spec.Node.grows(s2, Spec.Cast.vote(s, _, w, n, a0)) == True{}: Bool}
    Grows.trans(
      s2,
      s4,
      Spec.Cast.seal(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n))
    )(
      Grows.to(
        s2,
        s3,
        s4,
        Led.led(s, Spec.State.ledger(s3)),
        Put.grew(s2, [Spec.Tip.words(t2)], s3, e)
      )
    )(Cast.seal.grows(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n)))

def Spec.Cast.put_tip(n, w, th, qs, from, s2, t2, ns, s, s3):
  +s4 = Spec.State.led(s, Spec.State.ledger(s3))
  +a0 = {Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Spec.Tip.hash(t2)}}, from}: Ledgers.Act}
  +e =>
    %Equal.sym(
      Maybe<&2, Spec.State()>,
      Spec.State.put(s2, [Spec.Tip.words(t2)]),
      Some{s3},
      e
    ): {
      Spec.Tip.at(
        Spec.Cast.vote(s, _, w, n, a0),
        Spec.Tip.hash(t2)
      )
        == Some{t2}: Maybe<&2, Spec.Tip>
    }
    Tip.at.grows(
      s3,
      Spec.Cast.seal(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n)),
      Spec.Tip.hash(t2),
      t2,
      Grows.trans(
        s3,
        s4,
        Spec.Cast.seal(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n))
      )(
        Grows.to(s3, s3, s4, Led.led(s, Spec.State.ledger(s3)), Grows.refl(s3))
      )(Cast.seal.grows(s4, w, n, a0, Spec.Seal.chain(s4, Spec.Where.store(w), n)))
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
  +g = Spec.Seen.of(s, b)
  Shared.List.keep_holds(~Spec.Touch, ~Spec.Seen, ~Spec.Touch.holds, Spec.Affects.cands(s, b, g), g)

# Moves
# -----
# A move sets only keys of the version vector, so each resource of its target
# reads the same after it (Spec.Move.reads).

# the key of a resource is not the key of a line in the version vector
def Vector.apart(
  c: Ledgers.Chain,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.vector(c), Spec.Key.res(n)) == False{}: Bool}:
  {==}

# Vector.add keeps a resource, once it is known whether the vector covers the
# place (b)
def Vector.add.reads.if(
  s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +c: Ledgers.Chain,
  p: Spec.Place,
  +n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: {Spec.Node.get(s, h, Spec.Key.res(n)) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Spec.Work>,
    b,
    u => Some{Spec.Work{s, h, ns}},
    u => Spec.Work.set(Spec.Work{s, h, ns}, Spec.Key.vector(c), Spec.Place.code(p))
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Set.kept(
        s,
        h,
        ns,
        Spec.Key.vector(c),
        Spec.Place.code(p),
        Spec.Key.res(n),
        v,
        Vector.apart(c, n),
        hget
      )

# a new entry of the version vector keeps a resource
def Vector.add.reads(
  w: Spec.Work,
  +c: Ledgers.Chain,
  +p: Spec.Place,
  n: Resources.Name,
  v: List<&2, U32>
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Spec.Key.res(n), v, Spec.Vector.add(w, c, p)):
  match w:
    case Spec.Work{+s, +h, ns}:
      hget => Vector.add.reads.if(
        s,
        h,
        ns,
        c,
        p,
        n,
        v,
        Spec.Place.covered(Spec.Node.vector(s, h, c), p),
        hget
      )

# Vector.add.if keeps a resource, once it is known whether the place is of
# the line (b)
def Vector.add.if.reads.at(
  w: Spec.Work,
  +p: Spec.Place,
  n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: Spec.Work.Reads(Spec.Key.res(n), v, Some{w})
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Spec.Work>,
    b,
    u => Some{w},
    u => Spec.Vector.add(w, Spec.Place.chain(p), p)
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Vector.add.reads(w, Spec.Place.chain(p), p, n, v)(hget)

# an entry of the version vector, if any, keeps a resource
def Vector.add.if.reads(
  w: Spec.Work,
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Place>,
  n: Resources.Name,
  v: List<&2, U32>
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Spec.Key.res(n), v, Spec.Vector.add.if(w, c, m)):
  match m:
    case None{}:
      hget => hget
    case Some{+p}:
      hget => Vector.add.if.reads.at(w, p, n, v, Ledgers.Chain.is_eq(Spec.Place.chain(p), c), hget)

# a work that reads a key, after a step that keeps the read
def Reads.bind(
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Spec.Work>,
  -f: Spec.Work -> Maybe<&2, Spec.Work>
) -> Spec.Work.Reads(
  k,
  v,
  m
) -> (
  @w: Spec.Work -> Spec.Work.Reads(k, v, Some{w}) -> Spec.Work.Reads(k, v, f(w))
) -> Spec.Work.Reads(k, v, Maybe.bind(&2, Spec.Work, Spec.Work, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{w}:
      hm => hf => hf(w)(hm)

# the entries of some bindings keep a resource
def Vector.adds.reads(
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  m
) -> Spec.Work.Reads(Spec.Key.res(n), v, Spec.Vector.adds(bs, c, m)):
  match bs:
    case Nil{}:
      hm => hm
    case Con{+b, r}:
      hm => Vector.adds.reads(
        r,
        c,
        Maybe.bind(
          &2,
          Spec.Work,
          Spec.Work,
          m,
          w => Spec.Vector.add.if(w, c, Spec.Vector.entry(b))
        ),
        n,
        v
      )(
        Reads.bind(
          Spec.Key.res(n),
          v,
          m,
          w => Spec.Vector.add.if(w, c, Spec.Vector.entry(b))
        )(hm)(+w => hw => Vector.add.if.reads(w, c, Spec.Vector.entry(b), n, v)(hw))
      )

# the version vector of a version, joined in, keeps a resource
def Vector.joined.reads(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  m
) -> Spec.Work.Reads(Spec.Key.res(n), v, Spec.Vector.joined(s, c, x, m)):
  hm => Reads.bind(
    Spec.Key.res(n),
    v,
    Spec.Vector.adds(
      Trees.Tree.list(~Spec.State(), ~Spec.Store.fetch, s, Spec.Node.root_of(s, Some{x})),
      c,
      m
    ),
    w => Spec.Vector.add.if(w, c, Spec.Node.place(s, x))
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Spec.State(), ~Spec.Store.fetch, s, Spec.Node.root_of(s, Some{x})),
      c,
      m,
      n,
      v
    )(hm)
  )(+w => hw => Vector.add.if.reads(w, c, Spec.Node.place(s, x), n, v)(hw))

def Spec.Move.reads(s, c, to, h, n, v):
  hget => Vector.joined.reads(
    s,
    c,
    to,
    Spec.Vector.adds(
      Trees.Tree.list(~Spec.State(), ~Spec.Store.fetch, s, h),
      c,
      Some{Spec.Work{s, Spec.Node.root_of(s, Some{to}), []}}
    ),
    n,
    v
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Spec.State(), ~Spec.Store.fetch, s, h),
      c,
      Some{Spec.Work{s, Spec.Node.root_of(s, Some{to}), []}},
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
      Spec.Key.res(Resources.Name{t1}),
      Spec.Key.res(Resources.Name{t2})
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
                    Spec.Key.res(Resources.Name{t1}),
                    Spec.Key.res(Resources.Name{t2}),
                    Shared.List.is_eq_sound(
                      ~U32,
                      ~U32.is_eq,
                      ~Shared.U32.laws(),
                      Spec.Key.res(Resources.Name{t1}),
                      Spec.Key.res(Resources.Name{t2})
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
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.res(m), Spec.Key.res(n)) == False{}: Bool}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      hf => Res.apart.at(
        t1,
        t2,
        Shared.List.is_eq(
          ~U32,
          ~U32.is_eq,
          Spec.Key.res(Resources.Name{t1}),
          Spec.Key.res(Resources.Name{t2})
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
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.clash(m), Spec.Key.res(n)) == False{}: Bool}:
  {==}

# a work that reads a key, after a read that gives the next step
def Reads.with(
  -A: Data,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  +ma: Maybe<&2, A>,
  -f: A -> Maybe<&2, Spec.Work>
) -> (
  @a: A -> Spec.Work.Reads(k, v, f(a))
) -> Spec.Work.Reads(k, v, Maybe.bind(&2, A, Spec.Work, ma, f)):
  match ma:
    case None{}:
      hf => Unit{}
    case Some{a}:
      hf => hf(a)

# a set of another key keeps what a work reads
def Set.kept.work(
  +w: Spec.Work,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Spec.Work.Reads(k2, v, Some{w}) -> Spec.Work.Reads(k2, v, Spec.Work.set(w, k, x)):
  match w:
    case Spec.Work{s, h, ns}:
      hget => Set.kept(s, h, ns, k, x, k2, v, hne, hget)

# Keep.reads once it is known whether the node holds the new data (b)
def Keep.reads.if(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  old: List<&2, List<&2, U32>>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +b: Bool,
  hget: {Spec.Node.get(s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(
  k,
  v,
  Spec.Work.put(Shared.Maybe.when(Spec.State(), b, u => Some{Spec.State.keep(s, ns)}), h, ns, old)
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Get.grows(s, Spec.State.keep(s, ns), h, k, v, Grows.keep(s, ns))(hget)

# new data keeps what a work reads
def Keep.reads(
  +w: Spec.Work,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> Spec.Work.Reads(k, v, Some{w}) -> Spec.Work.Reads(k, v, Spec.Work.keep(w, ns)):
  match w:
    case Spec.Work{s, h, old}:
      hget => Keep.reads.if(
        s,
        h,
        old,
        ns,
        k,
        v,
        Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ns), ns),
        hget
      )

# Set.read once it is known whether the node holds the new nodes (b)
def Set.read.if(
  +s: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  +b: Bool,
  eb: {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ws), ws) == b: Bool},
  em: {Spec.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Spec.Work.Reads(
  k,
  x,
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
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Spec.Node.get(Spec.State.keep(s, ws), Some{hh}, k),
        Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ws), Some{hh}, k),
        Some{x},
        Get.is(Spec.State.keep(s, ws), Some{hh}, k),
        Trees.Tree.get_set(
          ~Spec.State(),
          ~Spec.Store.fetch,
          s,
          Spec.State.keep(s, ws),
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
            em
          )
        )(eb)
      )

# Set.read once the new subtree m is known
def Set.read.of(
  +s: Spec.State(),
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  +m: Maybe<&2, Trees.Put>,
  em: {Spec.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>}
) -> Spec.Work.Reads(k, x, Spec.Work.of(s, ns, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, ws}}:
      Set.read.if(
        s,
        h,
        ns,
        k,
        x,
        hh,
        ws,
        Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, Spec.State.keep(s, ws), ws),
        {==},
        em
      )

# a key that a work sets, it reads
def Set.read(
  +w: Spec.Work,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Spec.Work.Reads(k, x, Spec.Work.set(w, k, x)):
  match w:
    case Spec.Work{s, h, ns}:
      Set.read.of(s, h, ns, k, x, Spec.Node.set(s, h, k, x), {==})

# the merge of one resource m, of the trees hb (base), ho (ours) and ht
# (theirs), on the work w: one step of Spec.Merge.all
def Merge.step(
  +s: Spec.State(),
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  w: Spec.Work
) -> Maybe<&2, Spec.Work>:
  Maybe.bind(
    &2,
    Maybe<&2, Ropes.Root>,
    Spec.Work,
    Spec.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Spec.Work,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Spec.Work,
        Spec.Res.find(s, ht, m),
        x => Spec.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )

# what the merge of another resource puts keeps what a work reads for n
def Merge.put.other(
  f: Ledgers.Id,
  +m: Resources.Name,
  +n: Resources.Name,
  +o2: Maybe<&2, Ropes.Root>,
  +p: Spec.Pick,
  +w: Spec.Work,
  +v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.res(m), Spec.Key.res(n)) == False{}: Bool}
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Spec.Key.res(n), v, Spec.Merge.put(f, m, o2, p, w)):
  match p:
    case Spec.Pick.Take{mm}:
      Set.kept.work(w, Spec.Key.res(m), Spec.Res.code(mm), Spec.Key.res(n), v, hne)
    case Spec.Pick.Make{y}:
      hget => Reads.bind(
        Spec.Key.res(n),
        v,
        Spec.Work.keep(w, Ropes.Put.nodes(Spec.Bytes.rope(y))),
        w2 => Spec.Work.set(
          w2,
          Spec.Key.res(m),
          Spec.Res.code(Some{Ropes.Put.root(Spec.Bytes.rope(y))})
        )
      )(
        Keep.reads(w, Ropes.Put.nodes(Spec.Bytes.rope(y)), Spec.Key.res(n), v)(hget)
      )(
        w2 => hw => Set.kept.work(
          w2,
          Spec.Key.res(m),
          Spec.Res.code(Some{Ropes.Put.root(Spec.Bytes.rope(y))}),
          Spec.Key.res(n),
          v,
          hne
        )(hw)
      )
    case Spec.Pick.Clash{}:
      hget => Reads.bind(
        Spec.Key.res(n),
        v,
        Spec.Work.set(w, Spec.Key.res(m), Spec.Res.code(o2)),
        y => Spec.Work.set(y, Spec.Key.clash(m), Spec.Clash.code(f))
      )(
        Set.kept.work(w, Spec.Key.res(m), Spec.Res.code(o2), Spec.Key.res(n), v, hne)(hget)
      )(
        y => hy => Set.kept.work(
          y,
          Spec.Key.clash(m),
          Spec.Clash.code(f),
          Spec.Key.res(n),
          v,
          Clash.apart(m, n)
        )(hy)
      )

# the merge of another resource keeps what a work reads for n
def Merge.step.other(
  +s: Spec.State(),
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  n: Resources.Name,
  w: Spec.Work,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.res(m), Spec.Key.res(n)) == False{}: Bool}
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Spec.Key.res(n), v, Merge.step(s, f, hb, ho, ht, m, w)):
  hget => Reads.with(
    Maybe<&2, Ropes.Root>,
    Spec.Key.res(n),
    v,
    Spec.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Spec.Work,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Spec.Work,
        Spec.Res.find(s, ht, m),
        x => Spec.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )(
    b => Reads.with(
      Maybe<&2, Ropes.Root>,
      Spec.Key.res(n),
      v,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Spec.Work,
        Spec.Res.find(s, ht, m),
        x => Spec.Merge.one(s, f, m, b, o, x, w)
      )
    )(
      +o => Reads.with(
        Maybe<&2, Ropes.Root>,
        Spec.Key.res(n),
        v,
        Spec.Res.find(s, ht, m),
        x => Spec.Merge.one(s, f, m, b, o, x, w)
      )(
        x => Reads.with(
          Spec.Pick,
          Spec.Key.res(n),
          v,
          Spec.Pick.merge(Formats.Format.of(Resources.Name.path(m)), s, b, o, x),
          p => Spec.Merge.put(f, m, o, p, w)
        )(p => Merge.put.other(f, m, n, o, p, w, v, hne)(hget))
      )
    )
  )

# the merge of the resource n gives what its pick takes
def Merge.step.same(
  s: Spec.State(),
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  w: Spec.Work,
  eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  }
) -> Spec.Work.Reads(Spec.Key.res(n), Spec.Res.code(x), Merge.step(s, f, hb, ho, ht, n, w)):
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, hb, n),
    Some{b},
    eb
  ): Spec.Work.Reads(
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Spec.Work,
      _,
      b1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Spec.Work,
        Spec.Res.find(s, ho, n),
        o1 => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Spec.Work,
          Spec.Res.find(s, ht, n),
          x1 => Spec.Merge.one(s, f, n, b1, o1, x1, w)
        )
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, ho, n),
    Some{o},
    eo
  ): Spec.Work.Reads(
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Spec.Work,
      _,
      o1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Spec.Work,
        Spec.Res.find(s, ht, n),
        x1 => Spec.Merge.one(s, f, n, b, o1, x1, w)
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, ht, n),
    Some{t},
    et
  ): Spec.Work.Reads(
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(&2, Maybe<&2, Ropes.Root>, Spec.Work, _, x1 => Spec.Merge.one(s, f, n, b, o, x1, w))
  )
  %Equal.sym(
    Maybe<&2, Spec.Pick>,
    Spec.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    Some{Spec.Pick.Take{x}},
    ep
  ): Spec.Work.Reads(
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(&2, Spec.Pick, Spec.Work, _, p => Spec.Merge.put(f, n, o, p, w))
  )
  Set.read(w, Spec.Key.res(n), Spec.Res.code(x))

# Merge.step.same on the work m, if any
def Merge.step.takes(
  s: Spec.State(),
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  }
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  Spec.Res.code(x),
  Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, n, w))
):
  match m:
    case None{}:
      Unit{}
    case Some{w}:
      Merge.step.same(s, f, hb, ho, ht, n, b, o, t, x, w, eb, eo, et, ep)

# one step of a merge keeps what the work reads for n, once it is known
# whether the step is of n (same)
def Merge.step.keeps(
  s: Spec.State(),
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m1: Resources.Name,
  m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool}
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  Spec.Res.code(x),
  m
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  Spec.Res.code(x),
  Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
):
  match same:
    case True{}:
      hm =>
        %Equal.sym(
          Resources.Name,
          m1,
          n,
          Name.sound(m1, n)(es)
        ): Spec.Work.Reads(
          Spec.Key.res(n),
          Spec.Res.code(x),
          Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, _, w))
        )
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep)
    case False{}:
      hm => Reads.bind(
        Spec.Key.res(n),
        Spec.Res.code(x),
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
          Spec.Res.code(x),
          Res.apart(m1, n)(es)
        )(hw)
      )

# the merge of more resources keeps what the work reads for n
def Merge.all.keeps(
  +s: Spec.State(),
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  }
) -> Spec.Work.Reads(
  Spec.Key.res(n),
  Spec.Res.code(x),
  m
) -> Spec.Work.Reads(Spec.Key.res(n), Spec.Res.code(x), Spec.Merge.all(s, f, ns, hb, ho, ht, m)):
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
        Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
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
  +s: Spec.State(),
  +f: Ledgers.Id,
  +m1: Resources.Name,
  r: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool},
  ih: {
    List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n) == True{}: Bool
  } -> Spec.Work.Reads(
    Spec.Key.res(n),
    Spec.Res.code(x),
    Spec.Merge.all(
      s,
      f,
      r,
      hb,
      ho,
      ht,
      Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
    )
  )
) -> {
  List.any.if(
    u => List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n),
    same
  )
    == True{}: Bool
} -> Spec.Work.Reads(
  Spec.Key.res(n),
  Spec.Res.code(x),
  Spec.Merge.all(
    s,
    f,
    r,
    hb,
    ho,
    ht,
    Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
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
        Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
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
        %Equal.sym(Resources.Name, m1, n, Name.sound(m1, n)(es)): Spec.Work.Reads(Spec.Key.res(n), Spec.Res.code(x), Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, _, w)))
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep))
    case False{}:
      e => ih(e)

# a merge of the resources ns, with n among them, gives what the pick of n
# takes
def Merge.all.takes(
  +s: Spec.State(),
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Spec.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Spec.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Spec.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Spec.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Spec.Pick.Take{x}}: Maybe<&2, Spec.Pick>
  }
) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n) == True{}: Bool
} -> Spec.Work.Reads(Spec.Key.res(n), Spec.Res.code(x), Spec.Merge.all(s, f, ns, hb, ho, ht, m)):
  match ns:
    case Nil{}:
      e => Empty.absurd(
        Spec.Work.Reads(Spec.Key.res(n), Spec.Res.code(x), m),
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
          Maybe.bind(&2, Spec.Work, Spec.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
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
    Spec.Merge.all(
      s,
      from,
      Spec.Merge.names(s, h, Spec.Node.root_of(s, Some{from})),
      Spec.Node.root_of(s, Spec.Merge.base(s, c, from, h)),
      h,
      Spec.Node.root_of(s, Some{from}),
      Some{Spec.Work{s, h, []}}
    ),
    n,
    Spec.Res.code(x)
  )(
    Merge.all.takes(
      s,
      from,
      Spec.Merge.names(s, h, Spec.Node.root_of(s, Some{from})),
      Spec.Node.root_of(s, Spec.Merge.base(s, c, from, h)),
      h,
      Spec.Node.root_of(s, Some{from}),
      Some{Spec.Work{s, h, []}},
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
    Spec.Key.res(n),
    Spec.Res.code(m),
    Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m)),
    y => Spec.Work.set(y, Spec.Key.clash(n), [])
  )(
    Set.read(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m))
  )(
    y => hy => Set.kept.work(
      y,
      Spec.Key.clash(n),
      [],
      Spec.Key.res(n),
      Spec.Res.code(m),
      Clash.apart(n, n)
    )(hy)
  )

def Spec.Resolve.shuts(s, h, n, m):
  Reads.with(
    Spec.Work,
    Spec.Key.clash(n),
    [],
    Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(n), Spec.Res.code(m)),
    y => Spec.Work.set(y, Spec.Key.clash(n), [])
  )(y => Set.read(y, Spec.Key.clash(n), []))

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
          Spec.Node.get(s, h, Spec.Key.clash(n)),
          Some{[]},
          e
        ): {
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            _,
            Some{Spec.Clash.code(Ledgers.Id{w, q})}
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

# a key that a run sets in its log, it reads
def Add.reads.log(
  r: Spec.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Run.Keeps(k, x, Spec.Run.log(r, k, x)):
  match r:
    case Spec.Run{+s, Spec.Tip{c, +l}, +ns}:
      Run.of.keeps(
        k,
        x,
        c,
        Spec.Work.set(Spec.Work{s, l, ns}, k, x)
      )(Set.read(Spec.Work{s, l, ns}, k, x))

# Add.reads once the value m of the key in the log is known
def Add.reads.at(
  r: Spec.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Run.Keeps(k, x, Spec.Run.add.at(r, k, x, m)):
  match m:
    case Some{old}:
      Unit{}
    case None{}:
      Add.reads.log(r, k, x)

# a new key of the log of a run reads back
def Add.reads(
  +r: Spec.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> Run.Keeps(k, x, Spec.Run.add(r, k, x)):
  Add.reads.at(r, k, x, Spec.Node.get(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), k))

# a log that reads the outcome key of i as v holds an outcome of i
def Outs.of(
  i: Ledgers.Id,
  v: List<&2, U32>,
  +m: Maybe<&2, Spec.Run>
) -> Run.Keeps(Spec.Log.out(i), v, m) -> Spec.Run.Outs(m, i):
  match m:
    case None{}:
      h => Unit{}
    case Some{Spec.Run{s, t, ns}}:
      h =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(s, Spec.Tip.log(t), Spec.Log.out(i)),
          Some{v},
          h
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# each run that f gives has an outcome of i: so has the run after a step
def Outs.all(
  +m: Maybe<&2, Spec.Run>,
  -f: Spec.Run -> Maybe<&2, Spec.Run>,
  -i: Ledgers.Id,
  hf: @r: Spec.Run -> Spec.Run.Outs(f(r), i)
) -> Spec.Run.Outs(Maybe.bind(&2, Spec.Run, Spec.Run, m, f), i):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      hf(r)

# one of two runs, each with an outcome of i
def Outs.when(
  +b: Bool,
  -mx: Maybe<&2, Spec.Run>,
  -my: Maybe<&2, Spec.Run>,
  -i: Ledgers.Id,
  hx: Spec.Run.Outs(mx, i),
  hy: Spec.Run.Outs(my, i)
) -> Spec.Run.Outs(Shared.Bool.when(Maybe<&2, Spec.Run>, b, u => mx, u => my), i):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that is refused as stale has an outcome
def Stale.outs(+r: Spec.Run, +i: Ledgers.Id) -> Spec.Run.Outs(Spec.Step.stale(r, i), i):
  Outs.of(
    i,
    Spec.Out.words(Spec.Out.Stale{}),
    Spec.Run.add(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{}))
  )(Add.reads(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Stale{})))

# a request that is taken has an outcome
def Taken.outs(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> Spec.Run.Outs(Spec.Step.taken(r, i, own), i):
  +n = Spec.Line.count(Spec.Run.state(r), Spec.Run.tip(r))
  Outs.of(
    i,
    Spec.Out.words(Spec.Out.Taken{n}),
    Spec.Step.taken(r, i, own)
  )(
    Keeps.bind(
      Spec.Log.out(i),
      Spec.Out.words(Spec.Out.Taken{n}),
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
      Add.reads(r, Spec.Log.out(i), Spec.Out.words(Spec.Out.Taken{n}))
    )(
      +r1 => h1 => Keeps.bind(
        Spec.Log.out(i),
        Spec.Out.words(Spec.Out.Taken{n}),
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
          Spec.Log.out(i),
          Spec.Out.words(Spec.Out.Taken{n})
        )(h1)
      )(
        +r2 => h2 => Keeps.bind(
          Spec.Log.out(i),
          Spec.Out.words(Spec.Out.Taken{n}),
          Spec.Run.log(r2, Spec.Log.count(), [U32.inc(n)]),
          r3 => Spec.Run.owners(r3, own)
        )(
          Log.kept(
            r2,
            Spec.Log.count(),
            [U32.inc(n)],
            Spec.Log.out(i),
            Spec.Out.words(Spec.Out.Taken{n}),
            {==}
          )(h2)
        )(
          r3 => h3 => Owners.kept(
            r3,
            own,
            Spec.Log.out(i),
            Spec.Out.words(Spec.Out.Taken{n}),
            {==}
          )(h3)
        )
      )
    )
  )

# a judged request has an outcome
def Judged.outs(
  r: Spec.Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Spec.Verdict>
) -> Spec.Run.Outs(Spec.Step.judged(r, i, own, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Spec.Verdict{False{}, h, ds}}:
      Stale.outs(r, i)
    case Some{Spec.Verdict{True{}, h, ds}}:
      Outs.all(
        Spec.Run.content(r, h, ds),
        r2 => Spec.Step.taken(r2, i, own),
        i,
        r2 => Taken.outs(r2, i, own)
      )

# a mark on a version has an outcome
def Marked.outs(
  r: Spec.Run,
  i: Ledgers.Id,
  m: String,
  +v: Maybe<&2, Spec.Version>
) -> Spec.Run.Outs(Spec.Step.marked(r, i, m, v), i):
  match v:
    case None{}:
      Unit{}
    case Some{x}:
      Outs.all(
        Spec.Run.add(r, Spec.Log.mark(m), Ledgers.Id.code(Spec.Version.id(x), [])),
        r2 => Spec.Step.taken(r2, i, None{}),
        i,
        r2 => Taken.outs(r2, i, None{})
      )

# a request for a mark has an outcome
def Mark.outs(
  +r: Spec.Run,
  +i: Ledgers.Id,
  +m: String
) -> Spec.Run.Outs(Spec.Step.mark(r, i, m), i):
  +s = Spec.Run.state(r)
  +t = Spec.Run.tip(r)
  +n = Spec.Line.count(s, t)
  Outs.when(
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Spec.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Spec.Step.marked(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1))),
    Spec.Step.stale(r, i),
    i,
    Marked.outs(r, i, m, Spec.Line.version(s, t, U32.sub(n, 1))),
    Stale.outs(r, i)
  )

# the first tip of a new branch has an outcome
def Branch.made.outs(
  +r: Spec.Run,
  i: Ledgers.Id,
  b: String,
  +m: Maybe<&2, Spec.Made>
) -> Spec.Run.Outs(Spec.Branch.made(r, i, b, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Spec.Made{t, ds}}:
      Outs.all(
        Spec.Run.content(r, Spec.Tip.content(Spec.Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Spec.Run,
          Spec.Run,
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{})
        ),
        i,
        r1 => Outs.all(
          Spec.Run.add(r1, Spec.Log.start(b), Hashes.Hash.code(Spec.Tip.hash(t), [])),
          r2 => Spec.Step.taken(r2, i, None{}),
          i,
          r2 => Taken.outs(r2, i, None{})
        )
      )

# a request for a branch has an outcome, once it is known whether its version
# is one
def Branch.ready.outs(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  +m: Maybe<&2, Bool>
) -> Spec.Run.Outs(Spec.Branch.ready(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{False{}}:
      Stale.outs(r, i)
    case Some{True{}}:
      Outs.when(
        Trees.Tree.whole(
          ~Spec.State(),
          ~Spec.Store.fetch,
          Spec.Run.state(r),
          Spec.Node.root_of(Spec.Run.state(r), at)
        ),
        Spec.Branch.made(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          )
        ),
        None{},
        i,
        Branch.made.outs(
          r,
          i,
          b,
          Spec.Make.first(
            Spec.Make.branch(Spec.Run.state(r), Spec.Line.chain(st, Some{b}), at),
            Spec.Line.owners(Spec.Run.state(r), Spec.Run.tip(r))
          )
        ),
        Unit{}
      )

# a request for a branch has an outcome
def Branch.new.outs(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Spec.Run.Outs(Spec.Branch.new(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Stale.outs(r, i)
    case Some{None{}}:
      Branch.ready.outs(r, i, st, b, at, Spec.Judge.ready_maybe(Spec.Run.state(r), at))

# a change of a line has an outcome
def On.outs(
  +r: Spec.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Spec.Change
) -> Spec.Run.Outs(Spec.Step.on(r, i, st, l, ch), i):
  match l ch:
    case None{} Spec.Change.Branch{+a, b}:
      Branch.new.outs(
        r,
        i,
        st,
        a,
        b,
        Spec.Node.find(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), Spec.Log.start(a))
      )
    case None{} Spec.Change.Group{+a, +b}:
      Judged.outs(
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
    case None{} Spec.Change.Own{+a, +b, +c}:
      Judged.outs(
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
    case None{} Spec.Change.Write{+a, +b, +c}:
      Judged.outs(
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
    case None{} Spec.Change.Resolve{+a, +b, +c}:
      Judged.outs(
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
    case None{} Spec.Change.Merge{+a}:
      Judged.outs(
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
    case None{} Spec.Change.Move{+a}:
      Judged.outs(
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
    case None{} Spec.Change.Mark{+a, +b}:
      Judged.outs(
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
    case Some{x} Spec.Change.Branch{+a, +b}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Group{+a, +b}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Own{+a, +b, +c}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Write{+a, +b, +c}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Resolve{+a, +b, +c}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Merge{+a}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Move{+a}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Mark{a, b}:
      Mark.outs(r, i, a)
    case None{} Spec.Change.Key{+a, +b}:
      Judged.outs(
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
    case Some{+x} Spec.Change.Key{+a, +b}:
      Judged.outs(
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

# a request of a run has an outcome
def Change.outs(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Spec.Ask
) -> Spec.Run.Outs(Spec.Step.change(r, c, i, q), i):
  match q:
    case Spec.Ask.Start{os}:
      Stale.outs(r, i)
    case Spec.Ask.On{st, l, ch}:
      Outs.when(
        Ledgers.Chain.is_eq(Spec.Line.chain(st, l), c),
        Spec.Step.on(r, i, st, l, ch),
        Spec.Step.stale(r, i),
        i,
        On.outs(r, i, st, l, ch),
        Stale.outs(r, i)
      )

# a request that the node holds or not, of a run, has an outcome
def Asked.outs(
  r: Spec.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Spec.Ask>>
) -> Spec.Run.Outs(Spec.Step.asked(r, c, i, a), i):
  match a:
    case None{}:
      Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.outs(r, c, i, q)

# a run whose log reads the outcome key of i has an outcome of i
def Outs.self(
  +r: Spec.Run,
  i: Ledgers.Id,
  ws: List<&2, U32>
) -> {
  Spec.Node.get(
    Spec.Run.state(r),
    Spec.Tip.log(Spec.Run.tip(r)),
    Spec.Log.out(i)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
} -> Spec.Run.Outs(Some{r}, i):
  match r:
    case Spec.Run{s, t, ns}:
      eg =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Spec.Node.get(s, Spec.Tip.log(t), Spec.Log.out(i)),
          Some{ws},
          eg
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# One.outs once the outcome o that the words ws read as is known
def One.outs.read(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  ws: List<&2, U32>,
  +o: Maybe<&2, Spec.Out>,
  eg: {
    Spec.Node.get(
      Spec.Run.state(r),
      Spec.Tip.log(Spec.Run.tip(r)),
      Spec.Log.out(i)
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
) -> Spec.Run.Outs(Spec.Step.fresh(r, c, i, o), i):
  match o:
    case Some{x}:
      Outs.self(r, i, ws)(eg)
    case None{}:
      Asked.outs(r, c, i, Spec.Node.asked(Spec.Run.state(r), i))

# One.outs once what the log holds for the request is known (g)
def One.outs.at(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Spec.Node.get(
      Spec.Run.state(r),
      Spec.Tip.log(Spec.Run.tip(r)),
      Spec.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> Spec.Run.Outs(
  Spec.Step.fresh(r, c, i, Maybe.bind(&2, List<&2, U32>, Spec.Out, g, ws => Spec.Out.read(ws))),
  i
):
  match g:
    case None{}:
      Asked.outs(r, c, i, Spec.Node.asked(Spec.Run.state(r), i))
    case Some{+ws}:
      One.outs.read(r, c, i, ws, Spec.Out.read(ws), eg)

# a request has an outcome after its step
def One.outs(
  +r: Spec.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> Spec.Run.Outs(Spec.Step.one(r, c, i), i):
  One.outs.at(
    r,
    c,
    i,
    Spec.Node.get(Spec.Run.state(r), Spec.Tip.log(Spec.Run.tip(r)), Spec.Log.out(i)),
    {==}
  )

# no run gives no run
def All.none(
  c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>
) -> {Spec.Step.all(c, qs, None{}) == None{}: Maybe<&2, Spec.Run>}:
  match qs:
    case Nil{}:
      {==}
    case Con{i, rest}:
      All.none(c, rest)

# a run reads what its log holds
def Keeps.self(
  +r: Spec.Run,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Spec.Node.get(
    Spec.Run.state(r),
    Spec.Tip.log(Spec.Run.tip(r)),
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k, v, Some{r}):
  match r:
    case Spec.Run{s, t, ns}:
      e => e

# Outs.kept once what the log of the run holds for the request is known (g)
def Outs.kept.at(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +r: Spec.Run,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Spec.Node.get(
      Spec.Run.state(r),
      Spec.Tip.log(Spec.Run.tip(r)),
      Spec.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> {
  Maybe.is_some(&2, List<&2, U32>, g) == True{}: Bool
} -> Spec.Run.Outs(Spec.Step.all(c, qs, Some{r}), i):
  match g:
    case None{}:
      h => Empty.absurd(
        Spec.Run.Outs(Spec.Step.all(c, qs, Some{r}), i),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+v}:
      h => Outs.of(
        i,
        v,
        Spec.Step.all(c, qs, Some{r})
      )(
        All.kept(
          c,
          qs,
          Some{r},
          Spec.Log.out(i),
          v,
          {==},
          {==}
        )(Keeps.self(r, Spec.Log.out(i), v)(eg))
      )

# an outcome that a run has, it has after more requests
def Outs.kept(
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Spec.Run>,
  +i: Ledgers.Id
) -> Spec.Run.Outs(m, i) -> Spec.Run.Outs(Spec.Step.all(c, qs, m), i):
  match m:
    case None{}:
      h =>
        %Equal.sym(
          Maybe<&2, Spec.Run>,
          Spec.Step.all(c, qs, None{}),
          None{},
          All.none(c, qs)
        ): Spec.Run.Outs(_, i)
        Unit{}
    case Some{Spec.Run{s, t, ns}}:
      h => Outs.kept.at(
        c,
        qs,
        Spec.Run{s, t, ns},
        i,
        Spec.Node.get(s, Spec.Tip.log(t), Spec.Log.out(i)),
        {==}
      )(h)

# All.outs at the first request j, once it is known whether it is i
def All.outs.at(
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Spec.Run>,
  +i: Ledgers.Id,
  +same: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i) == True{}: Bool
  } -> Spec.Run.Outs(
    Spec.Step.all(c, rest, Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, j))),
    i
  )
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i), same) == True{}: Bool
} -> Spec.Run.Outs(
  Spec.Step.all(c, rest, Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, j))),
  i
):
  match same:
    case True{}:
      e => Outs.kept(
        c,
        rest,
        Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, j)),
        i
      )(
        %Equal.sym(Ledgers.Id, j, i, Ledgers.Id.is_eq_sound(j, i)(es)): Spec.Run.Outs(Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, _)), i)
        Outs.all(m, r => Spec.Step.one(r, c, i), i, r => One.outs(r, c, i)))
    case False{}:
      e => ih(e)

# each request of a step has an outcome after it
def All.outs(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Spec.Run>,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool
} -> Spec.Run.Outs(Spec.Step.all(c, qs, m), i):
  match qs:
    case Nil{}:
      e => Empty.absurd(Spec.Run.Outs(m, i), Shared.Bool.false_ne_true(e))
    case Con{j, rest}:
      All.outs.at(
        c,
        j,
        rest,
        m,
        i,
        Ledgers.Id.is_eq(j, i),
        {==},
        All.outs(c, rest, Maybe.bind(&2, Spec.Run, Spec.Run, m, r => Spec.Step.one(r, c, j)), i)
      )

def Spec.Step.run_outs(s, c, t, qs, i):
  All.outs(c, qs, Some{Spec.Run{s, t, []}}, i)

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
        Spec.Wait.left(rs, done),
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
  s: Spec.State(),
  c: Ledgers.Chain,
  t: Spec.Tip,
  th: Maybe<&2, Hashes.Hash>,
  v: Ledgers.Vote,
  from: List<&2, String>,
  b: Bool
) -> {
  Maybe.is_some(
    &2,
    Spec.Run,
    Spec.Plan.run(
      Shared.Bool.when(
        Spec.Plan,
        b,
        u => Spec.Plan.copy(s, c, t, th, Some{v}, from),
        u => Spec.Plan{[], None{}, []}
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
  Follow.allowed.at(s, c, t, th, v, from, Spec.Allowed(s, w, os, v, from))

# Waits
# -----
# A request that a node takes in waits on its line: a pending write goes with
# its writer to another node (Spec.Node.take_waits).

# a new ledger keeps the waiting requests
def Waiting.led(
  s: Spec.State(),
  l: Ledgers.State(Spec.Ask)
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.State.led(s, l)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Spec.Node{old, hs, ws, ks}:
      {==}

# new keys keep the waiting requests
def Waiting.keyed(
  s: Spec.State(),
  ks: Spec.Keys
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.State.keyed(s, ks)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Spec.Node{l, hs, ws, old}:
      {==}

# the waiting requests of the node m, if any, else of s
def Waiting.of(s: Spec.State(), m: Maybe<&2, Spec.State()>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match m:
    case None{}:
      Spec.State.waiting(s)
    case Some{s2}:
      Spec.State.waiting(s2)

# a node that is kept when b holds has the waiting requests of s, when it has
def Waiting.some.if(
  b: Bool,
  -s: Spec.State(),
  -x: Spec.State(),
  hx: {Spec.State.waiting(s) == Spec.State.waiting(x): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {
  Spec.State.waiting(
    s
  )
    == Waiting.of(
      s,
      Shared.Maybe.when(Spec.State(), b, u => Some{x})
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the waiting requests
def Accept.at.waiting(
  +s: Spec.State(),
  +b: Ledgers.Ballot,
  m: Maybe<&2, Spec.Chained>
) -> {
  Spec.State.waiting(
    s
  )
    == Waiting.of(s, Spec.Seal.accept.at(s, b, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Waiting.some.if(
        Spec.Seal.fits(c, b),
        s,
        Spec.State.keyed(
          Spec.State.led(
            s,
            Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
          ),
          Spec.Keys.saw(
            Spec.Keys.set(
              Spec.State.keys(s),
              Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
              Spec.Chained.next(c, b)
            ),
            Spec.Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<List<&2, Ledgers.Id>>,
          Spec.State.waiting(s),
          Spec.State.waiting(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            )
          ),
          Spec.State.waiting(
            Spec.State.keyed(
              Spec.State.led(
                s,
                Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
              ),
              Spec.Keys.saw(
                Spec.Keys.set(
                  Spec.State.keys(s),
                  Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                  Spec.Chained.next(c, b)
                ),
                Spec.Ballot.at(b)
              )
            )
          ),
          Waiting.led(s, Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)),
          Waiting.keyed(
            Spec.State.led(
              s,
              Ledgers.State.keep(~Spec.Ask, ~Spec.Ask.is_eq, Spec.State.ledger(s), b)
            ),
            Spec.Keys.saw(
              Spec.Keys.set(
                Spec.State.keys(s),
                Spec.Seal.slot(Spec.Ballot.store(b), Spec.Ballot.node(b)),
                Spec.Chained.next(c, b)
              ),
              Spec.Ballot.at(b)
            )
          )
        )
      )

# the ballots that a chain leads to keep the waiting requests, when each one more does
def Follow.step.waiting(
  -s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  -k: Spec.State() -> Spec.State(),
  ih: @s2: Spec.State() -> {
    Spec.State.waiting(s2) == Spec.State.waiting(k(s2)): Tries.Trie<List<&2, Ledgers.Id>>
  }
) -> {
  Spec.State.waiting(s) == Waiting.of(s, m): Tries.Trie<List<&2, Ledgers.Id>>
} -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(
      Maybe.default(
        &2,
        Spec.State(),
        Maybe.bind(&2, Spec.State(), Spec.State(), m, s2 => Some{k(s2)}),
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
        Spec.State.waiting(s),
        Spec.State.waiting(s2),
        Spec.State.waiting(k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the waiting requests
def Follow.waiting(
  f: Nat,
  +s: Spec.State(),
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Sealed.follow(f, s, p, r, n, mb)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.waiting(
        s,
        Spec.Seal.accept(s, b),
        +s2 => Spec.Sealed.follow(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n)),
        +s2 => Follow.waiting(g, s2, p, r, n, Spec.Pending.next(s2, p, r, n))
      )(Accept.at.waiting(s, b, Spec.Seal.chain(s, Spec.Ballot.store(b), Spec.Ballot.node(b))))

# the ballots that the chains of some ballots lead to keep the waiting requests
def Each.waiting(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Spec.State()
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Sealed.each(f, bs, p, s)): Tries.Trie<List<&2, Ledgers.Id>>
}:
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
        Tries.Trie<List<&2, Ledgers.Id>>,
        Spec.State.waiting(s),
        Spec.State.waiting(s1),
        Spec.State.waiting(Spec.Sealed.each(f, rest, p, s1)),
        Follow.waiting(
          f,
          s,
          p,
          Spec.Ballot.store(b),
          Spec.Ballot.node(b),
          Spec.Pending.next(s, p, Spec.Ballot.store(b), Spec.Ballot.node(b))
        ),
        Each.waiting(f, rest, p, s1)
      )

# a new head keeps the waiting requests
def Waiting.head(
  +s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.State.head(s, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Spec.Node{l, hs, ws, ks}:
      {==}

# a first head keeps the waiting requests
def First.at.waiting(
  s: Spec.State(),
  c: Ledgers.Chain,
  h: Spec.Head,
  +m: Maybe<&2, Spec.Head>
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.First.at(s, c, h, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{Spec.Head{r, b, n, Some{t}}}:
      {==}
    case Some{Spec.Head{r, b, n, None{}}}:
      Waiting.head(s, c, h)
    case None{}:
      Waiting.head(s, c, h)

# the first head of a store keeps the waiting requests
def Start.head.waiting(
  +s: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  h: Spec.Head
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Start.head(s, m, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+s2}:
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Spec.State.waiting(s),
        Spec.State.waiting(Spec.State.led(s, Spec.State.ledger(s2))),
        Spec.State.waiting(Spec.State.first(Spec.State.led(s, Spec.State.ledger(s2)), c, h)),
        Waiting.led(s, Spec.State.ledger(s2)),
        First.at.waiting(
          Spec.State.led(s, Spec.State.ledger(s2)),
          c,
          h,
          Spec.Node.head_of(Spec.State.led(s, Spec.State.ledger(s2)), c)
        )
      )

# the first tip of a store keeps the waiting requests
def Start.put.waiting(
  s: Spec.State(),
  +i: Ledgers.Id,
  +c: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Spec.Work>
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Start.put(s, i, c, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{Spec.Work{s2, +l, ns}}:
      Start.head.waiting(
        s,
        Spec.State.put(s2, [Spec.Tip.words(Spec.Tip{c, l})]),
        Ledgers.Chain{i, None{}},
        Spec.Head{i, None{}, 0, Some{Spec.Tip.hash(Spec.Tip{c, l})}}
      )

# a store that starts keeps the waiting requests
def Start.with.waiting(
  s: Spec.State(),
  i: Ledgers.Id,
  os: List<&2, String>,
  +m: Maybe<&2, Spec.Work>
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Start.with(s, i, os, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      Start.put.waiting(s, i, Spec.Work.root(w), Spec.Log.first(w, os))

# a line that a node starts to follow keeps the waiting requests
def Follow.new.waiting(
  s: Spec.State(),
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +m: Maybe<&2, Spec.Head>
) -> {
  Spec.State.waiting(
    s
  )
    == Spec.State.waiting(Spec.Follow.new(s, r, l, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{h}:
      {==}
    case None{}:
      Waiting.head(s, Spec.Line.chain(r, l), Spec.Head{r, l, 0, None{}})

# nodes with the same waiting requests have the same ones on each line
def Wait.same(
  a: Spec.State(),
  b: Spec.State(),
  c: Ledgers.Chain,
  e: {Spec.State.waiting(a) == Spec.State.waiting(b): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {Spec.Wait.of(a, c) == Spec.Wait.of(b, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    Tries.Trie<List<&2, Ledgers.Id>>,
    List<&2, Ledgers.Id>,
    ws => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c)),
      []
    ),
    Spec.State.waiting(a),
    Spec.State.waiting(b),
    e
  )

# lines with the same key have the same waiting requests
def Wait.keyed(
  s: Spec.State(),
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Spec.Wait.of(s, c2) == Spec.Wait.of(s, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    List<&2, Bool>,
    List<&2, Ledgers.Id>,
    kk => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, Spec.State.waiting(s), kk),
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +r: List<&2, Ledgers.Id>,
  +c2: Ledgers.Chain
) -> {
  Spec.Wait.of(
    Spec.Wait.set(s, c, x <> r),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      x <> r,
      Spec.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  match s:
    case Spec.Node{l, hs, +ws, ks}:
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
  s: Spec.State(),
  c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain,
  +ys: List<&2, Ledgers.Id>
) -> {
  Spec.Wait.of(
    Spec.Wait.set(s, c, List.append(&2, Ledgers.Id, ys, [j])),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, ys, [j]),
      Spec.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  match ys:
    case Nil{}:
      Wait.set.of(s, c, j, [], c2)
    case Con{x, r}:
      Wait.set.of(s, c, x, List.append(&2, Ledgers.Id, r, [j]), c2)

# the requests that wait on a line, after one more waits on the line c
def Wait.wait(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain
) -> {
  Spec.Wait.of(
    Spec.State.wait(s, c, j),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Spec.Wait.of(s, c), [j]),
      Spec.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  Wait.wait.at(s, c, j, c2, Spec.Wait.of(s, c))

# Wait.keeps once it is known whether the line has the key of c (b)
def Wait.keeps.if(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  +b: Bool,
  eb: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == b: Bool},
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      List.append(&2, Ledgers.Id, Spec.Wait.of(s, c), [j]),
      Spec.Wait.of(s, c2)
    ),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_left(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(s, c), [j], i, (
          %Wait.keyed(s, c2, c, Key.same(c2, c)(eb)): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))
    case False{}:
      h

# a request that waits on a line waits there after one more waits on a line
def Wait.keeps(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(Spec.State.wait(s, c, j), c2),
    i
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Spec.Wait.of(Spec.State.wait(s, c, j), c2),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Spec.Wait.of(s, c), [j]),
      Spec.Wait.of(s, c2)
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
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +j: Ledgers.Id
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(Spec.State.wait(s, c, j), c),
    j
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Spec.Wait.of(Spec.State.wait(s, c, j), c),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Spec.Wait.of(s, c), [j]),
      Spec.Wait.of(s, c)
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
        List.append(&2, Ledgers.Id, Spec.Wait.of(s, c), [j]),
        Spec.Wait.of(s, c)
      ),
      j
    )
      == True{}: Bool
  }
  Shared.List.contains_right(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(s, c),
    [j],
    j,
    Contains.one(j)
  )

# a request that waits on a line waits there after a request arrives
def Arrive.waits(
  +s: Spec.State(),
  +j: Ledgers.Id,
  +q: Spec.Ask,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(Spec.Node.arrive(s, j, q), c2),
    i
  )
    == True{}: Bool
}:
  match q:
    case Spec.Ask.Start{os}:
      %Wait.same(
        s,
        Spec.Node.start(s, j, os),
        c2,
        Start.with.waiting(
          s,
          j,
          Spec.Owner.names(os),
          Spec.Seal.firsts(os, Some{Spec.Work{s, None{}, []}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Spec.Ask.On{r, l, ch}:
      Wait.keeps(Spec.Node.follow(s, r, l), Spec.Line.chain(r, l), j, c2, i, (
          %Wait.same(s, Spec.Node.follow(s, r, l), c2, Follow.new.waiting(s, r, l, Spec.Node.head_of(s, Spec.Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

# one of two nodes, on each of which the request i waits on the line c2
def Contains.when(
  +b: Bool,
  -x: Spec.State(),
  -y: Spec.State(),
  -c2: Ledgers.Chain,
  -i: Ledgers.Id,
  hx: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(x, c2), i) == True{}: Bool},
  hy: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(y, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(Shared.Bool.when(Spec.State(), b, u => x, u => y), c2),
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
  +cs: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State(),
  +c2: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(s, c2), i) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(Spec.Take.asks(cs, old, s), c2),
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
          Spec.State(),
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Spec.Node.arrive(s, j, q),
          u => s
        ),
        c2,
        i
      )(
        Contains.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(j))
          ),
          Spec.Node.arrive(s, j, q),
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
  +pre: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  post: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State(),
  +i: Ledgers.Id,
  time: String,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  ch: Spec.Change
) -> {
  Ledgers.State.get(
    ~Spec.Ask,
    old,
    Ledgers.Slot.ask(i)
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Spec.Wait.of(
      Spec.Take.asks(
        List.append(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          pre,
          Cells.One{Ledgers.Entry.Ask{i, time, Spec.Ask.On{r, l, ch}}} <> post
        ),
        old,
        s
      ),
      Spec.Line.chain(r, l)
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
          Spec.State(),
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
          ),
          u => Spec.Node.arrive(s, i, Spec.Ask.On{r, l, ch}),
          u => s
        ),
        Spec.Line.chain(r, l),
        i
      )(
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i)), None{}, e): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Spec.Wait.of(Shared.Bool.when(Spec.State(), Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _), u => Spec.Node.arrive(s, i, Spec.Ask.On{r, l, ch}), u => s), Spec.Line.chain(r, l)), i) == True{}: Bool}
        Wait.adds(Spec.Node.follow(s, r, l), Spec.Line.chain(r, l), i))
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      e => Take.asks.adds(
        rest,
        post,
        old,
        Shared.Bool.when(
          Spec.State(),
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Spec.Node.arrive(s, j, q),
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
  +sent = Spec.Node.reads(t)
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  es => eb =>
    Ledgers.State.one_grows(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      Spec.State.ledger(Spec.State.led(s, l1)),
      Spec.State.ledger(Spec.Node.take(s, t)),
      k,
      e
    )(Take.tail(s, t))(
      %Equal.sym(Ledgers.State(Spec.Ask), Spec.State.ledger(Spec.State.led(s, l1)), l1, Led.led(s, l1)): {Ledgers.State.get(~Spec.Ask, _, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
      Equal.trans(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, Ledgers.State.get(~Spec.Ask, l1, k), Ledgers.State.get(~Spec.Ask, sent, k), Some{Cells.One{e}}, Ledgers.State.take_get(~Spec.Ask, Spec.State.ledger(s), sent, k)(eb), es))

def Spec.Node.take_waits(s, t, i, time, r, l, ch):
  +sent = Spec.Node.reads(t)
  l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  cell = {
    Cells.One{
      Ledgers.Entry.Ask{i, time, Spec.Ask.On{r, l, ch}}
    }: Cells.Cell<Ledgers.Entry<Spec.Ask>>
  }
  es => eb =>
    %Wait.same(
      s2,
      Spec.Sealed.take(bs, s2),
      Spec.Line.chain(r, l),
      Each.waiting(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2)
    ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
    %Equal.sym(
      List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
      cs,
      List.append(
        &2,
        Cells.Cell<Ledgers.Entry<Spec.Ask>>,
        Tries.Trie.before(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent, Ledgers.Slot.ask(i)),
        cell <> Tries.Trie.after(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent, Ledgers.Slot.ask(i))
      ),
      Tries.Trie.values_around(
        Cells.Cell<Ledgers.Entry<Spec.Ask>>,
        sent,
        Ledgers.Slot.ask(i),
        cell
      )(es)
    ): {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Spec.Wait.of(Spec.Take.asks(_, Spec.State.ledger(s), s1), Spec.Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }
    Take.asks.adds(
      Tries.Trie.before(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent, Ledgers.Slot.ask(i)),
      Tries.Trie.after(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent, Ledgers.Slot.ask(i)),
      Spec.State.ledger(s),
      s1,
      i,
      time,
      r,
      l,
      ch
    )(eb)

# Paths
# -----
# Every head is on the decided chain. A node sets a head in four places: a
# step that it checked (Advance.moved), and three that set only a head with no
# tip (Open.at, First.at, Follow.new). So a head that is some decided steps
# from a head with a tip stays so, one more step at a time, whatever the node
# does (Spec.Node.after_on).

# a head one height up has a tip
def Up.held(
  z: Spec.Head,
  y: Hashes.Hash
) -> {Spec.Head.held(Some{Spec.Head.up(z, y)}) == True{}: Bool}:
  match z:
    case Spec.Head{r, b, n, th}:
      {==}

# Moved.held once the tip m that the step names is known
def Moved.held.at(
  z: Spec.Head,
  m: Maybe<&2, Hashes.Hash>,
  -h: Spec.Head
) -> {
  Maybe.bind(
    &2,
    Hashes.Hash,
    Spec.Head,
    m,
    y => Some{Spec.Head.up(z, y)}
  )
    == Some{h}: Maybe<&2, Spec.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Spec.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Head, h, e)
      )
    case Some{y}:
      e =>
        %e: {Spec.Head.held(_) == True{}: Bool}
        Up.held(z, y)

# a head that a step moved has a tip
def Moved.held(
  z: Spec.Head,
  va: Maybe<&2, Ledgers.Vote>,
  -h: Spec.Head
) -> {
  Spec.Head.moved(z, va) == Some{h}: Maybe<&2, Spec.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  Moved.held.at(z, Spec.Vote.tip(va), h)

# Held.at for one more step, once the head m before it is known
def Held.at.step(
  s: Spec.State(),
  c: Ledgers.Chain,
  r: Nat,
  -h: Spec.Head,
  m: Maybe<&2, Spec.Head>
) -> {
  Maybe.bind(
    &2,
    Spec.Head,
    Spec.Head,
    m,
    +x => Spec.Head.moved(x, Spec.Advance.in(s, c, x, r))
  )
    == Some{h}: Maybe<&2, Spec.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Spec.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Head, h, e)
      )
    case Some{+z}:
      e => Moved.held(z, Spec.Advance.in(s, c, z, r), h)(e)

# a head that is some decided steps from a head with a tip has a tip
def Held.at(
  rs: List<&2, Nat>,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h0: Spec.Head,
  -h: Spec.Head
) -> {
  Spec.Head.held(Some{h0}) == True{}: Bool
} -> {
  Spec.Line.at(rs, s, c, h0) == Some{h}: Maybe<&2, Spec.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match rs:
    case Nil{}:
      t0 => e =>
        %e: {Spec.Head.held(_) == True{}: Bool}
        t0
    case Con{r, rest}:
      t0 => e => Held.at.step(s, c, r, h, Spec.Line.at(rest, s, c, h0))(e)

# a node is on its own paths
def Path.refl(-s: Spec.State()) -> Spec.Node.On(s, s):
  c => h0 => t0 => ra => ra

# paths compose
def Path.trans(
  -a: Spec.State(),
  -b: Spec.State(),
  -d: Spec.State(),
  h1: Spec.Node.On(a, b),
  h2: Spec.Node.On(b, d)
) -> Spec.Node.On(a, d):
  +c => +h0 => +t0 => ra => h2(c)(h0)(t0)(h1(c)(h0)(t0)(ra))

# one of two nodes, each on the paths of s
def Path.when(
  b: Bool,
  -s: Spec.State(),
  -x: Spec.State(),
  -y: Spec.State(),
  hx: Spec.Node.On(s, x),
  hy: Spec.Node.On(s, y)
) -> Spec.Node.On(s, Shared.Bool.when(Spec.State(), b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a line whose head is the same in a node that grew is where it was
def Reach.same(
  a: Spec.State(),
  b: Spec.State(),
  c: Ledgers.Chain,
  h0: Spec.Head,
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  eh: {Spec.Node.head_of(a, c) == Spec.Node.head_of(b, c): Maybe<&2, Spec.Head>},
  ra: Spec.Line.Reach(a, c, h0)
) -> Spec.Line.Reach(b, c, h0):
  match ra:
    case Tuple{+rs, Tuple{+h, Tuple{e1, e2}}}:
      Tuple{
        rs,
        Tuple{
          h,
          Tuple{
            Equal.trans(
              Maybe<&2, Spec.Head>,
              Spec.Node.head_of(b, c),
              Spec.Node.head_of(a, c),
              Some{h},
              Equal.sym(Maybe<&2, Spec.Head>, Spec.Node.head_of(a, c), Spec.Node.head_of(b, c), eh),
              e1
            ),
            Spec.Line.at_grows(rs, a, b, c, h0, h)(g)(e2)
          }
        }
      }

# a node that grew, with the same heads, is on the paths
def Path.same(
  a: Spec.State(),
  b: Spec.State(),
  g: {Spec.Node.grows(a, b) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b): Tries.Trie<Spec.Head>}
) -> Spec.Node.On(a, b):
  +c => +h0 => t0 => ra => Reach.same(
    a,
    b,
    c,
    h0,
    g,
    Equal.cong(
      Tries.Trie<Spec.Head>,
      Maybe<&2, Spec.Head>,
      hs => Tries.Trie.get(Spec.Head, hs, Ledgers.Chain.key(c)),
      Spec.State.heads(a),
      Spec.State.heads(b),
      eh
    ),
    ra
  )

# the head of another line, after the head of the line c is set
def Head.other(
  a: Spec.State(),
  b0: Spec.State(),
  c: Ledgers.Chain,
  hd: Spec.Head,
  c2: Ledgers.Chain,
  eh: {Spec.State.heads(a) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == False{}: Bool}
) -> {
  Spec.Node.head_of(
    a,
    c2
  )
    == Spec.Node.head_of(Spec.State.head(b0, c, hd), c2): Maybe<&2, Spec.Head>
}:
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

# the head of a line with the key of the line c, after the head of c is set
def Head.this(
  b0: Spec.State(),
  c: Ledgers.Chain,
  hd: Spec.Head,
  c2: Ledgers.Chain,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool}
) -> {Spec.Node.head_of(Spec.State.head(b0, c, hd), c2) == Some{hd}: Maybe<&2, Spec.Head>}:
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

# lines with the same key have the same head
def Head.keyed(
  a: Spec.State(),
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Spec.Node.head_of(a, c2) == Spec.Node.head_of(a, c): Maybe<&2, Spec.Head>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Spec.Head>,
    kk => Tries.Trie.get(Spec.Head, Spec.State.heads(a), kk),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# lines with the same key have the same decided steps
def In.key(
  s: Spec.State(),
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  x: Spec.Head,
  r: Nat,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Spec.Advance.in(s, c2, x, r) == Spec.Advance.in(s, c, x, r): Maybe<&2, Ledgers.Vote>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Ledgers.Vote>,
    kk => Maybe.bind(
      &2,
      Spec.Tip,
      Ledgers.Vote,
      Spec.Head.tip(s, x),
      t => Ledgers.Bucket.decide(
        ~Spec.Ask,
        Ledgers.State.under(
          ~Spec.Ask,
          Spec.State.ledger(s),
          List.append(
            &2,
            Bool,
            List.append(&2, Bool, False{} <> True{} <> kk, Ledgers.Word.key(Spec.Head.next(x))),
            Ledgers.Round.key(r, [False{}])
          )
        ),
        Spec.Line.owners(s, t)
      )
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# no line with the key of c is some decided steps from a head with a tip, when
# the head of c has no tip
def Path.set.no(
  +a: Spec.State(),
  c: Ledgers.Chain,
  +c2: Ledgers.Chain,
  h0: Spec.Head,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  nh: {Spec.Head.held(Spec.Node.head_of(a, c)) == False{}: Bool},
  t0: {Spec.Head.held(Some{h0}) == True{}: Bool},
  ra: Spec.Line.Reach(a, c2, h0)
) -> Empty:
  match ra:
    case Tuple{rs, Tuple{h, Tuple{e1, e2}}}:
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Spec.Head.held(Spec.Node.head_of(a, c)),
          True{},
          Equal.sym(Bool, Spec.Head.held(Spec.Node.head_of(a, c)), False{}, nh),
          Equal.trans(
            Bool,
            Spec.Head.held(Spec.Node.head_of(a, c)),
            Spec.Head.held(Some{h}),
            True{},
            Equal.cong(
              Maybe<&2, Spec.Head>,
              Bool,
              Spec.Head.held,
              Spec.Node.head_of(a, c),
              Some{h},
              Equal.trans(
                Maybe<&2, Spec.Head>,
                Spec.Node.head_of(a, c),
                Spec.Node.head_of(a, c2),
                Some{h},
                Equal.sym(
                  Maybe<&2, Spec.Head>,
                  Spec.Node.head_of(a, c2),
                  Spec.Node.head_of(a, c),
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
  +a: Spec.State(),
  +b0: Spec.State(),
  +c: Ledgers.Chain,
  +hd: Spec.Head,
  +c2: Ledgers.Chain,
  h0: Spec.Head,
  bs: Bool,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Spec.Node.grows(a, b0) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  nh: {Spec.Head.held(Spec.Node.head_of(a, c)) == False{}: Bool},
  t0: {Spec.Head.held(Some{h0}) == True{}: Bool},
  ra: Spec.Line.Reach(a, c2, h0)
) -> Spec.Line.Reach(Spec.State.head(b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Empty.absurd(
        Spec.Line.Reach(Spec.State.head(b0, c, hd), c2, h0),
        Path.set.no(a, c, c2, h0, Key.same(c2, c)(ebs), nh, t0, ra)
      )
    case False{}:
      Reach.same(
        a,
        Spec.State.head(b0, c, hd),
        c2,
        h0,
        Grows.to(a, b0, Spec.State.head(b0, c, hd), Led.head(b0, c, hd), g),
        Head.other(a, b0, c, hd, c2, eh, ebs),
        ra
      )

# a node b0 with a new head hd of the line c is on the paths of a, when b0
# grew from a with the same heads, and the head of c in a has no tip
def Path.set(
  a: Spec.State(),
  b0: Spec.State(),
  +c: Ledgers.Chain,
  hd: Spec.Head,
  g: {Spec.Node.grows(a, b0) == True{}: Bool},
  eh: {Spec.State.heads(a) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  nh: {Spec.Head.held(Spec.Node.head_of(a, c)) == False{}: Bool}
) -> Spec.Node.On(a, Spec.State.head(b0, c, hd)):
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
  +s: Spec.State(),
  +n: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  hd: Spec.Head,
  +q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Spec.Head,
  +ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  +gn: {Spec.Node.grows(s, n) == True{}: Bool},
  en: {Spec.Node.head_of(n, c2) == Some{hd}: Maybe<&2, Spec.Head>},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Spec.Head>},
  ra: Spec.Line.Reach(s, c2, h0)
) -> Spec.Line.Reach(n, c2, h0):
  match ra:
    case Tuple{+rs, Tuple{h2, Tuple{e1, e2}}}:
      Tuple{
        q <> rs,
        Tuple{
          hd,
          Tuple{
            en,
            Equal.trans(
              Maybe<&2, Spec.Head>,
              Spec.Line.at(q <> rs, n, c2, h0),
              Spec.Head.moved(h2, Spec.Advance.in(n, c2, h2, q)),
              Some{hd},
              Equal.cong(
                Maybe<&2, Spec.Head>,
                Maybe<&2, Spec.Head>,
                m => Maybe.bind(
                  &2,
                  Spec.Head,
                  Spec.Head,
                  m,
                  +z => Spec.Head.moved(z, Spec.Advance.in(n, c2, z, q))
                ),
                Spec.Line.at(rs, n, c2, h0),
                Some{h2},
                Spec.Line.at_grows(rs, s, n, c2, h0, h2)(gn)(e2)
              ),
              Equal.trans(
                Maybe<&2, Spec.Head>,
                Spec.Head.moved(h2, Spec.Advance.in(n, c2, h2, q)),
                Spec.Head.moved(h, Spec.Advance.in(n, c2, h, q)),
                Some{hd},
                Equal.cong(
                  Spec.Head,
                  Maybe<&2, Spec.Head>,
                  +z => Spec.Head.moved(z, Spec.Advance.in(n, c2, z, q)),
                  h2,
                  h,
                  Shared.Maybe.some_inj(
                    Spec.Head,
                    h2,
                    h,
                    Equal.trans(
                      Maybe<&2, Spec.Head>,
                      Some{h2},
                      Spec.Node.head_of(s, c2),
                      Some{h},
                      Equal.sym(Maybe<&2, Spec.Head>, Spec.Node.head_of(s, c2), Some{h2}, e1),
                      Equal.trans(
                        Maybe<&2, Spec.Head>,
                        Spec.Node.head_of(s, c2),
                        Spec.Node.head_of(s, c),
                        Some{h},
                        Head.keyed(s, c2, c, ek),
                        em
                      )
                    )
                  )
                ),
                Equal.trans(
                  Maybe<&2, Spec.Head>,
                  Spec.Head.moved(h, Spec.Advance.in(n, c2, h, q)),
                  Spec.Head.moved(h, Some{v}),
                  Some{hd},
                  Equal.cong(
                    Maybe<&2, Ledgers.Vote>,
                    Maybe<&2, Spec.Head>,
                    w => Spec.Head.moved(h, w),
                    Spec.Advance.in(n, c2, h, q),
                    Some{v},
                    Equal.trans(
                      Maybe<&2, Ledgers.Vote>,
                      Spec.Advance.in(n, c2, h, q),
                      Spec.Advance.in(n, c, h, q),
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
  +s: Spec.State(),
  +b0: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  +hd: Spec.Head,
  q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Spec.Head,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Spec.Node.grows(s, b0) == True{}: Bool},
  eh: {Spec.State.heads(s) == Spec.State.heads(b0): Tries.Trie<Spec.Head>},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Spec.Head>},
  ra: Spec.Line.Reach(s, c2, h0)
) -> Spec.Line.Reach(Spec.State.head(b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Path.moved.yes(
        s,
        Spec.State.head(b0, c, hd),
        c,
        h,
        hd,
        q,
        v,
        c2,
        h0,
        Key.same(c2, c)(ebs),
        Grows.to(s, b0, Spec.State.head(b0, c, hd), Led.head(b0, c, hd), g),
        Head.this(b0, c, hd, c2, ebs),
        em,
        ein,
        emv,
        ra
      )
    case False{}:
      Reach.same(
        s,
        Spec.State.head(b0, c, hd),
        c2,
        h0,
        Grows.to(s, b0, Spec.State.head(b0, c, hd), Led.head(b0, c, hd), g),
        Head.other(s, b0, c, hd, c2, eh, ebs),
        ra
      )

# a head moved over the step v that the owners decided at it, in the round
# q, is one more decided step on its path
def Path.moved(
  +s: Spec.State(),
  +s3: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  hd: Spec.Head,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g3: {Spec.Node.grows(s, s3) == True{}: Bool},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Spec.Head>}
) -> Spec.Node.On(s, Spec.State.moved(Spec.State.led(s, Spec.State.ledger(s3)), c, hd, qs)):
  +x = Spec.State.led(s, Spec.State.ledger(s3))
  +ws = Spec.Wait.left(
    Spec.Wait.of(x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Spec.Wait.set(x, c, ws)
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
      Tries.Trie<Spec.Head>,
      Spec.State.heads(s),
      Spec.State.heads(x),
      Spec.State.heads(b0),
      Heads.led(s, Spec.State.ledger(s3)),
      Heads.wait(x, c, ws)
    ),
    em,
    ein,
    emv,
    ra
  )

# Advance.moved is on the paths, once the node m that the put gives is known
def Advance.moved.path(
  +s: Spec.State(),
  +s2: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  c: Ledgers.Chain,
  h: Spec.Head,
  hd: Spec.Head,
  t2: Spec.Tip,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g2: {Spec.Node.grows(s, s2) == True{}: Bool},
  em: {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Spec.Head>}
) -> {
  Spec.State.put(s2, [Spec.Tip.words(t2)]) == m: Maybe<&2, Spec.State()>
} -> Spec.Node.On(s, Spec.Advance.moved(s, m, c, hd, qs)):
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
        Grows.trans(s, s2, s3)(g2)(Put.grew(s2, [Spec.Tip.words(t2)], s3, e2)),
        em,
        ein,
        emv
      )

# Advance.ran is on the paths, once it is known whether the run gives the tip
# that the step names (bq)
def Advance.ran.path.if(
  s: Spec.State(),
  +s2: Spec.State(),
  +t2: Spec.Tip,
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
  ebq: {Spec.Root.same(after, Some{Spec.Tip.hash(t2)}) == bq: Bool},
  g2: {Spec.Node.grows(s, s2) == True{}: Bool},
  em: {Spec.Node.head_of(s, c) == Some{Spec.Head{r, br, next, th}}: Maybe<&2, Spec.Head>},
  ein: {
    Spec.Advance.in(
      s,
      c,
      Spec.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> Spec.Node.On(
  s,
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
  )
):
  match bq:
    case True{}:
      Advance.moved.path(
        s,
        s2,
        Spec.State.put(s2, [Spec.Tip.words(t2)]),
        c,
        Spec.Head{r, br, next, th},
        Spec.Head{r, br, U32.inc(next), Some{Spec.Tip.hash(t2)}},
        t2,
        qs,
        q,
        Ledgers.Vote{before, qs, after},
        g2,
        em,
        ein,
        Equal.cong(
          Maybe<&2, Hashes.Hash>,
          Maybe<&2, Spec.Head>,
          a => Maybe.bind(
            &2,
            Hashes.Hash,
            Spec.Head,
            a,
            y => Some{Spec.Head.up(Spec.Head{r, br, next, th}, y)}
          ),
          after,
          Some{Spec.Tip.hash(t2)},
          Shared.Maybe.is_eq_sound(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Hashes.Hash.is_eq_sound,
            after,
            Some{Spec.Tip.hash(t2)}
          )(ebq)
        )
      )({==})
    case False{}:
      Path.refl(s)

# a checked step is on the paths
def Advance.ran.path(
  s: Spec.State(),
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Spec.Run>,
  q: Nat,
  em: {Spec.Node.head_of(s, c) == Some{Spec.Head{r, br, next, th}}: Maybe<&2, Spec.Head>},
  ein: {
    Spec.Advance.in(
      s,
      c,
      Spec.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> {
  Run.after(s, m) == True{}: Bool
} -> Spec.Node.On(s, Spec.Advance.ran(s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => Path.refl(s)
    case Some{Spec.Run{s2, +t2, ns}}:
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
        Spec.Root.same(after, Some{Spec.Tip.hash(t2)}),
        {==},
        ga,
        em,
        ein
      )

# Node.advance is on the paths, once the decided step m is known
def Advance.step.path(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  +t: Spec.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>}
  -> {Spec.Head.tip(s, h) == Some{t}: Maybe<&2, Spec.Tip>}
  -> {
    Spec.Height.decide(
      s,
      c,
      Spec.Head.next(h),
      Spec.Line.owners(s, t),
      Spec.Round.seen(s, c, Spec.Head.next(h))
    )
      == m: Maybe<&2, Ledgers.Vote>
  }
  -> Spec.Node.On(s, Spec.Advance.step(s, c, h, t, m)):
  match h m:
    case Spec.Head{r, br, +next, +th} Some{Ledgers.Vote{+before, +qs, after}}:
      em => et => ed => Path.when(
        Spec.Root.same(before, th),
        s,
        Spec.Advance.ran(s, c, r, br, next, after, qs, Spec.Step.run(s, c, t, qs)),
        s,
        Scan.elim(
          Spec.Node.On(
            s,
            Spec.Advance.ran(s, c, r, br, next, after, qs, Spec.Step.run(s, c, t, qs))
          ),
          s,
          c,
          next,
          Spec.Line.owners(s, t),
          Spec.Round.seen(s, c, next),
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
            Spec.Step.run(s, c, t, qs),
            q,
            em,
            (
              %Equal.sym(Maybe<&2, Spec.Tip>, Spec.Head.tip(s, Spec.Head{r, br, next, th}), Some{t}, et): {Maybe.bind(&2, Spec.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Spec.Ask, Spec.State.ledger(s), Ledgers.Where{c, next, q}, Spec.Line.owners(s, t1))) == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>}
              d)
          )(Run.grows(s, c, t, qs))
        ),
        Path.refl(s)
      )
    case Spec.Head{r, br, next, th} None{}:
      em => et => ed => Path.refl(s)

# Node.advance is on the paths, at the head h whose tip is m
def Advance.at.path(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  +h: Spec.Head,
  m: Maybe<&2, Spec.Tip>
) -> {
  Spec.Node.head_of(s, c) == Some{h}: Maybe<&2, Spec.Head>
} -> {
  Spec.Head.tip(s, h) == m: Maybe<&2, Spec.Tip>
} -> Spec.Node.On(s, Spec.Advance.at(s, c, h, m)):
  match m:
    case None{}:
      em => et => Path.refl(s)
    case Some{+t}:
      em => et => Advance.step.path(
        s,
        c,
        h,
        t,
        Spec.Height.decide(
          s,
          c,
          Spec.Head.next(h),
          Spec.Line.owners(s, t),
          Spec.Round.seen(s, c, Spec.Head.next(h))
        )
      )(em)(et)({==})

# a node's ballot keeps its logs
def Cast.path(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Node.cast(n, s, c)):
  Path.same(
    s,
    Spec.Node.cast(n, s, c),
    Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Spec.Node.head_of(s, c))
  )

# Advances.kept once the head m is known
def Advances.at.path(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {
  Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.On(s, Spec.Advances.at(f, s, c, m)):
  match f m:
    case 0n x:
      em => Path.refl(s)
    case 1n+p None{}:
      em => Path.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Spec.Advance.at(s, c, h, Spec.Head.tip(s, h))
        +m1 = Spec.Node.head_of(s1, c)
        Path.when(
          Spec.Heads.level(Some{h}, m1),
          s,
          s1,
          Spec.Advances.at(p, s1, c, m1),
          Advance.at.path(s, c, h, Spec.Head.tip(s, h))(em)({==}),
          Path.trans(
            s,
            s1,
            Spec.Advances.at(p, s1, c, m1),
            Advance.at.path(s, c, h, Spec.Head.tip(s, h))(em)({==}),
            Advances.at.path(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step is on the paths
def Advances.path(
  f: Nat,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Node.advances(f, s, c)):
  Advances.at.path(f, s, c, Spec.Node.head_of(s, c))({==})

# what a node does at a head is on the paths
def Step.head.path(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Step.head(n, s, c)):
  +s1 = Spec.Node.advances(4294967295n, s, c)
  +s2 = Spec.Node.cast(n, s1, c)
  s3 = Spec.Node.advances(4294967295n, s2, c)
  Path.trans(
    s,
    s1,
    s3,
    Advances.path(4294967295n, s, c),
    Path.trans(s1, s2, s3, Cast.path(n, s1, c), Advances.path(4294967295n, s2, c))
  )

# a head with no tip is not held
def Held.not(
  s: Spec.State(),
  c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>,
  em: {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>}
) -> {Spec.Head.held(Spec.Node.head_of(s, c)) == Spec.Head.held(m): Bool}:
  Equal.cong(Maybe<&2, Spec.Head>, Bool, Spec.Head.held, Spec.Node.head_of(s, c), m, em)

# a branch that opens is on the paths, once the head m of the line is known
def Open.at.path(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  m: Maybe<&2, Spec.Head>
) -> {Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>} -> Spec.Node.On(s, Spec.Open.at(s, c, m)):
  match m:
    case Some{Spec.Head{+r, Some{+b}, n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        Spec.Head{
          r,
          Some{b},
          0,
          Spec.Branch.first(s, b, Spec.Node.tip(s, Ledgers.Chain{r, None{}}))
        },
        Grows.refl(s),
        {==},
        Held.not(s, c, Some{Spec.Head{r, Some{b}, n, None{}}}, em)
      )
    case Some{Spec.Head{r, Some{b}, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Spec.Head{r, None{}, n, t}}:
      em => Path.refl(s)
    case None{}:
      em => Path.refl(s)

# what a node does on a line is on the paths
def Step.path(
  n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Node.step(n, s, c)):
  s1 = Spec.Node.open(s, c)
  Path.trans(
    s,
    s1,
    Spec.Step.head(n, s1, c),
    Open.at.path(s, c, Spec.Node.head_of(s, c))({==}),
    Step.head.path(n, s1, c)
  )

# a pass to the next round is on the paths
def Pass.path(
  +n: String,
  +s: Spec.State(),
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Node.pass(n, s, c)):
  +s1 = Spec.Pass.head(n, s, c, Spec.Node.head_of(s, c))
  Path.trans(
    s,
    s1,
    Spec.Node.step(n, s1, c),
    Path.same(
      s,
      s1,
      Pass.head.grows(n, s, c, Spec.Node.head_of(s, c)),
      Pass.head.heads(n, s, c, Spec.Node.head_of(s, c))
    ),
    Step.path(n, s1, c)
  )

# a first head is on the paths, once the head m of the line is known
def First.at.path(
  +s: Spec.State(),
  +c: Ledgers.Chain,
  h: Spec.Head,
  m: Maybe<&2, Spec.Head>
) -> {
  Spec.Node.head_of(s, c) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.On(s, Spec.First.at(s, c, h, m)):
  match m:
    case Some{Spec.Head{r, b, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Spec.Head{+r, +b, +n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        h,
        Grows.refl(s),
        {==},
        Held.not(s, c, Some{Spec.Head{r, b, n, None{}}}, em)
      )
    case None{}:
      em => Path.set(s, s, c, h, Grows.refl(s), {==}, Held.not(s, c, None{}, em))

# a first head on a node that grew from a, which grew from s, is on the paths
def Start.head.path(
  +s: Spec.State(),
  a: Spec.State(),
  m: Maybe<&2, Spec.State()>,
  +c: Ledgers.Chain,
  h: Spec.Head,
  g: {Spec.Node.grows(s, a) == True{}: Bool}
) -> {State.after(a, m) == True{}: Bool} -> Spec.Node.On(s, Spec.Start.head(s, m, c, h)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{+s3}:
      e =>
        +x = Spec.State.led(s, Spec.State.ledger(s3))
        Path.trans(
          s,
          x,
          Spec.State.first(x, c, h),
          Path.same(
            s,
            x,
            Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Spec.State.ledger(s3))
          ),
          First.at.path(x, c, h, Spec.Node.head_of(x, c))({==})
        )

# the first tip of a store is on the paths
def Start.put.path(
  s: Spec.State(),
  +i: Ledgers.Id,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> Spec.Node.On(s, Spec.Start.put(s, i, c, m)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{Spec.Work{+s2, l, ns}}:
      e =>
        +t = {Spec.Tip{c, l}: Spec.Tip}
        Start.head.path(
          s,
          s2,
          Spec.State.put(s2, [Spec.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Spec.Head{i, None{}, 0, Some{Spec.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Spec.Tip.words(t)]))

# Start.kept once the content m of the store is known
def Start.with.path(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Spec.Work>
) -> {Work.after(s, m) == True{}: Bool} -> Spec.Node.On(s, Spec.Start.with(s, i, os, m)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{+w}:
      e => Start.put.path(
        s,
        i,
        Spec.Work.root(w),
        Spec.Log.first(w, os)
      )(Log.first.after(s, w, os)(e))

# a store that starts is on the paths
def Start.path(
  +s: Spec.State(),
  i: Ledgers.Id,
  +os: List<&2, Spec.Owner>
) -> Spec.Node.On(s, Spec.Node.start(s, i, os)):
  Start.with.path(
    s,
    i,
    Spec.Owner.names(os),
    Spec.Seal.firsts(os, Some{Spec.Work{s, None{}, []}})
  )(Firsts.after(s, os, Some{Spec.Work{s, None{}, []}})(Grows.refl(s)))

# a line that a node starts to follow is on the paths
def Follow.new.path(
  +s: Spec.State(),
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Spec.Head>
) -> {
  Spec.Node.head_of(s, Spec.Line.chain(r, l)) == m: Maybe<&2, Spec.Head>
} -> Spec.Node.On(s, Spec.Follow.new(s, r, l, m)):
  match m:
    case Some{h}:
      em => Path.refl(s)
    case None{}:
      em => Path.set(
        s,
        s,
        Spec.Line.chain(r, l),
        Spec.Head{r, l, 0, None{}},
        Grows.refl(s),
        {==},
        Held.not(s, Spec.Line.chain(r, l), None{}, em)
      )

# a new request is on the paths
def Arrive.path(
  +s: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> Spec.Node.On(s, Spec.Node.arrive(s, i, q)):
  match q:
    case Spec.Ask.Start{os}:
      Start.path(s, i, os)
    case Spec.Ask.On{+r, +l, c}:
      +s1 = Spec.Node.follow(s, r, l)
      Path.trans(
        s,
        s1,
        Spec.State.wait(s1, Spec.Line.chain(r, l), i),
        Follow.new.path(s, r, l, Spec.Node.head_of(s, Spec.Line.chain(r, l)))({==}),
        Path.same(
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

# a new request is on the paths
def Ask.new.path(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask
) -> Spec.Node.On(s, Spec.Node.ask.new(n, s, e, q)):
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
  Path.trans(
    s,
    s0,
    Spec.Node.step(n, s1, c),
    Path.same(
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
    Path.trans(s0, s1, Spec.Node.step(n, s1, c), Arrive.path(s0, i, q), Step.path(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.path(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> Spec.Node.On(s, Spec.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Path.refl(s)
    case None{}:
      Path.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
        Spec.Node.ask.new(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        ),
        Path.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          Grows.to(
            s,
            s,
            Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
            Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
            Grows.refl(s)
          ),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e)))
        ),
        Ask.new.path(
          n,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), Spec.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask is on the paths
def Ask.path(
  n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  q: Spec.Ask
) -> Spec.Node.On(s, Spec.Node.ask(n, s, e, q)):
  Ask.at.path(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Spec.Ask, Spec.State.ledger(s), Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )

# the new requests among cells are on the paths
def Take.asks.path(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +old: Ledgers.State(Spec.Ask),
  +s: Spec.State()
) -> Spec.Node.On(s, Spec.Take.asks(cs, old, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Spec.State(),
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Spec.Node.arrive(s, i, q),
        u => s
      )
      Path.trans(
        s,
        s1,
        Spec.Take.asks(rest, old, s1),
        Path.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Spec.Ask>>,
            Ledgers.State.get(~Spec.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Spec.Node.arrive(s, i, q),
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
  +s: Spec.State(),
  +t: Ledgers.State(Spec.Ask)
) -> Spec.Node.On(s, Spec.Node.take(s, t)):
  +sent = Spec.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, t),
    Ledgers.State.empty(~Spec.Ask)
  )
  +l1 = Ledgers.State.take(~Spec.Ask, Spec.State.ledger(s), sent)
  +s1 = Spec.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Spec.Ask>>, sent)
  +s2 = Spec.Take.asks(cs, Spec.State.ledger(s), s1)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  Path.trans(
    s,
    s1,
    Spec.Sealed.take(bs, s2),
    Path.same(
      s,
      s1,
      Grows.led(
        s,
        l1,
        Ledgers.State.take_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          Spec.State.ledger(s),
          sent
        )
      ),
      Heads.led(s, l1)
    ),
    Path.trans(
      s1,
      s2,
      Spec.Sealed.take(bs, s2),
      Take.asks.path(cs, Spec.State.ledger(s), s1),
      Path.same(
        s2,
        Spec.Sealed.take(bs, s2),
        Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2),
        Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines is on the paths
def Steps.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> Spec.Node.On(s, Spec.Node.steps(n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      s1 = Spec.Node.step(n, s, c)
      Path.trans(s, s1, Spec.Node.steps(n, rest, s1), Step.path(n, s, c), Steps.path(n, rest, s1))

# an adoption is on the paths, once the request m is known
def Adopt.ask.path(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Spec.Request>
) -> Spec.Node.On(s, Spec.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Spec.Request{e, q}}:
      Ask.path(n, s, e, q)

# an adoption is on the paths, once the head m of the line is known
def Adopt.head.path(
  n: String,
  +s: Spec.State(),
  m: Maybe<&2, Spec.Head>
) -> Spec.Node.On(s, Spec.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Spec.Head{r, b, next, t}}:
      Adopt.ask.path(n, s, Spec.Node.adoption(s, r, b))

# the adoption of a line is on the paths
def Adopt.at.path(
  n: String,
  +s: Spec.State(),
  c: Ledgers.Chain
) -> Spec.Node.On(s, Spec.Adopt.at(n, s, c)):
  Adopt.head.path(n, s, Spec.Node.head_of(s, c))

# the adoption of a line, if any, is on the paths
def Adopt.maybe.path(
  n: String,
  s: Spec.State(),
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.On(s, Spec.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Adopt.at.path(n, s, c)

# the adoption of each of some lines is on the paths
def Adopts.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Spec.State()
) -> Spec.Node.On(s, Spec.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      Path.trans(
        s,
        Spec.Adopt.at(n, s, c),
        Spec.Node.adopts(n, rest, Spec.Adopt.at(n, s, c)),
        Adopt.at.path(n, s, c),
        Adopts.path(n, rest, Spec.Adopt.at(n, s, c))
      )

# more rounds of a sync, path
def More.path(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +bs: List<&2, Ledgers.Ballot>,
  +s: Spec.State()
) -> Spec.Node.On(s, Spec.Sync.more(f, n, cs, bs, s)):
  match f:
    case 0n:
      Path.refl(s)
    case 1n+(+p):
      Path.when(Spec.Lines.level(cs, s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Path.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Path.same(s, Spec.Sealed.take(bs, s), Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s), Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s)), Steps.path(n, cs, Spec.Sealed.take(bs, s))), Path.trans(s, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Spec.Sync.more(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s))), Path.trans(s, Spec.Sealed.take(bs, s), Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)), Path.same(s, Spec.Sealed.take(bs, s), Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s), Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Spec.Pending.of(bs), s)), Steps.path(n, cs, Spec.Sealed.take(bs, s))), More.path(p, n, cs, bs, Spec.Node.steps(n, cs, Spec.Sealed.take(bs, s)))))

# a sync is on the paths
def Sync.path(
  +n: String,
  +s: Spec.State(),
  +t: Ledgers.State(Spec.Ask)
) -> Spec.Node.On(s, Spec.Node.sync(n, s, t)):
  +s1 = Spec.Node.take(s, t)
  +cs = Spec.Sync.lines(s, s1, t)
  +bs = Spec.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Spec.Ask>>,
      Ledgers.State.missing(~Spec.Ask, ~Spec.Ask.is_eq, t, Spec.State.ledger(s))
    )
  )
  +s2 = Spec.Node.steps(n, cs, s1)
  +s3 = Spec.Sync.more(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2)
  Path.trans(s, s1, Spec.Node.adopts(n, cs, s3), Take.path(s, t), Path.trans(s1, s2, Spec.Node.adopts(n, cs, s3), Steps.path(n, cs, s1), Path.trans(s2, s3, Spec.Node.adopts(n, cs, s3), More.path(List.length(&2, Ledgers.Ballot, bs), n, cs, bs, s2), Adopts.path(n, cs, s3))))

# a request that a writer asks again at a node is on the paths
def Consent.path(
  n: String,
  +s: Spec.State(),
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.On(s, Spec.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Path.trans(
        s,
        Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
        Spec.Node.step(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c),
        Path.same(
          s,
          Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
          Grows.to(
            s,
            s,
            Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
            Led.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)),
            Grows.refl(s)
          ),
          Heads.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i))
        ),
        Step.path(n, Spec.State.keyed(s, Spec.Keys.mark(Spec.State.keys(s), i)), c)
      )

# what a node does is on the paths
def Does.path(
  +n: String,
  +s: Spec.State(),
  ev: Spec.Deed
) -> Spec.Node.On(s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Path.trans(
        s,
        Spec.Node.ask(n, s, e, q),
        Spec.Adopt.at(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q)),
        Ask.path(n, s, e, q),
        Adopt.at.path(n, Spec.Node.ask(n, s, e, q), Spec.Ask.chain(Spec.Envelope.of(e), q))
      )
    case Spec.Deed.Take{t}:
      Take.path(s, t)
    case Spec.Deed.Sync{t}:
      Sync.path(n, s, t)
    case Spec.Deed.Keep{+b}:
      Path.same(
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
      Path.trans(
        s,
        Spec.Node.consent(n, s, i),
        Spec.Adopt.maybe(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i)),
        Consent.path(n, s, i, Spec.Node.chain_of(s, i)),
        Adopt.maybe.path(n, Spec.Node.consent(n, s, i), Spec.Node.chain_of(s, i))
      )
    case Spec.Deed.Pass{+c}:
      Path.trans(
        s,
        Spec.Node.pass(n, s, c),
        Spec.Adopt.at(n, Spec.Node.pass(n, s, c), c),
        Pass.path(n, s, c),
        Adopt.at.path(n, Spec.Node.pass(n, s, c), c)
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
