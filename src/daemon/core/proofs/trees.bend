# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
import Base
import ../../../shared.bend as Shared
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

# Codes
# -----

# a member reads back
def Member.code_read(
  x: Basics.Member,
  r: List<&2, U32>
) -> {
  Basics.Member.code.read(
    Basics.Member.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Basics.Member>>
}:
  match x:
    case Basics.Member.Node{n}:
      Codes.Code.one_read(
        ~String,
        ~Basics.Member,
        ~Codes.Code.text.codec(),
        a => Basics.Member.Node{a},
        n,
        r
      )
    case Basics.Member.Group{n}:
      Codes.Code.one_read(
        ~String,
        ~Basics.Member,
        ~Codes.Code.text.codec(),
        a => Basics.Member.Group{a},
        n,
        r
      )

# the code of members
def Member.codec() -> Codes.Codec(Basics.Member):
  (Basics.Member.code, (Basics.Member.code.read, x => r => Member.code_read(x, r)))

# a content reads back
def Content.code_read(
  x: Basics.Content,
  r: List<&2, U32>
) -> {
  Basics.Content.code.read(
    Basics.Content.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Basics.Content>>
}:
  match x:
    case Basics.Content.Root{b}:
      Codes.Code.one_read(
        ~Ropes.Root,
        ~Basics.Content,
        ~Ropes.Root.codec(),
        a => Basics.Content.Root{a},
        b,
        r
      )
    case Basics.Content.Of{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Basics.Content,
        ~Ledgers.Id.codec(),
        a => Basics.Content.Of{a},
        v,
        r
      )

# the code of contents
def Content.codec() -> Codes.Codec(Basics.Content):
  (Basics.Content.code, (Basics.Content.code.read, x => r => Content.code_read(x, r)))

# a change reads back
def Change.code_read(
  x: Basics.Change,
  r: List<&2, U32>
) -> {
  Basics.Change.code.read(
    Basics.Change.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Basics.Change>>
}:
  match x:
    case Basics.Change.Branch{n, at}:
      Codes.Code.two_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~Basics.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        a => b => Basics.Change.Branch{a, b},
        n,
        at,
        r
      )
    case Basics.Change.Group{g, ms}:
      Codes.Code.two_read(
        ~String,
        ~List<&2, Basics.Member>,
        ~Basics.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.list.codec(~Basics.Member, ~Member.codec()),
        a => b => Basics.Change.Group{a, b},
        g,
        ms,
        r
      )
    case Basics.Change.Own{g, at, os}:
      Codes.Code.three_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Basics.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => b => c => Basics.Change.Own{a, b, c},
        g,
        at,
        os,
        r
      )
    case Basics.Change.Write{n, base, c}:
      Codes.Code.three_read(
        ~Resources.Name,
        ~Maybe<&2, Ledgers.Id>,
        ~Basics.Content,
        ~Basics.Change,
        ~Resources.Name.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Content.codec(),
        a => b => c => Basics.Change.Write{a, b, c},
        n,
        base,
        c,
        r
      )
    case Basics.Change.Resolve{k, n, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Resources.Name,
        ~Basics.Content,
        ~Basics.Change,
        ~Ledgers.Id.codec(),
        ~Resources.Name.codec(),
        ~Content.codec(),
        a => b => c => Basics.Change.Resolve{a, b, c},
        k,
        n,
        c,
        r
      )
    case Basics.Change.Merge{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Basics.Change,
        ~Ledgers.Id.codec(),
        a => Basics.Change.Merge{a},
        v,
        r
      )
    case Basics.Change.Move{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Basics.Change,
        ~Ledgers.Id.codec(),
        a => Basics.Change.Move{a},
        v,
        r
      )
    case Basics.Change.Mark{m, n}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Basics.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Basics.Change.Mark{a, b},
        m,
        n,
        r
      )
    case Basics.Change.Key{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Basics.Change,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Basics.Change.Key{a, b},
        n,
        k,
        r
      )

# the code of changes
def Change.codec() -> Codes.Codec(Basics.Change):
  (Basics.Change.code, (Basics.Change.code.read, x => r => Change.code_read(x, r)))

# a first owner reads back
def Owner.code_read(
  x: Basics.Owner,
  r: List<&2, U32>
) -> {
  Basics.Owner.code.read(
    Basics.Owner.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Basics.Owner>>
}:
  match x:
    case Basics.Owner{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Basics.Owner,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Basics.Owner{a, b},
        n,
        k,
        r
      )

# the code of first owners
def Owner.codec() -> Codes.Codec(Basics.Owner):
  (Basics.Owner.code, (Basics.Owner.code.read, x => r => Owner.code_read(x, r)))

# a request reads back
def Ask.code_read(
  x: Basics.Ask,
  r: List<&2, U32>
) -> {
  Basics.Ask.code.read(
    Basics.Ask.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Basics.Ask>>
}:
  match x:
    case Basics.Ask.Start{os}:
      Codes.Code.one_read(
        ~List<&2, Basics.Owner>,
        ~Basics.Ask,
        ~Codes.Code.list.codec(~Basics.Owner, ~Owner.codec()),
        a => Basics.Ask.Start{a},
        os,
        r
      )
    case Basics.Ask.On{st, l, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Maybe<&2, String>,
        ~Basics.Change,
        ~Basics.Ask,
        ~Ledgers.Id.codec(),
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        ~Change.codec(),
        a => b => c => Basics.Ask.On{a, b, c},
        st,
        l,
        c,
        r
      )

# the code of requests
def Ask.codec() -> Codes.Codec(Basics.Ask):
  (Basics.Ask.code, (Basics.Ask.code.read, x => r => Ask.code_read(x, r)))

# the laws of Spec.Ask.is_eq: two requests are the same exactly when their codes
# are
def Ask.laws() -> Shared.Eq.Laws(Basics.Ask, Basics.Ask.is_eq):
  Codes.Code.eq_laws(~Basics.Ask, ~Ask.codec())

def Spec.Ask.same():
  Ask.laws()

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
  +s: Basics.Node,
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

# Trees
# -----
# The node's read and write of a tree are the tree's own (Trees.Tree.get,
# Trees.Tree.set); they look at the root node before they make the path.

# a read below no node gives nothing
def Go.none(
  s: Basics.Node,
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {
  Trees.Tree.get.go(
    ~Basics.Node,
    ~Basics.Store.fetch,
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
  s: Basics.Node,
  p: List<&2, Nat>,
  k: List<&2, U32>
) -> {
  Trees.Tree.get.go(
    ~Basics.Node,
    ~Basics.Store.fetch,
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
  s: Basics.Node,
  +k: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {
  Basics.Node.get.at(
    s,
    k,
    m
  )
    == Trees.Tree.get.go(
      ~Basics.Node,
      ~Basics.Store.fetch,
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
        Trees.Tree.get.go(~Basics.Node, ~Basics.Store.fetch, s, Trees.Tree.path(k), k, None{}),
        None{},
        Go.none(s, Trees.Tree.path(k), k)
      )
    case Some{Trees.Node.Empty{}}:
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get.go(
          ~Basics.Node,
          ~Basics.Store.fetch,
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
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> {
  Basics.Node.get(
    s,
    h,
    k
  )
    == Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, s, h, k): Maybe<&2, List<&2, U32>>
}:
  Get.at.is(s, k, Trees.Tree.part(~Basics.Node, ~Basics.Store.fetch, s, h))

# a look below no node lacks it
def Look.go.none(
  s: Basics.Node,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  Trees.Tree.look.go(
    ~Basics.Node,
    ~Basics.Store.fetch,
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
  s: Basics.Node,
  p: List<&2, Nat>,
  k: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  Trees.Tree.look.go(
    ~Basics.Node,
    ~Basics.Store.fetch,
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
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {
  Basics.Node.look.at(
    s,
    h,
    k,
    m
  )
    == Trees.Tree.look.go(
      ~Basics.Node,
      ~Basics.Store.fetch,
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
        Trees.Tree.look.go(~Basics.Node, ~Basics.Store.fetch, s, Trees.Tree.path(k), k, h, None{}),
        Trees.Look.missing(h),
        Look.go.none(s, Trees.Tree.path(k), k, h)
      )
    case Some{Trees.Node.Empty{}}:
      Equal.sym(
        Trees.Look,
        Trees.Tree.look.go(
          ~Basics.Node,
          ~Basics.Store.fetch,
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
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> {
  Basics.Node.look(
    s,
    h,
    k
  )
    == Trees.Tree.look(~Basics.Node, ~Basics.Store.fetch, s, h, k): Trees.Look
}:
  Look.at.is(s, h, k, Trees.Tree.part(~Basics.Node, ~Basics.Store.fetch, s, h))

# a write below no node gives nothing
def Set.go.none(
  s: Basics.Node,
  p: List<&2, Nat>,
  d: Nat,
  k: List<&2, U32>,
  x: List<&2, U32>,
  h: Maybe<&2, Hashes.Hash>
) -> {
  Trees.Tree.set.go(
    ~Basics.Node,
    ~Basics.Store.fetch,
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
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> {
  Basics.Node.set.at(
    s,
    h,
    k,
    x,
    m
  )
    == Trees.Tree.set.go(
      ~Basics.Node,
      ~Basics.Store.fetch,
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
          ~Basics.Node,
          ~Basics.Store.fetch,
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
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {
  Basics.Node.set(
    s,
    h,
    k,
    x
  )
    == Trees.Tree.set(~Basics.Node, ~Basics.Store.fetch, s, h, k, x): Maybe<&2, Trees.Put>
}:
  Set.at.is(s, h, k, x, Trees.Tree.part(~Basics.Node, ~Basics.Store.fetch, s, h))

# the ledger of a node with a new ledger is that ledger
def Led.led(
  s: Basics.Node,
  l: Ledgers.State(Basics.Ask)
) -> {Basics.State.ledger(Basics.State.led(s, l)) == l: Ledgers.State(Basics.Ask)}:
  match s:
    case Basics.Node{old, hs, ws, ks}:
      {==}

# a new head keeps the ledger
def Led.head(
  s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head
) -> {
  Basics.State.ledger(
    Sealing.State.head(s, c, h)
  )
    == Basics.State.ledger(s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# new waiting requests keep the ledger
def Led.wait(
  s: Basics.Node,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  Basics.State.ledger(
    Sealing.Wait.set(s, c, qs)
  )
    == Basics.State.ledger(s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# a node grows to itself
def Grows.refl(s: Basics.Node) -> {Reading.Node.grows(s, s) == True{}: Bool}:
  Ledgers.State.grows_refl(~Basics.Ask, ~Basics.Ask.is_eq, ~Ask.laws(), Basics.State.ledger(s))

# growth composes
def Grows.trans(
  a: Basics.Node,
  b: Basics.Node,
  c: Basics.Node
) -> {
  Reading.Node.grows(a, b) == True{}: Bool
} -> {Reading.Node.grows(b, c) == True{}: Bool} -> {Reading.Node.grows(a, c) == True{}: Bool}:
  Ledgers.State.grows_trans(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    ~Ask.laws(),
    Basics.State.ledger(a),
    Basics.State.ledger(b),
    Basics.State.ledger(c)
  )

# a node with a new ledger grows when the ledger does
def Grows.led(
  s: Basics.Node,
  l: Ledgers.State(Basics.Ask),
  e: {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), l) == True{}: Bool
  }
) -> {Reading.Node.grows(s, Basics.State.led(s, l)) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Basics.Ask),
    Basics.State.ledger(Basics.State.led(s, l)),
    l,
    Led.led(s, l)
  ): {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), _) == True{}: Bool
  }
  e

# data only grows a node
def Grows.keep(
  +s: Basics.Node,
  +ds: List<&2, List<&2, U32>>
) -> {Reading.Node.grows(s, Basics.State.keep(s, ds)) == True{}: Bool}:
  Grows.led(
    s,
    Ledgers.State.put_datas(~Basics.Ask, ~Basics.Ask.is_eq, ds, Basics.State.ledger(s)),
    Ledgers.State.put_datas_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Ask.laws(),
      ds,
      Basics.State.ledger(s)
    )
  )

# the work m, if any, is on a node that grew from s
def Work.after(s: Basics.Node, m: Maybe<&2, Judging.Work>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Judging.Work{s2, h, ns}}:
      Reading.Node.grows(s, s2)

# the node m, if any, grew from s
def State.after(s: Basics.Node, m: Maybe<&2, Basics.Node>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{s2}:
      Reading.Node.grows(s, s2)

# a node that is kept when b holds grew from s, when it did
def Put.grows.if(
  s: Basics.Node,
  -s2: Basics.Node,
  b: Bool,
  g: {Reading.Node.grows(s, s2) == True{}: Bool}
) -> {State.after(s, Shared.Maybe.when(Basics.Node, b, u => Some{s2})) == True{}: Bool}:
  match b:
    case True{}:
      g
    case False{}:
      {==}

# data that a node puts and reads back only grows it
def Put.grows(
  +s: Basics.Node,
  +ds: List<&2, List<&2, U32>>
) -> {State.after(s, Judging.State.put(s, ds)) == True{}: Bool}:
  Put.grows.if(
    s,
    Basics.State.keep(s, ds),
    Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ds), ds),
    Grows.keep(s, ds)
  )

# a work on a node that grew
def Work.put.grows(
  s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  h: Maybe<&2, Hashes.Hash>,
  ws: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Work.after(s, Judging.Work.put(m, h, ws, ns)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a new subtree only grows a node
def Work.of.grows(
  +s: Basics.Node,
  ns: List<&2, List<&2, U32>>,
  m: Maybe<&2, Trees.Put>
) -> {Work.after(s, Judging.Work.of(s, ns, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Trees.Put{h, +ws}}:
      Work.put.grows(s, Judging.State.put(s, ws), Some{h}, ws, ns)(Put.grows(s, ws))

# a key set in a tree only grows a node
def Set.grows(
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> {Work.after(s, Judging.Work.set(Judging.Work{s, h, ns}, k, x)) == True{}: Bool}:
  Work.of.grows(s, ns, Basics.Node.set(s, h, k, x))

# the run m, if any, is on a node that grew from s
def Run.after(s: Basics.Node, m: Maybe<&2, Stepping.Run>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Stepping.Run{s2, t, ns}}:
      Reading.Node.grows(s, s2)

# a run is on its own node
def After.self(r: Stepping.Run) -> {Run.after(Stepping.Run.state(r), Some{r}) == True{}: Bool}:
  match r:
    case Stepping.Run{s, t, ns}:
      Grows.refl(s)

# a run on a node that grew from b is on one that grew from a, when b grew
# from a
def After.trans(
  a: Basics.Node,
  b: Basics.Node,
  +m: Maybe<&2, Stepping.Run>,
  e1: {Reading.Node.grows(a, b) == True{}: Bool},
  e2: {Run.after(b, m) == True{}: Bool}
) -> {Run.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{s2, t, ns}}:
      Grows.trans(a, b, s2)(e1)(e2)

# a run, then a run from it, is on a node that grew
def After.bind(
  s: Basics.Node,
  +m: Maybe<&2, Stepping.Run>,
  f: Stepping.Run -> Maybe<&2, Stepping.Run>,
  hm: {Run.after(s, m) == True{}: Bool},
  hf: @r: Stepping.Run -> {Run.after(Stepping.Run.state(r), f(r)) == True{}: Bool}
) -> {Run.after(s, Maybe.bind(&2, Stepping.Run, Stepping.Run, m, f)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{+s2, +t, +ns}}:
      After.trans(s, s2, f(Stepping.Run{s2, t, ns}), hm, hf(Stepping.Run{s2, t, ns}))

# one of two runs, each on a node that grew
def After.when(
  s: Basics.Node,
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

# the run of a new log is on a node that grew
def Run.of.grows(
  s: Basics.Node,
  c: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Judging.Work>,
  e: {Work.after(s, m) == True{}: Bool}
) -> {Run.after(s, Stepping.Run.of(c, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Judging.Work{s2, l, ns}}:
      e

# a key set in a run's log only grows its node
def Log.grows(
  +r: Stepping.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.log(r, k, x)) == True{}: Bool}:
  match r:
    case Stepping.Run{+s, Basics.Tip{c, +l}, +ns}:
      Run.of.grows(s, c, Judging.Work.set(Judging.Work{s, l, ns}, k, x), Set.grows(s, l, ns, k, x))

# a run on a node that grew
def Run.put.grows(
  s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  t: Basics.Tip,
  ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Run.after(s, Stepping.Run.put(m, t, ds, ns)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# new content only grows a run's node
def Content.grows(
  r: Stepping.Run,
  h: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.content(r, h, ds)) == True{}: Bool}:
  match r:
    case Stepping.Run{+s, Basics.Tip{c, l}, ns}:
      Run.put.grows(s, Judging.State.put(s, ds), Basics.Tip{h, l}, ds, ns)(Put.grows(s, ds))

# Add.grows once the value m of the key is known
def Add.at.grows(
  r: Stepping.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.add.at(r, k, x, m)) == True{}: Bool}:
  match m:
    case None{}:
      Log.grows(r, k, x)
    case Some{old}:
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
    Basics.Node.get(Stepping.Run.state(r), Basics.Tip.log(Stepping.Run.tip(r)), k)
  )

# new owners only grow a run's node
def Owners.grows(
  r: Stepping.Run,
  +m: Maybe<&2, List<&2, String>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Run.owners(r, m)) == True{}: Bool}:
  match m:
    case None{}:
      After.self(r)
    case Some{os}:
      Log.grows(r, Basics.Log.owners(), Ledgers.Owners.code(os, []))

# a refused request only grows a run's node
def Stale.grows(
  r: Stepping.Run,
  i: Ledgers.Id
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.stale(r, i)) == True{}: Bool}:
  Add.grows(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}))

# a taken request only grows a run's node
def Taken.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.taken(r, i, own)) == True{}: Bool}:
  +n = Basics.Line.count(Stepping.Run.state(r), Stepping.Run.tip(r))
  After.bind(
    Stepping.Run.state(r),
    Stepping.Run.add(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Stepping.Run,
      Stepping.Run,
      Stepping.Run.add(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))})
      ),
      +r2 => Maybe.bind(
        &2,
        Stepping.Run,
        Stepping.Run,
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own)
      )
    ),
    Add.grows(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n})),
    +r1 => After.bind(
      Stepping.Run.state(r1),
      Stepping.Run.add(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))})
      ),
      +r2 => Maybe.bind(
        &2,
        Stepping.Run,
        Stepping.Run,
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own)
      ),
      Add.grows(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))})
      ),
      +r2 => After.bind(
        Stepping.Run.state(r2),
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own),
        Log.grows(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Owners.grows(r3, own)
      )
    )
  )

# a judged request only grows a run's node
def Judged.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Basics.Verdict>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.judged(r, i, own, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Basics.Verdict{False{}, h, ds}}:
      Stale.grows(r, i)
    case Some{Basics.Verdict{True{}, +h, +ds}}:
      After.bind(
        Stepping.Run.state(r),
        Stepping.Run.content(r, h, ds),
        r2 => Stepping.Step.taken(r2, i, own),
        Content.grows(r, h, ds),
        r2 => Taken.grows(r2, i, own)
      )

# a mark on a version only grows a run's node
def Marked.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +m: String,
  +v: Maybe<&2, Basics.Version>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.marked(r, i, m, v)) == True{}: Bool}:
  match v:
    case None{}:
      {==}
    case Some{+x}:
      After.bind(
        Stepping.Run.state(r),
        Stepping.Run.add(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(x), [])),
        r2 => Stepping.Step.taken(r2, i, None{}),
        Add.grows(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(x), [])),
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
  +n = Basics.Line.count(s, t)
  After.when(
    s,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Basics.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Stepping.Step.marked(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    Stepping.Step.stale(r, i),
    Marked.grows(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    Stale.grows(r, i)
  )

# the first tip of a new branch only grows a run's node
def Branch.made.grows(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Judging.Made>
) -> {Run.after(Stepping.Run.state(r), Stepping.Branch.made(r, i, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Judging.Made{+t, +ds}}:
      After.bind(
        Stepping.Run.state(r),
        Stepping.Run.content(r, Basics.Tip.content(Stepping.Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Stepping.Run,
          Stepping.Run,
          Stepping.Run.add(r1, Basics.Log.start(b), Hashes.Hash.code(Basics.Tip.hash(t), [])),
          r2 => Stepping.Step.taken(r2, i, None{})
        ),
        Content.grows(r, Basics.Tip.content(Stepping.Run.tip(r)), ds),
        +r1 => After.bind(
          Stepping.Run.state(r1),
          Stepping.Run.add(r1, Basics.Log.start(b), Hashes.Hash.code(Basics.Tip.hash(t), [])),
          r2 => Stepping.Step.taken(r2, i, None{}),
          Add.grows(r1, Basics.Log.start(b), Hashes.Hash.code(Basics.Tip.hash(t), [])),
          r2 => Taken.grows(r2, i, None{})
        )
      )

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
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
          ~Basics.Node,
          ~Basics.Store.fetch,
          Stepping.Run.state(r),
          Basics.Node.root_of(Stepping.Run.state(r), at)
        ),
        Stepping.Branch.made(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          )
        ),
        None{},
        Branch.made.grows(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          )
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

# a change of a line only grows a run's node
def On.grows(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.on(r, i, st, l, ch)) == True{}: Bool}:
  match l ch:
    case None{} Basics.Change.Branch{+a, b}:
      Branch.new.grows(
        r,
        i,
        st,
        a,
        b,
        Basics.Node.find(
          Stepping.Run.state(r),
          Basics.Tip.log(Stepping.Run.tip(r)),
          Basics.Log.start(a)
        )
      )
    case None{} Basics.Change.Group{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Group{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Group{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Own{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Own{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Own{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Write{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Write{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Write{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Resolve{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Resolve{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Resolve{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Merge{a}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Merge{a}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Merge{a},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Move{a}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Move{a}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Move{a},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case None{} Basics.Change.Mark{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Mark{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Mark{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Branch{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Branch{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Branch{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Group{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Group{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Group{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Own{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Own{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Own{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Write{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Write{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Write{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Resolve{a, b, c}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Resolve{a, b, c}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Resolve{a, b, c},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Merge{a}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Merge{a}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Merge{a},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Move{a}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Move{a}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Move{a},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Mark{a, b}:
      Mark.grows(r, i, a)
    case None{} Basics.Change.Key{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Key{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          None{},
          Basics.Change.Key{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )
    case Some{x} Basics.Change.Key{a, b}:
      Judged.grows(
        r,
        i,
        Basics.Change.owners(Basics.Change.Key{a, b}),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          Some{x},
          Basics.Change.Key{a, b},
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )

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
        Ledgers.Chain.is_eq(Basics.Line.chain(st, l), c),
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
  +o: Maybe<&2, Basics.Out>
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.fresh(r, c, i, o)) == True{}: Bool}:
  match o:
    case Some{x}:
      After.self(r)
    case None{}:
      Asked.grows(r, c, i, Basics.Node.asked(Stepping.Run.state(r), i))

# one request of a step only grows a run's node
def One.grows(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> {Run.after(Stepping.Run.state(r), Stepping.Step.one(r, c, i)) == True{}: Bool}:
  Fresh.grows(r, c, i, Basics.Line.out(Stepping.Run.state(r), Stepping.Run.tip(r), i))

# the requests of a step only grow a run's node
def All.grows(
  +s: Basics.Node,
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
  +s: Basics.Node,
  c: Ledgers.Chain,
  t: Basics.Tip,
  qs: List<&2, Ledgers.Id>
) -> {Run.after(s, Stepping.Step.run(s, c, t, qs)) == True{}: Bool}:
  All.grows(s, c, qs, Some{Stepping.Run{s, t, []}})(Grows.refl(s))

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
    case Some{Stepping.Run{s2, t, ns}}:
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
  -s: Basics.Node,
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
  -s: Basics.Node,
  after: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Stepping.Run>
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Run.after(s, Sealing.Plan.fit(after, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => {==}
    case Some{Stepping.Run{s2, t2, ns}}:
      e => Fit.when.grows(
        s,
        Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}),
        Stepping.Run{s2, t2, ns},
        e
      )

# the run of one of two plans, each on a node that grew
def Plan.when.grows(
  -s: Basics.Node,
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  t: Basics.Tip,
  -from: List<&2, String>
) -> {Run.after(s, Sealing.Plan.run(Sealing.Plan.own(s, c, t, from))) == True{}: Bool}:
  Some.grows(c, Sealing.Cast.mine(s, Sealing.Wait.of(s, c)), Stepping.Run{s, t, []})

# the run of the plan for a step that another ballot names is on a node that
# grew
def Plan.copy.grows(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +t: Basics.Tip,
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
  s: Basics.Node,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Basics.Tip,
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Basics.Tip,
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
  +s: Basics.Node,
  c: Ledgers.Chain,
  w: Ledgers.Where,
  t: Basics.Tip,
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Basics.Tip,
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
  a: Basics.Node,
  b: Basics.Node,
  x: Basics.Node,
  e: {Basics.State.ledger(x) == Basics.State.ledger(b): Ledgers.State(Basics.Ask)},
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {Reading.Node.grows(a, x) == True{}: Bool}:
  %Equal.sym(
    Ledgers.State(Basics.Ask),
    Basics.State.ledger(x),
    Basics.State.ledger(b),
    e
  ): {
    Ledgers.State.grows(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(a), _) == True{}: Bool
  }
  g

# one of two nodes, each grown from s
def Grows.when(
  s: Basics.Node,
  b: Bool,
  -x: Basics.Node,
  -y: Basics.Node,
  hx: {Reading.Node.grows(s, x) == True{}: Bool},
  hy: {Reading.Node.grows(s, y) == True{}: Bool}
) -> {Reading.Node.grows(s, Shared.Bool.when(Basics.Node, b, u => x, u => y)) == True{}: Bool}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a moved head keeps the ledger
def Led.moved(
  s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head,
  qs: List<&2, Ledgers.Id>
) -> {
  Basics.State.ledger(
    Sealing.State.moved(s, c, h, qs)
  )
    == Basics.State.ledger(s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# a request that waits keeps the ledger
def Led.waits(
  s: Basics.Node,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  Basics.State.ledger(
    Sealing.State.wait(s, c, i)
  )
    == Basics.State.ledger(s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# a node with the ledger of a node that grew from it grew
def Grows.back(
  s: Basics.Node,
  s3: Basics.Node,
  g: {Reading.Node.grows(s, s3) == True{}: Bool}
) -> {Reading.Node.grows(s, Basics.State.led(s, Basics.State.ledger(s3))) == True{}: Bool}:
  Grows.led(s, Basics.State.ledger(s3), g)

# new keys keep the ledger
def Led.keyed(
  s: Basics.Node,
  ks: Basics.Keys
) -> {
  Basics.State.ledger(
    Basics.State.keyed(s, ks)
  )
    == Basics.State.ledger(s): Ledgers.State(Basics.Ask)
}:
  match s:
    case Basics.Node{l, hs, ws, old}:
      {==}

# a ballot that a node accepts only grows it
def Accept.at.grows(
  +s: Basics.Node,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Basics.Keychain>
) -> {State.after(s, Sealing.Seal.accept.at(s, b, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Put.grows.if(
        s,
        Basics.State.keyed(
          Basics.State.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
          ),
          Sealing.Keys.saw(
            Sealing.Keys.set(
              Basics.State.keys(s),
              Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
              Sealing.Keychain.next(c, b)
            ),
            Sealing.Ballot.at(b)
          )
        ),
        Sealing.Seal.fits(c, b),
        Grows.to(
          s,
          Basics.State.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
          ),
          Basics.State.keyed(
            Basics.State.led(
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
            ),
            Sealing.Keys.saw(
              Sealing.Keys.set(
                Basics.State.keys(s),
                Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
                Sealing.Keychain.next(c, b)
              ),
              Sealing.Ballot.at(b)
            )
          ),
          Led.keyed(
            Basics.State.led(
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
            ),
            Sealing.Keys.saw(
              Sealing.Keys.set(
                Basics.State.keys(s),
                Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
                Sealing.Keychain.next(c, b)
              ),
              Sealing.Ballot.at(b)
            )
          ),
          Grows.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b),
            Ledgers.State.add_grows(
              ~Basics.Ask,
              ~Basics.Ask.is_eq,
              ~Ask.laws(),
              Basics.State.ledger(s),
              Ledgers.Slot.of(b),
              Ledgers.Entry.Vote{b}
            )
          )
        )
      )

# the node m, if any, else s, grew from s when m did
def Default.grows(
  s: Basics.Node,
  m: Maybe<&2, Basics.Node>
) -> {
  State.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Maybe.default(&2, Basics.Node, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{s2}:
      e => e

# a sealed ballot only grows a node
def Cast.seal.grows(
  +s: Basics.Node,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Basics.Keychain>
) -> {Reading.Node.grows(s, Sealing.Cast.seal(s, w, n, a0, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Basics.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Sealing.Seal.secret(Sealing.Keys.seed(Basics.State.keys(s)), Sealing.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Sealing.Seal.secret(
            Sealing.Keys.seed(Basics.State.keys(s)),
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
  +s: Basics.Node,
  a: Basics.Node,
  m: Maybe<&2, Basics.Node>,
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
        +s4 = Basics.State.led(s, Basics.State.ledger(s3))
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
  s: Basics.Node
) -> {
  Run.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Cast.put(n, w, th, qs, from, m, s)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Stepping.Run{+s2, +t2, ns}}:
      e => Cast.vote.grows(
        s,
        s2,
        Judging.State.put(s2, [Basics.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Basics.Tip.hash(t2)}}, from},
        e
      )(Put.grows(s2, [Basics.Tip.words(t2)]))

# a pass only grows a node
def Pass.to.grows(
  +n: String,
  +s: Basics.Node,
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
            Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, r}, n)
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
  +s: Basics.Node,
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Basics.Tip
) -> {Reading.Node.grows(s, Voting.Cast.round(n, s, c, next, th, t)) == True{}: Bool}:
  +os = Basics.Line.owners(s, t)
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {Reading.Node.grows(s, Voting.Cast.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Basics.Head{r, b, +next, +th} Some{+t}:
      +s1 = Voting.Round.join(n, s, c, next, Basics.Line.owners(s, t))
      Grows.trans(
        s,
        s1,
        Voting.Cast.round(n, s1, c, next, th, t)
      )(
        Round.join.grows(n, s, c, next, Basics.Line.owners(s, t))
      )(Cast.round.grows(n, s1, c, next, th, t))
    case Basics.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, at the head h whose tip is m
def Pass.at.grows(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {Reading.Node.grows(s, Voting.Pass.at(n, s, c, h, m)) == True{}: Bool}:
  match h m:
    case Basics.Head{r, b, +next, th} Some{t}:
      Pass.to.grows(
        n,
        s,
        Ledgers.Where{c, next, 1n+Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))},
        Basics.Line.owners(s, t)
      )
    case Basics.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.pass only grows a node, once the head m is known
def Pass.head.grows(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Voting.Pass.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Pass.at.grows(n, s, c, h, Basics.Head.tip(s, h))

# Node.cast only grows a node, once the head m is known
def Cast.head.grows(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Voting.Cast.head(n, s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Cast.at.grows(n, s, c, h, Basics.Head.tip(s, h))

# a node's ballot only grows it
def Cast.grows(
  n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.cast(n, s, c)) == True{}: Bool}:
  Cast.head.grows(n, s, c, Basics.Node.head_of(s, c))

# a head moved on a node that grew from a, which grew from s, only grows s
def Advance.moved.grows(
  +s: Basics.Node,
  a: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +c: Ledgers.Chain,
  +h: Basics.Head,
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
        +x = Basics.State.led(s, Basics.State.ledger(s3))
        Grows.to(
          s,
          x,
          Sealing.State.moved(x, c, h, qs),
          Led.moved(x, c, h, qs),
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )

# a checked step only grows a node
def Advance.ran.grows(
  +s: Basics.Node,
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
    case Some{Stepping.Run{+s2, +t2, ns}}:
      e =>
        +hd = {Basics.Head{r, b, U32.inc(next), Some{Basics.Tip.hash(t2)}}: Basics.Head}
        Grows.when(
          s,
          Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}),
          Voting.Advance.moved(s, Judging.State.put(s2, [Basics.Tip.words(t2)]), c, hd, qs),
          s,
          Advance.moved.grows(
            s,
            s2,
            Judging.State.put(s2, [Basics.Tip.words(t2)]),
            c,
            hd,
            qs,
            e
          )(Put.grows(s2, [Basics.Tip.words(t2)])),
          Grows.refl(s)
        )

# Node.advance only grows a node, once the decided step m is known
def Advance.step.grows(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  +t: Basics.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Reading.Node.grows(s, Voting.Advance.step(s, c, h, t, m)) == True{}: Bool}:
  match h m:
    case Basics.Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
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
    case Basics.Head{r, b, next, th} None{}:
      Grows.refl(s)

# Node.advance only grows a node, at the head h whose tip is m
def Advance.at.grows(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
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
          Basics.Line.owners(s, t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )

# Node.advance only grows a node, once the head m is known
def Advance.head.grows(
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Voting.Advance.head(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{+h}:
      Advance.at.grows(s, c, h, Basics.Head.tip(s, h))

# Advances.grows once the head m is known
def Advances.at.grows(
  f: Nat,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Voting.Advances.at(f, s, c, m)) == True{}: Bool}:
  match f m:
    case 0n x:
      Grows.refl(s)
    case 1n+p None{}:
      Grows.refl(s)
    case 1n+(+p) Some{+h}:
      +s1 = Voting.Advance.at(s, c, h, Basics.Head.tip(s, h))
      +m1 = Basics.Node.head_of(s1, c)
      Grows.when(
        s,
        Voting.Heads.level(Some{h}, m1),
        s1,
        Voting.Advances.at(p, s1, c, m1),
        Advance.at.grows(s, c, h, Basics.Head.tip(s, h)),
        Grows.trans(
          s,
          s1,
          Voting.Advances.at(p, s1, c, m1)
        )(Advance.at.grows(s, c, h, Basics.Head.tip(s, h)))(Advances.at.grows(p, s1, c, m1))
      )

# a head that moves over each decided step only grows a node
def Advances.grows(
  f: Nat,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.advances(f, s, c)) == True{}: Bool}:
  Advances.at.grows(f, s, c, Basics.Node.head_of(s, c))

# what a node does at a head only grows it
def Step.head.grows(
  +n: String,
  +s: Basics.Node,
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
  +s: Basics.Node,
  +c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Sealing.Open.at(s, c, m)) == True{}: Bool}:
  match m:
    case Some{Basics.Head{+r, Some{+b}, n, None{}}}:
      +hd = {
        Basics.Head{
          r,
          Some{b},
          0,
          Sealing.Branch.first(s, b, Basics.Node.tip(s, Ledgers.Chain{r, None{}}))
        }: Basics.Head
      }
      Grows.to(s, s, Sealing.State.head(s, c, hd), Led.head(s, c, hd), Grows.refl(s))
    case Some{Basics.Head{r, Some{b}, n, Some{t}}}:
      Grows.refl(s)
    case Some{Basics.Head{r, None{}, n, t}}:
      Grows.refl(s)
    case None{}:
      Grows.refl(s)

# what a node does on a line only grows it
def Step.grows(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.step(n, s, c)) == True{}: Bool}:
  +s1 = Sealing.Node.open(s, c)
  Grows.trans(
    s,
    s1,
    Voting.Step.head(n, s1, c)
  )(Open.at.grows(s, c, Basics.Node.head_of(s, c)))(Step.head.grows(n, s1, c))

# a pass to the next round only grows a node
def Pass.grows(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> {Reading.Node.grows(s, Voting.Node.pass(n, s, c)) == True{}: Bool}:
  +s1 = Voting.Pass.head(n, s, c, Basics.Node.head_of(s, c))
  Grows.trans(
    s,
    s1,
    Voting.Node.step(n, s1, c)
  )(Pass.head.grows(n, s, c, Basics.Node.head_of(s, c)))(Step.grows(n, s1, c))

# a first head only grows a node, once the head m of its line is known
def First.at.grows(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Sealing.First.at(s, c, h, m)) == True{}: Bool}:
  match m:
    case Some{Basics.Head{r, b, n, Some{t}}}:
      Grows.refl(s)
    case Some{Basics.Head{r, b, n, None{}}}:
      Grows.to(s, s, Sealing.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))
    case None{}:
      Grows.to(s, s, Sealing.State.head(s, c, h), Led.head(s, c, h), Grows.refl(s))

# a first head on a node that grew from a, which grew from s, only grows s
def Start.head.grows(
  +s: Basics.Node,
  a: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  State.after(a, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Start.head(s, m, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+s3}:
      e =>
        +x = Basics.State.led(s, Basics.State.ledger(s3))
        Grows.trans(
          s,
          x,
          Sealing.State.first(x, c, h)
        )(
          Grows.back(s, s3, Grows.trans(s, a, s3)(g)(e))
        )(First.at.grows(x, c, h, Basics.Node.head_of(x, c)))

# a work on a node that grew from b is on one that grew from a, when b grew
# from a
def Work.after.trans(
  a: Basics.Node,
  b: Basics.Node,
  m: Maybe<&2, Judging.Work>,
  e1: {Reading.Node.grows(a, b) == True{}: Bool},
  e2: {Work.after(b, m) == True{}: Bool}
) -> {Work.after(a, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Judging.Work{s3, h, ns}}:
      Grows.trans(a, b, s3)(e1)(e2)

# a key set in a work on a node that grew from s is on a node that grew from s
def Work.set.after(
  s: Basics.Node,
  m: Maybe<&2, Judging.Work>,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {
  Work.after(
    s,
    Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Judging.Work.set(w, k, x))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      e => {==}
    case Some{Judging.Work{+s2, +h, +ns}}:
      e => Work.after.trans(
        s,
        s2,
        Judging.Work.set(Judging.Work{s2, h, ns}, k, x),
        e,
        Set.grows(s2, h, ns, k, x)
      )

# the first keys of a store are on a node that grew
def Firsts.after(
  +s: Basics.Node,
  os: List<&2, Basics.Owner>,
  +m: Maybe<&2, Judging.Work>
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
          Judging.Work,
          Judging.Work,
          m,
          w => Judging.Work.set(w, Basics.Key.seal(n), Hashes.Hash.code(k, []))
        )
      )(Work.set.after(s, m, Basics.Key.seal(n), Hashes.Hash.code(k, []))(e))

# the first log of a line is on a node that grew
def Log.first.after(
  s: Basics.Node,
  w: Judging.Work,
  +os: List<&2, String>
) -> {
  Work.after(s, Some{w}) == True{}: Bool
} -> {Work.after(s, Judging.Log.first(w, os)) == True{}: Bool}:
  match w:
    case Judging.Work{+s2, h, +ns}:
      e => Work.after.trans(
        s,
        s2,
        Judging.Work.set(
          Judging.Work{s2, None{}, ns},
          Basics.Log.owners(),
          Ledgers.Owners.code(os, [])
        ),
        e,
        Set.grows(s2, None{}, ns, Basics.Log.owners(), Ledgers.Owners.code(os, []))
      )

# the first tip of a store only grows a node
def Start.put.grows(
  s: Basics.Node,
  +i: Ledgers.Id,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Judging.Work>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Start.put(s, i, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{Judging.Work{+s2, l, ns}}:
      e =>
        +t = {Basics.Tip{c, l}: Basics.Tip}
        Start.head.grows(
          s,
          s2,
          Judging.State.put(s2, [Basics.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Basics.Head{i, None{}, 0, Some{Basics.Tip.hash(t)}},
          e
        )(Put.grows(s2, [Basics.Tip.words(t)]))

# Start.grows once the content m of the store is known
def Start.with.grows(
  +s: Basics.Node,
  i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Judging.Work>
) -> {
  Work.after(s, m) == True{}: Bool
} -> {Reading.Node.grows(s, Sealing.Start.with(s, i, os, m)) == True{}: Bool}:
  match m:
    case None{}:
      e => Grows.refl(s)
    case Some{+w}:
      e => Start.put.grows(
        s,
        i,
        Judging.Work.root(w),
        Judging.Log.first(w, os)
      )(Log.first.after(s, w, os)(e))

# a store that starts only grows a node
def Start.grows(
  +s: Basics.Node,
  i: Ledgers.Id,
  +os: List<&2, Basics.Owner>
) -> {Reading.Node.grows(s, Sealing.Node.start(s, i, os)) == True{}: Bool}:
  Start.with.grows(
    s,
    i,
    Basics.Owner.names(os),
    Sealing.Seal.firsts(os, Some{Judging.Work{s, None{}, []}})
  )(Firsts.after(s, os, Some{Judging.Work{s, None{}, []}})(Grows.refl(s)))

# a line that a node follows only grows it, once its head m is known
def Follow.new.grows(
  +s: Basics.Node,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Sealing.Follow.new(s, r, l, m)) == True{}: Bool}:
  match m:
    case Some{h}:
      Grows.refl(s)
    case None{}:
      Grows.to(
        s,
        s,
        Sealing.State.head(s, Basics.Line.chain(r, l), Basics.Head{r, l, 0, None{}}),
        Led.head(s, Basics.Line.chain(r, l), Basics.Head{r, l, 0, None{}}),
        Grows.refl(s)
      )

# a new request only grows a node
def Arrive.grows(
  +s: Basics.Node,
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
        Sealing.State.wait(s1, Basics.Line.chain(r, l), i),
        Led.waits(s1, Basics.Line.chain(r, l), i),
        Follow.new.grows(s, r, l, Basics.Node.head_of(s, Basics.Line.chain(r, l)))
      )

# a new request only grows a node
def Ask.new.grows(
  +n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  +q: Basics.Ask
) -> {Reading.Node.grows(s, Voting.Node.ask.new(n, s, e, q)) == True{}: Bool}:
  +i = Basics.Envelope.of(e)
  +c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Basics.State.ledger(s),
    i,
    Basics.Envelope.time(e),
    q
  )
  +s0 = Basics.State.led(s, l0)
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
        ~Ask.laws(),
        Basics.State.ledger(s),
        Ledgers.Slot.ask(i),
        Ledgers.Entry.Ask{i, Basics.Envelope.time(e), q}
      )
    )
  )(Grows.trans(s0, s1, Voting.Node.step(n, s1, c))(Arrive.grows(s0, i, q))(Step.grows(n, s1, c)))

# Node.ask_grows once the cell m of the request's ID is known
def Ask.at.grows(
  +n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  +q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {Reading.Node.grows(s, Voting.Node.ask.at(n, s, e, q, m)) == True{}: Bool}:
  match m:
    case Some{x}:
      Grows.refl(s)
    case None{}:
      Grows.trans(
        s,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
        Voting.Node.ask.new(
          n,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          e,
          q
        )
      )(
        Grows.to(
          s,
          s,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          Led.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          Grows.refl(s)
        )
      )(
        Ask.new.grows(
          n,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
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
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.ask(Basics.Envelope.of(e)))
  )

# the new requests among cells only grow a node
def Take.asks.grows(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Basics.Node
) -> {Reading.Node.grows(s, Voting.Take.asks(cs, old, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      Grows.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, +rest}:
      +s1 = Shared.Bool.when(
        Basics.Node,
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
  s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  k: Basics.Node -> Basics.Node,
  ih: @s2: Basics.Node -> {Reading.Node.grows(s2, k(s2)) == True{}: Bool}
) -> {
  State.after(s, m) == True{}: Bool
} -> {
  Reading.Node.grows(
    s,
    Maybe.default(
      &2,
      Basics.Node,
      Maybe.bind(&2, Basics.Node, Basics.Node, m, s2 => Some{k(s2)}),
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
  +s: Basics.Node,
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
  +s: Basics.Node
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

def Spec.Node.take_grows(s, t):
  +sent = Voting.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent)
  +s1 = Basics.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Basics.State.ledger(s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
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
        ~Ask.laws(),
        Basics.State.ledger(s),
        sent
      )
    )
  )(
    Grows.trans(
      s1,
      s2,
      Sealing.Sealed.take(bs, s2)
    )(
      Take.asks.grows(cs, Basics.State.ledger(s), s1)
    )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2))
  )

# after its ledger took in what was sent, a node only grows as it takes the
# rest in
def Take.tail(
  +s: Basics.Node,
  +t: Ledgers.State(Basics.Ask)
) -> {
  Reading.Node.grows(
    Basics.State.led(
      s,
      Ledgers.State.take(
        ~Basics.Ask,
        Basics.State.ledger(s),
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
  l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent)
  +s1 = Basics.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Basics.State.ledger(s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
    )
  )
  Grows.trans(
    s1,
    s2,
    Sealing.Sealed.take(bs, s2)
  )(
    Take.asks.grows(cs, Basics.State.ledger(s), s1)
  )(Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2))

# Node.fetch for the data ws itself
def Fetch.take(
  +b: Basics.Node,
  +ws: List<&2, U32>
) -> {
  Ledgers.State.get(
    ~Basics.Ask,
    Basics.State.ledger(b),
    Ledgers.Slot.data(Hashes.Sha.hash(ws))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
} -> {
  Ledgers.State.data(
    ~Basics.Ask,
    Basics.State.ledger(
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
  +l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(b), t)
  e =>
    Ledgers.State.data_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Ask.laws(),
      Basics.State.ledger(Basics.State.led(b, l1)),
      Basics.State.ledger(Voting.Node.take(b, t)),
      Hashes.Sha.hash(ws),
      ws
    )(Take.tail(b, t))(
      %Equal.sym(Ledgers.State(Basics.Ask), Basics.State.ledger(Basics.State.led(b, l1)), l1, Led.led(b, l1)): {Ledgers.State.data(~Basics.Ask, _, Hashes.Sha.hash(ws)) == Some{ws}: Maybe<&2, List<&2, U32>>}
      Ledgers.State.take_data(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(b), ws)(e))

def Spec.Node.fetch(a, b, h, ws):
  +ea => eb =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Ledgers.State.data(~Basics.Ask, Basics.State.ledger(a), h),
      Some{ws},
      ea
    ): {
      Ledgers.State.data(
        ~Basics.Ask,
        Basics.State.ledger(
          Voting.Node.take(b, Voting.Serve.put(_, Ledgers.State.empty(~Basics.Ask)))
        ),
        h
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Ledgers.State.data_hash(
      ~Basics.Ask,
      Basics.State.ledger(a),
      h,
      ws
    )(
      ea
    ): {
      Ledgers.State.data(
        ~Basics.Ask,
        Basics.State.ledger(
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
      %Equal.sym(Hashes.Hash, Hashes.Sha.hash(ws), h, Ledgers.State.data_hash(~Basics.Ask, Basics.State.ledger(a), h, ws)(ea)): {Ledgers.State.get(~Basics.Ask, Basics.State.ledger(b), Ledgers.Slot.data(_)) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
      eb)

# what a node does on each of some lines only grows it
def Steps.grows(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Basics.Node
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
  s: Basics.Node,
  m: Maybe<&2, Reading.Request>
) -> {Reading.Node.grows(s, Reading.Adopt.ask(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Reading.Request{e, q}}:
      Spec.Node.ask_grows(n, s, e, q)

# an adoption only grows a node, once the head m of the line is known
def Adopt.head.grows(
  n: String,
  +s: Basics.Node,
  m: Maybe<&2, Basics.Head>
) -> {Reading.Node.grows(s, Reading.Adopt.head(n, s, m)) == True{}: Bool}:
  match m:
    case None{}:
      Grows.refl(s)
    case Some{Basics.Head{r, b, next, t}}:
      Adopt.ask.grows(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line only grows a node
def Adopt.at.grows(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain
) -> {Reading.Node.grows(s, Reading.Adopt.at(n, s, c)) == True{}: Bool}:
  Adopt.head.grows(n, s, Basics.Node.head_of(s, c))

# the adoption of a line, if any, only grows a node
def Adopt.maybe.grows(
  n: String,
  s: Basics.Node,
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
  +s: Basics.Node
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
  +s: Basics.Node
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

def Spec.Node.sync_grows(n, s, t):
  +s1 = Voting.Node.take(s, t)
  +cs = Voting.Sync.lines(s, s1, t)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
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
    Spec.Node.take_grows(s, t)
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
