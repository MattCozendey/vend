import Base
import ../branch/merges.bend as Merges
import ../group/owners.bend as Owners
import ../resource/formats.bend as Formats
import ../resource/resources.bend as Resources
import ../shared/replica.bend as Replicas
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/text.bend as Texts
import ../shared/shared/tree.bend as Trees
import ../shared/vend.bend as Vend
import ./requests.bend as Requests

# Reads
# -----
# A writer reads its own pending write first: at the head of a branch, the
# newest write of the resource that the writer asked for and that the branch
# did not decide yet. It is a read of the ledger, so the writer reads the
# same at every node that holds its request.

# a pending write: its time, its request, and its content
type Draft is Data:
  Draft{time: String, request: String, content: Requests.Content}

# the draft b is newer than the draft a: by its time, then by its request
def Draft.newer(a: Draft, b: Draft) -> Bool:
  match a b:
    case Draft{t1, r1, c1} Draft{+t2, r2, c2}:
      +t1 = t1
      List.any.if(
        u => List.all.if(v => String.is_lt(r1, r2), String.eq(t1, t2)),
        String.is_lt(t1, t2)
      )

# the newer of the drafts m and x
def Draft.pick(m: Maybe<&2, Draft>, +x: Draft) -> Maybe<&2, Draft>:
  match m:
    case None{}:
      Some{x}
    case Some{+a}:
      Shared.Bool.when(Maybe<&2, Draft>, Draft.newer(a, x), u => Some{x}, u => Some{a})

# the content that the change q gives the resource n on the branch b, when it
# writes it there
def Draft.content(b: Vend.Branch, n: Resources.Name, q: Requests.Ask) -> Maybe<&2, Requests.Content>:
  match b q:
    case Vend.Branch{st, x} Requests.Ask.On{st2, Some{x2}, Requests.Change.Write{m, base, c}}:
      Shared.Maybe.when(
        Requests.Content,
        List.all.if(
          u => List.all.if(v => Resources.Name.is_eq(m, n), String.eq(x2, x)),
          Hashes.Hash.is_eq(st2, st)
        ),
        u => Some{c}
      )
    case _ _:
      None{}

# the draft of the entry e for the resource n on the branch b, when it writes
# it there and its ID has no outcome at the tip t of the branch
def Draft.of(
  ~d: Vend.Led(),
  l: Vend.L(d),
  t: Replicas.Tip,
  b: Vend.Branch,
  n: Resources.Name,
  e: Ledgers.Entry<Requests.Ask>
) -> Maybe<&2, Draft>:
  match e:
    case Ledgers.Entry.Ask{Ledgers.Id{w, +r}, time, q}:
      Maybe.bind(
        &2,
        Requests.Content,
        Draft,
        Draft.content(b, n, q),
        c => Shared.Maybe.when(
          Draft,
          Maybe.is_none(
            &2,
            Replicas.Out,
            Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, Ledgers.Id{w, r})
          ),
          u => Some{Draft{time, r, c}}
        )
      )
    case _:
      None{}

# the newest draft among the entries es, after the draft m
def Draft.newest(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +b: Vend.Branch,
  +n: Resources.Name,
  es: List<&2, Ledgers.Entry<Requests.Ask>>,
  +m: Maybe<&2, Draft>
) -> Maybe<&2, Draft>:
  match es:
    case Nil{}:
      m
    case Con{e, rest}:
      Draft.newest(
        ~d,
        l,
        t,
        b,
        n,
        rest,
        Maybe.default(
          &2,
          Maybe<&2, Draft>,
          Maybe.bind(&2, Draft, Maybe<&2, Draft>, Draft.of(~d, l, t, b, n, e), x => Some{Draft.pick(m, x)}),
          m
        )
      )

# the root of the content that the draft m gives the resource n, at the tip t
# of its branch
def Draft.root(
  ~d: Vend.Led(),
  l: Vend.L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  m: Draft
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match m:
    case Draft{time, r, c}:
      Vend.Content.find(~d, l, t, n, c)

# the root that the draft m gives the resource n, else what k gives
def Draft.or(
  ~d: Vend.Led(),
  l: Vend.L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  m: Maybe<&2, Draft>,
  k: Unit -> Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match m:
    case None{}:
      k(Unit{})
    case Some{x}:
      Draft.root(~d, l, t, n, x)

# what the writer w reads of the resource n at the head of the branch b,
# whose newest tip is t: its own newest pending write, else what the branch
# holds
def Head.read(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  w: String,
  b: Vend.Branch,
  +n: Resources.Name
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Draft.or(
    ~d,
    l,
    t,
    n,
    Draft.newest(
      ~d,
      l,
      t,
      b,
      n,
      Ledgers.Kind.asks(Requests.Ask, Replicas.Led.kind(Requests.Ask.machine(), d))(l)(w),
      None{}
    ),
    u => Vend.Res.find(~d, l, Replicas.Tip.content(t), n)
  )

# the root of the resource n at the version i of the branch whose newest tip
# is t
def Version.read(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  t: Replicas.Tip,
  i: Ledgers.Id,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Maybe<&2, Hashes.Hash>,
    Maybe<&2, Requests.Res>,
    Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i),
    h => Vend.Res.find(~d, l, h, n)
  )

# the root of what the writer w reads of the resource n at the point p, whose
# branch has the newest tip t
def Point.read(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  w: String,
  n: Resources.Name,
  p: Vend.Point
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match p:
    case Vend.Point.Head{b}:
      Head.read(~d, l, t, w, b, n)
    case Vend.Point.At{b, i}:
      Version.read(~d, l, t, i, n)
    case Vend.Point.Mark{b, m}:
      Maybe.bind(
        &2,
        Ledgers.Id,
        Maybe<&2, Requests.Res>,
        Replicas.Tip.label(~Requests.Ask.machine(), ~d, l, t, m),
        i => Version.read(~d, l, t, i, n)
      )

# the branch of the point p
def Point.branch(p: Vend.Point) -> Vend.Branch:
  match p:
    case Vend.Point.Head{b}:
      b
    case Vend.Point.At{b, i}:
      b
    case Vend.Point.Mark{b, m}:
      b

# the resource that the writer w reads as n at the point p (none: the
# ledger lacks a part; some none: it is not there)
def Node.find(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  w: String,
  n: Resources.Name,
  +p: Vend.Point
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Maybe<&2, Requests.Res>,
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, Vend.Branch.line(Point.branch(p))),
    t => Point.read(~d, ~kern, l, t, w, n, p)
  )

# the bytes that the writer w reads of the resource n at the point p (none:
# the resource is not there, or the ledger lacks a part)
def Node.read(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  w: String,
  n: Resources.Name,
  +p: Vend.Point
) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Texts.Bytes(),
    Node.find(~d, ~kern, l, w, n, p),
    m => Vend.Res.bytes(~d, l, m)
  )

# What a front lists
# ------------------
# Each is a read of the ledger. A clear def may walk a tree or a history: the
# cost of a fast one is what it gives, not what the node holds.

# the newest tip of the branch b
def Branch.head(~d: Vend.Led(), ~kern: Vend.Kern(d), l: Vend.L(d), b: Vend.Branch) -> Maybe<&2, Replicas.Tip>:
  Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, Vend.Branch.line(b))

# k versions of the branch b, from the number n, in order: a reader asks for
# a part of a history (none: l lacks a part)
def Node.versions(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  b: Vend.Branch,
  n: U32,
  k: Nat
) -> Maybe<&2, List<&2, Ledgers.Id>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, Ledgers.Id>,
    Branch.head(~d, ~kern, l, b),
    t => Maybe.map(
      &2,
      List<&2, Replicas.Taken>,
      List<&2, Ledgers.Id>,
      Replicas.Taken.ids,
      Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, t, n)
    )
  )

# the name of the resource of the binding x, when it is one: its key names a
# resource and its value is the code of one, as Res.find reads it
def Res.named(x: Trees.Binding) -> Maybe<&2, Resources.Name>:
  match x:
    case Trees.Binding{k, v}:
      Maybe.bind(&2, Requests.Res, Resources.Name, Vend.Res.found(Some{v}), r => Merges.Res.name(k))

# the names of the resources among the bindings xs
def Res.names(xs: List<&2, Trees.Binding>) -> List<&2, Resources.Name>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Shared.Maybe.cons(Resources.Name, Res.named(x), Res.names(rest))

# the names of the resources among the keys ks
def Keys.names(ks: List<&2, List<&2, U32>>) -> List<&2, Resources.Name>:
  match ks:
    case Nil{}:
      []
    case Con{k, rest}:
      Shared.Maybe.cons(Resources.Name, Merges.Res.name(k), Keys.names(rest))

# the resources of the tree whose root is h
def Tree.resources(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Resources.Name>, Res.names, Vend.Tree.range(~d, l, h, [0]))

# the resources of the branch b at its head
def Node.resources(~d: Vend.Led(), ~kern: Vend.Kern(d), +l: Vend.L(d), b: Vend.Branch) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, Resources.Name>,
    Branch.head(~d, ~kern, l, b),
    t => Tree.resources(~d, l, Replicas.Tip.content(t))
  )

# the members of the group g of the store st, or that g is not there (none:
# l lacks a node, so a read cannot tell)
def Node.members(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  st: Hashes.Hash,
  g: String
) -> Maybe<&2, Maybe<&2, List<&2, Requests.Member>>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Maybe<&2, List<&2, Requests.Member>>,
    Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st),
    t => Replicas.Tip.known(
      ~List<&2, Requests.Member>,
      ~Requests.Members.code,
      ~Requests.Members.code.read,
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Owners.Key.group(g))
    )
  )

# the bytes of the resource m, empty when it is not there (none: l lacks a
# node)
def Res.bytes.or_empty(~d: Vend.Led(), l: Vend.L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case None{}:
      Some{[]}
    case Some{x}:
      Vend.Root.bytes(~d, l, Vend.Res.root(x))

# Res.diff once the hash m of the format to read with is known (none: neither
# resource is there)
def Res.diff.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  a: Maybe<&2, Requests.Res>,
  b: Maybe<&2, Requests.Res>,
  m: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, Formats.Change>>:
  match m:
    case None{}:
      Some{[]}
    case Some{h}:
      Maybe.bind(
        &2,
        Formats.Format,
        List<&2, Formats.Change>,
        Vend.Format.at(~d, l, h),
        f => Maybe.bind(
          &2,
          Texts.Bytes(),
          List<&2, Formats.Change>,
          Res.bytes.or_empty(~d, l, a),
          xa => Maybe.bind(
            &2,
            Texts.Bytes(),
            List<&2, Formats.Change>,
            Res.bytes.or_empty(~d, l, b),
            xb => Some{Formats.Format.changes(f, xa, xb)}
          )
        )
      )

# what changed from the resource a to the resource b, in the format of b, else
# of a (none of them: nothing changed); none: l lacks a part
def Res.diff(~d: Vend.Led(), +l: Vend.L(d), +a: Maybe<&2, Requests.Res>, +b: Maybe<&2, Requests.Res>) -> Maybe<&2, List<&2, Formats.Change>>:
  Res.diff.of(~d, l, a, b, Merges.Res.format.of(b, a))

# what changed in the resource n from the point a to the point b, as the
# writer w reads them, in the format of the resource: a resource that is not
# there is empty (none: l lacks a part)
def Node.diff(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +w: String,
  +n: Resources.Name,
  +a: Vend.Point,
  b: Vend.Point
) -> Maybe<&2, List<&2, Formats.Change>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    List<&2, Formats.Change>,
    Node.find(~d, ~kern, l, w, n, a),
    ra => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      List<&2, Formats.Change>,
      Node.find(~d, ~kern, l, w, n, b),
      rb => Res.diff(~d, l, ra, rb)
    )
  )

# a branch, with its owners and its newest version (none: it has none yet)
type BranchEntry is Data:
  BranchEntry{branch: Vend.Branch, owners: List<&2, String>, head: Maybe<&2, Ledgers.Id>}

# the entry of the branch b, whose newest tip is m (none: l lacks a part)
def BranchEntry.of(~d: Vend.Led(), l: Vend.L(d), b: Vend.Branch, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, BranchEntry>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      Maybe.map(
        &2,
        Maybe<&2, Ledgers.Id>,
        BranchEntry,
        v => BranchEntry{b, Replicas.Tip.voters(t), v},
        Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t)
      )

# the name of the branch that the binding x of the log of a store starts
def Branch.started(x: Trees.Binding) -> Maybe<&2, String>:
  match x:
    case Trees.Binding{Con{5, r}, v}:
      Codes.Code.whole.read(~String, ~Codes.Code.text, ~Codes.Code.text.read, r)
    case _:
      None{}

# the names of the branches that the bindings xs of the log of a store start
def Branches.names(xs: List<&2, Trees.Binding>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Shared.Maybe.cons(String, Branch.started(x), Branches.names(rest))

# the branch of each of the names ns, in the store st
def Branches.of(+st: Hashes.Hash, ns: List<&2, String>) -> List<&2, Vend.Branch>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      Vend.Branch{st, n} <> Branches.of(st, rest)

# the branches of the store st, by the log of its newest tip m (none: l
# lacks the tip or a node of the log, so a read cannot tell)
def Store.branches(~d: Vend.Led(), l: Vend.L(d), +st: Hashes.Hash, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, List<&2, Vend.Branch>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.map(
        &2,
        List<&2, Trees.Binding>,
        List<&2, Vend.Branch>,
        xs => Branches.of(st, Branches.names(xs)),
        Vend.Tree.range(~d, l, Replicas.Tip.log(t), [5])
      )

# the entries of the branches bs (none: l lacks the head of one)
def Branches.entries(~d: Vend.Led(), ~kern: Vend.Kern(d), +l: Vend.L(d), bs: List<&2, Vend.Branch>) -> Maybe<&2, List<&2, BranchEntry>>:
  match bs:
    case Nil{}:
      Some{[]}
    case Con{+b, rest}:
      Maybe.bind(
        &2,
        BranchEntry,
        List<&2, BranchEntry>,
        BranchEntry.of(~d, l, b, Branch.head(~d, ~kern, l, b)),
        e => Maybe.map(&2, List<&2, BranchEntry>, List<&2, BranchEntry>, r => e <> r, Branches.entries(~d, ~kern, l, rest))
      )

# every branch of the store st
def Node.branches(~d: Vend.Led(), ~kern: Vend.Kern(d), +l: Vend.L(d), +st: Hashes.Hash) -> Maybe<&2, List<&2, BranchEntry>>:
  Maybe.bind(
    &2,
    List<&2, Vend.Branch>,
    List<&2, BranchEntry>,
    Store.branches(~d, l, st, Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st)),
    bs => Branches.entries(~d, ~kern, l, bs)
  )

# What a work uses
# ----------------
# A resource uses what it imports, directly or not. An import keeps its
# target as written (Formats.Edge); its language says how the target is found
# (Formats.Find, Resources.Name.candidates) and what it brings
# (Formats.Brings). An import that brings all of a place names each resource
# under it.

# Names.first once it is known whether the tree holds the name n (m); go
# looks at the names after it
def Names.first.at(
  m: Maybe<&2, Requests.Res>,
  n: Resources.Name,
  go: Unit -> Maybe<&2, Maybe<&2, Resources.Name>>
) -> Maybe<&2, Maybe<&2, Resources.Name>>:
  match m:
    case Some{x}:
      Some{Some{n}}
    case None{}:
      go(Unit{})

# the first of the names ns that is a resource of the tree h, or that none is
# (none: l lacks a node, so a read cannot tell)
def Names.first(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>
) -> Maybe<&2, Maybe<&2, Resources.Name>>:
  match ns:
    case Nil{}:
      Some{None{}}
    case Con{+n, rest}:
      Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Maybe<&2, Resources.Name>,
        Vend.Res.find(~d, l, h, n),
        m => Names.first.at(m, n, u => Names.first(~d, l, h, rest))
      )

# each resource under the first candidate cs, when the import brings all of
# its target (br), else none
def Import.under(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  br: Formats.Brings,
  cs: List<&2, Resources.Name>
) -> Maybe<&2, List<&2, Resources.Name>>:
  match br cs:
    case Formats.Brings.Named{} x:
      Some{[]}
    case y Nil{}:
      Some{[]}
    case y Con{+c, rest}:
      Maybe.map(
        &2,
        List<&2, Resources.Name>,
        List<&2, Resources.Name>,
        ns => Resources.Name.under(c, ns),
        Tree.resources(~d, l, h)
      )

# the names that an import names once its first candidate there is known (m):
# that one, else what under gives
def Import.names.of(
  m: Maybe<&2, Resources.Name>,
  under: Unit -> Maybe<&2, List<&2, Resources.Name>>
) -> Maybe<&2, List<&2, Resources.Name>>:
  match m:
    case Some{x}:
      Some{[x]}
    case None{}:
      under(Unit{})

# the resources that the import x of the resource n names, in the tree h: the
# first of its candidates that is there; else, when it brings all of its
# target, each resource under the first candidate
def Import.names(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  x: Formats.Import
) -> Maybe<&2, List<&2, Resources.Name>>:
  match x:
    case Formats.Import{Formats.Edge{target, alias, ns, conds}, br, fi}:
      +cs = Resources.Name.candidates(n, fi, Texts.Bytes.to_text(target))
      Maybe.bind(
        &2,
        Maybe<&2, Resources.Name>,
        List<&2, Resources.Name>,
        Names.first(~d, l, h, cs),
        m => Import.names.of(m, u => Import.under(~d, l, h, br, cs))
      )

# the resources that the imports xs of the resource n name, in the tree h
def Imports.names(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  xs: List<&2, Formats.Import>
) -> Maybe<&2, List<&2, Resources.Name>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{+x, rest}:
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        List<&2, Resources.Name>,
        Shared.Bool.when(
          Maybe<&2, List<&2, Resources.Name>>,
          Formats.Import.holds(view, x),
          u => Import.names(~d, l, h, n, x),
          u => Some{[]}
        ),
        a => Maybe.map(
          &2,
          List<&2, Resources.Name>,
          List<&2, Resources.Name>,
          b => List.append(&2, Resources.Name, a, b),
          Imports.names(~d, l, view, h, n, rest)
        )
      )

# Res.imports once the resource m is known
def Res.imports.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  m: Maybe<&2, Requests.Res>
) -> Maybe<&2, List<&2, Resources.Name>>:
  match m:
    case None{}:
      Some{[]}
    case Some{+x}:
      Maybe.bind(
        &2,
        Formats.Format,
        List<&2, Resources.Name>,
        Vend.Res.format(~d, l, x),
        f => Maybe.bind(
          &2,
          Texts.Bytes(),
          List<&2, Resources.Name>,
          Vend.Root.bytes(~d, l, Vend.Res.root(x)),
          bs => Imports.names(~d, l, view, h, n, Formats.Format.uses(f, [bs]))
        )
      )

# what the resource n imports directly, in the tree whose root is h, as its
# format reads it: each import found as its language finds it (nothing while
# l lacks the resource)
def Res.imports(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name
) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    List<&2, Resources.Name>,
    Vend.Res.find(~d, l, h, n),
    m => Res.imports.of(~d, l, view, h, n, m)
  )

# the key of the resource n in the graph of imports
def Name.key(n: Resources.Name) -> List<&2, U32>:
  Resources.Name.code(n, [])

# the key of each of the resources ns
def Names.keys(ns: List<&2, Resources.Name>) -> List<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      Name.key(n) <> Names.keys(rest)

# the graph g with the imports of each of the resources ns of the tree h: a
# resource leads to each resource that it imports
def Uses.graph(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  g: Reaches.Graph
) -> Maybe<&2, Reaches.Graph>:
  match ns:
    case Nil{}:
      Some{g}
    case Con{+n, rest}:
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Reaches.Graph,
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.graph(~d, l, view, h, rest, Reaches.Graph.links(Names.keys(ns2), Name.key(n), g))
      )

# the resource used is the resource changed, or uses it through its imports,
# at any depth, in the tree whose root is h. A clear def: it reads each
# resource of the tree
def Uses.reaches(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +used: Resources.Name,
  +changed: Resources.Name
) -> Maybe<&2, Bool>:
  Shared.Bool.when(
    Maybe<&2, Bool>,
    Resources.Name.is_eq(used, changed),
    u => Some{True{}},
    u => Maybe.bind(
      &2,
      Reaches.Graph,
      Bool,
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Reaches.Graph,
        Tree.resources(~d, l, h),
        ns => Uses.graph(~d, l, view, h, ns, Reaches.Graph.new())
      ),
      g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
    )
  )

# a change elsewhere that touches what a branch uses: the version of the
# branch from wrote the resource changed, and the resource used of the branch
# is that resource or uses it
type Touch is Data:
  Touch{
    from: Vend.Branch,
    version: Ledgers.Id,
    changed: Resources.Name,
    branch: Vend.Branch,
    used: Resources.Name
  }

# a and b are branches of one store, and not the same branch
def Branch.other(a: Vend.Branch, b: Vend.Branch) -> Bool:
  match a b:
    case Vend.Branch{s1, n1} Vend.Branch{s2, n2}:
      List.all.if(u => Bool.not(String.eq(n1, n2)), Hashes.Hash.is_eq(s1, s2))

# whether what the resource n holds in the tree h is not what it holds in
# the tree h2 (none: l lacks a node of either, so a read cannot tell)
def Res.differs(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name
) -> Maybe<&2, Bool>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Bool,
    Vend.Res.find(~d, l, h, n),
    a => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Bool,
      Vend.Res.find(~d, l, h2, n),
      b => Some{Bool.not(Vend.Res.same(a, b))}
    )
  )

# a version that changed a resource, and the time of its request
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the versions among xs that changed the resource n, the first of which came
# after the tree h0, at the tip t (none: l lacks a part)
def Log.entries(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  xs: List<&2, Replicas.Taken>,
  +h0: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, List<&2, LogEntry>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{Replicas.Taken{+i, +h}, rest}:
      Maybe.bind(
        &2,
        Bool,
        List<&2, LogEntry>,
        Res.differs(~d, l, h, h0, n),
        c => Maybe.bind(
          &2,
          List<&2, LogEntry>,
          List<&2, LogEntry>,
          Log.entries(~d, l, t, n, rest, h),
          +r => Shared.Bool.when(
            Maybe<&2, List<&2, LogEntry>>,
            c,
            u => Maybe.bind(
              &2,
              Replicas.Out,
              List<&2, LogEntry>,
              Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i),
              o => Maybe.map(
                &2,
                String,
                List<&2, LogEntry>,
                time => LogEntry{i, time} <> r,
                Replicas.Out.time(~Requests.Ask.machine(), ~d, l, o)
              )
            ),
            u => Some{r}
          )
        )
      )

# Node.log once the newest tip t of the branch is known
def Node.log.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  n: Resources.Name,
  +from: U32,
  k: Nat
) -> Maybe<&2, List<&2, LogEntry>>:
  Maybe.bind(
    &2,
    List<&2, Replicas.Taken>,
    List<&2, LogEntry>,
    Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, t, from),
    xs => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      List<&2, LogEntry>,
      Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, t, from),
      h0 => Log.entries(~d, l, t, n, xs, h0)
    )
  )

# the versions of the branch b that changed the resource n, among k versions
# from the number from (none: l lacks a part)
def Node.log(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  n: Resources.Name,
  b: Vend.Branch,
  from: U32,
  k: Nat
) -> Maybe<&2, List<&2, LogEntry>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, LogEntry>,
    Branch.head(~d, ~kern, l, b),
    t => Node.log.at(~d, l, t, n, from, k)
  )

# whether the version that the line took as the number m, at the tip t, wrote
# the resource n: the resource holds after it what it did not hold before it
# (none: l lacks a part)
def Version.wrote(~d: Vend.Led(), +l: Vend.L(d), +t: Replicas.Tip, +m: U32, +n: Resources.Name) -> Maybe<&2, Bool>:
  Maybe.bind(
    &2,
    Maybe<&2, Hashes.Hash>,
    Bool,
    Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, t, m),
    h0 => Maybe.bind(
      &2,
      Replicas.Taken,
      Bool,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, m),
      x => Res.differs(~d, l, Replicas.Taken.root(x), h0, n)
    )
  )

# Touch.holds once the newest tips tf of the branch from and tb of the branch
# are known
def Touch.holds.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name
) -> Maybe<&2, Bool>:
  +hb = Replicas.Tip.content(tb)
  Maybe.bind(
    &2,
    U32,
    Bool,
    Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v),
    m => Maybe.bind(
      &2,
      Bool,
      Bool,
      Version.wrote(~d, l, tf, m, changed),
      wrote => Shared.Bool.when(
        Maybe<&2, Bool>,
        wrote,
        u => Maybe.bind(
          &2,
          Maybe<&2, Hashes.Hash>,
          Bool,
          Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v),
          h => Maybe.bind(
            &2,
            Bool,
            Bool,
            Res.differs(~d, l, h, hb, changed),
            differs => Shared.Bool.when(
              Maybe<&2, Bool>,
              differs,
              u2 => Maybe.bind(
                &2,
                Maybe<&2, Requests.Res>,
                Bool,
                Vend.Res.find(~d, l, hb, used),
                r => Shared.Bool.when(
                  Maybe<&2, Bool>,
                  Maybe.is_some(&2, Requests.Res, r),
                  u3 => Uses.reaches(~d, l, view, hb, used, changed),
                  u3 => Some{False{}}
                )
              ),
              u2 => Some{False{}}
            )
          )
        ),
        u => Some{False{}}
      )
    )
  )

# whether the touch x holds: its two branches are of one store and are not the
# same; its version is a version of the branch from, and wrote the resource
# changed; the branch does not hold what that version gave the resource; and
# the resource used is of the branch, and is the one changed or uses it. So a
# writer is told only about changes to what its work uses (none: l lacks a
# part, so a read cannot tell)
def Touch.holds(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  x: Touch
) -> Maybe<&2, Bool>:
  match x:
    case Touch{+from, v, changed, +b, used}:
      Shared.Bool.when(
        Maybe<&2, Bool>,
        Branch.other(from, b),
        u => Maybe.bind(
          &2,
          Replicas.Tip,
          Bool,
          Branch.head(~d, ~kern, l, from),
          tf => Maybe.bind(
            &2,
            Replicas.Tip,
            Bool,
            Branch.head(~d, ~kern, l, b),
            tb => Touch.holds.at(~d, l, view, tf, tb, v, changed, used)
          )
        ),
        u => Some{False{}}
      )

# the graph g with the users of each import of the resources ns of the tree h:
# a resource leads to each resource that imports it. It is made once for a
# branch, and each search of it costs what it finds
def Uses.users(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  g: Reaches.Graph
) -> Maybe<&2, Reaches.Graph>:
  match ns:
    case Nil{}:
      Some{g}
    case Con{+n, rest}:
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Reaches.Graph,
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.users(~d, l, view, h, rest, Reaches.Graph.back(Names.keys(ns2), Name.key(n), g))
      )

# a touch of the version v of the branch from on the branch b, for the
# resource c and each resource of used that is c or that the set reach holds
def Touches.of(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  used: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit)
) -> List<&2, Touch>:
  match used:
    case Nil{}:
      []
    case Con{+u, rest}:
      List.filter.put(
        Touch,
        Touch{from, v, c, b, u},
        Touches.of(from, v, c, b, rest, reach),
        List.any.if(
          w => Crits.Dict.has(Unit, reach, Name.key(u)),
          Resources.Name.is_eq(u, c)
        )
      )

# the touches of the resource c when touched holds, else none: the search of
# the users of c runs only then
def Touches.when(
  touched: Bool,
  from: Vend.Branch,
  v: Ledgers.Id,
  +c: Resources.Name,
  b: Vend.Branch,
  used: List<&2, Resources.Name>,
  users: Reaches.Graph
) -> List<&2, Touch>:
  match touched:
    case False{}:
      []
    case True{}:
      Touches.of(from, v, c, b, used, Reaches.Graph.reach(users, Name.key(c)))

# the touches of the version v of the branch from, whose tree is h and came
# after the tree h0, on the branch b whose tree is hb: for each resource of
# changed that v wrote, and that b does not hold as v gave it
def Touches.each(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph
) -> Maybe<&2, List<&2, Touch>>:
  match changed:
    case Nil{}:
      Some{[]}
    case Con{+c, rest}:
      Maybe.bind(
        &2,
        Bool,
        List<&2, Touch>,
        Maybe.bind(
          &2,
          Bool,
          Bool,
          Res.differs(~d, l, h, h0, c),
          w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
        ),
        touched => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, Touches.when(touched, from, v, c, b, used, users), r),
          Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users)
        )
      )

# the touches of the versions xs of the branch from, the first of which came
# after the tree h0 and has the number n, on the branch b; a version counts
# when its number reads back by its ID at the tip tf (Replicas.Tip.number)
def Touches.all(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph
) -> Maybe<&2, List<&2, Touch>>:
  match xs:
    case Nil{}:
      Some{[]}
    case Con{Replicas.Taken{+i, +h}, rest}:
      Maybe.bind(
        &2,
        List<&2, List<&2, U32>>,
        List<&2, Touch>,
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, h),
        ks => Maybe.bind(
          &2,
          U32,
          List<&2, Touch>,
          Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
          m => Maybe.bind(
            &2,
            List<&2, Touch>,
            List<&2, Touch>,
            Shared.Bool.when(
              Maybe<&2, List<&2, Touch>>,
              U32.is_eq(m, n),
              u => Touches.each(~d, l, from, i, h0, h, Keys.names(ks), b, hb, used, users),
              u => Some{[]}
            ),
            a => Maybe.map(
              &2,
              List<&2, Touch>,
              List<&2, Touch>,
              r => List.append(&2, Touch, a, r),
              Touches.all(~d, l, from, tf, rest, U32.inc(n), h, b, hb, used, users)
            )
          )
        )
      )

# Branch.touches once the newest tips tf of the branch from and tb of the
# branch b are known: the resources of b and their users are read once
def Branch.touches.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  from: Vend.Branch,
  +tf: Replicas.Tip,
  b: Vend.Branch,
  tb: Replicas.Tip
) -> Maybe<&2, List<&2, Touch>>:
  +hb = Replicas.Tip.content(tb)
  Maybe.bind(
    &2,
    List<&2, Trees.Binding>,
    List<&2, Touch>,
    Vend.Tree.range(~d, l, hb, [0]),
    +xs => Maybe.bind(
      &2,
      Reaches.Graph,
      List<&2, Touch>,
      Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
      users => Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(
        ~d,
        l,
        from,
        tf,
        xs2,
        0,
        None{},
        b,
        hb,
        Res.names(xs),
        users
        )
      )
    )
  )

# Branch.touches once the newest tip m of the branch b is known
def Branch.touches.of(
  ~d: Vend.Led(),
  l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  from: Vend.Branch,
  tf: Replicas.Tip,
  b: Vend.Branch,
  m: Maybe<&2, Replicas.Tip>
) -> Maybe<&2, List<&2, Touch>>:
  match m:
    case None{}:
      None{}
    case Some{tb}:
      Branch.touches.at(~d, l, view, from, tf, b, tb)

# the changes of the branch from that touch what the branch b uses: of each
# version of from, each resource that it wrote and that b does not hold as it
# gave it, with each resource of b that is that resource or uses it. The cost
# is the history of from and the resources of b, each read once
def Branch.touches(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +b: Vend.Branch
) -> Maybe<&2, List<&2, Touch>>:
  Shared.Bool.when(
    Maybe<&2, List<&2, Touch>>,
    Branch.other(from, b),
    u => Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, Touch>,
      Branch.head(~d, ~kern, l, from),
      tf => Branch.touches.of(~d, l, view, from, tf, b, Branch.head(~d, ~kern, l, b))
    ),
    u => Some{[]}
  )

# a and b are the same branch
def Branch.is_eq(a: Vend.Branch, b: Vend.Branch) -> Bool:
  match a b:
    case Vend.Branch{s1, n1} Vend.Branch{s2, n2}:
      List.all.if(u => String.eq(n1, n2), Hashes.Hash.is_eq(s1, s2))

# a and b are the same touch
def Touch.is_eq(a: Touch, b: Touch) -> Bool:
  match a b:
    case Touch{f1, v1, c1, b1, u1} Touch{f2, v2, c2, b2, u2}:
      List.all.if(
        w => List.all.if(
          w2 => List.all.if(
            w3 => List.all.if(w4 => Resources.Name.is_eq(u1, u2), Branch.is_eq(b1, b2)),
            Resources.Name.is_eq(c1, c2)
          ),
          Ledgers.Id.is_eq(v1, v2)
        ),
        Branch.is_eq(f1, f2)
      )

# the branch that the touch x is on
def Touch.branch(x: Touch) -> Vend.Branch:
  match x:
    case Touch{f, v, c, b, u}:
      b

# the changes of each of the branches es that touch what the branch b uses
def Branches.touch(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  es: List<&2, BranchEntry>,
  +b: Vend.Branch
) -> Maybe<&2, List<&2, Touch>>:
  match es:
    case Nil{}:
      Some{[]}
    case Con{BranchEntry{from, os, hd}, rest}:
      Maybe.bind(
        &2,
        List<&2, Touch>,
        List<&2, Touch>,
        Branch.touches(~d, ~kern, l, view, from, b),
        a => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, a, r),
          Branches.touch(~d, ~kern, l, view, rest, b)
        )
      )

# the changes elsewhere that touch what the branch b uses, at any depth (none:
# l lacks a node that the answer reads, so it cannot tell yet)
def Node.affects(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +b: Vend.Branch
) -> Maybe<&2, List<&2, Touch>>:
  match b:
    case Vend.Branch{+st, +n}:
      Maybe.bind(
        &2,
        List<&2, BranchEntry>,
        List<&2, Touch>,
        Node.branches(~d, ~kern, l, st),
        es => Branches.touch(~d, ~kern, l, view, es, Vend.Branch{st, n})
      )

# what the changes of the branch from touch in each of the branches es
def Branches.touched(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  es: List<&2, BranchEntry>
) -> Maybe<&2, List<&2, Touch>>:
  match es:
    case Nil{}:
      Some{[]}
    case Con{BranchEntry{b, os, hd}, rest}:
      Maybe.bind(
        &2,
        List<&2, Touch>,
        List<&2, Touch>,
        Branch.touches(~d, ~kern, l, view, from, b),
        a => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, a, r),
          Branches.touched(~d, ~kern, l, view, from, rest)
        )
      )

# what the changes of the branch b touch elsewhere, in every build: the views
# of other writers are theirs (none: l lacks a part)
def Node.impact(~d: Vend.Led(), ~kern: Vend.Kern(d), +l: Vend.L(d), +b: Vend.Branch) -> Maybe<&2, List<&2, Touch>>:
  match b:
    case Vend.Branch{+st, +n}:
      Maybe.bind(
        &2,
        List<&2, BranchEntry>,
        List<&2, Touch>,
        Node.branches(~d, ~kern, l, st),
        es => Branches.touched(~d, ~kern, l, [], Vend.Branch{st, n}, es)
      )

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, the changes elsewhere that touch it in the build of a view, or the
# lies of the nodes in a store
type Topic is Data:
  Topic.Versions{branch: Vend.Branch}
  Topic.Conflicts{branch: Vend.Branch}
  Topic.Affects{branch: Vend.Branch, view: List<&2, Formats.Cond>}
  Topic.Lies{store: Hashes.Hash}

# an event of a topic. Lied: the node holds the proof that a node signed two
# ballots with one key in the store
type Notice is Data:
  Notice.Versioned{branch: Vend.Branch, version: Ledgers.Id}
  Notice.Conflicted{branch: Vend.Branch, version: Ledgers.Id}
  Notice.Touched{touch: Touch}
  Notice.Lied{store: Hashes.Hash, node: String}

# a notice of each of the versions ids of the branch b
def Notices.versions(+b: Vend.Branch, ids: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match ids:
    case Nil{}:
      []
    case Con{i, rest}:
      Notice.Versioned{b, i} <> Notices.versions(b, rest)

# a notice of each of the versions ids of the branch b after which a resource
# of the tree h still clashes
def Notices.conflicts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  ids: List<&2, Ledgers.Id>
) -> Maybe<&2, List<&2, Notice>>:
  match ids:
    case Nil{}:
      Some{[]}
    case Con{+i, rest}:
      Maybe.bind(
        &2,
        Bool,
        List<&2, Notice>,
        Vend.Clash.left(~d, l, h, i),
        c => Maybe.map(
          &2,
          List<&2, Notice>,
          List<&2, Notice>,
          r => List.filter.put(Notice, Notice.Conflicted{b, i}, r, c),
          Notices.conflicts(~d, l, h, b, rest)
        )
      )

# a notice of each of the touches xs
def Notices.touches(xs: List<&2, Touch>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Notice.Touched{x} <> Notices.touches(rest)

# a notice of each of the liars ns of the store st
def Notices.lies(+st: Hashes.Hash, ns: List<&2, String>) -> List<&2, Notice>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      Notice.Lied{st, n} <> Notices.lies(st, rest)

# the notices of the versions (all: every version; else those that still
# clash) of the branch b, whose newest tip is m (none: l lacks a part)
def Notices.branch(~d: Vend.Led(), +l: Vend.L(d), +b: Vend.Branch, all: Bool, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, List<&2, Notice>>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Notice>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(t)), l, t, 0),
        +xs => Shared.Bool.when(
          Maybe<&2, List<&2, Notice>>,
          all,
          u => Some{Notices.versions(b, Replicas.Taken.ids(xs))},
          u => Notices.conflicts(~d, l, Replicas.Tip.content(t), b, Replicas.Taken.ids(xs))
        )
      )

# every notice of the topic x, by what the ledger holds (none: l lacks a
# part, so a read cannot tell)
def Node.notices(~d: Vend.Led(), ~kern: Vend.Kern(d), +l: Vend.L(d), x: Topic) -> Maybe<&2, List<&2, Notice>>:
  match x:
    case Topic.Versions{+b}:
      Notices.branch(~d, l, b, True{}, Branch.head(~d, ~kern, l, b))
    case Topic.Conflicts{+b}:
      Notices.branch(~d, l, b, False{}, Branch.head(~d, ~kern, l, b))
    case Topic.Affects{b, view}:
      Maybe.map(&2, List<&2, Touch>, List<&2, Notice>, Notices.touches, Node.affects(~d, ~kern, l, view, b))
    case Topic.Lies{+st}:
      Some{Notices.lies(st, Ledgers.Kind.liars(Requests.Ask, Replicas.Led.kind(Requests.Ask.machine(), d))(l)(st))}

# Touches, proven
# -----------------
# The helpers of Node.affects_holds and Node.affects_complete.

# a bind that gives y: its read gives some a, and its rest gives y from a
def Affects.bind_some(
  -A: Data,
  -B: Data,
  -P: Type,
  m: Maybe<&2, A>,
  -f: A -> Maybe<&2, B>,
  -y: B,
  k: @a: A -> {m == Some{a}: Maybe<&2, A>} -> {f(a) == Some{y}: Maybe<&2, B>} -> P
) -> {Maybe.bind(&2, A, B, m, f) == Some{y}: Maybe<&2, B>} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(B, y, e))
    case Some{+a}:
      e => k(a)({==})(e)

# a map that gives y: its read gives some a, and y is f of a
def Affects.map_some(
  -A: Data,
  -B: Data,
  -P: Type,
  -f: A -> B,
  m: Maybe<&2, A>,
  -y: B,
  k: @a: A -> {m == Some{a}: Maybe<&2, A>} -> {f(a) == y: B} -> P
) -> {Maybe.map(&2, A, B, f, m) == Some{y}: Maybe<&2, B>} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(B, y, e))
    case Some{+a}:
      e => k(a)({==})(Shared.Maybe.some_inj(B, f(a), y, e))

# a choice that gives z: the test is True and the first gives z, or it is
# False and the second does
def Affects.when_is(
  -A: Type,
  -P: Type,
  b: Bool,
  -k: Unit -> A,
  -e: Unit -> A,
  -z: A,
  kt: {b == True{}: Bool} -> {k(Unit{}) == z: A} -> P,
  kf: {b == False{}: Bool} -> {e(Unit{}) == z: A} -> P
) -> {Shared.Bool.when(A, b, k, e) == z: A} -> P:
  match b:
    case True{}:
      h => kt({==})(h)
    case False{}:
      h => kf({==})(h)

# a branch is the same as itself
def Affects.branch_refl(a: Vend.Branch) -> {Branch.is_eq(a, a) == True{}: Bool}:
  match a:
    case Vend.Branch{+s, +n}:
      Shared.List.all.if_both(
        Hashes.Hash.is_eq(s, s),
        u => String.eq(n, n)
      )(Hashes.Hash.is_eq_refl(s))(Texts.String.eq_refl(n))

# branches that are the same are equal
def Affects.branch_sound(a: Vend.Branch, b: Vend.Branch) -> {Branch.is_eq(a, b) == True{}: Bool} -> {a == b: Vend.Branch}:
  match a b:
    case Vend.Branch{+s1, +n1} Vend.Branch{+s2, +n2}:
      +h =>
        %Equal.sym(
          Hashes.Hash,
          s1,
          s2,
          Hashes.Hash.is_eq_sound(s1, s2)(Shared.List.all.if_hit(Hashes.Hash.is_eq(s1, s2), u => String.eq(n1, n2))(h))
        ): {Vend.Branch{_, n1} == Vend.Branch{s2, n2}: Vend.Branch}
        %Equal.sym(
          String,
          n1,
          n2,
          Texts.String.eq_sound(n1, n2)(Shared.List.all.if_rest(Hashes.Hash.is_eq(s1, s2), u => String.eq(n1, n2))(h))
        ): {Vend.Branch{s2, _} == Vend.Branch{s2, n2}: Vend.Branch}
        {==}

# a touch is the same as itself
def Affects.touch_refl(a: Touch) -> {Touch.is_eq(a, a) == True{}: Bool}:
  match a:
    case Touch{+f, +v, +c, +b, +u}:
      +r4 = List.all.if(w4 => Resources.Name.is_eq(u, u), Branch.is_eq(b, b))
      +r3 = List.all.if(w3 => r4, Resources.Name.is_eq(c, c))
      +r2 = List.all.if(w2 => r3, Ledgers.Id.is_eq(v, v))
      Shared.List.all.if_both(Branch.is_eq(f, f), w => r2)(Affects.branch_refl(f))(
        Shared.List.all.if_both(Ledgers.Id.is_eq(v, v), w2 => r3)(Ledgers.Id.is_eq_refl(v))(
          Shared.List.all.if_both(Resources.Name.is_eq(c, c), w3 => r4)(Resources.Name.is_eq_refl(c))(
            Shared.List.all.if_both(Branch.is_eq(b, b), w4 => Resources.Name.is_eq(u, u))(Affects.branch_refl(b))(
              Resources.Name.is_eq_refl(u)
            )
          )
        )
      )

# touches that are the same are equal
def Affects.touch_sound(a: Touch, b: Touch) -> {Touch.is_eq(a, b) == True{}: Bool} -> {a == b: Touch}:
  match a b:
    case Touch{+f1, +v1, +c1, +b1, +u1} Touch{+f2, +v2, +c2, +b2, +u2}:
      +h =>
        +r4 = List.all.if(w4 => Resources.Name.is_eq(u1, u2), Branch.is_eq(b1, b2))
        +r3 = List.all.if(w3 => r4, Resources.Name.is_eq(c1, c2))
        +r2 = List.all.if(w2 => r3, Ledgers.Id.is_eq(v1, v2))
        +h2 = Shared.List.all.if_rest(Branch.is_eq(f1, f2), w => r2)(h)
        +h3 = Shared.List.all.if_rest(Ledgers.Id.is_eq(v1, v2), w2 => r3)(h2)
        +h4 = Shared.List.all.if_rest(Resources.Name.is_eq(c1, c2), w3 => r4)(h3)
        %Affects.branch_sound(f1, f2)(Shared.List.all.if_hit(Branch.is_eq(f1, f2), w => r2)(h)):
          {Touch{f1, v1, c1, b1, u1} == Touch{_, v2, c2, b2, u2}: Touch}
        %Ledgers.Id.is_eq_sound(v1, v2)(Shared.List.all.if_hit(Ledgers.Id.is_eq(v1, v2), w2 => r3)(h2)):
          {Touch{f1, v1, c1, b1, u1} == Touch{f1, _, c2, b2, u2}: Touch}
        %Resources.Name.is_eq_sound(c1, c2)(Shared.List.all.if_hit(Resources.Name.is_eq(c1, c2), w3 => r4)(h3)):
          {Touch{f1, v1, c1, b1, u1} == Touch{f1, v1, _, b2, u2}: Touch}
        %Affects.branch_sound(b1, b2)(Shared.List.all.if_hit(Branch.is_eq(b1, b2), w4 => Resources.Name.is_eq(u1, u2))(h4)):
          {Touch{f1, v1, c1, b1, u1} == Touch{f1, v1, c1, _, u2}: Touch}
        %Resources.Name.is_eq_sound(u1, u2)(Shared.List.all.if_rest(Branch.is_eq(b1, b2), w4 => Resources.Name.is_eq(u1, u2))(h4)):
          {Touch{f1, v1, c1, b1, u1} == Touch{f1, v1, c1, b1, _}: Touch}
        {==}

# the laws of Touch.is_eq
def Affects.touch_laws() -> Shared.Eq.Laws(Touch, Touch.is_eq):
  (a => Affects.touch_refl(a), a => b => Affects.touch_sound(a, b))

# a binding is the same as itself
def Affects.binding_refl(a: Trees.Binding) -> {Trees.Binding.is_eq(a, a) == True{}: Bool}:
  match a:
    case Trees.Binding{+k, +v}:
      Shared.List.all.if_both(
        Shared.List.is_eq(~U32, ~U32.is_eq, k, k),
        u => Shared.List.is_eq(~U32, ~U32.is_eq, v, v)
      )(Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), k))(
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), v)
      )

# bindings that are the same are equal
def Affects.binding_sound(a: Trees.Binding, b: Trees.Binding) -> {Trees.Binding.is_eq(a, b) == True{}: Bool} -> {a == b: Trees.Binding}:
  match a b:
    case Trees.Binding{+k1, +v1} Trees.Binding{+k2, +v2}:
      +h =>
        +hk = Shared.List.is_eq(~U32, ~U32.is_eq, k1, k2)
        +hv = Shared.List.is_eq(~U32, ~U32.is_eq, v1, v2)
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k1, k2)(Shared.List.all.if_hit(hk, u => hv)(h)):
          {Trees.Binding{k1, v1} == Trees.Binding{_, v2}: Trees.Binding}
        %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), v1, v2)(Shared.List.all.if_rest(hk, u => hv)(h)):
          {Trees.Binding{k1, v1} == Trees.Binding{k1, _}: Trees.Binding}
        {==}

# the law of a listing, of a tree t
def Affects.range_of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Range(S, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, Tuple{c, Tuple{r, rest}}}}}}:
      r

# the law of a difference, of a tree t
def Affects.diff_of(
  -S: Data,
  -fetch: S -> Hashes.Hash -> Maybe<&2, List<&2, U32>>,
  -grows: S -> S -> Bool,
  t: Trees.Tree(S, fetch, grows)
) -> Trees.Laws.Diff(S, Trees.Tree.ops(S, fetch, grows, t)):
  match t:
    case Tuple{o, Tuple{f, Tuple{p, Tuple{w, Tuple{c, Tuple{r, Tuple{df, wh}}}}}}}:
      df

# the law of a listing, of the tree of the ledger d
def Affects.range(d: Vend.Led()) -> Trees.Laws.Range(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, t}:
      Affects.range_of(
        Ledgers.Kind.L(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        Ledgers.Kind.data(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        a => b => Ledgers.Kind.grows(
          ~Replicas.Machine.Q(Requests.Ask.machine()),
          ~Replicas.Machine.code(Requests.Ask.machine()),
          ~Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x),
          a,
          b
        ),
        t
      )

# the law of a difference, of the tree of the ledger d
def Affects.diff(d: Vend.Led()) -> Trees.Laws.Diff(Vend.L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, t}:
      Affects.diff_of(
        Ledgers.Kind.L(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        Ledgers.Kind.data(
          Replicas.Machine.Q(Requests.Ask.machine()),
          Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x)
        ),
        a => b => Ledgers.Kind.grows(
          ~Replicas.Machine.Q(Requests.Ask.machine()),
          ~Replicas.Machine.code(Requests.Ask.machine()),
          ~Ledgers.Ledger.kind(Replicas.Machine.Q(Requests.Ask.machine()), Replicas.Machine.code(Requests.Ask.machine()), x),
          a,
          b
        ),
        t
      )

# a known read gives the value of the read
def Affects.known_value(l: Trees.Look, -m: Maybe<&2, List<&2, U32>>) -> {
  Trees.Look.known(l) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>
} -> {Trees.Look.value(l) == m: Maybe<&2, List<&2, U32>>}:
  match l:
    case Trees.Look.Found{v}:
      e => Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{v}, m, e)
    case Trees.Look.Absent{}:
      e => Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, m, e)
    case Trees.Look.Missing{h}:
      e => Empty.absurd({None{} == m: Maybe<&2, List<&2, U32>>}, Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, m, e))

# a read that found a value knows it
def Affects.value_known(l: Trees.Look, -v: List<&2, U32>) -> {
  Trees.Look.value(l) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Trees.Look.known(l) == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match l:
    case Trees.Look.Found{w}:
      e =>
        %Shared.Maybe.some_inj(List<&2, U32>, w, v, e): {Some{Some{w}} == Some{Some{_}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
        {==}
    case Trees.Look.Absent{}:
      e => Empty.absurd({Some{None{}} == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, Shared.Maybe.none_ne_some(List<&2, U32>, v, e))
    case Trees.Look.Missing{h}:
      e => Empty.absurd({None{} == Some{Some{v}}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, Shared.Maybe.none_ne_some(List<&2, U32>, v, e))

# a known taken request of a listing is what Tip.taken reads, for the read l
def Affects.known_taken.of(l: Trees.Look, -x: Replicas.Taken) -> {
  Replicas.Tip.known(~Replicas.Taken, ~Replicas.Taken.code, ~Replicas.Taken.code.read, Trees.Look.known(l))
    == Some{Some{x}}: Maybe<&2, Maybe<&2, Replicas.Taken>>
} -> {
  Codes.Code.whole.of(~Replicas.Taken, ~Replicas.Taken.code, ~Replicas.Taken.code.read, Trees.Look.value(l))
    == Some{x}: Maybe<&2, Replicas.Taken>
}:
  match l:
    case Trees.Look.Found{v}:
      e => Shared.Maybe.some_inj(
        Maybe<&2, Replicas.Taken>,
        Codes.Code.whole.of(~Replicas.Taken, ~Replicas.Taken.code, ~Replicas.Taken.code.read, Some{v}),
        Some{x},
        e
      )
    case Trees.Look.Absent{}:
      e => Empty.absurd(
        {None{} == Some{x}: Maybe<&2, Replicas.Taken>},
        Shared.Maybe.none_ne_some(Replicas.Taken, x, Shared.Maybe.some_inj(Maybe<&2, Replicas.Taken>, None{}, Some{x}, e))
      )
    case Trees.Look.Missing{h}:
      e => Empty.absurd({None{} == Some{x}: Maybe<&2, Replicas.Taken>}, Shared.Maybe.none_ne_some(Maybe<&2, Replicas.Taken>, Some{x}, e))

# the taken request that a listing reads at the number n is what Tip.taken
# reads there
def Affects.known_taken(~d: Vend.Led(), l: Vend.L(d), t: Replicas.Tip, n: U32, -x: Replicas.Taken) -> {
  Replicas.Tip.known(
    ~Replicas.Taken,
    ~Replicas.Taken.code,
    ~Replicas.Taken.code.read,
    Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, t, Replicas.Log.taken(n))
  )
    == Some{Some{x}}: Maybe<&2, Maybe<&2, Replicas.Taken>>
} -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, n) == Some{x}: Maybe<&2, Replicas.Taken>}:
  Affects.known_taken.of(
    Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, Replicas.Tip.log(t), Replicas.Log.taken(n)),
    x
  )

# a value of F at x is a value of F at y, when x is y
def Affects.cast(-A: Data, -F: A -> Type, -x: A, -y: A, e: {x == y: A}, v: F(x)) -> F(y):
  %e: F(_)
  v

# a list whose head is the same as x holds x
def Affects.contains_hit(
  ~A: Data,
  ~same: A -> A -> Bool,
  +h: A,
  r: List<&2, A>,
  +x: A,
  e: {same(h, x) == True{}: Bool}
) -> {List.contains(~A, ~same, h <> r, x) == True{}: Bool}:
  %Equal.sym(Bool, same(h, x), True{}, e): {List.any.if(u => List.contains(~A, ~same, r, x), _) == True{}: Bool}
  {==}

# a list holds its head
def Affects.contains_head(
  ~A: Data,
  ~same: A -> A -> Bool,
  ~laws: Shared.Eq.Laws(A, same),
  +h: A,
  r: List<&2, A>
) -> {List.contains(~A, ~same, h <> r, h) == True{}: Bool}:
  Affects.contains_hit(~A, ~same, h, r, h, Shared.Eq.refl(~A, ~same, laws, h))

# Graphs of what a work uses
# --------------------------
# The users graph of a tree (Uses.users) has the edges of its graph of imports
# (Uses.graph) reversed: a search of one finds what a search of the other
# finds, the other way.

# Graph.succ of a picked entry, once the pick is known
def Affects.pick_succ(b: Bool, -v: List<&2, List<&2, U32>>, x: Maybe<&2, List<&2, List<&2, U32>>>) -> {
  Maybe.default(
    &2,
    List<&2, List<&2, U32>>,
    Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, b, Some{v}, x),
    []
  )
    == Bool.pick(List<&2, List<&2, U32>>, b, v, Maybe.default(&2, List<&2, List<&2, U32>>, x, [])): List<&2, List<&2, U32>>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Affects.link_succ once the successors m of k are known
def Affects.link_succ.at(
  +e: Crits.Dict(List<&2, List<&2, U32>>),
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  m: Maybe<&2, List<&2, List<&2, U32>>>,
  em: {Crits.Dict.get(List<&2, List<&2, U32>>, e, k) == m: Maybe<&2, List<&2, List<&2, U32>>>},
  +p: List<&2, U32>
) -> {
  Reaches.Graph.succ(Reaches.Graph.link.at(e, ns, k, t, m), p)
    == Bool.pick(
      List<&2, List<&2, U32>>,
      Crits.Key.is_eq(p, k),
      t <> Reaches.Graph.succ(Reaches.Graph{e, ns}, k),
      Reaches.Graph.succ(Reaches.Graph{e, ns}, p)
    ): List<&2, List<&2, U32>>
}:
  match m:
    case None{}:
      %Equal.sym(
        Maybe<&2, List<&2, List<&2, U32>>>,
        Crits.Dict.get(List<&2, List<&2, U32>>, Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, [t]), p),
        Bool.pick(
          Maybe<&2, List<&2, List<&2, U32>>>,
          Crits.Key.is_eq(p, k),
          Some{[t]},
          Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
        ),
        Crits.Dict.get_set(~List<&2, List<&2, U32>>, e, k, [t], p)
      ): {
        Maybe.default(&2, List<&2, List<&2, U32>>, _, [])
          == Bool.pick(
            List<&2, List<&2, U32>>,
            Crits.Key.is_eq(p, k),
            t <> Reaches.Graph.succ(Reaches.Graph{e, ns}, k),
            Reaches.Graph.succ(Reaches.Graph{e, ns}, p)
          ): List<&2, List<&2, U32>>
      }
      %Equal.sym(Maybe<&2, List<&2, List<&2, U32>>>, Crits.Dict.get(List<&2, List<&2, U32>>, e, k), None{}, em): {
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Bool.pick(
            Maybe<&2, List<&2, List<&2, U32>>>,
            Crits.Key.is_eq(p, k),
            Some{[t]},
            Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
          ),
          []
        )
          == Bool.pick(
            List<&2, List<&2, U32>>,
            Crits.Key.is_eq(p, k),
            t <> Maybe.default(&2, List<&2, List<&2, U32>>, _, []),
            Reaches.Graph.succ(Reaches.Graph{e, ns}, p)
          ): List<&2, List<&2, U32>>
      }
      Affects.pick_succ(Crits.Key.is_eq(p, k), [t], Crits.Dict.get(List<&2, List<&2, U32>>, e, p))
    case Some{+ts}:
      %Equal.sym(
        Maybe<&2, List<&2, List<&2, U32>>>,
        Crits.Dict.get(List<&2, List<&2, U32>>, Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, t <> ts), p),
        Bool.pick(
          Maybe<&2, List<&2, List<&2, U32>>>,
          Crits.Key.is_eq(p, k),
          Some{t <> ts},
          Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
        ),
        Crits.Dict.get_set(~List<&2, List<&2, U32>>, e, k, t <> ts, p)
      ): {
        Maybe.default(&2, List<&2, List<&2, U32>>, _, [])
          == Bool.pick(
            List<&2, List<&2, U32>>,
            Crits.Key.is_eq(p, k),
            t <> Reaches.Graph.succ(Reaches.Graph{e, ns}, k),
            Reaches.Graph.succ(Reaches.Graph{e, ns}, p)
          ): List<&2, List<&2, U32>>
      }
      %Equal.sym(Maybe<&2, List<&2, List<&2, U32>>>, Crits.Dict.get(List<&2, List<&2, U32>>, e, k), Some{ts}, em): {
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Bool.pick(
            Maybe<&2, List<&2, List<&2, U32>>>,
            Crits.Key.is_eq(p, k),
            Some{t <> ts},
            Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
          ),
          []
        )
          == Bool.pick(
            List<&2, List<&2, U32>>,
            Crits.Key.is_eq(p, k),
            t <> Maybe.default(&2, List<&2, List<&2, U32>>, _, []),
            Reaches.Graph.succ(Reaches.Graph{e, ns}, p)
          ): List<&2, List<&2, U32>>
      }
      Affects.pick_succ(Crits.Key.is_eq(p, k), t <> ts, Crits.Dict.get(List<&2, List<&2, U32>>, e, p))

# the successors of p in g with t as one more successor of k: t and those of
# k when p is k, else those of p
def Affects.link_succ(+g: Reaches.Graph, +k: List<&2, U32>, +t: List<&2, U32>, +p: List<&2, U32>) -> {
  Reaches.Graph.succ(Reaches.Graph.link(g, k, t), p)
    == Bool.pick(
      List<&2, List<&2, U32>>,
      Crits.Key.is_eq(p, k),
      t <> Reaches.Graph.succ(g, k),
      Reaches.Graph.succ(g, p)
    ): List<&2, List<&2, U32>>
}:
  match g:
    case Reaches.Graph{+e, +ns}:
      Affects.link_succ.at(e, ns, k, t, Crits.Dict.get(List<&2, List<&2, U32>>, e, k), {==}, p)

# that q is a successor of p in g
def Affects.Edge(g: Reaches.Graph, p: List<&2, U32>, q: List<&2, U32>) -> Type:
  {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Reaches.Graph.succ(g, p), q) == True{}: Bool}

# Affects.link_in once the head of the successors of k is known to be q (c)
def Affects.link_in.hit(
  +g: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  +p: List<&2, U32>,
  +q: List<&2, U32>,
  -P: Type,
  ep: {Crits.Key.is_eq(p, k) == True{}: Bool},
  c: Bool,
  ec: {Crits.Key.is_eq(t, q) == c: Bool},
  kh: {Crits.Key.is_eq(p, k) == True{}: Bool} -> {Crits.Key.is_eq(t, q) == True{}: Bool} -> P,
  kr: Affects.Edge(g, p, q) -> P
) -> {
  List.any.if(u => List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Reaches.Graph.succ(g, k), q), c) == True{}: Bool
} -> P:
  match c:
    case True{}:
      h => kh(ep)(ec)
    case False{}:
      h => kr(
        Affects.cast(
          List<&2, U32>,
          z => Affects.Edge(g, z, q),
          k,
          p,
          Equal.sym(List<&2, U32>, p, k, Crits.Key.is_eq_sound(p, k)(ep)),
          h
        )
      )

# Affects.link_in once it is known whether p is k (b)
def Affects.link_in.at(
  +g: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  +p: List<&2, U32>,
  +q: List<&2, U32>,
  -P: Type,
  b: Bool,
  eb: {Crits.Key.is_eq(p, k) == b: Bool},
  kh: {Crits.Key.is_eq(p, k) == True{}: Bool} -> {Crits.Key.is_eq(t, q) == True{}: Bool} -> P,
  kr: Affects.Edge(g, p, q) -> P
) -> {
  List.contains(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Bool.pick(List<&2, List<&2, U32>>, b, t <> Reaches.Graph.succ(g, k), Reaches.Graph.succ(g, p)),
    q
  )
    == True{}: Bool
} -> P:
  match b:
    case True{}:
      h => Affects.link_in.hit(g, k, t, p, q, P, eb, Crits.Key.is_eq(t, q), {==}, kh, kr)(h)
    case False{}:
      h => kr(h)

# an edge of g with t as one more successor of k is that one, or one of g
def Affects.link_in(
  +g: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  +p: List<&2, U32>,
  +q: List<&2, U32>,
  -P: Type,
  kh: {Crits.Key.is_eq(p, k) == True{}: Bool} -> {Crits.Key.is_eq(t, q) == True{}: Bool} -> P,
  kr: Affects.Edge(g, p, q) -> P
) -> Affects.Edge(Reaches.Graph.link(g, k, t), p, q) -> P:
  h => Affects.link_in.at(g, k, t, p, q, P, Crits.Key.is_eq(p, k), {==}, kh, kr)(
    Affects.cast(
      List<&2, List<&2, U32>>,
      z => {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, z, q) == True{}: Bool},
      Reaches.Graph.succ(Reaches.Graph.link(g, k, t), p),
      Bool.pick(
        List<&2, List<&2, U32>>,
        Crits.Key.is_eq(p, k),
        t <> Reaches.Graph.succ(g, k),
        Reaches.Graph.succ(g, p)
      ),
      Affects.link_succ(g, k, t, p),
      h
    )
  )

# Affects.link_keep once it is known whether p is k (b)
def Affects.link_keep.at(
  +g: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  +p: List<&2, U32>,
  +q: List<&2, U32>,
  b: Bool,
  eb: {Crits.Key.is_eq(p, k) == b: Bool},
  h: Affects.Edge(g, p, q)
) -> {
  List.contains(
    ~List<&2, U32>,
    ~Crits.Key.is_eq,
    Bool.pick(List<&2, List<&2, U32>>, b, t <> Reaches.Graph.succ(g, k), Reaches.Graph.succ(g, p)),
    q
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_cons(~List<&2, U32>, ~Crits.Key.is_eq, t, Reaches.Graph.succ(g, k), q)(
        Affects.cast(
          List<&2, U32>,
          z => Affects.Edge(g, z, q),
          p,
          k,
          Crits.Key.is_eq_sound(p, k)(eb),
          h
        )
      )
    case False{}:
      h

# an edge of g stays when t becomes one more successor of k
def Affects.link_keep(
  +g: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  +p: List<&2, U32>,
  +q: List<&2, U32>
) -> Affects.Edge(g, p, q) -> Affects.Edge(Reaches.Graph.link(g, k, t), p, q):
  h => Affects.cast(
    List<&2, List<&2, U32>>,
    z => {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, z, q) == True{}: Bool},
    Bool.pick(
      List<&2, List<&2, U32>>,
      Crits.Key.is_eq(p, k),
      t <> Reaches.Graph.succ(g, k),
      Reaches.Graph.succ(g, p)
    ),
    Reaches.Graph.succ(Reaches.Graph.link(g, k, t), p),
    Equal.sym(
      List<&2, List<&2, U32>>,
      Reaches.Graph.succ(Reaches.Graph.link(g, k, t), p),
      Bool.pick(
        List<&2, List<&2, U32>>,
        Crits.Key.is_eq(p, k),
        t <> Reaches.Graph.succ(g, k),
        Reaches.Graph.succ(g, p)
      ),
      Affects.link_succ(g, k, t, p)
    ),
    Affects.link_keep.at(g, k, t, p, q, Crits.Key.is_eq(p, k), {==}, h)
  )

# the laws of Trie.same_key
def Affects.key_laws() -> Shared.Eq.Laws(List<&2, U32>, Crits.Key.is_eq):
  (a => Crits.Key.is_eq_refl(a), a => b => Crits.Key.is_eq_sound(a, b))

# t is a successor of k in g with t as one more successor of k
def Affects.link_new(+g: Reaches.Graph, +k: List<&2, U32>, +t: List<&2, U32>) -> Affects.Edge(Reaches.Graph.link(g, k, t), k, t):
  Affects.cast(
    List<&2, List<&2, U32>>,
    z => {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, z, t) == True{}: Bool},
    Bool.pick(
      List<&2, List<&2, U32>>,
      Crits.Key.is_eq(k, k),
      t <> Reaches.Graph.succ(g, k),
      Reaches.Graph.succ(g, k)
    ),
    Reaches.Graph.succ(Reaches.Graph.link(g, k, t), k),
    Equal.sym(
      List<&2, List<&2, U32>>,
      Reaches.Graph.succ(Reaches.Graph.link(g, k, t), k),
      Bool.pick(
        List<&2, List<&2, U32>>,
        Crits.Key.is_eq(k, k),
        t <> Reaches.Graph.succ(g, k),
        Reaches.Graph.succ(g, k)
      ),
      Affects.link_succ(g, k, t, k)
    ),
    Affects.cast(
      Bool,
      z => {
        List.contains(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          Bool.pick(List<&2, List<&2, U32>>, z, t <> Reaches.Graph.succ(g, k), Reaches.Graph.succ(g, k)),
          t
        )
          == True{}: Bool
      },
      True{},
      Crits.Key.is_eq(k, k),
      Equal.sym(Bool, Crits.Key.is_eq(k, k), True{}, Shared.Eq.refl(~List<&2, U32>, ~Crits.Key.is_eq, Affects.key_laws(), k)),
      Affects.contains_head(~List<&2, U32>, ~Crits.Key.is_eq, ~Affects.key_laws(), t, Reaches.Graph.succ(g, k))
    )
  )

# each node of g that has an entry is one of its nodes
def Affects.Has(g: Reaches.Graph) -> Type:
  match g:
    case Reaches.Graph{+e, +ns}:
      @p: List<&2, U32> -> {
        Maybe.is_some(&2, List<&2, List<&2, U32>>, Crits.Dict.get(List<&2, List<&2, U32>>, e, p)) == True{}: Bool
      } -> {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ns, p) == True{}: Bool}

# the graph with no node has no entry
def Affects.has_new() -> Affects.Has(Reaches.Graph.new()):
  p => h => Empty.absurd(
    {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, [], p) == True{}: Bool},
    Shared.Bool.false_ne_true(h)
  )

# Affects.has_link at a new node k, once it is known whether p is k (b)
def Affects.has_pick.new(
  +e: Crits.Dict(List<&2, List<&2, U32>>),
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +p: List<&2, U32>,
  b: Bool,
  eb: {Crits.Key.is_eq(p, k) == b: Bool},
  -v: List<&2, List<&2, U32>>,
  hg: Affects.Has(Reaches.Graph{e, ns})
) -> {
  Maybe.is_some(
    &2,
    List<&2, List<&2, U32>>,
    Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, b, Some{v}, Crits.Dict.get(List<&2, List<&2, U32>>, e, p))
  )
    == True{}: Bool
} -> {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, k <> ns, p) == True{}: Bool}:
  match b:
    case True{}:
      h => Affects.cast(
        List<&2, U32>,
        z => {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, k <> ns, z) == True{}: Bool},
        k,
        p,
        Equal.sym(List<&2, U32>, p, k, Crits.Key.is_eq_sound(p, k)(eb)),
        Affects.contains_head(~List<&2, U32>, ~Crits.Key.is_eq, ~Affects.key_laws(), k, ns)
      )
    case False{}:
      h => Shared.List.contains_cons(~List<&2, U32>, ~Crits.Key.is_eq, k, ns, p)(hg(p)(h))

# Affects.has_link at a node k that has an entry, once it is known whether p
# is k (b)
def Affects.has_pick.old(
  +e: Crits.Dict(List<&2, List<&2, U32>>),
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +p: List<&2, U32>,
  b: Bool,
  eb: {Crits.Key.is_eq(p, k) == b: Bool},
  -v: List<&2, List<&2, U32>>,
  +ek: {
    Maybe.is_some(&2, List<&2, List<&2, U32>>, Crits.Dict.get(List<&2, List<&2, U32>>, e, k)) == True{}: Bool
  },
  hg: Affects.Has(Reaches.Graph{e, ns})
) -> {
  Maybe.is_some(
    &2,
    List<&2, List<&2, U32>>,
    Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, b, Some{v}, Crits.Dict.get(List<&2, List<&2, U32>>, e, p))
  )
    == True{}: Bool
} -> {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ns, p) == True{}: Bool}:
  match b:
    case True{}:
      h => Affects.cast(
        List<&2, U32>,
        z => {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ns, z) == True{}: Bool},
        k,
        p,
        Equal.sym(List<&2, U32>, p, k, Crits.Key.is_eq_sound(p, k)(eb)),
        hg(k)(ek)
      )
    case False{}:
      h => hg(p)(h)

# a read of t set at k, as a pick
def Affects.set_get(
  +e: Crits.Dict(List<&2, List<&2, U32>>),
  +k: List<&2, U32>,
  +v: List<&2, List<&2, U32>>,
  +p: List<&2, U32>
) -> {
  Maybe.is_some(
    &2,
    List<&2, List<&2, U32>>,
    Crits.Dict.get(List<&2, List<&2, U32>>, Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, v), p)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    List<&2, List<&2, U32>>,
    Bool.pick(
      Maybe<&2, List<&2, List<&2, U32>>>,
      Crits.Key.is_eq(p, k),
      Some{v},
      Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
    )
  )
    == True{}: Bool
}:
  h => Affects.cast(
    Maybe<&2, List<&2, List<&2, U32>>>,
    z => {Maybe.is_some(&2, List<&2, List<&2, U32>>, z) == True{}: Bool},
    Crits.Dict.get(List<&2, List<&2, U32>>, Crits.Dict.set(~List<&2, List<&2, U32>>, e, k, v), p),
    Bool.pick(
      Maybe<&2, List<&2, List<&2, U32>>>,
      Crits.Key.is_eq(p, k),
      Some{v},
      Crits.Dict.get(List<&2, List<&2, U32>>, e, p)
    ),
    Crits.Dict.get_set(~List<&2, List<&2, U32>>, e, k, v, p),
    h
  )

# Affects.has_link once the successors m of k are known
def Affects.has_link.at(
  +e: Crits.Dict(List<&2, List<&2, U32>>),
  +ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  m: Maybe<&2, List<&2, List<&2, U32>>>,
  +em: {Crits.Dict.get(List<&2, List<&2, U32>>, e, k) == m: Maybe<&2, List<&2, List<&2, U32>>>},
  hg: Affects.Has(Reaches.Graph{e, ns})
) -> Affects.Has(Reaches.Graph.link.at(e, ns, k, t, m)):
  match m:
    case None{}:
      +p => h => Affects.has_pick.new(e, ns, k, p, Crits.Key.is_eq(p, k), {==}, [t], hg)(Affects.set_get(e, k, [t], p)(h))
    case Some{+ts}:
      +p => h => Affects.has_pick.old(
        e,
        ns,
        k,
        p,
        Crits.Key.is_eq(p, k),
        {==},
        t <> ts,
        Affects.cast(
          Maybe<&2, List<&2, List<&2, U32>>>,
          z => {Maybe.is_some(&2, List<&2, List<&2, U32>>, z) == True{}: Bool},
          Some{ts},
          Crits.Dict.get(List<&2, List<&2, U32>>, e, k),
          Equal.sym(Maybe<&2, List<&2, List<&2, U32>>>, Crits.Dict.get(List<&2, List<&2, U32>>, e, k), Some{ts}, em),
          {==}
        ),
        hg
      )(Affects.set_get(e, k, t <> ts, p)(h))

# each node with an entry is a node, still, with t as one more successor of k
def Affects.has_link(+g: Reaches.Graph, +k: List<&2, U32>, +t: List<&2, U32>, hg: Affects.Has(g)) -> Affects.Has(Reaches.Graph.link(g, k, t)):
  match g:
    case Reaches.Graph{+e, +ns}:
      Affects.has_link.at(e, ns, k, t, Crits.Dict.get(List<&2, List<&2, U32>>, e, k), {==}, hg)

# each node with an entry is a node, still, with the successors ts of k
def Affects.has_links(
  ts: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +g: Reaches.Graph,
  hg: Affects.Has(g)
) -> Affects.Has(Reaches.Graph.links(ts, k, g)):
  match ts:
    case Nil{}:
      hg
    case Con{+t, r}:
      Affects.has_links(r, k, Reaches.Graph.link(g, k, t), Affects.has_link(g, k, t, hg))

# each node with an entry is a node, still, with t a successor of each of ks
def Affects.has_back(
  ks: List<&2, List<&2, U32>>,
  +t: List<&2, U32>,
  +g: Reaches.Graph,
  hg: Affects.Has(g)
) -> Affects.Has(Reaches.Graph.back(ks, t, g)):
  match ks:
    case Nil{}:
      hg
    case Con{+k, r}:
      Affects.has_back(r, t, Reaches.Graph.link(g, k, t), Affects.has_link(g, k, t, hg))

# Affects.has_live once the entry m of p is known
def Affects.has_live.at(
  m: Maybe<&2, List<&2, List<&2, U32>>>,
  +q: List<&2, U32>,
  -R: Type,
  hc: {
    List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Maybe.default(&2, List<&2, List<&2, U32>>, m, []), q)
      == True{}: Bool
  },
  hs: {Maybe.is_some(&2, List<&2, List<&2, U32>>, m) == True{}: Bool} -> R
) -> R:
  match m:
    case None{}:
      Empty.absurd(R, Shared.Bool.false_ne_true(hc))
    case Some{ts}:
      hs({==})

# a node with a successor is a node of the graph
def Affects.has_live(
  +g: Reaches.Graph,
  hg: Affects.Has(g),
  +p: List<&2, U32>,
  +q: List<&2, U32>
) -> Affects.Edge(g, p, q) -> {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Reaches.Graph.nodes(g), p) == True{}: Bool}:
  match g:
    case Reaches.Graph{+e, +ns}:
      h => Affects.has_live.at(
        Crits.Dict.get(List<&2, List<&2, U32>>, e, p),
        q,
        {List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ns, p) == True{}: Bool},
        h,
        hg(p)
      )

# the edges of g2 are those of g1, reversed
def Affects.Inv(g1: Reaches.Graph, g2: Reaches.Graph) -> Type:
  (@p: List<&2, U32> -> @q: List<&2, U32> -> Affects.Edge(g1, p, q) -> Affects.Edge(g2, q, p))
    & (@p: List<&2, U32> -> @q: List<&2, U32> -> Affects.Edge(g2, p, q) -> Affects.Edge(g1, q, p))

# the graph with no node is its own reverse
def Affects.inv_new() -> Affects.Inv(Reaches.Graph.new(), Reaches.Graph.new()):
  (
    p => q => h => Empty.absurd(Affects.Edge(Reaches.Graph.new(), q, p), Shared.Bool.false_ne_true(h)),
    p => q => h => Empty.absurd(Affects.Edge(Reaches.Graph.new(), q, p), Shared.Bool.false_ne_true(h))
  )

# an edge from k to t, and the same edge reversed, keep two graphs reversed
def Affects.inv_link(
  +g1: Reaches.Graph,
  +g2: Reaches.Graph,
  +k: List<&2, U32>,
  +t: List<&2, U32>,
  i: Affects.Inv(g1, g2)
) -> Affects.Inv(Reaches.Graph.link(g1, k, t), Reaches.Graph.link(g2, t, k)):
  (i1, i2) = i
  (
    +p => +q => h => Affects.link_in(
      g1,
      k,
      t,
      p,
      q,
      Affects.Edge(Reaches.Graph.link(g2, t, k), q, p),
      a => b => Affects.cast(
        List<&2, U32>,
        z => Affects.Edge(Reaches.Graph.link(g2, t, k), q, z),
        k,
        p,
        Equal.sym(List<&2, U32>, p, k, Crits.Key.is_eq_sound(p, k)(a)),
        Affects.cast(
          List<&2, U32>,
          z => Affects.Edge(Reaches.Graph.link(g2, t, k), z, k),
          t,
          q,
          Crits.Key.is_eq_sound(t, q)(b),
          Affects.link_new(g2, t, k)
        )
      ),
      c => Affects.link_keep(g2, t, k, q, p)(i1(p)(q)(c))
    )(h),
    +p => +q => h => Affects.link_in(
      g2,
      t,
      k,
      p,
      q,
      Affects.Edge(Reaches.Graph.link(g1, k, t), q, p),
      a => b => Affects.cast(
        List<&2, U32>,
        z => Affects.Edge(Reaches.Graph.link(g1, k, t), q, z),
        t,
        p,
        Equal.sym(List<&2, U32>, p, t, Crits.Key.is_eq_sound(p, t)(a)),
        Affects.cast(
          List<&2, U32>,
          z => Affects.Edge(Reaches.Graph.link(g1, k, t), z, t),
          k,
          q,
          Crits.Key.is_eq_sound(k, q)(b),
          Affects.link_new(g1, k, t)
        )
      ),
      c => Affects.link_keep(g1, k, t, q, p)(i2(p)(q)(c))
    )(h)
  )

# the successors ts of k, and k as a successor of each of ts, keep two graphs
# reversed
def Affects.inv_links(
  ts: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +g1: Reaches.Graph,
  +g2: Reaches.Graph,
  i: Affects.Inv(g1, g2)
) -> Affects.Inv(Reaches.Graph.links(ts, k, g1), Reaches.Graph.back(ts, k, g2)):
  match ts:
    case Nil{}:
      i
    case Con{+t, r}:
      Affects.inv_links(r, k, Reaches.Graph.link(g1, k, t), Reaches.Graph.link(g2, t, k), Affects.inv_link(g1, g2, k, t, i))

# Affects.inv_fold once the imports m of a resource are read
def Affects.inv_fold.at(
  m: Maybe<&2, List<&2, Resources.Name>>,
  -f1: List<&2, Resources.Name> -> Maybe<&2, Reaches.Graph>,
  -f2: List<&2, Resources.Name> -> Maybe<&2, Reaches.Graph>,
  ih: @ns2: List<&2, Resources.Name> -> Affects.Inv(
    Maybe.default(&2, Reaches.Graph, f1(ns2), Reaches.Graph.new()),
    Maybe.default(&2, Reaches.Graph, f2(ns2), Reaches.Graph.new())
  )
) -> Affects.Inv(
  Maybe.default(&2, Reaches.Graph, Maybe.bind(&2, List<&2, Resources.Name>, Reaches.Graph, m, f1), Reaches.Graph.new()),
  Maybe.default(&2, Reaches.Graph, Maybe.bind(&2, List<&2, Resources.Name>, Reaches.Graph, m, f2), Reaches.Graph.new())
):
  match m:
    case None{}:
      Affects.inv_new()
    case Some{ns2}:
      ih(ns2)

# the users graph of the resources ns is their graph of imports, reversed
def Affects.inv_fold(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  +g1: Reaches.Graph,
  +g2: Reaches.Graph,
  i: Affects.Inv(g1, g2)
) -> Affects.Inv(
  Maybe.default(&2, Reaches.Graph, Uses.graph(~d, l, view, h, ns, g1), Reaches.Graph.new()),
  Maybe.default(&2, Reaches.Graph, Uses.users(~d, l, view, h, ns, g2), Reaches.Graph.new())
):
  match ns:
    case Nil{}:
      i
    case Con{+n, +rest}:
      Affects.inv_fold.at(
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.graph(~d, l, view, h, rest, Reaches.Graph.links(Names.keys(ns2), Name.key(n), g1)),
        ns2 => Uses.users(~d, l, view, h, rest, Reaches.Graph.back(Names.keys(ns2), Name.key(n), g2)),
        +ns2 => Affects.inv_fold(
          ~d,
          l,
          view,
          h,
          rest,
          Reaches.Graph.links(Names.keys(ns2), Name.key(n), g1),
          Reaches.Graph.back(Names.keys(ns2), Name.key(n), g2),
          Affects.inv_links(Names.keys(ns2), Name.key(n), g1, g2, i)
        )
      )

# Affects.has_graph and Affects.has_users once the imports m of a resource
# are read
def Affects.has_fold.at(
  m: Maybe<&2, List<&2, Resources.Name>>,
  -f: List<&2, Resources.Name> -> Maybe<&2, Reaches.Graph>,
  ih: @ns2: List<&2, Resources.Name> -> Affects.Has(Maybe.default(&2, Reaches.Graph, f(ns2), Reaches.Graph.new()))
) -> Affects.Has(
  Maybe.default(&2, Reaches.Graph, Maybe.bind(&2, List<&2, Resources.Name>, Reaches.Graph, m, f), Reaches.Graph.new())
):
  match m:
    case None{}:
      Affects.has_new()
    case Some{ns2}:
      ih(ns2)

# each node with an entry in a graph of imports is one of its nodes
def Affects.has_graph(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  +g: Reaches.Graph,
  hg: Affects.Has(g)
) -> Affects.Has(Maybe.default(&2, Reaches.Graph, Uses.graph(~d, l, view, h, ns, g), Reaches.Graph.new())):
  match ns:
    case Nil{}:
      hg
    case Con{+n, +rest}:
      Affects.has_fold.at(
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.graph(~d, l, view, h, rest, Reaches.Graph.links(Names.keys(ns2), Name.key(n), g)),
        +ns2 => Affects.has_graph(
          ~d,
          l,
          view,
          h,
          rest,
          Reaches.Graph.links(Names.keys(ns2), Name.key(n), g),
          Affects.has_links(Names.keys(ns2), Name.key(n), g, hg)
        )
      )

# each node with an entry in a users graph is one of its nodes
def Affects.has_users(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  +g: Reaches.Graph,
  hg: Affects.Has(g)
) -> Affects.Has(Maybe.default(&2, Reaches.Graph, Uses.users(~d, l, view, h, ns, g), Reaches.Graph.new())):
  match ns:
    case Nil{}:
      hg
    case Con{+n, +rest}:
      Affects.has_fold.at(
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.users(~d, l, view, h, rest, Reaches.Graph.back(Names.keys(ns2), Name.key(n), g)),
        +ns2 => Affects.has_users(
          ~d,
          l,
          view,
          h,
          rest,
          Reaches.Graph.back(Names.keys(ns2), Name.key(n), g),
          Affects.has_back(Names.keys(ns2), Name.key(n), g, hg)
        )
      )

# Affects.some_fold once the imports m of a resource are read
def Affects.some_fold.at(
  m: Maybe<&2, List<&2, Resources.Name>>,
  -f1: List<&2, Resources.Name> -> Maybe<&2, Reaches.Graph>,
  -f2: List<&2, Resources.Name> -> Maybe<&2, Reaches.Graph>,
  ih: @ns2: List<&2, Resources.Name> -> {
    Maybe.is_some(&2, Reaches.Graph, f2(ns2)) == Maybe.is_some(&2, Reaches.Graph, f1(ns2)): Bool
  }
) -> {
  Maybe.is_some(&2, Reaches.Graph, Maybe.bind(&2, List<&2, Resources.Name>, Reaches.Graph, m, f2))
    == Maybe.is_some(&2, Reaches.Graph, Maybe.bind(&2, List<&2, Resources.Name>, Reaches.Graph, m, f1)): Bool
}:
  match m:
    case None{}:
      {==}
    case Some{ns2}:
      ih(ns2)

# the users graph of the resources ns is read exactly when their graph of
# imports is: both read the same imports
def Affects.some_fold(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, Resources.Name>,
  +g1: Reaches.Graph,
  +g2: Reaches.Graph
) -> {
  Maybe.is_some(&2, Reaches.Graph, Uses.users(~d, l, view, h, ns, g2))
    == Maybe.is_some(&2, Reaches.Graph, Uses.graph(~d, l, view, h, ns, g1)): Bool
}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +rest}:
      Affects.some_fold.at(
        Res.imports(~d, l, view, h, n),
        ns2 => Uses.graph(~d, l, view, h, rest, Reaches.Graph.links(Names.keys(ns2), Name.key(n), g1)),
        ns2 => Uses.users(~d, l, view, h, rest, Reaches.Graph.back(Names.keys(ns2), Name.key(n), g2)),
        +ns2 => Affects.some_fold(
          ~d,
          l,
          view,
          h,
          rest,
          Reaches.Graph.links(Names.keys(ns2), Name.key(n), g1),
          Reaches.Graph.back(Names.keys(ns2), Name.key(n), g2)
        )
      )

# the graph of imports of the resources ns of the tree h (True), or their
# users graph (False); the graph with no node while l lacks an import
def Affects.side(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  b: Bool
) -> Reaches.Graph:
  match b:
    case True{}:
      Maybe.default(&2, Reaches.Graph, Uses.graph(~d, l, view, h, ns, Reaches.Graph.new()), Reaches.Graph.new())
    case False{}:
      Maybe.default(&2, Reaches.Graph, Uses.users(~d, l, view, h, ns, Reaches.Graph.new()), Reaches.Graph.new())

# the reverse of two reversed graphs
def Affects.inv_swap(-g1: Reaches.Graph, -g2: Reaches.Graph, i: Affects.Inv(g1, g2)) -> Affects.Inv(g2, g1):
  (i1, i2) = i
  (i2, i1)

# each side is the other, reversed
def Affects.side_inv(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  b: Bool
) -> Affects.Inv(Affects.side(~d, l, view, h, ns, b), Affects.side(~d, l, view, h, ns, Bool.not(b))):
  match b:
    case True{}:
      Affects.inv_fold(~d, l, view, h, ns, Reaches.Graph.new(), Reaches.Graph.new(), Affects.inv_new())
    case False{}:
      Affects.inv_swap(
        Affects.side(~d, l, view, h, ns, True{}),
        Affects.side(~d, l, view, h, ns, False{}),
        Affects.inv_fold(~d, l, view, h, ns, Reaches.Graph.new(), Reaches.Graph.new(), Affects.inv_new())
      )

# an edge of g1 is an edge of g2, reversed, when g2 is g1 reversed
def Affects.inv_fst(
  -g1: Reaches.Graph,
  -g2: Reaches.Graph,
  i: Affects.Inv(g1, g2),
  p: List<&2, U32>,
  q: List<&2, U32>
) -> Affects.Edge(g1, p, q) -> Affects.Edge(g2, q, p):
  (i1, i2) = i
  i1(p)(q)

# an edge of a side is an edge of the other side, reversed
def Affects.side_edge(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +p: List<&2, U32>,
  +q: List<&2, U32>
) -> Affects.Edge(Affects.side(~d, l, view, h, ns, b), p, q) -> Affects.Edge(Affects.side(~d, l, view, h, ns, Bool.not(b)), q, p):
  Affects.inv_fst(
    Affects.side(~d, l, view, h, ns, b),
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    Affects.side_inv(~d, l, view, h, ns, b),
    p,
    q
  )

# each node with an entry in a side is one of its nodes
def Affects.side_has(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  b: Bool
) -> Affects.Has(Affects.side(~d, l, view, h, ns, b)):
  match b:
    case True{}:
      Affects.has_graph(~d, l, view, h, ns, Reaches.Graph.new(), Affects.has_new())
    case False{}:
      Affects.has_users(~d, l, view, h, ns, Reaches.Graph.new(), Affects.has_new())

# a node with a successor in a side is one of its nodes
def Affects.side_live(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +p: List<&2, U32>,
  +q: List<&2, U32>
) -> Affects.Edge(Affects.side(~d, l, view, h, ns, b), p, q) -> {
  List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b)), p)
    == True{}: Bool
}:
  Affects.has_live(Affects.side(~d, l, view, h, ns, b), Affects.side_has(~d, l, view, h, ns, b), p, q)

# Affects.rev_path once the rest of the path is reversed (w)
def Affects.rev_path.cons(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +p: List<&2, U32>,
  +x: List<&2, U32>,
  +m: List<&2, U32>,
  he: Affects.Edge(Affects.side(~d, l, view, h, ns, b), x, p),
  w: &qs: List<&2, List<&2, U32>> -> {
    Reaches.Reach.path(
      ~List<&2, U32>,
      ~Reaches.Graph,
      ~Crits.Key.is_eq,
      ~Reaches.Graph.succ,
      qs,
      Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
      Affects.side(~d, l, view, h, ns, Bool.not(b)),
      p
    )
      == True{}: Bool
  }
) -> &qs: List<&2, List<&2, U32>> -> {
  Reaches.Reach.path(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    qs,
    Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    x
  )
    == True{}: Bool
}:
  match w:
    case (+qs, hq):
      (
        List.append(&2, List<&2, U32>, qs, [p]),
        Reaches.Reach.path_append(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          qs,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
          p,
          [],
          Affects.side(~d, l, view, h, ns, Bool.not(b)),
          x
        )(hq)(Affects.side_edge(~d, l, view, h, ns, b, x, p)(he))
      )

# a path from x to m in a side, reversed, is a path from m to x in the other
def Affects.rev_path(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  ps: List<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +m: List<&2, U32>
) -> {
  Reaches.Reach.path(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ps,
    Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
    Affects.side(~d, l, view, h, ns, b),
    m
  )
    == True{}: Bool
} -> &qs: List<&2, List<&2, U32>> -> {
  Reaches.Reach.path(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    qs,
    Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    x
  )
    == True{}: Bool
}:
  match ps:
    case Nil{}:
      hp => ([], Affects.side_edge(~d, l, view, h, ns, b, x, m)(hp))
    case Con{+p, +r}:
      +hp =>
        +contains1 = List.contains(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
          p
        )
        +path1 = Reaches.Reach.path(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          r,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), p),
          Affects.side(~d, l, view, h, ns, b),
          m
        )
        Affects.rev_path.cons(
          ~d,
          l,
          view,
          h,
          ns,
          b,
          p,
          x,
          m,
          Shared.Bool.and_true_left(contains1, path1)(hp),
          Affects.rev_path(~d, l, view, h, ns, b, r, p, m)(Shared.Bool.and_true_right(contains1, path1)(hp))
        )

# the nodes of a path in a side are nodes of it
def Affects.within(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +ps: List<&2, List<&2, U32>>,
  ys: List<&2, List<&2, U32>>,
  +m: List<&2, U32>
) -> {
  Reaches.Reach.path(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ps,
    ys,
    Affects.side(~d, l, view, h, ns, b),
    m
  )
    == True{}: Bool
} -> {
  Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, ps, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b)))
    == True{}: Bool
}:
  match ps:
    case Nil{}:
      +hp => {==}
    case Con{+p, +r}:
      +hp =>
        +path1 = Reaches.Reach.path(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          r,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), p),
          Affects.side(~d, l, view, h, ns, b),
          m
        )
        +contains1 = List.contains(~List<&2, U32>, ~Crits.Key.is_eq, ys, p)
        hf = Reaches.Reach.path_first(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          r,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), p),
          Affects.side(~d, l, view, h, ns, b),
          m
        )(Shared.Bool.and_true_right(contains1, path1)(hp))
        %Equal.sym(
          Bool,
          List.contains(~List<&2, U32>, ~Crits.Key.is_eq, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b)), p),
          True{},
          Affects.side_live(~d, l, view, h, ns, b, p, Reaches.Reach.first(List<&2, U32>, r, m))(hf)
        ): {
          Bool.and(
            _,
            Shared.List.within(~List<&2, U32>, ~Crits.Key.is_eq, r, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b)))
          )
            == True{}: Bool
        }
        Affects.within(
          ~d,
          l,
          view,
          h,
          ns,
          b,
          r,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), p),
          m
        )(Shared.Bool.and_true_right(contains1, path1)(hp))

# a path from x to m in a side that visits each node once makes its search
# find m
def Affects.fin(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +x: List<&2, U32>,
  +m: List<&2, U32>,
  w: &qs: List<&2, List<&2, U32>> -> {
    Reaches.Reach.path(
      ~List<&2, U32>,
      ~Reaches.Graph,
      ~Crits.Key.is_eq,
      ~Reaches.Graph.succ,
      qs,
      Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
      Affects.side(~d, l, view, h, ns, b),
      m
    )
      == True{}: Bool
  }
    & {Reaches.Reach.distinct(~List<&2, U32>, ~Crits.Key.is_eq, qs) == True{}: Bool}
) -> {
  Reaches.Reach.in(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ~Reaches.Graph.nodes,
    Affects.side(~d, l, view, h, ns, b),
    x,
    m
  )
    == True{}: Bool
}:
  match w:
    case (+qs, (+hq, hd)):
      Reaches.Reach.path_go(
        ~List<&2, U32>,
        ~Reaches.Graph,
        ~Crits.Key.is_eq,
        ~Reaches.Graph.succ,
        ~Affects.key_laws(),
        qs,
        List.length(&2, List<&2, U32>, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b))),
        Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
        Affects.side(~d, l, view, h, ns, b),
        m
      )(hq)(
        Reaches.Reach.fits_nodes(
          ~List<&2, U32>,
          ~Crits.Key.is_eq,
          ~Affects.key_laws(),
          qs,
          Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b))
        )(hd)(Affects.within(~d, l, view, h, ns, b, qs, Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x), m)(hq))
      )

# Affects.rev_in once a path of the search is found (w)
def Affects.rev_in.one(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +x: List<&2, U32>,
  +m: List<&2, U32>,
  w: &ps: List<&2, List<&2, U32>> -> {
    Reaches.Reach.path(
      ~List<&2, U32>,
      ~Reaches.Graph,
      ~Crits.Key.is_eq,
      ~Reaches.Graph.succ,
      ps,
      Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
      Affects.side(~d, l, view, h, ns, b),
      m
    )
      == True{}: Bool
  }
    & {
      Reaches.Reach.fits(
        List<&2, U32>,
        ps,
        List.length(&2, List<&2, U32>, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b)))
      )
        == True{}: Bool
    }
) -> &qs: List<&2, List<&2, U32>> -> {
  Reaches.Reach.path(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    qs,
    Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    x
  )
    == True{}: Bool
}:
  match w:
    case (+ps, (+hp, hf)):
      Affects.rev_path(~d, l, view, h, ns, b, ps, x, m)(hp)

# Affects.rev_in once the path is reversed (w)
def Affects.rev_in.two(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +x: List<&2, U32>,
  +m: List<&2, U32>,
  w: &qs: List<&2, List<&2, U32>> -> {
    Reaches.Reach.path(
      ~List<&2, U32>,
      ~Reaches.Graph,
      ~Crits.Key.is_eq,
      ~Reaches.Graph.succ,
      qs,
      Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
      Affects.side(~d, l, view, h, ns, Bool.not(b)),
      x
    )
      == True{}: Bool
  }
) -> {
  Reaches.Reach.in(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ~Reaches.Graph.nodes,
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    m,
    x
  )
    == True{}: Bool
}:
  match w:
    case (+qs, hq):
      Affects.fin(
        ~d,
        l,
        view,
        h,
        ns,
        Bool.not(b),
        m,
        x,
        Reaches.Reach.shorten(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          ~Affects.key_laws(),
          qs,
          Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, Bool.not(b)), m),
          Affects.side(~d, l, view, h, ns, Bool.not(b)),
          x
        )(hq)
      )

# what a search of a side finds from x, a search of the other side finds x
# from
def Affects.rev_in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +x: List<&2, U32>,
  +m: List<&2, U32>
) -> {
  Reaches.Reach.in(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ~Reaches.Graph.nodes,
    Affects.side(~d, l, view, h, ns, b),
    x,
    m
  )
    == True{}: Bool
} -> {
  Reaches.Reach.in(
    ~List<&2, U32>,
    ~Reaches.Graph,
    ~Crits.Key.is_eq,
    ~Reaches.Graph.succ,
    ~Reaches.Graph.nodes,
    Affects.side(~d, l, view, h, ns, Bool.not(b)),
    m,
    x
  )
    == True{}: Bool
}:
  hp => Affects.rev_in.two(
    ~d,
    l,
    view,
    h,
    ns,
    b,
    x,
    m,
    Affects.rev_in.one(
      ~d,
      l,
      view,
      h,
      ns,
      b,
      x,
      m,
      Reaches.Reach.go_path(
        ~List<&2, U32>,
        ~Reaches.Graph,
        ~Crits.Key.is_eq,
        ~Reaches.Graph.succ,
        ~Affects.key_laws(),
        List.length(&2, List<&2, U32>, Reaches.Graph.nodes(Affects.side(~d, l, view, h, ns, b))),
        Reaches.Graph.succ(Affects.side(~d, l, view, h, ns, b), x),
        Affects.side(~d, l, view, h, ns, b),
        m
      )(hp)
    )
  )

# what Graph.reach of a side finds from x, Graph.reach of the other side finds
# x from
def Affects.reach_rev(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, Resources.Name>,
  +b: Bool,
  +x: List<&2, U32>,
  +m: List<&2, U32>
) -> {
  Crits.Dict.has(Unit, Reaches.Graph.reach(Affects.side(~d, l, view, h, ns, b), x), m) == True{}: Bool
} -> {Crits.Dict.has(Unit, Reaches.Graph.reach(Affects.side(~d, l, view, h, ns, Bool.not(b)), m), x) == True{}: Bool}:
  hp =>
    %Equal.sym(
      Bool,
      Crits.Dict.has(Unit, Reaches.Graph.reach(Affects.side(~d, l, view, h, ns, Bool.not(b)), m), x),
      Reaches.Reach.in(
        ~List<&2, U32>,
        ~Reaches.Graph,
        ~Crits.Key.is_eq,
        ~Reaches.Graph.succ,
        ~Reaches.Graph.nodes,
        Affects.side(~d, l, view, h, ns, Bool.not(b)),
        m,
        x
      ),
      Reaches.Reach.all_in(~Reaches.Graph, ~Reaches.Graph.succ, ~Reaches.Graph.nodes, Affects.side(~d, l, view, h, ns, Bool.not(b)), m, x)
    ): {_ == True{}: Bool}
    Affects.rev_in(~d, l, view, h, ns, b, x, m)(
      Equal.trans(
        Bool,
        Reaches.Reach.in(
          ~List<&2, U32>,
          ~Reaches.Graph,
          ~Crits.Key.is_eq,
          ~Reaches.Graph.succ,
          ~Reaches.Graph.nodes,
          Affects.side(~d, l, view, h, ns, b),
          x,
          m
        ),
        Crits.Dict.has(Unit, Reaches.Graph.reach(Affects.side(~d, l, view, h, ns, b), x), m),
        True{},
        Equal.sym(
          Bool,
          Crits.Dict.has(Unit, Reaches.Graph.reach(Affects.side(~d, l, view, h, ns, b), x), m),
          Reaches.Reach.in(
            ~List<&2, U32>,
            ~Reaches.Graph,
            ~Crits.Key.is_eq,
            ~Reaches.Graph.succ,
            ~Reaches.Graph.nodes,
            Affects.side(~d, l, view, h, ns, b),
            x,
            m
          ),
          Reaches.Reach.all_in(~Reaches.Graph, ~Reaches.Graph.succ, ~Reaches.Graph.nodes, Affects.side(~d, l, view, h, ns, b), x, m)
        ),
        hp
      )
    )

# the key of a resource is the one key whose name is the resource
def Affects.key_of_name(k: List<&2, U32>, +u: Resources.Name) -> {
  Merges.Res.name(k) == Some{u}: Maybe<&2, Resources.Name>
} -> {Vend.Key.res(u) == k: List<&2, U32>}:
  match k:
    case Nil{}:
      h => Empty.absurd({Vend.Key.res(u) == []: List<&2, U32>}, Shared.Maybe.none_ne_some(Resources.Name, u, h))
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, +r}:
      h => Equal.cong(
        List<&2, U32>,
        List<&2, U32>,
        z => 0 <> z,
        Resources.Name.code(u, []),
        r,
        Codes.Code.whole_back(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, r, u)(h)
      )
    case Con{U32{WCon{True{}, t}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{True{}, t}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{True{}, t}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{True{}, t}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{True{}, t}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{True{}, t}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Vend.Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )

# the laws of Resources.Name.is_eq
def Affects.name_laws() -> Shared.Eq.Laws(Resources.Name, Resources.Name.is_eq):
  (n => Resources.Name.is_eq_refl(n), a => b => Resources.Name.is_eq_sound(a, b))

# the laws of Trees.Binding.is_eq
def Affects.binding_laws() -> Shared.Eq.Laws(Trees.Binding, Trees.Binding.is_eq):
  (a => Affects.binding_refl(a), a => b => Affects.binding_sound(a, b))

# the key of a resource names it
def Affects.name_key(+n: Resources.Name) -> {Merges.Res.name(Vend.Key.res(n)) == Some{n}: Maybe<&2, Resources.Name>}:
  Codes.Code.whole_read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, ~(a => r => Resources.Name.code_read(a, r)), n)

# Affects.range_has, from the law of a listing
def Affects.range_has.of(
  ~d: Vend.Led(),
  l: Vend.L(d),
  h: Maybe<&2, Hashes.Hash>,
  p: List<&2, U32>,
  bs: List<&2, Trees.Binding>,
  w: {Trees.Bindings.sorted(bs) == True{}: Bool}
    & (
      @k: List<&2, U32> -> @v: List<&2, U32> -> {
        List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v})
          == Bool.and(
            Trees.Key.leads(p, k),
            Shared.Maybe.is_eq(
              ~List<&2, U32>,
              ~Shared.List.is_eq(~U32, ~U32.is_eq),
              Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, k)),
              Some{v}
            )
          ): Bool
      }
    ),
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v})
    == Bool.and(
      Trees.Key.leads(p, k),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, k)),
        Some{v}
      )
    ): Bool
}:
  (s, f) = w
  f(k)(v)

# a listing holds a binding exactly when its key starts with the prefix and
# the tree reads it so
def Affects.range_has(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +p: List<&2, U32>,
  +bs: List<&2, Trees.Binding>,
  e: {Vend.Tree.range(~d, l, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  List.contains(~Trees.Binding, ~Trees.Binding.is_eq, bs, Trees.Binding{k, v})
    == Bool.and(
      Trees.Key.leads(p, k),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, k)),
        Some{v}
      )
    ): Bool
}:
  Affects.range_has.of(~d, l, h, p, bs, Affects.range(d)(l)(h)(p)(bs)(e), k, v)

# a difference holds a key exactly when the two trees read it differently
def Affects.diff_has(
  ~d: Vend.Led(),
  l: Vend.L(d),
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>,
  ks: List<&2, List<&2, U32>>,
  e: {
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, a, b) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>
  },
  k: List<&2, U32>
) -> {
  List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, k)
    == Bool.not(
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, a, k)),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, b, k))
      )
    ): Bool
}:
  Affects.diff(d)(l)(a)(b)(ks)(e)(k)

# Affects.names_in once it is known whether the name u0 of x is u (c)
def Affects.names_in.hit(
  +x: Trees.Binding,
  +rest: List<&2, Trees.Binding>,
  +u: Resources.Name,
  +u0: Resources.Name,
  +em: {Res.named(x) == Some{u0}: Maybe<&2, Resources.Name>},
  c: Bool,
  ec: {Resources.Name.is_eq(u0, u) == c: Bool},
  -P: Type,
  k: @b: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> rest, b) == True{}: Bool}
    -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P,
  ih: (
    @b: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, b) == True{}: Bool}
      -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P
  ) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(rest), u) == True{}: Bool} -> P
) -> {
  List.any.if(w => List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(rest), u), c) == True{}: Bool
} -> P:
  match c:
    case True{}:
      h => k(x)(Affects.contains_head(~Trees.Binding, ~Trees.Binding.is_eq, ~Affects.binding_laws(), x, rest))(
        Affects.cast(
          Resources.Name,
          z => {Res.named(x) == Some{z}: Maybe<&2, Resources.Name>},
          u0,
          u,
          Resources.Name.is_eq_sound(u0, u)(ec),
          em
        )
      )
    case False{}:
      h => ih(+b => hb => hn => k(b)(Shared.List.contains_cons(~Trees.Binding, ~Trees.Binding.is_eq, x, rest, b)(hb))(hn))(h)

# Affects.names_in once the name m of the binding x is known
def Affects.names_in.at(
  +x: Trees.Binding,
  +rest: List<&2, Trees.Binding>,
  +u: Resources.Name,
  m: Maybe<&2, Resources.Name>,
  +em: {Res.named(x) == m: Maybe<&2, Resources.Name>},
  -P: Type,
  k: @b: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, x <> rest, b) == True{}: Bool}
    -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P,
  ih: (
    @b: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, b) == True{}: Bool}
      -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P
  ) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(rest), u) == True{}: Bool} -> P
) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, m, Res.names(rest)), u) == True{}: Bool
} -> P:
  match m:
    case None{}:
      h => ih(+b => hb => hn => k(b)(Shared.List.contains_cons(~Trees.Binding, ~Trees.Binding.is_eq, x, rest, b)(hb))(hn))(h)
    case Some{+u0}:
      h => Affects.names_in.hit(x, rest, u, u0, em, Resources.Name.is_eq(u0, u), {==}, P, k, ih)(h)

# a resource of the bindings xs is the name of one of them
def Affects.names_in(
  xs: List<&2, Trees.Binding>,
  +u: Resources.Name,
  -P: Type,
  k: @b: Trees.Binding -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, b) == True{}: Bool}
    -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool} -> P:
  match xs:
    case Nil{}:
      h => Empty.absurd(P, Shared.Bool.false_ne_true(h))
    case Con{+x, +rest}:
      h => Affects.names_in.at(x, rest, u, Res.named(x), {==}, P, k, k2 => h2 => Affects.names_in(rest, u, P, k2)(h2))(h)

# a list that holds u holds it with one more value m before it, if any
def Affects.cons_keep(m: Maybe<&2, Resources.Name>, +r: List<&2, Resources.Name>, +u: Resources.Name) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, r, u) == True{}: Bool
} -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, m, r), u) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{y}:
      h => Shared.List.contains_cons(~Resources.Name, ~Resources.Name.is_eq, y, r, u)(h)

# Affects.names_of once it is known whether x is b (c)
def Affects.names_of.at(
  +x: Trees.Binding,
  +rest: List<&2, Trees.Binding>,
  +b: Trees.Binding,
  +u: Resources.Name,
  c: Bool,
  ec: {Trees.Binding.is_eq(x, b) == c: Bool},
  +en: {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>},
  ih: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, b) == True{}: Bool}
    -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(rest), u) == True{}: Bool}
) -> {
  List.any.if(w => List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, b), c) == True{}: Bool
} -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Res.named(x), Res.names(rest)), u)
    == True{}: Bool
}:
  match c:
    case True{}:
      h => Affects.cast(
        Trees.Binding,
        z => {
          List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Res.named(z), Res.names(rest)), u)
            == True{}: Bool
        },
        b,
        x,
        Equal.sym(Trees.Binding, x, b, Affects.binding_sound(x, b)(ec)),
        Affects.cast(
          Maybe<&2, Resources.Name>,
          z => {
            List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, z, Res.names(rest)), u)
              == True{}: Bool
          },
          Some{u},
          Res.named(b),
          Equal.sym(Maybe<&2, Resources.Name>, Res.named(b), Some{u}, en),
          Affects.contains_head(~Resources.Name, ~Resources.Name.is_eq, ~Affects.name_laws(), u, Res.names(rest))
        )
      )
    case False{}:
      h => Affects.cons_keep(Res.named(x), Res.names(rest), u)(ih(h))

# the name of a binding of xs is a resource of xs
def Affects.names_of(
  xs: List<&2, Trees.Binding>,
  +b: Trees.Binding,
  +u: Resources.Name,
  +en: {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>}
) -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, b) == True{}: Bool}
  -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd(
        {List.contains(~Resources.Name, ~Resources.Name.is_eq, [], u) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+x, +rest}:
      h => Affects.names_of.at(x, rest, b, u, Trees.Binding.is_eq(x, b), {==}, en, h2 => Affects.names_of(rest, b, u, en)(h2))(h)

# a resource, or none, is the same as itself
def Affects.same_refl(a: Maybe<&2, Requests.Res>) -> {Vend.Res.same(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Requests.Res.code(x, []))

# Affects.find_named once the binding is known to name u, and its value to be
# the resource r1
def Affects.find_named.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Vend.Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool} -> P,
  +k0: List<&2, U32>,
  +v0: List<&2, U32>,
  +r1: Requests.Res,
  +hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{k0, v0}) == True{}: Bool},
  +ef: {Vend.Res.found(Some{v0}) == Some{r1}: Maybe<&2, Requests.Res>},
  +ek: {Vend.Key.res(u) == k0: List<&2, U32>}
) -> P:
  +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, k0)
  +iseq = Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Some{v0})
  +htrue = Equal.trans(
    Bool,
    Bool.and(Trees.Key.leads([0], k0), iseq),
    List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{k0, v0}),
    True{},
    Equal.sym(
      Bool,
      List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{k0, v0}),
      Bool.and(Trees.Key.leads([0], k0), iseq),
      Affects.range_has(~d, l, hb, [0], xs, er, k0, v0)
    ),
    hc
  )
  +evalue = Shared.Maybe.is_eq_sound(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
    Trees.Look.value(look0),
    Some{v0}
  )(Shared.Bool.and_true_right(Trees.Key.leads([0], k0), iseq)(htrue))
  +eknown = Affects.cast(
    List<&2, U32>,
    z => {
      Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, z))
        == Some{Some{v0}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    },
    k0,
    Vend.Key.res(u),
    Equal.sym(List<&2, U32>, Vend.Key.res(u), k0, ek),
    Affects.value_known(look0, v0)(evalue)
  )
  k(Vend.Res.found(Some{v0}))(
    Affects.cast(
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      z => {
        Maybe.bind(&2, Maybe<&2, List<&2, U32>>, Maybe<&2, Requests.Res>, z, m => Some{Vend.Res.found(m)})
          == Some{Vend.Res.found(Some{v0})}: Maybe<&2, Maybe<&2, Requests.Res>>
      },
      Some{Some{v0}},
      Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Vend.Key.res(u))),
      Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Vend.Key.res(u))),
        Some{Some{v0}},
        eknown
      ),
      {==}
    )
  )(
    Affects.cast(
      Maybe<&2, Requests.Res>,
      z => {Maybe.is_some(&2, Requests.Res, z) == True{}: Bool},
      Some{r1},
      Vend.Res.found(Some{v0}),
      Equal.sym(Maybe<&2, Requests.Res>, Vend.Res.found(Some{v0}), Some{r1}, ef),
      {==}
    )
  )

# Affects.find_named for a binding b of xs that names u
def Affects.find_named.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Vend.Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool} -> P,
  b: Trees.Binding,
  +hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, b) == True{}: Bool}
) -> {Res.named(b) == Some{u}: Maybe<&2, Resources.Name>} -> P:
  match b:
    case Trees.Binding{+k0, +v0}:
      hn => Affects.bind_some(
        Requests.Res,
        Resources.Name,
        P,
        Vend.Res.found(Some{v0}),
        r => Merges.Res.name(k0),
        u,
        +r1 => ef => en => Affects.find_named.of(~d, l, hb, xs, er, u, P, k, k0, v0, r1, hc, ef, Affects.key_of_name(k0, u)(en))
      )(hn)

# a resource of a listing of a tree is there: Res.find gives some resource
def Affects.find_named(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Vend.Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool} -> P
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool} -> P:
  h => Affects.names_in(xs, u, P, +b => hc => hn => Affects.find_named.at(~d, l, hb, xs, er, u, P, k, b, hc)(hn))(h)

# Affects.find_names once the read m0 of the key of u is known
def Affects.find_names.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  +r0: Requests.Res,
  m0: Maybe<&2, List<&2, U32>>,
  +em0: {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, hb, Vend.Key.res(u)) == Some{m0}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  +ef: {Vend.Res.found(m0) == Some{r0}: Maybe<&2, Requests.Res>}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool}:
  match m0:
    case None{}:
      Empty.absurd(
        {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool},
        Shared.Maybe.none_ne_some(Requests.Res, r0, ef)
      )
    case Some{+v}:
      +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Vend.Key.res(u))
      +evalue = Affects.known_value(look0, Some{v})(em0)
      Affects.names_of(
        xs,
        Trees.Binding{Vend.Key.res(u), v},
        u,
        Affects.cast(
          Maybe<&2, Requests.Res>,
          z => {Maybe.bind(&2, Requests.Res, Resources.Name, z, r => Merges.Res.name(Vend.Key.res(u))) == Some{u}: Maybe<&2, Resources.Name>},
          Some{r0},
          Vend.Res.found(Some{v}),
          Equal.sym(Maybe<&2, Requests.Res>, Vend.Res.found(Some{v}), Some{r0}, ef),
          Affects.name_key(u)
        )
      )(
        Equal.trans(
          Bool,
          List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{Vend.Key.res(u), v}),
          Bool.and(
            Trees.Key.leads([0], Vend.Key.res(u)),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Some{v})
          ),
          True{},
          Affects.range_has(~d, l, hb, [0], xs, er, Vend.Key.res(u), v),
          Affects.cast(
            Maybe<&2, List<&2, U32>>,
            z => {
              Bool.and(
                Trees.Key.leads([0], Vend.Key.res(u)),
                Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), z, Some{v})
              )
                == True{}: Bool
            },
            Some{v},
            Trees.Look.value(look0),
            Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Look.value(look0), Some{v}, evalue),
            Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), v)
          )
        )
      )

# a resource that Res.find finds in a tree is a resource of its listing
def Affects.find_names(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  +r0: Requests.Res
) -> {Vend.Res.find(~d, l, hb, u) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>}
  -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool}:
  ef => Affects.bind_some(
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Requests.Res>,
    {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool},
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, hb, Vend.Key.res(u)),
    m => Some{Vend.Res.found(m)},
    Some{r0},
    +m0 => em0 => e2 => Affects.find_names.at(
      ~d,
      l,
      hb,
      xs,
      er,
      u,
      r0,
      m0,
      em0,
      Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Vend.Res.found(m0), Some{r0}, e2)
    )
  )(ef)

# Affects.keys_of once it is known whether the key j is k (b)
def Affects.keys_of.at(
  +j: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +c: Resources.Name,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, j, k) == b: Bool},
  +en: {Merges.Res.name(k) == Some{c}: Maybe<&2, Resources.Name>},
  ih: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, k) == True{}: Bool}
    -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(rest), c) == True{}: Bool}
) -> {
  List.any.if(w => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, k), b) == True{}: Bool
} -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Merges.Res.name(j), Keys.names(rest)), c)
    == True{}: Bool
}:
  match b:
    case True{}:
      h => Affects.cast(
        List<&2, U32>,
        z => {
          List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Merges.Res.name(z), Keys.names(rest)), c)
            == True{}: Bool
        },
        k,
        j,
        Equal.sym(List<&2, U32>, j, k, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), j, k)(eb)),
        Affects.cast(
          Maybe<&2, Resources.Name>,
          z => {
            List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, z, Keys.names(rest)), c)
              == True{}: Bool
          },
          Some{c},
          Merges.Res.name(k),
          Equal.sym(Maybe<&2, Resources.Name>, Merges.Res.name(k), Some{c}, en),
          Affects.contains_head(~Resources.Name, ~Resources.Name.is_eq, ~Affects.name_laws(), c, Keys.names(rest))
        )
      )
    case False{}:
      h => Affects.cons_keep(Merges.Res.name(j), Keys.names(rest), c)(ih(h))

# the name of a key among ks is among the names of ks
def Affects.keys_of(
  ks: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +c: Resources.Name,
  +en: {Merges.Res.name(k) == Some{c}: Maybe<&2, Resources.Name>}
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, k) == True{}: Bool}
  -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(ks), c) == True{}: Bool}:
  match ks:
    case Nil{}:
      h => Empty.absurd(
        {List.contains(~Resources.Name, ~Resources.Name.is_eq, [], c) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+j, +rest}:
      h => Affects.keys_of.at(j, rest, k, c, Shared.List.is_eq(~U32, ~U32.is_eq, j, k), {==}, en, h2 => Affects.keys_of(rest, k, c, en)(h2))(h)

# Affects.diff_names once it is known whether the two trees read the key of
# c the same (q)
def Affects.diff_names.bit(
  q: Bool,
  +v0: Maybe<&2, List<&2, U32>>,
  +v1: Maybe<&2, List<&2, U32>>,
  +eq: {
    Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), v0, v1) == q: Bool
  },
  +a: Maybe<&2, Requests.Res>,
  +b: Maybe<&2, Requests.Res>,
  eab: {v0 == v1: Maybe<&2, List<&2, U32>>} -> {a == b: Maybe<&2, Requests.Res>},
  +ns: {Bool.not(Vend.Res.same(a, b)) == True{}: Bool}
) -> {Bool.not(q) == True{}: Bool}:
  match q:
    case True{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Affects.cast(
            Bool,
            z => {Bool.not(z) == True{}: Bool},
            Vend.Res.same(a, b),
            True{},
            Affects.cast(
              Maybe<&2, Requests.Res>,
              z => {Vend.Res.same(a, z) == True{}: Bool},
              a,
              b,
              eab(
                Shared.Maybe.is_eq_sound(
                  ~List<&2, U32>,
                  ~Shared.List.is_eq(~U32, ~U32.is_eq),
                  x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
                  v0,
                  v1
                )(eq)
              ),
              Affects.same_refl(a)
            ),
            ns
          )
        )
      )
    case False{}:
      {==}

# Affects.diff_names once the reads m1 (of h) and m0 (of h0) of the key of c
# are known
def Affects.diff_names.fin(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +ed: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, h) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +c: Resources.Name,
  +a: Maybe<&2, Requests.Res>,
  +b: Maybe<&2, Requests.Res>,
  +ns: {Bool.not(Vend.Res.same(a, b)) == True{}: Bool},
  +m1: Maybe<&2, List<&2, U32>>,
  +m0: Maybe<&2, List<&2, U32>>,
  +em1: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(c)) == Some{m1}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +em0: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h0, Vend.Key.res(c)) == Some{m0}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +ea: {Vend.Res.found(m1) == a: Maybe<&2, Requests.Res>},
  +eb: {Vend.Res.found(m0) == b: Maybe<&2, Requests.Res>}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(ks), c) == True{}: Bool}:
  +look1 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(c))
  +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h0, Vend.Key.res(c))
  +e1 = Affects.known_value(look1, m1)(em1)
  +e0 = Affects.known_value(look0, m0)(em0)
  +iseq = Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Trees.Look.value(look1))
  Affects.keys_of(ks, Vend.Key.res(c), c, Affects.name_key(c))(
    Equal.trans(
      Bool,
      List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Vend.Key.res(c)),
      Bool.not(iseq),
      True{},
      Affects.diff_has(~d, l, h0, h, ks, ed, Vend.Key.res(c)),
      Affects.diff_names.bit(
        iseq,
        Trees.Look.value(look0),
        Trees.Look.value(look1),
        {==},
        a,
        b,
        e => Equal.trans(
          Maybe<&2, Requests.Res>,
          a,
          Vend.Res.found(m1),
          b,
          Equal.sym(Maybe<&2, Requests.Res>, Vend.Res.found(m1), a, ea),
          Equal.trans(
            Maybe<&2, Requests.Res>,
            Vend.Res.found(m1),
            Vend.Res.found(m0),
            b,
            Equal.cong(
              Maybe<&2, List<&2, U32>>,
              Maybe<&2, Requests.Res>,
              Vend.Res.found,
              m1,
              m0,
              Equal.trans(
                Maybe<&2, List<&2, U32>>,
                m1,
                Trees.Look.value(look0),
                m0,
                Equal.trans(
                  Maybe<&2, List<&2, U32>>,
                  m1,
                  Trees.Look.value(look1),
                  Trees.Look.value(look0),
                  Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Look.value(look1), m1, e1),
                  Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Look.value(look0), Trees.Look.value(look1), e)
                ),
                e0
              )
            ),
            eb
          )
        ),
        ns
      )
    )
  )

# a resource that a version changed is a name of a key of the difference of
# its trees
def Affects.diff_names(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +ed: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, h) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +c: Resources.Name
) -> {Res.differs(~d, l, h, h0, c) == Some{True{}}: Maybe<&2, Bool>}
  -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(ks), c) == True{}: Bool}:
  -goal = {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(ks), c) == True{}: Bool}
  ediff => Affects.bind_some(
    Maybe<&2, Requests.Res>,
    Bool,
    goal,
    Vend.Res.find(~d, l, h, c),
    a => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Bool,
      Vend.Res.find(~d, l, h0, c),
      b => Some{Bool.not(Vend.Res.same(a, b))}
    ),
    True{},
    +a => ea => e2 => Affects.bind_some(
      Maybe<&2, Requests.Res>,
      Bool,
      goal,
      Vend.Res.find(~d, l, h0, c),
      b => Some{Bool.not(Vend.Res.same(a, b))},
      True{},
      +b => eb => e3 => Affects.bind_some(
        Maybe<&2, List<&2, U32>>,
        Maybe<&2, Requests.Res>,
        goal,
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Vend.Key.res(c)),
        m => Some{Vend.Res.found(m)},
        a,
        +m1 => em1 => fa => Affects.bind_some(
          Maybe<&2, List<&2, U32>>,
          Maybe<&2, Requests.Res>,
          goal,
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h0, Vend.Key.res(c)),
          m => Some{Vend.Res.found(m)},
          b,
          +m0 => em0 => fb => Affects.diff_names.fin(
            ~d,
            l,
            h0,
            h,
            ks,
            ed,
            c,
            a,
            b,
            Shared.Maybe.some_inj(Bool, Bool.not(Vend.Res.same(a, b)), True{}, e3),
            m1,
            m0,
            em1,
            em0,
            Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Vend.Res.found(m1), a, fa),
            Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Vend.Res.found(m0), b, fb)
          )
        )(eb)
      )(ea)
    )(e2)
  )(ediff)

# a word less zero, with a borrow in, is the word
def Affects.adc_zero(p: Nat, t: Word(p)) -> {Word.adc(p, t, Word.zero(p), True{}, True{}) == t: Word(p)}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(
            Word(q),
            Word(1n+q),
            w => WCon{False{}, w},
            Word.adc(q, r, Word.zero(q), True{}, True{}),
            r,
            Affects.adc_zero(q, r)
          )
        case WCon{True{}, +r}:
          Equal.cong(
            Word(q),
            Word(1n+q),
            w => WCon{True{}, w},
            Word.adc(q, r, Word.zero(q), True{}, True{}),
            r,
            Affects.adc_zero(q, r)
          )

# a word one more, less zero with no borrow in, is the word
def Affects.adc_inc(p: Nat, t: Word(p)) -> {Word.adc(p, Word.inc(p, t), Word.zero(p), True{}, False{}) == t: Word(p)}:
  match p:
    case 0n:
      match t:
        case WNil{}:
          {==}
    case 1n+q:
      match t:
        case WCon{False{}, +r}:
          Equal.cong(
            Word(q),
            Word(1n+q),
            w => WCon{False{}, w},
            Word.adc(q, r, Word.zero(q), True{}, True{}),
            r,
            Affects.adc_zero(q, r)
          )
        case WCon{True{}, +r}:
          Equal.cong(
            Word(q),
            Word(1n+q),
            w => WCon{True{}, w},
            Word.adc(q, Word.inc(q, r), Word.zero(q), True{}, False{}),
            r,
            Affects.adc_inc(q, r)
          )

# one more, then one less, is the number
def Affects.sub_inc(n: U32) -> {U32.sub(U32.inc(n), 1) == n: U32}:
  match n:
    case U32{w}:
      match w:
        case WCon{False{}, +r}:
          Equal.cong(
            Word(31n),
            U32,
            z => U32{WCon{False{}, z}},
            Word.adc(31n, r, Word.zero(31n), True{}, True{}),
            r,
            Affects.adc_zero(31n, r)
          )
        case WCon{True{}, +r}:
          Equal.cong(
            Word(31n),
            U32,
            z => U32{WCon{True{}, z}},
            Word.adc(31n, Word.inc(31n, r), Word.zero(31n), True{}, False{}),
            r,
            Affects.adc_inc(31n, r)
          )

# Affects.lt_not_last once it is known whether n is the last number (q)
def Affects.lt_not_last.at(
  +n: U32,
  +c: U32,
  q: Bool,
  eq: {U32.is_eq(n, 4294967295) == q: Bool},
  +h: {U32.is_lt(n, c) == True{}: Bool}
) -> {q == False{}: Bool}:
  match q:
    case True{}:
      +tm = U32.to_nat(4294967295)
      +tc = U32.to_nat(c)
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Nat.is_lt(tm, tm),
            True{},
            Equal.sym(Bool, Nat.is_lt(tm, tm), False{}, Shared.Nat.lt_irrefl(tm)),
            Shared.Nat.lt_le(tm, tc, tm)(
              Equal.trans(
                Bool,
                Nat.is_lt(tm, tc),
                U32.is_lt(4294967295, c),
                True{},
                Equal.sym(Bool, U32.is_lt(4294967295, c), Nat.is_lt(tm, tc), Shared.U32.is_lt_to_nat(4294967295, c)),
                Affects.cast(
                  U32,
                  z => {U32.is_lt(z, c) == True{}: Bool},
                  n,
                  4294967295,
                  Shared.U32.is_eq_sound(n, 4294967295)(eq),
                  h
                )
              )
            )(
              Equal.trans(
                Bool,
                Nat.is_le(tc, tm),
                U32.is_le(c, 4294967295),
                True{},
                Equal.sym(Bool, U32.is_le(c, 4294967295), Nat.is_le(tc, tm), Shared.U32.is_le_to_nat(c, 4294967295)),
                Shared.U32.le_last(c)
              )
            )
          )
        )
      )
    case False{}:
      {==}

# a number below another is not the last number
def Affects.lt_not_last(+n: U32, +c: U32) -> {U32.is_lt(n, c) == True{}: Bool} -> {U32.is_eq(n, 4294967295) == False{}: Bool}:
  h => Affects.lt_not_last.at(n, c, U32.is_eq(n, 4294967295), {==}, h)

# one more than a number below another is its successor as a Nat
def Affects.inc_nat(+n: U32, +c: U32) -> {U32.is_lt(n, c) == True{}: Bool} -> {U32.to_nat(U32.inc(n)) == 1n+U32.to_nat(n): Nat}:
  h => Shared.U32.inc_to_nat(n)(Affects.lt_not_last(n, c)(h))

# Affects.inc_ne_zero once it is known whether one more than n is zero (q)
def Affects.inc_ne_zero.at(
  +n: U32,
  +c: U32,
  q: Bool,
  eq: {U32.is_eq(U32.inc(n), 0) == q: Bool},
  +h: {U32.is_lt(n, c) == True{}: Bool}
) -> {q == False{}: Bool}:
  match q:
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Nat,
            Bool,
            z => Nat.is_eq(z, 0n),
            1n+U32.to_nat(n),
            0n,
            Equal.trans(
              Nat,
              1n+U32.to_nat(n),
              U32.to_nat(U32.inc(n)),
              0n,
              Equal.sym(Nat, U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), Affects.inc_nat(n, c)(h)),
              Equal.cong(U32, Nat, U32.to_nat, U32.inc(n), 0, Shared.U32.is_eq_sound(U32.inc(n), 0)(eq))
            )
          )
        )
      )
    case False{}:
      {==}

# one more than a number below another is not zero
def Affects.inc_ne_zero(+n: U32, +c: U32) -> {U32.is_lt(n, c) == True{}: Bool} -> {U32.is_eq(U32.inc(n), 0) == False{}: Bool}:
  h => Affects.inc_ne_zero.at(n, c, U32.is_eq(U32.inc(n), 0), {==}, h)

# the tree before the version after the number n, below the count, is the
# tree of the version n
def Affects.before_next(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +n: U32,
  +x: Replicas.Taken,
  +hn: {U32.is_lt(n, Replicas.Tip.count(tf)) == True{}: Bool},
  +et: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n) == Some{x}: Maybe<&2, Replicas.Taken>}
) -> {
  Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, U32.inc(n))
    == Some{Replicas.Taken.root(x)}: Maybe<&2, Maybe<&2, Hashes.Hash>>
}:
  %Equal.sym(Bool, U32.is_eq(U32.inc(n), 0), False{}, Affects.inc_ne_zero(n, Replicas.Tip.count(tf))(hn)): {
    Shared.Bool.when(
      Maybe<&2, Maybe<&2, Hashes.Hash>>,
      _,
      u => Some{None{}},
      u => Maybe.bind(
        &2,
        Replicas.Taken,
        Maybe<&2, Hashes.Hash>,
        Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, U32.sub(U32.inc(n), 1)),
        x => Some{Replicas.Taken.root(x)}
      )
    )
      == Some{Replicas.Taken.root(x)}: Maybe<&2, Maybe<&2, Hashes.Hash>>
  }
  %Equal.sym(U32, U32.sub(U32.inc(n), 1), n, Affects.sub_inc(n)): {
    Maybe.bind(
      &2,
      Replicas.Taken,
      Maybe<&2, Hashes.Hash>,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, _),
      x => Some{Replicas.Taken.root(x)}
    )
      == Some{Replicas.Taken.root(x)}: Maybe<&2, Maybe<&2, Hashes.Hash>>
  }
  %Equal.sym(Maybe<&2, Replicas.Taken>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n), Some{x}, et): {
    Maybe.bind(&2, Replicas.Taken, Maybe<&2, Hashes.Hash>, _, x => Some{Replicas.Taken.root(x)})
      == Some{Replicas.Taken.root(x)}: Maybe<&2, Maybe<&2, Hashes.Hash>>
  }
  {==}

# no empty list is a list with a head
def Affects.nil_ne_cons(-A: Data, -x: A, -r: List<&2, A>, e: {[] == x <> r: List<&2, A>}) -> Empty:
  Shared.Bool.true_ne_false(
    Equal.cong(
      Nat,
      Bool,
      z => Nat.is_eq(z, 0n),
      0n,
      1n+List.length(&2, A, r),
      Equal.cong(List<&2, A>, Nat, z => List.length(&2, A, z), [], x <> r, e)
    )
  )

# Affects.versions_cons once the read m of the number n is known
def Affects.versions_con(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +p: Nat,
  +n: U32,
  m: Maybe<&2, Maybe<&2, Replicas.Taken>>,
  +em: {
    Replicas.Tip.known(
      ~Replicas.Taken,
      ~Replicas.Taken.code,
      ~Replicas.Taken.code.read,
      Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
    )
      == m: Maybe<&2, Maybe<&2, Replicas.Taken>>
  },
  +x: Replicas.Taken,
  +rest: List<&2, Replicas.Taken>,
  -P: Type,
  k: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n) == Some{x}: Maybe<&2, Replicas.Taken>}
    -> {
      Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n)) == Some{rest}: Maybe<&2, List<&2, Replicas.Taken>>
    } -> P
) -> {
  Replicas.Taken.con(m, u2 => Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n)))
    == Some{x <> rest}: Maybe<&2, List<&2, Replicas.Taken>>
} -> P:
  match m:
    case None{}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(List<&2, Replicas.Taken>, x <> rest, e))
    case Some{None{}}:
      e => Empty.absurd(P, Shared.Maybe.none_ne_some(List<&2, Replicas.Taken>, x <> rest, e))
    case Some{Some{+x0}}:
      e => Affects.map_some(
        List<&2, Replicas.Taken>,
        List<&2, Replicas.Taken>,
        P,
        r => x0 <> r,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n)),
        x <> rest,
        +r0 => er0 => +ec => k(
          Affects.known_taken(~d, l, tf, n, x)(
            Affects.cast(
              Replicas.Taken,
              z => {
                Replicas.Tip.known(
                  ~Replicas.Taken,
                  ~Replicas.Taken.code,
                  ~Replicas.Taken.code.read,
                  Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
                )
                  == Some{Some{z}}: Maybe<&2, Maybe<&2, Replicas.Taken>>
              },
              x0,
              x,
              Shared.List.head_eq(Replicas.Taken, x0, x, r0, rest, ec),
              em
            )
          )
        )(
          Affects.cast(
            List<&2, Replicas.Taken>,
            z => {
              Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n)) == Some{z}: Maybe<&2, List<&2, Replicas.Taken>>
            },
            r0,
            rest,
            Shared.List.tail_eq(Replicas.Taken, x0, x, r0, rest, ec),
            er0
          )
        )
      )(e)

# a listing of versions from the number n that starts with x: n is below the
# count, x is the version n, and the rest lists from the next number
def Affects.versions_cons(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +p: Nat,
  +n: U32,
  +x: Replicas.Taken,
  +rest: List<&2, Replicas.Taken>,
  -P: Type,
  k: {U32.is_lt(n, Replicas.Tip.count(tf)) == True{}: Bool}
    -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n) == Some{x}: Maybe<&2, Replicas.Taken>}
    -> {
      Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n)) == Some{rest}: Maybe<&2, List<&2, Replicas.Taken>>
    } -> P
) -> {
  Replicas.Tip.versions(~Requests.Ask.machine(), ~d, 1n+p, l, tf, n) == Some{x <> rest}: Maybe<&2, List<&2, Replicas.Taken>>
} -> P:
  e => Affects.when_is(
    Maybe<&2, List<&2, Replicas.Taken>>,
    P,
    U32.is_lt(n, Replicas.Tip.count(tf)),
    u => Replicas.Taken.con(
      Replicas.Tip.known(
        ~Replicas.Taken,
        ~Replicas.Taken.code,
        ~Replicas.Taken.code.read,
        Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
      ),
      u2 => Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n))
    ),
    u => Some{[]},
    Some{x <> rest},
    +et => e1 => Affects.versions_con(
      ~d,
      l,
      tf,
      p,
      n,
      Replicas.Tip.known(
        ~Replicas.Taken,
        ~Replicas.Taken.code,
        ~Replicas.Taken.code.read,
        Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
      ),
      {==},
      x,
      rest,
      P,
      k(et)
    )(e1),
    ef => e2 => Empty.absurd(
      P,
      Affects.nil_ne_cons(
        Replicas.Taken,
        x,
        rest,
        Shared.Maybe.some_inj(List<&2, Replicas.Taken>, [], x <> rest, e2)
      )
    )
  )(e)

# Touches.of, each touch: by the head u of used, once it is known whether the
# touch of u is x (q)
def Affects.of_in.hit(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  +u: Resources.Name,
  +rest: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit),
  -P: Touch -> Type,
  +x: Touch,
  q: Bool,
  eq: {Touch.is_eq(Touch{from, v, c, b, u}, x) == q: Bool},
  +econd: {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)) == True{}: Bool},
  hp: @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, u <> rest, u2) == True{}: Bool}
    -> {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u2)), Resources.Name.is_eq(u2, c)) == True{}: Bool}
    -> P(Touch{from, v, c, b, u2}),
  ih: (
    @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, u2) == True{}: Bool}
      -> {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u2)), Resources.Name.is_eq(u2, c)) == True{}: Bool}
      -> P(Touch{from, v, c, b, u2})
  ) -> {List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, rest, reach), x) == True{}: Bool} -> P(x)
) -> {
  List.any.if(w => List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, rest, reach), x), q) == True{}: Bool
} -> P(x):
  match q:
    case True{}:
      h => Affects.cast(
        Touch,
        P,
        Touch{from, v, c, b, u},
        x,
        Affects.touch_sound(Touch{from, v, c, b, u}, x)(eq),
        hp(u)(Affects.contains_head(~Resources.Name, ~Resources.Name.is_eq, ~Affects.name_laws(), u, rest))(econd)
      )
    case False{}:
      h => ih(+u2 => a => e => hp(u2)(Shared.List.contains_cons(~Resources.Name, ~Resources.Name.is_eq, u, rest, u2)(a))(e))(h)

# Touches.of, each touch: by the head u of used, once it is known whether u
# is kept (cnd)
def Affects.of_in.at(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  +u: Resources.Name,
  +rest: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit),
  -P: Touch -> Type,
  +x: Touch,
  cnd: Bool,
  +ecnd: {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)) == cnd: Bool},
  hp: @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, u <> rest, u2) == True{}: Bool}
    -> {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u2)), Resources.Name.is_eq(u2, c)) == True{}: Bool}
    -> P(Touch{from, v, c, b, u2}),
  ih: (
    @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, u2) == True{}: Bool}
      -> {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u2)), Resources.Name.is_eq(u2, c)) == True{}: Bool}
      -> P(Touch{from, v, c, b, u2})
  ) -> {List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, rest, reach), x) == True{}: Bool} -> P(x)
) -> {
  List.contains(
    ~Touch,
    ~Touch.is_eq,
    List.filter.put(Touch, Touch{from, v, c, b, u}, Touches.of(from, v, c, b, rest, reach), cnd),
    x
  )
    == True{}: Bool
} -> P(x):
  match cnd:
    case True{}:
      h => Affects.of_in.hit(from, v, c, b, u, rest, reach, P, x, Touch.is_eq(Touch{from, v, c, b, u}, x), {==}, ecnd, hp, ih)(h)
    case False{}:
      h => ih(+u2 => a => e => hp(u2)(Shared.List.contains_cons(~Resources.Name, ~Resources.Name.is_eq, u, rest, u2)(a))(e))(h)

# each touch that Touches.of gives is of a resource of used that is c or that
# the set reach holds
def Affects.of_in(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  used: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit),
  -P: Touch -> Type,
  hp: @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u2) == True{}: Bool}
    -> {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u2)), Resources.Name.is_eq(u2, c)) == True{}: Bool}
    -> P(Touch{from, v, c, b, u2}),
  +x: Touch
) -> {List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, used, reach), x) == True{}: Bool} -> P(x):
  match used:
    case Nil{}:
      h => Empty.absurd(P(x), Shared.Bool.false_ne_true(h))
    case Con{+u, +rest}:
      h => Affects.of_in.at(
        from,
        v,
        c,
        b,
        u,
        rest,
        reach,
        P,
        x,
        List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)),
        {==},
        hp,
        hp2 => h2 => Affects.of_in(from, v, c, b, rest, reach, P, hp2, x)(h2)
      )(h)

# Affects.app_in once it is known whether a holds x (q)
def Affects.app_in.at(
  -H: Type,
  -P: Touch -> Type,
  +a: List<&2, Touch>,
  +r: List<&2, Touch>,
  +x: Touch,
  q: Bool,
  eq: {List.contains(~Touch, ~Touch.is_eq, a, x) == q: Bool},
  hp: H,
  ka: H -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool} -> P(x),
  kr: H -> {List.contains(~Touch, ~Touch.is_eq, r, x) == True{}: Bool} -> P(x)
) -> {Bool.or(q, List.contains(~Touch, ~Touch.is_eq, r, x)) == True{}: Bool} -> P(x):
  match q:
    case True{}:
      h => ka(hp)(eq)
    case False{}:
      h => kr(hp)(h)

# a touch of a ++ r is a touch of a or of r
def Affects.app_in(
  -H: Type,
  -P: Touch -> Type,
  +a: List<&2, Touch>,
  +r: List<&2, Touch>,
  +x: Touch,
  hp: H,
  ka: H -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool} -> P(x),
  kr: H -> {List.contains(~Touch, ~Touch.is_eq, r, x) == True{}: Bool} -> P(x)
) -> {List.contains(~Touch, ~Touch.is_eq, List.append(&2, Touch, a, r), x) == True{}: Bool} -> P(x):
  h => Affects.app_in.at(H, P, a, r, x, List.contains(~Touch, ~Touch.is_eq, a, x), {==}, hp, ka, kr)(
    Equal.trans(
      Bool,
      Bool.or(List.contains(~Touch, ~Touch.is_eq, a, x), List.contains(~Touch, ~Touch.is_eq, r, x)),
      List.contains(~Touch, ~Touch.is_eq, List.append(&2, Touch, a, r), x),
      True{},
      Equal.sym(
        Bool,
        List.contains(~Touch, ~Touch.is_eq, List.append(&2, Touch, a, r), x),
        Bool.or(List.contains(~Touch, ~Touch.is_eq, a, x), List.contains(~Touch, ~Touch.is_eq, r, x)),
        Shared.List.contains_append(~Touch, ~Touch.is_eq, a, r, x)
      ),
      h
    )
  )

# no touch is in a list that a read gave as empty
def Affects.none_in(-P: Touch -> Type, +ts: List<&2, Touch>, +x: Touch, e: {Some{[]} == Some{ts}: Maybe<&2, List<&2, Touch>>}) -> {
  List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool
} -> P(x):
  h => Empty.absurd(
    P(x),
    Shared.Bool.false_ne_true(
      Affects.cast(
        List<&2, Touch>,
        z => {List.contains(~Touch, ~Touch.is_eq, z, x) == True{}: Bool},
        ts,
        [],
        Equal.sym(List<&2, Touch>, [], ts, Shared.Maybe.some_inj(List<&2, Touch>, [], ts, e)),
        h
      )
    )
  )

# that P holds of each touch of the version v of from, whose tree is h and
# came after the tree h0, on the branch b whose tree is hb: of each resource c
# that v wrote and that b does not hold as v gave it, for each resource u of
# used that is c or that uses it by the users graph
def Affects.HpEach(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type
) -> Type:
  @c: Resources.Name -> {Res.differs(~d, l, h, h0, c) == Some{True{}}: Maybe<&2, Bool>}
    -> {Res.differs(~d, l, h, hb, c) == Some{True{}}: Maybe<&2, Bool>}
    -> @u2: Resources.Name -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u2) == True{}: Bool}
    -> {
      List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(c)), Name.key(u2)), Resources.Name.is_eq(u2, c))
        == True{}: Bool
    } -> P(Touch{from, v, c, b, u2})

# Affects.touched_in once the first test w is known
def Affects.touched_in.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type,
  w: Bool,
  +ew: {Res.differs(~d, l, h, h0, c) == Some{w}: Maybe<&2, Bool>},
  +e2: {
    Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>
  },
  hp: Affects.HpEach(~d, l, from, v, h0, h, b, hb, used, users, P),
  +x: Touch
) -> {
  List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, used, Reaches.Graph.reach(users, Name.key(c))), x) == True{}: Bool
} -> P(x):
  match w:
    case True{}:
      hc => Affects.of_in(from, v, c, b, used, Reaches.Graph.reach(users, Name.key(c)), P, hp(c)(ew)(e2), x)(hc)
    case False{}:
      hc => Empty.absurd(P(x), Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e2)))

# each touch of a resource c that Touches.each touches
def Affects.touched_in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type,
  touched: Bool,
  +et: {
    Maybe.bind(
      &2,
      Bool,
      Bool,
      Res.differs(~d, l, h, h0, c),
      w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
    )
      == Some{touched}: Maybe<&2, Bool>
  },
  hp: Affects.HpEach(~d, l, from, v, h0, h, b, hb, used, users, P),
  +x: Touch
) -> {List.contains(~Touch, ~Touch.is_eq, Touches.when(touched, from, v, c, b, used, users), x) == True{}: Bool} -> P(x):
  match touched:
    case False{}:
      hc => Empty.absurd(P(x), Shared.Bool.false_ne_true(hc))
    case True{}:
      +hc => Affects.bind_some(
        Bool,
        Bool,
        P(x),
        Res.differs(~d, l, h, h0, c),
        w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}}),
        True{},
        +w => ew => e2 => Affects.touched_in.at(~d, l, from, v, h0, h, c, b, hb, used, users, P, w, ew, e2, hp, x)(hc)
      )(et)

# each touch that Touches.each gives
def Affects.each_in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type,
  hp: Affects.HpEach(~d, l, from, v, h0, h, b, hb, used, users, P),
  +x: Touch
) -> @ts: List<&2, Touch> -> {
  Touches.each(~d, l, from, v, h0, h, changed, b, hb, used, users) == Some{ts}: Maybe<&2, List<&2, Touch>>
} -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool} -> P(x):
  match changed:
    case Nil{}:
      +ts => e => hc => Affects.none_in(P, ts, x, e)(hc)
    case Con{+c, +rest}:
      +ts => e => +hc => Affects.bind_some(
        Bool,
        List<&2, Touch>,
        P(x),
        Maybe.bind(
          &2,
          Bool,
          Bool,
          Res.differs(~d, l, h, h0, c),
          w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
        ),
        touched => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, Touches.when(touched, from, v, c, b, used, users), r),
          Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users)
        ),
        ts,
        +touched => +et => e2 => Affects.map_some(
          List<&2, Touch>,
          List<&2, Touch>,
          P(x),
          r => List.append(&2, Touch, Touches.when(touched, from, v, c, b, used, users), r),
          Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users),
          ts,
          +r => +er => +eapp => Affects.app_in(
            Affects.HpEach(~d, l, from, v, h0, h, b, hb, used, users, P),
            P,
            Touches.when(touched, from, v, c, b, used, users),
            r,
            x,
            hp,
            hp1 => ha => Affects.touched_in(~d, l, from, v, h0, h, c, b, hb, used, users, P, touched, et, hp1, x)(ha),
            hp2 => hr => Affects.each_in(~d, l, from, v, h0, h, rest, b, hb, used, users, P, hp2, x)(r)(er)(hr)
          )(
            Affects.cast(
              List<&2, Touch>,
              z => {List.contains(~Touch, ~Touch.is_eq, z, x) == True{}: Bool},
              ts,
              List.append(&2, Touch, Touches.when(touched, from, v, c, b, used, users), r),
              Equal.sym(List<&2, Touch>, List.append(&2, Touch, Touches.when(touched, from, v, c, b, used, users), r), ts, eapp),
              hc
            )
          )
        )(e2)
      )(e)

# that P holds of each touch of each version of the listing at the tip tf of
# the branch from: of a version of the ID i whose number m reads back, whose
# tree hy came after hz
def Affects.HpAll(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type
) -> Type:
  @i: Ledgers.Id -> @hz: Maybe<&2, Hashes.Hash> -> @hy: Maybe<&2, Hashes.Hash> -> @m: U32
    -> {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{m}: Maybe<&2, U32>}
    -> {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>}
    -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>}
    -> Affects.HpEach(~d, l, from, i, hz, hy, b, hb, used, users, P)

# each touch of the version i of the listing, whose number m is n
def Affects.all_hit(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +i: Ledgers.Id,
  +hy: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +m: U32,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{m}: Maybe<&2, U32>},
  +eb: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n) == Some{h0}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>},
  +a: List<&2, Touch>,
  +ea: {
    Shared.Bool.when(
      Maybe<&2, List<&2, Touch>>,
      U32.is_eq(m, n),
      u => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
      u => Some{[]}
    )
      == Some{a}: Maybe<&2, List<&2, Touch>>
  },
  hp: Affects.HpAll(~d, l, from, tf, b, hb, used, users, P),
  +x: Touch
) -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool} -> P(x):
  +hc => Affects.when_is(
    Maybe<&2, List<&2, Touch>>,
    P(x),
    U32.is_eq(m, n),
    u => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
    u => Some{[]},
    Some{a},
    +eqt => e1 => Affects.each_in(
      ~d,
      l,
      from,
      i,
      h0,
      hy,
      Keys.names(ks),
      b,
      hb,
      used,
      users,
      P,
      hp(i)(h0)(hy)(n)(
        Affects.cast(
          U32,
          z => {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{z}: Maybe<&2, U32>},
          m,
          n,
          Shared.U32.is_eq_sound(m, n)(eqt),
          enum
        )
      )(eb)(etk),
      x
    )(a)(e1)(hc),
    eqf => e2 => Affects.none_in(P, a, x, e2)(hc)
  )(ea)

# each touch that Touches.all gives, of a listing of k versions from the
# number n, whose tree before is h0
def Affects.all_in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  -P: Touch -> Type,
  hp: Affects.HpAll(~d, l, from, tf, b, hb, used, users, P),
  k: Nat,
  +eb: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n) == Some{h0}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +ev: {Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, tf, n) == Some{xs}: Maybe<&2, List<&2, Replicas.Taken>>},
  +x: Touch
) -> @ts: List<&2, Touch> -> {
  Touches.all(~d, l, from, tf, xs, n, h0, b, hb, used, users) == Some{ts}: Maybe<&2, List<&2, Touch>>
} -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool} -> P(x):
  match xs k:
    case Nil{} j:
      +ts => e => hc => Affects.none_in(P, ts, x, e)(hc)
    case Con{Replicas.Taken{+i, +hy}, +rest} 0n:
      ts => e => hc => Empty.absurd(
        P(x),
        Affects.nil_ne_cons(
          Replicas.Taken,
          Replicas.Taken{i, hy},
          rest,
          Shared.Maybe.some_inj(List<&2, Replicas.Taken>, [], Replicas.Taken{i, hy} <> rest, ev)
        )
      )
    case Con{Replicas.Taken{+i, +hy}, +rest} 1n+(+p):
      +ts => e => +hc => Affects.versions_cons(
        ~d,
        l,
        tf,
        p,
        n,
        Replicas.Taken{i, hy},
        rest,
        P(x),
        +elt => +etk => +evr => Affects.bind_some(
          List<&2, List<&2, U32>>,
          List<&2, Touch>,
          P(x),
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, hy),
          ks => Maybe.bind(
            &2,
            U32,
            List<&2, Touch>,
            Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
            m => Maybe.bind(
              &2,
              List<&2, Touch>,
              List<&2, Touch>,
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m, n),
                u => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                u => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              )
            )
          ),
          ts,
          +ks => eks => e1 => Affects.bind_some(
            U32,
            List<&2, Touch>,
            P(x),
            Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
            m => Maybe.bind(
              &2,
              List<&2, Touch>,
              List<&2, Touch>,
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m, n),
                u => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                u => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              )
            ),
            ts,
            +m => +enum => e2 => Affects.bind_some(
              List<&2, Touch>,
              List<&2, Touch>,
              P(x),
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m, n),
                u => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                u => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              ),
              ts,
              +a => +ea => e3 => Affects.map_some(
                List<&2, Touch>,
                List<&2, Touch>,
                P(x),
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users),
                ts,
                +r => +er => +eapp => Affects.app_in(
                  Affects.HpAll(~d, l, from, tf, b, hb, used, users, P),
                  P,
                  a,
                  r,
                  x,
                  hp,
                  hp1 => ha => Affects.all_hit(~d, l, from, tf, i, hy, ks, m, n, h0, b, hb, used, users, P, enum, eb, etk, a, ea, hp1, x)(ha),
                  hp2 => hr => Affects.all_in(
                    ~d,
                    l,
                    from,
                    tf,
                    rest,
                    U32.inc(n),
                    hy,
                    b,
                    hb,
                    used,
                    users,
                    P,
                    hp2,
                    p,
                    Affects.before_next(~d, l, tf, n, Replicas.Taken{i, hy}, elt, etk),
                    evr,
                    x
                  )(r)(er)(hr)
                )(
                  Affects.cast(
                    List<&2, Touch>,
                    z => {List.contains(~Touch, ~Touch.is_eq, z, x) == True{}: Bool},
                    ts,
                    List.append(&2, Touch, a, r),
                    Equal.sym(List<&2, Touch>, List.append(&2, Touch, a, r), ts, eapp),
                    hc
                  )
                )
              )(e3)
            )(e2)
          )(e1)
        )(e)
      )(ev)

# a read that is some value is some of its value or the graph with no node
def Affects.some_is(m: Maybe<&2, Reaches.Graph>) -> {Maybe.is_some(&2, Reaches.Graph, m) == True{}: Bool}
  -> {m == Some{Maybe.default(&2, Reaches.Graph, m, Reaches.Graph.new())}: Maybe<&2, Reaches.Graph>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{Reaches.Graph.new()}: Maybe<&2, Reaches.Graph>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{g}:
      h => {==}

# Affects.reaches_of once it is known whether used is changed (q)
def Affects.reaches_of.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  },
  +used: Resources.Name,
  +changed: Resources.Name,
  q: Bool,
  +b1: {
    List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(changed)), Name.key(used)), q) == True{}: Bool
  }
) -> {
  Shared.Bool.when(
    Maybe<&2, Bool>,
    q,
    u => Some{True{}},
    u => Maybe.bind(
      &2,
      Reaches.Graph,
      Bool,
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Reaches.Graph,
        Tree.resources(~d, l, hb),
        ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
      ),
      g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
    )
  )
    == Some{True{}}: Maybe<&2, Bool>
}:
  match q:
    case True{}:
      {==}
    case False{}:
      +gr = Uses.graph(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
      +us = Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
      +side1 = Affects.side(~d, l, view, hb, Res.names(xs), True{})
      +eg = Affects.some_is(gr)(
        Equal.trans(
          Bool,
          Maybe.is_some(&2, Reaches.Graph, gr),
          Maybe.is_some(&2, Reaches.Graph, us),
          True{},
          Equal.sym(
            Bool,
            Maybe.is_some(&2, Reaches.Graph, us),
            Maybe.is_some(&2, Reaches.Graph, gr),
            Affects.some_fold(~d, l, view, hb, Res.names(xs), Reaches.Graph.new(), Reaches.Graph.new())
          ),
          Affects.cast(
            Maybe<&2, Reaches.Graph>,
            z => {Maybe.is_some(&2, Reaches.Graph, z) == True{}: Bool},
            Some{users},
            us,
            Equal.sym(Maybe<&2, Reaches.Graph>, us, Some{users}, eu),
            {==}
          )
        )
      )
      +ehas = Affects.reach_rev(~d, l, view, hb, Res.names(xs), False{}, Name.key(changed), Name.key(used))(
        Affects.cast(
          Reaches.Graph,
          z => {Crits.Dict.has(Unit, Reaches.Graph.reach(z, Name.key(changed)), Name.key(used)) == True{}: Bool},
          users,
          Affects.side(~d, l, view, hb, Res.names(xs), False{}),
          Equal.sym(
            Reaches.Graph,
            Affects.side(~d, l, view, hb, Res.names(xs), False{}),
            users,
            Equal.cong(
              Maybe<&2, Reaches.Graph>,
              Reaches.Graph,
              z => Maybe.default(&2, Reaches.Graph, z, Reaches.Graph.new()),
              us,
              Some{users},
              eu
            )
          ),
          b1
        )
      )
      %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, Vend.Tree.range(~d, l, hb, [0]), Some{xs}, er): {
        Maybe.bind(
          &2,
          Reaches.Graph,
          Bool,
          Maybe.bind(
            &2,
            List<&2, Resources.Name>,
            Reaches.Graph,
            Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Resources.Name>, Res.names, _),
            ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
          ),
          g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
        )
          == Some{True{}}: Maybe<&2, Bool>
      }
      %Equal.sym(Maybe<&2, Reaches.Graph>, gr, Some{side1}, eg): {
        Maybe.bind(
          &2,
          Reaches.Graph,
          Bool,
          _,
          g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
        )
          == Some{True{}}: Maybe<&2, Bool>
      }
      %Equal.sym(Bool, Crits.Dict.has(Unit, Reaches.Graph.reach(side1, Name.key(used)), Name.key(changed)), True{}, ehas): {
        Some{_} == Some{True{}}: Maybe<&2, Bool>
      }
      {==}

# a resource of a branch that the users graph of a changed resource finds, or
# that is that resource, uses it
def Affects.reaches_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  },
  +used: Resources.Name,
  +changed: Resources.Name,
  +b1: {
    List.any.if(
      w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(changed)), Name.key(used)),
      Resources.Name.is_eq(used, changed)
    )
      == True{}: Bool
  }
) -> {Uses.reaches(~d, l, view, hb, used, changed) == Some{True{}}: Maybe<&2, Bool>}:
  Affects.reaches_of.at(~d, l, view, hb, xs, er, users, eu, used, changed, Resources.Name.is_eq(used, changed), b1)

# the version m wrote the resource changed: the tree after it does not hold
# what the tree before it does
def Affects.wrote_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +m: U32,
  +changed: Resources.Name,
  +i: Ledgers.Id,
  +hz: Maybe<&2, Hashes.Hash>,
  +hy: Maybe<&2, Hashes.Hash>,
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>},
  +d1: {Res.differs(~d, l, hy, hz, changed) == Some{True{}}: Maybe<&2, Bool>}
) -> {Version.wrote(~d, l, tf, m, changed) == Some{True{}}: Maybe<&2, Bool>}:
  %Equal.sym(Maybe<&2, Maybe<&2, Hashes.Hash>>, Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m), Some{hz}, ebef): {
    Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Bool,
      _,
      h0 => Maybe.bind(
        &2,
        Replicas.Taken,
        Bool,
        Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m),
        x => Res.differs(~d, l, Replicas.Taken.root(x), h0, changed)
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Replicas.Taken>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), Some{Replicas.Taken{i, hy}}, etk): {
    Maybe.bind(&2, Replicas.Taken, Bool, _, x => Res.differs(~d, l, Replicas.Taken.root(x), hz, changed))
      == Some{True{}}: Maybe<&2, Bool>
  }
  d1

# the tree of the version i is the tree that the line took as its number
def Affects.version_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +i: Ledgers.Id,
  +m: U32,
  +hy: Maybe<&2, Hashes.Hash>,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{m}: Maybe<&2, U32>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>}
) -> {Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, i) == Some{hy}: Maybe<&2, Maybe<&2, Hashes.Hash>>}:
  %Equal.sym(Maybe<&2, U32>, Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i), Some{m}, enum): {
    Maybe.bind(
      &2,
      U32,
      Maybe<&2, Hashes.Hash>,
      _,
      m2 => Maybe.bind(
        &2,
        Replicas.Taken,
        Maybe<&2, Hashes.Hash>,
        Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m2),
        x => Some{Replicas.Taken.root(x)}
      )
    )
      == Some{hy}: Maybe<&2, Maybe<&2, Hashes.Hash>>
  }
  %Equal.sym(Maybe<&2, Replicas.Taken>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), Some{Replicas.Taken{i, hy}}, etk): {
    Maybe.bind(&2, Replicas.Taken, Maybe<&2, Hashes.Hash>, _, x => Some{Replicas.Taken.root(x)})
      == Some{hy}: Maybe<&2, Maybe<&2, Hashes.Hash>>
  }
  {==}

# Touch.holds.at, from each fact that it reads
def Affects.holds_at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +i: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  +m: U32,
  +hz: Maybe<&2, Hashes.Hash>,
  +hy: Maybe<&2, Hashes.Hash>,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{m}: Maybe<&2, U32>},
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>},
  +d1: {Res.differs(~d, l, hy, hz, changed) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, hy, Replicas.Tip.content(tb), changed) == Some{True{}}: Maybe<&2, Bool>},
  +r0: Maybe<&2, Requests.Res>,
  +efind: {Vend.Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +esome: {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool},
  +ereach: {Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed) == Some{True{}}: Maybe<&2, Bool>}
) -> {Touch.holds.at(~d, l, view, tf, tb, i, changed, used) == Some{True{}}: Maybe<&2, Bool>}:
  +hb = Replicas.Tip.content(tb)
  %Equal.sym(Maybe<&2, U32>, Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i), Some{m}, enum): {
    Maybe.bind(
      &2,
      U32,
      Bool,
      _,
      m2 => Maybe.bind(
        &2,
        Bool,
        Bool,
        Version.wrote(~d, l, tf, m2, changed),
        wrote => Shared.Bool.when(
          Maybe<&2, Bool>,
          wrote,
          u => Maybe.bind(
            &2,
            Maybe<&2, Hashes.Hash>,
            Bool,
            Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, i),
            h => Maybe.bind(
              &2,
              Bool,
              Bool,
              Res.differs(~d, l, h, hb, changed),
              differs => Shared.Bool.when(
                Maybe<&2, Bool>,
                differs,
                u2 => Maybe.bind(
                  &2,
                  Maybe<&2, Requests.Res>,
                  Bool,
                  Vend.Res.find(~d, l, hb, used),
                  r => Shared.Bool.when(
                    Maybe<&2, Bool>,
                    Maybe.is_some(&2, Requests.Res, r),
                    u3 => Uses.reaches(~d, l, view, hb, used, changed),
                    u3 => Some{False{}}
                  )
                ),
                u2 => Some{False{}}
              )
            )
          ),
          u => Some{False{}}
        )
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Bool>, Version.wrote(~d, l, tf, m, changed), Some{True{}}, Affects.wrote_of(~d, l, tf, m, changed, i, hz, hy, ebef, etk, d1)): {
    Maybe.bind(
      &2,
      Bool,
      Bool,
      _,
      wrote => Shared.Bool.when(
        Maybe<&2, Bool>,
        wrote,
        u => Maybe.bind(
          &2,
          Maybe<&2, Hashes.Hash>,
          Bool,
          Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, i),
          h => Maybe.bind(
            &2,
            Bool,
            Bool,
            Res.differs(~d, l, h, hb, changed),
            differs => Shared.Bool.when(
              Maybe<&2, Bool>,
              differs,
              u2 => Maybe.bind(
                &2,
                Maybe<&2, Requests.Res>,
                Bool,
                Vend.Res.find(~d, l, hb, used),
                r => Shared.Bool.when(
                  Maybe<&2, Bool>,
                  Maybe.is_some(&2, Requests.Res, r),
                  u3 => Uses.reaches(~d, l, view, hb, used, changed),
                  u3 => Some{False{}}
                )
              ),
              u2 => Some{False{}}
            )
          )
        ),
        u => Some{False{}}
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Maybe<&2, Hashes.Hash>>, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, i), Some{hy}, Affects.version_of(~d, l, tf, i, m, hy, enum, etk)): {
    Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Bool,
      _,
      h => Maybe.bind(
        &2,
        Bool,
        Bool,
        Res.differs(~d, l, h, hb, changed),
        differs => Shared.Bool.when(
          Maybe<&2, Bool>,
          differs,
          u2 => Maybe.bind(
            &2,
            Maybe<&2, Requests.Res>,
            Bool,
            Vend.Res.find(~d, l, hb, used),
            r => Shared.Bool.when(
              Maybe<&2, Bool>,
              Maybe.is_some(&2, Requests.Res, r),
              u3 => Uses.reaches(~d, l, view, hb, used, changed),
              u3 => Some{False{}}
            )
          ),
          u2 => Some{False{}}
        )
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Bool>, Res.differs(~d, l, hy, hb, changed), Some{True{}}, d2): {
    Maybe.bind(
      &2,
      Bool,
      Bool,
      _,
      differs => Shared.Bool.when(
        Maybe<&2, Bool>,
        differs,
        u2 => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Bool,
          Vend.Res.find(~d, l, hb, used),
          r => Shared.Bool.when(
            Maybe<&2, Bool>,
            Maybe.is_some(&2, Requests.Res, r),
            u3 => Uses.reaches(~d, l, view, hb, used, changed),
            u3 => Some{False{}}
          )
        ),
        u2 => Some{False{}}
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Vend.Res.find(~d, l, hb, used), Some{r0}, efind): {
    Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Bool,
      _,
      r => Shared.Bool.when(
        Maybe<&2, Bool>,
        Maybe.is_some(&2, Requests.Res, r),
        u3 => Uses.reaches(~d, l, view, hb, used, changed),
        u3 => Some{False{}}
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Bool, Maybe.is_some(&2, Requests.Res, r0), True{}, esome): {
    Shared.Bool.when(Maybe<&2, Bool>, _, u3 => Uses.reaches(~d, l, view, hb, used, changed), u3 => Some{False{}})
      == Some{True{}}: Maybe<&2, Bool>
  }
  ereach

# Touch.holds of a touch of other branches whose tips are tf and tb, from
# Touch.holds.at
def Affects.holds_of(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +b: Vend.Branch,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +eo: {Branch.other(from, b) == True{}: Bool},
  +ef: {Branch.head(~d, ~kern, l, from) == Some{tf}: Maybe<&2, Replicas.Tip>},
  +eb: {Branch.head(~d, ~kern, l, b) == Some{tb}: Maybe<&2, Replicas.Tip>},
  +i: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  +ehat: {Touch.holds.at(~d, l, view, tf, tb, i, changed, used) == Some{True{}}: Maybe<&2, Bool>}
) -> {Touch.holds(~d, ~kern, l, view, Touch{from, i, changed, b, used}) == Some{True{}}: Maybe<&2, Bool>}:
  %Equal.sym(Bool, Branch.other(from, b), True{}, eo): {
    Shared.Bool.when(
      Maybe<&2, Bool>,
      _,
      u => Maybe.bind(
        &2,
        Replicas.Tip,
        Bool,
        Branch.head(~d, ~kern, l, from),
        tf2 => Maybe.bind(
          &2,
          Replicas.Tip,
          Bool,
          Branch.head(~d, ~kern, l, b),
          tb2 => Touch.holds.at(~d, l, view, tf2, tb2, i, changed, used)
        )
      ),
      u => Some{False{}}
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Replicas.Tip>, Branch.head(~d, ~kern, l, from), Some{tf}, ef): {
    Maybe.bind(
      &2,
      Replicas.Tip,
      Bool,
      _,
      tf2 => Maybe.bind(
        &2,
        Replicas.Tip,
        Bool,
        Branch.head(~d, ~kern, l, b),
        tb2 => Touch.holds.at(~d, l, view, tf2, tb2, i, changed, used)
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Maybe<&2, Replicas.Tip>, Branch.head(~d, ~kern, l, b), Some{tb}, eb): {
    Maybe.bind(&2, Replicas.Tip, Bool, _, tb2 => Touch.holds.at(~d, l, view, tf, tb2, i, changed, used))
      == Some{True{}}: Maybe<&2, Bool>
  }
  ehat

# each touch that Branch.touches.at gives holds
def Affects.at_in(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +b: Vend.Branch,
  +tb: Replicas.Tip,
  +eo: {Branch.other(from, b) == True{}: Bool},
  +ef: {Branch.head(~d, ~kern, l, from) == Some{tf}: Maybe<&2, Replicas.Tip>},
  +eb: {Branch.head(~d, ~kern, l, b) == Some{tb}: Maybe<&2, Replicas.Tip>},
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Branch.touches.at(~d, l, view, from, tf, b, tb) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  +hb = Replicas.Tip.content(tb)
  e => +hc => Affects.bind_some(
    List<&2, Trees.Binding>,
    List<&2, Touch>,
    {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
    Vend.Tree.range(~d, l, hb, [0]),
    xs => Maybe.bind(
      &2,
      Reaches.Graph,
      List<&2, Touch>,
      Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
      users => Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users)
      )
    ),
    ts,
    +xs => +er => e2 => Affects.bind_some(
      Reaches.Graph,
      List<&2, Touch>,
      {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
      Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
      users => Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users)
      ),
      ts,
      +users => +eu => e3 => Affects.bind_some(
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users),
        ts,
        +xs2 => +ev => e4 => Affects.all_in(
          ~d,
          l,
          from,
          tf,
          xs2,
          0,
          None{},
          b,
          hb,
          Res.names(xs),
          users,
          y => {Touch.holds(~d, ~kern, l, view, y) == Some{True{}}: Maybe<&2, Bool>},
          +i => +hz => +hy => +m => +enum => +ebef => +etk => +c => +d1 => +d2 => +u2 => a1 => +b1 => Affects.find_named(
            ~d,
            l,
            hb,
            xs,
            er,
            u2,
            {Touch.holds(~d, ~kern, l, view, Touch{from, i, c, b, u2}) == Some{True{}}: Maybe<&2, Bool>},
            +r0 => +efind => +esome => Affects.holds_of(
              ~d,
              ~kern,
              l,
              view,
              from,
              b,
              tf,
              tb,
              eo,
              ef,
              eb,
              i,
              c,
              u2,
              Affects.holds_at(
                ~d,
                l,
                view,
                tf,
                tb,
                i,
                c,
                u2,
                m,
                hz,
                hy,
                enum,
                ebef,
                etk,
                d1,
                d2,
                r0,
                efind,
                esome,
                Affects.reaches_of(~d, l, view, hb, xs, er, users, eu, u2, c, b1)
              )
            )
          )(a1),
          U32.to_nat(Replicas.Tip.count(tf)),
          {==},
          ev,
          x
        )(ts)(e4)(hc)
      )(e3)
    )(e2)
  )(e)

# Affects.touches_in once the newest tip m of the branch b is known
def Affects.touches_of_in(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +b: Vend.Branch,
  m: Maybe<&2, Replicas.Tip>,
  +em: {Branch.head(~d, ~kern, l, b) == m: Maybe<&2, Replicas.Tip>},
  +eo: {Branch.other(from, b) == True{}: Bool},
  +ef: {Branch.head(~d, ~kern, l, from) == Some{tf}: Maybe<&2, Replicas.Tip>},
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Branch.touches.of(~d, l, view, from, tf, b, m) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  match m:
    case None{}:
      e => hc => Empty.absurd(
        {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
        Shared.Maybe.none_ne_some(List<&2, Touch>, ts, e)
      )
    case Some{+tb}:
      e => hc => Affects.at_in(~d, ~kern, l, view, from, tf, b, tb, eo, ef, em, ts, x)(e)(hc)

# each touch that Branch.touches gives holds
def Affects.touches_in(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +b: Vend.Branch,
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Branch.touches(~d, ~kern, l, view, from, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  e => +hc => Affects.when_is(
    Maybe<&2, List<&2, Touch>>,
    {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
    Branch.other(from, b),
    u => Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, Touch>,
      Branch.head(~d, ~kern, l, from),
      tf => Branch.touches.of(~d, l, view, from, tf, b, Branch.head(~d, ~kern, l, b))
    ),
    u => Some{[]},
    Some{ts},
    +eo => e1 => Affects.bind_some(
      Replicas.Tip,
      List<&2, Touch>,
      {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
      Branch.head(~d, ~kern, l, from),
      tf => Branch.touches.of(~d, l, view, from, tf, b, Branch.head(~d, ~kern, l, b)),
      ts,
      +tf => +ef => e2 => Affects.touches_of_in(~d, ~kern, l, view, from, tf, b, Branch.head(~d, ~kern, l, b), {==}, eo, ef, ts, x)(e2)(hc)
    )(e1),
    eo2 => e3 => Affects.none_in(y => {Touch.holds(~d, ~kern, l, view, y) == Some{True{}}: Maybe<&2, Bool>}, ts, x, e3)(hc)
  )(e)

# each touch that Branches.touch gives holds
def Affects.branches_in(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  es: List<&2, BranchEntry>,
  +b: Vend.Branch,
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Branches.touch(~d, ~kern, l, view, es, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  match es:
    case Nil{}:
      e => hc => Affects.none_in(y => {Touch.holds(~d, ~kern, l, view, y) == Some{True{}}: Maybe<&2, Bool>}, ts, x, e)(hc)
    case Con{BranchEntry{+from, os, hd}, +rest}:
      e => +hc => Affects.bind_some(
        List<&2, Touch>,
        List<&2, Touch>,
        {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
        Branch.touches(~d, ~kern, l, view, from, b),
        a => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, a, r),
          Branches.touch(~d, ~kern, l, view, rest, b)
        ),
        ts,
        +a => +ea => e2 => Affects.map_some(
          List<&2, Touch>,
          List<&2, Touch>,
          {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
          r => List.append(&2, Touch, a, r),
          Branches.touch(~d, ~kern, l, view, rest, b),
          ts,
          +r => +er => +eapp => Affects.app_in(
            Unit,
            y => {Touch.holds(~d, ~kern, l, view, y) == Some{True{}}: Maybe<&2, Bool>},
            a,
            r,
            x,
            Unit{},
            z => ha => Affects.touches_in(~d, ~kern, l, view, from, b, a, x)(ea)(ha),
            z => hr => Affects.branches_in(~d, ~kern, l, view, rest, b, r, x)(er)(hr)
          )(
            Affects.cast(
              List<&2, Touch>,
              z => {List.contains(~Touch, ~Touch.is_eq, z, x) == True{}: Bool},
              ts,
              List.append(&2, Touch, a, r),
              Equal.sym(List<&2, Touch>, List.append(&2, Touch, a, r), ts, eapp),
              hc
            )
          )
        )(e2)
      )(e)

# Node.affects_holds, with its binders reusable
def Affects.holds_law(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  b: Vend.Branch,
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Node.affects(~d, ~kern, l, view, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  match b:
    case Vend.Branch{+st, +n}:
      e => +hc => Affects.bind_some(
        List<&2, BranchEntry>,
        List<&2, Touch>,
        {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
        Node.branches(~d, ~kern, l, st),
        es => Branches.touch(~d, ~kern, l, view, es, Vend.Branch{st, n}),
        ts,
        +es => ees => e2 => Affects.branches_in(~d, ~kern, l, view, es, Vend.Branch{st, n}, ts, x)(e2)(hc)
      )(e)

# a list that holds x holds it with one more value h before it, if kept
def Affects.put_keep(+h: Touch, +r: List<&2, Touch>, cnd: Bool, +x: Touch) -> {
  List.contains(~Touch, ~Touch.is_eq, r, x) == True{}: Bool
} -> {List.contains(~Touch, ~Touch.is_eq, List.filter.put(Touch, h, r, cnd), x) == True{}: Bool}:
  match cnd:
    case True{}:
      e => Shared.List.contains_cons(~Touch, ~Touch.is_eq, h, r, x)(e)
    case False{}:
      e => e

# Affects.of_has once it is known whether the head u1 of used is u (q)
def Affects.of_has.at(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  +u1: Resources.Name,
  +rest: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit),
  +u: Resources.Name,
  q: Bool,
  eq: {Resources.Name.is_eq(u1, u) == q: Bool},
  +ein: {List.any.if(w => List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, u), q) == True{}: Bool},
  +econd: {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)) == True{}: Bool},
  ih: {List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, u) == True{}: Bool}
    -> {List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, rest, reach), Touch{from, v, c, b, u}) == True{}: Bool}
) -> {
  List.contains(
    ~Touch,
    ~Touch.is_eq,
    List.filter.put(
      Touch,
      Touch{from, v, c, b, u1},
      Touches.of(from, v, c, b, rest, reach),
      List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u1)), Resources.Name.is_eq(u1, c))
    ),
    Touch{from, v, c, b, u}
  )
    == True{}: Bool
}:
  match q:
    case True{}:
      Affects.cast(
        Resources.Name,
        z => {
          List.contains(
            ~Touch,
            ~Touch.is_eq,
            List.filter.put(
              Touch,
              Touch{from, v, c, b, z},
              Touches.of(from, v, c, b, rest, reach),
              List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(z)), Resources.Name.is_eq(z, c))
            ),
            Touch{from, v, c, b, u}
          )
            == True{}: Bool
        },
        u,
        u1,
        Equal.sym(Resources.Name, u1, u, Resources.Name.is_eq_sound(u1, u)(eq)),
        Affects.cast(
          Bool,
          z => {
            List.contains(
              ~Touch,
              ~Touch.is_eq,
              List.filter.put(Touch, Touch{from, v, c, b, u}, Touches.of(from, v, c, b, rest, reach), z),
              Touch{from, v, c, b, u}
            )
              == True{}: Bool
          },
          True{},
          List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)),
          Equal.sym(
            Bool,
            List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)),
            True{},
            econd
          ),
          Affects.contains_head(~Touch, ~Touch.is_eq, ~Affects.touch_laws(), Touch{from, v, c, b, u}, Touches.of(from, v, c, b, rest, reach))
        )
      )
    case False{}:
      Affects.put_keep(
        Touch{from, v, c, b, u1},
        Touches.of(from, v, c, b, rest, reach),
        List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u1)), Resources.Name.is_eq(u1, c)),
        Touch{from, v, c, b, u}
      )(ih(ein))

# Touches.of gives a touch of each resource of used that is c or that the
# set reach holds
def Affects.of_has(
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Vend.Branch,
  used: List<&2, Resources.Name>,
  +reach: Crits.Dict(Unit),
  +u: Resources.Name,
  +ein: {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u) == True{}: Bool},
  +econd: {List.any.if(w => Crits.Dict.has(Unit, reach, Name.key(u)), Resources.Name.is_eq(u, c)) == True{}: Bool}
) -> {List.contains(~Touch, ~Touch.is_eq, Touches.of(from, v, c, b, used, reach), Touch{from, v, c, b, u}) == True{}: Bool}:
  match used:
    case Nil{}:
      Empty.absurd(
        {List.contains(~Touch, ~Touch.is_eq, [], Touch{from, v, c, b, u}) == True{}: Bool},
        Shared.Bool.false_ne_true(ein)
      )
    case Con{+u1, +rest}:
      Affects.of_has.at(
        from,
        v,
        c,
        b,
        u1,
        rest,
        reach,
        u,
        Resources.Name.is_eq(u1, u),
        {==},
        ein,
        econd,
        h2 => Affects.of_has(from, v, c, b, rest, reach, u, h2, econd)
      )

# the first test of Touches.each is True for a resource that the version
# wrote and that b does not hold as it gave it
def Affects.inner_true(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +hb: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +d1: {Res.differs(~d, l, h, h0, c) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, h, hb, c) == Some{True{}}: Maybe<&2, Bool>}
) -> {
  Maybe.bind(
    &2,
    Bool,
    Bool,
    Res.differs(~d, l, h, h0, c),
    w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
  )
    == Some{True{}}: Maybe<&2, Bool>
}:
  %Equal.sym(Maybe<&2, Bool>, Res.differs(~d, l, h, h0, c), Some{True{}}, d1): {
    Maybe.bind(
      &2,
      Bool,
      Bool,
      _,
      w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
  d2

# Affects.each_has once it is known whether the head c1 of changed is c (q)
def Affects.each_has.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c1: Resources.Name,
  +rest: List<&2, Resources.Name>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  +c: Resources.Name,
  +u: Resources.Name,
  q: Bool,
  eq: {Resources.Name.is_eq(c1, c) == q: Bool},
  +hin: {List.any.if(w => List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, c), q) == True{}: Bool},
  +d1: {Res.differs(~d, l, h, h0, c) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, h, hb, c) == Some{True{}}: Maybe<&2, Bool>},
  +ein: {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u) == True{}: Bool},
  +econd: {
    List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(c)), Name.key(u)), Resources.Name.is_eq(u, c))
      == True{}: Bool
  },
  +touched: Bool,
  +et: {
    Maybe.bind(
      &2,
      Bool,
      Bool,
      Res.differs(~d, l, h, h0, c1),
      w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c1), u => Some{False{}})
    )
      == Some{touched}: Maybe<&2, Bool>
  },
  +r: List<&2, Touch>,
  ih: {List.contains(~Resources.Name, ~Resources.Name.is_eq, rest, c) == True{}: Bool}
    -> {List.contains(~Touch, ~Touch.is_eq, r, Touch{from, v, c, b, u}) == True{}: Bool}
) -> {
  List.contains(
    ~Touch,
    ~Touch.is_eq,
    List.append(&2, Touch, Touches.when(touched, from, v, c1, b, used, users), r),
    Touch{from, v, c, b, u}
  )
    == True{}: Bool
}:
  match q:
    case True{}:
      +ec = Resources.Name.is_eq_sound(c1, c)(eq)
      +tt = Shared.Maybe.some_inj(
        Bool,
        touched,
        True{},
        Equal.trans(
          Maybe<&2, Bool>,
          Some{touched},
          Maybe.bind(
            &2,
            Bool,
            Bool,
            Res.differs(~d, l, h, h0, c),
            w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
          ),
          Some{True{}},
          Equal.sym(
            Maybe<&2, Bool>,
            Maybe.bind(
              &2,
              Bool,
              Bool,
              Res.differs(~d, l, h, h0, c),
              w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c), u => Some{False{}})
            ),
            Some{touched},
            Affects.cast(
              Resources.Name,
              z => {
                Maybe.bind(
                  &2,
                  Bool,
                  Bool,
                  Res.differs(~d, l, h, h0, z),
                  w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, z), u => Some{False{}})
                )
                  == Some{touched}: Maybe<&2, Bool>
              },
              c1,
              c,
              ec,
              et
            )
          ),
          Affects.inner_true(~d, l, h0, h, hb, c, d1, d2)
        )
      )
      Shared.List.contains_left(
        ~Touch,
        ~Touch.is_eq,
        Touches.when(touched, from, v, c1, b, used, users),
        r,
        Touch{from, v, c, b, u},
        Affects.cast(
          Resources.Name,
          z => {
            List.contains(~Touch, ~Touch.is_eq, Touches.when(touched, from, v, z, b, used, users), Touch{from, v, c, b, u})
              == True{}: Bool
          },
          c,
          c1,
          Equal.sym(Resources.Name, c1, c, ec),
          Affects.cast(
            Bool,
            z => {
              List.contains(~Touch, ~Touch.is_eq, Touches.when(z, from, v, c, b, used, users), Touch{from, v, c, b, u})
                == True{}: Bool
            },
            True{},
            touched,
            Equal.sym(Bool, touched, True{}, tt),
            Affects.of_has(from, v, c, b, used, Reaches.Graph.reach(users, Name.key(c)), u, ein, econd)
          )
        )
      )
    case False{}:
      Shared.List.contains_right(
        ~Touch,
        ~Touch.is_eq,
        Touches.when(touched, from, v, c1, b, used, users),
        r,
        Touch{from, v, c, b, u},
        ih(hin)
      )

# Touches.each gives each touch of a resource of changed that the version
# wrote and that b does not hold as it gave it
def Affects.each_has(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  +c: Resources.Name,
  +u: Resources.Name,
  +hin: {List.contains(~Resources.Name, ~Resources.Name.is_eq, changed, c) == True{}: Bool},
  +d1: {Res.differs(~d, l, h, h0, c) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, h, hb, c) == Some{True{}}: Maybe<&2, Bool>},
  +ein: {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u) == True{}: Bool},
  +econd: {
    List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(c)), Name.key(u)), Resources.Name.is_eq(u, c))
      == True{}: Bool
  },
  +ts: List<&2, Touch>
) -> {Touches.each(~d, l, from, v, h0, h, changed, b, hb, used, users) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool}:
  match changed:
    case Nil{}:
      ea => Empty.absurd(
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
        Shared.Bool.false_ne_true(hin)
      )
    case Con{+c1, +rest}:
      ea => Affects.bind_some(
        Bool,
        List<&2, Touch>,
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
        Maybe.bind(
          &2,
          Bool,
          Bool,
          Res.differs(~d, l, h, h0, c1),
          w => Shared.Bool.when(Maybe<&2, Bool>, w, u => Res.differs(~d, l, h, hb, c1), u => Some{False{}})
        ),
        touched => Maybe.map(
          &2,
          List<&2, Touch>,
          List<&2, Touch>,
          r => List.append(&2, Touch, Touches.when(touched, from, v, c1, b, used, users), r),
          Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users)
        ),
        ts,
        +touched => +et => e2 => Affects.map_some(
          List<&2, Touch>,
          List<&2, Touch>,
          {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
          r => List.append(&2, Touch, Touches.when(touched, from, v, c1, b, used, users), r),
          Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users),
          ts,
          +r => +er => +eapp => Affects.cast(
            List<&2, Touch>,
            z => {List.contains(~Touch, ~Touch.is_eq, z, Touch{from, v, c, b, u}) == True{}: Bool},
            List.append(&2, Touch, Touches.when(touched, from, v, c1, b, used, users), r),
            ts,
            eapp,
            Affects.each_has.at(
              ~d,
              l,
              from,
              v,
              h0,
              h,
              c1,
              rest,
              b,
              hb,
              used,
              users,
              c,
              u,
              Resources.Name.is_eq(c1, c),
              {==},
              hin,
              d1,
              d2,
              ein,
              econd,
              touched,
              et,
              r,
              h2 => Affects.each_has(~d, l, from, v, h0, h, rest, b, hb, used, users, c, u, h2, d1, d2, ein, econd, r)(er)
            )
          )
        )(e2)
      )(ea)

# Affects.step_le once it is known whether n is below m as a Nat (b)
def Affects.step_le.at(
  +n: U32,
  +m: U32,
  b: Bool,
  eb: {Nat.is_le(1n+U32.to_nat(n), U32.to_nat(m)) == b: Bool},
  +ele: {Nat.is_le(U32.to_nat(n), U32.to_nat(m)) == True{}: Bool},
  +eq: {U32.is_eq(m, n) == False{}: Bool}
) -> {b == True{}: Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            U32.is_eq(m, n),
            True{},
            Equal.sym(Bool, U32.is_eq(m, n), False{}, eq),
            Equal.trans(
              Bool,
              U32.is_eq(m, n),
              Nat.is_eq(U32.to_nat(m), U32.to_nat(n)),
              True{},
              Equal.cong(Cmp, Bool, Cmp.is_eq, U32.cmp(m, n), Nat.cmp(U32.to_nat(m), U32.to_nat(n)), Shared.U32.cmp_to_nat(m, n)),
              Affects.cast(
                Nat,
                z => {Nat.is_eq(U32.to_nat(m), z) == True{}: Bool},
                U32.to_nat(m),
                U32.to_nat(n),
                Equal.sym(Nat, U32.to_nat(n), U32.to_nat(m), Shared.Nat.le_nlt_eq(U32.to_nat(n), U32.to_nat(m))(ele)(eb)),
                Shared.Nat.is_eq_refl(U32.to_nat(m))
              )
            )
          )
        )
      )

# a number at most m that is not m is below m
def Affects.step_le(
  +n: U32,
  +m: U32,
  +ele: {Nat.is_le(U32.to_nat(n), U32.to_nat(m)) == True{}: Bool},
  +eq: {U32.is_eq(m, n) == False{}: Bool}
) -> {Nat.is_le(1n+U32.to_nat(n), U32.to_nat(m)) == True{}: Bool}:
  Equal.trans(
    Bool,
    Nat.is_le(1n+U32.to_nat(n), U32.to_nat(m)),
    Nat.is_le(1n+U32.to_nat(n), U32.to_nat(m)),
    True{},
    {==},
    Affects.step_le.at(n, m, Nat.is_le(1n+U32.to_nat(n), U32.to_nat(m)), {==}, ele, eq)
  )

# a read of a version that is some taken request gives no empty listing
def Affects.con_nil(
  m: Maybe<&2, Maybe<&2, Replicas.Taken>>,
  rest: Unit -> Maybe<&2, List<&2, Replicas.Taken>>
) -> {Replicas.Taken.con(m, rest) == Some{[]}: Maybe<&2, List<&2, Replicas.Taken>>} -> Empty:
  match m:
    case None{}:
      e => Shared.Maybe.none_ne_some(List<&2, Replicas.Taken>, [], e)
    case Some{None{}}:
      e => Shared.Maybe.none_ne_some(List<&2, Replicas.Taken>, [], e)
    case Some{Some{+x}}:
      e => Affects.map_some(
        List<&2, Replicas.Taken>,
        List<&2, Replicas.Taken>,
        Empty,
        r => x <> r,
        rest(Unit{}),
        [],
        +r0 => er0 => e0 => Affects.nil_ne_cons(Replicas.Taken, x, r0, Equal.sym(List<&2, Replicas.Taken>, x <> r0, [], e0))
      )(e)

# a listing of k versions from n holds the version m, when n is at most m,
# m is below n and k, and below the count
def Affects.versions_nil(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  k: Nat,
  +n: U32,
  +m: U32,
  +ele: {Nat.is_le(U32.to_nat(n), U32.to_nat(m)) == True{}: Bool},
  +eltk: {Nat.is_lt(U32.to_nat(m), Nat.add(U32.to_nat(n), k)) == True{}: Bool},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool}
) -> {Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, tf, n) == Some{[]}: Maybe<&2, List<&2, Replicas.Taken>>} -> Empty:
  match k:
    case 0n:
      e => Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Nat.is_lt(U32.to_nat(n), U32.to_nat(n)),
          True{},
          Equal.sym(Bool, Nat.is_lt(U32.to_nat(n), U32.to_nat(n)), False{}, Shared.Nat.lt_irrefl(U32.to_nat(n))),
          Shared.Nat.le_lt(U32.to_nat(n), U32.to_nat(m), U32.to_nat(n))(ele)(
            Affects.cast(
              Nat,
              z => {Nat.is_lt(U32.to_nat(m), z) == True{}: Bool},
              Nat.add(U32.to_nat(n), 0n),
              U32.to_nat(n),
              Shared.Nat.add_zero(U32.to_nat(n)),
              eltk
            )
          )
        )
      )
    case 1n+p:
      e => Affects.when_is(
        Maybe<&2, List<&2, Replicas.Taken>>,
        Empty,
        U32.is_lt(n, Replicas.Tip.count(tf)),
        u => Replicas.Taken.con(
          Replicas.Tip.known(
            ~Replicas.Taken,
            ~Replicas.Taken.code,
            ~Replicas.Taken.code.read,
            Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
          ),
          u2 => Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n))
        ),
        u => Some{[]},
        Some{[]},
        et => e1 => Affects.con_nil(
          Replicas.Tip.known(
            ~Replicas.Taken,
            ~Replicas.Taken.code,
            ~Replicas.Taken.code.read,
            Replicas.Tip.find(~Requests.Ask.machine(), ~d, l, tf, Replicas.Log.taken(n))
          ),
          u2 => Replicas.Tip.versions(~Requests.Ask.machine(), ~d, p, l, tf, U32.inc(n))
        )(e1),
        ef => e2 => Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            U32.is_lt(n, Replicas.Tip.count(tf)),
            True{},
            Equal.sym(Bool, U32.is_lt(n, Replicas.Tip.count(tf)), False{}, ef),
            Equal.trans(
              Bool,
              U32.is_lt(n, Replicas.Tip.count(tf)),
              Nat.is_lt(U32.to_nat(n), U32.to_nat(Replicas.Tip.count(tf))),
              True{},
              Shared.U32.is_lt_to_nat(n, Replicas.Tip.count(tf)),
              Shared.Nat.le_lt(U32.to_nat(n), U32.to_nat(m), U32.to_nat(Replicas.Tip.count(tf)))(ele)(
                Equal.trans(
                  Bool,
                  Nat.is_lt(U32.to_nat(m), U32.to_nat(Replicas.Tip.count(tf))),
                  U32.is_lt(m, Replicas.Tip.count(tf)),
                  True{},
                  Equal.sym(
                    Bool,
                    U32.is_lt(m, Replicas.Tip.count(tf)),
                    Nat.is_lt(U32.to_nat(m), U32.to_nat(Replicas.Tip.count(tf))),
                    Shared.U32.is_lt_to_nat(m, Replicas.Tip.count(tf))
                  ),
                  elt
                )
              )
            )
          )
        )
      )(e)

# Affects.all_has at the version i of the number n, once it is known whether
# n is the number m of the touch (q)
def Affects.all_has.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +i: Ledgers.Id,
  +hy: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  +p: Nat,
  +m: U32,
  +v: Ledgers.Id,
  +hX: Maybe<&2, Hashes.Hash>,
  +hz: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +u: Resources.Name,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
  +ele: {Nat.is_le(U32.to_nat(n), U32.to_nat(m)) == True{}: Bool},
  +eltk: {Nat.is_lt(U32.to_nat(m), Nat.add(U32.to_nat(n), 1n+p)) == True{}: Bool},
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +d1: {Res.differs(~d, l, hX, hz, c) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, hX, hb, c) == Some{True{}}: Maybe<&2, Bool>},
  +ein: {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u) == True{}: Bool},
  +econd: {
    List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(c)), Name.key(u)), Resources.Name.is_eq(u, c))
      == True{}: Bool
  },
  +eltn: {U32.is_lt(n, Replicas.Tip.count(tf)) == True{}: Bool},
  +etkn: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n) == Some{Replicas.Taken{i, hy}}: Maybe<&2, Replicas.Taken>},
  +eb: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n) == Some{h0}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +ks: List<&2, List<&2, U32>>,
  +eks: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, hy) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +m2: U32,
  +enum2: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i) == Some{m2}: Maybe<&2, U32>},
  +a: List<&2, Touch>,
  +ewa: {
    Shared.Bool.when(
      Maybe<&2, List<&2, Touch>>,
      U32.is_eq(m2, n),
      w => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
      w => Some{[]}
    )
      == Some{a}: Maybe<&2, List<&2, Touch>>
  },
  +r: List<&2, Touch>,
  q: Bool,
  eq: {U32.is_eq(m, n) == q: Bool},
  ih: {Nat.is_le(U32.to_nat(U32.inc(n)), U32.to_nat(m)) == True{}: Bool}
    -> {Nat.is_lt(U32.to_nat(m), Nat.add(U32.to_nat(U32.inc(n)), p)) == True{}: Bool}
    -> {List.contains(~Touch, ~Touch.is_eq, r, Touch{from, v, c, b, u}) == True{}: Bool}
) -> {List.contains(~Touch, ~Touch.is_eq, List.append(&2, Touch, a, r), Touch{from, v, c, b, u}) == True{}: Bool}:
  match q:
    case True{}:
      +emn = Shared.U32.is_eq_sound(m, n)(eq)
      +ex = Shared.Maybe.some_inj(
        Replicas.Taken,
        Replicas.Taken{i, hy},
        Replicas.Taken{v, hX},
        Equal.trans(
          Maybe<&2, Replicas.Taken>,
          Some{Replicas.Taken{i, hy}},
          Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n),
          Some{Replicas.Taken{v, hX}},
          Equal.sym(Maybe<&2, Replicas.Taken>, Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, n), Some{Replicas.Taken{i, hy}}, etkn),
          Affects.cast(
            U32,
            z => {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, z) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
            m,
            n,
            emn,
            etk
          )
        )
      )
      +eiv = Equal.cong(Replicas.Taken, Ledgers.Id, Replicas.Taken.id, Replicas.Taken{i, hy}, Replicas.Taken{v, hX}, ex)
      +ehy = Equal.cong(Replicas.Taken, Maybe<&2, Hashes.Hash>, Replicas.Taken.root, Replicas.Taken{i, hy}, Replicas.Taken{v, hX}, ex)
      +em2 = Shared.Maybe.some_inj(
        U32,
        m2,
        m,
        Equal.trans(
          Maybe<&2, U32>,
          Some{m2},
          Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
          Some{m},
          Equal.sym(Maybe<&2, U32>, Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i), Some{m2}, enum2),
          Affects.cast(
            Ledgers.Id,
            z => {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, z) == Some{m}: Maybe<&2, U32>},
            v,
            i,
            Equal.sym(Ledgers.Id, i, v, eiv),
            enum
          )
        )
      )
      +eh0 = Shared.Maybe.some_inj(
        Maybe<&2, Hashes.Hash>,
        h0,
        hz,
        Equal.trans(
          Maybe<&2, Maybe<&2, Hashes.Hash>>,
          Some{h0},
          Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n),
          Some{hz},
          Equal.sym(Maybe<&2, Maybe<&2, Hashes.Hash>>, Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n), Some{h0}, eb),
          Affects.cast(
            U32,
            z => {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, z) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
            m,
            n,
            emn,
            ebef
          )
        )
      )
      +d1y = Affects.cast(
        Maybe<&2, Hashes.Hash>,
        z => {Res.differs(~d, l, hy, z, c) == Some{True{}}: Maybe<&2, Bool>},
        hz,
        h0,
        Equal.sym(Maybe<&2, Hashes.Hash>, h0, hz, eh0),
        Affects.cast(
          Maybe<&2, Hashes.Hash>,
          z => {Res.differs(~d, l, z, hz, c) == Some{True{}}: Maybe<&2, Bool>},
          hX,
          hy,
          Equal.sym(Maybe<&2, Hashes.Hash>, hy, hX, ehy),
          d1
        )
      )
      +d2y = Affects.cast(
        Maybe<&2, Hashes.Hash>,
        z => {Res.differs(~d, l, z, hb, c) == Some{True{}}: Maybe<&2, Bool>},
        hX,
        hy,
        Equal.sym(Maybe<&2, Hashes.Hash>, hy, hX, ehy),
        d2
      )
      +ewa2 = Affects.cast(
        Bool,
        z => {
          Shared.Bool.when(
            Maybe<&2, List<&2, Touch>>,
            z,
            w => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
            w => Some{[]}
          )
            == Some{a}: Maybe<&2, List<&2, Touch>>
        },
        U32.is_eq(m2, n),
        True{},
        Affects.cast(
          U32,
          z => {U32.is_eq(z, n) == True{}: Bool},
          n,
          m2,
          Equal.sym(U32, m2, n, Equal.trans(U32, m2, m, n, em2, emn)),
          Shared.U32.is_eq_refl(n)
        ),
        ewa
      )
      Shared.List.contains_left(
        ~Touch,
        ~Touch.is_eq,
        a,
        r,
        Touch{from, v, c, b, u},
        Affects.cast(
          Ledgers.Id,
          z => {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, z, c, b, u}) == True{}: Bool},
          i,
          v,
          eiv,
          Affects.each_has(
            ~d,
            l,
            from,
            i,
            h0,
            hy,
            Keys.names(ks),
            b,
            hb,
            used,
            users,
            c,
            u,
            Affects.diff_names(~d, l, h0, hy, ks, eks, c)(d1y),
            d1y,
            d2y,
            ein,
            econd,
            a
          )(ewa2)
        )
      )
    case False{}:
      +inc = Affects.inc_nat(n, Replicas.Tip.count(tf))(eltn)
      Shared.List.contains_right(
        ~Touch,
        ~Touch.is_eq,
        a,
        r,
        Touch{from, v, c, b, u},
        ih(
          Affects.cast(
            Nat,
            z => {Nat.is_le(z, U32.to_nat(m)) == True{}: Bool},
            1n+U32.to_nat(n),
            U32.to_nat(U32.inc(n)),
            Equal.sym(Nat, U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), inc),
            Affects.step_le(n, m, ele, eq)
          )
        )(
          Affects.cast(
            Nat,
            z => {Nat.is_lt(U32.to_nat(m), Nat.add(z, p)) == True{}: Bool},
            1n+U32.to_nat(n),
            U32.to_nat(U32.inc(n)),
            Equal.sym(Nat, U32.to_nat(U32.inc(n)), 1n+U32.to_nat(n), inc),
            Affects.cast(
              Nat,
              z => {Nat.is_lt(U32.to_nat(m), z) == True{}: Bool},
              Nat.add(U32.to_nat(n), 1n+p),
              1n+Nat.add(U32.to_nat(n), p),
              Shared.Nat.add_succ(U32.to_nat(n), p),
              eltk
            )
          )
        )
      )

# Touches.all gives each touch of the version m of the listing, when m is
# from n on and within k versions of n
def Affects.all_has(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Vend.Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph,
  k: Nat,
  +ev: {Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, tf, n) == Some{xs}: Maybe<&2, List<&2, Replicas.Taken>>},
  +eb: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, n) == Some{h0}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +m: U32,
  +v: Ledgers.Id,
  +hX: Maybe<&2, Hashes.Hash>,
  +hz: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +u: Resources.Name,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +ele: {Nat.is_le(U32.to_nat(n), U32.to_nat(m)) == True{}: Bool},
  +eltk: {Nat.is_lt(U32.to_nat(m), Nat.add(U32.to_nat(n), k)) == True{}: Bool},
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +d1: {Res.differs(~d, l, hX, hz, c) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, hX, hb, c) == Some{True{}}: Maybe<&2, Bool>},
  +ein: {List.contains(~Resources.Name, ~Resources.Name.is_eq, used, u) == True{}: Bool},
  +econd: {
    List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(c)), Name.key(u)), Resources.Name.is_eq(u, c))
      == True{}: Bool
  },
  +ts: List<&2, Touch>
) -> {Touches.all(~d, l, from, tf, xs, n, h0, b, hb, used, users) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool}:
  match xs k:
    case Nil{} j:
      ea => Empty.absurd(
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
        Affects.versions_nil(~d, l, tf, j, n, m, ele, eltk, elt)(ev)
      )
    case Con{Replicas.Taken{+i, +hy}, +rest} 0n:
      ea => Empty.absurd(
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
        Affects.nil_ne_cons(
          Replicas.Taken,
          Replicas.Taken{i, hy},
          rest,
          Shared.Maybe.some_inj(List<&2, Replicas.Taken>, [], Replicas.Taken{i, hy} <> rest, ev)
        )
      )
    case Con{Replicas.Taken{+i, +hy}, +rest} 1n+(+p):
      ea => Affects.versions_cons(
        ~d,
        l,
        tf,
        p,
        n,
        Replicas.Taken{i, hy},
        rest,
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
        +eltn => +etkn => +evr => Affects.bind_some(
          List<&2, List<&2, U32>>,
          List<&2, Touch>,
          {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, hy),
          ks => Maybe.bind(
            &2,
            U32,
            List<&2, Touch>,
            Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
            m2 => Maybe.bind(
              &2,
              List<&2, Touch>,
              List<&2, Touch>,
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m2, n),
                w => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                w => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              )
            )
          ),
          ts,
          +ks => +eks => e1 => Affects.bind_some(
            U32,
            List<&2, Touch>,
            {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
            Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, i),
            m2 => Maybe.bind(
              &2,
              List<&2, Touch>,
              List<&2, Touch>,
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m2, n),
                w => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                w => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              )
            ),
            ts,
            +m2 => +enum2 => e2 => Affects.bind_some(
              List<&2, Touch>,
              List<&2, Touch>,
              {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
              Shared.Bool.when(
                Maybe<&2, List<&2, Touch>>,
                U32.is_eq(m2, n),
                w => Touches.each(~d, l, from, i, h0, hy, Keys.names(ks), b, hb, used, users),
                w => Some{[]}
              ),
              a => Maybe.map(
                &2,
                List<&2, Touch>,
                List<&2, Touch>,
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users)
              ),
              ts,
              +a => +ewa => e3 => Affects.map_some(
                List<&2, Touch>,
                List<&2, Touch>,
                {List.contains(~Touch, ~Touch.is_eq, ts, Touch{from, v, c, b, u}) == True{}: Bool},
                r => List.append(&2, Touch, a, r),
                Touches.all(~d, l, from, tf, rest, U32.inc(n), hy, b, hb, used, users),
                ts,
                +r => +er => +eapp => Affects.cast(
                  List<&2, Touch>,
                  z => {List.contains(~Touch, ~Touch.is_eq, z, Touch{from, v, c, b, u}) == True{}: Bool},
                  List.append(&2, Touch, a, r),
                  ts,
                  eapp,
                  Affects.all_has.at(
                    ~d,
                    l,
                    from,
                    tf,
                    i,
                    hy,
                    n,
                    h0,
                    b,
                    hb,
                    used,
                    users,
                    p,
                    m,
                    v,
                    hX,
                    hz,
                    c,
                    u,
                    enum,
                    etk,
                    ele,
                    eltk,
                    ebef,
                    d1,
                    d2,
                    ein,
                    econd,
                    eltn,
                    etkn,
                    eb,
                    ks,
                    eks,
                    m2,
                    enum2,
                    a,
                    ewa,
                    r,
                    U32.is_eq(m, n),
                    {==},
                    ele2 => eltk2 => Affects.all_has(
                      ~d,
                      l,
                      from,
                      tf,
                      rest,
                      U32.inc(n),
                      hy,
                      b,
                      hb,
                      used,
                      users,
                      p,
                      evr,
                      Affects.before_next(~d, l, tf, n, Replicas.Taken{i, hy}, eltn, etkn),
                      m,
                      v,
                      hX,
                      hz,
                      c,
                      u,
                      enum,
                      etk,
                      elt,
                      ele2,
                      eltk2,
                      ebef,
                      d1,
                      d2,
                      ein,
                      econd,
                      r
                    )(er)
                  )
                )
              )(e3)
            )(e2)
          )(e1)
        )(ea)
      )(ev)

# what a touch that holds reads, at the tips tf and tb: the number m of its
# version, below the count; the trees hz before it and hX after it, which
# differ at the resource changed, and of which tb holds something else there;
# and the resource used of tb, that is changed or uses it
def Affects.AtFacts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type
) -> Type:
  @m: U32 -> {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>}
    -> {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool}
    -> @hz: Maybe<&2, Hashes.Hash> -> {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>}
    -> @hX: Maybe<&2, Hashes.Hash> -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>}
    -> {Res.differs(~d, l, hX, hz, changed) == Some{True{}}: Maybe<&2, Bool>}
    -> {Res.differs(~d, l, hX, Replicas.Tip.content(tb), changed) == Some{True{}}: Maybe<&2, Bool>}
    -> @r0: Requests.Res -> {Vend.Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed) == Some{True{}}: Maybe<&2, Bool>}
    -> R

# a choice that gives some y: the test holds, and its choice gives y
def Affects.when_facts(
  q: Bool,
  -B: Data,
  -kk: Unit -> Maybe<&2, B>,
  -y: B,
  -R: Type,
  k: {q == True{}: Bool} -> {kk(Unit{}) == Some{y}: Maybe<&2, B>} -> R
) -> {Shared.Maybe.when(B, q, kk) == Some{y}: Maybe<&2, B>} -> R:
  match q:
    case True{}:
      h => k({==})(h)
    case False{}:
      h => Empty.absurd(R, Shared.Maybe.none_ne_some(B, y, h))

# Affects.number_facts once the outcome o of the request is known
def Affects.number_facts.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +v: Ledgers.Id,
  +m: U32,
  o: Replicas.Out,
  -R: Type,
  k: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool}
    -> {Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), v) == True{}: Bool} -> R
) -> {Replicas.Out.number(~Requests.Ask.machine(), ~d, l, tf, v, o) == Some{m}: Maybe<&2, U32>} -> R:
  match o:
    case Replicas.Out.Stale{a}:
      e => Empty.absurd(R, Shared.Maybe.none_ne_some(U32, m, e))
    case Replicas.Out.Taken{a, +m1}:
      e => Affects.when_facts(
        Bool.and(U32.is_lt(m1, Replicas.Tip.count(tf)), Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m1), v)),
        U32,
        u => Some{m1},
        m,
        R,
        +eb => +e2 => k(
          Affects.cast(
            U32,
            z => {U32.is_lt(z, Replicas.Tip.count(tf)) == True{}: Bool},
            m1,
            m,
            Shared.Maybe.some_inj(U32, m1, m, e2),
            Shared.Bool.and_true_left(
              U32.is_lt(m1, Replicas.Tip.count(tf)),
              Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m1), v)
            )(eb)
          )
        )(
          Affects.cast(
            U32,
            z => {Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, z), v) == True{}: Bool},
            m1,
            m,
            Shared.Maybe.some_inj(U32, m1, m, e2),
            Shared.Bool.and_true_right(
              U32.is_lt(m1, Replicas.Tip.count(tf)),
              Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m1), v)
            )(eb)
          )
        )
      )(e)

# the number m of the request v at the tip tf is below the count, and the
# request taken there is v
def Affects.number_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +v: Ledgers.Id,
  +m: U32,
  -R: Type,
  k: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool}
    -> {Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), v) == True{}: Bool} -> R
) -> {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>} -> R:
  e => Affects.bind_some(
    Replicas.Out,
    U32,
    R,
    Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, tf, v),
    o => Replicas.Out.number(~Requests.Ask.machine(), ~d, l, tf, v, o),
    m,
    +o => eo => e2 => Affects.number_facts.at(~d, l, tf, v, m, o, R, k)(e2)
  )(e)

# the version m wrote the resource changed: the trees before and after it
def Affects.wrote_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +tf: Replicas.Tip,
  +m: U32,
  +changed: Resources.Name,
  -R: Type,
  k: @hz: Maybe<&2, Hashes.Hash> -> {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>}
    -> @x0: Replicas.Taken -> {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{x0}: Maybe<&2, Replicas.Taken>}
    -> {Res.differs(~d, l, Replicas.Taken.root(x0), hz, changed) == Some{True{}}: Maybe<&2, Bool>} -> R
) -> {Version.wrote(~d, l, tf, m, changed) == Some{True{}}: Maybe<&2, Bool>} -> R:
  e => Affects.bind_some(
    Maybe<&2, Hashes.Hash>,
    Bool,
    R,
    Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m),
    h0 => Maybe.bind(
      &2,
      Replicas.Taken,
      Bool,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m),
      x => Res.differs(~d, l, Replicas.Taken.root(x), h0, changed)
    ),
    True{},
    +hz => +ebef => e2 => Affects.bind_some(
      Replicas.Taken,
      Bool,
      R,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m),
      x => Res.differs(~d, l, Replicas.Taken.root(x), hz, changed),
      True{},
      +x0 => +etk0 => e3 => k(hz)(ebef)(x0)(etk0)(e3)
    )(e2)
  )(e)

# Affects.at_facts once the resource r that tb holds at used is known
def Affects.at_facts.find(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type,
  k: Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R),
  +m: U32,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +hz: Maybe<&2, Hashes.Hash>,
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +hX: Maybe<&2, Hashes.Hash>,
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
  +d1: {Res.differs(~d, l, hX, hz, changed) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, hX, Replicas.Tip.content(tb), changed) == Some{True{}}: Maybe<&2, Bool>},
  r: Maybe<&2, Requests.Res>,
  +efind: {Vend.Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}
) -> {Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  match r:
    case None{}:
      e => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e)))
    case Some{+r0}:
      e => k(m)(enum)(elt)(hz)(ebef)(hX)(etk)(d1)(d2)(r0)(efind)(e)

# Affects.at_facts once the test whether tb holds something else is known
def Affects.at_facts.dif(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type,
  k: Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R),
  +m: U32,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +hz: Maybe<&2, Hashes.Hash>,
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +hX: Maybe<&2, Hashes.Hash>,
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
  +d1: {Res.differs(~d, l, hX, hz, changed) == Some{True{}}: Maybe<&2, Bool>},
  dv: Bool,
  +ed: {Res.differs(~d, l, hX, Replicas.Tip.content(tb), changed) == Some{dv}: Maybe<&2, Bool>}
) -> {Shared.Bool.when(Maybe<&2, Bool>, dv, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  match dv:
    case False{}:
      e => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e)))
    case True{}:
      e => Affects.bind_some(
        Maybe<&2, Requests.Res>,
        Bool,
        R,
        Vend.Res.find(~d, l, Replicas.Tip.content(tb), used),
        r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}}),
        True{},
        +r => +efind => e2 => Affects.at_facts.find(~d, l, view, tf, tb, v, changed, used, R, k, m, enum, elt, hz, ebef, hX, etk, d1, ed, r, efind)(e2)
      )(e)

# Affects.at_facts once the taken request x0 of the number m is known
def Affects.at_facts.ver(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type,
  k: Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R),
  +m: U32,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +eisof: {Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), v) == True{}: Bool},
  +hz: Maybe<&2, Hashes.Hash>,
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  x0: Replicas.Taken,
  +etk0: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{x0}: Maybe<&2, Replicas.Taken>},
  +d10: {Res.differs(~d, l, Replicas.Taken.root(x0), hz, changed) == Some{True{}}: Maybe<&2, Bool>}
) -> {
  Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}})))
    == Some{True{}}: Maybe<&2, Bool>
} -> R:
  match x0:
    case Replicas.Taken{+j, +hX}:
      +eiv = Ledgers.Id.is_eq_sound(j, v)(
        Affects.cast(
          Maybe<&2, Replicas.Taken>,
          z => {Replicas.Taken.is_of(z, v) == True{}: Bool},
          Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m),
          Some{Replicas.Taken{j, hX}},
          etk0,
          eisof
        )
      )
      +etk = Affects.cast(
        Ledgers.Id,
        z => {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{z, hX}}: Maybe<&2, Replicas.Taken>},
        j,
        v,
        eiv,
        etk0
      )
      e => Affects.bind_some(
        Maybe<&2, Hashes.Hash>,
        Bool,
        R,
        Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v),
        h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}})),
        True{},
        +hv => +ever => e3 => Affects.bind_some(
          Bool,
          Bool,
          R,
          Res.differs(~d, l, hv, Replicas.Tip.content(tb), changed),
          differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}),
          True{},
          +dv => +ed => e4 => Affects.at_facts.dif(
            ~d,
            l,
            view,
            tf,
            tb,
            v,
            changed,
            used,
            R,
            k,
            m,
            enum,
            elt,
            hz,
            ebef,
            hX,
            etk,
            d10,
            dv,
            Affects.cast(
              Maybe<&2, Hashes.Hash>,
              z => {Res.differs(~d, l, z, Replicas.Tip.content(tb), changed) == Some{dv}: Maybe<&2, Bool>},
              hv,
              hX,
              Shared.Maybe.some_inj(
                Maybe<&2, Hashes.Hash>,
                hv,
                hX,
                Equal.trans(
                  Maybe<&2, Maybe<&2, Hashes.Hash>>,
                  Some{hv},
                  Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v),
                  Some{hX},
                  Equal.sym(Maybe<&2, Maybe<&2, Hashes.Hash>>, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), Some{hv}, ever),
                  Affects.version_of(~d, l, tf, v, m, hX, enum, etk)
                )
              ),
              ed
            )
          )(e4)
        )(e3)
      )(e)

# Affects.at_facts once it is known whether the version wrote the resource (w)
def Affects.at_facts.wrote(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type,
  k: Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R),
  +m: U32,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +eisof: {Replicas.Taken.is_of(Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m), v) == True{}: Bool},
  w: Bool,
  +ew: {Version.wrote(~d, l, tf, m, changed) == Some{w}: Maybe<&2, Bool>}
) -> {Shared.Bool.when(Maybe<&2, Bool>, w, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  match w:
    case False{}:
      e => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e)))
    case True{}:
      +e => Affects.wrote_facts(
        ~d,
        l,
        tf,
        m,
        changed,
        R,
        +hz => +ebef => +x0 => +etk0 => +d10 => Affects.at_facts.ver(~d, l, view, tf, tb, v, changed, used, R, k, m, enum, elt, eisof, hz, ebef, x0, etk0, d10)(e)
      )(ew)

# what Touch.holds.at reads, when it holds
def Affects.at_facts(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +tf: Replicas.Tip,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  -R: Type,
  k: Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R)
) -> {Touch.holds.at(~d, l, view, tf, tb, v, changed, used) == Some{True{}}: Maybe<&2, Bool>} -> R:
  e => Affects.bind_some(
    U32,
    Bool,
    R,
    Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v),
    m => Maybe.bind(&2, Bool, Bool, Version.wrote(~d, l, tf, m, changed), wrote => Shared.Bool.when(Maybe<&2, Bool>, wrote, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}})),
    True{},
    +m => +enum => e1 => Affects.number_facts(
      ~d,
      l,
      tf,
      v,
      m,
      R,
      +elt => +eisof => Affects.bind_some(
        Bool,
        Bool,
        R,
        Version.wrote(~d, l, tf, m, changed),
        wrote => Shared.Bool.when(Maybe<&2, Bool>, wrote, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Vend.Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}}),
        True{},
        +w => +ew => e2 => Affects.at_facts.wrote(~d, l, view, tf, tb, v, changed, used, R, k, m, enum, elt, eisof, w, ew)(e2)
      )(e1)
    )(enum)
  )(e)

# what Touch.holds reads, when it holds
def Affects.holds_facts(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +b: Vend.Branch,
  +used: Resources.Name,
  -R: Type,
  k: {Branch.other(from, b) == True{}: Bool}
    -> @tf: Replicas.Tip -> {Branch.head(~d, ~kern, l, from) == Some{tf}: Maybe<&2, Replicas.Tip>}
    -> @tb: Replicas.Tip -> {Branch.head(~d, ~kern, l, b) == Some{tb}: Maybe<&2, Replicas.Tip>}
    -> Affects.AtFacts(~d, l, view, tf, tb, v, changed, used, R)
) -> {Touch.holds(~d, ~kern, l, view, Touch{from, v, changed, b, used}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  e => Affects.when_is(
    Maybe<&2, Bool>,
    R,
    Branch.other(from, b),
    u => Maybe.bind(
      &2,
      Replicas.Tip,
      Bool,
      Branch.head(~d, ~kern, l, from),
      tf => Maybe.bind(&2, Replicas.Tip, Bool, Branch.head(~d, ~kern, l, b), tb => Touch.holds.at(~d, l, view, tf, tb, v, changed, used))
    ),
    u => Some{False{}},
    Some{True{}},
    +eo => e1 => Affects.bind_some(
      Replicas.Tip,
      Bool,
      R,
      Branch.head(~d, ~kern, l, from),
      tf => Maybe.bind(&2, Replicas.Tip, Bool, Branch.head(~d, ~kern, l, b), tb => Touch.holds.at(~d, l, view, tf, tb, v, changed, used)),
      True{},
      +tf => +ef => e2 => Affects.bind_some(
        Replicas.Tip,
        Bool,
        R,
        Branch.head(~d, ~kern, l, b),
        tb => Touch.holds.at(~d, l, view, tf, tb, v, changed, used),
        True{},
        +tb => +eb => e3 => Affects.at_facts(~d, l, view, tf, tb, v, changed, used, R, k(eo)(tf)(ef)(tb)(eb))(e3)
      )(e2)
    )(e1),
    eof => e4 => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e4)))
  )(e)

# the graph of imports of the resources of a listing is read when their users
# graph is: it is a side
def Affects.graph_some(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  }
) -> {
  Uses.graph(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
    == Some{Affects.side(~d, l, view, hb, Res.names(xs), True{})}: Maybe<&2, Reaches.Graph>
}:
  +gr = Uses.graph(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
  +us = Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
  Affects.some_is(gr)(
    Equal.trans(
      Bool,
      Maybe.is_some(&2, Reaches.Graph, gr),
      Maybe.is_some(&2, Reaches.Graph, us),
      True{},
      Equal.sym(
        Bool,
        Maybe.is_some(&2, Reaches.Graph, us),
        Maybe.is_some(&2, Reaches.Graph, gr),
        Affects.some_fold(~d, l, view, hb, Res.names(xs), Reaches.Graph.new(), Reaches.Graph.new())
      ),
      Affects.cast(
        Maybe<&2, Reaches.Graph>,
        z => {Maybe.is_some(&2, Reaches.Graph, z) == True{}: Bool},
        Some{users},
        us,
        Equal.sym(Maybe<&2, Reaches.Graph>, us, Some{users}, eu),
        {==}
      )
    )
  )

# the search of Uses.reaches, at a tree whose listing and users graph are
# read, is the search of the graph of imports of the listing
def Affects.rest_eq(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  },
  +used: Resources.Name,
  +changed: Resources.Name
) -> {
  Maybe.bind(
    &2,
    Reaches.Graph,
    Bool,
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Reaches.Graph,
      Tree.resources(~d, l, hb),
      ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
    ),
    g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
  )
    == Some{
      Crits.Dict.has(
        Unit,
        Reaches.Graph.reach(Affects.side(~d, l, view, hb, Res.names(xs), True{}), Name.key(used)),
        Name.key(changed)
      )
    }: Maybe<&2, Bool>
}:
  +side1 = Affects.side(~d, l, view, hb, Res.names(xs), True{})
  %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, Vend.Tree.range(~d, l, hb, [0]), Some{xs}, er): {
    Maybe.bind(
      &2,
      Reaches.Graph,
      Bool,
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Reaches.Graph,
        Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Resources.Name>, Res.names, _),
        ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
      ),
      g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
    )
      == Some{Crits.Dict.has(Unit, Reaches.Graph.reach(side1, Name.key(used)), Name.key(changed))}: Maybe<&2, Bool>
  }
  %Equal.sym(
    Maybe<&2, Reaches.Graph>,
    Uses.graph(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
    Some{side1},
    Affects.graph_some(~d, l, view, hb, xs, users, eu)
  ): {
    Maybe.bind(
      &2,
      Reaches.Graph,
      Bool,
      _,
      g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
    )
      == Some{Crits.Dict.has(Unit, Reaches.Graph.reach(side1, Name.key(used)), Name.key(changed))}: Maybe<&2, Bool>
  }
  {==}

# Affects.reaches_back once it is known whether used is changed (q)
def Affects.reaches_back.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  },
  +used: Resources.Name,
  +changed: Resources.Name,
  q: Bool,
  +ereach: {
    Shared.Bool.when(
      Maybe<&2, Bool>,
      q,
      u => Some{True{}},
      u => Maybe.bind(
        &2,
        Reaches.Graph,
        Bool,
        Maybe.bind(
          &2,
          List<&2, Resources.Name>,
          Reaches.Graph,
          Tree.resources(~d, l, hb),
          ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
        ),
        g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
      )
    )
      == Some{True{}}: Maybe<&2, Bool>
  }
) -> {
  List.any.if(w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(changed)), Name.key(used)), q) == True{}: Bool
}:
  match q:
    case True{}:
      {==}
    case False{}:
      +side1 = Affects.side(~d, l, view, hb, Res.names(xs), True{})
      +has1 = Crits.Dict.has(Unit, Reaches.Graph.reach(side1, Name.key(used)), Name.key(changed))
      Affects.cast(
        Reaches.Graph,
        z => {Crits.Dict.has(Unit, Reaches.Graph.reach(z, Name.key(changed)), Name.key(used)) == True{}: Bool},
        Affects.side(~d, l, view, hb, Res.names(xs), False{}),
        users,
        Equal.cong(
          Maybe<&2, Reaches.Graph>,
          Reaches.Graph,
          z => Maybe.default(&2, Reaches.Graph, z, Reaches.Graph.new()),
          Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
          Some{users},
          eu
        ),
        Affects.reach_rev(~d, l, view, hb, Res.names(xs), True{}, Name.key(used), Name.key(changed))(
          Shared.Maybe.some_inj(
            Bool,
            has1,
            True{},
            Equal.trans(
              Maybe<&2, Bool>,
              Some{has1},
              Maybe.bind(
                &2,
                Reaches.Graph,
                Bool,
                Maybe.bind(
                  &2,
                  List<&2, Resources.Name>,
                  Reaches.Graph,
                  Tree.resources(~d, l, hb),
                  ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
                ),
                g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
              ),
              Some{True{}},
              Equal.sym(
                Maybe<&2, Bool>,
                Maybe.bind(
                  &2,
                  Reaches.Graph,
                  Bool,
                  Maybe.bind(
                    &2,
                    List<&2, Resources.Name>,
                    Reaches.Graph,
                    Tree.resources(~d, l, hb),
                    ns => Uses.graph(~d, l, view, hb, ns, Reaches.Graph.new())
                  ),
                  g => Some{Crits.Dict.has(Unit, Reaches.Graph.reach(g, Name.key(used)), Name.key(changed))}
                ),
                Some{has1},
                Affects.rest_eq(~d, l, view, hb, xs, er, users, eu, used, changed)
              ),
              ereach
            )
          )
        )
      )

# a resource of a branch that uses a changed resource is c, or the users
# graph of c finds it
def Affects.reaches_back(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Vend.Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +users: Reaches.Graph,
  +eu: {
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()) == Some{users}: Maybe<&2, Reaches.Graph>
  },
  +used: Resources.Name,
  +changed: Resources.Name,
  +ereach: {Uses.reaches(~d, l, view, hb, used, changed) == Some{True{}}: Maybe<&2, Bool>}
) -> {
  List.any.if(
    w => Crits.Dict.has(Unit, Reaches.Graph.reach(users, Name.key(changed)), Name.key(used)),
    Resources.Name.is_eq(used, changed)
  )
    == True{}: Bool
}:
  Affects.reaches_back.at(~d, l, view, hb, xs, er, users, eu, used, changed, Resources.Name.is_eq(used, changed), ereach)

# the first tip m of a line whose newest tip is known is some tip
def Affects.head_of_some(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +c: Ledgers.Line,
  m: Maybe<&2, Replicas.Tip>,
  -t: Replicas.Tip,
  -R: Type,
  k: @t0: Replicas.Tip -> {m == Some{t0}: Maybe<&2, Replicas.Tip>} -> R
) -> {Replicas.Line.head.of(~Requests.Ask.machine(), ~d, ~kern, l, c, m) == Some{t}: Maybe<&2, Replicas.Tip>} -> R:
  match m:
    case None{}:
      e => Empty.absurd(R, Shared.Maybe.none_ne_some(Replicas.Tip, t, e))
    case Some{+t0}:
      e => k(t0)({==})

# a branch whose newest tip is known has a first tip in the log of the
# newest tip of its store
def Affects.head_start(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +st: Hashes.Hash,
  +nf: String,
  +tf: Replicas.Tip,
  -R: Type,
  k: @rt: Replicas.Tip -> {Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st) == Some{rt}: Maybe<&2, Replicas.Tip>}
    -> @ws: List<&2, U32> -> {Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, rt, Replicas.Log.start(nf)) == Some{ws}: Maybe<&2, List<&2, U32>>}
    -> R
) -> {Branch.head(~d, ~kern, l, Vend.Branch{st, nf}) == Some{tf}: Maybe<&2, Replicas.Tip>} -> R:
  e => Affects.head_of_some(
    ~d,
    ~kern,
    l,
    Ledgers.Line{st, Some{nf}},
    Replicas.Line.start(~Requests.Ask.machine(), ~d, ~kern, l, Ledgers.Line{st, Some{nf}}),
    tf,
    R,
    +t0 => es => Affects.bind_some(
      Replicas.Tip,
      Replicas.Tip,
      R,
      Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st),
      t => Maybe.bind(
        &2,
        List<&2, U32>,
        Replicas.Tip,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, t, Replicas.Log.start(nf)),
        ws => Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws)
      ),
      t0,
      +rt => +ert => e2 => Affects.bind_some(
        List<&2, U32>,
        Replicas.Tip,
        R,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, rt, Replicas.Log.start(nf)),
        ws => Replicas.Tip.named(~Requests.Ask.machine(), ~d, l, ws),
        t0,
        +ws => +ews => e3 => k(rt)(ert)(ws)(ews)
      )(e2)
    )(es)
  )(e)

# a list of names that holds u holds it with one more name m before it, if any
def Affects.cons_keep_s(m: Maybe<&2, String>, +r: List<&2, String>, +u: String) -> {
  List.contains(~String, ~String.eq, r, u) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, m, r), u) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{y}:
      h => Shared.List.contains_cons(~String, ~String.eq, y, r, u)(h)

# Affects.started_of once it is known whether x is bb (c)
def Affects.started_of.at(
  +x: Trees.Binding,
  +rest: List<&2, Trees.Binding>,
  +bb: Trees.Binding,
  +nf: String,
  c: Bool,
  ec: {Trees.Binding.is_eq(x, bb) == c: Bool},
  +en: {Branch.started(bb) == Some{nf}: Maybe<&2, String>},
  ih: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, bb) == True{}: Bool}
    -> {List.contains(~String, ~String.eq, Branches.names(rest), nf) == True{}: Bool}
) -> {
  List.any.if(w => List.contains(~Trees.Binding, ~Trees.Binding.is_eq, rest, bb), c) == True{}: Bool
} -> {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Branch.started(x), Branches.names(rest)), nf) == True{}: Bool}:
  match c:
    case True{}:
      h => Affects.cast(
        Trees.Binding,
        z => {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, Branch.started(z), Branches.names(rest)), nf) == True{}: Bool},
        bb,
        x,
        Equal.sym(Trees.Binding, x, bb, Affects.binding_sound(x, bb)(ec)),
        Affects.cast(
          Maybe<&2, String>,
          z => {List.contains(~String, ~String.eq, Shared.Maybe.cons(String, z, Branches.names(rest)), nf) == True{}: Bool},
          Some{nf},
          Branch.started(bb),
          Equal.sym(Maybe<&2, String>, Branch.started(bb), Some{nf}, en),
          Affects.contains_head(~String, ~String.eq, ~Texts.String.laws(), nf, Branches.names(rest))
        )
      )
    case False{}:
      h => Affects.cons_keep_s(Branch.started(x), Branches.names(rest), nf)(ih(h))

# the branch that a binding of xs starts is among the names of xs
def Affects.started_of(
  xs: List<&2, Trees.Binding>,
  +bb: Trees.Binding,
  +nf: String,
  +en: {Branch.started(bb) == Some{nf}: Maybe<&2, String>}
) -> {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, bb) == True{}: Bool}
  -> {List.contains(~String, ~String.eq, Branches.names(xs), nf) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => Empty.absurd({List.contains(~String, ~String.eq, [], nf) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{+x, +rest}:
      h => Affects.started_of.at(x, rest, bb, nf, Trees.Binding.is_eq(x, bb), {==}, en, h2 => Affects.started_of(rest, bb, nf, en)(h2))(h)

# a branch whose first tip the log of a store holds is among its names
def Affects.started_in(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +rt: Replicas.Tip,
  +lx: List<&2, Trees.Binding>,
  +elx: {Vend.Tree.range(~d, l, Replicas.Tip.log(rt), [5]) == Some{lx}: Maybe<&2, List<&2, Trees.Binding>>},
  +nf: String,
  +ws: List<&2, U32>,
  +ews: {Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, rt, Replicas.Log.start(nf)) == Some{ws}: Maybe<&2, List<&2, U32>>}
) -> {List.contains(~String, ~String.eq, Branches.names(lx), nf) == True{}: Bool}:
  +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, Replicas.Tip.log(rt), Replicas.Log.start(nf))
  Affects.started_of(
    lx,
    Trees.Binding{Replicas.Log.start(nf), ws},
    nf,
    Codes.Code.whole_read(~String, ~Codes.Code.text, ~Codes.Code.text.read, ~(a => r => Codes.Code.text_read(a, r)), nf)
  )(
    Equal.trans(
      Bool,
      List.contains(~Trees.Binding, ~Trees.Binding.is_eq, lx, Trees.Binding{Replicas.Log.start(nf), ws}),
      Bool.and(
        Trees.Key.leads([5], Replicas.Log.start(nf)),
        Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Some{ws})
      ),
      True{},
      Affects.range_has(~d, l, Replicas.Tip.log(rt), [5], lx, elx, Replicas.Log.start(nf), ws),
      Affects.cast(
        Maybe<&2, List<&2, U32>>,
        z => {
          Bool.and(
            Trees.Key.leads([5], Replicas.Log.start(nf)),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), z, Some{ws})
          )
            == True{}: Bool
        },
        Some{ws},
        Trees.Look.value(look0),
        Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Look.value(look0), Some{ws}, ews),
        Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), ws)
      )
    )
  )

# the entry of a branch is of that branch
def Affects.entry_of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +bb: Vend.Branch,
  m: Maybe<&2, Replicas.Tip>,
  -e0: BranchEntry,
  -R: Type,
  k: @vs: List<&2, String> -> @hv: Maybe<&2, Ledgers.Id> -> {BranchEntry{bb, vs, hv} == e0: BranchEntry} -> R
) -> {BranchEntry.of(~d, l, bb, m) == Some{e0}: Maybe<&2, BranchEntry>} -> R:
  match m:
    case None{}:
      e => Empty.absurd(R, Shared.Maybe.none_ne_some(BranchEntry, e0, e))
    case Some{+t}:
      e => Affects.map_some(
        Maybe<&2, Ledgers.Id>,
        BranchEntry,
        R,
        v => BranchEntry{bb, Replicas.Tip.voters(t), v},
        Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t),
        e0,
        +hv => ehv => eq => k(Replicas.Tip.voters(t))(hv)(eq)
      )(e)

# Affects.touch_has at the entry of the branch n1, once it is known whether
# n1 is nf (q)
def Affects.touch_has.hit(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +n1: String,
  +rest: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Vend.Branch,
  +x: Touch,
  +r0: List<&2, BranchEntry>,
  q: Bool,
  eq: {String.eq(n1, nf) == q: Bool},
  +hn: {List.any.if(w => List.contains(~String, ~String.eq, rest, nf), q) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool},
  ih: {List.contains(~String, ~String.eq, rest, nf) == True{}: Bool}
    -> (
      @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
        -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool}
    )
    -> @ts2: List<&2, Touch> -> {Branches.touch(~d, ~kern, l, view, r0, b) == Some{ts2}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts2, x) == True{}: Bool},
  +a: List<&2, Touch>,
  +ea: {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, n1}, b) == Some{a}: Maybe<&2, List<&2, Touch>>},
  +r: List<&2, Touch>,
  +er: {Branches.touch(~d, ~kern, l, view, r0, b) == Some{r}: Maybe<&2, List<&2, Touch>>}
) -> {List.contains(~Touch, ~Touch.is_eq, List.append(&2, Touch, a, r), x) == True{}: Bool}:
  match q:
    case True{}:
      Shared.List.contains_left(
        ~Touch,
        ~Touch.is_eq,
        a,
        r,
        x,
        hk(a)(
          Affects.cast(
            String,
            z => {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, z}, b) == Some{a}: Maybe<&2, List<&2, Touch>>},
            n1,
            nf,
            Texts.String.eq_sound(n1, nf)(eq),
            ea
          )
        )
      )
    case False{}:
      Shared.List.contains_right(~Touch, ~Touch.is_eq, a, r, x, ih(hn)(hk)(r)(er))

# Affects.touch_has at the entry of the branch n1
def Affects.touch_has.at(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +n1: String,
  +rest: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Vend.Branch,
  +x: Touch,
  +vs: List<&2, String>,
  +hv: Maybe<&2, Ledgers.Id>,
  +r0: List<&2, BranchEntry>,
  q: Bool,
  eq: {String.eq(n1, nf) == q: Bool},
  +hn: {List.any.if(w => List.contains(~String, ~String.eq, rest, nf), q) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool},
  ih: {List.contains(~String, ~String.eq, rest, nf) == True{}: Bool}
    -> (
      @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
        -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool}
    )
    -> @ts2: List<&2, Touch> -> {Branches.touch(~d, ~kern, l, view, r0, b) == Some{ts2}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts2, x) == True{}: Bool},
  +ts: List<&2, Touch>
) -> {
  Branches.touch(~d, ~kern, l, view, BranchEntry{Vend.Branch{st, n1}, vs, hv} <> r0, b) == Some{ts}: Maybe<&2, List<&2, Touch>>
} -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}:
  e => Affects.bind_some(
    List<&2, Touch>,
    List<&2, Touch>,
    {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
    Branch.touches(~d, ~kern, l, view, Vend.Branch{st, n1}, b),
    a => Maybe.map(&2, List<&2, Touch>, List<&2, Touch>, r => List.append(&2, Touch, a, r), Branches.touch(~d, ~kern, l, view, r0, b)),
    ts,
    +a => +ea => e2 => Affects.map_some(
      List<&2, Touch>,
      List<&2, Touch>,
      {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
      r => List.append(&2, Touch, a, r),
      Branches.touch(~d, ~kern, l, view, r0, b),
      ts,
      +r => +er => +eapp => Affects.cast(
        List<&2, Touch>,
        z => {List.contains(~Touch, ~Touch.is_eq, z, x) == True{}: Bool},
        List.append(&2, Touch, a, r),
        ts,
        eapp,
        Affects.touch_has.hit(~d, ~kern, l, view, n1, rest, st, nf, b, x, r0, q, eq, hn, hk, ih, a, ea, r, er)
      )
    )(e2)
  )(e)

# Branches.touch gives each touch that the changes of a branch of the names
# ns give
def Affects.touch_has(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  ns: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Vend.Branch,
  +x: Touch,
  +es: List<&2, BranchEntry>,
  +ee: {Branches.entries(~d, ~kern, l, Branches.of(st, ns)) == Some{es}: Maybe<&2, List<&2, BranchEntry>>},
  +hn: {List.contains(~String, ~String.eq, ns, nf) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool},
  +ts: List<&2, Touch>
) -> {Branches.touch(~d, ~kern, l, view, es, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}:
  match ns:
    case Nil{}:
      et => Empty.absurd({List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}, Shared.Bool.false_ne_true(hn))
    case Con{+n1, +rest}:
      +et => Affects.bind_some(
        BranchEntry,
        List<&2, BranchEntry>,
        {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
        BranchEntry.of(~d, l, Vend.Branch{st, n1}, Branch.head(~d, ~kern, l, Vend.Branch{st, n1})),
        e => Maybe.map(
          &2,
          List<&2, BranchEntry>,
          List<&2, BranchEntry>,
          r => e <> r,
          Branches.entries(~d, ~kern, l, Branches.of(st, rest))
        ),
        es,
        +e0 => +ee0 => e1 => Affects.map_some(
          List<&2, BranchEntry>,
          List<&2, BranchEntry>,
          {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
          r => e0 <> r,
          Branches.entries(~d, ~kern, l, Branches.of(st, rest)),
          es,
          +r0 => +er0 => +ees => Affects.entry_of(
            ~d,
            l,
            Vend.Branch{st, n1},
            Branch.head(~d, ~kern, l, Vend.Branch{st, n1}),
            e0,
            {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
            +vs => +hv => +e0eq => Affects.touch_has.at(
              ~d,
              ~kern,
              l,
              view,
              n1,
              rest,
              st,
              nf,
              b,
              x,
              vs,
              hv,
              r0,
              String.eq(n1, nf),
              {==},
              hn,
              hk,
              hn2 => hk2 => +ts2 => et2 => Affects.touch_has(~d, ~kern, l, view, rest, st, nf, b, x, r0, er0, hn2, hk2, ts2)(et2),
              ts
            )(
              Affects.cast(
                List<&2, BranchEntry>,
                z => {Branches.touch(~d, ~kern, l, view, z, b) == Some{ts}: Maybe<&2, List<&2, Touch>>},
                es,
                BranchEntry{Vend.Branch{st, n1}, vs, hv} <> r0,
                Equal.trans(
                  List<&2, BranchEntry>,
                  es,
                  e0 <> r0,
                  BranchEntry{Vend.Branch{st, n1}, vs, hv} <> r0,
                  Equal.sym(List<&2, BranchEntry>, e0 <> r0, es, ees),
                  Equal.cong(
                    BranchEntry,
                    List<&2, BranchEntry>,
                    z => z <> r0,
                    e0,
                    BranchEntry{Vend.Branch{st, n1}, vs, hv},
                    Equal.sym(BranchEntry, BranchEntry{Vend.Branch{st, n1}, vs, hv}, e0, e0eq)
                  )
                ),
                et
              )
            )
          )(ee0)
        )(e1)
      )(ee)

# the changes of another branch, whose tips are known, are those of its tips
def Affects.touches_at_of(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +b: Vend.Branch,
  +tb: Replicas.Tip,
  +eo: {Branch.other(from, b) == True{}: Bool},
  +ef: {Branch.head(~d, ~kern, l, from) == Some{tf}: Maybe<&2, Replicas.Tip>},
  +eb: {Branch.head(~d, ~kern, l, b) == Some{tb}: Maybe<&2, Replicas.Tip>}
) -> {
  Branch.touches(~d, ~kern, l, view, from, b) == Branch.touches.at(~d, l, view, from, tf, b, tb): Maybe<&2, List<&2, Touch>>
}:
  %Equal.sym(Bool, Branch.other(from, b), True{}, eo): {
    Shared.Bool.when(
      Maybe<&2, List<&2, Touch>>,
      _,
      u => Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, Touch>,
        Branch.head(~d, ~kern, l, from),
        tf2 => Branch.touches.of(~d, l, view, from, tf2, b, Branch.head(~d, ~kern, l, b))
      ),
      u => Some{[]}
    )
      == Branch.touches.at(~d, l, view, from, tf, b, tb): Maybe<&2, List<&2, Touch>>
  }
  %Equal.sym(Maybe<&2, Replicas.Tip>, Branch.head(~d, ~kern, l, from), Some{tf}, ef): {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, Touch>,
      _,
      tf2 => Branch.touches.of(~d, l, view, from, tf2, b, Branch.head(~d, ~kern, l, b))
    )
      == Branch.touches.at(~d, l, view, from, tf, b, tb): Maybe<&2, List<&2, Touch>>
  }
  %Equal.sym(Maybe<&2, Replicas.Tip>, Branch.head(~d, ~kern, l, b), Some{tb}, eb): {
    Branch.touches.of(~d, l, view, from, tf, b, _) == Branch.touches.at(~d, l, view, from, tf, b, tb): Maybe<&2, List<&2, Touch>>
  }
  {==}

# Branch.touches.at gives each touch that holds at the tips tf and tb
def Affects.at_has(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +from: Vend.Branch,
  +tf: Replicas.Tip,
  +b: Vend.Branch,
  +tb: Replicas.Tip,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +used: Resources.Name,
  +m: U32,
  +enum: {Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v) == Some{m}: Maybe<&2, U32>},
  +elt: {U32.is_lt(m, Replicas.Tip.count(tf)) == True{}: Bool},
  +hz: Maybe<&2, Hashes.Hash>,
  +ebef: {Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, tf, m) == Some{hz}: Maybe<&2, Maybe<&2, Hashes.Hash>>},
  +hX: Maybe<&2, Hashes.Hash>,
  +etk: {Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, tf, m) == Some{Replicas.Taken{v, hX}}: Maybe<&2, Replicas.Taken>},
  +d1: {Res.differs(~d, l, hX, hz, changed) == Some{True{}}: Maybe<&2, Bool>},
  +d2: {Res.differs(~d, l, hX, Replicas.Tip.content(tb), changed) == Some{True{}}: Maybe<&2, Bool>},
  +r0: Requests.Res,
  +efind: {Vend.Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ereach: {Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed) == Some{True{}}: Maybe<&2, Bool>},
  +a: List<&2, Touch>
) -> {Branch.touches.at(~d, l, view, from, tf, b, tb) == Some{a}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool}:
  +hb = Replicas.Tip.content(tb)
  e => Affects.bind_some(
    List<&2, Trees.Binding>,
    List<&2, Touch>,
    {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool},
    Vend.Tree.range(~d, l, hb, [0]),
    xs => Maybe.bind(
      &2,
      Reaches.Graph,
      List<&2, Touch>,
      Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
      users => Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users)
      )
    ),
    a,
    +xs => +er => e2 => Affects.bind_some(
      Reaches.Graph,
      List<&2, Touch>,
      {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool},
      Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new()),
      users => Maybe.bind(
        &2,
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users)
      ),
      a,
      +users => +eu => e3 => Affects.bind_some(
        List<&2, Replicas.Taken>,
        List<&2, Touch>,
        {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool},
        Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
        xs2 => Touches.all(~d, l, from, tf, xs2, 0, None{}, b, hb, Res.names(xs), users),
        a,
        +xs2 => +ev => e4 => Affects.all_has(
          ~d,
          l,
          from,
          tf,
          xs2,
          0,
          None{},
          b,
          hb,
          Res.names(xs),
          users,
          U32.to_nat(Replicas.Tip.count(tf)),
          ev,
          {==},
          m,
          v,
          hX,
          hz,
          changed,
          used,
          enum,
          etk,
          elt,
          Shared.Nat.le_zero(U32.to_nat(m)),
          Equal.trans(
            Bool,
            Nat.is_lt(U32.to_nat(m), U32.to_nat(Replicas.Tip.count(tf))),
            U32.is_lt(m, Replicas.Tip.count(tf)),
            True{},
            Equal.sym(
              Bool,
              U32.is_lt(m, Replicas.Tip.count(tf)),
              Nat.is_lt(U32.to_nat(m), U32.to_nat(Replicas.Tip.count(tf))),
              Shared.U32.is_lt_to_nat(m, Replicas.Tip.count(tf))
            ),
            elt
          ),
          ebef,
          d1,
          d2,
          Affects.find_names(~d, l, hb, xs, er, used, r0)(efind),
          Affects.reaches_back(~d, l, view, hb, xs, er, users, eu, used, changed, ereach),
          a
        )(e4)
      )(e3)
    )(e2)
  )(e)

# two branches of a touch that holds are of one store
def Affects.other_store(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +s1: Hashes.Hash,
  +nf: String,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +st: Hashes.Hash,
  +n: String,
  +used: Resources.Name
) -> {Touch.holds(~d, ~kern, l, view, Touch{Vend.Branch{s1, nf}, v, changed, Vend.Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>}
  -> {s1 == st: Hashes.Hash}:
  e => Affects.when_is(
    Maybe<&2, Bool>,
    {s1 == st: Hashes.Hash},
    Branch.other(Vend.Branch{s1, nf}, Vend.Branch{st, n}),
    u => Maybe.bind(
      &2,
      Replicas.Tip,
      Bool,
      Branch.head(~d, ~kern, l, Vend.Branch{s1, nf}),
      tf => Maybe.bind(
        &2,
        Replicas.Tip,
        Bool,
        Branch.head(~d, ~kern, l, Vend.Branch{st, n}),
        tb => Touch.holds.at(~d, l, view, tf, tb, v, changed, used)
      )
    ),
    u => Some{False{}},
    Some{True{}},
    eo => e1 => Hashes.Hash.is_eq_sound(s1, st)(
      Shared.List.all.if_hit(Hashes.Hash.is_eq(s1, st), w => Bool.not(String.eq(nf, n)))(eo)
    ),
    eof => e2 => Empty.absurd({s1 == st: Hashes.Hash}, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e2)))
  )(e)

# Node.affects gives each touch that holds, of a branch nf of the store st
def Affects.complete_at(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  +st: Hashes.Hash,
  +nf: String,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +n: String,
  +used: Resources.Name,
  +ts: List<&2, Touch>,
  hh: {
    Touch.holds(~d, ~kern, l, view, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>
  }
) -> {Node.affects(~d, ~kern, l, view, Vend.Branch{st, n}) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool}:
  +ea => Affects.holds_facts(
    ~d,
    ~kern,
    l,
    view,
    Vend.Branch{st, nf},
    v,
    changed,
    Vend.Branch{st, n},
    used,
    {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
    +eo => +tf => +ef => +tb => +eb => +m => +enum => +elt => +hz => +ebef => +hX => +etk => +d1 => +d2 => +r0 => +efind => +ereach => Affects.bind_some(
      List<&2, BranchEntry>,
      List<&2, Touch>,
      {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
      Node.branches(~d, ~kern, l, st),
      es => Branches.touch(~d, ~kern, l, view, es, Vend.Branch{st, n}),
      ts,
      +es => +ees => +et => Affects.bind_some(
        List<&2, Vend.Branch>,
        List<&2, BranchEntry>,
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
        Store.branches(~d, l, st, Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st)),
        bs => Branches.entries(~d, ~kern, l, bs),
        es,
        +bs => +ebs => +eent => Affects.head_start(
          ~d,
          ~kern,
          l,
          st,
          nf,
          tf,
          {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
          +rt => +ert => +ws => +ews => Affects.map_some(
            List<&2, Trees.Binding>,
            List<&2, Vend.Branch>,
            {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
            xs => Branches.of(st, Branches.names(xs)),
            Vend.Tree.range(~d, l, Replicas.Tip.log(rt), [5]),
            bs,
            +lx => +elx => +ebx => Affects.touch_has(
              ~d,
              ~kern,
              l,
              view,
              Branches.names(lx),
              st,
              nf,
              Vend.Branch{st, n},
              Touch{Vend.Branch{st, nf}, v, changed, Vend.Branch{st, n}, used},
              es,
              Affects.cast(
                List<&2, Vend.Branch>,
                z => {Branches.entries(~d, ~kern, l, z) == Some{es}: Maybe<&2, List<&2, BranchEntry>>},
                bs,
                Branches.of(st, Branches.names(lx)),
                Equal.sym(List<&2, Vend.Branch>, Branches.of(st, Branches.names(lx)), bs, ebx),
                eent
              ),
              Affects.started_in(~d, l, rt, lx, elx, nf, ws, ews),
              +a => ea2 => Affects.at_has(
                ~d,
                l,
                view,
                Vend.Branch{st, nf},
                tf,
                Vend.Branch{st, n},
                tb,
                v,
                changed,
                used,
                m,
                enum,
                elt,
                hz,
                ebef,
                hX,
                etk,
                d1,
                d2,
                r0,
                efind,
                ereach,
                a
              )(
                Equal.trans(
                  Maybe<&2, List<&2, Touch>>,
                  Branch.touches.at(~d, l, view, Vend.Branch{st, nf}, tf, Vend.Branch{st, n}, tb),
                  Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, Vend.Branch{st, n}),
                  Some{a},
                  Equal.sym(
                    Maybe<&2, List<&2, Touch>>,
                    Branch.touches(~d, ~kern, l, view, Vend.Branch{st, nf}, Vend.Branch{st, n}),
                    Branch.touches.at(~d, l, view, Vend.Branch{st, nf}, tf, Vend.Branch{st, n}, tb),
                    Affects.touches_at_of(~d, ~kern, l, view, Vend.Branch{st, nf}, tf, Vend.Branch{st, n}, tb, eo, ef, eb)
                  ),
                  ea2
                )
              ),
              ts
            )(et)
          )(
            Affects.cast(
              Maybe<&2, Replicas.Tip>,
              z => {Store.branches(~d, l, st, z) == Some{bs}: Maybe<&2, List<&2, Vend.Branch>>},
              Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st),
              Some{rt},
              ert,
              ebs
            )
          )
        )(ef)
      )(ees)
    )(ea)
  )(hh)

# Node.affects_complete, with its binders reusable
def Affects.complete_law(
  ~d: Vend.Led(),
  ~kern: Vend.Kern(d),
  +l: Vend.L(d),
  +view: List<&2, Formats.Cond>,
  x: Touch,
  +ts: List<&2, Touch>
) -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}
  -> {Node.affects(~d, ~kern, l, view, Touch.branch(x)) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}:
  match x:
    case Touch{Vend.Branch{+s1, +nf}, +v, +changed, Vend.Branch{+st, +n}, +used}:
      +hh => ea => Affects.cast(
        Hashes.Hash,
        z => {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Vend.Branch{z, nf}, v, changed, Vend.Branch{st, n}, used}) == True{}: Bool},
        st,
        s1,
        Equal.sym(Hashes.Hash, s1, st, Affects.other_store(~d, ~kern, l, view, s1, nf, v, changed, st, n, used)(hh)),
        Affects.complete_at(
          ~d,
          ~kern,
          l,
          view,
          st,
          nf,
          v,
          changed,
          n,
          used,
          ts,
          Affects.cast(
            Hashes.Hash,
            z => {
              Touch.holds(~d, ~kern, l, view, Touch{Vend.Branch{z, nf}, v, changed, Vend.Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>
            },
            s1,
            st,
            Affects.other_store(~d, ~kern, l, view, s1, nf, v, changed, st, n, used)(hh),
            hh
          )
        )(ea)
      )
