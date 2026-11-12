import Base
import ../../shared/replica.bend as Replicas
import ../../shared/shared/formats.bend as Formats
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/depot.bend as Depots
import ../../shared/shared/rope.bend as Ropes
import ../../shared/shared/shared/keyset.bend as KeySets
import ../../shared/shared/shared/pack.bend as Packs
import ../../shared/shared/shared/reach.bend as Reaches
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/shared/side.bend as Sides
import ../../shared/shared/shared/shared/crit.bend as Crits
import ../../shared/shared/shared/text.bend as Texts
import ../../shared/shared/tree.bend as Trees
import ../shared/requests.bend as Requests
import ../shared/shared/resources.bend as Resources

# The pure core of a Vend Node (README): what it answers, and the rules of
# Vend's kernel. A Vend Node is a replica (Replicas) of the machine of Vend
# (Requests.Ask.machine): a store is a root line, a branch is a sub line, the
# owners of a line are its voters, a version is a taken request, and a mark
# is a label. So every answer here is a read of a ledger, and what Replicas
# proves of every machine holds of Vend: a node only grows, a history is one,
# and what a line knows is final.
#
# A def here takes the ledger d as a template, and the kernel kern where it
# reads a history. transport/spec.bend carries the core over IO.

# The ledger and the kernel of Vend
# ---------------------------------

# a ledger for the requests of Vend
def Led() -> Type:
  Replicas.Led(Requests.Ask.machine())

# what the ledger d is kept as
def L(d: Led()) -> Data:
  Replicas.Led.L(Requests.Ask.machine(), d)

# a kernel for the requests of Vend, on the ledger d
def Kern(-d: Led()) -> Type:
  Replicas.Kernel(Requests.Ask.machine(), d)

# Names
# -----

# a branch: the root of its store, and its name
type Branch is Data:
  Branch{store: Hashes.Hash, name: String}

# the line of the branch b
def Branch.line(b: Branch) -> Ledgers.Line:
  match b:
    case Branch{st, n}:
      Ledgers.Line{st, Some{n}}

# a version of a branch, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{branch: Branch, version: Ledgers.Id}
  Point.Head{branch: Branch}
  Point.Mark{branch: Branch, mark: String}

# Resources in a tree
# -------------------

# a and b are the same resource, or both none: the same format and content
def Res.same(a: Maybe<&2, Requests.Res>, b: Maybe<&2, Requests.Res>) -> Bool:
  Shared.Maybe.is_eq(
    ~Requests.Res,
    ~(x => y => Codes.Code.is_eq(~Requests.Res, ~Requests.Res.code, x, y)),
    a,
    b
  )

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the value of the resource m in a tree (none: it is not there; the key goes)
def Res.value(m: Maybe<&2, Requests.Res>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Requests.Res, List<&2, U32>, m, x => Some{Requests.Res.code(x, [])})

# the resource in the value m, if any
def Res.found(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Requests.Res>:
  Codes.Code.whole.of(~Requests.Res, ~Requests.Res.code, ~Requests.Res.code.read, m)

# the root of the content of the resource n in the tree whose root is h, or
# that it is not there (none: l lacks a node of the tree)
def Res.find(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Requests.Res>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the bytes under the rope root r (none: l lacks a node)
def Root.bytes(~d: Led(), l: L(d), r: Ropes.Root) -> Maybe<&2, Texts.Bytes()>:
  Ropes.Rope.bytes(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, r)

# the root of the bytes of the resource x
def Res.root(x: Requests.Res) -> Ropes.Root:
  match x:
    case Requests.Res{f, r}:
      r

# the hash of the format of the resource x
def Res.format.hash(x: Requests.Res) -> Hashes.Hash:
  match x:
    case Requests.Res{f, r}:
      f

# the bytes of the resource m (none: it is not there, or l lacks a node)
def Res.bytes(~d: Led(), l: L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, Requests.Res, Texts.Bytes(), m, x => Root.bytes(~d, l, Res.root(x)))

# the format that the ledger holds under the hash h (none: l lacks it, or it
# is not the code of a format)
def Format.at(~d: Led(), l: L(d), h: Hashes.Hash) -> Maybe<&2, Formats.Format>:
  Codes.Code.whole.of(
    ~Formats.Format,
    ~Formats.Format.code,
    ~Formats.Format.code.read,
    Replicas.Led.fetch(~Requests.Ask.machine(), ~d)(l)(h)
  )

# the format of the resource x
def Res.format(~d: Led(), l: L(d), x: Requests.Res) -> Maybe<&2, Formats.Format>:
  Format.at(~d, l, Res.format.hash(x))

# Versions
# --------
# A version is a request that its branch took. Its content is the root that
# the log of the branch holds for its number.

# The rules of the kernel
# -----------------------
# What each change does to its line (README). A rule reads the ledger and the
# tip of its own line, and nothing else: content of another line comes with
# the change (Requests.Source), so no rule reads the history of a line. A rule
# waits for what the ledger lacks (none), and refuses only on what it knows.
# The owners of a line keep each part of what they decide: a rule waits for
# the bytes and the trees that its result holds.

# the act that takes the tree p as the content, after the nodes ns, with the
# owners vs if any
def Act.put(
  vs: Maybe<&2, List<&2, String>>,
  ns: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Maybe<&2, Replicas.Act>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Replicas.Act.Taken{
          vs,
          Trees.Edit.root(x),
          List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(x))
        }
      }

# l holds the resource m: its format and its bytes (a resource that is not
# there needs none)
def Res.kept(~d: Led(), +l: L(d), m: Maybe<&2, Requests.Res>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      List.all.if(
        u => Maybe.is_some(&2, Texts.Bytes(), Root.bytes(~d, l, Res.root(x))),
        Maybe.is_some(&2, Formats.Format, Res.format(~d, l, x))
      )

# the binding x is not a resource, or l holds its format and its bytes
def Res.held(~d: Led(), l: L(d), x: Trees.Binding) -> Bool:
  match x:
    case Trees.Binding{Con{0, r}, v}:
      Res.kept(~d, l, Codes.Code.whole.read(~Requests.Res, ~Requests.Res.code, ~Requests.Res.code.read, v))
    case _:
      True{}

# l holds the format and the bytes of each resource among the bindings xs
def Res.all_held(~d: Led(), +l: L(d), xs: List<&2, Trees.Binding>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      List.all.if(u => Res.all_held(~d, l, rest), Res.held(~d, l, x))

# the bindings of the tree whose root is h whose keys start with p (none: l
# lacks a node of the tree)
def Tree.range(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, p: List<&2, U32>) -> Maybe<&2, List<&2, Trees.Binding>>:
  Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, p)

# l holds the whole of the tree whose root is h: each of its nodes, and the
# format and the bytes of each of its resources. A clear def: it reads each
# resource
def Tree.kept(~d: Led(), +l: L(d), h: Maybe<&2, Hashes.Hash>) -> Bool:
  Maybe.default(
    &2,
    Bool,
    Maybe.bind(
      &2,
      List<&2, Trees.Binding>,
      Bool,
      Tree.range(~d, l, h, []),
      bs => Some{Res.all_held(~d, l, bs)}
    ),
    False{}
  )

# l holds each node of the tree whose root is h
def Tree.whole(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> Bool:
  Maybe.is_some(&2, List<&2, Trees.Binding>, Tree.range(~d, l, h, []))

# k when l holds the whole of the tree whose root is h, else wait
def Tree.when_kept(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  k: Unit -> Maybe<&2, Replicas.Act>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(Maybe<&2, Replicas.Act>, Tree.kept(~d, l, h), k, u => None{})

# the root that the content x gives the resource n at the tip t: a root, or
# what a version of the same line held (none: wait for that version, or for a
# node)
def Content.find(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  x: Requests.Content
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match x:
    case Requests.Content.New{r}:
      Some{Some{r}}
    case Requests.Content.Of{i}:
      Maybe.bind(
        &2,
        Maybe<&2, Hashes.Hash>,
        Maybe<&2, Requests.Res>,
        Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i),
        h => Res.find(~d, l, h, n)
      )

# the root of the content of the base m of a write, at the tip t (none: the
# line did not take the base yet). A resource with no base starts from the
# empty tree
def Base.root(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  match m:
    case None{}:
      Some{None{}}
    case Some{i}:
      Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i)

# the act that sets the resource n to the root new in the content of the tip
# t, once l holds its bytes (none: wait for them)
def Res.set(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  +new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Res.kept(~d, l, new),
    u => Act.put(
      None{},
      [],
      Replicas.Tree.put(
        ~Requests.Ask.machine(),
        ~d,
        l,
        Replicas.Tip.content(t),
        Key.res(n),
        Res.value(new)
      )
    ),
    u => None{}
  )

# Write.act once the resource holds ours at the tip, held at the base and
# gets new: taken when ours is what the base held, else stale
def Write.act.of(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  ours: Maybe<&2, Requests.Res>,
  held: Maybe<&2, Requests.Res>,
  new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Res.same(ours, held),
    u => Res.set(~d, l, t, n, new),
    u => Some{Replicas.Act.Stale{}}
  )

# what a write of the resource n since base, with the content x, does at the
# tip t of a branch: it is taken when n holds at t what it held at base, and
# then n holds x; else it is stale. So two writers that change one resource
# are a conflict, and the second is refused
def Write.act(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Requests.Content
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Res.find(~d, l, Replicas.Tip.content(t), n),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Base.root(~d, l, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Res.find(~d, l, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Content.find(~d, l, t, n, x),
          new => Write.act.of(~d, l, t, n, ours, held, new)
        )
      )
    )
  )

# the root of the tree of the source s
def Source.root(s: Requests.Source) -> Maybe<&2, Hashes.Hash>:
  match s:
    case Requests.Source{v, h}:
      h

# what a move to the source s does: the branch takes it, and its content is
# the tree of s, the same tree (none: wait for the whole tree)
def Move.act(~d: Led(), l: L(d), s: Requests.Source) -> Maybe<&2, Replicas.Act>:
  +h = Source.root(s)
  Tree.when_kept(~d, l, h, u => Some{Replicas.Act.Taken{None{}, h, []}})

# the first tip of a new branch whose content is h, at the tip t of its
# store: it starts with no log, and the owners of the store own it
def Branch.tip(t: Replicas.Tip, h: Maybe<&2, Hashes.Hash>) -> Replicas.Tip:
  Replicas.Tip{h, None{}, 0, Replicas.Tip.voters(t)}

# what a new branch b from the source m does, at the tip t of its store: the
# store opens the branch, empty or with the tree of the source (none: wait for
# the whole tree)
def Branch.act(
  ~d: Led(),
  l: L(d),
  +t: Replicas.Tip,
  +b: String,
  m: Maybe<&2, Requests.Source>
) -> Maybe<&2, Replicas.Act>:
  match m:
    case None{}:
      Some{Replicas.Act.Opens{b, Branch.tip(t, None{}), []}}
    case Some{s}:
      +h = Source.root(s)
      Tree.when_kept(~d, l, h, u => Some{Replicas.Act.Opens{b, Branch.tip(t, h), []}})

# what a first key k of the node n does, at the tip t of a store: the content
# of the store holds the key for the node
def Key.act(~d: Led(), l: L(d), t: Replicas.Tip, n: String, k: Hashes.Hash) -> Maybe<&2, Replicas.Act>:
  Act.put(
    None{},
    [],
    Replicas.Tree.put(
      ~Requests.Ask.machine(),
      ~d,
      l,
      Replicas.Tip.content(t),
      Requests.Key.seal(n),
      Some{Hashes.Hash.code(k, [])}
    )
  )

# Clashes
# -------

# the key of the open clashes of the merge of the request k: the resources
# that still clash after it. So what a merge left is one read, and no walk
def Key.clashes(k: Ledgers.Id) -> List<&2, U32>:
  3 <> Ledgers.Id.code(k, [])

# the value of the open clashes ns of a merge (none: no clash is open; the
# key goes)
def Clash.value(ns: List<&2, Resources.Name>) -> Maybe<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, rest}:
      Some{Codes.Code.list(~Resources.Name, ~Resources.Name.code, n <> rest, [])}

# the resources that still clash after the merge k, in the tree h (none: l
# lacks a node, so a read cannot tell)
def Clash.names(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  k: Ledgers.Id
) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(
    &2,
    Maybe<&2, List<&2, Resources.Name>>,
    List<&2, Resources.Name>,
    m => Maybe.default(&2, List<&2, Resources.Name>, m, []),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k))
    )
  )

# a resource of the tree h still clashes after the merge k
def Clash.left(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, k: Ledgers.Id) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => Bool.not(List.is_empty(&2, Resources.Name, ns)),
    Clash.names(~d, l, h, k)
  )

# the resources ns, with n when it is not among them
def Clash.put(+n: Resources.Name, +ns: List<&2, Resources.Name>) -> List<&2, Resources.Name>:
  Shared.Bool.when(
    List<&2, Resources.Name>,
    List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    u => ns,
    u => n <> ns
  )

# the clash that the merge k opened in the resource n is open in the tree h
def Clash.open(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id
) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    Clash.names(~d, l, h, k)
  )

# Trees being written
# -------------------

# a tree being written: the ledger with its new nodes, its root, and the new
# nodes
type Work<-L: Data> is Data:
  Work{ledger: L, root: Maybe<&2, Hashes.Hash>, nodes: List<&2, List<&2, U32>>}

# the work on l with the nodes ns, after the tree p
def Work.put(
  ~d: Led(),
  l: L(d),
  ns: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Maybe<&2, Work<L(d)>>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Work{
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(x), l),
          Trees.Edit.root(x),
          List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(x))
        }
      }

# the work w with the key k set to the value m (none: deleted; none at all:
# the ledger lacks a node)
def Work.set(~d: Led(), w: Work<L(d)>, k: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Work<L(d)>>:
  match w:
    case Work{+l, h, ns}:
      Work.put(~d, l, ns, Replicas.Tree.put(~Requests.Ask.machine(), ~d, l, h, k, m))

# the work w with the nodes ms as data
def Work.keep(~d: Led(), w: Work<L(d)>, +ms: List<&2, List<&2, U32>>) -> Work<L(d)>:
  match w:
    case Work{l, h, ns}:
      Work{
        Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, l),
        h,
        List.append(&2, List<&2, U32>, ns, ms)
      }

# the work w with the resource n among the open clashes of the merge k
def Work.clash(~d: Led(), w: Work<L(d)>, +k: Ledgers.Id, n: Resources.Name) -> Maybe<&2, Work<L(d)>>:
  match w:
    case Work{+l, +h, ns}:
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Work<L(d)>,
        Clash.names(~d, l, h, k),
        cs => Work.set(~d, Work{l, h, ns}, Key.clashes(k), Clash.value(Clash.put(n, cs)))
      )

# the act that takes the work m as the content, with the owners vs if any,
# once each node that the work adds reads back from its ledger: a node whose
# hash another one holds waits, so what an act writes is what a read finds
def Work.act(~d: Led(), vs: Maybe<&2, List<&2, String>>, m: Maybe<&2, Work<L(d)>>) -> Maybe<&2, Replicas.Act>:
  match m:
    case None{}:
      None{}
    case Some{Work{l, h, +ns}}:
      Shared.Maybe.when(
        Replicas.Act,
        Depots.Depot.holds(~L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), l, ns),
        u => Some{Replicas.Act.Taken{vs, h, ns}}
      )

# what a resolve of the resource n of the merge k, with the content x, does
# at the tip t: while the clash is open, and once l holds the bytes, the
# resource holds x and the clash is shut; else it is stale (none: wait for
# what l lacks)
def Resolve.act.of(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    List<&2, Resources.Name>,
    Replicas.Act,
    Clash.names(~d, l, Replicas.Tip.content(t), k),
    +cs => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n),
      u => Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Res.kept(~d, l, new),
        v => Work.act(
          ~d,
          None{},
          Maybe.bind(
            &2,
            Work<L(d)>,
            Work<L(d)>,
            Work.set(~d, Work{l, Replicas.Tip.content(t), []}, Key.res(n), Res.value(new)),
            w => Work.set(
              ~d,
              w,
              Key.clashes(k),
              Clash.value(Shared.List.remove(~Resources.Name, ~Resources.Name.is_eq, cs, n))
            )
          )
        ),
        v => None{}
      ),
      u => Some{Replicas.Act.Stale{}}
    )
  )

# what a resolve does (Resolve.act.of), once the root of its content is known
def Resolve.act(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  k: Ledgers.Id,
  +n: Resources.Name,
  x: Requests.Content
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Content.find(~d, l, t, n, x),
    new => Resolve.act.of(~d, l, t, k, n, new)
  )

# Merges
# ------
# A merge goes resource by resource, each in its own format. It takes theirs
# and the base as trees that come with the change.

# what a merge keeps of a resource: one side (none: removed), new bytes in a
# format, or a clash
type Pick is Data:
  Pick.Take{res: Maybe<&2, Requests.Res>}
  Pick.Make{format: Hashes.Hash, bytes: Texts.Bytes()}
  Pick.Clash{}

# the pick of a merge of bytes in the format whose hash is h
def Pick.of(h: Hashes.Hash, m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Pick.Make{h, x}
    case Formats.Merged.Clash{}:
      Pick.Clash{}

# what a submodule holds: a version of a branch of another store, by its
# number on the branch and its request. The history of a branch is one line,
# so of two pointers to one branch the higher number is the newer
type Pointer is Data:
  Pointer{store: Hashes.Hash, branch: String, number: U32, version: Ledgers.Id}

# the pointer x, then r
def Pointer.code(x: Pointer, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Pointer{st, b, k, v}:
      Hashes.Hash.code(st, Codes.Code.text(b, k <> Ledgers.Id.code(v, r)))

# a pointer
def Pointer.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Pointer>>:
  Codes.Code.four.read(
    ~Hashes.Hash,
    ~String,
    ~U32,
    ~Ledgers.Id,
    ~Pointer,
    ~Hashes.Hash.code.read,
    ~Codes.Code.text.read,
    ~Codes.Code.token.read,
    ~Ledgers.Id.code.read,
    st => b => k => v => Pointer{st, b, k, v},
    ts
  )

# a pointer reads back from its code: a submodule names one version of one
# branch of one store
law Pointer.code_read:
  for x: Pointer
  for r: List<&2, U32>
  {Pointer.code.read(Pointer.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Pointer>>}

def Pointer.code_read(x, r):
  match x:
    case Pointer{st, b, k, v}:
      Codes.Code.four_read(
        ~Hashes.Hash,
        ~String,
        ~U32,
        ~Ledgers.Id,
        ~Pointer,
        ~Hashes.Hash.codec(),
        ~Codes.Code.text.codec(),
        ~Codes.Code.token.codec(),
        ~Ledgers.Id.codec(),
        w => y => z => q => Pointer{w, y, z, q},
        st,
        b,
        k,
        v,
        r
      )

# the bytes of a submodule that holds the pointer x: its code, four bytes in a
# word
def Pointer.bytes(x: Pointer) -> Texts.Bytes():
  Packs.Pack.unpack(Pointer.code(x, []))

# the pointer that the bytes b of a submodule hold
def Pointer.read(b: Texts.Bytes()) -> Maybe<&2, Pointer>:
  Codes.Code.whole.read(~Pointer, ~Pointer.code, ~Pointer.code.read, Packs.Pack.words(b))

# the newer of the pointers x and y, when they point to one branch of one
# store and their numbers differ, or they are the same
def Pointer.newer(x: Pointer, y: Pointer) -> Maybe<&2, Pointer>:
  match x y:
    case Pointer{+s1, +b1, +k1, +v1} Pointer{+s2, +b2, +k2, +v2}:
      Shared.Bool.when(
        Maybe<&2, Pointer>,
        List.all.if(u => String.eq(b1, b2), Hashes.Hash.is_eq(s1, s2)),
        u => Shared.Bool.when(
          Maybe<&2, Pointer>,
          U32.is_lt(k1, k2),
          v => Some{Pointer{s2, b2, k2, v2}},
          v => Shared.Bool.when(
            Maybe<&2, Pointer>,
            U32.is_lt(k2, k1),
            w => Some{Pointer{s1, b1, k1, v1}},
            w => Shared.Maybe.when(
              Pointer,
              Ledgers.Id.is_eq(v1, v2),
              z => Some{Pointer{s1, b1, k1, v1}}
            )
          )
        ),
        u => None{}
      )

# the merge of two submodules that hold the pointers x and y, in the format
# whose hash is h: the newer one; a clash when they point to two branches, or
# a pointer does not read
def Pointer.merge(h: Hashes.Hash, x: Maybe<&2, Pointer>, y: Maybe<&2, Pointer>) -> Pick:
  match x y:
    case Some{px} Some{py}:
      Maybe.default(
        &2,
        Pick,
        Maybe.bind(&2, Pointer, Pick, Pointer.newer(px, py), p => Some{Pick.Make{h, Pointer.bytes(p)}}),
        Pick.Clash{}
      )
    case a b:
      Pick.Clash{}

# the bytes of the resource m: a resource that is not there is empty
def Res.text(~d: Led(), l: L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case None{}:
      Some{[]}
    case Some{x}:
      Root.bytes(~d, l, Res.root(x))

# the hash of the format of the resource m, else of n: the format of a merge
def Res.format.of(m: Maybe<&2, Requests.Res>, n: Maybe<&2, Requests.Res>) -> Maybe<&2, Hashes.Hash>:
  match m n:
    case Some{x} y:
      Some{Res.format.hash(x)}
    case None{} Some{y}:
      Some{Res.format.hash(y)}
    case None{} None{}:
      None{}

# the two sides hold one format, or one side holds none
def Res.one_format(+o: Maybe<&2, Requests.Res>, +t: Maybe<&2, Requests.Res>) -> Bool:
  match o t:
    case Some{x} Some{y}:
      Hashes.Hash.is_eq(Res.format.hash(x), Res.format.hash(y))
    case a b:
      True{}

# Pick.in once the bytes ob of ours and tb of theirs are known
def Pick.format(
  ~d: Led(),
  +l: L(d),
  h: Hashes.Hash,
  f: Formats.Format,
  b: Maybe<&2, Requests.Res>,
  ob: Texts.Bytes(),
  tb: Texts.Bytes()
) -> Maybe<&2, Pick>:
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      Some{Pointer.merge(h, Pointer.read(ob), Pointer.read(tb))}
    case g:
      Maybe.bind(
        &2,
        Texts.Bytes(),
        Pick,
        Res.text(~d, l, b),
        bb => Some{Pick.of(h, Formats.Format.merge(g, bb, ob, tb))}
      )

# the pick of a merge of both changes in the format f, whose hash is h: a
# submodule takes the newer pointer, any other format merges its bytes (none:
# wait for bytes)
def Pick.in(
  ~d: Led(),
  +l: L(d),
  +h: Hashes.Hash,
  f: Formats.Format,
  b: Maybe<&2, Requests.Res>,
  o: Maybe<&2, Requests.Res>,
  t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Maybe.bind(
    &2,
    Texts.Bytes(),
    Pick,
    Res.text(~d, l, o),
    ob => Maybe.bind(
      &2,
      Texts.Bytes(),
      Pick,
      Res.text(~d, l, t),
      tb => Pick.format(~d, l, h, f, b, ob, tb)
    )
  )

# the pick of a merge of both changes (none: wait for a format or bytes). Two
# sides in two formats clash
def Pick.both(
  ~d: Led(),
  +l: L(d),
  b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Shared.Bool.when(
    Maybe<&2, Pick>,
    Res.one_format(o, t),
    u => Maybe.default(
      &2,
      Maybe<&2, Pick>,
      Maybe.bind(
        &2,
        Hashes.Hash,
        Maybe<&2, Pick>,
        Res.format.of(o, t),
        +h => Some{
          Maybe.bind(
            &2,
            Formats.Format,
            Pick,
            Format.at(~d, l, h),
            f => Pick.in(~d, l, h, f, b, o, t)
          )
        }
      ),
      Some{Pick.Take{None{}}}
    ),
    u => Some{Pick.Clash{}}
  )

# what a merge keeps of a resource, once the side s is known
def Pick.side(
  ~d: Led(),
  l: L(d),
  b: Maybe<&2, Requests.Res>,
  o: Maybe<&2, Requests.Res>,
  t: Maybe<&2, Requests.Res>,
  s: Sides.Side
) -> Maybe<&2, Pick>:
  match s:
    case Sides.Side.Theirs{}:
      Some{Pick.Take{t}}
    case Sides.Side.Ours{}:
      Some{Pick.Take{o}}
    case Sides.Side.Both{}:
      Pick.both(~d, l, b, o, t)

# what a merge of the base b, ours o and theirs t keeps of a resource: the
# side that Side.of takes (theirs when ours is the base; ours when theirs is
# the base or both agree), else both merged, in their format. So a merge never
# loses a change that only one side made (Sides.Side.keeps_changes)
def Pick.merge(
  ~d: Led(),
  l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>
) -> Maybe<&2, Pick>:
  Pick.side(~d, l, b, o, t, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Res.same, b, o, t))

# the work w with the resource n as the pick p says, for the merge k: a clash
# keeps ours and opens the clash of the resource
def Merge.pick(
  ~d: Led(),
  w: Work<L(d)>,
  k: Ledgers.Id,
  +n: Resources.Name,
  p: Pick
) -> Maybe<&2, Work<L(d)>>:
  match p:
    case Pick.Take{x}:
      Work.set(~d, w, Key.res(n), Res.value(x))
    case Pick.Make{h, bytes}:
      +r = Ropes.Rope.of_bytes(bytes)
      Work.set(
        ~d,
        Work.keep(~d, w, Ropes.Put.nodes(r)),
        Key.res(n),
        Res.value(Some{Requests.Res{h, Ropes.Put.root(r)}})
      )
    case Pick.Clash{}:
      Work.clash(~d, w, k, n)

# the name of the resource of the key k, when it is the key of one
def Res.name(k: List<&2, U32>) -> Maybe<&2, Resources.Name>:
  match k:
    case Con{0, r}:
      Codes.Code.whole.read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, r)
    case _:
      None{}

# the work m after the merge of the resource n: the pick of the base hb, ours
# ho and theirs ht, read in l (none: wait for a node or for bytes)
def Merge.one(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +w: Work<L(d)>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<L(d)>,
    Res.find(~d, l, hb, n),
    +b => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Work<L(d)>,
      Res.find(~d, l, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Work<L(d)>,
        Res.find(~d, l, ht, n),
        t => Maybe.bind(
          &2,
          Pick,
          Work<L(d)>,
          Pick.merge(~d, l, b, o, t),
          p => Merge.pick(~d, w, k, n, p)
        )
      )
    )
  )

# the work m after the merge of each resource among the keys xs. A
# resource that comes twice is merged twice, with the same pick
def Merge.all(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  m: Maybe<&2, Work<L(d)>>
) -> Maybe<&2, Work<L(d)>>:
  match xs m:
    case Nil{} y:
      y
    case Con{x, rest} None{}:
      None{}
    case Con{x, rest} Some{+w}:
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        rest,
        Maybe.default(
          &2,
          Maybe<&2, Work<L(d)>>,
          Maybe.bind(
            &2,
            Resources.Name,
            Maybe<&2, Work<L(d)>>,
            Res.name(x),
            n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
          ),
          Some{w}
        )
      )

# the root of the tree of the base m of a merge: no base is the empty tree
def Base.tree(m: Maybe<&2, Requests.Source>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      Source.root(s)

# what the merge k of the source from, since the base, does at the tip t:
# once l holds the three whole trees, each resource that ours and theirs hold
# differently gets its pick (Pick.merge); every other resource stays
def Merge.act(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  +k: Ledgers.Id,
  from: Requests.Source,
  base: Maybe<&2, Requests.Source>
) -> Maybe<&2, Replicas.Act>:
  +ho = Replicas.Tip.content(t)
  +ht = Source.root(from)
  +hb = Base.tree(base)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    List.all.if(u => List.all.if(u2 => Tree.kept(~d, l, ho), Tree.kept(~d, l, hb)), Tree.kept(~d, l, ht)),
    u => Work.act(
      ~d,
      None{},
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        Maybe.default(
          &2,
          List<&2, List<&2, U32>>,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
          []
        ),
        Some{Work{l, ho, []}}
      )
    ),
    u => None{}
  )

# Groups and owners
# -----------------
# A group is in the tree of its store: its members, each a node or another
# group. The nodes of a group are all those that it reaches through its
# members. The owners of a line are the nodes of its owner group.

# the key of the members of the group g, in the tree of a store
def Key.group(g: String) -> List<&2, U32>:
  2 <> Codes.Code.text(g, [])

# the key of the owner group of a line, in its tree
def Key.owner() -> List<&2, U32>:
  [6]

# a group in a tree: its name and its members
type Group is Data:
  Group{name: String, members: List<&2, Requests.Member>}

# the group of the binding x, when it is one
def Group.read(x: Trees.Binding) -> Maybe<&2, Group>:
  match x:
    case Trees.Binding{Con{2, r}, v}:
      Maybe.bind(
        &2,
        String,
        Group,
        Codes.Code.whole.read(~String, ~Codes.Code.text, ~Codes.Code.text.read, r),
        n => Maybe.bind(
          &2,
          List<&2, Requests.Member>,
          Group,
          Codes.Code.whole.read(~List<&2, Requests.Member>, ~Requests.Members.code, ~Requests.Members.code.read, v),
          ms => Some{Group{n, ms}}
        )
      )
    case _:
      None{}

# the groups among the bindings xs
def Groups.of(xs: List<&2, Trees.Binding>) -> List<&2, Group>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Shared.Maybe.cons(Group, Group.read(x), Groups.of(rest))

# the key of the node n in the graph of members
def Node.key(n: String) -> List<&2, U32>:
  0 <> Codes.Code.text(n, [])

# the key of the group g in the graph of members
def Group.key(g: String) -> List<&2, U32>:
  1 <> Codes.Code.text(g, [])

# the key of each of the members ms
def Members.keys(ms: List<&2, Requests.Member>) -> List<&2, List<&2, U32>>:
  match ms:
    case Nil{}:
      []
    case Con{Requests.Member.Node{n}, rest}:
      Node.key(n) <> Members.keys(rest)
    case Con{Requests.Member.Group{g}, rest}:
      Group.key(g) <> Members.keys(rest)

# the graph g with each group of gs: a group leads to each of its members
def Groups.graph(gs: List<&2, Group>, g: Reaches.Graph) -> Reaches.Graph:
  match gs:
    case Nil{}:
      g
    case Con{Group{n, ms}, rest}:
      Groups.graph(rest, Reaches.Graph.links(Members.keys(ms), Group.key(n), g))

# the nodes among the members ms, then acc
def Members.nodes(ms: List<&2, Requests.Member>, acc: List<&2, String>) -> List<&2, String>:
  match ms:
    case Nil{}:
      acc
    case Con{Requests.Member.Node{n}, rest}:
      n <> Members.nodes(rest, acc)
    case Con{Requests.Member.Group{g}, rest}:
      Members.nodes(rest, acc)

# each node that is a member of a group of gs
def Groups.nodes(gs: List<&2, Group>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{Group{n, ms}, rest}:
      Members.nodes(ms, Groups.nodes(rest))

# the nodes of ns that the set reach holds
def Nodes.inside(ns: List<&2, String>, +reach: Crits.Dict(Unit)) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      List.filter.put(String, n, Nodes.inside(rest, reach), Crits.Dict.has(Unit, reach, Node.key(n)))

# what the group g reaches among the groups gs: each member, and each member
# of one, at any depth
def Group.reach(+gs: List<&2, Group>, g: String) -> Crits.Dict(Unit):
  Reaches.Graph.reach(Groups.graph(gs, Reaches.Graph.new()), Group.key(g))

# the nodes of the group g among the groups gs, each once
def Group.nodes.of(+gs: List<&2, Group>, g: String) -> List<&2, String>:
  KeySets.KeySet.unique(
    ~String,
    ~String.eq,
    ~(t => Codes.Code.text(t, [])),
    Nodes.inside(Groups.nodes(gs), Group.reach(gs, g)),
    Crits.Dict.new(~String)
  )

# the groups of the tree whose root is h
def Groups.in(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, List<&2, Group>>:
  Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Group>, Groups.of, Tree.range(~d, l, h, [2]))

# the nodes of the group g in the tree whose root is h, each once: the nodes
# that own what g owns. A clear def: it walks the tree
def Group.nodes(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, +g: String) -> Maybe<&2, List<&2, String>>:
  Maybe.map(&2, List<&2, Group>, List<&2, String>, gs => Group.nodes.of(gs, g), Groups.in(~d, l, h))

# Group.act once the tree with the new members is known: stale when the group
# then reaches itself
def Group.act.of(~d: Led(), l: L(d), +g: String, p: Maybe<&2, Trees.Edit>) -> Maybe<&2, Replicas.Act>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Maybe.bind(
        &2,
        List<&2, Group>,
        Replicas.Act,
        Groups.in(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(x), l), Trees.Edit.root(x)),
        gs => Shared.Bool.when(
          Maybe<&2, Replicas.Act>,
          Crits.Dict.has(Unit, Group.reach(gs, g), Group.key(g)),
          u => Some{Replicas.Act.Stale{}},
          u => Act.put(None{}, [], Some{x})
        )
      )

# what a group g with the members ms does, at the tip t of a store: the tree
# of the store holds the members of g; a group that would reach itself is
# refused (none: wait for the whole tree)
def Group.act(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  +g: String,
  ms: List<&2, Requests.Member>
) -> Maybe<&2, Replicas.Act>:
  +h = Replicas.Tip.content(t)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Tree.whole(~d, l, h),
    u => Group.act.of(
      ~d,
      l,
      g,
      Replicas.Tree.put(
        ~Requests.Ask.machine(),
        ~d,
        l,
        h,
        Key.group(g),
        Some{Requests.Members.code(ms, [])}
      )
    ),
    u => None{}
  )

# the tree in which an Own reads its group, at the tip t: the tree of the
# source that comes with it, else the tree of the line itself
def Own.tree(t: Replicas.Tip, at: Maybe<&2, Requests.Source>) -> Maybe<&2, Hashes.Hash>:
  match at:
    case None{}:
      Replicas.Tip.content(t)
    case Some{s}:
      Source.root(s)

# what an Own of the group g with the owners os does, at the tip t: it is
# taken when os are the nodes of g in the tree that it reads, and there is
# one at least; the line then records g as its owner group, and os own its
# next step. Else it is stale (none: wait for the whole tree)
def Own.act(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +g: String,
  at: Maybe<&2, Requests.Source>,
  +os: List<&2, String>
) -> Maybe<&2, Replicas.Act>:
  +h = Own.tree(t, at)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Tree.whole(~d, l, h),
    u => Maybe.bind(
      &2,
      List<&2, String>,
      Replicas.Act,
      Group.nodes(~d, l, h, g),
      +ns => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.all.if(
        v => Shared.List.same_set(~String, ~String.eq, os, ns),
        Bool.not(List.is_empty(&2, String, os))
      ),
      v => Act.put(
        Some{os},
        [],
        Replicas.Tree.put(
          ~Requests.Ask.machine(),
          ~d,
          l,
          Replicas.Tip.content(t),
          Key.owner(),
          Some{Codes.Code.text(g, [])}
        )
      ),
      v => Some{Replicas.Act.Stale{}}
      )
    ),
    u => None{}
  )

# what the change ch of the request i does at the tip t of the branch b (none:
# the store itself): each change by its rule, on the line where it belongs;
# any other is refused
def Change.act(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  b: Maybe<&2, String>,
  i: Ledgers.Id,
  ch: Requests.Change
) -> Maybe<&2, Replicas.Act>:
  match b ch:
    case Some{x} Requests.Change.Write{n, base, c}:
      Write.act(~d, l, t, n, base, c)
    case Some{x} Requests.Change.Resolve{k, n, c}:
      Resolve.act(~d, l, t, k, n, c)
    case Some{x} Requests.Change.Merge{from, base}:
      Merge.act(~d, l, t, i, from, base)
    case Some{x} Requests.Change.Move{to}:
      Move.act(~d, l, to)
    case Some{x} Requests.Change.Mark{m, text}:
      Some{Replicas.Act.Label{m}}
    case None{} Requests.Change.Branch{n, at}:
      Branch.act(~d, l, t, n, at)
    case None{} Requests.Change.Group{g, ms}:
      Group.act(~d, l, t, g, ms)
    case None{} Requests.Change.Key{n, k}:
      Key.act(~d, l, t, n, k)
    case y Requests.Change.Own{g, at, os}:
      Own.act(~d, l, t, g, at, os)
    case y z:
      Some{Replicas.Act.Stale{}}

# what the request q of the ID i does at the tip t of the line c: a change of
# the line of its store that c is; a request that starts a store, or that is
# of another line, is refused
def Ask.act(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  c: Ledgers.Line,
  i: Ledgers.Id,
  q: Requests.Ask
) -> Maybe<&2, Replicas.Act>:
  match q:
    case Requests.Ask.Start{vs}:
      Some{Replicas.Act.Stale{}}
    case Requests.Ask.On{st, +b, ch}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Ledgers.Line.is_eq(Ledgers.Line{st, b}, c),
        u => Change.act(~d, l, t, b, i, ch),
        u => Some{Replicas.Act.Stale{}}
      )

# Answers
# -------

# what a node answers to a change (README, Vend Writer). Written: its branch
# took it, and it is a version. Conflicted: a merge, or a resolve of one,
# after which resources still clash (the merge). Pending: its owners did not
# decide it yet. Stale: its owners refused it at their newest version.
# Refused: its ID names another change
type Answer is Data:
  Answer.Written{}
  Answer.Conflicted{merge: Ledgers.Id}
  Answer.Pending{}
  Answer.Stale{}
  Answer.Refused{}

# Written, or Conflicted while a resource still clashes after the merge k;
# Pending while l lacks a node of the clashes
def Answer.merged.of(m: Maybe<&2, Bool>, +k: Ledgers.Id) -> Answer:
  match m:
    case None{}:
      Answer.Pending{}
    case Some{c}:
      Shared.Bool.when(Answer, c, u => Answer.Conflicted{k}, u => Answer.Written{})

# Answer.merged.of, once l tells whether a resource of the tree h still
# clashes after the merge k
def Answer.merged(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, +k: Ledgers.Id) -> Answer:
  Answer.merged.of(Clash.left(~d, l, h, k), k)

# the answer to the change q of the request i, which its branch took, when
# the content of the branch is h
def Answer.taken(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  i: Ledgers.Id,
  q: Requests.Ask
) -> Answer:
  match q:
    case Requests.Ask.On{st, b, Requests.Change.Merge{v, base}}:
      Answer.merged(~d, l, h, i)
    case Requests.Ask.On{st, b, Requests.Change.Resolve{k, n, x}}:
      Answer.merged(~d, l, h, k)
    case _:
      Answer.Written{}

# the answer to the request i of the change q, whose entry has the hash a, by
# the outcome o of its ID at the tip t of its line: Pending while there is
# none; Refused when the ID names another entry
def Answer.out(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  i: Ledgers.Id,
  q: Requests.Ask,
  a: Hashes.Hash,
  o: Maybe<&2, Replicas.Out>
) -> Answer:
  match o:
    case None{}:
      Answer.Pending{}
    case Some{Replicas.Out.Stale{x}}:
      Shared.Bool.when(Answer, Hashes.Hash.is_eq(x, a), u => Answer.Stale{}, u => Answer.Refused{})
    case Some{Replicas.Out.Taken{x, n}}:
      Shared.Bool.when(
        Answer,
        Hashes.Hash.is_eq(x, a),
        u => Answer.taken(~d, l, Replicas.Tip.content(t), i, q),
        u => Answer.Refused{}
      )

# the answer to the request i of the change q on a line whose newest tip is m
# (none: the line has no start yet)
def Answer.at(
  ~d: Led(),
  +l: L(d),
  +i: Ledgers.Id,
  q: Requests.Ask,
  a: Hashes.Hash,
  m: Maybe<&2, Replicas.Tip>
) -> Answer:
  match m:
    case None{}:
      Answer.Pending{}
    case Some{+t}:
      Answer.out(~d, l, t, i, q, a, Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i))

# the answer to the request i of the change q, by how it arrives: a store
# that starts is Written at once
def Answer.of(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  i: Ledgers.Id,
  +q: Requests.Ask,
  a: Hashes.Hash,
  w: Replicas.Arrival
) -> Answer:
  match w:
    case Replicas.Arrival.Starts{vs}:
      Answer.Written{}
    case Replicas.Arrival.Waits{c}:
      Answer.at(~d, l, i, q, a, Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c))

# what a node whose ledger is l answers to the change q of the request i, at
# the time (none: the ledger does not hold the request)
def Node.answer(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +i: Ledgers.Id,
  +time: String,
  +q: Requests.Ask
) -> Maybe<&2, Answer>:
  Shared.Maybe.when(
    Answer,
    Replicas.Led.has(~Requests.Ask.machine(), ~d, l, Ledgers.Entry.Ask{i, time, q}),
    u => Some{
      Answer.of(
        ~d,
        ~kern,
        l,
        i,
        q,
        Ledgers.Name.hash(
          Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})
        ),
        Requests.Ask.arrival(q)
      )
    }
  )

# the answer m may come after the answer a: Pending may become any answer;
# Stale and Refused are final; a taken change stays taken (Written and
# Conflicted may follow each other: a merge is Conflicted while resources
# clash, and it is the same merge)
def Answer.follows(a: Answer, m: Maybe<&2, Answer>) -> Bool:
  match a m:
    case Answer.Pending{} Some{b}:
      True{}
    case Answer.Written{} Some{Answer.Written{}}:
      True{}
    case Answer.Written{} Some{Answer.Conflicted{k}}:
      True{}
    case Answer.Conflicted{k} Some{Answer.Written{}}:
      True{}
    case Answer.Conflicted{k} Some{Answer.Conflicted{k2}}:
      Ledgers.Id.is_eq(k, k2)
    case Answer.Stale{} Some{Answer.Stale{}}:
      True{}
    case Answer.Refused{} Some{Answer.Refused{}}:
      True{}
    case x y:
      False{}

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
def Draft.content(b: Branch, n: Resources.Name, q: Requests.Ask) -> Maybe<&2, Requests.Content>:
  match b q:
    case Branch{st, x} Requests.Ask.On{st2, Some{x2}, Requests.Change.Write{m, base, c}}:
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
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +b: Branch,
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
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  m: Draft
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match m:
    case Draft{time, r, c}:
      Content.find(~d, l, t, n, c)

# the root that the draft m gives the resource n, else what k gives
def Draft.or(
  ~d: Led(),
  l: L(d),
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
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  w: String,
  b: Branch,
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
    u => Res.find(~d, l, Replicas.Tip.content(t), n)
  )

# the root of the resource n at the version i of the branch whose newest tip
# is t
def Version.read(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  i: Ledgers.Id,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Maybe<&2, Hashes.Hash>,
    Maybe<&2, Requests.Res>,
    Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i),
    h => Res.find(~d, l, h, n)
  )

# the root of what the writer w reads of the resource n at the point p, whose
# branch has the newest tip t
def Point.read(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +t: Replicas.Tip,
  w: String,
  n: Resources.Name,
  p: Point
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match p:
    case Point.Head{b}:
      Head.read(~d, l, t, w, b, n)
    case Point.At{b, i}:
      Version.read(~d, l, t, i, n)
    case Point.Mark{b, m}:
      Maybe.bind(
        &2,
        Ledgers.Id,
        Maybe<&2, Requests.Res>,
        Replicas.Tip.label(~Requests.Ask.machine(), ~d, l, t, m),
        i => Version.read(~d, l, t, i, n)
      )

# the branch of the point p
def Point.branch(p: Point) -> Branch:
  match p:
    case Point.Head{b}:
      b
    case Point.At{b, i}:
      b
    case Point.Mark{b, m}:
      b

# the resource that the writer w reads as n at the point p (none: the
# ledger lacks a part; some none: it is not there)
def Node.find(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  w: String,
  n: Resources.Name,
  +p: Point
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Maybe<&2, Requests.Res>,
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, Branch.line(Point.branch(p))),
    t => Point.read(~d, ~kern, l, t, w, n, p)
  )

# the bytes that the writer w reads of the resource n at the point p (none:
# the resource is not there, or the ledger lacks a part)
def Node.read(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  w: String,
  n: Resources.Name,
  +p: Point
) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Texts.Bytes(),
    Node.find(~d, ~kern, l, w, n, p),
    m => Res.bytes(~d, l, m)
  )

# What a front lists
# ------------------
# Each is a read of the ledger. A clear def may walk a tree or a history: the
# cost of a fast one is what it gives, not what the node holds.

# the newest tip of the branch b
def Branch.head(~d: Led(), ~kern: Kern(d), l: L(d), b: Branch) -> Maybe<&2, Replicas.Tip>:
  Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, Branch.line(b))

# k versions of the branch b, from the number n, in order: a reader asks for
# a part of a history (none: l lacks a part)
def Node.versions(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  b: Branch,
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
      Maybe.bind(&2, Requests.Res, Resources.Name, Res.found(Some{v}), r => Res.name(k))

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
      Shared.Maybe.cons(Resources.Name, Res.name(k), Keys.names(rest))

# the resources of the tree whose root is h
def Tree.resources(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Resources.Name>, Res.names, Tree.range(~d, l, h, [0]))

# the resources of the branch b at its head
def Node.resources(~d: Led(), ~kern: Kern(d), +l: L(d), b: Branch) -> Maybe<&2, List<&2, Resources.Name>>:
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
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
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.group(g))
    )
  )

# the bytes of the resource m, empty when it is not there (none: l lacks a
# node)
def Res.bytes.or_empty(~d: Led(), l: L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case None{}:
      Some{[]}
    case Some{x}:
      Root.bytes(~d, l, Res.root(x))

# Res.diff once the hash m of the format to read with is known (none: neither
# resource is there)
def Res.diff.of(
  ~d: Led(),
  +l: L(d),
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
        Format.at(~d, l, h),
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
def Res.diff(~d: Led(), +l: L(d), +a: Maybe<&2, Requests.Res>, +b: Maybe<&2, Requests.Res>) -> Maybe<&2, List<&2, Formats.Change>>:
  Res.diff.of(~d, l, a, b, Res.format.of(b, a))

# what changed in the resource n from the point a to the point b, as the
# writer w reads them, in the format of the resource: a resource that is not
# there is empty (none: l lacks a part)
def Node.diff(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +w: String,
  +n: Resources.Name,
  +a: Point,
  b: Point
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
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Maybe<&2, Ledgers.Id>}

# the entry of the branch b, whose newest tip is m (none: l lacks a part)
def BranchEntry.of(~d: Led(), l: L(d), b: Branch, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, BranchEntry>:
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
def Branches.of(+st: Hashes.Hash, ns: List<&2, String>) -> List<&2, Branch>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      Branch{st, n} <> Branches.of(st, rest)

# the branches of the store st, by the log of its newest tip m (none: l
# lacks the tip or a node of the log, so a read cannot tell)
def Store.branches(~d: Led(), l: L(d), +st: Hashes.Hash, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, List<&2, Branch>>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.map(
        &2,
        List<&2, Trees.Binding>,
        List<&2, Branch>,
        xs => Branches.of(st, Branches.names(xs)),
        Tree.range(~d, l, Replicas.Tip.log(t), [5])
      )

# the entries of the branches bs (none: l lacks the head of one)
def Branches.entries(~d: Led(), ~kern: Kern(d), +l: L(d), bs: List<&2, Branch>) -> Maybe<&2, List<&2, BranchEntry>>:
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
def Node.branches(~d: Led(), ~kern: Kern(d), +l: L(d), +st: Hashes.Hash) -> Maybe<&2, List<&2, BranchEntry>>:
  Maybe.bind(
    &2,
    List<&2, Branch>,
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
  ~d: Led(),
  +l: L(d),
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
        Res.find(~d, l, h, n),
        m => Names.first.at(m, n, u => Names.first(~d, l, h, rest))
      )

# each resource under the first candidate cs, when the import brings all of
# its target (br), else none
def Import.under(
  ~d: Led(),
  l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
        Res.format(~d, l, x),
        f => Maybe.bind(
          &2,
          Texts.Bytes(),
          List<&2, Resources.Name>,
          Root.bytes(~d, l, Res.root(x)),
          bs => Imports.names(~d, l, view, h, n, Formats.Format.uses(f, [bs]))
        )
      )

# what the resource n imports directly, in the tree whose root is h, as its
# format reads it: each import found as its language finds it (nothing while
# l lacks the resource)
def Res.imports(
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name
) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    List<&2, Resources.Name>,
    Res.find(~d, l, h, n),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
    from: Branch,
    version: Ledgers.Id,
    changed: Resources.Name,
    branch: Branch,
    used: Resources.Name
  }

# a and b are branches of one store, and not the same branch
def Branch.other(a: Branch, b: Branch) -> Bool:
  match a b:
    case Branch{s1, n1} Branch{s2, n2}:
      List.all.if(u => Bool.not(String.eq(n1, n2)), Hashes.Hash.is_eq(s1, s2))

# whether what the resource n holds in the tree h is not what it holds in
# the tree h2 (none: l lacks a node of either, so a read cannot tell)
def Res.differs(
  ~d: Led(),
  +l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name
) -> Maybe<&2, Bool>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Bool,
    Res.find(~d, l, h, n),
    a => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Bool,
      Res.find(~d, l, h2, n),
      b => Some{Bool.not(Res.same(a, b))}
    )
  )

# a version that changed a resource, and the time of its request
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the versions among xs that changed the resource n, the first of which came
# after the tree h0, at the tip t (none: l lacks a part)
def Log.entries(
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  n: Resources.Name,
  b: Branch,
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
def Version.wrote(~d: Led(), +l: L(d), +t: Replicas.Tip, +m: U32, +n: Resources.Name) -> Maybe<&2, Bool>:
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
  ~d: Led(),
  +l: L(d),
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
                Res.find(~d, l, hb, used),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  from: Branch,
  v: Ledgers.Id,
  +c: Resources.Name,
  b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  from: Branch,
  +tf: Replicas.Tip,
  b: Branch,
  tb: Replicas.Tip
) -> Maybe<&2, List<&2, Touch>>:
  +hb = Replicas.Tip.content(tb)
  Maybe.bind(
    &2,
    List<&2, Trees.Binding>,
    List<&2, Touch>,
    Tree.range(~d, l, hb, [0]),
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
  ~d: Led(),
  l: L(d),
  +view: List<&2, Formats.Cond>,
  from: Branch,
  tf: Replicas.Tip,
  b: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +b: Branch
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
def Branch.is_eq(a: Branch, b: Branch) -> Bool:
  match a b:
    case Branch{s1, n1} Branch{s2, n2}:
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
def Touch.branch(x: Touch) -> Branch:
  match x:
    case Touch{f, v, c, b, u}:
      b

# the changes of each of the branches es that touch what the branch b uses
def Branches.touch(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  es: List<&2, BranchEntry>,
  +b: Branch
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +b: Branch
) -> Maybe<&2, List<&2, Touch>>:
  match b:
    case Branch{+st, +n}:
      Maybe.bind(
        &2,
        List<&2, BranchEntry>,
        List<&2, Touch>,
        Node.branches(~d, ~kern, l, st),
        es => Branches.touch(~d, ~kern, l, view, es, Branch{st, n})
      )

# what the changes of the branch from touch in each of the branches es
def Branches.touched(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
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
def Node.impact(~d: Led(), ~kern: Kern(d), +l: L(d), +b: Branch) -> Maybe<&2, List<&2, Touch>>:
  match b:
    case Branch{+st, +n}:
      Maybe.bind(
        &2,
        List<&2, BranchEntry>,
        List<&2, Touch>,
        Node.branches(~d, ~kern, l, st),
        es => Branches.touched(~d, ~kern, l, [], Branch{st, n}, es)
      )

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, the changes elsewhere that touch it in the build of a view, or the
# lies of the nodes in a store
type Topic is Data:
  Topic.Versions{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Affects{branch: Branch, view: List<&2, Formats.Cond>}
  Topic.Lies{store: Hashes.Hash}

# an event of a topic. Lied: the node holds the proof that a node signed two
# ballots with one key in the store
type Notice is Data:
  Notice.Versioned{branch: Branch, version: Ledgers.Id}
  Notice.Conflicted{branch: Branch, version: Ledgers.Id}
  Notice.Touched{touch: Touch}
  Notice.Lied{store: Hashes.Hash, node: String}

# a notice of each of the versions ids of the branch b
def Notices.versions(+b: Branch, ids: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match ids:
    case Nil{}:
      []
    case Con{i, rest}:
      Notice.Versioned{b, i} <> Notices.versions(b, rest)

# a notice of each of the versions ids of the branch b after which a resource
# of the tree h still clashes
def Notices.conflicts(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
        Clash.left(~d, l, h, i),
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
def Notices.branch(~d: Led(), +l: L(d), +b: Branch, all: Bool, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, List<&2, Notice>>:
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
def Node.notices(~d: Led(), ~kern: Kern(d), +l: L(d), x: Topic) -> Maybe<&2, List<&2, Notice>>:
  match x:
    case Topic.Versions{+b}:
      Notices.branch(~d, l, b, True{}, Branch.head(~d, ~kern, l, b))
    case Topic.Conflicts{+b}:
      Notices.branch(~d, l, b, False{}, Branch.head(~d, ~kern, l, b))
    case Topic.Affects{b, view}:
      Maybe.map(&2, List<&2, Touch>, List<&2, Notice>, Notices.touches, Node.affects(~d, ~kern, l, view, b))
    case Topic.Lies{+st}:
      Some{Notices.lies(st, Ledgers.Kind.liars(Requests.Ask, Replicas.Led.kind(Requests.Ask.machine(), d))(l)(st))}

# Mounts
# ------

# the resources mounted to a node: the branch of each, by the key of its URI.
# A resource is mounted to one branch at a time: to mount it to another is a
# checkout, and to mount another resource to another branch is a worktree
def Mounts() -> Data:
  Crits.Dict(Branch)

# a node may stop: it is forced to, or no resource is mounted and no writer
# is connected
def Node.may_stop(mounts: Mounts(), writers: Crits.Dict(Unit), force: Bool) -> Bool:
  Bool.or(
    force,
    Bool.and(Crits.Dict.is_empty(Branch, mounts), Crits.Dict.is_empty(Unit, writers))
  )

# the change that records what a resource held when it is mounted: a write
# of the resource x since the newest version, when the branch does not hold
# it at its tip t (some none: nothing to record; none: l lacks a part, so a
# read cannot tell). The node keeps the bytes and the format of x before it
# asks
def Mount.change(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +x: Requests.Res
) -> Maybe<&2, Maybe<&2, Requests.Change>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Maybe<&2, Requests.Change>,
    Res.find(~d, l, Replicas.Tip.content(t), n),
    m => Maybe.map(
      &2,
      Maybe<&2, Ledgers.Id>,
      Maybe<&2, Requests.Change>,
      v => Shared.Maybe.when(
        Requests.Change,
        Bool.not(Res.same(m, Some{x})),
        u => Some{Requests.Change.Write{n, v, Requests.Content.New{x}}}
      ),
      Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t)
    )
  )

# Owners that follow their group
# ------------------------------

# the name of the owner group of the line whose tip is t, if it has one
def Tip.group(~d: Led(), l: L(d), t: Replicas.Tip) -> Maybe<&2, String>:
  Codes.Code.whole.of(
    ~String,
    ~Codes.Code.text,
    ~Codes.Code.text.read,
    Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.owner())
  )

# the request that makes the nodes ns of the group g the owners of the line c,
# by the tree of the tip ts of its store: its ID is the count of the store, so
# every node asks for the same request
def Own.request(
  c: Ledgers.Line,
  +ts: Replicas.Tip,
  g: String,
  ns: List<&2, String>,
  v: Ledgers.Id
) -> Replicas.Request<Requests.Ask>:
  match c:
    case Ledgers.Line{st, b}:
      Replicas.Request{
        Ledgers.Id{"", Nat.show(U32.to_nat(Replicas.Tip.count(ts)))},
        "",
        Requests.Ask.On{
          st,
          b,
          Requests.Change.Own{
            g,
            Some{Requests.Source{Requests.Ref{None{}, v}, Replicas.Tip.content(ts)}},
            ns
          }
        }
      }

# Own.due once the nodes ns of the owner group g are known: a request when
# they are not the owners at the tip t, and there is one at least
def Own.due.of(
  c: Ledgers.Line,
  t: Replicas.Tip,
  ts: Replicas.Tip,
  g: String,
  +ns: List<&2, String>,
  v: Ledgers.Id
) -> Maybe<&2, Replicas.Request<Requests.Ask>>:
  Shared.Maybe.when(
    Replicas.Request<Requests.Ask>,
    List.all.if(
      u => Bool.not(List.is_empty(&2, String, ns)),
      Bool.not(Shared.List.same_set(~String, ~String.eq, ns, Replicas.Tip.voters(t)))
    ),
    u => Some{Own.request(c, ts, g, ns, v)}
  )

# Own.due once the newest tips t of the line and ts of its store are known
def Own.due.at(
  ~d: Led(),
  +l: L(d),
  c: Ledgers.Line,
  +t: Replicas.Tip,
  +ts: Replicas.Tip
) -> Maybe<&2, Replicas.Request<Requests.Ask>>:
  Maybe.bind(
    &2,
    String,
    Replicas.Request<Requests.Ask>,
    Tip.group(~d, l, t),
    +g => Maybe.bind(
      &2,
      Maybe<&2, Ledgers.Id>,
      Replicas.Request<Requests.Ask>,
      Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, ts),
      mv => Maybe.bind(
        &2,
        Ledgers.Id,
        Replicas.Request<Requests.Ask>,
        mv,
        v => Maybe.bind(
          &2,
          List<&2, String>,
          Replicas.Request<Requests.Ask>,
          Group.nodes(~d, l, Replicas.Tip.content(ts), g),
          ns => Own.due.of(c, t, ts, g, ns, v)
        )
      )
    )
  )

# the request that a node asks by itself for the line c: when the nodes of
# the owner group of c, in the newest tree of its store, are not the owners
# of c, the request that makes them the owners. So a change of a group
# changes the owners of each line that it owns, by the next decided step
def Own.due(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +c: Ledgers.Line
) -> Maybe<&2, Replicas.Request<Requests.Ask>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Replicas.Request<Requests.Ask>,
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c),
    +t => Maybe.bind(
      &2,
      Replicas.Tip,
      Replicas.Request<Requests.Ask>,
      Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, Replicas.Line.root(c)),
      ts => Own.due.at(~d, l, c, t, ts)
    )
  )

# The kernel of Vend
# ------------------

# that the kernel kern obeys the rules of Vend: what it does with a request
# is what Ask.act says, and what it asks by itself is what Own.due says
def Kernel.Rules(-d: Led(), -kern: Kern(d)) -> Type:
  (
    @l: L(
      d
    ) -> @t: Replicas.Tip -> @c: Ledgers.Line -> @i: Ledgers.Id -> @q: Requests.Ask -> {
      Replicas.Kernel.change(Requests.Ask.machine(), d, kern)(l)(t)(c)(i)(q)
        == Ask.act(~d, l, t, c, i, q): Maybe<&2, Replicas.Act>
    }
  )
    & (
      @l: L(
        d
      ) -> @c: Ledgers.Line -> {
        Replicas.Kernel.follow(Requests.Ask.machine(), d, kern)(l)(c)
          == Own.due(~d, ~kern, l, c): Maybe<&2, Replicas.Request<Requests.Ask>>
      }
    )

# the kernel of Vend: a kernel, and the proof that it obeys the rules
def Kernel(-d: Led()) -> Type:
  &kern: Kern(d) -> Kernel.Rules(d, kern)

# the acts of the rules of Vend stay as the ledger grows: each rule reads the
# ledger and the tip of its line, and waits for what it lacks
law Ask.act_stable:
  for ~d: Led()
  Replicas.Kernel.Stable(Requests.Ask.machine(), d, l => t => c => i => q => Ask.act(~d, l, t, c, i, q))

# Laws
# ----

# Answer.merged follows itself: a clash that is open or shut after the merge k
# gives Conflicted or Written, and both may follow each other
def Answer.merged_follows.at(
  p: Bool,
  p2: Bool,
  +k: Ledgers.Id
) -> {
  Answer.follows(
    Shared.Bool.when(Answer, p, u => Answer.Conflicted{k}, u => Answer.Written{}),
    Some{Shared.Bool.when(Answer, p2, u => Answer.Conflicted{k}, u => Answer.Written{})}
  )
    == True{}: Bool
}:
  match p p2:
    case True{} True{}:
      Ledgers.Id.is_eq_refl(k)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Answer.merged follows itself once the reads of the clashes (m, m2) are
# known: a read that told, tells in the next
def Answer.merged_follows.of(
  m: Maybe<&2, Bool>,
  m2: Maybe<&2, Bool>,
  +k: Ledgers.Id,
  kn: {Maybe.is_some(&2, Bool, m) == True{}: Bool} -> {Maybe.is_some(&2, Bool, m2) == True{}: Bool}
) -> {Answer.follows(Answer.merged.of(m, k), Some{Answer.merged.of(m2, k)}) == True{}: Bool}:
  match m m2:
    case None{} y:
      {==}
    case Some{p} None{}:
      Empty.absurd(
        {Answer.follows(Answer.merged.of(Some{p}, k), Some{Answer.merged.of(None{}, k)}) == True{}: Bool},
        Shared.Bool.false_ne_true(kn({==}))
      )
    case Some{+p} Some{+p2}:
      Answer.merged_follows.at(p, p2, k)

# that a read of the clashes of a merge that told in the first ledger and tree
# tells in the second
def Answer.Known(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, l2: L(d), h2: Maybe<&2, Hashes.Hash>) -> Type:
  @k: Ledgers.Id -> {Maybe.is_some(&2, Bool, Clash.left(~d, l, h, k)) == True{}: Bool} -> {
    Maybe.is_some(&2, Bool, Clash.left(~d, l2, h2, k)) == True{}: Bool
  }

# Answer.merged follows itself at another ledger and tree
def Answer.merged_follows(
  ~d: Led(),
  l: L(d),
  l2: L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  kn: Answer.Known(~d, l, h, l2, h2)
) -> {Answer.follows(Answer.merged(~d, l, h, k), Some{Answer.merged(~d, l2, h2, k)}) == True{}: Bool}:
  Answer.merged_follows.of(Clash.left(~d, l, h, k), Clash.left(~d, l2, h2, k), k, kn(k))

# Answer.taken follows itself at another ledger and tree: the merge that a
# change names is its own
def Answer.taken_follows(
  ~d: Led(),
  l: L(d),
  l2: L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  kn: Answer.Known(~d, l, h, l2, h2)
) -> {Answer.follows(Answer.taken(~d, l, h, i, q), Some{Answer.taken(~d, l2, h2, i, q)}) == True{}: Bool}:
  match q:
    case Requests.Ask.Start{os}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Branch{n, at}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Group{n, ms}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Own{g, at, os}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Write{n, base, x}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Resolve{k, n, x}}:
      Answer.merged_follows(~d, l, l2, h, h2, k, kn)
    case Requests.Ask.On{st, b, Requests.Change.Merge{v, base}}:
      Answer.merged_follows(~d, l, l2, h, h2, i, kn)
    case Requests.Ask.On{st, b, Requests.Change.Move{v}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Mark{m, text}}:
      {==}
    case Requests.Ask.On{st, b, Requests.Change.Key{n, k}}:
      {==}

# Answer.out follows itself once it is known whether the entry of the outcome
# is the request (p): Stale and Refused are final
def Answer.out_follows.stale(
  +p: Bool
) -> {
  Answer.follows(
    Shared.Bool.when(Answer, p, u => Answer.Stale{}, u => Answer.Refused{}),
    Some{Shared.Bool.when(Answer, p, u => Answer.Stale{}, u => Answer.Refused{})}
  )
    == True{}: Bool
}:
  match p:
    case True{}:
      {==}
    case False{}:
      {==}

# Answer.out follows itself for a taken outcome once it is known whether the
# entry of the outcome is the request (p)
def Answer.out_follows.taken(
  ~d: Led(),
  l: L(d),
  l2: L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +p: Bool,
  kn: Answer.Known(~d, l, h, l2, h2)
) -> {
  Answer.follows(
    Shared.Bool.when(Answer, p, u => Answer.taken(~d, l, h, i, q), u => Answer.Refused{}),
    Some{Shared.Bool.when(Answer, p, u => Answer.taken(~d, l2, h2, i, q), u => Answer.Refused{})}
  )
    == True{}: Bool
}:
  match p:
    case True{}:
      Answer.taken_follows(~d, l, l2, h, h2, i, q, kn)
    case False{}:
      {==}

# Answer.out follows itself for one outcome, at another ledger and tip: a
# request that has an outcome keeps its answer, but for the clash of a merge
def Answer.out_follows(
  ~d: Led(),
  l: L(d),
  l2: L(d),
  t: Replicas.Tip,
  t2: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  o: Maybe<&2, Replicas.Out>,
  kn: Answer.Known(~d, l, Replicas.Tip.content(t), l2, Replicas.Tip.content(t2))
) -> {
  Answer.follows(Answer.out(~d, l, t, i, q, a, o), Some{Answer.out(~d, l2, t2, i, q, a, o)}) == True{}: Bool
}:
  match o:
    case None{}:
      {==}
    case Some{Replicas.Out.Stale{x}}:
      Answer.out_follows.stale(Hashes.Hash.is_eq(x, a))
    case Some{Replicas.Out.Taken{x, n}}:
      Answer.out_follows.taken(
        ~d,
        l,
        l2,
        Replicas.Tip.content(t),
        Replicas.Tip.content(t2),
        i,
        q,
        Hashes.Hash.is_eq(x, a),
        kn
      )

# Answer.at follows itself once the outcome is read from two words (g1 at the
# first tip, g2 at the second) and g2 holds what g1 does
def Answer.at_follows.words(
  ~d: Led(),
  l: L(d),
  l2: L(d),
  t: Replicas.Tip,
  t2: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  g1: Maybe<&2, List<&2, U32>>,
  g2: Maybe<&2, List<&2, U32>>,
  keep: @ws: List<&2, U32> -> {g1 == Some{ws}: Maybe<&2, List<&2, U32>>} -> {g2 == Some{ws}: Maybe<&2, List<&2, U32>>},
  kn: Answer.Known(~d, l, Replicas.Tip.content(t), l2, Replicas.Tip.content(t2))
) -> {
  Answer.follows(
    Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g1)),
    Some{
      Answer.out(~d, l2, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g2))
    }
  )
    == True{}: Bool
}:
  match g1:
    case None{}:
      {==}
    case Some{+ws}:
      %Equal.sym(Maybe<&2, List<&2, U32>>, g2, Some{ws}, keep(ws)({==})): {
        Answer.follows(
          Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws})),
          Some{
            Answer.out(~d, l2, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, _))
          }
        )
          == True{}: Bool
      }
      Answer.out_follows(~d, l, l2, t, t2, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws}), kn)

# Answer.at follows Pending: no outcome words are read at the first tip
def Answer.at_follows.pending(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +a: Hashes.Hash,
  g1: Maybe<&2, List<&2, U32>>,
  none: @ws: List<&2, U32> -> {g1 == Some{ws}: Maybe<&2, List<&2, U32>>} -> Empty
) -> {
  Answer.follows(
    Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, g1)),
    Some{Answer.Pending{}}
  )
    == True{}: Bool
}:
  match g1:
    case None{}:
      {==}
    case Some{ws}:
      Empty.absurd(
        {
          Answer.follows(
            Answer.out(~d, l, t, i, q, a, Codes.Code.whole.of(~Replicas.Out, ~Replicas.Out.code, ~Replicas.Out.code.read, Some{ws})),
            Some{Answer.Pending{}}
          )
            == True{}: Bool
        },
        none(ws)({==})
      )

# Answer.at follows itself from a tip t of the first ledger, once the words
# that t holds for the outcome of i are held by the tip m2 of the second
def Answer.at_follows.tip(
  ~d: Led(),
  +a: L(d),
  +b: L(d),
  +t: Replicas.Tip,
  +m2: Maybe<&2, Replicas.Tip>,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  keep: @ws: List<&2, U32> -> {
    Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      m2,
      t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  },
  kn: @t2: Replicas.Tip -> {m2 == Some{t2}: Maybe<&2, Replicas.Tip>} -> Answer.Known(
    ~d,
    a,
    Replicas.Tip.content(t),
    b,
    Replicas.Tip.content(t2)
  )
) -> {Answer.follows(Answer.at(~d, a, i, q, h, Some{t}), Some{Answer.at(~d, b, i, q, h, m2)}) == True{}: Bool}:
  match m2:
    case None{}:
      Answer.at_follows.pending(
        ~d,
        a,
        t,
        i,
        q,
        h,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)),
        ws => e => Shared.Maybe.none_ne_some(List<&2, U32>, ws, keep(ws)(e))
      )
    case Some{+t2}:
      Answer.at_follows.words(
        ~d,
        a,
        b,
        t,
        t2,
        i,
        q,
        h,
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)),
        Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i)),
        keep,
        kn(t2)({==})
      )

# what Replicas.Line.get_grows says of the ledger d and the kernel kern: what
# the log of a line holds under a key, it holds for good
def Answer.Stays(~d: Led(), ~kern: Kern(d)) -> Type:
  @c: Ledgers.Line -> @key: List<&2, U32> -> Shared.Read.Stable(
    L(d),
    a => b => Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
    List<&2, U32>,
    l => Replicas.Line.get(~Requests.Ask.machine(), ~d, ~kern, l, c, key)
  )

# the log of the head of the line c holds, at a later ledger, what it holds
# under the key of the outcome of i (Answer.Stays)
def Answer.at_follows.keep(
  ~d: Led(),
  ~kern: Kern(d),
  +a: L(d),
  +b: L(d),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +t: Replicas.Tip,
  +m2: Maybe<&2, Replicas.Tip>,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Answer.Stays(~d, ~kern),
  e1: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>},
  e2: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == m2: Maybe<&2, Replicas.Tip>},
  +ws: List<&2, U32>,
  hw: {Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t, Replicas.Log.out(i)) == Some{ws}: Maybe<&2, List<&2, U32>>}
) -> {
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, U32>,
    m2,
    t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
}:
  %e2: {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      _,
      t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, b, t2, Replicas.Log.out(i))
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
  stays(c)(Replicas.Log.out(i))(a)(b)(ws)(g)(
    %Equal.sym(
      Maybe<&2, Replicas.Tip>,
      Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c),
      Some{t},
      e1
    ): {
      Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, U32>,
        _,
        t2 => Replicas.Tip.get(~Requests.Ask.machine(), ~d, a, t2, Replicas.Log.out(i))
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    hw
  )

# Answer.at follows itself at the heads m1 and m2 of the line c, in two
# ledgers where the second is a later state of the first
def Answer.at_follows.head(
  ~d: Led(),
  ~kern: Kern(d),
  +a: L(d),
  +b: L(d),
  +c: Ledgers.Line,
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Answer.Stays(~d, ~kern),
  m1: Maybe<&2, Replicas.Tip>,
  +m2: Maybe<&2, Replicas.Tip>,
  +e1: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == m1: Maybe<&2, Replicas.Tip>},
  +e2: {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == m2: Maybe<&2, Replicas.Tip>},
  kn: @t: Replicas.Tip -> @t2: Replicas.Tip -> {m1 == Some{t}: Maybe<&2, Replicas.Tip>} -> {
    m2 == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Answer.follows(Answer.at(~d, a, i, q, h, m1), Some{Answer.at(~d, b, i, q, h, m2)}) == True{}: Bool}:
  match m1:
    case None{}:
      {==}
    case Some{+t}:
      Answer.at_follows.tip(
        ~d,
        a,
        b,
        t,
        m2,
        i,
        q,
        h,
        ws => hw => Answer.at_follows.keep(~d, ~kern, a, b, c, i, t, m2, g, stays, e1, e2, ws, hw),
        t2 => e2x => kn(t)(t2)({==})(e2x)
      )

# Answer.of follows itself in a later state of the ledger
def Answer.of_follows(
  ~d: Led(),
  ~kern: Kern(d),
  +a: L(d),
  +b: L(d),
  +i: Ledgers.Id,
  +q: Requests.Ask,
  +h: Hashes.Hash,
  g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Answer.Stays(~d, ~kern),
  w: Replicas.Arrival,
  kn: @c: Ledgers.Line -> @t: Replicas.Tip -> @t2: Replicas.Tip -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Answer.follows(Answer.of(~d, ~kern, a, i, q, h, w), Some{Answer.of(~d, ~kern, b, i, q, h, w)}) == True{}: Bool}:
  match w:
    case Replicas.Arrival.Starts{vs}:
      {==}
    case Replicas.Arrival.Waits{+c}:
      Answer.at_follows.head(
        ~d,
        ~kern,
        a,
        b,
        c,
        i,
        q,
        h,
        g,
        stays,
        Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c),
        Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c),
        {==},
        {==},
        t => t2 => e1 => e2 => kn(c)(t)(t2)(e1)(e2)
      )

# Node.answer follows itself once it is known whether each ledger holds the
# request (pa, pb), and the answers that they give (A1, A2) follow
def Node.answer_follows.when(
  +pa: Bool,
  +pb: Bool,
  +A1: Answer,
  +A2: Answer,
  +x: Answer,
  keep: {pa == True{}: Bool} -> {pb == True{}: Bool},
  step: {Answer.follows(A1, Some{A2}) == True{}: Bool},
  e: {Shared.Maybe.when(Answer, pa, u => Some{A1}) == Some{x}: Maybe<&2, Answer>}
) -> {Answer.follows(x, Shared.Maybe.when(Answer, pb, u => Some{A2})) == True{}: Bool}:
  match pa pb:
    case True{} True{}:
      %Shared.Maybe.some_inj(Answer, A1, x, e): {Answer.follows(_, Some{A2}) == True{}: Bool}
      step
    case True{} False{}:
      Empty.absurd({Answer.follows(x, None{}) == True{}: Bool}, Shared.Bool.false_ne_true(keep({==})))
    case False{} y:
      Empty.absurd(
        {Answer.follows(x, Shared.Maybe.when(Answer, y, u => Some{A2})) == True{}: Bool},
        Shared.Maybe.none_ne_some(Answer, x, e)
      )

# Node.answer_follows for the ledgers a and b, once Line.get_grows is known
def Node.answer_follows.go(
  ~d: Led(),
  ~kern: Kern(d),
  +a: L(d),
  +b: L(d),
  +i: Ledgers.Id,
  +time: String,
  +q: Requests.Ask,
  +x: Answer,
  +g: Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
  stays: Answer.Stays(~d, ~kern),
  e: {Node.answer(~d, ~kern, a, i, time, q) == Some{x}: Maybe<&2, Answer>},
  kn: @c: Ledgers.Line -> @t: Replicas.Tip -> @t2: Replicas.Tip -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, a, c) == Some{t}: Maybe<&2, Replicas.Tip>
  } -> {
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, b, c) == Some{t2}: Maybe<&2, Replicas.Tip>
  } -> Answer.Known(~d, a, Replicas.Tip.content(t), b, Replicas.Tip.content(t2))
) -> {Answer.follows(x, Node.answer(~d, ~kern, b, i, time, q)) == True{}: Bool}:
  Node.answer_follows.when(
    Replicas.Led.has(~Requests.Ask.machine(), ~d, a, Ledgers.Entry.Ask{i, time, q}),
    Replicas.Led.has(~Requests.Ask.machine(), ~d, b, Ledgers.Entry.Ask{i, time, q}),
    Answer.of(~d, ~kern, a, i, q, Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})), Requests.Ask.arrival(q)),
    Answer.of(~d, ~kern, b, i, q, Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})), Requests.Ask.arrival(q)),
    x,
    Replicas.Hist.has_grows(~Requests.Ask.machine(), ~d, a, b, Ledgers.Entry.Ask{i, time, q}, Replicas.Led.later_grows(~Requests.Ask.machine(), ~d, a, b)(g)),
    Answer.of_follows(
      ~d,
      ~kern,
      a,
      b,
      i,
      q,
      Ledgers.Name.hash(Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})),
      g,
      stays,
      Requests.Ask.arrival(q),
      kn
    ),
    e
  )

# the owners of a line keep each part of what they decide: the ledger holds
# the whole of the content of the newest tip of each line, its nodes and the
# format and the bytes of each of its resources
law Node.head_kept:
  for ~d: Led()
  for ~kern: Kern(d)
  for ~rules: Kernel.Rules(d, kern)
  for l: L(d)
  for c: Ledgers.Line
  for t: Replicas.Tip
  {Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c) == Some{t}: Maybe<&2, Replicas.Tip>}
    -> {Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}

# answers only move forward: as the ledger grows, and while its ballots are
# honest, a request that a node answers stays answered; Stale and Refused are
# final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for ~d: Led()
  for ~kern: Kern(d)
  for rules: Kernel.Rules(d, kern)
  for i: Ledgers.Id
  for time: String
  for q: Requests.Ask
  Shared.Read.Forward(
    L(d),
    a => b => Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
    Answer,
    x => m => {Answer.follows(x, m) == True{}: Bool},
    l => Node.answer(~d, ~kern, l, i, time, q)
  )


# Merging, one tree at a time
# ---------------------------
# Lemmas for the two laws below. They read the ledger d only by its laws: a
# write changes its key and no other, and what a taken act writes reads back.

# both A and B, as Data: a proof of it may be used as often as a proof needs
def Merge.And(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# the nodes ns2 are the nodes ns, then others
def Merge.Nodes(-ns: List<&2, List<&2, U32>>, -ns2: List<&2, List<&2, U32>>) -> Data:
  Sigma<&2, &2, List<&2, List<&2, U32>>, ex => {ns2 == List.append(&2, List<&2, U32>, ns, ex): List<&2, List<&2, U32>>}>

# the add law of the laws of a ledger
def Merge.get_add.of(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledgers.Ledger.Kind(Q),
  laws: Ledgers.Ledger.Laws(Q, c, k)
) -> Ledgers.Laws.GetAdd(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, rest}}:
      ga

# a ledger with one more entry holds what it held, and the entry when its name
# was free
def Merge.get_add(~d: Led()) -> Ledgers.Laws.GetAdd(
  Requests.Ask,
  Replicas.Machine.code(Requests.Ask.machine()),
  Replicas.Led.kind(Requests.Ask.machine(), d)
):
  Merge.get_add.of(
    Requests.Ask,
    Replicas.Machine.code(Requests.Ask.machine()),
    Replicas.Led.kind(Requests.Ask.machine(), d),
    Replicas.Led.laws(Requests.Ask.machine(), d)
  )

# the entry e, when it is under the name n
def Merge.new_entry(~d: Led(), +e: Ledgers.Entry<Requests.Ask>, n: Ledgers.Name) -> Maybe<&2, Ledgers.Entry<Requests.Ask>>:
  Shared.Maybe.when(
    Ledgers.Entry<Requests.Ask>,
    Ledgers.Name.is_eq(Ledgers.Entry.name(~Requests.Ask, ~Replicas.Machine.code(Requests.Ask.machine()), e), n),
    u => Some{e}
  )

# what a read finds first, it finds before what comes after
def Merge.or_keeps(
  -A: Data,
  a: Maybe<&2, A>,
  b: Maybe<&2, A>,
  x: A,
  e: {a == Some{x}: Maybe<&2, A>}
) -> {Maybe.or(&2, A, a, b) == Some{x}: Maybe<&2, A>}:
  %Equal.sym(Maybe<&2, A>, a, Some{x}, e): {Maybe.or(&2, A, _, b) == Some{x}: Maybe<&2, A>}
  {==}

# a ledger that gets some data, then some more, is a ledger that gets both
def Merge.puts_append(
  ~d: Led(),
  as: List<&2, List<&2, U32>>,
  +bs: List<&2, List<&2, U32>>,
  +l: L(d)
) -> {
  Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, as, bs), l)
    == Replicas.Led.puts(~Requests.Ask.machine(), ~d, bs, Replicas.Led.puts(~Requests.Ask.machine(), ~d, as, l)): L(d)
}:
  match as:
    case Nil{}:
      {==}
    case Con{+ws, rest}:
      Merge.puts_append(~d, rest, bs, Replicas.Led.add(~Requests.Ask.machine(), ~d, l, Ledgers.Entry.Data{ws}))

# Merge.holds_fetch for the first words x of the list, once the checks are known
def Merge.holds_fetch.cons(
  ~d: Led(),
  +s: L(d),
  +x: List<&2, U32>,
  rest: List<&2, List<&2, U32>>,
  +w: List<&2, U32>,
  +q: Bool,
  +p: Bool,
  hq: {
    Depots.Depot.has(~L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, x) == q: Bool
  },
  hp: {Shared.List.is_eq(~U32, ~U32.is_eq, x, w) == p: Bool},
  h: {
    List.all.if(
      u => Depots.Depot.holds(~L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, rest),
      q
    )
      == True{}: Bool
  },
  c: {
    List.any.if(
      u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, w),
      p
    )
      == True{}: Bool
  },
  ih: {
    Depots.Depot.holds(~L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, rest) == True{}: Bool
  } -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, w) == True{}: Bool
  } -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}
) -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match q p:
    case True{} True{}:
      %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, w)(hp): {
        Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(_)) == Some{_}: Maybe<&2, List<&2, U32>>
      }
      Replicas.Hist.has(~Requests.Ask.machine(), ~d, s, x)(hq)
    case True{} False{}:
      ih(h)(c)
    case False{} y:
      Empty.absurd(
        {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(h)
      )

# a depot that holds each of some words gives each of them under its hash
def Merge.holds_fetch(
  ~d: Led(),
  +s: L(d),
  ns: List<&2, List<&2, U32>>,
  +w: List<&2, U32>
) -> {
  Depots.Depot.holds(~L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, ns) == True{}: Bool
} -> {
  List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ns, w) == True{}: Bool
} -> {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>}:
  match ns:
    case Nil{}:
      h => c => Empty.absurd(
        {Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, Hashes.Sha.hash(w)) == Some{w}: Maybe<&2, List<&2, U32>>},
        Shared.Bool.false_ne_true(c)
      )
    case Con{+x, +rest}:
      h => c => Merge.holds_fetch.cons(
        ~d,
        s,
        x,
        rest,
        w,
        Depots.Depot.has(~L(d), ~(s2 => y => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s2, y)), s, x),
        Shared.List.is_eq(~U32, ~U32.is_eq, x, w),
        {==},
        {==},
        h,
        c,
        Merge.holds_fetch(~d, s, rest, w)
      )

# the ledger of the work w
def Merge.ledger(~d: Led(), w: Work<L(d)>) -> L(d):
  match w:
    case Work{l, h, ns}:
      l

# the tree of the work w
def Merge.root(~d: Led(), w: Work<L(d)>) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{l, h, ns}:
      h

# the nodes that the work w added
def Merge.nodes(~d: Led(), w: Work<L(d)>) -> List<&2, List<&2, U32>>:
  match w:
    case Work{l, h, ns}:
      ns

# no nodes are no more nodes
def Merge.nodes_refl(+ns: List<&2, List<&2, U32>>) -> Merge.Nodes(ns, ns):
  (
    [],
    Equal.sym(
      List<&2, List<&2, U32>>,
      List.append(&2, List<&2, U32>, ns, []),
      ns,
      Shared.List.append_nil(List<&2, U32>, ns)
    )
  )

# the nodes after the nodes after a are the nodes after a
def Merge.nodes_trans(
  +a: List<&2, List<&2, U32>>,
  +b: List<&2, List<&2, U32>>,
  +c: List<&2, List<&2, U32>>,
  x: Merge.Nodes(a, b),
  y: Merge.Nodes(b, c)
) -> Merge.Nodes(a, c):
  (+ex1, p1) = x
  (+ex2, p2) = y
  (
    List.append(&2, List<&2, U32>, ex1, ex2),
    %Shared.List.append_assoc(List<&2, U32>, a, ex1, ex2): {c == _: List<&2, List<&2, U32>>}
    %p1: {c == List.append(&2, List<&2, U32>, _, ex2): List<&2, List<&2, U32>>}
    p2
  )

# the nodes after a and the nodes ne are nodes after a
def Merge.nodes_drop(
  +a: List<&2, List<&2, U32>>,
  +ne: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(List.append(&2, List<&2, U32>, a, ne), N)
) -> Merge.Nodes(a, N):
  (+ex, pe) = nd
  (
    List.append(&2, List<&2, U32>, ne, ex),
    %Shared.List.append_assoc(List<&2, U32>, a, ne, ex): {N == _: List<&2, List<&2, U32>>}
    pe
  )

# the nodes after a are those after b, when a is b
def Merge.nodes_cast(
  +a: List<&2, List<&2, U32>>,
  +a2: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  e: {a == a2: List<&2, List<&2, U32>>},
  nd: Merge.Nodes(a, N)
) -> Merge.Nodes(a2, N):
  %e: Merge.Nodes(_, N)
  nd

# a node among those that come after a and the nodes ne is among those that
# come after
def Merge.nodes_contains(
  +a: List<&2, List<&2, U32>>,
  +ne: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(List.append(&2, List<&2, U32>, a, ne), N),
  +w: List<&2, U32>,
  c: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ne, w) == True{}: Bool}
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), N, w) == True{}: Bool}:
  (+ex, pe) = nd
  %Equal.sym(
    List<&2, List<&2, U32>>,
    N,
    List.append(&2, List<&2, U32>, List.append(&2, List<&2, U32>, a, ne), ex),
    pe
  ): {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), _, w) == True{}: Bool}
  Shared.List.contains_left(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    List.append(&2, List<&2, U32>, a, ne),
    ex,
    w,
    Shared.List.contains_right(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), a, ne, w, c)
  )

# a ledger that gets the nodes ns, from the one that gets the nodes ps, grows
# from it
def Merge.grows_of(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +lf: L(d),
  +ps: List<&2, List<&2, U32>>,
  +ns: List<&2, List<&2, U32>>,
  wc: {lc == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l): L(d)},
  wf: {lf == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l): L(d)},
  nd: Merge.Nodes(ps, ns)
) -> Replicas.Led.Grows(Requests.Ask.machine(), d, lc, lf):
  (+ex, pe) = nd
  %Equal.sym(L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l), wc): Replicas.Led.Grows(Requests.Ask.machine(), d, _, lf)
  %Equal.sym(L(d), lf, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), wf): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    _
  )
  %Equal.sym(List<&2, List<&2, U32>>, ns, List.append(&2, List<&2, U32>, ps, ex), pe): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l)
  )
  %Equal.sym(
    L(d),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, ps, ex), l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ex, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l)),
    Merge.puts_append(~d, ps, ex, l)
  ): Replicas.Led.Grows(
    Requests.Ask.machine(),
    d,
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l),
    _
  )
  Replicas.Hist.puts(~Requests.Ask.machine(), ~d, ex, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l))

# what a write of the key kw to the value m, to the tree hc, gives in the ledger
# lf: the new tree h1 reads the key as written, and each other key as hc did
def Merge.Writes(
  ~d: Led(),
  lf: L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> Type:
  {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, kw) == Trees.Look.of(m): Trees.Look}
    & (
      @k2: List<&2, U32> -> @x: Maybe<&2, List<&2, U32>> -> {Shared.List.is_eq(~U32, ~U32.is_eq, kw, k2) == False{}: Bool} -> {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    )

# the data of the ledger lf that holds the nodes N are the nodes N
def Merge.Held(~d: Led(), lf: L(d), N: List<&2, List<&2, U32>>) -> Data:
  {
    Depots.Depot.holds(~L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lf, N) == True{}: Bool
  }

# the ledger lc is the ledger l with the nodes ps
def Merge.Puts(~d: Led(), l: L(d), lc: L(d), ps: List<&2, List<&2, U32>>) -> Data:
  {lc == Replicas.Led.puts(~Requests.Ask.machine(), ~d, ps, l): L(d)}

# the work after a write of the edit e is the work of its ledger, tree and nodes
def Merge.put_work(
  ~d: Led(),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> {
  Work{
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
    Trees.Edit.root(e),
    List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
  }
    == W1: Work<L(d)>
}:
  Shared.Maybe.some_inj(
    Work<L(d)>,
    Work{
      Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
      Trees.Edit.root(e),
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
    },
    W1,
    e1
  )

# the tree of the work after a write of the edit e is the tree of e
def Merge.put_root(
  ~d: Led(),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> {Trees.Edit.root(e) == Merge.root(~d, W1): Maybe<&2, Hashes.Hash>}:
  Equal.cong(
    Work<L(d)>,
    Maybe<&2, Hashes.Hash>,
    w => Merge.root(~d, w),
    Work{
      Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
      Trees.Edit.root(e),
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
    },
    W1,
    Merge.put_work(~d, lc, P, e, W1, e1)
  )

# the nodes of the work after a write of the edit e are those before it, and
# the nodes of e
def Merge.put_nodes(
  ~d: Led(),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +e: Trees.Edit,
  +W1: Work<L(d)>,
  e1: {Work.put(~d, lc, P, Some{e}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +N: List<&2, List<&2, U32>>,
  nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Nodes(List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), N):
  Merge.nodes_cast(
    Merge.nodes(~d, W1),
    List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)),
    N,
    Equal.sym(
      List<&2, List<&2, U32>>,
      List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)),
      Merge.nodes(~d, W1),
      Equal.cong(
        Work<L(d)>,
        List<&2, List<&2, U32>>,
        w => Merge.nodes(~d, w),
        Work{
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), lc),
          Trees.Edit.root(e),
          List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e))
        },
        W1,
        Merge.put_work(~d, lc, P, e, W1, e1)
      )
    ),
    nd
  )

# the work W1 is the work after a write of the key kw to the value m, to the
# tree hc of the work with the ledger lc and the nodes P, when the ledger lf
# holds the nodes N that come after those of W1
def Merge.set_core(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +kw: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  p: Maybe<&2, Trees.Edit>,
  +ep: {Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, kw, m) == p: Maybe<&2, Trees.Edit>},
  +e1: {Work.put(~d, lc, P, p) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Writes(~d, lf, Merge.root(~d, W1), hc, kw, m):
  match p:
    case None{}:
      Empty.absurd(Merge.Writes(~d, lf, Merge.root(~d, W1), hc, kw, m), Shared.Maybe.none_ne_some(Work<L(d)>, W1, e1))
    case Some{+e}:
      %Merge.put_root(~d, lc, P, e, W1, e1): Merge.Writes(~d, lf, _, hc, kw, m)
      Replicas.Hist.write(Requests.Ask.machine(), d)(lc)(lf)(hc)(kw)(m)(e)(ep)(
        Merge.grows_of(~d, l, lc, lf, P, N, wc, wf, Merge.nodes_drop(P, Trees.Edit.nodes(e), N, Merge.put_nodes(~d, lc, P, e, W1, e1, N, nd)))
      )(+w => c => Merge.holds_fetch(~d, lf, N, w)(held)(Merge.nodes_contains(P, Trees.Edit.nodes(e), N, Merge.put_nodes(~d, lc, P, e, W1, e1, N, nd), w, c)))

# the work after a write has the ledger of the nodes that it has, and its nodes
# come after those before it
def Merge.set_facts.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  p: Maybe<&2, Trees.Edit>,
  +e1: {Work.put(~d, lc, P, p) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match p:
    case None{}:
      Empty.absurd(
        Merge.And(
          Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
          Merge.Nodes(P, Merge.nodes(~d, W1))
        ),
        Shared.Maybe.none_ne_some(Work<L(d)>, W1, e1)
      )
    case Some{+e}:
      %Merge.put_work(~d, lc, P, e, W1, e1): Merge.And(
        Merge.Puts(~d, l, Merge.ledger(~d, _), Merge.nodes(~d, _)),
        Merge.Nodes(P, Merge.nodes(~d, _))
      )
      (
        %Equal.sym(L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l), wc): {
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), _)
            == Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), l): L(d)
        }
        Equal.sym(
          L(d),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, Trees.Edit.nodes(e)), l),
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(e), Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l)),
          Merge.puts_append(~d, P, Trees.Edit.nodes(e), l)
        ),
        (Trees.Edit.nodes(e), {==})
      )

# the work after a write of the key kw to the value m has the ledger of the
# nodes that it has, and its nodes come after those before it
def Merge.set_facts(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +kw: List<&2, U32>,
  +m: Maybe<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +e1: {Work.set(~d, Work{lc, hc, P}, kw, m) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  Merge.set_facts.at(
    ~d,
    l,
    lc,
    P,
    W1,
    Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, kw, m),
    e1,
    wc
  )

# the key written is the key read, when the write is read
def Merge.writes_hit(
  ~d: Led(),
  lf: L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m)
) -> {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, kw) == Trees.Look.of(m): Trees.Look}:
  match wr:
    case Tuple{hit, frame}:
      hit

# a key other than the key written is read as before, when the write is read
def Merge.writes_frame(
  ~d: Led(),
  lf: L(d),
  h1: Maybe<&2, Hashes.Hash>,
  hc: Maybe<&2, Hashes.Hash>,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  k2: List<&2, U32>,
  x: Maybe<&2, List<&2, U32>>,
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, k2) == False{}: Bool},
  kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, k2) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match wr:
    case Tuple{hit, frame}:
      frame(k2)(x)(hk)(kn)

# the ledger of a work that gets more nodes is the ledger of the nodes that it
# has
def Merge.keep_puts(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +ms: List<&2, List<&2, U32>>,
  wc: Merge.Puts(~d, l, lc, P)
) -> Merge.Puts(
  ~d,
  l,
  Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, lc),
  List.append(&2, List<&2, U32>, P, ms)
):
  %Equal.sym(L(d), lc, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l), wc): {
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, _)
      == Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, ms), l): L(d)
  }
  Equal.sym(
    L(d),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, List.append(&2, List<&2, U32>, P, ms), l),
    Replicas.Led.puts(~Requests.Ask.machine(), ~d, ms, Replicas.Led.puts(~Requests.Ask.machine(), ~d, P, l)),
    Merge.puts_append(~d, P, ms, l)
  )

# the facts about the work after a pick that makes nodes, from those of the
# write that follows them
def Merge.pick_facts.make(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +P: List<&2, List<&2, U32>>,
  +ms: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  f: Merge.And(
    Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
    Merge.Nodes(List.append(&2, List<&2, U32>, P, ms), Merge.nodes(~d, W1))
  )
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  (+a, nd) = f
  (
    a,
    Merge.nodes_trans(P, List.append(&2, List<&2, U32>, P, ms), Merge.nodes(~d, W1), (ms, {==}), nd)
  )

# the facts about the work after a clash, once the clashes that are open are
# read (mc)
def Merge.pick_facts.clash.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<L(d)>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Key.clashes(k), Clash.value(Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match mc:
    case None{}:
      Empty.absurd(
        Merge.And(
          Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
          Merge.Nodes(P, Merge.nodes(~d, W1))
        ),
        Shared.Maybe.none_ne_some(Work<L(d)>, W1, eb)
      )
    case Some{+cs}:
      Merge.set_facts(~d, l, lc, hc, P, Key.clashes(k), Clash.value(Clash.put(n, cs)), W1, eb, wc)

# the facts about the work after a clash
def Merge.pick_facts.clash(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<L(d)>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Clash.names(~d, lc, hc, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Clash{}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  Merge.pick_facts.clash.at(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    W1,
    mc,
    %emc: {
      Maybe.bind(
        &2,
        List<&2, Resources.Name>,
        Work<L(d)>,
        _,
        cs => Work.set(~d, Work{lc, hc, P}, Key.clashes(k), Clash.value(Clash.put(n, cs)))
      )
        == Some{W1}: Maybe<&2, Work<L(d)>>
    }
    e1,
    wc
  )

# what a pick of a merge gives the work: the ledger of the nodes that it has,
# and nodes that come after those before it
def Merge.pick_facts(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  p: Pick,
  +W1: Work<L(d)>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match p:
    case Pick.Take{x}:
      Merge.set_facts(~d, l, lc, hc, P, Key.res(n), Res.value(x), W1, e1, wc)
    case Pick.Make{+h, +bytes}:
      Merge.pick_facts.make(
        ~d,
        l,
        lc,
        P,
        Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)),
        W1,
        Merge.set_facts(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Key.res(n),
          Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          W1,
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc)
        )
      )
    case Pick.Clash{}:
      Merge.pick_facts.clash(~d, l, lc, hc, P, k, n, W1, Clash.names(~d, lc, hc, k), {==}, e1, wc)

# the tree of the work after a take reads the resource as taken
def Merge.take_hit(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: Maybe<&2, Requests.Res>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Take{x}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n)) == Trees.Look.of(Res.value(x)): Trees.Look
}:
  Merge.writes_hit(
    ~d,
    lf,
    Merge.root(~d, W1),
    hc,
    Key.res(n),
    Res.value(x),
    Merge.set_core(
      ~d,
      l,
      lc,
      hc,
      P,
      Key.res(n),
      Res.value(x),
      lf,
      N,
      W1,
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Key.res(n), Res.value(x)),
      {==},
      e1,
      wc,
      wf,
      held,
      nd
    )
  )

# a pick that clashes leaves the key of a resource as it was, once the clashes
# that are open are read (mc)
def Merge.pick_frame.clash.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Key.clashes(k), Clash.value(Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match mc:
    case None{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Maybe.none_ne_some(Work<L(d)>, W1, eb)
      )
    case Some{+cs}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Key.clashes(k),
        Clash.value(Clash.put(n, cs)),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Key.clashes(k),
          Clash.value(Clash.put(n, cs)),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Key.clashes(k), Clash.value(Clash.put(n, cs))),
          {==},
          eb,
          wc,
          wf,
          held,
          nd
        ),
        Key.res(n0),
        v,
        {==},
        kn
      )

# what a pick of a merge does to the key of a resource n0 that it does not
# write: it reads as it did
def Merge.pick_frame(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  p: Pick,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Shared.List.is_eq(~U32, ~U32.is_eq, Key.res(n), Key.res(n0)) == False{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match p:
    case Pick.Take{+x}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Key.res(n),
        Res.value(x),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Key.res(n),
          Res.value(x),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Key.res(n), Res.value(x)),
          {==},
          e1,
          wc,
          wf,
          held,
          nd
        ),
        Key.res(n0),
        v,
        hk,
        kn
      )
    case Pick.Make{+h, +bytes}:
      Merge.writes_frame(
        ~d,
        lf,
        Merge.root(~d, W1),
        hc,
        Key.res(n),
        Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
        Merge.set_core(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Key.res(n),
          Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          lf,
          N,
          W1,
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
            hc,
            Key.res(n),
            Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}})
          ),
          {==},
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc),
          wf,
          held,
          nd
        ),
        Key.res(n0),
        v,
        hk,
        kn
      )
    case Pick.Clash{}:
      Merge.pick_frame.clash.at(
        ~d,
        l,
        lc,
        hc,
        P,
        k,
        n,
        n0,
        W1,
        lf,
        N,
        Clash.names(~d, lc, hc, k),
        e1,
        wc,
        wf,
        held,
        nd,
        v,
        kn
      )

# Merge.one once the pick of the three reads is known (mp)
def Merge.one.p(
  ~d: Led(),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.bind(&2, Pick, Work<L(d)>, mp, p => Merge.pick(~d, w, k, n, p))

# Merge.one once the read of theirs is known (mt)
def Merge.one.t(
  ~d: Led(),
  +l: L(d),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<L(d)>,
    mt,
    t => Merge.one.p(~d, w, k, n, Pick.merge(~d, l, b, o, t))
  )

# Merge.one once the read of ours is known (mo)
def Merge.one.o(
  ~d: Led(),
  +l: L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<L(d)>,
    mo,
    +o => Merge.one.t(~d, l, w, k, n, b, o, Res.find(~d, l, ht, n))
  )

# Merge.one once the read of the base is known (mb)
def Merge.one.b(
  ~d: Led(),
  +l: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Work<L(d)>,
    mb,
    +b => Merge.one.o(~d, l, ht, w, k, n, b, Res.find(~d, l, ho, n))
  )

# the reads and the pick of a merge of a resource, that gave the work W1
def Merge.Read.p(
  ~d: Led(),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>,
  W1: Work<L(d)>
) -> Data:
  Sigma<&2, &2, Pick, p => Merge.And({mp == Some{p}: Maybe<&2, Pick>}, {Merge.pick(~d, w, k, n, p) == Some{W1}: Maybe<&2, Work<L(d)>>})>

def Merge.Read.t(
  ~d: Led(),
  +l: L(d),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, t => Merge.And({mt == Some{t}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.p(~d, w, k, n, Pick.merge(~d, l, b, o, t), W1))>

def Merge.Read.o(
  ~d: Led(),
  +l: L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, o => Merge.And({mo == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.t(~d, l, w, k, n, b, o, Res.find(~d, l, ht, n), W1))>

def Merge.Read.b(
  ~d: Led(),
  +l: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  W1: Work<L(d)>
) -> Data:
  Sigma<&2, &2, Maybe<&2, Requests.Res>, b => Merge.And({mb == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}, Merge.Read.o(~d, l, ht, w, k, n, b, Res.find(~d, l, ho, n), W1))>

def Merge.read.p(
  ~d: Led(),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mp: Maybe<&2, Pick>,
  +W1: Work<L(d)>,
  e: {Merge.one.p(~d, w, k, n, mp) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> Merge.Read.p(~d, w, k, n, mp, W1):
  match mp:
    case None{}:
      Empty.absurd(Merge.Read.p(~d, w, k, n, None{}, W1), Shared.Maybe.none_ne_some(Work<L(d)>, W1, e))
    case Some{+p}:
      (p, ({==}, e))

def Merge.read.t(
  ~d: Led(),
  +l: L(d),
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  mt: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  e: {Merge.one.t(~d, l, w, k, n, b, o, mt) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> Merge.Read.t(~d, l, w, k, n, b, o, mt, W1):
  match mt:
    case None{}:
      Empty.absurd(Merge.Read.t(~d, l, w, k, n, b, o, None{}, W1), Shared.Maybe.none_ne_some(Work<L(d)>, W1, e))
    case Some{+t}:
      (t, ({==}, Merge.read.p(~d, w, k, n, Pick.merge(~d, l, b, o, t), W1, e)))

def Merge.read.o(
  ~d: Led(),
  +l: L(d),
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  mo: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  e: {Merge.one.o(~d, l, ht, w, k, n, b, mo) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> Merge.Read.o(~d, l, ht, w, k, n, b, mo, W1):
  match mo:
    case None{}:
      Empty.absurd(Merge.Read.o(~d, l, ht, w, k, n, b, None{}, W1), Shared.Maybe.none_ne_some(Work<L(d)>, W1, e))
    case Some{+o}:
      (o, ({==}, Merge.read.t(~d, l, w, k, n, b, o, Res.find(~d, l, ht, n), W1, e)))

# the reads and the pick of a merge of a resource that gave the work W1
def Merge.read(
  ~d: Led(),
  +l: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  w: Work<L(d)>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  e: {Merge.one.b(~d, l, ho, ht, w, k, n, mb) == Some{W1}: Maybe<&2, Work<L(d)>>}
) -> Merge.Read.b(~d, l, ho, ht, w, k, n, mb, W1):
  match mb:
    case None{}:
      Empty.absurd(Merge.Read.b(~d, l, ho, ht, w, k, n, None{}, W1), Shared.Maybe.none_ne_some(Work<L(d)>, W1, e))
    case Some{+b}:
      (b, ({==}, Merge.read.o(~d, l, ht, w, k, n, b, Res.find(~d, l, ho, n), W1, e)))

# what a merge of a resource gives the work: the ledger of the nodes that it
# has, and nodes that come after those before it
def Merge.one_facts.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<L(d)>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +wc: Merge.Puts(~d, l, lc, P),
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_facts(~d, l, lc, hc, P, k, n, p, W1, e, wc)

# what a merge of a resource that does not write the key of the resource n0
# does to it: nothing
def Merge.one_frame.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Shared.List.is_eq(~U32, ~U32.is_eq, Key.res(n), Key.res(n0)) == False{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_frame(~d, l, lc, hc, P, k, n, n0, p, W1, lf, N, e, wc, wf, held, nd, hk, v, kn)

# the merge of the same reads is the same pick
def Merge.merge_args(
  ~d: Led(),
  +l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  eb: {b == b0: Maybe<&2, Requests.Res>},
  eo: {o == o0: Maybe<&2, Requests.Res>},
  et: {t == t0: Maybe<&2, Requests.Res>}
) -> {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, o0, t0): Maybe<&2, Pick>}:
  %et: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, o0, _): Maybe<&2, Pick>}
  %eo: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, b0, _, t): Maybe<&2, Pick>}
  %eb: {Pick.merge(~d, l, b, o, t) == Pick.merge(~d, l, _, o, t): Maybe<&2, Pick>}
  {==}

# the pick of a merge of a resource, as its premises say: the reads are those
# of the premises, so the pick is
def Merge.pick_same(
  ~d: Led(),
  +l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +t: Maybe<&2, Requests.Res>,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +p: Pick,
  +q: Pick,
  eb: {b == b0: Maybe<&2, Requests.Res>},
  eo: {o == o0: Maybe<&2, Requests.Res>},
  et: {t == t0: Maybe<&2, Requests.Res>},
  ep: {Pick.merge(~d, l, b, o, t) == Some{p}: Maybe<&2, Pick>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{q}: Maybe<&2, Pick>}
) -> {p == q: Pick}:
  Shared.Maybe.some_inj(
    Pick,
    p,
    q,
    Equal.trans(
      Maybe<&2, Pick>,
      Some{p},
      Pick.merge(~d, l, b, o, t),
      Some{q},
      Equal.sym(Maybe<&2, Pick>, Pick.merge(~d, l, b, o, t), Some{p}, ep),
      Equal.trans(
        Maybe<&2, Pick>,
        Pick.merge(~d, l, b, o, t),
        Pick.merge(~d, l, b0, o0, t0),
        Some{q},
        Merge.merge_args(~d, l, b, o, t, b0, o0, t0, eb, eo, et),
        hp
      )
    )
  )

# the tree of the work after the merge of the resource n reads it as taken,
# when its reads and its pick are those that the premises say
def Merge.one_hit.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  hb0: {mb == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n)) == Trees.Look.of(Res.value(x)): Trees.Look
}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.take_hit(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    x,
    W1,
    lf,
    N,
      %Merge.pick_same(
        ~d,
        l,
        b,
        o,
        t,
        b0,
        o0,
        t0,
        p,
        Pick.Take{x},
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          b,
          b0,
          Equal.trans(Maybe<&2, Maybe<&2, Requests.Res>>, Some{b}, mb, Some{b0}, Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, mb, Some{b}, eb), hb0)
        ),
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          o,
          o0,
          Equal.trans(
            Maybe<&2, Maybe<&2, Requests.Res>>,
            Some{o},
            Res.find(~d, l, ho, n),
            Some{o0},
            Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Res.find(~d, l, ho, n), Some{o}, eo),
            ho0
          )
        ),
        Shared.Maybe.some_inj(
          Maybe<&2, Requests.Res>,
          t,
          t0,
          Equal.trans(
            Maybe<&2, Maybe<&2, Requests.Res>>,
            Some{t},
            Res.find(~d, l, ht, n),
            Some{t0},
            Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Res.find(~d, l, ht, n), Some{t}, et),
            ht0
          )
        ),
        ep,
        hp
      ): {Merge.pick(~d, Work{lc, hc, P}, k, n, _) == Some{W1}: Maybe<&2, Work<L(d)>>}
      e,
    wc,
    wf,
    held,
    nd
  )

# the name of the key of a resource is the name
def Merge.key_name(+n: Resources.Name) -> {Res.name(Key.res(n)) == Some{n}: Maybe<&2, Resources.Name>}:
  Codes.Code.whole_read(
    ~Resources.Name,
    ~Resources.Name.code,
    ~Resources.Name.code.read,
    ~(x => r => Resources.Name.code_read(x, r)),
    n
  )

# a first word that is not zero is not the first word of the key of a resource
def Merge.head_nonzero(
  w: Word(32n),
  t: List<&2, U32>,
  +n: Resources.Name,
  nz: {Shared.Word.is_zero(32n, w) == False{}: Bool},
  hh: {Res.name(U32{w} <> t) == Some{n}: Maybe<&2, Resources.Name>}
) -> Empty:
  match w:
    case WCon{True{}, w2}:
      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
    case WCon{False{}, w2}:
      match w2:
        case WCon{True{}, w3}:
          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
        case WCon{False{}, w3}:
          match w3:
            case WCon{True{}, w4}:
              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
            case WCon{False{}, w4}:
              match w4:
                case WCon{True{}, w5}:
                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                case WCon{False{}, w5}:
                  match w5:
                    case WCon{True{}, w6}:
                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                    case WCon{False{}, w6}:
                      match w6:
                        case WCon{True{}, w7}:
                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                        case WCon{False{}, w7}:
                          match w7:
                            case WCon{True{}, w8}:
                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                            case WCon{False{}, w8}:
                              match w8:
                                case WCon{True{}, w9}:
                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                case WCon{False{}, w9}:
                                  match w9:
                                    case WCon{True{}, w10}:
                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                    case WCon{False{}, w10}:
                                      match w10:
                                        case WCon{True{}, w11}:
                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                        case WCon{False{}, w11}:
                                          match w11:
                                            case WCon{True{}, w12}:
                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                            case WCon{False{}, w12}:
                                              match w12:
                                                case WCon{True{}, w13}:
                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                case WCon{False{}, w13}:
                                                  match w13:
                                                    case WCon{True{}, w14}:
                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                    case WCon{False{}, w14}:
                                                      match w14:
                                                        case WCon{True{}, w15}:
                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                        case WCon{False{}, w15}:
                                                          match w15:
                                                            case WCon{True{}, w16}:
                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                            case WCon{False{}, w16}:
                                                              match w16:
                                                                case WCon{True{}, w17}:
                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                case WCon{False{}, w17}:
                                                                  match w17:
                                                                    case WCon{True{}, w18}:
                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                    case WCon{False{}, w18}:
                                                                      match w18:
                                                                        case WCon{True{}, w19}:
                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                        case WCon{False{}, w19}:
                                                                          match w19:
                                                                            case WCon{True{}, w20}:
                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                            case WCon{False{}, w20}:
                                                                              match w20:
                                                                                case WCon{True{}, w21}:
                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                case WCon{False{}, w21}:
                                                                                  match w21:
                                                                                    case WCon{True{}, w22}:
                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                    case WCon{False{}, w22}:
                                                                                      match w22:
                                                                                        case WCon{True{}, w23}:
                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                        case WCon{False{}, w23}:
                                                                                          match w23:
                                                                                            case WCon{True{}, w24}:
                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                            case WCon{False{}, w24}:
                                                                                              match w24:
                                                                                                case WCon{True{}, w25}:
                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                case WCon{False{}, w25}:
                                                                                                  match w25:
                                                                                                    case WCon{True{}, w26}:
                                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                    case WCon{False{}, w26}:
                                                                                                      match w26:
                                                                                                        case WCon{True{}, w27}:
                                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                        case WCon{False{}, w27}:
                                                                                                          match w27:
                                                                                                            case WCon{True{}, w28}:
                                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                            case WCon{False{}, w28}:
                                                                                                              match w28:
                                                                                                                case WCon{True{}, w29}:
                                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                case WCon{False{}, w29}:
                                                                                                                  match w29:
                                                                                                                    case WCon{True{}, w30}:
                                                                                                                      Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                    case WCon{False{}, w30}:
                                                                                                                      match w30:
                                                                                                                        case WCon{True{}, w31}:
                                                                                                                          Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                        case WCon{False{}, w31}:
                                                                                                                          match w31:
                                                                                                                            case WCon{True{}, w32}:
                                                                                                                              Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                            case WCon{False{}, w32}:
                                                                                                                              match w32:
                                                                                                                                case WCon{True{}, w33}:
                                                                                                                                  Shared.Maybe.none_ne_some(Resources.Name, n, hh)
                                                                                                                                case WCon{False{}, w33}:
                                                                                                                                  match w33:
                                                                                                                                    case WNil{}:
                                                                                                                                      Shared.Bool.true_ne_false(nz)

# a key that has a name is the key of that resource, once it is known whether
# its first word is zero (b)
def Merge.name_key.at(
  +w: Word(32n),
  +r: List<&2, U32>,
  +n: Resources.Name,
  +b: Bool,
  +eb: {Shared.Word.is_zero(32n, w) == b: Bool},
  +h: {Res.name(U32{w} <> r) == Some{n}: Maybe<&2, Resources.Name>}
) -> {U32{w} <> r == Key.res(n): List<&2, U32>}:
  match b:
    case True{}:
      %Equal.sym(
        Word(32n),
        w,
        Word.zero(32n),
        Shared.Word.is_zero_eq(32n, w)(eb)
      ): {U32{_} <> r == Key.res(n): List<&2, U32>}
      %Codes.Code.whole_back(
        ~Resources.Name,
        ~Resources.Name.code,
        ~Resources.Name.code.read,
        r,
        n
      )(
        %Shared.Word.is_zero_eq(32n, w)(eb): {Res.name(U32{_} <> r) == Some{n}: Maybe<&2, Resources.Name>}
        h
      ): {U32{Word.zero(32n)} <> _ == Key.res(n): List<&2, U32>}
      {==}
    case False{}:
      Empty.absurd({U32{w} <> r == Key.res(n): List<&2, U32>}, Merge.head_nonzero(w, r, n, eb, h))

# a key that has a name is the key of the resource of that name
def Merge.name_key(
  y: List<&2, U32>,
  +n: Resources.Name
) -> {Res.name(y) == Some{n}: Maybe<&2, Resources.Name>} -> {y == Key.res(n): List<&2, U32>}:
  match y:
    case Nil{}:
      h => Empty.absurd({Nil{} == Key.res(n): List<&2, U32>}, Shared.Maybe.none_ne_some(Resources.Name, n, h))
    case Con{U32{+w}, +r}:
      h => Merge.name_key.at(w, r, n, Shared.Word.is_zero(32n, w), {==}, h)

# the work after the merge of the key x: the work, or what the merge of the
# resource that the key names gives
def Merge.next(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +w: Work<L(d)>,
  mn: Maybe<&2, Resources.Name>
) -> Maybe<&2, Work<L(d)>>:
  match mn:
    case None{}:
      Some{w}
    case Some{+n}:
      Merge.one(~d, l, hb, ho, ht, k, n, w)

# the work that Merge.all goes on with after the key x
def Merge.step(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  x: List<&2, U32>,
  +w: Work<L(d)>
) -> Maybe<&2, Work<L(d)>>:
  Maybe.default(
    &2,
    Maybe<&2, Work<L(d)>>,
    Maybe.bind(
      &2,
      Resources.Name,
      Maybe<&2, Work<L(d)>>,
      Res.name(x),
      n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
    ),
    Some{w}
  )

# a step is the work that the name of its key gives, once it is read (mn)
def Merge.step_eq.at(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +w: Work<L(d)>,
  mn: Maybe<&2, Resources.Name>
) -> {
  Maybe.default(
    &2,
    Maybe<&2, Work<L(d)>>,
    Maybe.bind(
      &2,
      Resources.Name,
      Maybe<&2, Work<L(d)>>,
      mn,
      n => Some{Merge.one(~d, l, hb, ho, ht, k, n, w)}
    ),
    Some{w}
  )
    == Merge.next(~d, l, hb, ho, ht, k, w, mn): Maybe<&2, Work<L(d)>>
}:
  match mn:
    case None{}:
      {==}
    case Some{+n}:
      {==}

# the work that a merge goes on with after a key is the next work
def Merge.step_eq(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  x: List<&2, U32>,
  +w: Work<L(d)>
) -> {Merge.step(~d, l, hb, ho, ht, k, x, w) == Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)): Maybe<&2, Work<L(d)>>}:
  Merge.step_eq.at(~d, l, hb, ho, ht, k, w, Res.name(x))

# a merge that gave a work went on with a work
def Merge.all_from(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  m: Maybe<&2, Work<L(d)>>,
  +Wf: Work<L(d)>,
  e: {Merge.all(~d, l, hb, ho, ht, k, xs, m) == Some{Wf}: Maybe<&2, Work<L(d)>>}
) -> Sigma<&2, &2, Work<L(d)>, W1 => {m == Some{W1}: Maybe<&2, Work<L(d)>>}>:
  match xs m:
    case Nil{} y:
      (Wf, e)
    case Con{x, rest} None{}:
      Empty.absurd(
        Sigma<&2, &2, Work<L(d)>, W1 => {None{} == Some{W1}: Maybe<&2, Work<L(d)>>}>,
        Shared.Maybe.none_ne_some(Work<L(d)>, Wf, e)
      )
    case Con{x, rest} Some{+w}:
      (w, {==})

# the merge of the key x went on, from the work w, with a work W1: the merge of
# the keys after it went on from W1 to Wf
def Merge.Stepped(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<L(d)>,
  +Wf: Work<L(d)>
) -> Data:
  Sigma<&2, &2, Work<L(d)>, W1 => Merge.And({Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Wf}: Maybe<&2, Work<L(d)>>}, {Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>})>

# a merge that went on after a key, from the work w, went on with the work W1
def Merge.all_step.at(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<L(d)>,
  +Wf: Work<L(d)>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, x <> rest, Some{w}) == Some{Wf}: Maybe<&2, Work<L(d)>>},
  sg: Sigma<&2, &2, Work<L(d)>, W1 => {Merge.step(~d, l, hb, ho, ht, k, x, w) == Some{W1}: Maybe<&2, Work<L(d)>>}>
) -> Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, w, Wf):
  (+W1, +es) = sg
  (
    W1,
    (
      %es: {Merge.all(~d, l, hb, ho, ht, k, rest, _) == Some{Wf}: Maybe<&2, Work<L(d)>>}
      e,
      Equal.trans(
        Maybe<&2, Work<L(d)>>,
        Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)),
        Merge.step(~d, l, hb, ho, ht, k, x, w),
        Some{W1},
        Equal.sym(
          Maybe<&2, Work<L(d)>>,
          Merge.step(~d, l, hb, ho, ht, k, x, w),
          Merge.next(~d, l, hb, ho, ht, k, w, Res.name(x)),
          Merge.step_eq(~d, l, hb, ho, ht, k, x, w)
        ),
        es
      )
    )
  )

# a merge that went on after a key went on with a work
def Merge.all_step(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +w: Work<L(d)>,
  +Wf: Work<L(d)>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, x <> rest, Some{w}) == Some{Wf}: Maybe<&2, Work<L(d)>>}
) -> Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, w, Wf):
  Merge.all_step.at(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    x,
    rest,
    w,
    Wf,
    e,
    Merge.all_from(~d, l, hb, ho, ht, k, rest, Merge.step(~d, l, hb, ho, ht, k, x, w), Wf, e)
  )

# the first of a pair of Data
def Merge.And.left(-A: Data, -B: Data, p: Merge.And(A, B)) -> A:
  match p:
    case Tuple{a, b}:
      a

# the second of a pair of Data
def Merge.And.right(-A: Data, -B: Data, p: Merge.And(A, B)) -> B:
  match p:
    case Tuple{a, b}:
      b

# what the next merge gives the work: the ledger of the nodes that it has, and
# nodes that come after those before it
def Merge.next_facts(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<L(d)>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(
  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
  Merge.Nodes(P, Merge.nodes(~d, W1))
):
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, W1, e): Merge.And(
        Merge.Puts(~d, l, Merge.ledger(~d, _), Merge.nodes(~d, _)),
        Merge.Nodes(P, Merge.nodes(~d, _))
      )
      (wc, Merge.nodes_refl(P))
    case Some{+n}:
      Merge.one_facts.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        W1,
        Res.find(~d, l, hb, n),
        wc,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e)
      )

# the merge of the key of a name writes no other key than the key of that name
def Merge.apart(mn: Maybe<&2, Resources.Name>, n0: Resources.Name) -> Bool:
  match mn:
    case None{}:
      True{}
    case Some{n}:
      Bool.not(Shared.List.is_eq(~U32, ~U32.is_eq, Key.res(n), Key.res(n0)))

# the tree of the work after the next merge reads the key of a resource n0 as
# it did, when the merge does not write it
def Merge.next_frame(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hk: {Merge.apart(mn, n0) == True{}: Bool},
  +v: Maybe<&2, List<&2, U32>>,
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, W1, e): {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, _), Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      kn
    case Some{+n}:
      Merge.one_frame.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        n0,
        Res.find(~d, l, hb, n),
        W1,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e),
        lf,
        N,
        wc,
        wf,
        held,
        nd,
        Shared.Bool.not_true(Shared.List.is_eq(~U32, ~U32.is_eq, Key.res(n), Key.res(n0)))(hk),
        v,
        kn
      )

# the tree of the work after the next merge of the resource n reads it as taken,
# when the reads and the pick are those that the premises say
def Merge.next_hit(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {
  Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n)) == Trees.Look.of(Res.value(x)): Trees.Look
}:
  Merge.one_hit.at(
    ~d,
    l,
    lc,
    ho,
    ht,
    hc,
    P,
    k,
    n,
    b0,
    o0,
    t0,
    x,
    Res.find(~d, l, hb, n),
    W1,
    Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e),
    hb0,
    ho0,
    ht0,
    hp,
    lf,
    N,
    wc,
    wf,
    held,
    nd
  )

# two merges that end in the same work end in the same ledger and the same
# nodes
def Merge.work_eq(
  ~d: Led(),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>}
) -> Merge.And({lc == lf: L(d)}, Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>})):
  (
    Equal.cong(
      Work<L(d)>,
      L(d),
      w => Merge.ledger(~d, w),
      Work{lc, hc, P},
      Work{lf, hf, N},
      Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
    ),
    (
      Equal.cong(
        Work<L(d)>,
        Maybe<&2, Hashes.Hash>,
        w => Merge.root(~d, w),
        Work{lc, hc, P},
        Work{lf, hf, N},
        Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
      ),
      Equal.cong(
        Work<L(d)>,
        List<&2, List<&2, U32>>,
        w => Merge.nodes(~d, w),
        Work{lc, hc, P},
        Work{lf, hf, N},
        Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
      )
    )
  )

# two merges that end in the same work end in the same tree
def Merge.work_eq.root(
  ~d: Led(),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>}
) -> {hc == hf: Maybe<&2, Hashes.Hash>}:
  Equal.cong(
    Work<L(d)>,
    Maybe<&2, Hashes.Hash>,
    w => Merge.root(~d, w),
    Work{lc, hc, P},
    Work{lf, hf, N},
    Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
  )

# two merges that end in the same work end in the same nodes
def Merge.work_eq.nodes(
  ~d: Led(),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Some{Work{lc, hc, P}} == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>}
) -> {P == N: List<&2, List<&2, U32>>}:
  Equal.cong(
    Work<L(d)>,
    List<&2, List<&2, U32>>,
    w => Merge.nodes(~d, w),
    Work{lc, hc, P},
    Work{lf, hf, N},
    Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, Work{lf, hf, N}, e)
  )

# the induction hypothesis of Merge.all_puts for the keys rest
def Merge.PutsIH(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  rest: List<&2, List<&2, U32>>,
  lf: L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P1, N))

# the work of a merge is the ledger of its nodes, and its nodes come after those
# of the work before, from the facts of a step and of the rest
def Merge.all_puts.fin(
  ~d: Led(),
  +l: L(d),
  +lc1: L(d),
  +lf: L(d),
  +P: List<&2, List<&2, U32>>,
  +P1: List<&2, List<&2, U32>>,
  +N: List<&2, List<&2, U32>>,
  facts: Merge.And(Merge.Puts(~d, l, lc1, P1), Merge.Nodes(P, P1)),
  ihres: Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P1, N))
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  (+a, nd1) = facts
  (+b, nd2) = ihres
  (b, Merge.nodes_trans(P, P1, N, nd1, nd2))

# Merge.all_puts for the keys x then rest, once the work W1 after the first step
# is known
def Merge.all_puts.con2(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  W1: Work<L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  ih: Merge.PutsIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  match W1:
    case Work{+lc1, +hc1, +P1}:
      Merge.all_puts.fin(
        ~d,
        l,
        lc1,
        lf,
        P,
        P1,
        N,
        Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc),
        ih(lc1)(hc1)(P1)(erest)(
          Merge.And.left(
            Merge.Puts(~d, l, lc1, P1),
            Merge.Nodes(P, P1),
            Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
          )
        )
      )

# Merge.all_puts for the keys x then rest, once the first step is known
def Merge.all_puts.con(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.PutsIH(~d, l, hb, ho, ht, k, rest, lf, hf, N)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_puts.con2(~d, l, hb, ho, ht, k, x, rest, lc, hc, P, lf, hf, N, wc, W1, erest, enext, ih)

# a merge ends in the ledger of its nodes, and its nodes come after those of
# the work that it starts from
def Merge.all_puts(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P)
) -> Merge.And(Merge.Puts(~d, l, lf, N), Merge.Nodes(P, N)):
  match xs:
    case Nil{}:
      %Merge.And.left(
        {lc == lf: L(d)},
        Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>}),
        Merge.work_eq(~d, lc, hc, P, lf, hf, N, e)
      ): Merge.And(Merge.Puts(~d, l, _, N), Merge.Nodes(P, N))
      %Merge.And.right(
        {hc == hf: Maybe<&2, Hashes.Hash>},
        {P == N: List<&2, List<&2, U32>>},
        Merge.And.right(
          {lc == lf: L(d)},
          Merge.And({hc == hf: Maybe<&2, Hashes.Hash>}, {P == N: List<&2, List<&2, U32>>}),
          Merge.work_eq(~d, lc, hc, P, lf, hf, N, e)
        )
      ): Merge.And(Merge.Puts(~d, l, lc, _), Merge.Nodes(P, _))
      (wc, Merge.nodes_refl(P))
    case Con{+x, +rest}:
      Merge.all_puts.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => Merge.all_puts(~d, l, hb, ho, ht, k, rest, lc1, hc1, P1, lf, hf, N, e1, wc1)
      )

# the merge of the key x writes no key but x, once its name is read (mn)
def Merge.apart_of.at(
  +x: List<&2, U32>,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  emn: {Res.name(x) == mn: Maybe<&2, Resources.Name>},
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n0)) == False{}: Bool}
) -> {Merge.apart(mn, n0) == True{}: Bool}:
  match mn:
    case None{}:
      {==}
    case Some{+n}:
      %Merge.name_key(x, n)(emn): {Bool.not(Shared.List.is_eq(~U32, ~U32.is_eq, _, Key.res(n0))) == True{}: Bool}
      %Equal.sym(Bool, Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n0)), False{}, hx): {Bool.not(_) == True{}: Bool}
      {==}

# the merge of a key other than the key of a resource writes no key but its own
def Merge.apart_of(
  +x: List<&2, U32>,
  +n0: Resources.Name,
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n0)) == False{}: Bool}
) -> {Merge.apart(Res.name(x), n0) == True{}: Bool}:
  Merge.apart_of.at(x, n0, Res.name(x), {==}, hx)

# a key is not in the keys x then rest, once it is known whether it is x (p)
def Merge.cons_false.at(
  +p: Bool,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  h: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K), p) == False{}: Bool
  }
) -> Merge.And(
  {p == False{}: Bool},
  {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
):
  match p:
    case True{}:
      Empty.absurd(
        Merge.And(
          {True{} == False{}: Bool},
          {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
        ),
        Shared.Bool.true_ne_false(h)
      )
    case False{}:
      ({==}, h)

# a key that is not in the keys x then rest is not x, and is not in rest
def Merge.cons_false(
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  h: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, K) == False{}: Bool}
) -> Merge.And(
  {Shared.List.is_eq(~U32, ~U32.is_eq, x, K) == False{}: Bool},
  {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == False{}: Bool}
):
  Merge.cons_false.at(Shared.List.is_eq(~U32, ~U32.is_eq, x, K), rest, K, h)

# the induction hypothesis of Merge.all_frame for the keys rest
def Merge.FrameIH(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>,
  lf: L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n0)) == False{}: Bool
  } -> {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc1, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  } -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# Merge.all_frame for the keys x then rest, once the work W1 after the first
# step is known
def Merge.all_frame.con2(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  W1: Work<L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  ih: Merge.FrameIH(~d, l, hb, ho, ht, k, n0, v, rest, lf, hf, N)
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match W1:
    case Work{+lc1, +hc1, +P1}:
      ih(lc1)(hc1)(P1)(erest)(
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
        )
      )(
        Merge.And.right(
          {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n0)) == False{}: Bool},
          {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n0)) == False{}: Bool},
          Merge.cons_false(x, rest, Key.res(n0), hx)
        )
      )(
        Merge.next_frame(
          ~d,
          l,
          lc,
          hb,
          ho,
          ht,
          hc,
          P,
          k,
          n0,
          Res.name(x),
          Work{lc1, hc1, P1},
          lf,
          N,
          enext,
          wc,
          wf,
          held,
          Merge.And.right(
            Merge.Puts(~d, l, lf, N),
            Merge.Nodes(P1, N),
            Merge.all_puts(
              ~d,
              l,
              hb,
              ho,
              ht,
              k,
              rest,
              lc1,
              hc1,
              P1,
              lf,
              hf,
              N,
              erest,
              Merge.And.left(
                Merge.Puts(~d, l, lc1, P1),
                Merge.Nodes(P, P1),
                Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
              )
            )
          ),
          Merge.apart_of(
            x,
            n0,
            Merge.And.left(
              {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n0)) == False{}: Bool},
              {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n0)) == False{}: Bool},
              Merge.cons_false(x, rest, Key.res(n0), hx)
            )
          ),
          v,
          kn
        )
      )

# Merge.all_frame for the keys x then rest, once the first step is known
def Merge.all_frame.con(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.FrameIH(~d, l, hb, ho, ht, k, n0, v, rest, lf, hf, N)
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_frame.con2(~d, l, hb, ho, ht, k, n0, v, x, rest, lc, hc, P, lf, hf, N, wc, wf, held, hx, kn, W1, erest, enext, ih)

# a merge of keys among which is not the key of a resource leaves what it reads
# as it was
def Merge.all_frame(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  xs: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), xs, Key.res(n0)) == False{}: Bool},
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match xs:
    case Nil{}:
      %Merge.work_eq.root(~d, lc, hc, P, lf, hf, N, e): {
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, _, Key.res(n0)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
      kn
    case Con{+x, +rest}:
      Merge.all_frame.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n0,
        v,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hx,
        kn,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => hx1 => kn1 => Merge.all_frame(~d, l, hb, ho, ht, k, n0, v, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hx1, kn1)
      )

# a read that finds a value is known, once the value is the written one
def Merge.known_look(
  m: Maybe<&2, List<&2, U32>>
) -> {Trees.Look.known(Trees.Look.of(m)) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      {==}

# a read that is the read of a written value is known as that value
def Merge.known_of(
  l: Trees.Look,
  m: Maybe<&2, List<&2, U32>>,
  e: {l == Trees.Look.of(m): Trees.Look}
) -> {Trees.Look.known(l) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  %Equal.sym(Trees.Look, l, Trees.Look.of(m), e): {Trees.Look.known(_) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
  Merge.known_look(m)

# the key y is the key of the resource n, once it is known that it is the key
def Merge.name_of_key(
  +y: List<&2, U32>,
  +n: Resources.Name,
  e: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Key.res(n)) == True{}: Bool}
) -> {Res.name(y) == Some{n}: Maybe<&2, Resources.Name>}:
  %Equal.sym(
    List<&2, U32>,
    y,
    Key.res(n),
    Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), y, Key.res(n))(e)
  ): {Res.name(_) == Some{n}: Maybe<&2, Resources.Name>}
  Merge.key_name(n)

# the induction hypothesis of Merge.all_take for the keys rest
def Merge.TakeIH(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: Maybe<&2, Requests.Res>,
  rest: List<&2, List<&2, U32>>,
  lf: L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> {
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)) == True{}: Bool
  } -> {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  }

# Merge.all_take once the key y is the key of the resource n, and no key after
# it is
def Merge.all_take.hit(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +lc1: L(d),
  +hc1: Maybe<&2, Hashes.Hash>,
  +P1: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wc1: Merge.Puts(~d, l, lc1, P1),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ey: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Key.res(n)) == True{}: Bool},
  +erest: {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  },
  +enext: {
    Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<L(d)>>
  },
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)) == False{}: Bool}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  Merge.all_frame(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    Res.value(x),
    rest,
    lc1,
    hc1,
    P1,
    lf,
    hf,
    N,
    erest,
    wc1,
    wf,
    held,
    ec,
    Merge.known_of(
      Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, hc1, Key.res(n)),
      Res.value(x),
      Merge.next_hit(
        ~d,
        l,
        lc,
        hb,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        Work{lc1, hc1, P1},
        lf,
        N,
        %Merge.name_of_key(y, n, ey): {
          Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, _) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<L(d)>>
        }
        enext,
        hb0,
        ho0,
        ht0,
        hp,
        wc,
        wf,
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes(P1, N),
          Merge.all_puts(~d, l, hb, ho, ht, k, rest, lc1, hc1, P1, lf, hf, N, erest, wc1)
        )
      )
    )
  )

# Merge.all_take once it is known whether the key y is the key of the resource
# n (p), and whether the keys after it hold it (c)
def Merge.all_take.cc(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +lc1: L(d),
  +hc1: Maybe<&2, Hashes.Hash>,
  +P1: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wc1: Merge.Puts(~d, l, lc1, P1),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +erest: {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  },
  +enext: {
    Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{Work{lc1, hc1, P1}}: Maybe<&2, Work<L(d)>>
  },
  +p: Bool,
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, y, Key.res(n)) == p: Bool},
  +c: Bool,
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)) == c: Bool},
  +hx: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)), p) == True{}: Bool
  },
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match p c:
    case q True{}:
      ih(lc1)(hc1)(P1)(erest)(wc1)(ec)
    case True{} False{}:
      Merge.all_take.hit(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        lc1,
        hc1,
        P1,
        wc,
        wc1,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        ep,
        erest,
        enext,
        ec
      )
    case False{} False{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)),
            True{},
            Equal.sym(
              Bool,
              List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)),
              False{},
              ec
            ),
            hx
          )
        )
      )
# Merge.all_take for the keys y then rest, once the work W1 after the first step
# is known
def Merge.all_take.con2(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), y <> rest, Key.res(n)) == True{}: Bool},
  W1: Work<L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(y)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match W1:
    case Work{+lc1, +hc1, +P1}:
      Merge.all_take.cc(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        lc1,
        hc1,
        P1,
        wc,
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(y), Work{lc1, hc1, P1}, enext, wc)
        ),
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        erest,
        enext,
        Shared.List.is_eq(~U32, ~U32.is_eq, y, Key.res(n)),
        {==},
        List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)),
        {==},
        hx,
        ih
      )

# Merge.all_take for the keys y then rest, once the first step is known
def Merge.all_take.con(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +y: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), y <> rest, Key.res(n)) == True{}: Bool},
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, y, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.TakeIH(~d, l, hb, ho, ht, k, n, x, rest, lf, hf, N)
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_take.con2(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    b0,
    o0,
    t0,
    x,
    y,
    rest,
    lc,
    hc,
    P,
    lf,
    hf,
    N,
    wc,
    wf,
    held,
    hb0,
    ho0,
    ht0,
    hp,
    hx,
    W1,
    erest,
    enext,
    ih
  )

# a merge of keys among which is the key of a resource, whose merge takes a
# side, reads the resource as that side
def Merge.all_take(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  xs: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +hx: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), xs, Key.res(n)) == True{}: Bool}
) -> {
  Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
}:
  match xs:
    case Nil{}:
      Empty.absurd(
        {
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hf, Key.res(n)) == Some{Res.value(x)}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        },
        Shared.Bool.false_ne_true(hx)
      )
    case Con{+y, +rest}:
      Merge.all_take.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        x,
        y,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hp,
        hx,
        Merge.all_step(~d, l, hb, ho, ht, k, y, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => ec => Merge.all_take(~d, l, hb, ho, ht, k, n, b0, o0, t0, x, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hb0, ho0, ht0, hp, ec)
      )
# the resource that a resource of the tree holds as a value is the resource
def Merge.found_value(+x: Maybe<&2, Requests.Res>) -> {Res.found(Res.value(x)) == x: Maybe<&2, Requests.Res>}:
  match x:
    case None{}:
      {==}
    case Some{+r}:
      Codes.Code.whole_read(
        ~Requests.Res,
        ~Requests.Res.code,
        ~Requests.Res.code.read,
        ~(a => s => Requests.Res.code_read(a, s)),
        r
      )

# a read that finds a value finds the resource that the value holds
def Merge.find_res(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  v: Maybe<&2, List<&2, U32>>,
  e: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Res.find(~d, l, h, n) == Some{Res.found(v)}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)),
    Some{v},
    e
  ): {
    Maybe.bind(
      &2,
      Maybe<&2, List<&2, U32>>,
      Maybe<&2, Requests.Res>,
      _,
      m => Some{Res.found(m)}
    )
      == Some{Res.found(v)}: Maybe<&2, Maybe<&2, Requests.Res>>
  }
  {==}

# a read of a resource found the resource that a value holds
def Merge.Found(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>
) -> Data:
  Sigma<&2, &2, Maybe<&2, List<&2, U32>>, v => Merge.And({Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, {Res.found(v) == o: Maybe<&2, Requests.Res>})>

# a resource that a read finds is the resource that the value found holds, once
# the read is known (m)
def Merge.find_some.at(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {
    Maybe.bind(&2, Maybe<&2, List<&2, U32>>, Maybe<&2, Requests.Res>, m, v => Some{Res.found(v)})
      == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
  }
) -> Merge.Found(~d, l, h, n, o):
  match m:
    case None{}:
      Empty.absurd(
        Merge.Found(~d, l, h, n, o),
        Shared.Maybe.none_ne_some(Maybe<&2, Requests.Res>, o, e)
      )
    case Some{+v}:
      (v, (em, Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Res.found(v), o, e)))
# a resource that a read finds is the resource that the value found holds
def Merge.find_some(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +o: Maybe<&2, Requests.Res>,
  e: {Res.find(~d, l, h, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
) -> Merge.Found(~d, l, h, n, o):
  Merge.find_some.at(~d, l, h, n, o, Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)), {==}, e)

# the value that a read finds is the value that it is known as
def Merge.value_known(
  r: Trees.Look,
  m: Maybe<&2, List<&2, U32>>,
  e: {Trees.Look.known(r) == Some{m}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Trees.Look.value(r) == m: Maybe<&2, List<&2, U32>>}:
  match r:
    case Trees.Look.Found{+v}:
      Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, Some{v}, m, e)
    case Trees.Look.Absent{}:
      Shared.Maybe.some_inj(Maybe<&2, List<&2, U32>>, None{}, m, e)
    case Trees.Look.Missing{h}:
      Empty.absurd({Trees.Look.value(Trees.Look.Missing{h}) == m: Maybe<&2, List<&2, U32>>}, Shared.Maybe.none_ne_some(Maybe<&2, List<&2, U32>>, m, e))

# a resource is the same as itself
def Merge.same_refl(+a: Maybe<&2, Requests.Res>) -> {Res.same(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{+r}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Requests.Res.code(r, []))

# the resource that a pick takes
def Merge.pick_res(p: Pick) -> Maybe<&2, Requests.Res>:
  match p:
    case Pick.Take{r}:
      r
    case _:
      None{}

# a merge that takes a side, of two sides that are the same, takes them
def Merge.take_value.at(
  ~d: Led(),
  l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  s: Sides.Side,
  es: {Sides.Side.of(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th) == s: Sides.Side},
  hp: {Pick.side(~d, l, b, o, th, s) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  eoth: {o == th: Maybe<&2, Requests.Res>}
) -> {x == o: Maybe<&2, Requests.Res>}:
  match s:
    case Sides.Side.Theirs{}:
      Equal.trans(
        Maybe<&2, Requests.Res>,
        x,
        th,
        o,
        Equal.sym(
          Maybe<&2, Requests.Res>,
          th,
          x,
          Equal.cong(
            Pick,
            Maybe<&2, Requests.Res>,
            q => Merge.pick_res(q),
            Pick.Take{th},
            Pick.Take{x},
            Shared.Maybe.some_inj(Pick, Pick.Take{th}, Pick.Take{x}, hp)
          )
        ),
        Equal.sym(Maybe<&2, Requests.Res>, o, th, eoth)
      )
    case Sides.Side.Ours{}:
      Equal.sym(
        Maybe<&2, Requests.Res>,
        o,
        x,
        Equal.cong(
          Pick,
          Maybe<&2, Requests.Res>,
          q => Merge.pick_res(q),
          Pick.Take{o},
          Pick.Take{x},
          Shared.Maybe.some_inj(Pick, Pick.Take{o}, Pick.Take{x}, hp)
        )
      )
    case Sides.Side.Both{}:
      Empty.absurd(
        {x == o: Maybe<&2, Requests.Res>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Bool.or(Res.same(o, b), Bool.or(Res.same(th, b), Res.same(o, th))),
            True{},
            Equal.sym(
              Bool,
              Bool.or(Res.same(o, b), Bool.or(Res.same(th, b), Res.same(o, th))),
              False{},
              Sides.Side.both_changed(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th)(es)
            ),
            %Equal.sym(
              Bool,
              Bool.or(Res.same(th, b), Res.same(o, th)),
              True{},
              %Equal.sym(
                Bool,
                Res.same(o, th),
                True{},
                %eoth: {Res.same(o, _) == True{}: Bool}
                Merge.same_refl(o)
              ): {Bool.or(Res.same(th, b), _) == True{}: Bool}
              Shared.Bool.or_true_right(Res.same(th, b))
            ): {Bool.or(Res.same(o, b), _) == True{}: Bool}
            Shared.Bool.or_true_right(Res.same(o, b))
          )
        )
      )

# a merge that takes a side, of two sides that are the same, takes them
def Merge.take_value(
  ~d: Led(),
  l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  eoth: {o == th: Maybe<&2, Requests.Res>}
) -> {x == o: Maybe<&2, Requests.Res>}:
  Merge.take_value.at(~d, l, b, o, th, x, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th), {==}, hp, eoth)
# the second of a pair
def Merge.snd(-A: Type, -B: Type, p: A & B) -> B:
  match p:
    case Tuple{a, b}:
      b

# the law of a difference, of the tree of the ledger d
def Merge.laws_diff(d: Led()) -> Trees.Laws.Diff(L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, Tuple{df, rest}}}}}}}}:
      df

# the law of the trees that the ledger d holds whole
def Merge.laws_whole(d: Led()) -> Trees.Laws.Whole(L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
  match d:
    case Tuple{x, Tuple{o, Tuple{fin, Tuple{pf, Tuple{wr, Tuple{cn, Tuple{rg, Tuple{df, Tuple{wh, kp}}}}}}}}}:
      wh

# two whole trees differ, by the law of a tree
def Merge.whole_diff(
  -S: Data,
  -o: Trees.Tree.Ops(S),
  wh: Trees.Laws.Whole(S, o),
  s: S,
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  bs: List<&2, Trees.Binding>,
  bs2: List<&2, Trees.Binding>,
  e1: {Trees.Ops.range(S, o)(s)(h)([]) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
  e2: {Trees.Ops.range(S, o)(s)(h2)([]) == Some{bs2}: Maybe<&2, List<&2, Trees.Binding>>}
) -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Trees.Ops.diff(S, o)(s)(h)(h2)) == True{}: Bool}:
  match wh:
    case Tuple{empty, w2}:
      Merge.snd(
        (@k: List<&2, U32> -> @m: Maybe<&2, List<&2, U32>> -> @p: List<&2, U32> -> {
          Trees.Look.is_final(Trees.Ops.look(S, o)(s)(h)(k)) == True{}: Bool
        }
          & (
            {Maybe.is_some(&2, Trees.Edit, Trees.Ops.put(S, o)(s)(h)(k)(m)) == True{}: Bool}
              & {Maybe.is_some(&2, List<&2, Trees.Binding>, Trees.Ops.range(S, o)(s)(h)(p)) == True{}: Bool}
          )),
        (@h3: Maybe<&2, Hashes.Hash> -> @bs3: List<&2, Trees.Binding> -> {
          Trees.Ops.range(S, o)(s)(h3)([]) == Some{bs3}: Maybe<&2, List<&2, Trees.Binding>>
        } -> {Maybe.is_some(&2, List<&2, List<&2, U32>>, Trees.Ops.diff(S, o)(s)(h)(h3)) == True{}: Bool}),
        w2(s)(h)(bs)(e1)
      )(h2)(bs2)(e2)

# the tree whose root is h lists whole, once it is kept
def Merge.kept_range.at(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, List<&2, Trees.Binding>>,
  em: {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == m: Maybe<&2, List<&2, Trees.Binding>>},
  e: {
    Maybe.default(
      &2,
      Bool,
      Maybe.bind(&2, List<&2, Trees.Binding>, Bool, m, bs => Some{Res.all_held(~d, l, bs)}),
      False{}
    )
      == True{}: Bool
  }
) -> Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>:
  match m:
    case None{}:
      Empty.absurd(
        Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>,
        Shared.Bool.false_ne_true(e)
      )
    case Some{+bs}:
      (bs, em)

# a tree that is kept lists whole
def Merge.kept_range(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  e: {Tree.kept(~d, l, h) == True{}: Bool}
) -> Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>:
  Merge.kept_range.at(~d, l, h, Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []), {==}, e)
# the root that an act takes
def Merge.act_root(a: Replicas.Act) -> Maybe<&2, Hashes.Hash>:
  match a:
    case Replicas.Act.Taken{vs, h, ns}:
      h
    case _:
      None{}

# the nodes that an act takes
def Merge.act_nodes(a: Replicas.Act) -> List<&2, List<&2, U32>>:
  match a:
    case Replicas.Act.Taken{vs, h, ns}:
      ns
    case _:
      []

# the act of a work, once it is known whether the ledger of the work holds its
# nodes (p)
def Merge.work_act.at(
  ~d: Led(),
  +lw: L(d),
  +hw: Maybe<&2, Hashes.Hash>,
  +nsw: List<&2, List<&2, U32>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +p: Bool,
  +ep: {
    Depots.Depot.holds(~L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lw, nsw) == p: Bool
  },
  +e: {
    Shared.Maybe.when(Replicas.Act, p, u => Some{Replicas.Act.Taken{None{}, hw, nsw}})
      == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
  }
) -> Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw))):
  match p:
    case True{}:
      (
        Equal.cong(
          Replicas.Act,
          Maybe<&2, Hashes.Hash>,
          a => Merge.act_root(a),
          Replicas.Act.Taken{None{}, hw, nsw},
          Replicas.Act.Taken{vs, h2, ns},
          Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{None{}, hw, nsw}, Replicas.Act.Taken{vs, h2, ns}, e)
        ),
        (
          Equal.cong(
            Replicas.Act,
            List<&2, List<&2, U32>>,
            a => Merge.act_nodes(a),
            Replicas.Act.Taken{None{}, hw, nsw},
            Replicas.Act.Taken{vs, h2, ns},
            Shared.Maybe.some_inj(Replicas.Act, Replicas.Act.Taken{None{}, hw, nsw}, Replicas.Act.Taken{vs, h2, ns}, e)
          ),
          ep
        )
      )
    case False{}:
      Empty.absurd(
        Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw))),
        Shared.Maybe.none_ne_some(Replicas.Act, Replicas.Act.Taken{vs, h2, ns}, e)
      )

# the work that an act is of: its root and nodes are those of the act, and its
# ledger holds its nodes
def Merge.Acted(
  ~d: Led(),
  m: Maybe<&2, Work<L(d)>>,
  h2: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>
) -> Data:
  Sigma<&2, &2, Work<L(d)>, W => Merge.And({m == Some{W}: Maybe<&2, Work<L(d)>>}, Merge.And({Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>}, Merge.And({Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)))))>

# the facts of the act of a work give the work that the act is of
def Merge.work_act.acted(
  ~d: Led(),
  +lw: L(d),
  +hw: Maybe<&2, Hashes.Hash>,
  +nsw: List<&2, List<&2, U32>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  f: Merge.And({hw == h2: Maybe<&2, Hashes.Hash>}, Merge.And({nsw == ns: List<&2, List<&2, U32>>}, Merge.Held(~d, lw, nsw)))
) -> Merge.Acted(~d, Some{Work{lw, hw, nsw}}, h2, ns):
  (+a, r1) = f
  (+b, held) = r1
  (Work{lw, hw, nsw}, ({==}, (a, (b, held))))

# the act that takes a work is taken, with the nodes of the work, once the work
# is known
def Merge.work_act(
  ~d: Led(),
  m: Maybe<&2, Work<L(d)>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  e: {Work.act(~d, None{}, m) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Acted(~d, m, h2, ns):
  match m:
    case None{}:
      Empty.absurd(Merge.Acted(~d, None{}, h2, ns), Shared.Maybe.none_ne_some(Replicas.Act, Replicas.Act.Taken{vs, h2, ns}, e))
    case Some{Work{+lw, +hw, +nsw}}:
      Merge.work_act.acted(
        ~d,
        lw,
        hw,
        nsw,
        h2,
        ns,
        Merge.work_act.at(
          ~d,
          lw,
          hw,
          nsw,
          vs,
          h2,
          ns,
          Depots.Depot.holds(~L(d), ~(s => x => Replicas.Led.fetch(~Requests.Ask.machine(), ~d, s, x)), lw, nsw),
          {==},
          e
        )
      )
# that the three trees of a merge are whole
def Merge.ok(
  ~d: Led(),
  +l: L(d),
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>
) -> Bool:
  List.all.if(u => List.all.if(u2 => Tree.kept(~d, l, ho), Tree.kept(~d, l, hb)), Tree.kept(~d, l, ht))

# the act of a merge once the trees are checked (ok) and the keys to merge are
# read (md)
def Merge.act.go(
  ~d: Led(),
  +l: L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ok: Bool,
  md: Maybe<&2, List<&2, List<&2, U32>>>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    ok,
    u => Work.act(
      ~d,
      None{},
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        Maybe.default(&2, List<&2, List<&2, U32>>, md, []),
        Some{Work{l, ho, []}}
      )
    ),
    u => None{}
  )

# the act of a merge is the act once its trees are checked
def Merge.act_eq(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  +k: Ledgers.Id,
  from: Requests.Source,
  base: Maybe<&2, Requests.Source>
) -> {
  Merge.act(~d, l, t, k, from, base)
    == Merge.act.go(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Source.root(from),
      Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from))
    ): Maybe<&2, Replicas.Act>
}:
  {==}

# a merge that gives an act has its trees checked
def Merge.act_ok(
  ~d: Led(),
  +l: L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ok: Bool,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  ac: Replicas.Act,
  e: {Merge.act.go(~d, l, k, hb, ho, ht, ok, md) == Some{ac}: Maybe<&2, Replicas.Act>}
) -> {ok == True{}: Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Replicas.Act, ac, e))

# the three trees that a check holds of are each kept
def Merge.guard3(
  a: Bool,
  b: Bool,
  c: Bool,
  h: {List.all.if(u => List.all.if(u2 => c, b), a) == True{}: Bool}
) -> Merge.And({a == True{}: Bool}, Merge.And({b == True{}: Bool}, {c == True{}: Bool})):
  match a b c:
    case True{} True{} True{}:
      ({==}, ({==}, {==}))
    case True{} True{} False{}:
      Empty.absurd(
        Merge.And({True{} == True{}: Bool}, Merge.And({True{} == True{}: Bool}, {False{} == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )
    case True{} False{} z:
      Empty.absurd(
        Merge.And({True{} == True{}: Bool}, Merge.And({False{} == True{}: Bool}, {z == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )
    case False{} y z:
      Empty.absurd(
        Merge.And({False{} == True{}: Bool}, Merge.And({y == True{}: Bool}, {z == True{}: Bool})),
        Shared.Bool.false_ne_true(h)
      )

# the work that a merge that gives an act is of
def Merge.act_acted(
  ~d: Led(),
  +l: L(d),
  +k: Ledgers.Id,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  e: {Merge.act.go(~d, l, k, hb, ho, ht, True{}, md) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Acted(
  ~d,
  Merge.all(~d, l, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, md, []), Some{Work{l, ho, []}}),
  h2,
  ns
):
  Merge.work_act(
    ~d,
    Merge.all(~d, l, hb, ho, ht, k, Maybe.default(&2, List<&2, List<&2, U32>>, md, []), Some{Work{l, ho, []}}),
    vs,
    h2,
    ns,
    e
  )
# a test that gives False when its negation does is true
def Merge.not_false(a: Bool, h: {Bool.not(a) == False{}: Bool}) -> {a == True{}: Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))

# a key that is not among the keys of a difference reads the same in both trees
def Merge.diff_same(
  ~d: Led(),
  +l: L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  ks: List<&2, List<&2, U32>>,
  +mo: Maybe<&2, List<&2, U32>>,
  +mt: Maybe<&2, List<&2, U32>>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)) == False{}: Bool},
  eo: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, ho, Key.res(n)) == Some{mo}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  et: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)) == Some{mt}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {mo == mt: Maybe<&2, List<&2, U32>>}:
  Equal.trans(
    Maybe<&2, List<&2, U32>>,
    mo,
    Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
    mt,
    Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
      mo,
      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n)), mo, eo)
    ),
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n))),
      mt,
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
      )(
        Merge.not_false(
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
            Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
          ),
          Equal.trans(
            Bool,
            Bool.not(
              Shared.Maybe.is_eq(
                ~List<&2, U32>,
                ~Shared.List.is_eq(~U32, ~U32.is_eq),
                Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
              )
            ),
            List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)),
            False{},
            Equal.sym(
              Bool,
              List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)),
              Bool.not(
                Shared.Maybe.is_eq(
                  ~List<&2, U32>,
                  ~Shared.List.is_eq(~U32, ~U32.is_eq),
                  Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                  Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
                )
              ),
              Merge.laws_diff(d)(l)(ho)(ht)(ks)(ediff)(Key.res(n))
            ),
            ec
          )
        )
      ),
      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)), mt, et)
    )
  )
# a merge whose keys do not name a resource, which reads the same in both
# trees, leaves it, and its merge takes a side, so it is that side
def Merge.takes_core.fo(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)) == False{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o),
  ft: Merge.Found(~d, l, ht, n, th)
) -> {Res.find(~d, lf, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  (+mt, r2) = ft
  (+et1, +et2) = r2
  %Equal.sym(
    Maybe<&2, Requests.Res>,
    x,
    o,
    Merge.take_value(
      ~d,
      l,
      b,
      o,
      th,
      x,
      hp,
      Equal.trans(
        Maybe<&2, Requests.Res>,
        o,
        Res.found(mo),
        th,
        Equal.sym(Maybe<&2, Requests.Res>, Res.found(mo), o, eo2),
        Equal.trans(
          Maybe<&2, Requests.Res>,
          Res.found(mo),
          Res.found(mt),
          th,
          Equal.cong(
            Maybe<&2, List<&2, U32>>,
            Maybe<&2, Requests.Res>,
            v => Res.found(v),
            mo,
            mt,
            Merge.diff_same(~d, l, ho, ht, n, ks, mo, mt, ediff, ec, eo1, et1)
          ),
          et2
        )
      )
    )
  ): {Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
  %eo2: {Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
  Merge.find_res(
    ~d,
    lf,
    hf,
    n,
    mo,
    Merge.all_frame(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      n,
      mo,
      ks,
      l,
      ho,
      [],
      lf,
      hf,
      N,
      eall,
      {==},
      wf,
      held,
      ec,
      Replicas.Hist.find(
        ~Requests.Ask.machine(),
        ~d,
        l,
        lf,
        ho,
        Key.res(n),
        mo,
        Merge.grows_of(~d, l, l, lf, [], N, {==}, wf, nd)
      )(eo1)
    )
  )

# a merge whose pick of a resource takes a side reads the resource as that side
def Merge.takes_core.at(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +c: Bool,
  +ec: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)) == c: Bool}
) -> {Res.find(~d, lf, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  match c:
    case True{}:
      %Merge.found_value(x): {Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
      Merge.find_res(
        ~d,
        lf,
        hf,
        n,
        Res.value(x),
        Merge.all_take(~d, l, hb, ho, ht, k, n, b, o, th, x, ks, l, ho, [], lf, hf, N, eall, {==}, wf, held, hb0, ho0, ht0, hp, ec)
      )
    case False{}:
      Merge.takes_core.fo(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        x,
        ks,
        lf,
        hf,
        N,
        eall,
        wf,
        held,
        nd,
        hp,
        ediff,
        ec,
        Merge.find_some(~d, l, ho, n, o, ho0),
        Merge.find_some(~d, l, ht, n, th, ht0)
      )

# the merge of a resource whose pick takes a side, as the work that the merge
# ends in, is that side in the ledger of its nodes
def Merge.takes_final(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<L(d)>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<L(d)>>},
  +eroot: {Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>},
  +enodes: {Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>},
  +held: Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  match W:
    case Work{+lf, +hf, +N}:
      %enodes: {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      %eroot: {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      %Merge.And.left(
        Merge.Puts(~d, l, lf, N),
        Merge.Nodes([], N),
        Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
      ): {Res.find(~d, _, hf, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}
      Merge.takes_core.at(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        x,
        ks,
        lf,
        hf,
        N,
        eall,
        Merge.And.left(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        hb0,
        ho0,
        ht0,
        hp,
        ediff,
        List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)),
        {==}
      )
# the keys that a merge goes through are those of the difference
def Merge.keys_def(
  ~d: Led(),
  +l: L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  ks: List<&2, List<&2, U32>>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> {
  Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []) == ks: List<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, List<&2, List<&2, U32>>>,
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
    Some{ks},
    ediff
  ): {Maybe.default(&2, List<&2, List<&2, U32>>, _, []) == ks: List<&2, List<&2, U32>>}
  {==}

# what a merge that gives an act has gone through: from the keys of the
# difference ks, the work W that it ends in, whose root is h2 and whose nodes
# are ns
def Merge.Facts.work(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<L(d)>
) -> Data:
  Merge.And({Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<L(d)>>}, Merge.And({Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>}, Merge.And({Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>}, Merge.And({Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}, Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W))))))

# what a merge that gives an act has gone through
def Merge.Facts(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>
) -> Data:
  Sigma<&2, &2, List<&2, List<&2, U32>>, ks => Sigma<&2, &2, Work<L(d)>, W => Merge.Facts.work(~d, l, hb, ho, ht, k, h2, ns, ks, W)>>

# what a merge has gone through, once the act of the merge is known to be of a
# work
def Merge.facts_acted(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +ks: List<&2, List<&2, U32>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  ),
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  (+W, st) = acted
  (+eall0, st2) = st
  (+eroot, st3) = st2
  (+enodes, held) = st3
  (
    ks,
    (
      W,
      (
        %Merge.keys_def(~d, l, ho, ht, ks, ediff): {
          Merge.all(~d, l, hb, ho, ht, k, _, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<L(d)>>
        }
        eall0,
        (eroot, (enodes, (ediff, held)))
      )
    )
  )

# the bindings that a tree lists whole
def Merge.Listed(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> Data:
  Sigma<&2, &2, List<&2, Trees.Binding>, bs => {Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, []) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>}>

# what a merge has gone through, once the difference of the trees is known to be
# there (md)
def Merge.facts_ks(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  md: Maybe<&2, List<&2, List<&2, U32>>>,
  +emd: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == md: Maybe<&2, List<&2, List<&2, U32>>>},
  hs: {Maybe.is_some(&2, List<&2, List<&2, U32>>, md) == True{}: Bool},
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  )
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  match md:
    case None{}:
      Empty.absurd(Merge.Facts(~d, l, hb, ho, ht, k, h2, ns), Shared.Bool.false_ne_true(hs))
    case Some{+ks}:
      Merge.facts_acted(~d, l, hb, ho, ht, k, ks, h2, ns, acted, emd)

# what a merge has gone through, once the two trees are known to list whole
def Merge.facts_r2(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  r1: Merge.Listed(~d, l, ho),
  r2: Merge.Listed(~d, l, ht),
  acted: Merge.Acted(
    ~d,
    Merge.all(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      Maybe.default(&2, List<&2, List<&2, U32>>, Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht), []),
      Some{Work{l, ho, []}}
    ),
    h2,
    ns
  )
) -> Merge.Facts(~d, l, hb, ho, ht, k, h2, ns):
  (+bs1, e1) = r1
  (+bs2, e2) = r2
  Merge.facts_ks(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    h2,
    ns,
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht),
    {==},
    Merge.whole_diff(
      L(d),
      Replicas.Led.tree(Requests.Ask.machine(), d),
      Merge.laws_whole(d),
      l,
      ho,
      ht,
      bs1,
      bs2,
      e1,
      e2
    ),
    acted
  )

# the act of a merge is the act once its trees are checked
def Merge.act_go_of(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> {
  Merge.act.go(
    ~d,
    l,
    k,
    Base.tree(base),
    Replicas.Tip.content(t),
    Source.root(from),
    Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
    Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from))
  )
    == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
}:
  Equal.trans(
    Maybe<&2, Replicas.Act>,
    Merge.act.go(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Source.root(from),
      Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from))
    ),
    Merge.act(~d, l, t, k, from, base),
    Some{Replicas.Act.Taken{vs, h2, ns}},
    Equal.sym(
      Maybe<&2, Replicas.Act>,
      Merge.act(~d, l, t, k, from, base),
      Merge.act.go(
        ~d,
        l,
        k,
        Base.tree(base),
        Replicas.Tip.content(t),
        Source.root(from),
        Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from))
      ),
      Merge.act_eq(~d, l, t, k, from, base)
    ),
    e0
  )

# what a merge that gives an act has gone through
def Merge.facts_go(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
) -> Merge.Facts(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from), k, h2, ns):
  Merge.facts_r2(
    ~d,
    l,
    Base.tree(base),
    Replicas.Tip.content(t),
    Source.root(from),
    k,
    h2,
    ns,
    Merge.kept_range(
      ~d,
      l,
      Replicas.Tip.content(t),
      Merge.And.right(
        {Tree.kept(~d, l, Base.tree(base)) == True{}: Bool},
        {Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool},
        Merge.And.right(
          {Tree.kept(~d, l, Source.root(from)) == True{}: Bool},
          Merge.And({Tree.kept(~d, l, Base.tree(base)) == True{}: Bool}, {Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}),
          Merge.guard3(
            Tree.kept(~d, l, Source.root(from)),
            Tree.kept(~d, l, Base.tree(base)),
            Tree.kept(~d, l, Replicas.Tip.content(t)),
            Merge.act_ok(
              ~d,
              l,
              k,
              Base.tree(base),
              Replicas.Tip.content(t),
              Source.root(from),
              Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
              Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from)),
              Replicas.Act.Taken{vs, h2, ns},
              Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
            )
          )
        )
      )
    ),
    Merge.kept_range(
      ~d,
      l,
      Source.root(from),
      Merge.And.left(
        {Tree.kept(~d, l, Source.root(from)) == True{}: Bool},
        Merge.And({Tree.kept(~d, l, Base.tree(base)) == True{}: Bool}, {Tree.kept(~d, l, Replicas.Tip.content(t)) == True{}: Bool}),
        Merge.guard3(
          Tree.kept(~d, l, Source.root(from)),
          Tree.kept(~d, l, Base.tree(base)),
          Tree.kept(~d, l, Replicas.Tip.content(t)),
          Merge.act_ok(
            ~d,
            l,
            k,
            Base.tree(base),
            Replicas.Tip.content(t),
            Source.root(from),
            Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
            Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from)),
            Replicas.Act.Taken{vs, h2, ns},
            Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
          )
        )
      )
    ),
    Merge.act_acted(
      ~d,
      l,
      k,
      Base.tree(base),
      Replicas.Tip.content(t),
      Source.root(from),
      Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from)),
      vs,
      h2,
      ns,
      %Merge.act_ok(
        ~d,
        l,
        k,
        Base.tree(base),
        Replicas.Tip.content(t),
        Source.root(from),
        Merge.ok(~d, l, Base.tree(base), Replicas.Tip.content(t), Source.root(from)),
        Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from)),
        Replicas.Act.Taken{vs, h2, ns},
        Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
      ): {
        Merge.act.go(
          ~d,
          l,
          k,
          Base.tree(base),
          Replicas.Tip.content(t),
          Source.root(from),
          _,
          Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Source.root(from))
        )
          == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>
      }
      Merge.act_go_of(~d, l, t, k, from, base, vs, h2, ns, e0)
    )
  )

# a merge whose pick of a resource takes a side, once it is known what it has
# gone through, gives a tree that reads the resource as that side
def Merge.takes_facts(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  fs: Merge.Facts(~d, l, hb, ho, ht, k, h2, ns),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>}
) -> {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  (+ks, r1) = fs
  (+W, r2) = r1
  (+eall, r3) = r2
  (+eroot, r4) = r3
  (+enodes, r5) = r4
  (+ediff, held) = r5
  Merge.takes_final(~d, l, hb, ho, ht, k, n, b, o, th, x, ks, W, h2, ns, eall, eroot, enodes, held, hb0, ho0, ht0, hp, ediff)

# a merge that gives an act, and whose pick of a resource takes a side, gives a
# tree that reads the resource as that side
def Merge.takes_go(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +x: Maybe<&2, Requests.Res>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>},
  +hb0: {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>}
) -> {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>}:
  Merge.takes_facts(
    ~d,
    l,
    Base.tree(base),
    Replicas.Tip.content(t),
    Source.root(from),
    k,
    h2,
    ns,
    n,
    b,
    o,
    th,
    x,
    Merge.facts_go(~d, l, t, k, from, base, vs, h2, ns, e0),
    hb0,
    ho0,
    ht0,
    hp
  )

# the pick of the merge of a resource, as the premises say, gave the work W1
def Merge.one_pick(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  hb0: {mb == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +q: Pick,
  hq: {Pick.merge(~d, l, b0, o0, t0) == Some{q}: Maybe<&2, Pick>}
) -> {Merge.pick(~d, Work{lc, hc, P}, k, n, q) == Some{W1}: Maybe<&2, Work<L(d)>>}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  %Merge.pick_same(
    ~d,
    l,
    b,
    o,
    t,
    b0,
    o0,
    t0,
    p,
    q,
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      b,
      b0,
      Equal.trans(Maybe<&2, Maybe<&2, Requests.Res>>, Some{b}, mb, Some{b0}, Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, mb, Some{b}, eb), hb0)
    ),
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      o,
      o0,
      Equal.trans(
        Maybe<&2, Maybe<&2, Requests.Res>>,
        Some{o},
        Res.find(~d, l, ho, n),
        Some{o0},
        Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Res.find(~d, l, ho, n), Some{o}, eo),
        ho0
      )
    ),
    Shared.Maybe.some_inj(
      Maybe<&2, Requests.Res>,
      t,
      t0,
      Equal.trans(
        Maybe<&2, Maybe<&2, Requests.Res>>,
        Some{t},
        Res.find(~d, l, ht, n),
        Some{t0},
        Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Res.find(~d, l, ht, n), Some{t}, et),
        ht0
      )
    ),
    ep,
    hq
  ): {Merge.pick(~d, Work{lc, hc, P}, k, n, _) == Some{W1}: Maybe<&2, Work<L(d)>>}
  e

# the tree of the work after the next merge of the resource n, whose pick
# clashes, reads the key of the resource as it did
def Merge.next_clash_frame(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, Merge.root(~d, W1), Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}:
  Merge.pick_frame.clash.at(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    n,
    W1,
    lf,
    N,
    Clash.names(~d, lc, hc, k),
    Merge.one_pick(
      ~d,
      l,
      lc,
      ho,
      ht,
      hc,
      P,
      k,
      n,
      b0,
      o0,
      t0,
      Res.find(~d, l, hb, n),
      W1,
      Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e),
      hb0,
      ho0,
      ht0,
      Pick.Clash{},
      hpc
    ),
    wc,
    wf,
    held,
    nd,
    v,
    kn
  )
# the last of three that or to false is false
def Merge.or_last(
  a: Bool,
  b: Bool,
  c: Bool,
  h: {Bool.or(a, Bool.or(b, c)) == False{}: Bool}
) -> {c == False{}: Bool}:
  match c:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(
            Bool,
            True{},
            Bool.or(a, True{}),
            False{},
            Equal.sym(Bool, Bool.or(a, True{}), True{}, Shared.Bool.or_true_right(a)),
            %Shared.Bool.or_true_right(b): {Bool.or(a, _) == False{}: Bool}
            h
          )
        )
      )

# a test is false, when it is not true
def Merge.false_of(q: Bool, h: {q == True{}: Bool} -> Empty) -> {q == False{}: Bool}:
  match q:
    case False{}:
      {==}
    case True{}:
      Empty.absurd({True{} == False{}: Bool}, h({==}))

# whether a pick clashes
def Merge.is_clash(p: Pick) -> Bool:
  match p:
    case Pick.Clash{}:
      True{}
    case _:
      False{}

# a merge that clashes, once the side that it takes is known (s), is a merge of
# two sides that differ
def Merge.clash_diff.at(
  ~d: Led(),
  l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  s: Sides.Side,
  es: {Sides.Side.of(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th) == s: Sides.Side},
  hp: {Pick.side(~d, l, b, o, th, s) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {Res.same(o, th) == False{}: Bool}:
  match s:
    case Sides.Side.Theirs{}:
      Empty.absurd(
        {Res.same(o, th) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Pick,
            Bool,
            q => Merge.is_clash(q),
            Pick.Take{th},
            Pick.Clash{},
            Shared.Maybe.some_inj(Pick, Pick.Take{th}, Pick.Clash{}, hp)
          )
        )
      )
    case Sides.Side.Ours{}:
      Empty.absurd(
        {Res.same(o, th) == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Pick,
            Bool,
            q => Merge.is_clash(q),
            Pick.Take{o},
            Pick.Clash{},
            Shared.Maybe.some_inj(Pick, Pick.Take{o}, Pick.Clash{}, hp)
          )
        )
      )
    case Sides.Side.Both{}:
      Merge.or_last(
        Res.same(o, b),
        Res.same(th, b),
        Res.same(o, th),
        Sides.Side.both_changed(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th)(es)
      )

# a merge that clashes is a merge of two sides that differ
def Merge.clash_diff(
  ~d: Led(),
  l: L(d),
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  hp: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {Res.same(o, th) == False{}: Bool}:
  Merge.clash_diff.at(~d, l, b, o, th, Sides.Side.of(~Maybe<&2, Requests.Res>, ~Res.same, b, o, th), {==}, hp)

# two reads of the same resource that differ in the keys of a difference are in
# the keys that the difference lists
def Merge.clash_in_diff(
  ~d: Led(),
  +l: L(d),
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  ks: List<&2, List<&2, U32>>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  cd: {Res.same(o, th) == False{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o),
  ft: Merge.Found(~d, l, ht, n, th)
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)) == True{}: Bool}:
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  (+mt, r2) = ft
  (+et1, +et2) = r2
  Equal.trans(
    Bool,
    List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)),
    Bool.not(
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
      )
    ),
    True{},
    Merge.laws_diff(d)(l)(ho)(ht)(ks)(ediff)(Key.res(n)),
    Equal.cong(
      Bool,
      Bool,
      q => Bool.not(q),
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
      ),
      False{},
      Merge.false_of(
        Shared.Maybe.is_eq(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
          Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
        ),
        hq => Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Res.same(o, th),
            True{},
            Equal.sym(Bool, Res.same(o, th), False{}, cd),
            %Equal.trans(
              Maybe<&2, Requests.Res>,
              o,
              Res.found(mo),
              th,
              Equal.sym(Maybe<&2, Requests.Res>, Res.found(mo), o, eo2),
              Equal.trans(
                Maybe<&2, Requests.Res>,
                Res.found(mo),
                Res.found(mt),
                th,
                Equal.cong(
                  Maybe<&2, List<&2, U32>>,
                  Maybe<&2, Requests.Res>,
                  v => Res.found(v),
                  mo,
                  mt,
                  Equal.trans(
                    Maybe<&2, List<&2, U32>>,
                    mo,
                    Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                    mt,
                    Equal.sym(
                      Maybe<&2, List<&2, U32>>,
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                      mo,
                      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n)), mo, eo1)
                    ),
                    Equal.trans(
                      Maybe<&2, List<&2, U32>>,
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                      Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n))),
                      mt,
                      Shared.Maybe.is_eq_sound(
                        ~List<&2, U32>,
                        ~Shared.List.is_eq(~U32, ~U32.is_eq),
                        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
                        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ho, Key.res(n))),
                        Trees.Look.value(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)))
                      )(hq),
                      Merge.value_known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, ht, Key.res(n)), mt, et1)
                    )
                  )
                ),
                et2
              )
            ): {Res.same(o, _) == True{}: Bool}
            Merge.same_refl(o)
          )
        )
      )
    )
  )
# the resources that a read of the key of the open clashes tells are open (the
# body of Clash.names, apart from the read)
def Merge.names_of(m: Maybe<&2, Maybe<&2, List<&2, U32>>>) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(
    &2,
    Maybe<&2, List<&2, Resources.Name>>,
    List<&2, Resources.Name>,
    x => Maybe.default(&2, List<&2, Resources.Name>, x, []),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      m
    )
  )

# the clash of the resource n is among the resources that mc tells (the body of
# Clash.open, apart from the clashes)
def Merge.open_of(n: Resources.Name, mc: Maybe<&2, List<&2, Resources.Name>>) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    mc
  )

# the clashes that are open in the tree h of l are cs, and n is among them
def Merge.Names(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, k: Ledgers.Id, n: Resources.Name) -> Data:
  Sigma<&2, &2, List<&2, Resources.Name>, cs => Merge.And({Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}, {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool})>

# a read of the key K of the tree h of l is known as the value v
def Merge.Known(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, K: List<&2, U32>) -> Data:
  Sigma<&2, &2, Maybe<&2, List<&2, U32>>, v => {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, K) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}>

# a clash that is open, once the clashes that are open are read (mc), gives the
# clashes that are open and a name among them
def Merge.open_names.at(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Clash.names(~d, l, h, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  e: {Merge.open_of(n, mc) == Some{True{}}: Maybe<&2, Bool>}
) -> Merge.Names(~d, l, h, k, n):
  match mc:
    case None{}:
      Empty.absurd(Merge.Names(~d, l, h, k, n), Shared.Maybe.none_ne_some(Bool, True{}, e))
    case Some{+cs}:
      (cs, (emc, Shared.Maybe.some_inj(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, e)))

# a clash that is open is among the clashes that are open
def Merge.open_names(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  e: {Clash.open(~d, l, h, n, k) == Some{True{}}: Maybe<&2, Bool>}
) -> Merge.Names(~d, l, h, k, n):
  Merge.open_names.at(~d, l, h, k, n, Clash.names(~d, l, h, k), {==}, e)

# a resource among the clashes that are open has its clash open
def Merge.names_open(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  ns: Merge.Names(~d, l, h, k, n)
) -> {Clash.open(~d, l, h, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = ns
  (ec, ct) = r
  %Equal.sym(Maybe<&2, List<&2, Resources.Name>>, Clash.names(~d, l, h, k), Some{cs}, ec): {
    Merge.open_of(n, _) == Some{True{}}: Maybe<&2, Bool>
  }
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, ct): {
    Some{_} == Some{True{}}: Maybe<&2, Bool>
  }
  {==}

# the clashes that are open, once the read of them is known (m), give a value
# that the read finds
def Merge.names_known.at(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {Merge.names_of(m) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> Merge.Known(~d, l, h, Key.clashes(k)):
  match m:
    case None{}:
      Empty.absurd(Merge.Known(~d, l, h, Key.clashes(k)), Shared.Maybe.none_ne_some(List<&2, Resources.Name>, cs, e))
    case Some{+v}:
      (v, em)

# the clashes that are open are read as a value
def Merge.names_known(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  e: {Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> Merge.Known(~d, l, h, Key.clashes(k)):
  Merge.names_known.at(~d, l, h, k, cs, Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k)), {==}, e)

# the clashes that are open stay the same as the ledger grows
def Merge.names_grows.at(
  ~d: Led(),
  +a: L(d),
  +b: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  em: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Key.clashes(k)) == m: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  e: {Merge.names_of(m) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  match m:
    case None{}:
      Empty.absurd(
        {Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>},
        Shared.Maybe.none_ne_some(List<&2, Resources.Name>, cs, e)
      )
    case Some{+v}:
      %Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, b, h, Key.clashes(k)),
        Some{v},
        Replicas.Hist.find(~Requests.Ask.machine(), ~d, a, b, h, Key.clashes(k), v, g)(em)
      ): {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
      e

# the clashes that are open in a ledger are open in a ledger that grows from it
def Merge.names_grows(
  ~d: Led(),
  +a: L(d),
  +b: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b),
  e: {Clash.names(~d, a, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Clash.names(~d, b, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  Merge.names_grows.at(~d, a, b, h, k, cs, Replicas.Tree.find(~Requests.Ask.machine(), ~d, a, h, Key.clashes(k)), {==}, g, e)

# two trees that read the key of the open clashes alike have the same clashes
# that are open
def Merge.names_same(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +cs: List<&2, Resources.Name>,
  v: Maybe<&2, List<&2, U32>>,
  kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  kn1: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h1, Key.clashes(k)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  e: {Clash.names(~d, l, h, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
) -> {Clash.names(~d, l, h1, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h1, Key.clashes(k)),
    Some{v},
    kn1
  ): {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
  %kn: {Merge.names_of(_) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}
  e

# the clashes that a read of the code of some resources tells are those
# resources
def Merge.names_of_value(
  +y: Resources.Name,
  +ys: List<&2, Resources.Name>
) -> {Merge.names_of(Some{Clash.value(y <> ys)}) == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(
    Maybe<&2, List<&2, Resources.Name>>,
    Codes.Code.whole.read(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Codes.Code.list(~Resources.Name, ~Resources.Name.code, y <> ys, [])
    ),
    Some{y <> ys},
    Codes.Code.whole_read(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      ~(xs => r => Codes.Code.list_read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, ~(a => s => Resources.Name.code_read(a, s)), xs, r)),
      y <> ys
    )
  ): {Some{Maybe.default(&2, List<&2, Resources.Name>, _, [])} == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}
  {==}
# the clashes among which a resource is put, when it is among them, are the same
def Merge.put_true(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {Clash.put(n, cs) == cs: List<&2, Resources.Name>}:
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), True{}, ep): {
    Shared.Bool.when(List<&2, Resources.Name>, _, u => cs, u => n <> cs) == cs: List<&2, Resources.Name>
  }
  {==}

# the clashes among which a resource is put, when it is not among them, are
# those and it
def Merge.put_false(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == False{}: Bool}
) -> {Clash.put(n, cs) == n <> cs: List<&2, Resources.Name>}:
  %Equal.sym(Bool, List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), False{}, ep): {
    Shared.Bool.when(List<&2, Resources.Name>, _, u => cs, u => n <> cs) == n <> cs: List<&2, Resources.Name>
  }
  {==}

# the clashes are some, and others
def Merge.Cons(-ps: List<&2, Resources.Name>) -> Data:
  Sigma<&2, &2, Resources.Name, y => Sigma<&2, &2, List<&2, Resources.Name>, ys => {ps == y <> ys: List<&2, Resources.Name>}>>

# the clashes among which a resource is put are some, once it is known whether
# it is among them (p)
def Merge.put_cons.at(
  p: Bool,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == p: Bool}
) -> Merge.Cons(Clash.put(n, cs)):
  match p:
    case False{}:
      (n, (cs, Merge.put_false(n, cs, ep)))
    case True{}:
      match cs:
        case Nil{}:
          Empty.absurd(Merge.Cons(Clash.put(n, [])), Shared.Bool.false_ne_true(ep))
        case Con{+y, +ys}:
          (y, (ys, Merge.put_true(n, y <> ys, ep)))

# the clashes among which a resource is put are some
def Merge.put_cons(+n: Resources.Name, +cs: List<&2, Resources.Name>) -> Merge.Cons(Clash.put(n, cs)):
  Merge.put_cons.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), n, cs, {==})

# a resource that is put among the clashes is among them, once it is known
# whether it was among them (p)
def Merge.put_self.at(
  p: Bool,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  +ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == p: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Clash.put(n, cs), n) == True{}: Bool}:
  match p:
    case True{}:
      %Equal.sym(List<&2, Resources.Name>, Clash.put(n, cs), cs, Merge.put_true(n, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      ep
    case False{}:
      %Equal.sym(List<&2, Resources.Name>, Clash.put(n, cs), n <> cs, Merge.put_false(n, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      %Equal.sym(Bool, Resources.Name.is_eq(n, n), True{}, Resources.Name.is_eq_refl(n)): {
        List.any.if(u => List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), _) == True{}: Bool
      }
      {==}

# a resource that is put among the clashes is among them
def Merge.put_self(
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Clash.put(n, cs), n) == True{}: Bool}:
  Merge.put_self.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n), n, cs, {==})

# a resource that is put among the clashes keeps those that were among them,
# once it is known whether it was among them (p)
def Merge.put_keep.at(
  p: Bool,
  +n1: Resources.Name,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  ep: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n1) == p: Bool},
  h: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Clash.put(n1, cs), n) == True{}: Bool}:
  match p:
    case True{}:
      %Equal.sym(List<&2, Resources.Name>, Clash.put(n1, cs), cs, Merge.put_true(n1, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      h
    case False{}:
      %Equal.sym(List<&2, Resources.Name>, Clash.put(n1, cs), n1 <> cs, Merge.put_false(n1, cs, ep)): {
        List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n) == True{}: Bool
      }
      Shared.List.contains_cons(~Resources.Name, ~Resources.Name.is_eq, n1, cs, n)(h)

# a resource that is put among the clashes keeps those that were among them
def Merge.put_keep(
  +n1: Resources.Name,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  h: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n) == True{}: Bool}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Clash.put(n1, cs), n) == True{}: Bool}:
  Merge.put_keep.at(List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n1), n1, n, cs, {==}, h)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of some clashes, are those
def Merge.names_value(
  ~d: Led(),
  +lf: L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  ps: List<&2, Resources.Name>,
  +y: Resources.Name,
  +ys: List<&2, Resources.Name>,
  +ec: {ps == y <> ys: List<&2, Resources.Name>},
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)) == Trees.Look.of(Clash.value(ps)): Trees.Look}
) -> {Clash.names(~d, lf, h1, k) == Some{ps}: Maybe<&2, List<&2, Resources.Name>>}:
  %Equal.sym(List<&2, Resources.Name>, ps, y <> ys, ec): {Clash.names(~d, lf, h1, k) == Some{_}: Maybe<&2, List<&2, Resources.Name>>}
  %Equal.sym(
    Maybe<&2, Maybe<&2, List<&2, U32>>>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)),
    Some{Clash.value(y <> ys)},
    Merge.known_of(
      Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)),
      Clash.value(y <> ys),
      %ec: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)) == Trees.Look.of(Clash.value(_)): Trees.Look}
      e
    )
  ): {Merge.names_of(_) == Some{y <> ys}: Maybe<&2, List<&2, Resources.Name>>}
  Merge.names_of_value(y, ys)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of the clashes among which a resource is put, are those, once they
# are known to be some (cn)
def Merge.names_put.at(
  ~d: Led(),
  +lf: L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  cn: Merge.Cons(Clash.put(n, cs)),
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)) == Trees.Look.of(Clash.value(Clash.put(n, cs))): Trees.Look}
) -> {Clash.names(~d, lf, h1, k) == Some{Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>}:
  (+y, r) = cn
  (+ys, ec) = r
  Merge.names_value(~d, lf, h1, k, Clash.put(n, cs), y, ys, ec, e)

# the clashes that a tree tells, when it reads the key of the open clashes as
# the code of the clashes among which a resource is put, are those
def Merge.names_put(
  ~d: Led(),
  +lf: L(d),
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +cs: List<&2, Resources.Name>,
  e: {Replicas.Tree.look(~Requests.Ask.machine(), ~d, lf, h1, Key.clashes(k)) == Trees.Look.of(Clash.value(Clash.put(n, cs))): Trees.Look}
) -> {Clash.names(~d, lf, h1, k) == Some{Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>}:
  Merge.names_put.at(~d, lf, h1, k, n, cs, Merge.put_cons(n, cs), e)

# the clashes that are open before a clash, in the ledger of its nodes, and
# those after it, with the resource put among them
def Merge.Clashed(
  ~d: Led(),
  lf: L(d),
  hc: Maybe<&2, Hashes.Hash>,
  h1: Maybe<&2, Hashes.Hash>,
  k: Ledgers.Id,
  n: Resources.Name
) -> Data:
  Sigma<&2, &2, List<&2, Resources.Name>, cs => Merge.And({Clash.names(~d, lf, hc, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>}, {Clash.names(~d, lf, h1, k) == Some{Clash.put(n, cs)}: Maybe<&2, List<&2, Resources.Name>>})>

# what a clash does to the clashes that are open, once the ones that were open
# are read (mc)
def Merge.clash_after(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  mc: Maybe<&2, List<&2, Resources.Name>>,
  emc: {Clash.names(~d, lc, hc, k) == mc: Maybe<&2, List<&2, Resources.Name>>},
  +eb: {
    Maybe.bind(
      &2,
      List<&2, Resources.Name>,
      Work<L(d)>,
      mc,
      cs => Work.set(~d, Work{lc, hc, P}, Key.clashes(k), Clash.value(Clash.put(n, cs)))
    )
      == Some{W1}: Maybe<&2, Work<L(d)>>
  },
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> Merge.Clashed(~d, lf, hc, Merge.root(~d, W1), k, n):
  match mc:
    case None{}:
      Empty.absurd(Merge.Clashed(~d, lf, hc, Merge.root(~d, W1), k, n), Shared.Maybe.none_ne_some(Work<L(d)>, W1, eb))
    case Some{+cs}:
      (
        cs,
        (
          Merge.names_grows(
            ~d,
            lc,
            lf,
            hc,
            k,
            cs,
            Merge.grows_of(
              ~d,
              l,
              lc,
              lf,
              P,
              N,
              wc,
              wf,
              Merge.nodes_trans(
                P,
                Merge.nodes(~d, W1),
                N,
                Merge.And.right(
                  Merge.Puts(~d, l, Merge.ledger(~d, W1), Merge.nodes(~d, W1)),
                  Merge.Nodes(P, Merge.nodes(~d, W1)),
                  Merge.set_facts(~d, l, lc, hc, P, Key.clashes(k), Clash.value(Clash.put(n, cs)), W1, eb, wc)
                ),
                nd
              )
            ),
            emc
          ),
          Merge.names_put(
            ~d,
            lf,
            Merge.root(~d, W1),
            k,
            n,
            cs,
            Merge.writes_hit(
              ~d,
              lf,
              Merge.root(~d, W1),
              hc,
              Key.clashes(k),
              Clash.value(Clash.put(n, cs)),
              Merge.set_core(
                ~d,
                l,
                lc,
                hc,
                P,
                Key.clashes(k),
                Clash.value(Clash.put(n, cs)),
                lf,
                N,
                W1,
                Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Key.clashes(k), Clash.value(Clash.put(n, cs))),
                {==},
                eb,
                wc,
                wf,
                held,
                nd
              )
            )
          )
        )
      )

# the clash of a resource that a clash opens is open, once the clashes are known
# (cl)
def Merge.hit_of(
  ~d: Led(),
  +lf: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  cl: Merge.Clashed(~d, lf, hc, h1, k, n)
) -> {Clash.open(~d, lf, h1, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = cl
  (nb, na) = r
  Merge.names_open(~d, lf, h1, k, n, (Clash.put(n, cs), (na, Merge.put_self(n, cs))))

# a pick that clashes opens the clash of its resource
def Merge.clash_hit(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, Pick.Clash{}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {Clash.open(~d, lf, Merge.root(~d, W1), n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.hit_of(
    ~d,
    lf,
    hc,
    Merge.root(~d, W1),
    k,
    n,
    Merge.clash_after(~d, l, lc, hc, P, k, n, W1, lf, N, Clash.names(~d, lc, hc, k), {==}, e1, wc, wf, held, nd)
  )

# a write of a key that is not the key of the open clashes keeps the clash that
# is open, once the clashes that are open are read as a value (kk)
def Merge.keep_known(
  ~d: Led(),
  +lf: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Key.clashes(k)) == False{}: Bool},
  +cs: List<&2, Resources.Name>,
  +ec: {Clash.names(~d, lf, hc, k) == Some{cs}: Maybe<&2, List<&2, Resources.Name>>},
  ct: {List.contains(~Resources.Name, ~Resources.Name.is_eq, cs, n0) == True{}: Bool},
  kk: Merge.Known(~d, lf, hc, Key.clashes(k))
) -> {Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+v, +kn) = kk
  Merge.names_open(
    ~d,
    lf,
    h1,
    k,
    n0,
    (
      cs,
      (
        Merge.names_same(~d, lf, hc, h1, k, cs, v, kn, Merge.writes_frame(~d, lf, h1, hc, kw, m, wr, Key.clashes(k), v, hk, kn), ec),
        ct
      )
    )
  )

# a write of a key that is not the key of the open clashes keeps the clash that
# is open, once the clashes that are open are known (ns)
def Merge.keep_names(
  ~d: Led(),
  +lf: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Key.clashes(k)) == False{}: Bool},
  ns: Merge.Names(~d, lf, hc, k, n0)
) -> {Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs, r) = ns
  (+ec, ct) = r
  Merge.keep_known(~d, lf, hc, h1, k, n0, kw, m, wr, hk, cs, ec, ct, Merge.names_known(~d, lf, hc, k, cs, ec))

# a write of a key that is not the key of the open clashes keeps the clash that
# is open
def Merge.keep_by_writes(
  ~d: Led(),
  +lf: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  kw: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>,
  wr: Merge.Writes(~d, lf, h1, hc, kw, m),
  hk: {Shared.List.is_eq(~U32, ~U32.is_eq, kw, Key.clashes(k)) == False{}: Bool},
  op: {Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.keep_names(~d, lf, hc, h1, k, n0, kw, m, wr, hk, Merge.open_names(~d, lf, hc, k, n0, op))

# a clash keeps the clash that is open, once the clashes that are open (ns) and
# the clashes after it (cl) are known
def Merge.keep_clash(
  ~d: Led(),
  +lf: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +h1: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  ns: Merge.Names(~d, lf, hc, k, n0),
  cl: Merge.Clashed(~d, lf, hc, h1, k, n)
) -> {Clash.open(~d, lf, h1, n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+cs0, r0) = ns
  (+ec0, ct0) = r0
  (+cs, r1) = cl
  (nb, na) = r1
  Merge.names_open(
    ~d,
    lf,
    h1,
    k,
    n0,
    (
      Clash.put(n, cs),
      (
        na,
        Merge.put_keep(
          n,
          n0,
          cs,
          %Equal.sym(
            List<&2, Resources.Name>,
            cs,
            cs0,
            Shared.Maybe.some_inj(
              List<&2, Resources.Name>,
              cs,
              cs0,
              Equal.trans(
                Maybe<&2, List<&2, Resources.Name>>,
                Some{cs},
                Clash.names(~d, lf, hc, k),
                Some{cs0},
                Equal.sym(Maybe<&2, List<&2, Resources.Name>>, Clash.names(~d, lf, hc, k), Some{cs}, nb),
                ec0
              )
            )
          ): {List.contains(~Resources.Name, ~Resources.Name.is_eq, _, n0) == True{}: Bool}
          ct0
        )
      )
    )
  )

# what a pick of a merge does to the clash that is open in a tree: it keeps it
def Merge.pick_keep(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  p: Pick,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e1: {Merge.pick(~d, Work{lc, hc, P}, k, n, p) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  match p:
    case Pick.Take{+x}:
      Merge.keep_by_writes(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n0,
        Key.res(n),
        Res.value(x),
        Merge.set_core(
          ~d,
          l,
          lc,
          hc,
          P,
          Key.res(n),
          Res.value(x),
          lf,
          N,
          W1,
          Replicas.Tree.put(~Requests.Ask.machine(), ~d, lc, hc, Key.res(n), Res.value(x)),
          {==},
          e1,
          wc,
          wf,
          held,
          nd
        ),
        {==},
        op
      )
    case Pick.Make{+h, +bytes}:
      Merge.keep_by_writes(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n0,
        Key.res(n),
        Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
        Merge.set_core(
          ~d,
          l,
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
          hc,
          List.append(&2, List<&2, U32>, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes))),
          Key.res(n),
          Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}}),
          lf,
          N,
          W1,
          Replicas.Tree.put(
            ~Requests.Ask.machine(),
            ~d,
            Replicas.Led.puts(~Requests.Ask.machine(), ~d, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), lc),
            hc,
            Key.res(n),
            Res.value(Some{Requests.Res{h, Ropes.Put.root(Ropes.Rope.of_bytes(bytes))}})
          ),
          {==},
          e1,
          Merge.keep_puts(~d, l, lc, P, Ropes.Put.nodes(Ropes.Rope.of_bytes(bytes)), wc),
          wf,
          held,
          nd
        ),
        {==},
        op
      )
    case Pick.Clash{}:
      Merge.keep_clash(
        ~d,
        lf,
        hc,
        Merge.root(~d, W1),
        k,
        n,
        n0,
        Merge.open_names(~d, lf, hc, k, n0, op),
        Merge.clash_after(~d, l, lc, hc, P, k, n, W1, lf, N, Clash.names(~d, lc, hc, k), {==}, e1, wc, wf, held, nd)
      )
# what a merge of a resource does to the clash that is open in a tree: it keeps
# it
def Merge.one_keep.at(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +n0: Resources.Name,
  mb: Maybe<&2, Maybe<&2, Requests.Res>>,
  +W1: Work<L(d)>,
  rd: Merge.Read.b(~d, l, ho, ht, Work{lc, hc, P}, k, n, mb, W1),
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  (+b, r1) = rd
  (eb, r2) = r1
  (+o, r3) = r2
  (eo, r4) = r3
  (+t, r5) = r4
  (et, r6) = r5
  (+p, r7) = r6
  (ep, e) = r7
  Merge.pick_keep(~d, l, lc, hc, P, k, n, n0, p, W1, lf, N, e, wc, wf, held, nd, op)

# the next merge of the work keeps the clash that is open in its tree
def Merge.next_keep(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n0: Resources.Name,
  mn: Maybe<&2, Resources.Name>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, mn) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +op: {Clash.open(~d, lf, hc, n0, k) == Some{True{}}: Maybe<&2, Bool>}
) -> {Clash.open(~d, lf, Merge.root(~d, W1), n0, k) == Some{True{}}: Maybe<&2, Bool>}:
  match mn:
    case None{}:
      %Shared.Maybe.some_inj(Work<L(d)>, Work{lc, hc, P}, W1, e): {Clash.open(~d, lf, Merge.root(~d, _), n0, k) == Some{True{}}: Maybe<&2, Bool>}
      op
    case Some{+n}:
      Merge.one_keep.at(
        ~d,
        l,
        lc,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        n0,
        Res.find(~d, l, hb, n),
        W1,
        Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e),
        lf,
        N,
        wc,
        wf,
        held,
        nd,
        op
      )

# the next merge of the resource n, whose pick clashes, opens its clash
def Merge.next_hit_open(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N)
) -> {Clash.open(~d, lf, Merge.root(~d, W1), n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.clash_hit(
    ~d,
    l,
    lc,
    hc,
    P,
    k,
    n,
    W1,
    lf,
    N,
    Merge.one_pick(
      ~d,
      l,
      lc,
      ho,
      ht,
      hc,
      P,
      k,
      n,
      b0,
      o0,
      t0,
      Res.find(~d, l, hb, n),
      W1,
      Merge.read(~d, l, ho, ht, Work{lc, hc, P}, k, n, Res.find(~d, l, hb, n), W1, e),
      hb0,
      ho0,
      ht0,
      Pick.Clash{},
      hpc
    ),
    wc,
    wf,
    held,
    nd
  )

# one of two
type Merge.Or<-A: Data, -B: Data> is Data:
  Merge.Or.Left{left: A}
  Merge.Or.Right{right: B}

# the clash of the resource n is open in the tree h, or the key of n is in the
# keys rest
def Merge.Open(
  ~d: Led(),
  lf: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id,
  rest: List<&2, List<&2, U32>>
) -> Data:
  Merge.Or<{Clash.open(~d, lf, h, n, k) == Some{True{}}: Maybe<&2, Bool>}, {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, Key.res(n)) == True{}: Bool}>

# what a merge of the keys rest keeps of the resource n: the tree reads it as v,
# and the clash of n is open, or the keys have a key for n
def Merge.Inv(
  ~d: Led(),
  lf: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id,
  v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>
) -> Data:
  Merge.And({Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, h, Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}, Merge.Open(~d, lf, h, n, k, rest))

# a key that is in the keys x then rest, and is not x, is in rest
def Merge.cons_true.at(
  p: Bool,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  hp: {p == False{}: Bool},
  h: {
    List.any.if(u => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K), p) == True{}: Bool
  }
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool}:
  match p:
    case True{}:
      Empty.absurd(
        {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool},
        Shared.Bool.true_ne_false(hp)
      )
    case False{}:
      h

# a key that is in the keys x then rest, and is not x, is in rest
def Merge.cons_true(
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +K: List<&2, U32>,
  hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, K) == False{}: Bool},
  h: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x <> rest, K) == True{}: Bool}
) -> {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, K) == True{}: Bool}:
  Merge.cons_true.at(Shared.List.is_eq(~U32, ~U32.is_eq, x, K), rest, K, hx, h)

# the merge of the key of the resource n, whose pick clashes, keeps the resource
# as it was, and opens its clash
def Merge.next_inv.hit(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Some{n}) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +kn: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, lf, hc, Key.res(n)) == Some{v}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  (
    Merge.next_clash_frame(~d, l, lc, hb, ho, ht, hc, P, k, n, b0, o0, t0, v, W1, lf, N, e, hb0, ho0, ht0, hpc, wc, wf, held, nd, kn),
    Merge.Or.Left{Merge.next_hit_open(~d, l, lc, hb, ho, ht, hc, P, k, n, b0, o0, t0, W1, lf, N, e, hb0, ho0, ht0, hpc, wc, wf, held, nd)}
  )

# the merge of a key that is not the key of the resource n keeps the resource as
# it was, and the clash that is open or the key, once the one is known (orr)
def Merge.next_inv.or(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n)) == False{}: Bool},
  orr: Merge.Open(~d, lf, hc, n, k, x <> rest)
) -> Merge.Open(~d, lf, Merge.root(~d, W1), n, k, rest):
  match orr:
    case Merge.Or.Left{+opn}:
      Merge.Or.Left{Merge.next_keep(~d, l, lc, hb, ho, ht, hc, P, k, n, Res.name(x), W1, lf, N, e, wc, wf, held, nd, opn)}
    case Merge.Or.Right{+ctn}:
      Merge.Or.Right{Merge.cons_true(x, rest, Key.res(n), hx, ctn)}

# the merge of a key that is not the key of the resource n keeps the resource as
# it was, and the clash that is open or the key
def Merge.next_inv.miss(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +hx: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n)) == False{}: Bool},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  (+kn, orr) = inv
  (
    Merge.next_frame(~d, l, lc, hb, ho, ht, hc, P, k, n, Res.name(x), W1, lf, N, e, wc, wf, held, nd, Merge.apart_of(x, n, hx), v, kn),
    Merge.next_inv.or(~d, l, lc, hb, ho, ht, hc, P, k, n, x, rest, W1, lf, N, e, wc, wf, held, nd, hx, orr)
  )

# what the merge of the key x does to the resource n, once it is known whether
# x is its key (p)
def Merge.next_inv.at(
  ~d: Led(),
  p: Bool,
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  +ep: {Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n)) == p: Bool},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  match p:
    case True{}:
      (+kn, orr) = inv
      Merge.next_inv.hit(
        ~d,
        l,
        lc,
        hb,
        ho,
        ht,
        hc,
        P,
        k,
        n,
        b0,
        o0,
        t0,
        v,
        rest,
        W1,
        lf,
        N,
        %Merge.name_of_key(x, n, ep): {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, _) == Some{W1}: Maybe<&2, Work<L(d)>>}
        e,
        hb0,
        ho0,
        ht0,
        hpc,
        wc,
        wf,
        held,
        nd,
        kn
      )
    case False{}:
      Merge.next_inv.miss(~d, l, lc, hb, ho, ht, hc, P, k, n, v, x, rest, W1, lf, N, e, wc, wf, held, nd, ep, inv)

# what the merge of the key x does to the resource n
def Merge.next_inv(
  ~d: Led(),
  +l: L(d),
  +lc: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +W1: Work<L(d)>,
  +lf: L(d),
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes(Merge.nodes(~d, W1), N),
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest)
) -> Merge.Inv(~d, lf, Merge.root(~d, W1), n, k, v, rest):
  Merge.next_inv.at(
    ~d,
    Shared.List.is_eq(~U32, ~U32.is_eq, x, Key.res(n)),
    l,
    lc,
    hb,
    ho,
    ht,
    hc,
    P,
    k,
    n,
    b0,
    o0,
    t0,
    v,
    x,
    rest,
    W1,
    lf,
    N,
    e,
    hb0,
    ho0,
    ht0,
    hpc,
    wc,
    wf,
    held,
    nd,
    {==},
    inv
  )
# the induction hypothesis of Merge.all_inv for the keys rest
def Merge.InvIH(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +v: Maybe<&2, List<&2, U32>>,
  rest: List<&2, List<&2, U32>>,
  lf: L(d),
  hf: Maybe<&2, Hashes.Hash>,
  N: List<&2, List<&2, U32>>
) -> Type:
  @lc1: L(d) -> @hc1: Maybe<&2, Hashes.Hash> -> @P1: List<&2, List<&2, U32>> -> {
    Merge.all(~d, l, hb, ho, ht, k, rest, Some{Work{lc1, hc1, P1}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>
  } -> Merge.Puts(~d, l, lc1, P1) -> Merge.Inv(~d, lf, hc1, n, k, v, rest) -> Merge.Inv(~d, lf, hf, n, k, v, [])

# Merge.all_inv for the keys x then rest, once the work W1 after the first step
# is known
def Merge.all_inv.con2(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest),
  W1: Work<L(d)>,
  +erest: {Merge.all(~d, l, hb, ho, ht, k, rest, Some{W1}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +enext: {Merge.next(~d, l, hb, ho, ht, k, Work{lc, hc, P}, Res.name(x)) == Some{W1}: Maybe<&2, Work<L(d)>>},
  ih: Merge.InvIH(~d, l, hb, ho, ht, k, n, v, rest, lf, hf, N)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  match W1:
    case Work{+lc1, +hc1, +P1}:
      ih(lc1)(hc1)(P1)(erest)(
        Merge.And.left(
          Merge.Puts(~d, l, lc1, P1),
          Merge.Nodes(P, P1),
          Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
        )
      )(
        Merge.next_inv(
          ~d,
          l,
          lc,
          hb,
          ho,
          ht,
          hc,
          P,
          k,
          n,
          b0,
          o0,
          t0,
          v,
          x,
          rest,
          Work{lc1, hc1, P1},
          lf,
          N,
          enext,
          hb0,
          ho0,
          ht0,
          hpc,
          wc,
          wf,
          held,
          Merge.And.right(
            Merge.Puts(~d, l, lf, N),
            Merge.Nodes(P1, N),
            Merge.all_puts(
              ~d,
              l,
              hb,
              ho,
              ht,
              k,
              rest,
              lc1,
              hc1,
              P1,
              lf,
              hf,
              N,
              erest,
              Merge.And.left(
                Merge.Puts(~d, l, lc1, P1),
                Merge.Nodes(P, P1),
                Merge.next_facts(~d, l, lc, hb, ho, ht, hc, P, k, Res.name(x), Work{lc1, hc1, P1}, enext, wc)
              )
            )
          ),
          inv
        )
      )

# Merge.all_inv for the keys x then rest, once the first step is known
def Merge.all_inv.con(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  +x: List<&2, U32>,
  +rest: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, x <> rest),
  sg: Merge.Stepped(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}),
  ih: Merge.InvIH(~d, l, hb, ho, ht, k, n, v, rest, lf, hf, N)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  (+W1, st) = sg
  (erest, enext) = st
  Merge.all_inv.con2(~d, l, hb, ho, ht, k, n, b0, o0, t0, v, x, rest, lc, hc, P, lf, hf, N, wc, wf, held, hb0, ho0, ht0, hpc, inv, W1, erest, enext, ih)

# a merge of keys, among which is the key of a resource whose pick clashes, keeps
# the resource as it was, and opens its clash
def Merge.all_inv(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b0: Maybe<&2, Requests.Res>,
  +o0: Maybe<&2, Requests.Res>,
  +t0: Maybe<&2, Requests.Res>,
  +v: Maybe<&2, List<&2, U32>>,
  xs: List<&2, List<&2, U32>>,
  +lc: L(d),
  +hc: Maybe<&2, Hashes.Hash>,
  +P: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +e: {Merge.all(~d, l, hb, ho, ht, k, xs, Some{Work{lc, hc, P}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wc: Merge.Puts(~d, l, lc, P),
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{t0}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b0, o0, t0) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  inv: Merge.Inv(~d, lf, hc, n, k, v, xs)
) -> Merge.Inv(~d, lf, hf, n, k, v, []):
  match xs:
    case Nil{}:
      %Merge.work_eq.root(~d, lc, hc, P, lf, hf, N, e): Merge.Inv(~d, lf, _, n, k, v, [])
      inv
    case Con{+x, +rest}:
      Merge.all_inv.con(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b0,
        o0,
        t0,
        v,
        x,
        rest,
        lc,
        hc,
        P,
        lf,
        hf,
        N,
        wc,
        wf,
        held,
        hb0,
        ho0,
        ht0,
        hpc,
        inv,
        Merge.all_step(~d, l, hb, ho, ht, k, x, rest, Work{lc, hc, P}, Work{lf, hf, N}, e),
        lc1 => hc1 => P1 => e1 => wc1 => inv1 => Merge.all_inv(~d, l, hb, ho, ht, k, n, b0, o0, t0, v, rest, lc1, hc1, P1, lf, hf, N, e1, wc1, wf, held, hb0, ho0, ht0, hpc, inv1)
      )
# a clash that is open after all the keys of a merge, or whose key is among no
# keys, is open
def Merge.open_final(
  ~d: Led(),
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +k: Ledgers.Id,
  orr: Merge.Open(~d, lf, hf, n, k, [])
) -> {Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  match orr:
    case Merge.Or.Left{+op}:
      op
    case Merge.Or.Right{+c}:
      Empty.absurd({Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}, Shared.Bool.false_ne_true(c))

# a merge that keeps a resource as the value mo, and opens its clash, gives a
# tree that reads the resource that mo holds, and has the clash open
def Merge.clashes_inv(
  ~d: Led(),
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +k: Ledgers.Id,
  +o: Maybe<&2, Requests.Res>,
  +mo: Maybe<&2, List<&2, U32>>,
  eo2: {Res.found(mo) == o: Maybe<&2, Requests.Res>},
  inv: Merge.Inv(~d, lf, hf, n, k, mo, [])
) -> Merge.And(
  {Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+fin, orr) = inv
  (
    %eo2: {Res.find(~d, lf, hf, n) == Some{_}: Maybe<&2, Maybe<&2, Requests.Res>>}
    Merge.find_res(~d, lf, hf, n, mo, fin),
    Merge.open_final(~d, lf, hf, n, k, orr)
  )

# the merge of the keys of a difference, among which is the key of a resource
# whose pick clashes, once the read of ours is known (fo)
def Merge.clashes_core.at(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +hin: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(n)) == True{}: Bool},
  fo: Merge.Found(~d, l, ho, n, o)
) -> Merge.And(
  {Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+mo, r1) = fo
  (+eo1, +eo2) = r1
  Merge.clashes_inv(
    ~d,
    lf,
    hf,
    n,
    k,
    o,
    mo,
    eo2,
    Merge.all_inv(
      ~d,
      l,
      hb,
      ho,
      ht,
      k,
      n,
      b,
      o,
      th,
      mo,
      ks,
      l,
      ho,
      [],
      lf,
      hf,
      N,
      eall,
      {==},
      wf,
      held,
      hb0,
      ho0,
      ht0,
      hpc,
      (
        Replicas.Hist.find(~Requests.Ask.machine(), ~d, l, lf, ho, Key.res(n), mo, Merge.grows_of(~d, l, l, lf, [], N, {==}, wf, nd))(eo1),
        Merge.Or.Right{hin}
      )
    )
  )

# the merge of the keys of a difference, among which is the key of a resource
# whose pick clashes
def Merge.clashes_core(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  +lf: L(d),
  +hf: Maybe<&2, Hashes.Hash>,
  +N: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{Work{lf, hf, N}}: Maybe<&2, Work<L(d)>>},
  +wf: Merge.Puts(~d, l, lf, N),
  +held: Merge.Held(~d, lf, N),
  +nd: Merge.Nodes([], N),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.And(
  {Res.find(~d, lf, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Clash.open(~d, lf, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  Merge.clashes_core.at(
    ~d,
    l,
    hb,
    ho,
    ht,
    k,
    n,
    b,
    o,
    th,
    ks,
    lf,
    hf,
    N,
    eall,
    wf,
    held,
    nd,
    hb0,
    ho0,
    ht0,
    hpc,
    Merge.clash_in_diff(
      ~d,
      l,
      ho,
      ht,
      n,
      ks,
      o,
      th,
      ediff,
      Merge.clash_diff(~d, l, b, o, th, hpc),
      Merge.find_some(~d, l, ho, n, o, ho0),
      Merge.find_some(~d, l, ht, n, th, ht0)
    ),
    Merge.find_some(~d, l, ho, n, o, ho0)
  )

# the merge of a resource whose pick clashes, as the work that the merge ends
# in, keeps ours and opens the clash in the ledger of its nodes
def Merge.clashes_final(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +ks: List<&2, List<&2, U32>>,
  W: Work<L(d)>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +eall: {Merge.all(~d, l, hb, ho, ht, k, ks, Some{Work{l, ho, []}}) == Some{W}: Maybe<&2, Work<L(d)>>},
  +eroot: {Merge.root(~d, W) == h2: Maybe<&2, Hashes.Hash>},
  +enodes: {Merge.nodes(~d, W) == ns: List<&2, List<&2, U32>>},
  +held: Merge.Held(~d, Merge.ledger(~d, W), Merge.nodes(~d, W)),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>},
  +ediff: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, ho, ht) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>}
) -> Merge.And(
  {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  match W:
    case Work{+lf, +hf, +N}:
      %enodes: Merge.And(
        {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, _, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      %eroot: Merge.And(
        {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, N, l), _, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      %Merge.And.left(
        Merge.Puts(~d, l, lf, N),
        Merge.Nodes([], N),
        Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
      ): Merge.And(
        {Res.find(~d, _, hf, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
        {Clash.open(~d, _, hf, n, k) == Some{True{}}: Maybe<&2, Bool>}
      )
      Merge.clashes_core(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        n,
        b,
        o,
        th,
        ks,
        lf,
        hf,
        N,
        eall,
        Merge.And.left(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        held,
        Merge.And.right(
          Merge.Puts(~d, l, lf, N),
          Merge.Nodes([], N),
          Merge.all_puts(~d, l, hb, ho, ht, k, ks, l, ho, [], lf, hf, N, eall, {==})
        ),
        hb0,
        ho0,
        ht0,
        hpc,
        ediff
      )

# a merge that gives an act, and whose pick of a resource clashes, once it is
# known what it has gone through, keeps ours, and opens the clash
def Merge.clashes_facts(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  fs: Merge.Facts(~d, l, hb, ho, ht, k, h2, ns),
  +hb0: {Res.find(~d, l, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, ht, n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> Merge.And(
  {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}
):
  (+ks, r1) = fs
  (+W, r2) = r1
  (+eall, r3) = r2
  (+eroot, r4) = r3
  (+enodes, r5) = r4
  (+ediff, held) = r5
  Merge.clashes_final(~d, l, hb, ho, ht, k, n, b, o, th, ks, W, h2, ns, eall, eroot, enodes, held, hb0, ho0, ht0, hpc, ediff)

# the pair of two Data
def Merge.to_pair(-A: Data, -B: Data, p: Merge.And(A, B)) -> A & B:
  match p:
    case Tuple{a, b}:
      (a, b)
# a merge that gives an act, and whose pick of a resource clashes, keeps ours
# for it, and opens its clash
def Merge.clashes_go(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +from: Requests.Source,
  +base: Maybe<&2, Requests.Source>,
  +vs: Maybe<&2, List<&2, String>>,
  +h2: Maybe<&2, Hashes.Hash>,
  +ns: List<&2, List<&2, U32>>,
  +n: Resources.Name,
  +b: Maybe<&2, Requests.Res>,
  +o: Maybe<&2, Requests.Res>,
  +th: Maybe<&2, Requests.Res>,
  +e0: {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>},
  +hb0: {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ho0: {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ht0: {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +hpc: {Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>}
) -> {
  Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
}
  & {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>}:
  Merge.to_pair(
    {Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>},
    {Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>},
    Merge.clashes_facts(
      ~d,
      l,
      Base.tree(base),
      Replicas.Tip.content(t),
      Source.root(from),
      k,
      h2,
      ns,
      n,
      b,
      o,
      th,
      Merge.facts_go(~d, l, t, k, from, base, vs, h2, ns, e0),
      hb0,
      ho0,
      ht0,
      hpc
    )
  )

# a merge never loses a change that only one side made: when the merge of a
# resource takes the content of one side (Pick.merge: theirs when ours is the
# base, ours when theirs is the base or both agree), the tree that a taken
# merge gives holds the resource with that content
law Merge.act_takes:
  for ~d: Led()
  for l: L(d)
  for t: Replicas.Tip
  for k: Ledgers.Id
  for from: Requests.Source
  for base: Maybe<&2, Requests.Source>
  for vs: Maybe<&2, List<&2, String>>
  for h2: Maybe<&2, Hashes.Hash>
  for ns: List<&2, List<&2, U32>>
  for n: Resources.Name
  for b: Maybe<&2, Requests.Res>
  for o: Maybe<&2, Requests.Res>
  for th: Maybe<&2, Requests.Res>
  for x: Maybe<&2, Requests.Res>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {
      Pick.merge(~d, l, b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>
    }
    -> {
      Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
        == Some{x}: Maybe<&2, Maybe<&2, Requests.Res>>
    }

def Merge.act_takes(d, l, t, k, from, base, vs, h2, ns, n, b, o, th, x):
  e0 => hb0 => ho0 => ht0 => hp => Merge.takes_go(~d, l, t, k, from, base, vs, h2, ns, n, b, o, th, x, e0, hb0, ho0, ht0, hp)

# a merge keeps what both sides hold the same, and opens a clash only where
# the merge of a resource clashes: when the merge of a resource clashes, the
# tree that a taken merge gives holds ours for it, and its clash is open
law Merge.act_clashes:
  for ~d: Led()
  for l: L(d)
  for t: Replicas.Tip
  for k: Ledgers.Id
  for from: Requests.Source
  for base: Maybe<&2, Requests.Source>
  for vs: Maybe<&2, List<&2, String>>
  for h2: Maybe<&2, Hashes.Hash>
  for ns: List<&2, List<&2, U32>>
  for n: Resources.Name
  for b: Maybe<&2, Requests.Res>
  for o: Maybe<&2, Requests.Res>
  for th: Maybe<&2, Requests.Res>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {
      Pick.merge(~d, l, b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>
    }
    -> (
      {
        Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
          == Some{o}: Maybe<&2, Maybe<&2, Requests.Res>>
      }
        & {
          Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == Some{True{}}: Maybe<&2, Bool>
        }
    )

def Merge.act_clashes(d, l, t, k, from, base, vs, h2, ns, n, b, o, th):
  e0 => hb0 => ho0 => ht0 => hpc => Merge.clashes_go(~d, l, t, k, from, base, vs, h2, ns, n, b, o, th, e0, hb0, ho0, ht0, hpc)

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
def Affects.branch_refl(a: Branch) -> {Branch.is_eq(a, a) == True{}: Bool}:
  match a:
    case Branch{+s, +n}:
      Shared.List.all.if_both(
        Hashes.Hash.is_eq(s, s),
        u => String.eq(n, n)
      )(Hashes.Hash.is_eq_refl(s))(Texts.String.eq_refl(n))

# branches that are the same are equal
def Affects.branch_sound(a: Branch, b: Branch) -> {Branch.is_eq(a, b) == True{}: Bool} -> {a == b: Branch}:
  match a b:
    case Branch{+s1, +n1} Branch{+s2, +n2}:
      +h =>
        %Equal.sym(
          Hashes.Hash,
          s1,
          s2,
          Hashes.Hash.is_eq_sound(s1, s2)(Shared.List.all.if_hit(Hashes.Hash.is_eq(s1, s2), u => String.eq(n1, n2))(h))
        ): {Branch{_, n1} == Branch{s2, n2}: Branch}
        %Equal.sym(
          String,
          n1,
          n2,
          Texts.String.eq_sound(n1, n2)(Shared.List.all.if_rest(Hashes.Hash.is_eq(s1, s2), u => String.eq(n1, n2))(h))
        ): {Branch{s2, _} == Branch{s2, n2}: Branch}
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
def Affects.range(d: Led()) -> Trees.Laws.Range(L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
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
def Affects.diff(d: Led()) -> Trees.Laws.Diff(L(d), Replicas.Led.tree(Requests.Ask.machine(), d)):
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
def Affects.known_taken(~d: Led(), l: L(d), t: Replicas.Tip, n: U32, -x: Replicas.Taken) -> {
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  Res.name(k) == Some{u}: Maybe<&2, Resources.Name>
} -> {Key.res(u) == k: List<&2, U32>}:
  match k:
    case Nil{}:
      h => Empty.absurd({Key.res(u) == []: List<&2, U32>}, Shared.Maybe.none_ne_some(Resources.Name, u, h))
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
        {Key.res(u) == U32{WCon{True{}, t}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{True{}, t}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{True{}, t}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{True{}, t}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{True{}, t}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )
    case Con{U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}, r}:
      h => Empty.absurd(
        {Key.res(u) == U32{WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, t}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} <> r: List<&2, U32>},
        Shared.Maybe.none_ne_some(Resources.Name, u, h)
      )

# the laws of Resources.Name.is_eq
def Affects.name_laws() -> Shared.Eq.Laws(Resources.Name, Resources.Name.is_eq):
  (n => Resources.Name.is_eq_refl(n), a => b => Resources.Name.is_eq_sound(a, b))

# the laws of Trees.Binding.is_eq
def Affects.binding_laws() -> Shared.Eq.Laws(Trees.Binding, Trees.Binding.is_eq):
  (a => Affects.binding_refl(a), a => b => Affects.binding_sound(a, b))

# the key of a resource names it
def Affects.name_key(+n: Resources.Name) -> {Res.name(Key.res(n)) == Some{n}: Maybe<&2, Resources.Name>}:
  Codes.Code.whole_read(~Resources.Name, ~Resources.Name.code, ~Resources.Name.code.read, ~(a => r => Resources.Name.code_read(a, r)), n)

# Affects.range_has, from the law of a listing
def Affects.range_has.of(
  ~d: Led(),
  l: L(d),
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
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +p: List<&2, U32>,
  +bs: List<&2, Trees.Binding>,
  e: {Tree.range(~d, l, h, p) == Some{bs}: Maybe<&2, List<&2, Trees.Binding>>},
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
  ~d: Led(),
  l: L(d),
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
def Affects.same_refl(a: Maybe<&2, Requests.Res>) -> {Res.same(a, a) == True{}: Bool}:
  match a:
    case None{}:
      {==}
    case Some{x}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Requests.Res.code(x, []))

# Affects.find_named once the binding is known to name u, and its value to be
# the resource r1
def Affects.find_named.of(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool} -> P,
  +k0: List<&2, U32>,
  +v0: List<&2, U32>,
  +r1: Requests.Res,
  +hc: {List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{k0, v0}) == True{}: Bool},
  +ef: {Res.found(Some{v0}) == Some{r1}: Maybe<&2, Requests.Res>},
  +ek: {Key.res(u) == k0: List<&2, U32>}
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
    Key.res(u),
    Equal.sym(List<&2, U32>, Key.res(u), k0, ek),
    Affects.value_known(look0, v0)(evalue)
  )
  k(Res.found(Some{v0}))(
    Affects.cast(
      Maybe<&2, Maybe<&2, List<&2, U32>>>,
      z => {
        Maybe.bind(&2, Maybe<&2, List<&2, U32>>, Maybe<&2, Requests.Res>, z, m => Some{Res.found(m)})
          == Some{Res.found(Some{v0})}: Maybe<&2, Maybe<&2, Requests.Res>>
      },
      Some{Some{v0}},
      Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Key.res(u))),
      Equal.sym(
        Maybe<&2, Maybe<&2, List<&2, U32>>>,
        Trees.Look.known(Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Key.res(u))),
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
      Res.found(Some{v0}),
      Equal.sym(Maybe<&2, Requests.Res>, Res.found(Some{v0}), Some{r1}, ef),
      {==}
    )
  )

# Affects.find_named for a binding b of xs that names u
def Affects.find_named.at(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
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
        Res.found(Some{v0}),
        r => Res.name(k0),
        u,
        +r1 => ef => en => Affects.find_named.of(~d, l, hb, xs, er, u, P, k, k0, v0, r1, hc, ef, Affects.key_of_name(k0, u)(en))
      )(hn)

# a resource of a listing of a tree is there: Res.find gives some resource
def Affects.find_named(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  -P: Type,
  k: @r0: Maybe<&2, Requests.Res> -> {Res.find(~d, l, hb, u) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>}
    -> {Maybe.is_some(&2, Requests.Res, r0) == True{}: Bool} -> P
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool} -> P:
  h => Affects.names_in(xs, u, P, +b => hc => hn => Affects.find_named.at(~d, l, hb, xs, er, u, P, k, b, hc)(hn))(h)

# Affects.find_names once the read m0 of the key of u is known
def Affects.find_names.at(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  +r0: Requests.Res,
  m0: Maybe<&2, List<&2, U32>>,
  +em0: {
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, hb, Key.res(u)) == Some{m0}: Maybe<&2, Maybe<&2, List<&2, U32>>>
  },
  +ef: {Res.found(m0) == Some{r0}: Maybe<&2, Requests.Res>}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool}:
  match m0:
    case None{}:
      Empty.absurd(
        {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool},
        Shared.Maybe.none_ne_some(Requests.Res, r0, ef)
      )
    case Some{+v}:
      +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, hb, Key.res(u))
      +evalue = Affects.known_value(look0, Some{v})(em0)
      Affects.names_of(
        xs,
        Trees.Binding{Key.res(u), v},
        u,
        Affects.cast(
          Maybe<&2, Requests.Res>,
          z => {Maybe.bind(&2, Requests.Res, Resources.Name, z, r => Res.name(Key.res(u))) == Some{u}: Maybe<&2, Resources.Name>},
          Some{r0},
          Res.found(Some{v}),
          Equal.sym(Maybe<&2, Requests.Res>, Res.found(Some{v}), Some{r0}, ef),
          Affects.name_key(u)
        )
      )(
        Equal.trans(
          Bool,
          List.contains(~Trees.Binding, ~Trees.Binding.is_eq, xs, Trees.Binding{Key.res(u), v}),
          Bool.and(
            Trees.Key.leads([0], Key.res(u)),
            Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Some{v})
          ),
          True{},
          Affects.range_has(~d, l, hb, [0], xs, er, Key.res(u), v),
          Affects.cast(
            Maybe<&2, List<&2, U32>>,
            z => {
              Bool.and(
                Trees.Key.leads([0], Key.res(u)),
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
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
  +u: Resources.Name,
  +r0: Requests.Res
) -> {Res.find(~d, l, hb, u) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>}
  -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool}:
  ef => Affects.bind_some(
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Requests.Res>,
    {List.contains(~Resources.Name, ~Resources.Name.is_eq, Res.names(xs), u) == True{}: Bool},
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, hb, Key.res(u)),
    m => Some{Res.found(m)},
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
      Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Res.found(m0), Some{r0}, e2)
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
  +en: {Res.name(k) == Some{c}: Maybe<&2, Resources.Name>},
  ih: {List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, k) == True{}: Bool}
    -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(rest), c) == True{}: Bool}
) -> {
  List.any.if(w => List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), rest, k), b) == True{}: Bool
} -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Res.name(j), Keys.names(rest)), c)
    == True{}: Bool
}:
  match b:
    case True{}:
      h => Affects.cast(
        List<&2, U32>,
        z => {
          List.contains(~Resources.Name, ~Resources.Name.is_eq, Shared.Maybe.cons(Resources.Name, Res.name(z), Keys.names(rest)), c)
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
          Res.name(k),
          Equal.sym(Maybe<&2, Resources.Name>, Res.name(k), Some{c}, en),
          Affects.contains_head(~Resources.Name, ~Resources.Name.is_eq, ~Affects.name_laws(), c, Keys.names(rest))
        )
      )
    case False{}:
      h => Affects.cons_keep(Res.name(j), Keys.names(rest), c)(ih(h))

# the name of a key among ks is among the names of ks
def Affects.keys_of(
  ks: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +c: Resources.Name,
  +en: {Res.name(k) == Some{c}: Maybe<&2, Resources.Name>}
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
  +ns: {Bool.not(Res.same(a, b)) == True{}: Bool}
) -> {Bool.not(q) == True{}: Bool}:
  match q:
    case True{}:
      Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Affects.cast(
            Bool,
            z => {Bool.not(z) == True{}: Bool},
            Res.same(a, b),
            True{},
            Affects.cast(
              Maybe<&2, Requests.Res>,
              z => {Res.same(a, z) == True{}: Bool},
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
  ~d: Led(),
  +l: L(d),
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +ed: {Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, h) == Some{ks}: Maybe<&2, List<&2, List<&2, U32>>>},
  +c: Resources.Name,
  +a: Maybe<&2, Requests.Res>,
  +b: Maybe<&2, Requests.Res>,
  +ns: {Bool.not(Res.same(a, b)) == True{}: Bool},
  +m1: Maybe<&2, List<&2, U32>>,
  +m0: Maybe<&2, List<&2, U32>>,
  +em1: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(c)) == Some{m1}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +em0: {Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h0, Key.res(c)) == Some{m0}: Maybe<&2, Maybe<&2, List<&2, U32>>>},
  +ea: {Res.found(m1) == a: Maybe<&2, Requests.Res>},
  +eb: {Res.found(m0) == b: Maybe<&2, Requests.Res>}
) -> {List.contains(~Resources.Name, ~Resources.Name.is_eq, Keys.names(ks), c) == True{}: Bool}:
  +look1 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h, Key.res(c))
  +look0 = Replicas.Tree.look(~Requests.Ask.machine(), ~d, l, h0, Key.res(c))
  +e1 = Affects.known_value(look1, m1)(em1)
  +e0 = Affects.known_value(look0, m0)(em0)
  +iseq = Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), Trees.Look.value(look0), Trees.Look.value(look1))
  Affects.keys_of(ks, Key.res(c), c, Affects.name_key(c))(
    Equal.trans(
      Bool,
      List.contains(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), ks, Key.res(c)),
      Bool.not(iseq),
      True{},
      Affects.diff_has(~d, l, h0, h, ks, ed, Key.res(c)),
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
          Res.found(m1),
          b,
          Equal.sym(Maybe<&2, Requests.Res>, Res.found(m1), a, ea),
          Equal.trans(
            Maybe<&2, Requests.Res>,
            Res.found(m1),
            Res.found(m0),
            b,
            Equal.cong(
              Maybe<&2, List<&2, U32>>,
              Maybe<&2, Requests.Res>,
              Res.found,
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
  ~d: Led(),
  +l: L(d),
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
    Res.find(~d, l, h, c),
    a => Maybe.bind(
      &2,
      Maybe<&2, Requests.Res>,
      Bool,
      Res.find(~d, l, h0, c),
      b => Some{Bool.not(Res.same(a, b))}
    ),
    True{},
    +a => ea => e2 => Affects.bind_some(
      Maybe<&2, Requests.Res>,
      Bool,
      goal,
      Res.find(~d, l, h0, c),
      b => Some{Bool.not(Res.same(a, b))},
      True{},
      +b => eb => e3 => Affects.bind_some(
        Maybe<&2, List<&2, U32>>,
        Maybe<&2, Requests.Res>,
        goal,
        Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(c)),
        m => Some{Res.found(m)},
        a,
        +m1 => em1 => fa => Affects.bind_some(
          Maybe<&2, List<&2, U32>>,
          Maybe<&2, Requests.Res>,
          goal,
          Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h0, Key.res(c)),
          m => Some{Res.found(m)},
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
            Shared.Maybe.some_inj(Bool, Bool.not(Res.same(a, b)), True{}, e3),
            m1,
            m0,
            em1,
            em0,
            Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Res.found(m1), a, fa),
            Shared.Maybe.some_inj(Maybe<&2, Requests.Res>, Res.found(m0), b, fb)
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c: Resources.Name,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  +i: Ledgers.Id,
  +hy: Maybe<&2, Hashes.Hash>,
  +ks: List<&2, List<&2, U32>>,
  +m: U32,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
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
      %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, Tree.range(~d, l, hb, [0]), Some{xs}, er): {
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  +efind: {Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{r0}: Maybe<&2, Maybe<&2, Requests.Res>>},
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
                  Res.find(~d, l, hb, used),
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
                Res.find(~d, l, hb, used),
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
            Res.find(~d, l, hb, used),
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
          Res.find(~d, l, hb, used),
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
  %Equal.sym(Maybe<&2, Maybe<&2, Requests.Res>>, Res.find(~d, l, hb, used), Some{r0}, efind): {
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +b: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +tf: Replicas.Tip,
  +b: Branch,
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
    Tree.range(~d, l, hb, [0]),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +tf: Replicas.Tip,
  +b: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +b: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  es: List<&2, BranchEntry>,
  +b: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  b: Branch,
  +ts: List<&2, Touch>,
  +x: Touch
) -> {Node.affects(~d, ~kern, l, view, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
  -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}:
  match b:
    case Branch{+st, +n}:
      e => +hc => Affects.bind_some(
        List<&2, BranchEntry>,
        List<&2, Touch>,
        {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>},
        Node.branches(~d, ~kern, l, st),
        es => Branches.touch(~d, ~kern, l, view, es, Branch{st, n}),
        ts,
        +es => ees => e2 => Affects.branches_in(~d, ~kern, l, view, es, Branch{st, n}, ts, x)(e2)(hc)
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  +c1: Resources.Name,
  +rest: List<&2, Resources.Name>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +v: Ledgers.Id,
  +h0: Maybe<&2, Hashes.Hash>,
  +h: Maybe<&2, Hashes.Hash>,
  changed: List<&2, Resources.Name>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  +i: Ledgers.Id,
  +hy: Maybe<&2, Hashes.Hash>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  +tf: Replicas.Tip,
  xs: List<&2, Replicas.Taken>,
  +n: U32,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
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
    -> @r0: Requests.Res -> {Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>}
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
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
  +efind: {Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{r}: Maybe<&2, Maybe<&2, Requests.Res>>}
) -> {Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  match r:
    case None{}:
      e => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e)))
    case Some{+r0}:
      e => k(m)(enum)(elt)(hz)(ebef)(hX)(etk)(d1)(d2)(r0)(efind)(e)

# Affects.at_facts once the test whether tb holds something else is known
def Affects.at_facts.dif(
  ~d: Led(),
  +l: L(d),
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
) -> {Shared.Bool.when(Maybe<&2, Bool>, dv, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
  match dv:
    case False{}:
      e => Empty.absurd(R, Shared.Bool.false_ne_true(Shared.Maybe.some_inj(Bool, False{}, True{}, e)))
    case True{}:
      e => Affects.bind_some(
        Maybe<&2, Requests.Res>,
        Bool,
        R,
        Res.find(~d, l, Replicas.Tip.content(tb), used),
        r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}}),
        True{},
        +r => +efind => e2 => Affects.at_facts.find(~d, l, view, tf, tb, v, changed, used, R, k, m, enum, elt, hz, ebef, hX, etk, d1, ed, r, efind)(e2)
      )(e)

# Affects.at_facts once the taken request x0 of the number m is known
def Affects.at_facts.ver(
  ~d: Led(),
  +l: L(d),
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
  Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}})))
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
        h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}})),
        True{},
        +hv => +ever => e3 => Affects.bind_some(
          Bool,
          Bool,
          R,
          Res.differs(~d, l, hv, Replicas.Tip.content(tb), changed),
          differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}),
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
  ~d: Led(),
  +l: L(d),
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
) -> {Shared.Bool.when(Maybe<&2, Bool>, w, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}}) == Some{True{}}: Maybe<&2, Bool>} -> R:
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
  ~d: Led(),
  +l: L(d),
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
    m => Maybe.bind(&2, Bool, Bool, Version.wrote(~d, l, tf, m, changed), wrote => Shared.Bool.when(Maybe<&2, Bool>, wrote, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}})),
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
        wrote => Shared.Bool.when(Maybe<&2, Bool>, wrote, u => Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Bool, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), h => Maybe.bind(&2, Bool, Bool, Res.differs(~d, l, h, Replicas.Tip.content(tb), changed), differs => Shared.Bool.when(Maybe<&2, Bool>, differs, u2 => Maybe.bind(&2, Maybe<&2, Requests.Res>, Bool, Res.find(~d, l, Replicas.Tip.content(tb), used), r => Shared.Bool.when(Maybe<&2, Bool>, Maybe.is_some(&2, Requests.Res, r), u3 => Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed), u3 => Some{False{}})), u2 => Some{False{}}))), u => Some{False{}}),
        True{},
        +w => +ew => e2 => Affects.at_facts.wrote(~d, l, view, tf, tb, v, changed, used, R, k, m, enum, elt, eisof, w, ew)(e2)
      )(e1)
    )(enum)
  )(e)

# what Touch.holds reads, when it holds
def Affects.holds_facts(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
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
  %Equal.sym(Maybe<&2, List<&2, Trees.Binding>>, Tree.range(~d, l, hb, [0]), Some{xs}, er): {
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +hb: Maybe<&2, Hashes.Hash>,
  +xs: List<&2, Trees.Binding>,
  +er: {Tree.range(~d, l, hb, [0]) == Some{xs}: Maybe<&2, List<&2, Trees.Binding>>},
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +st: Hashes.Hash,
  +nf: String,
  +tf: Replicas.Tip,
  -R: Type,
  k: @rt: Replicas.Tip -> {Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st) == Some{rt}: Maybe<&2, Replicas.Tip>}
    -> @ws: List<&2, U32> -> {Replicas.Tip.get(~Requests.Ask.machine(), ~d, l, rt, Replicas.Log.start(nf)) == Some{ws}: Maybe<&2, List<&2, U32>>}
    -> R
) -> {Branch.head(~d, ~kern, l, Branch{st, nf}) == Some{tf}: Maybe<&2, Replicas.Tip>} -> R:
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
  ~d: Led(),
  +l: L(d),
  +rt: Replicas.Tip,
  +lx: List<&2, Trees.Binding>,
  +elx: {Tree.range(~d, l, Replicas.Tip.log(rt), [5]) == Some{lx}: Maybe<&2, List<&2, Trees.Binding>>},
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
  ~d: Led(),
  +l: L(d),
  +bb: Branch,
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +n1: String,
  +rest: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Branch,
  +x: Touch,
  +r0: List<&2, BranchEntry>,
  q: Bool,
  eq: {String.eq(n1, nf) == q: Bool},
  +hn: {List.any.if(w => List.contains(~String, ~String.eq, rest, nf), q) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool},
  ih: {List.contains(~String, ~String.eq, rest, nf) == True{}: Bool}
    -> (
      @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
        -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool}
    )
    -> @ts2: List<&2, Touch> -> {Branches.touch(~d, ~kern, l, view, r0, b) == Some{ts2}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts2, x) == True{}: Bool},
  +a: List<&2, Touch>,
  +ea: {Branch.touches(~d, ~kern, l, view, Branch{st, n1}, b) == Some{a}: Maybe<&2, List<&2, Touch>>},
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
            z => {Branch.touches(~d, ~kern, l, view, Branch{st, z}, b) == Some{a}: Maybe<&2, List<&2, Touch>>},
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +n1: String,
  +rest: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Branch,
  +x: Touch,
  +vs: List<&2, String>,
  +hv: Maybe<&2, Ledgers.Id>,
  +r0: List<&2, BranchEntry>,
  q: Bool,
  eq: {String.eq(n1, nf) == q: Bool},
  +hn: {List.any.if(w => List.contains(~String, ~String.eq, rest, nf), q) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool},
  ih: {List.contains(~String, ~String.eq, rest, nf) == True{}: Bool}
    -> (
      @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
        -> {List.contains(~Touch, ~Touch.is_eq, a, x) == True{}: Bool}
    )
    -> @ts2: List<&2, Touch> -> {Branches.touch(~d, ~kern, l, view, r0, b) == Some{ts2}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts2, x) == True{}: Bool},
  +ts: List<&2, Touch>
) -> {
  Branches.touch(~d, ~kern, l, view, BranchEntry{Branch{st, n1}, vs, hv} <> r0, b) == Some{ts}: Maybe<&2, List<&2, Touch>>
} -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}:
  e => Affects.bind_some(
    List<&2, Touch>,
    List<&2, Touch>,
    {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool},
    Branch.touches(~d, ~kern, l, view, Branch{st, n1}, b),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  ns: List<&2, String>,
  +st: Hashes.Hash,
  +nf: String,
  +b: Branch,
  +x: Touch,
  +es: List<&2, BranchEntry>,
  +ee: {Branches.entries(~d, ~kern, l, Branches.of(st, ns)) == Some{es}: Maybe<&2, List<&2, BranchEntry>>},
  +hn: {List.contains(~String, ~String.eq, ns, nf) == True{}: Bool},
  hk: @a: List<&2, Touch> -> {Branch.touches(~d, ~kern, l, view, Branch{st, nf}, b) == Some{a}: Maybe<&2, List<&2, Touch>>}
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
        BranchEntry.of(~d, l, Branch{st, n1}, Branch.head(~d, ~kern, l, Branch{st, n1})),
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
            Branch{st, n1},
            Branch.head(~d, ~kern, l, Branch{st, n1}),
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
                BranchEntry{Branch{st, n1}, vs, hv} <> r0,
                Equal.trans(
                  List<&2, BranchEntry>,
                  es,
                  e0 <> r0,
                  BranchEntry{Branch{st, n1}, vs, hv} <> r0,
                  Equal.sym(List<&2, BranchEntry>, e0 <> r0, es, ees),
                  Equal.cong(
                    BranchEntry,
                    List<&2, BranchEntry>,
                    z => z <> r0,
                    e0,
                    BranchEntry{Branch{st, n1}, vs, hv},
                    Equal.sym(BranchEntry, BranchEntry{Branch{st, n1}, vs, hv}, e0, e0eq)
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +tf: Replicas.Tip,
  +b: Branch,
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
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  +tf: Replicas.Tip,
  +b: Branch,
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
  +efind: {Res.find(~d, l, Replicas.Tip.content(tb), used) == Some{Some{r0}}: Maybe<&2, Maybe<&2, Requests.Res>>},
  +ereach: {Uses.reaches(~d, l, view, Replicas.Tip.content(tb), used, changed) == Some{True{}}: Maybe<&2, Bool>},
  +a: List<&2, Touch>
) -> {Branch.touches.at(~d, l, view, from, tf, b, tb) == Some{a}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool}:
  +hb = Replicas.Tip.content(tb)
  e => Affects.bind_some(
    List<&2, Trees.Binding>,
    List<&2, Touch>,
    {List.contains(~Touch, ~Touch.is_eq, a, Touch{from, v, changed, b, used}) == True{}: Bool},
    Tree.range(~d, l, hb, [0]),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +s1: Hashes.Hash,
  +nf: String,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +st: Hashes.Hash,
  +n: String,
  +used: Resources.Name
) -> {Touch.holds(~d, ~kern, l, view, Touch{Branch{s1, nf}, v, changed, Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>}
  -> {s1 == st: Hashes.Hash}:
  e => Affects.when_is(
    Maybe<&2, Bool>,
    {s1 == st: Hashes.Hash},
    Branch.other(Branch{s1, nf}, Branch{st, n}),
    u => Maybe.bind(
      &2,
      Replicas.Tip,
      Bool,
      Branch.head(~d, ~kern, l, Branch{s1, nf}),
      tf => Maybe.bind(
        &2,
        Replicas.Tip,
        Bool,
        Branch.head(~d, ~kern, l, Branch{st, n}),
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +st: Hashes.Hash,
  +nf: String,
  +v: Ledgers.Id,
  +changed: Resources.Name,
  +n: String,
  +used: Resources.Name,
  +ts: List<&2, Touch>,
  hh: {
    Touch.holds(~d, ~kern, l, view, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>
  }
) -> {Node.affects(~d, ~kern, l, view, Branch{st, n}) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool}:
  +ea => Affects.holds_facts(
    ~d,
    ~kern,
    l,
    view,
    Branch{st, nf},
    v,
    changed,
    Branch{st, n},
    used,
    {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
    +eo => +tf => +ef => +tb => +eb => +m => +enum => +elt => +hz => +ebef => +hX => +etk => +d1 => +d2 => +r0 => +efind => +ereach => Affects.bind_some(
      List<&2, BranchEntry>,
      List<&2, Touch>,
      {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
      Node.branches(~d, ~kern, l, st),
      es => Branches.touch(~d, ~kern, l, view, es, Branch{st, n}),
      ts,
      +es => +ees => +et => Affects.bind_some(
        List<&2, Branch>,
        List<&2, BranchEntry>,
        {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
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
          {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
          +rt => +ert => +ws => +ews => Affects.map_some(
            List<&2, Trees.Binding>,
            List<&2, Branch>,
            {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{st, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
            xs => Branches.of(st, Branches.names(xs)),
            Tree.range(~d, l, Replicas.Tip.log(rt), [5]),
            bs,
            +lx => +elx => +ebx => Affects.touch_has(
              ~d,
              ~kern,
              l,
              view,
              Branches.names(lx),
              st,
              nf,
              Branch{st, n},
              Touch{Branch{st, nf}, v, changed, Branch{st, n}, used},
              es,
              Affects.cast(
                List<&2, Branch>,
                z => {Branches.entries(~d, ~kern, l, z) == Some{es}: Maybe<&2, List<&2, BranchEntry>>},
                bs,
                Branches.of(st, Branches.names(lx)),
                Equal.sym(List<&2, Branch>, Branches.of(st, Branches.names(lx)), bs, ebx),
                eent
              ),
              Affects.started_in(~d, l, rt, lx, elx, nf, ws, ews),
              +a => ea2 => Affects.at_has(
                ~d,
                l,
                view,
                Branch{st, nf},
                tf,
                Branch{st, n},
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
                  Branch.touches.at(~d, l, view, Branch{st, nf}, tf, Branch{st, n}, tb),
                  Branch.touches(~d, ~kern, l, view, Branch{st, nf}, Branch{st, n}),
                  Some{a},
                  Equal.sym(
                    Maybe<&2, List<&2, Touch>>,
                    Branch.touches(~d, ~kern, l, view, Branch{st, nf}, Branch{st, n}),
                    Branch.touches.at(~d, l, view, Branch{st, nf}, tf, Branch{st, n}, tb),
                    Affects.touches_at_of(~d, ~kern, l, view, Branch{st, nf}, tf, Branch{st, n}, tb, eo, ef, eb)
                  ),
                  ea2
                )
              ),
              ts
            )(et)
          )(
            Affects.cast(
              Maybe<&2, Replicas.Tip>,
              z => {Store.branches(~d, l, st, z) == Some{bs}: Maybe<&2, List<&2, Branch>>},
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
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  x: Touch,
  +ts: List<&2, Touch>
) -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}
  -> {Node.affects(~d, ~kern, l, view, Touch.branch(x)) == Some{ts}: Maybe<&2, List<&2, Touch>>}
  -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}:
  match x:
    case Touch{Branch{+s1, +nf}, +v, +changed, Branch{+st, +n}, +used}:
      +hh => ea => Affects.cast(
        Hashes.Hash,
        z => {List.contains(~Touch, ~Touch.is_eq, ts, Touch{Branch{z, nf}, v, changed, Branch{st, n}, used}) == True{}: Bool},
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
              Touch.holds(~d, ~kern, l, view, Touch{Branch{z, nf}, v, changed, Branch{st, n}, used}) == Some{True{}}: Maybe<&2, Bool>
            },
            s1,
            st,
            Affects.other_store(~d, ~kern, l, view, s1, nf, v, changed, st, n, used)(hh),
            hh
          )
        )(ea)
      )

# writers are told only about changes to what their work uses: each touch
# that Node.affects gives for a branch holds (Touch.holds)
law Node.affects_holds:
  for ~d: Led()
  for ~kern: Kern(d)
  for ~rules: Kernel.Rules(d, kern)
  for l: L(d)
  for view: List<&2, Formats.Cond>
  for b: Branch
  for ts: List<&2, Touch>
  for x: Touch
  {Node.affects(~d, ~kern, l, view, b) == Some{ts}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}
    -> {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}

def Node.affects_holds(d, kern, rules, l, view, b, ts, x):
  Affects.holds_law(~d, ~kern, l, view, b, ts, x)

# and they are told about each of them: a touch that holds is among the
# touches that Node.affects gives for its branch
law Node.affects_complete:
  for ~d: Led()
  for ~kern: Kern(d)
  for ~rules: Kernel.Rules(d, kern)
  for l: L(d)
  for view: List<&2, Formats.Cond>
  for x: Touch
  for ts: List<&2, Touch>
  {Touch.holds(~d, ~kern, l, view, x) == Some{True{}}: Maybe<&2, Bool>}
    -> {Node.affects(~d, ~kern, l, view, Touch.branch(x)) == Some{ts}: Maybe<&2, List<&2, Touch>>}
    -> {List.contains(~Touch, ~Touch.is_eq, ts, x) == True{}: Bool}

def Node.affects_complete(d, kern, rules, l, view, x, ts):
  Affects.complete_law(~d, ~kern, l, view, x, ts)
