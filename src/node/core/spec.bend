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
import ../../shared/shared/shared/shared/trie.bend as Tries
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

# the bindings of the tree whose root is h whose keys start with p; none when
# l lacks a node of the tree
def Tree.list(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, p: List<&2, U32>) -> List<&2, Trees.Binding>:
  Maybe.default(&2, List<&2, Trees.Binding>, Tree.range(~d, l, h, p), [])

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

# the resources that still clash after the merge k, in the tree h
def Clash.names(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  k: Ledgers.Id
) -> List<&2, Resources.Name>:
  Maybe.default(
    &2,
    List<&2, Resources.Name>,
    Codes.Code.whole.of(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k))
    ),
    []
  )

# a resource of the tree h still clashes after the merge k
def Clash.left(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, k: Ledgers.Id) -> Bool:
  Bool.not(List.is_empty(&2, Resources.Name, Clash.names(~d, l, h, k)))

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
) -> Bool:
  List.contains(~Resources.Name, ~Resources.Name.is_eq, Clash.names(~d, l, h, k), n)

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
      Work.set(
        ~d,
        Work{l, h, ns},
        Key.clashes(k),
        Clash.value(Clash.put(n, Clash.names(~d, l, h, k)))
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
# resource holds x and the clash is shut; else it is stale
def Resolve.act.of(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Clash.open(~d, l, Replicas.Tip.content(t), n, k),
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
            Clash.value(
              Shared.List.remove(
                ~Resources.Name,
                ~Resources.Name.is_eq,
                Clash.names(~d, l, Replicas.Tip.content(t), k),
                n
              )
            )
          )
        )
      ),
      v => None{}
    ),
    u => Some{Replicas.Act.Stale{}}
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
    List.all.if(u => Tree.kept(~d, l, hb), Tree.kept(~d, l, ht)),
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
def Node.key(n: String) -> List<&2, Bool>:
  False{} <> Tries.Trie.text(n)

# the key of the group g in the graph of members
def Group.key(g: String) -> List<&2, Bool>:
  True{} <> Tries.Trie.text(g)

# the key of each of the members ms
def Members.keys(ms: List<&2, Requests.Member>) -> List<&2, List<&2, Bool>>:
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
def Nodes.inside(ns: List<&2, String>, +reach: Tries.Trie<Unit>) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      List.filter.put(String, n, Nodes.inside(rest, reach), Tries.Trie.has(Unit, reach, Node.key(n)))

# what the group g reaches among the groups gs: each member, and each member
# of one, at any depth
def Group.reach(+gs: List<&2, Group>, g: String) -> Tries.Trie<Unit>:
  Reaches.Graph.reach(Groups.graph(gs, Reaches.Graph.new()), Group.key(g))

# the nodes of the group g among the groups gs, each once
def Group.nodes.of(+gs: List<&2, Group>, g: String) -> List<&2, String>:
  KeySets.KeySet.unique(
    ~String,
    ~String.eq,
    ~Tries.Trie.text,
    Nodes.inside(Groups.nodes(gs), Group.reach(gs, g)),
    Tries.Trie.new(String)
  )

# the groups of the tree whose root is h
def Groups.in(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> List<&2, Group>:
  Groups.of(Tree.list(~d, l, h, [2]))

# the nodes of the group g in the tree whose root is h, each once: the nodes
# that own what g owns. A clear def: it walks the tree
def Group.nodes(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, g: String) -> List<&2, String>:
  Group.nodes.of(Groups.in(~d, l, h), g)

# Group.act once the tree with the new members is known: stale when the group
# then reaches itself
def Group.act.of(~d: Led(), l: L(d), +g: String, p: Maybe<&2, Trees.Edit>) -> Maybe<&2, Replicas.Act>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Act>,
        Tries.Trie.has(
          Unit,
          Group.reach(
            Groups.in(
              ~d,
              Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Edit.nodes(x), l),
              Trees.Edit.root(x)
            ),
            g
          ),
          Group.key(g)
        ),
        u => Some{Replicas.Act.Stale{}},
        u => Act.put(None{}, [], Some{x})
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
    u => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.all.if(
        v => Shared.List.same_set(~String, ~String.eq, os, Group.nodes(~d, l, h, g)),
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

# Written, or Conflicted while a resource still clashes after the merge k
def Answer.merged(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, +k: Ledgers.Id) -> Answer:
  Shared.Bool.when(
    Answer,
    Clash.left(~d, l, h, k),
    u => Answer.Conflicted{k},
    u => Answer.Written{}
  )

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
# a part of a history
def Node.versions(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  b: Branch,
  n: U32,
  k: Nat
) -> List<&2, Ledgers.Id>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, Ledgers.Id>,
      Branch.head(~d, ~kern, l, b),
      t => Some{Replicas.Taken.ids(Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, t, n))}
    ),
    []
  )

# the names of the resources among the bindings xs
def Res.names(xs: List<&2, Trees.Binding>) -> List<&2, Resources.Name>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Shared.Maybe.cons(Resources.Name, Res.name(Trees.Binding.key(x)), Res.names(rest))

# the names of the resources among the keys ks
def Keys.names(ks: List<&2, List<&2, U32>>) -> List<&2, Resources.Name>:
  match ks:
    case Nil{}:
      []
    case Con{k, rest}:
      Shared.Maybe.cons(Resources.Name, Res.name(k), Keys.names(rest))

# the resources of the tree whose root is h
def Tree.resources(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> List<&2, Resources.Name>:
  Res.names(Tree.list(~d, l, h, [0]))

# the resources of the branch b at its head
def Node.resources(~d: Led(), ~kern: Kern(d), +l: L(d), b: Branch) -> List<&2, Resources.Name>:
  Maybe.default(
    &2,
    List<&2, Resources.Name>,
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, Resources.Name>,
      Branch.head(~d, ~kern, l, b),
      t => Some{Tree.resources(~d, l, Replicas.Tip.content(t))}
    ),
    []
  )

# the members of the group g of the store st, if g is there
def Node.members(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  st: Hashes.Hash,
  g: String
) -> Maybe<&2, List<&2, Requests.Member>>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    List<&2, Requests.Member>,
    Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st),
    t => Codes.Code.whole.of(
      ~List<&2, Requests.Member>,
      ~Requests.Members.code,
      ~Requests.Members.code.read,
      Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.group(g))
    )
  )

# what changed from the resource a to the resource b, in the format of b, else
# of a (none of them: nothing changed)
def Res.diff(~d: Led(), +l: L(d), +a: Maybe<&2, Requests.Res>, +b: Maybe<&2, Requests.Res>) -> List<&2, Formats.Change>:
  Maybe.default(
    &2,
    List<&2, Formats.Change>,
    Maybe.bind(
      &2,
      Hashes.Hash,
      List<&2, Formats.Change>,
      Res.format.of(b, a),
      h => Maybe.bind(
        &2,
        Formats.Format,
        List<&2, Formats.Change>,
        Format.at(~d, l, h),
        f => Some{
          Formats.Format.changes(
            f,
            Maybe.default(&2, Texts.Bytes(), Res.bytes(~d, l, a), []),
            Maybe.default(&2, Texts.Bytes(), Res.bytes(~d, l, b), [])
          )
        }
      )
    ),
    []
  )

# what changed in the resource n from the point a to the point b, as the
# writer w reads them, in the format of the resource: a resource that is not
# there is empty
def Node.diff(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +w: String,
  +n: Resources.Name,
  a: Point,
  b: Point
) -> List<&2, Formats.Change>:
  Res.diff(
    ~d,
    l,
    Maybe.default(&2, Maybe<&2, Requests.Res>, Node.find(~d, ~kern, l, w, n, a), None{}),
    Maybe.default(&2, Maybe<&2, Requests.Res>, Node.find(~d, ~kern, l, w, n, b), None{})
  )

# a branch, with its owners and its newest version (none: it has none yet)
type BranchEntry is Data:
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Maybe<&2, Ledgers.Id>}

# the entry of the branch b, whose newest tip is m
def BranchEntry.of(~d: Led(), l: L(d), b: Branch, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, BranchEntry>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      Some{BranchEntry{b, Replicas.Tip.voters(t), Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t)}}

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

# the branches of the store st, by the log of its newest tip m
def Store.branches(~d: Led(), l: L(d), +st: Hashes.Hash, m: Maybe<&2, Replicas.Tip>) -> List<&2, Branch>:
  match m:
    case None{}:
      []
    case Some{t}:
      Branches.of(
        st,
        Branches.names(
          Tree.list(~d, l, Replicas.Tip.log(t), [5])
        )
      )

# the entries of the branches bs
def Branches.entries(~d: Led(), ~kern: Kern(d), +l: L(d), bs: List<&2, Branch>) -> List<&2, BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      Shared.Maybe.cons(
        BranchEntry,
        BranchEntry.of(~d, l, b, Branch.head(~d, ~kern, l, b)),
        Branches.entries(~d, ~kern, l, rest)
      )

# every branch of the store st
def Node.branches(~d: Led(), ~kern: Kern(d), +l: L(d), +st: Hashes.Hash) -> List<&2, BranchEntry>:
  Branches.entries(
    ~d,
    ~kern,
    l,
    Store.branches(~d, l, st, Replicas.Root.head(~Requests.Ask.machine(), ~d, ~kern, l, st))
  )

# What a work uses
# ----------------
# A resource uses what it imports, directly or not. An import keeps its
# target as written (Formats.Edge); its language says how the target is found
# (Formats.Find, Resources.Name.candidates) and what it brings
# (Formats.Brings). An import that brings all of a place names each resource
# under it.

# the first of the names ns that is a resource of the tree h
def Names.first(~d: Led(), +l: L(d), +h: Maybe<&2, Hashes.Hash>, ns: List<&2, Resources.Name>) -> Maybe<&2, Resources.Name>:
  match ns:
    case Nil{}:
      None{}
    case Con{+n, rest}:
      Shared.Bool.when(
        Maybe<&2, Resources.Name>,
        Maybe.is_some(
          &2,
          Requests.Res,
          Maybe.default(&2, Maybe<&2, Requests.Res>, Res.find(~d, l, h, n), None{})
        ),
        u => Some{n},
        u => Names.first(~d, l, h, rest)
      )

# each resource under the first candidate cs, when the import brings all of
# its target (br), else none
def Import.under(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  br: Formats.Brings,
  cs: List<&2, Resources.Name>
) -> List<&2, Resources.Name>:
  match br cs:
    case Formats.Brings.Named{} x:
      []
    case y Nil{}:
      []
    case y Con{c, rest}:
      Resources.Name.under(c, Tree.resources(~d, l, h))

# the resources that the import x of the resource n names, in the tree h: the
# first of its candidates that is there; else, when it brings all of its
# target, each resource under the first candidate
def Import.names(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  x: Formats.Import
) -> List<&2, Resources.Name>:
  match x:
    case Formats.Import{Formats.Edge{target, alias, ns, conds}, br, fi}:
      +cs = Resources.Name.candidates(n, fi, Texts.Bytes.to_text(target))
      Maybe.default(
        &2,
        List<&2, Resources.Name>,
        Maybe.bind(&2, Resources.Name, List<&2, Resources.Name>, Names.first(~d, l, h, cs), m => Some{[m]}),
        Import.under(~d, l, h, br, cs)
      )

# the resources that the imports xs of the resource n name, in the tree h
def Imports.names(
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  xs: List<&2, Formats.Import>
) -> List<&2, Resources.Name>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.append(
        &2,
        Resources.Name,
        Shared.Bool.when(
          List<&2, Resources.Name>,
          Formats.Import.holds(view, x),
          u => Import.names(~d, l, h, n, x),
          u => []
        ),
        Imports.names(~d, l, view, h, n, rest)
      )

# Res.imports once the resource m is known
def Res.imports.of(
  ~d: Led(),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  m: Maybe<&2, Requests.Res>
) -> List<&2, Resources.Name>:
  match m:
    case None{}:
      []
    case Some{+x}:
      Maybe.default(
        &2,
        List<&2, Resources.Name>,
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
            bs => Some{Imports.names(~d, l, view, h, n, Formats.Format.uses(f, [bs]))}
          )
        ),
        []
      )

# what the resource n imports directly, in the tree whose root is h, as its
# format reads it: each import found as its language finds it (nothing while
# l lacks the resource)
def Res.imports(~d: Led(), +l: L(d), +view: List<&2, Formats.Cond>, +h: Maybe<&2, Hashes.Hash>, +n: Resources.Name) -> List<&2, Resources.Name>:
  Res.imports.of(
    ~d,
    l,
    view,
    h,
    n,
    Maybe.default(&2, Maybe<&2, Requests.Res>, Res.find(~d, l, h, n), None{})
  )

# the key of the resource n in the graph of imports
def Name.key(n: Resources.Name) -> List<&2, Bool>:
  Tries.Trie.text(Resources.Name.show(n))

# the key of each of the resources ns
def Names.keys(ns: List<&2, Resources.Name>) -> List<&2, List<&2, Bool>>:
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
) -> Reaches.Graph:
  match ns:
    case Nil{}:
      g
    case Con{+n, rest}:
      Uses.graph(
        ~d,
        l,
        view,
        h,
        rest,
        Reaches.Graph.links(Names.keys(Res.imports(~d, l, view, h, n)), Name.key(n), g)
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
) -> Bool:
  List.any.if(
    u => Tries.Trie.has(
      Unit,
      Reaches.Graph.reach(
        Uses.graph(~d, l, view, h, Tree.resources(~d, l, h), Reaches.Graph.new()),
        Name.key(used)
      ),
      Name.key(changed)
    ),
    Resources.Name.is_eq(used, changed)
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

# what the resource n holds in the tree h is known, and is not what it holds
# in the tree h2
def Res.differs(
  ~d: Led(),
  +l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  h2: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name
) -> Bool:
  Maybe.default(
    &2,
    Bool,
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
    ),
    False{}
  )

# a version that changed a resource, and the time of its request
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the versions among xs that changed the resource n, the first of which came
# after the tree h0, at the tip t
def Log.entries(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  xs: List<&2, Replicas.Taken>,
  +h0: Maybe<&2, Hashes.Hash>
) -> List<&2, LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{Replicas.Taken{+i, +h}, rest}:
      List.filter.put(
        LogEntry,
        LogEntry{i, Replicas.Out.time(~Requests.Ask.machine(), ~d, l, Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i))},
        Log.entries(~d, l, t, n, rest, h),
        Res.differs(~d, l, h, h0, n)
      )

# Node.log once the newest tip t of the branch is known
def Node.log.at(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  n: Resources.Name,
  +from: U32,
  k: Nat
) -> List<&2, LogEntry>:
  Log.entries(
    ~d,
    l,
    t,
    n,
    Replicas.Tip.versions(~Requests.Ask.machine(), ~d, k, l, t, from),
    Maybe.default(&2, Maybe<&2, Hashes.Hash>, Replicas.Tip.before(~Requests.Ask.machine(), ~d, l, t, from), None{})
  )

# the versions of the branch b that changed the resource n, among k versions
# from the number from
def Node.log(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  n: Resources.Name,
  b: Branch,
  from: U32,
  k: Nat
) -> List<&2, LogEntry>:
  Maybe.default(
    &2,
    List<&2, LogEntry>,
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, LogEntry>,
      Branch.head(~d, ~kern, l, b),
      t => Some{Node.log.at(~d, l, t, n, from, k)}
    ),
    []
  )

# the version that the line took as the number m, at the tip t, wrote the
# resource n: the resource holds after it what it did not hold before it
def Version.wrote(~d: Led(), +l: L(d), +t: Replicas.Tip, +m: U32, +n: Resources.Name) -> Bool:
  Maybe.default(
    &2,
    Bool,
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
        x => Some{Res.differs(~d, l, Replicas.Taken.root(x), h0, n)}
      )
    ),
    False{}
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
) -> Bool:
  +hb = Replicas.Tip.content(tb)
  List.all.if(
    u => List.all.if(
      u2 => List.all.if(
        u3 => Uses.reaches(~d, l, view, hb, used, changed),
        Maybe.is_some(
          &2,
          Requests.Res,
          Maybe.default(&2, Maybe<&2, Requests.Res>, Res.find(~d, l, hb, used), None{})
        )
      ),
      Res.differs(
        ~d,
        l,
        Maybe.default(&2, Maybe<&2, Hashes.Hash>, Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, tf, v), None{}),
        hb,
        changed
      )
    ),
    Maybe.default(
      &2,
      Bool,
      Maybe.bind(
        &2,
        U32,
        Bool,
        Replicas.Tip.number(~Requests.Ask.machine(), ~d, l, tf, v),
        m => Some{Version.wrote(~d, l, tf, m, changed)}
      ),
      False{}
    )
  )

# the touch x holds: its two branches are of one store and are not the same;
# its version is a version of the branch from, and wrote the resource
# changed; the branch does not hold what that version gave the resource; and
# the resource used is of the branch, and is the one changed or uses it. So a
# writer is told only about changes to what its work uses
def Touch.holds(~d: Led(), ~kern: Kern(d), +l: L(d), +view: List<&2, Formats.Cond>, x: Touch) -> Bool:
  match x:
    case Touch{+from, v, changed, +b, used}:
      List.all.if(
        u => Maybe.default(
          &2,
          Bool,
          Maybe.bind(
            &2,
            Replicas.Tip,
            Bool,
            Branch.head(~d, ~kern, l, from),
            tf => Maybe.bind(
              &2,
              Replicas.Tip,
              Bool,
              Branch.head(~d, ~kern, l, b),
              tb => Some{Touch.holds.at(~d, l, view, tf, tb, v, changed, used)}
            )
          ),
          False{}
        ),
        Branch.other(from, b)
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
) -> Reaches.Graph:
  match ns:
    case Nil{}:
      g
    case Con{+n, rest}:
      Uses.users(
        ~d,
        l,
        view,
        h,
        rest,
        Reaches.Graph.back(Names.keys(Res.imports(~d, l, view, h, n)), Name.key(n), g)
      )

# a touch of the version v of the branch from on the branch b, for the
# resource c and each resource of used that is c or that the set reach holds
def Touches.of(
  +from: Branch,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch,
  used: List<&2, Resources.Name>,
  +reach: Tries.Trie<Unit>
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
          w => Tries.Trie.has(Unit, reach, Name.key(u)),
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
) -> List<&2, Touch>:
  match changed:
    case Nil{}:
      []
    case Con{+c, rest}:
      List.append(
        &2,
        Touch,
        Touches.when(
          List.all.if(u => Res.differs(~d, l, h, hb, c), Res.differs(~d, l, h, h0, c)),
          from,
          v,
          c,
          b,
          used,
          users
        ),
        Touches.each(~d, l, from, v, h0, h, rest, b, hb, used, users)
      )

# the touches of the versions xs of the branch from, the first of which came
# after the tree h0, on the branch b
def Touches.all(
  ~d: Led(),
  +l: L(d),
  +from: Branch,
  xs: List<&2, Replicas.Taken>,
  +h0: Maybe<&2, Hashes.Hash>,
  +b: Branch,
  +hb: Maybe<&2, Hashes.Hash>,
  +used: List<&2, Resources.Name>,
  +users: Reaches.Graph
) -> List<&2, Touch>:
  match xs:
    case Nil{}:
      []
    case Con{Replicas.Taken{+i, +h}, rest}:
      List.append(
        &2,
        Touch,
        Touches.each(
          ~d,
          l,
          from,
          i,
          h0,
          h,
          Keys.names(
            Maybe.default(
              &2,
              List<&2, List<&2, U32>>,
              Replicas.Tree.diff(~Requests.Ask.machine(), ~d, l, h0, h),
              []
            )
          ),
          b,
          hb,
          used,
          users
        ),
        Touches.all(~d, l, from, rest, h, b, hb, used, users)
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
) -> List<&2, Touch>:
  +hb = Replicas.Tip.content(tb)
  +xs = Tree.list(~d, l, hb, [0])
  Touches.all(
    ~d,
    l,
    from,
    Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
    None{},
    b,
    hb,
    Res.names(xs),
    Uses.users(~d, l, view, hb, Res.names(xs), Reaches.Graph.new())
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
) -> List<&2, Touch>:
  match m:
    case None{}:
      []
    case Some{tb}:
      Branch.touches.at(~d, l, view, from, tf, b, tb)

# the changes of the branch from that touch what the branch b uses: of each
# version of from, each resource that it wrote and that b does not hold as it
# gave it, with each resource of b that is that resource or uses it. The cost
# is the history of from and the resources of b, each read once
def Branch.touches(~d: Led(), ~kern: Kern(d), +l: L(d), +view: List<&2, Formats.Cond>, +from: Branch, +b: Branch) -> List<&2, Touch>:
  Shared.Bool.when(
    List<&2, Touch>,
    Branch.other(from, b),
    u => Maybe.default(
      &2,
      List<&2, Touch>,
      Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, Touch>,
        Branch.head(~d, ~kern, l, from),
        tf => Some{Branch.touches.of(~d, l, view, from, tf, b, Branch.head(~d, ~kern, l, b))}
      ),
      []
    ),
    u => []
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
) -> List<&2, Touch>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{from, os, hd}, rest}:
      List.append(
        &2,
        Touch,
        Branch.touches(~d, ~kern, l, view, from, b),
        Branches.touch(~d, ~kern, l, view, rest, b)
      )

# the changes elsewhere that touch what the branch b uses, at any depth
def Node.affects(~d: Led(), ~kern: Kern(d), +l: L(d), +view: List<&2, Formats.Cond>, +b: Branch) -> List<&2, Touch>:
  match b:
    case Branch{+st, n}:
      Branches.touch(~d, ~kern, l, view, Node.branches(~d, ~kern, l, st), Branch{st, n})

# what the changes of the branch from touch in each of the branches es
def Branches.touched(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +view: List<&2, Formats.Cond>,
  +from: Branch,
  es: List<&2, BranchEntry>
) -> List<&2, Touch>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{b, os, hd}, rest}:
      List.append(
        &2,
        Touch,
        Branch.touches(~d, ~kern, l, view, from, b),
        Branches.touched(~d, ~kern, l, view, from, rest)
      )

# what the changes of the branch b touch elsewhere, in every build: the views
# of other writers are theirs
def Node.impact(~d: Led(), ~kern: Kern(d), +l: L(d), +b: Branch) -> List<&2, Touch>:
  match b:
    case Branch{+st, n}:
      Branches.touched(~d, ~kern, l, [], Branch{st, n}, Node.branches(~d, ~kern, l, st))

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
) -> List<&2, Notice>:
  match ids:
    case Nil{}:
      []
    case Con{+i, rest}:
      List.filter.put(
        Notice,
        Notice.Conflicted{b, i},
        Notices.conflicts(~d, l, h, b, rest),
        Clash.left(~d, l, h, i)
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
# clash) of the branch b, whose newest tip is m
def Notices.branch(~d: Led(), +l: L(d), +b: Branch, all: Bool, m: Maybe<&2, Replicas.Tip>) -> List<&2, Notice>:
  match all m:
    case x None{}:
      []
    case True{} Some{+t}:
      Notices.versions(b, Replicas.Taken.ids(Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(t)), l, t, 0)))
    case False{} Some{+t}:
      Notices.conflicts(
        ~d,
        l,
        Replicas.Tip.content(t),
        b,
        Replicas.Taken.ids(Replicas.Tip.versions(~Requests.Ask.machine(), ~d, U32.to_nat(Replicas.Tip.count(t)), l, t, 0))
      )

# every notice of the topic x, by what the ledger holds
def Node.notices(~d: Led(), ~kern: Kern(d), +l: L(d), x: Topic) -> List<&2, Notice>:
  match x:
    case Topic.Versions{+b}:
      Notices.branch(~d, l, b, True{}, Branch.head(~d, ~kern, l, b))
    case Topic.Conflicts{+b}:
      Notices.branch(~d, l, b, False{}, Branch.head(~d, ~kern, l, b))
    case Topic.Affects{b, view}:
      Notices.touches(Node.affects(~d, ~kern, l, view, b))
    case Topic.Lies{+st}:
      Notices.lies(st, Ledgers.Kind.liars(Requests.Ask, Replicas.Led.kind(Requests.Ask.machine(), d))(l)(st))

# Mounts
# ------

# the resources mounted to a node: the branch of each, by the key of its URI.
# A resource is mounted to one branch at a time: to mount it to another is a
# checkout, and to mount another resource to another branch is a worktree
def Mounts() -> Data:
  Tries.Trie<Branch>

# a node may stop: it is forced to, or no resource is mounted and no writer
# is connected
def Node.may_stop(mounts: Mounts(), writers: Tries.Trie<Unit>, force: Bool) -> Bool:
  Bool.or(
    force,
    Bool.and(Tries.Trie.is_tip(Branch, mounts), Tries.Trie.is_tip(Unit, writers))
  )

# the change that records what a resource held when it is mounted: a write
# of the resource x since the newest version, when the branch does not hold
# it at its tip t (none: nothing to record). The node keeps the bytes and the
# format of x before it asks
def Mount.change(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +x: Requests.Res
) -> Maybe<&2, Requests.Change>:
  Shared.Maybe.when(
    Requests.Change,
    Bool.not(
      Res.same(
        Maybe.default(&2, Maybe<&2, Requests.Res>, Res.find(~d, l, Replicas.Tip.content(t), n), None{}),
        Some{x}
      )
    ),
    u => Some{Requests.Change.Write{n, Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t), Requests.Content.New{x}}}
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
      Ledgers.Id,
      Replicas.Request<Requests.Ask>,
      Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, ts),
      v => Own.due.of(c, t, ts, g, Group.nodes(~d, l, Replicas.Tip.content(ts), g), v)
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

# Laws
# ----

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
          Clash.open(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n, k) == True{}: Bool
        }
    )

# writers are told only about changes to what their work uses: each touch
# that Node.affects gives for a branch holds (Touch.holds)
law Node.affects_holds:
  for ~d: Led()
  for ~kern: Kern(d)
  for l: L(d)
  for view: List<&2, Formats.Cond>
  for b: Branch
  for x: Touch
  {List.contains(~Touch, ~Touch.is_eq, Node.affects(~d, ~kern, l, view, b), x) == True{}: Bool}
    -> {Touch.holds(~d, ~kern, l, view, x) == True{}: Bool}

# and they are told about each of them: a touch that holds is among the
# touches that Node.affects gives for its branch
law Node.affects_complete:
  for ~d: Led()
  for ~kern: Kern(d)
  for l: L(d)
  for view: List<&2, Formats.Cond>
  for x: Touch
  {Touch.holds(~d, ~kern, l, view, x) == True{}: Bool}
    -> {
      List.contains(~Touch, ~Touch.is_eq, Node.affects(~d, ~kern, l, view, Touch.branch(x)), x) == True{}: Bool
    }
