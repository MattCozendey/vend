import Base
import ../../shared/replica.bend as Replicas
import ../../shared/shared/formats.bend as Formats
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/rope.bend as Ropes
import ../../shared/shared/shared/keyset.bend as KeySets
import ../../shared/shared/shared/pack.bend as Packs
import ../../shared/shared/shared/reach.bend as Reaches
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
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

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the value of a resource whose content is under the root m (none: removed)
def Res.code(m: Maybe<&2, Ropes.Root>) -> List<&2, U32>:
  Codes.Code.maybe(~Ropes.Root, ~Ropes.Root.code, m, [])

# the root of the content in the value ws of a resource, when it is there
def Res.read(ws: List<&2, U32>) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(
    &2,
    Maybe<&2, Ropes.Root>,
    Ropes.Root,
    Replicas.Read.whole(
      Maybe<&2, Ropes.Root>,
      Codes.Code.maybe.read(~Ropes.Root, ~Ropes.Root.code.read, ws)
    ),
    x => x
  )

# the root in the value m of a resource, if any
def Res.found(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, m, ws => Res.read(ws))

# the root of the content of the resource n in the tree whose root is h, or
# that it is not there (none: l lacks a node of the tree)
def Res.find(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Ropes.Root>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the bytes under the root m (none: there is no root, or l lacks a node). The
# words of a rope are packed lines (Packs)
def Root.bytes(~d: Led(), l: L(d), m: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(
    &2,
    Ropes.Root,
    Texts.Bytes(),
    m,
    r => Maybe.bind(
      &2,
      List<&2, U32>,
      Texts.Bytes(),
      Ropes.Rope.read(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, r),
      ws => Some{Packs.Pack.read(ws, 0n)}
    )
  )

# Versions
# --------
# A version is a request that its branch took. Its content is the root that
# the log of the branch holds for its number.

# the root of the content of the taken request x
def Taken.root(x: Replicas.Taken) -> Maybe<&2, Hashes.Hash>:
  match x:
    case Replicas.Taken{i, r}:
      r

# the root of the content that the outcome o names at the tip t (none: the
# outcome is a refusal, or l lacks a node)
def Out.root(~d: Led(), l: L(d), t: Replicas.Tip, o: Replicas.Out) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  match o:
    case Replicas.Out.Stale{a}:
      None{}
    case Replicas.Out.Taken{a, n}:
      Maybe.bind(
        &2,
        Replicas.Taken,
        Maybe<&2, Hashes.Hash>,
        Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, n),
        x => Some{Taken.root(x)}
      )

# the root of the content of the version of the request i, at the tip t of
# its line (none: the line did not take it, or l lacks a node)
def Tip.version(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  i: Ledgers.Id
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(
    &2,
    Replicas.Out,
    Maybe<&2, Hashes.Hash>,
    Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i),
    o => Out.root(~d, l, t, o)
  )

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
  p: Maybe<&2, Trees.Put>
) -> Maybe<&2, Replicas.Act>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Replicas.Act.Taken{
          vs,
          Some{Trees.Put.root(x)},
          List.append(&2, List<&2, U32>, ns, Trees.Put.nodes(x))
        }
      }

# l holds the bytes under the root m (a resource that is not there has none)
def Root.held(~d: Led(), l: L(d), m: Maybe<&2, Ropes.Root>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{r}:
      Maybe.is_some(&2, Texts.Bytes(), Root.bytes(~d, l, Some{r}))

# the binding x is not a resource, or l holds its bytes
def Res.held(~d: Led(), l: L(d), x: Trees.Binding) -> Bool:
  match x:
    case Trees.Binding{Con{0, r}, v}:
      Root.held(~d, l, Res.read(v))
    case _:
      True{}

# l holds the bytes of each resource among the bindings xs
def Res.all_held(~d: Led(), +l: L(d), xs: List<&2, Trees.Binding>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      List.all.if(u => Res.all_held(~d, l, rest), Res.held(~d, l, x))

# l holds the whole of the tree whose root is h: each of its nodes, and the
# bytes of each of its resources. A clear def: it walks the tree
def Tree.kept(~d: Led(), +l: L(d), +h: Maybe<&2, Hashes.Hash>) -> Bool:
  List.all.if(
    u => Res.all_held(
      ~d,
      l,
      Trees.Tree.list(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h)
    ),
    Trees.Tree.whole(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h)
  )

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
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  match x:
    case Requests.Content.Root{r}:
      Some{Some{r}}
    case Requests.Content.Of{i}:
      Maybe.bind(
        &2,
        Maybe<&2, Hashes.Hash>,
        Maybe<&2, Ropes.Root>,
        Tip.version(~d, l, t, i),
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
      Tip.version(~d, l, t, i)

# the act that sets the resource n to the root new in the content of the tip
# t, once l holds its bytes (none: wait for them)
def Res.set(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  +new: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Root.held(~d, l, new),
    u => Act.put(
      None{},
      [],
      Replicas.Tree.set(
        ~Requests.Ask.machine(),
        ~d,
        l,
        Replicas.Tip.content(t),
        Key.res(n),
        Res.code(new)
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
  ours: Maybe<&2, Ropes.Root>,
  held: Maybe<&2, Ropes.Root>,
  new: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Roots.same(ours, held),
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
    Maybe<&2, Ropes.Root>,
    Replicas.Act,
    Res.find(~d, l, Replicas.Tip.content(t), n),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Base.root(~d, l, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Act,
        Res.find(~d, l, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
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
    Replicas.Tree.set(
      ~Requests.Ask.machine(),
      ~d,
      l,
      Replicas.Tip.content(t),
      Requests.Key.seal(n),
      Hashes.Hash.code(k, [])
    )
  )

# Clashes
# -------

# the key of the open clashes of the merge of the request k: the resources
# that still clash after it. So what a merge left is one read, and no walk
def Key.clashes(k: Ledgers.Id) -> List<&2, U32>:
  3 <> Ledgers.Id.code(k, [])

# the words of the resources ns
def Clash.words(ns: List<&2, Resources.Name>) -> List<&2, U32>:
  Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, [])

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
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, Resources.Name>,
      Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k)),
      ws => Replicas.Read.whole(
        List<&2, Resources.Name>,
        Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)
      )
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
  p: Maybe<&2, Trees.Put>
) -> Maybe<&2, Work<L(d)>>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Work{
          Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Put.nodes(x), l),
          Some{Trees.Put.root(x)},
          List.append(&2, List<&2, U32>, ns, Trees.Put.nodes(x))
        }
      }

# the work w with the key k set to x (none: the ledger lacks a node)
def Work.set(~d: Led(), w: Work<L(d)>, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Work<L(d)>>:
  match w:
    case Work{+l, h, ns}:
      Work.put(~d, l, ns, Replicas.Tree.set(~Requests.Ask.machine(), ~d, l, h, k, x))

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
        Clash.words(Clash.put(n, Clash.names(~d, l, h, k)))
      )

# the act that takes the work m as the content, with the owners vs if any
def Work.act(-L: Data, vs: Maybe<&2, List<&2, String>>, m: Maybe<&2, Work<L>>) -> Maybe<&2, Replicas.Act>:
  match m:
    case None{}:
      None{}
    case Some{Work{l, h, ns}}:
      Some{Replicas.Act.Taken{vs, h, ns}}

# what a resolve of the resource n of the merge k, with the content x, does
# at the tip t: while the clash is open, and once l holds the bytes, the
# resource holds x and the clash is shut; else it is stale
def Resolve.act.of(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +new: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Clash.open(~d, l, Replicas.Tip.content(t), n, k),
    u => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      Root.held(~d, l, new),
      v => Work.act(
        L(d),
        None{},
        Maybe.bind(
          &2,
          Work<L(d)>,
          Work<L(d)>,
          Work.set(~d, Work{l, Replicas.Tip.content(t), []}, Key.res(n), Res.code(new)),
          w => Work.set(
            ~d,
            w,
            Key.clashes(k),
            Clash.words(
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
    Maybe<&2, Ropes.Root>,
    Replicas.Act,
    Content.find(~d, l, t, n, x),
    new => Resolve.act.of(~d, l, t, k, n, new)
  )

# Merges
# ------
# A merge goes resource by resource, each in its own format. It takes theirs
# and the base as trees that come with the change.

# what a merge keeps of a resource: the content of one side (none: removed),
# new bytes, or a clash
type Pick is Data:
  Pick.Take{root: Maybe<&2, Ropes.Root>}
  Pick.Make{bytes: Texts.Bytes()}
  Pick.Clash{}

# the pick of a merge of bytes
def Pick.of(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Pick.Make{x}
    case Formats.Merged.Clash{}:
      Pick.Clash{}

# the bytes under the root m: a resource that is not there is empty
def Root.text(~d: Led(), l: L(d), m: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case None{}:
      Some{[]}
    case Some{r}:
      Root.bytes(~d, l, Some{r})

# the pick of a merge of both changes, in the format f (none: wait for bytes)
def Pick.both(
  ~d: Led(),
  +l: L(d),
  +f: Formats.Format,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Pick>:
  Maybe.bind(
    &2,
    Texts.Bytes(),
    Pick,
    Root.text(~d, l, b),
    bb => Maybe.bind(
      &2,
      Texts.Bytes(),
      Pick,
      Root.text(~d, l, o),
      ob => Maybe.bind(
        &2,
        Texts.Bytes(),
        Pick,
        Root.text(~d, l, t),
        tb => Some{Pick.of(Formats.Format.merge(f, bb, ob, tb))}
      )
    )
  )

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base; ours when theirs is the base or
# both agree; else both merged, in the format. So a merge never loses a
# change that only one side made
def Pick.merge(
  ~d: Led(),
  l: L(d),
  f: Formats.Format,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Pick>:
  Shared.Bool.when(
    Maybe<&2, Pick>,
    Roots.same(o, b),
    u => Some{Pick.Take{t}},
    u => Shared.Bool.when(
      Maybe<&2, Pick>,
      Bool.or(Roots.same(t, b), Roots.same(o, t)),
      v => Some{Pick.Take{o}},
      v => Pick.both(~d, l, f, b, o, t)
    )
  )

# x is the byte that ends a line
def Byte.is_end(x: U32) -> Bool:
  U32.is_eq(x, 10)

# the rope of the bytes b: cut after each line, and each line packed, four
# bytes in a word. So two contents share every line that an edit did not
# touch, and a byte costs a quarter of a word
def Bytes.rope(b: Texts.Bytes()) -> Ropes.Put:
  Ropes.Rope.put(Packs.Pack.lines(Ropes.Rope.cut(~U32, ~Byte.is_end, b)))

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
      Work.set(~d, w, Key.res(n), Res.code(x))
    case Pick.Make{bytes}:
      +r = Bytes.rope(bytes)
      Work.set(
        ~d,
        Work.keep(~d, w, Ropes.Put.nodes(r)),
        Key.res(n),
        Res.code(Some{Ropes.Put.root(r)})
      )
    case Pick.Clash{}:
      Work.clash(~d, w, k, n)

# x before rest, when m holds x
def Some.cons(-A: Data, m: Maybe<&2, A>, rest: List<&2, A>) -> List<&2, A>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

# the name of the resource of the binding x, when it is one
def Res.name(x: Trees.Binding) -> Maybe<&2, Resources.Name>:
  match x:
    case Trees.Binding{Con{0, r}, v}:
      Replicas.Read.whole(Resources.Name, Resources.Name.code.read(r))
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
    Maybe<&2, Ropes.Root>,
    Work<L(d)>,
    Res.find(~d, l, hb, n),
    +b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Work<L(d)>,
      Res.find(~d, l, ho, n),
      +o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Work<L(d)>,
        Res.find(~d, l, ht, n),
        t => Maybe.bind(
          &2,
          Pick,
          Work<L(d)>,
          Pick.merge(~d, l, Formats.Format.of(Resources.Name.path(n)), b, o, t),
          p => Merge.pick(~d, w, k, n, p)
        )
      )
    )
  )

# the work m after the merge of each resource among the bindings xs. A
# resource that comes twice is merged twice, with the same pick
def Merge.all(
  ~d: Led(),
  +l: L(d),
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +k: Ledgers.Id,
  xs: List<&2, Trees.Binding>,
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
      L(d),
      None{},
      Merge.all(
        ~d,
        l,
        hb,
        ho,
        ht,
        k,
        Trees.Tree.diff(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, ho, ht),
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
        Replicas.Read.whole(String, Codes.Code.text.read(r)),
        n => Maybe.bind(
          &2,
          List<&2, Requests.Member>,
          Group,
          Replicas.Read.whole(List<&2, Requests.Member>, Requests.Members.code.read(v)),
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
      Some.cons(Group, Group.read(x), Groups.of(rest))

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
  Groups.of(Trees.Tree.list(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h))

# the nodes of the group g in the tree whose root is h, each once: the nodes
# that own what g owns. A clear def: it walks the tree
def Group.nodes(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, g: String) -> List<&2, String>:
  Group.nodes.of(Groups.in(~d, l, h), g)

# each name of as is in bs
def Names.within(as: List<&2, String>, +bs: List<&2, String>) -> Bool:
  match as:
    case Nil{}:
      True{}
    case Con{a, rest}:
      List.all.if(u => Names.within(rest, bs), List.contains(~String, ~String.eq, bs, a))

# as and bs hold the same names
def Names.same(+as: List<&2, String>, +bs: List<&2, String>) -> Bool:
  List.all.if(u => Names.within(bs, as), Names.within(as, bs))

# Group.act once the tree with the new members is known: stale when the group
# then reaches itself
def Group.act.of(~d: Led(), l: L(d), +g: String, p: Maybe<&2, Trees.Put>) -> Maybe<&2, Replicas.Act>:
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
              Replicas.Led.puts(~Requests.Ask.machine(), ~d, Trees.Put.nodes(x), l),
              Some{Trees.Put.root(x)}
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
    Trees.Tree.whole(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h),
    u => Group.act.of(
      ~d,
      l,
      g,
      Replicas.Tree.set(
        ~Requests.Ask.machine(),
        ~d,
        l,
        h,
        Key.group(g),
        Requests.Members.code(ms, [])
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
    Trees.Tree.whole(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h),
    u => Shared.Bool.when(
      Maybe<&2, Replicas.Act>,
      List.all.if(
        v => Names.same(os, Group.nodes(~d, l, h, g)),
        Bool.not(List.is_empty(&2, String, os))
      ),
      v => Act.put(
        Some{os},
        [],
        Replicas.Tree.set(
          ~Requests.Ask.machine(),
          ~d,
          l,
          Replicas.Tip.content(t),
          Key.owner(),
          Codes.Code.text(g, [])
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
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
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
  k: Unit -> Maybe<&2, Maybe<&2, Ropes.Root>>
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
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
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
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
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  Maybe.bind(
    &2,
    Maybe<&2, Hashes.Hash>,
    Maybe<&2, Ropes.Root>,
    Tip.version(~d, l, t, i),
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
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  match p:
    case Point.Head{b}:
      Head.read(~d, l, t, w, b, n)
    case Point.At{b, i}:
      Version.read(~d, l, t, i, n)
    case Point.Mark{b, m}:
      Maybe.bind(
        &2,
        Ledgers.Id,
        Maybe<&2, Ropes.Root>,
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
    Replicas.Tip,
    Texts.Bytes(),
    Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, Branch.line(Point.branch(p))),
    t => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Texts.Bytes(),
      Point.read(~d, ~kern, l, t, w, n, p),
      m => Root.bytes(~d, l, m)
    )
  )

# What a front lists
# ------------------
# Each is a read of the ledger. A clear def may walk a tree or a history: the
# cost of a fast one is what it gives, not what the node holds.

# the IDs of the taken requests xs
def Taken.ids(xs: List<&2, Replicas.Taken>) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{Replicas.Taken{i, r}, rest}:
      i <> Taken.ids(rest)

# the taken request x, if any, before what rest gives; nothing after a
# missing one
def Taken.con(m: Maybe<&2, Replicas.Taken>, rest: Unit -> List<&2, Replicas.Taken>) -> List<&2, Replicas.Taken>:
  match m:
    case None{}:
      []
    case Some{x}:
      x <> rest(Unit{})

# k versions from the number n, in order, at the tip t
def Tip.versions(~d: Led(), k: Nat, +l: L(d), +t: Replicas.Tip, +n: U32) -> List<&2, Replicas.Taken>:
  match k:
    case 0n:
      []
    case 1n+p:
      Taken.con(
        Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, n),
        u => Tip.versions(~d, p, l, t, U32.inc(n))
      )

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
      t => Some{Taken.ids(Tip.versions(~d, k, l, t, n))}
    ),
    []
  )

# the names of the resources among the bindings xs
def Res.names(xs: List<&2, Trees.Binding>) -> List<&2, Resources.Name>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Some.cons(Resources.Name, Res.name(x), Res.names(rest))

# the resources of the tree whose root is h
def Tree.resources(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> List<&2, Resources.Name>:
  Res.names(Trees.Tree.list(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h))

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
    t => Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, Requests.Member>,
      Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.group(g)),
      ws => Replicas.Read.whole(List<&2, Requests.Member>, Requests.Members.code.read(ws))
    )
  )

# what changed in the resource n from the point a to the point b, as the
# writer w reads them: a resource that is not there is empty
def Node.diff(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +w: String,
  +n: Resources.Name,
  a: Point,
  b: Point
) -> List<&2, Formats.Change>:
  Formats.Format.changes(
    Formats.Format.of(Resources.Name.path(n)),
    Maybe.default(&2, Texts.Bytes(), Node.read(~d, ~kern, l, w, n, a), []),
    Maybe.default(&2, Texts.Bytes(), Node.read(~d, ~kern, l, w, n, b), [])
  )

# a branch, with its owners and its newest version (none: it has none yet)
type BranchEntry is Data:
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Maybe<&2, Ledgers.Id>}

# the ID of the newest version at the tip t
def Tip.newest(~d: Led(), l: L(d), +t: Replicas.Tip) -> Maybe<&2, Ledgers.Id>:
  Shared.Maybe.when(
    Ledgers.Id,
    Bool.not(U32.is_eq(Replicas.Tip.count(t), 0)),
    u => Maybe.bind(
      &2,
      Replicas.Taken,
      Ledgers.Id,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, U32.sub(Replicas.Tip.count(t), 1)),
      x => Some{Replicas.Taken.id(x)}
    )
  )

# the entry of the branch b, whose newest tip is m
def BranchEntry.of(~d: Led(), l: L(d), b: Branch, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, BranchEntry>:
  match m:
    case None{}:
      None{}
    case Some{+t}:
      Some{BranchEntry{b, Replicas.Tip.voters(t), Tip.newest(~d, l, t)}}

# the name of the branch that the binding x of the log of a store starts
def Branch.started(x: Trees.Binding) -> Maybe<&2, String>:
  match x:
    case Trees.Binding{Con{5, r}, v}:
      Replicas.Read.whole(String, Codes.Code.text.read(r))
    case _:
      None{}

# the names of the branches that the bindings xs of the log of a store start
def Branches.names(xs: List<&2, Trees.Binding>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Some.cons(String, Branch.started(x), Branches.names(rest))

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
          Trees.Tree.list(
            ~L(d),
            ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d),
            l,
            Replicas.Tip.log(t)
          )
        )
      )

# the entries of the branches bs
def Branches.entries(~d: Led(), ~kern: Kern(d), +l: L(d), bs: List<&2, Branch>) -> List<&2, BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      Some.cons(
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
# A resource uses what it imports, directly or not. An import names its
# target as written, in the space of the resource that imports it.

# the resource that the edge e of a resource of the space names
def Edge.name(space: String, e: Formats.Edge) -> Resources.Name:
  match e:
    case Formats.Edge{target, alias, conds}:
      Resources.Name{String.append(space, SCon{':', Texts.Bytes.to_text(target)})}

# the resources that the edges es of a resource of the space name
def Edges.names(+space: String, es: List<&2, Formats.Edge>) -> List<&2, Resources.Name>:
  match es:
    case Nil{}:
      []
    case Con{e, rest}:
      Edge.name(space, e) <> Edges.names(space, rest)

# what the resource n imports directly, in the tree whose root is h (nothing
# while l lacks its bytes)
def Res.imports(~d: Led(), +l: L(d), h: Maybe<&2, Hashes.Hash>, +n: Resources.Name) -> List<&2, Resources.Name>:
  Edges.names(
    Resources.Name.space(n),
    Formats.Format.uses(
      Formats.Format.of(Resources.Name.path(n)),
      [
        Maybe.default(
          &2,
          Texts.Bytes(),
          Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Texts.Bytes(),
            Res.find(~d, l, h, n),
            m => Root.bytes(~d, l, m)
          ),
          []
        )
      ]
    )
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
        h,
        rest,
        Reaches.Graph.links(Names.keys(Res.imports(~d, l, h, n)), Name.key(n), g)
      )

# the resource used is the resource changed, or uses it through its imports,
# at any depth, in the tree whose root is h. A clear def: it reads each
# resource of the tree
def Uses.reaches(
  ~d: Led(),
  +l: L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +used: Resources.Name,
  +changed: Resources.Name
) -> Bool:
  List.any.if(
    u => Tries.Trie.has(
      Unit,
      Reaches.Graph.reach(
        Uses.graph(~d, l, h, Tree.resources(~d, l, h), Reaches.Graph.new()),
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
      Maybe<&2, Ropes.Root>,
      Bool,
      Res.find(~d, l, h, n),
      a => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Bool,
        Res.find(~d, l, h2, n),
        b => Some{Bool.not(Roots.same(a, b))}
      )
    ),
    False{}
  )

# the root of the content before the version of the number n, at the tip t:
# the empty tree before the first one
def Tip.before(~d: Led(), l: L(d), t: Replicas.Tip, +n: U32) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Shared.Bool.when(
    Maybe<&2, Maybe<&2, Hashes.Hash>>,
    U32.is_eq(n, 0),
    u => Some{None{}},
    u => Maybe.bind(
      &2,
      Replicas.Taken,
      Maybe<&2, Hashes.Hash>,
      Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, U32.sub(n, 1)),
      x => Some{Taken.root(x)}
    )
  )

# a version that changed a resource, and the time of its request
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the time of the request of the entry m (none: it is not a request)
def Entry.time(m: Maybe<&2, Ledgers.Entry<Requests.Ask>>) -> String:
  match m:
    case Some{Ledgers.Entry.Ask{i, time, q}}:
      time
    case _:
      ""

# the time of the request that the outcome m is of, in l
def Out.time(~d: Led(), l: L(d), m: Maybe<&2, Replicas.Out>) -> String:
  match m:
    case Some{Replicas.Out.Taken{a, n}}:
      Entry.time(Replicas.Led.get(~Requests.Ask.machine(), ~d, l, Ledgers.Name.Ask{a}))
    case _:
      ""

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
        LogEntry{i, Out.time(~d, l, Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i))},
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
    Tip.versions(~d, k, l, t, from),
    Maybe.default(&2, Maybe<&2, Hashes.Hash>, Tip.before(~d, l, t, from), None{})
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

# the version of the outcome o, at the tip t, wrote the resource n: the
# resource holds after it what it did not hold before it
def Out.wrote(~d: Led(), +l: L(d), +t: Replicas.Tip, o: Replicas.Out, +n: Resources.Name) -> Bool:
  match o:
    case Replicas.Out.Stale{a}:
      False{}
    case Replicas.Out.Taken{a, +m}:
      Maybe.default(
        &2,
        Bool,
        Maybe.bind(
          &2,
          Maybe<&2, Hashes.Hash>,
          Bool,
          Tip.before(~d, l, t, m),
          h0 => Maybe.bind(
            &2,
            Replicas.Taken,
            Bool,
            Replicas.Tip.taken(~Requests.Ask.machine(), ~d, l, t, m),
            x => Some{Res.differs(~d, l, Taken.root(x), h0, n)}
          )
        ),
        False{}
      )

# Touch.holds once the newest tips tf of the branch from and tb of the branch
# are known
def Touch.holds.at(
  ~d: Led(),
  +l: L(d),
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
        u3 => Uses.reaches(~d, l, hb, used, changed),
        Maybe.is_some(
          &2,
          Ropes.Root,
          Maybe.default(&2, Maybe<&2, Ropes.Root>, Res.find(~d, l, hb, used), None{})
        )
      ),
      Res.differs(
        ~d,
        l,
        Maybe.default(&2, Maybe<&2, Hashes.Hash>, Tip.version(~d, l, tf, v), None{}),
        hb,
        changed
      )
    ),
    Maybe.default(
      &2,
      Bool,
      Maybe.bind(
        &2,
        Replicas.Out,
        Bool,
        Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, tf, v),
        o => Some{Out.wrote(~d, l, tf, o, changed)}
      ),
      False{}
    )
  )

# the touch x holds: its two branches are of one store and are not the same;
# its version is a version of the branch from, and wrote the resource
# changed; the branch does not hold what that version gave the resource; and
# the resource used is of the branch, and is the one changed or uses it. So a
# writer is told only about changes to what its work uses
def Touch.holds(~d: Led(), ~kern: Kern(d), +l: L(d), x: Touch) -> Bool:
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
              tb => Some{Touch.holds.at(~d, l, tf, tb, v, changed, used)}
            )
          ),
          False{}
        ),
        Branch.other(from, b)
      )

# the name of the resource of the binding x, when it is one that is there
def Res.live(x: Trees.Binding) -> Maybe<&2, Resources.Name>:
  match x:
    case Trees.Binding{Con{0, r}, v}:
      Shared.Maybe.when(
        Resources.Name,
        Maybe.is_some(&2, Ropes.Root, Res.read(v)),
        u => Replicas.Read.whole(Resources.Name, Resources.Name.code.read(r))
      )
    case _:
      None{}

# the resources that are there among the bindings xs
def Res.lives(xs: List<&2, Trees.Binding>) -> List<&2, Resources.Name>:
  match xs:
    case Nil{}:
      []
    case Con{x, rest}:
      Some.cons(Resources.Name, Res.live(x), Res.lives(rest))

# the graph g with the users of each import of the resources ns of the tree h:
# a resource leads to each resource that imports it. It is made once for a
# branch, and each search of it costs what it finds
def Uses.users(
  ~d: Led(),
  +l: L(d),
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
        h,
        rest,
        Reaches.Graph.back(Names.keys(Res.imports(~d, l, h, n)), Name.key(n), g)
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
          Res.names(
            Trees.Tree.diff(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, h0, h)
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
  from: Branch,
  +tf: Replicas.Tip,
  b: Branch,
  tb: Replicas.Tip
) -> List<&2, Touch>:
  +hb = Replicas.Tip.content(tb)
  +xs = Trees.Tree.list(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, hb)
  Touches.all(
    ~d,
    l,
    from,
    Tip.versions(~d, U32.to_nat(Replicas.Tip.count(tf)), l, tf, 0),
    None{},
    b,
    hb,
    Res.lives(xs),
    Uses.users(~d, l, hb, Res.names(xs), Reaches.Graph.new())
  )

# Branch.touches once the newest tip m of the branch b is known
def Branch.touches.of(
  ~d: Led(),
  l: L(d),
  from: Branch,
  tf: Replicas.Tip,
  b: Branch,
  m: Maybe<&2, Replicas.Tip>
) -> List<&2, Touch>:
  match m:
    case None{}:
      []
    case Some{tb}:
      Branch.touches.at(~d, l, from, tf, b, tb)

# the changes of the branch from that touch what the branch b uses: of each
# version of from, each resource that it wrote and that b does not hold as it
# gave it, with each resource of b that is that resource or uses it. The cost
# is the history of from and the resources of b, each read once
def Branch.touches(~d: Led(), ~kern: Kern(d), +l: L(d), +from: Branch, +b: Branch) -> List<&2, Touch>:
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
        tf => Some{Branch.touches.of(~d, l, from, tf, b, Branch.head(~d, ~kern, l, b))}
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
        Branch.touches(~d, ~kern, l, from, b),
        Branches.touch(~d, ~kern, l, rest, b)
      )

# the changes elsewhere that touch what the branch b uses, at any depth
def Node.affects(~d: Led(), ~kern: Kern(d), +l: L(d), +b: Branch) -> List<&2, Touch>:
  match b:
    case Branch{+st, n}:
      Branches.touch(~d, ~kern, l, Node.branches(~d, ~kern, l, st), Branch{st, n})

# what the changes of the branch from touch in each of the branches es
def Branches.touched(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
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
        Branch.touches(~d, ~kern, l, from, b),
        Branches.touched(~d, ~kern, l, from, rest)
      )

# what the changes of the branch b touch elsewhere
def Node.impact(~d: Led(), ~kern: Kern(d), +l: L(d), +b: Branch) -> List<&2, Touch>:
  match b:
    case Branch{+st, n}:
      Branches.touched(~d, ~kern, l, Branch{st, n}, Node.branches(~d, ~kern, l, st))

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, the changes elsewhere that touch it, or the lies of the nodes in a
# store
type Topic is Data:
  Topic.Versions{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Affects{branch: Branch}
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
      Notices.versions(b, Taken.ids(Tip.versions(~d, U32.to_nat(Replicas.Tip.count(t)), l, t, 0)))
    case False{} Some{+t}:
      Notices.conflicts(
        ~d,
        l,
        Replicas.Tip.content(t),
        b,
        Taken.ids(Tip.versions(~d, U32.to_nat(Replicas.Tip.count(t)), l, t, 0))
      )

# every notice of the topic x, by what the ledger holds
def Node.notices(~d: Led(), ~kern: Kern(d), +l: L(d), x: Topic) -> List<&2, Notice>:
  match x:
    case Topic.Versions{+b}:
      Notices.branch(~d, l, b, True{}, Branch.head(~d, ~kern, l, b))
    case Topic.Conflicts{+b}:
      Notices.branch(~d, l, b, False{}, Branch.head(~d, ~kern, l, b))
    case Topic.Affects{b}:
      Notices.touches(Node.affects(~d, ~kern, l, b))
    case Topic.Lies{+st}:
      Notices.lies(st, Ledgers.Kind.liars(Requests.Ask, Replicas.Led.kind(Requests.Ask.machine(), d))(l)(st))

# Mounts
# ------

# a resource mounted to a branch
type Mount is Data:
  Mount{resource: String, branch: Branch}

# a node may stop: it is forced to, or no resource is mounted and no writer
# is connected
def Node.may_stop(mounts: List<&2, Mount>, writers: List<&2, String>, force: Bool) -> Bool:
  Bool.or(
    force,
    Bool.and(List.is_empty(&2, Mount, mounts), List.is_empty(&2, String, writers))
  )

# the change that records what a resource held when it is mounted: a write
# of its bytes since the newest version, when the branch does not hold them
# at its tip t (none: nothing to record)
def Mount.change(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  held: Texts.Bytes()
) -> Maybe<&2, Requests.Change>:
  +r = Ropes.Put.root(Bytes.rope(held))
  Shared.Maybe.when(
    Requests.Change,
    Bool.not(
      Roots.same(
        Maybe.default(
          &2,
          Maybe<&2, Ropes.Root>,
          Res.find(~d, l, Replicas.Tip.content(t), n),
          None{}
        ),
        Some{r}
      )
    ),
    u => Some{Requests.Change.Write{n, Tip.newest(~d, l, t), Requests.Content.Root{r}}}
  )

# what a submodule holds: a branch of another store, and the version of it
# that the resource points to
type Pointer is Data:
  Pointer{store: Hashes.Hash, branch: String, version: Ledgers.Id}

# the pointer x, then r
def Pointer.code(x: Pointer, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Pointer{st, b, v}:
      Hashes.Hash.code(st, Codes.Code.text(b, Ledgers.Id.code(v, r)))

# a pointer
def Pointer.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Pointer>>:
  Codes.Code.three.read(
    ~Hashes.Hash,
    ~String,
    ~Ledgers.Id,
    ~Pointer,
    ~Hashes.Hash.code.read,
    ~Codes.Code.text.read,
    ~Ledgers.Id.code.read,
    st => b => v => Pointer{st, b, v},
    ts
  )

# a pointer reads back from its code: a submodule names one version of one
# branch of one store
def Pointer.code_read(
  x: Pointer,
  r: List<&2, U32>
) -> {Pointer.code.read(Pointer.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Pointer>>}:
  match x:
    case Pointer{st, b, v}:
      Codes.Code.three_read(
        ~Hashes.Hash,
        ~String,
        ~Ledgers.Id,
        ~Pointer,
        ~Hashes.Hash.codec(),
        ~Codes.Code.text.codec(),
        ~Ledgers.Id.codec(),
        a => c => e => Pointer{a, c, e},
        st,
        b,
        v,
        r
      )

# Owners that follow their group
# ------------------------------

# the name of the owner group of the line whose tip is t, if it has one
def Tip.group(~d: Led(), l: L(d), t: Replicas.Tip) -> Maybe<&2, String>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    String,
    Replicas.Tree.get(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.owner()),
    ws => Replicas.Read.whole(String, Codes.Code.text.read(ws))
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
      Bool.not(Names.same(ns, Replicas.Tip.voters(t)))
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
      Tip.newest(~d, l, ts),
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
  for a: L(d)
  for b: L(d)
  for i: Ledgers.Id
  for time: String
  for q: Requests.Ask
  for x: Answer
  for g: Replicas.Led.Grows(Requests.Ask.machine(), d, a, b)
  for honest: Replicas.Led.Honest(Requests.Ask.machine(), d, b)
  {Node.answer(~d, ~kern, a, i, time, q) == Some{x}: Maybe<&2, Answer>}
    -> {Answer.follows(x, Node.answer(~d, ~kern, b, i, time, q)) == True{}: Bool}

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
  for b: Maybe<&2, Ropes.Root>
  for o: Maybe<&2, Ropes.Root>
  for th: Maybe<&2, Ropes.Root>
  for x: Maybe<&2, Ropes.Root>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {
      Pick.merge(~d, l, Formats.Format.of(Resources.Name.path(n)), b, o, th) == Some{Pick.Take{x}}: Maybe<&2, Pick>
    }
    -> {
      Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
        == Some{x}: Maybe<&2, Maybe<&2, Ropes.Root>>
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
  for b: Maybe<&2, Ropes.Root>
  for o: Maybe<&2, Ropes.Root>
  for th: Maybe<&2, Ropes.Root>
  {Merge.act(~d, l, t, k, from, base) == Some{Replicas.Act.Taken{vs, h2, ns}}: Maybe<&2, Replicas.Act>}
    -> {Res.find(~d, l, Base.tree(base), n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.find(~d, l, Replicas.Tip.content(t), n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.find(~d, l, Source.root(from), n) == Some{th}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {
      Pick.merge(~d, l, Formats.Format.of(Resources.Name.path(n)), b, o, th) == Some{Pick.Clash{}}: Maybe<&2, Pick>
    }
    -> (
      {
        Res.find(~d, Replicas.Led.puts(~Requests.Ask.machine(), ~d, ns, l), h2, n)
          == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>
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
  for b: Branch
  for x: Touch
  {List.contains(~Touch, ~Touch.is_eq, Node.affects(~d, ~kern, l, b), x) == True{}: Bool}
    -> {Touch.holds(~d, ~kern, l, x) == True{}: Bool}

# and they are told about each of them: a touch that holds is among the
# touches that Node.affects gives for its branch
law Node.affects_complete:
  for ~d: Led()
  for ~kern: Kern(d)
  for l: L(d)
  for x: Touch
  {Touch.holds(~d, ~kern, l, x) == True{}: Bool}
    -> {
      List.contains(~Touch, ~Touch.is_eq, Node.affects(~d, ~kern, l, Touch.branch(x)), x) == True{}: Bool
    }
