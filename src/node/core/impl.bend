import Base
import ../../shared/replica.bend as Replicas
import ../../shared/shared/formats.bend as Formats
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/rope.bend as Ropes
import ../../shared/shared/shared/reach.bend as Reaches
import ../../shared/shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/shared/trie.bend as Tries
import ../../shared/shared/shared/text.bend as Texts
import ../../shared/shared/tree.bend as Trees
import ../shared/requests.bend as Requests
import ../shared/shared/resources.bend as Resources
import ./spec.bend as Spec

# Codes
# -----

# the owners that the change c gives its chain, when it sets them
def Change.owners(c: Requests.Change) -> Maybe<&2, List<&2, String>>:
  match c:
    case Requests.Change.Own{g, at, os}:
      Some{os}
    case _:
      None{}

# The state
# ---------

# Requests.Content
# -------
# The content of a line is a tree in key spaces: the first word of a key says
# which. 0: the root of a resource's content (none: removed). 2 (in a store's
# tree): a group's members. 3: a merge's clash, open or settled. 4: the version
# vector, the newest version of each other line that the content came from. 5
# (in a store's tree): the first tip of each of its branches. 6: the line's
# owner group. 7 (in a store's tree): the names of its groups.
# the key of the members of the group g
def Key.group(g: String) -> List<&2, U32>:
  2 <> Codes.Code.text(g, [])

# the key of a line's owner group
def Key.owner() -> List<&2, U32>:
  [6]

# the key of the names of a store's groups
def Key.groups() -> List<&2, U32>:
  [7]

# the key of the line c in a version vector
def Key.vector(c: Ledgers.Chain) -> List<&2, U32>:
  4 <> Ledgers.Chain.code(c, [])

def Spec.Content.of(b):
  Requests.Content.Root{Ropes.Put.root(Replicas.Bytes.rope(b))}

# the members of the group g in the store tree whose root is h, if g is there
def Members.in(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  g: String
) -> Maybe<&2, List<&2, Requests.Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Requests.Member>,
    Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.group(g)),
    ws => Replicas.Read.whole(List<&2, Requests.Member>, Requests.Members.code.read(ws))
  )

# Ancestry
# --------
# A version came from the versions before it on its line, by number, and from
# those that its version vector names, at their numbers or before.

# the newest place of the line c that the content whose root is h came from
def Node.vector(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  +c: Ledgers.Chain
) -> Maybe<&2, Replicas.Place>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Replicas.Place,
    Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.vector(c)),
    ws => Replicas.Place.read(c, ws)
  )

# the version at the place px, whose content has the root hx, came from the
# one at the place pv
def Place.from(
  s: Replicas.Node<Requests.Ask>,
  +px: Replicas.Place,
  hx: Maybe<&2, Hashes.Hash>,
  +pv: Replicas.Place
) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Replicas.Place.chain(px), Replicas.Place.chain(pv)),
    u => Replicas.Place.covers(px, pv),
    u => Replicas.Place.covered(Node.vector(s, hx, Replicas.Place.chain(pv)), pv)
  )

# Node.has once the places of x (mx) and of v (mv) and the root of x (mr) are
# known
def Has.of(
  s: Replicas.Node<Requests.Ask>,
  mx: Maybe<&2, Replicas.Place>,
  mv: Maybe<&2, Replicas.Place>,
  mr: Maybe<&2, Maybe<&2, Hashes.Hash>>
) -> Bool:
  match mx mv mr:
    case Some{px} Some{pv} Some{hx}:
      Place.from(s, px, hx, pv)
    case a b c:
      False{}

# x is v, or a version that v came from
def Node.has(+s: Replicas.Node<Requests.Ask>, +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Has.of(
      s,
      Replicas.Node.place(~Requests.Ask.machine(), s, x),
      Replicas.Node.place(~Requests.Ask.machine(), s, v),
      Replicas.Node.root(~Requests.Ask.machine(), s, x)
    ),
    Ledgers.Id.is_eq(x, v)
  )

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(
  +s: Replicas.Node<Requests.Ask>,
  +x: Ledgers.Id,
  +y: Ledgers.Id
) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )

# Writes
# ------

# w with the line c at the place p in its version vector, unless it holds that
# place or a newer one
def Vector.add(
  w: Replicas.Work<Requests.Ask>,
  +c: Ledgers.Chain,
  +p: Replicas.Place
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match w:
    case Replicas.Work{+s, +h}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Work<Requests.Ask>>,
        Replicas.Place.covered(Node.vector(s, h, c), p),
        u => Some{Replicas.Work{s, h}},
        u => Replicas.Work.set(
          ~Requests.Ask.machine(),
          Replicas.Work{s, h},
          Key.vector(c),
          Replicas.Place.code(p)
        )
      )

# the line and place of a version vector's entry, from its binding
def Vector.entry(b: Trees.Binding) -> Maybe<&2, Replicas.Place>:
  match b:
    case Trees.Binding{Con{4, k}, ws}:
      Maybe.bind(
        &2,
        Ledgers.Chain,
        Replicas.Place,
        Replicas.Read.whole(Ledgers.Chain, Ledgers.Chain.code.read(k)),
        c => Replicas.Place.read(c, ws)
      )
    case _:
      None{}

# w with the entry p in its version vector, when it is of a line other than c
def Vector.add.if(
  +w: Replicas.Work<Requests.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Place>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match m:
    case None{}:
      Some{w}
    case Some{+p}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Work<Requests.Ask>>,
        Ledgers.Chain.is_eq(Replicas.Place.chain(p), c),
        u => Some{w},
        u => Vector.add(w, Replicas.Place.chain(p), p)
      )

# m with the entries of the bindings bs, other than of the line c, in its
# version vector
def Vector.adds(
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match bs:
    case Nil{}:
      m
    case Con{b, r}:
      Vector.adds(
        r,
        c,
        Maybe.bind(
          &2,
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Vector.add.if(w, c, Vector.entry(b))
        )
      )

# a pointer to a child: a branch and a version of another store
type Pointer is Data:
  Pointer{space: String, store: Ledgers.Id, branch: String, version: Ledgers.Id}

# the version of the child that p points to
def Pointer.version(p: Pointer) -> Ledgers.Id:
  match p:
    case Pointer{sp, st, b, v}:
      v

# the bytes of the pointer p (Texts.Text.cuts_after_join reads them back)
def Pointer.show(p: Pointer) -> Texts.Bytes():
  match p:
    case Pointer{sp, Ledgers.Id{sw, sr}, b, Ledgers.Id{w, r}}:
      Texts.Bytes.of_text(Texts.Text.join([sp, sw, sr, b, w], Chr{10}, r))

# the pointer of the lines that a text cut into (m)
def Pointer.read.of(m: Maybe<&2, Texts.Parts>) -> Maybe<&2, Pointer>:
  match m:
    case Some{Texts.Parts{Con{sp, Con{sw, Con{sr, Con{b, Con{w, Nil{}}}}}}, r}}:
      Some{Pointer{sp, Ledgers.Id{sw, sr}, b, Ledgers.Id{w, r}}}
    case _:
      None{}

# the pointer in the bytes b
def Pointer.read(b: Texts.Bytes()) -> Maybe<&2, Pointer>:
  Pointer.read.of(Texts.Text.cuts(5n, Texts.Bytes.to_text(b), 10))

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Spec.Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Spec.Pick.Make{x}
    case Formats.Merged.Clash{}:
      Spec.Pick.Clash{}

# the merge of the submodules px and py: the one at the newer version m, if any
def Pick.module(m: Maybe<&2, Ledgers.Id>, px: Pointer, +py: Pointer) -> Spec.Pick:
  match m:
    case None{}:
      Spec.Pick.Clash{}
    case Some{k}:
      Spec.Pick.Make{
        Pointer.show(
          Shared.Bool.when(Pointer, Ledgers.Id.is_eq(k, Pointer.version(py)), u => py, u => px)
        )
      }

# the merge of two submodules that point as x and y
def Pick.pointers(
  s: Replicas.Node<Requests.Ask>,
  x: Maybe<&2, Pointer>,
  y: Maybe<&2, Pointer>
) -> Spec.Pick:
  match x y:
    case Some{+px} Some{+py}:
      Pick.module(Node.forward(s, Pointer.version(px), Pointer.version(py)), px, py)
    case _ _:
      Spec.Pick.Clash{}

# the merge of x and y, two changes of b, in the format f
def Pick.format(
  f: Formats.Format,
  s: Replicas.Node<Requests.Ask>,
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Spec.Pick:
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      Pick.pointers(s, Pointer.read(x), Pointer.read(y))
    case g:
      Pick.bytes(Formats.Format.merge(g, b, x, y))

# the merge of the bytes x and y, two changes of mb, in the format f (none: the
# node does not hold all of them yet)
def Pick.read(
  f: Formats.Format,
  s: Replicas.Node<Requests.Ask>,
  mb: Maybe<&2, Texts.Bytes()>,
  mx: Maybe<&2, Texts.Bytes()>,
  my: Maybe<&2, Texts.Bytes()>
) -> Maybe<&2, Spec.Pick>:
  match mb mx my:
    case Some{b} Some{x} Some{y}:
      Some{Pick.format(f, s, b, x, y)}
    case u v w:
      None{}

# the bytes of the base b of a merge (none: the node does not hold them yet):
# no base is no bytes
def Pick.base(s: Replicas.Node<Requests.Ask>, b: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  match b:
    case None{}:
      Some{[]}
    case Some{r}:
      Replicas.Root.bytes(~Requests.Ask.machine(), s, Some{r})

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f (none: wait for its bytes)
def Pick.both(
  f: Formats.Format,
  +s: Replicas.Node<Requests.Ask>,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Spec.Pick>:
  match o t:
    case Some{x} Some{y}:
      Pick.read(
        f,
        s,
        Pick.base(s, b),
        Replicas.Root.bytes(~Requests.Ask.machine(), s, Some{x}),
        Replicas.Root.bytes(~Requests.Ask.machine(), s, Some{y})
      )
    case _ _:
      Some{Spec.Pick.Clash{}}

def Spec.Pick.merge(f, s, b, o, t):
  Shared.Bool.when(
    Maybe<&2, Spec.Pick>,
    Spec.Roots.same(o, b),
    u => Some{Spec.Pick.Take{t}},
    u => Shared.Bool.when(
      Maybe<&2, Spec.Pick>,
      List.any.if(v => Spec.Roots.same(o, t), Spec.Roots.same(t, b)),
      w => Some{Spec.Pick.Take{o}},
      w => Pick.both(f, s, b, o, t)
    )
  )

# the resource n, when it is there, then rest
def Names.put(
  m: Maybe<&2, Resources.Name>,
  rest: List<&2, Resources.Name>
) -> List<&2, Resources.Name>:
  match m:
    case Some{n}:
      n <> rest
    case None{}:
      rest

# the resource of a binding of a tree, when it is a resource that is there
def Res.binding(b: Trees.Binding) -> Maybe<&2, Resources.Name>:
  match b:
    case Trees.Binding{Con{0, k}, ws}:
      Shared.Bool.when(
        Maybe<&2, Resources.Name>,
        Maybe.is_some(&2, Ropes.Root, Spec.Res.read(ws)),
        u => Replicas.Read.whole(Resources.Name, Resources.Name.code.read(k)),
        u => None{}
      )
    case _:
      None{}

# the resources among the bindings bs
def Res.of.bindings(bs: List<&2, Trees.Binding>) -> List<&2, Resources.Name>:
  match bs:
    case Nil{}:
      []
    case Con{b, r}:
      Names.put(Res.binding(b), Res.of.bindings(r))

# the resources of the tree whose root is h
def Res.names(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>
) -> List<&2, Resources.Name>:
  Res.of.bindings(
    Trees.Tree.list(
      ~Replicas.Node<Requests.Ask>,
      ~Replicas.Store.fetch(~Requests.Ask.machine()),
      s,
      h
    )
  )

# the key of the resource n
def Name.key(n: Resources.Name) -> List<&2, Bool>:
  Tries.Trie.text(Resources.Name.show(n))

def Spec.Merge.names(s, h, ht):
  Tries.Trie.unique(
    ~Resources.Name,
    ~Name.key,
    Res.of.bindings(
      Trees.Tree.diff(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h,
        ht
      )
    ),
    Tries.Trie.new(Unit)
  )

# the groups of a store tree, as a graph
type Groups is Data:
  Groups{state: Replicas.Node<Requests.Ask>, root: Maybe<&2, Hashes.Hash>}

# the members of m in the groups g, when it is a group
def Group.succ(g: Groups, m: Requests.Member) -> List<&2, Requests.Member>:
  match g m:
    case Groups{s, h} Requests.Member.Node{n}:
      []
    case Groups{s, h} Requests.Member.Group{x}:
      Maybe.default(&2, List<&2, Requests.Member>, Members.in(s, h, x), [])

# the names of the groups in the store tree whose root is h
def Group.names(s: Replicas.Node<Requests.Ask>, h: Maybe<&2, Hashes.Hash>) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, String>,
      Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.groups()),
      ws => Replicas.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
    ),
    []
  )

# the groups of the names ns, as members
def Group.of.names(ns: List<&2, String>) -> List<&2, Requests.Member>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Requests.Member.Group{n} <> Group.of.names(r)

# every group of the groups g, as a member
def Group.all(g: Groups) -> List<&2, Requests.Member>:
  match g:
    case Groups{s, h}:
      Group.of.names(Group.names(s, h))

# the key of the member m: a node and a group of one name have two keys
def Member.key(m: Requests.Member) -> List<&2, Bool>:
  match m:
    case Requests.Member.Node{n}:
      False{} <> Tries.Trie.text(n)
    case Requests.Member.Group{g}:
      True{} <> Tries.Trie.text(g)

# the keys of the members ms
def Member.keys(ms: List<&2, Requests.Member>) -> List<&2, List<&2, Bool>>:
  match ms:
    case Nil{}:
      []
    case Con{m, r}:
      Member.key(m) <> Member.keys(r)

# gr with the members of each group of ns, in the store tree whose root is h
def Group.graph.go(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, String>,
  gr: Reaches.Graph
) -> Reaches.Graph:
  match ns:
    case Nil{}:
      gr
    case Con{+x, r}:
      Group.graph.go(
        s,
        h,
        r,
        Reaches.Graph.links(
          Member.keys(Maybe.default(&2, List<&2, Requests.Member>, Members.in(s, h, x), [])),
          Member.key(Requests.Member.Group{x}),
          gr
        )
      )

# the groups of the store tree whose root is h, as a graph: each group, with
# its members
def Group.graph(+s: Replicas.Node<Requests.Ask>, +h: Maybe<&2, Hashes.Hash>) -> Reaches.Graph:
  Group.graph.go(s, h, Group.names(s, h), Reaches.Graph.new())

# the nodes among the members ms
def Group.nodes.of(ms: List<&2, Requests.Member>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Requests.Member.Node{n}, r}:
      n <> Group.nodes.of(r)
    case Con{Requests.Member.Group{g}, r}:
      Group.nodes.of(r)

# the nodes that each group of gs names, as they come
def Group.named.all(+g: Groups, gs: List<&2, Requests.Member>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{m, r}:
      List.append(&2, String, Group.nodes.of(Group.succ(g, m)), Group.named.all(g, r))

# the nodes that some group of gs names
def Group.named(g: Groups, gs: List<&2, Requests.Member>) -> List<&2, String>:
  Tries.Trie.unique(~String, ~Tries.Trie.text, Group.named.all(g, gs), Tries.Trie.new(Unit))

# the nodes of ns whose keys in holds
def Group.inside(ns: List<&2, String>, +in: Tries.Trie<Unit>) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      List.filter.put(
        String,
        n,
        Group.inside(rest, in),
        Tries.Trie.has(Unit, in, Member.key(Requests.Member.Node{n}))
      )

def Spec.Group.nodes(s, h, g):
  +gs = {Groups{s, h}: Groups}
  Group.inside(
    Group.named(gs, Group.all(gs)),
    Reaches.Graph.reach(Group.graph(s, h), Member.key(Requests.Member.Group{g}))
  )

# some member of ms makes the group g of the store tree h contain itself: g
# is one of them, or is inside one. One search finds it, from a node whose
# successors are the members (the empty key: no member has it)
def Group.loops.any(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  g: String,
  ms: List<&2, Requests.Member>
) -> Bool:
  Tries.Trie.has(
    Unit,
    Reaches.Graph.reach(Reaches.Graph.links(Member.keys(ms), [], Group.graph(s, h)), []),
    Member.key(Requests.Member.Group{g})
  )

# Judging
# -------
# The owners of a line give each request one outcome, in a step: take it, with
# the content that the line holds after it, or refuse it as stale. A step
# waits while a version that a request names is not decided yet, or the node
# lacks a node of a tree that it reads.

# the verdict that the outcome m of a version gives a request that names it:
# take it when it is a version, refuse it when it is stale, else wait
def Judge.ready.of(m: Maybe<&2, Replicas.Out>) -> Maybe<&2, Bool>:
  match m:
    case Some{Replicas.Out.Taken{n}}:
      Some{True{}}
    case Some{Replicas.Out.Stale{}}:
      Some{False{}}
    case None{}:
      None{}

# the verdict of the version v, for a request that names it
def Judge.ready(s: Replicas.Node<Requests.Ask>, v: Ledgers.Id) -> Maybe<&2, Bool>:
  Judge.ready.of(Replicas.Node.out(~Requests.Ask.machine(), s, v))

# the verdict of the version m, if any
def Judge.ready_maybe(s: Replicas.Node<Requests.Ask>, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      Some{True{}}
    case Some{v}:
      Judge.ready(s, v)

# the verdict on the content c: its version must be one
def Judge.content(s: Replicas.Node<Requests.Ask>, c: Requests.Content) -> Maybe<&2, Bool>:
  match c:
    case Requests.Content.Root{x}:
      Some{True{}}
    case Requests.Content.Of{w}:
      Judge.ready(s, w)

# a refusal
def Judge.refuse() -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  Some{Replicas.Verdict.Stale{}}

# the verdict m, then k when m takes
def Judge.then(
  m: Maybe<&2, Bool>,
  k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  match m:
    case Some{True{}}:
      k(Unit{})
    case Some{False{}}:
      Judge.refuse()
    case None{}:
      None{}

# k when b holds, else a refusal
def Judge.when(
  b: Bool,
  k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  Shared.Bool.when(Maybe<&2, Replicas.Verdict<Requests.Ask>>, b, k, u => Judge.refuse())

def Spec.Judge.write(s, n, base, c, h):
  Judge.then(
    Judge.ready_maybe(s, base),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Verdict<Requests.Ask>,
        Spec.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            )
          )
        )
      )
    )
  )

# the version that the request m merged, when m is a merge on the branch b of
# the store r
def Merge.from_on(
  m: Maybe<&2, Ledgers.Asked<Requests.Ask>>,
  r: Ledgers.Id,
  b: String
) -> Maybe<&2, Ledgers.Id>:
  match m:
    case Some{Ledgers.Asked{t, Requests.Ask.On{st, Some{x}, Requests.Change.Merge{f}}}}:
      Shared.Maybe.when(
        Ledgers.Id,
        Bool.and(Ledgers.Id.is_eq(st, r), String.eq(x, b)),
        u => Some{f}
      )
    case _:
      None{}

# the clash of the resource n is open in the tree h, by the merge of the
# version m, if any (none: the node lacks a node of the tree)
def Clash.find(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      Some{False{}}
    case Some{f}:
      Maybe.bind(
        &2,
        Maybe<&2, List<&2, U32>>,
        Bool,
        Replicas.Node.find(~Requests.Ask.machine(), s, h, Spec.Key.clash(n)),
        x => Some{
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            x,
            Some{Spec.Clash.code(f)}
          )
        }
      )

def Spec.Resolve.work(s, h, n, m):
  Maybe.bind(
    &2,
    Replicas.Work<Requests.Ask>,
    Replicas.Work<Requests.Ask>,
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Spec.Key.res(n),
      Spec.Res.code(m)
    ),
    y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), [])
  )

# the verdict on a resolve of the resource n, which the merge k left in clash
# on the branch b of the store r, with the content c, at the tree h
def Judge.resolve(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  b: String,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Requests.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  Judge.then(
    Judge.ready(s, k),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Replicas.Verdict<Requests.Ask>,
        Clash.find(
          s,
          h,
          n,
          Merge.from_on(Replicas.Node.asked(~Requests.Ask.machine(), s, k), r, b)
        ),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Content.find(s, n, c),
          m => Judge.when(
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m))
          )
        )
      )
    )
  )

# w with what the merge of the version f keeps of the resource n (p): the
# content of a side; new bytes, with their rope; or ours (o), and its clash
# open
def Merge.put(
  f: Ledgers.Id,
  +n: Resources.Name,
  o: Maybe<&2, Ropes.Root>,
  p: Spec.Pick,
  w: Replicas.Work<Requests.Ask>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match p:
    case Spec.Pick.Take{m}:
      Replicas.Work.set(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(m))
    case Spec.Pick.Make{x}:
      +rp = Replicas.Bytes.rope(x)
      Maybe.bind(
        &2,
        Replicas.Work<Requests.Ask>,
        Replicas.Work<Requests.Ask>,
        Replicas.Work.keep(~Requests.Ask.machine(), w, Ropes.Put.nodes(rp)),
        w2 => Replicas.Work.set(
          ~Requests.Ask.machine(),
          w2,
          Spec.Key.res(n),
          Spec.Res.code(Some{Ropes.Put.root(rp)})
        )
      )
    case Spec.Pick.Clash{}:
      Maybe.bind(
        &2,
        Replicas.Work<Requests.Ask>,
        Replicas.Work<Requests.Ask>,
        Replicas.Work.set(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(o)),
        y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), Spec.Clash.code(f))
      )

# w with the resource n merged: what the merge of the base b, ours o and theirs
# t (of the version f) keeps (none: wait for a node)
def Merge.one(
  s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  w: Replicas.Work<Requests.Ask>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  Maybe.bind(
    &2,
    Spec.Pick,
    Replicas.Work<Requests.Ask>,
    Spec.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    p => Merge.put(f, n, o, p, w)
  )

# m with each resource of ns merged, over the base hb, ours ho and theirs ht
# (of the version f)
def Merge.all(
  +s: Replicas.Node<Requests.Ask>,
  +f: Ledgers.Id,
  ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match ns:
    case Nil{}:
      m
    case Con{+n, r}:
      Merge.all(
        s,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(
          &2,
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Work<Requests.Ask>,
            Spec.Res.find(s, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Requests.Ask>,
              Spec.Res.find(s, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Requests.Ask>,
                Spec.Res.find(s, ht, n),
                x => Merge.one(s, f, n, b, o, x, w)
              )
            )
          )
        )
      )

# the request of the version v, as a version
def Version.some(v: Replicas.Version) -> Maybe<&2, Ledgers.Id>:
  Some{Replicas.Version.id(v)}

# the version of the number n of the line at the tip t
def Version.in(s: Replicas.Node<Requests.Ask>, n: U32, t: Replicas.Tip) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    Replicas.Version,
    Ledgers.Id,
    Replicas.Line.version(~Requests.Ask.machine(), s, t, n),
    v => Version.some(v)
  )

# the version at the place p
def Version.at(+s: Replicas.Node<Requests.Ask>, p: Replicas.Place) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Replicas.Place{c, n}:
      Maybe.bind(
        &2,
        Replicas.Tip,
        Ledgers.Id,
        Replicas.Node.tip(~Requests.Ask.machine(), s, c),
        t => Version.in(s, n, t)
      )

# the newer of two versions that both sides of a merge came from: a, a
# version of our line that theirs came from, and the version at the place p of
# their line cf that ours came from. a is the newer one when it came from the
# other
def Base.pick(
  +s: Replicas.Node<Requests.Ask>,
  cf: Ledgers.Chain,
  ma: Maybe<&2, Ledgers.Id>,
  mp: Maybe<&2, Replicas.Place>
) -> Maybe<&2, Ledgers.Id>:
  match ma mp:
    case None{} None{}:
      None{}
    case Some{a} None{}:
      Some{a}
    case None{} Some{p}:
      Version.at(s, p)
    case Some{+a} Some{+p}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Id>,
        Replicas.Place.covered(
          Node.vector(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{a}), cf),
          p
        ),
        u => Some{a},
        u => Version.at(s, p)
      )

def Spec.Merge.base(s, c, from, h):
  Maybe.bind(
    &2,
    Replicas.Place,
    Ledgers.Id,
    Replicas.Node.place(~Requests.Ask.machine(), s, from),
    +pf => Shared.Bool.when(
      Maybe<&2, Ledgers.Id>,
      Ledgers.Chain.is_eq(Replicas.Place.chain(pf), c),
      u => Some{from},
      u => Base.pick(
        s,
        Replicas.Place.chain(pf),
        Maybe.bind(
          &2,
          Replicas.Place,
          Ledgers.Id,
          Node.vector(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}), c),
          w => Version.at(s, w)
        ),
        Node.vector(s, h, Replicas.Place.chain(pf))
      )
    )
  )

# m with the version v, of a line other than c, in its version vector: its
# vector, and its own place
def Vector.joined(
  +s: Replicas.Node<Requests.Ask>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  Maybe.bind(
    &2,
    Replicas.Work<Requests.Ask>,
    Replicas.Work<Requests.Ask>,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{v})
      ),
      c,
      m
    ),
    w => Vector.add.if(w, c, Replicas.Node.place(~Requests.Ask.machine(), s, v))
  )

def Spec.Merge.work(s, c, from, h):
  +ht = Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})
  Vector.joined(
    s,
    c,
    from,
    Merge.all(
      s,
      from,
      Spec.Merge.names(s, h, ht),
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Spec.Merge.base(s, c, from, h)),
      h,
      ht,
      Some{Replicas.Work{s, h}}
    )
  )

def Spec.Move.work(s, c, to, h):
  Vector.joined(
    s,
    c,
    to,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h
      ),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})}}
    )
  )

# the first tree of a branch made at the version m, if any, of the line c: its
# tree, with what it came from in its version vector
def Make.branch(
  +s: Replicas.Node<Requests.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  match m:
    case None{}:
      Some{Replicas.Work{s, None{}}}
    case Some{+v}:
      Vector.joined(
        s,
        c,
        v,
        Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{v})}}
      )

# the store tree h with the group g, of the members ms, and its name among the
# names of its groups
def Group.work(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  ms: List<&2, Requests.Member>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  +ns = Group.names(s, h)
  Maybe.bind(
    &2,
    Replicas.Work<Requests.Ask>,
    Replicas.Work<Requests.Ask>,
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Key.group(g),
      Requests.Members.code(ms, [])
    ),
    +w => Shared.Bool.when(
      Maybe<&2, Replicas.Work<Requests.Ask>>,
      List.contains(~String, ~String.eq, ns, g),
      u => Some{w},
      u => Replicas.Work.set(
        ~Requests.Ask.machine(),
        w,
        Key.groups(),
        Ledgers.Owners.code(g <> ns, [])
      )
    )
  )

# the owners os are the nodes ns, and there is one
def Own.fits(+os: List<&2, String>, ns: List<&2, String>) -> Bool:
  List.all.if(u => Ledgers.Owners.is_eq(os, ns), Bool.not(List.is_empty(&2, String, os)))

# the first tip of a new branch, from its first content (the root of start):
# no log, no version, and the owners os of its store now
def Make.first(
  start: Maybe<&2, Replicas.Work<Requests.Ask>>,
  os: List<&2, String>
) -> Maybe<&2, Replicas.Made<Requests.Ask>>:
  match start:
    case None{}:
      None{}
    case Some{+w}:
      +t = {
        Replicas.Tip{Replicas.Work.root(~Requests.Ask.machine(), w), None{}, 0, os}: Replicas.Tip
      }
      Replicas.Made.put(
        ~Requests.Ask.machine(),
        t,
        Replicas.Work.keep(~Requests.Ask.machine(), w, [Replicas.Tip.words(t)])
      )

# the version at is a version of the store r: at the place m
def Own.at(r: Ledgers.Id, m: Maybe<&2, Replicas.Place>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      None{}
    case Some{Replicas.Place{c, n}}:
      Some{Ledgers.Chain.is_eq(c, Ledgers.Chain{r, None{}})}

# an Own of the line l of the store r may name the version at: a store reads
# its own content; a branch names a version of its store (none: wait for it)
def Own.ok(
  s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  at: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Bool>:
  match l at:
    case None{} y:
      Some{True{}}
    case Some{b} None{}:
      Some{False{}}
    case Some{b} Some{v}:
      Own.at(r, Replicas.Node.place(~Requests.Ask.machine(), s, v))

# the node holds the members of each group of ns of the store tree h
def Groups.held.all(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, String>
) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, r}:
      List.all.if(
        u => Groups.held.all(s, h, r),
        Maybe.is_some(
          &2,
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.find(~Requests.Ask.machine(), s, h, Key.group(n))
        )
      )

# the node holds the groups of the store tree h: their names, and the members
# of each. Only then does it know which nodes are inside a group
def Groups.held(+s: Replicas.Node<Requests.Ask>, +h: Maybe<&2, Hashes.Hash>) -> Bool:
  List.all.if(
    u => Groups.held.all(s, h, Group.names(s, h)),
    Maybe.is_some(
      &2,
      Maybe<&2, List<&2, U32>>,
      Replicas.Node.find(~Requests.Ask.machine(), s, h, Key.groups())
    )
  )

# Spec.Own.takes once whether the Own may name its version is known (k), in the
# store tree h (none: wait for the groups)
def Own.takes.at(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  g: String,
  os: List<&2, String>,
  k: Bool
) -> Maybe<&2, Bool>:
  match k:
    case False{}:
      Some{False{}}
    case True{}:
      Shared.Maybe.when(Bool, Groups.held(s, h), u => Some{Own.fits(os, Spec.Group.nodes(s, h, g))})

def Spec.Own.takes(s, r, l, g, at, os, h):
  Maybe.bind(
    &2,
    Bool,
    Bool,
    Own.ok(s, r, l, at),
    k => Own.takes.at(s, Spec.Own.tree(s, l, at, h), g, os, k)
  )

# the verdict on an Own of the line l of the store r: when its owners take it
# (Spec.Own.takes), its owner group is g
def Own.change(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  Judge.then(
    Spec.Own.takes(s, r, l, g, at, os, h),
    u => Replicas.Work.take(
      ~Requests.Ask.machine(),
      Replicas.Work.set(
        ~Requests.Ask.machine(),
        Replicas.Work{s, h},
        Key.owner(),
        Codes.Code.text(g, [])
      )
    )
  )

# the node s holds each node of the trees whose roots are a and b
def Whole.both(
  +s: Replicas.Node<Requests.Ask>,
  a: Maybe<&2, Hashes.Hash>,
  b: Maybe<&2, Hashes.Hash>
) -> Bool:
  List.all.if(
    u => Trees.Tree.whole(
      ~Replicas.Node<Requests.Ask>,
      ~Replicas.Store.fetch(~Requests.Ask.machine()),
      s,
      b
    ),
    Trees.Tree.whole(
      ~Replicas.Node<Requests.Ask>,
      ~Replicas.Store.fetch(~Requests.Ask.machine()),
      s,
      a
    )
  )

# k when the node holds the whole of the trees that a walk reads (b), else
# wait: a merge or a move acts on a whole tree, never on the part that the
# node holds
def Judge.whole(
  b: Bool,
  k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  match b:
    case True{}:
      k(Unit{})
    case False{}:
      None{}

# the verdict on the change c of the line l of the store r, at the content h,
# when the owners of the line are os
def Judge.change(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Requests.Change,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Replicas.Verdict<Requests.Ask>>:
  match l c:
    case None{} Requests.Change.Group{+g, +ms}:
      Judge.when(
        Bool.not(Group.loops.any(s, h, g, ms)),
        u => Replicas.Work.take(~Requests.Ask.machine(), Group.work(s, h, g, ms))
      )
    case None{} Requests.Change.Key{n, k}:
      Replicas.Work.take(
        ~Requests.Ask.machine(),
        Replicas.Work.set(
          ~Requests.Ask.machine(),
          Replicas.Work{s, h},
          Requests.Key.seal(n),
          Hashes.Hash.code(k, [])
        )
      )
    case w Requests.Change.Own{g, at, os2}:
      Own.change(s, r, w, g, at, os2, h)
    case Some{b} Requests.Change.Write{n, base, c2}:
      Spec.Judge.write(s, n, base, c2, h)
    case Some{+b} Requests.Change.Resolve{k, n, c2}:
      Judge.resolve(s, r, b, k, n, c2, h)
    case Some{+b} Requests.Change.Merge{+from}:
      Judge.then(
        Judge.ready(s, from),
        u => Judge.whole(
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)
          )
        )
      )
    case Some{+b} Requests.Change.Move{+to}:
      Judge.then(
        Judge.ready(s, to),
        u => Judge.whole(
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)
          )
        )
      )
    case w c3:
      Judge.refuse()

# Steps
# -----
# A step runs a batch of requests, in order, from a tip: each request gets its
# outcome in the log, once, and a request that the log holds already is
# skipped. A run is a function of the tip, the requests and the versions that
# they name, so every node that runs a step gets the same tip.

# Step.branch once it is known whether the version that the branch starts at
# is one (m; none: wait for it)
def Branch.ready(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{False{}}:
      Replicas.Step.stale(~Requests.Ask.machine(), r, i)
    case Some{True{}}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Run<Requests.Ask>>,
        Trees.Tree.whole(
          ~Replicas.Node<Requests.Ask>,
          ~Replicas.Store.fetch(~Requests.Ask.machine()),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Node.root_of(
            ~Requests.Ask.machine(),
            Replicas.Run.state(~Requests.Ask.machine(), r),
            at
          )
        ),
        u => Replicas.Branch.made(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        ),
        u => None{}
      )

# Step.branch once what the log of the store holds for the branch is known
# (m; none: the node lacks a part of the log)
def Branch.new(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{Some{x}}:
      Replicas.Step.stale(~Requests.Ask.machine(), r, i)
    case Some{None{}}:
      Branch.ready(
        r,
        i,
        st,
        b,
        at,
        Judge.ready_maybe(Replicas.Run.state(~Requests.Ask.machine(), r), at)
      )

# the run r of a store, after the request i for a new branch b from the
# version at: the log gets the first tip of b, for good; a store makes a
# branch once, so a branch that it has refuses the request
def Step.branch(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  at: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  Branch.new(
    r,
    i,
    st,
    b,
    at,
    Replicas.Node.find(
      ~Requests.Ask.machine(),
      Replicas.Run.state(~Requests.Ask.machine(), r),
      Replicas.Tip.log(Replicas.Run.tip(~Requests.Ask.machine(), r)),
      Replicas.Log.start(b)
    )
  )

# how a line takes a change: a branch writes a mark to its log, a store
# writes a new branch to its log, and a judge decides any other change
type Route is Data:
  Route.Mark{mark: String}
  Route.Branch{name: String, at: Maybe<&2, Ledgers.Id>}
  Route.Judge{}

# how the line l takes the change ch
def Route.of(l: Maybe<&2, String>, ch: Requests.Change) -> Route:
  match l ch:
    case Some{b} Requests.Change.Mark{m, d}:
      Route.Mark{m}
    case None{} Requests.Change.Branch{b, at}:
      Route.Branch{b, at}
    case x y:
      Route.Judge{}

# Step.on once it is known how the line takes the change (w)
def Step.on.of(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  +ch: Requests.Change,
  w: Route
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  match w:
    case Route.Mark{m}:
      Replicas.Step.mark(~Requests.Ask.machine(), r, i, m)
    case Route.Branch{b, at}:
      Step.branch(r, i, st, b, at)
    case Route.Judge{}:
      s = Replicas.Run.state(~Requests.Ask.machine(), r)
      t = Replicas.Run.tip(~Requests.Ask.machine(), r)
      Replicas.Step.judged(
        ~Requests.Ask.machine(),
        r,
        i,
        Change.owners(ch),
        Judge.change(s, st, l, ch, Replicas.Tip.content(t))
      )

# the run r, after the request i of the change ch of the line l of the store
# st
def Step.on(
  r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  Step.on.of(r, i, st, l, ch, Route.of(l, ch))

# the run r of the line c, after the request i of q: a request of another
# line, or one that starts a store, is stale here
def Step.change(
  +r: Replicas.Run<Requests.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Requests.Ask
) -> Maybe<&2, Replicas.Run<Requests.Ask>>:
  match q:
    case Requests.Ask.Start{os}:
      Replicas.Step.stale(~Requests.Ask.machine(), r, i)
    case Requests.Ask.On{+st, +l, ch}:
      Shared.Bool.when(
        Maybe<&2, Replicas.Run<Requests.Ask>>,
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        u => Step.on(r, i, st, l, ch),
        u => Replicas.Step.stale(~Requests.Ask.machine(), r, i)
      )

# the root of the content of the line c now (none: the empty tree, or the node
# does not follow c)
def Chain.root(s: Replicas.Node<Requests.Ask>, c: Ledgers.Chain) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Hashes.Hash,
    Replicas.Node.tip(~Requests.Ask.machine(), s, c),
    t => Replicas.Tip.content(t)
  )

# the root of the content of the store r now
def Store.root(s: Replicas.Node<Requests.Ask>, r: Ledgers.Id) -> Maybe<&2, Hashes.Hash>:
  Chain.root(s, Ledgers.Chain{r, None{}})

# the newest version of a line at the tip t, if it has one
def Line.newest(s: Replicas.Node<Requests.Ask>, +t: Replicas.Tip) -> Maybe<&2, Ledgers.Id>:
  +n = Replicas.Tip.count(t)
  Shared.Maybe.when(Ledgers.Id, Bool.not(U32.is_eq(n, 0)), u => Version.in(s, U32.sub(n, 1), t))

# the newest version of the line c, if it has one
def Chain.newest(+s: Replicas.Node<Requests.Ask>, c: Ledgers.Chain) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    Replicas.Tip,
    Ledgers.Id,
    Replicas.Node.tip(~Requests.Ask.machine(), s, c),
    t => Line.newest(s, t)
  )

# the newest version of the store r
def Store.head(s: Replicas.Node<Requests.Ask>, r: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Ledgers.Chain{r, None{}})

# the owners of the next step of the line l of the store r
def Node.owners(
  s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>
) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, String>,
      Replicas.Node.tip(~Requests.Ask.machine(), s, Replicas.Line.chain(r, l)),
      t => Some{Replicas.Tip.owners(t)}
    ),
    []
  )

# the nodes inside the group g of the store r
def Node.nodes(+s: Replicas.Node<Requests.Ask>, r: Ledgers.Id, g: String) -> List<&2, String>:
  Spec.Group.nodes(s, Store.root(s, r), g)

# the owner group of the line l of the store r, if it has one (none: its
# owners are the nodes that it started with)
def Node.group(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>
) -> Maybe<&2, String>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    String,
    Replicas.Node.get(
      ~Requests.Ask.machine(),
      s,
      Chain.root(s, Replicas.Line.chain(r, l)),
      Key.owner()
    ),
    ws => Replicas.Read.whole(String, Codes.Code.text.read(ws))
  )

# the text t, after its length
def Adopt.part(+t: String) -> String:
  Nat.show(String.length(t)) ++ ":" ++ t

# the ID of the adoption of the line l after the step at of its store: it
# names both, so every owner asks for the same request
def Adopt.id(l: Maybe<&2, String>, at: Maybe<&2, Ledgers.Id>) -> String:
  match l at:
    case None{} Some{Ledgers.Id{w, q}}:
      "-" ++ Adopt.part(w) ++ q
    case Some{b} Some{Ledgers.Id{w, q}}:
      "+" ++ Adopt.part(b) ++ Adopt.part(w) ++ q
    case x y:
      ""

# the adoption of the line l of the store r, whose owner group is m: the
# request that makes the nodes inside the group now its owners, when they are
# not (none: they are, or the line has no owner group). No writer asks for it
def Adopt.of(
  +s: Replicas.Node<Requests.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, String>
) -> Maybe<&2, Replicas.Request<Requests.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{+g}:
      +os = Node.nodes(s, r, g)
      +at = Store.head(s, r)
      Shared.Maybe.when(
        Replicas.Request<Requests.Ask>,
        Bool.not(Ledgers.Owners.is_eq(os, Node.owners(s, r, l))),
        u => Some{
          Replicas.Request{
            Replicas.Envelope{Adopt.id(l, at), "", ""},
            Requests.Ask.On{r, l, Requests.Change.Own{g, at, os}}
          }
        }
      )

# the adoption of the line l of the store r, if its owners are not the nodes
# inside its owner group
def Node.adoption(
  +s: Replicas.Node<Requests.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>
) -> Maybe<&2, Replicas.Request<Requests.Ask>>:
  Adopt.of(s, r, l, Node.group(s, r, l))

def Spec.Ask.kernel():
  (+r => c => +i => q => Step.change(r, c, i, q), +s => +r => +l => Node.adoption(s, r, l))

# Reads
# -----
# Each read is of the node's own state: its ledger, and its heads.

# the newest version of the branch b of the store r, if b has one
def Node.head(s: Replicas.Node<Requests.Ask>, r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Replicas.Line.chain(r, Some{b}))

# the version m, when it is there, then rest
def Ids.put(m: Maybe<&2, Ledgers.Id>, rest: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match m:
    case Some{i}:
      i <> rest
    case None{}:
      rest

# the k versions of a line at the tip t from the number n, in order
def Line.versions(
  k: Nat,
  +s: Replicas.Node<Requests.Ask>,
  +t: Replicas.Tip,
  +n: U32
) -> List<&2, Ledgers.Id>:
  match k:
    case 0n:
      []
    case 1n+p:
      Ids.put(Version.in(s, n, t), Line.versions(p, s, t, U32.inc(n)))

# k versions of the line whose tip is m, from the number n, in order
def Versions.of(
  s: Replicas.Node<Requests.Ask>,
  m: Maybe<&2, Replicas.Tip>,
  n: U32,
  k: Nat
) -> List<&2, Ledgers.Id>:
  match m:
    case None{}:
      []
    case Some{t}:
      Line.versions(k, s, t, n)

def Spec.Node.versions(s, r, b, n, k):
  Versions.of(
    s,
    Replicas.Node.tip(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
    n,
    k
  )

# the version before the number n of the line whose tip is m, if any
def Version.before(
  s: Replicas.Node<Requests.Ask>,
  m: Maybe<&2, Replicas.Tip>,
  +n: U32
) -> Maybe<&2, Ledgers.Id>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Shared.Maybe.when(Ledgers.Id, Bool.not(U32.is_eq(n, 0)), u => Version.in(s, U32.sub(n, 1), t))

# the request i is a version: a step took it
def Node.is_version(s: Replicas.Node<Requests.Ask>, i: Ledgers.Id) -> Bool:
  Maybe.is_some(&2, Replicas.Version, Replicas.Node.made(~Requests.Ask.machine(), s, i))

# the version at the point p, if there is one
def Node.version(s: Replicas.Node<Requests.Ask>, p: Spec.Point) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Spec.Point.At{+v}:
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.is_version(s, v), u => Some{v}, u => None{})
    case Spec.Point.Head{r, b}:
      Node.head(s, r, b)
    case Spec.Point.Mark{r, b, m}:
      Replicas.Chain.mark(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b}), m)

# the root of the content of the resource n at the version m, if it holds it
def Res.root_at(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(
    &2,
    Ledgers.Id,
    Ropes.Root,
    m,
    v => Spec.Res.root(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{v}), n)
  )

# the bytes of the resource n at the version m, if it holds them
def Res.at(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Texts.Bytes()>:
  Replicas.Root.bytes(~Requests.Ask.machine(), s, Res.root_at(s, n, m))

# the bytes of the resource n at the point p, if it is there
def Node.content(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  p: Spec.Point
) -> Maybe<&2, Texts.Bytes()>:
  Res.at(s, n, Node.version(s, p))

def Spec.Node.members(s, r, g):
  Members.in(s, Store.root(s, r), g)

def Spec.Node.own(s, r, l, g):
  Requests.Ask.On{r, l, Requests.Change.Own{g, Store.head(s, r), Node.nodes(s, r, g)}}

# a pending write: when its writer asked for it (the time, then the request
# ID, as a key), and the content that it gives
type Draft is Data:
  Draft{key: List<&2, Bool>, content: Requests.Content}

# the key a comes before the key b, or is b
def Bits.before(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} y:
      True{}
    case Con{x, r} Nil{}:
      False{}
    case Con{False{}, r} Con{True{}, q}:
      True{}
    case Con{True{}, r} Con{False{}, q}:
      False{}
    case Con{False{}, r} Con{False{}, q}:
      Bits.before(r, q)
    case Con{True{}, r} Con{True{}, q}:
      Bits.before(r, q)

# the newer of the draft found, if any, and the draft d
def Draft.newer(found: Maybe<&2, Draft>, +d: Draft) -> Draft:
  match found d:
    case None{} x:
      x
    case Some{Draft{+k1, c1}} Draft{+k2, c2}:
      Shared.Bool.when(Draft, Bits.before(k1, k2), u => Draft{k2, c2}, u => Draft{k1, c1})

# the newer of found and the write of the content m at the key k, if any
def Draft.with(
  found: Maybe<&2, Draft>,
  k: List<&2, Bool>,
  m: Maybe<&2, Requests.Content>
) -> Maybe<&2, Draft>:
  match m:
    case None{}:
      found
    case Some{c}:
      Some{Draft.newer(found, Draft{k, c})}

# the newer of found and the request i, which the node holds as a, when the
# writer w asked for it and it writes the resource n on the branch b of the
# store r
def Draft.of(
  w: String,
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Requests.Ask>>,
  +found: Maybe<&2, Draft>
) -> Maybe<&2, Draft>:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      Shared.Bool.when(
        Maybe<&2, Draft>,
        String.eq(w2, w),
        u => Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Spec.Draft.content(r, b, n, q)
        ),
        u => found
      )
    case x y:
      found

# the newest write of the resource n on the branch b of the store r that the
# writer w asked for, among the requests qs, else found
def Draft.last(
  +s: Replicas.Node<Requests.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  found: Maybe<&2, Draft>
) -> Maybe<&2, Draft>:
  match qs:
    case Nil{}:
      found
    case Con{+i, rest}:
      Draft.last(
        s,
        w,
        r,
        b,
        n,
        rest,
        Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)
      )

# the content of the draft m, if any
def Draft.what(m: Maybe<&2, Draft>) -> Maybe<&2, Requests.Content>:
  match m:
    case None{}:
      None{}
    case Some{Draft{k, c}}:
      Some{c}

def Spec.Node.draft(s, w, r, b, n):
  Draft.what(
    Draft.last(
      s,
      w,
      r,
      b,
      n,
      Replicas.Wait.of(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      None{}
    )
  )

# the bytes of the draft m of the resource n, else what the point p holds
def Read.of(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Requests.Content>,
  p: Spec.Point
) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case Some{c}:
      Replicas.Root.bytes(~Requests.Ask.machine(), s, Spec.Content.root(s, n, c))
    case None{}:
      Node.content(s, n, p)

def Spec.Node.read(s, w, n, p):
  match p:
    case Spec.Point.Head{+r, +b}:
      Read.of(s, n, Spec.Node.draft(s, w, r, b, n), Spec.Point.Head{r, b})
    case x:
      Node.content(s, n, x)

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Requests.Ask>>,
  rest: List<&2, Spec.LogEntry>
) -> List<&2, Spec.LogEntry>:
  match held r:
    case True{} Some{Ledgers.Asked{t, q}}:
      Spec.LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: Replicas.Node<Requests.Ask>,
  +n: Resources.Name,
  xs: List<&2, Ledgers.Id>,
  prev: Maybe<&2, Ledgers.Id>
) -> List<&2, Spec.LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(Spec.Roots.same(Res.root_at(s, n, Some{x}), Res.root_at(s, n, prev))),
        x,
        Replicas.Node.asked(~Requests.Ask.machine(), s, x),
        Log.of(s, n, r, Some{x})
      )

def Spec.Node.log(s, n, r, b, from, k):
  Log.of(
    s,
    n,
    Spec.Node.versions(s, r, b, from, k),
    Version.before(
      s,
      Replicas.Node.tip(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      from
    )
  )

def Spec.Node.diff(s, w, n, a, b):
  Formats.Format.changes(
    Formats.Format.of(Resources.Name.path(n)),
    Maybe.default(&2, Texts.Bytes(), Spec.Node.read(s, w, n, a), []),
    Maybe.default(&2, Texts.Bytes(), Spec.Node.read(s, w, n, b), [])
  )

# the resource of a binding of a tree, when it is a clash that the merge of
# the version f opened
def Clash.binding(b: Trees.Binding, f: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  match b:
    case Trees.Binding{Con{3, k}, ws}:
      Shared.Maybe.when(
        Resources.Name,
        Shared.List.is_eq(~U32, ~U32.is_eq, ws, Spec.Clash.code(f)),
        u => Replicas.Read.whole(Resources.Name, Resources.Name.code.read(k))
      )
    case _:
      None{}

# the clashes that the merge of the version f opened, among the bindings bs
def Clash.of.bindings(bs: List<&2, Trees.Binding>, +f: Ledgers.Id) -> List<&2, Resources.Name>:
  match bs:
    case Nil{}:
      []
    case Con{b, r}:
      Names.put(Clash.binding(b, f), Clash.of.bindings(r, f))

# the resources whose clash the merge of the version f left open in the tree
# whose root is h
def Clash.names(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  f: Ledgers.Id
) -> List<&2, Resources.Name>:
  Clash.of.bindings(
    Trees.Tree.list(
      ~Replicas.Node<Requests.Ask>,
      ~Replicas.Store.fetch(~Requests.Ask.machine()),
      s,
      h
    ),
    f
  )

# the resources of ns whose clash, which the merge of the version f opened, is
# still open in the tree h
def Clash.left(
  +s: Replicas.Node<Requests.Ask>,
  ns: List<&2, Resources.Name>,
  +h: Maybe<&2, Hashes.Hash>,
  +f: Ledgers.Id
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(Resources.Name, n, Clash.left(s, r, h, f), Spec.Clash.open(s, h, n, f))

# the resources that clashed at the request k, whose request is a, when it is a
# merge
def Merge.clashes(
  +s: Replicas.Node<Requests.Ask>,
  k: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Requests.Ask>>
) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Requests.Ask.On{r, l, Requests.Change.Merge{f}}}}:
      Clash.names(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{k}), f)
    case _:
      []

# the resources that still clash after the merge k, whose request is a: those
# whose clash it opened, and that no resolve or newer merge settled since, at
# the head of its line
def Merge.left(
  +s: Replicas.Node<Requests.Ask>,
  k: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Requests.Ask>>
) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Requests.Ask.On{r, Some{l}, Requests.Change.Merge{+f}}}}:
      Clash.left(
        s,
        Clash.names(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{k}), f),
        Chain.root(s, Replicas.Line.chain(r, Some{l})),
        f
      )
    case _:
      []

# the resources that still clash after the merge k
def Node.conflict(+s: Replicas.Node<Requests.Ask>, +k: Ledgers.Id) -> List<&2, Resources.Name>:
  Merge.left(s, k, Replicas.Node.asked(~Requests.Ask.machine(), s, k))

# Written i, or Conflicted k while the merge k still clashes
def Answer.left(s: Replicas.Node<Requests.Ask>, i: Ledgers.Id, +k: Ledgers.Id) -> Spec.Answer:
  Shared.Bool.when(
    Spec.Answer,
    List.is_empty(&2, Resources.Name, Node.conflict(s, k)),
    u => Spec.Answer.Written{i},
    u => Spec.Answer.Conflicted{k}
  )

# the answer to the change q of the request i, which a step took
def Answer.taken(s: Replicas.Node<Requests.Ask>, +i: Ledgers.Id, q: Requests.Ask) -> Spec.Answer:
  match q:
    case Requests.Ask.On{st, l, Requests.Change.Merge{f}}:
      Answer.left(s, i, i)
    case Requests.Ask.On{st, l, Requests.Change.Resolve{k, n, c}}:
      Answer.left(s, i, k)
    case _:
      Spec.Answer.Written{i}

# the answer to the request i of the change q, whose outcome is o: Pending
# while no step that the node knows decided it
def Answer.of(
  s: Replicas.Node<Requests.Ask>,
  i: Ledgers.Id,
  q: Requests.Ask,
  o: Maybe<&2, Replicas.Out>
) -> Spec.Answer:
  match o:
    case Some{Replicas.Out.Taken{n}}:
      Answer.taken(s, i, q)
    case Some{Replicas.Out.Stale{}}:
      Spec.Answer.Stale{}
    case None{}:
      Spec.Answer.Pending{}

# the answer to the request i that the node holds as the change q: a store
# that starts is Written at once
def Answer.asked(+s: Replicas.Node<Requests.Ask>, +i: Ledgers.Id, q: Requests.Ask) -> Spec.Answer:
  match q:
    case Requests.Ask.Start{os}:
      Spec.Answer.Written{i}
    case x:
      Answer.of(s, i, x, Replicas.Node.out(~Requests.Ask.machine(), s, i))

# the answer to the change q of the request i, whose slot holds m: none when it
# is empty, Refused when it holds another change
def Answer.held(
  s: Replicas.Node<Requests.Ask>,
  i: Ledgers.Id,
  q: Requests.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Requests.Ask>>>
) -> Maybe<&2, Spec.Answer>:
  match m:
    case None{}:
      None{}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Some{
        Shared.Bool.when(
          Spec.Answer,
          Requests.Ask.is_eq(q2, q),
          u => Answer.asked(s, i, q2),
          u => Spec.Answer.Refused{}
        )
      }
    case Some{c}:
      Some{Spec.Answer.Refused{}}

def Spec.Node.answer(s, e, q):
  +i = Replicas.Envelope.of(e)
  Answer.held(
    s,
    i,
    q,
    Ledgers.State.get(
      ~Requests.Ask,
      Replicas.State.ledger(~Requests.Ask.machine(), s),
      Ledgers.Slot.ask(i)
    )
  )

# Listings
# --------

# the branch b of the store r, with the owners os, at its newest version m,
# then rest
def Branch.put(
  r: Ledgers.Id,
  b: String,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Id>,
  rest: List<&2, Spec.BranchEntry>
) -> List<&2, Spec.BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{v}:
      Spec.BranchEntry{Spec.Branch{r, b}, os, v} <> rest

# the branch of the head h, when it is one that has a version, then rest
def Branch.at(
  +s: Replicas.Node<Requests.Ask>,
  h: Replicas.Head,
  rest: List<&2, Spec.BranchEntry>
) -> List<&2, Spec.BranchEntry>:
  match h:
    case Replicas.Head{+r, Some{+b}, n, t}:
      Branch.put(r, b, Node.owners(s, r, Some{b}), Node.head(s, r, b), rest)
    case x:
      rest

# the branches of the heads hs
def Branch.all(
  +s: Replicas.Node<Requests.Ask>,
  hs: List<&2, Replicas.Head>
) -> List<&2, Spec.BranchEntry>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      Branch.at(s, h, Branch.all(s, rest))

# every branch that the node follows
def Node.branches(+s: Replicas.Node<Requests.Ask>) -> List<&2, Spec.BranchEntry>:
  Branch.all(s, Tries.Trie.values(Replicas.Head, Replicas.State.heads(~Requests.Ask.machine(), s)))

# the branches es
def Branch.names(es: List<&2, Spec.BranchEntry>) -> List<&2, Spec.Branch>:
  match es:
    case Nil{}:
      []
    case Con{Spec.BranchEntry{b, os, h}, r}:
      b <> Branch.names(r)

# the head of the branch b, if b exists
def Branch.head(s: Replicas.Node<Requests.Ask>, b: Spec.Branch) -> Maybe<&2, Ledgers.Id>:
  match b:
    case Spec.Branch{r, n}:
      Node.head(s, r, n)

def Spec.Node.resources(s, b):
  Res.names(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Branch.head(s, b)))

# the bytes m, as a list of one item or none
def Uses.items(m: Maybe<&2, Texts.Bytes()>) -> List<&2, Texts.Bytes()>:
  match m:
    case None{}:
      []
    case Some{b}:
      [b]

# the resources that the edges es of the resource n name
def Uses.named(es: List<&2, Formats.Edge>, +n: Resources.Name) -> List<&2, Resources.Name>:
  match es:
    case Nil{}:
      []
    case Con{Formats.Edge{t, a, cs}, r}:
      Resources.Name.at(n, Texts.Bytes.to_text(t)) <> Uses.named(r, n)

# what the resource n imports at the version h of s, as its format reads it
def Uses.targets(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Ledgers.Id>,
  +n: Resources.Name
) -> List<&2, Resources.Name>:
  Uses.named(
    Formats.Format.uses(Formats.Format.of(Resources.Name.path(n)), Uses.items(Res.at(s, n, h))),
    n
  )

# the keys of the resources ns
def Name.keys(ns: List<&2, Resources.Name>) -> List<&2, List<&2, Bool>>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Name.key(n) <> Name.keys(r)

# the graph of the resources all: t and gr, with what each resource of ns
# imports at the version h of s, and with it as a user of each
def Uses.read(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Ledgers.Id>,
  ns: List<&2, Resources.Name>,
  all: List<&2, Resources.Name>,
  t: Tries.Trie<List<&2, Resources.Name>>,
  gr: Reaches.Graph
) -> Spec.Uses:
  match ns:
    case Nil{}:
      Spec.Uses{t, all, gr}
    case Con{+n, r}:
      +ts = Uses.targets(s, h, n)
      Uses.read(
        s,
        h,
        r,
        all,
        Tries.Trie.set(List<&2, Resources.Name>, t, Name.key(n), ts),
        Reaches.Graph.back(Name.keys(ts), Name.key(n), gr)
      )

# the graph of the imports of the branch b, at its head
def Uses.of(+s: Replicas.Node<Requests.Ask>, b: Spec.Branch) -> Spec.Uses:
  +h = Branch.head(s, b)
  +ns = Res.names(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, h))
  Uses.read(s, h, ns, ns, Tries.Trie.new(List<&2, Resources.Name>), Reaches.Graph.new())

# what the resources of g import
def Uses.imports(g: Spec.Uses) -> Tries.Trie<List<&2, Resources.Name>>:
  match g:
    case Spec.Uses{t, ns, gr}:
      t

# the resources of g
def Uses.nodes(g: Spec.Uses) -> List<&2, Resources.Name>:
  match g:
    case Spec.Uses{t, ns, gr}:
      ns

# who imports each resource of g
def Uses.users(g: Spec.Uses) -> Reaches.Graph:
  match g:
    case Spec.Uses{t, ns, gr}:
      gr

# the resource that the request r wrote: of a write or a resolve
def Wrote.of(r: Maybe<&2, Ledgers.Asked<Requests.Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, Requests.Ask.On{st, l, Requests.Change.Write{m, base, c}}}}:
      Some{m}
    case Some{Ledgers.Asked{t, Requests.Ask.On{st, l, Requests.Change.Resolve{k, m, c}}}}:
      Some{m}
    case _:
      None{}

# the resource that the version v wrote, when it is a write or a resolve
def Node.wrote(s: Replicas.Node<Requests.Ask>, v: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  Wrote.of(Replicas.Node.asked(~Requests.Ask.machine(), s, v))

# how many numbers are from a up to b, b not counted
def Count.span(+a: U32, +b: U32) -> Nat:
  Shared.Bool.when(Nat, U32.is_lt(a, b), u => U32.to_nat(U32.sub(b, a)), u => 0n)

# the versions of the line whose tip is m from the number n on, in order: the
# cost is theirs, not that of the line's history
def Line.since(
  s: Replicas.Node<Requests.Ask>,
  m: Maybe<&2, Replicas.Tip>,
  +n: U32
) -> List<&2, Ledgers.Id>:
  match m:
    case None{}:
      []
    case Some{+t}:
      Line.versions(Count.span(n, Replicas.Tip.count(t)), s, t, n)

# the number after the place m of a version vector, 0 without one
def Place.after(m: Maybe<&2, Replicas.Place>) -> U32:
  match m:
    case None{}:
      0
    case Some{Replicas.Place{c, n}}:
      U32.inc(n)

# a and b are the same branch
def Branch.same(a: Spec.Branch, b: Spec.Branch) -> Bool:
  match a b:
    case Spec.Branch{r1, n1} Spec.Branch{r2, n2}:
      List.all.if(u => String.eq(n1, n2), Ledgers.Id.is_eq(r1, r2))

# the versions of the branch x that the tree h did not take in: those after
# the place that its version vector holds for x
def Branch.news(
  +s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  x: Spec.Branch
) -> List<&2, Ledgers.Id>:
  match x:
    case Spec.Branch{r, n}:
      +c = Replicas.Line.chain(r, Some{n})
      Line.since(
        s,
        Replicas.Node.tip(~Requests.Ask.machine(), s, c),
        Place.after(Node.vector(s, h, c))
      )

# the versions of the branches es, other than b, that the tree h did not take
# in
def Lacked.of(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +b: Spec.Branch,
  es: List<&2, Spec.Branch>
) -> List<&2, Ledgers.Id>:
  match es:
    case Nil{}:
      []
    case Con{+x, r}:
      List.append(
        &2,
        Ledgers.Id,
        Shared.Bool.when(
          List<&2, Ledgers.Id>,
          Branch.same(x, b),
          u => [],
          u => Branch.news(s, h, x)
        ),
        Lacked.of(s, h, b, r)
      )

# the versions of the other branches that the branch b did not take in: what
# its version vector does not cover
def Branch.lacked(+s: Replicas.Node<Requests.Ask>, +b: Spec.Branch) -> List<&2, Ledgers.Id>:
  Lacked.of(
    s,
    Replicas.Node.root_of(~Requests.Ask.machine(), s, Branch.head(s, b)),
    b,
    Branch.names(Node.branches(s))
  )

# the branch b lacks the version v
def Touch.lacks(+s: Replicas.Node<Requests.Ask>, +b: Spec.Branch, +v: Ledgers.Id) -> Bool:
  List.all.if(
    u => Bool.not(Node.has(s, Maybe.default(&2, Ledgers.Id, Branch.head(s, b), v), v)),
    Maybe.is_some(&2, Ledgers.Id, Branch.head(s, b))
  )

# the key of the branch b
def Branch.key(b: Spec.Branch) -> List<&2, Bool>:
  match b:
    case Spec.Branch{r, n}:
      List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# used, with the resources that use the resource m, if any, at any depth: one
# search, once for each resource
def Used.put(
  us: Spec.Uses,
  m: Maybe<&2, Resources.Name>,
  +used: Tries.Trie<Tries.Trie<Unit>>
) -> Tries.Trie<Tries.Trie<Unit>>:
  match m:
    case None{}:
      used
    case Some{+c}:
      Shared.Bool.when(
        Tries.Trie<Tries.Trie<Unit>>,
        Tries.Trie.has(Tries.Trie<Unit>, used, Name.key(c)),
        w => used,
        w => Tries.Trie.set(
          Tries.Trie<Unit>,
          used,
          Name.key(c),
          Reaches.Graph.reach(Uses.users(us), Name.key(c))
        )
      )

# used, with the users of each resource that a version of vs wrote
def Used.of(
  +s: Replicas.Node<Requests.Ask>,
  +us: Spec.Uses,
  vs: List<&2, Ledgers.Id>,
  used: Tries.Trie<Tries.Trie<Unit>>
) -> Tries.Trie<Tries.Trie<Unit>>:
  match vs:
    case Nil{}:
      used
    case Con{v, r}:
      Used.of(s, us, r, Used.put(us, Node.wrote(s, v), used))

# the resource u uses the resource c, by used
def Used.has(used: Tries.Trie<Tries.Trie<Unit>>, c: Resources.Name, u: Resources.Name) -> Bool:
  Maybe.default(
    &2,
    Bool,
    Maybe.bind(
      &2,
      Tries.Trie<Unit>,
      Bool,
      Tries.Trie.get(Tries.Trie<Unit>, used, Name.key(c)),
      r => Some{Tries.Trie.has(Unit, r, Name.key(u))}
    ),
    False{}
  )

def Spec.Seen.of(s, b):
  +us = Uses.of(s, b)
  +ls = Branch.lacked(s, b)
  Spec.Seen{s, b, us, ls, Used.of(s, us, ls, Tries.Trie.new(Tries.Trie<Unit>))}

def Spec.Touch.holds(g, t):
  match g t:
    case Spec.Seen{+s, gb, us, ls, used} Spec.Touch{+v, +c, b, +u}:
      List.all.if(
        w => List.all.if(
          w => List.all.if(
            w => List.all.if(
              w => List.any.if(w => Used.has(used, c, u), Resources.Name.is_eq(u, c)),
              Tries.Trie.has(List<&2, Resources.Name>, Uses.imports(us), Name.key(u))
            ),
            Shared.Maybe.is_eq(~Resources.Name, ~Resources.Name.is_eq, Node.wrote(s, v), Some{c})
          ),
          Touch.lacks(s, b, v)
        ),
        Node.is_version(s, v)
      )

def Spec.Node.touches(s, t):
  match t:
    case Spec.Touch{v, c, +b, u}:
      Spec.Touch.holds(Spec.Seen.of(s, b), Spec.Touch{v, c, b, u})

# the touches of the version v that wrote c, on the branch b, one for each of
# its resources us
def Touch.each(
  us: List<&2, Resources.Name>,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Spec.Branch
) -> List<&2, Spec.Touch>:
  match us:
    case Nil{}:
      []
    case Con{u, r}:
      Spec.Touch{v, c, b, u} <> Touch.each(r, v, c, b)

# the touches of the version v that wrote the resource m (if any), on the
# branch b, one for each of its resources us
def Touch.of(
  m: Maybe<&2, Resources.Name>,
  v: Ledgers.Id,
  b: Spec.Branch,
  us: List<&2, Resources.Name>
) -> List<&2, Spec.Touch>:
  match m:
    case None{}:
      []
    case Some{c}:
      Touch.each(us, v, c, b)

# the touches of the version v on the branch of g
def Affects.at(g: Spec.Seen, v: Ledgers.Id) -> List<&2, Spec.Touch>:
  match g:
    case Spec.Seen{s, b, us, ls, used}:
      +v = v
      Touch.of(Node.wrote(s, v), v, b, Uses.nodes(us))

# the versions of other branches that the branch of g lacks
def Seen.lacked(g: Spec.Seen) -> List<&2, Ledgers.Id>:
  match g:
    case Spec.Seen{s, b, us, ls, used}:
      ls

# the touches that may hold of the branch of g: those of the versions of the
# other branches that it did not take in
def Affects.cands(+g: Spec.Seen) -> List<&2, Spec.Touch>:
  Shared.List.flat(~Ledgers.Id, ~Spec.Touch, ~Spec.Seen, ~Affects.at, Seen.lacked(g), g)

def Spec.Node.affects(s, b):
  +g = Spec.Seen.of(s, b)
  Shared.List.keep(~Spec.Touch, ~Spec.Seen, ~Spec.Touch.holds, Affects.cands(g), g)

# the checks of one branch, and the version of a point
type Impact is Data:
  Impact{seen: Spec.Seen, version: Maybe<&2, Ledgers.Id>}

# the touch t is of the version of g, or of a version that it came from, and
# holds
def Impact.keeps(g: Impact, t: Spec.Touch) -> Bool:
  match g t:
    case Impact{Spec.Seen{+s, gb, us, ls, used}, +m} Spec.Touch{+v, c, b, u}:
      List.all.if(
        w => Spec.Touch.holds(Spec.Seen{s, gb, us, ls, used}, Spec.Touch{v, c, b, u}),
        List.all.if(
          w => Node.has(s, Maybe.default(&2, Ledgers.Id, m, v), v),
          Maybe.is_some(&2, Ledgers.Id, m)
        )
      )

# what the changes up to the version m touch on the branches es
def Impact.of(
  +s: Replicas.Node<Requests.Ask>,
  +m: Maybe<&2, Ledgers.Id>,
  es: List<&2, Spec.Branch>
) -> List<&2, Spec.Touch>:
  match es:
    case Nil{}:
      []
    case Con{b, r}:
      +g = Spec.Seen.of(s, b)
      List.append(
        &2,
        Spec.Touch,
        Shared.List.keep(~Spec.Touch, ~Impact, ~Impact.keeps, Affects.cands(g), Impact{g, m}),
        Impact.of(s, m, r)
      )

def Spec.Node.impact(s, p):
  Impact.of(s, Node.version(s, p), Branch.names(Node.branches(s)))

# the key of the notice n: its kind, then its parts
def Notice.key(n: Spec.Notice) -> List<&2, Bool>:
  match n:
    case Spec.Notice.Versioned{b, v}:
      False{} <> False{} <> List.append(&2, Bool, Branch.key(b), Ledgers.Id.key(v))
    case Spec.Notice.Conflicted{b, v}:
      False{} <> True{} <> List.append(&2, Bool, Branch.key(b), Ledgers.Id.key(v))
    case Spec.Notice.Touched{Spec.Touch{v, c, b, u}}:
      True{}
        <> List.append(
          &2,
          Bool,
          Ledgers.Id.key(v),
          List.append(&2, Bool, Name.key(c), List.append(&2, Bool, Branch.key(b), Name.key(u)))
        )

# the versions xs of the branch b, as notices
def Notice.versions(+b: Spec.Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Spec.Notice.Versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(
  +s: Replicas.Node<Requests.Ask>,
  +b: Spec.Branch,
  xs: List<&2, Ledgers.Id>
) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Spec.Notice,
        Spec.Notice.Conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(
          List.is_empty(
            &2,
            Resources.Name,
            Merge.clashes(s, x, Replicas.Node.asked(~Requests.Ask.machine(), s, x))
          )
        )
      )

# the touches ts, as notices
def Notice.touches(ts: List<&2, Spec.Touch>) -> List<&2, Spec.Notice>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Spec.Notice.Touched{t} <> Notice.touches(r)

# the notices of ns whose keys old does not hold
def Notice.new(ns: List<&2, Spec.Notice>, +old: Tries.Trie<Unit>) -> List<&2, Spec.Notice>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Spec.Notice,
        n,
        Notice.new(r, old),
        Bool.not(Tries.Trie.has(Unit, old, Notice.key(n)))
      )

# the number of versions of the line c in s
def Chain.count(s: Replicas.Node<Requests.Ask>, c: Ledgers.Chain) -> U32:
  Maybe.default(
    &2,
    U32,
    Maybe.bind(
      &2,
      Replicas.Tip,
      U32,
      Replicas.Node.tip(~Requests.Ask.machine(), s, c),
      t => Some{Replicas.Tip.count(t)}
    ),
    0
  )

# the versions of the branch b that s has and since has not: those from the
# number of versions of b in since on
def Branch.since(
  +s: Replicas.Node<Requests.Ask>,
  since: Replicas.Node<Requests.Ask>,
  b: Spec.Branch
) -> List<&2, Ledgers.Id>:
  match b:
    case Spec.Branch{r, n}:
      +c = Replicas.Line.chain(r, Some{n})
      Line.since(s, Replicas.Node.tip(~Requests.Ask.machine(), s, c), Chain.count(since, c))

def Spec.Node.notices(s, t, since):
  match t:
    case Spec.Topic.Versions{+b}:
      Notice.versions(b, Branch.since(s, since, b))
    case Spec.Topic.Conflicts{+b}:
      Notice.conflicts(s, b, Branch.since(s, since, b))
    case Spec.Topic.Affects{+b}:
      Notice.new(
        Notice.touches(Spec.Node.affects(s, b)),
        Tries.Trie.put_keys(
          ~Spec.Notice,
          ~Notice.key,
          Notice.touches(Spec.Node.affects(since, b)),
          Tries.Trie.new(Unit)
        )
      )

def Spec.Vend.may_stop(v, force):
  match v:
    case Spec.Vend{n, s, ws, ms}:
      List.any.if(
        u => List.all.if(w => List.is_empty(&2, Spec.Mount, ms), List.is_empty(&2, String, ws)),
        force
      )

# The proofs of the core's laws.
# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in a proof a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- in a proof an unused binder is a premise of the proof's own type; a proof does not run
def Spec.Ask.same():
  Requests.Ask.laws()

# Owners
# ------

# owners that fit the nodes ns are ns
def Fits.same(
  +os: List<&2, String>,
  +ns: List<&2, String>
) -> {Own.fits(os, ns) == True{}: Bool} -> {os == ns: List<&2, String>}:
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
  Shared.Maybe.when(Bool, b, u => Some{Own.fits(os, ns)}) == Some{True{}}: Maybe<&2, Bool>
} -> {os == ns: List<&2, String>}:
  match b:
    case False{}:
      e => Empty.absurd({os == ns: List<&2, String>}, Shared.Maybe.none_ne_some(Bool, True{}, e))
    case True{}:
      e => Fits.same(os, ns)(Shared.Maybe.some_inj(Bool, Own.fits(os, ns), True{}, e))

# Own.takes_inside once whether the Own may name its version is known (m)
def Takes.at(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  g: String,
  os: List<&2, String>,
  m: Maybe<&2, Bool>
) -> {
  Maybe.bind(&2, Bool, Bool, m, k => Own.takes.at(s, h, g, os, k)) == Some{True{}}: Maybe<&2, Bool>
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
      Takes.held(os, Spec.Group.nodes(s, h, g), Groups.held(s, h))

def Spec.Own.takes_inside(s, r, l, g, at, os, h):
  Takes.at(s, Spec.Own.tree(s, l, at, h), g, os, Own.ok(s, r, l, at))

# Growth
# ------
# A node's ledger only grows: each operation keeps every entry that it held.

# a place added to a version vector only grows a node
def Grown.vector.add(
  w: Replicas.Work<Requests.Ask>,
  +c: Ledgers.Chain,
  +p: Replicas.Place
) -> {
  Replicas.Work.after(
    ~Requests.Ask.machine(),
    Replicas.Work.state(~Requests.Ask.machine(), w),
    Vector.add(w, c, p)
  )
    == True{}: Bool
}:
  match w:
    case Replicas.Work{+s, +h}:
      Replicas.Grown.when(
        ~Requests.Ask.machine(),
        s,
        Replicas.Place.covered(Node.vector(s, h, c), p),
        Some{Replicas.Work{s, h}},
        Replicas.Work.set(
          ~Requests.Ask.machine(),
          Replicas.Work{s, h},
          Key.vector(c),
          Replicas.Place.code(p)
        ),
        Replicas.Grows.refl(~Requests.Ask.machine(), s),
        Replicas.Set.grows(~Requests.Ask.machine(), s, h, Key.vector(c), Replicas.Place.code(p))
      )

# an entry added to a version vector only grows a node
def Grown.vector.add.if(
  +w: Replicas.Work<Requests.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Place>
) -> {
  Replicas.Work.after(
    ~Requests.Ask.machine(),
    Replicas.Work.state(~Requests.Ask.machine(), w),
    Vector.add.if(w, c, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      Replicas.Grown.self(~Requests.Ask.machine(), w)
    case Some{+p}:
      Replicas.Grown.when(
        ~Requests.Ask.machine(),
        Replicas.Work.state(~Requests.Ask.machine(), w),
        Ledgers.Chain.is_eq(Replicas.Place.chain(p), c),
        Some{w},
        Vector.add(w, Replicas.Place.chain(p), p),
        Replicas.Grown.self(~Requests.Ask.machine(), w),
        Grown.vector.add(w, Replicas.Place.chain(p), p)
      )

# the entries added to a version vector only grow a node
def Grown.vector.adds(
  +s: Replicas.Node<Requests.Ask>,
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Requests.Ask.machine(), s, Vector.adds(bs, c, m)) == True{}: Bool}:
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
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Vector.add.if(w, c, Vector.entry(b))
        )
      )(
        Replicas.Grown.bind(
          ~Requests.Ask.machine(),
          s,
          m,
          w => Vector.add.if(w, c, Vector.entry(b)),
          e,
          +w => Grown.vector.add.if(w, c, Vector.entry(b))
        )
      )

# a version joined to a version vector only grows a node
def Grown.vector.joined(
  +s: Replicas.Node<Requests.Ask>,
  +s0: Replicas.Node<Requests.Ask>,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, m) == True{}: Bool
} -> {Replicas.Work.after(~Requests.Ask.machine(), s, Vector.joined(s0, c, v, m)) == True{}: Bool}:
  e => Replicas.Grown.bind(
    ~Requests.Ask.machine(),
    s,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s0,
        Replicas.Node.root_of(~Requests.Ask.machine(), s0, Some{v})
      ),
      c,
      m
    ),
    w => Vector.add.if(w, c, Replicas.Node.place(~Requests.Ask.machine(), s0, v)),
    Grown.vector.adds(
      s,
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s0,
        Replicas.Node.root_of(~Requests.Ask.machine(), s0, Some{v})
      ),
      c,
      m
    )(e),
    +w => Grown.vector.add.if(w, c, Replicas.Node.place(~Requests.Ask.machine(), s0, v))
  )

# what a merge keeps of a resource only grows a node
def Grown.merge.put(
  +f: Ledgers.Id,
  +n: Resources.Name,
  +o: Maybe<&2, Ropes.Root>,
  p: Spec.Pick,
  +w: Replicas.Work<Requests.Ask>
) -> {
  Replicas.Work.after(
    ~Requests.Ask.machine(),
    Replicas.Work.state(~Requests.Ask.machine(), w),
    Merge.put(f, n, o, p, w)
  )
    == True{}: Bool
}:
  match p:
    case Spec.Pick.Take{m}:
      Replicas.Grown.set(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(m))
    case Spec.Pick.Make{+x}:
      Replicas.Grown.bind(
        ~Requests.Ask.machine(),
        Replicas.Work.state(~Requests.Ask.machine(), w),
        Replicas.Work.keep(~Requests.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(x))),
        w2 => Replicas.Work.set(
          ~Requests.Ask.machine(),
          w2,
          Spec.Key.res(n),
          Spec.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(x))})
        ),
        Replicas.Grown.keep(~Requests.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(x))),
        w2 => Replicas.Grown.set(
          ~Requests.Ask.machine(),
          w2,
          Spec.Key.res(n),
          Spec.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(x))})
        )
      )
    case Spec.Pick.Clash{}:
      Replicas.Grown.bind(
        ~Requests.Ask.machine(),
        Replicas.Work.state(~Requests.Ask.machine(), w),
        Replicas.Work.set(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(o)),
        y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), Spec.Clash.code(f)),
        Replicas.Grown.set(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(o)),
        y => Replicas.Grown.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), Spec.Clash.code(f))
      )

# a resource merged only grows a node
def Grown.merge.one(
  s0: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  +w: Replicas.Work<Requests.Ask>
) -> {
  Replicas.Work.after(
    ~Requests.Ask.machine(),
    Replicas.Work.state(~Requests.Ask.machine(), w),
    Merge.one(s0, f, n, b, o, t, w)
  )
    == True{}: Bool
}:
  Replicas.Grown.with(
    ~Requests.Ask.machine(),
    Spec.Pick,
    Replicas.Work.state(~Requests.Ask.machine(), w),
    Spec.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s0, b, o, t),
    p => Merge.put(f, n, o, p, w),
    p => Grown.merge.put(f, n, o, p, w)
  )

# the resources merged only grow a node
def Grown.merge.all(
  +s: Replicas.Node<Requests.Ask>,
  +s0: Replicas.Node<Requests.Ask>,
  +f: Ledgers.Id,
  ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, m) == True{}: Bool
} -> {
  Replicas.Work.after(
    ~Requests.Ask.machine(),
    s,
    Merge.all(s0, f, ns, hb, ho, ht, m)
  )
    == True{}: Bool
}:
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
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Work<Requests.Ask>,
            Spec.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Requests.Ask>,
              Spec.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Requests.Ask>,
                Spec.Res.find(s0, ht, n),
                x => Merge.one(s0, f, n, b, o, x, w)
              )
            )
          )
        )
      )(
        Replicas.Grown.bind(
          ~Requests.Ask.machine(),
          s,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Work<Requests.Ask>,
            Spec.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Requests.Ask>,
              Spec.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Requests.Ask>,
                Spec.Res.find(s0, ht, n),
                x => Merge.one(s0, f, n, b, o, x, w)
              )
            )
          ),
          e,
          +w => Replicas.Grown.with(
            ~Requests.Ask.machine(),
            Maybe<&2, Ropes.Root>,
            Replicas.Work.state(~Requests.Ask.machine(), w),
            Spec.Res.find(s0, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Work<Requests.Ask>,
              Spec.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Requests.Ask>,
                Spec.Res.find(s0, ht, n),
                x => Merge.one(s0, f, n, b, o, x, w)
              )
            ),
            +b => Replicas.Grown.with(
              ~Requests.Ask.machine(),
              Maybe<&2, Ropes.Root>,
              Replicas.Work.state(~Requests.Ask.machine(), w),
              Spec.Res.find(s0, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Work<Requests.Ask>,
                Spec.Res.find(s0, ht, n),
                x => Merge.one(s0, f, n, b, o, x, w)
              ),
              +o => Replicas.Grown.with(
                ~Requests.Ask.machine(),
                Maybe<&2, Ropes.Root>,
                Replicas.Work.state(~Requests.Ask.machine(), w),
                Spec.Res.find(s0, ht, n),
                x => Merge.one(s0, f, n, b, o, x, w),
                x => Grown.merge.one(s0, f, n, b, o, x, w)
              )
            )
          )
        )
      )

# the trees of a merge are on a node that grew
def Grown.merge.work(
  +s: Replicas.Node<Requests.Ask>,
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, Spec.Merge.work(s, c, from, h)) == True{}: Bool
}:
  Grown.vector.joined(
    s,
    s,
    c,
    from,
    Merge.all(
      s,
      from,
      Spec.Merge.names(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Spec.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    )
  )(
    Grown.merge.all(
      s,
      s,
      from,
      Spec.Merge.names(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Spec.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    )(Replicas.Grows.refl(~Requests.Ask.machine(), s))
  )

# the trees of a move are on a node that grew
def Grown.move.work(
  +s: Replicas.Node<Requests.Ask>,
  +c: Ledgers.Chain,
  +to: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> {Replicas.Work.after(~Requests.Ask.machine(), s, Spec.Move.work(s, c, to, h)) == True{}: Bool}:
  Grown.vector.joined(
    s,
    s,
    c,
    to,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h
      ),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})}}
    )
  )(
    Grown.vector.adds(
      s,
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h
      ),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})}}
    )(Replicas.Grows.refl(~Requests.Ask.machine(), s))
  )

# the trees of a resolve are on a node that grew
def Grown.resolve.work(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  +m: Maybe<&2, Ropes.Root>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, Spec.Resolve.work(s, h, n, m)) == True{}: Bool
}:
  Replicas.Grown.bind(
    ~Requests.Ask.machine(),
    s,
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Spec.Key.res(n),
      Spec.Res.code(m)
    ),
    y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), []),
    Replicas.Set.grows(~Requests.Ask.machine(), s, h, Spec.Key.res(n), Spec.Res.code(m)),
    y => Replicas.Grown.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), [])
  )

# the trees of a group are on a node that grew
def Grown.group.work(
  +s: Replicas.Node<Requests.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  +ms: List<&2, Requests.Member>
) -> {Replicas.Work.after(~Requests.Ask.machine(), s, Group.work(s, h, g, ms)) == True{}: Bool}:
  Replicas.Grown.bind(
    ~Requests.Ask.machine(),
    s,
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Key.group(g),
      Requests.Members.code(ms, [])
    ),
    +w => Shared.Bool.when(
      Maybe<&2, Replicas.Work<Requests.Ask>>,
      List.contains(~String, ~String.eq, Group.names(s, h), g),
      u => Some{w},
      u => Replicas.Work.set(
        ~Requests.Ask.machine(),
        w,
        Key.groups(),
        Ledgers.Owners.code(g <> Group.names(s, h), [])
      )
    ),
    Replicas.Set.grows(~Requests.Ask.machine(), s, h, Key.group(g), Requests.Members.code(ms, [])),
    +w => Replicas.Grown.when(
      ~Requests.Ask.machine(),
      Replicas.Work.state(~Requests.Ask.machine(), w),
      List.contains(~String, ~String.eq, Group.names(s, h), g),
      Some{w},
      Replicas.Work.set(
        ~Requests.Ask.machine(),
        w,
        Key.groups(),
        Ledgers.Owners.code(g <> Group.names(s, h), [])
      ),
      Replicas.Grown.self(~Requests.Ask.machine(), w),
      Replicas.Grown.set(
        ~Requests.Ask.machine(),
        w,
        Key.groups(),
        Ledgers.Owners.code(g <> Group.names(s, h), [])
      )
    )
  )

# the first tree of a branch is on a node that grew
def Grown.make.branch(
  +s: Replicas.Node<Requests.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Ledgers.Id>
) -> {Replicas.Work.after(~Requests.Ask.machine(), s, Make.branch(s, c, m)) == True{}: Bool}:
  match m:
    case None{}:
      Replicas.Grows.refl(~Requests.Ask.machine(), s)
    case Some{+v}:
      Grown.vector.joined(
        s,
        s,
        c,
        v,
        Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{v})}}
      )(Replicas.Grows.refl(~Requests.Ask.machine(), s))

# the first tip of a new branch is on a node that grew
def Grown.make.first(
  +s: Replicas.Node<Requests.Ask>,
  start: Maybe<&2, Replicas.Work<Requests.Ask>>,
  os: List<&2, String>
) -> {
  Replicas.Work.after(~Requests.Ask.machine(), s, start) == True{}: Bool
} -> {Replicas.Made.after(~Requests.Ask.machine(), s, Make.first(start, os)) == True{}: Bool}:
  match start:
    case None{}:
      e => {==}
    case Some{Replicas.Work{+s2, +h}}:
      e =>
        +t = {Replicas.Tip{h, None{}, 0, os}: Replicas.Tip}
        Replicas.Grown.made.put(
          ~Requests.Ask.machine(),
          s,
          t,
          Replicas.Work.keep(~Requests.Ask.machine(), Replicas.Work{s2, h}, [Replicas.Tip.words(t)])
        )(
          Replicas.Work.after.trans(
            ~Requests.Ask.machine(),
            s,
            s2,
            Replicas.Work.keep(
              ~Requests.Ask.machine(),
              Replicas.Work{s2, h},
              [Replicas.Tip.words(t)]
            ),
            e,
            Replicas.Grown.keep(
              ~Requests.Ask.machine(),
              Replicas.Work{s2, h},
              [Replicas.Tip.words(t)]
            )
          )
        )

# a verdict after a verdict holds a node that grew
def Verdict.then(
  s: Replicas.Node<Requests.Ask>,
  +m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>,
  hk: {Replicas.Verdict.after(~Requests.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Requests.Ask.machine(), s, Judge.then(m, k)) == True{}: Bool}:
  match m:
    case Some{True{}}:
      hk
    case Some{False{}}:
      {==}
    case None{}:
      {==}

# a verdict under a condition holds a node that grew
def Verdict.when(
  s: Replicas.Node<Requests.Ask>,
  +b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>,
  hk: {Replicas.Verdict.after(~Requests.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Requests.Ask.machine(), s, Judge.when(b, k)) == True{}: Bool}:
  match b:
    case True{}:
      hk
    case False{}:
      {==}

# a verdict on whole trees holds a node that grew
def Verdict.whole(
  s: Replicas.Node<Requests.Ask>,
  +b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>,
  hk: {Replicas.Verdict.after(~Requests.Ask.machine(), s, k(Unit{})) == True{}: Bool}
) -> {Replicas.Verdict.after(~Requests.Ask.machine(), s, Judge.whole(b, k)) == True{}: Bool}:
  match b:
    case True{}:
      hk
    case False{}:
      {==}

# the verdict on a write holds a node that grew
def Verdict.write(
  +s: Replicas.Node<Requests.Ask>,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Requests.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> {
  Replicas.Verdict.after(
    ~Requests.Ask.machine(),
    s,
    Spec.Judge.write(s, n, base, c, h)
  )
    == True{}: Bool
}:
  Verdict.then(
    s,
    Judge.ready_maybe(s, base),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Verdict<Requests.Ask>,
        Spec.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            )
          )
        )
      )
    ),
    Verdict.then(
      s,
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Verdict<Requests.Ask>,
        Spec.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            )
          )
        )
      ),
      Replicas.Verdict.with(
        ~Requests.Ask.machine(),
        Maybe<&2, Ropes.Root>,
        s,
        Spec.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            )
          )
        ),
        +a => Replicas.Verdict.with(
          ~Requests.Ask.machine(),
          Maybe<&2, Ropes.Root>,
          s,
          Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            )
          ),
          +b => Replicas.Verdict.with(
            ~Requests.Ask.machine(),
            Maybe<&2, Ropes.Root>,
            s,
            Spec.Content.find(s, n, c),
            m => Judge.when(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )
            ),
            +m => Verdict.when(
              s,
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              ),
              Replicas.Verdict.take(
                ~Requests.Ask.machine(),
                s,
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              )(
                Replicas.Set.grows(~Requests.Ask.machine(), s, h, Spec.Key.res(n), Spec.Res.code(m))
              )
            )
          )
        )
      )
    )
  )

# the verdict on a resolve holds a node that grew
def Verdict.resolve(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  b: String,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Requests.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> {
  Replicas.Verdict.after(
    ~Requests.Ask.machine(),
    s,
    Judge.resolve(s, r, b, k, n, c, h)
  )
    == True{}: Bool
}:
  Verdict.then(
    s,
    Judge.ready(s, k),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Replicas.Verdict<Requests.Ask>,
        Clash.find(
          s,
          h,
          n,
          Merge.from_on(Replicas.Node.asked(~Requests.Ask.machine(), s, k), r, b)
        ),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Content.find(s, n, c),
          m => Judge.when(
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m))
          )
        )
      )
    ),
    Verdict.then(
      s,
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Replicas.Verdict<Requests.Ask>,
        Clash.find(
          s,
          h,
          n,
          Merge.from_on(Replicas.Node.asked(~Requests.Ask.machine(), s, k), r, b)
        ),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Content.find(s, n, c),
          m => Judge.when(
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m))
          )
        )
      ),
      Replicas.Verdict.with(
        ~Requests.Ask.machine(),
        Bool,
        s,
        Clash.find(
          s,
          h,
          n,
          Merge.from_on(Replicas.Node.asked(~Requests.Ask.machine(), s, k), r, b)
        ),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Verdict<Requests.Ask>,
          Spec.Content.find(s, n, c),
          m => Judge.when(
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m))
          )
        ),
        +open => Replicas.Verdict.with(
          ~Requests.Ask.machine(),
          Maybe<&2, Ropes.Root>,
          s,
          Spec.Content.find(s, n, c),
          m => Judge.when(
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m))
          ),
          +m => Verdict.when(
            s,
            open,
            x => Replicas.Work.take(~Requests.Ask.machine(), Spec.Resolve.work(s, h, n, m)),
            Replicas.Verdict.take(
              ~Requests.Ask.machine(),
              s,
              Spec.Resolve.work(s, h, n, m)
            )(Grown.resolve.work(s, h, n, m))
          )
        )
      )
    )
  )

# the verdict on an Own holds a node that grew
def Verdict.own(
  +s: Replicas.Node<Requests.Ask>,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> {
  Replicas.Verdict.after(
    ~Requests.Ask.machine(),
    s,
    Own.change(s, r, l, g, at, os, h)
  )
    == True{}: Bool
}:
  Verdict.then(
    s,
    Spec.Own.takes(s, r, l, g, at, os, h),
    u => Replicas.Work.take(
      ~Requests.Ask.machine(),
      Replicas.Work.set(
        ~Requests.Ask.machine(),
        Replicas.Work{s, h},
        Key.owner(),
        Codes.Code.text(g, [])
      )
    ),
    Replicas.Verdict.take(
      ~Requests.Ask.machine(),
      s,
      Replicas.Work.set(
        ~Requests.Ask.machine(),
        Replicas.Work{s, h},
        Key.owner(),
        Codes.Code.text(g, [])
      )
    )(Replicas.Set.grows(~Requests.Ask.machine(), s, h, Key.owner(), Codes.Code.text(g, [])))
  )

# the verdict on a change holds a node that grew from the node that judged it
def Verdict.change(
  +s: Replicas.Node<Requests.Ask>,
  +r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Requests.Change,
  +h: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>
) -> {
  Replicas.Verdict.after(~Requests.Ask.machine(), s, Judge.change(s, r, l, c, h)) == True{}: Bool
}:
  match l c:
    case None{} Requests.Change.Group{+g, +ms}:
      Verdict.when(
        s,
        Bool.not(Group.loops.any(s, h, g, ms)),
        u => Replicas.Work.take(~Requests.Ask.machine(), Group.work(s, h, g, ms)),
        Replicas.Verdict.take(
          ~Requests.Ask.machine(),
          s,
          Group.work(s, h, g, ms)
        )(Grown.group.work(s, h, g, ms))
      )
    case None{} Requests.Change.Key{+n, +k}:
      Replicas.Verdict.take(
        ~Requests.Ask.machine(),
        s,
        Replicas.Work.set(
          ~Requests.Ask.machine(),
          Replicas.Work{s, h},
          Replicas.Machine.seal(Requests.Ask.machine())(n),
          Hashes.Hash.code(k, [])
        )
      )(
        Replicas.Set.grows(
          ~Requests.Ask.machine(),
          s,
          h,
          Replicas.Machine.seal(Requests.Ask.machine())(n),
          Hashes.Hash.code(k, [])
        )
      )
    case +w Requests.Change.Own{g, at, os2}:
      Verdict.own(s, r, w, g, at, os2, h)
    case Some{b} Requests.Change.Write{n, base, c2}:
      Verdict.write(s, n, base, c2, h)
    case Some{+b} Requests.Change.Resolve{k, n, c2}:
      Verdict.resolve(s, r, b, k, n, c2, h)
    case Some{+b} Requests.Change.Merge{+from}:
      Verdict.then(
        s,
        Judge.ready(s, from),
        u => Judge.whole(
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)
          )
        ),
        Verdict.whole(
          s,
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)
          ),
          Replicas.Verdict.take(
            ~Requests.Ask.machine(),
            s,
            Spec.Merge.work(s, Replicas.Line.chain(r, Some{b}), from, h)
          )(Grown.merge.work(s, Replicas.Line.chain(r, Some{b}), from, h))
        )
      )
    case Some{+b} Requests.Change.Move{+to}:
      Verdict.then(
        s,
        Judge.ready(s, to),
        u => Judge.whole(
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)
          )
        ),
        Verdict.whole(
          s,
          Whole.both(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})),
          v => Replicas.Work.take(
            ~Requests.Ask.machine(),
            Spec.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)
          ),
          Replicas.Verdict.take(
            ~Requests.Ask.machine(),
            s,
            Spec.Move.work(s, Replicas.Line.chain(r, Some{b}), to, h)
          )(Grown.move.work(s, Replicas.Line.chain(r, Some{b}), to, h))
        )
      )
    case None{} Requests.Change.Write{n, base, c2}:
      {==}
    case None{} Requests.Change.Resolve{k, n, c2}:
      {==}
    case None{} Requests.Change.Merge{from}:
      {==}
    case None{} Requests.Change.Move{to}:
      {==}
    case None{} Requests.Change.Mark{m, d}:
      {==}
    case None{} Requests.Change.Branch{b, at}:
      {==}
    case Some{b} Requests.Change.Group{g, ms}:
      {==}
    case Some{b} Requests.Change.Key{n, k}:
      {==}
    case Some{b} Requests.Change.Mark{m, d}:
      {==}
    case Some{b} Requests.Change.Branch{b2, at}:
      {==}

# a request for a branch only grows a run's node, once it is known whether
# its version is one
def Branch.ready.grows(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> {
  Replicas.Run.after(
    ~Requests.Ask.machine(),
    Replicas.Run.state(~Requests.Ask.machine(), r),
    Branch.ready(r, i, st, b, at, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{False{}}:
      Replicas.Stale.grows(~Requests.Ask.machine(), r, i)
    case Some{True{}}:
      Replicas.After.when(
        ~Requests.Ask.machine(),
        Replicas.Run.state(~Requests.Ask.machine(), r),
        Trees.Tree.whole(
          ~Replicas.Node<Requests.Ask>,
          ~Replicas.Store.fetch(~Requests.Ask.machine()),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Node.root_of(
            ~Requests.Ask.machine(),
            Replicas.Run.state(~Requests.Ask.machine(), r),
            at
          )
        ),
        Replicas.Branch.made(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        ),
        None{},
        Replicas.Branch.made.grows(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        )(
          Grown.make.first(
            Replicas.Run.state(~Requests.Ask.machine(), r),
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )(
            Grown.make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            )
          )
        ),
        {==}
      )

# a request for a branch only grows a run's node
def Branch.new.grows(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> {
  Replicas.Run.after(
    ~Requests.Ask.machine(),
    Replicas.Run.state(~Requests.Ask.machine(), r),
    Branch.new(r, i, st, b, at, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Some{x}}:
      Replicas.Stale.grows(~Requests.Ask.machine(), r, i)
    case Some{None{}}:
      Branch.ready.grows(
        r,
        i,
        st,
        b,
        at,
        Judge.ready_maybe(Replicas.Run.state(~Requests.Ask.machine(), r), at)
      )

# On.grows once it is known how the line takes the change (w)
def On.of.grows(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change,
  w: Route
) -> {
  Replicas.Run.after(
    ~Requests.Ask.machine(),
    Replicas.Run.state(~Requests.Ask.machine(), r),
    Step.on.of(r, i, st, l, ch, w)
  )
    == True{}: Bool
}:
  match w:
    case Route.Mark{a}:
      Replicas.Mark.grows(~Requests.Ask.machine(), r, i, a)
    case Route.Branch{+a, b}:
      Branch.new.grows(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(
          ~Requests.Ask.machine(),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Requests.Ask.machine(), r)),
          Replicas.Log.start(a)
        )
      )
    case Route.Judge{}:
      Replicas.Judged.grows(
        ~Requests.Ask.machine(),
        r,
        i,
        Change.owners(ch),
        Judge.change(
          Replicas.Run.state(~Requests.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Requests.Ask.machine(), r))
        )
      )(
        Verdict.change(
          Replicas.Run.state(~Requests.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Requests.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
        )
      )

# a change of a line only grows a run's node
def On.grows(
  r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change
) -> {
  Replicas.Run.after(
    ~Requests.Ask.machine(),
    Replicas.Run.state(~Requests.Ask.machine(), r),
    Step.on(r, i, st, l, ch)
  )
    == True{}: Bool
}:
  On.of.grows(r, i, st, l, ch, Route.of(l, ch))

# a request only grows a run's node
def Change.grows(
  +r: Replicas.Run<Requests.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Requests.Ask
) -> {
  Replicas.Run.after(
    ~Requests.Ask.machine(),
    Replicas.Run.state(~Requests.Ask.machine(), r),
    Step.change(r, c, i, q)
  )
    == True{}: Bool
}:
  match q:
    case Requests.Ask.Start{os}:
      Replicas.Stale.grows(~Requests.Ask.machine(), r, i)
    case Requests.Ask.On{+st, +l, ch}:
      Replicas.After.when(
        ~Requests.Ask.machine(),
        Replicas.Run.state(~Requests.Ask.machine(), r),
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Requests.Ask.machine(), r, i),
        On.grows(r, i, st, l, ch),
        Replicas.Stale.grows(~Requests.Ask.machine(), r, i)
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count, once it is known whether its version is one
def Branch.ready.kept(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Run.Keeps(
  ~Requests.Ask.machine(),
  k2,
  v,
  Some{r}
) -> Replicas.Run.Keeps(~Requests.Ask.machine(), k2, v, Branch.ready(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{False{}}:
      Replicas.Add.kept(
        ~Requests.Ask.machine(),
        r,
        Replicas.Log.out(i),
        Replicas.Out.words(Replicas.Out.Stale{}),
        k2,
        v
      )
    case Some{True{}}:
      Replicas.Keeps.when(
        ~Requests.Ask.machine(),
        k2,
        v,
        r,
        Trees.Tree.whole(
          ~Replicas.Node<Requests.Ask>,
          ~Replicas.Store.fetch(~Requests.Ask.machine()),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Node.root_of(
            ~Requests.Ask.machine(),
            Replicas.Run.state(~Requests.Ask.machine(), r),
            at
          )
        ),
        Replicas.Branch.made(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        ),
        None{},
        Replicas.Branch.made.kept(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          ),
          k2,
          v
        )(
          Grown.make.first(
            Replicas.Run.state(~Requests.Ask.machine(), r),
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )(
            Grown.make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            )
          )
        ),
        hr => Unit{}
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count
def Branch.new.kept(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Run.Keeps(
  ~Requests.Ask.machine(),
  k2,
  v,
  Some{r}
) -> Replicas.Run.Keeps(~Requests.Ask.machine(), k2, v, Branch.new(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Some{x}}:
      Replicas.Add.kept(
        ~Requests.Ask.machine(),
        r,
        Replicas.Log.out(i),
        Replicas.Out.words(Replicas.Out.Stale{}),
        k2,
        v
      )
    case Some{None{}}:
      Branch.ready.kept(
        r,
        i,
        st,
        b,
        at,
        Judge.ready_maybe(Replicas.Run.state(~Requests.Ask.machine(), r), at),
        k2,
        v
      )

# On.kept once it is known how the line takes the change (w)
def On.of.kept(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change,
  w: Route,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Run.Keeps(
  ~Requests.Ask.machine(),
  k2,
  v,
  Some{r}
) -> Replicas.Run.Keeps(~Requests.Ask.machine(), k2, v, Step.on.of(r, i, st, l, ch, w)):
  match w:
    case Route.Mark{a}:
      hr => Replicas.Mark.kept(~Requests.Ask.machine(), r, i, a, k2, v)(hr)
    case Route.Branch{+a, b}:
      Branch.new.kept(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(
          ~Requests.Ask.machine(),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Requests.Ask.machine(), r)),
          Replicas.Log.start(a)
        ),
        k2,
        v
      )
    case Route.Judge{}:
      hr => Replicas.Judged.kept(
        ~Requests.Ask.machine(),
        r,
        i,
        Change.owners(ch),
        Judge.change(
          Replicas.Run.state(~Requests.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Requests.Ask.machine(), r))
        ),
        k2,
        v
      )(
        Verdict.change(
          Replicas.Run.state(~Requests.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Requests.Ask.machine(), r)),
          Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
        )
      )(hr)

# a change of a line keeps each key of a run's log, other than the owners and
# the count
def On.kept(
  r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Replicas.Run.Keeps(
  ~Requests.Ask.machine(),
  k2,
  v,
  Some{r}
) -> Replicas.Run.Keeps(~Requests.Ask.machine(), k2, v, Step.on(r, i, st, l, ch)):
  On.of.kept(r, i, st, l, ch, Route.of(l, ch), k2, v)

# a request keeps each key of a run's log, other than the owners and the count
def Change.kept(
  +r: Replicas.Run<Requests.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Requests.Ask,
  +k2: List<&2, U32>,
  +v: List<&2, U32>
) -> Replicas.Run.Keeps(
  ~Requests.Ask.machine(),
  k2,
  v,
  Some{r}
) -> Replicas.Run.Keeps(~Requests.Ask.machine(), k2, v, Step.change(r, c, i, q)):
  match q:
    case Requests.Ask.Start{os}:
      hr => Replicas.Add.kept(
        ~Requests.Ask.machine(),
        r,
        Replicas.Log.out(i),
        Replicas.Out.words(Replicas.Out.Stale{}),
        k2,
        v
      )(hr)
    case Requests.Ask.On{+st, +l, ch}:
      Replicas.Keeps.when(
        ~Requests.Ask.machine(),
        k2,
        v,
        r,
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Requests.Ask.machine(), r, i),
        On.kept(r, i, st, l, ch, k2, v),
        Replicas.Add.kept(
          ~Requests.Ask.machine(),
          r,
          Replicas.Log.out(i),
          Replicas.Out.words(Replicas.Out.Stale{}),
          k2,
          v
        )
      )

# a request for a branch has an outcome, once it is known whether its version
# is one
def Branch.ready.outs(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  +m: Maybe<&2, Bool>
) -> Replicas.Run.Outs(~Requests.Ask.machine(), Branch.ready(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{False{}}:
      Replicas.Stale.outs(~Requests.Ask.machine(), r, i)
    case Some{True{}}:
      Replicas.Outs.when(
        ~Requests.Ask.machine(),
        Trees.Tree.whole(
          ~Replicas.Node<Requests.Ask>,
          ~Replicas.Store.fetch(~Requests.Ask.machine()),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Node.root_of(
            ~Requests.Ask.machine(),
            Replicas.Run.state(~Requests.Ask.machine(), r),
            at
          )
        ),
        Replicas.Branch.made(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        ),
        None{},
        i,
        Replicas.Branch.made.outs(
          ~Requests.Ask.machine(),
          r,
          i,
          b,
          Make.first(
            Make.branch(
              Replicas.Run.state(~Requests.Ask.machine(), r),
              Replicas.Line.chain(st, Some{b}),
              at
            ),
            Replicas.Tip.owners(Replicas.Run.tip(~Requests.Ask.machine(), r))
          )
        ),
        Unit{}
      )

# a request for a branch has an outcome
def Branch.new.outs(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Replicas.Run.Outs(~Requests.Ask.machine(), Branch.new(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Replicas.Stale.outs(~Requests.Ask.machine(), r, i)
    case Some{None{}}:
      Branch.ready.outs(
        r,
        i,
        st,
        b,
        at,
        Judge.ready_maybe(Replicas.Run.state(~Requests.Ask.machine(), r), at)
      )

# On.outs once it is known how the line takes the change (w)
def On.of.outs(
  +r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  l: Maybe<&2, String>,
  +ch: Requests.Change,
  w: Route
) -> Replicas.Run.Outs(~Requests.Ask.machine(), Step.on.of(r, i, st, l, ch, w), i):
  match w:
    case Route.Mark{a}:
      Replicas.Mark.outs(~Requests.Ask.machine(), r, i, a)
    case Route.Branch{+a, b}:
      Branch.new.outs(
        r,
        i,
        st,
        a,
        b,
        Replicas.Node.find(
          ~Requests.Ask.machine(),
          Replicas.Run.state(~Requests.Ask.machine(), r),
          Replicas.Tip.log(Replicas.Run.tip(~Requests.Ask.machine(), r)),
          Replicas.Log.start(a)
        )
      )
    case Route.Judge{}:
      Replicas.Judged.outs(
        ~Requests.Ask.machine(),
        r,
        i,
        Change.owners(ch),
        Judge.change(
          Replicas.Run.state(~Requests.Ask.machine(), r),
          st,
          l,
          ch,
          Replicas.Tip.content(Replicas.Run.tip(~Requests.Ask.machine(), r))
        )
      )

# a change of a line has an outcome
def On.outs(
  r: Replicas.Run<Requests.Ask>,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Requests.Change
) -> Replicas.Run.Outs(~Requests.Ask.machine(), Step.on(r, i, st, l, ch), i):
  On.of.outs(r, i, st, l, ch, Route.of(l, ch))

# a request of a run has an outcome
def Change.outs(
  +r: Replicas.Run<Requests.Ask>,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Requests.Ask
) -> Replicas.Run.Outs(~Requests.Ask.machine(), Step.change(r, c, i, q), i):
  match q:
    case Requests.Ask.Start{os}:
      Replicas.Stale.outs(~Requests.Ask.machine(), r, i)
    case Requests.Ask.On{st, l, ch}:
      Replicas.Outs.when(
        ~Requests.Ask.machine(),
        Ledgers.Chain.is_eq(Replicas.Line.chain(st, l), c),
        Step.on(r, i, st, l, ch),
        Replicas.Step.stale(~Requests.Ask.machine(), r, i),
        i,
        On.outs(r, i, st, l, ch),
        Replicas.Stale.outs(~Requests.Ask.machine(), r, i)
      )

# the lawful kernel of Spec.Vend: its change only grows the node of a run, keeps
# each key of its log, and gives its request an outcome
def Ask.lawful() -> Replicas.Lawful(Requests.Ask.machine()):
  (
    Spec.Ask.kernel(),
    (
      +r => c => +i => +q => Change.grows(r, c, i, q),
      (
        +r => c => +i => q => +k2 => +v => Change.kept(r, c, i, q, k2, v),
        +r => c => +i => +q => Change.outs(r, c, i, q)
      )
    )
  )

# Asks
# ----

# Logs
# ----
# A log only gains keys: a key that a log holds, other than the owners and the
# count, holds the same value after any step.

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# Moves
# -----
# A move sets only keys of the version vector, so each resource of its target
# reads the same after it (Spec.Move.reads).

# the key of a resource is not the key of a line in the version vector
def Vector.apart(
  c: Ledgers.Chain,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Key.vector(c), Spec.Key.res(n)) == False{}: Bool}:
  {==}

# Vector.add keeps a resource, once it is known whether the vector covers the
# place (b)
def Vector.add.reads.if(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  +c: Ledgers.Chain,
  p: Replicas.Place,
  +n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: {
    Replicas.Node.get(
      ~Requests.Ask.machine(),
      s,
      h,
      Spec.Key.res(n)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Replicas.Work<Requests.Ask>>,
    b,
    u => Some{Replicas.Work{s, h}},
    u => Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Key.vector(c),
      Replicas.Place.code(p)
    )
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Replicas.Set.kept(
        ~Requests.Ask.machine(),
        s,
        h,
        Key.vector(c),
        Replicas.Place.code(p),
        Spec.Key.res(n),
        v,
        Vector.apart(c, n),
        hget
      )

# a new entry of the version vector keeps a resource
def Vector.add.reads(
  w: Replicas.Work<Requests.Ask>,
  +c: Ledgers.Chain,
  +p: Replicas.Place,
  n: Resources.Name,
  v: List<&2, U32>
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Vector.add(w, c, p)):
  match w:
    case Replicas.Work{+s, +h}:
      hget => Vector.add.reads.if(
        s,
        h,
        c,
        p,
        n,
        v,
        Replicas.Place.covered(Node.vector(s, h, c), p),
        hget
      )

# Vector.add.if keeps a resource, once it is known whether the place is of
# the line (b)
def Vector.add.if.reads.at(
  w: Replicas.Work<Requests.Ask>,
  +p: Replicas.Place,
  n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Some{w})
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Replicas.Work<Requests.Ask>>,
    b,
    u => Some{w},
    u => Vector.add(w, Replicas.Place.chain(p), p)
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Vector.add.reads(w, Replicas.Place.chain(p), p, n, v)(hget)

# an entry of the version vector, if any, keeps a resource
def Vector.add.if.reads(
  w: Replicas.Work<Requests.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Place>,
  n: Resources.Name,
  v: List<&2, U32>
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Vector.add.if(w, c, m)):
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
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  m
) -> Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Vector.adds(bs, c, m)):
  match bs:
    case Nil{}:
      hm => hm
    case Con{+b, r}:
      hm => Vector.adds.reads(
        r,
        c,
        Maybe.bind(
          &2,
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Vector.add.if(w, c, Vector.entry(b))
        ),
        n,
        v
      )(
        Replicas.Reads.bind(
          ~Requests.Ask.machine(),
          Spec.Key.res(n),
          v,
          m,
          w => Vector.add.if(w, c, Vector.entry(b))
        )(hm)(+w => hw => Vector.add.if.reads(w, c, Vector.entry(b), n, v)(hw))
      )

# the version vector of a version, joined in, keeps a resource
def Vector.joined.reads(
  +s: Replicas.Node<Requests.Ask>,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  m
) -> Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Vector.joined(s, c, x, m)):
  hm => Replicas.Reads.bind(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    v,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{x})
      ),
      c,
      m
    ),
    w => Vector.add.if(w, c, Replicas.Node.place(~Requests.Ask.machine(), s, x))
  )(
    Vector.adds.reads(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{x})
      ),
      c,
      m,
      n,
      v
    )(hm)
  )(
    +w => hw => Vector.add.if.reads(
      w,
      c,
      Replicas.Node.place(~Requests.Ask.machine(), s, x),
      n,
      v
    )(hw)
  )

def Spec.Move.reads(s, c, to, h, n, v):
  hget => Vector.joined.reads(
    s,
    c,
    to,
    Vector.adds(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h
      ),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})}}
    ),
    n,
    v
  )(
    Vector.adds.reads(
      Trees.Tree.list(
        ~Replicas.Node<Requests.Ask>,
        ~Replicas.Store.fetch(~Requests.Ask.machine()),
        s,
        h
      ),
      c,
      Some{Replicas.Work{s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to})}},
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
                Replicas.Text.same(
                  t1,
                  t2,
                  Equal.cong(
                    List<&2, U32>,
                    List<&2, U32>,
                    Replicas.Words.rest,
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

# the key of a clash is not the key of a resource
def Clash.apart(
  m: Resources.Name,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.clash(m), Spec.Key.res(n)) == False{}: Bool}:
  {==}

# the merge of one resource m, of the trees hb (base), ho (ours) and ht
# (theirs), on the work w: one step of Spec.Merge.all
def Merge.step(
  +s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  w: Replicas.Work<Requests.Ask>
) -> Maybe<&2, Replicas.Work<Requests.Ask>>:
  Maybe.bind(
    &2,
    Maybe<&2, Ropes.Root>,
    Replicas.Work<Requests.Ask>,
    Spec.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Requests.Ask>,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Requests.Ask>,
        Spec.Res.find(s, ht, m),
        x => Merge.one(s, f, m, b, o, x, w)
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
  +w: Replicas.Work<Requests.Ask>,
  +v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.res(m), Spec.Key.res(n)) == False{}: Bool}
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), v, Merge.put(f, m, o2, p, w)):
  match p:
    case Spec.Pick.Take{mm}:
      Replicas.Set.kept.work(
        ~Requests.Ask.machine(),
        w,
        Spec.Key.res(m),
        Spec.Res.code(mm),
        Spec.Key.res(n),
        v,
        hne
      )
    case Spec.Pick.Make{y}:
      hget => Replicas.Reads.bind(
        ~Requests.Ask.machine(),
        Spec.Key.res(n),
        v,
        Replicas.Work.keep(~Requests.Ask.machine(), w, Ropes.Put.nodes(Replicas.Bytes.rope(y))),
        w2 => Replicas.Work.set(
          ~Requests.Ask.machine(),
          w2,
          Spec.Key.res(m),
          Spec.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(y))})
        )
      )(
        Replicas.Keep.reads(
          ~Requests.Ask.machine(),
          w,
          Ropes.Put.nodes(Replicas.Bytes.rope(y)),
          Spec.Key.res(n),
          v
        )(hget)
      )(
        w2 => hw => Replicas.Set.kept.work(
          ~Requests.Ask.machine(),
          w2,
          Spec.Key.res(m),
          Spec.Res.code(Some{Ropes.Put.root(Replicas.Bytes.rope(y))}),
          Spec.Key.res(n),
          v,
          hne
        )(hw)
      )
    case Spec.Pick.Clash{}:
      hget => Replicas.Reads.bind(
        ~Requests.Ask.machine(),
        Spec.Key.res(n),
        v,
        Replicas.Work.set(~Requests.Ask.machine(), w, Spec.Key.res(m), Spec.Res.code(o2)),
        y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(m), Spec.Clash.code(f))
      )(
        Replicas.Set.kept.work(
          ~Requests.Ask.machine(),
          w,
          Spec.Key.res(m),
          Spec.Res.code(o2),
          Spec.Key.res(n),
          v,
          hne
        )(hget)
      )(
        y => hy => Replicas.Set.kept.work(
          ~Requests.Ask.machine(),
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
  +s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  n: Resources.Name,
  w: Replicas.Work<Requests.Ask>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Spec.Key.res(m), Spec.Key.res(n)) == False{}: Bool}
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Some{w}
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  v,
  Merge.step(s, f, hb, ho, ht, m, w)
):
  hget => Replicas.Reads.with(
    ~Requests.Ask.machine(),
    Maybe<&2, Ropes.Root>,
    Spec.Key.res(n),
    v,
    Spec.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Requests.Ask>,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Requests.Ask>,
        Spec.Res.find(s, ht, m),
        x => Merge.one(s, f, m, b, o, x, w)
      )
    )
  )(
    b => Replicas.Reads.with(
      ~Requests.Ask.machine(),
      Maybe<&2, Ropes.Root>,
      Spec.Key.res(n),
      v,
      Spec.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Requests.Ask>,
        Spec.Res.find(s, ht, m),
        x => Merge.one(s, f, m, b, o, x, w)
      )
    )(
      +o => Replicas.Reads.with(
        ~Requests.Ask.machine(),
        Maybe<&2, Ropes.Root>,
        Spec.Key.res(n),
        v,
        Spec.Res.find(s, ht, m),
        x => Merge.one(s, f, m, b, o, x, w)
      )(
        x => Replicas.Reads.with(
          ~Requests.Ask.machine(),
          Spec.Pick,
          Spec.Key.res(n),
          v,
          Spec.Pick.merge(Formats.Format.of(Resources.Name.path(m)), s, b, o, x),
          p => Merge.put(f, m, o, p, w)
        )(p => Merge.put.other(f, m, n, o, p, w, v, hne)(hget))
      )
    )
  )

# the merge of the resource n gives what its pick takes
def Merge.step.same(
  s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  w: Replicas.Work<Requests.Ask>,
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
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Merge.step(s, f, hb, ho, ht, n, w)
):
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, hb, n),
    Some{b},
    eb
  ): Replicas.Work.Reads(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Requests.Ask>,
      _,
      b1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Requests.Ask>,
        Spec.Res.find(s, ho, n),
        o1 => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Replicas.Work<Requests.Ask>,
          Spec.Res.find(s, ht, n),
          x1 => Merge.one(s, f, n, b1, o1, x1, w)
        )
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, ho, n),
    Some{o},
    eo
  ): Replicas.Work.Reads(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Requests.Ask>,
      _,
      o1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Replicas.Work<Requests.Ask>,
        Spec.Res.find(s, ht, n),
        x1 => Merge.one(s, f, n, b, o1, x1, w)
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Spec.Res.find(s, ht, n),
    Some{t},
    et
  ): Replicas.Work.Reads(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Replicas.Work<Requests.Ask>,
      _,
      x1 => Merge.one(s, f, n, b, o, x1, w)
    )
  )
  %Equal.sym(
    Maybe<&2, Spec.Pick>,
    Spec.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    Some{Spec.Pick.Take{x}},
    ep
  ): Replicas.Work.Reads(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(x),
    Maybe.bind(&2, Spec.Pick, Replicas.Work<Requests.Ask>, _, p => Merge.put(f, n, o, p, w))
  )
  Replicas.Set.read(~Requests.Ask.machine(), w, Spec.Key.res(n), Spec.Res.code(x))

# Merge.step.same on the work m, if any
def Merge.step.takes(
  s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
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
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Maybe.bind(
    &2,
    Replicas.Work<Requests.Ask>,
    Replicas.Work<Requests.Ask>,
    m,
    w => Merge.step(s, f, hb, ho, ht, n, w)
  )
):
  match m:
    case None{}:
      Unit{}
    case Some{w}:
      Merge.step.same(s, f, hb, ho, ht, n, b, o, t, x, w, eb, eo, et, ep)

# one step of a merge keeps what the work reads for n, once it is known
# whether the step is of n (same)
def Merge.step.keeps(
  s: Replicas.Node<Requests.Ask>,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m1: Resources.Name,
  m: Maybe<&2, Replicas.Work<Requests.Ask>>,
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
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  m
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Maybe.bind(
    &2,
    Replicas.Work<Requests.Ask>,
    Replicas.Work<Requests.Ask>,
    m,
    w => Merge.step(s, f, hb, ho, ht, m1, w)
  )
):
  match same:
    case True{}:
      hm =>
        %Equal.sym(
          Resources.Name,
          m1,
          n,
          Resources.Name.is_eq_sound(m1, n)(es)
        ): Replicas.Work.Reads(
          ~Requests.Ask.machine(),
          Spec.Key.res(n),
          Spec.Res.code(x),
          Maybe.bind(
            &2,
            Replicas.Work<Requests.Ask>,
            Replicas.Work<Requests.Ask>,
            m,
            w => Merge.step(s, f, hb, ho, ht, _, w)
          )
        )
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep)
    case False{}:
      hm => Replicas.Reads.bind(
        ~Requests.Ask.machine(),
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
  +s: Replicas.Node<Requests.Ask>,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
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
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  m
) -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Merge.all(s, f, ns, hb, ho, ht, m)
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
        Maybe.bind(
          &2,
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Merge.step(s, f, hb, ho, ht, m1, w)
        ),
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
  +s: Replicas.Node<Requests.Ask>,
  +f: Ledgers.Id,
  +m1: Resources.Name,
  r: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
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
  } -> Replicas.Work.Reads(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(x),
    Merge.all(
      s,
      f,
      r,
      hb,
      ho,
      ht,
      Maybe.bind(
        &2,
        Replicas.Work<Requests.Ask>,
        Replicas.Work<Requests.Ask>,
        m,
        w => Merge.step(s, f, hb, ho, ht, m1, w)
      )
    )
  )
) -> {
  List.any.if(
    u => List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n),
    same
  )
    == True{}: Bool
} -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Merge.all(
    s,
    f,
    r,
    hb,
    ho,
    ht,
    Maybe.bind(
      &2,
      Replicas.Work<Requests.Ask>,
      Replicas.Work<Requests.Ask>,
      m,
      w => Merge.step(s, f, hb, ho, ht, m1, w)
    )
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
        Maybe.bind(
          &2,
          Replicas.Work<Requests.Ask>,
          Replicas.Work<Requests.Ask>,
          m,
          w => Merge.step(s, f, hb, ho, ht, m1, w)
        ),
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
        %Equal.sym(Resources.Name, m1, n, Resources.Name.is_eq_sound(m1, n)(es)): Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), Spec.Res.code(x), Maybe.bind(&2, Replicas.Work<Requests.Ask>, Replicas.Work<Requests.Ask>, m, w => Merge.step(s, f, hb, ho, ht, _, w)))
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep))
    case False{}:
      e => ih(e)

# a merge of the resources ns, with n among them, gives what the pick of n
# takes
def Merge.all.takes(
  +s: Replicas.Node<Requests.Ask>,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Replicas.Work<Requests.Ask>>,
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
} -> Replicas.Work.Reads(
  ~Requests.Ask.machine(),
  Spec.Key.res(n),
  Spec.Res.code(x),
  Merge.all(s, f, ns, hb, ho, ht, m)
):
  match ns:
    case Nil{}:
      e => Empty.absurd(
        Replicas.Work.Reads(~Requests.Ask.machine(), Spec.Key.res(n), Spec.Res.code(x), m),
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
          Maybe.bind(
            &2,
            Replicas.Work<Requests.Ask>,
            Replicas.Work<Requests.Ask>,
            m,
            w => Merge.step(s, f, hb, ho, ht, m1, w)
          ),
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
    Merge.all(
      s,
      from,
      Spec.Merge.names(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Spec.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}),
      Some{Replicas.Work{s, h}}
    ),
    n,
    Spec.Res.code(x)
  )(
    Merge.all.takes(
      s,
      from,
      Spec.Merge.names(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Spec.Merge.base(s, c, from, h)),
      h,
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}),
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
  Replicas.Reads.bind(
    ~Requests.Ask.machine(),
    Spec.Key.res(n),
    Spec.Res.code(m),
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Spec.Key.res(n),
      Spec.Res.code(m)
    ),
    y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), [])
  )(
    Replicas.Set.read(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Spec.Key.res(n),
      Spec.Res.code(m)
    )
  )(
    y => hy => Replicas.Set.kept.work(
      ~Requests.Ask.machine(),
      y,
      Spec.Key.clash(n),
      [],
      Spec.Key.res(n),
      Spec.Res.code(m),
      Clash.apart(n, n)
    )(hy)
  )

def Spec.Resolve.shuts(s, h, n, m):
  Replicas.Reads.with(
    ~Requests.Ask.machine(),
    Replicas.Work<Requests.Ask>,
    Spec.Key.clash(n),
    [],
    Replicas.Work.set(
      ~Requests.Ask.machine(),
      Replicas.Work{s, h},
      Spec.Key.res(n),
      Spec.Res.code(m)
    ),
    y => Replicas.Work.set(~Requests.Ask.machine(), y, Spec.Key.clash(n), [])
  )(y => Replicas.Set.read(~Requests.Ask.machine(), y, Spec.Key.clash(n), []))

def Spec.Clash.shut(s, h, n, f):
  match f:
    case Ledgers.Id{w, q}:
      e =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Replicas.Node.get(~Requests.Ask.machine(), s, h, Spec.Key.clash(n)),
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
        Replicas.Count.full(
          Codes.Code.length(w),
          Codes.Code.chars(w, Codes.Code.count(Codes.Code.length(q), Codes.Code.chars(q, [])))
        )

# Outcomes
# --------
# A step gives each of its requests an outcome (Step.run_outs), and only
# the requests of a step leave the requests that wait (Replicas.Wait.left_keeps).

# Agreement
# ---------

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

# a verdict that takes, after a verdict, is the verdict of what comes next
def Then.took(
  m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Replicas.Node<Requests.Ask>
) -> {
  Judge.then(
    m,
    k
  )
    == Some{
      Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
    }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
} -> {
  k(
    Unit{}
  )
    == Some{
      Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
    }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
}:
  match m:
    case Some{True{}}:
      e => e
    case Some{False{}}:
      e => Empty.absurd(
        {
          k(
            Unit{}
          )
            == Some{
              Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
            }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Replicas.Verdict<Requests.Ask>>,
            Bool,
            v => Replicas.Verdict.took(~Requests.Ask.machine(), v),
            Judge.refuse(),
            Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
            e
          )
        )
      )
    case None{}:
      e => Empty.absurd(
        {
          k(
            Unit{}
          )
            == Some{
              Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
            }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
        },
        Shared.Maybe.none_ne_some(
          Replicas.Verdict<Requests.Ask>,
          Replicas.Verdict.Taken{Replicas.Work{s3, h2}},
          e
        )
      )

# a verdict that takes, under a condition, is the verdict of what comes next
def When.took(
  b: Bool,
  -k: Unit -> Maybe<&2, Replicas.Verdict<Requests.Ask>>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Replicas.Node<Requests.Ask>
) -> {
  Judge.when(
    b,
    k
  )
    == Some{
      Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
    }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
} -> {
  k(
    Unit{}
  )
    == Some{
      Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
    }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {
          k(
            Unit{}
          )
            == Some{
              Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
            }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Replicas.Verdict<Requests.Ask>>,
            Bool,
            v => Replicas.Verdict.took(~Requests.Ask.machine(), v),
            Judge.refuse(),
            Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}},
            e
          )
        )
      )

def Spec.Judge.write_reads(s, n, base, c, h, h2, s3, m):
  e => ec =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Replicas.Node.get(~Requests.Ask.machine(), s3, h2, Spec.Key.res(n)),
      Some{Spec.Res.code(m)},
      Replicas.Set.reads(
        ~Requests.Ask.machine(),
        s,
        h,
        Spec.Key.res(n),
        Spec.Res.code(m),
        Replicas.Node.set(~Requests.Ask.machine(), s, h, Spec.Key.res(n), Spec.Res.code(m)),
        h2,
        s3
      )(
        {==}
      )(
        Replicas.With.took(
          ~Requests.Ask.machine(),
          Maybe<&2, Ropes.Root>,
          Spec.Res.find(s, h, n),
          a1 => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Replicas.Verdict<Requests.Ask>,
            Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Requests.Ask>,
              Spec.Content.find(s, n, c),
              m1 => Judge.when(
                Spec.Roots.same(a1, b1),
                x => Replicas.Work.take(
                  ~Requests.Ask.machine(),
                  Replicas.Work.set(
                    ~Requests.Ask.machine(),
                    Replicas.Work{s, h},
                    Spec.Key.res(n),
                    Spec.Res.code(m1)
                  )
                )
              )
            )
          ),
          Replicas.Work.take(
            ~Requests.Ask.machine(),
            Replicas.Work.set(
              ~Requests.Ask.machine(),
              Replicas.Work{s, h},
              Spec.Key.res(n),
              Spec.Res.code(m)
            )
          ),
          h2,
          s3
        )(
          +a => Replicas.With.took(
            ~Requests.Ask.machine(),
            Maybe<&2, Ropes.Root>,
            Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Requests.Ask>,
              Spec.Content.find(s, n, c),
              m1 => Judge.when(
                Spec.Roots.same(a, b1),
                x => Replicas.Work.take(
                  ~Requests.Ask.machine(),
                  Replicas.Work.set(
                    ~Requests.Ask.machine(),
                    Replicas.Work{s, h},
                    Spec.Key.res(n),
                    Spec.Res.code(m1)
                  )
                )
              )
            ),
            Replicas.Work.take(
              ~Requests.Ask.machine(),
              Replicas.Work.set(
                ~Requests.Ask.machine(),
                Replicas.Work{s, h},
                Spec.Key.res(n),
                Spec.Res.code(m)
              )
            ),
            h2,
            s3
          )(
            +b => ex => When.took(
              Spec.Roots.same(a, b),
              x => Replicas.Work.take(
                ~Requests.Ask.machine(),
                Replicas.Work.set(
                  ~Requests.Ask.machine(),
                  Replicas.Work{s, h},
                  Spec.Key.res(n),
                  Spec.Res.code(m)
                )
              ),
              h2,
              s3
            )(
              %ec: {Maybe.bind(&2, Maybe<&2, Ropes.Root>, Replicas.Verdict<Requests.Ask>, _, m1 => Judge.when(Spec.Roots.same(a, b), x => Replicas.Work.take(~Requests.Ask.machine(), Replicas.Work.set(~Requests.Ask.machine(), Replicas.Work{s, h}, Spec.Key.res(n), Spec.Res.code(m1))))) == Some{Replicas.Verdict.Taken{Replicas.Work{s3, h2}}}: Maybe<&2, Replicas.Verdict<Requests.Ask>>}
              ex)
          )
        )(
          Then.took(
            Judge.content(s, c),
            w => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Replicas.Verdict<Requests.Ask>,
              Spec.Res.find(s, h, n),
              a1 => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Replicas.Verdict<Requests.Ask>,
                Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
                b1 => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Replicas.Verdict<Requests.Ask>,
                  Spec.Content.find(s, n, c),
                  m1 => Judge.when(
                    Spec.Roots.same(a1, b1),
                    x => Replicas.Work.take(
                      ~Requests.Ask.machine(),
                      Replicas.Work.set(
                        ~Requests.Ask.machine(),
                        Replicas.Work{s, h},
                        Spec.Key.res(n),
                        Spec.Res.code(m1)
                      )
                    )
                  )
                )
              )
            ),
            h2,
            s3
          )(
            Then.took(
              Judge.ready_maybe(s, base),
              u => Judge.then(
                Judge.content(s, c),
                w => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Replicas.Verdict<Requests.Ask>,
                  Spec.Res.find(s, h, n),
                  a1 => Maybe.bind(
                    &2,
                    Maybe<&2, Ropes.Root>,
                    Replicas.Verdict<Requests.Ask>,
                    Spec.Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, base), n),
                    b1 => Maybe.bind(
                      &2,
                      Maybe<&2, Ropes.Root>,
                      Replicas.Verdict<Requests.Ask>,
                      Spec.Content.find(s, n, c),
                      m1 => Judge.when(
                        Spec.Roots.same(a1, b1),
                        x => Replicas.Work.take(
                          ~Requests.Ask.machine(),
                          Replicas.Work.set(
                            ~Requests.Ask.machine(),
                            Replicas.Work{s, h},
                            Spec.Key.res(n),
                            Spec.Res.code(m1)
                          )
                        )
                      )
                    )
                  )
                )
              ),
              h2,
              s3
            )(e)
          )
        )
      )
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
          w => Pick.both(f, s, b, o, t)
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
          w => Pick.both(f, s, b, o, t)
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
          w => Pick.both(f, s, b, o, t)
        )
      )
        == Some{Spec.Pick.Take{o}}: Maybe<&2, Spec.Pick>
    }
    {==}

def Spec.Node.read_draft(s, w, r, b, n, c):
  e =>
    %Equal.sym(
      Maybe<&2, Requests.Content>,
      Spec.Node.draft(s, w, r, b, n),
      Some{c},
      e
    ): {
      Read.of(
        s,
        n,
        _,
        Spec.Point.Head{r, b}
      )
        == Replicas.Root.bytes(
          ~Requests.Ask.machine(),
          s,
          Spec.Content.root(s, n, c)
        ): Maybe<&2, Texts.Bytes()>
    }
    {==}

def Spec.Node.affects_used(s, b):
  +g = Spec.Seen.of(s, b)
  Shared.List.keep_holds(~Spec.Touch, ~Spec.Seen, ~Spec.Touch.holds, Affects.cands(g), g)

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
  a: Replicas.Node<Requests.Ask>,
  b: Replicas.Node<Requests.Ask>,
  +i: Ledgers.Id,
  q: Requests.Ask
) -> {Spec.Answer.follows(Answer.taken(a, i, q), Some{Answer.taken(b, i, q)}) == True{}: Bool}:
  match q:
    case Requests.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Branch{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Group{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Own{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Write{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Resolve{+k, y, z}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Node.conflict(a, k)),
        List.is_empty(&2, Resources.Name, Node.conflict(b, k)),
        i,
        k
      )
    case Requests.Ask.On{st, l, Requests.Change.Merge{f}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Node.conflict(a, i)),
        List.is_empty(&2, Resources.Name, Node.conflict(b, i)),
        i,
        i
      )
    case Requests.Ask.On{st, l, Requests.Change.Move{x}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Mark{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, Requests.Change.Key{x, y}}:
      Ledgers.Id.is_eq_refl(i)

# Asked.follows once the outcome oa of the request is known
def Of.follows(
  a: Replicas.Node<Requests.Ask>,
  b: Replicas.Node<Requests.Ask>,
  i: Ledgers.Id,
  q: Requests.Ask,
  oa: Maybe<&2, Replicas.Out>
) -> {
  Replicas.Node.out(~Requests.Ask.machine(), a, i) == oa: Maybe<&2, Replicas.Out>
} -> (
  @o: Replicas.Out -> {
    Replicas.Node.out(~Requests.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Requests.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Spec.Answer.follows(
    Answer.of(a, i, q, Replicas.Node.out(~Requests.Ask.machine(), a, i)),
    Some{Answer.of(b, i, q, Replicas.Node.out(~Requests.Ask.machine(), b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Requests.Ask.machine(), a, i),
          None{},
          eo
        ): {
          Spec.Answer.follows(
            Answer.of(a, i, q, _),
            Some{Answer.of(b, i, q, Replicas.Node.out(~Requests.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Replicas.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Requests.Ask.machine(), a, i),
          Some{Replicas.Out.Stale{}},
          eo
        ): {
          Spec.Answer.follows(
            Answer.of(a, i, q, _),
            Some{Answer.of(b, i, q, Replicas.Node.out(~Requests.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Requests.Ask.machine(), b, i),
          Some{Replicas.Out.Stale{}},
          ho(Replicas.Out.Stale{})(eo)
        ): {
          Spec.Answer.follows(
            Answer.of(a, i, q, Some{Replicas.Out.Stale{}}),
            Some{Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        {==}
    case Some{Replicas.Out.Taken{k}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Requests.Ask.machine(), a, i),
          Some{Replicas.Out.Taken{k}},
          eo
        ): {
          Spec.Answer.follows(
            Answer.of(a, i, q, _),
            Some{Answer.of(b, i, q, Replicas.Node.out(~Requests.Ask.machine(), b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Replicas.Out>,
          Replicas.Node.out(~Requests.Ask.machine(), b, i),
          Some{Replicas.Out.Taken{k}},
          ho(Replicas.Out.Taken{k})(eo)
        ): {
          Spec.Answer.follows(
            Answer.of(a, i, q, Some{Replicas.Out.Taken{k}}),
            Some{Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        Taken.follows(a, b, i, q)

# the answer to a request that a node holds may come after the answer to it
def Asked.follows(
  +a: Replicas.Node<Requests.Ask>,
  b: Replicas.Node<Requests.Ask>,
  +i: Ledgers.Id,
  q: Requests.Ask,
  ho: @o: Replicas.Out -> {
    Replicas.Node.out(~Requests.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Requests.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {Spec.Answer.follows(Answer.asked(a, i, q), Some{Answer.asked(b, i, q)}) == True{}: Bool}:
  match q:
    case Requests.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Requests.Ask.On{st, l, ch}:
      Of.follows(
        a,
        b,
        i,
        Requests.Ask.On{st, l, ch},
        Replicas.Node.out(~Requests.Ask.machine(), a, i)
      )({==})(ho)

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
  a: Replicas.Node<Requests.Ask>,
  b: Replicas.Node<Requests.Ask>,
  i: Ledgers.Id,
  q: Requests.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Requests.Ask>>>,
  ho: @o: Replicas.Out -> {
    Replicas.Node.out(~Requests.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Requests.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {Follows.opt(Answer.held(a, i, q, m), Answer.held(b, i, q, m)) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Held.follows.if(
        Requests.Ask.is_eq(q2, q),
        Answer.asked(a, i, q2),
        Answer.asked(b, i, q2),
        Asked.follows(a, b, i, q2, ho)
      )
    case Some{Cells.One{Ledgers.Entry.Vote{v}}}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Data{d}}}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Lie{x}}}:
      {==}
    case Some{Cells.Many{}}:
      {==}

# Node.answer_follows once the cell ma of the request's ID is known
def Answer.follows.at(
  a: Replicas.Node<Requests.Ask>,
  b: Replicas.Node<Requests.Ask>,
  i: Ledgers.Id,
  q: Requests.Ask,
  -x: Spec.Answer,
  ma: Maybe<&2, Cells.Cell<Ledgers.Entry<Requests.Ask>>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Requests.Ask>>>,
  ho: @o: Replicas.Out -> {
    Replicas.Node.out(~Requests.Ask.machine(), a, i) == Some{o}: Maybe<&2, Replicas.Out>
  } -> {Replicas.Node.out(~Requests.Ask.machine(), b, i) == Some{o}: Maybe<&2, Replicas.Out>}
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Requests.Ask>,
    ~Ledgers.Entry.is_eq(~Requests.Ask, ~Requests.Ask.is_eq),
    ma,
    mb
  )
    == True{}: Bool
} -> {
  Answer.held(a, i, q, ma) == Some{x}: Maybe<&2, Spec.Answer>
} -> {Spec.Answer.follows(x, Answer.held(b, i, q, mb)) == True{}: Bool}:
  match ma:
    case None{}:
      ek => e => Empty.absurd(
        {Spec.Answer.follows(x, Answer.held(b, i, q, mb)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Spec.Answer, x, e)
      )
    case Some{+c}:
      ek => e =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Requests.Ask>>>,
          mb,
          Some{c},
          Replicas.Cell.kept.eq(~Requests.Ask.machine(), c, mb)(ek)
        ): {Spec.Answer.follows(x, Answer.held(b, i, q, _)) == True{}: Bool}
        %e: {Follows.opt(_, Answer.held(b, i, q, Some{c})) == True{}: Bool}
        Held.follows(a, b, i, q, Some{c}, ho)

def Spec.Node.answer_follows(n, evs, s, e, q, x):
  Answer.follows.at(
    s,
    Replicas.Node.after(~Requests.Ask.machine(), ~Spec.Ask.kernel(), n, evs, s),
    Replicas.Envelope.of(e),
    q,
    x,
    Ledgers.State.get(
      ~Requests.Ask,
      Replicas.State.ledger(~Requests.Ask.machine(), s),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    ),
    Ledgers.State.get(
      ~Requests.Ask,
      Replicas.State.ledger(
        ~Requests.Ask.machine(),
        Replicas.Node.after(~Requests.Ask.machine(), ~Spec.Ask.kernel(), n, evs, s)
      ),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    ),
    o => Replicas.Out.kept(
      ~Requests.Ask.machine(),
      s,
      Replicas.Node.after(~Requests.Ask.machine(), ~Spec.Ask.kernel(), n, evs, s),
      Replicas.Envelope.of(e),
      o,
      Replicas.Node.after_grows(~Requests.Ask.machine(), ~Ask.lawful(), n, evs, s),
      Replicas.Node.after_keeps(~Requests.Ask.machine(), ~Ask.lawful(), n, evs, s)
    )
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Requests.Ask>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Requests.Ask>,
        ~Ledgers.Entry.is_eq(~Requests.Ask, ~Requests.Ask.is_eq)
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Requests.Ask>,
        ~Ledgers.Entry.is_eq(~Requests.Ask, ~Requests.Ask.is_eq)
      ),
      Replicas.State.ledger(~Requests.Ask.machine(), s),
      Replicas.State.ledger(
        ~Requests.Ask.machine(),
        Replicas.Node.after(~Requests.Ask.machine(), ~Spec.Ask.kernel(), n, evs, s)
      ),
      Ledgers.Slot.ask(Replicas.Envelope.of(e))
    )(Replicas.Node.after_grows(~Requests.Ask.machine(), ~Ask.lawful(), n, evs, s))
  )

# Drafts
# ------

# one of two drafts that are there
def When.some(
  b: Bool,
  -x: Maybe<&2, Draft>,
  -y: Maybe<&2, Draft>,
  hx: {Maybe.is_some(&2, Draft, x) == True{}: Bool},
  hy: {Maybe.is_some(&2, Draft, y) == True{}: Bool}
) -> {
  Maybe.is_some(&2, Draft, Shared.Bool.when(Maybe<&2, Draft>, b, u => x, u => y)) == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a draft that is there stays, with a write or not
def Draft.with.some(
  -found: Maybe<&2, Draft>,
  -k: List<&2, Bool>,
  m: Maybe<&2, Requests.Content>
) -> {
  Maybe.is_some(&2, Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Draft, Draft.with(found, k, m)) == True{}: Bool}:
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
  a: Maybe<&2, Ledgers.Asked<Requests.Ask>>,
  -found: Maybe<&2, Draft>
) -> {
  Maybe.is_some(&2, Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Draft, Draft.of(w, r, b, n, i, a, found)) == True{}: Bool}:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      +h => When.some(
        String.eq(w2, w),
        Draft.with(
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
  +s: Replicas.Node<Requests.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  found: Maybe<&2, Draft>
) -> {
  Maybe.is_some(&2, Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Draft, Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool}:
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
        Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)
      )(Draft.of.some(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)(h))

# a write of the writer w to the resource gives a draft
def Draft.of.hit(
  w: String,
  -r: Ledgers.Id,
  -b: String,
  -n: Resources.Name,
  -q2: String,
  -t: String,
  -q: Requests.Ask,
  -c: Requests.Content,
  -found: Maybe<&2, Draft>,
  ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Requests.Content>}
) -> {
  Maybe.is_some(
    &2,
    Draft,
    Draft.of(w, r, b, n, Ledgers.Id{w, q2}, Some{Ledgers.Asked{t, q}}, found)
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
      Draft,
      Shared.Bool.when(
        Maybe<&2, Draft>,
        _,
        u => Draft.with(
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
    Maybe<&2, Requests.Content>,
    Spec.Draft.content(r, b, n, q),
    Some{c},
    ec
  ): {
    Maybe.is_some(
      &2,
      Draft,
      Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), _)
    )
      == True{}: Bool
  }
  {==}

# Last.hit once whether the first request is the one looked for is known (bh)
def Last.hit.if(
  +s: Replicas.Node<Requests.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  +i: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  found: Maybe<&2, Draft>,
  q2: String,
  -t: String,
  -q: Requests.Ask,
  -c: Requests.Content,
  bh: Bool,
  ebh: {Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}) == bh: Bool},
  ea: {
    Replicas.Node.asked(
      ~Requests.Ask.machine(),
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Requests.Ask>>
  },
  ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Requests.Content>},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}) == True{}: Bool
  } -> {
    Maybe.is_some(
      &2,
      Draft,
      Draft.last(
        s,
        w,
        r,
        b,
        n,
        rest,
        Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)
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
    Draft,
    Draft.last(
      s,
      w,
      r,
      b,
      n,
      rest,
      Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)
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
        Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found)
      )(
        %Equal.sym(Ledgers.Id, i, Ledgers.Id{w, q2}, Ledgers.Id.is_eq_sound(i, Ledgers.Id{w, q2})(ebh)): {Maybe.is_some(&2, Draft, Draft.of(w, r, b, n, _, Replicas.Node.asked(~Requests.Ask.machine(), s, _), found)) == True{}: Bool}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Requests.Ask>>, Replicas.Node.asked(~Requests.Ask.machine(), s, Ledgers.Id{w, q2}), Some{Ledgers.Asked{t, q}}, ea): {Maybe.is_some(&2, Draft, Draft.of(w, r, b, n, Ledgers.Id{w, q2}, _, found)) == True{}: Bool}
        Draft.of.hit(w, r, b, n, q2, t, q, c, found, ec))

# a write of the writer w among requests gives a draft
def Last.hit(
  +s: Replicas.Node<Requests.Ask>,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  +found: Maybe<&2, Draft>,
  +q2: String,
  -t: String,
  -q: Requests.Ask,
  -c: Requests.Content,
  +ea: {
    Replicas.Node.asked(
      ~Requests.Ask.machine(),
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Requests.Ask>>
  },
  +ec: {Spec.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Requests.Content>}
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, Ledgers.Id{w, q2}) == True{}: Bool
} -> {Maybe.is_some(&2, Draft, Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool}:
  match qs:
    case Nil{}:
      h => Empty.absurd(
        {Maybe.is_some(&2, Draft, found) == True{}: Bool},
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
          Draft.of(w, r, b, n, i, Replicas.Node.asked(~Requests.Ask.machine(), s, i), found),
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
  m: Maybe<&2, Draft>
) -> {
  Maybe.is_some(&2, Draft, m) == True{}: Bool
} -> {Maybe.is_some(&2, Requests.Content, Draft.what(m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{Draft{k, c}}:
      h => {==}

def Spec.Node.draft_some(s, w, r, b, n, q2, t, q, c):
  hc => ea => ec => What.some(
    Draft.last(
      s,
      w,
      r,
      b,
      n,
      Replicas.Wait.of(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      None{}
    )
  )(
    Last.hit(
      s,
      w,
      r,
      b,
      n,
      Replicas.Wait.of(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      None{},
      q2,
      t,
      q,
      c,
      ea,
      ec
    )(hc)
  )

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
