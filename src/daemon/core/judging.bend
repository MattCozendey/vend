import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/reach.bend as Reaches
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ../shared/shared/store.bend as Stores

# Writes
# ------

# trees being written: the root, and the node that holds what was written
type Work is Data:
  Work{state: Basics.Node, root: Maybe<&2, Hashes.Hash>}

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a judge says of one change: refuse it as stale, or take it, with the
# trees that it wrote
type Verdict is Data:
  Verdict.Stale{}
  Verdict.Taken{work: Work}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# s with the words ds as data, when it then holds each of them under its hash
# (none: a slot holds other words). A node reads back what it puts, so what a
# tree or a rope reads after a put never rests on what the store held before
def State.put(s: Basics.Node, +ds: List<&2, List<&2, U32>>) -> Maybe<&2, Basics.Node>:
  +s2 = Basics.State.keep(s, ds)
  Shared.Maybe.when(
    Basics.Node,
    Stores.Store.holds(~Basics.Node, ~Basics.Store.fetch, s2, ds),
    u => Some{s2}
  )

# the work at the root h on the state m
def Work.on(m: Maybe<&2, Basics.Node>, h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Work{s2, h}}

# the work that the new subtree m gives on the state s
def Work.of(s: Basics.Node, m: Maybe<&2, Trees.Put>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Put{h, ws}}:
      Work.on(State.put(s, ws), Some{h})

# w with the key k set to the value x (none: the store lacks a node)
def Work.set(w: Work, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Work>:
  match w:
    case Work{+s, h}:
      Work.of(s, Basics.Node.set(s, h, k, x))

# w with the words ns as data
def Work.keep(w: Work, ns: List<&2, List<&2, U32>>) -> Maybe<&2, Work>:
  match w:
    case Work{s, h}:
      Work.on(State.put(s, ns), h)

# the root of w
def Work.root(w: Work) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{s, h}:
      h

# a verdict that takes the trees of m (none: wait)
def Work.take(m: Maybe<&2, Work>) -> Maybe<&2, Verdict>:
  match m:
    case None{}:
      None{}
    case Some{w}:
      Some{Verdict.Taken{w}}

# w with the line c at the place p in its version vector, unless it holds that
# place or a newer one
def Vector.add(w: Work, +c: Ledgers.Chain, +p: Basics.Place) -> Maybe<&2, Work>:
  match w:
    case Work{+s, +h}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Basics.Place.covered(Basics.Node.vector(s, h, c), p),
        u => Some{Work{s, h}},
        u => Work.set(Work{s, h}, Basics.Key.vector(c), Basics.Place.code(p))
      )

# the line and place of a version vector's entry, from its binding
def Vector.entry(b: Trees.Binding) -> Maybe<&2, Basics.Place>:
  match b:
    case Trees.Binding{Con{4, k}, ws}:
      Maybe.bind(
        &2,
        Ledgers.Chain,
        Basics.Place,
        Basics.Read.whole(Ledgers.Chain, Ledgers.Chain.code.read(k)),
        c => Basics.Place.read(c, ws)
      )
    case _:
      None{}

# w with the entry p in its version vector, when it is of a line other than c
def Vector.add.if(+w: Work, c: Ledgers.Chain, m: Maybe<&2, Basics.Place>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      Some{w}
    case Some{+p}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Ledgers.Chain.is_eq(Basics.Place.chain(p), c),
        u => Some{w},
        u => Vector.add(w, Basics.Place.chain(p), p)
      )

# m with the entries of the bindings bs, other than of the line c, in its
# version vector
def Vector.adds(
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Work>
) -> Maybe<&2, Work>:
  match bs:
    case Nil{}:
      m
    case Con{b, r}:
      Vector.adds(r, c, Maybe.bind(&2, Work, Work, m, w => Vector.add.if(w, c, Vector.entry(b))))

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

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a merge keeps of a resource: the content of one side (none: removed),
# new bytes, or a clash
type Pick is Data:
  Pick.Take{root: Maybe<&2, Ropes.Root>}
  Pick.Make{bytes: Texts.Bytes()}
  Pick.Clash{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Pick.Make{x}
    case Formats.Merged.Clash{}:
      Pick.Clash{}

# the merge of the submodules px and py: the one at the newer version m, if any
def Pick.module(m: Maybe<&2, Ledgers.Id>, px: Pointer, +py: Pointer) -> Pick:
  match m:
    case None{}:
      Pick.Clash{}
    case Some{k}:
      Pick.Make{
        Pointer.show(
          Shared.Bool.when(Pointer, Ledgers.Id.is_eq(k, Pointer.version(py)), u => py, u => px)
        )
      }

# the merge of two submodules that point as x and y
def Pick.pointers(s: Basics.Node, x: Maybe<&2, Pointer>, y: Maybe<&2, Pointer>) -> Pick:
  match x y:
    case Some{+px} Some{+py}:
      Pick.module(Basics.Node.forward(s, Pointer.version(px), Pointer.version(py)), px, py)
    case _ _:
      Pick.Clash{}

# the merge of x and y, two changes of b, in the format f
def Pick.format(
  f: Formats.Format,
  s: Basics.Node,
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Pick:
  match f:
    case Formats.Format.Leaf{Formats.Leaf.Module{}}:
      Pick.pointers(s, Pointer.read(x), Pointer.read(y))
    case g:
      Pick.bytes(Formats.Format.merge(g, b, x, y))

# the merge of the bytes x and y, two changes of mb, in the format f (none: the
# node does not hold all of them yet)
def Pick.read(
  f: Formats.Format,
  s: Basics.Node,
  mb: Maybe<&2, Texts.Bytes()>,
  mx: Maybe<&2, Texts.Bytes()>,
  my: Maybe<&2, Texts.Bytes()>
) -> Maybe<&2, Pick>:
  match mb mx my:
    case Some{b} Some{x} Some{y}:
      Some{Pick.format(f, s, b, x, y)}
    case u v w:
      None{}

# the bytes of the base b of a merge (none: the node does not hold them yet):
# no base is no bytes
def Pick.base(s: Basics.Node, b: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  match b:
    case None{}:
      Some{[]}
    case Some{r}:
      Basics.Root.bytes(s, Some{r})

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f (none: wait for its bytes)
def Pick.both(
  f: Formats.Format,
  +s: Basics.Node,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Pick>:
  match o t:
    case Some{x} Some{y}:
      Pick.read(f, s, Pick.base(s, b), Basics.Root.bytes(s, Some{x}), Basics.Root.bytes(s, Some{y}))
    case _ _:
      Some{Pick.Clash{}}

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base, ours when theirs is the base or both
# agree, else both merged (none: wait for their bytes). So a merge never loses
# a change that only one side made
def Pick.merge(
  f: Formats.Format,
  s: Basics.Node,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Pick>:
  Shared.Bool.when(
    Maybe<&2, Pick>,
    Basics.Roots.same(o, b),
    u => Some{Pick.Take{t}},
    u => Shared.Bool.when(
      Maybe<&2, Pick>,
      List.any.if(v => Basics.Roots.same(o, t), Basics.Roots.same(t, b)),
      w => Some{Pick.Take{o}},
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
        Maybe.is_some(&2, Ropes.Root, Basics.Res.read(ws)),
        u => Basics.Read.whole(Resources.Name, Resources.Name.code.read(k)),
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
def Res.names(s: Basics.Node, h: Maybe<&2, Hashes.Hash>) -> List<&2, Resources.Name>:
  Res.of.bindings(Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, h))

# the key of the resource n
def Name.key(n: Resources.Name) -> List<&2, Bool>:
  Tries.Trie.text(Resources.Name.show(n))

# the resources that ours (the tree h) and theirs (ht) may hold differently,
# once each: a walk of both trees skips what they share, and where both hold
# the same bytes a merge keeps them (Format.merge_same)
def Merge.names(
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>
) -> List<&2, Resources.Name>:
  Tries.Trie.unique(
    ~Resources.Name,
    ~Name.key,
    Res.of.bindings(Trees.Tree.diff(~Basics.Node, ~Basics.Store.fetch, s, h, ht)),
    Tries.Trie.new(Unit)
  )

# the groups of a store tree, as a graph
type Groups is Data:
  Groups{state: Basics.Node, root: Maybe<&2, Hashes.Hash>}

# the members of m in the groups g, when it is a group
def Group.succ(g: Groups, m: Basics.Member) -> List<&2, Basics.Member>:
  match g m:
    case Groups{s, h} Basics.Member.Node{n}:
      []
    case Groups{s, h} Basics.Member.Group{x}:
      Maybe.default(&2, List<&2, Basics.Member>, Basics.Members.in(s, h, x), [])

# the names of the groups in the store tree whose root is h
def Group.names(s: Basics.Node, h: Maybe<&2, Hashes.Hash>) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, String>,
      Basics.Node.get(s, h, Basics.Key.groups()),
      ws => Basics.Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
    ),
    []
  )

# the groups of the names ns, as members
def Group.of.names(ns: List<&2, String>) -> List<&2, Basics.Member>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Basics.Member.Group{n} <> Group.of.names(r)

# every group of the groups g, as a member
def Group.all(g: Groups) -> List<&2, Basics.Member>:
  match g:
    case Groups{s, h}:
      Group.of.names(Group.names(s, h))

# m is a member of the group g of the store tree h, or of a group inside g
def Group.is_inside(s: Basics.Node, h: Maybe<&2, Hashes.Hash>, m: Basics.Member, g: String) -> Bool:
  Reaches.Reach.in(
    ~Basics.Member,
    ~Groups,
    ~Basics.Member.is_eq,
    ~Group.succ,
    ~Group.all,
    Groups{s, h},
    Basics.Member.Group{g},
    m
  )

# the nodes among the members ms
def Group.nodes.of(ms: List<&2, Basics.Member>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Basics.Member.Node{n}, r}:
      n <> Group.nodes.of(r)
    case Con{Basics.Member.Group{g}, r}:
      Group.nodes.of(r)

# the nodes that each group of gs names, as they come
def Group.named.all(+g: Groups, gs: List<&2, Basics.Member>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{m, r}:
      List.append(&2, String, Group.nodes.of(Group.succ(g, m)), Group.named.all(g, r))

# the nodes that some group of gs names
def Group.named(g: Groups, gs: List<&2, Basics.Member>) -> List<&2, String>:
  Tries.Trie.unique(~String, ~Tries.Trie.text, Group.named.all(g, gs), Tries.Trie.new(Unit))

# the nodes of ns that are inside the group g of the store tree h
def Group.inside(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, String>,
  +g: String
) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      List.filter.put(
        String,
        n,
        Group.inside(s, h, rest, g),
        Group.is_inside(s, h, Basics.Member.Node{n}, g)
      )

# the nodes inside the group g of the store tree h, each once: the nodes that
# own what g owns
def Group.nodes(+s: Basics.Node, +h: Maybe<&2, Hashes.Hash>, g: String) -> List<&2, String>:
  +gs = {Groups{s, h}: Groups}
  Group.inside(s, h, Group.named(gs, Group.all(gs)), g)

# the member m of a new set of the group g makes g contain itself
def Group.loops(s: Basics.Node, h: Maybe<&2, Hashes.Hash>, +g: String, m: Basics.Member) -> Bool:
  match m:
    case Basics.Member.Node{n}:
      False{}
    case Basics.Member.Group{+x}:
      List.any.if(u => Group.is_inside(s, h, Basics.Member.Group{g}, x), String.eq(x, g))

# some member of ms makes the group g of the store tree h contain itself
def Group.loops.any(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  ms: List<&2, Basics.Member>
) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, rest}:
      List.any.if(u => Group.loops.any(s, h, g, rest), Group.loops(s, h, g, m))

# Judging
# -------
# The owners of a line give each request one outcome, in a step: take it, with
# the content that the line holds after it, or refuse it as stale. A step
# waits while a version that a request names is not decided yet, or the node
# lacks a node of a tree that it reads.

# the verdict that the outcome m of a version gives a request that names it:
# take it when it is a version, refuse it when it is stale, else wait
def Judge.ready.of(m: Maybe<&2, Basics.Out>) -> Maybe<&2, Bool>:
  match m:
    case Some{Basics.Out.Taken{n}}:
      Some{True{}}
    case Some{Basics.Out.Stale{}}:
      Some{False{}}
    case None{}:
      None{}

# the verdict of the version v, for a request that names it
def Judge.ready(s: Basics.Node, v: Ledgers.Id) -> Maybe<&2, Bool>:
  Judge.ready.of(Basics.Node.out(s, v))

# the verdict of the version m, if any
def Judge.ready_maybe(s: Basics.Node, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      Some{True{}}
    case Some{v}:
      Judge.ready(s, v)

# the verdict on the content c: its version must be one
def Judge.content(s: Basics.Node, c: Basics.Content) -> Maybe<&2, Bool>:
  match c:
    case Basics.Content.Root{x}:
      Some{True{}}
    case Basics.Content.Of{w}:
      Judge.ready(s, w)

# a refusal
def Judge.refuse() -> Maybe<&2, Verdict>:
  Some{Verdict.Stale{}}

# the verdict m, then k when m takes
def Judge.then(
  m: Maybe<&2, Bool>,
  k: Unit -> Maybe<&2, Verdict>
) -> Maybe<&2, Verdict>:
  match m:
    case Some{True{}}:
      k(Unit{})
    case Some{False{}}:
      Judge.refuse()
    case None{}:
      None{}

# k when b holds, else a refusal
def Judge.when(b: Bool, k: Unit -> Maybe<&2, Verdict>) -> Maybe<&2, Verdict>:
  Shared.Bool.when(Maybe<&2, Verdict>, b, k, u => Judge.refuse())

# the root that the content c gives the resource n (none: the version holds
# none)
def Content.root(+s: Basics.Node, n: Resources.Name, c: Basics.Content) -> Maybe<&2, Ropes.Root>:
  match c:
    case Basics.Content.Root{x}:
      Some{x}
    case Basics.Content.Of{w}:
      Basics.Res.root(s, Basics.Node.root_of(s, Some{w}), n)

# the root that the content c gives the resource n, or that it gives none
# (none: the node lacks a node of the version's tree)
def Content.find(
  +s: Basics.Node,
  n: Resources.Name,
  c: Basics.Content
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  match c:
    case Basics.Content.Root{x}:
      Some{Some{x}}
    case Basics.Content.Of{w}:
      Basics.Res.find(s, Basics.Node.root_of(s, Some{w}), n)

# the verdict on a write of the resource n since base, with the content c, at
# the tree h: take it when n holds at h what it held at base. It waits for a
# node that it lacks: it does not refuse on what it cannot read
def Judge.write(
  +s: Basics.Node,
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Basics.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Judge.ready_maybe(s, base),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Verdict,
        Basics.Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Verdict,
          Basics.Res.find(s, Basics.Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Verdict,
            Content.find(s, n, c),
            m => Judge.when(
              Basics.Roots.same(a, b),
              x => Work.take(Work.set(Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)))
            )
          )
        )
      )
    )
  )

# the value of the clash that the merge of the version f opened (a settled
# clash holds no words)
def Clash.code(f: Ledgers.Id) -> List<&2, U32>:
  Ledgers.Id.code(f, [])

# the clash that the merge of the version f opened in the resource n is open
# in the tree h
def Clash.open(s: Basics.Node, h: Maybe<&2, Hashes.Hash>, n: Resources.Name, f: Ledgers.Id) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    Basics.Node.get(s, h, Basics.Key.clash(n)),
    Some{Clash.code(f)}
  )

# the version that the request m merged, when m is a merge on the branch b of
# the store r
def Merge.from_on(
  m: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  r: Ledgers.Id,
  b: String
) -> Maybe<&2, Ledgers.Id>:
  match m:
    case Some{Ledgers.Asked{t, Basics.Ask.On{st, Some{x}, Basics.Change.Merge{f}}}}:
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
  s: Basics.Node,
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
        Basics.Node.find(s, h, Basics.Key.clash(n)),
        x => Some{
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            x,
            Some{Clash.code(f)}
          )
        }
      )

# the trees of a resolve of the resource n with the root m, in the tree h:
# the resource holds m, and its clash is shut (its key holds no request)
def Resolve.work(
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  m: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Work>:
  Maybe.bind(
    &2,
    Work,
    Work,
    Work.set(Work{s, h}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Work.set(y, Basics.Key.clash(n), [])
  )

# the verdict on a resolve of the resource n, which the merge k left in clash
# on the branch b of the store r, with the content c, at the tree h
def Judge.resolve(
  +s: Basics.Node,
  r: Ledgers.Id,
  b: String,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Basics.Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Judge.ready(s, k),
    u => Judge.then(
      Judge.content(s, c),
      w => Maybe.bind(
        &2,
        Bool,
        Verdict,
        Clash.find(s, h, n, Merge.from_on(Basics.Node.asked(s, k), r, b)),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Verdict,
          Content.find(s, n, c),
          m => Judge.when(open, x => Work.take(Resolve.work(s, h, n, m)))
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
  p: Pick,
  w: Work
) -> Maybe<&2, Work>:
  match p:
    case Pick.Take{m}:
      Work.set(w, Basics.Key.res(n), Basics.Res.code(m))
    case Pick.Make{x}:
      +rp = Basics.Bytes.rope(x)
      Maybe.bind(
        &2,
        Work,
        Work,
        Work.keep(w, Ropes.Put.nodes(rp)),
        w2 => Work.set(w2, Basics.Key.res(n), Basics.Res.code(Some{Ropes.Put.root(rp)}))
      )
    case Pick.Clash{}:
      Maybe.bind(
        &2,
        Work,
        Work,
        Work.set(w, Basics.Key.res(n), Basics.Res.code(o)),
        y => Work.set(y, Basics.Key.clash(n), Clash.code(f))
      )

# w with the resource n merged: what the merge of the base b, ours o and theirs
# t (of the version f) keeps (none: wait for a node)
def Merge.one(
  s: Basics.Node,
  f: Ledgers.Id,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  w: Work
) -> Maybe<&2, Work>:
  Maybe.bind(
    &2,
    Pick,
    Work,
    Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    p => Merge.put(f, n, o, p, w)
  )

# m with each resource of ns merged, over the base hb, ours ho and theirs ht
# (of the version f)
def Merge.all(
  +s: Basics.Node,
  +f: Ledgers.Id,
  ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Work>
) -> Maybe<&2, Work>:
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
          Work,
          Work,
          m,
          w => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Work,
            Basics.Res.find(s, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Work,
              Basics.Res.find(s, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Work,
                Basics.Res.find(s, ht, n),
                x => Merge.one(s, f, n, b, o, x, w)
              )
            )
          )
        )
      )

# the request of the version v, as a version
def Version.some(v: Basics.Version) -> Maybe<&2, Ledgers.Id>:
  Some{Basics.Version.id(v)}

# the version of the number n of the line at the tip t
def Version.in(s: Basics.Node, n: U32, t: Basics.Tip) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(&2, Basics.Version, Ledgers.Id, Basics.Line.version(s, t, n), v => Version.some(v))

# the version at the place p
def Version.at(+s: Basics.Node, p: Basics.Place) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Basics.Place{c, n}:
      Maybe.bind(&2, Basics.Tip, Ledgers.Id, Basics.Node.tip(s, c), t => Version.in(s, n, t))

# the newer of two versions that both sides of a merge came from: a, a
# version of our line that theirs came from, and the version at the place p of
# their line cf that ours came from. a is the newer one when it came from the
# other
def Base.pick(
  +s: Basics.Node,
  cf: Ledgers.Chain,
  ma: Maybe<&2, Ledgers.Id>,
  mp: Maybe<&2, Basics.Place>
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
        Basics.Place.covered(Basics.Node.vector(s, Basics.Node.root_of(s, Some{a}), cf), p),
        u => Some{a},
        u => Version.at(s, p)
      )

# the base of a merge of from into the line c, whose tree is h: from itself
# when it is of c; else the newest version that both came from, by the version
# vectors of both sides (the version of c that from came from, or the version
# of from's line that h came from)
def Merge.base(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    Basics.Place,
    Ledgers.Id,
    Basics.Node.place(s, from),
    +pf => Shared.Bool.when(
      Maybe<&2, Ledgers.Id>,
      Ledgers.Chain.is_eq(Basics.Place.chain(pf), c),
      u => Some{from},
      u => Base.pick(
        s,
        Basics.Place.chain(pf),
        Maybe.bind(
          &2,
          Basics.Place,
          Ledgers.Id,
          Basics.Node.vector(s, Basics.Node.root_of(s, Some{from}), c),
          w => Version.at(s, w)
        ),
        Basics.Node.vector(s, h, Basics.Place.chain(pf))
      )
    )
  )

# m with the version v, of a line other than c, in its version vector: its
# vector, and its own place
def Vector.joined(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  m: Maybe<&2, Work>
) -> Maybe<&2, Work>:
  Maybe.bind(
    &2,
    Work,
    Work,
    Vector.adds(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, Basics.Node.root_of(s, Some{v})),
      c,
      m
    ),
    w => Vector.add.if(w, c, Basics.Node.place(s, v))
  )

# the trees of a merge of from into the line c, whose tree is h
def Merge.work(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work>:
  +ht = Basics.Node.root_of(s, Some{from})
  Vector.joined(
    s,
    c,
    from,
    Merge.all(
      s,
      from,
      Merge.names(s, h, ht),
      Basics.Node.root_of(s, Merge.base(s, c, from, h)),
      h,
      ht,
      Some{Work{s, h}}
    )
  )

# the trees of a move of the line c, whose tree is h, to the version to: to's
# tree, with what the line came from added to its version vector
def Move.work(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +to: Ledgers.Id,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work>:
  Vector.joined(
    s,
    c,
    to,
    Vector.adds(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, h),
      c,
      Some{Work{s, Basics.Node.root_of(s, Some{to})}}
    )
  )

# the first tree of a branch made at the version m, if any, of the line c: its
# tree, with what it came from in its version vector
def Make.branch(+s: Basics.Node, c: Ledgers.Chain, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      Some{Work{s, None{}}}
    case Some{+v}:
      Vector.joined(s, c, v, Some{Work{s, Basics.Node.root_of(s, Some{v})}})

# the store tree h with the group g, of the members ms, and its name among the
# names of its groups
def Group.work(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  ms: List<&2, Basics.Member>
) -> Maybe<&2, Work>:
  +ns = Group.names(s, h)
  Maybe.bind(
    &2,
    Work,
    Work,
    Work.set(Work{s, h}, Basics.Key.group(g), Basics.Members.code(ms, [])),
    +w => Shared.Bool.when(
      Maybe<&2, Work>,
      List.contains(~String, ~String.eq, ns, g),
      u => Some{w},
      u => Work.set(w, Basics.Key.groups(), Ledgers.Owners.code(g <> ns, []))
    )
  )

# the owners os are the nodes ns, and there is one
def Own.fits(+os: List<&2, String>, ns: List<&2, String>) -> Bool:
  List.all.if(u => Ledgers.Owners.is_eq(os, ns), Bool.not(List.is_empty(&2, String, os)))

# the first tip of a new branch, and the node that holds it
type Made is Data:
  Made{tip: Basics.Tip, node: Basics.Node}

# the first tip t of a branch, once the trees of m hold it
def Made.put(t: Basics.Tip, m: Maybe<&2, Work>) -> Maybe<&2, Made>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, l}}:
      Some{Made{t, s}}

# the first tip of a new branch, from its first content (the root of start):
# no log, no version, and the owners os of its store now
def Make.first(start: Maybe<&2, Work>, os: List<&2, String>) -> Maybe<&2, Made>:
  match start:
    case None{}:
      None{}
    case Some{+w}:
      +t = {Basics.Tip{Work.root(w), None{}, 0, os}: Basics.Tip}
      Made.put(t, Work.keep(w, [Basics.Tip.words(t)]))

# the store tree in which an Own of the line l, at the content h, reads its
# group: a store reads its own content; a branch, the content of the version
# at of its store
def Own.tree(
  s: Basics.Node,
  l: Maybe<&2, String>,
  at: Maybe<&2, Ledgers.Id>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Hashes.Hash>:
  match l at:
    case Some{b} Some{v}:
      Basics.Node.root_of(s, Some{v})
    case x y:
      h

# the version at is a version of the store r: at the place m
def Own.at(r: Ledgers.Id, m: Maybe<&2, Basics.Place>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      None{}
    case Some{Basics.Place{c, n}}:
      Some{Ledgers.Chain.is_eq(c, Ledgers.Chain{r, None{}})}

# an Own of the line l of the store r may name the version at: a store reads
# its own content; a branch names a version of its store (none: wait for it)
def Own.ok(
  s: Basics.Node,
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
      Own.at(r, Basics.Node.place(s, v))

# the node holds the members of each group of ns of the store tree h
def Groups.held.all(+s: Basics.Node, +h: Maybe<&2, Hashes.Hash>, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, r}:
      List.all.if(
        u => Groups.held.all(s, h, r),
        Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, Basics.Node.find(s, h, Basics.Key.group(n)))
      )

# the node holds the groups of the store tree h: their names, and the members
# of each. Only then does it know which nodes are inside a group
def Groups.held(+s: Basics.Node, +h: Maybe<&2, Hashes.Hash>) -> Bool:
  List.all.if(
    u => Groups.held.all(s, h, Group.names(s, h)),
    Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, Basics.Node.find(s, h, Basics.Key.groups()))
  )

# Own.takes once whether the Own may name its version is known (k), in the
# store tree h (none: wait for the groups)
def Own.takes.at(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  g: String,
  os: List<&2, String>,
  k: Bool
) -> Maybe<&2, Bool>:
  match k:
    case False{}:
      Some{False{}}
    case True{}:
      Shared.Maybe.when(Bool, Groups.held(s, h), u => Some{Own.fits(os, Group.nodes(s, h, g))})

# whether the owners of the line l of the store r take an Own of the group g
# with the owners os, at the tree h: os are the nodes inside g in the store
# tree that it names (Own.tree; none: wait for its step, or for the groups)
def Own.takes(
  +s: Basics.Node,
  r: Ledgers.Id,
  +l: Maybe<&2, String>,
  g: String,
  +at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Bool>:
  Maybe.bind(
    &2,
    Bool,
    Bool,
    Own.ok(s, r, l, at),
    k => Own.takes.at(s, Own.tree(s, l, at, h), g, os, k)
  )

# the verdict on an Own of the line l of the store r: when its owners take it
# (Own.takes), its owner group is g
def Own.change(
  +s: Basics.Node,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Own.takes(s, r, l, g, at, os, h),
    u => Work.take(Work.set(Work{s, h}, Basics.Key.owner(), Codes.Code.text(g, [])))
  )

# the node s holds each node of the trees whose roots are a and b
def Whole.both(+s: Basics.Node, a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  List.all.if(
    u => Trees.Tree.whole(~Basics.Node, ~Basics.Store.fetch, s, b),
    Trees.Tree.whole(~Basics.Node, ~Basics.Store.fetch, s, a)
  )

# k when the node holds the whole of the trees that a walk reads (b), else
# wait: a merge or a move acts on a whole tree, never on the part that the
# node holds
def Judge.whole(b: Bool, k: Unit -> Maybe<&2, Verdict>) -> Maybe<&2, Verdict>:
  match b:
    case True{}:
      k(Unit{})
    case False{}:
      None{}

# the verdict on the change c of the line l of the store r, at the content h,
# when the owners of the line are os
def Judge.change(
  +s: Basics.Node,
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Basics.Change,
  +h: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>
) -> Maybe<&2, Verdict>:
  match l c:
    case None{} Basics.Change.Group{+g, +ms}:
      Judge.when(Bool.not(Group.loops.any(s, h, g, ms)), u => Work.take(Group.work(s, h, g, ms)))
    case None{} Basics.Change.Key{n, k}:
      Work.take(Work.set(Work{s, h}, Basics.Key.seal(n), Hashes.Hash.code(k, [])))
    case w Basics.Change.Own{g, at, os2}:
      Own.change(s, r, w, g, at, os2, h)
    case Some{b} Basics.Change.Write{n, base, c2}:
      Judge.write(s, n, base, c2, h)
    case Some{+b} Basics.Change.Resolve{k, n, c2}:
      Judge.resolve(s, r, b, k, n, c2, h)
    case Some{+b} Basics.Change.Merge{+from}:
      Judge.then(
        Judge.ready(s, from),
        u => Judge.whole(
          Whole.both(s, h, Basics.Node.root_of(s, Some{from})),
          v => Work.take(Merge.work(s, Basics.Line.chain(r, Some{b}), from, h))
        )
      )
    case Some{+b} Basics.Change.Move{+to}:
      Judge.then(
        Judge.ready(s, to),
        u => Judge.whole(
          Whole.both(s, h, Basics.Node.root_of(s, Some{to})),
          v => Work.take(Move.work(s, Basics.Line.chain(r, Some{b}), to, h))
        )
      )
    case w c3:
      Judge.refuse()
