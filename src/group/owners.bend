import Base
import ../branch/merges.bend as Merges
import ../shared/replica.bend as Replicas
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/keyset.bend as KeySets
import ../shared/shared/shared/reach.bend as Reaches
import ../shared/shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/tree.bend as Trees
import ../shared/vend.bend as Vend
import ../writer/requests.bend as Requests

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
  Shared.List.filter_map(~Trees.Binding, ~Group, ~Group.read, xs)

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
def Groups.in(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, List<&2, Group>>:
  Maybe.map(&2, List<&2, Trees.Binding>, List<&2, Group>, Groups.of, Vend.Tree.range(~d, l, h, [2]))

# the nodes of the group g in the tree whose root is h, each once: the nodes
# that own what g owns. A clear def: it walks the tree
def Group.nodes(~d: Vend.Led(), l: Vend.L(d), h: Maybe<&2, Hashes.Hash>, +g: String) -> Maybe<&2, List<&2, String>>:
  Maybe.map(&2, List<&2, Group>, List<&2, String>, gs => Group.nodes.of(gs, g), Groups.in(~d, l, h))

# the groups gs with the group g of the members ms in place of any group g
def Groups.set(gs: List<&2, Group>, +g: String, +ms: List<&2, Requests.Member>) -> List<&2, Group>:
  match gs:
    case Nil{}:
      [Group{g, ms}]
    case Con{Group{+n, ns}, +rest}:
      Shared.Bool.when(
        List<&2, Group>,
        String.eq(n, g),
        u => Groups.set(rest, g, ms),
        u => Group{n, ns} <> Groups.set(rest, g, ms)
      )

# Group.act once the groups gs of the tree h are known: stale when the group
# g with the members ms would reach itself; else the tree h with g set. The
# groups after it are gs with g set, so the act reads only the tree that the
# ledger holds
def Group.act.of(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  +ms: List<&2, Requests.Member>,
  gs: List<&2, Group>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Crits.Dict.has(Unit, Group.reach(Groups.set(gs, g, ms), g), Group.key(g)),
    u => Some{Replicas.Act.Stale{}},
    u => Vend.Act.put(
      None{},
      [],
      Replicas.Tree.put(~Requests.Ask.machine(), ~d, l, h, Key.group(g), Some{Requests.Members.code(ms, [])})
    )
  )

# what a group g with the members ms does, at the tip t of a store: the tree
# of the store holds the members of g; a group that would reach itself is
# refused (none: wait for the whole tree)
def Group.act(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  t: Replicas.Tip,
  +g: String,
  +ms: List<&2, Requests.Member>
) -> Maybe<&2, Replicas.Act>:
  +h = Replicas.Tip.content(t)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Vend.Tree.whole(~d, l, h),
    u => Maybe.bind(&2, List<&2, Group>, Replicas.Act, Groups.in(~d, l, h), gs => Group.act.of(~d, l, h, g, ms, gs)),
    u => None{}
  )

# the tree in which an Own reads its group, at the tip t: the tree of the
# source that comes with it, else the tree of the line itself
def Own.tree(t: Replicas.Tip, at: Maybe<&2, Requests.Source>) -> Maybe<&2, Hashes.Hash>:
  match at:
    case None{}:
      Replicas.Tip.content(t)
    case Some{s}:
      Vend.Source.root(s)

# what an Own of the group g with the owners os does, at the tip t: it is
# taken when os are the nodes of g in the tree that it reads, and there is
# one at least; the line then records g as its owner group, and os own its
# next step. Else it is stale (none: wait for the whole tree)
def Own.act(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +g: String,
  at: Maybe<&2, Requests.Source>,
  +os: List<&2, String>
) -> Maybe<&2, Replicas.Act>:
  +h = Own.tree(t, at)
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Vend.Tree.whole(~d, l, h),
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
      v => Vend.Act.put(
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
  ~d: Vend.Led(),
  l: Vend.L(d),
  t: Replicas.Tip,
  b: Maybe<&2, String>,
  i: Ledgers.Id,
  ch: Requests.Change
) -> Maybe<&2, Replicas.Act>:
  match b ch:
    case Some{x} Requests.Change.Write{n, base, c}:
      Vend.Write.act(~d, l, t, n, base, c)
    case Some{x} Requests.Change.Resolve{k, n, c}:
      Merges.Resolve.act(~d, l, t, k, n, c)
    case Some{x} Requests.Change.Merge{from, base}:
      Merges.Merge.act(~d, l, t, i, from, base)
    case Some{x} Requests.Change.Move{to}:
      Vend.Move.act(~d, l, to)
    case Some{x} Requests.Change.Mark{m, text}:
      Some{Replicas.Act.Label{m}}
    case None{} Requests.Change.Branch{n, at}:
      Vend.Branch.act(~d, l, t, n, at)
    case None{} Requests.Change.Group{g, ms}:
      Group.act(~d, l, t, g, ms)
    case None{} Requests.Change.Key{n, k}:
      Vend.Key.act(~d, l, t, n, k)
    case y Requests.Change.Own{g, at, os}:
      Own.act(~d, l, t, g, at, os)
    case y z:
      Some{Replicas.Act.Stale{}}

# what the request q of the ID i does at the tip t of the line c: a change of
# the line of its store that c is; a request that starts a store, or that is
# of another line, is refused
def Ask.act(
  ~d: Vend.Led(),
  l: Vend.L(d),
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

# Owners that follow their group
# ------------------------------

# the name of the owner group of the line whose tip is t, or that it has none
# (none: l lacks a node, so a read cannot tell)
def Tip.group(~d: Vend.Led(), l: Vend.L(d), t: Replicas.Tip) -> Maybe<&2, Maybe<&2, String>>:
  Replicas.Tip.known(
    ~String,
    ~Codes.Code.text,
    ~Codes.Code.text.read,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, Replicas.Tip.content(t), Key.owner())
  )

# what go gives of the value of m, or no request when m holds none
def Due.then(~A: Data, m: Maybe<&2, A>, go: A -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>) -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>:
  match m:
    case None{}:
      Some{None{}}
    case Some{x}:
      go(x)

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
# (none: l lacks a node, so it cannot tell)
def Own.due.at(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  c: Ledgers.Line,
  +t: Replicas.Tip,
  +ts: Replicas.Tip
) -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>:
  Maybe.bind(
    &2,
    Maybe<&2, String>,
    Maybe<&2, Replicas.Request<Requests.Ask>>,
    Tip.group(~d, l, t),
    mg => Due.then(
      ~String,
      mg,
      +g => Maybe.bind(
        &2,
        Maybe<&2, Ledgers.Id>,
        Maybe<&2, Replicas.Request<Requests.Ask>>,
        Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, ts),
        mv => Due.then(
          ~Ledgers.Id,
          mv,
          v => Maybe.map(
            &2,
            List<&2, String>,
            Maybe<&2, Replicas.Request<Requests.Ask>>,
            ns => Own.due.of(c, t, ts, g, ns, v),
            Group.nodes(~d, l, Replicas.Tip.content(ts), g)
          )
        )
      )
    )
  )

# the request that a node asks by itself for the line c: when the nodes of
# the owner group of c, in the newest tree of its store, are not the owners
# of c, the request that makes them the owners. So a change of a group
# changes the owners of each line that it owns, by the next decided step (some
# none: no request, or the line or its store has no top among hs yet; none: l
# lacks a node, so it cannot tell)
def Own.due(
  ~d: Vend.Led(),
  +hs: Replicas.Tops(),
  +l: Vend.L(d),
  +c: Ledgers.Line
) -> Maybe<&2, Maybe<&2, Replicas.Request<Requests.Ask>>>:
  Due.then(
    ~Replicas.Tip,
    Replicas.Tops.tip(hs, c),
    +t => Due.then(
      ~Replicas.Tip,
      Replicas.Tops.tip(hs, Replicas.Root.line(Ledgers.Line.root(c))),
      ts => Own.due.at(~d, l, c, t, ts)
    )
  )

# the lines whose newest tips Own.due reads for the line c: c, and the root
# line of its store once c has a top among hs (Replicas.Kernel.Reads)
def Own.deps(+hs: Replicas.Tops(), +c: Ledgers.Line) -> List<&2, Ledgers.Line>:
  Shared.Bool.when(
    List<&2, Ledgers.Line>,
    Maybe.is_some(&2, Replicas.Tip, Replicas.Tops.tip(hs, c)),
    u => [c, Replicas.Root.line(Ledgers.Line.root(c))],
    u => [c]
  )

# the lines that read the line m (Own.deps): m, and when it is the root line of
# a store, each line under that root that has a top among hs
def Own.watch.one(+hs: Replicas.Tops(), m: Ledgers.Line) -> List<&2, Ledgers.Line>:
  match m:
    case Ledgers.Line{+st, None{}}:
      Ledgers.Line{st, None{}} <> Replicas.Tops.under(hs, st)
    case Ledgers.Line{st, Some{b}}:
      [Ledgers.Line{st, Some{b}}]

# the lines that read a line among ms (Replicas.Kernel.Covers), each once or
# more
def Own.watch(+hs: Replicas.Tops(), ms: List<&2, Ledgers.Line>) -> List<&2, Ledgers.Line>:
  match ms:
    case Nil{}:
      []
    case Con{m, rest}:
      List.append(&2, Ledgers.Line, Own.watch.one(hs, m), Own.watch(hs, rest))
