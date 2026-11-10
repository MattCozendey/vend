import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/reach.bend as Reaches
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./basics.bend as Basics
import ./judging.bend as Judging
import ./voting.bend as Voting
import ../replica/impl.bend as Replicas
import ./stepping.bend as Stepping

# Reads
# -----
# Each read is of the node's own state: its ledger, and its heads.

# the root of the content of the line c now (none: the empty tree, or the node
# does not follow c)
def Chain.root(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(&2, Replicas.Tip, Hashes.Hash, Replicas.Node.tip(~Basics.Ask.machine(), s, c), t => Replicas.Tip.content(t))

# the root of the content of the store r now
def Store.root(s: Replicas.Node<Basics.Ask>, r: Ledgers.Id) -> Maybe<&2, Hashes.Hash>:
  Chain.root(s, Ledgers.Chain{r, None{}})

# the newest version of a line at the tip t, if it has one
def Line.newest(+s: Replicas.Node<Basics.Ask>, +t: Replicas.Tip) -> Maybe<&2, Ledgers.Id>:
  +n = Replicas.Tip.count(t)
  Shared.Maybe.when(
    Ledgers.Id,
    Bool.not(U32.is_eq(n, 0)),
    u => Judging.Version.in(s, U32.sub(n, 1), t)
  )

# the newest version of the line c, if it has one
def Chain.newest(+s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(&2, Replicas.Tip, Ledgers.Id, Replicas.Node.tip(~Basics.Ask.machine(), s, c), t => Line.newest(s, t))

# the newest version of the branch b of the store r, if b has one
def Node.head(s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Replicas.Line.chain(r, Some{b}))

# the newest version of the store r
def Store.head(s: Replicas.Node<Basics.Ask>, r: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Ledgers.Chain{r, None{}})

# the version m, when it is there, then rest
def Ids.put(m: Maybe<&2, Ledgers.Id>, rest: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match m:
    case Some{i}:
      i <> rest
    case None{}:
      rest

# the k versions of a line at the tip t from the number n, in order
def Line.versions(k: Nat, +s: Replicas.Node<Basics.Ask>, +t: Replicas.Tip, +n: U32) -> List<&2, Ledgers.Id>:
  match k:
    case 0n:
      []
    case 1n+p:
      Ids.put(Judging.Version.in(s, n, t), Line.versions(p, s, t, U32.inc(n)))

# k versions of the line whose tip is m, from the number n, in order
def Versions.of(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Tip>, n: U32, k: Nat) -> List<&2, Ledgers.Id>:
  match m:
    case None{}:
      []
    case Some{t}:
      Line.versions(k, s, t, n)

# k versions of the branch b of the store r, from the number n, in order: a
# reader asks for a part of a history, and pays for that part
def Node.versions(
  +s: Replicas.Node<Basics.Ask>,
  r: Ledgers.Id,
  b: String,
  n: U32,
  k: Nat
) -> List<&2, Ledgers.Id>:
  Versions.of(s, Replicas.Node.tip(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})), n, k)

# the version before the number n of the line whose tip is m, if any
def Version.before(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Tip>, +n: U32) -> Maybe<&2, Ledgers.Id>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Shared.Maybe.when(
        Ledgers.Id,
        Bool.not(U32.is_eq(n, 0)),
        u => Judging.Version.in(s, U32.sub(n, 1), t)
      )

# the owners of the next step of the line l of the store r
def Node.owners(+s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, l: Maybe<&2, String>) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, String>,
      Replicas.Node.tip(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)),
      t => Some{Replicas.Tip.owners(t)}
    ),
    []
  )

# the request i is a version: a step took it
def Node.is_version(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id) -> Bool:
  Maybe.is_some(&2, Replicas.Version, Basics.Node.made(s, i))

# the version at the point p, if there is one
def Node.version(s: Replicas.Node<Basics.Ask>, p: Basics.Point) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Basics.Point.At{+v}:
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.is_version(s, v), u => Some{v}, u => None{})
    case Basics.Point.Head{r, b}:
      Node.head(s, r, b)
    case Basics.Point.Mark{r, b, m}:
      Replicas.Chain.mark(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b}), m)

# the root of the content of the resource n at the version m, if it holds it
def Res.root_at(
  +s: Replicas.Node<Basics.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(
    &2,
    Ledgers.Id,
    Ropes.Root,
    m,
    v => Basics.Res.root(s, Basics.Node.root_of(s, Some{v}), n)
  )

# the bytes of the resource n at the version m, if it holds them
def Res.at(
  +s: Replicas.Node<Basics.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Texts.Bytes()>:
  Basics.Root.bytes(s, Res.root_at(s, n, m))

# the bytes of the resource n at the point p, if it is there
def Node.content(+s: Replicas.Node<Basics.Ask>, n: Resources.Name, p: Basics.Point) -> Maybe<&2, Texts.Bytes()>:
  Res.at(s, n, Node.version(s, p))

# the members of the group g of the store r, if g exists
def Node.members(+s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, g: String) -> Maybe<&2, List<&2, Basics.Member>>:
  Basics.Members.in(s, Store.root(s, r), g)

# the nodes inside the group g of the store r
def Node.nodes(+s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, g: String) -> List<&2, String>:
  Judging.Group.nodes(s, Store.root(s, r), g)

# the owner group of the line l of the store r, if it has one (none: its
# owners are the nodes that it started with)
def Node.group(+s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, l: Maybe<&2, String>) -> Maybe<&2, String>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    String,
    Replicas.Node.get(~Basics.Ask.machine(), s, Chain.root(s, Replicas.Line.chain(r, l)), Basics.Key.owner()),
    ws => Replicas.Read.whole(String, Codes.Code.text.read(ws))
  )

# the request that makes the group g, with the nodes inside it now, the owner
# group of the line l of the store r
def Node.own(+s: Replicas.Node<Basics.Ask>, +r: Ledgers.Id, l: Maybe<&2, String>, +g: String) -> Basics.Ask:
  Basics.Ask.On{r, l, Basics.Change.Own{g, Store.head(s, r), Node.nodes(s, r, g)}}

# a request, and who asks for it
type Request is Data:
  Request{envelope: Replicas.Envelope, ask: Basics.Ask}

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
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, String>
) -> Maybe<&2, Request>:
  match m:
    case None{}:
      None{}
    case Some{+g}:
      +os = Node.nodes(s, r, g)
      +at = Store.head(s, r)
      Shared.Maybe.when(
        Request,
        Bool.not(Ledgers.Owners.is_eq(os, Node.owners(s, r, l))),
        u => Some{
          Request{
            Replicas.Envelope{Adopt.id(l, at), "", ""},
            Basics.Ask.On{r, l, Basics.Change.Own{g, at, os}}
          }
        }
      )

# the adoption of the line l of the store r, if its owners are not the nodes
# inside its owner group
def Node.adoption(+s: Replicas.Node<Basics.Ask>, +r: Ledgers.Id, +l: Maybe<&2, String>) -> Maybe<&2, Request>:
  Adopt.of(s, r, l, Node.group(s, r, l))

# s, after the node n took in the request m, if any
def Adopt.ask(n: String, s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Request>) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{Request{e, q}}:
      Voting.Node.ask(n, s, e, q)

# s, after the node n asked for the adoption of the line l of the store r, if
# its owners are not the nodes inside its owner group
def Node.adopt(n: String, +s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, l: Maybe<&2, String>) -> Replicas.Node<Basics.Ask>:
  Adopt.ask(n, s, Node.adoption(s, r, l))

# Adopt.at once the head m of the line is known
def Adopt.head(n: String, s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Head>) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{Replicas.Head{r, b, next, t}}:
      Node.adopt(n, s, r, b)

# s, after the node n asked for the adoption of the line c, if s follows c:
# a change of a group reaches each line that the group owns by a step of the
# line, which a node asks for by itself when it works on the line
def Adopt.at(n: String, +s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> Replicas.Node<Basics.Ask>:
  Adopt.head(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# Adopt.at for the line m, if any
def Adopt.maybe(n: String, s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Ledgers.Chain>) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{c}:
      Adopt.at(n, s, c)

# s, after the node n asked for the adoption of each of the lines cs
def Node.adopts(+n: String, cs: List<&2, Ledgers.Chain>, s: Replicas.Node<Basics.Ask>) -> Replicas.Node<Basics.Ask>:
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.adopts(n, rest, Adopt.at(n, s, c))

# the heads of each of the lines cs are at the same height in a and in b
def Lines.level(cs: List<&2, Ledgers.Chain>, +a: Replicas.Node<Basics.Ask>, +b: Replicas.Node<Basics.Ask>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, r}:
      List.all.if(
        u => Lines.level(r, a, b),
        Voting.Heads.level(Replicas.Node.head_of(~Basics.Ask.machine(), a, c), Replicas.Node.head_of(~Basics.Ask.machine(), b, c))
      )

# s, after it took the ballots bs (k of them, pd by where each waits) in again
# and did what it can on the lines cs, until no head moves, f times at most. A ballot whose key the store gives
# at a later height is kept once the node is there: one sync catches up over
# each change of a key
def Sync.more(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node<Basics.Ask>:
  match f:
    case 0n:
      s
    case 1n+p:
      +s2 = Voting.Node.steps(n, cs, Replicas.Sealed.each(~Stepping.Ask.kernel(), k, bs, pd, s))
      Shared.Bool.when(
        Replicas.Node<Basics.Ask>,
        Lines.level(cs, s, s2),
        u => s2,
        u => Sync.more(p, n, cs, k, bs, pd, s2)
      )

# s, after the node n took in t, which another node sent, did what it can on
# each line that this may move, and asked for the adoption of each: how a
# node that is behind catches up
def Node.sync(+n: String, +s: Replicas.Node<Basics.Ask>, +t: Ledgers.State(Basics.Ask)) -> Replicas.Node<Basics.Ask>:
  +s1 = Voting.Node.take(s, t)
  +cs = Voting.Sync.lines(s, s1, t)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +k = List.length(&2, Ledgers.Ballot, bs)
  Node.adopts(
    n,
    cs,
    Sync.more(k, n, cs, k, bs, Replicas.Pending.of(bs), Voting.Node.steps(n, cs, s1))
  )

# the resource m of the branch x of the store st is the resource n of the
# branch b of the store r
def Draft.is_on(
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  st: Ledgers.Id,
  x: String,
  m: Resources.Name
) -> Bool:
  List.all.if(
    u => List.all.if(v => Resources.Name.is_eq(m, n), String.eq(x, b)),
    Ledgers.Id.is_eq(st, r)
  )

# the content that the request q gives the resource n on the branch b of the
# store r, when it writes it there
def Draft.content(
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  q: Basics.Ask
) -> Maybe<&2, Basics.Content>:
  match q:
    case Basics.Ask.On{st, Some{x}, Basics.Change.Write{m, base, c}}:
      Shared.Maybe.when(Basics.Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case Basics.Ask.On{st, Some{x}, Basics.Change.Resolve{k, m, c}}:
      Shared.Maybe.when(Basics.Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case _:
      None{}

# a pending write: when its writer asked for it (the time, then the request
# ID, as a key), and the content that it gives
type Draft is Data:
  Draft{key: List<&2, Bool>, content: Basics.Content}

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
  m: Maybe<&2, Basics.Content>
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
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
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
          Draft.content(r, b, n, q)
        ),
        u => found
      )
    case x y:
      found

# the newest write of the resource n on the branch b of the store r that the
# writer w asked for, among the requests qs, else found
def Draft.last(
  +s: Replicas.Node<Basics.Ask>,
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
      Draft.last(s, w, r, b, n, rest, Draft.of(w, r, b, n, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i), found))

# the content of the draft m, if any
def Draft.what(m: Maybe<&2, Draft>) -> Maybe<&2, Basics.Content>:
  match m:
    case None{}:
      None{}
    case Some{Draft{k, c}}:
      Some{c}

# the content of the newest pending write of the resource n on the branch b
# of the store r that the writer w asked for, if there is one. The requests
# that wait on the line are the pending ones: the cost is theirs, not that of
# every request of the writer
def Node.draft(
  +s: Replicas.Node<Basics.Ask>,
  w: String,
  +r: Ledgers.Id,
  +b: String,
  n: Resources.Name
) -> Maybe<&2, Basics.Content>:
  Draft.what(Draft.last(s, w, r, b, n, Replicas.Wait.of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})), None{}))

# the bytes of the draft m of the resource n, else what the point p holds
def Read.of(
  +s: Replicas.Node<Basics.Ask>,
  n: Resources.Name,
  m: Maybe<&2, Basics.Content>,
  p: Basics.Point
) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case Some{c}:
      Basics.Root.bytes(s, Judging.Content.root(s, n, c))
    case None{}:
      Node.content(s, n, p)

# what the writer w reads of the resource n at the point p: at the head of a
# branch, its own pending write; else what the point holds
def Node.read(
  +s: Replicas.Node<Basics.Ask>,
  w: String,
  +n: Resources.Name,
  p: Basics.Point
) -> Maybe<&2, Texts.Bytes()>:
  match p:
    case Basics.Point.Head{+r, +b}:
      Read.of(s, n, Node.draft(s, w, r, b, n), Basics.Point.Head{r, b})
    case x:
      Node.content(s, n, x)

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  rest: List<&2, LogEntry>
) -> List<&2, LogEntry>:
  match held r:
    case True{} Some{Ledgers.Asked{t, q}}:
      LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: Replicas.Node<Basics.Ask>,
  +n: Resources.Name,
  xs: List<&2, Ledgers.Id>,
  prev: Maybe<&2, Ledgers.Id>
) -> List<&2, LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(Basics.Roots.same(Res.root_at(s, n, Some{x}), Res.root_at(s, n, prev))),
        x,
        Replicas.Node.asked(~Basics.Ask.machine(), s, x),
        Log.of(s, n, r, Some{x})
      )

# the versions of the branch b of the store r that changed the resource n,
# among k versions from the number from
def Node.log(
  +s: Replicas.Node<Basics.Ask>,
  n: Resources.Name,
  +r: Ledgers.Id,
  +b: String,
  +from: U32,
  k: Nat
) -> List<&2, LogEntry>:
  Log.of(
    s,
    n,
    Node.versions(s, r, b, from, k),
    Version.before(s, Replicas.Node.tip(~Basics.Ask.machine(), s, Replicas.Line.chain(r, Some{b})), from)
  )

# what changed in the resource n from the point a to the point b, as the
# writer w reads them
def Node.diff(
  +s: Replicas.Node<Basics.Ask>,
  +w: String,
  +n: Resources.Name,
  a: Basics.Point,
  b: Basics.Point
) -> List<&2, Formats.Change>:
  Formats.Format.changes(
    Formats.Format.of(Resources.Name.path(n)),
    Maybe.default(&2, Texts.Bytes(), Node.read(s, w, n, a), []),
    Maybe.default(&2, Texts.Bytes(), Node.read(s, w, n, b), [])
  )

# the resource of a binding of a tree, when it is a clash that the merge of
# the version f opened
def Clash.binding(b: Trees.Binding, f: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  match b:
    case Trees.Binding{Con{3, k}, ws}:
      Shared.Maybe.when(
        Resources.Name,
        Shared.List.is_eq(~U32, ~U32.is_eq, ws, Judging.Clash.code(f)),
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
      Judging.Names.put(Clash.binding(b, f), Clash.of.bindings(r, f))

# the resources whose clash the merge of the version f left open in the tree
# whose root is h
def Clash.names(
  s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  f: Ledgers.Id
) -> List<&2, Resources.Name>:
  Clash.of.bindings(Trees.Tree.list(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s, h), f)

# the resources of ns whose clash, which the merge of the version f opened, is
# still open in the tree h
def Clash.left(
  +s: Replicas.Node<Basics.Ask>,
  ns: List<&2, Resources.Name>,
  +h: Maybe<&2, Hashes.Hash>,
  +f: Ledgers.Id
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(Resources.Name, n, Clash.left(s, r, h, f), Judging.Clash.open(s, h, n, f))

# the resources that clashed at the request k, whose request is a, when it is a
# merge
def Merge.clashes(
  +s: Replicas.Node<Basics.Ask>,
  k: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Basics.Ask.On{r, l, Basics.Change.Merge{f}}}}:
      Clash.names(s, Basics.Node.root_of(s, Some{k}), f)
    case _:
      []

# the resources that still clash after the merge k, whose request is a: those
# whose clash it opened, and that no resolve or newer merge settled since, at
# the head of its line
def Merge.left(
  +s: Replicas.Node<Basics.Ask>,
  k: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Basics.Ask.On{r, Some{l}, Basics.Change.Merge{+f}}}}:
      Clash.left(
        s,
        Clash.names(s, Basics.Node.root_of(s, Some{k}), f),
        Chain.root(s, Replicas.Line.chain(r, Some{l})),
        f
      )
    case _:
      []

# the resources that still clash after the merge k
def Node.conflict(+s: Replicas.Node<Basics.Ask>, +k: Ledgers.Id) -> List<&2, Resources.Name>:
  Merge.left(s, k, Replicas.Node.asked(~Basics.Ask.machine(), s, k))

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a node answers to a change (README, Vend Writer). Written: its version.
# Conflicted: a merge, or a resolve of one, after which resources still clash
# (the merge). Pending: its owners did not decide it yet. Stale: its owners
# refused it at their newest version. Refused: its ID names another change.
type Answer is Data:
  Answer.Written{version: Ledgers.Id}
  Answer.Conflicted{merge: Ledgers.Id}
  Answer.Pending{}
  Answer.Stale{}
  Answer.Refused{}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# Written i, or Conflicted k while the merge k still clashes
def Answer.left(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, +k: Ledgers.Id) -> Answer:
  Shared.Bool.when(
    Answer,
    List.is_empty(&2, Resources.Name, Node.conflict(s, k)),
    u => Answer.Written{i},
    u => Answer.Conflicted{k}
  )

# the answer to the change q of the request i, which a step took
def Answer.taken(s: Replicas.Node<Basics.Ask>, +i: Ledgers.Id, q: Basics.Ask) -> Answer:
  match q:
    case Basics.Ask.On{st, l, Basics.Change.Merge{f}}:
      Answer.left(s, i, i)
    case Basics.Ask.On{st, l, Basics.Change.Resolve{k, n, c}}:
      Answer.left(s, i, k)
    case _:
      Answer.Written{i}

# the answer to the request i of the change q, whose outcome is o: Pending
# while no step that the node knows decided it
def Answer.of(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, q: Basics.Ask, o: Maybe<&2, Replicas.Out>) -> Answer:
  match o:
    case Some{Replicas.Out.Taken{n}}:
      Answer.taken(s, i, q)
    case Some{Replicas.Out.Stale{}}:
      Answer.Stale{}
    case None{}:
      Answer.Pending{}

# the answer to the request i that the node holds as the change q: a store
# that starts is Written at once
def Answer.asked(+s: Replicas.Node<Basics.Ask>, +i: Ledgers.Id, q: Basics.Ask) -> Answer:
  match q:
    case Basics.Ask.Start{os}:
      Answer.Written{i}
    case x:
      Answer.of(s, i, x, Basics.Node.out(s, i))

# the answer to the change q of the request i, whose slot holds m: none when it
# is empty, Refused when it holds another change
def Answer.held(
  s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Maybe<&2, Answer>:
  match m:
    case None{}:
      None{}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Some{
        Shared.Bool.when(
          Answer,
          Basics.Ask.is_eq(q2, q),
          u => Answer.asked(s, i, q2),
          u => Answer.Refused{}
        )
      }
    case Some{c}:
      Some{Answer.Refused{}}

# what the node answers to the change q of e (none: it did not take it in)
def Node.answer(+s: Replicas.Node<Basics.Ask>, e: Replicas.Envelope, q: Basics.Ask) -> Maybe<&2, Answer>:
  +i = Replicas.Envelope.of(e)
  Answer.held(s, i, q, Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(i)))

# the answer m may come after the answer a as the node goes on: a request
# that a node answers stays answered; Pending may become any answer; Stale
# and Refused are final; a taken change stays taken, as the same version or
# the same merge (Written and Conflicted may follow each other: a merge is
# Conflicted while resources clash)
def Answer.follows(a: Answer, m: Maybe<&2, Answer>) -> Bool:
  match a m:
    case Answer.Pending{} Some{b}:
      True{}
    case Answer.Written{v} Some{Answer.Written{w}}:
      Ledgers.Id.is_eq(v, w)
    case Answer.Written{v} Some{Answer.Conflicted{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Written{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Conflicted{w}}:
      Ledgers.Id.is_eq(v, w)
    case Answer.Stale{} Some{Answer.Stale{}}:
      True{}
    case Answer.Refused{} Some{Answer.Refused{}}:
      True{}
    case x y:
      False{}

# Listings
# --------

# a branch: its store and its name
type Branch is Data:
  Branch{store: Ledgers.Id, name: String}

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Ledgers.Id}

# the branch b of the store r, with the owners os, at its newest version m,
# then rest
def Branch.put(
  r: Ledgers.Id,
  b: String,
  os: List<&2, String>,
  m: Maybe<&2, Ledgers.Id>,
  rest: List<&2, BranchEntry>
) -> List<&2, BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{v}:
      BranchEntry{Branch{r, b}, os, v} <> rest

# the branch of the head h, when it is one that has a version, then rest
def Branch.at(
  +s: Replicas.Node<Basics.Ask>,
  h: Replicas.Head,
  rest: List<&2, BranchEntry>
) -> List<&2, BranchEntry>:
  match h:
    case Replicas.Head{+r, Some{+b}, n, t}:
      Branch.put(r, b, Node.owners(s, r, Some{b}), Node.head(s, r, b), rest)
    case x:
      rest

# the branches of the heads hs
def Branch.all(+s: Replicas.Node<Basics.Ask>, hs: List<&2, Replicas.Head>) -> List<&2, BranchEntry>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      Branch.at(s, h, Branch.all(s, rest))

# every branch that the node follows
def Node.branches(+s: Replicas.Node<Basics.Ask>) -> List<&2, BranchEntry>:
  Branch.all(s, Tries.Trie.values(Replicas.Head, Replicas.State.heads(~Basics.Ask.machine(), s)))

# the branches es
def Branch.names(es: List<&2, BranchEntry>) -> List<&2, Branch>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{b, os, h}, r}:
      b <> Branch.names(r)

# the head of the branch b, if b exists
def Branch.head(s: Replicas.Node<Basics.Ask>, b: Branch) -> Maybe<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      Node.head(s, r, n)

# the resources of the branch b at its head
def Node.resources(+s: Replicas.Node<Basics.Ask>, b: Branch) -> List<&2, Resources.Name>:
  Judging.Res.names(s, Basics.Node.root_of(s, Branch.head(s, b)))

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
  s: Replicas.Node<Basics.Ask>,
  h: Maybe<&2, Ledgers.Id>,
  +n: Resources.Name
) -> List<&2, Resources.Name>:
  Uses.named(
    Formats.Format.uses(Formats.Format.of(Resources.Name.path(n)), Uses.items(Res.at(s, n, h))),
    n
  )

# the resources of a branch, each with what it imports, read once: the graph
# of its imports
type Uses is Data:
  Uses{imports: Tries.Trie<List<&2, Resources.Name>>, names: List<&2, Resources.Name>}

# t with what each resource of ns imports at the version h of s
def Uses.read(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Ledgers.Id>,
  ns: List<&2, Resources.Name>,
  t: Tries.Trie<List<&2, Resources.Name>>
) -> Tries.Trie<List<&2, Resources.Name>>:
  match ns:
    case Nil{}:
      t
    case Con{+n, r}:
      Uses.read(
        s,
        h,
        r,
        Tries.Trie.set(List<&2, Resources.Name>, t, Judging.Name.key(n), Uses.targets(s, h, n))
      )

# the graph of the imports of the branch b, at its head
def Uses.of(+s: Replicas.Node<Basics.Ask>, b: Branch) -> Uses:
  +h = Branch.head(s, b)
  +ns = Judging.Res.names(s, Basics.Node.root_of(s, h))
  Uses{Uses.read(s, h, ns, Tries.Trie.new(List<&2, Resources.Name>)), ns}

# what the resources of g import
def Uses.imports(g: Uses) -> Tries.Trie<List<&2, Resources.Name>>:
  match g:
    case Uses{t, ns}:
      t

# the resources of g
def Uses.nodes(g: Uses) -> List<&2, Resources.Name>:
  match g:
    case Uses{t, ns}:
      ns

# what n imports in g, when it is a resource of g
def Uses.succ(g: Uses, n: Resources.Name) -> List<&2, Resources.Name>:
  match g:
    case Uses{t, ns}:
      Maybe.default(
        &2,
        List<&2, Resources.Name>,
        Tries.Trie.get(List<&2, Resources.Name>, t, Judging.Name.key(n)),
        []
      )

# u uses c in g: c is reached from u through the imports, at any depth
def Uses.reach(g: Uses, u: Resources.Name, c: Resources.Name) -> Bool:
  Reaches.Reach.in(~Resources.Name, ~Uses, ~Resources.Name.is_eq, ~Uses.succ, ~Uses.nodes, g, u, c)

# a change elsewhere that touches what a branch uses: the version wrote the
# resource changed, and the resource used of the branch is that resource or
# uses it (Node.touches)
type Touch is Data:
  Touch{version: Ledgers.Id, changed: Resources.Name, branch: Branch, used: Resources.Name}

# the resource that the request r wrote: of a write or a resolve
def Wrote.of(r: Maybe<&2, Ledgers.Asked<Basics.Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, Basics.Ask.On{st, l, Basics.Change.Write{m, base, c}}}}:
      Some{m}
    case Some{Ledgers.Asked{t, Basics.Ask.On{st, l, Basics.Change.Resolve{k, m, c}}}}:
      Some{m}
    case _:
      None{}

# the resource that the version v wrote, when it is a write or a resolve
def Node.wrote(s: Replicas.Node<Basics.Ask>, v: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  Wrote.of(Replicas.Node.asked(~Basics.Ask.machine(), s, v))

# how many numbers are from a up to b, b not counted
def Count.span(+a: U32, +b: U32) -> Nat:
  Shared.Bool.when(Nat, U32.is_lt(a, b), u => U32.to_nat(U32.sub(b, a)), u => 0n)

# the versions of the line whose tip is m from the number n on, in order: the
# cost is theirs, not that of the line's history
def Line.since(+s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Tip>, +n: U32) -> List<&2, Ledgers.Id>:
  match m:
    case None{}:
      []
    case Some{+t}:
      Line.versions(Count.span(n, Replicas.Tip.count(t)), s, t, n)

# the number after the place m of a version vector, 0 without one
def Place.after(m: Maybe<&2, Basics.Place>) -> U32:
  match m:
    case None{}:
      0
    case Some{Basics.Place{c, n}}:
      U32.inc(n)

# a and b are the same branch
def Branch.same(a: Branch, b: Branch) -> Bool:
  match a b:
    case Branch{r1, n1} Branch{r2, n2}:
      List.all.if(u => String.eq(n1, n2), Ledgers.Id.is_eq(r1, r2))

# the versions of the branch x that the tree h did not take in: those after
# the place that its version vector holds for x
def Branch.news(+s: Replicas.Node<Basics.Ask>, h: Maybe<&2, Hashes.Hash>, x: Branch) -> List<&2, Ledgers.Id>:
  match x:
    case Branch{r, n}:
      +c = Replicas.Line.chain(r, Some{n})
      Line.since(s, Replicas.Node.tip(~Basics.Ask.machine(), s, c), Place.after(Basics.Node.vector(s, h, c)))

# the versions of the branches es, other than b, that the tree h did not take
# in
def Lacked.of(
  +s: Replicas.Node<Basics.Ask>,
  +h: Maybe<&2, Hashes.Hash>,
  +b: Branch,
  es: List<&2, Branch>
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
def Branch.lacked(+s: Replicas.Node<Basics.Ask>, +b: Branch) -> List<&2, Ledgers.Id>:
  Lacked.of(s, Basics.Node.root_of(s, Branch.head(s, b)), b, Branch.names(Node.branches(s)))

# the branch b lacks the version v
def Touch.lacks(+s: Replicas.Node<Basics.Ask>, +b: Branch, +v: Ledgers.Id) -> Bool:
  List.all.if(
    u => Bool.not(Basics.Node.has(s, Maybe.default(&2, Ledgers.Id, Branch.head(s, b), v), v)),
    Maybe.is_some(&2, Ledgers.Id, Branch.head(s, b))
  )

# the key of the branch b
def Branch.key(b: Branch) -> List<&2, Bool>:
  match b:
    case Branch{r, n}:
      List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# what the checks of touches on one branch read of s once: the branch, and
# its imports
type Seen is Data:
  Seen{state: Replicas.Node<Basics.Ask>, branch: Branch, uses: Uses}

# what the checks on the branch b read of s
def Seen.of(+s: Replicas.Node<Basics.Ask>, +b: Branch) -> Seen:
  Seen{s, b, Uses.of(s, b)}

# the touch t, of the branch of g, holds: its branch is a branch and lacks
# its version, which is a version and wrote the resource changed, and the
# resource used is of the branch, and is the one changed or uses it; each
# part runs only when the ones before it hold, from the cheapest
def Touch.holds(g: Seen, t: Touch) -> Bool:
  match g t:
    case Seen{+s, gb, +us} Touch{+v, +c, b, +u}:
      List.all.if(
        w => List.all.if(
          w => List.all.if(
            w => List.all.if(
              w => List.any.if(w => Uses.reach(us, u, c), Resources.Name.is_eq(u, c)),
              Tries.Trie.has(List<&2, Resources.Name>, Uses.imports(us), Judging.Name.key(u))
            ),
            Shared.Maybe.is_eq(~Resources.Name, ~Resources.Name.is_eq, Node.wrote(s, v), Some{c})
          ),
          Touch.lacks(s, b, v)
        ),
        Node.is_version(s, v)
      )

# the touch t holds
def Node.touches(s: Replicas.Node<Basics.Ask>, t: Touch) -> Bool:
  match t:
    case Touch{v, c, +b, u}:
      Touch.holds(Seen.of(s, b), Touch{v, c, b, u})

# the touches of the version v that wrote c, on the branch b, one for each of
# its resources us
def Touch.each(
  us: List<&2, Resources.Name>,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch
) -> List<&2, Touch>:
  match us:
    case Nil{}:
      []
    case Con{u, r}:
      Touch{v, c, b, u} <> Touch.each(r, v, c, b)

# the touches of the version v that wrote the resource m (if any), on the
# branch b, one for each of its resources us
def Touch.of(
  m: Maybe<&2, Resources.Name>,
  v: Ledgers.Id,
  b: Branch,
  us: List<&2, Resources.Name>
) -> List<&2, Touch>:
  match m:
    case None{}:
      []
    case Some{c}:
      Touch.each(us, v, c, b)

# the touches of the version v on the branch of g
def Affects.at(g: Seen, v: Ledgers.Id) -> List<&2, Touch>:
  match g:
    case Seen{s, b, us}:
      +v = v
      Touch.of(Node.wrote(s, v), v, b, Uses.nodes(us))

# the touches that may hold of the branch b, of g: those of the versions of
# the other branches that b did not take in
def Affects.cands(s: Replicas.Node<Basics.Ask>, b: Branch, g: Seen) -> List<&2, Touch>:
  Shared.List.flat(~Ledgers.Id, ~Touch, ~Seen, ~Affects.at, Branch.lacked(s, b), g)

# the changes elsewhere that touch what the branch b uses, at any depth
def Node.affects(+s: Replicas.Node<Basics.Ask>, +b: Branch) -> List<&2, Touch>:
  +g = Seen.of(s, b)
  Shared.List.keep(~Touch, ~Seen, ~Touch.holds, Affects.cands(s, b, g), g)

# the checks of one branch, and the version of a point
type Impact is Data:
  Impact{seen: Seen, version: Maybe<&2, Ledgers.Id>}

# the touch t is of the version of g, or of a version that it came from, and
# holds
def Impact.keeps(g: Impact, t: Touch) -> Bool:
  match g t:
    case Impact{Seen{+s, gb, us}, +m} Touch{+v, c, b, u}:
      List.all.if(
        w => Touch.holds(Seen{s, gb, us}, Touch{v, c, b, u}),
        List.all.if(
          w => Basics.Node.has(s, Maybe.default(&2, Ledgers.Id, m, v), v),
          Maybe.is_some(&2, Ledgers.Id, m)
        )
      )

# what the changes up to the version m touch on the branches es
def Impact.of(+s: Replicas.Node<Basics.Ask>, +m: Maybe<&2, Ledgers.Id>, es: List<&2, Branch>) -> List<&2, Touch>:
  match es:
    case Nil{}:
      []
    case Con{+b, r}:
      +g = Seen.of(s, b)
      List.append(
        &2,
        Touch,
        Shared.List.keep(~Touch, ~Impact, ~Impact.keeps, Affects.cands(s, b, g), Impact{g, m}),
        Impact.of(s, m, r)
      )

# what the changes up to the point p touch elsewhere
def Node.impact(+s: Replicas.Node<Basics.Ask>, p: Basics.Point) -> List<&2, Touch>:
  Impact.of(s, Node.version(s, p), Branch.names(Node.branches(s)))

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# what a subscription or a poll follows: the versions or the conflicts of a
# branch, or the changes elsewhere that touch it
type Topic is Data:
  Topic.Versions{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Affects{branch: Branch}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# an event of a topic
type Notice is Data:
  Notice.Versioned{branch: Branch, version: Ledgers.Id}
  Notice.Conflicted{branch: Branch, version: Ledgers.Id}
  Notice.Touched{touch: Touch}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# the key of the notice n: its kind, then its parts
def Notice.key(n: Notice) -> List<&2, Bool>:
  match n:
    case Notice.Versioned{b, v}:
      False{} <> False{} <> List.append(&2, Bool, Branch.key(b), Ledgers.Id.key(v))
    case Notice.Conflicted{b, v}:
      False{} <> True{} <> List.append(&2, Bool, Branch.key(b), Ledgers.Id.key(v))
    case Notice.Touched{Touch{v, c, b, u}}:
      True{}
        <> List.append(
          &2,
          Bool,
          Ledgers.Id.key(v),
          List.append(
            &2,
            Bool,
            Judging.Name.key(c),
            List.append(&2, Bool, Branch.key(b), Judging.Name.key(u))
          )
        )

# the versions xs of the branch b, as notices
def Notice.versions(+b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Notice.Versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(+s: Replicas.Node<Basics.Ask>, +b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Notice,
        Notice.Conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(List.is_empty(&2, Resources.Name, Merge.clashes(s, x, Replicas.Node.asked(~Basics.Ask.machine(), s, x))))
      )

# the touches ts, as notices
def Notice.touches(ts: List<&2, Touch>) -> List<&2, Notice>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Notice.Touched{t} <> Notice.touches(r)

# the notices of ns whose keys old does not hold
def Notice.new(ns: List<&2, Notice>, +old: Tries.Trie<Unit>) -> List<&2, Notice>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Notice,
        n,
        Notice.new(r, old),
        Bool.not(Tries.Trie.has(Unit, old, Notice.key(n)))
      )

# the number of versions of the line c in s
def Chain.count(+s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> U32:
  Maybe.default(
    &2,
    U32,
    Maybe.bind(&2, Replicas.Tip, U32, Replicas.Node.tip(~Basics.Ask.machine(), s, c), t => Some{Replicas.Tip.count(t)}),
    0
  )

# the versions of the branch b that s has and since has not: those from the
# number of versions of b in since on
def Branch.since(+s: Replicas.Node<Basics.Ask>, since: Replicas.Node<Basics.Ask>, b: Branch) -> List<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      +c = Replicas.Line.chain(r, Some{n})
      Line.since(s, Replicas.Node.tip(~Basics.Ask.machine(), s, c), Chain.count(since, c))

# the notices of the topic t in s that since, an earlier state of the node,
# does not have: the cost is that of what is new, not of the history
def Node.notices(+s: Replicas.Node<Basics.Ask>, t: Topic, since: Replicas.Node<Basics.Ask>) -> List<&2, Notice>:
  match t:
    case Topic.Versions{+b}:
      Notice.versions(b, Branch.since(s, since, b))
    case Topic.Conflicts{+b}:
      Notice.conflicts(s, b, Branch.since(s, since, b))
    case Topic.Affects{+b}:
      Notice.new(
        Notice.touches(Node.affects(s, b)),
        Tries.Trie.put_keys(
          ~Notice,
          ~Notice.key,
          Notice.touches(Node.affects(since, b)),
          Tries.Trie.new(Unit)
        )
      )

# a resource mounted to a branch
type Mount is Data:
  Mount{resource: String, branch: Branch}

# what a Vend Node holds: its name, the parts of the stores that it uses, the
# writers connected to it, and the resources mounted to it
type Vend is Data:
  Vend{name: String, state: Replicas.Node<Basics.Ask>, writers: List<&2, String>, mounts: List<&2, Mount>}

# the node v may stop: it is forced to, or no resource is mounted and no
# writer is connected
def Vend.may_stop(v: Vend, force: Bool) -> Bool:
  match v:
    case Vend{n, s, ws, ms}:
      List.any.if(
        u => List.all.if(w => List.is_empty(&2, Mount, ms), List.is_empty(&2, String, ws)),
        force
      )

# the node b holds every entry that the node a holds: its ledger only grew
def Node.grows(a: Replicas.Node<Basics.Ask>, b: Replicas.Node<Basics.Ask>) -> Bool:
  Ledgers.State.grows(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Replicas.State.ledger(~Basics.Ask.machine(), a),
    Replicas.State.ledger(~Basics.Ask.machine(), b)
  )
