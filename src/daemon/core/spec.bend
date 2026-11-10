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
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees

# The pure core of a Vend Node (README): what it holds, what it answers, and
# the laws about both. transport/spec.bend carries it over IO.
#
# A line is a store, or one of its branches. What a line holds is a tip: its
# content, a tree of what it holds now, and its log, a tree that only gains
# keys (the outcome of each request, each version by its number, the count of
# versions, the marks, and the owners of the next step). So the answer to a
# request, the newest version, a version by number, a mark and the owners are
# each one read of a tree: about log(size) nodes, each checked by its hash.
#
# A step takes a tip to the next one: it runs a batch of requests, in order
# (Step.run), and any node can run it again. The owners of a line cast ballots
# for steps (Ledgers); a node moves its head of a line only to a step that the
# owners in its tip decided (a majority of them, or all of them: Quorum.decide),
# and that it ran itself with the same result (Node.advance). A node's ledger only grows, and its heads only move
# along steps, so what it answers stays.

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Ledgers.Id. A store is named by
# the request that started it. A line is a store itself (no branch) or one of
# its branches.

# a member of an owner group: a node, or another group of its store
type Member is Data:
  Member.Node{name: String}
  Member.Group{name: String}

# new content: what a node holds under a root (the root of the rope of its
# bytes: Content.of), or what an old version held. A change names its content
# and does not carry it, so a change of a huge resource is small
type Content is Data:
  Content.Root{root: Ropes.Root}
  Content.Of{version: Ledgers.Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}

# a change of a branch, or of its store (Ask.on). Key: the store gives the
# node the key that signs its first ballot in the store (again after the node
# lost its secret: a new chain of keys). Branch: the store makes the
# branch, at a version if any. Group: the store makes the group, or replaces
# its members. Own: the line's owner group is group, whose nodes, in the tree
# of the step at of the store (a store reads its own tree), are owners
type Change is Data:
  Change.Branch{name: String, at: Maybe<&2, Ledgers.Id>}
  Change.Group{name: String, members: List<&2, Member>}
  Change.Own{group: String, at: Maybe<&2, Ledgers.Id>, owners: List<&2, String>}
  Change.Write{name: Resources.Name, base: Maybe<&2, Ledgers.Id>, content: Content}
  Change.Resolve{conflict: Ledgers.Id, name: Resources.Name, content: Content}
  Change.Merge{from: Ledgers.Id}
  Change.Move{to: Ledgers.Id}
  Change.Mark{mark: String, message: String}
  Change.Key{node: String, key: Hashes.Hash}

# a first owner of a store: a node, and the key that signs its first ballot in
# the store
type Owner is Data:
  Owner{name: String, key: Hashes.Hash}

# a change that a writer asks for: a store that starts with its first owners,
# or a change of a branch of a store (none: of the store itself)
type Ask is Data:
  Ask.Start{owners: List<&2, Owner>}
  Ask.On{store: Ledgers.Id, branch: Maybe<&2, String>, change: Change}

# who asks for a change, and when
type Envelope is Data:
  Envelope{id: String, writer: String, time: String}

# the request of e
def Envelope.of(e: Envelope) -> Ledgers.Id:
  match e:
    case Envelope{r, w, t}:
      Ledgers.Id{w, r}

# the time of e
def Envelope.time(e: Envelope) -> String:
  match e:
    case Envelope{r, w, t}:
      t

# a and b are the same member
def Member.is_eq(a: Member, b: Member) -> Bool:
  match a b:
    case Member.Node{x} Member.Node{y}:
      String.eq(x, y)
    case Member.Group{x} Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# the version m, if any (where a line starts, or the base of a write), then r
def Base.code(m: Maybe<&2, Ledgers.Id>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Ledgers.Id, ~Ledgers.Id.code, m, r)

# a version, if any
def Base.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Ledgers.Id>>>:
  Codes.Code.maybe.read(~Ledgers.Id, ~Ledgers.Id.code.read, ts)

# the text t with the tag k, then r
def Tag.text(k: U32, t: String, r: List<&2, U32>) -> List<&2, U32>:
  k <> Codes.Code.text(t, r)

# the branch m, if any (none: the store), then r
def Target.code(m: Maybe<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~String, ~Codes.Code.text, m, r)

# a branch, if any
def Target.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, String>>>:
  Codes.Code.maybe.read(~String, ~Codes.Code.text.read, ts)

# the member l, then r
def Member.code(l: Member, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Member.Node{n}:
      Tag.text(0, n, r)
    case Member.Group{n}:
      Tag.text(1, n, r)

# a member
def Member.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Member>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Member>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.Node{n}, r),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Member>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.Group{n}, r),
          u => None{}
        )
      )

# the members ms, then r
def Members.code(ms: List<&2, Member>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Member, ~Member.code, ms, r)

# members
def Members.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Member>>>:
  Codes.Code.list.read(~Member, ~Member.code.read, ts)

# the content c, then r
def Content.code(c: Content, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Content.Root{x}:
      0 <> Ropes.Root.code(x, r)
    case Content.Of{v}:
      1 <> Ledgers.Id.code(v, r)

# a content
def Content.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Content>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Content>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~Ropes.Root,
          ~Content,
          ~Ropes.Root.code.read,
          x => Content.Root{x},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Content>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(
            ~Ledgers.Id,
            ~Content,
            ~Ledgers.Id.code.read,
            v => Content.Of{v},
            r
          ),
          u => None{}
        )
      )

# the change c, then r
def Change.code(c: Change, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Change.Branch{n, at}:
      0 <> Codes.Code.text(n, Base.code(at, r))
    case Change.Own{g, at, os}:
      1 <> Codes.Code.text(g, Base.code(at, Ledgers.Owners.code(os, r)))
    case Change.Write{n, base, x}:
      2 <> Resources.Name.code(n, Base.code(base, Content.code(x, r)))
    case Change.Resolve{k, n, x}:
      3 <> Ledgers.Id.code(k, Resources.Name.code(n, Content.code(x, r)))
    case Change.Merge{v}:
      4 <> Ledgers.Id.code(v, r)
    case Change.Move{v}:
      5 <> Ledgers.Id.code(v, r)
    case Change.Mark{m, t}:
      6 <> Codes.Code.text(m, Codes.Code.text(t, r))
    case Change.Group{g, ms}:
      7 <> Codes.Code.text(g, Members.code(ms, r))
    case Change.Key{n, k}:
      8 <> Codes.Code.text(n, Hashes.Hash.code(k, r))

# a change whose tag is x, from the tokens r after it
def Change.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Change>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Change>>,
    U32.is_eq(x, 0),
    u => Codes.Code.two.read(
      ~String,
      ~Maybe<&2, Ledgers.Id>,
      ~Change,
      ~Codes.Code.text.read,
      ~Base.code.read,
      n => a => Change.Branch{n, a},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Change>>,
      U32.is_eq(x, 1),
      u => Codes.Code.three.read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Change,
        ~Codes.Code.text.read,
        ~Base.code.read,
        ~Ledgers.Owners.code.read,
        g => a => os => Change.Own{g, a, os},
        r
      ),
      u => Shared.Bool.when(
        Maybe<&2, Codes.Read<Change>>,
        U32.is_eq(x, 2),
        u => Codes.Code.three.read(
          ~Resources.Name,
          ~Maybe<&2, Ledgers.Id>,
          ~Content,
          ~Change,
          ~Resources.Name.code.read,
          ~Base.code.read,
          ~Content.code.read,
          n => b => c => Change.Write{n, b, c},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Change>>,
          U32.is_eq(x, 3),
          u => Codes.Code.three.read(
            ~Ledgers.Id,
            ~Resources.Name,
            ~Content,
            ~Change,
            ~Ledgers.Id.code.read,
            ~Resources.Name.code.read,
            ~Content.code.read,
            k => n => c => Change.Resolve{k, n, c},
            r
          ),
          u => Shared.Bool.when(
            Maybe<&2, Codes.Read<Change>>,
            U32.is_eq(x, 4),
            u => Codes.Code.one.read(
              ~Ledgers.Id,
              ~Change,
              ~Ledgers.Id.code.read,
              v => Change.Merge{v},
              r
            ),
            u => Shared.Bool.when(
              Maybe<&2, Codes.Read<Change>>,
              U32.is_eq(x, 5),
              u => Codes.Code.one.read(
                ~Ledgers.Id,
                ~Change,
                ~Ledgers.Id.code.read,
                v => Change.Move{v},
                r
              ),
              u => Shared.Bool.when(
                Maybe<&2, Codes.Read<Change>>,
                U32.is_eq(x, 6),
                u => Codes.Code.two.read(
                  ~String,
                  ~String,
                  ~Change,
                  ~Codes.Code.text.read,
                  ~Codes.Code.text.read,
                  m => n => Change.Mark{m, n},
                  r
                ),
                u => Shared.Bool.when(
                  Maybe<&2, Codes.Read<Change>>,
                  U32.is_eq(x, 8),
                  u => Codes.Code.two.read(
                    ~String,
                    ~Hashes.Hash,
                    ~Change,
                    ~Codes.Code.text.read,
                    ~Hashes.Hash.code.read,
                    n => k => Change.Key{n, k},
                    r
                  ),
                  u => Shared.Bool.when(
                    Maybe<&2, Codes.Read<Change>>,
                    U32.is_eq(x, 7),
                    u => Codes.Code.two.read(
                      ~String,
                      ~List<&2, Member>,
                      ~Change,
                      ~Codes.Code.text.read,
                      ~Members.code.read,
                      g => ms => Change.Group{g, ms},
                      r
                    ),
                    u => None{}
                  )
                )
              )
            )
          )
        )
      )
    )
  )

# a change
def Change.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Change>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Change.code.read.of(x, r)

# the first owner o, then r
def Owner.code(o: Owner, r: List<&2, U32>) -> List<&2, U32>:
  match o:
    case Owner{n, k}:
      Codes.Code.text(n, Hashes.Hash.code(k, r))

# a first owner
def Owner.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Owner>>:
  Codes.Code.two.read(
    ~String,
    ~Hashes.Hash,
    ~Owner,
    ~Codes.Code.text.read,
    ~Hashes.Hash.code.read,
    n => k => Owner{n, k},
    ts
  )

# the names of the first owners os
def Owner.names(os: List<&2, Owner>) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{Owner{n, k}, r}:
      n <> Owner.names(r)

# the request q, then r
def Ask.code(q: Ask, r: List<&2, U32>) -> List<&2, U32>:
  match q:
    case Ask.Start{os}:
      0 <> Codes.Code.list(~Owner, ~Owner.code, os, r)
    case Ask.On{st, l, c}:
      1 <> Ledgers.Id.code(st, Target.code(l, Change.code(c, r)))

# a request
def Ask.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ask>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Ask>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~List<&2, Owner>,
          ~Ask,
          ~(m => Codes.Code.list.read(~Owner, ~Owner.code.read, m)),
          os => Ask.Start{os},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Ask>>,
          U32.is_eq(x, 1),
          u => Codes.Code.three.read(
            ~Ledgers.Id,
            ~Maybe<&2, String>,
            ~Change,
            ~Ask,
            ~Ledgers.Id.code.read,
            ~Target.code.read,
            ~Change.code.read,
            s => l => c => Ask.On{s, l, c},
            r
          ),
          u => None{}
        )
      )

# a and b are the same request: they have the same code
def Ask.is_eq(a: Ask, b: Ask) -> Bool:
  Codes.Code.is_eq(~Ask, ~Ask.code, a, b)

# the key of the branch n below its store: prefix-free
def Line.key(n: String) -> List<&2, Bool>:
  Tries.Trie.text(n)

# the chain of the branch l of the store r (none: the store's own chain)
def Line.chain(r: Ledgers.Id, l: Maybe<&2, String>) -> Ledgers.Chain:
  match l:
    case None{}:
      Ledgers.Chain{r, None{}}
    case Some{x}:
      Ledgers.Chain{r, Some{Line.key(x)}}

# the owners that the change c gives its chain, when it sets them
def Change.owners(c: Change) -> Maybe<&2, List<&2, String>>:
  match c:
    case Change.Own{g, at, os}:
      Some{os}
    case _:
      None{}

# The state
# ---------

# what a judge says of one change: take it or refuse it as stale, the root of
# the content after it, and the new nodes
type Verdict is Data:
  Verdict{takes: Bool, result: Maybe<&2, Hashes.Hash>, data: List<&2, List<&2, U32>>}

# what a line holds: the root of its content and the root of its log
type Tip is Data:
  Tip{content: Maybe<&2, Hashes.Hash>, log: Maybe<&2, Hashes.Hash>}

# a node's head of a line: the line, the height of its next step, and the hash
# of its tip (none: the node waits for the store's step that makes the line)
type Head is Data:
  Head{store: Ledgers.Id, branch: Maybe<&2, String>, next: U32, tip: Maybe<&2, Hashes.Hash>}

# the key chain of one node in one store, as a node knows it: how many of its
# ballots the node holds, the place of the last one, the key that signs the
# next one, and the first key of the chain (the one that the store gave it)
type Chained is Data:
  Chained{count: U32, last: Maybe<&2, Ledgers.Where>, key: Hashes.Hash, first: Hashes.Hash}

# what a node keeps to seal its ballots and to check those of other nodes: its
# secret seed; the key chain of each node in each store (its own too); the
# requests that a writer connected to it asked for (an owner casts for a
# change of who decides only when it was asked at the owner itself); and the
# highest round of which it holds a ballot, for each height that has a round
# after the first
type Keys is Data:
  Keys{
    seed: Hashes.Hash,
    chains: Tries.Trie<Chained>,
    asked: Tries.Trie<Unit>,
    rounds: Tries.Trie<Nat>
  }

# what a node holds: its ledger, which nodes replicate; its head of each line
# that it follows; the requests of each line that wait for a step; and its
# keys. Heads, waiting requests and keys are the node's own: no other node
# sends them
type Node is Data:
  Node{
    ledger: Ledgers.State(Ask),
    heads: Tries.Trie<Head>,
    waiting: Tries.Trie<List<&2, Ledgers.Id>>,
    keys: Keys
  }

# what a node holds
def State() -> Data:
  Node

# the ledger of s
def State.ledger(s: State()) -> Ledgers.State(Ask):
  match s:
    case Node{l, hs, ws, ks}:
      l

# the heads of s
def State.heads(s: State()) -> Tries.Trie<Head>:
  match s:
    case Node{l, hs, ws, ks}:
      hs

# the requests of s that wait for a step, by line
def State.waiting(s: State()) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match s:
    case Node{l, hs, ws, ks}:
      ws

# the keys of s
def State.keys(s: State()) -> Keys:
  match s:
    case Node{l, hs, ws, ks}:
      ks

# s with the ledger l
def State.led(s: State(), l: Ledgers.State(Ask)) -> State():
  match s:
    case Node{old, hs, ws, ks}:
      Node{l, hs, ws, ks}

# s with the keys ks
def State.keyed(s: State(), ks: Keys) -> State():
  match s:
    case Node{l, hs, ws, old}:
      Node{l, hs, ws, ks}

# a node that holds nothing yet, with the secret seed
def Node.empty(seed: Hashes.Hash) -> State():
  Node{
    Ledgers.State.empty(~Ask),
    Tries.Trie.new(Head),
    Tries.Trie.new(List<&2, Ledgers.Id>),
    Keys{seed, Tries.Trie.new(Chained), Tries.Trie.new(Unit), Tries.Trie.new(Nat)}
  }

# the words that s holds under the hash h
def Store.fetch(s: State(), h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Ledgers.State.data(~Ask, State.ledger(s), h)

# s with the words ds as data, each under its hash
def State.keep(+s: State(), ds: List<&2, List<&2, U32>>) -> State():
  State.led(s, Ledgers.State.put_datas(~Ask, ~Ask.is_eq, ds, State.ledger(s)))

# the request i, when s holds it
def Node.asked(s: State(), i: Ledgers.Id) -> Maybe<&2, Ledgers.Asked<Ask>>:
  Ledgers.State.asked(~Ask, State.ledger(s), i)

# Content
# -------
# The content of a line is a tree in key spaces: the first word of a key says
# which. 0: the root of a resource's content (none: removed). 2 (in a store's
# tree): a group's members. 3: a merge's clash, open or settled. 4: the version
# vector, the newest version of each other line that the content came from. 5
# (in a store's tree): the first tip of each of its branches. 6: the line's
# owner group. 7 (in a store's tree): the names of its groups.

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the key of the members of the group g
def Key.group(g: String) -> List<&2, U32>:
  2 <> Codes.Code.text(g, [])

# the key of a line's owner group
def Key.owner() -> List<&2, U32>:
  [6]

# the key of the names of a store's groups
def Key.groups() -> List<&2, U32>:
  [7]

# the key of the clash of the resource n
def Key.clash(n: Resources.Name) -> List<&2, U32>:
  3 <> Resources.Name.code(n, [])

# the key of the line c in a version vector
def Key.vector(c: Ledgers.Chain) -> List<&2, U32>:
  4 <> Ledgers.Chain.code(c, [])

# the key of the first key of the node n in a store
def Key.seal(n: String) -> List<&2, U32>:
  8 <> Codes.Code.text(n, [])

# the value of a resource whose content is under the root m (none: removed)
def Res.code(m: Maybe<&2, Ropes.Root>) -> List<&2, U32>:
  Codes.Code.maybe(~Ropes.Root, ~Ropes.Root.code, m, [])

# the value of a resource, flattened: the root of its content, when it is
# there
def Res.of.read(m: Maybe<&2, Codes.Read<Maybe<&2, Ropes.Root>>>) -> Maybe<&2, Ropes.Root>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      x
    case _:
      None{}

# the root of the content in the value ws of a resource, when it is there
def Res.read(ws: List<&2, U32>) -> Maybe<&2, Ropes.Root>:
  Res.of.read(Codes.Code.maybe.read(~Ropes.Root, ~Ropes.Root.code.read, ws))

# Node.get once the root node m of the tree is known. The node comes before
# the path of the key (a hash): a tree with no node costs no hash, and a proof
# about a tree that is not known makes none
def Node.get.at(s: State(), +k: List<&2, U32>, m: Maybe<&2, Trees.Node>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Node.Empty{}}:
      None{}
    case Some{+n}:
      Trees.Tree.get.go(~State(), ~Store.fetch, s, Trees.Tree.path(k), k, Some{n})

# what the tree whose root is h holds under the key k, in the store s
def Node.get(+s: State(), h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Node.get.at(s, k, Trees.Tree.part(~State(), ~Store.fetch, s, h))

# Node.set once the root node m of the tree is known (see Node.get.at)
def Node.set.at(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> Maybe<&2, Trees.Put>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Trees.Tree.set.go(~State(), ~Store.fetch, s, Trees.Tree.path(k), 0n, k, x, h, Some{n})

# the tree whose root is h with the key k set to x: Trees.Tree.set (impl:
# Set.is)
def Node.set(
  +s: State(),
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Trees.Put>:
  Node.set.at(s, h, k, x, Trees.Tree.part(~State(), ~Store.fetch, s, h))

# Node.look once the root node m of the tree is known (see Node.get.at)
def Node.look.at(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> Trees.Look:
  match m:
    case None{}:
      Trees.Look.missing(h)
    case Some{Trees.Node.Empty{}}:
      Trees.Look.Absent{}
    case Some{+n}:
      Trees.Tree.look.go(~State(), ~Store.fetch, s, Trees.Tree.path(k), k, h, Some{n})

# what a read of the key k finds in the tree whose root is h: Trees.Tree.look
# (impl: Look.is)
def Node.look(+s: State(), +h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Trees.Look:
  Node.look.at(s, h, k, Trees.Tree.part(~State(), ~Store.fetch, s, h))

# what a look knows: the value, or that there is none (none: it lacks a node,
# and cannot tell)
def Look.known(l: Trees.Look) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  match l:
    case Trees.Look.Found{v}:
      Some{Some{v}}
    case Trees.Look.Absent{}:
      Some{None{}}
    case Trees.Look.Missing{x}:
      None{}

# what the tree whose root is h holds under the key k, or that it holds
# nothing there (none: the node lacks a node of the tree). A judge reads with
# this: it refuses only on what it knows, and waits for what it lacks
def Node.find(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>
) -> Maybe<&2, Maybe<&2, List<&2, U32>>>:
  Look.known(Node.look(s, h, k))

# the root in the value m of a resource, if any
def Res.found(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, m, ws => Res.read(ws))

# the root of the content of the resource n in the tree whose root is h, or
# that it is not there (none: the node lacks a node of the tree)
def Res.find(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Ropes.Root>,
    Node.find(s, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the root of the content of the resource n in the tree whose root is h (none:
# it is not there)
def Res.root(s: State(), h: Maybe<&2, Hashes.Hash>, n: Resources.Name) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, Node.get(s, h, Key.res(n)), ws => Res.read(ws))

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the bytes under the root m, if any, when s holds their rope
def Root.bytes(s: State(), m: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(
    &2,
    Ropes.Root,
    Texts.Bytes(),
    m,
    r => Ropes.Rope.read(~State(), ~Store.fetch, s, r)
  )

# x is the byte that ends a line
def Byte.is_end(x: U32) -> Bool:
  U32.is_eq(x, 10)

# the rope of the bytes b, cut after each line: content is stored once by
# hash, and two contents share every part that an edit did not touch
def Bytes.rope(b: Texts.Bytes()) -> Ropes.Put:
  Ropes.Rope.put(Ropes.Rope.cut(~U32, ~Byte.is_end, b))

# the content of the bytes b: the root of their rope
def Content.of(b: Texts.Bytes()) -> Content:
  Content.Root{Ropes.Put.root(Bytes.rope(b))}

# the value of a read that is the whole of some words
def Read.whole(-A: Data, m: Maybe<&2, Codes.Read<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# the members of the group g in the store tree whose root is h, if g is there
def Members.in(s: State(), h: Maybe<&2, Hashes.Hash>, g: String) -> Maybe<&2, List<&2, Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Member>,
    Node.get(s, h, Key.group(g)),
    ws => Read.whole(List<&2, Member>, Members.code.read(ws))
  )

# s with the bytes b: the nodes of their rope, each under its hash. A node
# keeps new bytes before it asks for a write of their content
def Node.keep(s: State(), b: Texts.Bytes()) -> State():
  State.keep(s, Ropes.Put.nodes(Bytes.rope(b)))

# Tips and logs
# -------------
# A log is a tree in key spaces. 0: the owners of the next step. 1: the count
# of versions. 2: the outcome of a request. 3: a version, by its number. 4: a
# mark.

# the words of the tip t
def Tip.words(t: Tip) -> List<&2, U32>:
  match t:
    case Tip{c, l}:
      Codes.Code.maybe(
        ~Hashes.Hash,
        ~Hashes.Hash.code,
        c,
        Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, l, [])
      )

# the tip that some words are, when they are one
def Tip.read(ws: List<&2, U32>) -> Maybe<&2, Tip>:
  Read.whole(
    Tip,
    Codes.Code.two.read(
      ~Maybe<&2, Hashes.Hash>,
      ~Maybe<&2, Hashes.Hash>,
      ~Tip,
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      c => l => Tip{c, l},
      ws
    )
  )

# the hash of the tip t: what a ballot names
def Tip.hash(t: Tip) -> Hashes.Hash:
  Hashes.Sha.hash(Tip.words(t))

# the tip that s holds under the hash h
def Tip.at(s: State(), h: Hashes.Hash) -> Maybe<&2, Tip>:
  Maybe.bind(&2, List<&2, U32>, Tip, Store.fetch(s, h), ws => Tip.read(ws))

# the content of the tip t
def Tip.content(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l}:
      c

# the log of the tip t
def Tip.log(t: Tip) -> Maybe<&2, Hashes.Hash>:
  match t:
    case Tip{c, l}:
      l

# the key of the owners of the next step
def Log.owners() -> List<&2, U32>:
  [0]

# the key of the count of versions
def Log.count() -> List<&2, U32>:
  [1]

# the key of the outcome of the request i
def Log.out(i: Ledgers.Id) -> List<&2, U32>:
  2 <> Ledgers.Id.code(i, [])

# the key of the version of the number n
def Log.version(n: U32) -> List<&2, U32>:
  [3, n]

# the key of the mark m
def Log.mark(m: String) -> List<&2, U32>:
  4 <> Codes.Code.text(m, [])

# the key of the first tip of the branch b, in the log of its store
def Log.start(b: String) -> List<&2, U32>:
  5 <> Codes.Code.text(b, [])

# the outcome of a request: its owners refused it as stale, or took it as the
# version of a number
type Out is Data:
  Out.Stale{}
  Out.Taken{number: U32}

# the words of the outcome o
def Out.words(o: Out) -> List<&2, U32>:
  match o:
    case Out.Stale{}:
      [0]
    case Out.Taken{n}:
      [1, n]

# the outcome that some words are
def Out.read(ws: List<&2, U32>) -> Maybe<&2, Out>:
  match ws:
    case Con{0, Nil{}}:
      Some{Out.Stale{}}
    case Con{1, Con{n, Nil{}}}:
      Some{Out.Taken{n}}
    case _:
      None{}

# a version: the request that made it, and the root of the content after it
type Version is Data:
  Version{id: Ledgers.Id, root: Maybe<&2, Hashes.Hash>}

# the words of the version v
def Version.words(v: Version) -> List<&2, U32>:
  match v:
    case Version{i, r}:
      Ledgers.Id.code(i, Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, r, []))

# the version that some words are
def Version.read(ws: List<&2, U32>) -> Maybe<&2, Version>:
  Read.whole(
    Version,
    Codes.Code.two.read(
      ~Ledgers.Id,
      ~Maybe<&2, Hashes.Hash>,
      ~Version,
      ~Ledgers.Id.code.read,
      ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
      i => r => Version{i, r},
      ws
    )
  )

# the request of the version v
def Version.id(v: Version) -> Ledgers.Id:
  match v:
    case Version{i, r}:
      i

# the root of the content of the version v
def Version.root(v: Version) -> Maybe<&2, Hashes.Hash>:
  match v:
    case Version{i, r}:
      r

# the owners of the next step of a line at the tip t
def Line.owners(s: State(), t: Tip) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, String>,
      Node.get(s, Tip.log(t), Log.owners()),
      ws => Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
    ),
    []
  )

# the count in the value ws
def Count.read(ws: List<&2, U32>) -> Maybe<&2, U32>:
  match ws:
    case Con{n, Nil{}}:
      Some{n}
    case _:
      None{}

# the count of versions of a line at the tip t
def Line.count(s: State(), t: Tip) -> U32:
  Maybe.default(
    &2,
    U32,
    Maybe.bind(&2, List<&2, U32>, U32, Node.get(s, Tip.log(t), Log.count()), ws => Count.read(ws)),
    0
  )

# the outcome of the request i on a line at the tip t (none: no step decided
# it yet)
def Line.out(s: State(), t: Tip, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Node.get(s, Tip.log(t), Log.out(i)), ws => Out.read(ws))

# the version of the number n of a line at the tip t
def Line.version(s: State(), t: Tip, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Version,
    Node.get(s, Tip.log(t), Log.version(n)),
    ws => Version.read(ws)
  )

# the version that the mark m names on a line at the tip t
def Line.mark(s: State(), t: Tip, m: String) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Node.get(s, Tip.log(t), Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# Heads
# -----

# the node's head of the line c, if it follows c
def Node.head_of(s: State(), c: Ledgers.Chain) -> Maybe<&2, Head>:
  Tries.Trie.get(Head, State.heads(s), Ledgers.Chain.key(c))

# the tip of the head h, when s holds it
def Head.tip(s: State(), h: Head) -> Maybe<&2, Tip>:
  match h:
    case Head{r, b, n, t}:
      Maybe.bind(&2, Hashes.Hash, Tip, t, x => Tip.at(s, x))

# what the line c holds now, as the node knows it
def Node.tip(+s: State(), c: Ledgers.Chain) -> Maybe<&2, Tip>:
  Maybe.bind(&2, Head, Tip, Node.head_of(s, c), h => Head.tip(s, h))

# what the log of the head h holds under the key k
def Head.get(+s: State(), h: Head, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Tip, List<&2, U32>, Head.tip(s, h), t => Node.get(s, Tip.log(t), k))

# what the log of the line c holds under the key k, as the node knows it
def Line.get(+s: State(), c: Ledgers.Chain, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Head, List<&2, U32>, Node.head_of(s, c), h => Head.get(s, h, k))

# the line that the request i of the change q changes: a request that starts a
# store changes the store of its own name
def Ask.chain(i: Ledgers.Id, q: Ask) -> Ledgers.Chain:
  match q:
    case Ask.Start{os}:
      Ledgers.Chain{i, None{}}
    case Ask.On{r, l, c}:
      Line.chain(r, l)

# the change of the request a
def Asked.ask(a: Ledgers.Asked<Ask>) -> Ask:
  match a:
    case Ledgers.Asked{t, q}:
      q

# the line of the request i, when s holds it
def Node.chain_of(s: State(), +i: Ledgers.Id) -> Maybe<&2, Ledgers.Chain>:
  Maybe.bind(
    &2,
    Ledgers.Asked<Ask>,
    Ledgers.Chain,
    Node.asked(s, i),
    a => Some{Ask.chain(i, Asked.ask(a))}
  )

# the outcome of the request i on the line c, as the node knows it
def Chain.out(s: State(), c: Ledgers.Chain, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Line.get(s, c, Log.out(i)), ws => Out.read(ws))

# the version of the number n of the line c, as the node knows it
def Chain.version(s: State(), c: Ledgers.Chain, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(&2, List<&2, U32>, Version, Line.get(s, c, Log.version(n)), ws => Version.read(ws))

# the version that the mark m names on the line c, as the node knows it
def Chain.mark(s: State(), c: Ledgers.Chain, m: String) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Line.get(s, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# the outcome of the request i (none: no step that the node knows decided it)
def Node.out(+s: State(), +i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, Ledgers.Chain, Out, Node.chain_of(s, i), c => Chain.out(s, c, i))

# the version of the outcome o on the line c, when it took one
def Out.on(s: State(), c: Ledgers.Chain, o: Out) -> Maybe<&2, Version>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Chain.version(s, c, n)

# the version that the request v made on the line c
def Chain.made(+s: State(), +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Out, Version, Chain.out(s, c, v), o => Out.on(s, c, o))

# the version that the request v made (none: v is not a version that the node
# knows)
def Node.made(+s: State(), +v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Ledgers.Chain, Version, Node.chain_of(s, v), +c => Chain.made(s, c, v))

# the root of the content of the version v (none: v is not a version)
def Node.root(s: State(), v: Ledgers.Id) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(&2, Version, Maybe<&2, Hashes.Hash>, Node.made(s, v), x => Some{Version.root(x)})

# the root of the content of the version m, if any (none, or not a version:
# the empty tree)
def Node.root_of(s: State(), m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Node.root(s, v), h => h)

# Ancestry
# --------
# A version came from the versions before it on its line, by number, and from
# those that its version vector names, at their numbers or before.

# a version's place: its line and its number
type Place is Data:
  Place{chain: Ledgers.Chain, number: U32}

# the place on the line c of the outcome o, when it took a version
def Out.place(c: Ledgers.Chain, o: Out) -> Maybe<&2, Place>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Some{Place{c, n}}

# the place of the version v on the line c, at the tip t
def Place.at(s: State(), c: Ledgers.Chain, v: Ledgers.Id, t: Tip) -> Maybe<&2, Place>:
  Maybe.bind(&2, Out, Place, Line.out(s, t, v), o => Out.place(c, o))

# the place of the version v on the line c
def Place.on(+s: State(), +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Tip, Place, Node.tip(s, c), t => Place.at(s, c, v, t))

# the place of the version v
def Node.place(+s: State(), +v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Ledgers.Chain, Place, Node.chain_of(s, v), +c => Place.on(s, c, v))

# the place a is at or after the place b, of the same line
def Place.covers(a: Place, b: Place) -> Bool:
  match a b:
    case Place{c1, n1} Place{c2, n2}:
      U32.is_le(n2, n1)

# the line of the place p
def Place.chain(p: Place) -> Ledgers.Chain:
  match p:
    case Place{c, n}:
      c

# the place of the line c in the value of a version vector's entry
def Place.read(c: Ledgers.Chain, ws: List<&2, U32>) -> Maybe<&2, Place>:
  match ws:
    case Con{n, Nil{}}:
      Some{Place{c, n}}
    case _:
      None{}

# the value of a version vector's entry at the place p
def Place.code(p: Place) -> List<&2, U32>:
  match p:
    case Place{c, n}:
      [n]

# the newest place of the line c that the content whose root is h came from
def Node.vector(s: State(), h: Maybe<&2, Hashes.Hash>, +c: Ledgers.Chain) -> Maybe<&2, Place>:
  Maybe.bind(&2, List<&2, U32>, Place, Node.get(s, h, Key.vector(c)), ws => Place.read(c, ws))

# the place q, if any, covers the place p
def Place.covered(m: Maybe<&2, Place>, p: Place) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{q}:
      Place.covers(q, p)

# the version at the place px, whose content has the root hx, came from the
# one at the place pv
def Place.from(s: State(), +px: Place, hx: Maybe<&2, Hashes.Hash>, +pv: Place) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Place.chain(px), Place.chain(pv)),
    u => Place.covers(px, pv),
    u => Place.covered(Node.vector(s, hx, Place.chain(pv)), pv)
  )

# Node.has once the places of x (mx) and of v (mv) and the root of x (mr) are
# known
def Has.of(
  s: State(),
  mx: Maybe<&2, Place>,
  mv: Maybe<&2, Place>,
  mr: Maybe<&2, Maybe<&2, Hashes.Hash>>
) -> Bool:
  match mx mv mr:
    case Some{px} Some{pv} Some{hx}:
      Place.from(s, px, hx, pv)
    case a b c:
      False{}

# x is v, or a version that v came from
def Node.has(+s: State(), +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Has.of(s, Node.place(s, x), Node.place(s, v), Node.root(s, x)),
    Ledgers.Id.is_eq(x, v)
  )

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(+s: State(), +x: Ledgers.Id, +y: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )

# Writes
# ------

# trees being written: the state with their new nodes, the root, and the new
# nodes
type Work is Data:
  Work{state: State(), root: Maybe<&2, Hashes.Hash>, nodes: List<&2, List<&2, U32>>}

# s with the words ds as data, when it then holds each of them under its hash
# (none: a slot holds other words). A node reads back what it puts, so what a
# tree or a rope reads after a put never rests on what the store held before
def State.put(s: State(), +ds: List<&2, List<&2, U32>>) -> Maybe<&2, State()>:
  +s2 = State.keep(s, ds)
  Shared.Maybe.when(State(), Trees.Tree.holds(~State(), ~Store.fetch, s2, ds), u => Some{s2})

# the work at the root h on the state m, with the new nodes ws before ns
def Work.put(
  m: Maybe<&2, State()>,
  h: Maybe<&2, Hashes.Hash>,
  ws: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> Maybe<&2, Work>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Work{s2, h, List.append(&2, List<&2, U32>, ws, ns)}}

# the work that the new subtree m gives, after the state s and the nodes ns
def Work.of(s: State(), ns: List<&2, List<&2, U32>>, m: Maybe<&2, Trees.Put>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Put{h, +ws}}:
      Work.put(State.put(s, ws), Some{h}, ws, ns)

# w with the key k set to the value x (none: the store lacks a node)
def Work.set(w: Work, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Work>:
  match w:
    case Work{+s, h, ns}:
      Work.of(s, ns, Node.set(s, h, k, x))

# w with the words ns as data, and among its new nodes
def Work.keep(w: Work, +ns: List<&2, List<&2, U32>>) -> Maybe<&2, Work>:
  match w:
    case Work{s, h, old}:
      Work.put(State.put(s, ns), h, ns, old)

# the root of w
def Work.root(w: Work) -> Maybe<&2, Hashes.Hash>:
  match w:
    case Work{s, h, ns}:
      h

# w with its root put back to h, keeping its state and nodes
def Work.at(w: Work, h: Maybe<&2, Hashes.Hash>) -> Work:
  match w:
    case Work{s, g, ns}:
      Work{s, h, ns}

# a verdict that takes the trees of m (none: wait)
def Work.take(m: Maybe<&2, Work>) -> Maybe<&2, Verdict>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, h, ns}}:
      Some{Verdict{True{}, h, ns}}

# w with the line c at the place p in its version vector, unless it holds that
# place or a newer one
def Vector.add(w: Work, +c: Ledgers.Chain, +p: Place) -> Maybe<&2, Work>:
  match w:
    case Work{+s, +h, +ns}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Place.covered(Node.vector(s, h, c), p),
        u => Some{Work{s, h, ns}},
        u => Work.set(Work{s, h, ns}, Key.vector(c), Place.code(p))
      )

# the line and place of a version vector's entry, from its binding
def Vector.entry(b: Trees.Binding) -> Maybe<&2, Place>:
  match b:
    case Trees.Binding{Con{4, k}, ws}:
      Maybe.bind(
        &2,
        Ledgers.Chain,
        Place,
        Read.whole(Ledgers.Chain, Ledgers.Chain.code.read(k)),
        c => Place.read(c, ws)
      )
    case _:
      None{}

# w with the entry p in its version vector, when it is of a line other than c
def Vector.add.if(+w: Work, c: Ledgers.Chain, m: Maybe<&2, Place>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      Some{w}
    case Some{+p}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Ledgers.Chain.is_eq(Place.chain(p), c),
        u => Some{w},
        u => Vector.add(w, Place.chain(p), p)
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

# what a merge keeps of a resource: the content of one side (none: removed),
# new bytes, or a clash
type Pick is Data:
  Pick.Take{root: Maybe<&2, Ropes.Root>}
  Pick.Make{bytes: Texts.Bytes()}
  Pick.Clash{}

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
def Pick.pointers(s: State(), x: Maybe<&2, Pointer>, y: Maybe<&2, Pointer>) -> Pick:
  match x y:
    case Some{+px} Some{+py}:
      Pick.module(Node.forward(s, Pointer.version(px), Pointer.version(py)), px, py)
    case _ _:
      Pick.Clash{}

# the merge of x and y, two changes of b, in the format f
def Pick.format(
  f: Formats.Format,
  s: State(),
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
  s: State(),
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
def Pick.base(s: State(), b: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  match b:
    case None{}:
      Some{[]}
    case Some{r}:
      Root.bytes(s, Some{r})

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f (none: wait for its bytes)
def Pick.both(
  f: Formats.Format,
  +s: State(),
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>
) -> Maybe<&2, Pick>:
  match o t:
    case Some{x} Some{y}:
      Pick.read(f, s, Pick.base(s, b), Root.bytes(s, Some{x}), Root.bytes(s, Some{y}))
    case _ _:
      Some{Pick.Clash{}}

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base, ours when theirs is the base or both
# agree, else both merged (none: wait for their bytes). So a merge never loses
# a change that only one side made
def Pick.merge(
  f: Formats.Format,
  s: State(),
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
      List.any.if(v => Roots.same(o, t), Roots.same(t, b)),
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
        Maybe.is_some(&2, Ropes.Root, Res.read(ws)),
        u => Read.whole(Resources.Name, Resources.Name.code.read(k)),
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
def Res.names(s: State(), h: Maybe<&2, Hashes.Hash>) -> List<&2, Resources.Name>:
  Res.of.bindings(Trees.Tree.list(~State(), ~Store.fetch, s, h))

# the key of the resource n
def Name.key(n: Resources.Name) -> List<&2, Bool>:
  Tries.Trie.text(Resources.Name.show(n))

# the resources that ours (the tree h) and theirs (ht) may hold differently,
# once each: a walk of both trees skips what they share, and where both hold
# the same bytes a merge keeps them (Format.merge_same)
def Merge.names(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>
) -> List<&2, Resources.Name>:
  Tries.Trie.unique(~Resources.Name, ~Name.key, 
    Res.of.bindings(Trees.Tree.diff(~State(), ~Store.fetch, s, h, ht)),
    Tries.Trie.new(Unit)
  )

# the groups of a store tree, as a graph
type Groups is Data:
  Groups{state: State(), root: Maybe<&2, Hashes.Hash>}

# the members of m in the groups g, when it is a group
def Group.succ(g: Groups, m: Member) -> List<&2, Member>:
  match g m:
    case Groups{s, h} Member.Node{n}:
      []
    case Groups{s, h} Member.Group{x}:
      Maybe.default(&2, List<&2, Member>, Members.in(s, h, x), [])

# the names of the groups in the store tree whose root is h
def Group.names(s: State(), h: Maybe<&2, Hashes.Hash>) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, String>,
      Node.get(s, h, Key.groups()),
      ws => Read.whole(List<&2, String>, Ledgers.Owners.code.read(ws))
    ),
    []
  )

# the groups of the names ns, as members
def Group.of.names(ns: List<&2, String>) -> List<&2, Member>:
  match ns:
    case Nil{}:
      []
    case Con{n, r}:
      Member.Group{n} <> Group.of.names(r)

# every group of the groups g, as a member
def Group.all(g: Groups) -> List<&2, Member>:
  match g:
    case Groups{s, h}:
      Group.of.names(Group.names(s, h))

# m is a member of the group g of the store tree h, or of a group inside g
def Group.is_inside(s: State(), h: Maybe<&2, Hashes.Hash>, m: Member, g: String) -> Bool:
  Reaches.Reach.in(
    ~Member,
    ~Groups,
    ~Member.is_eq,
    ~Group.succ,
    ~Group.all,
    Groups{s, h},
    Member.Group{g},
    m
  )

# the nodes among the members ms
def Group.nodes.of(ms: List<&2, Member>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Member.Node{n}, r}:
      n <> Group.nodes.of(r)
    case Con{Member.Group{g}, r}:
      Group.nodes.of(r)

# the nodes that each group of gs names, as they come
def Group.named.all(+g: Groups, gs: List<&2, Member>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{m, r}:
      List.append(&2, String, Group.nodes.of(Group.succ(g, m)), Group.named.all(g, r))

# the nodes that some group of gs names
def Group.named(g: Groups, gs: List<&2, Member>) -> List<&2, String>:
  Tries.Trie.unique(~String, ~Tries.Trie.text, Group.named.all(g, gs), Tries.Trie.new(Unit))

# the nodes of ns that are inside the group g of the store tree h
def Group.inside(
  +s: State(),
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
        Group.is_inside(s, h, Member.Node{n}, g)
      )

# the nodes inside the group g of the store tree h, each once: the nodes that
# own what g owns
def Group.nodes(+s: State(), +h: Maybe<&2, Hashes.Hash>, g: String) -> List<&2, String>:
  +gs = {Groups{s, h}: Groups}
  Group.inside(s, h, Group.named(gs, Group.all(gs)), g)

# the member m of a new set of the group g makes g contain itself
def Group.loops(s: State(), h: Maybe<&2, Hashes.Hash>, +g: String, m: Member) -> Bool:
  match m:
    case Member.Node{n}:
      False{}
    case Member.Group{+x}:
      List.any.if(u => Group.is_inside(s, h, Member.Group{g}, x), String.eq(x, g))

# some member of ms makes the group g of the store tree h contain itself
def Group.loops.any(
  +s: State(),
  +h: Maybe<&2, Hashes.Hash>,
  +g: String,
  ms: List<&2, Member>
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
def Judge.ready.of(m: Maybe<&2, Out>) -> Maybe<&2, Bool>:
  match m:
    case Some{Out.Taken{n}}:
      Some{True{}}
    case Some{Out.Stale{}}:
      Some{False{}}
    case None{}:
      None{}

# the verdict of the version v, for a request that names it
def Judge.ready(s: State(), v: Ledgers.Id) -> Maybe<&2, Bool>:
  Judge.ready.of(Node.out(s, v))

# the verdict of the version m, if any
def Judge.ready_maybe(s: State(), m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      Some{True{}}
    case Some{v}:
      Judge.ready(s, v)

# the verdict on the content c: its version must be one
def Judge.content(s: State(), c: Content) -> Maybe<&2, Bool>:
  match c:
    case Content.Root{x}:
      Some{True{}}
    case Content.Of{w}:
      Judge.ready(s, w)

# a refusal, which keeps the tree whose root is h
def Judge.refuse(h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Verdict>:
  Some{Verdict{False{}, h, []}}

# the verdict m, then k when m takes; a refusal keeps the tree h
def Judge.then(
  m: Maybe<&2, Bool>,
  h: Maybe<&2, Hashes.Hash>,
  k: Unit -> Maybe<&2, Verdict>
) -> Maybe<&2, Verdict>:
  match m:
    case Some{True{}}:
      k(Unit{})
    case Some{False{}}:
      Judge.refuse(h)
    case None{}:
      None{}

# k when b holds, else a refusal that keeps the tree h
def Judge.when(
  b: Bool,
  h: Maybe<&2, Hashes.Hash>,
  k: Unit -> Maybe<&2, Verdict>
) -> Maybe<&2, Verdict>:
  Shared.Bool.when(Maybe<&2, Verdict>, b, k, u => Judge.refuse(h))

# the root that the content c gives the resource n (none: the version holds
# none)
def Content.root(+s: State(), n: Resources.Name, c: Content) -> Maybe<&2, Ropes.Root>:
  match c:
    case Content.Root{x}:
      Some{x}
    case Content.Of{w}:
      Res.root(s, Node.root_of(s, Some{w}), n)

# the root that the content c gives the resource n, or that it gives none
# (none: the node lacks a node of the version's tree)
def Content.find(+s: State(), n: Resources.Name, c: Content) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  match c:
    case Content.Root{x}:
      Some{Some{x}}
    case Content.Of{w}:
      Res.find(s, Node.root_of(s, Some{w}), n)

# the verdict on a write of the resource n since base, with the content c, at
# the tree h: take it when n holds at h what it held at base. It waits for a
# node that it lacks: it does not refuse on what it cannot read
def Judge.write(
  +s: State(),
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Judge.ready_maybe(s, base),
    h,
    u => Judge.then(
      Judge.content(s, c),
      h,
      w => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Verdict,
        Res.find(s, h, n),
        a => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Verdict,
          Res.find(s, Node.root_of(s, base), n),
          b => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Verdict,
            Content.find(s, n, c),
            m => Judge.when(
              Roots.same(a, b),
              h,
              x => Work.take(Work.set(Work{s, h, []}, Key.res(n), Res.code(m)))
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
def Clash.open(s: State(), h: Maybe<&2, Hashes.Hash>, n: Resources.Name, f: Ledgers.Id) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    Node.get(s, h, Key.clash(n)),
    Some{Clash.code(f)}
  )

# the version that the request m merged, when m is a merge on the branch b of
# the store r
def Merge.from_on(m: Maybe<&2, Ledgers.Asked<Ask>>, r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  match m:
    case Some{Ledgers.Asked{t, Ask.On{st, Some{x}, Change.Merge{f}}}}:
      Shared.Maybe.when(Ledgers.Id, Bool.and(Ledgers.Id.is_eq(st, r), String.eq(x, b)), u => Some{f})
    case _:
      None{}

# the clash of the resource n is open in the tree h, by the merge of the
# version m, if any (none: the node lacks a node of the tree)
def Clash.find(
  s: State(),
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
        Node.find(s, h, Key.clash(n)),
        x => Some{
          Shared.Maybe.is_eq(~List<&2, U32>, ~Shared.List.is_eq(~U32, ~U32.is_eq), x, Some{Clash.code(f)})
        }
      )

# the verdict on a resolve of the resource n, which the merge k left in clash
# on the branch b of the store r, with the content c, at the tree h
def Judge.resolve(
  +s: State(),
  r: Ledgers.Id,
  b: String,
  +k: Ledgers.Id,
  +n: Resources.Name,
  +c: Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Judge.ready(s, k),
    h,
    u => Judge.then(
      Judge.content(s, c),
      h,
      w => Maybe.bind(
        &2,
        Bool,
        Verdict,
        Clash.find(s, h, n, Merge.from_on(Node.asked(s, k), r, b)),
        open => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Verdict,
          Content.find(s, n, c),
          m => Judge.when(
            open,
            h,
            x => Work.take(
              Maybe.bind(
                &2,
                Work,
                Work,
                Work.set(Work{s, h, []}, Key.res(n), Res.code(m)),
                y => Work.set(y, Key.clash(n), [])
              )
            )
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
  p: Pick,
  w: Work
) -> Maybe<&2, Work>:
  match p:
    case Pick.Take{m}:
      Work.set(w, Key.res(n), Res.code(m))
    case Pick.Make{x}:
      +rp = Bytes.rope(x)
      Maybe.bind(
        &2,
        Work,
        Work,
        Work.keep(w, Ropes.Put.nodes(rp)),
        w2 => Work.set(w2, Key.res(n), Res.code(Some{Ropes.Put.root(rp)}))
      )
    case Pick.Clash{}:
      Maybe.bind(
        &2,
        Work,
        Work,
        Work.set(w, Key.res(n), Res.code(o)),
        y => Work.set(y, Key.clash(n), Clash.code(f))
      )

# w with the resource n merged: what the merge of the base b, ours o and theirs
# t (of the version f) keeps (none: wait for a node)
def Merge.one(
  s: State(),
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
  +s: State(),
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
            Res.find(s, hb, n),
            b => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Work,
              Res.find(s, ho, n),
              o => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Work,
                Res.find(s, ht, n),
                x => Merge.one(s, f, n, b, o, x, w)
              )
            )
          )
        )
      )

# the request of the version v, as a version
def Version.some(v: Version) -> Maybe<&2, Ledgers.Id>:
  Some{Version.id(v)}

# the version of the number n of the line at the tip t
def Version.in(s: State(), n: U32, t: Tip) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(&2, Version, Ledgers.Id, Line.version(s, t, n), v => Version.some(v))

# the version at the place p
def Version.at(+s: State(), p: Place) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Place{c, n}:
      Maybe.bind(&2, Tip, Ledgers.Id, Node.tip(s, c), t => Version.in(s, n, t))

# the newer of two versions that both sides of a merge came from: a, a
# version of our line that theirs came from, and the version at the place p of
# their line cf that ours came from. a is the newer one when it came from the
# other
def Base.pick(
  +s: State(),
  cf: Ledgers.Chain,
  ma: Maybe<&2, Ledgers.Id>,
  mp: Maybe<&2, Place>
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
        Place.covered(Node.vector(s, Node.root_of(s, Some{a}), cf), p),
        u => Some{a},
        u => Version.at(s, p)
      )

# the base of a merge of from into the line c, whose tree is h: from itself
# when it is of c; else the newest version that both came from, by the version
# vectors of both sides (the version of c that from came from, or the version
# of from's line that h came from)
def Merge.base(
  +s: State(),
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    Place,
    Ledgers.Id,
    Node.place(s, from),
    +pf => Shared.Bool.when(
      Maybe<&2, Ledgers.Id>,
      Ledgers.Chain.is_eq(Place.chain(pf), c),
      u => Some{from},
      u => Base.pick(
        s,
        Place.chain(pf),
        Maybe.bind(
          &2,
          Place,
          Ledgers.Id,
          Node.vector(s, Node.root_of(s, Some{from}), c),
          w => Version.at(s, w)
        ),
        Node.vector(s, h, Place.chain(pf))
      )
    )
  )

# m with the version v, of a line other than c, in its version vector: its
# vector, and its own place
def Vector.joined(
  +s: State(),
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  m: Maybe<&2, Work>
) -> Maybe<&2, Work>:
  Maybe.bind(
    &2,
    Work,
    Work,
    Vector.adds(Trees.Tree.list(~State(), ~Store.fetch, s, Node.root_of(s, Some{v})), c, m),
    w => Vector.add.if(w, c, Node.place(s, v))
  )

# the trees of a merge of from into the line c, whose tree is h
def Merge.work(
  +s: State(),
  +c: Ledgers.Chain,
  +from: Ledgers.Id,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work>:
  +ht = Node.root_of(s, Some{from})
  Vector.joined(
    s,
    c,
    from,
    Merge.all(
      s,
      from,
      Merge.names(s, h, ht),
      Node.root_of(s, Merge.base(s, c, from, h)),
      h,
      ht,
      Some{Work{s, h, []}}
    )
  )

# the trees of a move of the line c, whose tree is h, to the version to: to's
# tree, with what the line came from added to its version vector
def Move.work(
  +s: State(),
  +c: Ledgers.Chain,
  +to: Ledgers.Id,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work>:
  Vector.joined(
    s,
    c,
    to,
    Vector.adds(
      Trees.Tree.list(~State(), ~Store.fetch, s, h),
      c,
      Some{Work{s, Node.root_of(s, Some{to}), []}}
    )
  )

# the first tree of a branch made at the version m, if any, of the line c: its
# tree, with what it came from in its version vector
def Make.branch(+s: State(), c: Ledgers.Chain, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      Some{Work{s, None{}, []}}
    case Some{+v}:
      Vector.joined(s, c, v, Some{Work{s, Node.root_of(s, Some{v}), []}})

# the store tree h with the group g, of the members ms, and its name among the
# names of its groups
def Group.work(+s: State(), +h: Maybe<&2, Hashes.Hash>, +g: String, ms: List<&2, Member>) -> Maybe<&2, Work>:
  +ns = Group.names(s, h)
  Maybe.bind(
    &2,
    Work,
    Work,
    Work.set(Work{s, h, []}, Key.group(g), Members.code(ms, [])),
    +w => Shared.Bool.when(
      Maybe<&2, Work>,
      List.contains(~String, ~String.eq, ns, g),
      u => Some{w},
      u => Work.set(w, Key.groups(), Ledgers.Owners.code(g <> ns, []))
    )
  )

# the owners os are the nodes ns, and there is one
def Own.fits(+os: List<&2, String>, ns: List<&2, String>) -> Bool:
  List.all.if(u => Ledgers.Owners.is_eq(os, ns), Bool.not(List.is_empty(&2, String, os)))

# the first log of a line whose owners are os, on the trees of w
def Log.first(w: Work, os: List<&2, String>) -> Maybe<&2, Work>:
  Work.set(Work.at(w, None{}), Log.owners(), Ledgers.Owners.code(os, []))

# the first tip of a new branch, with the new nodes of its trees
type Made is Data:
  Made{tip: Tip, nodes: List<&2, List<&2, U32>>}

# the first tip of a branch whose content is c, once its first log is on the
# trees of m
def Made.of(+c: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Work>) -> Maybe<&2, Made>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, +l, ns}}:
      Some{Made{Tip{c, l}, Tip.words(Tip{c, l}) <> ns}}

# the first tip of a new branch, from its first content (the root of start),
# with a log whose owners are the store's owners os now
def Make.first(start: Maybe<&2, Work>, +os: List<&2, String>) -> Maybe<&2, Made>:
  Maybe.bind(&2, Work, Made, start, +w => Made.of(Work.root(w), Log.first(w, os)))

# the store tree in which an Own of the line l, at the content h, reads its
# group: a store reads its own content; a branch, the content of the version
# at of its store
def Own.tree(
  s: State(),
  l: Maybe<&2, String>,
  at: Maybe<&2, Ledgers.Id>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Hashes.Hash>:
  match l at:
    case Some{b} Some{v}:
      Node.root_of(s, Some{v})
    case x y:
      h

# the version at is a version of the store r: at the place m
def Own.at(r: Ledgers.Id, m: Maybe<&2, Place>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      None{}
    case Some{Place{c, n}}:
      Some{Ledgers.Chain.is_eq(c, Ledgers.Chain{r, None{}})}

# an Own of the line l of the store r may name the version at: a store reads
# its own content; a branch names a version of its store (none: wait for it)
def Own.ok(s: State(), r: Ledgers.Id, l: Maybe<&2, String>, at: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Bool>:
  match l at:
    case None{} y:
      Some{True{}}
    case Some{b} None{}:
      Some{False{}}
    case Some{b} Some{v}:
      Own.at(r, Node.place(s, v))

# the node holds the members of each group of ns of the store tree h
def Groups.held.all(+s: State(), +h: Maybe<&2, Hashes.Hash>, ns: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case Con{n, r}:
      List.all.if(
        u => Groups.held.all(s, h, r),
        Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, Node.find(s, h, Key.group(n)))
      )

# the node holds the groups of the store tree h: their names, and the members
# of each. Only then does it know which nodes are inside a group
def Groups.held(+s: State(), +h: Maybe<&2, Hashes.Hash>) -> Bool:
  List.all.if(
    u => Groups.held.all(s, h, Group.names(s, h)),
    Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, Node.find(s, h, Key.groups()))
  )

# Own.takes once whether the Own may name its version is known (k), in the
# store tree h (none: wait for the groups)
def Own.takes.at(
  +s: State(),
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
  +s: State(),
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
  +s: State(),
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Verdict>:
  Judge.then(
    Own.takes(s, r, l, g, at, os, h),
    h,
    u => Work.take(Work.set(Work{s, h, []}, Key.owner(), Codes.Code.text(g, [])))
  )

# the verdict on the change c of the line l of the store r, at the content h,
# when the owners of the line are os
def Judge.change(
  +s: State(),
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Change,
  +h: Maybe<&2, Hashes.Hash>,
  os: List<&2, String>
) -> Maybe<&2, Verdict>:
  match l c:
    case None{} Change.Group{+g, +ms}:
      Judge.when(Bool.not(Group.loops.any(s, h, g, ms)), h, u => Work.take(Group.work(s, h, g, ms)))
    case None{} Change.Key{n, k}:
      Work.take(Work.set(Work{s, h, []}, Key.seal(n), Hashes.Hash.code(k, [])))
    case w Change.Own{g, at, os2}:
      Own.change(s, r, w, g, at, os2, h)
    case Some{b} Change.Write{n, base, c2}:
      Judge.write(s, n, base, c2, h)
    case Some{+b} Change.Resolve{k, n, c2}:
      Judge.resolve(s, r, b, k, n, c2, h)
    case Some{+b} Change.Merge{+from}:
      Judge.then(
        Judge.ready(s, from),
        h,
        u => Work.take(Merge.work(s, Line.chain(r, Some{b}), from, h))
      )
    case Some{+b} Change.Move{+to}:
      Judge.then(
        Judge.ready(s, to),
        h,
        u => Work.take(Move.work(s, Line.chain(r, Some{b}), to, h))
      )
    case w c3:
      Judge.refuse(h)

# Steps
# -----
# A step runs a batch of requests, in order, from a tip: each request gets its
# outcome in the log, once, and a request that the log holds already is
# skipped. A run is a function of the tip, the requests and the versions that
# they name, so every node that runs a step gets the same tip.

# a run: the state with its new nodes, the tip so far, and the new nodes
type Run is Data:
  Run{state: State(), tip: Tip, nodes: List<&2, List<&2, U32>>}

# the state of the run r
def Run.state(r: Run) -> State():
  match r:
    case Run{s, t, ns}:
      s

# the tip of the run r
def Run.tip(r: Run) -> Tip:
  match r:
    case Run{s, t, ns}:
      t

# the run of the content c and the new log m
def Run.of(c: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Work>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, l, ns}}:
      Some{Run{s, Tip{c, l}, ns}}

# the run r with the key k of its log set to x (none: the node lacks a node)
def Run.log(r: Run, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Run>:
  match r:
    case Run{s, Tip{c, l}, ns}:
      Run.of(c, Work.set(Work{s, l, ns}, k, x))

# the run on the state m, at the tip t, with the new nodes ds before ns
def Run.put(
  m: Maybe<&2, State()>,
  t: Tip,
  ds: List<&2, List<&2, U32>>,
  ns: List<&2, List<&2, U32>>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{s2}:
      Some{Run{s2, t, List.append(&2, List<&2, U32>, ds, ns)}}

# Run.add once the value m of the key in the log is known
def Run.add.at(r: Run, k: List<&2, U32>, x: List<&2, U32>, m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      Run.log(r, k, x)
    case Some{old}:
      None{}

# the run r with the new key k of its log set to x (none: the log holds k, or
# the node lacks a node). A log only gains keys: an outcome, a version and a
# mark are written once
def Run.add(+r: Run, +k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Run>:
  Run.add.at(r, k, x, Node.get(Run.state(r), Tip.log(Run.tip(r)), k))

# the run r with the content h, and its new nodes ds
def Run.content(r: Run, h: Maybe<&2, Hashes.Hash>, +ds: List<&2, List<&2, U32>>) -> Maybe<&2, Run>:
  match r:
    case Run{s, Tip{c, l}, ns}:
      Run.put(State.put(s, ds), Tip{h, l}, ds, ns)

# the run r with the owners os of the next step, if the change gives any
def Run.owners(r: Run, m: Maybe<&2, List<&2, String>>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      Some{r}
    case Some{os}:
      Run.log(r, Log.owners(), Ledgers.Owners.code(os, []))

# the run r, after it refused the request i as stale
def Step.stale(r: Run, i: Ledgers.Id) -> Maybe<&2, Run>:
  Run.add(r, Log.out(i), Out.words(Out.Stale{}))

# the run r, after it took the request i as the version of the number n: its
# outcome, its version (the content of r), the count, and the owners that it
# gives
def Step.taken.at(
  r: Run,
  +i: Ledgers.Id,
  +n: U32,
  own: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Run>:
  Maybe.bind(
    &2,
    Run,
    Run,
    Run.add(r, Log.out(i), Out.words(Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Run,
      Run,
      Run.add(r1, Log.version(n), Version.words(Version{i, Tip.content(Run.tip(r1))})),
      r2 => Maybe.bind(&2, Run, Run, Run.log(r2, Log.count(), [U32.inc(n)]), r3 => Run.owners(r3, own))
    )
  )

# the run r, after it took the request i as its next version
def Step.taken(+r: Run, i: Ledgers.Id, own: Maybe<&2, List<&2, String>>) -> Maybe<&2, Run>:
  Step.taken.at(r, i, Line.count(Run.state(r), Run.tip(r)), own)

# the run r, after the verdict m on the request i (none: wait)
def Step.judged(
  r: Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Verdict>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Verdict{False{}, h, ds}}:
      Step.stale(r, i)
    case Some{Verdict{True{}, h, ds}}:
      Maybe.bind(&2, Run, Run, Run.content(r, h, ds), r2 => Step.taken(r2, i, own))

# the run r with the mark m on the version v, then the request i taken
def Step.marked(r: Run, i: Ledgers.Id, m: String, v: Maybe<&2, Version>) -> Maybe<&2, Run>:
  match v:
    case None{}:
      None{}
    case Some{x}:
      Maybe.bind(
        &2,
        Run,
        Run,
        Run.add(r, Log.mark(m), Ledgers.Id.code(Version.id(x), [])),
        r2 => Step.taken(r2, i, None{})
      )

# the run r, after a request i for the mark m: it names the newest version,
# for good; a mark that the line has, or a line with no version, refuses it
def Step.mark(+r: Run, +i: Ledgers.Id, +m: String) -> Maybe<&2, Run>:
  +s = Run.state(r)
  +t = Run.tip(r)
  +n = Line.count(s, t)
  Shared.Bool.when(
    Maybe<&2, Run>,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    u => Step.marked(r, i, m, Line.version(s, t, U32.sub(n, 1))),
    u => Step.stale(r, i)
  )

# the run r with the first tip m of the new branch b of its store in its log,
# then the request i taken (none: the node lacks a node)
def Branch.made(+r: Run, +i: Ledgers.Id, +b: String, m: Maybe<&2, Made>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Made{+t, +ds}}:
      Maybe.bind(
        &2,
        Run,
        Run,
        Run.content(r, Tip.content(Run.tip(r)), ds),
        +r1 => Maybe.bind(
          &2,
          Run,
          Run,
          Run.add(r1, Log.start(b), Hashes.Hash.code(Tip.hash(t), [])),
          r2 => Step.taken(r2, i, None{})
        )
      )

# Step.branch once it is known whether the version that the branch starts at
# is one (m; none: wait for it)
def Branch.ready(
  +r: Run,
  +i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{False{}}:
      Step.stale(r, i)
    case Some{True{}}:
      Branch.made(
        r,
        i,
        b,
        Make.first(
          Make.branch(Run.state(r), Line.chain(st, Some{b}), at),
          Line.owners(Run.state(r), Run.tip(r))
        )
      )

# Step.branch once what the log of the store holds for the branch is known
# (m; none: the node lacks a part of the log)
def Branch.new(
  +r: Run,
  +i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Some{x}}:
      Step.stale(r, i)
    case Some{None{}}:
      Branch.ready(r, i, st, b, at, Judge.ready_maybe(Run.state(r), at))

# the run r of a store, after the request i for a new branch b from the
# version at: the log gets the first tip of b, for good; a store makes a
# branch once, so a branch that it has refuses the request
def Step.branch(+r: Run, +i: Ledgers.Id, st: Ledgers.Id, +b: String, +at: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Run>:
  Branch.new(r, i, st, b, at, Node.find(Run.state(r), Tip.log(Run.tip(r)), Log.start(b)))

# the run r, after the request i of the change ch of the line l of the store
# st
def Step.on(+r: Run, i: Ledgers.Id, st: Ledgers.Id, l: Maybe<&2, String>, ch: Change) -> Maybe<&2, Run>:
  match l ch:
    case Some{b} Change.Mark{m, d}:
      Step.mark(r, i, m)
    case None{} Change.Branch{+b, +at}:
      Step.branch(r, i, st, b, at)
    case x +y:
      +s = Run.state(r)
      +t = Run.tip(r)
      Step.judged(
        r,
        i,
        Change.owners(y),
        Judge.change(s, st, x, y, Tip.content(t), Line.owners(s, t))
      )

# the run r of the line c, after the request i of q: a request of another
# line, or one that starts a store, is stale here
def Step.change(+r: Run, c: Ledgers.Chain, +i: Ledgers.Id, q: Ask) -> Maybe<&2, Run>:
  match q:
    case Ask.Start{os}:
      Step.stale(r, i)
    case Ask.On{+st, +l, ch}:
      Shared.Bool.when(
        Maybe<&2, Run>,
        Ledgers.Chain.is_eq(Line.chain(st, l), c),
        u => Step.on(r, i, st, l, ch),
        u => Step.stale(r, i)
      )

# the run r of the line c, after the request i, which the node holds as a
# (none: wait for the request)
def Step.asked(r: Run, c: Ledgers.Chain, i: Ledgers.Id, a: Maybe<&2, Ledgers.Asked<Ask>>) -> Maybe<&2, Run>:
  match a:
    case None{}:
      None{}
    case Some{Ledgers.Asked{t, q}}:
      Step.change(r, c, i, q)

# the run r of the line c, after the request i, whose outcome in the log is o:
# a request that has one is skipped
def Step.fresh(+r: Run, c: Ledgers.Chain, +i: Ledgers.Id, o: Maybe<&2, Out>) -> Maybe<&2, Run>:
  match o:
    case Some{x}:
      Some{r}
    case None{}:
      Step.asked(r, c, i, Node.asked(Run.state(r), i))

# the run r of the line c, after the request i
def Step.one(+r: Run, c: Ledgers.Chain, +i: Ledgers.Id) -> Maybe<&2, Run>:
  Step.fresh(r, c, i, Line.out(Run.state(r), Run.tip(r), i))

# the run m of the line c, after each request of is, in order
def Step.all(+c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, m: Maybe<&2, Run>) -> Maybe<&2, Run>:
  match qs:
    case Nil{}:
      m
    case Con{i, rest}:
      Step.all(c, rest, Maybe.bind(&2, Run, Run, m, r => Step.one(r, c, i)))

# the requests of a step that a node can run now, in order, and the run after
# them
type Picked is Data:
  Picked{run: Run, asks: List<&2, Ledgers.Id>}

# the run of p
def Picked.run(p: Picked) -> Run:
  match p:
    case Picked{r, qs}:
      r

# the requests of p
def Picked.asks(p: Picked) -> List<&2, Ledgers.Id>:
  match p:
    case Picked{r, qs}:
      qs

# p, with the request i before its requests when b holds
def Picked.add(b: Bool, i: Ledgers.Id, p: Picked) -> Picked:
  match p:
    case Picked{r, qs}:
      Picked{r, List.filter.put(Ledgers.Id, i, qs, b)}

# the requests of qs that can run now on the line c, from the run r, and the
# run after them. A request that must wait (for a version, a request or a
# node) is left out: it waits, and does not stop the others
def Step.some(+c: Ledgers.Chain, qs: List<&2, Ledgers.Id>, +r: Run) -> Picked:
  match qs:
    case Nil{}:
      Picked{r, []}
    case Con{+i, rest}:
      +m = Step.one(r, c, i)
      Picked.add(
        Maybe.is_some(&2, Run, m),
        i,
        Step.some(c, rest, Maybe.default(&2, Run, m, r))
      )

# the step of the line c that runs the requests qs from the tip t (none: wait
# for a request, a version or a node)
def Step.run(s: State(), c: Ledgers.Chain, t: Tip, qs: List<&2, Ledgers.Id>) -> Maybe<&2, Run>:
  Step.all(c, qs, Some{Run{s, t, []}})

# The node
# --------
# A node takes in requests and what other nodes send, casts its ballot for the
# next step of each line that it owns, and moves each head along the steps
# that are decided.

# Seals
# -----
# A node signs each ballot. Its ballots in one store are a chain: each names
# the place of the one before it and the key of the next one, so a key signs
# once (Seals). The store gives a node the first key of its chain (a first
# owner's in the request that starts the store, then by a Key change). A node
# keeps a ballot only when it is the next of its chain and the key of the
# chain signs it, so a ledger holds no ballot that its node did not check.

# the place of the ballot b
def Ballot.at(b: Ledgers.Ballot) -> Ledgers.Where:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      w

# the node of the ballot b
def Ballot.node(b: Ledgers.Ballot) -> String:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      n

# the place of the ballot before b in its chain
def Ballot.prev(b: Ledgers.Ballot) -> Maybe<&2, Ledgers.Where>:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      p

# the key of the ballot after b in its chain
def Ballot.next(b: Ledgers.Ballot) -> Hashes.Hash:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      k

# the store of the place w
def Where.store(w: Ledgers.Where) -> Ledgers.Id:
  match w:
    case Ledgers.Where{Ledgers.Chain{r, k}, h, z}:
      r

# the line of the place w
def Where.line(w: Ledgers.Where) -> Ledgers.Chain:
  match w:
    case Ledgers.Where{c, h, z}:
      c

# the store of the ballot b
def Ballot.store(b: Ledgers.Ballot) -> Ledgers.Id:
  Where.store(Ballot.at(b))

# the key of the chain of the node n in the store r
def Seal.slot(r: Ledgers.Id, n: String) -> List<&2, Bool>:
  List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# a and b are the same place, or both none
def Prev.same(a: Maybe<&2, Ledgers.Where>, b: Maybe<&2, Ledgers.Where>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Codes.Code.is_eq(~Ledgers.Where, ~Ledgers.Where.code, x, y)
    case x y:
      False{}

# the key in the value m, if any
def Seal.read(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Hashes.Hash,
    m,
    ws => Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
  )

# the first key that the store r gave the node n, as s knows the store
def Seal.first(+s: State(), r: Ledgers.Id, n: String) -> Maybe<&2, Hashes.Hash>:
  Seal.read(
    Node.get(
      s,
      Maybe.bind(&2, Tip, Hashes.Hash, Node.tip(s, Ledgers.Chain{r, None{}}), t => Tip.content(t)),
      Key.seal(n)
    )
  )

# the chain c, when it starts from the first key m; else a new chain from m
# (none: the store gave the node no key)
def Chained.from(m: Maybe<&2, Hashes.Hash>, c: Maybe<&2, Chained>) -> Maybe<&2, Chained>:
  match m c:
    case None{} y:
      None{}
    case Some{k} None{}:
      Some{Chained{0, None{}, k, k}}
    case Some{+k} Some{Chained{n, l, x, +f}}:
      Some{
        Shared.Bool.when(
          Chained,
          Hashes.Hash.is_eq(f, k),
          u => Chained{n, l, x, f},
          u => Chained{0, None{}, k, k}
        )
      }

# the chains of the keys ks
def Keys.chains(ks: Keys) -> Tries.Trie<Chained>:
  match ks:
    case Keys{seed, cs, as, rs}:
      cs

# the secret seed of the keys ks
def Keys.seed(ks: Keys) -> Hashes.Hash:
  match ks:
    case Keys{seed, cs, as, rs}:
      seed

# ks, with the request i asked at this node
def Keys.mark(ks: Keys, i: Ledgers.Id) -> Keys:
  match ks:
    case Keys{seed, cs, as, rs}:
      Keys{seed, cs, Tries.Trie.set(Unit, as, Ledgers.Id.key(i), Unit{}), rs}

# the request i was asked at this node
def Keys.asked(ks: Keys, i: Ledgers.Id) -> Bool:
  match ks:
    case Keys{seed, cs, as, rs}:
      Tries.Trie.has(Unit, as, Ledgers.Id.key(i))

# ks with the chain c at the key k
def Keys.set(ks: Keys, k: List<&2, Bool>, c: Chained) -> Keys:
  match ks:
    case Keys{seed, cs, as, rs}:
      Keys{seed, Tries.Trie.set(Chained, cs, k, c), as, rs}

# the highest round, in the rounds rs, of the height h of the line c (0: the
# first round)
def Rounds.at(rs: Tries.Trie<Nat>, c: Ledgers.Chain, h: U32) -> Nat:
  Maybe.default(&2, Nat, Tries.Trie.get(Nat, rs, Ledgers.Slot.height(c, h)), 0n)

# the rounds of the keys ks
def Keys.rounds(ks: Keys) -> Tries.Trie<Nat>:
  match ks:
    case Keys{seed, cs, as, rs}:
      rs

# ks, which saw a ballot at the place w: the highest round of its height
def Keys.saw(ks: Keys, w: Ledgers.Where) -> Keys:
  match ks w:
    case Keys{seed, cs, as, +rs} Ledgers.Where{+c, +h, +r}:
      Keys{
        seed,
        cs,
        as,
        Shared.Bool.when(
          Tries.Trie<Nat>,
          Nat.is_lt(Rounds.at(rs, c, h), r),
          u => Tries.Trie.set(Nat, rs, Ledgers.Slot.height(c, h), r),
          u => rs
        )
      }

# the highest round of the height h of the line c of which s holds a ballot
def Round.seen(s: State(), c: Ledgers.Chain, h: U32) -> Nat:
  Rounds.at(Keys.rounds(State.keys(s)), c, h)

# the chain of the node n in the store r, as s knows it
def Seal.chain(+s: State(), +r: Ledgers.Id, +n: String) -> Maybe<&2, Chained>:
  Chained.from(
    Seal.first(s, r, n),
    Tries.Trie.get(Chained, Keys.chains(State.keys(s)), Seal.slot(r, n))
  )

# the ballot b is the next of the chain c, and the key of c signs it
def Seal.fits(c: Chained, +b: Ledgers.Ballot) -> Bool:
  match c:
    case Chained{n, last, key, f}:
      List.all.if(u => Ledgers.Ballot.sealed(key, b), Prev.same(Ballot.prev(b), last))

# the chain c after its next ballot b
def Chained.next(c: Chained, +b: Ledgers.Ballot) -> Chained:
  match c:
    case Chained{n, last, key, f}:
      Chained{U32.inc(n), Some{Ballot.at(b)}, Ballot.next(b), f}

# Seal.accept once the chain m of the ballot's node is known
def Seal.accept.at(+s: State(), +b: Ledgers.Ballot, m: Maybe<&2, Chained>) -> Maybe<&2, State()>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Shared.Maybe.when(
        State(),
        Seal.fits(c, b),
        u => Some{
          State.keyed(
            State.led(
              s,
              Ledgers.State.keep(~Ask, ~Ask.is_eq, State.ledger(s), b)
            ),
            Keys.saw(
              Keys.set(State.keys(s), Seal.slot(Ballot.store(b), Ballot.node(b)), Chained.next(c, b)),
              Ballot.at(b)
            )
          )
        }
      )

# s with the ballot b, when it is the next of its node's chain in its store
# and the key of the chain signs it (none: not now)
def Seal.accept(+s: State(), +b: Ledgers.Ballot) -> Maybe<&2, State()>:
  Seal.accept.at(s, b, Seal.chain(s, Ballot.store(b), Ballot.node(b)))

# the secret of the ballot of the number j of a node in the store r, from the
# node's seed
def Seal.secret(seed: Hashes.Hash, r: Ledgers.Id, j: U32) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, Ledgers.Id.code(r, [j])))

# the key of the place m, if any
def Prev.key(m: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  match m:
    case None{}:
      [False{}]
    case Some{w}:
      True{} <> Ledgers.Slot.vote(w, "")

# the key of where the ballot after the one at last waits, for the node n in
# the store r
def Seal.link(r: Ledgers.Id, n: String, last: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  List.append(
    &2,
    Bool,
    Seal.slot(r, n),
    Prev.key(last)
  )

# the ballots bs, each at the key of where it waits in its chain
def Pending.of(bs: List<&2, Ledgers.Ballot>) -> Tries.Trie<Ledgers.Ballot>:
  match bs:
    case Nil{}:
      Tries.Trie.new(Ledgers.Ballot)
    case Con{+b, r}:
      Tries.Trie.set(
        Ledgers.Ballot,
        Pending.of(r),
        Seal.link(Ballot.store(b), Ballot.node(b), Ballot.prev(b)),
        b
      )

# the last place of the chain c
def Chained.last(c: Chained) -> Maybe<&2, Ledgers.Where>:
  match c:
    case Chained{n, last, key, f}:
      last

# the ballot of p that is the next of the chain of the node n in the store r
def Pending.next(
  s: State(),
  p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String
) -> Maybe<&2, Ledgers.Ballot>:
  Maybe.bind(
    &2,
    Chained,
    Ledgers.Ballot,
    Seal.chain(s, r, n),
    c => Tries.Trie.get(Ledgers.Ballot, p, Seal.link(r, n, Chained.last(c)))
  )

# s with each ballot of p that the chain of the node n in the store r leads
# to, from the ballot mb, f ballots at most
def Sealed.follow(
  f: Nat,
  +s: State(),
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> State():
  match f mb:
    case 1n+g Some{b}:
      Maybe.default(
        &2,
        State(),
        Maybe.bind(
          &2,
          State(),
          State(),
          Seal.accept(s, b),
          +s2 => Some{Sealed.follow(g, s2, p, r, n, Pending.next(s2, p, r, n))}
        ),
        s
      )
    case x y:
      s

# s with the ballots of p that the chains of the ballots bs lead to
def Sealed.each(+f: Nat, bs: List<&2, Ledgers.Ballot>, +p: Tries.Trie<Ledgers.Ballot>, +s: State()) -> State():
  match bs:
    case Nil{}:
      s
    case Con{+b, rest}:
      Sealed.each(
        f,
        rest,
        p,
        Sealed.follow(
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(s, p, Ballot.store(b), Ballot.node(b))
        )
      )

# s with each ballot of bs that its node's chain leads to and its key signs:
# the cost is about that of the ballots, in any order
def Sealed.take(+bs: List<&2, Ledgers.Ballot>, s: State()) -> State():
  Sealed.each(List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s)

# the height of the next step of the head h
def Head.next(h: Head) -> U32:
  match h:
    case Head{r, b, n, t}:
      n

# s with the head h of the line c
def State.head(s: State(), c: Ledgers.Chain, h: Head) -> State():
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, Tries.Trie.set(Head, hs, Ledgers.Chain.key(c), h), ws, ks}

# the requests of the line c that wait for a step, in the order that the node
# took them in
def Wait.of(s: State(), c: Ledgers.Chain) -> List<&2, Ledgers.Id>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Tries.Trie.get(List<&2, Ledgers.Id>, State.waiting(s), Ledgers.Chain.key(c)),
    []
  )

# ws with the requests qs waiting at the key k: a line with no waiting request
# has no entry, so the lines that wait are read without a walk of every line
def Wait.put(
  ws: Tries.Trie<List<&2, Ledgers.Id>>,
  k: List<&2, Bool>,
  qs: List<&2, Ledgers.Id>
) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match qs:
    case Nil{}:
      Tries.Trie.drop(List<&2, Ledgers.Id>, ws, k)
    case Con{i, r}:
      Tries.Trie.set(List<&2, Ledgers.Id>, ws, k, Con{i, r})

# s with the requests qs waiting on the line c
def Wait.set(s: State(), c: Ledgers.Chain, qs: List<&2, Ledgers.Id>) -> State():
  match s:
    case Node{l, hs, ws, ks}:
      Node{l, hs, Wait.put(ws, Ledgers.Chain.key(c), qs), ks}

# s with the request i waiting on the line c, after those that wait
def State.wait(+s: State(), +c: Ledgers.Chain, i: Ledgers.Id) -> State():
  Wait.set(s, c, List.append(&2, Ledgers.Id, Wait.of(s, c), [i]))

# the requests of qs whose keys done does not hold
def Wait.left(qs: List<&2, Ledgers.Id>, +done: Tries.Trie<Unit>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(
        Ledgers.Id,
        i,
        Wait.left(r, done),
        Bool.not(Tries.Trie.has(Unit, done, Ledgers.Id.key(i)))
      )

# s at the head h of the line c, after a step that ran the requests qs: they
# wait no more
def State.moved(+s: State(), +c: Ledgers.Chain, h: Head, qs: List<&2, Ledgers.Id>) -> State():
  State.head(
    Wait.set(
      s,
      c,
      Wait.left(
        Wait.of(s, c),
        Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
      )
    ),
    c,
    h
  )

# State.first once the head m of the line is known
def First.at(s: State(), c: Ledgers.Chain, h: Head, m: Maybe<&2, Head>) -> State():
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      s
    case x:
      State.head(s, c, h)

# s with the first head h of the line c, when the line has no tip: a line
# that has a tip moves only by a step
def State.first(+s: State(), +c: Ledgers.Chain, h: Head) -> State():
  First.at(s, c, h, Node.head_of(s, c))

# the state m with the first head h of the line c, else s
def Start.head(s: State(), m: Maybe<&2, State()>, c: Ledgers.Chain, h: Head) -> State():
  match m:
    case None{}:
      s
    case Some{s2}:
      State.first(State.led(s, State.ledger(s2)), c, h)

# w with the first key of each first owner of os
def Seal.firsts(os: List<&2, Owner>, m: Maybe<&2, Work>) -> Maybe<&2, Work>:
  match os:
    case Nil{}:
      m
    case Con{Owner{n, k}, r}:
      Seal.firsts(
        r,
        Maybe.bind(&2, Work, Work, m, w => Work.set(w, Key.seal(n), Hashes.Hash.code(k, [])))
      )

# s with the first tip of the store i, whose content is c and whose log is on
# the trees of m: its owners are the store's first owners
def Start.put(s: State(), +i: Ledgers.Id, c: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Work>) -> State():
  match m:
    case None{}:
      s
    case Some{Work{s2, l, ns}}:
      +t = {Tip{c, l}: Tip}
      Start.head(
        s,
        State.put(s2, [Tip.words(t)]),
        Ledgers.Chain{i, None{}},
        Head{i, None{}, 0, Some{Tip.hash(t)}}
      )

# Node.start once the content m of the store is known
def Start.with(s: State(), i: Ledgers.Id, os: List<&2, String>, m: Maybe<&2, Work>) -> State():
  match m:
    case None{}:
      s
    case Some{+w}:
      Start.put(s, i, Work.root(w), Log.first(w, os))

# s, which follows the store that the request i starts with the first owners
# os: its content holds their first keys
def Node.start(+s: State(), i: Ledgers.Id, +os: List<&2, Owner>) -> State():
  Start.with(s, i, Owner.names(os), Seal.firsts(os, Some{Work{s, None{}, []}}))

# the first tip of the branch b of a store whose tip is m, if the store made
# b: the log of the store holds it, written once, so every node opens the
# branch at the same tip (Chain.start_final)
def Branch.first(s: State(), b: String, m: Maybe<&2, Tip>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.bind(
        &2,
        List<&2, U32>,
        Hashes.Hash,
        Node.get(s, Tip.log(t), Log.start(b)),
        ws => Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
      )

# Node.open once the head m of the line is known
def Open.at(+s: State(), c: Ledgers.Chain, m: Maybe<&2, Head>) -> State():
  match m:
    case Some{Head{+r, Some{+b}, n, None{}}}:
      State.head(
        s,
        c,
        Head{r, Some{b}, 0, Branch.first(s, b, Node.tip(s, Ledgers.Chain{r, None{}}))}
      )
    case x:
      s

# s, which follows the line c: a branch that the node waits for opens at its
# first tip, once the store that the node follows made it
def Node.open(+s: State(), +c: Ledgers.Chain) -> State():
  Open.at(s, c, Node.head_of(s, c))

# s, which follows the line l of the store r, when the head m says that it
# does not yet
def Follow.new(s: State(), +r: Ledgers.Id, +l: Maybe<&2, String>, m: Maybe<&2, Head>) -> State():
  match m:
    case Some{h}:
      s
    case None{}:
      State.head(s, Line.chain(r, l), Head{r, l, 0, None{}})

# s, which follows the line l of the store r
def Node.follow(+s: State(), +r: Ledgers.Id, +l: Maybe<&2, String>) -> State():
  Follow.new(s, r, l, Node.head_of(s, Line.chain(r, l)))

# s, once it holds the new request i of the change q: a store starts, or the
# request waits on its line
def Node.arrive(s: State(), i: Ledgers.Id, q: Ask) -> State():
  match q:
    case Ask.Start{os}:
      Node.start(s, i, os)
    case Ask.On{+r, +l, c}:
      State.wait(Node.follow(s, r, l), Line.chain(r, l), i)

# a and b are the same root
def Root.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the node n may cast a ballot at the place w of a line at the tip t, for the
# requests qs: there is a request, n is an owner, and n cast none there
def Cast.may(+n: String, +s: State(), w: Ledgers.Where, t: Tip, qs: List<&2, Ledgers.Id>) -> Bool:
  List.all.if(
    u => List.all.if(
      v => Maybe.is_none(
        &2,
        Cells.Cell<Ledgers.Entry<Ask>>,
        Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.vote(w, n))
      ),
      List.contains(~String, ~String.eq, Line.owners(s, t), n)
    ),
    Bool.not(List.is_empty(&2, Ledgers.Id, qs))
  )

# s with the node n's ballot for the act a at the place w, sealed as the next
# of the node's chain m (none: the store gave the node no key)
def Cast.seal(+s: State(), +w: Ledgers.Where, n: String, a: Ledgers.Act, m: Maybe<&2, Chained>) -> State():
  match m:
    case None{}:
      s
    case Some{Chained{+j, last, key, f}}:
      +seed = Keys.seed(State.keys(s))
      +r = Where.store(w)
      Maybe.default(
        &2,
        State(),
        Seal.accept(
          s,
          Ledgers.Ballot.make(
            Seal.secret(seed, r, j),
            Ledgers.Signed{w, n, a},
            last,
            Seals.Seal.public(Seal.secret(seed, r, U32.inc(j)))
          )
        ),
        s
      )

# the state m with the node n's ballot for the act a at the place w, else s
def Cast.vote(s: State(), m: Maybe<&2, State()>, +w: Ledgers.Where, +n: String, a: Ledgers.Act) -> State():
  match m:
    case None{}:
      s
    case Some{s3}:
      +s4 = State.led(s, State.ledger(s3))
      Cast.seal(s4, w, n, a, Seal.chain(s4, Where.store(w), n))

# s with the node n's vote at the place w for the step that ran qs from the
# tip of the hash th, which the passes of the nodes from allow, when the run m
# is there: the run's nodes, its tip, and the ballot
def Cast.put(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Run>,
  s: State()
) -> State():
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2, ns}}:
      Cast.vote(
        s,
        State.put(s2, [Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Tip.hash(t2)}}, from}
      )

# the change q is one of who decides: a first key of a node, a group, the
# owners of a line, or a new branch. The owners of a store decide these, so an
# owner casts for one only when a writer connected to it asked for it
def Ask.governs(q: Ask) -> Bool:
  match q:
    case Ask.On{r, l, Change.Key{n, k}}:
      True{}
    case Ask.On{r, l, Change.Group{g, ms}}:
      True{}
    case Ask.On{r, l, Change.Own{g, at, os}}:
      True{}
    case Ask.On{r, l, Change.Branch{b, at}}:
      True{}
    case x:
      False{}

# the node s may cast for the request i, which it holds as m: any request,
# but one of who decides only when it was asked at s
def Cast.mine.of(s: State(), i: Ledgers.Id, m: Maybe<&2, Ledgers.Asked<Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Asked{t, q}}:
      List.any.if(u => Keys.asked(State.keys(s), i), Bool.not(Ask.governs(q)))

# the requests of qs that the node s may cast for
def Cast.mine(+s: State(), qs: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(Ledgers.Id, i, Cast.mine(s, r), Cast.mine.of(s, i, Node.asked(s, i)))

# the owner whose turn it is to propose the step at the height h, among the
# owners os: each in turn, by the height. One owner proposes a step and the
# others cast for the same step, so the owners do not split over what waits
# at each of them
def Owners.turn(+os: List<&2, String>, h: U32) -> Maybe<&2, String>:
  List.get(
    &2,
    String,
    os,
    U32.to_nat(U32.mod(h, U32.from_nat(List.length(&2, String, os))))
  )

# the node n is the node m, if any
def Turn.is(m: Maybe<&2, String>, n: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      String.eq(p, n)

# the step in the cell m of a ballot, if it holds one
def Cast.step(m: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{b}}}:
      Ledgers.Ballot.vote(b)
    case x:
      None{}

# the step that the node p cast at the place w, if s holds its ballot
def Cast.of(s: State(), w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Vote>:
  Cast.step(Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.vote(w, p)))

# what a node casts for: the requests of a step, its own run of them (none:
# it cannot run them now), and the nodes whose passes allow the step
type Plan is Data:
  Plan{asks: List<&2, Ledgers.Id>, run: Maybe<&2, Run>, from: List<&2, String>}

# the requests of the plan p
def Plan.asks(p: Plan) -> List<&2, Ledgers.Id>:
  match p:
    case Plan{qs, m, from}:
      qs

# the run of the plan p
def Plan.run(p: Plan) -> Maybe<&2, Run>:
  match p:
    case Plan{qs, m, from}:
      m

# the nodes whose passes allow the step of the plan p
def Plan.from(p: Plan) -> List<&2, String>:
  match p:
    case Plan{qs, m, from}:
      from

# the plan of an owner that proposes freely, on the line c at the tip t: the
# requests that wait at it, that it may cast for and that can run now
def Plan.own(+s: State(), +c: Ledgers.Chain, t: Tip, from: List<&2, String>) -> Plan:
  +p = Step.some(c, Cast.mine(s, Wait.of(s, c)), Run{s, t, []})
  Plan{Picked.asks(p), Some{Picked.run(p)}, from}

# the node s may cast for each request of qs
def Cast.all_mine(+s: State(), qs: List<&2, Ledgers.Id>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+i, r}:
      List.all.if(u => Cast.all_mine(s, r), Cast.mine.of(s, i, Node.asked(s, i)))

# the run m, when it gives the tip of the hash after
def Plan.fit(after: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Run>) -> Maybe<&2, Run>:
  match m:
    case None{}:
      None{}
    case Some{Run{s2, +t2, ns}}:
      Shared.Maybe.when(Run, Root.same(after, Some{Tip.hash(t2)}), u => Some{Run{s2, t2, ns}})

# the plan for a step m that another ballot names, on the line c at the tip t
# of the hash th: when the step starts from this tip, the node may cast for
# each of its requests, and the node's own run of them gives the same tip
def Plan.copy(
  +s: State(),
  +c: Ledgers.Chain,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  from: List<&2, String>
) -> Plan:
  match m:
    case None{}:
      Plan{[], None{}, []}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Plan,
        List.all.if(u => Cast.all_mine(s, qs), Root.same(before, th)),
        u => Plan{qs, Plan.fit(after, Step.run(s, c, t, qs)), from},
        u => Plan{[], None{}, []}
      )

# Rounds
# ------
# The decision of a height goes in rounds. In the round r the owner (h + r),
# in turn, proposes. In the first round it proposes freely. A node that waited
# too long passes to the next round: it casts no vote in the rounds below any
# more, and names its last vote at the height. In a later round the proposer
# needs the passes of a majority; it proposes the last vote of the highest
# round among them, if there is one, so a step that a round decided is the
# only one that a later round can decide.

# the round of the place w
def Where.round(w: Ledgers.Where) -> Nat:
  match w:
    case Ledgers.Where{c, h, r}:
      r

# what the node p did at the place w, in the cell m of its vote
def Cast.act.of(m: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>) -> Maybe<&2, Ledgers.Act>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}}}}:
      Some{a}
    case x:
      None{}

# the vote of the node p at the place w, with the nodes whose passes allow
# it, if s holds it
def Cast.act(s: State(), w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Act>:
  Cast.act.of(Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.vote(w, p)))

# the nodes that the vote m names, if m is a vote
def Act.from(m: Maybe<&2, Ledgers.Act>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Act.Vote{v, from}}:
      from
    case x:
      []

# the nodes whose passes allow the vote of the node p at the place w, as the
# vote names them
def Cast.from(s: State(), w: Ledgers.Where, p: String) -> List<&2, String>:
  Act.from(Cast.act(s, w, p))

# the highest round, up to k, to which the node n passed at the height h of
# the line c (0: it passed to none)
def Round.mine(+n: String, +s: State(), +c: Ledgers.Chain, +h: U32, k: Nat) -> Nat:
  match k:
    case 0n:
      0n
    case 1n+(+p):
      Shared.Bool.when(
        Nat,
        Maybe.is_some(
          &2,
          Maybe<&2, Ledgers.Last>,
          Ledgers.State.passed(~Ask, State.ledger(s), Ledgers.Where{c, h, 1n+p}, n)
        ),
        u => 1n+p,
        u => Round.mine(n, s, c, h, p)
      )

# the vote m of the round r, as a last vote, else what rest gives
def Last.or(r: Nat, m: Maybe<&2, Ledgers.Vote>, rest: Unit -> Maybe<&2, Ledgers.Last>) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{v}:
      Some{Ledgers.Last{r, v}}
    case None{}:
      rest(Unit{})

# the last vote of the node n at the height h of the line c, in a round up to
# k, if it cast one
def Last.mine(+n: String, +s: State(), +c: Ledgers.Chain, +h: U32, k: Nat) -> Maybe<&2, Ledgers.Last>:
  match k:
    case 0n:
      Last.or(0n, Cast.of(s, Ledgers.Where{c, h, 0n}, n), u => None{})
    case 1n+(+p):
      Last.or(
        1n+p,
        Cast.of(s, Ledgers.Where{c, h, 1n+p}, n),
        u => Last.mine(n, s, c, h, p)
      )

# the last vote of the node n at the height h of the line c, in a round below
# r, if it cast one
def Last.below(+n: String, +s: State(), +c: Ledgers.Chain, +h: U32, r: Nat) -> Maybe<&2, Ledgers.Last>:
  match r:
    case 0n:
      None{}
    case 1n+p:
      Last.mine(n, s, c, h, p)

# the nodes of os whose pass to the place w the node s holds
def Passes.of(+s: State(), +w: Ledgers.Where, os: List<&2, String>) -> List<&2, String>:
  match os:
    case Nil{}:
      []
    case Con{+o, r}:
      List.filter.put(
        String,
        o,
        Passes.of(s, w, r),
        Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Ledgers.State.passed(~Ask, State.ledger(s), w, o))
      )

# the last vote of the higher round of a and b
def Last.newer(a: Maybe<&2, Ledgers.Last>, b: Maybe<&2, Ledgers.Last>) -> Maybe<&2, Ledgers.Last>:
  match a b:
    case None{} y:
      y
    case Some{x} None{}:
      Some{x}
    case Some{Ledgers.Last{+r1, v1}} Some{Ledgers.Last{+r2, v2}}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Last>,
        Nat.is_lt(r1, r2),
        u => Some{Ledgers.Last{r2, v2}},
        u => Some{Ledgers.Last{r1, v1}}
      )

# the last vote that a pass names, flattened
def Passed.last(m: Maybe<&2, Maybe<&2, Ledgers.Last>>) -> Maybe<&2, Ledgers.Last>:
  match m:
    case Some{x}:
      x
    case None{}:
      None{}

# the last vote of the highest round that the passes of the nodes from to the
# place w name, if any names one
def Passes.last(+s: State(), +w: Ledgers.Where, from: List<&2, String>) -> Maybe<&2, Ledgers.Last>:
  match from:
    case Nil{}:
      None{}
    case Con{o, r}:
      Last.newer(
        Passed.last(Ledgers.State.passed(~Ask, State.ledger(s), w, o)),
        Passes.last(s, w, r)
      )

# the nodes from are a majority of the owners os
def Major(os: List<&2, String>, +from: List<&2, String>) -> Bool:
  Nat.is_lt(
    List.length(&2, String, os),
    Nat.add(List.length(&2, String, from), List.length(&2, String, from))
  )

# the last vote m, if any, is for the step v
def Last.is(m: Maybe<&2, Ledgers.Last>, v: Ledgers.Vote) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Last{r, x}}:
      Ledgers.Vote.is_eq(x, v)

# the node s holds the pass to the place w of each of the nodes from
def Passed.all(+s: State(), +w: Ledgers.Where, from: List<&2, String>) -> Bool:
  match from:
    case Nil{}:
      True{}
    case Con{o, r}:
      List.all.if(
        u => Passed.all(s, w, r),
        Maybe.is_some(&2, Maybe<&2, Ledgers.Last>, Ledgers.State.passed(~Ask, State.ledger(s), w, o))
      )

# the nodes from are some of the owners os, each once, in their order
def Owners.sub(os: List<&2, String>, from: List<&2, String>) -> Bool:
  match os from:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{f, fs}:
      False{}
    case Con{o, r} Nil{}:
      True{}
    case Con{o, +r} Con{+f, +fs}:
      Shared.Bool.when(Bool, String.eq(f, o), u => Owners.sub(r, fs), u => Owners.sub(r, f <> fs))

# the passes of the nodes from allow a vote for the step v at the place w of
# the owners os: in the first round, any step; later, the node holds the pass
# to w of each of them, they are owners and a majority, and v is the last vote
# of the highest round among them, if any
def Allowed(+s: State(), +w: Ledgers.Where, +os: List<&2, String>, v: Ledgers.Vote, +from: List<&2, String>) -> Bool:
  List.any.if(
    u => List.all.if(
      u2 => List.all.if(
        u3 => List.all.if(
          u4 => Last.is(Passes.last(s, w, from), v),
          Major(os, from)
        ),
        Owners.sub(os, from)
      ),
      Passed.all(s, w, from)
    ),
    Nat.is_eq(Where.round(w), 0n)
  )

# the plan of the proposer of a later round at the place w, once the nodes
# from that passed to it are known: none until they are a majority; then the
# last vote of the highest round among them, else what waits at the proposer
def Plan.later(
  +s: State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  +from: List<&2, String>,
  m: Maybe<&2, Ledgers.Last>
) -> Plan:
  match m:
    case None{}:
      Shared.Bool.when(Plan, Major(os, from), u => Plan.own(s, c, t, from), u => Plan{[], None{}, []})
    case Some{Ledgers.Last{r, v}}:
      Shared.Bool.when(
        Plan,
        Major(os, from),
        u => Plan.copy(s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )

# the plan of the proposer at the place w
def Plan.lead(
  +s: State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>
) -> Plan:
  +from = Passes.of(s, w, os)
  Shared.Bool.when(
    Plan,
    Nat.is_eq(Where.round(w), 0n),
    u => Plan.own(s, c, t, []),
    u => Plan.later(s, c, w, t, th, os, from, Passes.last(s, w, from))
  )

# the plan of another owner at the place w, once what the proposer did there
# is known (m): the proposer's step, when its passes allow it
def Plan.follow(
  +s: State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  t: Tip,
  th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  m: Maybe<&2, Ledgers.Act>
) -> Plan:
  match m:
    case Some{Ledgers.Act.Vote{+v, +from}}:
      Shared.Bool.when(
        Plan,
        Allowed(s, w, os, v, from),
        u => Plan.copy(s, c, t, th, Some{v}, from),
        u => Plan{[], None{}, []}
      )
    case x:
      Plan{[], None{}, []}

# what the node n casts for at the place w of the line c, at the tip t of the
# hash th, with the owners os, when it is turn's turn to propose
def Plan.of(
  n: String,
  +s: State(),
  +c: Ledgers.Chain,
  +w: Ledgers.Where,
  +t: Tip,
  +th: Maybe<&2, Hashes.Hash>,
  +os: List<&2, String>,
  turn: Maybe<&2, String>
) -> Plan:
  match turn:
    case None{}:
      Plan{[], None{}, []}
    case Some{+p}:
      Shared.Bool.when(
        Plan,
        String.eq(p, n),
        u => Plan.lead(s, c, w, t, th, os),
        u => Plan.follow(s, c, w, t, th, os, Cast.act(s, w, p))
      )

# s with the node n's pass to the place w, when n is one of the owners os and
# did not pass to w: it names its last vote at the height, in a round below
def Pass.to(+n: String, +s: State(), +w: Ledgers.Where, os: List<&2, String>) -> State():
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Shared.Bool.when(
        State(),
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Ask, State.ledger(s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        u => Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Last.below(n, s, c, h, r)},
          Seal.chain(s, Where.store(Ledgers.Where{c, h, r}), n)
        ),
        u => s
      )

# s, after the owner n joined the highest round of which it holds a ballot at
# the height h of the line c: a node casts in the round that the others reached
def Round.join(+n: String, +s: State(), +c: Ledgers.Chain, +h: U32, os: List<&2, String>) -> State():
  +top = Round.seen(s, c, h)
  Shared.Bool.when(
    State(),
    Nat.is_lt(Round.mine(n, s, c, h, top), top),
    u => Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    u => s
  )

# Node.cast in the round of the node n at the height next of the line c, at
# the tip t of the hash th
def Cast.round(+n: String, +s: State(), +c: Ledgers.Chain, +next: U32, +th: Maybe<&2, Hashes.Hash>, +t: Tip) -> State():
  +os = Line.owners(s, t)
  +r = Round.mine(n, s, c, next, Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Plan.of(n, s, c, w, t, th, os, Owners.turn(os, U32.add(next, U32.from_nat(r))))
  Shared.Bool.when(
    State(),
    Cast.may(n, s, w, t, Plan.asks(p)),
    u => Cast.put(n, w, th, Plan.asks(p), Plan.from(p), Plan.run(p), s),
    u => s
  )

# Node.cast at the head h of the line c, whose tip is m
def Cast.at(+n: String, +s: State(), +c: Ledgers.Chain, h: Head, m: Maybe<&2, Tip>) -> State():
  match h m:
    case Head{r, b, +next, +th} Some{+t}:
      Cast.round(n, Round.join(n, s, c, next, Line.owners(s, t)), c, next, th, t)
    case x y:
      s

# Node.pass at the head h of the line c, whose tip is m
def Pass.at(+n: String, +s: State(), +c: Ledgers.Chain, h: Head, m: Maybe<&2, Tip>) -> State():
  match h m:
    case Head{r, b, +next, th} Some{t}:
      +k = Round.seen(s, c, next)
      Pass.to(
        n,
        s,
        Ledgers.Where{c, next, 1n+Round.mine(n, s, c, next, k)},
        Line.owners(s, t)
      )
    case x y:
      s

# Node.pass once the head m of the line c is known
def Pass.head(+n: String, +s: State(), +c: Ledgers.Chain, m: Maybe<&2, Head>) -> State():
  match m:
    case None{}:
      s
    case Some{+h}:
      Pass.at(n, s, c, h, Head.tip(s, h))

# Node.cast once the head m of the line c is known
def Cast.head(n: String, +s: State(), c: Ledgers.Chain, m: Maybe<&2, Head>) -> State():
  match m:
    case None{}:
      s
    case Some{+h}:
      Cast.at(n, s, c, h, Head.tip(s, h))

# s, after the node n cast its ballot for the next step of the line c, in its
# round (Rounds): when it is its turn, the step that the rules of the round
# give it; else the step that the owner whose turn it is cast, when the rules
# allow it and the node's own run of it gives the same tip
def Node.cast(n: String, +s: State(), +c: Ledgers.Chain) -> State():
  Cast.head(n, s, c, Node.head_of(s, c))

# the state m at the head h of the line c, after a step that ran qs, else s
def Advance.moved(
  s: State(),
  m: Maybe<&2, State()>,
  c: Ledgers.Chain,
  h: Head,
  qs: List<&2, Ledgers.Id>
) -> State():
  match m:
    case None{}:
      s
    case Some{s3}:
      State.moved(State.led(s, State.ledger(s3)), c, h, qs)

# s at the head of the next height of the line c, when the run m of the
# decided requests qs gives the tip that the ballots name (after): a node
# checks a step before it keeps it
def Advance.ran(
  +s: State(),
  c: Ledgers.Chain,
  r: Ledgers.Id,
  b: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Run>
) -> State():
  match m:
    case None{}:
      s
    case Some{Run{s2, +t2, ns}}:
      Shared.Bool.when(
        State(),
        Root.same(after, Some{Tip.hash(t2)}),
        u => Advance.moved(
          s,
          State.put(s2, [Tip.words(t2)]),
          c,
          Head{r, b, U32.inc(next), Some{Tip.hash(t2)}},
          qs
        ),
        u => s
      )

# Node.advance once the step m that the owners decided at the head is known
def Advance.step(+s: State(), +c: Ledgers.Chain, h: Head, t: Tip, m: Maybe<&2, Ledgers.Vote>) -> State():
  match h m:
    case Head{r, b, next, th} Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        State(),
        Root.same(before, th),
        u => Advance.ran(s, c, r, b, next, after, qs, Step.run(s, c, t, qs)),
        u => s
      )
    case x y:
      s

# the step m, if any, else the step that rest gives
def Vote.first(m: Maybe<&2, Ledgers.Vote>, rest: Unit -> Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{v}:
      Some{v}
    case None{}:
      rest(Unit{})

# the step that the owners os decided at the height h of the line c, in a
# round up to k, the highest first, if they did. The rounds of a height decide
# one step (Height.One), so the order does not matter
def Height.decide(
  +s: State(),
  +c: Ledgers.Chain,
  +h: U32,
  +os: List<&2, String>,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  match k:
    case 0n:
      Ledgers.State.decide(~Ask, State.ledger(s), Ledgers.Where{c, h, 0n}, os)
    case 1n+(+p):
      Vote.first(
        Ledgers.State.decide(~Ask, State.ledger(s), Ledgers.Where{c, h, 1n+p}, os),
        u => Height.decide(s, c, h, os, p)
      )

# that the rounds of the height h of the line c decide one step in s, for the
# owners os: a law of rounds, and a premise of the laws of agreement
def Height.One(s: State(), c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r1: Nat -> @r2: Nat -> @v1: Ledgers.Vote -> @v2: Ledgers.Vote -> {
    Ledgers.State.decide(~Ask, State.ledger(s), Ledgers.Where{c, h, r1}, os) == Some{v1}: Maybe<&2, Ledgers.Vote>
  } -> {
    Ledgers.State.decide(~Ask, State.ledger(s), Ledgers.Where{c, h, r2}, os) == Some{v2}: Maybe<&2, Ledgers.Vote>
  } -> {v1 == v2: Ledgers.Vote}

# The rules of rounds, for the ballots that s holds at the height h of the line
# c. A node that follows them makes them true of its own ballots; that every
# node follows them is the premise of Rounds.one.

# that the passes that a vote names allow it (Allowed), for the owners os
def Rounds.Allow(s: State(), c: Ledgers.Chain, h: U32, os: List<&2, String>) -> Type:
  @r: Nat -> @q: String -> @v: Ledgers.Vote -> {
    Cast.of(s, Ledgers.Where{c, h, r}, q) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> {
    Allowed(s, Ledgers.Where{c, h, r}, os, v, Cast.from(s, Ledgers.Where{c, h, r}, q)) == True{}: Bool
  }

# that a pass names the last vote of its node below its round: a node that
# passed to a round casts no vote below it
def Rounds.Last(s: State(), c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q: String -> @l: Maybe<&2, Ledgers.Last> -> {
    Ledgers.State.passed(~Ask, State.ledger(s), Ledgers.Where{c, h, r}, q)
      == Some{l}: Maybe<&2, Maybe<&2, Ledgers.Last>>
  } -> {l == Last.below(q, s, c, h, r): Maybe<&2, Ledgers.Last>}

# that the votes of one round are for one step: one owner proposes, and the
# others copy
def Rounds.Same(s: State(), c: Ledgers.Chain, h: U32) -> Type:
  @r: Nat -> @q1: String -> @q2: String -> @a: Ledgers.Vote -> @b: Ledgers.Vote -> {
    Cast.of(s, Ledgers.Where{c, h, r}, q1) == Some{a}: Maybe<&2, Ledgers.Vote>
  } -> {
    Cast.of(s, Ledgers.Where{c, h, r}, q2) == Some{b}: Maybe<&2, Ledgers.Vote>
  } -> {a == b: Ledgers.Vote}

# the rounds of a height decide one step, when the ballots follow the rules
# of rounds: a later round can only decide what an earlier round decided
law Rounds.one:
  for ~s: State()
  for ~c: Ledgers.Chain
  for ~h: U32
  for ~os: List<&2, String>
  for ~fa: Rounds.Allow(s, c, h, os)
  for ~fb: Rounds.Last(s, c, h)
  for ~fc: Rounds.Same(s, c, h)
  Height.One(s, c, h, os)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(+s: State(), +c: Ledgers.Chain, +h: Head, k: Nat) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(s, h),
    t => Height.decide(s, c, Head.next(h), Line.owners(s, t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(+s: State(), +c: Ledgers.Chain, +h: Head) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(s, c, h, Round.seen(s, c, Head.next(h)))

# Node.advance at the head h of the line c, whose tip is m
def Advance.at(+s: State(), +c: Ledgers.Chain, +h: Head, m: Maybe<&2, Tip>) -> State():
  match m:
    case None{}:
      s
    case Some{+t}:
      Advance.step(
        s,
        c,
        h,
        t,
        Height.decide(
          s,
          c,
          Head.next(h),
          Line.owners(s, t),
          Round.seen(s, c, Head.next(h))
        )
      )

# the head h after the step m: one height up, at the tip that the step names
# (no step, or one that names no tip: h)
def Head.step(h: Head, m: Maybe<&2, Ledgers.Vote>) -> Head:
  match h m:
    case Head{r, b, n, th} Some{Ledgers.Vote{before, qs, Some{x}}}:
      Head{r, b, U32.inc(n), Some{x}}
    case x y:
      x

# Node.advance once the head m of the line c is known
def Advance.head(+s: State(), c: Ledgers.Chain, m: Maybe<&2, Head>) -> State():
  match m:
    case None{}:
      s
    case Some{+h}:
      Advance.at(s, c, h, Head.tip(s, h))

# s, with its head of the line c moved over the next step, when a majority of
# the owners in its tip cast it and the node's own run of it gives the same
# tip
def Node.advance(+s: State(), +c: Ledgers.Chain) -> State():
  Advance.head(s, c, Node.head_of(s, c))

# the heads a and b are at the same height, or one is none
def Heads.level(a: Maybe<&2, Head>, b: Maybe<&2, Head>) -> Bool:
  match a b:
    case Some{x} Some{y}:
      U32.is_eq(Head.next(x), Head.next(y))
    case x y:
      True{}

# Node.advances once the head m of the line c is known
def Advances.at(f: Nat, +s: State(), +c: Ledgers.Chain, m: Maybe<&2, Head>) -> State():
  match f m:
    case 1n+p Some{+h}:
      +s1 = Advance.at(s, c, h, Head.tip(s, h))
      +m1 = Node.head_of(s1, c)
      Shared.Bool.when(
        State(),
        Heads.level(Some{h}, m1),
        u => s1,
        u => Advances.at(p, s1, c, m1)
      )
    case g x:
      s

# s, with its head of the line c moved over each step that is decided, f
# steps at most
def Node.advances(f: Nat, +s: State(), +c: Ledgers.Chain) -> State():
  Advances.at(f, s, c, Node.head_of(s, c))

# s, after the node n moved its head of the line c over each step that is
# decided, cast its ballot for the next step, and moved its head again
def Step.head(n: String, s: State(), +c: Ledgers.Chain) -> State():
  s1 = Node.advances(4294967295n, s, c)
  Node.advances(4294967295n, Node.cast(n, s1, c), c)

# s, after the node n did what it can on the line c
def Node.step(n: String, s: State(), +c: Ledgers.Chain) -> State():
  Step.head(n, Node.open(s, c), c)

# s, after the owner n passed to the next round of the next step of the line
# c, and did what it can there: the round took too long (the proposer may be
# away). Transport asks for this; the core has no clock
def Node.pass(+n: String, +s: State(), +c: Ledgers.Chain) -> State():
  Node.step(n, Pass.head(n, s, c, Node.head_of(s, c)), c)

# s, after the node n took in the new request q of e
def Node.ask.new(n: String, +s: State(), +e: Envelope, +q: Ask) -> State():
  +i = Envelope.of(e)
  c = Ask.chain(i, q)
  s1 = Node.arrive(
    State.led(s, Ledgers.State.ask(~Ask, ~Ask.is_eq, State.ledger(s), i, Envelope.time(e), q)),
    i,
    q
  )
  Node.step(n, s1, c)

# Node.ask once the cell m of the request's ID is known
def Node.ask.at(
  n: String,
  +s: State(),
  +e: Envelope,
  +q: Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
) -> State():
  match m:
    case Some{x}:
      s
    case None{}:
      Node.ask.new(n, State.keyed(s, Keys.mark(State.keys(s), Envelope.of(e))), e, q)

# s, after the node n took in the request q of e, cast its ballot when it owns
# its line, and moved its head when that decides the step. A request ID that s
# holds counts once: asked again, it changes nothing
def Node.ask(n: String, +s: State(), +e: Envelope, q: Ask) -> State():
  Node.ask.at(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.ask(Envelope.of(e)))
  )

# s, once it holds each request among the cells cs whose slot was empty in the
# ledger old: a request that the node held does not arrive again
def Take.asks(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>,
  +old: Ledgers.State(Ask),
  +s: State()
) -> State():
  match cs:
    case Nil{}:
      s
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, q}}, rest}:
      Take.asks(
        rest,
        old,
        Shared.Bool.when(
          State(),
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Ask>>,
            Ledgers.State.get(~Ask, old, Ledgers.Slot.ask(i))
          ),
          u => Node.arrive(s, i, q),
          u => s
        )
      )
    case Con{c, rest}:
      Take.asks(rest, old, s)

# l with the requests and the data among the cells cs, each in the slot that
# its own content names (a request by its ID, data by its hash). A ballot, a
# cell that is not one entry, and the slot that the sender gave are not kept:
# what another node sent is read, not believed
def Take.clean(cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>, l: Ledgers.State(Ask)) -> Ledgers.State(Ask):
  match cs:
    case Nil{}:
      l
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, rest}:
      Take.clean(rest, Ledgers.State.ask(~Ask, ~Ask.is_eq, l, i, t, q))
    case Con{Cells.One{Ledgers.Entry.Data{ws}}, rest}:
      Take.clean(rest, Ledgers.State.put_data(~Ask, ~Ask.is_eq, l, ws))
    case Con{c, rest}:
      Take.clean(rest, l)

# Node.consent once the line m of the request is known
def Consent.at(n: String, +s: State(), i: Ledgers.Id, m: Maybe<&2, Ledgers.Chain>) -> State():
  match m:
    case None{}:
      s
    case Some{c}:
      Node.step(n, State.keyed(s, Keys.mark(State.keys(s), i)), c)

# s, after a writer connected to the node n asked for the request i, which s
# holds already (it came from another node): the request counts once, and the
# node now casts for it as one that was asked at it
def Node.consent(n: String, +s: State(), +i: Ledgers.Id) -> State():
  Consent.at(n, s, i, Node.chain_of(s, i))

# the hash of the node that the look l lacks, if it lacks one
def Look.lack(l: Trees.Look) -> Maybe<&2, Hashes.Hash>:
  match l:
    case Trees.Look.Missing{x}:
      Some{x}
    case Trees.Look.Found{v}:
      None{}
    case Trees.Look.Absent{}:
      None{}

# the hash of the node that a read of the key k of the tree whose root is h
# lacks in s, if it lacks one: what the node asks another node for. A node
# keeps the part of a store that it uses, and fetches the rest on demand
def Node.lacks(+s: State(), +h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Maybe<&2, Hashes.Hash>:
  Look.lack(Node.look(s, h, k))

# l with the data m, if any
def Serve.put(m: Maybe<&2, List<&2, U32>>, +l: Ledgers.State(Ask)) -> Ledgers.State(Ask):
  match m:
    case None{}:
      l
    case Some{+ws}:
      Ledgers.State.put_data(~Ask, ~Ask.is_eq, l, ws)

# the data that s holds under the hashes hs, as a ledger: what a node sends
# to a node that asks for them (Node.fetch)
def Node.serve(+s: State(), hs: List<&2, Hashes.Hash>) -> Ledgers.State(Ask):
  match hs:
    case Nil{}:
      Ledgers.State.empty(~Ask)
    case Con{+h, r}:
      Serve.put(Ledgers.State.data(~Ask, State.ledger(s), h), Node.serve(s, r))

# what the ledger r lacks of s: what a sync from s to a holder of r sends
def Node.missing(s: State(), r: Ledgers.State(Ask)) -> Ledgers.State(Ask):
  Ledgers.State.missing(~Ask, ~Ask.is_eq, State.ledger(s), r)

# what a node reads of the ledger t that another node sent: each request and
# each data, in the slot that its own content names (Take.clean)
def Node.reads(t: Ledgers.State(Ask)) -> Ledgers.State(Ask):
  Take.clean(Tries.Trie.values(Cells.Cell<Ledgers.Entry<Ask>>, t), Ledgers.State.empty(~Ask))

# the ballots among the cells cs
def Ballots.of(cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>) -> List<&2, Ledgers.Ballot>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, rest}:
      b <> Ballots.of(rest)
    case Con{c, rest}:
      Ballots.of(rest)

# what a holder of s keeps of t, which another node sent. It checks everything
# before it keeps it: a request and data go to the slot that their own content
# names (Take.clean; data is read only under its hash), in the slots where s
# holds nothing; a ballot is kept when its node's chain leads to it and its
# key signs it (a ballot that it cannot check yet comes again with the next
# sync). Nothing that s holds is lost or changed. Each new request waits on
# its line: the cost is what t brings, not what s holds
def Node.take(+s: State(), +t: Ledgers.State(Ask)) -> State():
  +sent = Take.clean(Tries.Trie.values(Cells.Cell<Ledgers.Entry<Ask>>, t), Ledgers.State.empty(~Ask))
  Sealed.take(
    Ballots.of(
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Ask>>,
        Ledgers.State.missing(~Ask, ~Ask.is_eq, t, State.ledger(s))
      )
    ),
    Take.asks(
      Tries.Trie.values(Cells.Cell<Ledgers.Entry<Ask>>, sent),
      State.ledger(s),
      State.led(s, Ledgers.State.take(~Ask, State.ledger(s), sent))
    )
  )

# s, after the node n did what it can on each line of cs
def Node.steps(+n: String, cs: List<&2, Ledgers.Chain>, s: State()) -> State():
  match cs:
    case Nil{}:
      s
    case Con{c, rest}:
      Node.steps(n, rest, Node.step(n, s, c))

# the line of the first of the waiting requests qs, then rest
def Lines.waiting(
  s: State(),
  qs: List<&2, Ledgers.Id>,
  +rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match qs:
    case Nil{}:
      rest
    case Con{i, r}:
      Maybe.default(
        &2,
        List<&2, Ledgers.Chain>,
        Maybe.bind(&2, Ledgers.Chain, List<&2, Ledgers.Chain>, Node.chain_of(s, i), c => Some{c <> rest}),
        rest
      )

# the lines of the lists of waiting requests qss
def Lines.waits(+s: State(), qss: List<&2, List<&2, Ledgers.Id>>) -> List<&2, Ledgers.Chain>:
  match qss:
    case Nil{}:
      []
    case Con{qs, r}:
      Lines.waiting(s, qs, Lines.waits(s, r))

# the lines of the requests and the ballots among the cells cs, then rest
def Lines.new(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>,
  rest: List<&2, Ledgers.Chain>
) -> List<&2, Ledgers.Chain>:
  match cs:
    case Nil{}:
      rest
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, r}:
      Ask.chain(i, q) <> Lines.new(r, rest)
    case Con{Cells.One{Ledgers.Entry.Vote{b}}, r}:
      Where.line(Ballot.at(b)) <> Lines.new(r, rest)
    case Con{c, r}:
      Lines.new(r, rest)

# the lines that a sync of t into s may move, each once: those of the new
# requests and ballots of t, and those with waiting requests (new data can let
# them run). So a sync costs about what it brings, not every line of the node
def Sync.lines(s: State(), +s1: State(), t: Ledgers.State(Ask)) -> List<&2, Ledgers.Chain>:
  Tries.Trie.unique(
    ~Ledgers.Chain,
    ~Ledgers.Chain.key,
    Lines.new(
      Tries.Trie.values(
        Cells.Cell<Ledgers.Entry<Ask>>,
        Ledgers.State.missing(~Ask, ~Ask.is_eq, t, State.ledger(s))
      ),
      Lines.waits(s1, Tries.Trie.values(List<&2, Ledgers.Id>, State.waiting(s1)))
    ),
    Tries.Trie.new(Unit)
  )

# s, after the node n took in t, which another node sent, and did what it can
# on each line that this may move: how a node that is behind catches up
def Node.sync(n: String, +s: State(), +t: Ledgers.State(Ask)) -> State():
  +s1 = Node.take(s, t)
  Node.steps(n, Sync.lines(s, s1, t), s1)

# Reads
# -----
# Each read is of the node's own state: its ledger, and its heads.

# the root of the content of the line c now (none: the empty tree, or the node
# does not follow c)
def Chain.root(s: State(), c: Ledgers.Chain) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(&2, Tip, Hashes.Hash, Node.tip(s, c), t => Tip.content(t))

# the root of the content of the store r now
def Store.root(s: State(), r: Ledgers.Id) -> Maybe<&2, Hashes.Hash>:
  Chain.root(s, Ledgers.Chain{r, None{}})

# the newest version of a line at the tip t, if it has one
def Line.newest(+s: State(), +t: Tip) -> Maybe<&2, Ledgers.Id>:
  +n = Line.count(s, t)
  Shared.Maybe.when(Ledgers.Id, Bool.not(U32.is_eq(n, 0)), u => Version.in(s, U32.sub(n, 1), t))

# the newest version of the line c, if it has one
def Chain.newest(+s: State(), c: Ledgers.Chain) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(&2, Tip, Ledgers.Id, Node.tip(s, c), t => Line.newest(s, t))

# the newest version of the branch b of the store r, if b has one
def Node.head(s: State(), r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Line.chain(r, Some{b}))

# the newest version of the store r
def Store.head(s: State(), r: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Chain.newest(s, Ledgers.Chain{r, None{}})

# the version m, when it is there, then rest
def Ids.put(m: Maybe<&2, Ledgers.Id>, rest: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match m:
    case Some{i}:
      i <> rest
    case None{}:
      rest

# the k versions of a line at the tip t from the number n, in order
def Line.versions(k: Nat, +s: State(), +t: Tip, +n: U32) -> List<&2, Ledgers.Id>:
  match k:
    case 0n:
      []
    case 1n+p:
      Ids.put(Version.in(s, n, t), Line.versions(p, s, t, U32.inc(n)))

# the versions of the line whose tip is m, in order
def Versions.of(+s: State(), m: Maybe<&2, Tip>) -> List<&2, Ledgers.Id>:
  match m:
    case None{}:
      []
    case Some{+t}:
      Line.versions(U32.to_nat(Line.count(s, t)), s, t, 0)

# the versions of the branch b of the store r, in order
def Node.versions(+s: State(), r: Ledgers.Id, b: String) -> List<&2, Ledgers.Id>:
  Versions.of(s, Node.tip(s, Line.chain(r, Some{b})))

# the owners of the next step of the line l of the store r
def Node.owners(+s: State(), r: Ledgers.Id, l: Maybe<&2, String>) -> List<&2, String>:
  Maybe.default(
    &2,
    List<&2, String>,
    Maybe.bind(&2, Tip, List<&2, String>, Node.tip(s, Line.chain(r, l)), t => Some{Line.owners(s, t)}),
    []
  )

# the request i is a version: a step took it
def Node.is_version(s: State(), i: Ledgers.Id) -> Bool:
  Maybe.is_some(&2, Version, Node.made(s, i))

# the version at the point p, if there is one
def Node.version(s: State(), p: Point) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Point.At{+v}:
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.is_version(s, v), u => Some{v}, u => None{})
    case Point.Head{r, b}:
      Node.head(s, r, b)
    case Point.Mark{r, b, m}:
      Chain.mark(s, Line.chain(r, Some{b}), m)

# the root of the content of the resource n at the version m, if it holds it
def Res.root_at(+s: State(), n: Resources.Name, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, Ledgers.Id, Ropes.Root, m, v => Res.root(s, Node.root_of(s, Some{v}), n))

# the bytes of the resource n at the version m, if it holds them
def Res.at(+s: State(), n: Resources.Name, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Texts.Bytes()>:
  Root.bytes(s, Res.root_at(s, n, m))

# the bytes of the resource n at the point p, if it is there
def Node.content(+s: State(), n: Resources.Name, p: Point) -> Maybe<&2, Texts.Bytes()>:
  Res.at(s, n, Node.version(s, p))

# the members of the group g of the store r, if g exists
def Node.members(+s: State(), r: Ledgers.Id, g: String) -> Maybe<&2, List<&2, Member>>:
  Members.in(s, Store.root(s, r), g)

# the nodes inside the group g of the store r
def Node.nodes(+s: State(), r: Ledgers.Id, g: String) -> List<&2, String>:
  Group.nodes(s, Store.root(s, r), g)

# the owner group of the line l of the store r, if it has one (none: its
# owners are the nodes that it started with)
def Node.group(+s: State(), r: Ledgers.Id, l: Maybe<&2, String>) -> Maybe<&2, String>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    String,
    Node.get(s, Chain.root(s, Line.chain(r, l)), Key.owner()),
    ws => Read.whole(String, Codes.Code.text.read(ws))
  )

# the request that makes the group g, with the nodes inside it now, the owner
# group of the line l of the store r
def Node.own(+s: State(), +r: Ledgers.Id, l: Maybe<&2, String>, +g: String) -> Ask:
  Ask.On{r, l, Change.Own{g, Store.head(s, r), Node.nodes(s, r, g)}}

# a request, and who asks for it
type Request is Data:
  Request{envelope: Envelope, ask: Ask}

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
  +s: State(),
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
          Request{Envelope{Adopt.id(l, at), "", ""}, Ask.On{r, l, Change.Own{g, at, os}}}
        }
      )

# the adoption of the line l of the store r, if its owners are not the nodes
# inside its owner group
def Node.adoption(+s: State(), +r: Ledgers.Id, +l: Maybe<&2, String>) -> Maybe<&2, Request>:
  Adopt.of(s, r, l, Node.group(s, r, l))

# s, after the node n took in the request m, if any
def Adopt.ask(n: String, s: State(), m: Maybe<&2, Request>) -> State():
  match m:
    case None{}:
      s
    case Some{Request{e, q}}:
      Node.ask(n, s, e, q)

# s, after the node n asked for the adoption of the line l of the store r, if
# its owners are not the nodes inside its owner group
def Node.adopt(n: String, +s: State(), r: Ledgers.Id, l: Maybe<&2, String>) -> State():
  Adopt.ask(n, s, Node.adoption(s, r, l))

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
def Draft.content(r: Ledgers.Id, b: String, n: Resources.Name, q: Ask) -> Maybe<&2, Content>:
  match q:
    case Ask.On{st, Some{x}, Change.Write{m, base, c}}:
      Shared.Maybe.when(Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case Ask.On{st, Some{x}, Change.Resolve{k, m, c}}:
      Shared.Maybe.when(Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case _:
      None{}

# a pending write: when its writer asked for it (the time, then the request
# ID, as a key), and the content that it gives
type Draft is Data:
  Draft{key: List<&2, Bool>, content: Content}

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
def Draft.with(found: Maybe<&2, Draft>, k: List<&2, Bool>, m: Maybe<&2, Content>) -> Maybe<&2, Draft>:
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
  a: Maybe<&2, Ledgers.Asked<Ask>>,
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
  +s: State(),
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
      Draft.last(s, w, r, b, n, rest, Draft.of(w, r, b, n, i, Node.asked(s, i), found))

# the content of the draft m, if any
def Draft.what(m: Maybe<&2, Draft>) -> Maybe<&2, Content>:
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
  +s: State(),
  w: String,
  +r: Ledgers.Id,
  +b: String,
  n: Resources.Name
) -> Maybe<&2, Content>:
  Draft.what(Draft.last(s, w, r, b, n, Wait.of(s, Line.chain(r, Some{b})), None{}))

# the bytes of the draft m of the resource n, else what the point p holds
def Read.of(+s: State(), n: Resources.Name, m: Maybe<&2, Content>, p: Point) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case Some{c}:
      Root.bytes(s, Content.root(s, n, c))
    case None{}:
      Node.content(s, n, p)

# what the writer w reads of the resource n at the point p: at the head of a
# branch, its own pending write; else what the point holds
def Node.read(+s: State(), w: String, +n: Resources.Name, p: Point) -> Maybe<&2, Texts.Bytes()>:
  match p:
    case Point.Head{+r, +b}:
      Read.of(s, n, Node.draft(s, w, r, b, n), Point.Head{r, b})
    case x:
      Node.content(s, n, x)

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Ask>>,
  rest: List<&2, LogEntry>
) -> List<&2, LogEntry>:
  match held r:
    case True{} Some{Ledgers.Asked{t, q}}:
      LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: State(),
  +n: Resources.Name,
  xs: List<&2, Ledgers.Id>,
  prev: Maybe<&2, Ledgers.Id>
) -> List<&2, LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(Roots.same(Res.root_at(s, n, Some{x}), Res.root_at(s, n, prev))),
        x,
        Node.asked(s, x),
        Log.of(s, n, r, Some{x})
      )

# the versions of the branch b of the store r that changed the resource n
def Node.log(+s: State(), n: Resources.Name, r: Ledgers.Id, b: String) -> List<&2, LogEntry>:
  Log.of(s, n, Node.versions(s, r, b), None{})

# what changed in the resource n from the point a to the point b, as the
# writer w reads them
def Node.diff(
  +s: State(),
  +w: String,
  +n: Resources.Name,
  a: Point,
  b: Point
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
        Shared.List.is_eq(~U32, ~U32.is_eq, ws, Clash.code(f)),
        u => Read.whole(Resources.Name, Resources.Name.code.read(k))
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
def Clash.names(s: State(), h: Maybe<&2, Hashes.Hash>, f: Ledgers.Id) -> List<&2, Resources.Name>:
  Clash.of.bindings(Trees.Tree.list(~State(), ~Store.fetch, s, h), f)

# the resources of ns whose clash, which the merge of the version f opened, is
# still open in the tree h
def Clash.left(
  +s: State(),
  ns: List<&2, Resources.Name>,
  +h: Maybe<&2, Hashes.Hash>,
  +f: Ledgers.Id
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(Resources.Name, n, Clash.left(s, r, h, f), Clash.open(s, h, n, f))

# the resources that clashed at the request k, whose request is a, when it is a
# merge
def Merge.clashes(+s: State(), k: Ledgers.Id, a: Maybe<&2, Ledgers.Asked<Ask>>) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Ask.On{r, l, Change.Merge{f}}}}:
      Clash.names(s, Node.root_of(s, Some{k}), f)
    case _:
      []

# the resources that still clash after the merge k, whose request is a: those
# whose clash it opened, and that no resolve or newer merge settled since, at
# the head of its line
def Merge.left(
  +s: State(),
  k: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Ask>>
) -> List<&2, Resources.Name>:
  match a:
    case Some{Ledgers.Asked{t, Ask.On{r, Some{l}, Change.Merge{+f}}}}:
      Clash.left(
        s,
        Clash.names(s, Node.root_of(s, Some{k}), f),
        Chain.root(s, Line.chain(r, Some{l})),
        f
      )
    case _:
      []

# the resources that still clash after the merge k
def Node.conflict(+s: State(), +k: Ledgers.Id) -> List<&2, Resources.Name>:
  Merge.left(s, k, Node.asked(s, k))

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

# Written i, or Conflicted k while the merge k still clashes
def Answer.left(s: State(), i: Ledgers.Id, +k: Ledgers.Id) -> Answer:
  Shared.Bool.when(
    Answer,
    List.is_empty(&2, Resources.Name, Node.conflict(s, k)),
    u => Answer.Written{i},
    u => Answer.Conflicted{k}
  )

# the answer to the change q of the request i, which a step took
def Answer.taken(s: State(), +i: Ledgers.Id, q: Ask) -> Answer:
  match q:
    case Ask.On{st, l, Change.Merge{f}}:
      Answer.left(s, i, i)
    case Ask.On{st, l, Change.Resolve{k, n, c}}:
      Answer.left(s, i, k)
    case _:
      Answer.Written{i}

# the answer to the request i of the change q, whose outcome is o: Pending
# while no step that the node knows decided it
def Answer.of(s: State(), i: Ledgers.Id, q: Ask, o: Maybe<&2, Out>) -> Answer:
  match o:
    case Some{Out.Taken{n}}:
      Answer.taken(s, i, q)
    case Some{Out.Stale{}}:
      Answer.Stale{}
    case None{}:
      Answer.Pending{}

# the answer to the request i that the node holds as the change q: a store
# that starts is Written at once
def Answer.asked(+s: State(), +i: Ledgers.Id, q: Ask) -> Answer:
  match q:
    case Ask.Start{os}:
      Answer.Written{i}
    case x:
      Answer.of(s, i, x, Node.out(s, i))

# the answer to the change q of the request i, whose slot holds m: none when it
# is empty, Refused when it holds another change
def Answer.held(
  s: State(),
  i: Ledgers.Id,
  q: Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
) -> Maybe<&2, Answer>:
  match m:
    case None{}:
      None{}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Some{
        Shared.Bool.when(
          Answer,
          Ask.is_eq(q2, q),
          u => Answer.asked(s, i, q2),
          u => Answer.Refused{}
        )
      }
    case Some{c}:
      Some{Answer.Refused{}}

# what the node answers to the change q of e (none: it did not take it in)
def Node.answer(+s: State(), e: Envelope, q: Ask) -> Maybe<&2, Answer>:
  +i = Envelope.of(e)
  Answer.held(s, i, q, Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.ask(i)))

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
def Branch.at(+s: State(), h: Head, rest: List<&2, BranchEntry>) -> List<&2, BranchEntry>:
  match h:
    case Head{+r, Some{+b}, n, t}:
      Branch.put(r, b, Node.owners(s, r, Some{b}), Node.head(s, r, b), rest)
    case x:
      rest

# the branches of the heads hs
def Branch.all(+s: State(), hs: List<&2, Head>) -> List<&2, BranchEntry>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      Branch.at(s, h, Branch.all(s, rest))

# every branch that the node follows
def Node.branches(+s: State()) -> List<&2, BranchEntry>:
  Branch.all(s, Tries.Trie.values(Head, State.heads(s)))

# the branches es
def Branch.names(es: List<&2, BranchEntry>) -> List<&2, Branch>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{b, os, h}, r}:
      b <> Branch.names(r)

# the versions of the branch b
def Branch.versions(s: State(), b: Branch) -> List<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      Node.versions(s, r, n)

# the head of the branch b, if b exists
def Branch.head(s: State(), b: Branch) -> Maybe<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      Node.head(s, r, n)

# the resources of the branch b at its head
def Node.resources(+s: State(), b: Branch) -> List<&2, Resources.Name>:
  Res.names(s, Node.root_of(s, Branch.head(s, b)))

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
  s: State(),
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
  +s: State(),
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
        Tries.Trie.set(List<&2, Resources.Name>, t, Name.key(n), Uses.targets(s, h, n))
      )

# the graph of the imports of the branch b, at its head
def Uses.of(+s: State(), b: Branch) -> Uses:
  +h = Branch.head(s, b)
  +ns = Res.names(s, Node.root_of(s, h))
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
        Tries.Trie.get(List<&2, Resources.Name>, t, Name.key(n)),
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
def Wrote.of(r: Maybe<&2, Ledgers.Asked<Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, Ask.On{st, l, Change.Write{m, base, c}}}}:
      Some{m}
    case Some{Ledgers.Asked{t, Ask.On{st, l, Change.Resolve{k, m, c}}}}:
      Some{m}
    case _:
      None{}

# the resource that the version v wrote, when it is a write or a resolve
def Node.wrote(s: State(), v: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  Wrote.of(Node.asked(s, v))

# the versions of the branches es
def Touch.versions.of(+s: State(), es: List<&2, Branch>) -> List<&2, Ledgers.Id>:
  match es:
    case Nil{}:
      []
    case Con{b, r}:
      List.append(&2, Ledgers.Id, Branch.versions(s, b), Touch.versions.of(s, r))

# the versions of every branch
def Touch.versions(+s: State()) -> List<&2, Ledgers.Id>:
  Touch.versions.of(s, Branch.names(Node.branches(s)))

# the branch b lacks the version v
def Touch.lacks(+s: State(), +b: Branch, +v: Ledgers.Id) -> Bool:
  Bool.and(
    Maybe.is_some(&2, Ledgers.Id, Branch.head(s, b)),
    Bool.not(Node.has(s, Maybe.default(&2, Ledgers.Id, Branch.head(s, b), v), v))
  )

# the key of the branch b
def Branch.key(b: Branch) -> List<&2, Bool>:
  match b:
    case Branch{r, n}:
      List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# what the checks of touches on one branch read of s once: a key for each
# branch and for each version of a branch, the branch, and its imports
type Seen is Data:
  Seen{
    state: State(),
    branches: Tries.Trie<Unit>,
    versions: Tries.Trie<Unit>,
    branch: Branch,
    uses: Uses
  }

# what the checks on the branch b read of s, with the keys of the branches bs
# and of the versions vs
def Seen.of(+s: State(), bs: Tries.Trie<Unit>, vs: Tries.Trie<Unit>, +b: Branch) -> Seen:
  Seen{s, bs, vs, b, Uses.of(s, b)}

# the keys of the branches of s
def Branch.keys(s: State()) -> Tries.Trie<Unit>:
  Tries.Trie.put_keys(~Branch, ~Branch.key, Branch.names(Node.branches(s)), Tries.Trie.new(Unit))

# the keys of the versions of every branch of s
def Version.keys(s: State()) -> Tries.Trie<Unit>:
  Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, Touch.versions(s), Tries.Trie.new(Unit))

# the touch t, of the branch of g, holds: its branch is a branch and lacks
# its version, which is a version of a branch and wrote the resource changed,
# and the resource used is of the branch, and is the one changed or uses it;
# each part runs only when the ones before it hold, from the cheapest
def Touch.holds(g: Seen, t: Touch) -> Bool:
  match g t:
    case Seen{+s, bs, vs, gb, +us} Touch{+v, +c, +b, +u}:
      List.all.if(
        w => List.all.if(
          w => List.all.if(
            w => List.all.if(
              w => List.all.if(
                w => List.any.if(w => Uses.reach(us, u, c), Resources.Name.is_eq(u, c)),
                Tries.Trie.has(List<&2, Resources.Name>, Uses.imports(us), Name.key(u))
              ),
              Shared.Maybe.is_eq(~Resources.Name, ~Resources.Name.is_eq, Node.wrote(s, v), Some{c})
            ),
            Touch.lacks(s, b, v)
          ),
          Tries.Trie.has(Unit, vs, Ledgers.Id.key(v))
        ),
        Tries.Trie.has(Unit, bs, Branch.key(b))
      )

# the touch t holds
def Node.touches(+s: State(), t: Touch) -> Bool:
  match t:
    case Touch{v, c, +b, u}:
      Touch.holds(Seen.of(s, Branch.keys(s), Version.keys(s), b), Touch{v, c, b, u})

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
    case Seen{s, bs, vs, b, us}:
      +v = v
      Touch.of(Node.wrote(s, v), v, b, Uses.nodes(us))

# the touches that may hold of the branch of g
def Affects.cands(s: State(), g: Seen) -> List<&2, Touch>:
  Shared.List.flat(~Ledgers.Id, ~Touch, ~Seen, ~Affects.at, Touch.versions(s), g)

# the changes elsewhere that touch what the branch b uses, at any depth
def Node.affects(+s: State(), b: Branch) -> List<&2, Touch>:
  +g = Seen.of(s, Branch.keys(s), Version.keys(s), b)
  Shared.List.keep(~Touch, ~Seen, ~Touch.holds, Affects.cands(s, g), g)

# the checks of one branch, and the version of a point
type Impact is Data:
  Impact{seen: Seen, version: Maybe<&2, Ledgers.Id>}

# the touch t is of the version of g, or of a version that it came from, and
# holds
def Impact.keeps(g: Impact, t: Touch) -> Bool:
  match g t:
    case Impact{Seen{+s, bs, vs, gb, us}, +m} Touch{+v, c, b, u}:
      List.all.if(
        w => Touch.holds(Seen{s, bs, vs, gb, us}, Touch{v, c, b, u}),
        List.all.if(
          w => Node.has(s, Maybe.default(&2, Ledgers.Id, m, v), v),
          Maybe.is_some(&2, Ledgers.Id, m)
        )
      )

# what the changes up to the version m touch on the branches es, with the
# keys of the branches bs and of the versions vs
def Impact.of(
  +s: State(),
  +bs: Tries.Trie<Unit>,
  +vs: Tries.Trie<Unit>,
  +m: Maybe<&2, Ledgers.Id>,
  es: List<&2, Branch>
) -> List<&2, Touch>:
  match es:
    case Nil{}:
      []
    case Con{b, r}:
      +g = Seen.of(s, bs, vs, b)
      List.append(
        &2,
        Touch,
        Shared.List.keep(~Touch, ~Impact, ~Impact.keeps, Affects.cands(s, g), Impact{g, m}),
        Impact.of(s, bs, vs, m, r)
      )

# what the changes up to the point p touch elsewhere
def Node.impact(+s: State(), p: Point) -> List<&2, Touch>:
  Impact.of(s, Branch.keys(s), Version.keys(s), Node.version(s, p), Branch.names(Node.branches(s)))

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, or the changes elsewhere that touch it
type Topic is Data:
  Topic.Versions{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Affects{branch: Branch}

# an event of a topic
type Notice is Data:
  Notice.Versioned{branch: Branch, version: Ledgers.Id}
  Notice.Conflicted{branch: Branch, version: Ledgers.Id}
  Notice.Touched{touch: Touch}

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
          List.append(&2, Bool, Name.key(c), List.append(&2, Bool, Branch.key(b), Name.key(u)))
        )

# the versions xs of the branch b, as notices
def Notice.versions(+b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Notice.Versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(+s: State(), +b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Notice,
        Notice.Conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(List.is_empty(&2, Resources.Name, Merge.clashes(s, x, Node.asked(s, x))))
      )

# the touches ts, as notices
def Notice.touches(ts: List<&2, Touch>) -> List<&2, Notice>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Notice.Touched{t} <> Notice.touches(r)

# the notices of the topic t in s
def Notice.all(+s: State(), t: Topic) -> List<&2, Notice>:
  match t:
    case Topic.Versions{+b}:
      Notice.versions(b, Branch.versions(s, b))
    case Topic.Conflicts{+b}:
      Notice.conflicts(s, b, Branch.versions(s, b))
    case Topic.Affects{b}:
      Notice.touches(Node.affects(s, b))

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

# the notices of the topic t in s that since does not have
def Node.notices(s: State(), +t: Topic, since: State()) -> List<&2, Notice>:
  Notice.new(
    Notice.all(s, t),
    Tries.Trie.put_keys(~Notice, ~Notice.key, Notice.all(since, t), Tries.Trie.new(Unit))
  )

# a resource mounted to a branch
type Mount is Data:
  Mount{resource: String, branch: Branch}

# what a Vend Node holds: its name, the parts of the stores that it uses, the
# writers connected to it, and the resources mounted to it
type Vend is Data:
  Vend{name: String, state: State(), writers: List<&2, String>, mounts: List<&2, Mount>}

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
def Node.grows(a: State(), b: State()) -> Bool:
  Ledgers.State.grows(~Ask, ~Ask.is_eq, State.ledger(a), State.ledger(b))

# Laws
# ----
# What README says of a Vend Node's core, as laws. src/daemon/DESIGN.md lists
# the laws that are not stated yet. A law of the ledger that asks for the laws
# of a change's equality holds of a node's ledger by Ask.same.

# two requests are the same exactly when they are equal
law Ask.same:
  Shared.Eq.Laws(Ask, Ask.is_eq)

# the owners of a line are the nodes inside its owner group: its owners take
# an Own only when its owners are the nodes inside its group, in the store
# tree that it names (Own.tree)
law Own.takes_inside:
  for +s: State()
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +g: String
  for +at: Maybe<&2, Ledgers.Id>
  for +os: List<&2, String>
  for +h: Maybe<&2, Hashes.Hash>
  {Own.takes(s, r, l, g, at, os, h) == Some{True{}}: Maybe<&2, Bool>}
    -> {os == Group.nodes(s, Own.tree(s, l, at, h), g): List<&2, String>}

# a node that takes in a request only grows: it keeps every entry that it
# holds
law Node.ask_grows:
  for +n: String
  for +s: State()
  for +e: Envelope
  for +q: Ask
  {Node.grows(s, Node.ask(n, s, e, q)) == True{}: Bool}

# a node that takes in what another node sent only grows, whatever was sent
law Node.take_grows:
  for +s: State()
  for +t: Ledgers.State(Ask)
  {Node.grows(s, Node.take(s, t)) == True{}: Bool}

# a sync only grows a node: catching up loses and changes nothing that the
# node holds
law Node.sync_grows:
  for +n: String
  for +s: State()
  for +t: Ledgers.State(Ask)
  {Node.grows(s, Node.sync(n, s, t)) == True{}: Bool}

# the tip that the step m names, if any
def Vote.tip(m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Ledgers.Vote{before, qs, after}}:
      after
    case None{}:
      None{}

# the head x one height up, at the tip y
def Head.up(x: Head, y: Hashes.Hash) -> Head:
  match x:
    case Head{r, b, n, th}:
      Head{r, b, U32.inc(n), Some{y}}

# the head x after the step m (none: no step, or one that names no tip)
def Head.moved(x: Head, m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Head>:
  Maybe.bind(&2, Hashes.Hash, Head, Vote.tip(m), y => Some{Head.up(x, y)})

# the step that the owners in the tip of the head x decided next on the line
# c, in the round r, if they did
def Advance.in(+s: State(), c: Ledgers.Chain, +x: Head, r: Nat) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Tip,
    Ledgers.Vote,
    Head.tip(s, x),
    t => Ledgers.State.decide(~Ask, State.ledger(s), Ledgers.Where{c, Head.next(x), r}, Line.owners(s, t))
  )

# the head of the line c after one decided step for each round of rs, the
# last first, from the head h, by the ledger of s alone (none: a step is not
# decided in its round). A law's measure: no node runs it
def Line.at(rs: List<&2, Nat>, +s: State(), +c: Ledgers.Chain, h: Head) -> Maybe<&2, Head>:
  match rs:
    case Nil{}:
      Some{h}
    case Con{+r, rest}:
      Maybe.bind(
        &2,
        Head,
        Head,
        Line.at(rest, s, c, h),
        +x => Head.moved(x, Advance.in(s, c, x, r))
      )

# that the rounds of each height of the line c decide one step in s
def Line.One(s: State(), c: Ledgers.Chain) -> Type:
  @x: Head -> @t: Tip -> {Head.tip(s, x) == Some{t}: Maybe<&2, Tip>} -> Height.One(
    s,
    c,
    Head.next(x),
    Line.owners(s, t)
  )

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(k: Nat, s: State(), c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(p, s, c) & Line.One(s, c)

# what a node does next: it takes in a request, or what another node sent,
# or it does a sync, or it keeps new bytes, or a writer connected to it asks
# for a request that it holds, or it passes to the next round on a line
type Deed is Data:
  Deed.Ask{envelope: Envelope, ask: Ask}
  Deed.Take{sent: Ledgers.State(Ask)}
  Deed.Sync{sent: Ledgers.State(Ask)}
  Deed.Keep{bytes: Texts.Bytes()}
  Deed.Consent{id: Ledgers.Id}
  Deed.Pass{line: Ledgers.Chain}

# s, after the node n did ev
def Node.does(n: String, s: State(), ev: Deed) -> State():
  match ev:
    case Deed.Ask{e, q}:
      Node.ask(n, s, e, q)
    case Deed.Take{t}:
      Node.take(s, t)
    case Deed.Sync{t}:
      Node.sync(n, s, t)
    case Deed.Keep{b}:
      Node.keep(s, b)
    case Deed.Consent{i}:
      Node.consent(n, s, i)
    case Deed.Pass{c}:
      Node.pass(n, s, c)

# s, after the node n did each of evs, in order: any later state of the node
def Node.after(+n: String, evs: List<&2, Deed>, s: State()) -> State():
  match evs:
    case Nil{}:
      s
    case Con{ev, rest}:
      Node.after(n, rest, Node.does(n, s, ev))

# that b holds, in the log of each line, each key that a holds there, other
# than the owners of the next step and the count of versions
def Node.Keeps(a: State(), b: State()) -> Type:
  @c: Ledgers.Chain -> @k: List<&2, U32> -> @v: List<&2, U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Log.owners(), k) == False{}: Bool
  } -> {Shared.List.is_eq(~U32, ~U32.is_eq, Log.count(), k) == False{}: Bool} -> {
    Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Line.get(b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}

# a node only grows, whatever it does
law Node.after_grows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  {Node.grows(s, Node.after(n, evs, s)) == True{}: Bool}

# a log only gains keys: what the log of a line holds, it holds for good,
# whatever the node does next
law Node.after_keeps:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  Node.Keeps(s, Node.after(n, evs, s))

# the head m has a tip
def Head.held(m: Maybe<&2, Head>) -> Bool:
  match m:
    case Some{Head{r, b, n, Some{t}}}:
      True{}
    case x:
      False{}

# that the head of the line c in s is some decided steps from the head h0, by
# the ledger of s
def Line.Reach(s: State(), c: Ledgers.Chain, h0: Head) -> Type:
  Exists(
    List<&2, Nat>,
    rs => Exists(
      Head,
      h => {Node.head_of(s, c) == Some{h}: Maybe<&2, Head>} & {Line.at(rs, s, c, h0) == Some{h}: Maybe<&2, Head>}
    )
  )

# that each head of a that is some decided steps from a head with a tip is,
# in b, some decided steps from it
def Node.On(a: State(), b: State()) -> Type:
  @c: Ledgers.Chain -> @h0: Head -> {Head.held(Some{h0}) == True{}: Bool} -> Line.Reach(a, c, h0) -> Line.Reach(
    b,
    c,
    h0
  )

# every head is on the decided chain: a head that has a tip moves only over
# decided steps, whatever the node does next
law Node.after_on:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  Node.On(s, Node.after(n, evs, s))

# an outcome is final: a request that a step took stays taken, as the same
# version number, and one that its owners refused stays refused
law Node.out_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +i: Ledgers.Id
  for +o: Out
  {Node.out(s, i) == Some{o}: Maybe<&2, Out>}
    -> {Node.out(Node.after(n, evs, s), i) == Some{o}: Maybe<&2, Out>}

# a version never changes: the request that made it and the root of its
# content stay
law Node.made_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +v: Ledgers.Id
  for +x: Version
  {Node.made(s, v) == Some{x}: Maybe<&2, Version>}
    -> {Node.made(Node.after(n, evs, s), v) == Some{x}: Maybe<&2, Version>}

# the history of a line only grows at its end: the version of a number stays
law Chain.version_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +c: Ledgers.Chain
  for +k: U32
  for +x: Version
  {Chain.version(s, c, k) == Some{x}: Maybe<&2, Version>}
    -> {Chain.version(Node.after(n, evs, s), c, k) == Some{x}: Maybe<&2, Version>}

# a mark names its version for good
law Chain.mark_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +c: Ledgers.Chain
  for +m: String
  for +v: Ledgers.Id
  {Chain.mark(s, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}
    -> {Chain.mark(Node.after(n, evs, s), c, m) == Some{v}: Maybe<&2, Ledgers.Id>}

# the first tip of a branch is for good: what the log of a store holds for a
# branch, it holds whatever the node does next, so a node that opens the
# branch later opens it at the same tip
law Chain.start_final:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +r: Ledgers.Id
  for +b: String
  for +v: List<&2, U32>
  {Line.get(s, Ledgers.Chain{r, None{}}, Log.start(b)) == Some{v}: Maybe<&2, List<&2, U32>>}
    -> {
      Line.get(Node.after(n, evs, s), Ledgers.Chain{r, None{}}, Log.start(b))
        == Some{v}: Maybe<&2, List<&2, U32>>
    }

# answers only move forward: a request that a node answers stays answered;
# Stale and Refused are final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for +n: String
  for +evs: List<&2, Deed>
  for +s: State()
  for +e: Envelope
  for +q: Ask
  for +x: Answer
  {Node.answer(s, e, q) == Some{x}: Maybe<&2, Answer>}
    -> {Answer.follows(x, Node.answer(Node.after(n, evs, s), e, q)) == True{}: Bool}

# while a write that the writer w asked for waits on its line, the node has a
# draft of the resource for w (the newest of its pending writes, by
# Draft.newer)
law Node.draft_some:
  for +s: State()
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +q2: String
  for +t: String
  for +q: Ask
  for +c: Content
  {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Wait.of(s, Line.chain(r, Some{b})),
      Ledgers.Id{w, q2}
    )
      == True{}: Bool
  }
    -> {Node.asked(s, Ledgers.Id{w, q2}) == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Ask>>}
    -> {Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Content>}
    -> {Maybe.is_some(&2, Content, Node.draft(s, w, r, b, n)) == True{}: Bool}

# a majority decides, in sequence: a head moves only to the tip that the
# owners in its tip decided next (Advance.vote)
law Node.advance_decided:
  for +s: State()
  for +c: Ledgers.Chain
  for +h: Head
  {Node.head_of(s, c) == Some{h}: Maybe<&2, Head>}
    -> {Heads.level(Some{h}, Node.head_of(Node.advance(s, c), c)) == False{}: Bool}
    -> {
      Node.head_of(Node.advance(s, c), c) == Some{Head.step(h, Advance.vote(s, c, h))}: Maybe<&2, Head>
    }

# so two nodes at the same head of a line, whose ledgers do not clash (one
# node u keeps every cell of both, and the rounds of the height decide one
# step in it), move to the same head
law Node.advance_agrees:
  for +a: State()
  for +b: State()
  for +u: State()
  for +c: Ledgers.Chain
  for +h: Head
  {Node.grows(a, u) == True{}: Bool}
    -> {Node.grows(b, u) == True{}: Bool}
    -> Line.One(u, c)
    -> {Node.head_of(a, c) == Some{h}: Maybe<&2, Head>}
    -> {Node.head_of(b, c) == Some{h}: Maybe<&2, Head>}
    -> {Heads.level(Some{h}, Node.head_of(Node.advance(a, c), c)) == False{}: Bool}
    -> {Heads.level(Some{h}, Node.head_of(Node.advance(b, c), c)) == False{}: Bool}
    -> {
      Node.head_of(Node.advance(a, c), c) == Node.head_of(Node.advance(b, c), c): Maybe<&2, Head>
    }

# a write that its owners take is what the resource holds after it: in a node
# that holds the new nodes, the resource reads as the content of the write
law Judge.write_reads:
  for +s: State()
  for +n: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +c: Content
  for +h: Maybe<&2, Hashes.Hash>
  for +h2: Maybe<&2, Hashes.Hash>
  for +ds: List<&2, List<&2, U32>>
  for +s3: State()
  for +m: Maybe<&2, Ropes.Root>
  {Judge.write(s, n, base, c, h) == Some{Verdict{True{}, h2, ds}}: Maybe<&2, Verdict>}
    -> {State.put(s, ds) == Some{s3}: Maybe<&2, State()>}
    -> {Content.find(s, n, c) == Some{m}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.root(s3, h2, n) == m: Maybe<&2, Ropes.Root>}

# a merge keeps, for each resource, a change that only one side made: when
# ours is the base, it keeps theirs
law Pick.merge_theirs:
  for f: Formats.Format
  for s: State()
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Roots.same(o, b) == True{}: Bool}
    -> {Pick.merge(f, s, b, o, t) == Some{Pick.Take{t}}: Maybe<&2, Pick>}

# and when theirs is the base, it keeps ours
law Pick.merge_ours:
  for f: Formats.Format
  for s: State()
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Roots.same(o, b) == False{}: Bool}
    -> {Roots.same(t, b) == True{}: Bool}
    -> {Pick.merge(f, s, b, o, t) == Some{Pick.Take{o}}: Maybe<&2, Pick>}

# a node keeps only ballots that it checked: a ballot that it accepts is the
# next of its node's chain in its store, and the key of that chain signs it
law Seal.accept_fits:
  for +s: State()
  for +b: Ledgers.Ballot
  for +c: Chained
  for +s2: State()
  {Seal.chain(s, Ballot.store(b), Ballot.node(b)) == Some{c}: Maybe<&2, Chained>}
    -> {Seal.accept(s, b) == Some{s2}: Maybe<&2, State()>}
    -> {Seal.fits(c, b) == True{}: Bool}

# a ballot that a node seals with the secret of its chain's key fits the chain.
# (That no other node can make one is the assumption of Seals: a hash has no
# known second input.)
law Seal.fits_own:
  for +seed: Hashes.Hash
  for +x: Ledgers.Signed
  for +last: Maybe<&2, Ledgers.Where>
  for +k: Hashes.Hash
  for +n: U32
  for +f: Hashes.Hash
  {
    Seal.fits(Chained{n, last, Seals.Seal.public(seed), f}, Ledgers.Ballot.make(seed, x, last, k))
      == True{}: Bool
  }

# a move of a head is one decided step of its line, in some round
law Node.advance_at:
  for +s: State()
  for +c: Ledgers.Chain
  for +h: Head
  {Node.head_of(s, c) == Some{h}: Maybe<&2, Head>}
    -> {Heads.level(Some{h}, Node.head_of(Node.advance(s, c), c)) == False{}: Bool}
    -> Exists(
      Nat,
      q => {Line.at([q], s, c, h) == Node.head_of(Node.advance(s, c), c): Maybe<&2, Head>}
    )

# the decided steps of a line stay as a node grows: a head that is some
# decided steps from a head h is so in any node that keeps every cell
law Line.at_grows:
  for +rs: List<&2, Nat>
  for +a: State()
  for +u: State()
  for +c: Ledgers.Chain
  for +h: Head
  for +x: Head
  {Node.grows(a, u) == True{}: Bool}
    -> {Line.at(rs, a, c, h) == Some{x}: Maybe<&2, Head>}
    -> {Line.at(rs, u, c, h) == Some{x}: Maybe<&2, Head>}

# so two nodes whose ledgers do not clash (one node u keeps every cell of
# both, and the rounds of each height decide one step in it), the same number
# of decided steps from the same head of a line, are at the same head,
# whatever the round of each step: one history
law Line.at_agrees:
  for +rs1: List<&2, Nat>
  for +rs2: List<&2, Nat>
  for +a: State()
  for +b: State()
  for +u: State()
  for +c: Ledgers.Chain
  for +h: Head
  for +x: Head
  for +y: Head
  {Node.grows(a, u) == True{}: Bool}
    -> {Node.grows(b, u) == True{}: Bool}
    -> Line.Ones(List.length(&2, Nat, rs1), u, c)
    -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
    -> {Line.at(rs1, a, c, h) == Some{x}: Maybe<&2, Head>}
    -> {Line.at(rs2, b, c, h) == Some{y}: Maybe<&2, Head>}
    -> {x == y: Head}

# a node fetches on demand: a node b that lacks the data of the hash h holds
# it after it takes in what a node a that holds it serves
law Node.fetch:
  for +a: State()
  for +b: State()
  for +h: Hashes.Hash
  for +ws: List<&2, U32>
  {Ledgers.State.data(~Ask, State.ledger(a), h) == Some{ws}: Maybe<&2, List<&2, U32>>}
    -> {
      Ledgers.State.get(~Ask, State.ledger(b), Ledgers.Slot.data(h))
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
    }
    -> {
      Ledgers.State.data(~Ask, State.ledger(Node.take(b, Node.serve(a, [h]))), h)
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }

# every part is kept by enough nodes: a node that casts for a step keeps each
# new part of the step (what its own run of the step put: the node of the run
# is s2), so a majority of the owners holds each part of a decided step; and a
# node only grows (Node.after_grows)
law Cast.put_keeps:
  for +n: String
  for +w: Ledgers.Where
  for +th: Maybe<&2, Hashes.Hash>
  for +qs: List<&2, Ledgers.Id>
  for +from: List<&2, String>
  for +s2: State()
  for +t2: Tip
  for +ns: List<&2, List<&2, U32>>
  for +s: State()
  for +s3: State()
  {State.put(s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, State()>}
    -> {Node.grows(s2, Cast.put(n, w, th, qs, from, Some{Run{s2, t2, ns}}, s)) == True{}: Bool}

# and it holds the tip that it casts for
law Cast.put_tip:
  for +n: String
  for +w: Ledgers.Where
  for +th: Maybe<&2, Hashes.Hash>
  for +qs: List<&2, Ledgers.Id>
  for +from: List<&2, String>
  for +s2: State()
  for +t2: Tip
  for +ns: List<&2, List<&2, U32>>
  for +s: State()
  for +s3: State()
  {State.put(s2, [Tip.words(t2)]) == Some{s3}: Maybe<&2, State()>}
    -> {
      Tip.at(Cast.put(n, w, th, qs, from, Some{Run{s2, t2, ns}}, s), Tip.hash(t2))
        == Some{t2}: Maybe<&2, Tip>
    }

# a node holds what it takes in: an entry that it reads of what was sent, in
# a slot that it lacks, it then holds
law Node.take_holds:
  for +s: State()
  for +t: Ledgers.State(Ask)
  for +k: List<&2, Bool>
  for +e: Ledgers.Entry<Ask>
  {
    Ledgers.State.get(~Ask, Node.reads(t), k)
      == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
  }
    -> {Ledgers.State.get(~Ask, State.ledger(s), k) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>}
    -> {
      Ledgers.State.get(~Ask, State.ledger(Node.take(s, t)), k)
        == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
    }

# a pending write goes with its writer to another node: a request that a node
# takes in waits on its line there, so the node has a draft for its writer
# (Node.draft_some) and the writer's read shows it (Node.read_draft)
law Node.take_waits:
  for +s: State()
  for +t: Ledgers.State(Ask)
  for +i: Ledgers.Id
  for +time: String
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +ch: Change
  {
    Ledgers.State.get(~Ask, Node.reads(t), Ledgers.Slot.ask(i))
      == Some{Cells.One{Ledgers.Entry.Ask{i, time, Ask.On{r, l, ch}}}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
  }
    -> {
      Ledgers.State.get(~Ask, State.ledger(s), Ledgers.Slot.ask(i))
        == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
    }
    -> {
      List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Wait.of(Node.take(s, t), Line.chain(r, l)), i) == True{}: Bool
    }

# a writer reads its own pending write: at the head of a branch, its read is
# the bytes of its draft, not what the branch holds
law Node.read_draft:
  for +s: State()
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +c: Content
  {Node.draft(s, w, r, b, n) == Some{c}: Maybe<&2, Content>}
    -> {
      Node.read(s, w, n, Point.Head{r, b}) == Root.bytes(s, Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }

# a change counts once on a node, however often it is asked: a node that took
# a request in changes nothing when its ID is asked again (across nodes: a
# node takes a request that it holds no second time, Node.take, and a step
# skips a request that its log holds, Step.fresh)
law Node.ask_once:
  for +n: String
  for +m: String
  for +s: State()
  for +e: Envelope
  for +q: Ask
  for +e2: Envelope
  for +q2: Ask
  {Envelope.of(e2) == Envelope.of(e): Ledgers.Id}
    -> {Node.ask(m, Node.ask(n, s, e, q), e2, q2) == Node.ask(n, s, e, q): State()}
