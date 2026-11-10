import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Ledgers.Id. A store is named by
# the request that started it. A line is a store itself (no branch) or one of
# its branches.

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a member of an owner group: a node, or another group of its store
type Member is Data:
  Member.Node{name: String}
  Member.Group{name: String}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# new content: what a node holds under a root (the root of the rope of its
# bytes: Content.of), or what an old version held. A change names its content
# and does not carry it, so a change of a huge resource is small
type Content is Data:
  Content.Root{root: Ropes.Root}
  Content.Of{version: Ledgers.Id}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
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
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# a first owner of a store: a node, and the key that signs its first ballot in
# the store
type Owner is Data:
  Owner{name: String, key: Hashes.Hash}

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a change that a writer asks for: a store that starts with its first owners,
# or a change of a branch of a store (none: of the store itself)
type Ask is Data:
  Ask.Start{owners: List<&2, Owner>}
  Ask.On{store: Ledgers.Id, branch: Maybe<&2, String>, change: Change}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

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
          u => Codes.Code.one.read(
            ~String,
            ~Member,
            ~Codes.Code.text.read,
            n => Member.Group{n},
            r
          ),
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
type Keychain is Data:
  Keychain{count: U32, last: Maybe<&2, Ledgers.Where>, key: Hashes.Hash, first: Hashes.Hash}

# what a node keeps to seal its ballots and to check those of other nodes: its
# secret seed; the key chain of each node in each store (its own too); the
# requests that a writer connected to it asked for (an owner casts for a
# change of who decides only when it was asked at the owner itself); and the
# highest round of which it holds a ballot, for each height that has a round
# after the first
type Keys is Data:
  Keys{
    seed: Hashes.Hash,
    chains: Tries.Trie<Keychain>,
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

# the ledger of s
def State.ledger(s: Node) -> Ledgers.State(Ask):
  match s:
    case Node{l, hs, ws, ks}:
      l

# the heads of s
def State.heads(s: Node) -> Tries.Trie<Head>:
  match s:
    case Node{l, hs, ws, ks}:
      hs

# the requests of s that wait for a step, by line
def State.waiting(s: Node) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match s:
    case Node{l, hs, ws, ks}:
      ws

# the keys of s
def State.keys(s: Node) -> Keys:
  match s:
    case Node{l, hs, ws, ks}:
      ks

# s with the ledger l
def State.led(s: Node, l: Ledgers.State(Ask)) -> Node:
  match s:
    case Node{old, hs, ws, ks}:
      Node{l, hs, ws, ks}

# s with the keys ks
def State.keyed(s: Node, ks: Keys) -> Node:
  match s:
    case Node{l, hs, ws, old}:
      Node{l, hs, ws, ks}

# a node that holds nothing yet, with the secret seed
def Node.empty(seed: Hashes.Hash) -> Node:
  Node{
    Ledgers.State.empty(~Ask),
    Tries.Trie.new(Head),
    Tries.Trie.new(List<&2, Ledgers.Id>),
    Keys{seed, Tries.Trie.new(Keychain), Tries.Trie.new(Unit), Tries.Trie.new(Nat)}
  }

# the words that s holds under the hash h
def Store.fetch(s: Node, h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Ledgers.State.data(~Ask, State.ledger(s), h)

# s with the words ds as data, each under its hash
def State.keep(+s: Node, ds: List<&2, List<&2, U32>>) -> Node:
  State.led(s, Ledgers.State.put_datas(~Ask, ~Ask.is_eq, ds, State.ledger(s)))

# the request i, when s holds it
def Node.asked(s: Node, i: Ledgers.Id) -> Maybe<&2, Ledgers.Asked<Ask>>:
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
def Node.get.at(s: Node, +k: List<&2, U32>, m: Maybe<&2, Trees.Node>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Node.Empty{}}:
      None{}
    case Some{+n}:
      Trees.Tree.get.go(~Node, ~Store.fetch, s, Trees.Tree.path(k), k, Some{n})

# what the tree whose root is h holds under the key k, in the store s
def Node.get(+s: Node, h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Node.get.at(s, k, Trees.Tree.part(~Node, ~Store.fetch, s, h))

# Node.set once the root node m of the tree is known (see Node.get.at)
def Node.set.at(
  s: Node,
  h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Node>
) -> Maybe<&2, Trees.Put>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Trees.Tree.set.go(~Node, ~Store.fetch, s, Trees.Tree.path(k), 0n, k, x, h, Some{n})

# the tree whose root is h with the key k set to x: Trees.Tree.set (impl:
# Set.is)
def Node.set(
  +s: Node,
  +h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>
) -> Maybe<&2, Trees.Put>:
  Node.set.at(s, h, k, x, Trees.Tree.part(~Node, ~Store.fetch, s, h))

# Node.look once the root node m of the tree is known (see Node.get.at)
def Node.look.at(
  s: Node,
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
      Trees.Tree.look.go(~Node, ~Store.fetch, s, Trees.Tree.path(k), k, h, Some{n})

# what a read of the key k finds in the tree whose root is h: Trees.Tree.look
# (impl: Look.is)
def Node.look(+s: Node, +h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Trees.Look:
  Node.look.at(s, h, k, Trees.Tree.part(~Node, ~Store.fetch, s, h))

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
  s: Node,
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
  s: Node,
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
def Res.root(s: Node, h: Maybe<&2, Hashes.Hash>, n: Resources.Name) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, Node.get(s, h, Key.res(n)), ws => Res.read(ws))

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the bytes under the root m, if any, when s holds their rope
def Root.bytes(s: Node, m: Maybe<&2, Ropes.Root>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, Ropes.Root, Texts.Bytes(), m, r => Ropes.Rope.read(~Node, ~Store.fetch, s, r))

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
def Members.in(s: Node, h: Maybe<&2, Hashes.Hash>, g: String) -> Maybe<&2, List<&2, Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Member>,
    Node.get(s, h, Key.group(g)),
    ws => Read.whole(List<&2, Member>, Members.code.read(ws))
  )

# s with the bytes b: the nodes of their rope, each under its hash. A node
# keeps new bytes before it asks for a write of their content
def Node.keep(s: Node, b: Texts.Bytes()) -> Node:
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
def Tip.at(s: Node, h: Hashes.Hash) -> Maybe<&2, Tip>:
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

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# the outcome of a request: its owners refused it as stale, or took it as the
# version of a number
type Out is Data:
  Out.Stale{}
  Out.Taken{number: U32}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

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
def Line.owners(s: Node, t: Tip) -> List<&2, String>:
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
def Line.count(s: Node, t: Tip) -> U32:
  Maybe.default(
    &2,
    U32,
    Maybe.bind(&2, List<&2, U32>, U32, Node.get(s, Tip.log(t), Log.count()), ws => Count.read(ws)),
    0
  )

# the outcome of the request i on a line at the tip t (none: no step decided
# it yet)
def Line.out(s: Node, t: Tip, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Node.get(s, Tip.log(t), Log.out(i)), ws => Out.read(ws))

# the version of the number n of a line at the tip t
def Line.version(s: Node, t: Tip, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Version,
    Node.get(s, Tip.log(t), Log.version(n)),
    ws => Version.read(ws)
  )

# the version that the mark m names on a line at the tip t
def Line.mark(s: Node, t: Tip, m: String) -> Maybe<&2, Ledgers.Id>:
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
def Node.head_of(s: Node, c: Ledgers.Chain) -> Maybe<&2, Head>:
  Tries.Trie.get(Head, State.heads(s), Ledgers.Chain.key(c))

# the tip of the head h, when s holds it
def Head.tip(s: Node, h: Head) -> Maybe<&2, Tip>:
  match h:
    case Head{r, b, n, t}:
      Maybe.bind(&2, Hashes.Hash, Tip, t, x => Tip.at(s, x))

# what the line c holds now, as the node knows it
def Node.tip(+s: Node, c: Ledgers.Chain) -> Maybe<&2, Tip>:
  Maybe.bind(&2, Head, Tip, Node.head_of(s, c), h => Head.tip(s, h))

# what the log of the head h holds under the key k
def Head.get(+s: Node, h: Head, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Tip, List<&2, U32>, Head.tip(s, h), t => Node.get(s, Tip.log(t), k))

# what the log of the line c holds under the key k, as the node knows it
def Line.get(+s: Node, c: Ledgers.Chain, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
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
def Node.chain_of(s: Node, +i: Ledgers.Id) -> Maybe<&2, Ledgers.Chain>:
  Maybe.bind(
    &2,
    Ledgers.Asked<Ask>,
    Ledgers.Chain,
    Node.asked(s, i),
    a => Some{Ask.chain(i, Asked.ask(a))}
  )

# the outcome of the request i on the line c, as the node knows it
def Chain.out(s: Node, c: Ledgers.Chain, i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, List<&2, U32>, Out, Line.get(s, c, Log.out(i)), ws => Out.read(ws))

# the version of the number n of the line c, as the node knows it
def Chain.version(s: Node, c: Ledgers.Chain, n: U32) -> Maybe<&2, Version>:
  Maybe.bind(&2, List<&2, U32>, Version, Line.get(s, c, Log.version(n)), ws => Version.read(ws))

# the version that the mark m names on the line c, as the node knows it
def Chain.mark(s: Node, c: Ledgers.Chain, m: String) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Id,
    Line.get(s, c, Log.mark(m)),
    ws => Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws))
  )

# the outcome of the request i (none: no step that the node knows decided it)
def Node.out(+s: Node, +i: Ledgers.Id) -> Maybe<&2, Out>:
  Maybe.bind(&2, Ledgers.Chain, Out, Node.chain_of(s, i), c => Chain.out(s, c, i))

# the version of the outcome o on the line c, when it took one
def Out.on(s: Node, c: Ledgers.Chain, o: Out) -> Maybe<&2, Version>:
  match o:
    case Out.Stale{}:
      None{}
    case Out.Taken{n}:
      Chain.version(s, c, n)

# the version that the request v made on the line c
def Chain.made(+s: Node, +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Out, Version, Chain.out(s, c, v), o => Out.on(s, c, o))

# the version that the request v made (none: v is not a version that the node
# knows)
def Node.made(+s: Node, +v: Ledgers.Id) -> Maybe<&2, Version>:
  Maybe.bind(&2, Ledgers.Chain, Version, Node.chain_of(s, v), +c => Chain.made(s, c, v))

# the root of the content of the version v (none: v is not a version)
def Node.root(s: Node, v: Ledgers.Id) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(&2, Version, Maybe<&2, Hashes.Hash>, Node.made(s, v), x => Some{Version.root(x)})

# the root of the content of the version m, if any (none, or not a version:
# the empty tree)
def Node.root_of(s: Node, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Hashes.Hash>:
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
def Place.at(s: Node, c: Ledgers.Chain, v: Ledgers.Id, t: Tip) -> Maybe<&2, Place>:
  Maybe.bind(&2, Out, Place, Line.out(s, t, v), o => Out.place(c, o))

# the place of the version v on the line c
def Place.on(+s: Node, +c: Ledgers.Chain, v: Ledgers.Id) -> Maybe<&2, Place>:
  Maybe.bind(&2, Tip, Place, Node.tip(s, c), t => Place.at(s, c, v, t))

# the place of the version v
def Node.place(+s: Node, +v: Ledgers.Id) -> Maybe<&2, Place>:
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
def Node.vector(s: Node, h: Maybe<&2, Hashes.Hash>, +c: Ledgers.Chain) -> Maybe<&2, Place>:
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
def Place.from(s: Node, +px: Place, hx: Maybe<&2, Hashes.Hash>, +pv: Place) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Place.chain(px), Place.chain(pv)),
    u => Place.covers(px, pv),
    u => Place.covered(Node.vector(s, hx, Place.chain(pv)), pv)
  )

# Node.has once the places of x (mx) and of v (mv) and the root of x (mr) are
# known
def Has.of(
  s: Node,
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
def Node.has(+s: Node, +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Has.of(s, Node.place(s, x), Node.place(s, v), Node.root(s, x)),
    Ledgers.Id.is_eq(x, v)
  )

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(+s: Node, +x: Ledgers.Id, +y: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )
