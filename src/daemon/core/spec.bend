import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/reach.bend as Reaches
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees

# The pure core of a Vend Node (README): what it holds, what it answers, and
# the laws about both. transport/spec.bend carries it over IO.
#
# A node is a ledger of Vend's changes (Ledgers): it holds requests, votes and
# data, and each line (a branch or an owner group) is a chain of steps that
# its owners decided. Each version of a line is a tree (Trees) held as data:
# its root is the result of the vote that decided it. A store is the root
# chain that makes its lines, so two nodes never make one line twice. Every
# answer is read from the state alone, and every change of a node's state
# (Node.ask, Node.vote, Node.take) only grows it (Ledgers.State.grows), so
# what a law says stays as a state grows, stays for good.

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

# new content: bytes, or what an old version held
type Content is Data:
  Content.Bytes{bytes: Texts.Bytes()}
  Content.Of{version: Ledgers.Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}

# Requests
# --------
# A request is data alone: a point becomes a version before it is asked for,
# so that a request sent again, to any node, is the same request.

# a change of a branch, or of its store (Ask.on). Branch: the store makes the
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

# a change that a writer asks for: a store that starts with its first owners,
# or a change of a branch of a store (none: of the store itself)
type Ask is Data:
  Ask.Start{owners: List<&2, String>}
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

# Equality
# --------

# a and b are the same member
def Member.is_eq(a: Member, b: Member) -> Bool:
  match a b:
    case Member.Node{x} Member.Node{y}:
      String.eq(x, y)
    case Member.Group{x} Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# Codes
# -----
# A request is sent and stored as its code (Codes); two requests are the same
# exactly when their codes are.

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
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Member>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.Node{n}, r),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.Group{n}, r)
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
    case Content.Bytes{b}:
      0 <> Codes.Code.words(b, r)
    case Content.Of{v}:
      1 <> Ledgers.Id.code(v, r)

# a content
def Content.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Content>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Content>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~Texts.Bytes(),
          ~Content,
          ~Codes.Code.words.read,
          b => Content.Bytes{b},
          r
        ),
        u => Codes.Code.one.read(
          ~Ledgers.Id,
          ~Content,
          ~Ledgers.Id.code.read,
          v => Content.Of{v},
          r
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
                u => Codes.Code.two.read(
                  ~String,
                  ~List<&2, Member>,
                  ~Change,
                  ~Codes.Code.text.read,
                  ~Members.code.read,
                  g => ms => Change.Group{g, ms},
                  r
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

# the request q, then r
def Ask.code(q: Ask, r: List<&2, U32>) -> List<&2, U32>:
  match q:
    case Ask.Start{os}:
      0 <> Ledgers.Owners.code(os, r)
    case Ask.On{st, l, c}:
      1 <> Ledgers.Id.code(st, Target.code(l, Change.code(c, r)))

# a request
def Ask.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ask>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Ask>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~List<&2, String>,
          ~Ask,
          ~Ledgers.Owners.code.read,
          os => Ask.Start{os},
          r
        ),
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
        )
      )

# a and b are the same request: they have the same code
def Ask.is_eq(a: Ask, b: Ask) -> Bool:
  Codes.Code.is_eq(~Ask, ~Ask.code, a, b)

# Lines
# -----

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

# the line that the change c makes, when it makes one
def Change.makes(c: Change) -> Maybe<&2, List<&2, Bool>>:
  match c:
    case Change.Branch{n, at}:
      Some{Line.key(n)}
    case _:
      None{}

# what the ledger reads of q
def Ask.view(q: Ask) -> Ledgers.View:
  match q:
    case Ask.Start{os}:
      Ledgers.View.Root{os}
    case Ask.On{r, l, +c}:
      Ledgers.View.On{Line.chain(r, l), Change.owners(c), Change.makes(c)}

# The state
# ---------

# what a node holds
def State() -> Data:
  Ledgers.State(Ask)

# a node that holds nothing yet
def Node.empty() -> State():
  Ledgers.State.empty(~Ask)

# what a holder of a and of b holds: a sync
def Node.join(a: State(), b: State()) -> State():
  Ledgers.State.join(~Ask, ~Ask.is_eq, a, b)

# what a holder of r lacks of s: what a sync from s to r sends
def Node.missing(s: State(), r: State()) -> State():
  Ledgers.State.missing(~Ask, ~Ask.is_eq, s, r)

# no entry of t contradicts one of s
def Node.agrees(s: State(), t: State()) -> Bool:
  Ledgers.State.agrees(~Ask, ~Ask.is_eq, s, t)

# what a holder of s keeps of t, which another node sent: the entries of t in
# the slots where s holds nothing. A node checks what it receives against what
# it holds, so nothing that it holds is lost or changed; of states that agree,
# it is the sync (Ledgers.State.take_join)
def Node.take(s: State(), t: State()) -> State():
  Ledgers.State.take(~Ask, s, t)

# Versions
# --------
# A version of a line is a tree that holds what the line holds after it, in
# key spaces: the first word of a key says which. 0: a resource's bytes (none:
# removed). 1: a mark. 2 (in a store's tree): a group's members. 3: a merge's
# clash, open or settled. 4: the version vector, the newest place of each
# other line that the version came from. 5 (in a store's tree): where each of
# its branches starts. 6: the line's owner group. 7 (in a store's tree): the
# names of its groups.

# the words that the store s holds under the hash h
def Store.fetch(s: State(), h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Ledgers.State.data(~Ask, s, h)

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the key of the mark m
def Key.mark(m: String) -> List<&2, U32>:
  1 <> Codes.Code.text(m, [])

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

# the key of where the line of the key k below a store starts
def Key.start(k: List<&2, Bool>) -> List<&2, U32>:
  5 <> Ledgers.Bits.code(k, [])

# the value of a resource whose bytes are m (none: removed)
def Res.code(m: Maybe<&2, Texts.Bytes()>) -> List<&2, U32>:
  Codes.Code.maybe(~Texts.Bytes(), ~Codes.Code.words, m, [])

# the value of a resource, flattened: its bytes, when they are there
def Res.of.read(m: Maybe<&2, Codes.Read<Maybe<&2, Texts.Bytes()>>>) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      x
    case _:
      None{}

# the bytes in the value ws of a resource, when they are there
def Res.read(ws: List<&2, U32>) -> Maybe<&2, Texts.Bytes()>:
  Res.of.read(Codes.Code.maybe.read(~Texts.Bytes(), ~Codes.Code.words.read, ws))

# the value of where a line starts: the root of its first tree
def Start.code(h: Maybe<&2, Hashes.Hash>) -> List<&2, U32>:
  Codes.Code.maybe(~Hashes.Hash, ~Trees.Hash.code, h, [])

# the root in the value of where a line starts, flattened
def Start.of.read(m: Maybe<&2, Codes.Read<Maybe<&2, Hashes.Hash>>>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      x
    case _:
      None{}

# the place of the line c in the value of a version vector's entry
def Place.read(c: Ledgers.Chain, ws: List<&2, U32>) -> Maybe<&2, Ledgers.Where>:
  match ws:
    case Con{e, Con{h, Nil{}}}:
      Some{Ledgers.Where{c, e, h}}
    case _:
      None{}

# the value of a version vector's entry at the place w
def Place.code(w: Ledgers.Where) -> List<&2, U32>:
  match w:
    case Ledgers.Where{c, e, h}:
      [e, h]

# what the tree whose root is h holds under the key k, in the store s
def Node.get(s: State(), h: Maybe<&2, Hashes.Hash>, k: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Trees.Tree.get(~State(), ~Store.fetch, s, h, k)

# the bytes of the resource n in the tree whose root is h
def Res.get(s: State(), h: Maybe<&2, Hashes.Hash>, n: Resources.Name) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, List<&2, U32>, Texts.Bytes(), Node.get(s, h, Key.res(n)), ws => Res.read(ws))

# the vote that took the version v (none: no step took it)
def Vote.taken(x: Ledgers.Vote) -> Maybe<&2, Ledgers.Vote>:
  match x:
    case Ledgers.Vote{i, True{}, w, r}:
      Some{Ledgers.Vote{i, True{}, w, r}}
    case _:
      None{}

# the vote of the version v: the step that took it
def Version.vote(s: State(), v: Ledgers.Id) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Ledgers.Vote,
    Ledgers.Vote,
    Ledgers.State.decided(~Ask, ~Ask.view, s, v),
    x => Vote.taken(x)
  )

# the root of the tree of the version v (none: v is not a version)
def Node.root(s: State(), v: Ledgers.Id) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  Maybe.bind(
    &2,
    Ledgers.Vote,
    Maybe<&2, Hashes.Hash>,
    Version.vote(s, v),
    x => Some{Ledgers.Vote.result_of(Some{x})}
  )

# the root of the tree of the version m, if any (none, or not a version: the
# empty tree)
def Node.root_of(s: State(), m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Node.root(s, v), h => h)

# Lines
# -----

# the steps of the line l of the store r (none: the store's own steps)
def Node.steps(s: State(), r: Ledgers.Id, l: Maybe<&2, String>) -> List<&2, Ledgers.Vote>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Vote>,
    Ledgers.Line.steps(~Ask, ~Ask.view, s, Line.chain(r, l)),
    []
  )

# the requests that the steps xs took, in order: the versions of their line
def Steps.taken(xs: List<&2, Ledgers.Vote>) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{Ledgers.Vote{i, True{}, w, h}, r}:
      i <> Steps.taken(r)
    case Con{x, r}:
      Steps.taken(r)

# the versions of the branch b of the store r, in order
def Node.versions(s: State(), r: Ledgers.Id, b: String) -> List<&2, Ledgers.Id>:
  Steps.taken(Node.steps(s, r, Some{b}))

# the last of xs, if any
def Ids.last(xs: List<&2, Ledgers.Id>) -> Maybe<&2, Ledgers.Id>:
  List.last(&2, Ledgers.Id, xs)

# the newest version of the branch b of the store r, if b has one
def Node.head(s: State(), r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  Ids.last(Node.versions(s, r, b))

# the owners at the tip of the line l of the store r
def Tip.owners(m: Maybe<&2, Ledgers.Tip>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Tip{e, os, n, l}}:
      os
    case None{}:
      []

# the owners at the tip of the line l of the store r
def Node.owners(s: State(), r: Ledgers.Id, l: Maybe<&2, String>) -> List<&2, String>:
  Tip.owners(Ledgers.Line.tip(~Ask, ~Ask.view, s, Line.chain(r, l)))

# the vote of the last step before the tip m of the line c
def Chain.head.of(+s: State(), +c: Ledgers.Chain, m: Maybe<&2, Ledgers.Tip>) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{Ledgers.Tip{e, ms, h, last}}:
      Ledgers.Line.head(~Ask, ~Ask.view, s, c, e, ms, last)
    case None{}:
      None{}

# the head of the line c: the vote of its last step, which a judge of its next
# step reads (none: it has no step yet). It is one key away, not a walk
def Chain.head(+s: State(), +c: Ledgers.Chain) -> Maybe<&2, Ledgers.Vote>:
  Chain.head.of(s, c, Ledgers.Line.tip(~Ask, ~Ask.view, s, c))

# the root of the tree of the store r now
def Store.root(s: State(), r: Ledgers.Id) -> Maybe<&2, Hashes.Hash>:
  Ledgers.Vote.result_of(Chain.head(s, Ledgers.Chain{r, None{}}))

# the value of a read that is the whole of some words
def Read.whole(-A: Data, m: Maybe<&2, Codes.Read<A>>) -> Maybe<&2, A>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      Some{x}
    case _:
      None{}

# where the line of the key k below the store r starts: the root that its make
# gave it in the store's tree (none: the empty tree)
def Line.start(+s: State(), r: Ledgers.Id, k: List<&2, Bool>) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Hashes.Hash,
    Node.get(s, Store.root(s, r), Key.start(k)),
    ws => Start.of.read(Codes.Code.maybe.read(~Hashes.Hash, ~Trees.Hash.code.read, ws))
  )

# where the line c starts: a line below a store where its make put it, a store
# with the empty tree
def Chain.start(s: State(), c: Ledgers.Chain) -> Maybe<&2, Hashes.Hash>:
  match c:
    case Ledgers.Chain{r, None{}}:
      None{}
    case Ledgers.Chain{r, Some{k}}:
      Line.start(s, r, k)

# the tree of the line c before a step whose head is m: the head's result,
# else where the line starts
def Judge.root(s: State(), c: Ledgers.Chain, m: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{x}:
      Ledgers.Vote.result_of(Some{x})
    case None{}:
      Chain.start(s, c)

# the root of the tree of the line c now: what a judge of its next step reads
def Chain.root(+s: State(), +c: Ledgers.Chain) -> Maybe<&2, Hashes.Hash>:
  Judge.root(s, c, Chain.head(s, c))

# the members of the group g in the store tree whose root is h, if g is there
def Members.in(s: State(), h: Maybe<&2, Hashes.Hash>, g: String) -> Maybe<&2, List<&2, Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Member>,
    Node.get(s, h, Key.group(g)),
    ws => Read.whole(List<&2, Member>, Members.code.read(ws))
  )

# Ancestry
# --------
# A version came from the versions before it on its line, by place, and from
# those that its version vector names, at their places or before.

# the place where the version v was decided
def Node.place(s: State(), v: Ledgers.Id) -> Maybe<&2, Ledgers.Where>:
  Ledgers.State.place(~Ask, ~Ask.view, s, v)

# the place a is at or after the place b, of the same line
def Where.covers(a: Ledgers.Where, b: Ledgers.Where) -> Bool:
  match a b:
    case Ledgers.Where{c1, +e1, h1} Ledgers.Where{c2, +e2, h2}:
      Shared.Bool.when(Bool, U32.is_eq(e1, e2), u => U32.is_le(h2, h1), u => U32.is_lt(e2, e1))

# the line of the place w
def Where.chain(w: Ledgers.Where) -> Ledgers.Chain:
  match w:
    case Ledgers.Where{c, e, h}:
      c

# the newest place of the line c that the tree whose root is h came from
def Node.vector(
  s: State(),
  h: Maybe<&2, Hashes.Hash>,
  +c: Ledgers.Chain
) -> Maybe<&2, Ledgers.Where>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ledgers.Where,
    Node.get(s, h, Key.vector(c)),
    ws => Place.read(c, ws)
  )

# the version at the place px, whose tree has the root hx, came from the one at
# the place pv
def Place.from(
  s: State(),
  +px: Ledgers.Where,
  hx: Maybe<&2, Hashes.Hash>,
  +pv: Ledgers.Where
) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Where.chain(px), Where.chain(pv)),
    u => Where.covers(px, pv),
    u => Maybe.default(
      &2,
      Bool,
      Maybe.bind(
        &2,
        Ledgers.Where,
        Bool,
        Node.vector(s, hx, Where.chain(pv)),
        w => Some{Where.covers(w, pv)}
      ),
      False{}
    )
  )

# x is v, or a version that v came from
def Node.has(+s: State(), +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Maybe.default(
      &2,
      Bool,
      Maybe.bind(
        &2,
        Ledgers.Where,
        Bool,
        Node.place(s, x),
        +px => Maybe.bind(
          &2,
          Ledgers.Where,
          Bool,
          Node.place(s, v),
          pv => Maybe.bind(
            &2,
            Ledgers.Vote,
            Bool,
            Version.vote(s, x),
            vx => Some{Place.from(s, px, Ledgers.Vote.result_of(Some{vx}), pv)}
          )
        )
      ),
      False{}
    ),
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

# the work that the new subtree m gives, after the state s and the nodes ns
def Work.of(s: State(), ns: List<&2, List<&2, U32>>, m: Maybe<&2, Trees.Put>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      None{}
    case Some{Trees.Put{h, +ws}}:
      Some{
        Work{
          Ledgers.State.put_datas(~Ask, ~Ask.is_eq, ws, s),
          Some{h},
          List.append(&2, List<&2, U32>, ws, ns)
        }
      }

# w with the key k set to the value x (none: the store lacks a node)
def Work.set(w: Work, k: List<&2, U32>, x: List<&2, U32>) -> Maybe<&2, Work>:
  match w:
    case Work{+s, h, ns}:
      Work.of(s, ns, Trees.Tree.set(~State(), ~Store.fetch, s, h, k, x))

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
def Work.take(m: Maybe<&2, Work>) -> Maybe<&2, Ledgers.Verdict>:
  match m:
    case None{}:
      None{}
    case Some{Work{s, h, ns}}:
      Some{Ledgers.Verdict{True{}, h, ns}}

# w with the line c at the place p in its version vector, unless it holds that
# place or a newer one
def Vector.add(w: Work, +c: Ledgers.Chain, +p: Ledgers.Where) -> Maybe<&2, Work>:
  match w:
    case Work{+s, +h, +ns}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Maybe.default(
          &2,
          Bool,
          Maybe.bind(&2, Ledgers.Where, Bool, Node.vector(s, h, c), q => Some{Where.covers(q, p)}),
          False{}
        ),
        u => Some{Work{s, h, ns}},
        u => Work.set(Work{s, h, ns}, Key.vector(c), Place.code(p))
      )

# the line and place of a version vector's entry, from its binding
def Vector.entry(b: Trees.Binding) -> Maybe<&2, Ledgers.Where>:
  match b:
    case Trees.Binding{Con{4, k}, ws}:
      Maybe.bind(
        &2,
        Ledgers.Chain,
        Ledgers.Where,
        Read.whole(Ledgers.Chain, Ledgers.Chain.code.read(k)),
        c => Place.read(c, ws)
      )
    case _:
      None{}

# w with the entry p in its version vector, when it is of a line other than c
def Vector.add.if(+w: Work, c: Ledgers.Chain, m: Maybe<&2, Ledgers.Where>) -> Maybe<&2, Work>:
  match m:
    case None{}:
      Some{w}
    case Some{+p}:
      Shared.Bool.when(
        Maybe<&2, Work>,
        Ledgers.Chain.is_eq(Where.chain(p), c),
        u => Some{w},
        u => Vector.add(w, Where.chain(p), p)
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

# Submodules
# ----------
# A submodule is a resource whose bytes point to a child (Format.module): the
# space of the child's resources, the store and the branch that it follows,
# and its version, on lines of their own. Never a node: any node that has the
# version can serve it. A merge of two pointers takes the newer one when one
# came from the other (Node.forward).

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

# Content
# -------
# The bytes of a resource at a version, found one resource at a time: a write
# or a resolve of it holds them, a move or a make at a point takes them from
# its target, a merge merges its base, the version before it and the one merged
# in, and every other change keeps the version before it.

# what a merge keeps of a resource: its bytes or none, or a clash
type Pick is Data:
  Pick.Take{bytes: Maybe<&2, Texts.Bytes()>}
  Pick.Clash{}

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.Clean{x}:
      Pick.Take{Some{x}}
    case Formats.Merged.Clash{}:
      Pick.Clash{}

# the merge of the submodules px and py: the one at the newer version m, if any
def Pick.module(m: Maybe<&2, Ledgers.Id>, px: Pointer, +py: Pointer) -> Pick:
  match m:
    case None{}:
      Pick.Clash{}
    case Some{k}:
      Pick.Take{
        Some{
          Pointer.show(
            Shared.Bool.when(Pointer, Ledgers.Id.is_eq(k, Pointer.version(py)), u => py, u => px)
          )
        }
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

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f
def Pick.both(
  f: Formats.Format,
  s: State(),
  b: Maybe<&2, Texts.Bytes()>,
  o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match o t:
    case Some{x} Some{y}:
      Pick.format(f, s, Maybe.default(&2, Texts.Bytes(), b, []), x, y)
    case _ _:
      Pick.Clash{}

# a and b hold the same bytes, or both none
def Bytes.same(a: Maybe<&2, Texts.Bytes()>, b: Maybe<&2, Texts.Bytes()>) -> Bool:
  Shared.Maybe.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base, ours when theirs is the base or both
# agree, else both merged
def Pick.merge(
  f: Formats.Format,
  s: State(),
  +b: Maybe<&2, Texts.Bytes()>,
  +o: Maybe<&2, Texts.Bytes()>,
  +t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  Shared.Bool.when(
    Pick,
    Bytes.same(o, b),
    u => Pick.Take{t},
    u => Shared.Bool.when(
      Pick,
      List.any.if(v => Bytes.same(o, t), Bytes.same(t, b)),
      w => Pick.Take{o},
      w => Pick.both(f, s, b, o, t)
    )
  )

# the bytes of a merge: ours on a clash
def Pick.kept(p: Pick, o: Maybe<&2, Texts.Bytes()>) -> Maybe<&2, Texts.Bytes()>:
  match p:
    case Pick.Take{x}:
      x
    case Pick.Clash{}:
      o

# p is a clash
def Pick.is_clash(p: Pick) -> Bool:
  match p:
    case Pick.Take{x}:
      False{}
    case Pick.Clash{}:
      True{}

# Names
# -----

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
        Maybe.is_some(&2, Texts.Bytes(), Res.read(ws)),
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

# Groups
# ------
# The owner groups of a store are in its own tree, so its own owner group
# decides them, one after the other: a group never comes to contain itself.

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
def Group.named(+g: Groups, gs: List<&2, Member>) -> List<&2, String>:
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

# the members of the group g of the store r, if g exists
def Node.members(+s: State(), r: Ledgers.Id, g: String) -> Maybe<&2, List<&2, Member>>:
  Members.in(s, Store.root(s, r), g)

# the nodes inside the group g of the store r
def Node.nodes(+s: State(), r: Ledgers.Id, g: String) -> List<&2, String>:
  Group.nodes(s, Store.root(s, r), g)

# Judging
# -------
# The owners of a line give each request one verdict, once, at the tip: take
# it, with the tree that the line holds after it, or refuse it as stale. They
# wait while a version it names is not decided yet, or the state lacks a node
# of a tree it reads.

# the verdict that the status st of a version gives a request that names it:
# take it when it is a version, refuse it when it never will be, else wait
def Judge.ready.of(st: Ledgers.Status) -> Maybe<&2, Bool>:
  match st:
    case Ledgers.Status.Done{k}:
      Some{k}
    case Ledgers.Status.Refused{}:
      Some{False{}}
    case _:
      None{}

# the verdict of the version v, for a request that names it
def Judge.ready(s: State(), v: Ledgers.Id) -> Maybe<&2, Bool>:
  Judge.ready.of(Ledgers.State.status(~Ask, ~Ask.view, s, v))

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
    case Content.Bytes{x}:
      Some{True{}}
    case Content.Of{w}:
      Judge.ready(s, w)

# a refusal, which keeps the tree whose root is h
def Judge.refuse(h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Ledgers.Verdict>:
  Some{Ledgers.Verdict{False{}, h, []}}

# the verdict m, then k when m takes; a refusal keeps the tree h
def Judge.then(
  m: Maybe<&2, Bool>,
  h: Maybe<&2, Hashes.Hash>,
  k: Unit -> Maybe<&2, Ledgers.Verdict>
) -> Maybe<&2, Ledgers.Verdict>:
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
  k: Unit -> Maybe<&2, Ledgers.Verdict>
) -> Maybe<&2, Ledgers.Verdict>:
  Shared.Bool.when(Maybe<&2, Ledgers.Verdict>, b, k, u => Judge.refuse(h))

# the bytes that the content c gives the resource n (none: the version holds
# none)
def Content.bytes(+s: State(), n: Resources.Name, c: Content) -> Maybe<&2, Texts.Bytes()>:
  match c:
    case Content.Bytes{x}:
      Some{x}
    case Content.Of{w}:
      Res.get(s, Node.root_of(s, Some{w}), n)

# the verdict on a write of the resource n since base, with the content c, at
# the tree h: take it when n holds at h what it held at base
def Judge.write(
  +s: State(),
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  +c: Content,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Ledgers.Verdict>:
  Judge.then(
    Judge.ready_maybe(s, base),
    h,
    u => Judge.then(
      Judge.content(s, c),
      h,
      w => Judge.when(
        Bytes.same(Res.get(s, h, n), Res.get(s, Node.root_of(s, base), n)),
        h,
        x => Work.take(Work.set(Work{s, h, []}, Key.res(n), Res.code(Content.bytes(s, n, c))))
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
# version m, if any
def Clash.open_by(s: State(), h: Maybe<&2, Hashes.Hash>, n: Resources.Name, m: Maybe<&2, Ledgers.Id>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{f}:
      Clash.open(s, h, n, f)

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
) -> Maybe<&2, Ledgers.Verdict>:
  Judge.then(
    Judge.ready(s, k),
    h,
    u => Judge.then(
      Judge.content(s, c),
      h,
      w => Judge.when(
        Clash.open_by(s, h, n, Merge.from_on(Ledgers.State.asked(~Ask, s, k), r, b)),
        h,
        x => Work.take(
          Maybe.bind(
            &2,
            Work,
            Work,
            Work.set(Work{s, h, []}, Key.res(n), Res.code(Content.bytes(s, n, c))),
            y => Work.set(y, Key.clash(n), [])
          )
        )
      )
    )
  )

# m with the resource n merged: the bytes that the merge of the base b, ours o
# and theirs t (of the version f) keeps, and its clash open when it clashes
def Merge.one(
  s: State(),
  +f: Ledgers.Id,
  +n: Resources.Name,
  b: Maybe<&2, Texts.Bytes()>,
  +o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>,
  w: Work
) -> Maybe<&2, Work>:
  +p = Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t)
  Maybe.bind(
    &2,
    Work,
    Work,
    Work.set(w, Key.res(n), Res.code(Pick.kept(p, o))),
    +y => Shared.Bool.when(
      Maybe<&2, Work>,
      Pick.is_clash(p),
      u => Work.set(y, Key.clash(n), Clash.code(f)),
      u => Some{y}
    )
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
          w => Merge.one(s, f, n, Res.get(s, hb, n), Res.get(s, ho, n), Res.get(s, ht, n), w)
        )
      )

# the request of the vote x
def Vote.id(x: Ledgers.Vote) -> Maybe<&2, Ledgers.Id>:
  match x:
    case Ledgers.Vote{i, k, w, r}:
      Some{i}

# the version at the place w, when a step there took one
def Version.at(+s: State(), w: Ledgers.Where) -> Maybe<&2, Ledgers.Id>:
  match w:
    case Ledgers.Where{+c, +e, h}:
      Maybe.bind(
        &2,
        List<&2, String>,
        Ledgers.Id,
        Ledgers.Line.owners(~Ask, ~Ask.view, s, c, e),
        ms => Maybe.bind(
          &2,
          Ledgers.Vote,
          Ledgers.Id,
          Ledgers.State.decide(~Ask, s, Ledgers.Where{c, e, h}, ms),
          x => Maybe.bind(&2, Ledgers.Vote, Ledgers.Id, Vote.taken(x), y => Vote.id(y))
        )
      )

# the base of a merge of from into the line c: from itself when it is of c,
# else the version of c at the place that from's version vector gives c
def Merge.base(+s: State(), +c: Ledgers.Chain, +from: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(
    &2,
    Ledgers.Where,
    Ledgers.Id,
    Node.place(s, from),
    pf => Shared.Bool.when(
      Maybe<&2, Ledgers.Id>,
      Ledgers.Chain.is_eq(Where.chain(pf), c),
      u => Some{from},
      u => Maybe.bind(
        &2,
        Ledgers.Where,
        Ledgers.Id,
        Node.vector(s, Node.root_of(s, Some{from}), c),
        w => Version.at(s, w)
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
      Node.root_of(s, Merge.base(s, c, from)),
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

# the trees of a make of the line of the key k, from its first tree start, in
# the tree h of its store: the store's tree holds where the line starts
def Make.work(
  start: Maybe<&2, Work>,
  k: List<&2, Bool>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Work>:
  Maybe.bind(
    &2,
    Work,
    Work,
    start,
    +w => Work.set(Work.at(w, h), Key.start(k), Start.code(Work.root(w)))
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

# the root of the tree of the step v, taken or not (none: the empty tree, or v
# is not decided here)
def Step.root(s: State(), v: Ledgers.Id) -> Maybe<&2, Hashes.Hash>:
  Ledgers.Vote.result_of(Ledgers.State.decided(~Ask, ~Ask.view, s, v))

# the store tree in which an Own of the line l, at the tree h, reads its group:
# a store reads its own tree; a branch, the tree of the step at of its store
def Own.tree(
  s: State(),
  l: Maybe<&2, String>,
  at: Maybe<&2, Ledgers.Id>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Hashes.Hash>:
  match l at:
    case Some{b} Some{v}:
      Step.root(s, v)
    case x y:
      h

# the owners os are the nodes inside the group g of the store tree t, and there
# is one
def Own.fits(s: State(), t: Maybe<&2, Hashes.Hash>, g: String, +os: List<&2, String>) -> Bool:
  List.all.if(
    u => Ledgers.Owners.is_eq(os, Group.nodes(s, t, g)),
    Bool.not(List.is_empty(&2, String, os))
  )

# the verdict on an Own of the group g, with the owners os, at the tree h, when
# it fits: the line's owner group is g
def Own.take(+s: State(), +g: String, fits: Bool, +h: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Ledgers.Verdict>:
  Judge.when(
    fits,
    h,
    u => Work.take(Work.set(Work{s, h, []}, Key.owner(), Codes.Code.text(g, [])))
  )

# the step at is a step of the store r: decided at the place m
def Own.at(r: Ledgers.Id, m: Maybe<&2, Ledgers.Where>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      None{}
    case Some{Ledgers.Where{c, e, h}}:
      Some{Ledgers.Chain.is_eq(c, Ledgers.Chain{r, None{}})}

# the verdict on an Own of the line l of the store r: its owner group is g,
# whose nodes in the tree that it names (Own.tree) are os
def Own.change(
  +s: State(),
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  +g: String,
  at: Maybe<&2, Ledgers.Id>,
  +os: List<&2, String>,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Ledgers.Verdict>:
  match l at:
    case None{} y:
      Own.take(s, g, Own.fits(s, h, g, os), h)
    case Some{b} None{}:
      Judge.refuse(h)
    case Some{b} Some{+v}:
      Judge.then(
        Own.at(r, Node.place(s, v)),
        h,
        u => Own.take(s, g, Own.fits(s, Step.root(s, v), g, os), h)
      )

# the verdict on the change c of the line l of the store r, at the tree h
def Judge.change(
  +s: State(),
  r: Ledgers.Id,
  l: Maybe<&2, String>,
  c: Change,
  +h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Ledgers.Verdict>:
  match l c:
    case None{} Change.Branch{+b, +at}:
      Judge.then(
        Judge.ready_maybe(s, at),
        h,
        u => Work.take(Make.work(Make.branch(s, Line.chain(r, Some{b}), at), Line.key(b), h))
      )
    case None{} Change.Group{+g, +ms}:
      Judge.when(Bool.not(Group.loops.any(s, h, g, ms)), h, u => Work.take(Group.work(s, h, g, ms)))
    case w Change.Own{g, at, os}:
      Own.change(s, r, w, g, at, os, h)
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
    case Some{b} Change.Mark{+m, t}:
      Judge.when(
        Maybe.is_none(&2, List<&2, U32>, Node.get(s, h, Key.mark(m))),
        h,
        u => Work.take(Work.set(Work{s, h, []}, Key.mark(m), []))
      )
    case w c3:
      Judge.refuse(h)

# the verdict of the owners on a change c of the line l of the store r, after
# the step head of the line
def Node.judge.on(
  +s: State(),
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  c: Change,
  head: Maybe<&2, Ledgers.Vote>
) -> Maybe<&2, Ledgers.Verdict>:
  Judge.change(s, r, l, c, Judge.root(s, Line.chain(r, l), head))

# the verdict of the owners on q, after the step head of its line (none: wait)
def Node.judge(s: State(), q: Ask, head: Maybe<&2, Ledgers.Vote>) -> Maybe<&2, Ledgers.Verdict>:
  match q:
    case Ask.Start{os}:
      Some{Ledgers.Verdict{True{}, None{}, []}}
    case Ask.On{r, l, c}:
      Node.judge.on(s, r, l, c, head)

# Changes
# -------

# s with the facts of the last step of the line that q changes
def Node.land(s: State(), q: Ask) -> State():
  match q:
    case Ask.Start{os}:
      s
    case Ask.On{r, l, c}:
      Ledgers.State.land(~Ask, ~Ask.is_eq, ~Ask.view, s, Line.chain(r, l))

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
      Ledgers.State.ask(
        ~Ask,
        ~Ask.is_eq,
        ~Ask.view,
        ~Node.judge,
        n,
        Node.land(s, q),
        Envelope.of(e),
        Envelope.time(e),
        q
      )

# s, after the node n took in the request q of e, and voted on it when it owns
# its line. A request ID that s holds counts once: asked again, it changes
# nothing
def Node.ask(n: String, +s: State(), +e: Envelope, q: Ask) -> State():
  Node.ask.at(n, s, e, q, Ledgers.State.get(~Ask, s, Ledgers.Slot.ask(Envelope.of(e))))

# s, after the node n voted, at the tip of each line that it owns, for each
# request that s holds
def Node.vote(n: String, s: State()) -> State():
  Ledgers.State.vote(~Ask, ~Ask.is_eq, ~Ask.view, ~Node.judge, n, s)

# s, after the node n took in t, which another node sent, and voted on what it
# holds now: how a node that is behind catches up
def Node.sync(n: String, s: State(), t: State()) -> State():
  Node.vote(n, Node.take(s, t))

# Owners
# ------
# A line names its owner group, and its owners are the nodes inside it. When
# the group changes, an owner asks for the line's owners to be the group's
# nodes again (Node.adopt), and the owners that the line has decide it: so a
# change of a group changes the owners of everything that it owns.

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

# the last step of the store r
def Store.head(s: State(), r: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Maybe.bind(&2, Ledgers.Vote, Ledgers.Id, Chain.head(s, Ledgers.Chain{r, None{}}), x => Vote.id(x))

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

# Reads
# -----

# whether the step (taken or not: k) whose request is a names the mark m (none:
# a taken step whose request the node does not hold yet)
def Mark.at(k: Bool, a: Maybe<&2, Ledgers.Asked<Ask>>, m: String) -> Maybe<&2, Bool>:
  match k a:
    case False{} w:
      Some{False{}}
    case True{} None{}:
      None{}
    case True{} Some{Ledgers.Asked{t, Ask.On{st, l, Change.Mark{x, d}}}}:
      Some{String.eq(x, m)}
    case True{} Some{b}:
      Some{False{}}

# prev when the step names the mark (x), else rest; none while x is not known
def Mark.pick(
  x: Maybe<&2, Bool>,
  prev: Maybe<&2, Ledgers.Id>,
  rest: Unit -> Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Ledgers.Id>:
  match x:
    case None{}:
      None{}
    case Some{True{}}:
      prev
    case Some{False{}}:
      rest(Unit{})

# the version that the first mark m of the steps xs names: the version before
# it, after prev. It reads only steps whose requests the node holds, so a mark
# that it finds is the mark for good (Node.mark_kept)
def Mark.first(
  +s: State(),
  xs: List<&2, Ledgers.Vote>,
  +prev: Maybe<&2, Ledgers.Id>,
  +m: String
) -> Maybe<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{Ledgers.Vote{+i, +k, w, h}, r}:
      Mark.pick(
        Mark.at(k, Ledgers.State.asked(~Ask, s, i), m),
        prev,
        u => Mark.first(
          s,
          r,
          Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, v => Some{i}, v => prev),
          m
        )
      )

# the request i is a version: a step took it
def Node.is_version(s: State(), i: Ledgers.Id) -> Bool:
  Shared.Maybe.is_eq(
    ~Bool,
    ~Shared.Bool.is_eq,
    Ledgers.Status.verdict(Ledgers.State.status(~Ask, ~Ask.view, s, i)),
    Some{True{}}
  )

# the version at the point p, if there is one
def Node.version(+s: State(), p: Point) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Point.At{+v}:
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.is_version(s, v), u => Some{v}, u => None{})
    case Point.Head{r, b}:
      Node.head(s, r, b)
    case Point.Mark{r, b, m}:
      Mark.first(s, Node.steps(s, r, Some{b}), None{}, m)

# the bytes of the resource n at the version m, if it holds them
def Res.at(+s: State(), n: Resources.Name, m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, Ledgers.Id, Texts.Bytes(), m, v => Res.get(s, Node.root_of(s, Some{v}), n))

# the bytes of the resource n at the point p, if it is there
def Node.content(+s: State(), n: Resources.Name, p: Point) -> Maybe<&2, Texts.Bytes()>:
  Res.at(s, n, Node.version(s, p))

# Views
# -----
# What a writer reads shows its own changes before their owners decide them:
# at the head of a branch, a resource reads as the writer's pending write of
# it with the highest request ID, if it has one.

# the content that the request q gives the resource n on the branch b of the
# store r, when it writes it there
def Draft.content(r: Ledgers.Id, b: String, n: Resources.Name, q: Ask) -> Maybe<&2, Content>:
  match q:
    case Ask.On{st, Some{x}, Change.Write{m, base, c}}:
      Shared.Maybe.when(
        Content,
        List.all.if(
          u => List.all.if(v => Resources.Name.is_eq(m, n), String.eq(x, b)),
          Ledgers.Id.is_eq(st, r)
        ),
        u => Some{c}
      )
    case Ask.On{st, Some{x}, Change.Resolve{k, m, c}}:
      Shared.Maybe.when(
        Content,
        List.all.if(
          u => List.all.if(v => Resources.Name.is_eq(m, n), String.eq(x, b)),
          Ledgers.Id.is_eq(st, r)
        ),
        u => Some{c}
      )
    case _:
      None{}

# st is pending
def Status.is_pending(st: Ledgers.Status) -> Bool:
  match st:
    case Ledgers.Status.Pending{}:
      True{}
    case _:
      False{}

# the content m of the request i, when it is a pending write, else found
def Draft.put(
  s: State(),
  i: Ledgers.Id,
  m: Maybe<&2, Content>,
  found: Maybe<&2, Content>
) -> Maybe<&2, Content>:
  match m:
    case None{}:
      found
    case Some{c}:
      Shared.Bool.when(
        Maybe<&2, Content>,
        Status.is_pending(Ledgers.State.status(~Ask, ~Ask.view, s, i)),
        u => Some{c},
        u => found
      )

# the content of the last pending write of the resource n on the branch b of
# the store r among the cells cs, else found
def Draft.last(
  +s: State(),
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>,
  found: Maybe<&2, Content>
) -> Maybe<&2, Content>:
  match cs:
    case Nil{}:
      found
    case Con{Cells.One{Ledgers.Entry.Ask{i, t, q}}, rest}:
      Draft.last(s, r, b, n, rest, Draft.put(s, i, Draft.content(r, b, n, q), found))
    case Con{c, rest}:
      Draft.last(s, r, b, n, rest, found)

# the requests of the writer w that s holds, in the order of their IDs
def Writer.asks(s: State(), w: String) -> List<&2, Cells.Cell<Ledgers.Entry<Ask>>>:
  Tries.Trie.values(
    Cells.Cell<Ledgers.Entry<Ask>>,
    Ledgers.State.under(~Ask, s, Ledgers.Slot.writer(w))
  )

# the requests of the writer w whose IDs come after q, as s holds them
def Writer.after(s: State(), w: String, q: String) -> List<&2, Cells.Cell<Ledgers.Entry<Ask>>>:
  Tries.Trie.after(
    Cells.Cell<Ledgers.Entry<Ask>>,
    Ledgers.State.under(~Ask, s, Ledgers.Slot.writer(w)),
    Tries.Trie.text(q)
  )

# the content of the writer w's pending write of the resource n on the branch
# b of the store r with the highest request ID, if it has one
def Node.draft(
  +s: State(),
  w: String,
  r: Ledgers.Id,
  b: String,
  n: Resources.Name
) -> Maybe<&2, Content>:
  Draft.last(s, r, b, n, Writer.asks(s, w), None{})

# the bytes of the draft m of the resource n, else what the point p holds
def Read.of(+s: State(), n: Resources.Name, m: Maybe<&2, Content>, p: Point) -> Maybe<&2, Texts.Bytes()>:
  match m:
    case Some{c}:
      Content.bytes(s, n, c)
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
        Bool.not(Bytes.same(Res.at(s, n, Some{x}), Res.at(s, n, prev))),
        x,
        Ledgers.State.asked(~Ask, s, x),
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

# Conflicts
# ---------

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
  Merge.left(s, k, Ledgers.State.asked(~Ask, s, k))

# Answers
# -------

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

# the answer to the change q of the request i, whose status is st
def Answer.of(s: State(), i: Ledgers.Id, q: Ask, st: Ledgers.Status) -> Answer:
  match st:
    case Ledgers.Status.Done{True{}}:
      Answer.taken(s, i, q)
    case Ledgers.Status.Done{False{}}:
      Answer.Stale{}
    case Ledgers.Status.Pending{}:
      Answer.Pending{}
    case _:
      Answer.Refused{}

# the answer to the change q of the request i, whose slot holds m: none when it
# is empty, Refused when it holds another change
def Answer.held(
  +s: State(),
  +i: Ledgers.Id,
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
          u => Answer.of(
            s,
            i,
            q2,
            Ledgers.Status.of.view(Ask.view(q2), Ledgers.State.decided(~Ask, ~Ask.view, s, i))
          ),
          u => Answer.Refused{}
        )
      }
    case Some{c}:
      Some{Answer.Refused{}}

# what the node answers to the change q of e (none: it did not take it in)
def Node.answer(+s: State(), e: Envelope, q: Ask) -> Maybe<&2, Answer>:
  +i = Envelope.of(e)
  Answer.held(s, i, q, Ledgers.State.get(~Ask, s, Ledgers.Slot.ask(i)))

# b may come after the answer a as the state grows: a request that a node took
# in stays; Stale and Refused are final; a taken change stays taken
def Answer.follows(a: Answer, m: Maybe<&2, Answer>) -> Bool:
  match a m:
    case Answer.Pending{} Some{b}:
      True{}
    case Answer.Written{v} Some{Answer.Written{w}}:
      True{}
    case Answer.Written{v} Some{Answer.Conflicted{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Written{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Conflicted{w}}:
      True{}
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

# the stores among the facts cs of where lines were made: the root line of
# the step that made each
def Store.roots(cs: List<&2, Cells.Cell<Ledgers.Entry<Ask>>>) -> List<&2, Ledgers.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Cells.One{Ledgers.Entry.At{Ledgers.Where{Ledgers.Chain{r, None{}}, e, h}}}, rest}:
      r <> Store.roots(rest)
    case Con{c, rest}:
      Store.roots(rest)

# the branch that the request m makes, when it makes one, then rest
def Branch.made.of(m: Maybe<&2, Ledgers.Asked<Ask>>, rest: List<&2, String>) -> List<&2, String>:
  match m:
    case Some{Ledgers.Asked{t, Ask.On{st, None{}, Change.Branch{b, at}}}}:
      b <> rest
    case _:
      rest

# the branches that the steps xs of a store make
def Branch.made(+s: State(), xs: List<&2, Ledgers.Vote>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{Ledgers.Vote{i, True{}, w, h}, r}:
      Branch.made.of(Ledgers.State.asked(~Ask, s, i), Branch.made(s, r))
    case Con{x, r}:
      Branch.made(s, r)

# the branch b of the store r, at its head m, then rest
def Branch.at(
  +r: Ledgers.Id,
  +b: String,
  s: State(),
  m: Maybe<&2, Ledgers.Id>,
  rest: List<&2, BranchEntry>
) -> List<&2, BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{h}:
      BranchEntry{Branch{r, b}, Node.owners(s, r, Some{b}), h} <> rest

# the branches of the names bs of the store r
def Branch.of(+s: State(), +r: Ledgers.Id, bs: List<&2, String>) -> List<&2, BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      Branch.at(r, b, s, Node.head(s, r, b), Branch.of(s, r, rest))

# the branches of the stores rs
def Branch.all(+s: State(), rs: List<&2, Ledgers.Id>) -> List<&2, BranchEntry>:
  match rs:
    case Nil{}:
      []
    case Con{+r, rest}:
      List.append(
        &2,
        BranchEntry,
        Branch.of(s, r, Branch.made(s, Node.steps(s, r, None{}))),
        Branch.all(s, rest)
      )

# the stores of s that made a line: a store's branches and groups are its
# lines, and each line's start is a fact under one prefix, so this costs the
# lines, not the whole state
def Node.stores(+s: State()) -> List<&2, Ledgers.Id>:
  Tries.Trie.unique(
    ~Ledgers.Id,
    ~Ledgers.Id.key,
    Store.roots(Tries.Trie.values(Cells.Cell<Ledgers.Entry<Ask>>, Ledgers.State.under(~Ask, s, Ledgers.Slot.lines()))),
    Tries.Trie.new(Unit)
  )

# every branch
def Node.branches(+s: State()) -> List<&2, BranchEntry>:
  Branch.all(s, Node.stores(s))

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

# Uses
# ----

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

# Touches
# -------

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
  Wrote.of(Ledgers.State.asked(~Ask, s, v))

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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it runs only after the branch is known, so the head is there and both sides are needed
# the branch b lacks the version v
def Touch.lacks(+s: State(), +b: Branch, +v: Ledgers.Id) -> Bool:
  Bool.and(
    Maybe.is_some(&2, Ledgers.Id, Branch.head(s, b)),
    Bool.not(Node.has(s, Maybe.default(&2, Ledgers.Id, Branch.head(s, b), v), v))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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

# Notices
# -------

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
        Bool.not(List.is_empty(&2, Resources.Name, Merge.clashes(s, x, Ledgers.State.asked(~Ask, s, x))))
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

# The node
# --------

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

# Laws
# ----
# What README says of a Vend Node's core, as laws. A law of the ledger that
# asks for the laws of a change's equality holds of a node's state by
# Ask.same.

# two requests are the same exactly when they are equal
law Ask.same:
  Shared.Eq.Laws(Ask, Ask.is_eq)

# a node that takes in a request only grows its state: nothing that it held is
# lost or changed. So do its votes (Ledgers.State.vote_grows) and whatever it
# takes from another node (Ledgers.State.take_grows)
law Node.ask_grows:
  for +n: String
  for +s: State()
  for +e: Envelope
  for +q: Ask
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, Node.ask(n, s, e, q)) == True{}: Bool}

# a sync only grows a node's state: catching up loses and changes nothing
# that the node holds, whatever the other node sent
law Node.sync_grows:
  for +n: String
  for +s: State()
  for +t: State()
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, Node.sync(n, s, t)) == True{}: Bool}

# a change counts once, however often and wherever it is sent: a node that
# took a request in changes nothing when any node sends its ID again
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

# a node answers every change that it took in
law Node.ask_seen:
  for +n: String
  for +s: State()
  for +e: Envelope
  for +q: Ask
  {Maybe.is_some(&2, Answer, Node.answer(Node.ask(n, s, e, q), e, q)) == True{}: Bool}

# an answer only moves forward as the state grows: a change that the node took
# in stays; Stale and Refused are final; a taken change stays taken
law Node.answer_kept:
  for +s: State()
  for +s2: State()
  for +e: Envelope
  for +q: Ask
  for +a: Answer
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, s2) == True{}: Bool}
    -> {Node.answer(s, e, q) == Some{a}: Maybe<&2, Answer>}
    -> {Answer.follows(a, Node.answer(s2, e, q)) == True{}: Bool}

# the owners of a line are the nodes inside its owner group: its owners take
# an Own only when its owners are the nodes inside its group, in the store
# tree that it names (Own.tree)
law Judge.own_inside:
  for +s: State()
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +g: String
  for +at: Maybe<&2, Ledgers.Id>
  for +os: List<&2, String>
  for +h: Maybe<&2, Hashes.Hash>
  for +x: Maybe<&2, Hashes.Hash>
  for +ds: List<&2, List<&2, U32>>
  {
    Judge.change(
      s,
      r,
      l,
      Change.Own{g, at, os},
      h
    )
      == Some{Ledgers.Verdict{True{}, x, ds}}: Maybe<&2, Ledgers.Verdict>
  }
    -> {os == Group.nodes(s, Own.tree(s, l, at, h), g): List<&2, String>}

# every read of a writer shows its own pending change. When a node holds the
# writer w's request q, which writes the content c to the resource n on the
# branch b of the store r, its owners did not decide it yet, and w has no
# pending write of n there under a higher ID, c is w's draft of n: what
# Node.read gives at the head of b. A node that the writer switches to holds
# the request once a sync brought it, and keeps it (Node.answer_kept)
law Node.draft_own:
  for +s: State()
  for +w: String
  for +q: String
  for +t: String
  for +a: Ask
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +c: Content
  {
    Ledgers.State.get(
      ~Ask,
      s,
      Ledgers.Slot.ask(Ledgers.Id{w, q})
    )
      == Some{Cells.One{Ledgers.Entry.Ask{Ledgers.Id{w, q}, t, a}}}: Maybe<
      &2,
      Cells.Cell<Ledgers.Entry<Ask>>>
  }
    -> {Draft.content(r, b, n, a) == Some{c}: Maybe<&2, Content>}
    -> {
      Ledgers.State.status(~Ask, ~Ask.view, s, Ledgers.Id{w, q}) == Ledgers.Status.Pending{}: Ledgers.Status
    }
    -> {Draft.last(s, r, b, n, Writer.after(s, w, q), None{}) == None{}: Maybe<&2, Content>}
    -> {Node.draft(s, w, r, b, n) == Some{c}: Maybe<&2, Content>}

# s with the request q of e, before any vote: what a node holds once it takes
# q in
def Node.taken(s: State(), +e: Envelope, +q: Ask) -> State():
  Ledgers.State.put(
    ~Ask,
    ~Ask.is_eq,
    Node.land(s, q),
    Ledgers.Slot.ask(Envelope.of(e)),
    Ledgers.Entry.Ask{Envelope.of(e), Envelope.time(e), q}
  )

# the premises of Node.write_written, then C. t is what the node n holds once
# it took in the write i of the resource name, with the bytes x since base, on
# the line c. n is the sole owner of the tip of c, has not voted there, and no
# fact says where i was decided; the base is a version, and the resource did
# not change since it; t holds the tree of the head of c (the write's new
# subtree is p) and no other words under the hashes of the new nodes
def Write.Sole(
  n: String,
  t: State(),
  i: Ledgers.Id,
  c: Ledgers.Chain,
  name: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Texts.Bytes(),
  ep: U32,
  h: U32,
  last: Maybe<&2, Ledgers.Where>,
  p: Trees.Put,
  C: Type
) -> Type:
  {
    Ledgers.Line.tip(~Ask, ~Ask.view, t, c) == Some{Ledgers.Tip{ep, [n], h, last}}: Maybe<&2, Ledgers.Tip>
  }
  -> {Ledgers.Line.owners(~Ask, ~Ask.view, t, c, ep) == Some{[n]}: Maybe<&2, List<&2, String>>}
  -> {
    Ledgers.State.get(
      ~Ask,
      t,
      Ledgers.Slot.vote(Ledgers.Where{c, ep, h}, n)
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
  }
  -> {
    Ledgers.State.get(~Ask, t, Ledgers.Slot.where(i)) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
  }
  -> {Judge.ready_maybe(t, base) == Some{True{}}: Maybe<&2, Bool>}
  -> {
    Bytes.same(
      Res.get(
        t,
        Judge.root(t, c, Ledgers.Line.head(~Ask, ~Ask.view, t, c, ep, [n], last)),
        name
      ),
      Res.get(t, Node.root_of(t, base), name)
    )
      == True{}: Bool
  }
  -> {
    Trees.Tree.set(
      ~State(),
      ~Store.fetch,
      t,
      Judge.root(t, c, Ledgers.Line.head(~Ask, ~Ask.view, t, c, ep, [n], last)),
      Key.res(name),
      Res.code(Some{x})
    )
      == Some{p}: Maybe<&2, Trees.Put>
  }
  -> {
    Ledgers.Data.fresh(
      ~Ask,
      ~Ask.is_eq,
      List.append(&2, List<&2, U32>, Trees.Put.nodes(p), []),
      t
    )
      == True{}: Bool
  }
  -> C

# the sole owner of the tip of a branch takes in a new write of a resource
# that did not change since its base (Write.Sole): the write is Written, and
# its version holds the bytes
law Node.write_written:
  for +n: String
  for +s: State()
  for +e: Envelope
  for +r: Ledgers.Id
  for +b: String
  for +name: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +x: Texts.Bytes()
  for +ep: U32
  for +h: U32
  for +last: Maybe<&2, Ledgers.Where>
  for +p: Trees.Put
  {
    Ledgers.State.get(
      ~Ask,
      Node.land(s, Ask.On{r, Some{b}, Change.Write{name, base, Content.Bytes{x}}}),
      Ledgers.Slot.ask(Envelope.of(e))
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Ask>>>
  }
    -> Write.Sole(
      n,
      Node.taken(s, e, Ask.On{r, Some{b}, Change.Write{name, base, Content.Bytes{x}}}),
      Envelope.of(e),
      Line.chain(r, Some{b}),
      name,
      base,
      x,
      ep,
      h,
      last,
      p,
      {
        Node.answer(
          Node.ask(
            n,
            s,
            e,
            Ask.On{r, Some{b}, Change.Write{name, base, Content.Bytes{x}}}
          ),
          e,
          Ask.On{r, Some{b}, Change.Write{name, base, Content.Bytes{x}}}
        )
          == Some{Answer.Written{Envelope.of(e)}}: Maybe<&2, Answer>
      }
        & {
          Node.content(
            Node.ask(
              n,
              s,
              e,
              Ask.On{r, Some{b}, Change.Write{name, base, Content.Bytes{x}}}
            ),
            name,
            Point.At{Envelope.of(e)}
          )
            == Some{x}: Maybe<&2, Texts.Bytes()>
        }
    )

# the content of a resource at a version stays as the node's state grows (by
# a sync that agrees, or by its own writes): a version never changes
law Node.content_kept:
  for +s: State()
  for +s2: State()
  for +n: Resources.Name
  for +v: Ledgers.Id
  for +x: Texts.Bytes()
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, s2) == True{}: Bool}
    -> {Node.content(s, n, Point.At{v}) == Some{x}: Maybe<&2, Texts.Bytes()>}
    -> {Node.content(s2, n, Point.At{v}) == Some{x}: Maybe<&2, Texts.Bytes()>}

# a version stays a version as the state grows: a step that took a request
# is final
law Node.version_kept:
  for +s: State()
  for +s2: State()
  for +v: Ledgers.Id
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, s2) == True{}: Bool}
    -> {Node.is_version(s, v) == True{}: Bool}
    -> {Node.is_version(s2, v) == True{}: Bool}

# a mark names its version for good: the version that a mark names stays as
# the state grows
law Node.mark_kept:
  for +s: State()
  for +s2: State()
  for +r: Ledgers.Id
  for +b: String
  for +m: String
  for +v: Ledgers.Id
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, s2) == True{}: Bool}
    -> {Node.version(s, Point.Mark{r, b, m}) == Some{v}: Maybe<&2, Ledgers.Id>}
    -> {Node.version(s2, Point.Mark{r, b, m}) == Some{v}: Maybe<&2, Ledgers.Id>}

# the versions of a branch only grow at their end as the state grows: its
# history is never rewritten
law Node.versions_grow:
  for +s: State()
  for +s2: State()
  for +r: Ledgers.Id
  for +b: String
  {Ledgers.State.grows(~Ask, ~Ask.is_eq, s, s2) == True{}: Bool}
    -> {
      List.take(
        &2,
        Ledgers.Id,
        Node.versions(s2, r, b),
        List.length(&2, Ledgers.Id, Node.versions(s, r, b))
      )
        == Node.versions(s, r, b): List<&2, Ledgers.Id>
    }
