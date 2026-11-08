import Base
import ../../shared/bytes.bend as Octets
import ../../shared/cells.bend as Cells
import ../../shared/formats.bend as Formats
import ../../shared/lists.bend as Lists
import ../../shared/maybes.bend as Maybes
import ../../shared/resources.bend as Resources
import ../../shared/tries.bend as Tries

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API).
#
# A node holds entries in slots. Two nodes sync by joining what they hold, so
# every node that took in the same entries holds the same state, in any order
# and any number of times (Tries.Trie.union_comm, union_assoc, union_idem, with
# the laws of Cells.Cell.join). Every answer is read from the state alone.
#
# A chain (a branch, or an owner group) is a list of versions. Its first
# version is the request that a root entry names; each next one is the
# request that most of the chain's owners vote for, after the version before
# it. A slot with two different entries holds Many: the request, the vote or
# the root in it counts for nothing.

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts.

# a request: the writer that made it and the ID that the writer gave it. A
# version is the request that made it.
type Id is Data:
  Id{writer: String, request: String}

# what has versions and owners: a branch, or an owner group
type Chain is Data:
  Chain.Branch{name: String}
  Chain.Group{name: String}

# a member of an owner group: a node, or another group
type Member is Data:
  Member.Node{name: String}
  Member.Group{name: String}

# new content: bytes, or what an old version held
type Content is Data:
  Content.Bytes{bytes: Octets.Bytes()}
  Content.Of{version: Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Id}
  Point.Head{branch: String}
  Point.Mark{branch: String, mark: String}

# Requests
# --------
# A request is data alone: a point becomes a version before it is asked for,
# so that a request sent again, to any node, is the same request.

# a change that a writer asks for
type Ask is Data:
  Ask.Write{branch: String, name: Resources.Name, base: Maybe<&2, Id>, content: Content}
  Ask.SetBranch{branch: String, to: Id}
  Ask.Merge{branch: String, from: Id}
  Ask.Resolve{branch: String, conflict: Id, name: Resources.Name, content: Content}
  Ask.Mark{branch: String, mark: String, message: String}
  Ask.SetOwner{chain: Chain, members: List<&2, String>}
  Ask.SetGroup{group: String, members: List<&2, Member>}

# the chain that q changes
def Ask.chain(q: Ask) -> Chain:
  match q:
    case Ask.Write{b, n, base, c}:
      Chain.Branch{b}
    case Ask.SetBranch{b, v}:
      Chain.Branch{b}
    case Ask.Merge{b, v}:
      Chain.Branch{b}
    case Ask.Resolve{b, k, n, c}:
      Chain.Branch{b}
    case Ask.Mark{b, m, t}:
      Chain.Branch{b}
    case Ask.SetOwner{c, ms}:
      c
    case Ask.SetGroup{g, ms}:
      Chain.Group{g}

# who asks for a change, and when
type Envelope is Data:
  Envelope{id: String, writer: String, time: String}

# the request of e
def Envelope.of(e: Envelope) -> Id:
  match e:
    case Envelope{r, w, t}:
      Id{w, r}

# Entries
# -------

# a request, with its time; a vote of a node for a version; or a node's claim
# of the first version of a chain, which that node owns then
type Entry is Data:
  Entry.Ask{id: Id, time: String, ask: Ask}
  Entry.Vote{choice: Id}
  Entry.Root{chain: Chain, first: Id, owner: String}

# where an entry is: a request by its ID, a vote by its node and the version
# that it follows, a root by its chain and the node that claims it
type Slot is Data:
  Slot.Ask{id: Id}
  Slot.Vote{node: String, chain: Chain, after: Id}
  Slot.Root{chain: Chain, owner: String}

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Tries.Trie.text(w), Tries.Trie.text(r))

# the key of c
def Chain.key(c: Chain) -> List<&2, Bool>:
  match c:
    case Chain.Branch{n}:
      False{} <> Tries.Trie.text(n)
    case Chain.Group{n}:
      True{} <> Tries.Trie.text(n)

# the start of the keys of the roots of c
def Root.key(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> Chain.key(c)

# the key of k: no two slots share one
def Slot.key(k: Slot) -> List<&2, Bool>:
  match k:
    case Slot.Ask{i}:
      False{} <> Id.key(i)
    case Slot.Vote{n, c, i}:
      True{} <> False{} <> List.append(&2, Bool, Tries.Trie.text(n), List.append(&2, Bool, Chain.key(c), Id.key(i)))
    case Slot.Root{c, n}:
      List.append(&2, Bool, Root.key(c), Tries.Trie.text(n))

# Equality
# --------

# a and b are the same request
def Id.same(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same chain
def Chain.same(a: Chain, b: Chain) -> Bool:
  match a b:
    case Chain.Branch{x} Chain.Branch{y}:
      String.eq(x, y)
    case Chain.Group{x} Chain.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# a and b are the same member
def Member.same(a: Member, b: Member) -> Bool:
  match a b:
    case Member.Node{x} Member.Node{y}:
      String.eq(x, y)
    case Member.Group{x} Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# a and b are the same content
def Content.same(a: Content, b: Content) -> Bool:
  match a b:
    case Content.Bytes{x} Content.Bytes{y}:
      Octets.Bytes.is_eq(x, y)
    case Content.Of{x} Content.Of{y}:
      Id.same(x, y)
    case _ _:
      False{}

# a and b are the same resource
def Name.same(a: Resources.Name, b: Resources.Name) -> Bool:
  String.eq(Resources.Name.show(a), Resources.Name.show(b))

# a and b are the same change
def Ask.same(a: Ask, b: Ask) -> Bool:
  match a b:
    case Ask.Write{b1, n1, v1, c1} Ask.Write{b2, n2, v2, c2}:
      Bool.and(
        String.eq(b1, b2),
        Bool.and(Name.same(n1, n2), Bool.and(Maybes.Maybe.same(~Id, ~Id.same, v1, v2), Content.same(c1, c2)))
      )
    case Ask.SetBranch{b1, v1} Ask.SetBranch{b2, v2}:
      Bool.and(String.eq(b1, b2), Id.same(v1, v2))
    case Ask.Merge{b1, v1} Ask.Merge{b2, v2}:
      Bool.and(String.eq(b1, b2), Id.same(v1, v2))
    case Ask.Resolve{b1, k1, n1, c1} Ask.Resolve{b2, k2, n2, c2}:
      Bool.and(String.eq(b1, b2), Bool.and(Id.same(k1, k2), Bool.and(Name.same(n1, n2), Content.same(c1, c2))))
    case Ask.Mark{b1, m1, t1} Ask.Mark{b2, m2, t2}:
      Bool.and(String.eq(b1, b2), Bool.and(String.eq(m1, m2), String.eq(t1, t2)))
    case Ask.SetOwner{c1, ms1} Ask.SetOwner{c2, ms2}:
      Bool.and(Chain.same(c1, c2), Lists.List.same(~String, ~String.eq, ms1, ms2))
    case Ask.SetGroup{g1, ms1} Ask.SetGroup{g2, ms2}:
      Bool.and(String.eq(g1, g2), Lists.List.same(~Member, ~Member.same, ms1, ms2))
    case _ _:
      False{}

# a and b are the same entry
def Entry.same(a: Entry, b: Entry) -> Bool:
  match a b:
    case Entry.Ask{i1, t1, q1} Entry.Ask{i2, t2, q2}:
      Bool.and(Id.same(i1, i2), Bool.and(String.eq(t1, t2), Ask.same(q1, q2)))
    case Entry.Vote{i1} Entry.Vote{i2}:
      Id.same(i1, i2)
    case Entry.Root{c1, i1, n1} Entry.Root{c2, i2, n2}:
      Bool.and(Chain.same(c1, c2), Bool.and(Id.same(i1, i2), String.eq(n1, n2)))
    case _ _:
      False{}

# Entry.same is True for an entry and itself
law Entry.same_refl:
  for a: Entry
  {Entry.same(a, a) == True{}: Bool}

# Entry.same is True only for equal entries
law Entry.same_sound:
  for a: Entry
  for b: Entry
  {Entry.same(a, b) == True{}: Bool} -> {a == b: Entry}

# The state
# ---------

# what a node holds: the cell of each slot, by the slot's key
def State() -> Data:
  Tries.Trie<Cells.Cell<Entry>>

# a node that holds nothing yet
def Node.empty() -> State():
  Tries.Tip{}

# what a holder of a and of b holds: a sync
def Node.join(a: State(), b: State()) -> State():
  Tries.Trie.union(~Cells.Cell<Entry>, ~Cells.Cell.join(~Entry, ~Entry.same), a, b)

# what a holder of r lacks of s: what a sync from s to r sends
# (Tries.Trie.union_minus)
def Node.missing(s: State(), r: State()) -> State():
  Tries.Trie.minus(~Cells.Cell<Entry>, ~Cells.Cell.same(~Entry, ~Entry.same), s, r)

# no entry of t contradicts one of s
def Node.agrees(s: State(), t: State()) -> Bool:
  Cells.Cell.agrees(~Entry, ~Entry.same, s, t)

# the first claim among the cells cs that every holder agrees on
def Root.first(cs: List<&2, Cells.Cell<Entry>>) -> Maybe<&2, Entry>:
  match cs:
    case Nil{}:
      None{}
    case Con{Cells.One{e}, r}:
      Some{e}
    case Con{Cells.Many{}, r}:
      Root.first(r)

# the claim of the first version of the chain c: when nodes claim it apart,
# the one with the smallest key
def Node.claim(s: State(), c: Chain) -> Maybe<&2, Entry>:
  Root.first(Tries.Trie.values(Cells.Cell<Entry>, Tries.Trie.under(Cells.Cell<Entry>, s, Root.key(c))))

# Answers
# -------

# where a request is. Written: in its chain. Conflicted: a merge or a resolve
# in its chain, after which resources still clash. Pending: not in its chain
# yet, and its owners may still vote for it. Stale: its owners cannot vote for
# it at the head any more. Refused: it, or its chain, is contradicted, or it
# changes a chain that does not exist.
type Answer is Data:
  Answer.Written{version: Id}
  Answer.Conflicted{version: Id}
  Answer.Pending{}
  Answer.Stale{head: Id}
  Answer.Refused{why: String}
  Answer.NotSeen{}

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: String, owners: List<&2, String>, head: Id}

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Id, time: String}

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, or the groups
type Topic is Data:
  Topic.Versions{branch: String}
  Topic.Conflicts{branch: String}
  Topic.Groups{}

# an event of a topic. GroupCycle: the group is inside itself, as syncs can
# leave groups; a set-group settles it
type Notice is Data:
  Notice.Versioned{branch: String, version: Id}
  Notice.Conflicted{branch: String, version: Id}
  Notice.GroupCycle{group: String}

# Reads
# -----

# the versions of the chain c, in order
law Node.chain:
  for s: State()
  for c: Chain
  List<&2, Id>

# the nodes that vote for the next version of the chain c
law Node.owners:
  for s: State()
  for c: Chain
  List<&2, String>

# the newest version of the branch b, if b exists
law Node.head:
  for s: State()
  for b: String
  Maybe<&2, Id>

# the bytes of the resource n at the point p, if it is there
law Node.content:
  for s: State()
  for n: Resources.Name
  for p: Point
  Maybe<&2, Octets.Bytes()>

# the bytes of the resource n at the version base, if any
law Node.content_at:
  for s: State()
  for n: Resources.Name
  for base: Maybe<&2, Id>
  Maybe<&2, Octets.Bytes()>

# every branch
law Node.branches:
  for s: State()
  List<&2, BranchEntry>

# the versions of the branch b that changed the resource n
law Node.log:
  for s: State()
  for n: Resources.Name
  for b: String
  List<&2, LogEntry>

# what changed in the resource n from the point a to the point b
law Node.diff:
  for s: State()
  for n: Resources.Name
  for a: Point
  for b: Point
  List<&2, Formats.Change>

# where the request i is
law Node.answer:
  for s: State()
  for i: Id
  Answer

# the resources that still clash after the merge k
law Node.conflict:
  for s: State()
  for k: Id
  List<&2, Resources.Name>

# the members of the group g, if g exists
law Node.members:
  for s: State()
  for g: String
  Maybe<&2, List<&2, Member>>

# m is a member of the group g, or of a group inside g
law Node.is_inside:
  for s: State()
  for m: Member
  for g: String
  Bool

# the nodes inside the group g: what a set-owner to g asks for
law Node.nodes:
  for s: State()
  for g: String
  List<&2, String>

# the notices of the topic t in s that since does not have
law Node.notices:
  for s: State()
  for t: Topic
  for since: State()
  List<&2, Notice>

# Changes
# -------

# s, after the node n took in the request q of e: the request, n's vote for
# it when n owns its chain and q fits the head, or its root when q makes a
# chain. A request that s holds already changes nothing.
law Node.ask:
  for n: String
  for s: State()
  for e: Envelope
  for q: Ask
  State()

# s, after the node n voted at the head of each chain that it owns, for the
# first request there that fits it
law Node.vote:
  for n: String
  for s: State()
  State()

# Laws
# ----

# a chain only grows when no new entry contradicts an old one and its claim
# stays: what a node answered Written stays so after such a sync
law Node.chain_kept:
  for s: State()
  for t: State()
  for c: Chain
  {Node.agrees(s, t) == True{}: Bool}
    -> {Node.claim(Node.join(s, t), c) == Node.claim(s, c): Maybe<&2, Entry>}
    -> {
      List.take(&2, Id, Node.chain(Node.join(s, t), c), List.length(&2, Id, Node.chain(s, c)))
        == Node.chain(s, c): List<&2, Id>
    }

# the sole owner of a branch writes a resource that did not change since its
# base: the write is Written, and its version holds the bytes
law Node.write_written:
  for n: String
  for s: State()
  for e: Envelope
  for b: String
  for name: Resources.Name
  for base: Maybe<&2, Id>
  for x: Octets.Bytes()
  for v: Id
  {Node.owners(s, Chain.Branch{b}) == [n]: List<&2, String>}
    -> {Node.head(s, b) == Some{v}: Maybe<&2, Id>}
    -> {Tries.Trie.get(Cells.Cell<Entry>, s, Slot.key(Slot.Ask{Envelope.of(e)})) == None{}: Maybe<&2, Cells.Cell<Entry>>}
    -> {Tries.Trie.get(Cells.Cell<Entry>, s, Slot.key(Slot.Vote{n, Chain.Branch{b}, v})) == None{}: Maybe<&2, Cells.Cell<Entry>>}
    -> {Node.content(s, name, Point.Head{b}) == Node.content_at(s, name, base): Maybe<&2, Octets.Bytes()>}
    -> {
      Node.answer(Node.ask(n, s, e, Ask.Write{b, name, base, Content.Bytes{x}}), Envelope.of(e))
        == Answer.Written{Envelope.of(e)}: Answer
    }
      & {
        Node.content(Node.ask(n, s, e, Ask.Write{b, name, base, Content.Bytes{x}}), name, Point.At{Envelope.of(e)})
          == Some{x}: Maybe<&2, Octets.Bytes()>
      }

# the sole owner of a branch refuses a write of a resource that changed since
# its base: the branch stays as it was
law Node.write_stale:
  for n: String
  for s: State()
  for e: Envelope
  for b: String
  for name: Resources.Name
  for base: Maybe<&2, Id>
  for x: Content
  for v: Id
  {Node.owners(s, Chain.Branch{b}) == [n]: List<&2, String>}
    -> {Node.head(s, b) == Some{v}: Maybe<&2, Id>}
    -> {Tries.Trie.get(Cells.Cell<Entry>, s, Slot.key(Slot.Ask{Envelope.of(e)})) == None{}: Maybe<&2, Cells.Cell<Entry>>}
    -> {Tries.Trie.get(Cells.Cell<Entry>, s, Slot.key(Slot.Vote{n, Chain.Branch{b}, v})) == None{}: Maybe<&2, Cells.Cell<Entry>>}
    -> {
      Maybes.Maybe.same(
        ~Octets.Bytes(),
        ~Octets.Bytes.is_eq,
        Node.content(s, name, Point.Head{b}),
        Node.content_at(s, name, base)
      )
        == False{}: Bool
    }
    -> {Node.chain(Node.ask(n, s, e, Ask.Write{b, name, base, x}), Chain.Branch{b}) == Node.chain(s, Chain.Branch{b}): List<&2, Id>}
