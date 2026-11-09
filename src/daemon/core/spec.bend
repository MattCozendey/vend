import Base
import ../../shared/cells.bend as Cells
import ../../shared/formats.bend as Formats
import ../../shared/resources.bend as Resources
import ../../shared/shared.bend as Shared

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API).
#
# A node holds entries in slots. Two nodes sync by joining what they hold, so
# every node that took in the same entries holds the same state, in any order
# and any number of times (Shared.Trie.union_comm, union_assoc, union_idem, with
# the laws of Cells.Cell.join). Every answer is read from the state alone.
#
# A chain (a branch, or an owner group) is a list of versions. Its first
# version is the request that a root entry names; each next one is the
# request that most of the chain's owners vote for, after the version before
# it. A slot with two different entries holds many: the request, the vote or
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
  Chain.branch{name: String}
  Chain.group{name: String}

# a member of an owner group: a node, or another group
type Member is Data:
  Member.node{name: String}
  Member.group{name: String}

# new content: bytes, or what an old version held
type Content is Data:
  Content.bytes{bytes: Shared.Bytes()}
  Content.of{version: Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.at{version: Id}
  Point.head{branch: String}
  Point.mark{branch: String, mark: String}

# Requests
# --------
# A request is data alone: a point becomes a version before it is asked for,
# so that a request sent again, to any node, is the same request.

# a change that a writer asks for
type Ask is Data:
  Ask.write{branch: String, name: Resources.Name, base: Maybe<&2, Id>, content: Content}
  Ask.set_branch{branch: String, to: Id}
  Ask.merge{branch: String, from: Id}
  Ask.resolve{branch: String, conflict: Id, name: Resources.Name, content: Content}
  Ask.mark{branch: String, mark: String, message: String}
  Ask.set_owner{chain: Chain, members: List<&2, String>}
  Ask.set_group{group: String, members: List<&2, Member>}

# the chain that q changes
def Ask.chain(q: Ask) -> Chain:
  match q:
    case Ask.write{b, n, base, c}:
      Chain.branch{b}
    case Ask.set_branch{b, v}:
      Chain.branch{b}
    case Ask.merge{b, v}:
      Chain.branch{b}
    case Ask.resolve{b, k, n, c}:
      Chain.branch{b}
    case Ask.mark{b, m, t}:
      Chain.branch{b}
    case Ask.set_owner{c, ms}:
      c
    case Ask.set_group{g, ms}:
      Chain.group{g}

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
  Entry.ask{id: Id, time: String, ask: Ask}
  Entry.vote{choice: Id}
  Entry.root{chain: Chain, first: Id, owner: String}

# where an entry is: a request by its ID, a vote by its node and the version
# that it follows, a root by its chain and the node that claims it
type Slot is Data:
  Slot.ask{id: Id}
  Slot.vote{node: String, chain: Chain, after: Id}
  Slot.root{chain: Chain, owner: String}

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Shared.Trie.text(w), Shared.Trie.text(r))

# the key of c
def Chain.key(c: Chain) -> List<&2, Bool>:
  match c:
    case Chain.branch{n}:
      False{} <> Shared.Trie.text(n)
    case Chain.group{n}:
      True{} <> Shared.Trie.text(n)

# the start of the keys of the roots of c
def Root.key(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> Chain.key(c)

# the key of k: no two slots share one
def Slot.key(k: Slot) -> List<&2, Bool>:
  match k:
    case Slot.ask{i}:
      False{} <> Id.key(i)
    case Slot.vote{n, c, i}:
      True{}
        <> False{}
        <> List.append(
          &2,
          Bool,
          Shared.Trie.text(n),
          List.append(&2, Bool, Chain.key(c), Id.key(i))
        )
    case Slot.root{c, n}:
      List.append(&2, Bool, Root.key(c), Shared.Trie.text(n))

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
    case Chain.branch{x} Chain.branch{y}:
      String.eq(x, y)
    case Chain.group{x} Chain.group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# a and b are the same member
def Member.same(a: Member, b: Member) -> Bool:
  match a b:
    case Member.node{x} Member.node{y}:
      String.eq(x, y)
    case Member.group{x} Member.group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# a and b are the same content
def Content.same(a: Content, b: Content) -> Bool:
  match a b:
    case Content.bytes{x} Content.bytes{y}:
      Shared.Bytes.is_eq(x, y)
    case Content.of{x} Content.of{y}:
      Id.same(x, y)
    case _ _:
      False{}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- an equality, or a proof, keeps each and/or as one value for the proofs to split on
# a and b are the same change
def Ask.same(a: Ask, b: Ask) -> Bool:
  match a b:
    case Ask.write{b1, n1, v1, c1} Ask.write{b2, n2, v2, c2}:
      Bool.and(
        String.eq(b1, b2),
        Bool.and(
          Resources.Name.same(n1, n2),
          Bool.and(Shared.Maybe.same(~Id, ~Id.same, v1, v2), Content.same(c1, c2))
        )
      )
    case Ask.set_branch{b1, v1} Ask.set_branch{b2, v2}:
      Bool.and(String.eq(b1, b2), Id.same(v1, v2))
    case Ask.merge{b1, v1} Ask.merge{b2, v2}:
      Bool.and(String.eq(b1, b2), Id.same(v1, v2))
    case Ask.resolve{b1, k1, n1, c1} Ask.resolve{b2, k2, n2, c2}:
      Bool.and(
        String.eq(b1, b2),
        Bool.and(Id.same(k1, k2), Bool.and(Resources.Name.same(n1, n2), Content.same(c1, c2)))
      )
    case Ask.mark{b1, m1, t1} Ask.mark{b2, m2, t2}:
      Bool.and(String.eq(b1, b2), Bool.and(String.eq(m1, m2), String.eq(t1, t2)))
    case Ask.set_owner{c1, ms1} Ask.set_owner{c2, ms2}:
      Bool.and(Chain.same(c1, c2), Shared.List.same(~String, ~String.eq, ms1, ms2))
    case Ask.set_group{g1, ms1} Ask.set_group{g2, ms2}:
      Bool.and(String.eq(g1, g2), Shared.List.same(~Member, ~Member.same, ms1, ms2))
    case _ _:
      False{}

# a and b are the same entry
def Entry.same(a: Entry, b: Entry) -> Bool:
  match a b:
    case Entry.ask{i1, t1, q1} Entry.ask{i2, t2, q2}:
      Bool.and(Id.same(i1, i2), Bool.and(String.eq(t1, t2), Ask.same(q1, q2)))
    case Entry.vote{i1} Entry.vote{i2}:
      Id.same(i1, i2)
    case Entry.root{c1, i1, n1} Entry.root{c2, i2, n2}:
      Bool.and(Chain.same(c1, c2), Bool.and(Id.same(i1, i2), String.eq(n1, n2)))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

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
  Shared.Trie<Cells.Cell<Entry>>

# a node that holds nothing yet
def Node.empty() -> State():
  Shared.Trie.new(Cells.Cell<Entry>)

# what a holder of a and of b holds: a sync
def Node.join(a: State(), b: State()) -> State():
  Shared.Trie.union(~Cells.Cell<Entry>, ~Cells.Cell.join(~Entry, ~Entry.same), a, b)

# what a holder of r lacks of s: what a sync from s to r sends
# (Shared.Trie.union_minus)
def Node.missing(s: State(), r: State()) -> State():
  Shared.Trie.minus(~Cells.Cell<Entry>, ~Cells.Cell.same(~Entry, ~Entry.same), s, r)

# no entry of t contradicts one of s
def Node.agrees(s: State(), t: State()) -> Bool:
  Cells.Cell.agrees(~Entry, ~Entry.same, s, t)

# the first claim among the cells cs that every holder agrees on
def Root.first(cs: List<&2, Cells.Cell<Entry>>) -> Maybe<&2, Entry>:
  match cs:
    case Nil{}:
      None{}
    case Con{Cells.one{e}, r}:
      Some{e}
    case Con{Cells.many{}, r}:
      Root.first(r)

# the claim of the first version of the chain c: when nodes claim it apart,
# the one with the smallest key
def Node.claim(s: State(), c: Chain) -> Maybe<&2, Entry>:
  Root.first(
    Shared.Trie.values(Cells.Cell<Entry>, Shared.Trie.under(Cells.Cell<Entry>, s, Root.key(c)))
  )

# Answers
# -------

# where a request is. Written: in its chain. Conflicted: a merge or a resolve
# in its chain, after which resources still clash. Pending: not in its chain
# yet, and its owners may still vote for it. Stale: its owners cannot vote for
# it at the head any more: a write whose resource changed since its base, a
# mark whose name is taken, or a set-group that would make the group contain
# itself. Refused: it, or its chain, is contradicted, or it
# changes a chain that does not exist.
type Answer is Data:
  Answer.written{version: Id}
  Answer.conflicted{version: Id}
  Answer.pending{}
  Answer.stale{head: Id}
  Answer.refused{why: String}
  Answer.not_seen{}

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: String, owners: List<&2, String>, head: Id}

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Id, time: String}

# a change elsewhere that touches what a branch uses: the version wrote the
# resource changed, and the resource used of the branch is that resource or
# uses it (Node.affects_exactly)
type Touch is Data:
  Touch{version: Id, changed: Resources.Name, branch: String, used: Resources.Name}

# a and b are the same touch
def Touch.same(a: Touch, b: Touch) -> Bool:
  match a b:
    case Touch{v1, c1, b1, u1} Touch{v2, c2, b2, u2}:
      Bool.and(
        Id.same(v1, v2),
        Bool.and(
          Resources.Name.same(c1, c2),
          Bool.and(String.eq(b1, b2), Resources.Name.same(u1, u2))
        )
      )

# the branch of t
def Touch.branch(t: Touch) -> String:
  match t:
    case Touch{v, c, b, u}:
      b

# the version of t
def Touch.version(t: Touch) -> Id:
  match t:
    case Touch{v, c, b, u}:
      v

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, the changes elsewhere that touch it, or the groups
type Topic is Data:
  Topic.versions{branch: String}
  Topic.conflicts{branch: String}
  Topic.affects{branch: String}
  Topic.groups{}

# an event of a topic. GroupCycle: the group is inside itself, as syncs can
# leave groups; a set-group settles it
type Notice is Data:
  Notice.versioned{branch: String, version: Id}
  Notice.conflicted{branch: String, version: Id}
  Notice.touched{touch: Touch}
  Notice.group_cycle{group: String}

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
  Maybe<&2, Shared.Bytes()>

# the bytes of the resource n at the version base, if any
law Node.content_at:
  for s: State()
  for n: Resources.Name
  for base: Maybe<&2, Id>
  Maybe<&2, Shared.Bytes()>

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

# the version at the point p, if there is one
law Node.version:
  for s: State()
  for p: Point
  Maybe<&2, Id>

# x is the version v, or a version that v came from
law Node.has:
  for s: State()
  for v: Id
  for x: Id
  Bool

# the resource that the version v wrote, when it is a write or a resolve
law Node.wrote:
  for s: State()
  for v: Id
  Maybe<&2, Resources.Name>

# the resources of the branch b at its head
law Node.resources:
  for s: State()
  for b: String
  List<&2, Resources.Name>

# the resources that the resource u of the branch b imports, as the format of
# u reads them at the head of b
law Node.imports:
  for s: State()
  for b: String
  for u: Resources.Name
  List<&2, Resources.Name>

# the resource u of the branch b uses c: through its imports, at any depth
law Node.uses:
  for s: State()
  for b: String
  for u: Resources.Name
  for c: Resources.Name
  Bool

# the newer of the versions x and y, when one came from the other
law Node.forward:
  for s: State()
  for x: Id
  for y: Id
  Maybe<&2, Id>

# the touch t holds (Node.touches_exactly)
law Node.touches:
  for s: State()
  for t: Touch
  Bool

# the changes elsewhere that touch what the branch b uses
law Node.affects:
  for s: State()
  for b: String
  List<&2, Touch>

# what the changes up to the point p touch elsewhere
law Node.impact:
  for s: State()
  for p: Point
  List<&2, Touch>

# Submodules
# ----------
# A submodule is a resource whose bytes point to a child (Format.module): the
# space of the child's resources, the branch that it follows, and its
# version, on lines of their own. Never a node: any node that has the version
# can serve it. A reader goes through it to the content at Point.at of that
# version, and a merge of two pointers takes the newer one when one came from
# the other (Node.forward).

# a pointer to a child
type Pointer is Data:
  Pointer{space: String, branch: String, version: Id}

# the version of the child that p points to
def Pointer.version(p: Pointer) -> Id:
  match p:
    case Pointer{sp, b, v}:
      v

# the bytes of the pointer p
def Pointer.show(p: Pointer) -> Shared.Bytes():
  match p:
    case Pointer{sp, b, Id{w, r}}:
      Shared.Bytes.of_text(
        String.append(
          sp,
          SCon{Chr{10}, String.append(b, SCon{Chr{10}, String.append(w, SCon{Chr{10}, r})})}
        )
      )

# the pointer of the space sp and the branch b, once the text after them is
# cut at its first line (c)
def Pointer.read.last(sp: String, b: String, c: Maybe<&2, Shared.Cut>) -> Maybe<&2, Pointer>:
  match c:
    case None{}:
      None{}
    case Some{Shared.Cut{w, r}}:
      Some{Pointer{sp, b, Id{w, r}}}

# the pointer of the space sp, once the text after it is cut at its first
# line (c)
def Pointer.read.rest(sp: String, c: Maybe<&2, Shared.Cut>) -> Maybe<&2, Pointer>:
  match c:
    case None{}:
      None{}
    case Some{Shared.Cut{b, t}}:
      Pointer.read.last(sp, b, Shared.Text.cut(t, 10))

# the pointer of a text, once it is cut at its first line (c)
def Pointer.read.cut(c: Maybe<&2, Shared.Cut>) -> Maybe<&2, Pointer>:
  match c:
    case None{}:
      None{}
    case Some{Shared.Cut{sp, t}}:
      Pointer.read.rest(sp, Shared.Text.cut(t, 10))

# the pointer in the bytes b
def Pointer.read(b: Shared.Bytes()) -> Maybe<&2, Pointer>:
  Pointer.read.cut(Shared.Text.cut(Shared.Bytes.to_text(b), 10))

# Touches
# -------

# the names of the branches es
def Branch.names(es: List<&2, BranchEntry>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{b, os, h}, r}:
      b <> Branch.names(r)

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
      List.take(
        &2,
        Id,
        Node.chain(Node.join(s, t), c),
        List.length(&2, Id, Node.chain(s, c))
      )
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
  for x: Shared.Bytes()
  for v: Id
  {Node.owners(s, Chain.branch{b}) == [n]: List<&2, String>}
    -> {Node.head(s, b) == Some{v}: Maybe<&2, Id>}
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.ask{Envelope.of(e)})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.vote{n, Chain.branch{b}, v})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {
      Node.content(
        s,
        name,
        Point.head{b}
      )
        == Node.content_at(s, name, base): Maybe<&2, Shared.Bytes()>
    }
    -> {
      Node.answer(
        Node.ask(n, s, e, Ask.write{b, name, base, Content.bytes{x}}),
        Envelope.of(e)
      )
        == Answer.written{Envelope.of(e)}: Answer
    }
      & {
        Node.content(
          Node.ask(n, s, e, Ask.write{b, name, base, Content.bytes{x}}),
          name,
          Point.at{Envelope.of(e)}
        )
          == Some{x}: Maybe<&2, Shared.Bytes()>
      }

# the sole owner of a group refuses a set-group that would make the group
# contain itself, as a member h of the new set is the group or holds it: the
# group stays as it was
law Node.set_group_cycle:
  for n: String
  for s: State()
  for e: Envelope
  for g: String
  for ms: List<&2, Member>
  for h: String
  for v: Id
  {Node.owners(s, Chain.group{g}) == [n]: List<&2, String>}
    -> {List.last(&2, Id, Node.chain(s, Chain.group{g})) == Some{v}: Maybe<&2, Id>}
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.ask{Envelope.of(e)})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.vote{n, Chain.group{g}, v})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {Shared.List.has(~Member, ~Member.same, ms, Member.group{h}) == True{}: Bool}
    -> {Bool.or(String.eq(h, g), Node.is_inside(s, Member.group{g}, h)) == True{}: Bool}
    -> {
      Node.chain(
        Node.ask(n, s, e, Ask.set_group{g, ms}),
        Chain.group{g}
      )
        == Node.chain(s, Chain.group{g}): List<&2, Id>
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
  {Node.owners(s, Chain.branch{b}) == [n]: List<&2, String>}
    -> {Node.head(s, b) == Some{v}: Maybe<&2, Id>}
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.ask{Envelope.of(e)})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {
      Shared.Trie.get(
        Cells.Cell<Entry>,
        s,
        Slot.key(Slot.vote{n, Chain.branch{b}, v})
      )
        == None{}: Maybe<&2, Cells.Cell<Entry>>
    }
    -> {
      Shared.Maybe.same(
        ~Shared.Bytes(),
        ~Shared.Bytes.is_eq,
        Node.content(s, name, Point.head{b}),
        Node.content_at(s, name, base)
      )
        == False{}: Bool
    }
    -> {
      Node.chain(
        Node.ask(n, s, e, Ask.write{b, name, base, x}),
        Chain.branch{b}
      )
        == Node.chain(s, Chain.branch{b}): List<&2, Id>
    }

# a touch holds when its branch is a branch and lacks its version, which is a
# version of a branch and wrote the resource changed, and the resource used is
# of the branch, and is the one changed or uses it
law Node.touches_exactly:
  for s: State()
  for v: Id
  for c: Resources.Name
  for b: String
  for u: Resources.Name
  {
    Node.touches(
      s,
      Touch{v, c, b, u}
    )
      == Bool.and(
        Shared.List.has(~String, ~String.eq, Branch.names(Node.branches(s)), b),
        Bool.and(
          Shared.List.has(
            ~Id,
            ~Id.same,
            Shared.List.flat(
              ~String,
              ~Id,
              ~State(),
              ~(t => x => Node.chain(t, Chain.branch{x})),
              Branch.names(Node.branches(s)),
              s
            ),
            v
          ),
          Bool.and(
            Bool.and(
              Maybe.is_some(&2, Id, Node.head(s, b)),
              Bool.not(Node.has(s, Maybe.default(&2, Id, Node.head(s, b), v), v))
            ),
            Bool.and(
              Shared.Maybe.same(~Resources.Name, ~Resources.Name.same, Node.wrote(s, v), Some{c}),
              Bool.and(
                Shared.List.has(~Resources.Name, ~Resources.Name.same, Node.resources(s, b), u),
                Bool.or(Resources.Name.same(u, c), Node.uses(s, b, u, c))
              )
            )
          )
        )
      ): Bool
  }

# the branch b is affected by exactly the touches of b that hold: the changes
# elsewhere to what b uses, at any depth
law Node.affects_exactly:
  for s: State()
  for b: String
  for t: Touch
  {
    Shared.List.has(
      ~Touch,
      ~Touch.same,
      Node.affects(s, b),
      t
    )
      == Bool.and(String.eq(Touch.branch(t), b), Node.touches(s, t)): Bool
  }

# the impact of the point p is exactly the touches that hold of its version or
# of a version that it came from
law Node.impact_exactly:
  for s: State()
  for p: Point
  for t: Touch
  {
    Shared.List.has(
      ~Touch,
      ~Touch.same,
      Node.impact(s, p),
      t
    )
      == Bool.and(
        Bool.and(
          Maybe.is_some(&2, Id, Node.version(s, p)),
          Node.has(s, Maybe.default(&2, Id, Node.version(s, p), Touch.version(t)), Touch.version(t))
        ),
        Node.touches(s, t)
      ): Bool
  }

# a resource of a branch uses what it imports
law Node.uses_import:
  for s: State()
  for b: String
  for u: Resources.Name
  for c: Resources.Name
  {Shared.List.has(~Resources.Name, ~Resources.Name.same, Node.resources(s, b), u) == True{}: Bool}
    -> {
      Shared.List.has(
        ~Resources.Name,
        ~Resources.Name.same,
        Node.imports(s, b, u),
        c
      )
        == True{}: Bool
    }
    -> {Node.uses(s, b, u, c) == True{}: Bool}

# what a used resource uses is used
law Node.uses_through:
  for s: State()
  for b: String
  for u: Resources.Name
  for h: Resources.Name
  for c: Resources.Name
  {Node.uses(s, b, u, h) == True{}: Bool}
    -> {Node.uses(s, b, h, c) == True{}: Bool}
    -> {Node.uses(s, b, u, c) == True{}: Bool}

# a pointer reads back from its bytes, when no part of it holds a line break
law Pointer.read_show:
  for sp: String
  for b: String
  for w: String
  for r: String
  {Shared.Text.has(sp, 10) == False{}: Bool}
    -> {Shared.Text.has(b, 10) == False{}: Bool}
    -> {Shared.Text.has(w, 10) == False{}: Bool}
    -> {
      Pointer.read(
        Pointer.show(Pointer{sp, b, Id{w, r}})
      )
        == Some{Pointer{sp, b, Id{w, r}}}: Maybe<&2, Pointer>
    }

# of two versions, the one that came from the other is newer
law Node.forward_theirs:
  for s: State()
  for x: Id
  for y: Id
  {Node.has(s, y, x) == True{}: Bool} -> {Node.forward(s, x, y) == Some{y}: Maybe<&2, Id>}

# of two versions, the one that the other came before is newer
law Node.forward_ours:
  for s: State()
  for x: Id
  for y: Id
  {Node.has(s, y, x) == False{}: Bool}
    -> {Node.has(s, x, y) == True{}: Bool}
    -> {Node.forward(s, x, y) == Some{x}: Maybe<&2, Id>}
