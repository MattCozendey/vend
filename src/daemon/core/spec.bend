import Base
import ../../shared/formats.bend as Formats
import ../../shared/reach.bend as Reaches
import ../../shared/replica.bend as Replica
import ../../shared/resources.bend as Resources
import ../../shared/shared.bend as Shared
import ../../shared/text.bend as Texts
import ../../shared/trie.bend as Tries

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API).
#
# A node is a replica of Vend's changes (Replica): it holds requests, votes and
# claims in slots, nodes sync by joining what they hold, and each chain (a
# branch, or an owner group) is the list of versions that its owners vote for.
# Every answer is read from the state alone.

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Replica.Id.

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
  Content.bytes{bytes: Texts.Bytes()}
  Content.of{version: Replica.Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.at{version: Replica.Id}
  Point.head{branch: String}
  Point.mark{branch: String, mark: String}

# the key of c: the replica names each chain by it
def Chain.key(c: Chain) -> List<&2, Bool>:
  match c:
    case Chain.branch{n}:
      False{} <> Tries.Trie.text(n)
    case Chain.group{n}:
      True{} <> Tries.Trie.text(n)

# Requests
# --------
# A request is data alone: a point becomes a version before it is asked for,
# so that a request sent again, to any node, is the same request.

# a change that a writer asks for
type Ask is Data:
  Ask.write{branch: String, name: Resources.Name, base: Maybe<&2, Replica.Id>, content: Content}
  Ask.set_branch{branch: String, to: Replica.Id}
  Ask.merge{branch: String, from: Replica.Id}
  Ask.resolve{branch: String, conflict: Replica.Id, name: Resources.Name, content: Content}
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

# the owners that q gives its chain, when it sets them
def Ask.owners(q: Ask) -> Maybe<&2, List<&2, String>>:
  match q:
    case Ask.set_owner{c, ms}:
      Some{ms}
    case _:
      None{}

# q makes its chain when the chain does not exist: a write with no base, a
# set-branch and a set-group do
def Ask.creates(q: Ask) -> Bool:
  match q:
    case Ask.write{b, n, None{}, c}:
      True{}
    case Ask.set_branch{b, to}:
      True{}
    case Ask.set_group{g, ms}:
      True{}
    case _:
      False{}

# what the replica reads of q
def Ask.view(q: Ask) -> Replica.View:
  +q = q
  Replica.View{Chain.key(Ask.chain(q)), Ask.owners(q), Ask.creates(q)}

# who asks for a change, and when
type Envelope is Data:
  Envelope{id: String, writer: String, time: String}

# the request of e
def Envelope.of(e: Envelope) -> Replica.Id:
  match e:
    case Envelope{r, w, t}:
      Replica.Id{w, r}

# the time of e
def Envelope.time(e: Envelope) -> String:
  match e:
    case Envelope{r, w, t}:
      t

# Equality
# --------

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
      Texts.Bytes.is_eq(x, y)
    case Content.of{x} Content.of{y}:
      Replica.Id.same(x, y)
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
          Bool.and(Shared.Maybe.same(~Replica.Id, ~Replica.Id.same, v1, v2), Content.same(c1, c2))
        )
      )
    case Ask.set_branch{b1, v1} Ask.set_branch{b2, v2}:
      Bool.and(String.eq(b1, b2), Replica.Id.same(v1, v2))
    case Ask.merge{b1, v1} Ask.merge{b2, v2}:
      Bool.and(String.eq(b1, b2), Replica.Id.same(v1, v2))
    case Ask.resolve{b1, k1, n1, c1} Ask.resolve{b2, k2, n2, c2}:
      Bool.and(
        String.eq(b1, b2),
        Bool.and(
          Replica.Id.same(k1, k2),
          Bool.and(Resources.Name.same(n1, n2), Content.same(c1, c2))
        )
      )
    case Ask.mark{b1, m1, t1} Ask.mark{b2, m2, t2}:
      Bool.and(String.eq(b1, b2), Bool.and(String.eq(m1, m2), String.eq(t1, t2)))
    case Ask.set_owner{c1, ms1} Ask.set_owner{c2, ms2}:
      Bool.and(Chain.same(c1, c2), Shared.List.same(~String, ~String.eq, ms1, ms2))
    case Ask.set_group{g1, ms1} Ask.set_group{g2, ms2}:
      Bool.and(String.eq(g1, g2), Shared.List.same(~Member, ~Member.same, ms1, ms2))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# The state
# ---------

# what a node holds
def State() -> Data:
  Replica.State(Ask)

# a node that holds nothing yet
def Node.empty() -> State():
  Replica.State.empty(~Ask)

# what a holder of a and of b holds: a sync
def Node.join(a: State(), b: State()) -> State():
  Replica.State.join(~Ask, ~Ask.same, a, b)

# what a holder of r lacks of s: what a sync from s to r sends
# (Tries.Trie.union_minus)
def Node.missing(s: State(), r: State()) -> State():
  Replica.State.missing(~Ask, ~Ask.same, s, r)

# no entry of t contradicts one of s
def Node.agrees(s: State(), t: State()) -> Bool:
  Replica.State.agrees(~Ask, ~Ask.same, s, t)

# the versions of the chain c, in order
def Node.chain(s: State(), c: Chain) -> List<&2, Replica.Id>:
  Replica.State.chain(~Ask, ~Ask.view, s, Chain.key(c))

# the nodes that vote for the next version of the chain c
def Node.owners(s: State(), c: Chain) -> List<&2, String>:
  Replica.State.owners(~Ask, ~Ask.view, s, Chain.key(c))

# the newest version of the branch b, if b exists
def Node.head(s: State(), b: String) -> Maybe<&2, Replica.Id>:
  Replica.State.head(~Ask, ~Ask.view, s, Chain.key(Chain.branch{b}))

# Answers
# -------

# a request in its chain (Replica.Status.done). Written: its version.
# Conflicted: a merge or a resolve after which resources still clash. A
# request is stale (Replica.Status.stale) when it does not fit the head
# (Node.fits): a write whose resource changed since its base, a mark whose
# name is taken, or a set-group that would make the group contain itself.
type Done is Data:
  Done.written{version: Replica.Id}
  Done.conflicted{version: Replica.Id}

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: String, owners: List<&2, String>, head: Replica.Id}

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Replica.Id, time: String}

# a change elsewhere that touches what a branch uses: the version wrote the
# resource changed, and the resource used of the branch is that resource or
# uses it (Node.affects_exactly)
type Touch is Data:
  Touch{version: Replica.Id, changed: Resources.Name, branch: String, used: Resources.Name}

# a and b are the same touch
def Touch.same(a: Touch, b: Touch) -> Bool:
  match a b:
    case Touch{v1, c1, b1, u1} Touch{v2, c2, b2, u2}:
      Bool.and(
        Replica.Id.same(v1, v2),
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
def Touch.version(t: Touch) -> Replica.Id:
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
  Notice.versioned{branch: String, version: Replica.Id}
  Notice.conflicted{branch: String, version: Replica.Id}
  Notice.touched{touch: Touch}
  Notice.group_cycle{group: String}

# Reads
# -----

# the bytes of the resource n at the point p, if it is there
law Node.content:
  for s: State()
  for n: Resources.Name
  for p: Point
  Maybe<&2, Texts.Bytes()>

# the bytes of the resource n at the version base, if any
law Node.content_at:
  for s: State()
  for n: Resources.Name
  for base: Maybe<&2, Replica.Id>
  Maybe<&2, Texts.Bytes()>

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
  for i: Replica.Id
  Replica.Status<Done>

# the resources that still clash after the merge k
law Node.conflict:
  for s: State()
  for k: Replica.Id
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
  Maybe<&2, Replica.Id>

# x is the version v, or a version that v came from
law Node.has:
  for s: State()
  for v: Replica.Id
  for x: Replica.Id
  Bool

# the resource that the version v wrote, when it is a write or a resolve
law Node.wrote:
  for s: State()
  for v: Replica.Id
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
# (Node.uses_exactly)
law Node.uses:
  for s: State()
  for b: String
  for u: Resources.Name
  for c: Resources.Name
  Bool

# the newer of the versions x and y, when one came from the other
# (Node.forward_exactly)
law Node.forward:
  for s: State()
  for x: Replica.Id
  for y: Replica.Id
  Maybe<&2, Replica.Id>

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
  Pointer{space: String, branch: String, version: Replica.Id}

# the version of the child that p points to
def Pointer.version(p: Pointer) -> Replica.Id:
  match p:
    case Pointer{sp, b, v}:
      v

# the bytes of the pointer p (Texts.Text.cuts_after_join reads them back)
def Pointer.show(p: Pointer) -> Texts.Bytes():
  match p:
    case Pointer{sp, b, Replica.Id{w, r}}:
      Texts.Bytes.of_text(Texts.Text.join([sp, b, w], Chr{10}, r))

# the pointer of the lines that a text cut into (m)
def Pointer.read.of(m: Maybe<&2, Texts.Parts>) -> Maybe<&2, Pointer>:
  match m:
    case Some{Texts.Parts{Con{sp, Con{b, Con{w, Nil{}}}}, r}}:
      Some{Pointer{sp, b, Replica.Id{w, r}}}
    case _:
      None{}

# the pointer in the bytes b
def Pointer.read(b: Texts.Bytes()) -> Maybe<&2, Pointer>:
  Pointer.read.of(Texts.Text.cuts(3n, Texts.Bytes.to_text(b), 10))

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

# the owners may vote for the change q at the head h of its chain: a write
# whose resource did not change since its base (Node.fits_write), a set-branch
# or a merge from a version that the node holds, a resolve of a resource that
# still clashes, a mark whose name is free, a set-owner to some node, and a
# set-group that keeps the group out of itself (Node.fits_set_group)
law Node.fits:
  for s: State()
  for q: Ask
  for h: Replica.Id
  Bool

# s, after the node n took in the request q of e (Node.ask_exactly)
law Node.ask:
  for n: String
  for s: State()
  for e: Envelope
  for q: Ask
  State()

# s, after the node n voted at the head of each chain that it owns
# (Node.vote_exactly)
law Node.vote:
  for n: String
  for s: State()
  State()

# Laws
# ----

# a node takes in a request as a replica of Vend's changes does
law Node.ask_exactly:
  for n: String
  for s: State()
  for e: Envelope
  for q: Ask
  {
    Node.ask(
      n,
      s,
      e,
      q
    )
      == Replica.State.ask(
        ~Ask,
        ~Ask.same,
        ~Ask.view,
        ~Node.fits,
        n,
        s,
        Envelope.of(e),
        Envelope.time(e),
        q
      ): State()
  }

# a node votes as a replica of Vend's changes does
law Node.vote_exactly:
  for n: String
  for s: State()
  {Node.vote(n, s) == Replica.State.vote(~Ask, ~Ask.same, ~Ask.view, ~Node.fits, n, s): State()}

# a write fits the head h exactly when its resource holds at h what it held at
# its base
law Node.fits_write:
  for s: State()
  for b: String
  for name: Resources.Name
  for base: Maybe<&2, Replica.Id>
  for x: Content
  for h: Replica.Id
  {
    Node.fits(
      s,
      Ask.write{b, name, base, x},
      h
    )
      == Shared.Maybe.same(
        ~Texts.Bytes(),
        ~Texts.Bytes.is_eq,
        Node.content_at(s, name, Some{h}),
        Node.content_at(s, name, base)
      ): Bool
  }

# a set-group does not fit when a member h of the new set is the group or
# holds it
law Node.fits_set_group:
  for s: State()
  for g: String
  for ms: List<&2, Member>
  for h: String
  for v: Replica.Id
  {List.contains(~Member, ~Member.same, ms, Member.group{h}) == True{}: Bool}
    -> {Bool.or(String.eq(h, g), Node.is_inside(s, Member.group{g}, h)) == True{}: Bool}
    -> {Node.fits(s, Ask.set_group{g, ms}, v) == False{}: Bool}

# the sole owner of a branch writes a resource that did not change since its
# base: the write is Written, and its version holds the bytes
law Node.write_written:
  for n: String
  for s: State()
  for e: Envelope
  for b: String
  for name: Resources.Name
  for base: Maybe<&2, Replica.Id>
  for x: Texts.Bytes()
  for v: Replica.Id
  {Node.owners(s, Chain.branch{b}) == [n]: List<&2, String>}
    -> {Node.head(s, b) == Some{v}: Maybe<&2, Replica.Id>}
    -> {
      Replica.State.cell(
        ~Ask,
        s,
        Replica.Slot.ask{Envelope.of(e)}
      )
        == None{}: Maybe<&2, Replica.Cell<Replica.Entry<Ask>>>
    }
    -> {
      Replica.State.cell(
        ~Ask,
        s,
        Replica.Slot.vote{n, Chain.key(Chain.branch{b}), v}
      )
        == None{}: Maybe<&2, Replica.Cell<Replica.Entry<Ask>>>
    }
    -> {
      Node.content(
        s,
        name,
        Point.head{b}
      )
        == Node.content_at(s, name, base): Maybe<&2, Texts.Bytes()>
    }
    -> {
      Node.answer(
        Node.ask(n, s, e, Ask.write{b, name, base, Content.bytes{x}}),
        Envelope.of(e)
      )
        == Replica.Status.done{Done.written{Envelope.of(e)}}: Replica.Status<Done>
    }
      & {
        Node.content(
          Node.ask(n, s, e, Ask.write{b, name, base, Content.bytes{x}}),
          name,
          Point.at{Envelope.of(e)}
        )
          == Some{x}: Maybe<&2, Texts.Bytes()>
      }

# a touch holds when its branch is a branch and lacks its version, which is a
# version of a branch and wrote the resource changed, and the resource used is
# of the branch, and is the one changed or uses it
law Node.touches_exactly:
  for s: State()
  for v: Replica.Id
  for c: Resources.Name
  for b: String
  for u: Resources.Name
  {
    Node.touches(
      s,
      Touch{v, c, b, u}
    )
      == Bool.and(
        List.contains(~String, ~String.eq, Branch.names(Node.branches(s)), b),
        Bool.and(
          List.contains(
            ~Replica.Id,
            ~Replica.Id.same,
            Shared.List.flat(
              ~String,
              ~Replica.Id,
              ~State(),
              ~(t => x => Node.chain(t, Chain.branch{x})),
              Branch.names(Node.branches(s)),
              s
            ),
            v
          ),
          Bool.and(
            Bool.and(
              Maybe.is_some(&2, Replica.Id, Node.head(s, b)),
              Bool.not(Node.has(s, Maybe.default(&2, Replica.Id, Node.head(s, b), v), v))
            ),
            Bool.and(
              Shared.Maybe.same(~Resources.Name, ~Resources.Name.same, Node.wrote(s, v), Some{c}),
              Bool.and(
                List.contains(~Resources.Name, ~Resources.Name.same, Node.resources(s, b), u),
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
    List.contains(
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
    List.contains(
      ~Touch,
      ~Touch.same,
      Node.impact(s, p),
      t
    )
      == Bool.and(
        Bool.and(
          Maybe.is_some(&2, Replica.Id, Node.version(s, p)),
          Node.has(
            s,
            Maybe.default(&2, Replica.Id, Node.version(s, p), Touch.version(t)),
            Touch.version(t)
          )
        ),
        Node.touches(s, t)
      ): Bool
  }

# the branch of a node, as a graph: its resources, and what each imports
type Uses is Data:
  Uses{state: State(), branch: String, names: List<&2, Resources.Name>}

# the node of g
def Uses.state(g: Uses) -> State():
  match g:
    case Uses{s, b, ns}:
      s

# the branch of g
def Uses.branch(g: Uses) -> String:
  match g:
    case Uses{s, b, ns}:
      b

# the resources of g
def Uses.names(g: Uses) -> List<&2, Resources.Name>:
  match g:
    case Uses{s, b, ns}:
      ns

# the resource u of the branch b uses c exactly when c is reached from u
# through the imports of the resources of b
law Node.uses_exactly:
  for s: State()
  for b: String
  for u: Resources.Name
  for c: Resources.Name
  {
    Node.uses(
      s,
      b,
      u,
      c
    )
      == Reaches.Reach.in(
        ~Resources.Name,
        ~Uses,
        ~Resources.Name.same,
        ~(
          +g => +n => Shared.Bool.when(
            List<&2, Resources.Name>,
            List.contains(~Resources.Name, ~Resources.Name.same, Uses.names(g), n),
            w => Node.imports(Uses.state(g), Uses.branch(g), n),
            w => []
          )
        ),
        ~Uses.names,
        Uses{s, b, Node.resources(s, b)},
        u,
        c
      ): Bool
  }

# the newer of the versions x and y: y when it came from x, else x when it
# came from y, else none
law Node.forward_exactly:
  for s: State()
  for x: Replica.Id
  for y: Replica.Id
  {
    Node.forward(
      s,
      x,
      y
    )
      == Bool.pick(
        Maybe<&2, Replica.Id>,
        Node.has(s, y, x),
        Some{y},
        Bool.pick(Maybe<&2, Replica.Id>, Node.has(s, x, y), Some{x}, None{})
      ): Maybe<&2, Replica.Id>
  }
