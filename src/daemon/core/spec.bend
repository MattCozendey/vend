import Base
import ../../shared/bytes.bend as Octets
import ../../shared/resources.bend as Resources

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API).

# Names
# -----

# a Vend Node
law VendNode:
  Data

# the node that t names
law VendNode.read:
  for t: String
  Maybe<&2, VendNode>

# the text of n
law VendNode.show:
  for n: VendNode
  String

# an owner group
law Group:
  Data

# the group that t names
law Group.read:
  for t: String
  Maybe<&2, Group>

# the text of g
law Group.show:
  for g: Group
  String

# a space: the resources that version together
law Space:
  Data

# the space that t names
law Space.read:
  for t: String
  Maybe<&2, Space>

# the text of s
law Space.show:
  for s: Space
  String

# a branch
law Branch:
  Data

# the branch that t names
law Branch.read:
  for t: String
  Maybe<&2, Branch>

# the text of b
law Branch.show:
  for b: Branch
  String

# a mark: a named point of a branch
law Mark:
  Data

# the mark that t names
law Mark.read:
  for t: String
  Maybe<&2, Mark>

# the text of m
law Mark.show:
  for m: Mark
  String

# a writer
law Writer:
  Data

# the writer that t names
law Writer.read:
  for t: String
  Maybe<&2, Writer>

# the text of w
law Writer.show:
  for w: Writer
  String

# a version
law Version:
  Data

# the version that t names
law Version.read:
  for t: String
  Maybe<&2, Version>

# the text of v
law Version.show:
  for v: Version
  String

# the ID of a request that changes something
law RequestId:
  Data

# the request ID that t names
law RequestId.read:
  for t: String
  Maybe<&2, RequestId>

# the text of r
law RequestId.show:
  for r: RequestId
  String

# a position, to start from with "since"
law Position:
  Data

# the position that t names
law Position.read:
  for t: String
  Maybe<&2, Position>

# the text of p
law Position.show:
  for p: Position
  String

# a stored conflict
law Conflict:
  Data

# the conflict that t names
law Conflict.read:
  for t: String
  Maybe<&2, Conflict>

# the text of c
law Conflict.show:
  for c: Conflict
  String

# the epoch of an owner group: which ownership accepted a write
law Epoch:
  Data

# the epoch that t names
law Epoch.read:
  for t: String
  Maybe<&2, Epoch>

# the text of e
law Epoch.show:
  for e: Epoch
  String

# a time
law Time:
  Data

# the time that t names
law Time.read:
  for t: String
  Maybe<&2, Time>

# the text of t
law Time.show:
  for t: Time
  String

# a format: what decodes content into items (bend, c, text)
law Format:
  Data

# the format that t names
law Format.read:
  for t: String
  Maybe<&2, Format>

# the text of f
law Format.show:
  for f: Format
  String

# where an item is in its resource
law Place:
  Data

# the place that t names
law Place.read:
  for t: String
  Maybe<&2, Place>

# the text of p
law Place.show:
  for p: Place
  String

# Values that callers make
# ------------------------

# a point: a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Version}
  Point.Head{branch: Branch}
  Point.Mark{branch: Branch, mark: Mark}

# new content: bytes, or the content of an old version
type Content is Data:
  Content.Bytes{bytes: Octets.Bytes()}
  Content.Of{version: Version}

# who asks for a change, and when: what a pure step records with it
type Envelope is Data:
  Envelope{id: RequestId, writer: Writer, time: Time}

# the request ID of e
def Envelope.id(e: Envelope) -> RequestId:
  match e:
    case Envelope{r, w, t}:
      r

# a member of an owner group
type Member is Data:
  Member.VendNode{node: VendNode}
  Member.Group{group: Group}

# what a subscription or a poll follows: on a branch, or the groups
type Topic is Data:
  Topic.Affects{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Versions{branch: Branch}
  Topic.Groups{}

# Items
# -----

# a unit of content that a format decoded (a function, a type, a line)
law Item:
  Data

# the format that decoded i
law Item.format:
  for i: Item
  Format

# the label that the format gives i (function, type, line)
law Item.kind:
  for i: Item
  String

# the name of i
law Item.name:
  for i: Item
  String

# where i is
law Item.place:
  for i: Item
  Place

# the condition under which i exists, in the format's own text
law Item.condition:
  for i: Item
  Maybe<&2, String>

# the item that i is inside
law Item.parent:
  for i: Item
  Maybe<&2, Item>

# a change between two points, item by item
type Change is Data:
  Change.Added{item: Item}
  Change.Removed{item: Item}
  Change.Edited{before: Item, after: Item}

# a change that touches an item that other work uses
law Touch:
  Data

# the version that made the change
law Touch.version:
  for t: Touch
  Version

# the item that changed
law Touch.changed:
  for t: Touch
  Item

# the item that uses it
law Touch.used:
  for t: Touch
  Item

# Answers that callers read
# -------------------------

# a branch, as try_get_branches lists it
law BranchEntry:
  Data

# the branch
law BranchEntry.branch:
  for e: BranchEntry
  Branch

# its owner group
law BranchEntry.owner:
  for e: BranchEntry
  Group

# its newest version
law BranchEntry.newest:
  for e: BranchEntry
  Version

# a version, as try_get_log lists it
law LogEntry:
  Data

# the version
law LogEntry.version:
  for e: LogEntry
  Version

# its writer
law LogEntry.author:
  for e: LogEntry
  Writer

# when it was recorded
law LogEntry.time:
  for e: LogEntry
  Time

# an event of a topic. GroupCycle: a sync took the group's members although
# they close a cycle (see none_inside_itself_after); a set-group settles it.
# MarkMoved: a sync met the same mark of another node, on another version, and
# the smaller version won on both nodes
type Notice is Data:
  Notice.Touched{touch: Touch}
  Notice.Conflicted{conflict: Conflict}
  Notice.Versioned{branch: Branch, version: Version}
  Notice.GroupCycle{group: Group, members: List<&2, Member>}
  Notice.MarkMoved{branch: Branch, mark: Mark, from: Version, to: Version}

# Answers
# -------

# whether a request that timed out happened
type Outcome is Data:
  Outcome.Applied{at: Position}
  Outcome.NotSeen{}

# Pending: the owner group was not reached, and may still turn it into a
# conflict
type Write is Data:
  Write.Written{version: Version}
  Write.Pending{version: Version}
  Write.Stale{current: Version}
  Write.Refused{why: String}

# Partial: the submodules in missing could not be fetched
type SetBranch is Data:
  SetBranch.Created{version: Version}
  SetBranch.Restored{version: Version}
  SetBranch.Pending{version: Version}
  SetBranch.Partial{version: Version, missing: List<&2, Space>}
  SetBranch.Stale{current: Version}
  SetBranch.Refused{why: String}

type CreateMark is Data:
  CreateMark.Marked{mark: Mark}
  CreateMark.Taken{}
  CreateMark.Refused{why: String}

type Merge is Data:
  Merge.Merged{version: Version}
  Merge.Conflicted{conflict: Conflict}
  Merge.Stale{current: Version}
  Merge.Refused{why: String}

# Left: the resources of the conflict that still clash
type Resolve is Data:
  Resolve.Resolved{version: Version}
  Resolve.Left{names: List<&2, Resources.Name>}
  Resolve.Stale{current: Version}
  Resolve.Refused{why: String}

type SetOwner is Data:
  SetOwner.Set{epoch: Epoch}
  SetOwner.NoMajority{}
  SetOwner.Refused{why: String}

# Cycle: the group would contain itself
type SetGroup is Data:
  SetGroup.Set{epoch: Epoch}
  SetGroup.Cycle{}
  SetGroup.NoMajority{}
  SetGroup.Refused{why: String}

type Sync is Data:
  Sync.Synced{}
  Sync.Partial{}
  Sync.Refused{why: String}

# The pure node
# -------------
# What a node does, without IO: the laws are about these. Each try_
# operation of transport/spec.bend asks a node to run its pure variant: a
# read, or VendNode.ask for a change. Mounts, stops and connections have none:
# their behavior is IO.

# what a node holds
law VendNode.State:
  Data

# the node n, holding nothing yet
law VendNode.empty:
  for n: VendNode
  VendNode.State

# the position of s, to start from with "since"
law VendNode.position:
  for s: VendNode.State
  Position

# every branch of s
law VendNode.get_branches:
  for s: VendNode.State
  List<&2, BranchEntry>

# the versions of the resource n on the branch b
law VendNode.get_log:
  for s: VendNode.State
  for n: Resources.Name
  for b: Branch
  List<&2, LogEntry>

# the bytes of the resource n at the point p, if it is there
law VendNode.get_content:
  for s: VendNode.State
  for n: Resources.Name
  for p: Point
  Maybe<&2, Octets.Bytes()>

# what changed in the resource n from the point a to the point b
law VendNode.get_diff:
  for s: VendNode.State
  for n: Resources.Name
  for a: Point
  for b: Point
  List<&2, Change>

# the changes elsewhere that touch what the branch b uses
law VendNode.get_affects:
  for s: VendNode.State
  for b: Branch
  List<&2, Touch>

# what the changes up to the point p touch elsewhere
law VendNode.get_impact:
  for s: VendNode.State
  for p: Point
  List<&2, Touch>

# whether the request r happened
law VendNode.get_outcome:
  for s: VendNode.State
  for r: RequestId
  Outcome

# the notices of the topic t since the position p (from the start without
# one)
law VendNode.get_changes:
  for s: VendNode.State
  for t: Topic
  for p: Maybe<&2, Position>
  List<&2, Notice>

# a change that a node can be asked for
type Ask is Data:
  Ask.Write{name: Resources.Name, branch: Branch, base: Maybe<&2, Version>, content: Content}
  Ask.SetBranch{branch: Branch, point: Point}
  Ask.CreateMark{branch: Branch, mark: Mark, message: String}
  Ask.Merge{point: Point, branch: Branch}
  Ask.Resolve{conflict: Conflict, name: Resources.Name, content: Content}
  Ask.SetOwner{branch: Branch, group: Group}
  Ask.SetGroup{group: Group, members: List<&2, Member>}
  Ask.Sync{other: VendNode.State, since: Maybe<&2, Position>}

# q is made on this node: anything but taking in another node
def Ask.local(q: Ask) -> Bool:
  match q:
    case Ask.Sync{o, p}:
      False{}
    case _:
      True{}

# the answer to an Ask
type Answer is Data:
  Answer.Write{answer: Write}
  Answer.SetBranch{answer: SetBranch}
  Answer.CreateMark{answer: CreateMark}
  Answer.Merge{answer: Merge}
  Answer.Resolve{answer: Resolve}
  Answer.SetOwner{answer: SetOwner}
  Answer.SetGroup{answer: SetGroup}
  Answer.Sync{answer: Sync}

# s after the change q, beside its answer
law VendNode.ask:
  for s: VendNode.State
  for e: Envelope
  for q: Ask
  VendNode.State & Answer

# the epoch of the owner group of the branch b, if b exists
law VendNode.get_epoch:
  for s: VendNode.State
  for b: Branch
  Maybe<&2, Epoch>

# the number of e: a later epoch has a larger one
law Epoch.number:
  for e: Epoch
  Nat

# the newest version of the branch b, if b exists
law VendNode.get_head:
  for s: VendNode.State
  for b: Branch
  Maybe<&2, Version>

# the node of s is in the owner group of the branch b
law VendNode.is_owner:
  for s: VendNode.State
  for b: Branch
  Bool

# the members that the group g was last set to; None for a group never set
law VendNode.get_members:
  for s: VendNode.State
  for g: Group
  Maybe<&2, List<&2, Member>>

# m is a member of the group g, or of a group inside g
law VendNode.is_inside:
  for s: VendNode.State
  for m: Member
  for g: Group
  Bool

# Laws
# ----

# m is among ms: ms is ys, then m, then zs
def Member.Among(m: Member, ms: List<&2, Member>) -> Type:
  &ys: List<
    &2,
    Member> -> &zs: List<
    &2,
    Member> -> {ms == List.append(&2, Member, ys, m <> zs): List<&2, Member>}

# m is a member of the group g in s
def Member.Of(s: VendNode.State, g: Group, m: Member) -> Type:
  &ms: List<
    &2,
    Member> -> {
    VendNode.get_members(s, g) == Some{ms}: Maybe<&2, List<&2, Member>>
  }
    & Member.Among(m, ms)

# a chain of groups ps from g to m: each group of ps is a member of the one
# before it (the first, of g), and m is a member of the last
def VendNode.Chain(s: VendNode.State, g: Group, ps: List<&2, Group>, m: Member) -> Type:
  match ps:
    case Nil{}:
      Member.Of(s, g, m)
    case Con{h, r}:
      Member.Of(s, g, Member.Group{h}) & VendNode.Chain(s, h, r, m)

# setting the members of g to a list with m closes a cycle: m is a group, and
# when it is not g, g is inside it
def Member.Closes(s: VendNode.State, g: Group, m: Member) -> Type:
  match m:
    case Member.VendNode{n}:
      Empty
    case Member.Group{h}:
      {h != g: Group} -> {VendNode.is_inside(s, Member.Group{g}, h) == True{}: Bool}

# a and b hold the same content, for every resource at every point
def VendNode.SameContent(a: VendNode.State, b: VendNode.State) -> Type:
  @n: Resources.Name -> @p: Point -> {
    VendNode.get_content(a, n, p) == VendNode.get_content(b, n, p): Maybe<&2, Octets.Bytes()>
  }

# a change keeps every version that existed, with its content
law history_kept:
  for s: VendNode.State
  for e: Envelope
  for q: Ask
  for t: VendNode.State
  for a: Answer
  for n: Resources.Name
  for v: Version
  for x: Octets.Bytes()
  {
    VendNode.ask(s, e, q) == (t, a): VendNode.State & Answer
  } -> {
    VendNode.get_content(s, n, Point.At{v}) == Some{x}: Maybe<&2, Octets.Bytes()>
  } -> {VendNode.get_content(t, n, Point.At{v}) == Some{x}: Maybe<&2, Octets.Bytes()>}

# a change sent again with the same request ID gives the same answer and
# changes nothing more
law retry_is_safe:
  for s: VendNode.State
  for r: RequestId
  for w: Writer
  for t1: Time
  for t2: Time
  for q: Ask
  for s1: VendNode.State
  for a1: Answer
  {
    VendNode.ask(s, Envelope{r, w, t1}, q) == (s1, a1): VendNode.State & Answer
  } -> {VendNode.ask(s1, Envelope{r, w, t2}, q) == (s1, a1): VendNode.State & Answer}

# on the owner, a new request that writes bytes on the head answers Written
law write_at_head_is_written:
  for s: VendNode.State
  for r: RequestId
  for w: Writer
  for time: Time
  for n: Resources.Name
  for b: Branch
  for v: Version
  for x: Octets.Bytes()
  exs t: VendNode.State
  exs u: Version
  {
    VendNode.is_owner(s, b) == True{}: Bool
  } -> {
    VendNode.get_head(s, b) == Some{v}: Maybe<&2, Version>
  } -> {
    VendNode.get_outcome(s, r) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      Envelope{r, w, time},
      Ask.Write{n, b, Some{v}, Content.Bytes{x}}
    )
      == (t, Answer.Write{Write.Written{u}}): VendNode.State
      & Answer
  }

# after a write answers Written, the head of the branch holds the bytes
law read_after_write:
  for s: VendNode.State
  for e: Envelope
  for n: Resources.Name
  for b: Branch
  for base: Maybe<&2, Version>
  for x: Octets.Bytes()
  for t: VendNode.State
  for v: Version
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.Write{n, b, base, Content.Bytes{x}}
    )
      == (t, Answer.Write{Write.Written{v}}): VendNode.State
      & Answer
  } -> {VendNode.get_content(t, n, Point.Head{b}) == Some{x}: Maybe<&2, Octets.Bytes()>}

# a stale write changes no content, and its base is not the current version
law stale_changes_nothing:
  for s: VendNode.State
  for e: Envelope
  for n: Resources.Name
  for b: Branch
  for base: Maybe<&2, Version>
  for x: Content
  for t: VendNode.State
  for current: Version
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.Write{n, b, base, x}
    )
      == (t, Answer.Write{Write.Stale{current}}): VendNode.State
      & Answer
  } -> VendNode.SameContent(t, s)
    & {base != Some{current}: Maybe<&2, Version>}

# when c starts from b, and each then writes a different resource, merging c
# into b answers Merged and keeps both writes
law merge_disjoint_keeps_both:
  for s: VendNode.State
  for s1: VendNode.State
  for s2: VendNode.State
  for s3: VendNode.State
  for s4: VendNode.State
  for a4: Answer
  for e1: Envelope
  for e2: Envelope
  for e3: Envelope
  for e4: Envelope
  for b: Branch
  for c: Branch
  for n1: Resources.Name
  for n2: Resources.Name
  for base1: Maybe<&2, Version>
  for base2: Maybe<&2, Version>
  for x1: Octets.Bytes()
  for x2: Octets.Bytes()
  for v0: Version
  for v1: Version
  for v2: Version
  exs v3: Version
  {
    VendNode.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s1, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s2, Envelope.id(e3)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s3, Envelope.id(e4)) == Outcome.NotSeen{}: Outcome
  } -> {
    n1 != n2: Resources.Name
  } -> {
    VendNode.ask(
      s,
      e1,
      Ask.SetBranch{c, Point.Head{b}}
    )
      == (s1, Answer.SetBranch{SetBranch.Created{v0}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      s1,
      e2,
      Ask.Write{n1, b, base1, Content.Bytes{x1}}
    )
      == (s2, Answer.Write{Write.Written{v1}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      s2,
      e3,
      Ask.Write{n2, c, base2, Content.Bytes{x2}}
    )
      == (s3, Answer.Write{Write.Written{v2}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(s3, e4, Ask.Merge{Point.Head{c}, b}) == (s4, a4): VendNode.State & Answer
  } -> {
    a4 == Answer.Merge{Merge.Merged{v3}}: Answer
  }
    & {VendNode.get_content(s4, n1, Point.Head{b}) == Some{x1}: Maybe<&2, Octets.Bytes()>}
    & {VendNode.get_content(s4, n2, Point.Head{b}) == Some{x2}: Maybe<&2, Octets.Bytes()>}

# a merge that conflicts changes no content, and stores the conflict as the
# one new conflict notice of the branch
law conflict_changes_nothing:
  for s: VendNode.State
  for e: Envelope
  for p: Point
  for b: Branch
  for t: VendNode.State
  for k: Conflict
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.Merge{p, b}
    )
      == (t, Answer.Merge{Merge.Conflicted{k}}): VendNode.State
      & Answer
  } -> VendNode.SameContent(
    t,
    s
  )
    & {
      VendNode.get_changes(
        t,
        Topic.Conflicts{b},
        Some{VendNode.position(s)}
      )
        == [Notice.Conflicted{k}]: List<&2, Notice>
    }

# after the group g is set to ms, its members are exactly ms
law members_after_set:
  for s: VendNode.State
  for e: Envelope
  for g: Group
  for ms: List<&2, Member>
  for t: VendNode.State
  for x: Epoch
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.SetGroup{g, ms}
    )
      == (t, Answer.SetGroup{SetGroup.Set{x}}): VendNode.State
      & Answer
  } -> {VendNode.get_members(t, g) == Some{ms}: Maybe<&2, List<&2, Member>>}

# setting the group g leaves the members of every other group
law set_keeps_others:
  for s: VendNode.State
  for e: Envelope
  for g: Group
  for h: Group
  for ms: List<&2, Member>
  for t: VendNode.State
  for a: Answer
  {
    VendNode.ask(s, e, Ask.SetGroup{g, ms}) == (t, a): VendNode.State & Answer
  } -> {
    h != g: Group
  } -> {VendNode.get_members(t, h) == VendNode.get_members(s, h): Maybe<&2, List<&2, Member>>}

# what is inside a group that is inside g is inside g
law inside_through:
  for s: VendNode.State
  for m: Member
  for h: Group
  for g: Group
  {
    VendNode.is_inside(s, Member.Group{h}, g) == True{}: Bool
  } -> {
    VendNode.is_inside(s, m, h) == True{}: Bool
  } -> {VendNode.is_inside(s, m, g) == True{}: Bool}

# m is inside g exactly when a chain of groups leads from g to m
law inside_has_chain:
  for s: VendNode.State
  for m: Member
  for g: Group
  {
    VendNode.is_inside(s, m, g) == True{}: Bool
  } -> &ps: List<&2, Group> -> VendNode.Chain(s, g, ps, m)

law chain_is_inside:
  for s: VendNode.State
  for g: Group
  for ps: List<&2, Group>
  for m: Member
  VendNode.Chain(s, g, ps, m) -> {VendNode.is_inside(s, m, g) == True{}: Bool}

# a set-group answers Cycle exactly when one of its members closes a cycle
law cycle_has_closer:
  for s: VendNode.State
  for e: Envelope
  for g: Group
  for ms: List<&2, Member>
  for t: VendNode.State
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.SetGroup{g, ms}
    )
      == (t, Answer.SetGroup{SetGroup.Cycle{}}): VendNode.State
      & Answer
  } -> &m: Member -> Member.Among(m, ms)
    & Member.Closes(s, g, m)

law closer_is_cycle:
  for s: VendNode.State
  for e: Envelope
  for g: Group
  for ms: List<&2, Member>
  for m: Member
  for t: VendNode.State
  for a: Answer
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> Member.Among(
    m,
    ms
  ) -> Member.Closes(
    s,
    g,
    m
  ) -> {
    VendNode.ask(s, e, Ask.SetGroup{g, ms}) == (t, a): VendNode.State & Answer
  } -> {a == Answer.SetGroup{SetGroup.Cycle{}}: Answer}

# no group is inside itself at the start
law none_inside_itself_at_start:
  for n: VendNode
  for g: Group
  {VendNode.is_inside(VendNode.empty(n), Member.Group{g}, g) == False{}: Bool}

# a change made on this node keeps every group outside itself. A sync does
# not: when two nodes set groups before they meet, the groups that win on each
# may hold one another. Refusing those would cost a search of the whole group
# graph on every sync, and the nodes could still keep different groups. So a
# sync takes the winning groups as they are, and notices the cycle
# (GroupCycle): inside stays well defined, and the groups on a cycle hold the
# same members. groups_converge is what that buys.
law none_inside_itself_after:
  for s: VendNode.State
  for e: Envelope
  for q: Ask
  for t: VendNode.State
  for a: Answer
  for g: Group
  {
    VendNode.ask(s, e, q) == (t, a): VendNode.State & Answer
  } -> {
    Ask.local(q) == True{}: Bool
  } -> (
    @h: Group -> {VendNode.is_inside(s, Member.Group{h}, h) == False{}: Bool}
  ) -> {VendNode.is_inside(t, Member.Group{g}, g) == False{}: Bool}

# setting an owner group gives the branch a larger epoch
law epoch_grows:
  for s: VendNode.State
  for e: Envelope
  for b: Branch
  for g: Group
  for t: VendNode.State
  for old: Epoch
  for new: Epoch
  {
    VendNode.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_epoch(s, b) == Some{old}: Maybe<&2, Epoch>
  } -> {
    VendNode.ask(
      s,
      e,
      Ask.SetOwner{b, g}
    )
      == (t, Answer.SetOwner{SetOwner.Set{new}}): VendNode.State
      & Answer
  } -> {
    Nat.is_lt(Epoch.number(old), Epoch.number(new)) == True{}: Bool
  }
    & {VendNode.get_epoch(t, b) == Some{new}: Maybe<&2, Epoch>}

# after a takes in b, and b takes in that, both hold the same content
law sync_converges:
  for a: VendNode.State
  for b: VendNode.State
  for a1: VendNode.State
  for b1: VendNode.State
  for e1: Envelope
  for e2: Envelope
  {
    VendNode.get_outcome(a, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(b, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      a,
      e1,
      Ask.Sync{b, None{}}
    )
      == (a1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      b,
      e2,
      Ask.Sync{a1, None{}}
    )
      == (b1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> VendNode.SameContent(a1, b1)

# after a takes in b, and b takes in that, both hold the same groups: each
# group has the members of its larger stamp (its epoch, then its members)
law groups_converge:
  for a: VendNode.State
  for b: VendNode.State
  for a1: VendNode.State
  for b1: VendNode.State
  for e1: Envelope
  for e2: Envelope
  for g: Group
  {
    VendNode.get_outcome(a, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(b, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      a,
      e1,
      Ask.Sync{b, None{}}
    )
      == (a1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      b,
      e2,
      Ask.Sync{a1, None{}}
    )
      == (b1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {VendNode.get_members(a1, g) == VendNode.get_members(b1, g): Maybe<&2, List<&2, Member>>}

# taking in a then b holds the same content as taking in b then a
law sync_commutes:
  for s: VendNode.State
  for a: VendNode.State
  for b: VendNode.State
  for s1: VendNode.State
  for s2: VendNode.State
  for s3: VendNode.State
  for s4: VendNode.State
  for e1: Envelope
  for e2: Envelope
  for e3: Envelope
  for e4: Envelope
  {
    VendNode.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s1, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s, Envelope.id(e3)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.get_outcome(s3, Envelope.id(e4)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e1,
      Ask.Sync{a, None{}}
    )
      == (s1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      s1,
      e2,
      Ask.Sync{b, None{}}
    )
      == (s2, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      s,
      e3,
      Ask.Sync{b, None{}}
    )
      == (s3, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(
      s3,
      e4,
      Ask.Sync{a, None{}}
    )
      == (s4, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> VendNode.SameContent(s2, s4)

# taking in the same node twice holds the same content as once
law sync_idempotent:
  for s: VendNode.State
  for a: VendNode.State
  for s1: VendNode.State
  for s2: VendNode.State
  for a2: Answer
  for e1: Envelope
  for e2: Envelope
  {
    VendNode.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    VendNode.ask(
      s,
      e1,
      Ask.Sync{a, None{}}
    )
      == (s1, Answer.Sync{Sync.Synced{}}): VendNode.State
      & Answer
  } -> {
    VendNode.ask(s1, e2, Ask.Sync{a, None{}}) == (s2, a2): VendNode.State & Answer
  } -> VendNode.SameContent(s2, s1)

# the notices after a change are the notices before it, then the notices
# since it: none is missed or doubled between polls
law since_splits:
  for s: VendNode.State
  for e: Envelope
  for q: Ask
  for t: VendNode.State
  for a: Answer
  for k: Topic
  {
    VendNode.ask(s, e, q) == (t, a): VendNode.State & Answer
  } -> {
    VendNode.get_changes(
      t,
      k,
      None{}
    )
      == List.append(
        &2,
        Notice,
        VendNode.get_changes(s, k, None{}),
        VendNode.get_changes(t, k, Some{VendNode.position(s)})
      ): List<&2, Notice>
  }
