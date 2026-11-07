import Base

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API). Bytes are List<&2, U32>, as in Base.

# Names
# -----

# a Vend Node
law Node:
  Data

# the node that t names
law Node.read:
  for t: String
  Maybe<&2, Node>

# the text of n
law Node.show:
  for n: Node
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

# a resource name: a space and a path in it
law Name:
  Data

# the name that t names
law Name.read:
  for t: String
  Maybe<&2, Name>

# the text of n
law Name.show:
  for n: Name
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
  Content.Bytes{bytes: List<&2, U32>}
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
  Member.Node{node: Node}
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

# an event of a topic. GroupKept: a sync kept this node's members of the group,
# since the other node's members would close a cycle; a set-group settles it.
# MarkMoved: a sync met the same mark of another node, on another version, and
# the smaller version won on both nodes
type Notice is Data:
  Notice.Touched{touch: Touch}
  Notice.Conflicted{conflict: Conflict}
  Notice.Versioned{branch: Branch, version: Version}
  Notice.GroupKept{group: Group, members: List<&2, Member>}
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
  Resolve.Left{names: List<&2, Name>}
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
# read, or Node.ask for a change. Mounts, stops and connections have none:
# their behavior is IO.

# what a node holds
law Node.State:
  Data

# the node n, holding nothing yet
law Node.empty:
  for n: Node
  Node.State

# the position of s, to start from with "since"
law Node.position:
  for s: Node.State
  Position

# every branch of s
law Node.get_branches:
  for s: Node.State
  List<&2, BranchEntry>

# the versions of the resource n on the branch b
law Node.get_log:
  for s: Node.State
  for n: Name
  for b: Branch
  List<&2, LogEntry>

# the bytes of the resource n at the point p, if it is there
law Node.get_content:
  for s: Node.State
  for n: Name
  for p: Point
  Maybe<&2, List<&2, U32>>

# what changed in the resource n from the point a to the point b
law Node.get_diff:
  for s: Node.State
  for n: Name
  for a: Point
  for b: Point
  List<&2, Change>

# the changes elsewhere that touch what the branch b uses
law Node.get_affects:
  for s: Node.State
  for b: Branch
  List<&2, Touch>

# what the changes up to the point p touch elsewhere
law Node.get_impact:
  for s: Node.State
  for p: Point
  List<&2, Touch>

# whether the request r happened
law Node.get_outcome:
  for s: Node.State
  for r: RequestId
  Outcome

# the notices of the topic t since the position p (from the start without
# one)
law Node.get_changes:
  for s: Node.State
  for t: Topic
  for p: Maybe<&2, Position>
  List<&2, Notice>

# a change that a node can be asked for
type Ask is Data:
  Ask.Write{name: Name, branch: Branch, base: Maybe<&2, Version>, content: Content}
  Ask.SetBranch{branch: Branch, point: Point}
  Ask.CreateMark{branch: Branch, mark: Mark, message: String}
  Ask.Merge{point: Point, branch: Branch}
  Ask.Resolve{conflict: Conflict, name: Name, content: Content}
  Ask.SetOwner{branch: Branch, group: Group}
  Ask.SetGroup{group: Group, members: List<&2, Member>}
  Ask.Sync{other: Node.State, since: Maybe<&2, Position>}

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
law Node.ask:
  for s: Node.State
  for e: Envelope
  for q: Ask
  Node.State & Answer

# the epoch of the owner group of the branch b, if b exists
law Node.get_epoch:
  for s: Node.State
  for b: Branch
  Maybe<&2, Epoch>

# the number of e: a later epoch has a larger one
law Epoch.number:
  for e: Epoch
  Nat

# the newest version of the branch b, if b exists
law Node.get_head:
  for s: Node.State
  for b: Branch
  Maybe<&2, Version>

# the node of s is in the owner group of the branch b
law Node.is_owner:
  for s: Node.State
  for b: Branch
  Bool

# m is a member of the group g, or of a group inside g
law Node.is_inside:
  for s: Node.State
  for m: Member
  for g: Group
  Bool

# Laws
# ----

# a and b hold the same content, for every resource at every point
def Node.SameContent(a: Node.State, b: Node.State) -> Type:
  @n: Name -> @p: Point -> {
    Node.get_content(a, n, p) == Node.get_content(b, n, p): Maybe<&2, List<&2, U32>>
  }

# a change keeps every version that existed, with its content
law history_kept:
  for s: Node.State
  for e: Envelope
  for q: Ask
  for t: Node.State
  for a: Answer
  for n: Name
  for v: Version
  for x: List<&2, U32>
  {
    Node.ask(s, e, q) == (t, a): Node.State & Answer
  } -> {
    Node.get_content(s, n, Point.At{v}) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {Node.get_content(t, n, Point.At{v}) == Some{x}: Maybe<&2, List<&2, U32>>}

# a change sent again with the same request ID gives the same answer and
# changes nothing more
law retry_is_safe:
  for s: Node.State
  for r: RequestId
  for w: Writer
  for t1: Time
  for t2: Time
  for q: Ask
  for s1: Node.State
  for a1: Answer
  {
    Node.ask(s, Envelope{r, w, t1}, q) == (s1, a1): Node.State & Answer
  } -> {Node.ask(s1, Envelope{r, w, t2}, q) == (s1, a1): Node.State & Answer}

# on the owner, a new request that writes bytes on the head answers Written
law write_at_head_is_written:
  for s: Node.State
  for r: RequestId
  for w: Writer
  for time: Time
  for n: Name
  for b: Branch
  for v: Version
  for x: List<&2, U32>
  exs t: Node.State
  exs u: Version
  {
    Node.is_owner(s, b) == True{}: Bool
  } -> {
    Node.get_head(s, b) == Some{v}: Maybe<&2, Version>
  } -> {
    Node.get_outcome(s, r) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(
      s,
      Envelope{r, w, time},
      Ask.Write{n, b, Some{v}, Content.Bytes{x}}
    )
      == (t, Answer.Write{Write.Written{u}}): Node.State
      & Answer
  }

# after a write answers Written, the head of the branch holds the bytes
law read_after_write:
  for s: Node.State
  for e: Envelope
  for n: Name
  for b: Branch
  for base: Maybe<&2, Version>
  for x: List<&2, U32>
  for t: Node.State
  for v: Version
  {
    Node.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(
      s,
      e,
      Ask.Write{n, b, base, Content.Bytes{x}}
    )
      == (t, Answer.Write{Write.Written{v}}): Node.State
      & Answer
  } -> {Node.get_content(t, n, Point.Head{b}) == Some{x}: Maybe<&2, List<&2, U32>>}

# a stale write changes no content, and its base is not the current version
law stale_changes_nothing:
  for s: Node.State
  for e: Envelope
  for n: Name
  for b: Branch
  for base: Maybe<&2, Version>
  for x: Content
  for t: Node.State
  for current: Version
  {
    Node.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(
      s,
      e,
      Ask.Write{n, b, base, x}
    )
      == (t, Answer.Write{Write.Stale{current}}): Node.State
      & Answer
  } -> Node.SameContent(t, s)
    & {base != Some{current}: Maybe<&2, Version>}

# when c starts from b, and each then writes a different resource, merging c
# into b answers Merged and keeps both writes
law merge_disjoint_keeps_both:
  for s: Node.State
  for s1: Node.State
  for s2: Node.State
  for s3: Node.State
  for s4: Node.State
  for a4: Answer
  for e1: Envelope
  for e2: Envelope
  for e3: Envelope
  for e4: Envelope
  for b: Branch
  for c: Branch
  for n1: Name
  for n2: Name
  for base1: Maybe<&2, Version>
  for base2: Maybe<&2, Version>
  for x1: List<&2, U32>
  for x2: List<&2, U32>
  for v0: Version
  for v1: Version
  for v2: Version
  exs v3: Version
  {
    Node.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s1, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s2, Envelope.id(e3)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s3, Envelope.id(e4)) == Outcome.NotSeen{}: Outcome
  } -> {
    n1 != n2: Name
  } -> {
    Node.ask(
      s,
      e1,
      Ask.SetBranch{c, Point.Head{b}}
    )
      == (s1, Answer.SetBranch{SetBranch.Created{v0}}): Node.State
      & Answer
  } -> {
    Node.ask(
      s1,
      e2,
      Ask.Write{n1, b, base1, Content.Bytes{x1}}
    )
      == (s2, Answer.Write{Write.Written{v1}}): Node.State
      & Answer
  } -> {
    Node.ask(
      s2,
      e3,
      Ask.Write{n2, c, base2, Content.Bytes{x2}}
    )
      == (s3, Answer.Write{Write.Written{v2}}): Node.State
      & Answer
  } -> {
    Node.ask(s3, e4, Ask.Merge{Point.Head{c}, b}) == (s4, a4): Node.State & Answer
  } -> {
    a4 == Answer.Merge{Merge.Merged{v3}}: Answer
  }
    & {Node.get_content(s4, n1, Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>}
    & {Node.get_content(s4, n2, Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}

# a merge that conflicts changes no content, and stores the conflict as the
# one new conflict notice of the branch
law conflict_changes_nothing:
  for s: Node.State
  for e: Envelope
  for p: Point
  for b: Branch
  for t: Node.State
  for k: Conflict
  {
    Node.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(s, e, Ask.Merge{p, b}) == (t, Answer.Merge{Merge.Conflicted{k}}): Node.State & Answer
  } -> Node.SameContent(
    t,
    s
  )
    & {
      Node.get_changes(
        t,
        Topic.Conflicts{b},
        Some{Node.position(s)}
      )
        == [Notice.Conflicted{k}]: List<&2, Notice>
    }

# after a group is set, each member is inside it
law inside_after_set:
  for s: Node.State
  for e: Envelope
  for g: Group
  for m: Member
  for ms: List<&2, Member>
  for t: Node.State
  for x: Epoch
  {
    Node.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(
      s,
      e,
      Ask.SetGroup{g, m <> ms}
    )
      == (t, Answer.SetGroup{SetGroup.Set{x}}): Node.State
      & Answer
  } -> {Node.is_inside(t, m, g) == True{}: Bool}

# what is inside a group that is inside g is inside g
law inside_through:
  for s: Node.State
  for m: Member
  for h: Group
  for g: Group
  {
    Node.is_inside(s, Member.Group{h}, g) == True{}: Bool
  } -> {Node.is_inside(s, m, h) == True{}: Bool} -> {Node.is_inside(s, m, g) == True{}: Bool}

# no group is inside itself at the start
law none_inside_itself_at_start:
  for n: Node
  for g: Group
  {Node.is_inside(Node.empty(n), Member.Group{g}, g) == False{}: Bool}

# a change keeps every group outside itself
law none_inside_itself_after:
  for s: Node.State
  for e: Envelope
  for q: Ask
  for t: Node.State
  for a: Answer
  for g: Group
  {
    Node.ask(s, e, q) == (t, a): Node.State & Answer
  } -> (
    @h: Group -> {Node.is_inside(s, Member.Group{h}, h) == False{}: Bool}
  ) -> {Node.is_inside(t, Member.Group{g}, g) == False{}: Bool}

# setting an owner group gives the branch a larger epoch
law epoch_grows:
  for s: Node.State
  for e: Envelope
  for b: Branch
  for g: Group
  for t: Node.State
  for old: Epoch
  for new: Epoch
  {
    Node.get_outcome(s, Envelope.id(e)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_epoch(s, b) == Some{old}: Maybe<&2, Epoch>
  } -> {
    Node.ask(
      s,
      e,
      Ask.SetOwner{b, g}
    )
      == (t, Answer.SetOwner{SetOwner.Set{new}}): Node.State
      & Answer
  } -> {
    Nat.is_lt(Epoch.number(old), Epoch.number(new)) == True{}: Bool
  }
    & {Node.get_epoch(t, b) == Some{new}: Maybe<&2, Epoch>}

# after a takes in b, and b takes in that, both hold the same content
law sync_converges:
  for a: Node.State
  for b: Node.State
  for a1: Node.State
  for b1: Node.State
  for e1: Envelope
  for e2: Envelope
  {
    Node.get_outcome(a, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(b, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(a, e1, Ask.Sync{b, None{}}) == (a1, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> {
    Node.ask(b, e2, Ask.Sync{a1, None{}}) == (b1, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> Node.SameContent(a1, b1)

# taking in a then b holds the same content as taking in b then a
law sync_commutes:
  for s: Node.State
  for a: Node.State
  for b: Node.State
  for s1: Node.State
  for s2: Node.State
  for s3: Node.State
  for s4: Node.State
  for e1: Envelope
  for e2: Envelope
  for e3: Envelope
  for e4: Envelope
  {
    Node.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s1, Envelope.id(e2)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s, Envelope.id(e3)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.get_outcome(s3, Envelope.id(e4)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(s, e1, Ask.Sync{a, None{}}) == (s1, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> {
    Node.ask(s1, e2, Ask.Sync{b, None{}}) == (s2, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> {
    Node.ask(s, e3, Ask.Sync{b, None{}}) == (s3, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> {
    Node.ask(s3, e4, Ask.Sync{a, None{}}) == (s4, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> Node.SameContent(s2, s4)

# taking in the same node twice holds the same content as once
law sync_idempotent:
  for s: Node.State
  for a: Node.State
  for s1: Node.State
  for s2: Node.State
  for a2: Answer
  for e1: Envelope
  for e2: Envelope
  {
    Node.get_outcome(s, Envelope.id(e1)) == Outcome.NotSeen{}: Outcome
  } -> {
    Node.ask(s, e1, Ask.Sync{a, None{}}) == (s1, Answer.Sync{Sync.Synced{}}): Node.State & Answer
  } -> {
    Node.ask(s1, e2, Ask.Sync{a, None{}}) == (s2, a2): Node.State & Answer
  } -> Node.SameContent(s2, s1)

# the notices after a change are the notices before it, then the notices
# since it: none is missed or doubled between polls
law since_splits:
  for s: Node.State
  for e: Envelope
  for q: Ask
  for t: Node.State
  for a: Answer
  for k: Topic
  {
    Node.ask(s, e, q) == (t, a): Node.State & Answer
  } -> {
    Node.get_changes(
      t,
      k,
      None{}
    )
      == List.append(
        &2,
        Notice,
        Node.get_changes(s, k, None{}),
        Node.get_changes(t, k, Some{Node.position(s)})
      ): List<&2, Notice>
  }
