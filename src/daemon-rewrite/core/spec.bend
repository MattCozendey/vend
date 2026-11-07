import Base

# The public API of a Vend Node (README, Public API). Every front offers
# exactly these operations. Bytes are List<&2, U32>, as in Base.

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

# a URI
law Uri:
  Data

# the URI that t names
law Uri.read:
  for t: String
  Maybe<&2, Uri>

# the text of u
law Uri.show:
  for u: Uri
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

# where new content comes from: bytes, a resource, or an old version
type Content is Data:
  Content.Bytes{bytes: List<&2, U32>}
  Content.From{uri: Uri}
  Content.Of{version: Version}

# a member of an owner group
type Member is Data:
  Member.Node{node: Node}
  Member.Group{group: Group}

# what a subscription or a poll follows, on a branch
type Topic is Data:
  Topic.Affects{branch: Branch}
  Topic.Conflicts{branch: Branch}
  Topic.Versions{branch: Branch}

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

# what a node holds
law Status:
  Data

# the mounted resources
law Status.mounts:
  for s: Status
  List<&2, Uri>

# the writers that are connected
law Status.writers:
  for s: Status
  List<&2, Writer>

# the branches that this node's groups own
law Status.owned:
  for s: Status
  List<&2, Branch>

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

# an event of a topic
type Notice is Data:
  Notice.Touched{touch: Touch}
  Notice.Conflicted{conflict: Conflict}
  Notice.Versioned{branch: Branch, version: Version}

# Answers
# -------

# an answer that crossed IO: delivered at a position, or not delivered
type Reply<a, -A: Kind(a)> is Kind(a):
  Reply.Delivered{at: Position, answer: A}
  Reply.TimedOut{}
  Reply.Unreachable{}

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

type CreateMark is Data:
  CreateMark.Marked{mark: Mark}
  CreateMark.Taken{}

type Merge is Data:
  Merge.Merged{version: Version}
  Merge.Conflicted{conflict: Conflict}
  Merge.Stale{current: Version}

type Resolve is Data:
  Resolve.Resolved{version: Version}
  Resolve.Stale{current: Version}

# Partial: the submodules in missing could not be fetched. Unsupported: the
# kind of the resource does not support a setting
type Mount is Data:
  Mount.Mounted{}
  Mount.Partial{missing: List<&2, Space>}
  Mount.Unsupported{why: String}
  Mount.Refused{why: String}

type Unmount is Data:
  Unmount.Unmounted{}
  Unmount.NotMounted{}

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

# Refused: without force, while mounts are active or other writers are
# connected
type Stop is Data:
  Stop.Stopped{}
  Stop.Refused{why: String}

# Busy: another node holds the store
type Start is Data:
  Start.Ended{}
  Start.Busy{}
  Start.Refused{why: String}

# Operations
# ----------

# a connection to a node, as one writer
law Client:
  Type

# a live stream of the notices of a topic
law Subscription:
  Type

# runs a node on the store at store, until a stop
law Node.try_start_or_resume:
  for store: Uri
  IO(Start)

# a connection to the node at node, as writer
law Client.try_open:
  for node: Uri
  for writer: Writer
  IO(Reply<&1, Client>)

# ends the connection c
law Client.try_close:
  for c: Client
  IO(Reply<&2, Unit>)

# what the node holds
law Client.try_get_status:
  for c: Client
  IO(Client & Reply<&2, Status>)

# every branch
law Client.try_get_branches:
  for c: Client
  IO(Client & Reply<&2, List<&2, BranchEntry>>)

# the versions of the resource n on the branch b
law Client.try_get_log:
  for c: Client
  for n: Name
  for b: Branch
  IO(Client & Reply<&2, List<&2, LogEntry>>)

# the bytes of the resource n at the point p
law Client.try_get_content:
  for c: Client
  for n: Name
  for p: Point
  IO(Client & Reply<&2, List<&2, U32>>)

# what changed in the resource n from the point a to the point b
law Client.try_get_diff:
  for c: Client
  for n: Name
  for a: Point
  for b: Point
  IO(Client & Reply<&2, List<&2, Change>>)

# the changes elsewhere that touch what the branch b uses
law Client.try_get_affects:
  for c: Client
  for b: Branch
  IO(Client & Reply<&2, List<&2, Touch>>)

# what the changes up to the point p touch elsewhere
law Client.try_get_impact:
  for c: Client
  for p: Point
  IO(Client & Reply<&2, List<&2, Touch>>)

# whether the request r happened
law Client.try_get_outcome:
  for c: Client
  for r: RequestId
  IO(Client & Reply<&2, Outcome>)

# the notices of the topic t since the position s (from the start without one)
law Client.try_get_changes:
  for c: Client
  for t: Topic
  for s: Maybe<&2, Position>
  IO(Client & Reply<&2, List<&2, Notice>>)

# writes the content x to the resource n on the branch b, based on the
# version base (none for a new resource)
law Client.try_write:
  for c: Client
  for r: RequestId
  for n: Name
  for b: Branch
  for base: Maybe<&2, Version>
  for x: Content
  IO(Client & Reply<&2, Write>)

# makes the branch b at the point p or, when b exists, records a new version
# of b that equals p, with its submodules
law Client.try_set_branch:
  for c: Client
  for r: RequestId
  for b: Branch
  for p: Point
  IO(Client & Reply<&2, SetBranch>)

# names the newest point of the branch b as the mark m, with the message t
law Client.try_create_mark:
  for c: Client
  for r: RequestId
  for b: Branch
  for m: Mark
  for t: String
  IO(Client & Reply<&2, CreateMark>)

# merges the point p into the branch b, item by item
law Client.try_merge:
  for c: Client
  for r: RequestId
  for p: Point
  for b: Branch
  IO(Client & Reply<&2, Merge>)

# settles the conflict k with the content x
law Client.try_resolve:
  for c: Client
  for r: RequestId
  for k: Conflict
  for x: Content
  IO(Client & Reply<&2, Resolve>)

# ties the resource u to the branch b, with the settings ss that the kind of
# u reads, and fills u when it is empty; when u is mounted, sets its settings
# and branch
law Client.try_mount:
  for c: Client
  for r: RequestId
  for u: Uri
  for ss: List<&2, String>
  for b: Branch
  IO(Client & Reply<&2, Mount>)

# stops versioning u
law Client.try_unmount:
  for c: Client
  for r: RequestId
  for u: Uri
  IO(Client & Reply<&2, Unmount>)

# sets the owner group of the branch b to g
law Client.try_set_owner:
  for c: Client
  for r: RequestId
  for b: Branch
  for g: Group
  IO(Client & Reply<&2, SetOwner>)

# makes the group g with the members ms or, when g exists, replaces its
# members
law Client.try_set_group:
  for c: Client
  for r: RequestId
  for g: Group
  for ms: List<&2, Member>
  IO(Client & Reply<&2, SetGroup>)

# swaps history with the node n, since the position s (all without one)
law Client.try_sync:
  for c: Client
  for r: RequestId
  for n: Node
  for s: Maybe<&2, Position>
  IO(Client & Reply<&2, Sync>)

# stops the node; force stops it even with mounts or other writers
law Client.try_stop:
  for c: Client
  for r: RequestId
  for force: Bool
  IO(Client & Reply<&2, Stop>)

# a live stream of the notices of the topic t since the position s (from now
# without one)
law Client.try_subscribe:
  for c: Client
  for t: Topic
  for s: Maybe<&2, Position>
  IO(Client & Reply<&1, Subscription>)

# the next notice of the stream x
law Subscription.try_next:
  for x: Subscription
  IO(Subscription & Reply<&2, Notice>)

# ends the stream x
law Subscription.try_close:
  for x: Subscription
  IO(Reply<&2, Unit>)
