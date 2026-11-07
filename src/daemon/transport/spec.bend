import Base
import ../../shared/bytes.bend as Octets
import ../../shared/uris.bend as Uris
import ../core/spec.bend as Core

# The public API of a Vend Node (README, Public API): the core, carried over
# IO. Every front offers exactly these operations.

# Values that callers make
# ------------------------

# where new content comes from: content, or a resource that the node reads
# first
type Source is Data:
  Source.Content{content: Core.Content}
  Source.From{uri: Uris.Uri}

# Answers
# -------

# an answer that crossed IO: delivered at a position, or not delivered
type Reply<a, -A: Kind(a)> is Kind(a):
  Reply.Delivered{at: Core.Position, answer: A}
  Reply.TimedOut{}
  Reply.Unreachable{}

# what a running node reports
law Status:
  Data

# the mounted resources
law Status.mounts:
  for s: Status
  List<&2, Uris.Uri>

# the writers that are connected
law Status.writers:
  for s: Status
  List<&2, Core.Writer>

# the branches that this node's groups own
law Status.owned:
  for s: Status
  List<&2, Core.Branch>

# Partial: the submodules in missing could not be fetched. Unsupported: the
# kind of the resource does not support a setting
type Mount is Data:
  Mount.Mounted{}
  Mount.Partial{missing: List<&2, Core.Space>}
  Mount.Unsupported{why: String}
  Mount.Refused{why: String}

type Unmount is Data:
  Unmount.Unmounted{}
  Unmount.NotMounted{}

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
  for store: Uris.Uri
  IO(Start)

# a connection to the node at node, as writer
law Client.try_open:
  for node: Uris.Uri
  for writer: Core.Writer
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
  IO(Client & Reply<&2, List<&2, Core.BranchEntry>>)

# the versions of the resource n on the branch b
law Client.try_get_log:
  for c: Client
  for n: Core.Name
  for b: Core.Branch
  IO(Client & Reply<&2, List<&2, Core.LogEntry>>)

# the bytes of the resource n at the point p, if it is there
law Client.try_get_content:
  for c: Client
  for n: Core.Name
  for p: Core.Point
  IO(Client & Reply<&2, Maybe<&2, Octets.Bytes()>>)

# what changed in the resource n from the point a to the point b
law Client.try_get_diff:
  for c: Client
  for n: Core.Name
  for a: Core.Point
  for b: Core.Point
  IO(Client & Reply<&2, List<&2, Core.Change>>)

# the changes elsewhere that touch what the branch b uses
law Client.try_get_affects:
  for c: Client
  for b: Core.Branch
  IO(Client & Reply<&2, List<&2, Core.Touch>>)

# what the changes up to the point p touch elsewhere
law Client.try_get_impact:
  for c: Client
  for p: Core.Point
  IO(Client & Reply<&2, List<&2, Core.Touch>>)

# whether the request r happened
law Client.try_get_outcome:
  for c: Client
  for r: Core.RequestId
  IO(Client & Reply<&2, Core.Outcome>)

# the notices of the topic t since the position s (from the start without one)
law Client.try_get_changes:
  for c: Client
  for t: Core.Topic
  for s: Maybe<&2, Core.Position>
  IO(Client & Reply<&2, List<&2, Core.Notice>>)

# writes the content x to the resource n on the branch b, based on the
# version base (none for a new resource)
law Client.try_write:
  for c: Client
  for r: Core.RequestId
  for n: Core.Name
  for b: Core.Branch
  for base: Maybe<&2, Core.Version>
  for x: Source
  IO(Client & Reply<&2, Core.Write>)

# makes the branch b at the point p or, when b exists, records a new version
# of b that equals p, with its submodules
law Client.try_set_branch:
  for c: Client
  for r: Core.RequestId
  for b: Core.Branch
  for p: Core.Point
  IO(Client & Reply<&2, Core.SetBranch>)

# names the newest point of the branch b as the mark m, with the message t
law Client.try_create_mark:
  for c: Client
  for r: Core.RequestId
  for b: Core.Branch
  for m: Core.Mark
  for t: String
  IO(Client & Reply<&2, Core.CreateMark>)

# merges the point p into the branch b, item by item
law Client.try_merge:
  for c: Client
  for r: Core.RequestId
  for p: Core.Point
  for b: Core.Branch
  IO(Client & Reply<&2, Core.Merge>)

# settles the resource n of the conflict k with the content x
law Client.try_resolve:
  for c: Client
  for r: Core.RequestId
  for k: Core.Conflict
  for n: Core.Name
  for x: Source
  IO(Client & Reply<&2, Core.Resolve>)

# ties the resource u to the branch b, with the settings ss that the kind of
# u reads, and fills u when it is empty; when u is mounted, sets its settings
# and branch
law Client.try_mount:
  for c: Client
  for r: Core.RequestId
  for u: Uris.Uri
  for ss: List<&2, String>
  for b: Core.Branch
  IO(Client & Reply<&2, Mount>)

# stops versioning u
law Client.try_unmount:
  for c: Client
  for r: Core.RequestId
  for u: Uris.Uri
  IO(Client & Reply<&2, Unmount>)

# sets the owner group of the branch b to g
law Client.try_set_owner:
  for c: Client
  for r: Core.RequestId
  for b: Core.Branch
  for g: Core.Group
  IO(Client & Reply<&2, Core.SetOwner>)

# makes the group g with the members ms or, when g exists, replaces its
# members
law Client.try_set_group:
  for c: Client
  for r: Core.RequestId
  for g: Core.Group
  for ms: List<&2, Core.Member>
  IO(Client & Reply<&2, Core.SetGroup>)

# swaps history with the node n, since the position s (all without one)
law Client.try_sync:
  for c: Client
  for r: Core.RequestId
  for n: Core.Node
  for s: Maybe<&2, Core.Position>
  IO(Client & Reply<&2, Core.Sync>)

# stops the node; force stops it even with mounts or other writers
law Client.try_stop:
  for c: Client
  for r: Core.RequestId
  for force: Bool
  IO(Client & Reply<&2, Stop>)

# a live stream of the notices of the topic t since the position s (from now
# without one)
law Client.try_subscribe:
  for c: Client
  for t: Core.Topic
  for s: Maybe<&2, Core.Position>
  IO(Client & Reply<&1, Subscription>)

# the next notice of the stream x
law Subscription.try_next:
  for x: Subscription
  IO(Subscription & Reply<&2, Core.Notice>)

# ends the stream x
law Subscription.try_close:
  for x: Subscription
  IO(Reply<&2, Unit>)
