import Base
import ../../shared/bytes.bend as Octets
import ../../shared/formats.bend as Formats
import ../../shared/resources.bend as Resources
import ../../shared/uris.bend as Uris
import ../core/spec.bend as Core

# The public API of a Vend Node (README, Public API): the core, carried over
# IO. Every front offers exactly these operations. A change is a request, sent
# again unchanged until it is answered: the core keeps it once (Core.Node.ask),
# so any front may retry it, to any node.

# Values that callers make
# ------------------------

# where new content comes from: content, or a resource that the node reads
# first
type Source is Data:
  Source.Content{content: Core.Content}
  Source.From{uri: Uris.Uri}

# Answers
# -------

# an answer that crossed IO, or why it did not
type Reply<a, -A: Kind(a)> is Kind(a):
  Reply.Delivered{answer: A}
  Reply.TimedOut{}
  Reply.Unreachable{}

# the notices that a poll returns, and what to pass as since next time
type Changes is Data:
  Changes{notices: List<&2, Core.Notice>, since: Core.State()}

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
  List<&2, String>

# the branches whose owners this node is among
law Status.owned:
  for s: Status
  List<&2, String>

# Partial: the submodules in missing could not be fetched. Unsupported: the
# kind of the resource does not support a setting
type Mount is Data:
  Mount.Mounted{}
  Mount.Partial{missing: List<&2, String>}
  Mount.Unsupported{why: String}
  Mount.Refused{why: String}

type Unmount is Data:
  Unmount.Unmounted{}
  Unmount.NotMounted{}

# Partial: some entries of the other node did not arrive; the ones that did
# are taken in
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

# runs the node named n on the store at store, until a stop
law VendNode.try_start_or_resume:
  for n: String
  for store: Uris.Uri
  IO(Start)

# a connection to the node at node, as writer
law Client.try_open:
  for node: Uris.Uri
  for writer: String
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

# the versions of the branch b that changed the resource n
law Client.try_get_log:
  for c: Client
  for n: Resources.Name
  for b: String
  IO(Client & Reply<&2, List<&2, Core.LogEntry>>)

# the bytes of the resource n at the point p, if it is there
law Client.try_get_content:
  for c: Client
  for n: Resources.Name
  for p: Core.Point
  IO(Client & Reply<&2, Maybe<&2, Octets.Bytes()>>)

# what changed in the resource n from the point a to the point b
law Client.try_get_diff:
  for c: Client
  for n: Resources.Name
  for a: Core.Point
  for b: Core.Point
  IO(Client & Reply<&2, List<&2, Formats.Change>>)

# where the request r of this writer is: an answer to a change that timed out
law Client.try_get_answer:
  for c: Client
  for r: String
  IO(Client & Reply<&2, Core.Answer>)

# the resources that still clash after the merge k
law Client.try_get_conflict:
  for c: Client
  for k: Core.Id
  IO(Client & Reply<&2, List<&2, Resources.Name>>)

# the notices of the topic t that since does not have (all without it)
law Client.try_get_changes:
  for c: Client
  for t: Core.Topic
  for since: Maybe<&2, Core.State()>
  IO(Client & Reply<&2, Changes>)

# the request r: writes the content x to the resource n on the branch b, based
# on the version base (none for a new resource)
law Client.try_write:
  for c: Client
  for r: String
  for n: Resources.Name
  for b: String
  for base: Maybe<&2, Core.Id>
  for x: Source
  IO(Client & Reply<&2, Core.Answer>)

# the request r: makes the branch b at the point p or, when b exists, records
# a new version of b that equals p, with its submodules
law Client.try_set_branch:
  for c: Client
  for r: String
  for b: String
  for p: Core.Point
  IO(Client & Reply<&2, Core.Answer>)

# the request r: names the newest version of the branch b as the mark m, with
# the message t
law Client.try_create_mark:
  for c: Client
  for r: String
  for b: String
  for m: String
  for t: String
  IO(Client & Reply<&2, Core.Answer>)

# the request r: merges the point p into the branch b, item by item
law Client.try_merge:
  for c: Client
  for r: String
  for p: Core.Point
  for b: String
  IO(Client & Reply<&2, Core.Answer>)

# the request r: settles the resource n of the merge k with the content x
law Client.try_resolve:
  for c: Client
  for r: String
  for k: Core.Id
  for n: Resources.Name
  for x: Source
  IO(Client & Reply<&2, Core.Answer>)

# ties the resource u to the branch b, with the settings ss that the kind of
# u reads, and fills u when it is empty; when u is mounted, sets its settings
# and branch
law Client.try_mount:
  for c: Client
  for u: Uris.Uri
  for ss: List<&2, String>
  for b: String
  IO(Client & Reply<&2, Mount>)

# stops versioning u
law Client.try_unmount:
  for c: Client
  for u: Uris.Uri
  IO(Client & Reply<&2, Unmount>)

# the request r: makes the nodes inside the group g the owners of the branch b
law Client.try_set_owner:
  for c: Client
  for r: String
  for b: String
  for g: String
  IO(Client & Reply<&2, Core.Answer>)

# the request r: makes the group g with the members ms or, when g exists,
# replaces its members
law Client.try_set_group:
  for c: Client
  for r: String
  for g: String
  for ms: List<&2, Core.Member>
  IO(Client & Reply<&2, Core.Answer>)

# swaps entries with the node at n: each sends what the other lacks
# (Core.Node.missing)
law Client.try_sync:
  for c: Client
  for n: Uris.Uri
  IO(Client & Reply<&2, Sync>)

# stops the node; force stops it even with mounts or other writers
law Client.try_stop:
  for c: Client
  for force: Bool
  IO(Client & Reply<&2, Stop>)

# a live stream of the notices of the topic t that since does not have (from
# now without it)
law Client.try_subscribe:
  for c: Client
  for t: Core.Topic
  for since: Maybe<&2, Core.State()>
  IO(Client & Reply<&1, Subscription>)

# the next notice of the stream x
law Subscription.try_next:
  for x: Subscription
  IO(Subscription & Reply<&2, Core.Notice>)

# ends the stream x
law Subscription.try_close:
  for x: Subscription
  IO(Reply<&2, Unit>)
