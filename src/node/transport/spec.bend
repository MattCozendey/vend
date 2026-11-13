import Base
import ../../resource/formats.bend as Formats
import ../../resource/resources.bend as Resources
import ../../resource/uris.bend as Uris
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/text.bend as Texts
import ../../shared/vend.bend as Vend
import ../../writer/reads.bend as Reads
import ../../writer/requests.bend as Requests

# A Vend Node over IO (README): the core, carried to writers and to other
# nodes. Every front offers exactly these operations. A change is a request,
# sent again unchanged until it is answered: a ledger holds an entry once
# (Ledgers.Laws.AddTwice), so any front may retry it, to any node. A
# connection is one writer's, so each read shows that writer's own pending
# changes (Reads.Node.read).

# Values that callers make
# ------------------------

# where new content comes from: bytes, which the node keeps as data and names
# by the root of their rope; content that it holds; or a resource that the
# node reads first
type Source is Data:
  Source.Bytes{bytes: Texts.Bytes()}
  Source.Content{content: Requests.Content}
  Source.From{uri: Uris.Uri}

# Answers
# -------

# an answer that crossed IO, or why it did not
type Reply<a, -A: Kind(a)> is Kind(a):
  Reply.Delivered{answer: A}
  Reply.TimedOut{}
  Reply.Unreachable{}

# how far a reader of notices is: a small token, not what the node holds
law Cursor:
  Data

# the notices that a poll returns, and what to pass as since next time
type Changes is Data:
  Changes{notices: List<&2, Reads.Notice>, since: Cursor}

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
  List<&2, Vend.Branch>

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

# runs the node named n on the data address at store, until a stop. The node
# keeps its secret seed there. A node that starts a new Vend Store asks for
# Requests.Ask.Start with itself as the first owner, and the first key of its
# chain in the store
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
  IO(Client & Reply<&2, List<&2, Reads.BranchEntry>>)

# the versions of the branch b that changed the resource n
law Client.try_get_log:
  for c: Client
  for n: Resources.Name
  for b: Vend.Branch
  IO(Client & Reply<&2, List<&2, Reads.LogEntry>>)

# the bytes of the resource n at the point p, if it is there, as the writer
# reads it (Reads.Node.read)
law Client.try_get_content:
  for c: Client
  for n: Resources.Name
  for p: Vend.Point
  IO(Client & Reply<&2, Maybe<&2, Texts.Bytes()>>)

# what changed in the resource n from the point a to the point b, as the
# writer reads them
law Client.try_get_diff:
  for c: Client
  for n: Resources.Name
  for a: Vend.Point
  for b: Vend.Point
  IO(Client & Reply<&2, List<&2, Formats.Change>>)

# the changes elsewhere that touch what the branch b uses
law Client.try_get_affects:
  for c: Client
  for b: Vend.Branch
  IO(Client & Reply<&2, List<&2, Reads.Touch>>)

# what the changes up to the point p touch elsewhere
law Client.try_get_impact:
  for c: Client
  for p: Vend.Point
  IO(Client & Reply<&2, List<&2, Reads.Touch>>)

# the resources that still clash after the merge k
law Client.try_get_conflict:
  for c: Client
  for k: Ledgers.Id
  IO(Client & Reply<&2, List<&2, Resources.Name>>)

# the notices of the topic t that since does not have (all without it)
law Client.try_get_changes:
  for c: Client
  for t: Reads.Topic
  for since: Maybe<&2, Cursor>
  IO(Client & Reply<&2, Changes>)

# the request r: writes the content x to the resource n on the branch b, based
# on the version base (none for a new resource)
law Client.try_write:
  for c: Client
  for r: String
  for n: Resources.Name
  for b: Vend.Branch
  for base: Maybe<&2, Ledgers.Id>
  for x: Source
  IO(Client & Reply<&2, Vend.Answer>)

# the request r: makes the branch b at the point p (Requests.Change.Branch)
# or, when b exists, records a new version of b that equals p, with its
# submodules (Requests.Change.Move)
law Client.try_set_branch:
  for c: Client
  for r: String
  for b: Vend.Branch
  for p: Vend.Point
  IO(Client & Reply<&2, Vend.Answer>)

# the request r: names the newest version of the branch b as the mark m, with
# the message t
law Client.try_create_mark:
  for c: Client
  for r: String
  for b: Vend.Branch
  for m: String
  for t: String
  IO(Client & Reply<&2, Vend.Answer>)

# the request r: merges the point p into the branch b, item by item
law Client.try_merge:
  for c: Client
  for r: String
  for p: Vend.Point
  for b: Vend.Branch
  IO(Client & Reply<&2, Vend.Answer>)

# the request r: settles the resource n of the merge k on the branch b with the
# content x
law Client.try_resolve:
  for c: Client
  for r: String
  for b: Vend.Branch
  for k: Ledgers.Id
  for n: Resources.Name
  for x: Source
  IO(Client & Reply<&2, Vend.Answer>)

# ties the resource u to the branch b, with the settings ss that the kind of
# u reads, and fills u when it is empty; when u is mounted, sets its settings
# and branch
law Client.try_mount:
  for c: Client
  for u: Uris.Uri
  for ss: List<&2, String>
  for b: Vend.Branch
  IO(Client & Reply<&2, Mount>)

# stops versioning u
law Client.try_unmount:
  for c: Client
  for u: Uris.Uri
  IO(Client & Reply<&2, Unmount>)

# the request r: makes the group g of the store the owner group of its branch
# l (none: of the store itself), with the nodes inside it now. When g changes
# later, the node asks for its nodes again
law Client.try_set_owner:
  for c: Client
  for r: String
  for store: Hashes.Hash
  for l: Maybe<&2, String>
  for g: String
  IO(Client & Reply<&2, Vend.Answer>)

# the request r: makes the group g of the store with the members ms or, when g
# exists, replaces its members (Requests.Change.Group)
law Client.try_set_group:
  for c: Client
  for r: String
  for store: Hashes.Hash
  for g: String
  for ms: List<&2, Requests.Member>
  IO(Client & Reply<&2, Vend.Answer>)

# swaps entries with the node at n: each sends what the other lacks
# (Ledgers.Laws.Missing) and keeps what checks (Replicas.Laws.Takes)
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
  for t: Reads.Topic
  for since: Maybe<&2, Cursor>
  IO(Client & Reply<&1, Subscription>)

# the next notice of the stream x
law Subscription.try_next:
  for x: Subscription
  IO(Subscription & Reply<&2, Reads.Notice>)

# ends the stream x
law Subscription.try_close:
  for x: Subscription
  IO(Reply<&2, Unit>)
