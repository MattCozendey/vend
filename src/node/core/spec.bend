import Base
import ../../shared/replica.bend as Replicas
import ../../shared/shared/formats.bend as Formats
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/rope.bend as Ropes
import ../../shared/shared/shared/reach.bend as Reaches
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ../../shared/shared/shared/shared/trie.bend as Tries
import ../../shared/shared/shared/text.bend as Texts
import ../shared/requests.bend as Requests
import ../shared/shared/resources.bend as Resources

# The pure core of a Vend Node (README): what it holds, what it answers, and
# the laws about both. transport/spec.bend carries it over IO.
#
# A line is a store, or one of its branches. What a line holds is a tip: its
# content, a tree of what it holds now; its log, a tree that only gains keys
# (the outcome of each request, each version by its number, the marks); the
# count of its versions; and the owners of its next step. So the count and the
# owners are a read of the tip, and the answer to a request, a version by
# number and a mark are each one read of a tree: about log(size) nodes, each
# checked by its hash.
#
# A step takes a tip to the next one: it runs a batch of requests, in order
# (Step.run), and any node can run it again. The owners of a line cast ballots
# for steps (Ledgers); a node moves its head of a line only to a step that the
# owners in its tip decided (a majority of them, in one round), and that it
# ran itself with the same result (Node.advance). A node's ledger only grows,
# and its heads only move along steps, so what it answers stays.

# What the laws speak of
# -----------------------
# The types of the core, and its operations: impl.bend gives each its body.

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}

# what a merge keeps of a resource: the content of one side (none: removed),
# new bytes, or a clash
type Pick is Data:
  Pick.Take{root: Maybe<&2, Ropes.Root>}
  Pick.Make{bytes: Texts.Bytes()}
  Pick.Clash{}

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base, ours when theirs is the base or both
# agree, else both merged (none: wait for their bytes). So a merge never loses
# a change that only one side made
law Pick.merge:
  for f: Formats.Format
  for s: Replicas.Node<Requests.Ask>
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  Maybe<&2, Pick>

# the resources that ours (the tree h) and theirs (ht) may hold differently,
# once each: a walk of both trees skips what they share, and where both hold
# the same bytes a merge keeps them (Format.merge_same)
law Merge.names:
  for s: Replicas.Node<Requests.Ask>
  for h: Maybe<&2, Hashes.Hash>
  for ht: Maybe<&2, Hashes.Hash>
  List<&2, Resources.Name>

# the nodes inside the group g of the store tree h, each once: the nodes that
# own what g owns
law Group.nodes:
  for +s: Replicas.Node<Requests.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for g: String
  List<&2, String>

# the verdict on a write of the resource n since base, with the content c, at
# the tree h: take it when n holds at h what it held at base. It waits for a
# node that it lacks: it does not refuse on what it cannot read
law Judge.write:
  for +s: Replicas.Node<Requests.Ask>
  for +n: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +c: Requests.Content
  for +h: Maybe<&2, Hashes.Hash>
  Maybe<&2, Replicas.Verdict<Requests.Ask>>

# the trees of a resolve of the resource n with the root m, in the tree h:
# the resource holds m, and its clash is shut (its key holds no request)
law Resolve.work:
  for s: Replicas.Node<Requests.Ask>
  for h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for m: Maybe<&2, Ropes.Root>
  Maybe<&2, Replicas.Work<Requests.Ask>>

# the base of a merge of from into the line c, whose tree is h: from itself
# when it is of c; else the newest version that both came from, by the version
# vectors of both sides (the version of c that from came from, or the version
# of from's line that h came from)
law Merge.base:
  for +s: Replicas.Node<Requests.Ask>
  for +c: Ledgers.Chain
  for +from: Ledgers.Id
  for h: Maybe<&2, Hashes.Hash>
  Maybe<&2, Ledgers.Id>

# the trees of a merge of from into the line c, whose tree is h
law Merge.work:
  for +s: Replicas.Node<Requests.Ask>
  for +c: Ledgers.Chain
  for +from: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  Maybe<&2, Replicas.Work<Requests.Ask>>

# the trees of a move of the line c, whose tree is h, to the version to: to's
# tree, with what the line came from added to its version vector
law Move.work:
  for +s: Replicas.Node<Requests.Ask>
  for +c: Ledgers.Chain
  for +to: Ledgers.Id
  for h: Maybe<&2, Hashes.Hash>
  Maybe<&2, Replicas.Work<Requests.Ask>>

# whether the owners of the line l of the store r take an Own of the group g
# with the owners os, at the tree h: os are the nodes inside g in the store
# tree that it names (Own.tree; none: wait for its step, or for the groups)
law Own.takes:
  for +s: Replicas.Node<Requests.Ask>
  for r: Ledgers.Id
  for +l: Maybe<&2, String>
  for g: String
  for +at: Maybe<&2, Ledgers.Id>
  for os: List<&2, String>
  for h: Maybe<&2, Hashes.Hash>
  Maybe<&2, Bool>

# the kernel of Vend
law Ask.kernel:
  Replicas.Kernel(Requests.Ask.machine())

# the content of the newest pending write of the resource n on the branch b
# of the store r that the writer w asked for, if there is one. The requests
# that wait on the line are the pending ones: the cost is theirs, not that of
# every request of the writer
law Node.draft:
  for +s: Replicas.Node<Requests.Ask>
  for w: String
  for +r: Ledgers.Id
  for +b: String
  for n: Resources.Name
  Maybe<&2, Requests.Content>

# what the writer w reads of the resource n at the point p: at the head of a
# branch, its own pending write; else what the point holds
law Node.read:
  for +s: Replicas.Node<Requests.Ask>
  for w: String
  for +n: Resources.Name
  for p: Point
  Maybe<&2, Texts.Bytes()>

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

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

# what the node answers to the change q of e (none: it did not take it in)
law Node.answer:
  for +s: Replicas.Node<Requests.Ask>
  for e: Replicas.Envelope
  for q: Requests.Ask
  Maybe<&2, Answer>

# a branch: its store and its name
type Branch is Data:
  Branch{store: Ledgers.Id, name: String}

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Ledgers.Id}

# the resources of a branch, each with what it imports, read once: the graph
# of its imports, and the same graph turned round (who imports each)
type Uses is Data:
  Uses{
    imports: Tries.Trie<List<&2, Resources.Name>>,
    names: List<&2, Resources.Name>,
    users: Reaches.Graph
  }

# a change elsewhere that touches what a branch uses: the version wrote the
# resource changed, and the resource used of the branch is that resource or
# uses it (Node.touches)
type Touch is Data:
  Touch{version: Ledgers.Id, changed: Resources.Name, branch: Branch, used: Resources.Name}

# what the checks of touches on one branch read of s once: the branch, its
# imports, the versions of other branches that it lacks, and, for each
# resource that one of them wrote, the resources that use it at any depth
type Seen is Data:
  Seen{
    state: Replicas.Node<Requests.Ask>,
    branch: Branch,
    uses: Uses,
    lacked: List<&2, Ledgers.Id>,
    used: Tries.Trie<Tries.Trie<Unit>>
  }

# what the checks on the branch b read of s
law Seen.of:
  for +s: Replicas.Node<Requests.Ask>
  for +b: Branch
  Seen

# the touch t, of the branch of g, holds: its branch is a branch and lacks
# its version, which is a version and wrote the resource changed, and the
# resource used is of the branch, and is the one changed or uses it; each
# part runs only when the ones before it hold, from the cheapest
law Touch.holds:
  for g: Seen
  for t: Touch
  Bool

# the changes elsewhere that touch what the branch b uses, at any depth
law Node.affects:
  for +s: Replicas.Node<Requests.Ask>
  for +b: Branch
  List<&2, Touch>

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

# a resource mounted to a branch
type Mount is Data:
  Mount{resource: String, branch: Branch}

# the content of the bytes b: the root of their rope
law Content.of:
  for b: Texts.Bytes()
  Requests.Content

# k versions of the branch b of the store r, from the number n, in order: a
# reader asks for a part of a history, and pays for that part
law Node.versions:
  for +s: Replicas.Node<Requests.Ask>
  for r: Ledgers.Id
  for b: String
  for n: U32
  for k: Nat
  List<&2, Ledgers.Id>

# the members of the group g of the store r, if g exists
law Node.members:
  for +s: Replicas.Node<Requests.Ask>
  for r: Ledgers.Id
  for g: String
  Maybe<&2, List<&2, Requests.Member>>

# the request that makes the group g, with the nodes inside it now, the owner
# group of the line l of the store r
law Node.own:
  for +s: Replicas.Node<Requests.Ask>
  for +r: Ledgers.Id
  for l: Maybe<&2, String>
  for +g: String
  Requests.Ask

# the versions of the branch b of the store r that changed the resource n,
# among k versions from the number from
law Node.log:
  for +s: Replicas.Node<Requests.Ask>
  for n: Resources.Name
  for +r: Ledgers.Id
  for +b: String
  for +from: U32
  for k: Nat
  List<&2, LogEntry>

# what changed in the resource n from the point a to the point b, as the
# writer w reads them
law Node.diff:
  for +s: Replicas.Node<Requests.Ask>
  for +w: String
  for +n: Resources.Name
  for a: Point
  for b: Point
  List<&2, Formats.Change>

# the resources of the branch b at its head
law Node.resources:
  for +s: Replicas.Node<Requests.Ask>
  for b: Branch
  List<&2, Resources.Name>

# the touch t holds
law Node.touches:
  for s: Replicas.Node<Requests.Ask>
  for t: Touch
  Bool

# what the changes up to the point p touch elsewhere
law Node.impact:
  for +s: Replicas.Node<Requests.Ask>
  for p: Point
  List<&2, Touch>

# the notices of the topic t in s that since, an earlier state of the node,
# does not have: the cost is that of what is new, not of the history
law Node.notices:
  for +s: Replicas.Node<Requests.Ask>
  for t: Topic
  for since: Replicas.Node<Requests.Ask>
  List<&2, Notice>

# what a Vend Node holds: its name, the parts of the stores that it uses, the
# writers connected to it, and the resources mounted to it
type Vend is Data:
  Vend{
    name: String,
    state: Replicas.Node<Requests.Ask>,
    writers: List<&2, String>,
    mounts: List<&2, Mount>
  }

# the node v may stop: it is forced to, or no resource is mounted and no
# writer is connected
law Vend.may_stop:
  for v: Vend
  for force: Bool
  Bool

# What the claims are stated in
# ------------------------------
# Defs that a reader of a claim must see: each is its own meaning.

# the answer m may come after the answer a as the node goes on: a request
# that a node answers stays answered; Pending may become any answer; Stale
# and Refused are final; a taken change stays taken, as the same version or
# the same merge (Written and Conflicted may follow each other: a merge is
# Conflicted while resources clash)
def Answer.follows(a: Answer, m: Maybe<&2, Answer>) -> Bool:
  match a m:
    case Answer.Pending{} Some{b}:
      True{}
    case Answer.Written{v} Some{Answer.Written{w}}:
      Ledgers.Id.is_eq(v, w)
    case Answer.Written{v} Some{Answer.Conflicted{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Written{w}}:
      True{}
    case Answer.Conflicted{v} Some{Answer.Conflicted{w}}:
      Ledgers.Id.is_eq(v, w)
    case Answer.Stale{} Some{Answer.Stale{}}:
      True{}
    case Answer.Refused{} Some{Answer.Refused{}}:
      True{}
    case x y:
      False{}

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the key of the clash of the resource n
def Key.clash(n: Resources.Name) -> List<&2, U32>:
  3 <> Resources.Name.code(n, [])

# the value of a resource whose content is under the root m (none: removed)
def Res.code(m: Maybe<&2, Ropes.Root>) -> List<&2, U32>:
  Codes.Code.maybe(~Ropes.Root, ~Ropes.Root.code, m, [])

# the value of a resource, flattened: the root of its content, when it is
# there
def Res.of.read(m: Maybe<&2, Codes.Read<Maybe<&2, Ropes.Root>>>) -> Maybe<&2, Ropes.Root>:
  match m:
    case Some{Codes.Read{x, Nil{}}}:
      x
    case _:
      None{}

# the root of the content in the value ws of a resource, when it is there
def Res.read(ws: List<&2, U32>) -> Maybe<&2, Ropes.Root>:
  Res.of.read(Codes.Code.maybe.read(~Ropes.Root, ~Ropes.Root.code.read, ws))

# the root in the value m of a resource, if any
def Res.found(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, m, ws => Res.read(ws))

# the root of the content of the resource n in the tree whose root is h, or
# that it is not there (none: the node lacks a node of the tree)
def Res.find(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Ropes.Root>,
    Replicas.Node.find(~Requests.Ask.machine(), s, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the root of the content of the resource n in the tree whose root is h (none:
# it is not there)
def Res.root(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Ropes.Root,
    Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.res(n)),
    ws => Res.read(ws)
  )

# the root that the content c gives the resource n (none: the version holds
# none)
def Content.root(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  c: Requests.Content
) -> Maybe<&2, Ropes.Root>:
  match c:
    case Requests.Content.Root{x}:
      Some{x}
    case Requests.Content.Of{w}:
      Res.root(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{w}), n)

# the root that the content c gives the resource n, or that it gives none
# (none: the node lacks a node of the version's tree)
def Content.find(
  +s: Replicas.Node<Requests.Ask>,
  n: Resources.Name,
  c: Requests.Content
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  match c:
    case Requests.Content.Root{x}:
      Some{Some{x}}
    case Requests.Content.Of{w}:
      Res.find(s, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{w}), n)

# the store tree in which an Own of the line l, at the content h, reads its
# group: a store reads its own content; a branch, the content of the version
# at of its store
def Own.tree(
  s: Replicas.Node<Requests.Ask>,
  l: Maybe<&2, String>,
  at: Maybe<&2, Ledgers.Id>,
  h: Maybe<&2, Hashes.Hash>
) -> Maybe<&2, Hashes.Hash>:
  match l at:
    case Some{b} Some{v}:
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{v})
    case x y:
      h

# the value of the clash that the merge of the version f opened (a settled
# clash holds no words)
def Clash.code(f: Ledgers.Id) -> List<&2, U32>:
  Ledgers.Id.code(f, [])

# the clash that the merge of the version f opened in the resource n is open
# in the tree h
def Clash.open(
  s: Replicas.Node<Requests.Ask>,
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  f: Ledgers.Id
) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.clash(n)),
    Some{Clash.code(f)}
  )

# the resource m of the branch x of the store st is the resource n of the
# branch b of the store r
def Draft.is_on(
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  st: Ledgers.Id,
  x: String,
  m: Resources.Name
) -> Bool:
  List.all.if(
    u => List.all.if(v => Resources.Name.is_eq(m, n), String.eq(x, b)),
    Ledgers.Id.is_eq(st, r)
  )

# the content that the request q gives the resource n on the branch b of the
# store r, when it writes it there
def Draft.content(
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  q: Requests.Ask
) -> Maybe<&2, Requests.Content>:
  match q:
    case Requests.Ask.On{st, Some{x}, Requests.Change.Write{m, base, c}}:
      Shared.Maybe.when(Requests.Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case Requests.Ask.On{st, Some{x}, Requests.Change.Resolve{k, m, c}}:
      Shared.Maybe.when(Requests.Content, Draft.is_on(r, b, n, st, x, m), u => Some{c})
    case _:
      None{}

# Laws
# ----
# What README says of what is Vend's in a Vend Node, as laws. The laws of the
# machine (a node only grows, a log only gains keys, one history) are the
# replica's: src/shared/replica.bend proves them for any lawful kernel, and
# impl.bend gives the lawful kernel of Vend.

# two requests are the same exactly when they are equal
law Ask.same:
  Shared.Eq.Laws(Requests.Ask, Requests.Ask.is_eq)

# the owners of a line are the nodes inside its owner group: its owners take
# an Own only when its owners are the nodes inside its group, in the store
# tree that it names (Own.tree)
law Own.takes_inside:
  for +s: Replicas.Node<Requests.Ask>
  for +r: Ledgers.Id
  for +l: Maybe<&2, String>
  for +g: String
  for +at: Maybe<&2, Ledgers.Id>
  for +os: List<&2, String>
  for +h: Maybe<&2, Hashes.Hash>
  {Own.takes(s, r, l, g, at, os, h) == Some{True{}}: Maybe<&2, Bool>}
    -> {os == Group.nodes(s, Own.tree(s, l, at, h), g): List<&2, String>}

# answers only move forward: a request that a node answers stays answered;
# Stale and Refused are final; a taken change stays taken (Answer.follows)
law Node.answer_follows:
  for +n: String
  for +evs: List<&2, Replicas.Deed<Requests.Ask>>
  for +s: Replicas.Node<Requests.Ask>
  for +e: Replicas.Envelope
  for +q: Requests.Ask
  for +x: Answer
  {Node.answer(s, e, q) == Some{x}: Maybe<&2, Answer>}
    -> {
      Answer.follows(
        x,
        Node.answer(Replicas.Node.after(~Requests.Ask.machine(), ~Ask.kernel(), n, evs, s), e, q)
      )
        == True{}: Bool
    }

# while a write that the writer w asked for waits on its line, the node has a
# draft of the resource for w (the newest of its pending writes, by
# Draft.newer)
law Node.draft_some:
  for +s: Replicas.Node<Requests.Ask>
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +q2: String
  for +t: String
  for +q: Requests.Ask
  for +c: Requests.Content
  {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Replicas.Wait.of(~Requests.Ask.machine(), s, Replicas.Line.chain(r, Some{b})),
      Ledgers.Id{w, q2}
    )
      == True{}: Bool
  }
    -> {
      Replicas.Node.asked(
        ~Requests.Ask.machine(),
        s,
        Ledgers.Id{w, q2}
      )
        == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Requests.Ask>>
    }
    -> {Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Requests.Content>}
    -> {Maybe.is_some(&2, Requests.Content, Node.draft(s, w, r, b, n)) == True{}: Bool}

# a write that the owners take: in the node that the verdict holds, the
# resource reads as the content of the write
law Judge.write_reads:
  for +s: Replicas.Node<Requests.Ask>
  for +n: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +c: Requests.Content
  for +h: Maybe<&2, Hashes.Hash>
  for +h2: Maybe<&2, Hashes.Hash>
  for +s3: Replicas.Node<Requests.Ask>
  for +m: Maybe<&2, Ropes.Root>
  {
    Judge.write(
      s,
      n,
      base,
      c,
      h
    )
      == Some{
        Replicas.Verdict.Taken{Replicas.Work{s3, h2}}
      }: Maybe<&2, Replicas.Verdict<Requests.Ask>>
  }
    -> {Content.find(s, n, c) == Some{m}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {Res.root(s3, h2, n) == m: Maybe<&2, Ropes.Root>}

# a move records a version equal to its target: each resource of the version
# to is, with the same content, in the tree that a move to it gives
law Move.reads:
  for +s: Replicas.Node<Requests.Ask>
  for +c: Ledgers.Chain
  for +to: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +v: List<&2, U32>
  {
    Replicas.Node.get(
      ~Requests.Ask.machine(),
      s,
      Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{to}),
      Key.res(n)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
    -> Replicas.Work.Reads(~Requests.Ask.machine(), Key.res(n), v, Move.work(s, c, to, h))

# a merge turns Written once each clashing resource is resolved: a resolve
# gives the resource its content, and shuts its clash (a clash whose key holds
# no request is not open: Clash.shut)
law Resolve.reads:
  for +s: Replicas.Node<Requests.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Replicas.Work.Reads(~Requests.Ask.machine(), Key.res(n), Res.code(m), Resolve.work(s, h, n, m))

law Resolve.shuts:
  for +s: Replicas.Node<Requests.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +m: Maybe<&2, Ropes.Root>
  Replicas.Work.Reads(~Requests.Ask.machine(), Key.clash(n), [], Resolve.work(s, h, n, m))

law Clash.shut:
  for +s: Replicas.Node<Requests.Ask>
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +f: Ledgers.Id
  {
    Replicas.Node.get(
      ~Requests.Ask.machine(),
      s,
      h,
      Key.clash(n)
    )
      == Some{[]}: Maybe<&2, List<&2, U32>>
  }
    -> {Clash.open(s, h, n, f) == False{}: Bool}

# a merge of whole trees keeps what the merge of each resource takes: when the
# merge of the resource n takes the root x (Pick.merge_theirs, Pick.merge_ours:
# a change that only one side made), the tree that the merge gives holds n
# with x
law Merge.keeps:
  for +s: Replicas.Node<Requests.Ask>
  for +c: Ledgers.Chain
  for +from: Ledgers.Id
  for +h: Maybe<&2, Hashes.Hash>
  for +n: Resources.Name
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  for +x: Maybe<&2, Ropes.Root>
  {
    List.contains(
      ~Resources.Name,
      ~Resources.Name.is_eq,
      Merge.names(s, h, Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from})),
      n
    )
      == True{}: Bool
  }
    -> {
      Res.find(
        s,
        Replicas.Node.root_of(~Requests.Ask.machine(), s, Merge.base(s, c, from, h)),
        n
      )
        == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>
    }
    -> {Res.find(s, h, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>}
    -> {
      Res.find(
        s,
        Replicas.Node.root_of(~Requests.Ask.machine(), s, Some{from}),
        n
      )
        == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>
    }
    -> {
      Pick.merge(
        Formats.Format.of(Resources.Name.path(n)),
        s,
        b,
        o,
        t
      )
        == Some{Pick.Take{x}}: Maybe<&2, Pick>
    }
    -> Replicas.Work.Reads(
      ~Requests.Ask.machine(),
      Key.res(n),
      Res.code(x),
      Merge.work(s, c, from, h)
    )

# a merge keeps, for each resource, a change that only one side made: when
# ours is the base, it keeps theirs
law Pick.merge_theirs:
  for f: Formats.Format
  for s: Replicas.Node<Requests.Ask>
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Roots.same(o, b) == True{}: Bool}
    -> {Pick.merge(f, s, b, o, t) == Some{Pick.Take{t}}: Maybe<&2, Pick>}

# and when theirs is the base, it keeps ours
law Pick.merge_ours:
  for f: Formats.Format
  for s: Replicas.Node<Requests.Ask>
  for +b: Maybe<&2, Ropes.Root>
  for +o: Maybe<&2, Ropes.Root>
  for +t: Maybe<&2, Ropes.Root>
  {Roots.same(o, b) == False{}: Bool}
    -> {Roots.same(t, b) == True{}: Bool}
    -> {Pick.merge(f, s, b, o, t) == Some{Pick.Take{o}}: Maybe<&2, Pick>}

# writers are told only about changes to what their work uses: each change
# that Node.affects gives for a branch holds (Touch.holds): another line made
# it, the branch lacks it, and it wrote a resource that a resource of the
# branch is, or uses through its imports, at any depth
law Node.affects_used:
  for +s: Replicas.Node<Requests.Ask>
  for +b: Branch
  {
    Shared.List.holds(
      ~Touch,
      ~Seen,
      ~Touch.holds,
      Node.affects(s, b),
      Seen.of(s, b)
    )
      == True{}: Bool
  }

# a writer reads its own pending write: at the head of a branch, its read is
# the bytes of its draft, not what the branch holds
law Node.read_draft:
  for +s: Replicas.Node<Requests.Ask>
  for +w: String
  for +r: Ledgers.Id
  for +b: String
  for +n: Resources.Name
  for +c: Requests.Content
  {Node.draft(s, w, r, b, n) == Some{c}: Maybe<&2, Requests.Content>}
    -> {
      Node.read(
        s,
        w,
        n,
        Point.Head{r, b}
      )
        == Replicas.Root.bytes(
          ~Requests.Ask.machine(),
          s,
          Content.root(s, n, c)
        ): Maybe<&2, Texts.Bytes()>
    }
