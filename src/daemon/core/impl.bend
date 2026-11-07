import Base
import ../../shared/bools.bend as Bools
import ../../shared/bytes.bend as Octets
import ../../shared/cmps.bend as Cmps
import ../../shared/lists.bend as Lists
import ../../shared/maybes.bend as Maybes
import ../../shared/nats.bend as Nats
import ../../shared/orders.bend as Orders
import ../../shared/reach.bend as Reaches
import ../../shared/resources.bend as Resources
import ../../shared/shared.bend as Shared
import ../../shared/strings.bend as Strings
import ../../shared/tables.bend as Tables
import ./spec.bend as Spec

# The pure core of a Vend Node. Every opaque name of the spec is a String,
# compared with String.eq; every collection that is keyed by a name is a
# Table.

# Names
# -----
def Spec.VendNode():
  String

def Spec.VendNode.read(t):
  Strings.String.nonempty(t)

def Spec.VendNode.show(n):
  n

def Spec.Group():
  String

def Spec.Group.read(t):
  Strings.String.nonempty(t)

def Spec.Group.show(g):
  g

def Spec.Space():
  String

def Spec.Space.read(t):
  Strings.String.nonempty(t)

def Spec.Space.show(s):
  s

def Spec.Branch():
  String

def Spec.Branch.read(t):
  Strings.String.nonempty(t)

def Spec.Branch.show(b):
  b

def Spec.Mark():
  String

def Spec.Mark.read(t):
  Strings.String.nonempty(t)

def Spec.Mark.show(m):
  m

def Spec.Writer():
  String

def Spec.Writer.read(t):
  Strings.String.nonempty(t)

def Spec.Writer.show(w):
  w

def Spec.Version():
  String

def Spec.Version.read(t):
  Strings.String.nonempty(t)

def Spec.Version.show(v):
  v

def Spec.RequestId():
  String

def Spec.RequestId.read(t):
  Strings.String.nonempty(t)

def Spec.RequestId.show(r):
  r

def Spec.Conflict():
  String

def Spec.Conflict.read(t):
  Strings.String.nonempty(t)

def Spec.Conflict.show(c):
  c

def Spec.Time():
  String

def Spec.Time.read(t):
  Strings.String.nonempty(t)

def Spec.Time.show(t):
  t

def Spec.Format():
  String

def Spec.Format.read(t):
  Strings.String.nonempty(t)

def Spec.Format.show(f):
  f

def Spec.Place():
  String

def Spec.Place.read(t):
  Strings.String.nonempty(t)

def Spec.Place.show(p):
  p

# a position: how many notices came before it
def Spec.Position():
  Nat

def Spec.Position.read(t):
  Nat.read(t)

def Spec.Position.show(p):
  Nat.show(p)

# an epoch: how many times the ownership changed
def Spec.Epoch():
  Nat

def Spec.Epoch.read(t):
  Nat.read(t)

def Spec.Epoch.show(e):
  Nat.show(e)

def Spec.Epoch.number(e):
  e

# Records
# -------

# a version: its resources by name, the versions it came from, who made it,
# and when; its ID is its key
type VersionRecord is Data:
  VersionRecord{
    blobs: Tables.Table<List<&2, U32>>,
    parents: List<&2, String>,
    author: String,
    time: String
  }

# a branch: its newest version, its owner group, and the stamp of that head:
# the owner's epoch, then how many heads the owner set in that epoch; its
# name is its key
type BranchRecord is Data:
  BranchRecord{head: String, owner: String, epoch: Nat, count: Nat}

# a mark: a fixed name for a version of a branch
type MarkAt is Data:
  MarkAt{version: String, message: String}

# an owner group: its members, and how many times they were set
type GroupRecord is Data:
  GroupRecord{members: List<&2, Spec.Member>, epoch: Nat}

# a merge that clashed: its branch and that branch's head then, the version
# merged in, the resources settled so far, and the resources that still clash
type Clash is Data:
  Clash{
    branch: String,
    head: String,
    from: String,
    blobs: Tables.Table<List<&2, U32>>,
    left: List<&2, String>
  }

# a request that was answered, and the position before it
type Seen is Data:
  Seen{answer: Spec.Answer, at: Nat}

# a notice, and its topic
type Logged is Data:
  Logged{topic: Spec.Topic, notice: Spec.Notice}

# what a node holds: who it is, its versions, branches, marks (by branch, then
# name), groups and clashes, the requests it answered, and its notices in
# order
type NodeState is Data:
  NodeState{
    self: String,
    versions: Tables.Table<VersionRecord>,
    branches: Tables.Table<BranchRecord>,
    marks: Tables.Table<Tables.Table<MarkAt>>,
    groups: Tables.Table<GroupRecord>,
    clashes: Tables.Table<Clash>,
    seen: Tables.Table<Seen>,
    log: List<&2, Logged>
  }

def Spec.VendNode.State():
  NodeState

# what a change does: the versions it adds, the branches, marks, groups and
# clashes after it, its notices, and its answer
type Out is Data:
  Out{
    versions: List<&2, Tables.Row<VersionRecord>>,
    branches: Tables.Table<BranchRecord>,
    marks: Tables.Table<Tables.Table<MarkAt>>,
    groups: Tables.Table<GroupRecord>,
    clashes: Tables.Table<Clash>,
    news: List<&2, Logged>,
    answer: Spec.Answer
  }

# Lookups
# -------
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the pure node is the model that the laws are about: an and/or keeps one value for a proof to split on; speed belongs in a later fast node, proven equal to this one

# vs holds the version k
def VersionRecord.has(vs: Tables.Table<VersionRecord>, k: String) -> Bool:
  Maybe.is_some(&2, VersionRecord, Tables.Table.get(VersionRecord, vs, k))

# vs, with v unless vs holds a version with its ID (held)
def VersionRecord.add.put(
  i: String,
  v: VersionRecord,
  vs: Tables.Table<VersionRecord>,
  held: Bool
) -> Tables.Table<VersionRecord>:
  match held:
    case True{}:
      vs
    case False{}:
      Tables.Table.set(VersionRecord, vs, i, v)

# vs, with v unless vs holds a version with its ID
def VersionRecord.add.one(
  v: Tables.Row<VersionRecord>,
  +vs: Tables.Table<VersionRecord>
) -> Tables.Table<VersionRecord>:
  match v:
    case Tables.Row{+i, x}:
      VersionRecord.add.put(i, x, vs, VersionRecord.has(vs, i))

# vs, with each version of news whose ID vs does not hold
def VersionRecord.add(
  news: List<&2, Tables.Row<VersionRecord>>,
  vs: Tables.Table<VersionRecord>
) -> Tables.Table<VersionRecord>:
  match news:
    case Nil{}:
      vs
    case Con{v, r}:
      VersionRecord.add(r, VersionRecord.add.one(v, vs))

# the marks of the branch b, none when it has none
def Marks.of(ms: Tables.Table<Tables.Table<MarkAt>>, b: String) -> Tables.Table<MarkAt>:
  Maybe.default(
    &2,
    Tables.Table<MarkAt>,
    Tables.Table.get(Tables.Table<MarkAt>, ms, b),
    Tables.Table.new(MarkAt)
  )

# the version of the mark that m holds
def MarkAt.version.of(m: Maybe<&2, MarkAt>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{MarkAt{v, t}}:
      Some{v}

# the version of the mark m of the branch b among ms
def MarkAt.find(ms: Tables.Table<Tables.Table<MarkAt>>, b: String, m: String) -> Maybe<&2, String>:
  MarkAt.version.of(Tables.Table.get(MarkAt, Marks.of(ms, b), m))

# ms, with x as the mark m of the branch b
def MarkAt.set(
  +ms: Tables.Table<Tables.Table<MarkAt>>,
  +b: String,
  m: String,
  x: MarkAt
) -> Tables.Table<Tables.Table<MarkAt>>:
  Tables.Table.set(Tables.Table<MarkAt>, ms, b, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x))

# Comparisons
# -----------

# a and b are the same member
def Member.same(a: Spec.Member, b: Spec.Member) -> Bool:
  match a b:
    case Spec.Member.VendNode{x} Spec.Member.VendNode{y}:
      String.eq(x, y)
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# the order of members: nodes first, then groups, each by name
def Member.order(a: Spec.Member, b: Spec.Member) -> Cmp:
  match a b:
    case Spec.Member.VendNode{x} Spec.Member.VendNode{y}:
      String.order(x, y)
    case Spec.Member.VendNode{x} Spec.Member.Group{y}:
      LT{}
    case Spec.Member.Group{x} Spec.Member.VendNode{y}:
      GT{}
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      String.order(x, y)

# the stamp of a group: its epoch, then its members
def GroupRecord.stamp.cmp(a: GroupRecord, b: GroupRecord) -> Cmp:
  match a b:
    case GroupRecord{m1, e1} GroupRecord{m2, e2}:
      Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.List.order(~Spec.Member, ~Member.order, m1, m2))

# the members of a group
def GroupRecord.members(x: GroupRecord) -> List<&2, Spec.Member>:
  match x:
    case GroupRecord{ms, e}:
      ms

# a and b are the same topic
def Topic.same(a: Spec.Topic, b: Spec.Topic) -> Bool:
  match a b:
    case Spec.Topic.Affects{x} Spec.Topic.Affects{y}:
      String.eq(x, y)
    case Spec.Topic.Conflicts{x} Spec.Topic.Conflicts{y}:
      String.eq(x, y)
    case Spec.Topic.Versions{x} Spec.Topic.Versions{y}:
      String.eq(x, y)
    case Spec.Topic.Groups{} Spec.Topic.Groups{}:
      True{}
    case _ _:
      False{}

# The parts of a state
# --------------------
def NodeState.self(s: NodeState) -> String:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      k

def NodeState.versions(s: NodeState) -> Tables.Table<VersionRecord>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      vs

def NodeState.branches(s: NodeState) -> Tables.Table<BranchRecord>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      bs

def NodeState.marks(s: NodeState) -> Tables.Table<Tables.Table<MarkAt>>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      ms

def NodeState.groups(s: NodeState) -> Tables.Table<GroupRecord>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      gs

def NodeState.clashes(s: NodeState) -> Tables.Table<Clash>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      cs

def NodeState.seen(s: NodeState) -> Tables.Table<Seen>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      ss

def NodeState.log(s: NodeState) -> List<&2, Logged>:
  match s:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l}:
      l

# Reads
# -----

# the head of the branch that m holds
def BranchRecord.head.of(m: Maybe<&2, BranchRecord>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{BranchRecord{h, o, e, c}}:
      Some{h}

# the version that p names in s
def Point.version(s: NodeState, p: Spec.Point) -> Maybe<&2, String>:
  match p:
    case Spec.Point.At{v}:
      Some{v}
    case Spec.Point.Head{b}:
      BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b))
    case Spec.Point.Mark{b, m}:
      MarkAt.find(NodeState.marks(s), b, m)

# the resources of the version that m holds
def VersionRecord.blobs.of(m: Maybe<&2, VersionRecord>) -> Maybe<&2, Tables.Table<List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{VersionRecord{b, p, a, t}}:
      Some{b}

# the version that m names, among vs
def VersionRecord.find.of(
  vs: Tables.Table<VersionRecord>,
  m: Maybe<&2, String>
) -> Maybe<&2, VersionRecord>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Tables.Table.get(VersionRecord, vs, k)

# the bytes of the resource n among the resources that m holds
def Blob.find.of(m: Maybe<&2, Tables.Table<List<&2, U32>>>, n: String) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{bs}:
      Tables.Table.get(List<&2, U32>, bs, n)

# the resources of the version k among vs, none when vs does not hold it
def Vers.blobs(vs: Tables.Table<VersionRecord>, k: String) -> Tables.Table<List<&2, U32>>:
  Maybe.default(
    &2,
    Tables.Table<List<&2, U32>>,
    VersionRecord.blobs.of(Tables.Table.get(VersionRecord, vs, k)),
    Tables.Table.new(List<&2, U32>)
  )

# the bytes of the resource n at the point p of s
def NodeState.content(+s: NodeState, n: String, p: Spec.Point) -> Maybe<&2, List<&2, U32>>:
  Blob.find.of(
    VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s), Point.version(s, p))),
    n
  )

# one step of a walk: the versions it reached, the frontier after it, and the
# versions seen so far
type Walked is Data:
  Walked{
    reached: List<&2, Tables.Row<VersionRecord>>,
    next: List<&2, String>,
    done: List<&2, String>
  }

# the step of a walk at the version that m holds, with the frontier r after
def History.at(
  +k: String,
  r: List<&2, String>,
  done: List<&2, String>,
  m: Maybe<&2, VersionRecord>
) -> Walked:
  match m:
    case None{}:
      Walked{[], r, k <> done}
    case Some{VersionRecord{b, +p, a, t}}:
      Walked{[Tables.Row{k, VersionRecord{b, p, a, t}}], List.append(&2, String, r, p), k <> done}

# the step of a walk at the key k, skipped when done holds it (was)
def History.next(
  +k: String,
  r: List<&2, String>,
  done: List<&2, String>,
  vs: Tables.Table<VersionRecord>,
  was: Bool
) -> Walked:
  match was:
    case True{}:
      Walked{[], r, done}
    case False{}:
      History.at(k, r, done, Tables.Table.get(VersionRecord, vs, k))

def Walked.reached(w: Walked) -> List<&2, Tables.Row<VersionRecord>>:
  match w:
    case Walked{x, n, d}:
      x

def Walked.next(w: Walked) -> List<&2, String>:
  match w:
    case Walked{x, n, d}:
      n

def Walked.done(w: Walked) -> List<&2, String>:
  match w:
    case Walked{x, n, d}:
      d

# the parents of the version that m holds
def History.parents(m: Maybe<&2, VersionRecord>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{VersionRecord{b, p, a, t}}:
      p

# a version of vs among the keys ks names k as a parent
def VersionRecord.named(ks: List<&2, String>, +vs: Tables.Table<VersionRecord>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{j, r}:
      Bool.or(
        Shared.List.has(
          ~String,
          ~String.eq,
          History.parents(Tables.Table.get(VersionRecord, vs, j)),
          k
        ),
        VersionRecord.named(r, vs, k)
      )

# the ID k is taken: vs holds a version with it, or a version that names it as
# a parent, whose version lives on another node
def VersionRecord.taken(+vs: Tables.Table<VersionRecord>, +k: String) -> Bool:
  Bool.or(
    VersionRecord.has(vs, k),
    VersionRecord.named(Tables.Table.keys(VersionRecord, vs), vs, k)
  )

# the number of parent links of the versions with the keys ks
def History.links(ks: List<&2, String>, +vs: Tables.Table<VersionRecord>) -> Nat:
  match ks:
    case Nil{}:
      1n
    case Con{k, r}:
      Nat.add(
        1n+List.length(&2, String, History.parents(Tables.Table.get(VersionRecord, vs, k))),
        History.links(r, vs)
      )

# the versions reached from the frontier ks, in that order, without the ones
# in done: one key per step of the fuel f
def History.walk(
  f: Nat,
  ks: List<&2, String>,
  +done: List<&2, String>,
  +vs: Tables.Table<VersionRecord>
) -> List<&2, Tables.Row<VersionRecord>>:
  match f:
    case 0n:
      Nil{}
    case 1n+g:
      match ks:
        case Nil{}:
          Nil{}
        case Con{+k, r}:
          +w = History.next(k, r, done, vs, Shared.List.has(~String, ~String.eq, done, k))
          List.append(
            &2,
            Tables.Row<VersionRecord>,
            Walked.reached(w),
            History.walk(g, Walked.next(w), Walked.done(w), vs)
          )

# the version k and the versions it came from, among vs; fuel for every
# version, once per parent link
def History.of(+vs: Tables.Table<VersionRecord>, k: String) -> List<&2, Tables.Row<VersionRecord>>:
  History.walk(History.links(Tables.Table.keys(VersionRecord, vs), vs), [k], [], vs)

# Groups
# ------

# the members of the group that m holds; None when there is none
def GroupRecord.members.got(m: Maybe<&2, GroupRecord>) -> Maybe<&2, List<&2, Spec.Member>>:
  Maybe.map(&2, GroupRecord, List<&2, Spec.Member>, y => GroupRecord.members(y), m)

# the members of the group that m holds
def GroupRecord.members.in(m: Maybe<&2, GroupRecord>) -> List<&2, Spec.Member>:
  match m:
    case None{}:
      Nil{}
    case Some{GroupRecord{ms, e}}:
      ms

# the members of the group that m is, among gs; none for a node
def GroupRecord.members.of(gs: Tables.Table<GroupRecord>, m: Spec.Member) -> List<&2, Spec.Member>:
  match m:
    case Spec.Member.VendNode{n}:
      Nil{}
    case Spec.Member.Group{g}:
      GroupRecord.members.in(Tables.Table.get(GroupRecord, gs, g))

# the groups named ks, as members
def GroupRecord.groups(ks: List<&2, String>) -> List<&2, Spec.Member>:
  match ks:
    case Nil{}:
      []
    case Con{k, r}:
      Spec.Member.Group{k} <> GroupRecord.groups(r)

# the groups of gs, as members: the members that can have members
def GroupRecord.all(gs: Tables.Table<GroupRecord>) -> List<&2, Spec.Member>:
  GroupRecord.groups(Tables.Table.keys(GroupRecord, gs))

# gs with x as the group c; a node has no group to set
def GroupRecord.put(
  gs: Tables.Table<GroupRecord>,
  c: Spec.Member,
  x: GroupRecord
) -> Tables.Table<GroupRecord>:
  match c:
    case Spec.Member.VendNode{n}:
      gs
    case Spec.Member.Group{k}:
      Tables.Table.set(GroupRecord, gs, k, x)

# m is inside the group g of gs: a member of g, or of a group inside g
def GroupRecord.inside(gs: Tables.Table<GroupRecord>, m: Spec.Member, g: String) -> Bool:
  Reaches.Reach.in(
    ~Spec.Member,
    ~Tables.Table<GroupRecord>,
    ~Member.same,
    ~GroupRecord.members.of,
    ~GroupRecord.all,
    gs,
    Spec.Member.Group{g},
    m
  )

# Changes
# -------
# A change reads the state and says what to do (an Out); VendNode.ask applies it.
# A change never removes a version, and it writes no notice of its own: both
# are VendNode.ask's.

# nothing changes, and the answer is a
def Out.same(+s: NodeState, a: Spec.Answer) -> Out:
  Out{
    [],
    NodeState.branches(s),
    NodeState.marks(s),
    NodeState.groups(s),
    NodeState.clashes(s),
    [],
    a
  }

# the node of s is in the owner group of the branch b
def Owner.of(+s: NodeState, b: BranchRecord) -> Bool:
  match b:
    case BranchRecord{h, +o, e, c}:
      Bool.or(
        String.eq(o, NodeState.self(s)),
        GroupRecord.inside(NodeState.groups(s), Spec.Member.VendNode{NodeState.self(s)}, o)
      )

# the bytes that x names, for the resource n of s
def Content.bytes(s: NodeState, n: String, x: Spec.Content) -> Maybe<&2, List<&2, U32>>:
  match x:
    case Spec.Content.Bytes{y}:
      Some{y}
    case Spec.Content.Of{v}:
      NodeState.content(s, n, Spec.Point.At{v})

# m names the version k
def Base.is(m: Maybe<&2, String>, k: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{j}:
      String.eq(j, k)

# a new head h for the branch b, as its owner
def BranchRecord.moved(b: BranchRecord, h: String) -> BranchRecord:
  match b:
    case BranchRecord{old, o, e, c}:
      BranchRecord{h, o, e, 1n+c}

# the notice that the branch b has the new head v
def Logged.head(+b: String, v: String) -> Logged:
  Logged{Spec.Topic.Versions{b}, Spec.Notice.Versioned{b, v}}

# the answer to a write
def Write.answer(w: Spec.Write) -> Spec.Answer:
  Spec.Answer.Write{w}

# a write of y to n as the owner of br, the branch b, when its base is the head
# (ok)
def Write.at(
  ok: Bool,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  y: List<&2, U32>,
  br: BranchRecord
) -> Out:
  match ok:
    case False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out.same(s, Write.answer(Spec.Write.Stale{h}))
    case True{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Out{
            [
              Tables.Row{
                r,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, y),
                  [h],
                  w,
                  t
                }
              }
            ],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              b,
              BranchRecord.moved(BranchRecord{h, o, e, c}, r)
            ),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [Logged.head(b, r)],
            Write.answer(Spec.Write.Written{r})
          }

# a write of y to n on br, the branch b, as its owner or not
def Write.on(
  owner: Bool,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>,
  +br: BranchRecord
) -> Out:
  match owner:
    case True{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Write.at(Base.is(base, h), s, r, w, t, n, b, y, BranchRecord{h, o, e, c})
    case False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Out{
            [
              Tables.Row{
                r,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, y),
                  [h],
                  w,
                  t
                }
              }
            ],
            NodeState.branches(s),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [],
            Write.answer(Spec.Write.Pending{r})
          }

# a write of y to n on the branch b, which m holds when it exists
def Write.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> Out:
  match m:
    case Some{+br}:
      Write.on(Owner.of(s, br), s, r, w, t, n, b, base, y, br)
    case None{}:
      match base:
        case Some{k}:
          Out.same(s, Write.answer(Spec.Write.Refused{"no such branch"}))
        case None{}:
          Out{
            [
              Tables.Row{
                r,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, y),
                  [],
                  w,
                  t
                }
              }
            ],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              b,
              BranchRecord{r, NodeState.self(s), 0n, 0n}
            ),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [Logged.head(b, r)],
            Write.answer(Spec.Write.Written{r})
          }

# a write of y, unless the version ID r is taken
def Write.free(
  taken: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> Out:
  match taken:
    case True{}:
      Out.same(s, Write.answer(Spec.Write.Refused{"version ID taken"}))
    case False{}:
      Write.branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        t,
        n,
        b,
        base,
        y
      )

# a write of the bytes that m holds
def Write.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>
) -> Out:
  match m:
    case None{}:
      Out.same(s, Write.answer(Spec.Write.Refused{"no such content"}))
    case Some{y}:
      Write.free(VersionRecord.taken(NodeState.versions(s), r), s, r, w, t, n, b, base, y)

# the answer to a set-branch
def SetBranch.answer(a: Spec.SetBranch) -> Spec.Answer:
  Spec.Answer.SetBranch{a}

# the branch br set to the resources bs of a version, as its owner or not; r
# is the new version, unless its ID is taken
def SetBranch.on(
  owner: Bool,
  taken: Bool,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  +b: String,
  bs: Tables.Table<List<&2, U32>>,
  +br: BranchRecord
) -> Out:
  match owner taken:
    case _ True{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"version ID taken"}))
    case False{} False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out{
            [Tables.Row{r, VersionRecord{bs, [h], w, t}}],
            NodeState.branches(s),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [],
            SetBranch.answer(Spec.SetBranch.Pending{r})
          }
    case True{} False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Out{
            [Tables.Row{r, VersionRecord{bs, [h], w, t}}],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              b,
              BranchRecord.moved(BranchRecord{h, o, e, c}, r)
            ),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [Logged.head(b, r)],
            SetBranch.answer(Spec.SetBranch.Restored{r})
          }

# the branch b set to the version k, whose resources bs are; m holds b when
# it exists
def SetBranch.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  +b: String,
  +k: String,
  bs: Tables.Table<List<&2, U32>>
) -> Out:
  match m:
    case None{}:
      Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord{k, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, k)],
        SetBranch.answer(Spec.SetBranch.Created{k})
      }
    case Some{+br}:
      SetBranch.on(
        Owner.of(s, br),
        VersionRecord.taken(NodeState.versions(s), r),
        s,
        r,
        w,
        t,
        b,
        bs,
        br
      )

# the branch b set to the version k, which m holds when s has it
def SetBranch.version(
  m: Maybe<&2, VersionRecord>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +b: String,
  k: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"no such version"}))
    case Some{VersionRecord{bs, p, a, z}}:
      SetBranch.branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        t,
        b,
        k,
        bs
      )

# the branch b set to the version that m names
def SetBranch.point(
  m: Maybe<&2, String>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  b: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"no such point"}))
    case Some{+k}:
      SetBranch.version(Tables.Table.get(VersionRecord, NodeState.versions(s), k), s, r, w, t, b, k)

# the answer to a create-mark
def CreateMark.answer(a: Spec.CreateMark) -> Spec.Answer:
  Spec.Answer.CreateMark{a}

# the mark m of br with the message x, unless m names a version of br (held)
def CreateMark.free(
  held: Maybe<&2, String>,
  +s: NodeState,
  b: String,
  +m: String,
  x: String,
  br: BranchRecord
) -> Out:
  match held:
    case Some{k}:
      Out.same(s, CreateMark.answer(Spec.CreateMark.Taken{}))
    case None{}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out{
            [],
            NodeState.branches(s),
            MarkAt.set(NodeState.marks(s), b, m, MarkAt{h, x}),
            NodeState.groups(s),
            NodeState.clashes(s),
            [],
            CreateMark.answer(Spec.CreateMark.Marked{m})
          }

# the mark m with the message x on the branch b, which f holds when it exists
def CreateMark.branch(
  f: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +b: String,
  +m: String,
  x: String
) -> Out:
  match f:
    case None{}:
      Out.same(s, CreateMark.answer(Spec.CreateMark.Refused{"no such branch"}))
    case Some{br}:
      CreateMark.free(MarkAt.find(NodeState.marks(s), b, m), s, b, m, x, br)

# the answer to a set-owner
def SetOwner.answer(a: Spec.SetOwner) -> Spec.Answer:
  Spec.Answer.SetOwner{a}

# the owner group g for br, when the node of s owns br
def SetOwner.on(owner: Bool, +s: NodeState, b: String, g: String, br: BranchRecord) -> Out:
  match owner:
    case False{}:
      Out.same(s, SetOwner.answer(Spec.SetOwner.Refused{"not the owner"}))
    case True{}:
      match br:
        case BranchRecord{h, o, +e, c}:
          Out{
            [],
            Tables.Table.set(BranchRecord, NodeState.branches(s), b, BranchRecord{h, g, 1n+e, 0n}),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [],
            SetOwner.answer(Spec.SetOwner.Set{1n+e})
          }

# the owner group g for the branch that f holds
def SetOwner.branch(f: Maybe<&2, BranchRecord>, +s: NodeState, b: String, g: String) -> Out:
  match f:
    case None{}:
      Out.same(s, SetOwner.answer(Spec.SetOwner.Refused{"no such branch"}))
    case Some{+br}:
      SetOwner.on(Owner.of(s, br), s, b, g, br)

# the answer to a set-group
def SetGroup.answer(a: Spec.SetGroup) -> Spec.Answer:
  Spec.Answer.SetGroup{a}

# the epoch of the group that m holds, or none
def GroupRecord.epoch.of(m: Maybe<&2, GroupRecord>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{GroupRecord{ms, e}}:
      e

# the epoch that the group g gets when it is set next
def GroupRecord.epoch.next(gs: Tables.Table<GroupRecord>, g: String) -> Nat:
  1n+GroupRecord.epoch.of(Tables.Table.get(GroupRecord, gs, g))

# setting the members of the group g to ms closes a cycle: a member of ms is
# g, or has g inside it
def Cycle.has(gs: Tables.Table<GroupRecord>, g: String, ms: List<&2, Spec.Member>) -> Bool:
  Reaches.Reach.closes(
    ~Spec.Member,
    ~Tables.Table<GroupRecord>,
    ~Member.same,
    ~GroupRecord.members.of,
    ~GroupRecord.all,
    gs,
    Spec.Member.Group{g},
    ms
  )

# the group g with the members ms, unless that closes a cycle
def SetGroup.on(cycle: Bool, +s: NodeState, +g: String, ms: List<&2, Spec.Member>) -> Out:
  match cycle:
    case True{}:
      Out.same(s, SetGroup.answer(Spec.SetGroup.Cycle{}))
    case False{}:
      Out{
        [],
        NodeState.branches(s),
        NodeState.marks(s),
        Tables.Table.set(
          GroupRecord,
          NodeState.groups(s),
          g,
          GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)}
        ),
        NodeState.clashes(s),
        [],
        SetGroup.answer(Spec.SetGroup.Set{GroupRecord.epoch.next(NodeState.groups(s), g)})
      }

# the IDs of vs
def Vers.ids(vs: List<&2, Tables.Row<VersionRecord>>) -> List<&2, String>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Tables.Row{i, v}, r}:
      i <> Vers.ids(r)

# the first version of vs whose ID ks holds
def Vers.first_in(
  vs: List<&2, Tables.Row<VersionRecord>>,
  +ks: List<&2, String>
) -> Maybe<&2, String>:
  match vs:
    case Nil{}:
      None{}
    case Con{Tables.Row{+i, v}, r}:
      List.find.if(
        String,
        i,
        u => Vers.first_in(r, ks),
        Shared.List.has(~String, ~String.eq, ks, i)
      )

# what a three-way merge picks for one resource
type Picked is Data:
  Picked.Take{held: Maybe<&2, List<&2, U32>>}
  Picked.Clash{}

# the pick for h (the head's bytes) and f (the bytes merged in), given whether
# f is the base (fo), h is the base (ho), and h is f (hf)
def Picked.of(
  fo: Bool,
  ho: Bool,
  hf: Bool,
  h: Maybe<&2, List<&2, U32>>,
  f: Maybe<&2, List<&2, U32>>
) -> Picked:
  match fo ho hf:
    case True{} _ _:
      Picked.Take{h}
    case False{} True{} _:
      Picked.Take{f}
    case False{} False{} True{}:
      Picked.Take{h}
    case False{} False{} False{}:
      Picked.Clash{}

# the pick for the resource n, from the head's resources hb, the resources
# merged in fb, and the base's bb
def Picked.at(
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>,
  +n: String
) -> Picked:
  Picked.of(
    Maybes.Maybe.same(
      ~List<&2, U32>,
      ~Octets.Bytes.is_eq,
      Tables.Table.get(List<&2, U32>, fb, n),
      Tables.Table.get(List<&2, U32>, bb, n)
    ),
    Maybes.Maybe.same(
      ~List<&2, U32>,
      ~Octets.Bytes.is_eq,
      Tables.Table.get(List<&2, U32>, hb, n),
      Tables.Table.get(List<&2, U32>, bb, n)
    ),
    Maybes.Maybe.same(
      ~List<&2, U32>,
      ~Octets.Bytes.is_eq,
      Tables.Table.get(List<&2, U32>, hb, n),
      Tables.Table.get(List<&2, U32>, fb, n)
    ),
    Tables.Table.get(List<&2, U32>, hb, n),
    Tables.Table.get(List<&2, U32>, fb, n)
  )

# rest, with the resource n when p keeps its bytes
def Picked.blob(
  p: Picked,
  n: String,
  rest: Tables.Table<List<&2, U32>>
) -> Tables.Table<List<&2, U32>>:
  match p:
    case Picked.Take{Some{x}}:
      Tables.Table.set(List<&2, U32>, rest, n, x)
    case _:
      rest

# rest, with n when p clashes
def Picked.clash(p: Picked, n: String, rest: List<&2, String>) -> List<&2, String>:
  match p:
    case Picked.Clash{}:
      n <> rest
    case _:
      rest

# the merged resources of the names ns that do not clash
def Merge.blobs(
  ns: List<&2, String>,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>
) -> Tables.Table<List<&2, U32>>:
  match ns:
    case Nil{}:
      Tables.Table.new(List<&2, U32>)
    case Con{+n, r}:
      Picked.blob(Picked.at(hb, fb, bb, n), n, Merge.blobs(r, hb, fb, bb))

# the names of ns that clash
def Merge.clashes(
  ns: List<&2, String>,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>
) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, r}:
      Picked.clash(Picked.at(hb, fb, bb, n), n, Merge.clashes(r, hb, fb, bb))

# the answer to a merge
def Merge.answer(a: Spec.Merge) -> Spec.Answer:
  Spec.Answer.Merge{a}

# the merge r of the version f into br: its merged resources bs, and the names
# that clash (cs)
def Merge.result(
  cs: List<&2, String>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  f: String,
  +b: String,
  bs: Tables.Table<List<&2, U32>>,
  br: BranchRecord
) -> Out:
  match cs:
    case Nil{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Out{
            [Tables.Row{r, VersionRecord{bs, [h, f], w, t}}],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              b,
              BranchRecord.moved(BranchRecord{h, o, e, c}, r)
            ),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [Logged.head(b, r)],
            Merge.answer(Spec.Merge.Merged{r})
          }
    case Con{k, more}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out{
            [],
            NodeState.branches(s),
            NodeState.marks(s),
            NodeState.groups(s),
            Tables.Table.set(Clash, NodeState.clashes(s), r, Clash{b, h, f, bs, k <> more}),
            [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}],
            Merge.answer(Spec.Merge.Conflicted{r})
          }

# the merge of the version f into br, from the resources of its head hb, of f
# (fb), and of their base (bb)
def Merge.three(
  s: NodeState,
  r: String,
  w: String,
  t: String,
  f: String,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>,
  b: String,
  br: BranchRecord
) -> Out:
  +ns = Strings.union(
    Tables.Table.keys(List<&2, U32>, bb),
    Strings.union(
      Tables.Table.keys(List<&2, U32>, fb),
      Strings.union(Tables.Table.keys(List<&2, U32>, hb), [])
    )
  )
  Merge.result(Merge.clashes(ns, hb, fb, bb), s, r, w, t, f, b, Merge.blobs(ns, hb, fb, bb), br)

# the resources of the base that m holds, none without a base
def Merge.base(s: NodeState, m: Maybe<&2, String>) -> Tables.Table<List<&2, U32>>:
  match m:
    case None{}:
      Tables.Table.new(List<&2, U32>)
    case Some{k}:
      Vers.blobs(NodeState.versions(s), k)

# the merge of the version f into br, unless the head already holds f
def Merge.inside(
  held: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: BranchRecord
) -> Out:
  match held:
    case True{}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out.same(s, Merge.answer(Spec.Merge.Merged{h}))
    case False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          hh = History.of(NodeState.versions(s), h)
          Merge.three(
            s,
            r,
            w,
            t,
            f,
            Vers.blobs(NodeState.versions(s), h),
            Vers.blobs(NodeState.versions(s), f),
            Merge.base(s, Vers.first_in(History.of(NodeState.versions(s), f), Vers.ids(hh))),
            b,
            BranchRecord{h, o, e, c}
          )

# the merge of the version f into br, as its owner, unless the ID r is taken
def Merge.owner(
  owner: Bool,
  taken: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: BranchRecord
) -> Out:
  match owner taken:
    case False{} _:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"not the owner"}))
    case True{} True{}:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"version ID taken"}))
    case True{} False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          Merge.inside(
            Shared.List.has(~String, ~String.eq, Vers.ids(History.of(NodeState.versions(s), h)), f),
            s,
            r,
            w,
            t,
            f,
            b,
            BranchRecord{h, o, e, c}
          )

# the merge of the version f into the branch that m holds
def Merge.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  f: String,
  b: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"no such branch"}))
    case Some{+br}:
      Merge.owner(
        Owner.of(s, br),
        VersionRecord.taken(NodeState.versions(s), r),
        s,
        r,
        w,
        t,
        f,
        b,
        br
      )

# the merge of the version that m names into the branch b
def Merge.point(
  m: Maybe<&2, String>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +b: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"no such point"}))
    case Some{f}:
      Merge.branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, r, w, t, f, b)

# the names whose texts are ks
def Names.of(ks: List<&2, String>) -> List<&2, Resources.Name>:
  match ks:
    case Nil{}:
      []
    case Con{k, r}:
      Resources.Name{k} <> Names.of(r)

# the answer to a resolve
def Resolve.answer(a: Spec.Resolve) -> Spec.Answer:
  Spec.Answer.Resolve{a}

# the clash k after its resource n got y: the names that still clash (left),
# and whether the version ID r is taken
def Resolve.done(
  left: List<&2, String>,
  taken: Bool,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  y: List<&2, U32>,
  cl: Clash,
  br: BranchRecord
) -> Out:
  match left:
    case Nil{}:
      match taken:
        case True{}:
          Out.same(s, Resolve.answer(Spec.Resolve.Refused{"version ID taken"}))
        case False{}:
          match cl br:
            case Clash{+b, h, f, bs, l} BranchRecord{h2, o, e, c}:
              Out{
                [
                  Tables.Row{
                    r,
                    VersionRecord{Tables.Table.set(List<&2, U32>, bs, n, y), [h, f], w, t}
                  }
                ],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s),
                  b,
                  BranchRecord.moved(BranchRecord{h2, o, e, c}, r)
                ),
                NodeState.marks(s),
                NodeState.groups(s),
                Tables.Table.del(Clash, NodeState.clashes(s), k),
                [Logged.head(b, r)],
                Resolve.answer(Spec.Resolve.Resolved{r})
              }
    case Con{+x, +more}:
      match cl:
        case Clash{b, h, f, bs, l}:
          Out{
            [],
            NodeState.branches(s),
            NodeState.marks(s),
            NodeState.groups(s),
            Tables.Table.set(
              Clash,
              NodeState.clashes(s),
              k,
              Clash{b, h, f, Tables.Table.set(List<&2, U32>, bs, n, y), x <> more}
            ),
            [],
            Resolve.answer(Spec.Resolve.Left{Names.of(x <> more)})
          }

# the clash k settled for n with the bytes that m holds
def Resolve.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  +cl: Clash,
  br: BranchRecord
) -> Out:
  match m:
    case None{}:
      Out.same(s, Resolve.answer(Spec.Resolve.Refused{"no such content"}))
    case Some{y}:
      match cl:
        case Clash{b, h, f, bs, +l}:
          Resolve.done(
            Shared.List.remove(~String, ~String.eq, l, n),
            VersionRecord.taken(NodeState.versions(s), r),
            s,
            r,
            w,
            t,
            k,
            n,
            y,
            Clash{b, h, f, bs, l},
            br
          )

# the clash k settled for n with x, when its head is still the branch's (ok)
def Resolve.fresh(
  ok: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content,
  cl: Clash,
  br: BranchRecord
) -> Out:
  match ok:
    case False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          Out.same(s, Resolve.answer(Spec.Resolve.Stale{h}))
    case True{}:
      Resolve.bytes(Content.bytes(s, n, x), s, r, w, t, k, n, cl, br)

# the clash k settled for n with x, on the branch that m holds
def Resolve.branch(
  m: Maybe<&2, BranchRecord>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> Out:
  match m:
    case None{}:
      Out.same(s, Resolve.answer(Spec.Resolve.Refused{"no such branch"}))
    case Some{BranchRecord{+h, o, e, c}}:
      match cl:
        case Clash{b2, +h2, f, bs, l}:
          Resolve.fresh(
            String.eq(h, h2),
            s,
            r,
            w,
            t,
            k,
            n,
            x,
            Clash{b2, h2, f, bs, l},
            BranchRecord{h, o, e, c}
          )

# the clash k settled for n with x, when n clashes in it (has)
def Resolve.named(
  has: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> Out:
  match has:
    case False{}:
      Out.same(s, Resolve.answer(Spec.Resolve.Refused{"not a clashing resource"}))
    case True{}:
      match cl:
        case Clash{+b, h, f, bs, l}:
          Resolve.branch(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b),
            s,
            r,
            w,
            t,
            k,
            n,
            x,
            Clash{b, h, f, bs, l}
          )

# the clash that m holds, settled for n with x
def Resolve.clash(
  m: Maybe<&2, Clash>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content
) -> Out:
  match m:
    case None{}:
      Out.same(s, Resolve.answer(Spec.Resolve.Refused{"no such conflict"}))
    case Some{Clash{b, h, f, bs, +l}}:
      Resolve.named(
        Shared.List.has(~String, ~String.eq, l, n),
        s,
        r,
        w,
        t,
        k,
        n,
        x,
        Clash{b, h, f, bs, l}
      )

# the answer to a sync
def Sync.answer(a: Spec.Sync) -> Spec.Answer:
  Spec.Answer.Sync{a}

# the order of the stamps of the heads of a and b: epoch, then count, then
# the head's ID, so that every node picks the same winner
def BranchRecord.stamp.cmp(a: BranchRecord, b: BranchRecord) -> Cmp:
  match a b:
    case BranchRecord{h1, o1, e1, c1} BranchRecord{h2, o2, e2, c2}:
      Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))

# both lookups found a version under the same ID, with other resources
def Sync.clash.at(mine: Maybe<&2, VersionRecord>, theirs: Maybe<&2, VersionRecord>) -> Bool:
  match mine theirs:
    case Some{VersionRecord{b1, p1, a1, t1}} Some{VersionRecord{b2, p2, a2, t2}}:
      Bool.not(Tables.Table.same(~List<&2, U32>, ~Octets.Bytes.is_eq, b1, b2))
    case _ _:
      False{}

# a version of os under one of the keys ks has the ID of a version of vs, with
# other resources
def Sync.collides(
  ks: List<&2, String>,
  +os: Tables.Table<VersionRecord>,
  +vs: Tables.Table<VersionRecord>
) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, r}:
      Bool.or(
        Sync.clash.at(
          Tables.Table.get(VersionRecord, vs, k),
          Tables.Table.get(VersionRecord, os, k)
        ),
        Sync.collides(r, os, vs)
      )

# the names of ns whose bytes differ between the resources a and b
def Names.differ(
  ns: List<&2, String>,
  +a: Tables.Table<List<&2, U32>>,
  +b: Tables.Table<List<&2, U32>>
) -> List<&2, String>:
  match ns:
    case Nil{}:
      Nil{}
    case Con{+n, r}:
      List.filter.put(
        String,
        n,
        Names.differ(r, a, b),
        Bool.not(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, a, n),
            Tables.Table.get(List<&2, U32>, b, n)
          )
        )
      )

# what a sync does to branches: the branches, the clashes, and the notices
type Mix is Data:
  Mix{branches: Tables.Table<BranchRecord>, clashes: Tables.Table<Clash>, news: List<&2, Logged>}

# cs, with the clash of the head l, unless h's history holds l (held) or no
# resource differs (ns)
def Sync.lost.if(
  held: Bool,
  ns: List<&2, String>,
  h: String,
  b: String,
  +l: String,
  hb: Tables.Table<List<&2, U32>>,
  cs: Tables.Table<Clash>
) -> Tables.Table<Clash>:
  match held ns:
    case True{} _:
      cs
    case False{} Nil{}:
      cs
    case False{} Con{n, r}:
      Tables.Table.set(Clash, cs, l, Clash{b, h, l, hb, n <> r})

# cs, with a clash when the head l of the branch b lost to the head h and is
# not in its history; its resources that differ from h's clash
def Sync.lost(
  +vs: Tables.Table<VersionRecord>,
  +h: String,
  b: String,
  +l: String,
  cs: Tables.Table<Clash>
) -> Tables.Table<Clash>:
  +hb = Vers.blobs(vs, h)
  +lb = Vers.blobs(vs, l)
  Sync.lost.if(
    Shared.List.has(~String, ~String.eq, Vers.ids(History.of(vs, h)), l),
    Names.differ(
      Strings.union(
        Tables.Table.keys(List<&2, U32>, lb),
        Strings.union(Tables.Table.keys(List<&2, U32>, hb), [])
      ),
      hb,
      lb
    ),
    h,
    b,
    l,
    hb,
    cs
  )

# the branches after their mine and theirs met, for the branch b, by the order
# c of their stamps; the winner's head is the branch's, and the loser may clash
def Sync.pick(
  c: Cmp,
  +b: String,
  mine: BranchRecord,
  theirs: BranchRecord,
  vs: Tables.Table<VersionRecord>,
  acc: Mix
) -> Mix:
  match c mine theirs acc:
    case LT{} BranchRecord{h1, o1, e1, c1} BranchRecord{+h, o, e, k} Mix{bs, cs, ns}:
      Mix{
        Tables.Table.set(BranchRecord, bs, b, BranchRecord{h, o, e, k}),
        Sync.lost(vs, h, b, h1, cs),
        List.append(&2, Logged, ns, [Logged.head(b, h)])
      }
    case GT{} BranchRecord{h, o, e, k} BranchRecord{h2, o2, e2, c2} Mix{bs, cs, ns}:
      Mix{bs, Sync.lost(vs, h, b, h2, cs), ns}
    case EQ{} m t z:
      z

# the branches after theirs, the branch b, met the one that m holds
def Sync.at(
  m: Maybe<&2, BranchRecord>,
  +b: String,
  +theirs: BranchRecord,
  vs: Tables.Table<VersionRecord>,
  acc: Mix
) -> Mix:
  match m:
    case None{}:
      match theirs acc:
        case BranchRecord{+h, o, e, k} Mix{bs, cs, ns}:
          Mix{
            Tables.Table.set(BranchRecord, bs, b, BranchRecord{h, o, e, k}),
            cs,
            List.append(&2, Logged, ns, [Logged.head(b, h)])
          }
    case Some{+mine}:
      Sync.pick(BranchRecord.stamp.cmp(mine, theirs), b, mine, theirs, vs, acc)

# the branches after theirs, the branch b, met them
def Sync.meet(acc: Mix, +b: String, theirs: BranchRecord, vs: Tables.Table<VersionRecord>) -> Mix:
  match acc:
    case Mix{+bs, cs, ns}:
      Sync.at(Tables.Table.get(BranchRecord, bs, b), b, theirs, vs, Mix{bs, cs, ns})

# the branches after the branch b that m holds met them; none when m is empty
def Sync.seen.meet(
  b: String,
  m: Maybe<&2, BranchRecord>,
  acc: Mix,
  vs: Tables.Table<VersionRecord>
) -> Mix:
  match m:
    case None{}:
      acc
    case Some{br}:
      Sync.meet(acc, b, br, vs)

# the branches after the branch of each key of ks in full met them
def Sync.branches(
  ks: List<&2, String>,
  +full: Tables.Table<BranchRecord>,
  +vs: Tables.Table<VersionRecord>,
  acc: Mix
) -> Mix:
  match ks:
    case Nil{}:
      acc
    case Con{+k, r}:
      Sync.branches(
        r,
        full,
        vs,
        Sync.seen.meet(k, Tables.Table.get(BranchRecord, full, k), acc, vs)
      )

def Mix.branches(m: Mix) -> Tables.Table<BranchRecord>:
  match m:
    case Mix{bs, cs, ns}:
      bs

def Mix.clashes(m: Mix) -> Tables.Table<Clash>:
  match m:
    case Mix{bs, cs, ns}:
      cs

def Mix.news(m: Mix) -> List<&2, Logged>:
  match m:
    case Mix{bs, cs, ns}:
      ns

# what a sync does to marks: the marks, and the notices of the ones it moved
type Marked is Data:
  Marked{marks: Tables.Table<Tables.Table<MarkAt>>, news: List<&2, Logged>}

# the marks with x as the mark m of the branch b, whose version is smaller
# than k (smaller): x wins, with a notice that the mark moved from k
def Sync.mark.smaller(
  smaller: Bool,
  +b: String,
  +m: String,
  k: String,
  x: MarkAt,
  acc: Marked
) -> Marked:
  match smaller x acc:
    case True{} MarkAt{+v, t} Marked{ms, ns}:
      Marked{
        MarkAt.set(ms, b, m, MarkAt{v, t}),
        List.append(
          &2,
          Logged,
          ns,
          [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.MarkMoved{b, m, k, v}}]
        )
      }
    case False{} y z:
      z

# the marks after their mark x, the mark m of the branch b, met the version
# that own holds: the smaller version wins, so that every node keeps the same
def Sync.mark.at(own: Maybe<&2, String>, b: String, m: String, x: MarkAt, acc: Marked) -> Marked:
  match own x acc:
    case None{} y Marked{ms, ns}:
      Marked{MarkAt.set(ms, b, m, y), ns}
    case Some{+k} MarkAt{+v, t} z:
      Sync.mark.smaller(Cmp.is_lt(String.order(v, k)), b, m, k, MarkAt{v, t}, z)

# the marks after the mark that vis holds, the mark m of the branch b, met them
def Sync.mark.seen(+b: String, +m: String, vis: Maybe<&2, MarkAt>, acc: Marked) -> Marked:
  match vis acc:
    case None{} z:
      z
    case Some{x} Marked{+ms, ns}:
      Sync.mark.at(MarkAt.find(ms, b, m), b, m, x, Marked{ms, ns})

# the marks after each mark of the names ms of the branch b, in inner, met them
def Sync.marks.of(
  +b: String,
  ms: List<&2, String>,
  +inner: Tables.Table<MarkAt>,
  acc: Marked
) -> Marked:
  match ms:
    case Nil{}:
      acc
    case Con{+m, r}:
      Sync.marks.of(b, r, inner, Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc))

# the marks after the marks of each branch of bks in full met them
def Sync.marks(
  bks: List<&2, String>,
  +full: Tables.Table<Tables.Table<MarkAt>>,
  acc: Marked
) -> Marked:
  match bks:
    case Nil{}:
      acc
    case Con{+b, r}:
      +inner = Marks.of(full, b)
      Sync.marks(r, full, Sync.marks.of(b, Tables.Table.keys(MarkAt, inner), inner, acc))

def Marked.marks(m: Marked) -> Tables.Table<Tables.Table<MarkAt>>:
  match m:
    case Marked{ms, ns}:
      ms

def Marked.news(m: Marked) -> List<&2, Logged>:
  match m:
    case Marked{ms, ns}:
      ns

# what a sync does to groups: the groups, and the notices of the ones it kept
type Kept is Data:
  Kept{groups: Tables.Table<GroupRecord>, news: List<&2, Logged>}

# the groups with x as g. A notice says when x closes a cycle: the groups on
# it then hold one another (see none_inside_itself_after in the spec)
def Sync.group.put(+g: String, x: GroupRecord, k: Kept) -> Kept:
  match x k:
    case GroupRecord{+ms, e} Kept{+gs, ns}:
      Kept{
        Tables.Table.set(GroupRecord, gs, g, GroupRecord{ms, e}),
        List.append(
          &2,
          Logged,
          ns,
          List.filter.put(
            Logged,
            Logged{Spec.Topic.Groups{}, Spec.Notice.GroupCycle{g, ms}},
            [],
            Cycle.has(gs, g, ms)
          )
        )
      }

# the groups after the other node's group x, named g, met the node's own: the
# larger stamp (c) wins
def Sync.group.pick(c: Cmp, g: String, x: GroupRecord, k: Kept) -> Kept:
  match c:
    case LT{}:
      Sync.group.put(g, x, k)
    case EQ{}:
      k
    case GT{}:
      k

# the groups after their group x, named g, met the group that m holds
def Sync.group.at(m: Maybe<&2, GroupRecord>, g: String, +x: GroupRecord, k: Kept) -> Kept:
  match m:
    case None{}:
      Sync.group.put(g, x, k)
    case Some{mine}:
      Sync.group.pick(GroupRecord.stamp.cmp(mine, x), g, x, k)

# the groups after the group that vis holds, named g, met them
def Sync.group.seen(+g: String, vis: Maybe<&2, GroupRecord>, k: Kept) -> Kept:
  match vis k:
    case None{} z:
      z
    case Some{x} Kept{+gs, ns}:
      Sync.group.at(Tables.Table.get(GroupRecord, gs, g), g, x, Kept{gs, ns})

# the groups after the group of each key of ks in full met them
def Sync.groups(ks: List<&2, String>, +full: Tables.Table<GroupRecord>, k: Kept) -> Kept:
  match ks:
    case Nil{}:
      k
    case Con{+g, r}:
      Sync.groups(r, full, Sync.group.seen(g, Tables.Table.get(GroupRecord, full, g), k))

def Kept.groups(k: Kept) -> Tables.Table<GroupRecord>:
  match k:
    case Kept{gs, ns}:
      gs

def Kept.news(k: Kept) -> List<&2, Logged>:
  match k:
    case Kept{gs, ns}:
      ns

# s after it took in o, unless their versions collide; it takes in all of o,
# since a position only narrows what the transport sends
def Sync.go(collides: Bool, +s: NodeState, +o: NodeState) -> Out:
  match collides:
    case True{}:
      Out.same(s, Sync.answer(Spec.Sync.Refused{"version ID collision"}))
    case False{}:
      +news = Tables.Table.rows(
        VersionRecord,
        Tables.Table.keys(VersionRecord, NodeState.versions(o)),
        NodeState.versions(o)
      )
      +mix = Sync.branches(
        Tables.Table.keys(BranchRecord, NodeState.branches(o)),
        NodeState.branches(o),
        VersionRecord.add(news, NodeState.versions(s)),
        Mix{NodeState.branches(s), NodeState.clashes(s), []}
      )
      +kept = Sync.groups(
        Tables.Table.keys(GroupRecord, NodeState.groups(o)),
        NodeState.groups(o),
        Kept{NodeState.groups(s), []}
      )
      +marked = Sync.marks(
        Tables.Table.keys(Tables.Table<MarkAt>, NodeState.marks(o)),
        NodeState.marks(o),
        Marked{NodeState.marks(s), []}
      )
      Out{
        news,
        Mix.branches(mix),
        Marked.marks(marked),
        Kept.groups(kept),
        Mix.clashes(mix),
        List.append(
          &2,
          Logged,
          List.append(&2, Logged, Mix.news(mix), Kept.news(kept)),
          Marked.news(marked)
        ),
        Sync.answer(Spec.Sync.Synced{})
      }

# The node
# --------

# what the change q of the request r, by the writer w at the time t, does to s
def Step.of(+s: NodeState, r: String, w: String, t: String, q: Spec.Ask) -> Out:
  match q:
    case Spec.Ask.Write{Resources.Name{+n}, b, base, x}:
      Write.bytes(Content.bytes(s, n, x), s, r, w, t, n, b, base)
    case Spec.Ask.SetBranch{b, p}:
      SetBranch.point(Point.version(s, p), s, r, w, t, b)
    case Spec.Ask.CreateMark{+b, m, x}:
      CreateMark.branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, b, m, x)
    case Spec.Ask.Merge{p, b}:
      Merge.point(Point.version(s, p), s, r, w, t, b)
    case Spec.Ask.Resolve{+k, Resources.Name{n}, x}:
      Resolve.clash(Tables.Table.get(Clash, NodeState.clashes(s), k), s, r, w, t, k, n, x)
    case Spec.Ask.SetOwner{+b, g}:
      SetOwner.branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, b, g)
    case Spec.Ask.SetGroup{+g, +ms}:
      SetGroup.on(Cycle.has(NodeState.groups(s), g, ms), s, g, ms)
    case Spec.Ask.Sync{+o, p}:
      Sync.go(
        Sync.collides(
          Tables.Table.keys(VersionRecord, NodeState.versions(o)),
          NodeState.versions(o),
          NodeState.versions(s)
        ),
        s,
        o
      )

# s after out, the answer to the request r: new versions join the ones s
# holds, the answer is kept for retries, and the notices go last
def VendNode.applied(s: NodeState, r: String, out: Out) -> NodeState & Spec.Answer:
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, +l} Out{nv, nb, nm, ng, nc, news, +a}:
      (
        NodeState{
          k,
          VersionRecord.add(nv, vs),
          nb,
          nm,
          ng,
          nc,
          Tables.Table.set(Seen, ss, r, Seen{a, List.length(&2, Logged, l)}),
          List.append(&2, Logged, l, news)
        },
        a
      )

# s after the change q of the request r, unless found holds r's answer
def VendNode.asked(
  found: Maybe<&2, Seen>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  q: Spec.Ask
) -> NodeState
  & Spec.Answer:
  match found:
    case Some{Seen{a, p}}:
      (s, a)
    case None{}:
      VendNode.applied(s, r, Step.of(s, r, w, t, q))

# a unit of content: its format, kind, name, place, condition and parent
type Piece is Data:
  Piece{
    format: String,
    kind: String,
    name: String,
    place: String,
    condition: Maybe<&2, String>,
    parent: Maybe<&2, Piece>
  }

# a change that touches an item that other work uses
type Touched is Data:
  Touched{version: String, changed: Piece, used: Piece}

def Spec.Item():
  Piece

def Spec.Touch():
  Touched

# the resource n as one item: without a format that decodes it, the core sees
# a resource as a whole
def Piece.of(+n: String) -> Piece:
  Piece{"bytes", "resource", n, n, None{}, None{}}

# no change when same, else i edited
def Diff.if(same: Bool, +i: Piece) -> List<&2, Spec.Change>:
  match same:
    case True{}:
      Nil{}
    case False{}:
      [Spec.Change.Edited{i, i}]

# the change from a to b of the item i
def Diff.of(
  i: Piece,
  a: Maybe<&2, List<&2, U32>>,
  b: Maybe<&2, List<&2, U32>>
) -> List<&2, Spec.Change>:
  match a b:
    case None{} None{}:
      Nil{}
    case None{} Some{y}:
      [Spec.Change.Added{i}]
    case Some{x} None{}:
      [Spec.Change.Removed{i}]
    case Some{x} Some{y}:
      Diff.if(Octets.Bytes.is_eq(x, y), i)

# the notices of xs whose topic is k
def Logged.pick(+k: Spec.Topic, xs: List<&2, Logged>) -> List<&2, Spec.Notice>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{Logged{t, n}, r}:
      List.filter.put(Spec.Notice, n, Logged.pick(k, r), Topic.same(t, k))

# the versions of vs that hold the resource n
def Log.of(
  vs: List<&2, Tables.Row<VersionRecord>>,
  +n: String
) -> List<&2, Tables.Row<VersionRecord>>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Tables.Row{i, VersionRecord{+b, p, a, t}}, r}:
      List.filter.put(
        Tables.Row<VersionRecord>,
        Tables.Row{i, VersionRecord{b, p, a, t}},
        Log.of(r, n),
        Maybe.is_some(&2, List<&2, U32>, Tables.Table.get(List<&2, U32>, b, n))
      )

# the history of the head that m holds, among vs
def Log.history(
  vs: Tables.Table<VersionRecord>,
  m: Maybe<&2, String>
) -> List<&2, Tables.Row<VersionRecord>>:
  match m:
    case None{}:
      Nil{}
    case Some{h}:
      History.of(vs, h)

# whether the request r happened: found holds its answer, or held says that a
# version has its ID; at is the position now
def Outcome.of(found: Maybe<&2, Seen>, held: Bool, at: Nat) -> Spec.Outcome:
  match found held:
    case Some{Seen{a, p}} _:
      Spec.Outcome.Applied{p}
    case None{} True{}:
      Spec.Outcome.Applied{at}
    case None{} False{}:
      Spec.Outcome.NotSeen{}

# the epoch of the branch that m holds
def BranchRecord.epoch.of(m: Maybe<&2, BranchRecord>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{BranchRecord{h, o, e, c}}:
      Some{e}

# the node of s owns the branch that m holds
def Owner.in(s: NodeState, m: Maybe<&2, BranchRecord>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{br}:
      Owner.of(s, br)

# The spec's node
# ---------------
def Spec.Item.format(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      f

def Spec.Item.kind(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      k

def Spec.Item.name(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      n

def Spec.Item.place(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      p

def Spec.Item.condition(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      c

def Spec.Item.parent(i):
  match i:
    case Piece{f, k, n, p, c, q}:
      q

def Spec.Touch.version(t):
  match t:
    case Touched{v, c, u}:
      v

def Spec.Touch.changed(t):
  match t:
    case Touched{v, c, u}:
      c

def Spec.Touch.used(t):
  match t:
    case Touched{v, c, u}:
      u

def Spec.BranchEntry():
  Tables.Row<BranchRecord>

def Spec.BranchEntry.branch(e):
  match e:
    case Tables.Row{n, b}:
      n

def Spec.BranchEntry.owner(e):
  match e:
    case Tables.Row{n, BranchRecord{h, o, x, c}}:
      o

def Spec.BranchEntry.newest(e):
  match e:
    case Tables.Row{n, BranchRecord{h, o, x, c}}:
      h

def Spec.LogEntry():
  Tables.Row<VersionRecord>

def Spec.LogEntry.version(e):
  match e:
    case Tables.Row{i, v}:
      i

def Spec.LogEntry.author(e):
  match e:
    case Tables.Row{i, VersionRecord{b, p, a, t}}:
      a

def Spec.LogEntry.time(e):
  match e:
    case Tables.Row{i, VersionRecord{b, p, a, t}}:
      t

def Spec.VendNode.empty(n):
  NodeState{
    n,
    Tables.Table.new(VersionRecord),
    Tables.Table.new(BranchRecord),
    Tables.Table.new(Tables.Table<MarkAt>),
    Tables.Table.new(GroupRecord),
    Tables.Table.new(Clash),
    Tables.Table.new(Seen),
    []
  }

def Spec.VendNode.position(s):
  List.length(&2, Logged, NodeState.log(s))

def Spec.VendNode.get_branches(s):
  +s = s
  Tables.Table.rows(
    BranchRecord,
    Tables.Table.keys(BranchRecord, NodeState.branches(s)),
    NodeState.branches(s)
  )

def Spec.VendNode.get_log(s, n, b):
  +s = s
  Log.of(
    Log.history(
      NodeState.versions(s),
      BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b))
    ),
    Resources.Name.show(n)
  )

def Spec.VendNode.get_content(s, n, p):
  NodeState.content(s, Resources.Name.show(n), p)

def Spec.VendNode.get_diff(s, n, a, b):
  +s = s
  +n = Resources.Name.show(n)
  Diff.of(Piece.of(n), NodeState.content(s, n, a), NodeState.content(s, n, b))

# no format in the core says what an item uses; formats add these
def Spec.VendNode.get_affects(s, b):
  Nil{}

def Spec.VendNode.get_impact(s, p):
  Nil{}

def Spec.VendNode.get_outcome(s, r):
  +s = s
  +r = r
  Outcome.of(
    Tables.Table.get(Seen, NodeState.seen(s), r),
    VersionRecord.taken(NodeState.versions(s), r),
    List.length(&2, Logged, NodeState.log(s))
  )

def Spec.VendNode.get_changes(s, k, p):
  Logged.pick(k, List.drop(&2, Logged, NodeState.log(s), Maybe.default(&2, Nat, p, 0n)))

def Spec.VendNode.ask(s, e, q):
  match e:
    case Spec.Envelope{+r, w, t}:
      +s = s
      VendNode.asked(Tables.Table.get(Seen, NodeState.seen(s), r), s, r, w, t, q)

def Spec.VendNode.get_epoch(s, b):
  BranchRecord.epoch.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b))

def Spec.VendNode.get_head(s, b):
  BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b))

def Spec.VendNode.is_owner(s, b):
  +s = s
  Owner.in(s, Tables.Table.get(BranchRecord, NodeState.branches(s), b))

def Spec.VendNode.get_members(s, g):
  GroupRecord.members.got(Tables.Table.get(GroupRecord, NodeState.groups(s), g))

def Spec.VendNode.is_inside(s, m, g):
  GroupRecord.inside(NodeState.groups(s), m, g)

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Lemmas
# ------

# the parts of out
def Out.versions(out: Out) -> List<&2, Tables.Row<VersionRecord>>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nv

def Out.branches(out: Out) -> Tables.Table<BranchRecord>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nb

def Out.marks(out: Out) -> Tables.Table<Tables.Table<MarkAt>>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nm

def Out.groups(out: Out) -> Tables.Table<GroupRecord>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      ng

def Out.news(out: Out) -> List<&2, Logged>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      news

def Out.answer(out: Out) -> Spec.Answer:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      a

# the notices a change adds: none for a retry, else the change's own
def VendNode.news(
  found: Maybe<&2, Seen>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  q: Spec.Ask
) -> List<&2, Logged>:
  match found:
    case Some{Seen{a, p}}:
      Nil{}
    case None{}:
      Out.news(Step.of(s, r, w, t, q))

# the answer of the request that m holds
def Seen.answer.of(m: Maybe<&2, Seen>) -> Maybe<&2, Spec.Answer>:
  match m:
    case None{}:
      None{}
    case Some{Seen{a, p}}:
      Some{a}

# the notices of a topic in two lists are those of each, in order
law pick_append:
  for k: Spec.Topic
  for xs: List<&2, Logged>
  for ys: List<&2, Logged>
  {
    Logged.pick(
      k,
      List.append(&2, Logged, xs, ys)
    )
      == List.append(&2, Spec.Notice, Logged.pick(k, xs), Logged.pick(k, ys)): List<&2, Spec.Notice>
  }

def pick_append(k, xs, ys):
  match xs:
    case Nil{}:
      {==}
    case Con{Logged{t, n}, +r}:
      +k = k
      +ys = ys
      %Equal.sym(
        List<&2, Spec.Notice>,
        Logged.pick(k, List.append(&2, Logged, r, ys)),
        List.append(&2, Spec.Notice, Logged.pick(k, r), Logged.pick(k, ys)),
        pick_append(k, r, ys)
      ):
        {
          List.filter.put(
            Spec.Notice,
            n,
            _,
            Topic.same(t, k)
          )
            == List.append(
              &2,
              Spec.Notice,
              List.filter.put(Spec.Notice, n, Logged.pick(k, r), Topic.same(t, k)),
              Logged.pick(k, ys)
            ): List<&2, Spec.Notice>
        }
      Lists.List.filter.put_append(
        Spec.Notice,
        n,
        Logged.pick(k, r),
        Logged.pick(k, ys),
        Topic.same(t, k)
      )

# the notices since a position are the ones after the log up to it
law since_on:
  for k: Spec.Topic
  for xs: List<&2, Logged>
  for ys: List<&2, Logged>
  {
    Logged.pick(
      k,
      List.drop(&2, Logged, List.append(&2, Logged, xs, ys), 0n)
    )
      == List.append(
        &2,
        Spec.Notice,
        Logged.pick(k, List.drop(&2, Logged, xs, 0n)),
        Logged.pick(
          k,
          List.drop(&2, Logged, List.append(&2, Logged, xs, ys), List.length(&2, Logged, xs))
        )
      ): List<&2, Spec.Notice>
  }

def since_on(k, xs, ys):
  +xs = xs
  +ys = ys
  %Equal.sym(
    List<&2, Logged>,
    List.drop(&2, Logged, List.append(&2, Logged, xs, ys), 0n),
    List.append(&2, Logged, xs, ys),
    Lists.List.drop_zero(&2, Logged, List.append(&2, Logged, xs, ys))
  ):
    {
      Logged.pick(
        k,
        _
      )
        == List.append(
          &2,
          Spec.Notice,
          Logged.pick(k, List.drop(&2, Logged, xs, 0n)),
          Logged.pick(
            k,
            List.drop(&2, Logged, List.append(&2, Logged, xs, ys), List.length(&2, Logged, xs))
          )
        ): List<&2, Spec.Notice>
    }
  %Equal.sym(
    List<&2, Logged>,
    List.drop(&2, Logged, xs, 0n),
    xs,
    Lists.List.drop_zero(&2, Logged, xs)
  ):
    {
      Logged.pick(
        k,
        List.append(&2, Logged, xs, ys)
      )
        == List.append(
          &2,
          Spec.Notice,
          Logged.pick(k, _),
          Logged.pick(
            k,
            List.drop(&2, Logged, List.append(&2, Logged, xs, ys), List.length(&2, Logged, xs))
          )
        ): List<&2, Spec.Notice>
    }
  %Equal.sym(
    List<&2, Logged>,
    List.drop(&2, Logged, List.append(&2, Logged, xs, ys), List.length(&2, Logged, xs)),
    ys,
    Lists.List.drop_after_append(Logged, xs, ys)
  ):
    {
      Logged.pick(
        k,
        List.append(&2, Logged, xs, ys)
      )
        == List.append(
          &2,
          Spec.Notice,
          Logged.pick(k, xs),
          Logged.pick(k, _)
        ): List<&2, Spec.Notice>
    }
  pick_append(k, xs, ys)

# a change appends its notices to the log
law applied_log:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.log(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == List.append(&2, Logged, NodeState.log(s), Out.news(out)): List<&2, Logged>
  }

def applied_log(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a change, or its retry, appends its notices to the log
law asked_log:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    NodeState.log(
      Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q))
    )
      == List.append(
        &2,
        Logged,
        NodeState.log(s),
        VendNode.news(found, s, r, w, t, q)
      ): List<&2, Logged>
  }

def asked_log(found, s, r, w, t, q):
  match found:
    case Some{Seen{a, p}}:
      Equal.sym(
        List<&2, Logged>,
        List.append(&2, Logged, NodeState.log(s), []),
        NodeState.log(s),
        Lists.List.append_nil(Logged, NodeState.log(s))
      )
    case None{}:
      +s = s
      +r = r
      applied_log(s, r, Step.of(s, r, w, t, q))

# the notices after a change or a retry split at the position before it
law since_asked:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for k: Spec.Topic
  {
    Spec.VendNode.get_changes(
      Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q)),
      k,
      None{}
    )
      == List.append(
        &2,
        Spec.Notice,
        Spec.VendNode.get_changes(s, k, None{}),
        Spec.VendNode.get_changes(
          Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q)),
          k,
          Some{Spec.VendNode.position(s)}
        )
      ): List<&2, Spec.Notice>
  }

def since_asked(found, s, r, w, t, q, k):
  +found = found
  +s = s
  +r = r
  +w = w
  +t = t
  +q = q
  %Equal.sym(
    List<&2, Logged>,
    NodeState.log(Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q))),
    List.append(&2, Logged, NodeState.log(s), VendNode.news(found, s, r, w, t, q)),
    asked_log(found, s, r, w, t, q)
  ):
    {
      Logged.pick(
        k,
        List.drop(&2, Logged, _, 0n)
      )
        == List.append(
          &2,
          Spec.Notice,
          Logged.pick(k, List.drop(&2, Logged, NodeState.log(s), 0n)),
          Logged.pick(k, List.drop(&2, Logged, _, List.length(&2, Logged, NodeState.log(s))))
        ): List<&2, Spec.Notice>
    }
  since_on(k, NodeState.log(s), VendNode.news(found, s, r, w, t, q))

# the notices after any change split at the position before it
law since_ask:
  for s: NodeState
  for e: Spec.Envelope
  for q: Spec.Ask
  for k: Spec.Topic
  {
    Spec.VendNode.get_changes(
      Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, e, q)),
      k,
      None{}
    )
      == List.append(
        &2,
        Spec.Notice,
        Spec.VendNode.get_changes(s, k, None{}),
        Spec.VendNode.get_changes(
          Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, e, q)),
          k,
          Some{Spec.VendNode.position(s)}
        )
      ): List<&2, Spec.Notice>
  }

def since_ask(s, e, q, k):
  match e:
    case Spec.Envelope{+r, w, t}:
      +s = s
      since_asked(Tables.Table.get(Seen, NodeState.seen(s), r), s, r, w, t, q, k)

# after a change, the node keeps its answer under its request ID
law seen_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    Seen.answer.of(
      Tables.Table.get(
        Seen,
        NodeState.seen(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))),
        r
      )
    )
      == Some{Pair.snd(NodeState, Spec.Answer, VendNode.applied(s, r, out))}: Maybe<&2, Spec.Answer>
  }

def seen_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      %Equal.sym(
        Maybe<&2, Seen>,
        Tables.Table.get(
          Seen,
          Tables.Table.set(Seen, ss, r, Seen{a, List.length(&2, Logged, l)}),
          r
        ),
        Some{Seen{a, List.length(&2, Logged, l)}},
        Tables.Table.get_after_set(Seen, ss, r, Seen{a, List.length(&2, Logged, l)})
      ):
        {Seen.answer.of(_) == Some{a}: Maybe<&2, Spec.Answer>}
      {==}

# after a change or a retry, the node keeps the answer under its request ID
law seen_after_asked:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    Tables.Table.get(Seen, NodeState.seen(s), r) == found: Maybe<&2, Seen>
  } -> {
    Seen.answer.of(
      Tables.Table.get(
        Seen,
        NodeState.seen(Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q))),
        r
      )
    )
      == Some{
        Pair.snd(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q))
      }: Maybe<&2, Spec.Answer>
  }

def seen_after_asked(found, s, r, w, t, q):
  match found:
    case Some{Seen{a, p}}:
      h =>
        +s = s
        +r = r
        %Equal.sym(
          Maybe<&2, Seen>,
          Tables.Table.get(Seen, NodeState.seen(s), r),
          Some{Seen{a, p}},
          h
        ):
          {Seen.answer.of(_) == Some{a}: Maybe<&2, Spec.Answer>}
        {==}
    case None{}:
      h =>
        +s = s
        +r = r
        seen_after_applied(s, r, Step.of(s, r, w, t, q))

# after a change of the request r, the node keeps its answer under r
law seen_after_ask:
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    Seen.answer.of(
      Tables.Table.get(
        Seen,
        NodeState.seen(
          Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t}, q))
        ),
        r
      )
    )
      == Some{
        Pair.snd(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t}, q))
      }: Maybe<&2, Spec.Answer>
  }

def seen_after_ask(s, r, w, t, q):
  +s = s
  +r = r
  seen_after_asked(Tables.Table.get(Seen, NodeState.seen(s), r), s, r, w, t, q)({==})

# a request whose answer the node keeps gets that answer, and changes nothing
law asked_found:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for a: Spec.Answer
  {
    Seen.answer.of(found) == Some{a}: Maybe<&2, Spec.Answer>
  } -> {VendNode.asked(found, s, r, w, t, q) == (s, a): NodeState & Spec.Answer}

def asked_found(found, s, r, w, t, q, a):
  match found:
    case None{}:
      h => Empty.absurd(
        {VendNode.asked(None{}, s, r, w, t, q) == (s, a): NodeState & Spec.Answer},
        Maybes.Maybe.none_ne_some(Spec.Answer, a, h)
      )
    case Some{Seen{b, p}}:
      h =>
        %Maybes.Maybe.some_inj(Spec.Answer, b, a, h): {(s, b) == (s, _): NodeState & Spec.Answer}
        {==}

# the versions after a change are its new ones joined to the old
law versions_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.versions(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == VersionRecord.add(Out.versions(out), NodeState.versions(s)): Tables.Table<VersionRecord>
  }

def versions_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# adding a version keeps one found by another key: by whether the keys are the
# same (hit)
law put_keeps.at:
  for hit: Bool
  for i: String
  for x: VersionRecord
  for vs: Tables.Table<VersionRecord>
  for v: String
  for u: VersionRecord
  {
    String.eq(i, v) == hit: Bool
  } -> {
    VersionRecord.has(vs, i) == False{}: Bool
  } -> {
    Tables.Table.get(VersionRecord, vs, v) == Some{u}: Maybe<&2, VersionRecord>
  } -> {
    Bools.Bool.when(
      Maybe<&2, VersionRecord>,
      hit,
      z => Some{x},
      z => Tables.Table.get(VersionRecord, vs, v)
    )
      == Some{u}: Maybe<&2, VersionRecord>
  }

def put_keeps.at(hit, i, x, vs, v, u):
  match hit:
    case False{}:
      he => hh => hf => hf
    case True{}:
      he => hh => +hf =>
        +i = i
        +v = v
        +vs = vs
        +u = u
        Empty.absurd(
          {
            Bools.Bool.when(
              Maybe<&2, VersionRecord>,
              True{},
              z => Some{x},
              z => Tables.Table.get(VersionRecord, vs, v)
            )
              == Some{u}: Maybe<&2, VersionRecord>
          },
          Shared.Bool.false_ne_true(
            Equal.sym(
              Bool,
              True{},
              False{},
              Equal.trans(
                Bool,
                True{},
                VersionRecord.has(vs, v),
                False{},
                Equal.sym(
                  Bool,
                  VersionRecord.has(vs, v),
                  True{},
                  Equal.cong(
                    Maybe<&2, VersionRecord>,
                    Bool,
                    m => Maybe.is_some(&2, VersionRecord, m),
                    Tables.Table.get(VersionRecord, vs, v),
                    Some{u},
                    hf
                  )
                ),
                Equal.trans(
                  Bool,
                  VersionRecord.has(vs, v),
                  VersionRecord.has(vs, i),
                  False{},
                  Equal.sym(
                    Bool,
                    VersionRecord.has(vs, i),
                    VersionRecord.has(vs, v),
                    Equal.cong(
                      String,
                      Bool,
                      k => VersionRecord.has(vs, k),
                      i,
                      v,
                      Strings.String.eq_sound(i, v)(he)
                    )
                  ),
                  hh
                )
              )
            )
          )
        )

# adding a version keeps every version that was found, when its ID is new or
# already held
law put_keeps:
  for held: Bool
  for i: String
  for x: VersionRecord
  for vs: Tables.Table<VersionRecord>
  for v: String
  for u: VersionRecord
  {
    VersionRecord.has(vs, i) == held: Bool
  } -> {
    Tables.Table.get(VersionRecord, vs, v) == Some{u}: Maybe<&2, VersionRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add.put(i, x, vs, held),
      v
    )
      == Some{u}: Maybe<&2, VersionRecord>
  }

def put_keeps(held, i, x, vs, v, u):
  match held:
    case True{}:
      hh => hf => hf
    case False{}:
      hh => hf =>
        +i = i
        +x = x
        +vs = vs
        +v = v
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, Tables.Table.set(VersionRecord, vs, i, x), v),
          Bools.Bool.when(
            Maybe<&2, VersionRecord>,
            String.eq(i, v),
            z => Some{x},
            z => Tables.Table.get(VersionRecord, vs, v)
          ),
          Tables.Table.get_set(VersionRecord, vs, i, x, v)
        ):
          {_ == Some{u}: Maybe<&2, VersionRecord>}
        put_keeps.at(String.eq(i, v), i, x, vs, v, u)({==})(hh)(hf)

# adding one version keeps every version that was found
law add_one_keeps:
  for c: Tables.Row<VersionRecord>
  for vs: Tables.Table<VersionRecord>
  for v: String
  for u: VersionRecord
  {
    Tables.Table.get(VersionRecord, vs, v) == Some{u}: Maybe<&2, VersionRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add.one(c, vs),
      v
    )
      == Some{u}: Maybe<&2, VersionRecord>
  }

def add_one_keeps(c, vs, v, u):
  match c:
    case Tables.Row{+i, x}:
      +vs = vs
      put_keeps(VersionRecord.has(vs, i), i, x, vs, v, u)({==})

# adding versions keeps every version that was found
law add_keeps:
  for news: List<&2, Tables.Row<VersionRecord>>
  for vs: Tables.Table<VersionRecord>
  for v: String
  for u: VersionRecord
  {
    Tables.Table.get(VersionRecord, vs, v) == Some{u}: Maybe<&2, VersionRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add(news, vs),
      v
    )
      == Some{u}: Maybe<&2, VersionRecord>
  }

def add_keeps(news, vs, v, u):
  match news:
    case Nil{}:
      h => h
    case Con{+c, r}:
      h =>
        +vs = vs
        +v = v
        +u = u
        add_keeps(r, VersionRecord.add.one(c, vs), v, u)(add_one_keeps(c, vs, v, u)(h))

# the bytes of a resource of the version that m holds stay, when that version
# stays
law kept_at:
  for m: Maybe<&2, VersionRecord>
  for vs: Tables.Table<VersionRecord>
  for ws: Tables.Table<VersionRecord>
  for v: String
  for n: String
  for x: List<&2, U32>
  {
    Tables.Table.get(VersionRecord, vs, v) == m: Maybe<&2, VersionRecord>
  } -> (
    @u: VersionRecord -> {
      Tables.Table.get(VersionRecord, vs, v) == Some{u}: Maybe<&2, VersionRecord>
    } -> {Tables.Table.get(VersionRecord, ws, v) == Some{u}: Maybe<&2, VersionRecord>}
  ) -> {
    Blob.find.of(VersionRecord.blobs.of(m), n) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(Tables.Table.get(VersionRecord, ws, v)),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def kept_at(m, vs, ws, v, n, x):
  match m:
    case None{}:
      he => hk => hc => Empty.absurd(
        {
          Blob.find.of(
            VersionRecord.blobs.of(Tables.Table.get(VersionRecord, ws, v)),
            n
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        },
        Maybes.Maybe.none_ne_some(List<&2, U32>, x, hc)
      )
    case Some{u}:
      he => hk => hc =>
        +ws = ws
        +v = v
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, ws, v),
          Some{u},
          hk(u)(he)
        ):
          {Blob.find.of(VersionRecord.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        hc

# a change or a retry keeps every version that existed, with its content
law kept_asked:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for n: String
  for v: String
  for x: List<&2, U32>
  {
    NodeState.content(s, n, Spec.Point.At{v}) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {
    NodeState.content(
      Pair.fst(NodeState, Spec.Answer, VendNode.asked(found, s, r, w, t, q)),
      n,
      Spec.Point.At{v}
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def kept_asked(found, s, r, w, t, q, n, v, x):
  match found:
    case Some{Seen{a, p}}:
      h => h
    case None{}:
      h =>
        +s = s
        +r = r
        +w = w
        +t = t
        +q = q
        +v = v
        %Equal.sym(
          Tables.Table<VersionRecord>,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Step.of(s, r, w, t, q)))
          ),
          VersionRecord.add(Out.versions(Step.of(s, r, w, t, q)), NodeState.versions(s)),
          versions_after_applied(s, r, Step.of(s, r, w, t, q))
        ):
          {
            Blob.find.of(
              VersionRecord.blobs.of(Tables.Table.get(VersionRecord, _, v)),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        kept_at(
          Tables.Table.get(VersionRecord, NodeState.versions(s), v),
          NodeState.versions(s),
          VersionRecord.add(Out.versions(Step.of(s, r, w, t, q)), NodeState.versions(s)),
          v,
          n,
          x
        )(
          {==}
        )(u => add_keeps(Out.versions(Step.of(s, r, w, t, q)), NodeState.versions(s), v, u))(h)

# a number for each kind of answer, so that two kinds can be told apart
def Answer.tag(a: Spec.Answer) -> Nat:
  match a:
    case Spec.Answer.Write{Spec.Write.Written{v}}:
      0n
    case Spec.Answer.Write{Spec.Write.Pending{v}}:
      1n
    case Spec.Answer.Write{Spec.Write.Stale{v}}:
      2n
    case Spec.Answer.Write{Spec.Write.Refused{y}}:
      3n
    case Spec.Answer.SetOwner{Spec.SetOwner.Set{e}}:
      4n
    case Spec.Answer.SetOwner{Spec.SetOwner.NoMajority{}}:
      5n
    case Spec.Answer.SetOwner{Spec.SetOwner.Refused{y}}:
      6n
    case Spec.Answer.Merge{Spec.Merge.Merged{v}}:
      7n
    case Spec.Answer.Merge{Spec.Merge.Conflicted{k}}:
      8n
    case Spec.Answer.Merge{Spec.Merge.Stale{v}}:
      9n
    case Spec.Answer.Merge{Spec.Merge.Refused{y}}:
      10n
    case Spec.Answer.SetGroup{Spec.SetGroup.Set{e}}:
      11n
    case Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}}:
      12n
    case Spec.Answer.Sync{Spec.Sync.Synced{}}:
      14n
    case Spec.Answer.Sync{Spec.Sync.Refused{y}}:
      15n
    case _:
      13n

# answers of two kinds are not equal: their tags differ (the caller's Bool
# clash closes it)
def Answer.clash(
  -a: Spec.Answer,
  -b: Spec.Answer,
  h: {a == b: Spec.Answer}
) -> {Nat.is_eq(Answer.tag(a), Answer.tag(b)) == Nat.is_eq(Answer.tag(b), Answer.tag(b)): Bool}:
  Equal.cong(Spec.Answer, Bool, x => Nat.is_eq(Answer.tag(x), Answer.tag(b)), a, b, h)

# the version that a Written, Created or Merged answer names, else none
def Answer.version(a: Spec.Answer) -> Maybe<&2, String>:
  match a:
    case Spec.Answer.Write{Spec.Write.Written{v}}:
      Some{v}
    case Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}:
      Some{v}
    case Spec.Answer.Merge{Spec.Merge.Merged{v}}:
      Some{v}
    case _:
      None{}

# the epoch of a set-owner answer, else none
def Answer.epoch(a: Spec.Answer) -> Nat:
  match a:
    case Spec.Answer.SetOwner{Spec.SetOwner.Set{e}}:
      e
    case _:
      0n

# the version of a stale write, else none
def Answer.stale(a: Spec.Answer) -> Maybe<&2, String>:
  match a:
    case Spec.Answer.Write{Spec.Write.Stale{v}}:
      Some{v}
    case _:
      None{}

# the conflict of a merge that clashed, else none
def Answer.conflict(a: Spec.Answer) -> Maybe<&2, String>:
  match a:
    case Spec.Answer.Merge{Spec.Merge.Conflicted{k}}:
      Some{k}
    case _:
      None{}

# what holds when o is Applied
def Outcome.IsApplied(o: Spec.Outcome) -> Type:
  match o:
    case Spec.Outcome.Applied{p}:
      Unit
    case Spec.Outcome.NotSeen{}:
      Empty

# Applied is not NotSeen
def Outcome.clash(
  -p: Nat,
  h: {Spec.Outcome.Applied{p} == Spec.Outcome.NotSeen{}: Spec.Outcome}
) -> Empty:
  %h: Outcome.IsApplied(_)
  Unit{}

# a new request has no kept answer, and no version has its ID
law outcome_new:
  for found: Maybe<&2, Seen>
  for held: Bool
  for at: Nat
  {
    Outcome.of(found, held, at) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {found == None{}: Maybe<&2, Seen>}
    & {held == False{}: Bool}

def outcome_new(found, held, at):
  match found held:
    case Some{Seen{a, p}} _:
      h => Empty.absurd(
        {Some{Seen{a, p}} == None{}: Maybe<&2, Seen>} & {held == False{}: Bool},
        Outcome.clash(p, h)
      )
    case None{} True{}:
      h => Empty.absurd(
        {None{} == None{}: Maybe<&2, Seen>} & {True{} == False{}: Bool},
        Outcome.clash(at, h)
      )
    case None{} False{}:
      h => ({==}, {==})

# an ID that is not taken is not held
law taken_free:
  for vs: Tables.Table<VersionRecord>
  for k: String
  {VersionRecord.taken(vs, k) == False{}: Bool} -> {VersionRecord.has(vs, k) == False{}: Bool}

def taken_free(vs, k):
  +vs = vs
  +k = k
  Bools.Bool.or_false_left(
    VersionRecord.has(vs, k),
    VersionRecord.named(Tables.Table.keys(VersionRecord, vs), vs, k)
  )

# a new request has no kept answer
law new_found:
  for s: NodeState
  for r: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {Tables.Table.get(Seen, NodeState.seen(s), r) == None{}: Maybe<&2, Seen>}

def new_found(s, r):
  h =>
    +s = s
    +r = r
    Pair.fst(
      {Tables.Table.get(Seen, NodeState.seen(s), r) == None{}: Maybe<&2, Seen>},
      {VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, NodeState.seen(s), r),
        VersionRecord.taken(NodeState.versions(s), r),
        List.length(&2, Logged, NodeState.log(s))
      )(h)
    )

# no version has the ID of a new request
law new_free:
  for s: NodeState
  for r: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool}

def new_free(s, r):
  h =>
    +s = s
    +r = r
    Pair.snd(
      {Tables.Table.get(Seen, NodeState.seen(s), r) == None{}: Maybe<&2, Seen>},
      {VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, NodeState.seen(s), r),
        VersionRecord.taken(NodeState.versions(s), r),
        List.length(&2, Logged, NodeState.log(s))
      )(h)
    )

# a new request runs its change, and the node keeps its answer
law ask_step:
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  for t: NodeState
  for a: Spec.Answer
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(s, Spec.Envelope{r, w, z}, q) == (t, a): NodeState & Spec.Answer
  } -> {VendNode.applied(s, r, Step.of(s, r, w, z, q)) == (t, a): NodeState & Spec.Answer}

def ask_step(s, r, w, z, q, t, a):
  hn => h =>
    +s = s
    +r = r
    %new_found(s, r)(hn): {VendNode.asked(_, s, r, w, z, q) == (t, a): NodeState & Spec.Answer}
    h

# a change whose result is (t, a) answers a
law applied_answer:
  for s: NodeState
  for r: String
  for out: Out
  for t: NodeState
  for a: Spec.Answer
  {
    VendNode.applied(s, r, out) == (t, a): NodeState & Spec.Answer
  } -> {Out.answer(out) == a: Spec.Answer}

def applied_answer(s, r, out, t, a):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, b}:
      h => Equal.cong(
        NodeState & Spec.Answer,
        Spec.Answer,
        x => Pair.snd(NodeState, Spec.Answer, x),
        VendNode.applied(
          NodeState{k, vs, bs, ms, gs, cs, ss, l},
          r,
          Out{nv, nb, nm, ng, nc, news, b}
        ),
        (t, a),
        h
      )

# a change whose result is (t, a) leaves the node as t
law applied_state:
  for s: NodeState
  for r: String
  for out: Out
  for t: NodeState
  for a: Spec.Answer
  {
    VendNode.applied(s, r, out) == (t, a): NodeState & Spec.Answer
  } -> {Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out)) == t: NodeState}

def applied_state(s, r, out, t, a):
  h => Equal.cong(
    NodeState & Spec.Answer,
    NodeState,
    x => Pair.fst(NodeState, Spec.Answer, x),
    VendNode.applied(s, r, out),
    (t, a),
    h
  )

# the answer after a change is the change's
law answer_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {Pair.snd(NodeState, Spec.Answer, VendNode.applied(s, r, out)) == Out.answer(out): Spec.Answer}

def answer_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# the branches after a change are the change's
law branches_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.branches(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == Out.branches(out): Tables.Table<BranchRecord>
  }

def branches_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# the groups after a change are the change's
law groups_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.groups(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == Out.groups(out): Tables.Table<GroupRecord>
  }

def groups_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a version whose ID is new is found after it is added
law add_new_find:
  for r: String
  for bl: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w: String
  for z: String
  for vs: Tables.Table<VersionRecord>
  {
    VersionRecord.has(vs, r) == False{}: Bool
  } -> {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add([Tables.Row{r, VersionRecord{bl, ps, w, z}}], vs),
      r
    )
      == Some{VersionRecord{bl, ps, w, z}}: Maybe<&2, VersionRecord>
  }

def add_new_find(r, bl, ps, w, z, vs):
  hh =>
    +r = r
    +vs = vs
    +bl = bl
    +ps = ps
    +w = w
    +z = z
    %Equal.sym(Bool, VersionRecord.has(vs, r), False{}, hh):
      {
        Tables.Table.get(
          VersionRecord,
          VersionRecord.add.put(r, VersionRecord{bl, ps, w, z}, vs, _),
          r
        )
          == Some{VersionRecord{bl, ps, w, z}}: Maybe<&2, VersionRecord>
      }
    Tables.Table.get_after_set(VersionRecord, vs, r, VersionRecord{bl, ps, w, z})

# a write on the head v of the branch that m holds, as its owner, is written
law write_on_head:
  for m: Maybe<&2, BranchRecord>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for v: String
  for x: List<&2, U32>
  {
    BranchRecord.head.of(m) == Some{v}: Maybe<&2, String>
  } -> {
    Owner.in(s, m) == True{}: Bool
  } -> {
    Out.answer(
      Write.branch(m, s, r, w, t, n, b, Some{v}, x)
    )
      == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
  }

def write_on_head(m, s, r, w, t, n, b, v, x):
  match m:
    case None{}:
      hh => ho => Empty.absurd(
        {
          Out.answer(
            Write.branch(None{}, s, r, w, t, n, b, Some{v}, x)
          )
            == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
        },
        Maybes.Maybe.none_ne_some(String, v, hh)
      )
    case Some{BranchRecord{h, o, e, c}}:
      hh => ho =>
        +s = s
        +r = r
        +v = v
        %Equal.sym(Bool, Owner.of(s, BranchRecord{h, o, e, c}), True{}, ho):
          {
            Out.answer(
              Write.on(_, s, r, w, t, n, b, Some{v}, x, BranchRecord{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        %Equal.sym(String, h, v, Maybes.Maybe.some_inj(String, h, v, hh)):
          {
            Out.answer(
              Write.at(String.eq(v, _), s, r, w, t, n, b, x, BranchRecord{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        %Equal.sym(Bool, String.eq(v, v), True{}, Strings.String.eq_refl(v)):
          {
            Out.answer(
              Write.at(_, s, r, w, t, n, b, x, BranchRecord{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        {==}

# a write as the owner that answers Written: the head holds the bytes
law raw_at:
  for ok: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for b: String
  for v: String
  {
    VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.at(ok, s, r, w, z, n, b, x, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        VersionRecord.find.of(
          VersionRecord.add(
            Out.versions(Write.at(ok, s, r, w, z, n, b, x, BranchRecord{h, o, e, c})),
            NodeState.versions(s)
          ),
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              Out.branches(Write.at(ok, s, r, w, z, n, b, x, BranchRecord{h, o, e, c})),
              b
            )
          )
        )
      ),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def raw_at(ok, s, r, w, z, n, x, h, o, e, c, b, v):
  match ok:
    case False{}:
      hh => ha => Empty.absurd(
        {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(
                VersionRecord.add(
                  Out.versions(Write.at(False{}, s, r, w, z, n, b, x, BranchRecord{h, o, e, c})),
                  NodeState.versions(s)
                ),
                BranchRecord.head.of(
                  Tables.Table.get(
                    BranchRecord,
                    Out.branches(Write.at(False{}, s, r, w, z, n, b, x, BranchRecord{h, o, e, c})),
                    b
                  )
                )
              )
            ),
            n
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Stale{h}},
            Spec.Answer.Write{Spec.Write.Written{v}},
            ha
          )
        )
      )
    case True{}:
      hh => ha =>
        +s = s
        +r = r
        +h = h
        +n = n
        +x = x
        +b = b
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(BranchRecord, NodeState.branches(s), b, BranchRecord{r, o, e, 1n+c}),
            b
          ),
          Some{BranchRecord{r, o, e, 1n+c}},
          Tables.Table.get_after_set(
            BranchRecord,
            NodeState.branches(s),
            b,
            BranchRecord{r, o, e, 1n+c}
          )
        ):
          {
            Blob.find.of(
              VersionRecord.blobs.of(
                VersionRecord.find.of(
                  VersionRecord.add(
                    [
                      Tables.Row{
                        r,
                        VersionRecord{
                          Tables.Table.set(
                            List<&2, U32>,
                            Vers.blobs(NodeState.versions(s), h),
                            n,
                            x
                          ),
                          [h],
                          w,
                          z
                        }
                      }
                    ],
                    NodeState.versions(s)
                  ),
                  BranchRecord.head.of(_)
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(
            VersionRecord,
            VersionRecord.add(
              [
                Tables.Row{
                  r,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                    [h],
                    w,
                    z
                  }
                }
              ],
              NodeState.versions(s)
            ),
            r
          ),
          Some{
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          },
          add_new_find(
            r,
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
            [h],
            w,
            z,
            NodeState.versions(s)
          )(taken_free(NodeState.versions(s), r)(hh))
        ):
          {Blob.find.of(VersionRecord.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tables.Table.get_after_set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x)

# a write on a branch, as its owner or not, that answers Written
law raw_on:
  for owner: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for v: String
  {
    VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.on(owner, s, r, w, z, n, b, base, x, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        VersionRecord.find.of(
          VersionRecord.add(
            Out.versions(Write.on(owner, s, r, w, z, n, b, base, x, BranchRecord{h, o, e, c})),
            NodeState.versions(s)
          ),
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              Out.branches(Write.on(owner, s, r, w, z, n, b, base, x, BranchRecord{h, o, e, c})),
              b
            )
          )
        )
      ),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def raw_on(owner, s, r, w, z, n, b, base, x, h, o, e, c, v):
  match owner:
    case True{}:
      +h = h
      raw_at(Base.is(base, h), s, r, w, z, n, x, h, o, e, c, b, v)
    case False{}:
      hh => ha => Empty.absurd(
        {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(
                VersionRecord.add(
                  Out.versions(
                    Write.on(False{}, s, r, w, z, n, b, base, x, BranchRecord{h, o, e, c})
                  ),
                  NodeState.versions(s)
                ),
                BranchRecord.head.of(
                  Tables.Table.get(
                    BranchRecord,
                    Out.branches(
                      Write.on(False{}, s, r, w, z, n, b, base, x, BranchRecord{h, o, e, c})
                    ),
                    b
                  )
                )
              )
            ),
            n
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Pending{r}},
            Spec.Answer.Write{Spec.Write.Written{v}},
            ha
          )
        )
      )

# a write on the branch that m holds that answers Written
law raw_branch:
  for m: Maybe<&2, BranchRecord>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for v: String
  {
    VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.branch(m, s, r, w, z, n, b, base, x)
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        VersionRecord.find.of(
          VersionRecord.add(
            Out.versions(Write.branch(m, s, r, w, z, n, b, base, x)),
            NodeState.versions(s)
          ),
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              Out.branches(Write.branch(m, s, r, w, z, n, b, base, x)),
              b
            )
          )
        )
      ),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def raw_branch(m, s, r, w, z, n, b, base, x, v):
  match m base:
    case Some{BranchRecord{+h, +o, +e, +c}} k:
      +s = s
      raw_on(Owner.of(s, BranchRecord{h, o, e, c}), s, r, w, z, n, b, k, x, h, o, e, c, v)
    case None{} Some{k}:
      hh => ha => Empty.absurd(
        {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(
                VersionRecord.add(
                  Out.versions(Write.branch(None{}, s, r, w, z, n, b, Some{k}, x)),
                  NodeState.versions(s)
                ),
                BranchRecord.head.of(
                  Tables.Table.get(
                    BranchRecord,
                    Out.branches(Write.branch(None{}, s, r, w, z, n, b, Some{k}, x)),
                    b
                  )
                )
              )
            ),
            n
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Refused{"no such branch"}},
            Spec.Answer.Write{Spec.Write.Written{v}},
            ha
          )
        )
      )
    case None{} None{}:
      hh => ha =>
        +s = s
        +r = r
        +b = b
        +n = n
        +x = x
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              b,
              BranchRecord{r, NodeState.self(s), 0n, 0n}
            ),
            b
          ),
          Some{BranchRecord{r, NodeState.self(s), 0n, 0n}},
          Tables.Table.get_after_set(
            BranchRecord,
            NodeState.branches(s),
            b,
            BranchRecord{r, NodeState.self(s), 0n, 0n}
          )
        ):
          {
            Blob.find.of(
              VersionRecord.blobs.of(
                VersionRecord.find.of(
                  VersionRecord.add(
                    [
                      Tables.Row{
                        r,
                        VersionRecord{
                          Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
                          [],
                          w,
                          z
                        }
                      }
                    ],
                    NodeState.versions(s)
                  ),
                  BranchRecord.head.of(_)
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(
            VersionRecord,
            VersionRecord.add(
              [
                Tables.Row{
                  r,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
                    [],
                    w,
                    z
                  }
                }
              ],
              NodeState.versions(s)
            ),
            r
          ),
          Some{
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
              [],
              w,
              z
            }
          },
          add_new_find(
            r,
            Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
            [],
            w,
            z,
            NodeState.versions(s)
          )(taken_free(NodeState.versions(s), r)(hh))
        ):
          {Blob.find.of(VersionRecord.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tables.Table.get_after_set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x)

# a write that answers Written, unless its version ID is taken
law raw_free:
  for taken: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for v: String
  {
    VersionRecord.taken(NodeState.versions(s), r) == taken: Bool
  } -> {
    Out.answer(
      Write.free(taken, s, r, w, z, n, b, base, x)
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        VersionRecord.find.of(
          VersionRecord.add(
            Out.versions(Write.free(taken, s, r, w, z, n, b, base, x)),
            NodeState.versions(s)
          ),
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              Out.branches(Write.free(taken, s, r, w, z, n, b, base, x)),
              b
            )
          )
        )
      ),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def raw_free(taken, s, r, w, z, n, b, base, x, v):
  match taken:
    case True{}:
      hh => ha => Empty.absurd(
        {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(
                VersionRecord.add(
                  Out.versions(Write.free(True{}, s, r, w, z, n, b, base, x)),
                  NodeState.versions(s)
                ),
                BranchRecord.head.of(
                  Tables.Table.get(
                    BranchRecord,
                    Out.branches(Write.free(True{}, s, r, w, z, n, b, base, x)),
                    b
                  )
                )
              )
            ),
            n
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Refused{"version ID taken"}},
            Spec.Answer.Write{Spec.Write.Written{v}},
            ha
          )
        )
      )
    case False{}:
      hh =>
        +s = s
        +b = b
        raw_branch(
          Tables.Table.get(BranchRecord, NodeState.branches(s), b),
          s,
          r,
          w,
          z,
          n,
          b,
          base,
          x,
          v
        )(hh)

# a change that adds no version and keeps the branches and marks keeps the
# content at every point
law same_content_out:
  for s: NodeState
  for r: String
  for cs: Tables.Table<Clash>
  for news: List<&2, Logged>
  for a: Spec.Answer
  for n: String
  for p: Spec.Point
  {
    NodeState.content(
      Pair.fst(
        NodeState,
        Spec.Answer,
        VendNode.applied(
          s,
          r,
          Out{[], NodeState.branches(s), NodeState.marks(s), NodeState.groups(s), cs, news, a}
        )
      ),
      n,
      p
    )
      == NodeState.content(s, n, p): Maybe<&2, List<&2, U32>>
  }

def same_content_out(s, r, cs, news, a, n, p):
  match s p:
    case NodeState{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.At{v}:
      {==}
    case NodeState{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.Head{b}:
      {==}
    case NodeState{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.Mark{b, m}:
      {==}

# a stale write as the owner: its base is not the head (ok is False)
law stale_at:
  for ok: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for y: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for base: Maybe<&2, String>
  for cur: String
  {
    Base.is(base, h) == ok: Bool
  } -> {
    Out.answer(
      Write.at(ok, s, r, w, z, n, b, y, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Write.at(ok, s, r, w, z, n, b, y, BranchRecord{h, o, e, c}))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_at(ok, s, r, w, z, n, b, y, h, o, e, c, base, cur):
  match ok:
    case True{}:
      hb => ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Write.at(True{}, s, r, w, z, n, b, y, BranchRecord{h, o, e, c}))
          ),
          s
        )
          & {base != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Written{r}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )
    case False{}:
      +hb => ha =>
        +s = s
        +r = r
        +h = h
        +base = base
        +cur = cur
        (
          n2 => p2 => same_content_out(
            s,
            r,
            NodeState.clashes(s),
            [],
            Spec.Answer.Write{Spec.Write.Stale{h}},
            Resources.Name.show(n2),
            p2
          ),
          heq => Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Base.is(base, h),
              True{},
              Equal.sym(Bool, Base.is(base, h), False{}, hb),
              Equal.trans(
                Bool,
                Base.is(base, h),
                String.eq(cur, h),
                True{},
                Equal.cong(Maybe<&2, String>, Bool, q => Base.is(q, h), base, Some{cur}, heq),
                (
                  %Maybes.Maybe.some_inj(String, h, cur, Equal.cong(Spec.Answer, Maybe<&2, String>, q => Answer.stale(q), Spec.Answer.Write{Spec.Write.Stale{h}}, Spec.Answer.Write{Spec.Write.Stale{cur}}, ha)):
                    {String.eq(_, h) == True{}: Bool}
                  Strings.String.eq_refl(h))
              )
            )
          )
        )

# a stale write on a branch, as its owner or not
law stale_on:
  for owner: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for y: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for cur: String
  {
    Out.answer(
      Write.on(owner, s, r, w, z, n, b, base, y, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Write.on(owner, s, r, w, z, n, b, base, y, BranchRecord{h, o, e, c}))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_on(owner, s, r, w, z, n, b, base, y, h, o, e, c, cur):
  match owner:
    case True{}:
      +base = base
      +h = h
      stale_at(Base.is(base, h), s, r, w, z, n, b, y, h, o, e, c, base, cur)({==})
    case False{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              s,
              r,
              Write.on(False{}, s, r, w, z, n, b, base, y, BranchRecord{h, o, e, c})
            )
          ),
          s
        )
          & {base != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Pending{r}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )

# a stale write on the branch that m holds
law stale_branch:
  for m: Maybe<&2, BranchRecord>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for y: List<&2, U32>
  for cur: String
  {
    Out.answer(
      Write.branch(m, s, r, w, z, n, b, base, y)
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Write.branch(m, s, r, w, z, n, b, base, y))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_branch(m, s, r, w, z, n, b, base, y, cur):
  match m base:
    case Some{BranchRecord{+h, +o, +e, +c}} k:
      +s = s
      stale_on(Owner.of(s, BranchRecord{h, o, e, c}), s, r, w, z, n, b, k, y, h, o, e, c, cur)
    case None{} Some{k}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Write.branch(None{}, s, r, w, z, n, b, Some{k}, y))
          ),
          s
        )
          & {Some{k} != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Refused{"no such branch"}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )
    case None{} None{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Write.branch(None{}, s, r, w, z, n, b, None{}, y))
          ),
          s
        )
          & {None{} != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Written{r}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )

# a stale write, unless its version ID is taken
law stale_free:
  for taken: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for y: List<&2, U32>
  for cur: String
  {
    Out.answer(
      Write.free(taken, s, r, w, z, n, b, base, y)
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Write.free(taken, s, r, w, z, n, b, base, y))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_free(taken, s, r, w, z, n, b, base, y, cur):
  match taken:
    case True{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Write.free(True{}, s, r, w, z, n, b, base, y))
          ),
          s
        )
          & {base != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Refused{"version ID taken"}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )
    case False{}:
      +s = s
      +b = b
      stale_branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        y,
        cur
      )

# a stale write of the bytes that m holds
law stale_bytes:
  for m: Maybe<&2, List<&2, U32>>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for cur: String
  {
    Out.answer(
      Write.bytes(m, s, r, w, z, n, b, base)
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Write.bytes(m, s, r, w, z, n, b, base))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_bytes(m, s, r, w, z, n, b, base, cur):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Write.bytes(None{}, s, r, w, z, n, b, base))
          ),
          s
        )
          & {base != Some{cur}: Maybe<&2, String>},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Write{Spec.Write.Refused{"no such content"}},
            Spec.Answer.Write{Spec.Write.Stale{cur}},
            ha
          )
        )
      )
    case Some{y}:
      +s = s
      +r = r
      stale_free(VersionRecord.taken(NodeState.versions(s), r), s, r, w, z, n, b, base, y, cur)

# a merge that clashed on the names cl: no content changes, and its one new
# notice on the branch is the conflict
law cf_result:
  for cl: List<&2, String>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for f: String
  for b: String
  for bs: Tables.Table<List<&2, U32>>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for k: String
  {
    Out.answer(
      Merge.result(cl, s, r, w, z, f, b, bs, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Merge.result(cl, s, r, w, z, f, b, bs, BranchRecord{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.VendNode.get_changes(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(s, r, Merge.result(cl, s, r, w, z, f, b, bs, BranchRecord{h, o, e, c}))
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.VendNode.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_result(cl, s, r, w, z, f, b, bs, h, o, e, c, k):
  match cl:
    case Nil{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              s,
              r,
              Merge.result(Nil{}, s, r, w, z, f, b, bs, BranchRecord{h, o, e, c})
            )
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  s,
                  r,
                  Merge.result(Nil{}, s, r, w, z, f, b, bs, BranchRecord{h, o, e, c})
                )
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Merged{r}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case Con{+x, +more}:
      +ha =>
        +s = s
        +r = r
        +h = h
        +f = f
        +bs = bs
        +b = b
        +k = k
        (
          n2 => p2 => same_content_out(
            s,
            r,
            Tables.Table.set(Clash, NodeState.clashes(s), r, Clash{b, h, f, bs, x <> more}),
            [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}],
            Spec.Answer.Merge{Spec.Merge.Conflicted{r}},
            Resources.Name.show(n2),
            p2
          ),
          (
            %Equal.sym(List<&2, Logged>, NodeState.log(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Out{[], NodeState.branches(s), NodeState.marks(s), NodeState.groups(s), Tables.Table.set(Clash, NodeState.clashes(s), r, Clash{b, h, f, bs, x <> more}), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Spec.Answer.Merge{Spec.Merge.Conflicted{r}}}))), List.append(&2, Logged, NodeState.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}]), applied_log(s, r, Out{[], NodeState.branches(s), NodeState.marks(s), NodeState.groups(s), Tables.Table.set(Clash, NodeState.clashes(s), r, Clash{b, h, f, bs, x <> more}), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Spec.Answer.Merge{Spec.Merge.Conflicted{r}}})):
              {Logged.pick(Spec.Topic.Conflicts{b}, List.drop(&2, Logged, _, List.length(&2, Logged, NodeState.log(s)))) == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>}
            %Equal.sym(List<&2, Logged>, List.drop(&2, Logged, List.append(&2, Logged, NodeState.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}]), List.length(&2, Logged, NodeState.log(s))), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Lists.List.drop_after_append(Logged, NodeState.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}])):
              {Logged.pick(Spec.Topic.Conflicts{b}, _) == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>}
            %Equal.sym(Bool, String.eq(b, b), True{}, Strings.String.eq_refl(b)):
              {List.filter.put(Spec.Notice, Spec.Notice.Conflicted{r}, [], _) == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>}
            %Maybes.Maybe.some_inj(String, r, k, Equal.cong(Spec.Answer, Maybe<&2, String>, y => Answer.conflict(y), Spec.Answer.Merge{Spec.Merge.Conflicted{r}}, Spec.Answer.Merge{Spec.Merge.Conflicted{k}}, ha)):
              {[Spec.Notice.Conflicted{r}] == [Spec.Notice.Conflicted{_}]: List<&2, Spec.Notice>}
            {==})
        )

# a merge that clashed, unless the head already holds the version f (held)
law cf_inside:
  for held: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for f: String
  for b: String
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for k: String
  {
    Out.answer(
      Merge.inside(held, s, r, w, z, f, b, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Merge.inside(held, s, r, w, z, f, b, BranchRecord{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.VendNode.get_changes(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(s, r, Merge.inside(held, s, r, w, z, f, b, BranchRecord{h, o, e, c}))
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.VendNode.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_inside(held, s, r, w, z, f, b, h, o, e, c, k):
  match held:
    case True{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Merge.inside(True{}, s, r, w, z, f, b, BranchRecord{h, o, e, c}))
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  s,
                  r,
                  Merge.inside(True{}, s, r, w, z, f, b, BranchRecord{h, o, e, c})
                )
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Merged{h}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case False{}:
      +s = s
      +h = h
      +f = f
      cf_result(
        Merge.clashes(
          Strings.union(
            Tables.Table.keys(
              List<&2, U32>,
              Merge.base(
                s,
                Vers.first_in(
                  History.of(NodeState.versions(s), f),
                  Vers.ids(History.of(NodeState.versions(s), h))
                )
              )
            ),
            Strings.union(
              Tables.Table.keys(List<&2, U32>, Vers.blobs(NodeState.versions(s), f)),
              Strings.union(
                Tables.Table.keys(List<&2, U32>, Vers.blobs(NodeState.versions(s), h)),
                []
              )
            )
          ),
          Vers.blobs(NodeState.versions(s), h),
          Vers.blobs(NodeState.versions(s), f),
          Merge.base(
            s,
            Vers.first_in(
              History.of(NodeState.versions(s), f),
              Vers.ids(History.of(NodeState.versions(s), h))
            )
          )
        ),
        s,
        r,
        w,
        z,
        f,
        b,
        Merge.blobs(
          Strings.union(
            Tables.Table.keys(
              List<&2, U32>,
              Merge.base(
                s,
                Vers.first_in(
                  History.of(NodeState.versions(s), f),
                  Vers.ids(History.of(NodeState.versions(s), h))
                )
              )
            ),
            Strings.union(
              Tables.Table.keys(List<&2, U32>, Vers.blobs(NodeState.versions(s), f)),
              Strings.union(
                Tables.Table.keys(List<&2, U32>, Vers.blobs(NodeState.versions(s), h)),
                []
              )
            )
          ),
          Vers.blobs(NodeState.versions(s), h),
          Vers.blobs(NodeState.versions(s), f),
          Merge.base(
            s,
            Vers.first_in(
              History.of(NodeState.versions(s), f),
              Vers.ids(History.of(NodeState.versions(s), h))
            )
          )
        ),
        h,
        o,
        e,
        c,
        k
      )

# a merge that clashed, as the owner, unless the version ID r is taken
law cf_owner:
  for owner: Bool
  for taken: Bool
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for f: String
  for b: String
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for k: String
  {
    Out.answer(
      Merge.owner(owner, taken, s, r, w, z, f, b, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r, Merge.owner(owner, taken, s, r, w, z, f, b, BranchRecord{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.VendNode.get_changes(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            s,
            r,
            Merge.owner(owner, taken, s, r, w, z, f, b, BranchRecord{h, o, e, c})
          )
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.VendNode.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_owner(owner, taken, s, r, w, z, f, b, h, o, e, c, k):
  match owner taken:
    case False{} _:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              s,
              r,
              Merge.owner(False{}, taken, s, r, w, z, f, b, BranchRecord{h, o, e, c})
            )
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  s,
                  r,
                  Merge.owner(False{}, taken, s, r, w, z, f, b, BranchRecord{h, o, e, c})
                )
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Refused{"not the owner"}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case True{} True{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              s,
              r,
              Merge.owner(True{}, True{}, s, r, w, z, f, b, BranchRecord{h, o, e, c})
            )
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  s,
                  r,
                  Merge.owner(True{}, True{}, s, r, w, z, f, b, BranchRecord{h, o, e, c})
                )
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Refused{"version ID taken"}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case True{} False{}:
      +s = s
      +h = h
      +f = f
      cf_inside(
        Shared.List.has(~String, ~String.eq, Vers.ids(History.of(NodeState.versions(s), h)), f),
        s,
        r,
        w,
        z,
        f,
        b,
        h,
        o,
        e,
        c,
        k
      )

# a merge into the branch that m holds that clashed
law cf_branch:
  for m: Maybe<&2, BranchRecord>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for f: String
  for b: String
  for k: String
  {
    Out.answer(
      Merge.branch(m, s, r, w, z, f, b)
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Merge.branch(m, s, r, w, z, f, b))),
    s
  )
    & {
      Spec.VendNode.get_changes(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Merge.branch(m, s, r, w, z, f, b))),
        Spec.Topic.Conflicts{b},
        Some{Spec.VendNode.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_branch(m, s, r, w, z, f, b, k):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Merge.branch(None{}, s, r, w, z, f, b))
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(s, r, Merge.branch(None{}, s, r, w, z, f, b))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Refused{"no such branch"}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case Some{BranchRecord{+h, +o, +e, +c}}:
      +s = s
      +r = r
      cf_owner(
        Owner.of(s, BranchRecord{h, o, e, c}),
        VersionRecord.taken(NodeState.versions(s), r),
        s,
        r,
        w,
        z,
        f,
        b,
        h,
        o,
        e,
        c,
        k
      )

# a merge of the version that m names into the branch b that clashed
law cf_point:
  for m: Maybe<&2, String>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for k: String
  {
    Out.answer(
      Merge.point(m, s, r, w, z, b)
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.VendNode.SameContent(
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Merge.point(m, s, r, w, z, b))),
    s
  )
    & {
      Spec.VendNode.get_changes(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Merge.point(m, s, r, w, z, b))),
        Spec.Topic.Conflicts{b},
        Some{Spec.VendNode.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_point(m, s, r, w, z, b, k):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(s, r, Merge.point(None{}, s, r, w, z, b))
          ),
          s
        )
          & {
            Spec.VendNode.get_changes(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(s, r, Merge.point(None{}, s, r, w, z, b))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.VendNode.position(s)}
            )
              == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
          },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Merge{Spec.Merge.Refused{"no such point"}},
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}},
            ha
          )
        )
      )
    case Some{f}:
      +s = s
      +b = b
      cf_branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, r, w, z, f, b, k)

# a set-owner on the branch b, of epoch e, that answers Set{new}, gives b a
# larger epoch, new
law set_owner_on:
  for own: Bool
  for s: NodeState
  for b: String
  for g: String
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for old: Nat
  for new: Nat
  {
    e == old: Nat
  } -> {
    Out.answer(
      SetOwner.on(own, s, b, g, BranchRecord{h, o, e, c})
    )
      == Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}: Spec.Answer
  } -> {
    Nat.is_lt(old, new) == True{}: Bool
  }
    & {
      BranchRecord.epoch.of(
        Tables.Table.get(
          BranchRecord,
          Out.branches(SetOwner.on(own, s, b, g, BranchRecord{h, o, e, c})),
          b
        )
      )
        == Some{new}: Maybe<&2, Nat>
    }

def set_owner_on(own, s, b, g, h, o, e, c, old, new):
  match own:
    case False{}:
      heo => ha =>
        Empty.absurd(
          {
            Nat.is_lt(old, new) == True{}: Bool
          }
            & {
              BranchRecord.epoch.of(
                Tables.Table.get(
                  BranchRecord,
                  Out.branches(SetOwner.on(False{}, s, b, g, BranchRecord{h, o, e, c})),
                  b
                )
              )
                == Some{new}: Maybe<&2, Nat>
            },
          Shared.Bool.false_ne_true(
            Answer.clash(
              Spec.Answer.SetOwner{Spec.SetOwner.Refused{"not the owner"}},
              Spec.Answer.SetOwner{Spec.SetOwner.Set{new}},
              ha
            )
          )
        )
    case True{}:
      heo => +ha =>
        +e = e
        +new = new
        +b = b
        +s = s
        ((
            %heo: {Nat.is_lt(_, new) == True{}: Bool}
            %Equal.cong(Spec.Answer, Nat, x => Answer.epoch(x), Spec.Answer.SetOwner{Spec.SetOwner.Set{1n+e}}, Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}, ha):
              {Nat.is_lt(e, _) == True{}: Bool}
            Nats.Nat.lt_succ(e)), (
            %Equal.sym(Maybe<&2, BranchRecord>, Tables.Table.get(BranchRecord, Tables.Table.set(BranchRecord, NodeState.branches(s), b, BranchRecord{h, g, 1n+e, 0n}), b), Some{BranchRecord{h, g, 1n+e, 0n}}, Tables.Table.get_after_set(BranchRecord, NodeState.branches(s), b, BranchRecord{h, g, 1n+e, 0n})):
              {BranchRecord.epoch.of(_) == Some{new}: Maybe<&2, Nat>}
            %Equal.cong(Spec.Answer, Nat, x => Answer.epoch(x), Spec.Answer.SetOwner{Spec.SetOwner.Set{1n+e}}, Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}, ha):
              {Some{1n+e} == Some{_}: Maybe<&2, Nat>}
            {==}))

# a set-owner on the branch that m holds, of epoch old, that answers Set{new},
# gives b a larger epoch, new
law set_owner_lemma:
  for m: Maybe<&2, BranchRecord>
  for s: NodeState
  for b: String
  for g: String
  for old: Nat
  for new: Nat
  {
    BranchRecord.epoch.of(m) == Some{old}: Maybe<&2, Nat>
  } -> {
    Out.answer(
      SetOwner.branch(m, s, b, g)
    )
      == Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}: Spec.Answer
  } -> {
    Nat.is_lt(old, new) == True{}: Bool
  }
    & {
      BranchRecord.epoch.of(
        Tables.Table.get(BranchRecord, Out.branches(SetOwner.branch(m, s, b, g)), b)
      )
        == Some{new}: Maybe<&2, Nat>
    }

def set_owner_lemma(m, s, b, g, old, new):
  match m:
    case None{}:
      hep => ha =>
        Empty.absurd(
          {
            Nat.is_lt(old, new) == True{}: Bool
          }
            & {
              BranchRecord.epoch.of(
                Tables.Table.get(BranchRecord, Out.branches(SetOwner.branch(None{}, s, b, g)), b)
              )
                == Some{new}: Maybe<&2, Nat>
            },
          Maybes.Maybe.none_ne_some(Nat, old, hep)
        )
    case Some{BranchRecord{+h, +o, +e, +c}}:
      hep => ha =>
        +s = s
        set_owner_on(
          Owner.of(s, BranchRecord{h, o, e, c}),
          s,
          b,
          g,
          h,
          o,
          e,
          c,
          old,
          new
        )(Maybes.Maybe.some_inj(Nat, e, old, hep))(ha)

# every member is the same as itself
law member_same_refl:
  for m: Spec.Member
  {Member.same(m, m) == True{}: Bool}

def member_same_refl(m):
  match m:
    case Spec.Member.VendNode{k}:
      Strings.String.eq_refl(k)
    case Spec.Member.Group{k}:
      Strings.String.eq_refl(k)

# a and b are the same member only when they are equal
law member_same_sound:
  for a: Spec.Member
  for b: Spec.Member
  {Member.same(a, b) == True{}: Bool} -> {a == b: Spec.Member}

def member_same_sound(a, b):
  match a b:
    case Spec.Member.VendNode{x} Spec.Member.VendNode{y}:
      h => Equal.cong(
        String,
        Spec.Member,
        z => Spec.Member.VendNode{z},
        x,
        y,
        Strings.String.eq_sound(x, y)(h)
      )
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      h => Equal.cong(
        String,
        Spec.Member,
        z => Spec.Member.Group{z},
        x,
        y,
        Strings.String.eq_sound(x, y)(h)
      )
    case Spec.Member.VendNode{x} Spec.Member.Group{y}:
      h => Empty.absurd(
        {Spec.Member.VendNode{x} == Spec.Member.Group{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.Group{x} Spec.Member.VendNode{y}:
      h => Empty.absurd(
        {Spec.Member.Group{x} == Spec.Member.VendNode{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )

# grp_all_has at the first name j, by whether it is k (hit)
law grp_all_has.at:
  for hit: Bool
  for r: List<&2, String>
  for k: String
  (
    {
      Shared.List.has(~String, ~String.eq, r, k) == True{}: Bool
    } -> {
      Shared.List.has(
        ~Spec.Member,
        ~Member.same,
        GroupRecord.groups(r),
        Spec.Member.Group{k}
      )
        == True{}: Bool
    }
  ) -> {
    List.any.if(u => Shared.List.has(~String, ~String.eq, r, k), hit) == True{}: Bool
  } -> {
    List.any.if(
      u => Shared.List.has(~Spec.Member, ~Member.same, GroupRecord.groups(r), Spec.Member.Group{k}),
      hit
    )
      == True{}: Bool
  }

def grp_all_has.at(hit, r, k):
  match hit:
    case True{}:
      ih => h => {==}
    case False{}:
      ih => h => ih(h)

# a group named in ks is among the groups of ks
law grp_all_has:
  for ks: List<&2, String>
  for k: String
  {
    Shared.List.has(~String, ~String.eq, ks, k) == True{}: Bool
  } -> {
    Shared.List.has(
      ~Spec.Member,
      ~Member.same,
      GroupRecord.groups(ks),
      Spec.Member.Group{k}
    )
      == True{}: Bool
  }

def grp_all_has(ks, k):
  match ks:
    case Nil{}:
      h => h
    case Con{j, +r}:
      +k = k
      grp_all_has.at(String.eq(j, k), r, k)(grp_all_has(r, k))

# grp_live for the group k, by what gs holds for it (mg)
law grp_live.at:
  for mg: Maybe<&2, GroupRecord>
  for gs: Tables.Table<GroupRecord>
  for k: String
  for q: Spec.Member
  {
    Tables.Table.get(GroupRecord, gs, k) == mg: Maybe<&2, GroupRecord>
  } -> {
    Shared.List.has(~Spec.Member, ~Member.same, GroupRecord.members.in(mg), q) == True{}: Bool
  } -> {
    Shared.List.has(
      ~Spec.Member,
      ~Member.same,
      GroupRecord.all(gs),
      Spec.Member.Group{k}
    )
      == True{}: Bool
  }

def grp_live.at(mg, gs, k, q):
  match mg:
    case None{}:
      e => h => Empty.absurd(
        {
          Shared.List.has(
            ~Spec.Member,
            ~Member.same,
            GroupRecord.all(gs),
            Spec.Member.Group{k}
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Some{x}:
      e => h =>
        +gs = gs
        +k = k
        grp_all_has(
          Tables.Table.keys(GroupRecord, gs),
          k
        )(
          Equal.trans(
            Bool,
            Shared.List.has(~String, ~String.eq, Tables.Table.keys(GroupRecord, gs), k),
            Maybe.is_some(&2, GroupRecord, Tables.Table.get(GroupRecord, gs, k)),
            True{},
            Tables.Table.keys_get(GroupRecord, gs, k),
            Equal.cong(
              Maybe<&2, GroupRecord>,
              Bool,
              z => Maybe.is_some(&2, GroupRecord, z),
              Tables.Table.get(GroupRecord, gs, k),
              Some{x},
              e
            )
          )
        )

# a member with members is a group of gs
law grp_live:
  for gs: Tables.Table<GroupRecord>
  for p: Spec.Member
  for q: Spec.Member
  {
    Shared.List.has(~Spec.Member, ~Member.same, GroupRecord.members.of(gs, p), q) == True{}: Bool
  } -> {Shared.List.has(~Spec.Member, ~Member.same, GroupRecord.all(gs), p) == True{}: Bool}

def grp_live(gs, p, q):
  match p:
    case Spec.Member.VendNode{n}:
      h => Empty.absurd(
        {
          Shared.List.has(
            ~Spec.Member,
            ~Member.same,
            GroupRecord.all(gs),
            Spec.Member.VendNode{n}
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.Group{+k}:
      +gs = gs
      grp_live.at(Tables.Table.get(GroupRecord, gs, k), gs, k, q)({==})

# Write.at keeps the groups
def grp_kept.Write.at(
  ok: Bool,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  y: List<&2, U32>,
  br: BranchRecord
) -> {
  Out.groups(
    Write.at(ok, s, r, w, t, n, b, y, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match ok:
    case False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case True{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# Write.on keeps the groups
def grp_kept.Write.on(
  owner: Bool,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>,
  +br: BranchRecord
) -> {
  Out.groups(
    Write.on(owner, s, r, w, t, n, b, base, y, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match owner:
    case True{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          grp_kept.Write.at(Base.is(base, h), s, r, w, t, n, b, y, BranchRecord{h, o, e, c})
    case False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# Write.branch keeps the groups
def grp_kept.Write.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> {
  Out.groups(
    Write.branch(m, s, r, w, t, n, b, base, y)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case Some{+br}:
      grp_kept.Write.on(Owner.of(s, br), s, r, w, t, n, b, base, y, br)
    case None{}:
      match base:
        case Some{k}:
          {==}
        case None{}:
          {==}

# Write.free keeps the groups
def grp_kept.Write.free(
  taken: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> {
  Out.groups(
    Write.free(taken, s, r, w, t, n, b, base, y)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match taken:
    case True{}:
      {==}
    case False{}:
      grp_kept.Write.branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        t,
        n,
        b,
        base,
        y
      )

# Write.bytes keeps the groups
def grp_kept.Write.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>
) -> {
  Out.groups(
    Write.bytes(m, s, r, w, t, n, b, base)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      grp_kept.Write.free(VersionRecord.taken(NodeState.versions(s), r), s, r, w, t, n, b, base, y)

# SetBranch.on keeps the groups
def grp_kept.SetBranch.on(
  owner: Bool,
  taken: Bool,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  b: String,
  bs: Tables.Table<List<&2, U32>>,
  +br: BranchRecord
) -> {
  Out.groups(
    SetBranch.on(owner, taken, s, r, w, t, b, bs, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match owner taken:
    case _ True{}:
      {==}
    case False{} False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case True{} False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# SetBranch.branch keeps the groups
def grp_kept.SetBranch.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  b: String,
  k: String,
  bs: Tables.Table<List<&2, U32>>
) -> {
  Out.groups(
    SetBranch.branch(m, s, r, w, t, b, k, bs)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.SetBranch.on(
        Owner.of(s, br),
        VersionRecord.taken(NodeState.versions(s), r),
        s,
        r,
        w,
        t,
        b,
        bs,
        br
      )

# SetBranch.version keeps the groups
def grp_kept.SetBranch.version(
  m: Maybe<&2, VersionRecord>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +b: String,
  k: String
) -> {
  Out.groups(
    SetBranch.version(m, s, r, w, t, b, k)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{VersionRecord{bs, p, a, z}}:
      grp_kept.SetBranch.branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        t,
        b,
        k,
        bs
      )

# SetBranch.point keeps the groups
def grp_kept.SetBranch.point(
  m: Maybe<&2, String>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  b: String
) -> {
  Out.groups(SetBranch.point(m, s, r, w, t, b)) == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      grp_kept.SetBranch.version(
        Tables.Table.get(VersionRecord, NodeState.versions(s), k),
        s,
        r,
        w,
        t,
        b,
        k
      )

# CreateMark.free keeps the groups
def grp_kept.CreateMark.free(
  held: Maybe<&2, String>,
  s: NodeState,
  b: String,
  m: String,
  x: String,
  br: BranchRecord
) -> {
  Out.groups(
    CreateMark.free(held, s, b, m, x, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match held:
    case Some{k}:
      {==}
    case None{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# CreateMark.branch keeps the groups
def grp_kept.CreateMark.branch(
  f: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +b: String,
  +m: String,
  x: String
) -> {
  Out.groups(CreateMark.branch(f, s, b, m, x)) == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match f:
    case None{}:
      {==}
    case Some{br}:
      grp_kept.CreateMark.free(MarkAt.find(NodeState.marks(s), b, m), s, b, m, x, br)

# SetOwner.on keeps the groups
def grp_kept.SetOwner.on(
  owner: Bool,
  s: NodeState,
  b: String,
  g: String,
  br: BranchRecord
) -> {
  Out.groups(SetOwner.on(owner, s, b, g, br)) == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match owner:
    case False{}:
      {==}
    case True{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# SetOwner.branch keeps the groups
def grp_kept.SetOwner.branch(
  f: Maybe<&2, BranchRecord>,
  +s: NodeState,
  b: String,
  g: String
) -> {Out.groups(SetOwner.branch(f, s, b, g)) == NodeState.groups(s): Tables.Table<GroupRecord>}:
  match f:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.SetOwner.on(Owner.of(s, br), s, b, g, br)

# Merge.result keeps the groups
def grp_kept.Merge.result(
  cs: List<&2, String>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  f: String,
  b: String,
  bs: Tables.Table<List<&2, U32>>,
  br: BranchRecord
) -> {
  Out.groups(
    Merge.result(cs, s, r, w, t, f, b, bs, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match cs:
    case Nil{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case Con{k, more}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# Merge.three keeps the groups
def grp_kept.Merge.three(
  s: NodeState,
  r: String,
  w: String,
  t: String,
  f: String,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>,
  b: String,
  br: BranchRecord
) -> {
  Out.groups(
    Merge.three(s, r, w, t, f, hb, fb, bb, b, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  +ns = Strings.union(
    Tables.Table.keys(List<&2, U32>, bb),
    Strings.union(
      Tables.Table.keys(List<&2, U32>, fb),
      Strings.union(Tables.Table.keys(List<&2, U32>, hb), [])
    )
  )
  grp_kept.Merge.result(
    Merge.clashes(ns, hb, fb, bb),
    s,
    r,
    w,
    t,
    f,
    b,
    Merge.blobs(ns, hb, fb, bb),
    br
  )

# Merge.inside keeps the groups
def grp_kept.Merge.inside(
  held: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: BranchRecord
) -> {
  Out.groups(
    Merge.inside(held, s, r, w, t, f, b, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match held:
    case True{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          hh = History.of(NodeState.versions(s), h)
          grp_kept.Merge.three(
            s,
            r,
            w,
            t,
            f,
            Vers.blobs(NodeState.versions(s), h),
            Vers.blobs(NodeState.versions(s), f),
            Merge.base(s, Vers.first_in(History.of(NodeState.versions(s), f), Vers.ids(hh))),
            b,
            BranchRecord{h, o, e, c}
          )

# Merge.owner keeps the groups
def grp_kept.Merge.owner(
  owner: Bool,
  taken: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: BranchRecord
) -> {
  Out.groups(
    Merge.owner(owner, taken, s, r, w, t, f, b, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match owner taken:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      match br:
        case BranchRecord{+h, o, e, c}:
          grp_kept.Merge.inside(
            Shared.List.has(~String, ~String.eq, Vers.ids(History.of(NodeState.versions(s), h)), f),
            s,
            r,
            w,
            t,
            f,
            b,
            BranchRecord{h, o, e, c}
          )

# Merge.branch keeps the groups
def grp_kept.Merge.branch(
  m: Maybe<&2, BranchRecord>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  f: String,
  b: String
) -> {
  Out.groups(Merge.branch(m, s, r, w, t, f, b)) == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.Merge.owner(
        Owner.of(s, br),
        VersionRecord.taken(NodeState.versions(s), r),
        s,
        r,
        w,
        t,
        f,
        b,
        br
      )

# Merge.point keeps the groups
def grp_kept.Merge.point(
  m: Maybe<&2, String>,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  +b: String
) -> {Out.groups(Merge.point(m, s, r, w, t, b)) == NodeState.groups(s): Tables.Table<GroupRecord>}:
  match m:
    case None{}:
      {==}
    case Some{f}:
      grp_kept.Merge.branch(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        s,
        r,
        w,
        t,
        f,
        b
      )

# Resolve.done keeps the groups
def grp_kept.Resolve.done(
  left: List<&2, String>,
  taken: Bool,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  y: List<&2, U32>,
  cl: Clash,
  br: BranchRecord
) -> {
  Out.groups(
    Resolve.done(left, taken, s, r, w, t, k, n, y, cl, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match left:
    case Nil{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          match cl br:
            case Clash{b, h, f, bs, l} BranchRecord{h2, o, e, c}:
              {==}
    case Con{x, more}:
      match cl:
        case Clash{b, h, f, bs, l}:
          {==}

# Resolve.bytes keeps the groups
def grp_kept.Resolve.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: NodeState,
  +r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  +cl: Clash,
  br: BranchRecord
) -> {
  Out.groups(
    Resolve.bytes(m, s, r, w, t, k, n, cl, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      match cl:
        case Clash{b, h, f, bs, +l}:
          grp_kept.Resolve.done(
            Shared.List.remove(~String, ~String.eq, l, n),
            VersionRecord.taken(NodeState.versions(s), r),
            s,
            r,
            w,
            t,
            k,
            n,
            y,
            Clash{b, h, f, bs, l},
            br
          )

# Resolve.fresh keeps the groups
def grp_kept.Resolve.fresh(
  ok: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content,
  cl: Clash,
  br: BranchRecord
) -> {
  Out.groups(
    Resolve.fresh(ok, s, r, w, t, k, n, x, cl, br)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match ok:
    case False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case True{}:
      grp_kept.Resolve.bytes(Content.bytes(s, n, x), s, r, w, t, k, n, cl, br)

# Resolve.branch keeps the groups
def grp_kept.Resolve.branch(
  m: Maybe<&2, BranchRecord>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> {
  Out.groups(
    Resolve.branch(m, s, r, w, t, k, n, x, cl)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{BranchRecord{+h, o, e, c}}:
      match cl:
        case Clash{b2, +h2, f, bs, l}:
          grp_kept.Resolve.fresh(
            String.eq(h, h2),
            s,
            r,
            w,
            t,
            k,
            n,
            x,
            Clash{b2, h2, f, bs, l},
            BranchRecord{h, o, e, c}
          )

# Resolve.named keeps the groups
def grp_kept.Resolve.named(
  has: Bool,
  +s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> {
  Out.groups(
    Resolve.named(has, s, r, w, t, k, n, x, cl)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match has:
    case False{}:
      {==}
    case True{}:
      match cl:
        case Clash{+b, h, f, bs, l}:
          grp_kept.Resolve.branch(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b),
            s,
            r,
            w,
            t,
            k,
            n,
            x,
            Clash{b, h, f, bs, l}
          )

# Resolve.clash keeps the groups
def grp_kept.Resolve.clash(
  m: Maybe<&2, Clash>,
  s: NodeState,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content
) -> {
  Out.groups(
    Resolve.clash(m, s, r, w, t, k, n, x)
  )
    == NodeState.groups(s): Tables.Table<GroupRecord>
}:
  match m:
    case None{}:
      {==}
    case Some{Clash{b, h, f, bs, +l}}:
      grp_kept.Resolve.named(
        Shared.List.has(~String, ~String.eq, l, n),
        s,
        r,
        w,
        t,
        k,
        n,
        x,
        Clash{b, h, f, bs, l}
      )

# no member of gs is inside itself
def GroupRecord.Acyclic(gs: Tables.Table<GroupRecord>) -> Type:
  @y: Spec.Member -> {
    Reaches.Reach.in(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ~GroupRecord.all,
      gs,
      y,
      y
    )
      == False{}: Bool
  }

# setting a group elsewhere leaves a member's members
law grp_agree:
  for gs: Tables.Table<GroupRecord>
  for c: Spec.Member
  for x: GroupRecord
  for p: Spec.Member
  {
    Member.same(p, c) == False{}: Bool
  } -> {
    GroupRecord.members.of(
      GroupRecord.put(gs, c, x),
      p
    )
      == GroupRecord.members.of(gs, p): List<&2, Spec.Member>
  }

def grp_agree(gs, c, x, p):
  match c p:
    case Spec.Member.VendNode{n} q:
      h => {==}
    case Spec.Member.Group{k} Spec.Member.VendNode{n}:
      h => {==}
    case Spec.Member.Group{+k} Spec.Member.Group{+j}:
      +h =>
        +gs = gs
        +x = x
        %Equal.sym(
          Maybe<&2, GroupRecord>,
          Tables.Table.get(GroupRecord, Tables.Table.set(GroupRecord, gs, k, x), j),
          Bools.Bool.when(
            Maybe<&2, GroupRecord>,
            String.eq(k, j),
            u => Some{x},
            u => Tables.Table.get(GroupRecord, gs, j)
          ),
          Tables.Table.get_set(GroupRecord, gs, k, x, j)
        ):
          {
            GroupRecord.members.in(
              _
            )
              == GroupRecord.members.in(Tables.Table.get(GroupRecord, gs, j)): List<&2, Spec.Member>
          }
        %Equal.sym(Bool, String.eq(k, j), False{}, Strings.String.eq_flip(j, k)(h)):
          {
            GroupRecord.members.in(
              Bools.Bool.when(
                Maybe<&2, GroupRecord>,
                _,
                u => Some{x},
                u => Tables.Table.get(GroupRecord, gs, j)
              )
            )
              == GroupRecord.members.in(Tables.Table.get(GroupRecord, gs, j)): List<&2, Spec.Member>
          }
        {==}

# acyc_all for one member y
law acyc_all.at:
  for gs: Tables.Table<GroupRecord>
  for y: Spec.Member
  (
    @h: String -> {GroupRecord.inside(gs, Spec.Member.Group{h}, h) == False{}: Bool}
  ) -> {
    Reaches.Reach.in(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ~GroupRecord.all,
      gs,
      y,
      y
    )
      == False{}: Bool
  }

def acyc_all.at(gs, y):
  match y:
    case Spec.Member.VendNode{n}:
      a =>
        +gs = gs
        Reaches.Reach.go_nil(
          ~Spec.Member,
          ~Tables.Table<GroupRecord>,
          ~Member.same,
          ~GroupRecord.members.of,
          List.length(&2, Spec.Member, GroupRecord.all(gs)),
          gs,
          Spec.Member.VendNode{n}
        )
    case Spec.Member.Group{h}:
      a => a(h)

# no group of gs inside itself: then no member is
law acyc_all:
  for gs: Tables.Table<GroupRecord>
  (
    @h: String -> {GroupRecord.inside(gs, Spec.Member.Group{h}, h) == False{}: Bool}
  ) -> GroupRecord.Acyclic(gs)

def acyc_all(gs):
  a => y => acyc_all.at(gs, y)(a)

# setting the group g to ms, when that closes no cycle, keeps gs acyclic
law set_acyclic:
  for gs: Tables.Table<GroupRecord>
  for g: String
  for ms: List<&2, Spec.Member>
  for e: Nat
  GroupRecord.Acyclic(
    gs
  ) -> {
    Cycle.has(gs, g, ms) == False{}: Bool
  } -> GroupRecord.Acyclic(Tables.Table.set(GroupRecord, gs, g, GroupRecord{ms, e}))

def set_acyclic(gs, g, ms, e):
  a => +hc =>
    +gs = gs
    +g = g
    +ms = ms
    +e = e
    y => Reaches.Reach.put_acyclic(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ~GroupRecord.all,
      ~member_same_refl,
      ~member_same_sound,
      ~grp_live,
      ~GroupRecord,
      ~GroupRecord.put,
      ~grp_agree,
      gs,
      Spec.Member.Group{g},
      GroupRecord{ms, e},
      y
    )(a)((
        %Equal.sym(Maybe<&2, GroupRecord>, Tables.Table.get(GroupRecord, Tables.Table.set(GroupRecord, gs, g, GroupRecord{ms, e}), g), Some{GroupRecord{ms, e}}, Tables.Table.get_after_set(GroupRecord, gs, g, GroupRecord{ms, e})):
          {Reaches.Reach.closes(~Spec.Member, ~Tables.Table<GroupRecord>, ~Member.same, ~GroupRecord.members.of, ~GroupRecord.all, gs, Spec.Member.Group{g}, GroupRecord.members.in(_)) == False{}: Bool}
        hc))

# a set-group keeps the groups acyclic, by whether it closes a cycle
law sg_acyclic:
  for cycle: Bool
  for s: NodeState
  for g: String
  for ms: List<&2, Spec.Member>
  {
    Cycle.has(NodeState.groups(s), g, ms) == cycle: Bool
  } -> GroupRecord.Acyclic(
    NodeState.groups(s)
  ) -> GroupRecord.Acyclic(Out.groups(SetGroup.on(cycle, s, g, ms)))

def sg_acyclic(cycle, s, g, ms):
  match cycle:
    case True{}:
      hc => a => a
    case False{}:
      hc => a =>
        +s = s
        +g = g
        set_acyclic(
          NodeState.groups(s),
          g,
          ms,
          GroupRecord.epoch.next(NodeState.groups(s), g)
        )(a)(hc)

# every change keeps the groups acyclic
law step_acyclic:
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  {
    Spec.Ask.local(q) == True{}: Bool
  } -> GroupRecord.Acyclic(
    NodeState.groups(s)
  ) -> GroupRecord.Acyclic(Out.groups(Step.of(s, r, w, z, q)))

def step_acyclic(s, r, w, z, q):
  match q:
    case Spec.Ask.Write{Resources.Name{+n}, b, base, x}:
      hl => a =>
        +s = s
        +r = r
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(Write.bytes(Content.bytes(s, n, x), s, r, w, z, n, b, base)),
          NodeState.groups(s),
          grp_kept.Write.bytes(Content.bytes(s, n, x), s, r, w, z, n, b, base)
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.SetBranch{b, p}:
      hl => a =>
        +s = s
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(SetBranch.point(Point.version(s, p), s, r, w, z, b)),
          NodeState.groups(s),
          grp_kept.SetBranch.point(Point.version(s, p), s, r, w, z, b)
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.CreateMark{+b, m, x}:
      hl => a =>
        +s = s
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(
            CreateMark.branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, b, m, x)
          ),
          NodeState.groups(s),
          grp_kept.CreateMark.branch(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b),
            s,
            b,
            m,
            x
          )
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.Merge{p, b}:
      hl => a =>
        +s = s
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(Merge.point(Point.version(s, p), s, r, w, z, b)),
          NodeState.groups(s),
          grp_kept.Merge.point(Point.version(s, p), s, r, w, z, b)
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.Resolve{+k, Resources.Name{n}, x}:
      hl => a =>
        +s = s
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(
            Resolve.clash(Tables.Table.get(Clash, NodeState.clashes(s), k), s, r, w, z, k, n, x)
          ),
          NodeState.groups(s),
          grp_kept.Resolve.clash(
            Tables.Table.get(Clash, NodeState.clashes(s), k),
            s,
            r,
            w,
            z,
            k,
            n,
            x
          )
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.SetOwner{+b, g}:
      hl => a =>
        +s = s
        %Equal.sym(
          Tables.Table<GroupRecord>,
          Out.groups(
            SetOwner.branch(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, b, g)
          ),
          NodeState.groups(s),
          grp_kept.SetOwner.branch(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b),
            s,
            b,
            g
          )
        ): GroupRecord.Acyclic(_)
        a
    case Spec.Ask.SetGroup{+g, +ms}:
      hl => a =>
        +s = s
        sg_acyclic(Cycle.has(NodeState.groups(s), g, ms), s, g, ms)({==})(a)
    case Spec.Ask.Sync{o, p}:
      hl => a => Empty.absurd(
        GroupRecord.Acyclic(Out.groups(Step.of(s, r, w, z, Spec.Ask.Sync{o, p}))),
        Shared.Bool.false_ne_true(hl)
      )

# a change keeps every group outside itself, by whether its request was seen
law nia_asked:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  for t: NodeState
  for a: Spec.Answer
  for g: String
  {
    VendNode.asked(found, s, r, w, z, q) == (t, a): NodeState & Spec.Answer
  } -> {
    Spec.Ask.local(q) == True{}: Bool
  } -> GroupRecord.Acyclic(
    NodeState.groups(s)
  ) -> {GroupRecord.inside(NodeState.groups(t), Spec.Member.Group{g}, g) == False{}: Bool}

def nia_asked(found, s, r, w, z, q, t, a, g):
  match found:
    case Some{Seen{b, p}}:
      h => hl => ac =>
        +s = s
        %Equal.cong(
          NodeState & Spec.Answer,
          NodeState,
          x => Pair.fst(NodeState, Spec.Answer, x),
          (s, b),
          (t, a),
          h
        ): {GroupRecord.inside(NodeState.groups(_), Spec.Member.Group{g}, g) == False{}: Bool}
        ac(Spec.Member.Group{g})
    case None{}:
      h => hl => ac =>
        +s = s
        +r = r
        +w = w
        +z = z
        +q = q
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, q),
          t,
          a
        )(h): {GroupRecord.inside(NodeState.groups(_), Spec.Member.Group{g}, g) == False{}: Bool}
        %Equal.sym(
          Tables.Table<GroupRecord>,
          NodeState.groups(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Step.of(s, r, w, z, q)))
          ),
          Out.groups(Step.of(s, r, w, z, q)),
          groups_after_applied(s, r, Step.of(s, r, w, z, q))
        ):
          {GroupRecord.inside(_, Spec.Member.Group{g}, g) == False{}: Bool}
        step_acyclic(s, r, w, z, q)(hl)(ac)(Spec.Member.Group{g})

# the node of a state stays across a change
law self_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.self(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == NodeState.self(s): String
  }

def self_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a change whose result is (t, a), and whose Out is o: the versions of t
law view_v:
  for s: NodeState
  for r: String
  for x: Out
  for t: NodeState
  for a: Spec.Answer
  for o: Out
  {
    VendNode.applied(s, r, x) == (t, a): NodeState & Spec.Answer
  } -> {
    x == o: Out
  } -> {
    NodeState.versions(
      t
    )
      == VersionRecord.add(Out.versions(o), NodeState.versions(s)): Tables.Table<VersionRecord>
  }

def view_v(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<VersionRecord>,
      NodeState.versions(t),
      VersionRecord.add(Out.versions(x), NodeState.versions(s)),
      VersionRecord.add(Out.versions(o), NodeState.versions(s)),
      Equal.trans(
        Tables.Table<VersionRecord>,
        NodeState.versions(t),
        NodeState.versions(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x))),
        VersionRecord.add(Out.versions(x), NodeState.versions(s)),
        Equal.cong(
          NodeState,
          Tables.Table<VersionRecord>,
          z => NodeState.versions(z),
          t,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
          Equal.sym(
            NodeState,
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        versions_after_applied(s, r, x)
      ),
      Equal.cong(
        Out,
        Tables.Table<VersionRecord>,
        z => VersionRecord.add(Out.versions(z), NodeState.versions(s)),
        x,
        o,
        hout
      )
    )

# ... the branches of t
law view_b:
  for s: NodeState
  for r: String
  for x: Out
  for t: NodeState
  for a: Spec.Answer
  for o: Out
  {
    VendNode.applied(s, r, x) == (t, a): NodeState & Spec.Answer
  } -> {x == o: Out} -> {NodeState.branches(t) == Out.branches(o): Tables.Table<BranchRecord>}

def view_b(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<BranchRecord>,
      NodeState.branches(t),
      Out.branches(x),
      Out.branches(o),
      Equal.trans(
        Tables.Table<BranchRecord>,
        NodeState.branches(t),
        NodeState.branches(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x))),
        Out.branches(x),
        Equal.cong(
          NodeState,
          Tables.Table<BranchRecord>,
          z => NodeState.branches(z),
          t,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
          Equal.sym(
            NodeState,
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        branches_after_applied(s, r, x)
      ),
      Equal.cong(Out, Tables.Table<BranchRecord>, z => Out.branches(z), x, o, hout)
    )

# ... the groups of t
law view_g:
  for s: NodeState
  for r: String
  for x: Out
  for t: NodeState
  for a: Spec.Answer
  for o: Out
  {
    VendNode.applied(s, r, x) == (t, a): NodeState & Spec.Answer
  } -> {x == o: Out} -> {NodeState.groups(t) == Out.groups(o): Tables.Table<GroupRecord>}

def view_g(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<GroupRecord>,
      NodeState.groups(t),
      Out.groups(x),
      Out.groups(o),
      Equal.trans(
        Tables.Table<GroupRecord>,
        NodeState.groups(t),
        NodeState.groups(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x))),
        Out.groups(x),
        Equal.cong(
          NodeState,
          Tables.Table<GroupRecord>,
          z => NodeState.groups(z),
          t,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
          Equal.sym(
            NodeState,
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        groups_after_applied(s, r, x)
      ),
      Equal.cong(Out, Tables.Table<GroupRecord>, z => Out.groups(z), x, o, hout)
    )

# ... the node of t
law view_self:
  for s: NodeState
  for r: String
  for x: Out
  for t: NodeState
  for a: Spec.Answer
  {
    VendNode.applied(s, r, x) == (t, a): NodeState & Spec.Answer
  } -> {NodeState.self(t) == NodeState.self(s): String}

def view_self(s, r, x, t, a):
  hask =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      String,
      NodeState.self(t),
      NodeState.self(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x))),
      NodeState.self(s),
      Equal.cong(
        NodeState,
        String,
        z => NodeState.self(z),
        t,
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
        Equal.sym(
          NodeState,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, x)),
          t,
          applied_state(s, r, x, t, a)(hask)
        )
      ),
      self_after_applied(s, r, x)
    )

# a change answers what its Out answers, so the version it names
law view_ver:
  for s: NodeState
  for r: String
  for x: Out
  for t: NodeState
  for a: Spec.Answer
  {
    VendNode.applied(s, r, x) == (t, a): NodeState & Spec.Answer
  } -> {Answer.version(Out.answer(x)) == Answer.version(a): Maybe<&2, String>}

def view_ver(s, r, x, t, a):
  hask =>
    +a = a
    +x = x
    Equal.cong(
      Spec.Answer,
      Maybe<&2, String>,
      z => Answer.version(z),
      Out.answer(x),
      a,
      applied_answer(s, r, x, t, a)(hask)
    )

# a set-branch of an existing branch names no created version
law sb_on_none:
  for owner: Bool
  for taken: Bool
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for b: String
  for bs: Tables.Table<List<&2, U32>>
  for br: BranchRecord
  {
    Answer.version(
      Out.answer(SetBranch.on(owner, taken, s, r, w, t, b, bs, br))
    )
      == None{}: Maybe<&2, String>
  }

def sb_on_none(owner, taken, s, r, w, t, b, bs, br):
  match owner taken:
    case x True{}:
      {==}
    case False{} False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}
    case True{} False{}:
      match br:
        case BranchRecord{h, o, e, c}:
          {==}

# a set-branch that creates c at k
law sb_branch:
  for mb: Maybe<&2, BranchRecord>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for bs: Tables.Table<List<&2, U32>>
  for v: String
  {
    Tables.Table.get(BranchRecord, NodeState.branches(s), c) == mb: Maybe<&2, BranchRecord>
  } -> {
    Answer.version(
      Out.answer(SetBranch.branch(mb, s, r, w, t, c, k, bs))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>
  }
    & (
      {
        k == v: String
      }
        & {
          SetBranch.branch(
            mb,
            s,
            r,
            w,
            t,
            c,
            k,
            bs
          )
            == Out{
              [],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s),
                c,
                BranchRecord{k, NodeState.self(s), 0n, 0n}
              ),
              NodeState.marks(s),
              NodeState.groups(s),
              NodeState.clashes(s),
              [Logged.head(c, k)],
              SetBranch.answer(Spec.SetBranch.Created{k})
            }: Out
        }
    )

def sb_branch(mb, s, r, w, t, c, k, bs, v):
  match mb:
    case None{}:
      e => h => (e, (Maybes.Maybe.some_inj(String, k, v, h), {==}))
    case Some{+br}:
      e => +h =>
        +s = s
        +r = r
        +w = w
        +t = t
        +c = c
        +bs = bs
        Empty.absurd(
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & (
              {
                k == v: String
              }
                & {
                  SetBranch.branch(
                    Some{br},
                    s,
                    r,
                    w,
                    t,
                    c,
                    k,
                    bs
                  )
                    == Out{
                      [],
                      Tables.Table.set(
                        BranchRecord,
                        NodeState.branches(s),
                        c,
                        BranchRecord{k, NodeState.self(s), 0n, 0n}
                      ),
                      NodeState.marks(s),
                      NodeState.groups(s),
                      NodeState.clashes(s),
                      [Logged.head(c, k)],
                      SetBranch.answer(Spec.SetBranch.Created{k})
                    }: Out
                }
            ),
          Maybes.Maybe.none_ne_some(
            String,
            v,
            Equal.trans(
              Maybe<&2, String>,
              None{},
              Answer.version(
                Out.answer(
                  SetBranch.on(
                    Owner.of(s, br),
                    VersionRecord.taken(NodeState.versions(s), r),
                    s,
                    r,
                    w,
                    t,
                    c,
                    bs,
                    br
                  )
                )
              ),
              Some{v},
              Equal.sym(
                Maybe<&2, String>,
                Answer.version(
                  Out.answer(
                    SetBranch.on(
                      Owner.of(s, br),
                      VersionRecord.taken(NodeState.versions(s), r),
                      s,
                      r,
                      w,
                      t,
                      c,
                      bs,
                      br
                    )
                  )
                ),
                None{},
                sb_on_none(
                  Owner.of(s, br),
                  VersionRecord.taken(NodeState.versions(s), r),
                  s,
                  r,
                  w,
                  t,
                  c,
                  bs,
                  br
                )
              ),
              h
            )
          )
        )

# a set-branch to the version k, which mv holds
law sb_version:
  for mv: Maybe<&2, VersionRecord>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    Tables.Table.get(VersionRecord, NodeState.versions(s), k) == mv: Maybe<&2, VersionRecord>
  } -> {
    Answer.version(
      Out.answer(SetBranch.version(mv, s, r, w, t, c, k))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    VersionRecord.has(NodeState.versions(s), k) == True{}: Bool
  }
    & (
      {
        Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>
      }
        & (
          {
            k == v: String
          }
            & {
              SetBranch.version(
                mv,
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{k, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, k)],
                  SetBranch.answer(Spec.SetBranch.Created{k})
                }: Out
            }
        )
    )

def sb_version(mv, s, r, w, t, c, k, v):
  match mv:
    case None{}:
      e => h => Empty.absurd(
        {
          VersionRecord.has(NodeState.versions(s), k) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(s),
                c
              )
                == None{}: Maybe<&2, BranchRecord>
            }
              & (
                {
                  k == v: String
                }
                  & {
                    SetBranch.version(
                      None{},
                      s,
                      r,
                      w,
                      t,
                      c,
                      k
                    )
                      == Out{
                        [],
                        Tables.Table.set(
                          BranchRecord,
                          NodeState.branches(s),
                          c,
                          BranchRecord{k, NodeState.self(s), 0n, 0n}
                        ),
                        NodeState.marks(s),
                        NodeState.groups(s),
                        NodeState.clashes(s),
                        [Logged.head(c, k)],
                        SetBranch.answer(Spec.SetBranch.Created{k})
                      }: Out
                  }
              )
          ),
        Maybes.Maybe.none_ne_some(String, v, h)
      )
    case Some{VersionRecord{bs, ps, a, z}}:
      +e => h =>
        +s = s
        +c = c
        +k = k
        (
          Equal.cong(
            Maybe<&2, VersionRecord>,
            Bool,
            y => Maybe.is_some(&2, VersionRecord, y),
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            Some{VersionRecord{bs, ps, a, z}},
            e
          ),
          sb_branch(
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            s,
            r,
            w,
            t,
            c,
            k,
            bs,
            v
          )({==})(h)
        )

law sb_point.fin.of:
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    VersionRecord.has(NodeState.versions(s), k) == True{}: Bool
  } -> {
    Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>
  } -> {
    k == v: String
  } -> {
    SetBranch.version(
      Tables.Table.get(VersionRecord, NodeState.versions(s), k),
      s,
      r,
      w,
      t,
      c,
      k
    )
      == Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{k, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(c, k)],
        SetBranch.answer(Spec.SetBranch.Created{k})
      }: Out
  } -> {
    Some{k} == Some{v}: Maybe<&2, String>
  }
    & (
      {
        VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & {
              SetBranch.version(
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{v, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_point.fin.of(s, r, w, t, c, k, v):
  hk => hc => +kv => ho =>
    %kv: {
      Some{k} == Some{_}: Maybe<&2, String>
    }
      & (
        {
          VersionRecord.has(NodeState.versions(s), _) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(s),
                c
              )
                == None{}: Maybe<&2, BranchRecord>
            }
              & {
                SetBranch.version(
                  Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                  s,
                  r,
                  w,
                  t,
                  c,
                  k
                )
                  == Out{
                    [],
                    Tables.Table.set(
                      BranchRecord,
                      NodeState.branches(s),
                      c,
                      BranchRecord{_, NodeState.self(s), 0n, 0n}
                    ),
                    NodeState.marks(s),
                    NodeState.groups(s),
                    NodeState.clashes(s),
                    [Logged.head(c, _)],
                    SetBranch.answer(Spec.SetBranch.Created{_})
                  }: Out
              }
          )
      )
    ({==}, (hk, (hc, ho)))

# sb_point, once the version k is found to be v
law sb_point.fin:
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    VersionRecord.has(NodeState.versions(s), k) == True{}: Bool
  }
    & (
      {
        Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>
      }
        & (
          {
            k == v: String
          }
            & {
              SetBranch.version(
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{k, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, k)],
                  SetBranch.answer(Spec.SetBranch.Created{k})
                }: Out
            }
        )
    ) -> {Some{k} == Some{v}: Maybe<&2, String>}
    & (
      {
        VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & {
              SetBranch.version(
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{v, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_point.fin.g1(
  s: NodeState,
  r: String,
  w: String,
  t: String,
  c: String,
  k: String,
  v: String,
  x: Pair(
    {VersionRecord.has(NodeState.versions(s), k) == True{}: Bool},
    Pair(
      {Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>},
      Pair(
        {k == v: String},
        {
          SetBranch.version(
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            s,
            r,
            w,
            t,
            c,
            k
          )
            == Out{
              [],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s),
                c,
                BranchRecord{k, NodeState.self(s), 0n, 0n}
              ),
              NodeState.marks(s),
              NodeState.groups(s),
              NodeState.clashes(s),
              [Logged.head(c, k)],
              SetBranch.answer(Spec.SetBranch.Created{k})
            }: Out
        }
      )
    )
  )
) -> Pair(
  {Some{k} == Some{v}: Maybe<&2, String>},
  Pair(
    {VersionRecord.has(NodeState.versions(s), v) == True{}: Bool},
    Pair(
      {Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>},
      {
        SetBranch.version(
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          s,
          r,
          w,
          t,
          c,
          k
        )
          == Out{
            [],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              c,
              BranchRecord{v, NodeState.self(s), 0n, 0n}
            ),
            NodeState.marks(s),
            NodeState.groups(s),
            NodeState.clashes(s),
            [Logged.head(c, v)],
            SetBranch.answer(Spec.SetBranch.Created{v})
          }: Out
      }
    )
  )
):
  match x:
    case Tuple{fst, snd}:
      match snd:
        case Tuple{fst1, snd1}:
          match snd1:
            case Tuple{fst2, snd}:
              sb_point.fin.of(s, r, w, t, c, k, v)(fst)(fst1)(fst2)(snd)

def sb_point.fin(s, r, w, t, c, k, v):
  x => sb_point.fin.g1(s, r, w, t, c, k, v, x)

# a set-branch to the point m that answers Created
law sb_point:
  for m: Maybe<&2, String>
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for c: String
  for v: String
  {
    Answer.version(Out.answer(SetBranch.point(m, s, r, w, t, c))) == Some{v}: Maybe<&2, String>
  } -> {
    m == Some{v}: Maybe<&2, String>
  }
    & (
      {
        VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & {
              SetBranch.point(
                m,
                s,
                r,
                w,
                t,
                c
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{v, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_point(m, s, r, w, t, c, v):
  match m:
    case None{}:
      h => Empty.absurd(
        {
          None{} == Some{v}: Maybe<&2, String>
        }
          & (
            {
              VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
            }
              & (
                {
                  Tables.Table.get(
                    BranchRecord,
                    NodeState.branches(s),
                    c
                  )
                    == None{}: Maybe<&2, BranchRecord>
                }
                  & {
                    SetBranch.point(
                      None{},
                      s,
                      r,
                      w,
                      t,
                      c
                    )
                      == Out{
                        [],
                        Tables.Table.set(
                          BranchRecord,
                          NodeState.branches(s),
                          c,
                          BranchRecord{v, NodeState.self(s), 0n, 0n}
                        ),
                        NodeState.marks(s),
                        NodeState.groups(s),
                        NodeState.clashes(s),
                        [Logged.head(c, v)],
                        SetBranch.answer(Spec.SetBranch.Created{v})
                      }: Out
                  }
              )
          ),
        Maybes.Maybe.none_ne_some(String, v, h)
      )
    case Some{+k}:
      h =>
        +s = s
        +c = c
        +r = r
        +w = w
        +t = t
        +v = v
        sb_point.fin(
          s,
          r,
          w,
          t,
          c,
          k,
          v,
          sb_version(
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            s,
            r,
            w,
            t,
            c,
            k,
            v
          )({==})(h)
        )

# a write as the owner that answers Written: its Out
law wr_at:
  for ok: Bool
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for v: String
  {
    Answer.version(
      Out.answer(Write.at(ok, s, r, w, t, n, b, x, BranchRecord{h, o, e, c}))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    Write.at(
      ok,
      s,
      r,
      w,
      t,
      n,
      b,
      x,
      BranchRecord{h, o, e, c}
    )
      == Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              t
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, c}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }: Out
  }

def wr_at(ok, s, r, w, t, n, b, x, h, o, e, c, v):
  match ok:
    case False{}:
      hv => Empty.absurd(
        {
          Write.at(
            False{},
            s,
            r,
            w,
            t,
            n,
            b,
            x,
            BranchRecord{h, o, e, c}
          )
            == Out{
              [
                Tables.Row{
                  r,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                    [h],
                    w,
                    t
                  }
                }
              ],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s),
                b,
                BranchRecord.moved(BranchRecord{h, o, e, c}, r)
              ),
              NodeState.marks(s),
              NodeState.groups(s),
              NodeState.clashes(s),
              [Logged.head(b, r)],
              Write.answer(Spec.Write.Written{r})
            }: Out
        },
        Maybes.Maybe.none_ne_some(String, v, hv)
      )
    case True{}:
      hv => {==}

# a write on a branch that answers Written: as its owner, with that Out
law wr_on:
  for owner: Bool
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for c: Nat
  for v: String
  {
    Answer.version(
      Out.answer(Write.on(owner, s, r, w, t, n, b, base, x, BranchRecord{h, o, e, c}))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    owner == True{}: Bool
  }
    & {
      Write.on(
        owner,
        s,
        r,
        w,
        t,
        n,
        b,
        base,
        x,
        BranchRecord{h, o, e, c}
      )
        == Out{
          [
            Tables.Row{
              r,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                [h],
                w,
                t
              }
            }
          ],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            b,
            BranchRecord.moved(BranchRecord{h, o, e, c}, r)
          ),
          NodeState.marks(s),
          NodeState.groups(s),
          NodeState.clashes(s),
          [Logged.head(b, r)],
          Write.answer(Spec.Write.Written{r})
        }: Out
    }

def wr_on(owner, s, r, w, t, n, b, base, x, h, o, e, c, v):
  match owner:
    case False{}:
      hv => Empty.absurd(
        {
          False{} == True{}: Bool
        }
          & {
            Write.on(
              False{},
              s,
              r,
              w,
              t,
              n,
              b,
              base,
              x,
              BranchRecord{h, o, e, c}
            )
              == Out{
                [
                  Tables.Row{
                    r,
                    VersionRecord{
                      Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                      [h],
                      w,
                      t
                    }
                  }
                ],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s),
                  b,
                  BranchRecord.moved(BranchRecord{h, o, e, c}, r)
                ),
                NodeState.marks(s),
                NodeState.groups(s),
                NodeState.clashes(s),
                [Logged.head(b, r)],
                Write.answer(Spec.Write.Written{r})
              }: Out
          },
        Maybes.Maybe.none_ne_some(String, v, hv)
      )
    case True{}:
      hv =>
        +h = h
        ({==}, wr_at(Base.is(base, h), s, r, w, t, n, b, x, h, o, e, c, v)(hv))

# a write with a free ID on an existing branch is a write on that branch
law wr_reduce:
  for s: NodeState
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for br: BranchRecord
  {
    VersionRecord.taken(NodeState.versions(s), r) == False{}: Bool
  } -> {
    Tables.Table.get(BranchRecord, NodeState.branches(s), b) == Some{br}: Maybe<&2, BranchRecord>
  } -> {
    Write.free(
      VersionRecord.taken(NodeState.versions(s), r),
      s,
      r,
      w,
      t,
      n,
      b,
      base,
      x
    )
      == Write.on(Owner.of(s, br), s, r, w, t, n, b, base, x, br): Out
  }

def wr_reduce(s, r, w, t, n, b, base, x, br):
  ht => hb =>
    +s = s
    +r = r
    +b = b
    +br = br
    %Equal.sym(
      Bool,
      VersionRecord.taken(NodeState.versions(s), r),
      False{},
      ht
    ): {
      Write.free(
        _,
        s,
        r,
        w,
        t,
        n,
        b,
        base,
        x
      )
        == Write.on(Owner.of(s, br), s, r, w, t, n, b, base, x, br): Out
    }
    %Equal.sym(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s), b),
      Some{br},
      hb
    ): {
      Write.branch(
        _,
        s,
        r,
        w,
        t,
        n,
        b,
        base,
        x
      )
        == Write.on(Owner.of(s, br), s, r, w, t, n, b, base, x, br): Out
    }
    {==}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a sync that answers Synced found no collision
law sync_free:
  for c: Bool
  for a: NodeState
  for o: NodeState
  {
    Out.answer(Sync.go(c, a, o)) == Spec.Answer.Sync{Spec.Sync.Synced{}}: Spec.Answer
  } -> {c == False{}: Bool}

def sync_free(c, a, o):
  match c:
    case True{}:
      h => Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.Sync{Spec.Sync.Refused{"version ID collision"}},
            Spec.Answer.Sync{Spec.Sync.Synced{}},
            h
          )
        )
      )
    case False{}:
      h => {==}

# add_find when the first new version, under i, is already held: by the lookup
# m of k, when i is k
law add_find.held.of:
  for m: Maybe<&2, VersionRecord>
  for i: String
  for x: VersionRecord
  for r: List<&2, Tables.Row<VersionRecord>>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    Tables.Table.get(VersionRecord, ys, k) == m: Maybe<&2, VersionRecord>
  } -> {
    VersionRecord.has(ys, i) == True{}: Bool
  } -> {
    String.eq(i, k) == True{}: Bool
  } -> {
    Maybe.or(
      &2,
      VersionRecord,
      Tables.Table.get(VersionRecord, ys, k),
      Tables.Table.find_row(VersionRecord, r, k)
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Some{x}
      ): Maybe<&2, VersionRecord>
  }

def add_find.held.of(m, i, x, r, ys, k):
  match m:
    case Some{u}:
      hm => hh => he =>
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, ys, k),
          Some{u},
          hm
        ): {
          Maybe.or(
            &2,
            VersionRecord,
            _,
            Tables.Table.find_row(VersionRecord, r, k)
          )
            == Maybe.or(&2, VersionRecord, _, Some{x}): Maybe<&2, VersionRecord>
        }
        {==}
    case None{}:
      +hm => +hh => he =>
        +ys = ys
        +i = i
        +k = k
        Empty.absurd(
          {
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, ys, k),
              Tables.Table.find_row(VersionRecord, r, k)
            )
              == Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, ys, k),
                Some{x}
              ): Maybe<&2, VersionRecord>
          },
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              VersionRecord.has(ys, i),
              True{},
              Equal.trans(
                Bool,
                False{},
                VersionRecord.has(ys, k),
                VersionRecord.has(ys, i),
                Equal.sym(
                  Bool,
                  VersionRecord.has(ys, k),
                  False{},
                  Equal.cong(
                    Maybe<&2, VersionRecord>,
                    Bool,
                    z => Maybe.is_some(&2, VersionRecord, z),
                    Tables.Table.get(VersionRecord, ys, k),
                    None{},
                    hm
                  )
                ),
                Equal.cong(
                  String,
                  Bool,
                  z => VersionRecord.has(ys, z),
                  k,
                  i,
                  Equal.sym(String, i, k, Strings.String.eq_sound(i, k)(he))
                )
              ),
              hh
            )
          )
        )

# add_find when the first new version, under i, is already held
law add_find.held:
  for hit: Bool
  for i: String
  for x: VersionRecord
  for r: List<&2, Tables.Row<VersionRecord>>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    VersionRecord.has(ys, i) == True{}: Bool
  } -> {
    String.eq(i, k) == hit: Bool
  } -> {
    Maybe.or(
      &2,
      VersionRecord,
      Tables.Table.get(VersionRecord, ys, k),
      Tables.Table.find_row(VersionRecord, r, k)
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Bools.Bool.when(
          Maybe<&2, VersionRecord>,
          hit,
          u => Some{x},
          u => Tables.Table.find_row(VersionRecord, r, k)
        )
      ): Maybe<&2, VersionRecord>
  }

def add_find.held(hit, i, x, r, ys, k):
  match hit:
    case False{}:
      hh => he => {==}
    case True{}:
      hh => he =>
        +ys = ys
        +k = k
        add_find.held.of(Tables.Table.get(VersionRecord, ys, k), i, x, r, ys, k)({==})(hh)(he)

# add_find when the first new version, under i, is not held
law add_find.fresh:
  for hit: Bool
  for i: String
  for x: VersionRecord
  for r: List<&2, Tables.Row<VersionRecord>>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    VersionRecord.has(ys, i) == False{}: Bool
  } -> {
    String.eq(i, k) == hit: Bool
  } -> {
    Maybe.or(
      &2,
      VersionRecord,
      Bools.Bool.when(
        Maybe<&2, VersionRecord>,
        hit,
        u => Some{x},
        u => Tables.Table.get(VersionRecord, ys, k)
      ),
      Tables.Table.find_row(VersionRecord, r, k)
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Bools.Bool.when(
          Maybe<&2, VersionRecord>,
          hit,
          u => Some{x},
          u => Tables.Table.find_row(VersionRecord, r, k)
        )
      ): Maybe<&2, VersionRecord>
  }

def add_find.fresh(hit, i, x, r, ys, k):
  match hit:
    case False{}:
      hh => he => {==}
    case True{}:
      hh => he =>
        +ys = ys
        +k = k
        +i = i
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, ys, k),
          None{},
          Tables.Table.none_of(
            VersionRecord,
            Tables.Table.get(VersionRecord, ys, k)
          )(
            Equal.trans(
              Bool,
              VersionRecord.has(ys, k),
              VersionRecord.has(ys, i),
              False{},
              Equal.cong(
                String,
                Bool,
                z => VersionRecord.has(ys, z),
                k,
                i,
                Equal.sym(String, i, k, Strings.String.eq_sound(i, k)(he))
              ),
              hh
            )
          )
        ):
          {Some{x} == Maybe.or(&2, VersionRecord, _, Some{x}): Maybe<&2, VersionRecord>}
        {==}

# add_find, for the first new version, under i
law add_find.one:
  for held: Bool
  for i: String
  for x: VersionRecord
  for r: List<&2, Tables.Row<VersionRecord>>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    VersionRecord.has(ys, i) == held: Bool
  } -> {
    Maybe.or(
      &2,
      VersionRecord,
      Tables.Table.get(VersionRecord, VersionRecord.add.put(i, x, ys, held), k),
      Tables.Table.find_row(VersionRecord, r, k)
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Tables.Table.find_row(VersionRecord, Tables.Row{i, x} <> r, k)
      ): Maybe<&2, VersionRecord>
  }

def add_find.one(held, i, x, r, ys, k):
  match held:
    case True{}:
      hh =>
        +i = i
        +k = k
        add_find.held(String.eq(i, k), i, x, r, ys, k)(hh)({==})
    case False{}:
      hh =>
        +i = i
        +k = k
        +x = x
        +ys = ys
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, Tables.Table.set(VersionRecord, ys, i, x), k),
          Bools.Bool.when(
            Maybe<&2, VersionRecord>,
            String.eq(i, k),
            u => Some{x},
            u => Tables.Table.get(VersionRecord, ys, k)
          ),
          Tables.Table.get_set(VersionRecord, ys, i, x, k)
        ):
          {
            Maybe.or(
              &2,
              VersionRecord,
              _,
              Tables.Table.find_row(VersionRecord, r, k)
            )
              == Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, ys, k),
                Bools.Bool.when(
                  Maybe<&2, VersionRecord>,
                  String.eq(i, k),
                  u => Some{x},
                  u => Tables.Table.find_row(VersionRecord, r, k)
                )
              ): Maybe<&2, VersionRecord>
          }
        add_find.fresh(String.eq(i, k), i, x, r, ys, k)(hh)({==})

# a version found after versions are added: the old one when held, else the
# first new one
law add_find:
  for xs: List<&2, Tables.Row<VersionRecord>>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add(xs, ys),
      k
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Tables.Table.find_row(VersionRecord, xs, k)
      ): Maybe<&2, VersionRecord>
  }

def add_find(xs, ys, k):
  match xs:
    case Nil{}:
      Equal.sym(
        Maybe<&2, VersionRecord>,
        Maybe.or(&2, VersionRecord, Tables.Table.get(VersionRecord, ys, k), None{}),
        Tables.Table.get(VersionRecord, ys, k),
        Maybes.Maybe.or_none(VersionRecord, Tables.Table.get(VersionRecord, ys, k))
      )
    case Con{Tables.Row{+i, +x}, +r}:
      +ys = ys
      +k = k
      Equal.trans(
        Maybe<&2, VersionRecord>,
        Tables.Table.get(
          VersionRecord,
          VersionRecord.add(r, VersionRecord.add.one(Tables.Row{i, x}, ys)),
          k
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, VersionRecord.add.one(Tables.Row{i, x}, ys), k),
          Tables.Table.find_row(VersionRecord, r, k)
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, ys, k),
          Tables.Table.find_row(VersionRecord, Tables.Row{i, x} <> r, k)
        ),
        add_find(r, VersionRecord.add.one(Tables.Row{i, x}, ys), k),
        add_find.one(VersionRecord.has(ys, i), i, x, r, ys, k)({==})
      )

# after a sync, a version is the own one when held, else the other node's
law sync_find:
  for o: Tables.Table<VersionRecord>
  for ys: Tables.Table<VersionRecord>
  for k: String
  {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add(
        Tables.Table.rows(VersionRecord, Tables.Table.keys(VersionRecord, o), o),
        ys
      ),
      k
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, ys, k),
        Tables.Table.get(VersionRecord, o, k)
      ): Maybe<&2, VersionRecord>
  }

def sync_find(o, ys, k):
  +o = o
  +k = k
  %Tables.Table.rows_find_keys(VersionRecord, o, k):
    {
      Tables.Table.get(
        VersionRecord,
        VersionRecord.add(
          Tables.Table.rows(VersionRecord, Tables.Table.keys(VersionRecord, o), o),
          ys
        ),
        k
      )
        == Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, ys, k),
          _
        ): Maybe<&2, VersionRecord>
    }
  add_find(Tables.Table.rows(VersionRecord, Tables.Table.keys(VersionRecord, o), o), ys, k)

# a sync that finds no collision found none at each key it walked
law collides_at.at:
  for hit: Bool
  for j: String
  for r: List<&2, String>
  for os: Tables.Table<VersionRecord>
  for vs: Tables.Table<VersionRecord>
  for k: String
  (
    {
      Sync.collides(r, os, vs) == False{}: Bool
    } -> {
      Shared.List.has(~String, ~String.eq, r, k) == True{}: Bool
    } -> {
      Sync.clash.at(
        Tables.Table.get(VersionRecord, vs, k),
        Tables.Table.get(VersionRecord, os, k)
      )
        == False{}: Bool
    }
  ) -> {
    String.eq(j, k) == hit: Bool
  } -> {
    Bool.or(
      Sync.clash.at(Tables.Table.get(VersionRecord, vs, j), Tables.Table.get(VersionRecord, os, j)),
      Sync.collides(r, os, vs)
    )
      == False{}: Bool
  } -> {
    List.any.if(u => Shared.List.has(~String, ~String.eq, r, k), hit) == True{}: Bool
  } -> {
    Sync.clash.at(
      Tables.Table.get(VersionRecord, vs, k),
      Tables.Table.get(VersionRecord, os, k)
    )
      == False{}: Bool
  }

def collides_at.at(hit, j, r, os, vs, k):
  match hit:
    case False{}:
      ih => he => +hc => hn =>
        +j = j
        +os = os
        +vs = vs
        ih(
          Bools.Bool.or_false_right(
            Sync.clash.at(
              Tables.Table.get(VersionRecord, vs, j),
              Tables.Table.get(VersionRecord, os, j)
            ),
            Sync.collides(r, os, vs)
          )(hc)
        )(hn)
    case True{}:
      ih => he => +hc => hn =>
        +j = j
        +k = k
        +os = os
        +vs = vs
        %Strings.String.eq_sound(
          j,
          k
        )(
          he
        ): {
          Sync.clash.at(
            Tables.Table.get(VersionRecord, vs, _),
            Tables.Table.get(VersionRecord, os, _)
          )
            == False{}: Bool
        }
        Bools.Bool.or_false_left(
          Sync.clash.at(
            Tables.Table.get(VersionRecord, vs, j),
            Tables.Table.get(VersionRecord, os, j)
          ),
          Sync.collides(r, os, vs)
        )(hc)

law collides_at:
  for ks: List<&2, String>
  for os: Tables.Table<VersionRecord>
  for vs: Tables.Table<VersionRecord>
  for k: String
  {
    Sync.collides(ks, os, vs) == False{}: Bool
  } -> {
    Shared.List.has(~String, ~String.eq, ks, k) == True{}: Bool
  } -> {
    Sync.clash.at(
      Tables.Table.get(VersionRecord, vs, k),
      Tables.Table.get(VersionRecord, os, k)
    )
      == False{}: Bool
  }

def collides_at(ks, os, vs, k):
  match ks:
    case Nil{}:
      hc => hn => Empty.absurd(
        {
          Sync.clash.at(
            Tables.Table.get(VersionRecord, vs, k),
            Tables.Table.get(VersionRecord, os, k)
          )
            == False{}: Bool
        },
        Shared.Bool.false_ne_true(hn)
      )
    case Con{+j, +r}:
      +os = os
      +vs = vs
      +k = k
      collides_at.at(String.eq(j, k), j, r, os, vs, k)(collides_at(r, os, vs, k))({==})

# when both lookups find a version, they hold the same bytes for each resource
def Compat(mb: Maybe<&2, VersionRecord>, ma: Maybe<&2, VersionRecord>) -> Type:
  match mb:
    case None{}:
      Unit
    case Some{v}:
      match ma:
        case None{}:
          Unit
        case Some{u}:
          @n: String -> {
            Blob.find.of(
              VersionRecord.blobs.of(Some{u}),
              n
            )
              == Blob.find.of(VersionRecord.blobs.of(Some{v}), n): Maybe<&2, List<&2, U32>>
          }

# compat_of, by the own lookup ma, once the other one found v
law compat_mine:
  for ma: Maybe<&2, VersionRecord>
  for v: VersionRecord
  {Sync.clash.at(ma, Some{v}) == False{}: Bool} -> Compat(Some{v}, ma)

def compat_mine(ma, v):
  match ma v:
    case None{} y:
      h => Unit{}
    case Some{VersionRecord{+ub, up, ua, ut}} VersionRecord{+vb, vp, va, vt}:
      +h =>
        n => Tables.Table.same_sound(
          ~List<&2, U32>,
          ~Octets.Bytes.is_eq,
          x => y => Octets.Bytes.is_eq_sound(x, y),
          ub,
          vb,
          n
        )(Bools.Bool.not_false(Tables.Table.same(~List<&2, U32>, ~Octets.Bytes.is_eq, ub, vb))(h))

# compat_of, by the other lookup mb
law compat_of.at:
  for mb: Maybe<&2, VersionRecord>
  for bs: Tables.Table<VersionRecord>
  for as: Tables.Table<VersionRecord>
  for k: String
  {
    Tables.Table.get(VersionRecord, bs, k) == mb: Maybe<&2, VersionRecord>
  } -> {
    Sync.collides(Tables.Table.keys(VersionRecord, bs), bs, as) == False{}: Bool
  } -> Compat(mb, Tables.Table.get(VersionRecord, as, k))

def compat_of.at(mb, bs, as, k):
  match mb:
    case None{}:
      hm => hc => Unit{}
    case Some{v}:
      +hm => hc =>
        +bs = bs
        +as = as
        +k = k
        compat_mine(Tables.Table.get(VersionRecord, as, k), v)((
            %hm: {Sync.clash.at(Tables.Table.get(VersionRecord, as, k), _) == False{}: Bool}
            collides_at(Tables.Table.keys(VersionRecord, bs), bs, as, k)(hc)(Equal.trans(Bool, Shared.List.has(~String, ~String.eq, Tables.Table.keys(VersionRecord, bs), k), Maybe.is_some(&2, VersionRecord, Tables.Table.get(VersionRecord, bs, k)), True{}, Tables.Table.keys_get(VersionRecord, bs, k), Equal.cong(Maybe<&2, VersionRecord>, Bool, z => Maybe.is_some(&2, VersionRecord, z), Tables.Table.get(VersionRecord, bs, k), Some{v}, hm)))))

# when a sync found no collision, versions under the same ID hold the same
# bytes for each resource
law compat_of:
  for bs: Tables.Table<VersionRecord>
  for as: Tables.Table<VersionRecord>
  for k: String
  {
    Sync.collides(Tables.Table.keys(VersionRecord, bs), bs, as) == False{}: Bool
  } -> Compat(Tables.Table.get(VersionRecord, bs, k), Tables.Table.get(VersionRecord, as, k))

def compat_of(bs, as, k):
  +bs = bs
  +k = k
  compat_of.at(Tables.Table.get(VersionRecord, bs, k), bs, as, k)({==})

# after a takes in b, and b takes in that, a resource of a version has the same
# bytes on both
law vb_conv:
  for ma: Maybe<&2, VersionRecord>
  for mb: Maybe<&2, VersionRecord>
  for n: String
  Compat(
    mb,
    ma
  ) -> {
    Blob.find.of(
      VersionRecord.blobs.of(Maybe.or(&2, VersionRecord, ma, mb)),
      n
    )
      == Blob.find.of(
        VersionRecord.blobs.of(
          Maybe.or(&2, VersionRecord, mb, Maybe.or(&2, VersionRecord, ma, mb))
        ),
        n
      ): Maybe<&2, List<&2, U32>>
  }

def vb_conv(ma, mb, n):
  match ma mb:
    case None{} None{}:
      h => {==}
    case None{} Some{v}:
      h => {==}
    case Some{u} None{}:
      h => {==}
    case Some{u} Some{v}:
      h => h(n)

# a stamp compares EQ with itself
law stamp_refl:
  for x: BranchRecord
  {BranchRecord.stamp.cmp(x, x) == EQ{}: Cmp}

def stamp_refl(x):
  match x:
    case BranchRecord{h, o, e, c}:
      %Equal.sym(Cmp, Nat.cmp(e, e), EQ{}, Nats.Nat.cmp_refl(e)):
        {Cmps.Cmp.then(_, Cmps.Cmp.then(Nat.cmp(c, c), String.order(h, h))) == EQ{}: Cmp}
      %Equal.sym(Cmp, Nat.cmp(c, c), EQ{}, Nats.Nat.cmp_refl(c)):
        {Cmps.Cmp.then(EQ{}, Cmps.Cmp.then(_, String.order(h, h))) == EQ{}: Cmp}
      Strings.String.order_refl(h)

# comparing stamps the other way round flips the order
law stamp_swap:
  for x: BranchRecord
  for y: BranchRecord
  {BranchRecord.stamp.cmp(y, x) == Cmps.Cmp.flip(BranchRecord.stamp.cmp(x, y)): Cmp}

def stamp_swap(x, y):
  match x y:
    case BranchRecord{+h1, o1, +e1, +c1} BranchRecord{+h2, o2, +e2, +c2}:
      %Equal.sym(
        Cmp,
        String.order(h2, h1),
        Cmps.Cmp.flip(String.order(h1, h2)),
        Strings.String.order_swap(h1, h2, EQ{})
      ):
        {
          Cmps.Cmp.then(
            Nat.cmp(e2, e1),
            Cmps.Cmp.then(Nat.cmp(c2, c1), _)
          )
            == Cmps.Cmp.flip(
              Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))
            ): Cmp
        }
      %Equal.sym(Cmp, Nat.cmp(c2, c1), Cmps.Cmp.flip(Nat.cmp(c1, c2)), Nats.Nat.cmp_swap(c1, c2)):
        {
          Cmps.Cmp.then(
            Nat.cmp(e2, e1),
            Cmps.Cmp.then(_, Cmps.Cmp.flip(String.order(h1, h2)))
          )
            == Cmps.Cmp.flip(
              Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))
            ): Cmp
        }
      %Equal.sym(Cmp, Nat.cmp(e2, e1), Cmps.Cmp.flip(Nat.cmp(e1, e2)), Nats.Nat.cmp_swap(e1, e2)):
        {
          Cmps.Cmp.then(
            _,
            Cmps.Cmp.then(Cmps.Cmp.flip(Nat.cmp(c1, c2)), Cmps.Cmp.flip(String.order(h1, h2)))
          )
            == Cmps.Cmp.flip(
              Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))
            ): Cmp
        }
      %Equal.sym(
        Cmp,
        Cmps.Cmp.then(Cmps.Cmp.flip(Nat.cmp(c1, c2)), Cmps.Cmp.flip(String.order(h1, h2))),
        Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2))),
        Cmps.Cmp.then_flip(Nat.cmp(c1, c2), String.order(h1, h2))
      ):
        {
          Cmps.Cmp.then(
            Cmps.Cmp.flip(Nat.cmp(e1, e2)),
            _
          )
            == Cmps.Cmp.flip(
              Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))
            ): Cmp
        }
      Cmps.Cmp.then_flip(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))

# the head of a branch
def BranchRecord.head(b: BranchRecord) -> String:
  match b:
    case BranchRecord{h, o, e, c}:
      h

# branches whose stamps compare EQ have the same head
law stamp_eq_head:
  for x: BranchRecord
  for y: BranchRecord
  {
    BranchRecord.stamp.cmp(x, y) == EQ{}: Cmp
  } -> {BranchRecord.head(x) == BranchRecord.head(y): String}

def stamp_eq_head(x, y):
  match x y:
    case BranchRecord{+h1, o1, e1, +c1} BranchRecord{+h2, o2, e2, +c2}:
      h => Strings.String.order_sound(
        h1,
        h2
      )(
        Cmps.Cmp.then_eq_right(
          Nat.cmp(c1, c2),
          String.order(h1, h2)
        )(
          Cmps.Cmp.then_eq_right(
            Nat.cmp(e1, e2),
            Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2))
          )(h)
        )
      )

# the head of the branch that m holds is its head mapped
law head_of_map:
  for m: Maybe<&2, BranchRecord>
  {
    BranchRecord.head.of(
      m
    )
      == Maybe.map(&2, BranchRecord, String, y => BranchRecord.head(y), m): Maybe<&2, String>
  }

def head_of_map(m):
  match m:
    case None{}:
      {==}
    case Some{BranchRecord{h, o, e, c}}:
      {==}

# after a takes in b's branch, and b takes in that, both have the same head
law hb_conv:
  for ma: Maybe<&2, BranchRecord>
  for mb: Maybe<&2, BranchRecord>
  {
    BranchRecord.head.of(
      Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
    )
      == BranchRecord.head.of(
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          mb,
          Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
        )
      ): Maybe<&2, String>
  }

def hb_conv(ma, mb):
  +ma = ma
  +mb = mb
  %Equal.sym(
    Maybe<&2, String>,
    BranchRecord.head.of(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)),
    Maybe.map(
      &2,
      BranchRecord,
      String,
      y => BranchRecord.head(y),
      Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
    ),
    head_of_map(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb))
  ):
    {
      _
        == BranchRecord.head.of(
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            mb,
            Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
          )
        ): Maybe<&2, String>
    }
  %Equal.sym(
    Maybe<&2, String>,
    BranchRecord.head.of(
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        mb,
        Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
      )
    ),
    Maybe.map(
      &2,
      BranchRecord,
      String,
      y => BranchRecord.head(y),
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        mb,
        Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
      )
    ),
    head_of_map(
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        mb,
        Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
      )
    )
  ):
    {
      Maybe.map(
        &2,
        BranchRecord,
        String,
        y => BranchRecord.head(y),
        Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, ma, mb)
      )
        == _: Maybe<&2, String>
    }
  Orders.Order.join_conv(
    ~BranchRecord,
    ~String,
    ~BranchRecord.stamp.cmp,
    ~BranchRecord.head,
    y => stamp_refl(y),
    a => b => stamp_swap(a, b),
    a => b => stamp_eq_head(a, b),
    ma,
    mb
  )

# a new branch t of another node, under the key k, where the node had none
law at_new:
  for hit: Bool
  for bs: Tables.Table<BranchRecord>
  for k: String
  for t: BranchRecord
  for c: String
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(BranchRecord, bs, k) == None{}: Maybe<&2, BranchRecord>
  } -> {
    Bools.Bool.when(
      Maybe<&2, BranchRecord>,
      hit,
      u => Some{t},
      u => Tables.Table.get(BranchRecord, bs, c)
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(BranchRecord, bs, c)
      ): Maybe<&2, BranchRecord>
  }

def at_new(hit, bs, k, t, c):
  match hit:
    case False{}:
      x => x1 => {==}
    case True{}:
      x => x1 => (%Strings.String.eq_sound(
        k,
        c
      )(
        x
      ): {
        Some{
          t
        }
          == Some{
            Orders.Order.pick(
              BranchRecord,
              BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, bs, _),
              t
            )
          }: Maybe<&2, BranchRecord>
      }; (%Equal.sym(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(BranchRecord, bs, k),
        None{},
        x1
      ): {
        Some{
          t
        }
          == Some{
            Orders.Order.pick(BranchRecord, BranchRecord.stamp.cmp, _, t)
          }: Maybe<&2, BranchRecord>
      }; {==}))

# a branch t of another node that wins over the node's mine (LT)
law at_set:
  for hit: Bool
  for bs: Tables.Table<BranchRecord>
  for k: String
  for mine: BranchRecord
  for t: BranchRecord
  for c: String
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(BranchRecord, bs, k) == Some{mine}: Maybe<&2, BranchRecord>
  } -> {
    BranchRecord.stamp.cmp(mine, t) == LT{}: Cmp
  } -> {
    Bools.Bool.when(
      Maybe<&2, BranchRecord>,
      hit,
      u => Some{t},
      u => Tables.Table.get(BranchRecord, bs, c)
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(BranchRecord, bs, c)
      ): Maybe<&2, BranchRecord>
  }

def at_set(hit, bs, k, mine, t, c):
  match hit:
    case False{}:
      he => hm => hc => {==}
    case True{}:
      he => hm => hc =>
        +bs = bs
        +k = k
        +c = c
        +mine = mine
        +t = t
        %Strings.String.eq_sound(
          k,
          c
        )(
          he
        ): {
          Some{
            t
          }
            == Orders.Order.step(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              True{},
              Some{t},
              Tables.Table.get(BranchRecord, bs, _)
            ): Maybe<&2, BranchRecord>
        }
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(BranchRecord, bs, k),
          Some{mine},
          hm
        ): {
          Some{
            t
          }
            == Orders.Order.step(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              True{},
              Some{t},
              _
            ): Maybe<&2, BranchRecord>
        }
        %Equal.sym(
          Cmp,
          BranchRecord.stamp.cmp(mine, t),
          LT{},
          hc
        ): {Some{t} == Some{Orders.Order.by(BranchRecord, _, mine, t)}: Maybe<&2, BranchRecord>}
        {==}

# a branch t of another node that does not win over the node's mine
law at_stay:
  for hit: Bool
  for bs: Tables.Table<BranchRecord>
  for k: String
  for mine: BranchRecord
  for t: BranchRecord
  for c: String
  for c0: Cmp
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(BranchRecord, bs, k) == Some{mine}: Maybe<&2, BranchRecord>
  } -> {
    BranchRecord.stamp.cmp(mine, t) == c0: Cmp
  } -> {
    Orders.Order.by(BranchRecord, c0, mine, t) == mine: BranchRecord
  } -> {
    Tables.Table.get(
      BranchRecord,
      bs,
      c
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(BranchRecord, bs, c)
      ): Maybe<&2, BranchRecord>
  }

def at_stay(hit, bs, k, mine, t, c, c0):
  match hit:
    case False{}:
      he => hm => hc => hb => {==}
    case True{}:
      he => +hm => hc => hb =>
        +bs = bs
        +k = k
        +c = c
        +mine = mine
        +t = t
        %Strings.String.eq_sound(
          k,
          c
        )(
          he
        ): {
          Tables.Table.get(
            BranchRecord,
            bs,
            _
          )
            == Orders.Order.step(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              True{},
              Some{t},
              Tables.Table.get(BranchRecord, bs, _)
            ): Maybe<&2, BranchRecord>
        }
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(BranchRecord, bs, k),
          Some{mine},
          hm
        ): {
          _
            == Orders.Order.step(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              True{},
              Some{t},
              _
            ): Maybe<&2, BranchRecord>
        }
        %Equal.sym(
          Cmp,
          BranchRecord.stamp.cmp(mine, t),
          c0,
          hc
        ): {Some{mine} == Some{Orders.Order.by(BranchRecord, _, mine, t)}: Maybe<&2, BranchRecord>}
        %Equal.sym(
          BranchRecord,
          Orders.Order.by(BranchRecord, c0, mine, t),
          mine,
          hb
        ): {Some{mine} == Some{_}: Maybe<&2, BranchRecord>}
        {==}

# the branches after another node's t met the node's mine, by the order c0
law pick_find:
  for c0: Cmp
  for k: String
  for mh: String
  for mo: String
  for me: Nat
  for mk: Nat
  for th: String
  for to: String
  for te: Nat
  for tk: Nat
  for vs: Tables.Table<VersionRecord>
  for bs: Tables.Table<BranchRecord>
  for cs: Tables.Table<Clash>
  for ns: List<&2, Logged>
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      bs,
      k
    )
      == Some{BranchRecord{mh, mo, me, mk}}: Maybe<&2, BranchRecord>
  } -> {
    BranchRecord.stamp.cmp(BranchRecord{mh, mo, me, mk}, BranchRecord{th, to, te, tk}) == c0: Cmp
  } -> {
    Tables.Table.get(
      BranchRecord,
      Mix.branches(
        Sync.pick(
          c0,
          k,
          BranchRecord{mh, mo, me, mk},
          BranchRecord{th, to, te, tk},
          vs,
          Mix{bs, cs, ns}
        )
      ),
      c
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        String.eq(k, c),
        Some{BranchRecord{th, to, te, tk}},
        Tables.Table.get(BranchRecord, bs, c)
      ): Maybe<&2, BranchRecord>
  }

def pick_find(c0, k, mh, mo, me, mk, th, to, te, tk, vs, bs, cs, ns, c):
  match c0:
    case LT{}:
      hm => hc =>
        +k = k
        +c = c
        +bs = bs
        +th = th
        +to = to
        +te = te
        +tk = tk
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(BranchRecord, bs, k, BranchRecord{th, to, te, tk}),
            c
          ),
          Bools.Bool.when(
            Maybe<&2, BranchRecord>,
            String.eq(k, c),
            u => Some{BranchRecord{th, to, te, tk}},
            u => Tables.Table.get(BranchRecord, bs, c)
          ),
          Tables.Table.get_set(BranchRecord, bs, k, BranchRecord{th, to, te, tk}, c)
        ):
          {
            _
              == Orders.Order.step(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                String.eq(k, c),
                Some{BranchRecord{th, to, te, tk}},
                Tables.Table.get(BranchRecord, bs, c)
              ): Maybe<&2, BranchRecord>
          }
        at_set(
          String.eq(k, c),
          bs,
          k,
          BranchRecord{mh, mo, me, mk},
          BranchRecord{th, to, te, tk},
          c
        )({==})(hm)(hc)
    case GT{}:
      hm => hc =>
        +k = k
        +c = c
        at_stay(
          String.eq(k, c),
          bs,
          k,
          BranchRecord{mh, mo, me, mk},
          BranchRecord{th, to, te, tk},
          c,
          GT{}
        )({==})(hm)(hc)({==})
    case EQ{}:
      hm => hc =>
        +k = k
        +c = c
        at_stay(
          String.eq(k, c),
          bs,
          k,
          BranchRecord{mh, mo, me, mk},
          BranchRecord{th, to, te, tk},
          c,
          EQ{}
        )({==})(hm)(hc)({==})

# the branches after another node's t met the branch that m0 holds
law at_find:
  for m0: Maybe<&2, BranchRecord>
  for k: String
  for th: String
  for to: String
  for te: Nat
  for tk: Nat
  for vs: Tables.Table<VersionRecord>
  for bs: Tables.Table<BranchRecord>
  for cs: Tables.Table<Clash>
  for ns: List<&2, Logged>
  for c: String
  {
    Tables.Table.get(BranchRecord, bs, k) == m0: Maybe<&2, BranchRecord>
  } -> {
    Tables.Table.get(
      BranchRecord,
      Mix.branches(Sync.at(m0, k, BranchRecord{th, to, te, tk}, vs, Mix{bs, cs, ns})),
      c
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        String.eq(k, c),
        Some{BranchRecord{th, to, te, tk}},
        Tables.Table.get(BranchRecord, bs, c)
      ): Maybe<&2, BranchRecord>
  }

def at_find(m0, k, th, to, te, tk, vs, bs, cs, ns, c):
  match m0:
    case None{}:
      hm =>
        +k = k
        +c = c
        +bs = bs
        +th = th
        +to = to
        +te = te
        +tk = tk
        %Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(BranchRecord, bs, k, BranchRecord{th, to, te, tk}),
            c
          ),
          Bools.Bool.when(
            Maybe<&2, BranchRecord>,
            String.eq(k, c),
            u => Some{BranchRecord{th, to, te, tk}},
            u => Tables.Table.get(BranchRecord, bs, c)
          ),
          Tables.Table.get_set(BranchRecord, bs, k, BranchRecord{th, to, te, tk}, c)
        ):
          {
            _
              == Orders.Order.step(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                String.eq(k, c),
                Some{BranchRecord{th, to, te, tk}},
                Tables.Table.get(BranchRecord, bs, c)
              ): Maybe<&2, BranchRecord>
          }
        at_new(String.eq(k, c), bs, k, BranchRecord{th, to, te, tk}, c)({==})(hm)
    case Some{BranchRecord{+mh, +mo, +me, +mk}}:
      hm =>
        +th = th
        +to = to
        +te = te
        +tk = tk
        pick_find(
          BranchRecord.stamp.cmp(BranchRecord{mh, mo, me, mk}, BranchRecord{th, to, te, tk}),
          k,
          mh,
          mo,
          me,
          mk,
          th,
          to,
          te,
          tk,
          vs,
          bs,
          cs,
          ns,
          c
        )(hm)({==})

# one step of a sync's branch pass, for the branch f of another node, named k
law seen_find:
  for k: String
  for f: Maybe<&2, BranchRecord>
  for acc: Mix
  for vs: Tables.Table<VersionRecord>
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      Mix.branches(Sync.seen.meet(k, f, acc, vs)),
      c
    )
      == Orders.Order.step(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        String.eq(k, c),
        f,
        Tables.Table.get(BranchRecord, Mix.branches(acc), c)
      ): Maybe<&2, BranchRecord>
  }

def seen_find(k, f, acc, vs, c):
  match f acc:
    case None{} Mix{bs, cs, ns}:
      +c = c
      Equal.sym(
        Maybe<&2, BranchRecord>,
        Orders.Order.step(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          String.eq(k, c),
          None{},
          Tables.Table.get(BranchRecord, bs, c)
        ),
        Tables.Table.get(BranchRecord, bs, c),
        Orders.Order.step_none(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          String.eq(k, c),
          Tables.Table.get(BranchRecord, bs, c)
        )
      )
    case Some{BranchRecord{th, to, te, tk}} Mix{+bs, cs, ns}:
      +k = k
      at_find(Tables.Table.get(BranchRecord, bs, k), k, th, to, te, tk, vs, bs, cs, ns, c)({==})

# a sync's branch pass, as a fold
law brs_fold_find:
  for ks: List<&2, String>
  for full: Tables.Table<BranchRecord>
  for vs: Tables.Table<VersionRecord>
  for acc: Mix
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      Mix.branches(Sync.branches(ks, full, vs, acc)),
      c
    )
      == Orders.Order.fold(
        ~BranchRecord,
        ~Tables.Table<BranchRecord>,
        ~BranchRecord.stamp.cmp,
        ~(t => k => Tables.Table.get(BranchRecord, t, k)),
        ks,
        full,
        c,
        Tables.Table.get(BranchRecord, Mix.branches(acc), c)
      ): Maybe<&2, BranchRecord>
  }

def brs_fold_find(ks, full, vs, acc, c):
  match ks:
    case Nil{}:
      {==}
    case Con{+k, r}:
      +full = full
      +vs = vs
      +c = c
      +acc = acc
      %seen_find(k, Tables.Table.get(BranchRecord, full, k), acc, vs, c):
        {
          Tables.Table.get(
            BranchRecord,
            Mix.branches(
              Sync.branches(
                r,
                full,
                vs,
                Sync.seen.meet(k, Tables.Table.get(BranchRecord, full, k), acc, vs)
              )
            ),
            c
          )
            == Orders.Order.fold(
              ~BranchRecord,
              ~Tables.Table<BranchRecord>,
              ~BranchRecord.stamp.cmp,
              ~(t => k => Tables.Table.get(BranchRecord, t, k)),
              r,
              full,
              c,
              _
            ): Maybe<&2, BranchRecord>
        }
      brs_fold_find(
        r,
        full,
        vs,
        Sync.seen.meet(k, Tables.Table.get(BranchRecord, full, k), acc, vs),
        c
      )

# after a sync's branch pass, a branch is the winner of the node's own and the
# other node's
law sync_branches_find:
  for full: Tables.Table<BranchRecord>
  for vs: Tables.Table<VersionRecord>
  for acc: Mix
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      Mix.branches(Sync.branches(Tables.Table.keys(BranchRecord, full), full, vs, acc)),
      c
    )
      == Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Tables.Table.get(BranchRecord, Mix.branches(acc), c),
        Tables.Table.get(BranchRecord, full, c)
      ): Maybe<&2, BranchRecord>
  }

def sync_branches_find(full, vs, acc, c):
  +full = full
  +acc = acc
  +c = c
  Equal.trans(
    Maybe<&2, BranchRecord>,
    Tables.Table.get(
      BranchRecord,
      Mix.branches(Sync.branches(Tables.Table.keys(BranchRecord, full), full, vs, acc)),
      c
    ),
    Orders.Order.fold(
      ~BranchRecord,
      ~Tables.Table<BranchRecord>,
      ~BranchRecord.stamp.cmp,
      ~(t => k => Tables.Table.get(BranchRecord, t, k)),
      Tables.Table.keys(BranchRecord, full),
      full,
      c,
      Tables.Table.get(BranchRecord, Mix.branches(acc), c)
    ),
    Orders.Order.join(
      ~BranchRecord,
      ~BranchRecord.stamp.cmp,
      Tables.Table.get(BranchRecord, Mix.branches(acc), c),
      Tables.Table.get(BranchRecord, full, c)
    ),
    brs_fold_find(Tables.Table.keys(BranchRecord, full), full, vs, acc, c),
    Orders.Order.fold_all(
      ~BranchRecord,
      ~Tables.Table<BranchRecord>,
      ~BranchRecord.stamp.cmp,
      ~(t => k => Tables.Table.get(BranchRecord, t, k)),
      y => stamp_refl(y),
      Tables.Table.keys(BranchRecord, full),
      full,
      c,
      Tables.Table.get(BranchRecord, Mix.branches(acc), c),
      h => Tables.Table.none_of(
        BranchRecord,
        Tables.Table.get(BranchRecord, full, c)
      )(
        Equal.trans(
          Bool,
          Maybe.is_some(&2, BranchRecord, Tables.Table.get(BranchRecord, full, c)),
          Shared.List.has(~String, ~String.eq, Tables.Table.keys(BranchRecord, full), c),
          False{},
          Equal.sym(
            Bool,
            Shared.List.has(~String, ~String.eq, Tables.Table.keys(BranchRecord, full), c),
            Maybe.is_some(&2, BranchRecord, Tables.Table.get(BranchRecord, full, c)),
            Tables.Table.keys_get(BranchRecord, full, c)
          ),
          h
        )
      )
    )
  )

# the order of versions for marks: the smaller version is the greater
def VersionRecord.rev(a: String, b: String) -> Cmp:
  String.order(b, a)

# the version order of marks compares EQ with itself
law rev_refl:
  for a: String
  {VersionRecord.rev(a, a) == EQ{}: Cmp}

def rev_refl(a):
  Strings.String.order_refl(a)

# the version order of marks the other way round is flipped
law rev_swap:
  for a: String
  for b: String
  {VersionRecord.rev(b, a) == Cmps.Cmp.flip(VersionRecord.rev(a, b)): Cmp}

def rev_swap(a, b):
  Strings.String.order_swap(b, a, EQ{})

# versions that the version order of marks calls EQ are equal
law rev_same:
  for a: String
  for b: String
  {VersionRecord.rev(a, b) == EQ{}: Cmp} -> {a == b: String}

def rev_same(a, b):
  h =>
    +a = a
    +b = b
    Equal.sym(String, b, a, Strings.String.order_sound(b, a)(h))

# the marks of a branch after a set: by whether the set was on that branch
law marks_of_set:
  for hit: Bool
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for b: String
  for x: Tables.Table<MarkAt>
  for qb: String
  {
    String.eq(b, qb) == hit: Bool
  } -> {
    Marks.of(
      Tables.Table.set(Tables.Table<MarkAt>, ms, b, x),
      qb
    )
      == Bools.Bool.when(
        Tables.Table<MarkAt>,
        hit,
        u => x,
        u => Marks.of(ms, qb)
      ): Tables.Table<MarkAt>
  }

def marks_of_set(hit, ms, b, x, qb):
  match hit:
    case True{}:
      +he =>
        +ms = ms
        +b = b
        +x = x
        +qb = qb
        %Equal.sym(
          Maybe<&2, Tables.Table<MarkAt>>,
          Tables.Table.get(
            Tables.Table<MarkAt>,
            Tables.Table.set(Tables.Table<MarkAt>, ms, b, x),
            qb
          ),
          Bools.Bool.when(
            Maybe<&2, Tables.Table<MarkAt>>,
            String.eq(b, qb),
            u => Some{x},
            u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)
          ),
          Tables.Table.get_set(Tables.Table<MarkAt>, ms, b, x, qb)
        ):
          {
            Maybe.default(
              &2,
              Tables.Table<MarkAt>,
              _,
              Tables.Table.new(MarkAt)
            )
              == x: Tables.Table<MarkAt>
          }
        %Equal.sym(Bool, String.eq(b, qb), True{}, he):
          {
            Maybe.default(
              &2,
              Tables.Table<MarkAt>,
              Bools.Bool.when(
                Maybe<&2, Tables.Table<MarkAt>>,
                _,
                u => Some{x},
                u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)
              ),
              Tables.Table.new(MarkAt)
            )
              == x: Tables.Table<MarkAt>
          }
        {==}
    case False{}:
      +he =>
        +ms = ms
        +b = b
        +x = x
        +qb = qb
        %Equal.sym(
          Maybe<&2, Tables.Table<MarkAt>>,
          Tables.Table.get(
            Tables.Table<MarkAt>,
            Tables.Table.set(Tables.Table<MarkAt>, ms, b, x),
            qb
          ),
          Bools.Bool.when(
            Maybe<&2, Tables.Table<MarkAt>>,
            String.eq(b, qb),
            u => Some{x},
            u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)
          ),
          Tables.Table.get_set(Tables.Table<MarkAt>, ms, b, x, qb)
        ):
          {
            Maybe.default(
              &2,
              Tables.Table<MarkAt>,
              _,
              Tables.Table.new(MarkAt)
            )
              == Marks.of(ms, qb): Tables.Table<MarkAt>
          }
        %Equal.sym(Bool, String.eq(b, qb), False{}, he):
          {
            Maybe.default(
              &2,
              Tables.Table<MarkAt>,
              Bools.Bool.when(
                Maybe<&2, Tables.Table<MarkAt>>,
                _,
                u => Some{x},
                u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)
              ),
              Tables.Table.new(MarkAt)
            )
              == Marks.of(ms, qb): Tables.Table<MarkAt>
          }
        {==}

# a mark's version after a set, when the set is on its branch: by whether it
# is on its name too
law mark_set_find.name:
  for hit: Bool
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for b: String
  for m: String
  for v: String
  for t: String
  for qm: String
  {
    String.eq(m, qm) == hit: Bool
  } -> {
    MarkAt.version.of(
      Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm)
    )
      == Bools.Bool.when(
        Maybe<&2, String>,
        hit,
        u => Some{v},
        u => MarkAt.find(ms, b, qm)
      ): Maybe<&2, String>
  }

def mark_set_find.name(hit, ms, b, m, v, t, qm):
  match hit:
    case True{}:
      he =>
        +ms = ms
        +b = b
        +m = m
        +v = v
        +t = t
        +qm = qm
        %Equal.sym(
          Maybe<&2, MarkAt>,
          Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm),
          Bools.Bool.when(
            Maybe<&2, MarkAt>,
            String.eq(m, qm),
            u => Some{MarkAt{v, t}},
            u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)
          ),
          Tables.Table.get_set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}, qm)
        ):
          {MarkAt.version.of(_) == Some{v}: Maybe<&2, String>}
        %Equal.sym(Bool, String.eq(m, qm), True{}, he):
          {
            MarkAt.version.of(
              Bools.Bool.when(
                Maybe<&2, MarkAt>,
                _,
                u => Some{MarkAt{v, t}},
                u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)
              )
            )
              == Some{v}: Maybe<&2, String>
          }
        {==}
    case False{}:
      he =>
        +ms = ms
        +b = b
        +m = m
        +v = v
        +t = t
        +qm = qm
        %Equal.sym(
          Maybe<&2, MarkAt>,
          Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm),
          Bools.Bool.when(
            Maybe<&2, MarkAt>,
            String.eq(m, qm),
            u => Some{MarkAt{v, t}},
            u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)
          ),
          Tables.Table.get_set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}, qm)
        ):
          {MarkAt.version.of(_) == MarkAt.find(ms, b, qm): Maybe<&2, String>}
        %Equal.sym(Bool, String.eq(m, qm), False{}, he):
          {
            MarkAt.version.of(
              Bools.Bool.when(
                Maybe<&2, MarkAt>,
                _,
                u => Some{MarkAt{v, t}},
                u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)
              )
            )
              == MarkAt.find(ms, b, qm): Maybe<&2, String>
          }
        {==}

# the version of the mark named by the second of q, on the branch b, in the
# marks that are the first of q
def Marks.at(
  q: +Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>,
  b: String
) -> Maybe<&2, String>:
  match q:
    case (ms, m):
      MarkAt.find(ms, b, m)

# a mark's version after another node's version f met mv, when the step is
# on the mark's branch (hb) and name (hm)
def Marks.on(hb: Bool, hm: Bool, f: Maybe<&2, String>, mv: Maybe<&2, String>) -> Maybe<&2, String>:
  match hb:
    case False{}:
      mv
    case True{}:
      Orders.Order.step(~String, ~VersionRecord.rev, hm, f, mv)

# a mark's version after the marks ks of the branch inner met mv, when that
# branch is the mark's (hb)
def Marks.in(
  hb: Bool,
  ks: List<&2, String>,
  inner: Tables.Table<MarkAt>,
  qm: String,
  mv: Maybe<&2, String>
) -> Maybe<&2, String>:
  match hb:
    case False{}:
      mv
    case True{}:
      Orders.Order.fold(
        ~String,
        ~Tables.Table<MarkAt>,
        ~VersionRecord.rev,
        ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
        ks,
        inner,
        qm,
        mv
      )

# a set elsewhere leaves a mark's version: by whether it is on its branch (hb)
law set_other.at:
  for hb: Bool
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for b: String
  for m: String
  for x: MarkAt
  for qb: String
  for qm: String
  {
    String.eq(b, qb) == hb: Bool
  } -> {
    Bool.and(hb, String.eq(m, qm)) == False{}: Bool
  } -> {MarkAt.find(MarkAt.set(ms, b, m, x), qb, qm) == MarkAt.find(ms, qb, qm): Maybe<&2, String>}

def set_other.at(hb, ms, b, m, x, qb, qm):
  match hb:
    case False{}:
      he => hm =>
        +ms = ms
        +b = b
        +m = m
        +x = x
        +qb = qb
        Equal.cong(
          Tables.Table<MarkAt>,
          Maybe<&2, String>,
          z => MarkAt.version.of(Tables.Table.get(MarkAt, z, qm)),
          Marks.of(MarkAt.set(ms, b, m, x), qb),
          Marks.of(ms, qb),
          marks_of_set(False{}, ms, b, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x), qb)(he)
        )
    case True{}:
      +he => +hm =>
        +ms = ms
        +b = b
        +m = m
        +x = x
        +qb = qb
        +qm = qm
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(MarkAt.set(ms, b, m, x), qb, qm),
          MarkAt.version.of(
            Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x), qm)
          ),
          MarkAt.find(ms, qb, qm),
          Equal.cong(
            Tables.Table<MarkAt>,
            Maybe<&2, String>,
            z => MarkAt.version.of(Tables.Table.get(MarkAt, z, qm)),
            Marks.of(MarkAt.set(ms, b, m, x), qb),
            Tables.Table.set(MarkAt, Marks.of(ms, b), m, x),
            marks_of_set(True{}, ms, b, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x), qb)(he)
          ),
          Equal.trans(
            Maybe<&2, String>,
            MarkAt.version.of(
              Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x), qm)
            ),
            MarkAt.find(ms, b, qm),
            MarkAt.find(ms, qb, qm),
            (
              %Equal.sym(Maybe<&2, MarkAt>, Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, x), qm), Bools.Bool.when(Maybe<&2, MarkAt>, String.eq(m, qm), u => Some{x}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)), Tables.Table.get_set(MarkAt, Marks.of(ms, b), m, x, qm)): {MarkAt.version.of(_) == MarkAt.find(ms, b, qm): Maybe<&2, String>}
              %Equal.sym(Bool, String.eq(m, qm), False{}, hm): {MarkAt.version.of(Bools.Bool.when(Maybe<&2, MarkAt>, _, u => Some{x}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm))) == MarkAt.find(ms, b, qm): Maybe<&2, String>}
              {==}),
            Equal.cong(
              String,
              Maybe<&2, String>,
              z => MarkAt.find(ms, z, qm),
              b,
              qb,
              Strings.String.eq_sound(b, qb)(he)
            )
          )
        )

# a mark's version after a step at another mark: by the own version
law seen_other.sm:
  for sm: Bool
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for ns: List<&2, Logged>
  for b: String
  for m: String
  for k: String
  for x: MarkAt
  for qb: String
  for qm: String
  {
    Bool.and(String.eq(b, qb), String.eq(m, qm)) == False{}: Bool
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.smaller(sm, b, m, k, x, Marked{ms, ns})),
      qb,
      qm
    )
      == MarkAt.find(ms, qb, qm): Maybe<&2, String>
  }

def seen_other.sm(sm, ms, ns, b, m, k, x, qb, qm):
  match sm x:
    case True{} MarkAt{v, t}:
      h =>
        +b = b
        +qb = qb
        set_other.at(String.eq(b, qb), ms, b, m, MarkAt{v, t}, qb, qm)({==})(h)
    case False{} y:
      h => {==}

law seen_other.at:
  for own: Maybe<&2, String>
  for b: String
  for m: String
  for x: MarkAt
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for ns: List<&2, Logged>
  for qb: String
  for qm: String
  {
    Bool.and(String.eq(b, qb), String.eq(m, qm)) == False{}: Bool
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.at(own, b, m, x, Marked{ms, ns})),
      qb,
      qm
    )
      == MarkAt.find(ms, qb, qm): Maybe<&2, String>
  }

def seen_other.at(own, b, m, x, ms, ns, qb, qm):
  match own x:
    case None{} y:
      h =>
        +b = b
        +qb = qb
        set_other.at(String.eq(b, qb), ms, b, m, y, qb, qm)({==})(h)
    case Some{+k} MarkAt{+v, t}:
      h => seen_other.sm(Cmp.is_lt(String.order(v, k)), ms, ns, b, m, k, MarkAt{v, t}, qb, qm)(h)

# a step at another mark leaves a mark's version
law seen_other:
  for b: String
  for m: String
  for vis: Maybe<&2, MarkAt>
  for acc: Marked
  for qb: String
  for qm: String
  {
    Bool.and(String.eq(b, qb), String.eq(m, qm)) == False{}: Bool
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.seen(b, m, vis, acc)),
      qb,
      qm
    )
      == MarkAt.find(Marked.marks(acc), qb, qm): Maybe<&2, String>
  }

def seen_other(b, m, vis, acc, qb, qm):
  match vis acc:
    case None{} z:
      h => {==}
    case Some{x} Marked{+ms, ns}:
      h =>
        +b = b
        +m = m
        seen_other.at(MarkAt.find(ms, b, m), b, m, x, ms, ns, qb, qm)(h)

# a set of a mark is found under that mark
law set_self:
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for b: String
  for m: String
  for v: String
  for t: String
  {MarkAt.find(MarkAt.set(ms, b, m, MarkAt{v, t}), b, m) == Some{v}: Maybe<&2, String>}

def set_self(ms, b, m, v, t):
  +ms = ms
  +b = b
  +m = m
  +v = v
  +t = t
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(MarkAt.set(ms, b, m, MarkAt{v, t}), b, m),
    MarkAt.version.of(
      Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), m)
    ),
    Some{v},
    Equal.cong(
      Tables.Table<MarkAt>,
      Maybe<&2, String>,
      z => MarkAt.version.of(Tables.Table.get(MarkAt, z, m)),
      Marks.of(MarkAt.set(ms, b, m, MarkAt{v, t}), b),
      Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}),
      marks_of_set(
        True{},
        ms,
        b,
        Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}),
        b
      )(Strings.String.eq_refl(b))
    ),
    mark_set_find.name(True{}, ms, b, m, v, t, m)(Strings.String.eq_refl(m))
  )

# a step at the mark itself, by the order c0 of the other version v and the
# own k
law seen_hit.by:
  for c0: Cmp
  for b: String
  for m: String
  for k: String
  for v: String
  for t: String
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for ns: List<&2, Logged>
  {
    MarkAt.find(ms, b, m) == Some{k}: Maybe<&2, String>
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.smaller(Cmp.is_lt(c0), b, m, k, MarkAt{v, t}, Marked{ms, ns})),
      b,
      m
    )
      == Some{Orders.Order.by(String, c0, k, v)}: Maybe<&2, String>
  }

def seen_hit.by(c0, b, m, k, v, t, ms, ns):
  match c0:
    case LT{}:
      h => set_self(ms, b, m, v, t)
    case EQ{}:
      h => h
    case GT{}:
      h => h

law seen_hit.at:
  for own: Maybe<&2, String>
  for b: String
  for m: String
  for x: MarkAt
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for ns: List<&2, Logged>
  {
    MarkAt.find(ms, b, m) == own: Maybe<&2, String>
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.at(own, b, m, x, Marked{ms, ns})),
      b,
      m
    )
      == Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(ms, b, m),
        MarkAt.version.of(Some{x})
      ): Maybe<&2, String>
  }

def seen_hit.at(own, b, m, x, ms, ns):
  match own x:
    case None{} MarkAt{v, t}:
      +h =>
        +ms = ms
        +b = b
        +m = m
        %Equal.sym(
          Maybe<&2, String>,
          MarkAt.find(ms, b, m),
          None{},
          h
        ): {
          MarkAt.find(
            MarkAt.set(ms, b, m, MarkAt{v, t}),
            b,
            m
          )
            == Orders.Order.join(~String, ~VersionRecord.rev, _, Some{v}): Maybe<&2, String>
        }
        set_self(ms, b, m, v, t)
    case Some{+k} MarkAt{+v, t}:
      +h =>
        +ms = ms
        +b = b
        +m = m
        %Equal.sym(
          Maybe<&2, String>,
          MarkAt.find(ms, b, m),
          Some{k},
          h
        ): {
          MarkAt.find(
            Marked.marks(
              Sync.mark.smaller(
                Cmp.is_lt(String.order(v, k)),
                b,
                m,
                k,
                MarkAt{v, t},
                Marked{ms, ns}
              )
            ),
            b,
            m
          )
            == Orders.Order.join(~String, ~VersionRecord.rev, _, Some{v}): Maybe<&2, String>
        }
        seen_hit.by(String.order(v, k), b, m, k, v, t, ms, ns)(h)

# a step at the mark itself joins the other node's version
law seen_hit:
  for b: String
  for m: String
  for vis: Maybe<&2, MarkAt>
  for acc: Marked
  {
    MarkAt.find(
      Marked.marks(Sync.mark.seen(b, m, vis, acc)),
      b,
      m
    )
      == Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(Marked.marks(acc), b, m),
        MarkAt.version.of(vis)
      ): Maybe<&2, String>
  }

def seen_hit(b, m, vis, acc):
  match vis acc:
    case None{} z:
      {==}
    case Some{x} Marked{+ms, ns}:
      +b = b
      +m = m
      seen_hit.at(MarkAt.find(ms, b, m), b, m, x, ms, ns)({==})

# one step of a sync's mark pass, by whether it is on the mark's branch (hb)
# and name (hm)
law seen_step.at:
  for hb: Bool
  for hm: Bool
  for b: String
  for m: String
  for vis: Maybe<&2, MarkAt>
  for acc: Marked
  for qb: String
  for qm: String
  {
    String.eq(b, qb) == hb: Bool
  } -> {
    String.eq(m, qm) == hm: Bool
  } -> {
    MarkAt.find(
      Marked.marks(Sync.mark.seen(b, m, vis, acc)),
      qb,
      qm
    )
      == Marks.on(
        hb,
        hm,
        MarkAt.version.of(vis),
        MarkAt.find(Marked.marks(acc), qb, qm)
      ): Maybe<&2, String>
  }

def seen_step.at(hb, hm, b, m, vis, acc, qb, qm):
  match hb hm:
    case False{} z:
      +eb => em =>
        +b = b
        +qb = qb
        seen_other(b, m, vis, acc, qb, qm)((
            %Equal.sym(Bool, String.eq(b, qb), False{}, eb): {Bool.and(_, String.eq(m, qm)) == False{}: Bool}
            {==}))
    case True{} False{}:
      +eb => +em =>
        +b = b
        +qb = qb
        +m = m
        +qm = qm
        seen_other(b, m, vis, acc, qb, qm)((
            %Equal.sym(Bool, String.eq(b, qb), True{}, eb): {Bool.and(_, String.eq(m, qm)) == False{}: Bool}
            %Equal.sym(Bool, String.eq(m, qm), False{}, em): {Bool.and(True{}, _) == False{}: Bool}
            {==}))
    case True{} True{}:
      +eb => +em =>
        +b = b
        +qb = qb
        +m = m
        +qm = qm
        %Strings.String.eq_sound(
          b,
          qb
        )(
          eb
        ): {
          MarkAt.find(
            Marked.marks(Sync.mark.seen(b, m, vis, acc)),
            _,
            qm
          )
            == Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(Marked.marks(acc), _, qm),
              MarkAt.version.of(vis)
            ): Maybe<&2, String>
        }
        %Strings.String.eq_sound(
          m,
          qm
        )(
          em
        ): {
          MarkAt.find(
            Marked.marks(Sync.mark.seen(b, m, vis, acc)),
            b,
            _
          )
            == Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(Marked.marks(acc), b, _),
              MarkAt.version.of(vis)
            ): Maybe<&2, String>
        }
        seen_hit(b, m, vis, acc)

# one step of a sync's mark pass
law seen_step:
  for b: String
  for m: String
  for vis: Maybe<&2, MarkAt>
  for acc: Marked
  for qb: String
  for qm: String
  {
    MarkAt.find(
      Marked.marks(Sync.mark.seen(b, m, vis, acc)),
      qb,
      qm
    )
      == Marks.on(
        String.eq(b, qb),
        String.eq(m, qm),
        MarkAt.version.of(vis),
        MarkAt.find(Marked.marks(acc), qb, qm)
      ): Maybe<&2, String>
  }

def seen_step(b, m, vis, acc, qb, qm):
  +b = b
  +m = m
  +qb = qb
  +qm = qm
  seen_step.at(String.eq(b, qb), String.eq(m, qm), b, m, vis, acc, qb, qm)({==})({==})

# the pass over the marks ks of one branch b, as a fold
law marks_in_find:
  for hb: Bool
  for ks: List<&2, String>
  for b: String
  for inner: Tables.Table<MarkAt>
  for acc: Marked
  for qb: String
  for qm: String
  {
    String.eq(b, qb) == hb: Bool
  } -> {
    MarkAt.find(
      Marked.marks(Sync.marks.of(b, ks, inner, acc)),
      qb,
      qm
    )
      == Marks.in(hb, ks, inner, qm, MarkAt.find(Marked.marks(acc), qb, qm)): Maybe<&2, String>
  }

def marks_in_find(hb, ks, b, inner, acc, qb, qm):
  match hb ks:
    case False{} Nil{}:
      he => {==}
    case True{} Nil{}:
      he => {==}
    case False{} Con{+m, r}:
      +he =>
        +b = b
        +inner = inner
        +acc = acc
        +qb = qb
        +qm = qm
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            Marked.marks(
              Sync.marks.of(
                b,
                r,
                inner,
                Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)
              )
            ),
            qb,
            qm
          ),
          MarkAt.find(
            Marked.marks(Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)),
            qb,
            qm
          ),
          MarkAt.find(Marked.marks(acc), qb, qm),
          marks_in_find(
            False{},
            r,
            b,
            inner,
            Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc),
            qb,
            qm
          )(he),
          (
            %he: {MarkAt.find(Marked.marks(Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)), qb, qm) == Marks.on(_, String.eq(m, qm), MarkAt.version.of(Tables.Table.get(MarkAt, inner, m)), MarkAt.find(Marked.marks(acc), qb, qm)): Maybe<&2, String>}
            seen_step(b, m, Tables.Table.get(MarkAt, inner, m), acc, qb, qm))
        )
    case True{} Con{+m, r}:
      +he =>
        +b = b
        +inner = inner
        +acc = acc
        +qb = qb
        +qm = qm
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            Marked.marks(
              Sync.marks.of(
                b,
                r,
                inner,
                Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)
              )
            ),
            qb,
            qm
          ),
          Orders.Order.fold(
            ~String,
            ~Tables.Table<MarkAt>,
            ~VersionRecord.rev,
            ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
            r,
            inner,
            qm,
            MarkAt.find(
              Marked.marks(Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)),
              qb,
              qm
            )
          ),
          Orders.Order.fold(
            ~String,
            ~Tables.Table<MarkAt>,
            ~VersionRecord.rev,
            ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
            r,
            inner,
            qm,
            Orders.Order.step(
              ~String,
              ~VersionRecord.rev,
              String.eq(m, qm),
              MarkAt.version.of(Tables.Table.get(MarkAt, inner, m)),
              MarkAt.find(Marked.marks(acc), qb, qm)
            )
          ),
          marks_in_find(
            True{},
            r,
            b,
            inner,
            Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc),
            qb,
            qm
          )(he),
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, String>,
            z => Orders.Order.fold(
              ~String,
              ~Tables.Table<MarkAt>,
              ~VersionRecord.rev,
              ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
              r,
              inner,
              qm,
              z
            ),
            MarkAt.find(
              Marked.marks(Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)),
              qb,
              qm
            ),
            Orders.Order.step(
              ~String,
              ~VersionRecord.rev,
              String.eq(m, qm),
              MarkAt.version.of(Tables.Table.get(MarkAt, inner, m)),
              MarkAt.find(Marked.marks(acc), qb, qm)
            ),
            (
              %he: {MarkAt.find(Marked.marks(Sync.mark.seen(b, m, Tables.Table.get(MarkAt, inner, m), acc)), qb, qm) == Marks.on(_, String.eq(m, qm), MarkAt.version.of(Tables.Table.get(MarkAt, inner, m)), MarkAt.find(Marked.marks(acc), qb, qm)): Maybe<&2, String>}
              seen_step(b, m, Tables.Table.get(MarkAt, inner, m), acc, qb, qm))
          )
        )

# the pass over all marks of one branch joins their versions, on that branch
law marks_in_all:
  for hb: Bool
  for inner: Tables.Table<MarkAt>
  for qm: String
  for mv: Maybe<&2, String>
  {
    Marks.in(
      hb,
      Tables.Table.keys(MarkAt, inner),
      inner,
      qm,
      mv
    )
      == Orders.Order.step(
        ~String,
        ~VersionRecord.rev,
        hb,
        MarkAt.version.of(Tables.Table.get(MarkAt, inner, qm)),
        mv
      ): Maybe<&2, String>
  }

def marks_in_all(hb, inner, qm, mv):
  match hb:
    case False{}:
      {==}
    case True{}:
      +inner = inner
      +qm = qm
      Orders.Order.fold_all(
        ~String,
        ~Tables.Table<MarkAt>,
        ~VersionRecord.rev,
        ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
        y => rev_refl(y),
        Tables.Table.keys(MarkAt, inner),
        inner,
        qm,
        mv,
        h => Equal.cong(
          Maybe<&2, MarkAt>,
          Maybe<&2, String>,
          z => MarkAt.version.of(z),
          Tables.Table.get(MarkAt, inner, qm),
          None{},
          Tables.Table.none_of(
            MarkAt,
            Tables.Table.get(MarkAt, inner, qm)
          )(
            Equal.trans(
              Bool,
              Maybe.is_some(&2, MarkAt, Tables.Table.get(MarkAt, inner, qm)),
              Shared.List.has(~String, ~String.eq, Tables.Table.keys(MarkAt, inner), qm),
              False{},
              Equal.sym(
                Bool,
                Shared.List.has(~String, ~String.eq, Tables.Table.keys(MarkAt, inner), qm),
                Maybe.is_some(&2, MarkAt, Tables.Table.get(MarkAt, inner, qm)),
                Tables.Table.keys_get(MarkAt, inner, qm)
              ),
              h
            )
          )
        )
      )

# the pass over one branch b of another node
law marks_branch_find:
  for b: String
  for full: Tables.Table<Tables.Table<MarkAt>>
  for acc: Marked
  for qb: String
  for qm: String
  {
    MarkAt.find(
      Marked.marks(
        Sync.marks.of(b, Tables.Table.keys(MarkAt, Marks.of(full, b)), Marks.of(full, b), acc)
      ),
      qb,
      qm
    )
      == Orders.Order.step(
        ~String,
        ~VersionRecord.rev,
        String.eq(b, qb),
        MarkAt.find(full, b, qm),
        MarkAt.find(Marked.marks(acc), qb, qm)
      ): Maybe<&2, String>
  }

def marks_branch_find(b, full, acc, qb, qm):
  +b = b
  +full = full
  +acc = acc
  +qb = qb
  +qm = qm
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      Marked.marks(
        Sync.marks.of(b, Tables.Table.keys(MarkAt, Marks.of(full, b)), Marks.of(full, b), acc)
      ),
      qb,
      qm
    ),
    Marks.in(
      String.eq(b, qb),
      Tables.Table.keys(MarkAt, Marks.of(full, b)),
      Marks.of(full, b),
      qm,
      MarkAt.find(Marked.marks(acc), qb, qm)
    ),
    Orders.Order.step(
      ~String,
      ~VersionRecord.rev,
      String.eq(b, qb),
      MarkAt.find(full, b, qm),
      MarkAt.find(Marked.marks(acc), qb, qm)
    ),
    marks_in_find(
      String.eq(b, qb),
      Tables.Table.keys(MarkAt, Marks.of(full, b)),
      b,
      Marks.of(full, b),
      acc,
      qb,
      qm
    )({==}),
    marks_in_all(String.eq(b, qb), Marks.of(full, b), qm, MarkAt.find(Marked.marks(acc), qb, qm))
  )

# a sync's mark pass, as a fold over the branches of another node
law marks_fold_find:
  for bks: List<&2, String>
  for full: Tables.Table<Tables.Table<MarkAt>>
  for acc: Marked
  for qb: String
  for qm: String
  {
    MarkAt.find(
      Marked.marks(Sync.marks(bks, full, acc)),
      qb,
      qm
    )
      == Orders.Order.fold(
        ~String,
        ~(+Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>),
        ~VersionRecord.rev,
        ~Marks.at,
        bks,
        (full, qm),
        qb,
        MarkAt.find(Marked.marks(acc), qb, qm)
      ): Maybe<&2, String>
  }

def marks_fold_find(bks, full, acc, qb, qm):
  match bks:
    case Nil{}:
      {==}
    case Con{+b, r}:
      +full = full
      +acc = acc
      +qb = qb
      +qm = qm
      %marks_branch_find(b, full, acc, qb, qm):
        {
          MarkAt.find(
            Marked.marks(
              Sync.marks(
                r,
                full,
                Sync.marks.of(
                  b,
                  Tables.Table.keys(MarkAt, Marks.of(full, b)),
                  Marks.of(full, b),
                  acc
                )
              )
            ),
            qb,
            qm
          )
            == Orders.Order.fold(
              ~String,
              ~(+Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>),
              ~VersionRecord.rev,
              ~Marks.at,
              r,
              (full, qm),
              qb,
              _
            ): Maybe<&2, String>
        }
      marks_fold_find(
        r,
        full,
        Sync.marks.of(b, Tables.Table.keys(MarkAt, Marks.of(full, b)), Marks.of(full, b), acc),
        qb,
        qm
      )

# after a sync's mark pass, a mark has the smaller of the own and the other
# node's versions
law marks_sync_find:
  for full: Tables.Table<Tables.Table<MarkAt>>
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for ns: List<&2, Logged>
  for qb: String
  for qm: String
  {
    MarkAt.find(
      Marked.marks(Sync.marks(Tables.Table.keys(Tables.Table<MarkAt>, full), full, Marked{ms, ns})),
      qb,
      qm
    )
      == Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(ms, qb, qm),
        MarkAt.find(full, qb, qm)
      ): Maybe<&2, String>
  }

def marks_sync_find(full, ms, ns, qb, qm):
  +full = full
  +ms = ms
  +qb = qb
  +qm = qm
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      Marked.marks(Sync.marks(Tables.Table.keys(Tables.Table<MarkAt>, full), full, Marked{ms, ns})),
      qb,
      qm
    ),
    Orders.Order.fold(
      ~String,
      ~(+Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>),
      ~VersionRecord.rev,
      ~Marks.at,
      Tables.Table.keys(Tables.Table<MarkAt>, full),
      (full, qm),
      qb,
      MarkAt.find(ms, qb, qm)
    ),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      MarkAt.find(ms, qb, qm),
      MarkAt.find(full, qb, qm)
    ),
    marks_fold_find(Tables.Table.keys(Tables.Table<MarkAt>, full), full, Marked{ms, ns}, qb, qm),
    Orders.Order.fold_all(
      ~String,
      ~(+Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>),
      ~VersionRecord.rev,
      ~Marks.at,
      y => rev_refl(y),
      Tables.Table.keys(Tables.Table<MarkAt>, full),
      (full, qm),
      qb,
      MarkAt.find(ms, qb, qm),
      h => Equal.cong(
        Maybe<&2, Tables.Table<MarkAt>>,
        Maybe<&2, String>,
        z => MarkAt.version.of(
          Tables.Table.get(
            MarkAt,
            Maybe.default(&2, Tables.Table<MarkAt>, z, Tables.Table.new(MarkAt)),
            qm
          )
        ),
        Tables.Table.get(Tables.Table<MarkAt>, full, qb),
        None{},
        Tables.Table.none_of(
          Tables.Table<MarkAt>,
          Tables.Table.get(Tables.Table<MarkAt>, full, qb)
        )(
          Equal.trans(
            Bool,
            Maybe.is_some(
              &2,
              Tables.Table<MarkAt>,
              Tables.Table.get(Tables.Table<MarkAt>, full, qb)
            ),
            Shared.List.has(~String, ~String.eq, Tables.Table.keys(Tables.Table<MarkAt>, full), qb),
            False{},
            Equal.sym(
              Bool,
              Shared.List.has(
                ~String,
                ~String.eq,
                Tables.Table.keys(Tables.Table<MarkAt>, full),
                qb
              ),
              Maybe.is_some(
                &2,
                Tables.Table<MarkAt>,
                Tables.Table.get(Tables.Table<MarkAt>, full, qb)
              ),
              Tables.Table.keys_get(Tables.Table<MarkAt>, full, qb)
            ),
            h
          )
        )
      )
    )
  )

# the marks after a change are the change's
law marks_after_applied:
  for s: NodeState
  for r: String
  for out: Out
  {
    NodeState.marks(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, out))
    )
      == Out.marks(out): Tables.Table<Tables.Table<MarkAt>>
  }

def marks_after_applied(s, r, out):
  match s out:
    case NodeState{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# after a takes in b's mark, and b takes in that, both hold the same version
law mk_conv:
  for ma: Maybe<&2, String>
  for mb: Maybe<&2, String>
  {
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      ma,
      mb
    )
      == Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        mb,
        Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)
      ): Maybe<&2, String>
  }

def mk_conv(ma, mb):
  +ma = ma
  +mb = mb
  Equal.trans(
    Maybe<&2, String>,
    Orders.Order.join(~String, ~VersionRecord.rev, ma, mb),
    Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      mb,
      Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)
    ),
    Equal.sym(
      Maybe<&2, String>,
      Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)),
      Orders.Order.join(~String, ~VersionRecord.rev, ma, mb),
      Maybes.Maybe.map_id(String, Orders.Order.join(~String, ~VersionRecord.rev, ma, mb))
    ),
    Equal.trans(
      Maybe<&2, String>,
      Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)),
      Maybe.map(
        &2,
        String,
        String,
        y => y,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          mb,
          Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)
        )
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        mb,
        Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)
      ),
      Orders.Order.join_conv(
        ~String,
        ~String,
        ~VersionRecord.rev,
        ~(y => y),
        y => rev_refl(y),
        a => b => rev_swap(a, b),
        a => b => rev_same(a, b),
        ma,
        mb
      ),
      Maybes.Maybe.map_id(
        String,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          mb,
          Orders.Order.join(~String, ~VersionRecord.rev, ma, mb)
        )
      )
    )
  )

# versions that agree on a resource at each key agree at any version m
law find_any:
  for m: Maybe<&2, String>
  for v1: Tables.Table<VersionRecord>
  for v2: Tables.Table<VersionRecord>
  for n: String
  (
    @k: String -> {
      Blob.find.of(
        VersionRecord.blobs.of(Tables.Table.get(VersionRecord, v1, k)),
        n
      )
        == Blob.find.of(
          VersionRecord.blobs.of(Tables.Table.get(VersionRecord, v2, k)),
          n
        ): Maybe<&2, List<&2, U32>>
    }
  ) -> {
    Blob.find.of(
      VersionRecord.blobs.of(VersionRecord.find.of(v1, m)),
      n
    )
      == Blob.find.of(
        VersionRecord.blobs.of(VersionRecord.find.of(v2, m)),
        n
      ): Maybe<&2, List<&2, U32>>
  }

def find_any(m, v1, v2, n):
  match m:
    case None{}:
      vv => {==}
    case Some{k}:
      vv => vv(k)

# states whose versions, heads and marks agree hold the same content
law content_eq:
  for s1: NodeState
  for s2: NodeState
  for n: String
  for p: Spec.Point
  (
    @k: String -> {
      Blob.find.of(
        VersionRecord.blobs.of(Tables.Table.get(VersionRecord, NodeState.versions(s1), k)),
        n
      )
        == Blob.find.of(
          VersionRecord.blobs.of(Tables.Table.get(VersionRecord, NodeState.versions(s2), k)),
          n
        ): Maybe<&2, List<&2, U32>>
    }
  ) -> (
    @c: String -> {
      BranchRecord.head.of(
        Tables.Table.get(BranchRecord, NodeState.branches(s1), c)
      )
        == BranchRecord.head.of(
          Tables.Table.get(BranchRecord, NodeState.branches(s2), c)
        ): Maybe<&2, String>
    }
  ) -> (
    @b: String -> @m: String -> {
      MarkAt.find(
        NodeState.marks(s1),
        b,
        m
      )
        == MarkAt.find(NodeState.marks(s2), b, m): Maybe<&2, String>
    }
  ) -> {NodeState.content(s1, n, p) == NodeState.content(s2, n, p): Maybe<&2, List<&2, U32>>}

def content_eq(s1, s2, n, p):
  match p:
    case Spec.Point.At{v}:
      vv => hh => mm => vv(v)
    case Spec.Point.Head{+b}:
      vv => hh => mm =>
        +s1 = s1
        +s2 = s2
        +n = n
        %hh(
          b
        ): {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(
                NodeState.versions(s1),
                BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s1), b))
              )
            ),
            n
          )
            == Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s2), _)),
              n
            ): Maybe<&2, List<&2, U32>>
        }
        find_any(
          BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s1), b)),
          NodeState.versions(s1),
          NodeState.versions(s2),
          n
        )(vv)
    case Spec.Point.Mark{+b, +m}:
      vv => hh => mm =>
        +s1 = s1
        +s2 = s2
        +n = n
        %mm(
          b
        )(
          m
        ): {
          Blob.find.of(
            VersionRecord.blobs.of(
              VersionRecord.find.of(NodeState.versions(s1), MarkAt.find(NodeState.marks(s1), b, m))
            ),
            n
          )
            == Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s2), _)),
              n
            ): Maybe<&2, List<&2, U32>>
        }
        find_any(
          MarkAt.find(NodeState.marks(s1), b, m),
          NodeState.versions(s1),
          NodeState.versions(s2),
          n
        )(vv)

# after a sync, a version is the own one when held, else the other node's
law after_v:
  for s: NodeState
  for o: NodeState
  for r: String
  for k: String
  {
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      k
    )
      == Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, NodeState.versions(s), k),
        Tables.Table.get(VersionRecord, NodeState.versions(o), k)
      ): Maybe<&2, VersionRecord>
  }

def after_v(s, o, r, k):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, VersionRecord>,
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      k
    ),
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add(
        Tables.Table.rows(
          VersionRecord,
          Tables.Table.keys(VersionRecord, NodeState.versions(o)),
          NodeState.versions(o)
        ),
        NodeState.versions(s)
      ),
      k
    ),
    Maybe.or(
      &2,
      VersionRecord,
      Tables.Table.get(VersionRecord, NodeState.versions(s), k),
      Tables.Table.get(VersionRecord, NodeState.versions(o), k)
    ),
    Equal.cong(
      Tables.Table<VersionRecord>,
      Maybe<&2, VersionRecord>,
      z => Tables.Table.get(VersionRecord, z, k),
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      VersionRecord.add(
        Tables.Table.rows(
          VersionRecord,
          Tables.Table.keys(VersionRecord, NodeState.versions(o)),
          NodeState.versions(o)
        ),
        NodeState.versions(s)
      ),
      versions_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    sync_find(NodeState.versions(o), NodeState.versions(s), k)
  )

# after a sync, a branch is the winner of the own and the other node's
law after_b:
  for s: NodeState
  for o: NodeState
  for r: String
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      c
    )
      == Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Tables.Table.get(BranchRecord, NodeState.branches(s), c),
        Tables.Table.get(BranchRecord, NodeState.branches(o), c)
      ): Maybe<&2, BranchRecord>
  }

def after_b(s, o, r, c):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, BranchRecord>,
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      c
    ),
    Tables.Table.get(
      BranchRecord,
      Mix.branches(
        Sync.branches(
          Tables.Table.keys(BranchRecord, NodeState.branches(o)),
          NodeState.branches(o),
          VersionRecord.add(
            Tables.Table.rows(
              VersionRecord,
              Tables.Table.keys(VersionRecord, NodeState.versions(o)),
              NodeState.versions(o)
            ),
            NodeState.versions(s)
          ),
          Mix{NodeState.branches(s), NodeState.clashes(s), []}
        )
      ),
      c
    ),
    Orders.Order.join(
      ~BranchRecord,
      ~BranchRecord.stamp.cmp,
      Tables.Table.get(BranchRecord, NodeState.branches(s), c),
      Tables.Table.get(BranchRecord, NodeState.branches(o), c)
    ),
    Equal.cong(
      Tables.Table<BranchRecord>,
      Maybe<&2, BranchRecord>,
      z => Tables.Table.get(BranchRecord, z, c),
      NodeState.branches(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      Mix.branches(
        Sync.branches(
          Tables.Table.keys(BranchRecord, NodeState.branches(o)),
          NodeState.branches(o),
          VersionRecord.add(
            Tables.Table.rows(
              VersionRecord,
              Tables.Table.keys(VersionRecord, NodeState.versions(o)),
              NodeState.versions(o)
            ),
            NodeState.versions(s)
          ),
          Mix{NodeState.branches(s), NodeState.clashes(s), []}
        )
      ),
      branches_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    sync_branches_find(
      NodeState.branches(o),
      VersionRecord.add(
        Tables.Table.rows(
          VersionRecord,
          Tables.Table.keys(VersionRecord, NodeState.versions(o)),
          NodeState.versions(o)
        ),
        NodeState.versions(s)
      ),
      Mix{NodeState.branches(s), NodeState.clashes(s), []},
      c
    )
  )

# after a sync, a mark has the smaller of the own and the other node's versions
law after_m:
  for s: NodeState
  for o: NodeState
  for r: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      qb,
      qm
    )
      == Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(NodeState.marks(s), qb, qm),
        MarkAt.find(NodeState.marks(o), qb, qm)
      ): Maybe<&2, String>
  }

def after_m(s, o, r, qb, qm):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      qb,
      qm
    ),
    MarkAt.find(
      Marked.marks(
        Sync.marks(
          Tables.Table.keys(Tables.Table<MarkAt>, NodeState.marks(o)),
          NodeState.marks(o),
          Marked{NodeState.marks(s), []}
        )
      ),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      MarkAt.find(NodeState.marks(s), qb, qm),
      MarkAt.find(NodeState.marks(o), qb, qm)
    ),
    Equal.cong(
      Tables.Table<Tables.Table<MarkAt>>,
      Maybe<&2, String>,
      z => MarkAt.find(z, qb, qm),
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      Marked.marks(
        Sync.marks(
          Tables.Table.keys(Tables.Table<MarkAt>, NodeState.marks(o)),
          NodeState.marks(o),
          Marked{NodeState.marks(s), []}
        )
      ),
      marks_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    marks_sync_find(NodeState.marks(o), NodeState.marks(s), [], qb, qm)
  )

# a takes in b, then b takes in that: a resource of a version agrees
law conv_v:
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for n: String
  for k: String
  {
    Sync.collides(
      Tables.Table.keys(VersionRecord, NodeState.versions(b)),
      NodeState.versions(b),
      NodeState.versions(a)
    )
      == False{}: Bool
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
          ),
          k
        )
      ),
      n
    )
      == Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(a, r1, Sync.go(False{}, a, b))
                    )
                  )
                )
              )
            ),
            k
          )
        ),
        n
      ): Maybe<&2, List<&2, U32>>
  }

def conv_v(a, b, r1, r2, n, k):
  +hc =>
    +a = a
    +b = b
    +r1 = r1
    +r2 = r2
    +n = n
    +k = k
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
            ),
            k
          )
        ),
        n
      ),
      Blob.find.of(
        VersionRecord.blobs.of(
          Maybe.or(
            &2,
            VersionRecord,
            Tables.Table.get(VersionRecord, NodeState.versions(a), k),
            Tables.Table.get(VersionRecord, NodeState.versions(b), k)
          )
        ),
        n
      ),
      Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(a, r1, Sync.go(False{}, a, b))
                    )
                  )
                )
              )
            ),
            k
          )
        ),
        n
      ),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Maybe<&2, List<&2, U32>>,
        z => Blob.find.of(VersionRecord.blobs.of(z), n),
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
          ),
          k
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, NodeState.versions(a), k),
          Tables.Table.get(VersionRecord, NodeState.versions(b), k)
        ),
        after_v(a, b, r1, k)
      ),
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Blob.find.of(
          VersionRecord.blobs.of(
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, NodeState.versions(a), k),
              Tables.Table.get(VersionRecord, NodeState.versions(b), k)
            )
          ),
          n
        ),
        Blob.find.of(
          VersionRecord.blobs.of(
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, NodeState.versions(b), k),
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(a), k),
                Tables.Table.get(VersionRecord, NodeState.versions(b), k)
              )
            )
          ),
          n
        ),
        Blob.find.of(
          VersionRecord.blobs.of(
            Tables.Table.get(
              VersionRecord,
              NodeState.versions(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(a, r1, Sync.go(False{}, a, b))
                      )
                    )
                  )
                )
              ),
              k
            )
          ),
          n
        ),
        vb_conv(
          Tables.Table.get(VersionRecord, NodeState.versions(a), k),
          Tables.Table.get(VersionRecord, NodeState.versions(b), k),
          n
        )(compat_of(NodeState.versions(b), NodeState.versions(a), k)(hc)),
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Blob.find.of(
            VersionRecord.blobs.of(
              Tables.Table.get(
                VersionRecord,
                NodeState.versions(
                  Pair.fst(
                    NodeState,
                    Spec.Answer,
                    VendNode.applied(
                      b,
                      r2,
                      Sync.go(
                        False{},
                        b,
                        Pair.fst(
                          NodeState,
                          Spec.Answer,
                          VendNode.applied(a, r1, Sync.go(False{}, a, b))
                        )
                      )
                    )
                  )
                ),
                k
              )
            ),
            n
          ),
          Blob.find.of(
            VersionRecord.blobs.of(
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(b), k),
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(a), k),
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k)
                )
              )
            ),
            n
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(
              VersionRecord.blobs.of(
                Tables.Table.get(
                  VersionRecord,
                  NodeState.versions(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(
                        b,
                        r2,
                        Sync.go(
                          False{},
                          b,
                          Pair.fst(
                            NodeState,
                            Spec.Answer,
                            VendNode.applied(a, r1, Sync.go(False{}, a, b))
                          )
                        )
                      )
                    )
                  ),
                  k
                )
              ),
              n
            ),
            Blob.find.of(
              VersionRecord.blobs.of(
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k),
                  Tables.Table.get(
                    VersionRecord,
                    NodeState.versions(
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(a, r1, Sync.go(False{}, a, b))
                      )
                    ),
                    k
                  )
                )
              ),
              n
            ),
            Blob.find.of(
              VersionRecord.blobs.of(
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k),
                  Maybe.or(
                    &2,
                    VersionRecord,
                    Tables.Table.get(VersionRecord, NodeState.versions(a), k),
                    Tables.Table.get(VersionRecord, NodeState.versions(b), k)
                  )
                )
              ),
              n
            ),
            Equal.cong(
              Maybe<&2, VersionRecord>,
              Maybe<&2, List<&2, U32>>,
              z => Blob.find.of(VersionRecord.blobs.of(z), n),
              Tables.Table.get(
                VersionRecord,
                NodeState.versions(
                  Pair.fst(
                    NodeState,
                    Spec.Answer,
                    VendNode.applied(
                      b,
                      r2,
                      Sync.go(
                        False{},
                        b,
                        Pair.fst(
                          NodeState,
                          Spec.Answer,
                          VendNode.applied(a, r1, Sync.go(False{}, a, b))
                        )
                      )
                    )
                  )
                ),
                k
              ),
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(b), k),
                Tables.Table.get(
                  VersionRecord,
                  NodeState.versions(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(a, r1, Sync.go(False{}, a, b))
                    )
                  ),
                  k
                )
              ),
              after_v(
                b,
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
                r2,
                k
              )
            ),
            Equal.cong(
              Maybe<&2, VersionRecord>,
              Maybe<&2, List<&2, U32>>,
              z => Blob.find.of(
                VersionRecord.blobs.of(
                  Maybe.or(
                    &2,
                    VersionRecord,
                    Tables.Table.get(VersionRecord, NodeState.versions(b), k),
                    z
                  )
                ),
                n
              ),
              Tables.Table.get(
                VersionRecord,
                NodeState.versions(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                ),
                k
              ),
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(a), k),
                Tables.Table.get(VersionRecord, NodeState.versions(b), k)
              ),
              after_v(a, b, r1, k)
            )
          )
        )
      )
    )

# a takes in b, then b takes in that: a branch head agrees
law conv_h:
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for c: String
  {
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        ),
        c
      )
    )
      == BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          c
        )
      ): Maybe<&2, String>
  }

def conv_h(a, b, r1, r2, c):
  +a = a
  +b = b
  +r1 = r1
  +c = c
  Equal.trans(
    Maybe<&2, String>,
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        ),
        c
      )
    ),
    BranchRecord.head.of(
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Tables.Table.get(BranchRecord, NodeState.branches(a), c),
        Tables.Table.get(BranchRecord, NodeState.branches(b), c)
      )
    ),
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              )
            )
          )
        ),
        c
      )
    ),
    Equal.cong(
      Maybe<&2, BranchRecord>,
      Maybe<&2, String>,
      z => BranchRecord.head.of(z),
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        ),
        c
      ),
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Tables.Table.get(BranchRecord, NodeState.branches(a), c),
        Tables.Table.get(BranchRecord, NodeState.branches(b), c)
      ),
      after_b(a, b, r1, c)
    ),
    Equal.trans(
      Maybe<&2, String>,
      BranchRecord.head.of(
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(a), c),
          Tables.Table.get(BranchRecord, NodeState.branches(b), c)
        )
      ),
      BranchRecord.head.of(
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(b), c),
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(a), c),
            Tables.Table.get(BranchRecord, NodeState.branches(b), c)
          )
        )
      ),
      BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          c
        )
      ),
      hb_conv(
        Tables.Table.get(BranchRecord, NodeState.branches(a), c),
        Tables.Table.get(BranchRecord, NodeState.branches(b), c)
      ),
      Equal.sym(
        Maybe<&2, String>,
        BranchRecord.head.of(
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(a, r1, Sync.go(False{}, a, b))
                    )
                  )
                )
              )
            ),
            c
          )
        ),
        BranchRecord.head.of(
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(b), c),
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(a), c),
              Tables.Table.get(BranchRecord, NodeState.branches(b), c)
            )
          )
        ),
        Equal.trans(
          Maybe<&2, String>,
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(a, r1, Sync.go(False{}, a, b))
                      )
                    )
                  )
                )
              ),
              c
            )
          ),
          BranchRecord.head.of(
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(b), c),
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                ),
                c
              )
            )
          ),
          BranchRecord.head.of(
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(b), c),
              Orders.Order.join(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                Tables.Table.get(BranchRecord, NodeState.branches(a), c),
                Tables.Table.get(BranchRecord, NodeState.branches(b), c)
              )
            )
          ),
          Equal.cong(
            Maybe<&2, BranchRecord>,
            Maybe<&2, String>,
            z => BranchRecord.head.of(z),
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(a, r1, Sync.go(False{}, a, b))
                      )
                    )
                  )
                )
              ),
              c
            ),
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(b), c),
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                ),
                c
              )
            ),
            after_b(
              b,
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
              r2,
              c
            )
          ),
          Equal.cong(
            Maybe<&2, BranchRecord>,
            Maybe<&2, String>,
            z => BranchRecord.head.of(
              Orders.Order.join(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                Tables.Table.get(BranchRecord, NodeState.branches(b), c),
                z
              )
            ),
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              ),
              c
            ),
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(a), c),
              Tables.Table.get(BranchRecord, NodeState.branches(b), c)
            ),
            after_b(a, b, r1, c)
          )
        )
      )
    )
  )

# a takes in b, then b takes in that: a mark agrees
law conv_m:
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
      ),
      qb,
      qm
    )
      == MarkAt.find(
        NodeState.marks(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              )
            )
          )
        ),
        qb,
        qm
      ): Maybe<&2, String>
  }

def conv_m(a, b, r1, r2, qb, qm):
  +a = a
  +b = b
  +r1 = r1
  +qb = qb
  +qm = qm
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
      ),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      MarkAt.find(NodeState.marks(a), qb, qm),
      MarkAt.find(NodeState.marks(b), qb, qm)
    ),
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            b,
            r2,
            Sync.go(
              False{},
              b,
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
            )
          )
        )
      ),
      qb,
      qm
    ),
    after_m(a, b, r1, qb, qm),
    Equal.trans(
      Maybe<&2, String>,
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(NodeState.marks(a), qb, qm),
        MarkAt.find(NodeState.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(NodeState.marks(b), qb, qm),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(a), qb, qm),
          MarkAt.find(NodeState.marks(b), qb, qm)
        )
      ),
      MarkAt.find(
        NodeState.marks(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              )
            )
          )
        ),
        qb,
        qm
      ),
      mk_conv(MarkAt.find(NodeState.marks(a), qb, qm), MarkAt.find(NodeState.marks(b), qb, qm)),
      Equal.sym(
        Maybe<&2, String>,
        MarkAt.find(
          NodeState.marks(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(b), qb, qm),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(a), qb, qm),
            MarkAt.find(NodeState.marks(b), qb, qm)
          )
        ),
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            NodeState.marks(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(a, r1, Sync.go(False{}, a, b))
                    )
                  )
                )
              )
            ),
            qb,
            qm
          ),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(b), qb, qm),
            MarkAt.find(
              NodeState.marks(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              ),
              qb,
              qm
            )
          ),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(b), qb, qm),
            Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(NodeState.marks(a), qb, qm),
              MarkAt.find(NodeState.marks(b), qb, qm)
            )
          ),
          after_m(
            b,
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
            r2,
            qb,
            qm
          ),
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, String>,
            z => Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(NodeState.marks(b), qb, qm),
              z
            ),
            MarkAt.find(
              NodeState.marks(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
              ),
              qb,
              qm
            ),
            Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(NodeState.marks(a), qb, qm),
              MarkAt.find(NodeState.marks(b), qb, qm)
            ),
            after_m(a, b, r1, qb, qm)
          )
        )
      )
    )
  )

# a takes in b, then b takes in that: both hold the same content
law conv_core:
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  {
    Sync.collides(
      Tables.Table.keys(VersionRecord, NodeState.versions(b)),
      NodeState.versions(b),
      NodeState.versions(a)
    )
      == False{}: Bool
  } -> Spec.VendNode.SameContent(
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(
        b,
        r2,
        Sync.go(
          False{},
          b,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        )
      )
    )
  )

def conv_core(a, b, r1, r2):
  +hc =>
    +a = a
    +b = b
    +r1 = r1
    +r2 = r2
    +n => p => content_eq(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
      Pair.fst(
        NodeState,
        Spec.Answer,
        VendNode.applied(
          b,
          r2,
          Sync.go(
            False{},
            b,
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
          )
        )
      ),
      Resources.Name.show(n),
      p
    )(
      k => conv_v(a, b, r1, r2, Resources.Name.show(n), k)(hc)
    )(c => conv_h(a, b, r1, r2, c))(qb => qm => conv_m(a, b, r1, r2, qb, qm))

# a sync that answers Synced found no collision
law sync_clean:
  for s: NodeState
  for o: NodeState
  for r: String
  for w: String
  for z: String
  for t: NodeState
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Sync{o, None{}}
    )
      == (t, Spec.Answer.Sync{Spec.Sync.Synced{}}): NodeState
      & Spec.Answer
  } -> {
    Sync.collides(
      Tables.Table.keys(VersionRecord, NodeState.versions(o)),
      NodeState.versions(o),
      NodeState.versions(s)
    )
      == False{}: Bool
  }

def sync_clean(s, o, r, w, z, t):
  hn => h =>
    +s = s
    +o = o
    +r = r
    +t = t
    sync_free(
      Sync.collides(
        Tables.Table.keys(VersionRecord, NodeState.versions(o)),
        NodeState.versions(o),
        NodeState.versions(s)
      ),
      s,
      o
    )(
      applied_answer(
        s,
        r,
        Sync.go(
          Sync.collides(
            Tables.Table.keys(VersionRecord, NodeState.versions(o)),
            NodeState.versions(o),
            NodeState.versions(s)
          ),
          s,
          o
        ),
        t,
        Spec.Answer.Sync{Spec.Sync.Synced{}}
      )(
        ask_step(
          s,
          r,
          w,
          z,
          Spec.Ask.Sync{o, None{}},
          t,
          Spec.Answer.Sync{Spec.Sync.Synced{}}
        )(hn)(h)
      )
    )

# a sync that answers Synced leaves the node as it would with no collision
law sync_state:
  for s: NodeState
  for o: NodeState
  for r: String
  for w: String
  for z: String
  for t: NodeState
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Sync{o, None{}}
    )
      == (t, Spec.Answer.Sync{Spec.Sync.Synced{}}): NodeState
      & Spec.Answer
  } -> {
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o))) == t: NodeState
  }

def sync_state(s, o, r, w, z, t):
  +hn => +h =>
    +s = s
    +o = o
    +r = r
    +w = w
    +z = z
    +t = t
    Equal.trans(
      NodeState,
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o))),
      Pair.fst(
        NodeState,
        Spec.Answer,
        VendNode.applied(
          s,
          r,
          Sync.go(
            Sync.collides(
              Tables.Table.keys(VersionRecord, NodeState.versions(o)),
              NodeState.versions(o),
              NodeState.versions(s)
            ),
            s,
            o
          )
        )
      ),
      t,
      Equal.cong(
        Bool,
        NodeState,
        x => Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(x, s, o))),
        False{},
        Sync.collides(
          Tables.Table.keys(VersionRecord, NodeState.versions(o)),
          NodeState.versions(o),
          NodeState.versions(s)
        ),
        Equal.sym(
          Bool,
          Sync.collides(
            Tables.Table.keys(VersionRecord, NodeState.versions(o)),
            NodeState.versions(o),
            NodeState.versions(s)
          ),
          False{},
          sync_clean(s, o, r, w, z, t)(hn)(h)
        )
      ),
      applied_state(
        s,
        r,
        Sync.go(
          Sync.collides(
            Tables.Table.keys(VersionRecord, NodeState.versions(o)),
            NodeState.versions(o),
            NodeState.versions(s)
          ),
          s,
          o
        ),
        t,
        Spec.Answer.Sync{Spec.Sync.Synced{}}
      )(
        ask_step(
          s,
          r,
          w,
          z,
          Spec.Ask.Sync{o, None{}},
          t,
          Spec.Answer.Sync{Spec.Sync.Synced{}}
        )(hn)(h)
      )
    )

# s takes in a twice: a version is as after once
law idem_v:
  for s: NodeState
  for a: NodeState
  for r1: String
  for r2: String
  for k: String
  {
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      k
    )
      == Tables.Table.get(
        VersionRecord,
        NodeState.versions(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        k
      ): Maybe<&2, VersionRecord>
  }

def idem_v(s, a, r1, r2, k):
  +s = s
  +a = a
  +r1 = r1
  +k = k
  Equal.trans(
    Maybe<&2, VersionRecord>,
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      k
    ),
    Maybe.or(
      &2,
      VersionRecord,
      Tables.Table.get(
        VersionRecord,
        NodeState.versions(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        k
      ),
      Tables.Table.get(VersionRecord, NodeState.versions(a), k)
    ),
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
      ),
      k
    ),
    after_v(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
      a,
      r2,
      k
    ),
    Equal.trans(
      Maybe<&2, VersionRecord>,
      Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          k
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(a), k)
      ),
      Maybe.or(
        &2,
        VersionRecord,
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(a), k)
      ),
      Tables.Table.get(
        VersionRecord,
        NodeState.versions(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        k
      ),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Maybe<&2, VersionRecord>,
        z => Maybe.or(
          &2,
          VersionRecord,
          z,
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          k
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        after_v(s, a, r1, k)
      ),
      Equal.trans(
        Maybe<&2, VersionRecord>,
        Maybe.or(
          &2,
          VersionRecord,
          Maybe.or(
            &2,
            VersionRecord,
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            Tables.Table.get(VersionRecord, NodeState.versions(a), k)
          ),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          k
        ),
        Maybes.Maybe.or_idem(
          VersionRecord,
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k)
        ),
        Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
            ),
            k
          ),
          Maybe.or(
            &2,
            VersionRecord,
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            Tables.Table.get(VersionRecord, NodeState.versions(a), k)
          ),
          after_v(s, a, r1, k)
        )
      )
    )
  )

# s takes in a twice: a branch is as after once
law idem_b:
  for s: NodeState
  for a: NodeState
  for r1: String
  for r2: String
  for c: String
  {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      c
    )
      == Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        c
      ): Maybe<&2, BranchRecord>
  }

def idem_b(s, a, r1, r2, c):
  +s = s
  +a = a
  +r1 = r1
  +c = c
  Equal.trans(
    Maybe<&2, BranchRecord>,
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      c
    ),
    Orders.Order.join(
      ~BranchRecord,
      ~BranchRecord.stamp.cmp,
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        c
      ),
      Tables.Table.get(BranchRecord, NodeState.branches(a), c)
    ),
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
      ),
      c
    ),
    after_b(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
      a,
      r2,
      c
    ),
    Equal.trans(
      Maybe<&2, BranchRecord>,
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          c
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(a), c)
      ),
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(a), c)
      ),
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        c
      ),
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Maybe<&2, BranchRecord>,
        z => Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          z,
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          c
        ),
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        after_b(s, a, r1, c)
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          c
        ),
        Orders.Order.join_idem(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          y => stamp_refl(y),
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Equal.sym(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
            ),
            c
          ),
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          after_b(s, a, r1, c)
        )
      )
    )
  )

# s takes in a twice: a mark is as after once
law idem_m:
  for s: NodeState
  for a: NodeState
  for r1: String
  for r2: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      qb,
      qm
    )
      == MarkAt.find(
        NodeState.marks(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        qb,
        qm
      ): Maybe<&2, String>
  }

def idem_m(s, a, r1, r2, qb, qm):
  +s = s
  +a = a
  +r1 = r1
  +qb = qb
  +qm = qm
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      MarkAt.find(
        NodeState.marks(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        qb,
        qm
      ),
      MarkAt.find(NodeState.marks(a), qb, qm)
    ),
    MarkAt.find(
      NodeState.marks(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
      ),
      qb,
      qm
    ),
    after_m(
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
      a,
      r2,
      qb,
      qm
    ),
    Equal.trans(
      Maybe<&2, String>,
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(
          NodeState.marks(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          qb,
          qm
        ),
        MarkAt.find(NodeState.marks(a), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        MarkAt.find(NodeState.marks(a), qb, qm)
      ),
      MarkAt.find(
        NodeState.marks(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        qb,
        qm
      ),
      Equal.cong(
        Maybe<&2, String>,
        Maybe<&2, String>,
        z => Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          z,
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        MarkAt.find(
          NodeState.marks(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        after_m(s, a, r1, qb, qm)
      ),
      Equal.trans(
        Maybe<&2, String>,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(s), qb, qm),
            MarkAt.find(NodeState.marks(a), qb, qm)
          ),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        MarkAt.find(
          NodeState.marks(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          qb,
          qm
        ),
        Orders.Order.join_idem(
          ~String,
          ~VersionRecord.rev,
          y => rev_refl(y),
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        Equal.sym(
          Maybe<&2, String>,
          MarkAt.find(
            NodeState.marks(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
            ),
            qb,
            qm
          ),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(s), qb, qm),
            MarkAt.find(NodeState.marks(a), qb, qm)
          ),
          after_m(s, a, r1, qb, qm)
        )
      )
    )
  )

# s takes in a twice: the content is as after once
law idem_core:
  for s: NodeState
  for a: NodeState
  for r1: String
  for r2: String
  Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(
          False{},
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
          a
        )
      )
    ),
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
  )

def idem_core(s, a, r1, r2):
  +s = s
  +a = a
  +r1 = r1
  +r2 = r2
  +n => p => content_eq(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(
          False{},
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
          a
        )
      )
    ),
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
    Resources.Name.show(n),
    p
  )(
    k => Equal.cong(
      Maybe<&2, VersionRecord>,
      Maybe<&2, List<&2, U32>>,
      z => Blob.find.of(VersionRecord.blobs.of(z), Resources.Name.show(n)),
      Tables.Table.get(
        VersionRecord,
        NodeState.versions(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                a
              )
            )
          )
        ),
        k
      ),
      Tables.Table.get(
        VersionRecord,
        NodeState.versions(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        k
      ),
      idem_v(s, a, r1, r2, k)
    )
  )(
    c => Equal.cong(
      Maybe<&2, BranchRecord>,
      Maybe<&2, String>,
      z => BranchRecord.head.of(z),
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                a
              )
            )
          )
        ),
        c
      ),
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
        ),
        c
      ),
      idem_b(s, a, r1, r2, c)
    )
  )(qb => qm => idem_m(s, a, r1, r2, qb, qm))

# a second sync with a, by whether it found a collision (c)
law idem_go:
  for c: Bool
  for s: NodeState
  for a: NodeState
  for r1: String
  for s1: NodeState
  for r2: String
  {
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r1, Sync.go(False{}, s, a))
    )
      == s1: NodeState
  } -> Spec.VendNode.SameContent(
    Pair.fst(NodeState, Spec.Answer, VendNode.applied(s1, r2, Sync.go(c, s1, a))),
    s1
  )

def idem_go(c, s, a, r1, s1, r2):
  match c:
    case True{}:
      e =>
        +s1 = s1
        +r2 = r2
        n => p => same_content_out(
          s1,
          r2,
          NodeState.clashes(s1),
          [],
          Sync.answer(Spec.Sync.Refused{"version ID collision"}),
          Resources.Name.show(n),
          p
        )
    case False{}:
      e =>
        +s = s
        +a = a
        +r1 = r1
        +r2 = r2
        %e: Spec.VendNode.SameContent(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(_, r2, Sync.go(False{}, _, a))),
          _
        )
        idem_core(s, a, r1, r2)

# a second sync with a, by whether its request was seen (found)
law idem_ask:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for a: NodeState
  for r1: String
  for s1: NodeState
  for r2: String
  for w2: String
  for z2: String
  for s2: NodeState
  for a2: Spec.Answer
  {
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(s, r1, Sync.go(False{}, s, a))
    )
      == s1: NodeState
  } -> {
    VendNode.asked(
      found,
      s1,
      r2,
      w2,
      z2,
      Spec.Ask.Sync{a, None{}}
    )
      == (s2, a2): NodeState
      & Spec.Answer
  } -> Spec.VendNode.SameContent(s2, s1)

def idem_ask(found, s, a, r1, s1, r2, w2, z2, s2, a2):
  match found:
    case Some{Seen{b, q}}:
      e => h =>
        +s1 = s1
        %Equal.cong(
          NodeState & Spec.Answer,
          NodeState,
          x => Pair.fst(NodeState, Spec.Answer, x),
          (s1, b),
          (s2, a2),
          h
        ): Spec.VendNode.SameContent(_, s1)
        n => p => {==}
    case None{}:
      e => h =>
        +s1 = s1
        +r2 = r2
        +a = a
        %applied_state(
          s1,
          r2,
          Step.of(s1, r2, w2, z2, Spec.Ask.Sync{a, None{}}),
          s2,
          a2
        )(h): Spec.VendNode.SameContent(_, s1)
        idem_go(
          Sync.collides(
            Tables.Table.keys(VersionRecord, NodeState.versions(a)),
            NodeState.versions(a),
            NodeState.versions(s1)
          ),
          s,
          a,
          r1,
          s1,
          r2
        )(e)

# the stamps of three branches chain
law stamp_chain:
  for x: BranchRecord
  for y: BranchRecord
  for z: BranchRecord
  {
    Cmps.Cmp.chain(
      BranchRecord.stamp.cmp(x, y),
      BranchRecord.stamp.cmp(y, z),
      BranchRecord.stamp.cmp(x, z)
    )
      == True{}: Bool
  }

def stamp_chain(x, y, z):
  match x y z:
    case BranchRecord{
      +h1,
      o1,
      +e1,
      +c1
    } BranchRecord{+h2, o2, +e2, +c2} BranchRecord{+h3, o3, +e3, +c3}:
      Cmps.Cmp.then_chain(
        Nat.cmp(e1, e2),
        Nat.cmp(e2, e3),
        Nat.cmp(e1, e3),
        Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)),
        Cmps.Cmp.then(Nat.cmp(c2, c3), String.order(h2, h3)),
        Cmps.Cmp.then(Nat.cmp(c1, c3), String.order(h1, h3))
      )(
        Nats.Nat.cmp_chain(e1, e2, e3)
      )(
        Cmps.Cmp.then_chain(
          Nat.cmp(c1, c2),
          Nat.cmp(c2, c3),
          Nat.cmp(c1, c3),
          String.order(h1, h2),
          String.order(h2, h3),
          String.order(h1, h3)
        )(Nats.Nat.cmp_chain(c1, c2, c3))(Strings.String.order_chain(h1, h2, h3))
      )

# the version order of marks chains
law rev_chain:
  for a: String
  for b: String
  for c: String
  {
    Cmps.Cmp.chain(
      VersionRecord.rev(a, b),
      VersionRecord.rev(b, c),
      VersionRecord.rev(a, c)
    )
      == True{}: Bool
  }

def rev_chain(a, b, c):
  +a = a
  +b = b
  +c = c
  Equal.trans(
    Bool,
    Cmps.Cmp.chain(String.order(b, a), String.order(c, b), String.order(c, a)),
    Cmps.Cmp.chain(String.order(c, b), String.order(b, a), String.order(c, a)),
    True{},
    Equal.sym(
      Bool,
      Cmps.Cmp.chain(String.order(c, b), String.order(b, a), String.order(c, a)),
      Cmps.Cmp.chain(String.order(b, a), String.order(c, b), String.order(c, a)),
      Cmps.Cmp.chain_swap(String.order(b, a), String.order(c, b), String.order(c, a))
    ),
    Strings.String.order_chain(c, b, a)
  )

# taking in vb then va holds the same bytes as va then vb, when vb agrees with
# what was held before it
law comm_blob:
  for vs: Maybe<&2, VersionRecord>
  for va: Maybe<&2, VersionRecord>
  for vb: Maybe<&2, VersionRecord>
  for n: String
  Compat(
    vb,
    Maybe.or(&2, VersionRecord, vs, va)
  ) -> {
    Blob.find.of(
      VersionRecord.blobs.of(Maybe.or(&2, VersionRecord, Maybe.or(&2, VersionRecord, vs, va), vb)),
      n
    )
      == Blob.find.of(
        VersionRecord.blobs.of(
          Maybe.or(&2, VersionRecord, Maybe.or(&2, VersionRecord, vs, vb), va)
        ),
        n
      ): Maybe<&2, List<&2, U32>>
  }

def comm_blob(vs, va, vb, n):
  match vs va vb:
    case None{} None{} None{}:
      h => {==}
    case None{} None{} Some{w}:
      h => {==}
    case None{} Some{v} None{}:
      h => {==}
    case None{} Some{v} Some{w}:
      h => h(n)
    case Some{u} y z:
      h => {==}

# s takes in a then b, or b then a: a version agrees
law comm_v:
  for s: NodeState
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for n: String
  for k: String
  {
    Sync.collides(
      Tables.Table.keys(VersionRecord, NodeState.versions(b)),
      NodeState.versions(b),
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
      )
    )
      == False{}: Bool
  } -> {
    Blob.find.of(
      VersionRecord.blobs.of(
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                  b
                )
              )
            )
          ),
          k
        )
      ),
      n
    )
      == Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    a
                  )
                )
              )
            ),
            k
          )
        ),
        n
      ): Maybe<&2, List<&2, U32>>
  }

def comm_v(s, a, b, r1, r2, r3, r4, n, k):
  +hc =>
    +s = s
    +a = a
    +b = b
    +r1 = r1
    +r2 = r2
    +r3 = r3
    +r4 = r4
    +n = n
    +k = k
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                  r2,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r1, Sync.go(False{}, s, a))
                    ),
                    b
                  )
                )
              )
            ),
            k
          )
        ),
        n
      ),
      Blob.find.of(
        VersionRecord.blobs.of(
          Maybe.or(
            &2,
            VersionRecord,
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, NodeState.versions(s), k),
              Tables.Table.get(VersionRecord, NodeState.versions(a), k)
            ),
            Tables.Table.get(VersionRecord, NodeState.versions(b), k)
          )
        ),
        n
      ),
      Blob.find.of(
        VersionRecord.blobs.of(
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    a
                  )
                )
              )
            ),
            k
          )
        ),
        n
      ),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Maybe<&2, List<&2, U32>>,
        z => Blob.find.of(VersionRecord.blobs.of(z), n),
        Tables.Table.get(
          VersionRecord,
          NodeState.versions(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                  b
                )
              )
            )
          ),
          k
        ),
        Maybe.or(
          &2,
          VersionRecord,
          Maybe.or(
            &2,
            VersionRecord,
            Tables.Table.get(VersionRecord, NodeState.versions(s), k),
            Tables.Table.get(VersionRecord, NodeState.versions(a), k)
          ),
          Tables.Table.get(VersionRecord, NodeState.versions(b), k)
        ),
        Equal.trans(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(
            VersionRecord,
            NodeState.versions(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                  r2,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r1, Sync.go(False{}, s, a))
                    ),
                    b
                  )
                )
              )
            ),
            k
          ),
          Maybe.or(
            &2,
            VersionRecord,
            Tables.Table.get(
              VersionRecord,
              NodeState.versions(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
              ),
              k
            ),
            Tables.Table.get(VersionRecord, NodeState.versions(b), k)
          ),
          Maybe.or(
            &2,
            VersionRecord,
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, NodeState.versions(s), k),
              Tables.Table.get(VersionRecord, NodeState.versions(a), k)
            ),
            Tables.Table.get(VersionRecord, NodeState.versions(b), k)
          ),
          after_v(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            b,
            r2,
            k
          ),
          Equal.cong(
            Maybe<&2, VersionRecord>,
            Maybe<&2, VersionRecord>,
            z => Maybe.or(
              &2,
              VersionRecord,
              z,
              Tables.Table.get(VersionRecord, NodeState.versions(b), k)
            ),
            Tables.Table.get(
              VersionRecord,
              NodeState.versions(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
              ),
              k
            ),
            Maybe.or(
              &2,
              VersionRecord,
              Tables.Table.get(VersionRecord, NodeState.versions(s), k),
              Tables.Table.get(VersionRecord, NodeState.versions(a), k)
            ),
            after_v(s, a, r1, k)
          )
        )
      ),
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Blob.find.of(
          VersionRecord.blobs.of(
            Maybe.or(
              &2,
              VersionRecord,
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                Tables.Table.get(VersionRecord, NodeState.versions(a), k)
              ),
              Tables.Table.get(VersionRecord, NodeState.versions(b), k)
            )
          ),
          n
        ),
        Blob.find.of(
          VersionRecord.blobs.of(
            Maybe.or(
              &2,
              VersionRecord,
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                Tables.Table.get(VersionRecord, NodeState.versions(b), k)
              ),
              Tables.Table.get(VersionRecord, NodeState.versions(a), k)
            )
          ),
          n
        ),
        Blob.find.of(
          VersionRecord.blobs.of(
            Tables.Table.get(
              VersionRecord,
              NodeState.versions(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(s, r3, Sync.go(False{}, s, b))
                      ),
                      a
                    )
                  )
                )
              ),
              k
            )
          ),
          n
        ),
        comm_blob(
          Tables.Table.get(VersionRecord, NodeState.versions(s), k),
          Tables.Table.get(VersionRecord, NodeState.versions(a), k),
          Tables.Table.get(VersionRecord, NodeState.versions(b), k),
          n
        )((
            %after_v(s, a, r1, k): Compat(Tables.Table.get(VersionRecord, NodeState.versions(b), k), _)
            compat_of(NodeState.versions(b), NodeState.versions(Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))), k)(hc))),
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Blob.find.of(
            VersionRecord.blobs.of(
              Tables.Table.get(
                VersionRecord,
                NodeState.versions(
                  Pair.fst(
                    NodeState,
                    Spec.Answer,
                    VendNode.applied(
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(s, r3, Sync.go(False{}, s, b))
                      ),
                      r4,
                      Sync.go(
                        False{},
                        Pair.fst(
                          NodeState,
                          Spec.Answer,
                          VendNode.applied(s, r3, Sync.go(False{}, s, b))
                        ),
                        a
                      )
                    )
                  )
                ),
                k
              )
            ),
            n
          ),
          Blob.find.of(
            VersionRecord.blobs.of(
              Maybe.or(
                &2,
                VersionRecord,
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k)
                ),
                Tables.Table.get(VersionRecord, NodeState.versions(a), k)
              )
            ),
            n
          ),
          Equal.cong(
            Maybe<&2, VersionRecord>,
            Maybe<&2, List<&2, U32>>,
            z => Blob.find.of(VersionRecord.blobs.of(z), n),
            Tables.Table.get(
              VersionRecord,
              NodeState.versions(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(s, r3, Sync.go(False{}, s, b))
                      ),
                      a
                    )
                  )
                )
              ),
              k
            ),
            Maybe.or(
              &2,
              VersionRecord,
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                Tables.Table.get(VersionRecord, NodeState.versions(b), k)
              ),
              Tables.Table.get(VersionRecord, NodeState.versions(a), k)
            ),
            Equal.trans(
              Maybe<&2, VersionRecord>,
              Tables.Table.get(
                VersionRecord,
                NodeState.versions(
                  Pair.fst(
                    NodeState,
                    Spec.Answer,
                    VendNode.applied(
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(s, r3, Sync.go(False{}, s, b))
                      ),
                      r4,
                      Sync.go(
                        False{},
                        Pair.fst(
                          NodeState,
                          Spec.Answer,
                          VendNode.applied(s, r3, Sync.go(False{}, s, b))
                        ),
                        a
                      )
                    )
                  )
                ),
                k
              ),
              Maybe.or(
                &2,
                VersionRecord,
                Tables.Table.get(
                  VersionRecord,
                  NodeState.versions(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    )
                  ),
                  k
                ),
                Tables.Table.get(VersionRecord, NodeState.versions(a), k)
              ),
              Maybe.or(
                &2,
                VersionRecord,
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k)
                ),
                Tables.Table.get(VersionRecord, NodeState.versions(a), k)
              ),
              after_v(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                a,
                r4,
                k
              ),
              Equal.cong(
                Maybe<&2, VersionRecord>,
                Maybe<&2, VersionRecord>,
                z => Maybe.or(
                  &2,
                  VersionRecord,
                  z,
                  Tables.Table.get(VersionRecord, NodeState.versions(a), k)
                ),
                Tables.Table.get(
                  VersionRecord,
                  NodeState.versions(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    )
                  ),
                  k
                ),
                Maybe.or(
                  &2,
                  VersionRecord,
                  Tables.Table.get(VersionRecord, NodeState.versions(s), k),
                  Tables.Table.get(VersionRecord, NodeState.versions(b), k)
                ),
                after_v(s, b, r3, k)
              )
            )
          )
        )
      )
    )

# s takes in a then b, or b then a: a branch head agrees
law comm_h:
  for s: NodeState
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for c: String
  {
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      )
    )
      == BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  a
                )
              )
            )
          ),
          c
        )
      ): Maybe<&2, String>
  }

def comm_h(s, a, b, r1, r2, r3, r4, c):
  +s = s
  +a = a
  +b = b
  +r1 = r1
  +r3 = r3
  +c = c
  Equal.trans(
    Maybe<&2, String>,
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      )
    ),
    BranchRecord.head.of(
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(b), c)
      )
    ),
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                a
              )
            )
          )
        ),
        c
      )
    ),
    Equal.cong(
      Maybe<&2, BranchRecord>,
      Maybe<&2, String>,
      z => BranchRecord.head.of(z),
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      ),
      Orders.Order.join(
        ~BranchRecord,
        ~BranchRecord.stamp.cmp,
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(BranchRecord, NodeState.branches(s), c),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(b), c)
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                  b
                )
              )
            )
          ),
          c
        ),
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
            ),
            c
          ),
          Tables.Table.get(BranchRecord, NodeState.branches(b), c)
        ),
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          Tables.Table.get(BranchRecord, NodeState.branches(b), c)
        ),
        after_b(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
          b,
          r2,
          c
        ),
        Equal.cong(
          Maybe<&2, BranchRecord>,
          Maybe<&2, BranchRecord>,
          z => Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            z,
            Tables.Table.get(BranchRecord, NodeState.branches(b), c)
          ),
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
            ),
            c
          ),
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          after_b(s, a, r1, c)
        )
      )
    ),
    Equal.trans(
      Maybe<&2, String>,
      BranchRecord.head.of(
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          Tables.Table.get(BranchRecord, NodeState.branches(b), c)
        )
      ),
      BranchRecord.head.of(
        Orders.Order.join(
          ~BranchRecord,
          ~BranchRecord.stamp.cmp,
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Tables.Table.get(BranchRecord, NodeState.branches(s), c),
            Tables.Table.get(BranchRecord, NodeState.branches(b), c)
          ),
          Tables.Table.get(BranchRecord, NodeState.branches(a), c)
        )
      ),
      BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  a
                )
              )
            )
          ),
          c
        )
      ),
      (
        %Equal.sym(Maybe<&2, String>, BranchRecord.head.of(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(a), c)), Tables.Table.get(BranchRecord, NodeState.branches(b), c))), Maybe.map(&2, BranchRecord, String, y => BranchRecord.head(y), Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(a), c)), Tables.Table.get(BranchRecord, NodeState.branches(b), c))), head_of_map(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(a), c)), Tables.Table.get(BranchRecord, NodeState.branches(b), c)))): {_ == BranchRecord.head.of(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(b), c)), Tables.Table.get(BranchRecord, NodeState.branches(a), c))): Maybe<&2, String>}
        %Equal.sym(Maybe<&2, String>, BranchRecord.head.of(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(b), c)), Tables.Table.get(BranchRecord, NodeState.branches(a), c))), Maybe.map(&2, BranchRecord, String, y => BranchRecord.head(y), Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(b), c)), Tables.Table.get(BranchRecord, NodeState.branches(a), c))), head_of_map(Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(b), c)), Tables.Table.get(BranchRecord, NodeState.branches(a), c)))): {Maybe.map(&2, BranchRecord, String, y => BranchRecord.head(y), Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Orders.Order.join(~BranchRecord, ~BranchRecord.stamp.cmp, Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(a), c)), Tables.Table.get(BranchRecord, NodeState.branches(b), c))) == _: Maybe<&2, String>}
        Orders.Order.join_comm(~BranchRecord, ~String, ~BranchRecord.stamp.cmp, ~BranchRecord.head, x => y => stamp_swap(x, y), x => y => stamp_eq_head(x, y), x => y => z => stamp_chain(x, y, z), Tables.Table.get(BranchRecord, NodeState.branches(s), c), Tables.Table.get(BranchRecord, NodeState.branches(a), c), Tables.Table.get(BranchRecord, NodeState.branches(b), c))),
      Equal.sym(
        Maybe<&2, String>,
        BranchRecord.head.of(
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    a
                  )
                )
              )
            ),
            c
          )
        ),
        BranchRecord.head.of(
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(s), c),
              Tables.Table.get(BranchRecord, NodeState.branches(b), c)
            ),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          )
        ),
        Equal.cong(
          Maybe<&2, BranchRecord>,
          Maybe<&2, String>,
          z => BranchRecord.head.of(z),
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    a
                  )
                )
              )
            ),
            c
          ),
          Orders.Order.join(
            ~BranchRecord,
            ~BranchRecord.stamp.cmp,
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(BranchRecord, NodeState.branches(s), c),
              Tables.Table.get(BranchRecord, NodeState.branches(b), c)
            ),
            Tables.Table.get(BranchRecord, NodeState.branches(a), c)
          ),
          Equal.trans(
            Maybe<&2, BranchRecord>,
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  VendNode.applied(
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(
                        NodeState,
                        Spec.Answer,
                        VendNode.applied(s, r3, Sync.go(False{}, s, b))
                      ),
                      a
                    )
                  )
                )
              ),
              c
            ),
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b)))
                ),
                c
              ),
              Tables.Table.get(BranchRecord, NodeState.branches(a), c)
            ),
            Orders.Order.join(
              ~BranchRecord,
              ~BranchRecord.stamp.cmp,
              Orders.Order.join(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                Tables.Table.get(BranchRecord, NodeState.branches(s), c),
                Tables.Table.get(BranchRecord, NodeState.branches(b), c)
              ),
              Tables.Table.get(BranchRecord, NodeState.branches(a), c)
            ),
            after_b(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
              a,
              r4,
              c
            ),
            Equal.cong(
              Maybe<&2, BranchRecord>,
              Maybe<&2, BranchRecord>,
              z => Orders.Order.join(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                z,
                Tables.Table.get(BranchRecord, NodeState.branches(a), c)
              ),
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b)))
                ),
                c
              ),
              Orders.Order.join(
                ~BranchRecord,
                ~BranchRecord.stamp.cmp,
                Tables.Table.get(BranchRecord, NodeState.branches(s), c),
                Tables.Table.get(BranchRecord, NodeState.branches(b), c)
              ),
              after_b(s, b, r3, c)
            )
          )
        )
      )
    )
  )

# s takes in a then b, or b then a: a mark agrees
law comm_m:
  for s: NodeState
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              b
            )
          )
        )
      ),
      qb,
      qm
    )
      == MarkAt.find(
        NodeState.marks(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                a
              )
            )
          )
        ),
        qb,
        qm
      ): Maybe<&2, String>
  }

def comm_m(s, a, b, r1, r2, r3, r4, qb, qm):
  +s = s
  +a = a
  +b = b
  +r1 = r1
  +r3 = r3
  +qb = qb
  +qm = qm
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              b
            )
          )
        )
      ),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~VersionRecord.rev,
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(NodeState.marks(s), qb, qm),
        MarkAt.find(NodeState.marks(a), qb, qm)
      ),
      MarkAt.find(NodeState.marks(b), qb, qm)
    ),
    MarkAt.find(
      NodeState.marks(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
            r4,
            Sync.go(
              False{},
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
              a
            )
          )
        )
      ),
      qb,
      qm
    ),
    Equal.trans(
      Maybe<&2, String>,
      MarkAt.find(
        NodeState.marks(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        qb,
        qm
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        MarkAt.find(
          NodeState.marks(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          qb,
          qm
        ),
        MarkAt.find(NodeState.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        MarkAt.find(NodeState.marks(b), qb, qm)
      ),
      after_m(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
        b,
        r2,
        qb,
        qm
      ),
      Equal.cong(
        Maybe<&2, String>,
        Maybe<&2, String>,
        z => Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          z,
          MarkAt.find(NodeState.marks(b), qb, qm)
        ),
        MarkAt.find(
          NodeState.marks(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
          ),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        after_m(s, a, r1, qb, qm)
      )
    ),
    Equal.trans(
      Maybe<&2, String>,
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        MarkAt.find(NodeState.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~VersionRecord.rev,
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          MarkAt.find(NodeState.marks(s), qb, qm),
          MarkAt.find(NodeState.marks(b), qb, qm)
        ),
        MarkAt.find(NodeState.marks(a), qb, qm)
      ),
      MarkAt.find(
        NodeState.marks(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                a
              )
            )
          )
        ),
        qb,
        qm
      ),
      (
        %Maybes.Maybe.map_id(String, Orders.Order.join(~String, ~VersionRecord.rev, Orders.Order.join(~String, ~VersionRecord.rev, MarkAt.find(NodeState.marks(s), qb, qm), MarkAt.find(NodeState.marks(a), qb, qm)), MarkAt.find(NodeState.marks(b), qb, qm))): {_ == Orders.Order.join(~String, ~VersionRecord.rev, Orders.Order.join(~String, ~VersionRecord.rev, MarkAt.find(NodeState.marks(s), qb, qm), MarkAt.find(NodeState.marks(b), qb, qm)), MarkAt.find(NodeState.marks(a), qb, qm)): Maybe<&2, String>}
        %Maybes.Maybe.map_id(String, Orders.Order.join(~String, ~VersionRecord.rev, Orders.Order.join(~String, ~VersionRecord.rev, MarkAt.find(NodeState.marks(s), qb, qm), MarkAt.find(NodeState.marks(b), qb, qm)), MarkAt.find(NodeState.marks(a), qb, qm))): {Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~VersionRecord.rev, Orders.Order.join(~String, ~VersionRecord.rev, MarkAt.find(NodeState.marks(s), qb, qm), MarkAt.find(NodeState.marks(a), qb, qm)), MarkAt.find(NodeState.marks(b), qb, qm))) == _: Maybe<&2, String>}
        Orders.Order.join_comm(~String, ~String, ~VersionRecord.rev, ~(y => y), x => y => rev_swap(x, y), x => y => rev_same(x, y), x => y => z => rev_chain(x, y, z), MarkAt.find(NodeState.marks(s), qb, qm), MarkAt.find(NodeState.marks(a), qb, qm), MarkAt.find(NodeState.marks(b), qb, qm))),
      Equal.sym(
        Maybe<&2, String>,
        MarkAt.find(
          NodeState.marks(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  a
                )
              )
            )
          ),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~VersionRecord.rev,
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(NodeState.marks(s), qb, qm),
            MarkAt.find(NodeState.marks(b), qb, qm)
          ),
          MarkAt.find(NodeState.marks(a), qb, qm)
        ),
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            NodeState.marks(
              Pair.fst(
                NodeState,
                Spec.Answer,
                VendNode.applied(
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(
                      NodeState,
                      Spec.Answer,
                      VendNode.applied(s, r3, Sync.go(False{}, s, b))
                    ),
                    a
                  )
                )
              )
            ),
            qb,
            qm
          ),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            MarkAt.find(
              NodeState.marks(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b)))
              ),
              qb,
              qm
            ),
            MarkAt.find(NodeState.marks(a), qb, qm)
          ),
          Orders.Order.join(
            ~String,
            ~VersionRecord.rev,
            Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(NodeState.marks(s), qb, qm),
              MarkAt.find(NodeState.marks(b), qb, qm)
            ),
            MarkAt.find(NodeState.marks(a), qb, qm)
          ),
          after_m(
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
            a,
            r4,
            qb,
            qm
          ),
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, String>,
            z => Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              z,
              MarkAt.find(NodeState.marks(a), qb, qm)
            ),
            MarkAt.find(
              NodeState.marks(
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b)))
              ),
              qb,
              qm
            ),
            Orders.Order.join(
              ~String,
              ~VersionRecord.rev,
              MarkAt.find(NodeState.marks(s), qb, qm),
              MarkAt.find(NodeState.marks(b), qb, qm)
            ),
            after_m(s, b, r3, qb, qm)
          )
        )
      )
    )
  )

# s takes in a then b, or b then a: both hold the same content
law comm_core:
  for s: NodeState
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  {
    Sync.collides(
      Tables.Table.keys(VersionRecord, NodeState.versions(b)),
      NodeState.versions(b),
      NodeState.versions(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a)))
      )
    )
      == False{}: Bool
  } -> Spec.VendNode.SameContent(
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(
          False{},
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
          b
        )
      )
    ),
    Pair.fst(
      NodeState,
      Spec.Answer,
      VendNode.applied(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
        r4,
        Sync.go(
          False{},
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
          a
        )
      )
    )
  )

def comm_core(s, a, b, r1, r2, r3, r4):
  +hc =>
    +s = s
    +a = a
    +b = b
    +r1 = r1
    +r2 = r2
    +r3 = r3
    +r4 = r4
    +n => p => content_eq(
      Pair.fst(
        NodeState,
        Spec.Answer,
        VendNode.applied(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
          r2,
          Sync.go(
            False{},
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
            b
          )
        )
      ),
      Pair.fst(
        NodeState,
        Spec.Answer,
        VendNode.applied(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
          r4,
          Sync.go(
            False{},
            Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r3, Sync.go(False{}, s, b))),
            a
          )
        )
      ),
      Resources.Name.show(n),
      p
    )(
      k => comm_v(s, a, b, r1, r2, r3, r4, Resources.Name.show(n), k)(hc)
    )(c => comm_h(s, a, b, r1, r2, r3, r4, c))(qb => qm => comm_m(s, a, b, r1, r2, r3, r4, qb, qm))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a walk step at a version that m holds
law walk_at:
  for m: Maybe<&2, VersionRecord>
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for vs: Tables.Table<VersionRecord>
  for b: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w0: String
  for t0: String
  {
    m == Some{VersionRecord{b, ps, w0, t0}}: Maybe<&2, VersionRecord>
  } -> {
    List.append(
      &2,
      Tables.Row<VersionRecord>,
      Walked.reached(History.at(k, r, done, m)),
      History.walk(
        g,
        Walked.next(History.at(k, r, done, m)),
        Walked.done(History.at(k, r, done, m)),
        vs
      )
    )
      == Tables.Row{k, VersionRecord{b, ps, w0, t0}}
      <> History.walk(
        g,
        List.append(&2, String, r, ps),
        k <> done,
        vs
      ): List<&2, Tables.Row<VersionRecord>>
  }

def walk_at(m, g, k, r, done, vs, b, ps, w0, t0):
  e =>
    %Equal.sym(
      Maybe<&2, VersionRecord>,
      m,
      Some{VersionRecord{b, ps, w0, t0}},
      e
    ): {
      List.append(
        &2,
        Tables.Row<VersionRecord>,
        Walked.reached(History.at(k, r, done, _)),
        History.walk(
          g,
          Walked.next(History.at(k, r, done, _)),
          Walked.done(History.at(k, r, done, _)),
          vs
        )
      )
        == Tables.Row{k, VersionRecord{b, ps, w0, t0}}
        <> History.walk(
          g,
          List.append(&2, String, r, ps),
          k <> done,
          vs
        ): List<&2, Tables.Row<VersionRecord>>
    }
    {==}

# a walk step at a version k not yet walked
law walk_one:
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for vs: Tables.Table<VersionRecord>
  for b: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w0: String
  for t0: String
  {
    Shared.List.has(~String, ~String.eq, done, k) == False{}: Bool
  } -> {
    Tables.Table.get(
      VersionRecord,
      vs,
      k
    )
      == Some{VersionRecord{b, ps, w0, t0}}: Maybe<&2, VersionRecord>
  } -> {
    History.walk(
      1n+g,
      k <> r,
      done,
      vs
    )
      == Tables.Row{k, VersionRecord{b, ps, w0, t0}}
      <> History.walk(
        g,
        List.append(&2, String, r, ps),
        k <> done,
        vs
      ): List<&2, Tables.Row<VersionRecord>>
  }

def walk_one(g, k, r, done, vs, b, ps, w0, t0):
  hd => hg =>
    +k = k
    +r = r
    +done = done
    +vs = vs
    %Equal.sym(
      Bool,
      Shared.List.has(~String, ~String.eq, done, k),
      False{},
      hd
    ): {
      List.append(
        &2,
        Tables.Row<VersionRecord>,
        Walked.reached(History.next(k, r, done, vs, _)),
        History.walk(
          g,
          Walked.next(History.next(k, r, done, vs, _)),
          Walked.done(History.next(k, r, done, vs, _)),
          vs
        )
      )
        == Tables.Row{k, VersionRecord{b, ps, w0, t0}}
        <> History.walk(
          g,
          List.append(&2, String, r, ps),
          k <> done,
          vs
        ): List<&2, Tables.Row<VersionRecord>>
    }
    walk_at(Tables.Table.get(VersionRecord, vs, k), g, k, r, done, vs, b, ps, w0, t0)(hg)

# the first two versions of a walk from a, whose one parent is bb
law hist_two:
  for f: Nat
  for a: String
  for bb: String
  for xb: Tables.Table<List<&2, U32>>
  for xw: String
  for xt: String
  for yb: Tables.Table<List<&2, U32>>
  for yp: List<&2, String>
  for yw: String
  for yt: String
  for vs: Tables.Table<VersionRecord>
  {
    Tables.Table.get(
      VersionRecord,
      vs,
      a
    )
      == Some{VersionRecord{xb, [bb], xw, xt}}: Maybe<&2, VersionRecord>
  } -> {
    String.eq(a, bb) == False{}: Bool
  } -> {
    Tables.Table.get(
      VersionRecord,
      vs,
      bb
    )
      == Some{VersionRecord{yb, yp, yw, yt}}: Maybe<&2, VersionRecord>
  } -> {
    History.walk(
      1n+1n+f,
      [a],
      [],
      vs
    )
      == Tables.Row{a, VersionRecord{xb, [bb], xw, xt}}
      <> (
        Tables.Row{bb, VersionRecord{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs)
      ): List<&2, Tables.Row<VersionRecord>>
  }

def hist_two(f, a, bb, xb, xw, xt, yb, yp, yw, yt, vs):
  ha => +hab => hb =>
    +f = f
    +a = a
    +bb = bb
    +vs = vs
    +xb = xb
    +xw = xw
    +xt = xt
    Equal.trans(
      List<&2, Tables.Row<VersionRecord>>,
      History.walk(1n+1n+f, [a], [], vs),
      Tables.Row{a, VersionRecord{xb, [bb], xw, xt}} <> History.walk(1n+f, [bb], [a], vs),
      Tables.Row{
        a,
        VersionRecord{xb, [bb], xw, xt}
      }
        <> (Tables.Row{bb, VersionRecord{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs)),
      walk_one(1n+f, a, [], [], vs, xb, [bb], xw, xt)({==})(ha),
      Equal.cong(
        List<&2, Tables.Row<VersionRecord>>,
        List<&2, Tables.Row<VersionRecord>>,
        z => Tables.Row{a, VersionRecord{xb, [bb], xw, xt}} <> z,
        History.walk(1n+f, [bb], [a], vs),
        Tables.Row{bb, VersionRecord{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs),
        walk_one(f, bb, [], [a], vs, yb, yp, yw, yt)((
            %Equal.sym(Bool, String.eq(a, bb), False{}, hab): {List.any.if(u => Shared.List.has(~String, ~String.eq, [], bb), _) == False{}: Bool}
            {==}))(hb)
      )
    )

# the first version of a, bb, ... that ids holds is bb, when it does not hold a
law first_two:
  for a: String
  for bb: String
  for x: VersionRecord
  for y: VersionRecord
  for rest: List<&2, Tables.Row<VersionRecord>>
  for ids: List<&2, String>
  {
    Shared.List.has(~String, ~String.eq, ids, a) == False{}: Bool
  } -> {
    Shared.List.has(~String, ~String.eq, ids, bb) == True{}: Bool
  } -> {
    Vers.first_in(
      Tables.Row{a, x} <> (Tables.Row{bb, y} <> rest),
      ids
    )
      == Some{bb}: Maybe<&2, String>
  }

def first_two(a, bb, x, y, rest, ids):
  ha => hb =>
    +ids = ids
    +a = a
    +bb = bb
    %Equal.sym(
      Bool,
      Shared.List.has(~String, ~String.eq, ids, a),
      False{},
      ha
    ): {
      List.find.if(
        String,
        a,
        u => Vers.first_in(Tables.Row{bb, y} <> rest, ids),
        _
      )
        == Some{bb}: Maybe<&2, String>
    }
    %Equal.sym(
      Bool,
      Shared.List.has(~String, ~String.eq, ids, bb),
      True{},
      hb
    ): {List.find.if(String, bb, u => Vers.first_in(rest, ids), _) == Some{bb}: Maybe<&2, String>}
    {==}

# the IDs of a, bb, ... hold bb
law ids_second:
  for a: String
  for bb: String
  for x: VersionRecord
  for y: VersionRecord
  for rest: List<&2, Tables.Row<VersionRecord>>
  {
    String.eq(a, bb) == False{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      Vers.ids(Tables.Row{a, x} <> (Tables.Row{bb, y} <> rest)),
      bb
    )
      == True{}: Bool
  }

def ids_second(a, bb, x, y, rest):
  e =>
    +a = a
    +bb = bb
    %Equal.sym(
      Bool,
      String.eq(a, bb),
      False{},
      e
    ): {
      List.any.if(
        u => Shared.List.has(~String, ~String.eq, bb <> Vers.ids(rest), bb),
        _
      )
        == True{}: Bool
    }
    %Equal.sym(
      Bool,
      String.eq(bb, bb),
      True{},
      Strings.String.eq_refl(bb)
    ): {
      List.any.if(u => Shared.List.has(~String, ~String.eq, Vers.ids(rest), bb), _) == True{}: Bool
    }
    {==}

# a version found after adding one with another ID is the one found before
law add1_other:
  for vs: Tables.Table<VersionRecord>
  for x: String
  for xv: VersionRecord
  for k: String
  {
    String.eq(x, k) == False{}: Bool
  } -> {
    Tables.Table.get(
      VersionRecord,
      VersionRecord.add([Tables.Row{x, xv}], vs),
      k
    )
      == Tables.Table.get(VersionRecord, vs, k): Maybe<&2, VersionRecord>
  }

def add1_other(vs, x, xv, k):
  e =>
    +vs = vs
    +x = x
    +xv = xv
    +k = k
    Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, VersionRecord.add([Tables.Row{x, xv}], vs), k),
      Maybe.or(
        &2,
        VersionRecord,
        Tables.Table.get(VersionRecord, vs, k),
        Tables.Table.find_row(VersionRecord, [Tables.Row{x, xv}], k)
      ),
      Tables.Table.get(VersionRecord, vs, k),
      add_find([Tables.Row{x, xv}], vs, k),
      (
        %Equal.sym(Bool, String.eq(x, k), False{}, e): {Maybe.or(&2, VersionRecord, Tables.Table.get(VersionRecord, vs, k), Bools.Bool.when(Maybe<&2, VersionRecord>, _, u => Some{xv}, u => Tables.Table.find_row(VersionRecord, [], k))) == Tables.Table.get(VersionRecord, vs, k): Maybe<&2, VersionRecord>}
        Maybes.Maybe.or_none(VersionRecord, Tables.Table.get(VersionRecord, vs, k)))
    )

# named_at at the first key j, by whether j is k (hit)
law named_at.at:
  for hit: Bool
  for j: String
  for r: List<&2, String>
  for vs: Tables.Table<VersionRecord>
  for x: String
  for k: String
  (
    {
      Shared.List.has(~String, ~String.eq, r, k) == True{}: Bool
    } -> {
      Shared.List.has(
        ~String,
        ~String.eq,
        History.parents(Tables.Table.get(VersionRecord, vs, k)),
        x
      )
        == False{}: Bool
    }
  ) -> {
    String.eq(j, k) == hit: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      History.parents(Tables.Table.get(VersionRecord, vs, j)),
      x
    )
      == False{}: Bool
  } -> {
    List.any.if(u => Shared.List.has(~String, ~String.eq, r, k), hit) == True{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      History.parents(Tables.Table.get(VersionRecord, vs, k)),
      x
    )
      == False{}: Bool
  }

def named_at.at(hit, j, r, vs, x, k):
  match hit:
    case True{}:
      ih => e => h0 => hk =>
        %Strings.String.eq_sound(
          j,
          k
        )(
          e
        ): {
          Shared.List.has(
            ~String,
            ~String.eq,
            History.parents(Tables.Table.get(VersionRecord, vs, _)),
            x
          )
            == False{}: Bool
        }
        h0
    case False{}:
      ih => e => h0 => hk => ih(hk)

# a version that no version names as a parent is not a parent of a version
# among ks
law named_at:
  for ks: List<&2, String>
  for vs: Tables.Table<VersionRecord>
  for x: String
  for k: String
  {
    VersionRecord.named(ks, vs, x) == False{}: Bool
  } -> {
    Shared.List.has(~String, ~String.eq, ks, k) == True{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      History.parents(Tables.Table.get(VersionRecord, vs, k)),
      x
    )
      == False{}: Bool
  }

def named_at(ks, vs, x, k):
  match ks:
    case Nil{}:
      hn => hk => Empty.absurd(
        {
          Shared.List.has(
            ~String,
            ~String.eq,
            History.parents(Tables.Table.get(VersionRecord, vs, k)),
            x
          )
            == False{}: Bool
        },
        Shared.Bool.false_ne_true(hk)
      )
    case Con{+j, +r}:
      +hn =>
        +vs = vs
        +x = x
        +k = k
        named_at.at(
          String.eq(j, k),
          j,
          r,
          vs,
          x,
          k
        )(
          named_at(
            r,
            vs,
            x,
            k
          )(
            Bools.Bool.or_false_right(
              Shared.List.has(
                ~String,
                ~String.eq,
                History.parents(Tables.Table.get(VersionRecord, vs, j)),
                x
              ),
              VersionRecord.named(r, vs, x)
            )(hn)
          )
        )(
          {==}
        )(
          Bools.Bool.or_false_left(
            Shared.List.has(
              ~String,
              ~String.eq,
              History.parents(Tables.Table.get(VersionRecord, vs, j)),
              x
            ),
            VersionRecord.named(r, vs, x)
          )(hn)
        )

# walk_avoid at a version k that vs holds as m
law avoid_at:
  for mv: Maybe<&2, VersionRecord>
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: VersionRecord
  for v2s: Tables.Table<VersionRecord>
  (
    @ks2: List<
      &2,
      String> -> @d2: List<
      &2,
      String> -> {
      Shared.List.has(~String, ~String.eq, ks2, x) == False{}: Bool
    } -> {
      VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool
    } -> {
      Shared.List.has(
        ~String,
        ~String.eq,
        Vers.ids(History.walk(g, ks2, d2, VersionRecord.add([Tables.Row{x, xv}], v2s))),
        x
      )
        == False{}: Bool
    }
  ) -> {
    Tables.Table.get(VersionRecord, v2s, k) == mv: Maybe<&2, VersionRecord>
  } -> {
    String.eq(k, x) == False{}: Bool
  } -> {
    Shared.List.has(~String, ~String.eq, r, x) == False{}: Bool
  } -> {
    VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      Vers.ids(
        List.append(
          &2,
          Tables.Row<VersionRecord>,
          Walked.reached(History.at(k, r, done, mv)),
          History.walk(
            g,
            Walked.next(History.at(k, r, done, mv)),
            Walked.done(History.at(k, r, done, mv)),
            VersionRecord.add([Tables.Row{x, xv}], v2s)
          )
        )
      ),
      x
    )
      == False{}: Bool
  }

def avoid_at(mv, g, k, r, done, x, xv, v2s):
  match mv:
    case None{}:
      ih => e => hk => hr => hn => ih(r)(k <> done)(hr)(hn)
    case Some{VersionRecord{b, +ps, a, t}}:
      ih => +e => hk => hr => +hn =>
        +k = k
        +x = x
        +v2s = v2s
        +r = r
        +done = done
        %Equal.sym(
          Bool,
          String.eq(k, x),
          False{},
          hk
        ): {
          List.any.if(
            u => Shared.List.has(
              ~String,
              ~String.eq,
              Vers.ids(
                History.walk(
                  g,
                  List.append(&2, String, r, ps),
                  k <> done,
                  VersionRecord.add([Tables.Row{x, xv}], v2s)
                )
              ),
              x
            ),
            _
          )
            == False{}: Bool
        }
        ih(
          List.append(&2, String, r, ps)
        )(k <> done)(Shared.List.has_append_false(~String, ~String.eq, r, ps, x)(hr)((
              %e: {Shared.List.has(~String, ~String.eq, History.parents(_), x) == False{}: Bool}
              named_at(Tables.Table.keys(VersionRecord, v2s), v2s, x, k)(hn)(Equal.trans(Bool, Shared.List.has(~String, ~String.eq, Tables.Table.keys(VersionRecord, v2s), k), Maybe.is_some(&2, VersionRecord, Tables.Table.get(VersionRecord, v2s, k)), True{}, Tables.Table.keys_get(VersionRecord, v2s, k), Equal.cong(Maybe<&2, VersionRecord>, Bool, z => Maybe.is_some(&2, VersionRecord, z), Tables.Table.get(VersionRecord, v2s, k), Some{VersionRecord{b, ps, a, t}}, e))))))(
          hn
        )

# walk_avoid at a version k, by whether the walk saw it (was)
law avoid_was:
  for was: Bool
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: VersionRecord
  for v2s: Tables.Table<VersionRecord>
  (
    @ks2: List<
      &2,
      String> -> @d2: List<
      &2,
      String> -> {
      Shared.List.has(~String, ~String.eq, ks2, x) == False{}: Bool
    } -> {
      VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool
    } -> {
      Shared.List.has(
        ~String,
        ~String.eq,
        Vers.ids(History.walk(g, ks2, d2, VersionRecord.add([Tables.Row{x, xv}], v2s))),
        x
      )
        == False{}: Bool
    }
  ) -> {
    Shared.List.has(~String, ~String.eq, k <> r, x) == False{}: Bool
  } -> {
    VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      Vers.ids(
        List.append(
          &2,
          Tables.Row<VersionRecord>,
          Walked.reached(
            History.next(k, r, done, VersionRecord.add([Tables.Row{x, xv}], v2s), was)
          ),
          History.walk(
            g,
            Walked.next(History.next(k, r, done, VersionRecord.add([Tables.Row{x, xv}], v2s), was)),
            Walked.done(History.next(k, r, done, VersionRecord.add([Tables.Row{x, xv}], v2s), was)),
            VersionRecord.add([Tables.Row{x, xv}], v2s)
          )
        )
      ),
      x
    )
      == False{}: Bool
  }

def avoid_was(was, g, k, r, done, x, xv, v2s):
  match was:
    case True{}:
      ih => hk => hn =>
        +k = k
        +r = r
        +x = x
        ih(
          r
        )(
          done
        )(
          Pair.snd(
            {String.eq(k, x) == False{}: Bool},
            {Shared.List.has(~String, ~String.eq, r, x) == False{}: Bool},
            Shared.List.has_cons_false(~String, ~String.eq, k, r, x)(hk)
          )
        )(hn)
    case False{}:
      ih => +hk => hn =>
        +k = k
        +r = r
        +x = x
        +xv = xv
        +v2s = v2s
        +done = done
        %Equal.sym(
          Maybe<&2, VersionRecord>,
          Tables.Table.get(VersionRecord, VersionRecord.add([Tables.Row{x, xv}], v2s), k),
          Tables.Table.get(VersionRecord, v2s, k),
          add1_other(
            v2s,
            x,
            xv,
            k
          )(
            Strings.String.eq_flip(
              k,
              x
            )(
              Pair.fst(
                {String.eq(k, x) == False{}: Bool},
                {Shared.List.has(~String, ~String.eq, r, x) == False{}: Bool},
                Shared.List.has_cons_false(~String, ~String.eq, k, r, x)(hk)
              )
            )
          )
        ):
          {
            Shared.List.has(
              ~String,
              ~String.eq,
              Vers.ids(
                List.append(
                  &2,
                  Tables.Row<VersionRecord>,
                  Walked.reached(History.at(k, r, done, _)),
                  History.walk(
                    g,
                    Walked.next(History.at(k, r, done, _)),
                    Walked.done(History.at(k, r, done, _)),
                    VersionRecord.add([Tables.Row{x, xv}], v2s)
                  )
                )
              ),
              x
            )
              == False{}: Bool
          }
        avoid_at(
          Tables.Table.get(VersionRecord, v2s, k),
          g,
          k,
          r,
          done,
          x,
          xv,
          v2s
        )(
          ih
        )(
          {==}
        )(
          Pair.fst(
            {String.eq(k, x) == False{}: Bool},
            {Shared.List.has(~String, ~String.eq, r, x) == False{}: Bool},
            Shared.List.has_cons_false(~String, ~String.eq, k, r, x)(hk)
          )
        )(
          Pair.snd(
            {String.eq(k, x) == False{}: Bool},
            {Shared.List.has(~String, ~String.eq, r, x) == False{}: Bool},
            Shared.List.has_cons_false(~String, ~String.eq, k, r, x)(hk)
          )
        )(hn)

# a walk from versions that are not x, after x was added with no version
# naming it as a parent, never reaches x
law walk_avoid:
  for f: Nat
  for ks: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: VersionRecord
  for v2s: Tables.Table<VersionRecord>
  {
    Shared.List.has(~String, ~String.eq, ks, x) == False{}: Bool
  } -> {
    VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool
  } -> {
    Shared.List.has(
      ~String,
      ~String.eq,
      Vers.ids(History.walk(f, ks, done, VersionRecord.add([Tables.Row{x, xv}], v2s))),
      x
    )
      == False{}: Bool
  }

def walk_avoid.g1(
  +f: Nat,
  +ks: List<&2, String>,
  +done: List<&2, String>,
  +x: String,
  +xv: VersionRecord,
  +v2s: Tables.Table<VersionRecord>,
  x1: {Shared.List.has(~String, ~String.eq, ks, x) == False{}: Bool},
  x2: {VersionRecord.named(Tables.Table.keys(VersionRecord, v2s), v2s, x) == False{}: Bool}
) -> {
  Shared.List.has(
    ~String,
    ~String.eq,
    Vers.ids(History.walk(f, ks, done, VersionRecord.add([Tables.Row{x, xv}], v2s))),
    x
  )
    == False{}: Bool
}:
  match f:
    case 0n:
      {==}
    case 1n+fp:
      match ks:
        case Nil{}:
          {==}
        case Con{head, tail}:
          avoid_was(
            Shared.List.has(~String, ~String.eq, done, head),
            fp,
            head,
            tail,
            done,
            x,
            xv,
            v2s
          )(ks2 => d2 => x3 => x4 => walk_avoid.g1(fp, ks2, d2, x, xv, v2s, x3, x4))(x1)(x2)

def walk_avoid(f, ks, done, x, xv, v2s):
  x1 => x2 => walk_avoid.g1(f, ks, done, x, xv, v2s, x1, x2)

# there is always fuel for one step of a walk
def links_one(ks: List<&2, String>, +vs: Tables.Table<VersionRecord>) -> &y:
  Nat -> {History.links(ks, vs) == 1n+y: Nat}:
  match ks:
    case Nil{}:
      (0n, {==})
    case Con{k, r}:
      (
        Nat.add(
          List.length(&2, String, History.parents(Tables.Table.get(VersionRecord, vs, k))),
          History.links(r, vs)
        ),
        {==}
      )

# links_two, once the rest is found to have fuel for one step
def links_two.of(
  +l: Nat,
  r: List<&2, String>,
  vs: Tables.Table<VersionRecord>,
  w: &y: Nat -> {History.links(r, vs) == 1n+y: Nat}
) -> &f:
  Nat -> {Nat.add(1n+l, History.links(r, vs)) == 1n+1n+f: Nat}:
  match w:
    case (+y, e):
      (Nat.add(l, y), (
          %Equal.sym(Nat, History.links(r, vs), 1n+y, e): {Nat.add(1n+l, _) == 1n+1n+Nat.add(l, y): Nat}
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(l, 1n+y), 1n+Nat.add(l, y), Nats.Nat.add_succ(l, y))))

# a walk over some versions has fuel for two steps
def links_two(
  ks: List<&2, String>,
  +vs: Tables.Table<VersionRecord>,
  k: String
) -> {Shared.List.has(~String, ~String.eq, ks, k) == True{}: Bool} -> &f:
  Nat -> {History.links(ks, vs) == 1n+1n+f: Nat}:
  match ks:
    case Nil{}:
      h => Empty.absurd(
        &f: Nat -> {History.links([], vs) == 1n+1n+f: Nat},
        Shared.Bool.false_ne_true(h)
      )
    case Con{j, +r}:
      h => links_two.of(
        List.length(&2, String, History.parents(Tables.Table.get(VersionRecord, vs, j))),
        r,
        vs,
        links_one(r, vs)
      )

# the merge picks the head's write for n1
law pick1:
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Picked.at(
      Tables.Table.set(List<&2, U32>, b0, n1, x1),
      Tables.Table.set(List<&2, U32>, b0, n2, x2),
      b0,
      n1
    )
      == Picked.Take{Some{x1}}: Picked
  }

def pick1(b0, n1, x1, n2, x2):
  hne =>
    +b0 = b0
    +n1 = n1
    +x1 = x1
    +n2 = n2
    +x2 = x2
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n1),
      Some{x1},
      Tables.Table.get_after_set(List<&2, U32>, b0, n1, x1)
    ):
      {
        Picked.of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n1),
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n1)
          ),
          _,
          Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n1)
        )
          == Picked.Take{Some{x1}}: Picked
      }
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n1),
      Tables.Table.get(List<&2, U32>, b0, n1),
      Tables.Table.set_keeps_other(
        List<&2, U32>,
        b0,
        n2,
        x2,
        n1,
        Strings.String.eq_flip(n1, n2)(hne)
      )
    ):
      {
        Picked.of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Some{x1},
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Maybes.Maybe.same(~List<&2, U32>, ~Octets.Bytes.is_eq, Some{x1}, _),
          Some{x1},
          _
        )
          == Picked.Take{Some{x1}}: Picked
      }
    %Equal.sym(
      Bool,
      Maybes.Maybe.same(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        Tables.Table.get(List<&2, U32>, b0, n1),
        Tables.Table.get(List<&2, U32>, b0, n1)
      ),
      True{},
      Maybes.Maybe.same_refl(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        ~Octets.Bytes.is_eq_refl,
        Tables.Table.get(List<&2, U32>, b0, n1)
      )
    ):
      {
        Picked.of(
          _,
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Some{x1},
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Some{x1},
            Tables.Table.get(List<&2, U32>, b0, n1)
          ),
          Some{x1},
          Tables.Table.get(List<&2, U32>, b0, n1)
        )
          == Picked.Take{Some{x1}}: Picked
      }
    {==}

# pick2, by whether the merged-in bytes are the base's (fo)
law pick2.at:
  for fo: Bool
  for b0: Tables.Table<List<&2, U32>>
  for n2: String
  for x2: List<&2, U32>
  {
    Maybes.Maybe.same(
      ~List<&2, U32>,
      ~Octets.Bytes.is_eq,
      Some{x2},
      Tables.Table.get(List<&2, U32>, b0, n2)
    )
      == fo: Bool
  } -> {
    Picked.of(
      fo,
      True{},
      Maybes.Maybe.same(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        Tables.Table.get(List<&2, U32>, b0, n2),
        Some{x2}
      ),
      Tables.Table.get(List<&2, U32>, b0, n2),
      Some{x2}
    )
      == Picked.Take{Some{x2}}: Picked
  }

def pick2.at(fo, b0, n2, x2):
  match fo:
    case True{}:
      e =>
        +b0 = b0
        +n2 = n2
        +x2 = x2
        Equal.sym(
          Picked,
          Picked.Take{Some{x2}},
          Picked.Take{Tables.Table.get(List<&2, U32>, b0, n2)},
          Equal.cong(
            Maybe<&2, List<&2, U32>>,
            Picked,
            z => Picked.Take{z},
            Some{x2},
            Tables.Table.get(List<&2, U32>, b0, n2),
            Maybes.Maybe.same_sound(
              ~List<&2, U32>,
              ~Octets.Bytes.is_eq,
              y => z => Octets.Bytes.is_eq_sound(y, z),
              Some{x2},
              Tables.Table.get(List<&2, U32>, b0, n2)
            )(e)
          )
        )
    case False{}:
      e => {==}

# the merge picks the merged-in write for n2
law pick2:
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Picked.at(
      Tables.Table.set(List<&2, U32>, b0, n1, x1),
      Tables.Table.set(List<&2, U32>, b0, n2, x2),
      b0,
      n2
    )
      == Picked.Take{Some{x2}}: Picked
  }

def pick2(b0, n1, x1, n2, x2):
  hne =>
    +b0 = b0
    +n1 = n1
    +x1 = x1
    +n2 = n2
    +x2 = x2
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n2),
      Tables.Table.get(List<&2, U32>, b0, n2),
      Tables.Table.set_keeps_other(List<&2, U32>, b0, n1, x1, n2, hne)
    ):
      {
        Picked.of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n2),
            Tables.Table.get(List<&2, U32>, b0, n2)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, b0, n2)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n2)
          ),
          _,
          Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n2)
        )
          == Picked.Take{Some{x2}}: Picked
      }
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n2),
      Some{x2},
      Tables.Table.get_after_set(List<&2, U32>, b0, n2, x2)
    ):
      {
        Picked.of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            _,
            Tables.Table.get(List<&2, U32>, b0, n2)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n2),
            Tables.Table.get(List<&2, U32>, b0, n2)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n2),
            _
          ),
          Tables.Table.get(List<&2, U32>, b0, n2),
          _
        )
          == Picked.Take{Some{x2}}: Picked
      }
    %Equal.sym(
      Bool,
      Maybes.Maybe.same(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        Tables.Table.get(List<&2, U32>, b0, n2),
        Tables.Table.get(List<&2, U32>, b0, n2)
      ),
      True{},
      Maybes.Maybe.same_refl(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        ~Octets.Bytes.is_eq_refl,
        Tables.Table.get(List<&2, U32>, b0, n2)
      )
    ):
      {
        Picked.of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Some{x2},
            Tables.Table.get(List<&2, U32>, b0, n2)
          ),
          _,
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n2),
            Some{x2}
          ),
          Tables.Table.get(List<&2, U32>, b0, n2),
          Some{x2}
        )
          == Picked.Take{Some{x2}}: Picked
      }
    pick2.at(
      Maybes.Maybe.same(
        ~List<&2, U32>,
        ~Octets.Bytes.is_eq,
        Some{x2},
        Tables.Table.get(List<&2, U32>, b0, n2)
      ),
      b0,
      n2,
      x2
    )({==})

# a pick that takes whatever is merged in, or keeps the head, never clashes
law clash_of:
  for fo: Bool
  for hf: Bool
  for h: Maybe<&2, List<&2, U32>>
  for f: Maybe<&2, List<&2, U32>>
  for n: String
  for rest: List<&2, String>
  {Picked.clash(Picked.of(fo, True{}, hf, h, f), n, rest) == rest: List<&2, String>}

def clash_of(fo, hf, h, f, n, rest):
  match fo:
    case True{}:
      {==}
    case False{}:
      {==}

# clash_none at n, by whether n is n1 (c1)
law clash_none.at:
  for c1: Bool
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  for n: String
  for rest: List<&2, String>
  {
    String.eq(n1, n) == c1: Bool
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Picked.clash(
      Picked.at(
        Tables.Table.set(List<&2, U32>, b0, n1, x1),
        Tables.Table.set(List<&2, U32>, b0, n2, x2),
        b0,
        n
      ),
      n,
      rest
    )
      == rest: List<&2, String>
  }

def clash_none.at(c1, b0, n1, x1, n2, x2, n, rest):
  match c1:
    case True{}:
      e => hne =>
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        +n = n
        +rest = rest
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n),
          Tables.Table.get(List<&2, U32>, b0, n),
          Tables.Table.set_keeps_other(List<&2, U32>, b0, n2, x2, n, Strings.String.eq_flip(n, n2)((
                %Strings.String.eq_sound(n1, n)(e): {String.eq(_, n2) == False{}: Bool}
                hne)))
        ):
          {
            Picked.clash(
              Picked.of(
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  _,
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                  _
                ),
                Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                _
              ),
              n,
              rest
            )
              == rest: List<&2, String>
          }
        %Equal.sym(
          Bool,
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n),
            Tables.Table.get(List<&2, U32>, b0, n)
          ),
          True{},
          Maybes.Maybe.same_refl(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            ~Octets.Bytes.is_eq_refl,
            Tables.Table.get(List<&2, U32>, b0, n)
          )
        ):
          {
            Picked.clash(
              Picked.of(
                _,
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
                Tables.Table.get(List<&2, U32>, b0, n)
              ),
              n,
              rest
            )
              == rest: List<&2, String>
          }
        {==}
    case False{}:
      e => hne =>
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        +n = n
        +rest = rest
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n1, x1), n),
          Tables.Table.get(List<&2, U32>, b0, n),
          Tables.Table.set_keeps_other(List<&2, U32>, b0, n1, x1, n, e)
        ):
          {
            Picked.clash(
              Picked.of(
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n),
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  _,
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  _,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n)
                ),
                _,
                Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n)
              ),
              n,
              rest
            )
              == rest: List<&2, String>
          }
        %Equal.sym(
          Bool,
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n),
            Tables.Table.get(List<&2, U32>, b0, n)
          ),
          True{},
          Maybes.Maybe.same_refl(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            ~Octets.Bytes.is_eq_refl,
            Tables.Table.get(List<&2, U32>, b0, n)
          )
        ):
          {
            Picked.clash(
              Picked.of(
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n),
                  Tables.Table.get(List<&2, U32>, b0, n)
                ),
                _,
                Maybes.Maybe.same(
                  ~List<&2, U32>,
                  ~Octets.Bytes.is_eq,
                  Tables.Table.get(List<&2, U32>, b0, n),
                  Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n)
                ),
                Tables.Table.get(List<&2, U32>, b0, n),
                Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n)
              ),
              n,
              rest
            )
              == rest: List<&2, String>
          }
        clash_of(
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n),
            Tables.Table.get(List<&2, U32>, b0, n)
          ),
          Maybes.Maybe.same(
            ~List<&2, U32>,
            ~Octets.Bytes.is_eq,
            Tables.Table.get(List<&2, U32>, b0, n),
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n)
          ),
          Tables.Table.get(List<&2, U32>, b0, n),
          Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, b0, n2, x2), n),
          n,
          rest
        )

# no resource clashes in this merge
law clashes_nil:
  for ns: List<&2, String>
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Merge.clashes(
      ns,
      Tables.Table.set(List<&2, U32>, b0, n1, x1),
      Tables.Table.set(List<&2, U32>, b0, n2, x2),
      b0
    )
      == []: List<&2, String>
  }

def clashes_nil(ns, b0, n1, x1, n2, x2):
  match ns:
    case Nil{}:
      hne => {==}
    case Con{+n, r}:
      +hne =>
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        Equal.trans(
          List<&2, String>,
          Picked.clash(
            Picked.at(
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0,
              n
            ),
            n,
            Merge.clashes(
              r,
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0
            )
          ),
          Picked.clash(
            Picked.at(
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0,
              n
            ),
            n,
            []
          ),
          [],
          Equal.cong(
            List<&2, String>,
            List<&2, String>,
            z => Picked.clash(
              Picked.at(
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0,
                n
              ),
              n,
              z
            ),
            Merge.clashes(
              r,
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0
            ),
            [],
            clashes_nil(r, b0, n1, x1, n2, x2)(hne)
          ),
          clash_none.at(String.eq(n1, n), b0, n1, x1, n2, x2, n, [])({==})(hne)
        )

# a pick at another resource leaves a resource's bytes
law blob_other:
  for pk: Picked
  for n: String
  for rest: Tables.Table<List<&2, U32>>
  for q: String
  {
    String.eq(n, q) == False{}: Bool
  } -> {
    Tables.Table.get(
      List<&2, U32>,
      Picked.blob(pk, n, rest),
      q
    )
      == Tables.Table.get(List<&2, U32>, rest, q): Maybe<&2, List<&2, U32>>
  }

def blob_other(pk, n, rest, q):
  match pk:
    case Picked.Take{None{}}:
      e => {==}
    case Picked.Take{Some{x}}:
      e => Tables.Table.set_keeps_other(List<&2, U32>, rest, n, x, q, e)
    case Picked.Clash{}:
      e => {==}

# blobs_get at the first name n, by whether it is q (hit)
law blobs_get.at:
  for hit: Bool
  for n: String
  for r: List<&2, String>
  for q: String
  for y: List<&2, U32>
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  (
    {
      Shared.List.has(~String, ~String.eq, r, q) == True{}: Bool
    } -> {
      Tables.Table.get(
        List<&2, U32>,
        Merge.blobs(
          r,
          Tables.Table.set(List<&2, U32>, b0, n1, x1),
          Tables.Table.set(List<&2, U32>, b0, n2, x2),
          b0
        ),
        q
      )
        == Some{y}: Maybe<&2, List<&2, U32>>
    }
  ) -> {
    String.eq(n, q) == hit: Bool
  } -> {
    Picked.at(
      Tables.Table.set(List<&2, U32>, b0, n1, x1),
      Tables.Table.set(List<&2, U32>, b0, n2, x2),
      b0,
      q
    )
      == Picked.Take{Some{y}}: Picked
  } -> {
    List.any.if(u => Shared.List.has(~String, ~String.eq, r, q), hit) == True{}: Bool
  } -> {
    Tables.Table.get(
      List<&2, U32>,
      Picked.blob(
        Picked.at(
          Tables.Table.set(List<&2, U32>, b0, n1, x1),
          Tables.Table.set(List<&2, U32>, b0, n2, x2),
          b0,
          n
        ),
        n,
        Merge.blobs(
          r,
          Tables.Table.set(List<&2, U32>, b0, n1, x1),
          Tables.Table.set(List<&2, U32>, b0, n2, x2),
          b0
        )
      ),
      q
    )
      == Some{y}: Maybe<&2, List<&2, U32>>
  }

def blobs_get.at(hit, n, r, q, y, b0, n1, x1, n2, x2):
  match hit:
    case True{}:
      ih => e => hp => hh =>
        +q = q
        +y = y
        +r = r
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        %Equal.sym(
          String,
          n,
          q,
          Strings.String.eq_sound(n, q)(e)
        ): {
          Tables.Table.get(
            List<&2, U32>,
            Picked.blob(
              Picked.at(
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0,
                _
              ),
              _,
              Merge.blobs(
                r,
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0
              )
            ),
            q
          )
            == Some{y}: Maybe<&2, List<&2, U32>>
        }
        %Equal.sym(
          Picked,
          Picked.at(
            Tables.Table.set(List<&2, U32>, b0, n1, x1),
            Tables.Table.set(List<&2, U32>, b0, n2, x2),
            b0,
            q
          ),
          Picked.Take{Some{y}},
          hp
        ): {
          Tables.Table.get(
            List<&2, U32>,
            Picked.blob(
              _,
              q,
              Merge.blobs(
                r,
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0
              )
            ),
            q
          )
            == Some{y}: Maybe<&2, List<&2, U32>>
        }
        Tables.Table.get_after_set(
          List<&2, U32>,
          Merge.blobs(
            r,
            Tables.Table.set(List<&2, U32>, b0, n1, x1),
            Tables.Table.set(List<&2, U32>, b0, n2, x2),
            b0
          ),
          q,
          y
        )
    case False{}:
      ih => e => hp => hh =>
        +q = q
        +n = n
        +r = r
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Tables.Table.get(
            List<&2, U32>,
            Picked.blob(
              Picked.at(
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0,
                n
              ),
              n,
              Merge.blobs(
                r,
                Tables.Table.set(List<&2, U32>, b0, n1, x1),
                Tables.Table.set(List<&2, U32>, b0, n2, x2),
                b0
              )
            ),
            q
          ),
          Tables.Table.get(
            List<&2, U32>,
            Merge.blobs(
              r,
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0
            ),
            q
          ),
          Some{y},
          blob_other(
            Picked.at(
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0,
              n
            ),
            n,
            Merge.blobs(
              r,
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0
            ),
            q
          )(e),
          ih(hh)
        )

# the merged resources hold the bytes picked for a resource of ns
law blobs_get:
  for ns: List<&2, String>
  for q: String
  for y: List<&2, U32>
  for b0: Tables.Table<List<&2, U32>>
  for n1: String
  for x1: List<&2, U32>
  for n2: String
  for x2: List<&2, U32>
  {
    Picked.at(
      Tables.Table.set(List<&2, U32>, b0, n1, x1),
      Tables.Table.set(List<&2, U32>, b0, n2, x2),
      b0,
      q
    )
      == Picked.Take{Some{y}}: Picked
  } -> {
    Shared.List.has(~String, ~String.eq, ns, q) == True{}: Bool
  } -> {
    Tables.Table.get(
      List<&2, U32>,
      Merge.blobs(
        ns,
        Tables.Table.set(List<&2, U32>, b0, n1, x1),
        Tables.Table.set(List<&2, U32>, b0, n2, x2),
        b0
      ),
      q
    )
      == Some{y}: Maybe<&2, List<&2, U32>>
  }

def blobs_get(ns, q, y, b0, n1, x1, n2, x2):
  match ns:
    case Nil{}:
      hp => hh => Empty.absurd(
        {
          Tables.Table.get(
            List<&2, U32>,
            Merge.blobs(
              [],
              Tables.Table.set(List<&2, U32>, b0, n1, x1),
              Tables.Table.set(List<&2, U32>, b0, n2, x2),
              b0
            ),
            q
          )
            == Some{y}: Maybe<&2, List<&2, U32>>
        },
        Shared.Bool.false_ne_true(hh)
      )
    case Con{+n, +r}:
      +hp => hh =>
        +q = q
        +y = y
        +b0 = b0
        +n1 = n1
        +x1 = x1
        +n2 = n2
        +x2 = x2
        blobs_get.at(
          String.eq(n, q),
          n,
          r,
          q,
          y,
          b0,
          n1,
          x1,
          n2,
          x2
        )(hr => blobs_get(r, q, y, b0, n1, x1, n2, x2)(hp)(hr))({==})(hp)(hh)

# a set-branch of c to the head of b that answers Created
law sb_core:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {
    BranchRecord.head.of(
      Tables.Table.get(BranchRecord, NodeState.branches(s), b)
    )
      == Some{v}: Maybe<&2, String>
  }
    & (
      {
        VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & {
              SetBranch.point(
                BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                s,
                r,
                w,
                z,
                c
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{v, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_core.g7(
  +self: String,
  +versions: Tables.Table<VersionRecord>,
  +branches: Tables.Table<BranchRecord>,
  +marks: Tables.Table<Tables.Table<MarkAt>>,
  +groups: Tables.Table<GroupRecord>,
  +clashes: Tables.Table<Clash>,
  +seen: Tables.Table<Seen>,
  +log: List<&2, Logged>,
  +t: NodeState,
  +r: String,
  +w: String,
  +z: String,
  +b: String,
  +c: String,
  +v: String,
  +x2: Maybe<&2, Seen>,
  hx2: {x2 == Tables.Table.get(Seen, seen, r): Maybe<&2, Seen>},
  x: {
    Outcome.of(
      x2,
      VersionRecord.taken(versions, r),
      List.length(&2, Logged, log)
    )
      == Spec.Outcome.NotSeen{}: Spec.Outcome
  },
  x1: {
    VendNode.asked(
      x2,
      NodeState{self, versions, branches, marks, groups, clashes, seen, log},
      r,
      w,
      z,
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): Pair(NodeState, Spec.Answer)
  }
) -> Pair(
  {
    BranchRecord.head.of(
      Tables.Table.get(
        BranchRecord,
        NodeState.branches(NodeState{self, versions, branches, marks, groups, clashes, seen, log}),
        b
      )
    )
      == Some{v}: Maybe<&2, String>
  },
  Pair(
    {
      VersionRecord.has(
        NodeState.versions(NodeState{self, versions, branches, marks, groups, clashes, seen, log}),
        v
      )
        == True{}: Bool
    },
    Pair(
      {
        Tables.Table.get(
          BranchRecord,
          NodeState.branches(
            NodeState{self, versions, branches, marks, groups, clashes, seen, log}
          ),
          c
        )
          == None{}: Maybe<&2, BranchRecord>
      },
      {
        SetBranch.point(
          BranchRecord.head.of(
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(
                NodeState{self, versions, branches, marks, groups, clashes, seen, log}
              ),
              b
            )
          ),
          NodeState{self, versions, branches, marks, groups, clashes, seen, log},
          r,
          w,
          z,
          c
        )
          == Out{
            [],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(
                NodeState{self, versions, branches, marks, groups, clashes, seen, log}
              ),
              c,
              BranchRecord{
                v,
                NodeState.self(
                  NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                ),
                0n,
                0n
              }
            ),
            NodeState.marks(NodeState{self, versions, branches, marks, groups, clashes, seen, log}),
            NodeState.groups(
              NodeState{self, versions, branches, marks, groups, clashes, seen, log}
            ),
            NodeState.clashes(
              NodeState{self, versions, branches, marks, groups, clashes, seen, log}
            ),
            [Logged.head(c, v)],
            SetBranch.answer(Spec.SetBranch.Created{v})
          }: Out
      }
    )
  )
):
  match t:
    case NodeState{self1, versions1, branches1, marks1, groups1, clashes1, seen1, log1}:
      match x2:
        case None{}:
          sb_point(
            BranchRecord.head.of(
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(
                  NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                ),
                b
              )
            ),
            NodeState{self, versions, branches, marks, groups, clashes, seen, log},
            r,
            w,
            z,
            c,
            v
          )(
            view_ver(
              NodeState{self, versions, branches, marks, groups, clashes, seen, log},
              r,
              SetBranch.point(
                BranchRecord.head.of(Tables.Table.get(BranchRecord, branches, b)),
                NodeState{self, versions, branches, marks, groups, clashes, seen, log},
                r,
                w,
                z,
                c
              ),
              NodeState{self1, versions1, branches1, marks1, groups1, clashes1, seen1, log1},
              Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
            )(x1)
          )
        case Some{value}:
          match value:
            case Seen{answer, at}:
              Empty.absurd(
                Pair(
                  {
                    BranchRecord.head.of(
                      Tables.Table.get(
                        BranchRecord,
                        NodeState.branches(
                          NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                        ),
                        b
                      )
                    )
                      == Some{v}: Maybe<&2, String>
                  },
                  Pair(
                    {
                      VersionRecord.has(
                        NodeState.versions(
                          NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                        ),
                        v
                      )
                        == True{}: Bool
                    },
                    Pair(
                      {
                        Tables.Table.get(
                          BranchRecord,
                          NodeState.branches(
                            NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                          ),
                          c
                        )
                          == None{}: Maybe<&2, BranchRecord>
                      },
                      {
                        SetBranch.point(
                          BranchRecord.head.of(
                            Tables.Table.get(
                              BranchRecord,
                              NodeState.branches(
                                NodeState{
                                  self,
                                  versions,
                                  branches,
                                  marks,
                                  groups,
                                  clashes,
                                  seen,
                                  log
                                }
                              ),
                              b
                            )
                          ),
                          NodeState{self, versions, branches, marks, groups, clashes, seen, log},
                          r,
                          w,
                          z,
                          c
                        )
                          == Out{
                            [],
                            Tables.Table.set(
                              BranchRecord,
                              NodeState.branches(
                                NodeState{
                                  self,
                                  versions,
                                  branches,
                                  marks,
                                  groups,
                                  clashes,
                                  seen,
                                  log
                                }
                              ),
                              c,
                              BranchRecord{
                                v,
                                NodeState.self(
                                  NodeState{
                                    self,
                                    versions,
                                    branches,
                                    marks,
                                    groups,
                                    clashes,
                                    seen,
                                    log
                                  }
                                ),
                                0n,
                                0n
                              }
                            ),
                            NodeState.marks(
                              NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                            ),
                            NodeState.groups(
                              NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                            ),
                            NodeState.clashes(
                              NodeState{self, versions, branches, marks, groups, clashes, seen, log}
                            ),
                            [Logged.head(c, v)],
                            SetBranch.answer(Spec.SetBranch.Created{v})
                          }: Out
                      }
                    )
                  )
                ),
                {
                  (%x: {\{Spec.Outcome.Applied: f0 => Unit; \{Spec.Outcome.NotSeen: Empty; \{}}}: Spec.Outcome -> Type}(
                    _
                  ); Unit{}): Empty
                }
              )

def sb_core(s, t, r, w, z, b, c, v):
  match s:
    case NodeState{self, versions, branches, marks, groups, clashes, +seen, log}:
      +r = r
      x => x1 => sb_core.g7(
        self,
        versions,
        branches,
        marks,
        groups,
        clashes,
        seen,
        log,
        t,
        r,
        w,
        z,
        b,
        c,
        v,
        Tables.Table.get(Seen, seen, r),
        {==},
        x,
        x1
      )

# ... b's head was v
law sb_head:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {
    BranchRecord.head.of(
      Tables.Table.get(BranchRecord, NodeState.branches(s), b)
    )
      == Some{v}: Maybe<&2, String>
  }

def sb_head(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {
      BranchRecord.head.of(
        Tables.Table.get(BranchRecord, NodeState.branches(s), b)
      )
        == Some{v}: Maybe<&2, String>
    },
    (
      {
        VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(
              BranchRecord,
              NodeState.branches(s),
              c
            )
              == None{}: Maybe<&2, BranchRecord>
          }
            & {
              SetBranch.point(
                BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                s,
                r,
                w,
                z,
                c
              )
                == Out{
                  [],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s),
                    c,
                    BranchRecord{v, NodeState.self(s), 0n, 0n}
                  ),
                  NodeState.marks(s),
                  NodeState.groups(s),
                  NodeState.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    ),
    sb_core(s, t, r, w, z, b, c, v)(hn)(h)
  )

# ... v was a version
law sb_has:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {VersionRecord.has(NodeState.versions(s), v) == True{}: Bool}

def sb_has(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {VersionRecord.has(NodeState.versions(s), v) == True{}: Bool},
    (
      {
        Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>
      }
        & {
          SetBranch.point(
            BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
            s,
            r,
            w,
            z,
            c
          )
            == Out{
              [],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s),
                c,
                BranchRecord{v, NodeState.self(s), 0n, 0n}
              ),
              NodeState.marks(s),
              NodeState.groups(s),
              NodeState.clashes(s),
              [Logged.head(c, v)],
              SetBranch.answer(Spec.SetBranch.Created{v})
            }: Out
        }
    ),
    Pair.snd(
      {
        BranchRecord.head.of(
          Tables.Table.get(BranchRecord, NodeState.branches(s), b)
        )
          == Some{v}: Maybe<&2, String>
      },
      (
        {
          VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(
                BranchRecord,
                NodeState.branches(s),
                c
              )
                == None{}: Maybe<&2, BranchRecord>
            }
              & {
                SetBranch.point(
                  BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                  s,
                  r,
                  w,
                  z,
                  c
                )
                  == Out{
                    [],
                    Tables.Table.set(
                      BranchRecord,
                      NodeState.branches(s),
                      c,
                      BranchRecord{v, NodeState.self(s), 0n, 0n}
                    ),
                    NodeState.marks(s),
                    NodeState.groups(s),
                    NodeState.clashes(s),
                    [Logged.head(c, v)],
                    SetBranch.answer(Spec.SetBranch.Created{v})
                  }: Out
              }
          )
      ),
      sb_core(s, t, r, w, z, b, c, v)(hn)(h)
    )
  )

# ... c did not exist
law sb_none:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>}

def sb_none(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>},
    {
      SetBranch.point(
        BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
        s,
        r,
        w,
        z,
        c
      )
        == Out{
          [],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v, NodeState.self(s), 0n, 0n}
          ),
          NodeState.marks(s),
          NodeState.groups(s),
          NodeState.clashes(s),
          [Logged.head(c, v)],
          SetBranch.answer(Spec.SetBranch.Created{v})
        }: Out
    },
    Pair.snd(
      {VersionRecord.has(NodeState.versions(s), v) == True{}: Bool},
      (
        {
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(s),
            c
          )
            == None{}: Maybe<&2, BranchRecord>
        }
          & {
            SetBranch.point(
              BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
              s,
              r,
              w,
              z,
              c
            )
              == Out{
                [],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s),
                  c,
                  BranchRecord{v, NodeState.self(s), 0n, 0n}
                ),
                NodeState.marks(s),
                NodeState.groups(s),
                NodeState.clashes(s),
                [Logged.head(c, v)],
                SetBranch.answer(Spec.SetBranch.Created{v})
              }: Out
          }
      ),
      Pair.snd(
        {
          BranchRecord.head.of(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b)
          )
            == Some{v}: Maybe<&2, String>
        },
        (
          {
            VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
          }
            & (
              {
                Tables.Table.get(
                  BranchRecord,
                  NodeState.branches(s),
                  c
                )
                  == None{}: Maybe<&2, BranchRecord>
              }
                & {
                  SetBranch.point(
                    BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                    s,
                    r,
                    w,
                    z,
                    c
                  )
                    == Out{
                      [],
                      Tables.Table.set(
                        BranchRecord,
                        NodeState.branches(s),
                        c,
                        BranchRecord{v, NodeState.self(s), 0n, 0n}
                      ),
                      NodeState.marks(s),
                      NodeState.groups(s),
                      NodeState.clashes(s),
                      [Logged.head(c, v)],
                      SetBranch.answer(Spec.SetBranch.Created{v})
                    }: Out
                }
            )
        ),
        sb_core(s, t, r, w, z, b, c, v)(hn)(h)
      )
    )
  )

# ... its Out
law sb_out:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {
    SetBranch.point(
      BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
      s,
      r,
      w,
      z,
      c
    )
      == Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(c, v)],
        SetBranch.answer(Spec.SetBranch.Created{v})
      }: Out
  }

def sb_out(s, t, r, w, z, b, c, v):
  hn => h => Pair.snd(
    {Tables.Table.get(BranchRecord, NodeState.branches(s), c) == None{}: Maybe<&2, BranchRecord>},
    {
      SetBranch.point(
        BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
        s,
        r,
        w,
        z,
        c
      )
        == Out{
          [],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v, NodeState.self(s), 0n, 0n}
          ),
          NodeState.marks(s),
          NodeState.groups(s),
          NodeState.clashes(s),
          [Logged.head(c, v)],
          SetBranch.answer(Spec.SetBranch.Created{v})
        }: Out
    },
    Pair.snd(
      {VersionRecord.has(NodeState.versions(s), v) == True{}: Bool},
      (
        {
          Tables.Table.get(
            BranchRecord,
            NodeState.branches(s),
            c
          )
            == None{}: Maybe<&2, BranchRecord>
        }
          & {
            SetBranch.point(
              BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
              s,
              r,
              w,
              z,
              c
            )
              == Out{
                [],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s),
                  c,
                  BranchRecord{v, NodeState.self(s), 0n, 0n}
                ),
                NodeState.marks(s),
                NodeState.groups(s),
                NodeState.clashes(s),
                [Logged.head(c, v)],
                SetBranch.answer(Spec.SetBranch.Created{v})
              }: Out
          }
      ),
      Pair.snd(
        {
          BranchRecord.head.of(
            Tables.Table.get(BranchRecord, NodeState.branches(s), b)
          )
            == Some{v}: Maybe<&2, String>
        },
        (
          {
            VersionRecord.has(NodeState.versions(s), v) == True{}: Bool
          }
            & (
              {
                Tables.Table.get(
                  BranchRecord,
                  NodeState.branches(s),
                  c
                )
                  == None{}: Maybe<&2, BranchRecord>
              }
                & {
                  SetBranch.point(
                    BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                    s,
                    r,
                    w,
                    z,
                    c
                  )
                    == Out{
                      [],
                      Tables.Table.set(
                        BranchRecord,
                        NodeState.branches(s),
                        c,
                        BranchRecord{v, NodeState.self(s), 0n, 0n}
                      ),
                      NodeState.marks(s),
                      NodeState.groups(s),
                      NodeState.clashes(s),
                      [Logged.head(c, v)],
                      SetBranch.answer(Spec.SetBranch.Created{v})
                    }: Out
                }
            )
        ),
        sb_core(s, t, r, w, z, b, c, v)(hn)(h)
      )
    )
  )

# ... the versions after it
law sb_vv:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {NodeState.versions(t) == NodeState.versions(s): Tables.Table<VersionRecord>}

def sb_vv(s, t, r, w, z, b, c, v):
  +hn => +h =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +b = b
    +c = c
    +v = v
    view_v(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.SetBranch{c, Spec.Point.Head{b}}),
      t,
      Spec.Answer.SetBranch{Spec.SetBranch.Created{v}},
      Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(c, v)],
        SetBranch.answer(Spec.SetBranch.Created{v})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.SetBranch{c, Spec.Point.Head{b}},
        t,
        Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
      )(hn)(h)
    )(sb_out(s, t, r, w, z, b, c, v)(hn)(h))

# ... the branches after it
law sb_vb:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {
    NodeState.branches(
      t
    )
      == Tables.Table.set(
        BranchRecord,
        NodeState.branches(s),
        c,
        BranchRecord{v, NodeState.self(s), 0n, 0n}
      ): Tables.Table<BranchRecord>
  }

def sb_vb(s, t, r, w, z, b, c, v):
  +hn => +h =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +b = b
    +c = c
    +v = v
    view_b(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.SetBranch{c, Spec.Point.Head{b}}),
      t,
      Spec.Answer.SetBranch{Spec.SetBranch.Created{v}},
      Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(c, v)],
        SetBranch.answer(Spec.SetBranch.Created{v})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.SetBranch{c, Spec.Point.Head{b}},
        t,
        Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
      )(hn)(h)
    )(sb_out(s, t, r, w, z, b, c, v)(hn)(h))

# ... the groups after it
law sb_vg:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {NodeState.groups(t) == NodeState.groups(s): Tables.Table<GroupRecord>}

def sb_vg(s, t, r, w, z, b, c, v):
  +hn => +h =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +b = b
    +c = c
    +v = v
    view_g(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.SetBranch{c, Spec.Point.Head{b}}),
      t,
      Spec.Answer.SetBranch{Spec.SetBranch.Created{v}},
      Out{
        [],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v, NodeState.self(s), 0n, 0n}
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(c, v)],
        SetBranch.answer(Spec.SetBranch.Created{v})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.SetBranch{c, Spec.Point.Head{b}},
        t,
        Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
      )(hn)(h)
    )(sb_out(s, t, r, w, z, b, c, v)(hn)(h))

# ... the node after it
law sb_vself:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): NodeState
      & Spec.Answer
  } -> {NodeState.self(t) == NodeState.self(s): String}

def sb_vself.g4(
  +s: NodeState,
  t: NodeState,
  +r: String,
  w: String,
  z: String,
  b: String,
  c: String,
  v: String,
  +x2: Maybe<&2, Seen>,
  hx2: {x2 == Tables.Table.get(Seen, NodeState.seen(s), r): Maybe<&2, Seen>},
  x: {
    Outcome.of(
      x2,
      VersionRecord.taken(NodeState.versions(s), r),
      List.length(&2, Logged, NodeState.log(s))
    )
      == Spec.Outcome.NotSeen{}: Spec.Outcome
  },
  x1: {
    VendNode.asked(
      x2,
      s,
      r,
      w,
      z,
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): Pair(NodeState, Spec.Answer)
  }
) -> {NodeState.self(t) == NodeState.self(s): String}:
  match x2:
    case None{}:
      view_self(
        s,
        r,
        SetBranch.point(
          BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
          s,
          r,
          w,
          z,
          c
        ),
        t,
        Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
      )(x1)
    case Some{value}:
      match value:
        case Seen{answer, at}:
          Empty.absurd(
            {NodeState.self(t) == NodeState.self(s): String},
            {
              (%x: {\{Spec.Outcome.Applied: f0 => Unit; \{Spec.Outcome.NotSeen: Empty; \{}}}: Spec.Outcome -> Type}(
                _
              ); Unit{}): Empty
            }
          )

def sb_vself(s, t, r, w, z, b, c, v):
  +s = s
  +r = r
  x => x1 => sb_vself.g4(
    s,
    t,
    r,
    w,
    z,
    b,
    c,
    v,
    Tables.Table.get(Seen, NodeState.seen(s), r),
    {==},
    x,
    x1
  )

# a write on the branch b, at its head h, that answers Written: the write as
# the owner it was
law ws_core:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    Owner.of(s, BranchRecord{h, o, e, k}) == True{}: Bool
  }
    & {
      Write.on(
        Owner.of(s, BranchRecord{h, o, e, k}),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        x,
        BranchRecord{h, o, e, k}
      )
        == Out{
          [
            Tables.Row{
              r,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                [h],
                w,
                z
              }
            }
          ],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            b,
            BranchRecord.moved(BranchRecord{h, o, e, k}, r)
          ),
          NodeState.marks(s),
          NodeState.groups(s),
          NodeState.clashes(s),
          [Logged.head(b, r)],
          Write.answer(Spec.Write.Written{r})
        }: Out
    }

def ws_core(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  +hn => hask => hb =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +h = h
    +o = o
    +e = e
    +k = k
    +v = v
    +red = wr_reduce(s, r, w, z, n, b, base, x, BranchRecord{h, o, e, k})(new_free(s, r)(hn))(hb)
    wr_on(
      Owner.of(s, BranchRecord{h, o, e, k}),
      s,
      r,
      w,
      z,
      n,
      b,
      base,
      x,
      h,
      o,
      e,
      k,
      v
    )(
      Equal.trans(
        Maybe<&2, String>,
        Answer.version(
          Out.answer(
            Write.on(
              Owner.of(s, BranchRecord{h, o, e, k}),
              s,
              r,
              w,
              z,
              n,
              b,
              base,
              x,
              BranchRecord{h, o, e, k}
            )
          )
        ),
        Answer.version(
          Out.answer(
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}})
          )
        ),
        Some{v},
        Equal.cong(
          Out,
          Maybe<&2, String>,
          y => Answer.version(Out.answer(y)),
          Write.on(
            Owner.of(s, BranchRecord{h, o, e, k}),
            s,
            r,
            w,
            z,
            n,
            b,
            base,
            x,
            BranchRecord{h, o, e, k}
          ),
          Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
          Equal.sym(
            Out,
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
            Write.on(
              Owner.of(s, BranchRecord{h, o, e, k}),
              s,
              r,
              w,
              z,
              n,
              b,
              base,
              x,
              BranchRecord{h, o, e, k}
            ),
            red
          )
        ),
        view_ver(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
          t,
          Spec.Answer.Write{Spec.Write.Written{v}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(hn)(hask)
        )
      )
    )

# ... its Out
law ws_out:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    Step.of(
      s,
      r,
      w,
      z,
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, k}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }: Out
  }

def ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  +hn => hask => +hb =>
    +s = s
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +h = h
    +o = o
    +e = e
    +k = k
    Equal.trans(
      Out,
      Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
      Write.on(
        Owner.of(s, BranchRecord{h, o, e, k}),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        x,
        BranchRecord{h, o, e, k}
      ),
      Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, k}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      },
      wr_reduce(s, r, w, z, n, b, base, x, BranchRecord{h, o, e, k})(new_free(s, r)(hn))(hb),
      Pair.snd(
        {Owner.of(s, BranchRecord{h, o, e, k}) == True{}: Bool},
        {
          Write.on(
            Owner.of(s, BranchRecord{h, o, e, k}),
            s,
            r,
            w,
            z,
            n,
            b,
            base,
            x,
            BranchRecord{h, o, e, k}
          )
            == Out{
              [
                Tables.Row{
                  r,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                    [h],
                    w,
                    z
                  }
                }
              ],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s),
                b,
                BranchRecord.moved(BranchRecord{h, o, e, k}, r)
              ),
              NodeState.marks(s),
              NodeState.groups(s),
              NodeState.clashes(s),
              [Logged.head(b, r)],
              Write.answer(Spec.Write.Written{r})
            }: Out
        },
        ws_core(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb)
      )
    )

# ... it was the owner's
law ws_own:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {Owner.of(s, BranchRecord{h, o, e, k}) == True{}: Bool}

def ws_own(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  hn => hask => hb => Pair.fst(
    {Owner.of(s, BranchRecord{h, o, e, k}) == True{}: Bool},
    {
      Write.on(
        Owner.of(s, BranchRecord{h, o, e, k}),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        x,
        BranchRecord{h, o, e, k}
      )
        == Out{
          [
            Tables.Row{
              r,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
                [h],
                w,
                z
              }
            }
          ],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            b,
            BranchRecord.moved(BranchRecord{h, o, e, k}, r)
          ),
          NodeState.marks(s),
          NodeState.groups(s),
          NodeState.clashes(s),
          [Logged.head(b, r)],
          Write.answer(Spec.Write.Written{r})
        }: Out
    },
    ws_core(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb)
  )

# ... the versions after it
law ws_vv:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    NodeState.versions(
      t
    )
      == VersionRecord.add(
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        NodeState.versions(s)
      ): Tables.Table<VersionRecord>
  }

def ws_vv(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  +hn => +hask => hb =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +h = h
    +o = o
    +e = e
    +k = k
    +v = v
    view_v(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, k}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the branches after it
law ws_vb:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    NodeState.branches(
      t
    )
      == Tables.Table.set(
        BranchRecord,
        NodeState.branches(s),
        b,
        BranchRecord{r, o, e, 1n+k}
      ): Tables.Table<BranchRecord>
  }

def ws_vb(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  +hn => +hask => hb =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +h = h
    +o = o
    +e = e
    +k = k
    +v = v
    view_b(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, k}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the groups after it
law ws_vg:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {NodeState.groups(t) == NodeState.groups(s): Tables.Table<GroupRecord>}

def ws_vg(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  +hn => +hask => hb =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +h = h
    +o = o
    +e = e
    +k = k
    +v = v
    view_g(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s), h), n, x),
              [h],
              w,
              z
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          b,
          BranchRecord.moved(BranchRecord{h, o, e, k}, r)
        ),
        NodeState.marks(s),
        NodeState.groups(s),
        NodeState.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the node after it
law ws_vself:
  for s: NodeState
  for t: NodeState
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for h: String
  for o: String
  for e: Nat
  for k: Nat
  for v: String
  {
    Spec.VendNode.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{h, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {NodeState.self(t) == NodeState.self(s): String}

def ws_vself(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  hn => hask => hb =>
    +s = s
    +t = t
    +r = r
    +w = w
    +z = z
    +n = n
    +b = b
    +base = base
    +x = x
    +v = v
    view_self(
      s,
      r,
      Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}}
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the law is about the owner check as the node runs it; a proof does not run
# merge_disjoint_keeps_both, once the walks of the merge have fuel f for two
# steps
law mdk_fin:
  for s: NodeState
  for s1: NodeState
  for s2: NodeState
  for s3: NodeState
  for s4: NodeState
  for a4: Spec.Answer
  for r1: String
  for w1: String
  for z1: String
  for r2: String
  for w2: String
  for z2: String
  for r3: String
  for w3: String
  for z3: String
  for r4: String
  for w4: String
  for z4: String
  for b: String
  for c: String
  for n1: String
  for n2: String
  for base1: Maybe<&2, String>
  for base2: Maybe<&2, String>
  for x1: List<&2, U32>
  for x2: List<&2, U32>
  for v0: String
  for v1: String
  for v2: String
  for o: String
  for e: Nat
  for k: Nat
  for yb: Tables.Table<List<&2, U32>>
  for yp: List<&2, String>
  for yw: String
  for yt: String
  for f: Nat
  {
    Spec.VendNode.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{Resources.Name{n1}, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{Resources.Name{n2}, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{v0, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(s),
      v0
    )
      == Some{VersionRecord{yb, yp, yw, yt}}: Maybe<&2, VersionRecord>
  } -> {
    History.links(
      Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
      NodeState.versions(s3)
    )
      == 1n+1n+f: Nat
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {NodeState.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
    )

def mdk_fin(
  s,
  s1,
  s2,
  s3,
  s4,
  a4,
  r1,
  w1,
  z1,
  r2,
  w2,
  z2,
  r3,
  w3,
  z3,
  r4,
  w4,
  z4,
  b,
  c,
  n1,
  n2,
  base1,
  base2,
  x1,
  x2,
  v0,
  v1,
  v2,
  o,
  e,
  k,
  yb,
  yp,
  yw,
  yt,
  f
):
  +hn1 => +hn2 => +hn3 => +hn4 => +hne => +h1 => +h2 => +h3 => +h4 => +hbs => +hvs => +hl =>
    +s = s
    +s1 = s1
    +s2 = s2
    +s3 = s3
    +s4 = s4
    +a4 = a4
    +r1 = r1
    +w1 = w1
    +z1 = z1
    +r2 = r2
    +w2 = w2
    +z2 = z2
    +r3 = r3
    +w3 = w3
    +z3 = z3
    +r4 = r4
    +w4 = w4
    +z4 = z4
    +b = b
    +c = c
    +n1 = n1
    +n2 = n2
    +base1 = base1
    +base2 = base2
    +x1 = x1
    +x2 = x2
    +v0 = v0
    +v1 = v1
    +v2 = v2
    +o = o
    +e = e
    +k = k
    +yb = yb
    +yp = yp
    +yw = yw
    +yt = yt
    +f = f
    +s1v = sb_vv(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +s1b = sb_vb(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +s1g = sb_vg(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +s1s = sb_vself(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +hcn = sb_none(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +ecb = Tables.Table.differ(
      BranchRecord,
      NodeState.branches(s),
      c,
      b
    )(
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Bool,
        z => Maybe.is_some(&2, BranchRecord, z),
        Tables.Table.get(BranchRecord, NodeState.branches(s), c),
        None{},
        hcn
      )
    )(
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Bool,
        z => Maybe.is_some(&2, BranchRecord, z),
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        Some{BranchRecord{v0, o, e, k}},
        hbs
      )
    )
    +ebc = Strings.String.eq_flip(c, b)(ecb)
    +b1b = Equal.trans(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s1), b),
      Tables.Table.get(
        BranchRecord,
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n}
        ),
        b
      ),
      Some{BranchRecord{v0, o, e, k}},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, BranchRecord>,
        y => Tables.Table.get(BranchRecord, y, b),
        NodeState.branches(s1),
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n}
        ),
        s1b
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v0, NodeState.self(s), 0n, 0n}
          ),
          b
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        Some{BranchRecord{v0, o, e, k}},
        Tables.Table.set_keeps_other(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n},
          b,
          ecb
        ),
        hbs
      )
    )
    +s2v = ws_vv(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2b = ws_vb(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2g = ws_vg(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2s = ws_vself(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +own = ws_own(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +b2c = Equal.trans(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s2), c),
      Tables.Table.get(
        BranchRecord,
        Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
        c
      ),
      Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, BranchRecord>,
        y => Tables.Table.get(BranchRecord, y, c),
        NodeState.branches(s2),
        Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
        s2b
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
          c
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(s1), c),
        Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
        Tables.Table.set_keeps_other(
          BranchRecord,
          NodeState.branches(s1),
          b,
          BranchRecord{r2, o, e, 1n+k},
          c,
          ebc
        ),
        Equal.trans(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(BranchRecord, NodeState.branches(s1), c),
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              c,
              BranchRecord{v0, NodeState.self(s), 0n, 0n}
            ),
            c
          ),
          Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
          Equal.cong(
            Tables.Table<BranchRecord>,
            Maybe<&2, BranchRecord>,
            y => Tables.Table.get(BranchRecord, y, c),
            NodeState.branches(s1),
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              c,
              BranchRecord{v0, NodeState.self(s), 0n, 0n}
            ),
            s1b
          ),
          Tables.Table.get_after_set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v0, NodeState.self(s), 0n, 0n}
          )
        )
      )
    )
    +s3v = ws_vv(
      s2,
      s3,
      r3,
      w3,
      z3,
      n2,
      c,
      base2,
      x2,
      v0,
      NodeState.self(s),
      0n,
      0n,
      v2
    )(hn3)(h3)(b2c)
    +s3b = ws_vb(
      s2,
      s3,
      r3,
      w3,
      z3,
      n2,
      c,
      base2,
      x2,
      v0,
      NodeState.self(s),
      0n,
      0n,
      v2
    )(hn3)(h3)(b2c)
    +s3g = ws_vg(
      s2,
      s3,
      r3,
      w3,
      z3,
      n2,
      c,
      base2,
      x2,
      v0,
      NodeState.self(s),
      0n,
      0n,
      v2
    )(hn3)(h3)(b2c)
    +s3s = ws_vself(
      s2,
      s3,
      r3,
      w3,
      z3,
      n2,
      c,
      base2,
      x2,
      v0,
      NodeState.self(s),
      0n,
      0n,
      v2
    )(hn3)(h3)(b2c)
    +ha = Equal.trans(
      Maybe<&2, String>,
      BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s3), c)),
      BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s2),
            c,
            BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
          ),
          c
        )
      ),
      Some{r3},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, String>,
        y => BranchRecord.head.of(Tables.Table.get(BranchRecord, y, c)),
        NodeState.branches(s3),
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s2),
          c,
          BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
        ),
        s3b
      ),
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Maybe<&2, String>,
        y => BranchRecord.head.of(y),
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s2),
            c,
            BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
          ),
          c
        ),
        Some{BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}},
        Tables.Table.get_after_set(
          BranchRecord,
          NodeState.branches(s2),
          c,
          BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
        )
      )
    )
    +hb3 = Equal.trans(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s3), b),
      Tables.Table.get(
        BranchRecord,
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s2),
          c,
          BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
        ),
        b
      ),
      Some{BranchRecord{r2, o, e, 1n+k}},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, BranchRecord>,
        y => Tables.Table.get(BranchRecord, y, b),
        NodeState.branches(s3),
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s2),
          c,
          BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
        ),
        s3b
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s2),
            c,
            BranchRecord{r3, NodeState.self(s), 0n, 1n+0n}
          ),
          b
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(s2), b),
        Some{BranchRecord{r2, o, e, 1n+k}},
        Tables.Table.set_keeps_other(
          BranchRecord,
          NodeState.branches(s2),
          c,
          BranchRecord{r3, NodeState.self(s), 0n, 1n+0n},
          b,
          ecb
        ),
        Equal.trans(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(BranchRecord, NodeState.branches(s2), b),
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
            b
          ),
          Some{BranchRecord{r2, o, e, 1n+k}},
          Equal.cong(
            Tables.Table<BranchRecord>,
            Maybe<&2, BranchRecord>,
            y => Tables.Table.get(BranchRecord, y, b),
            NodeState.branches(s2),
            Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
            s2b
          ),
          Tables.Table.get_after_set(
            BranchRecord,
            NodeState.branches(s1),
            b,
            BranchRecord{r2, o, e, 1n+k}
          )
        )
      )
    )
    +s31 = Equal.trans(String, NodeState.self(s3), NodeState.self(s2), NodeState.self(s1), s3s, s2s)
    +g31 = Equal.trans(
      Tables.Table<GroupRecord>,
      NodeState.groups(s3),
      NodeState.groups(s2),
      NodeState.groups(s1),
      s3g,
      s2g
    )
    +hown = Equal.trans(
      Bool,
      Owner.of(s3, BranchRecord{r2, o, e, 1n+k}),
      Bool.or(
        String.eq(o, NodeState.self(s1)),
        GroupRecord.inside(NodeState.groups(s3), Spec.Member.VendNode{NodeState.self(s1)}, o)
      ),
      True{},
      Equal.cong(
        String,
        Bool,
        y => Bool.or(
          String.eq(o, y),
          GroupRecord.inside(NodeState.groups(s3), Spec.Member.VendNode{y}, o)
        ),
        NodeState.self(s3),
        NodeState.self(s1),
        s31
      ),
      Equal.trans(
        Bool,
        Bool.or(
          String.eq(o, NodeState.self(s1)),
          GroupRecord.inside(NodeState.groups(s3), Spec.Member.VendNode{NodeState.self(s1)}, o)
        ),
        Owner.of(s1, BranchRecord{v0, o, e, k}),
        True{},
        Equal.cong(
          Tables.Table<GroupRecord>,
          Bool,
          y => Bool.or(
            String.eq(o, NodeState.self(s1)),
            GroupRecord.inside(y, Spec.Member.VendNode{NodeState.self(s1)}, o)
          ),
          NodeState.groups(s3),
          NodeState.groups(s1),
          g31
        ),
        own
      )
    )
    +ht4 = new_free(s3, r4)(hn4)
    +ht2 = new_free(s1, r2)(hn2)
    +ht3 = new_free(s2, r3)(hn3)
    +g1v0 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s1), v0),
      Tables.Table.get(VersionRecord, NodeState.versions(s), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      Equal.cong(
        Tables.Table<VersionRecord>,
        Maybe<&2, VersionRecord>,
        y => Tables.Table.get(VersionRecord, y, v0),
        NodeState.versions(s1),
        NodeState.versions(s),
        s1v
      ),
      hvs
    )
    +hv1 = Equal.cong(
      Maybe<&2, VersionRecord>,
      Bool,
      y => Maybe.is_some(&2, VersionRecord, y),
      Tables.Table.get(VersionRecord, NodeState.versions(s1), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      g1v0
    )
    +er2v0 = Tables.Table.differ(
      VersionRecord,
      NodeState.versions(s1),
      r2,
      v0
    )(taken_free(NodeState.versions(s1), r2)(ht2))(hv1)
    +g2v0 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
      Tables.Table.get(VersionRecord, NodeState.versions(s1), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      Equal.trans(
        Maybe<&2, VersionRecord>,
        Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
        Tables.Table.get(
          VersionRecord,
          VersionRecord.add(
            [
              Tables.Row{
                r2,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
                  [v0],
                  w2,
                  z2
                }
              }
            ],
            NodeState.versions(s1)
          ),
          v0
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(s1), v0),
        Equal.cong(
          Tables.Table<VersionRecord>,
          Maybe<&2, VersionRecord>,
          y => Tables.Table.get(VersionRecord, y, v0),
          NodeState.versions(s2),
          VersionRecord.add(
            [
              Tables.Row{
                r2,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
                  [v0],
                  w2,
                  z2
                }
              }
            ],
            NodeState.versions(s1)
          ),
          s2v
        ),
        add1_other(
          NodeState.versions(s1),
          r2,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
            [v0],
            w2,
            z2
          },
          v0
        )(er2v0)
      ),
      g1v0
    )
    +hv2 = Equal.cong(
      Maybe<&2, VersionRecord>,
      Bool,
      y => Maybe.is_some(&2, VersionRecord, y),
      Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      g2v0
    )
    +er3v0 = Tables.Table.differ(
      VersionRecord,
      NodeState.versions(s2),
      r3,
      v0
    )(taken_free(NodeState.versions(s2), r3)(ht3))(hv2)
    +g2r2 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s2), r2),
      Tables.Table.get(
        VersionRecord,
        VersionRecord.add(
          [
            Tables.Row{
              r2,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
                [v0],
                w2,
                z2
              }
            }
          ],
          NodeState.versions(s1)
        ),
        r2
      ),
      Some{
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
          [v0],
          w2,
          z2
        }
      },
      Equal.cong(
        Tables.Table<VersionRecord>,
        Maybe<&2, VersionRecord>,
        y => Tables.Table.get(VersionRecord, y, r2),
        NodeState.versions(s2),
        VersionRecord.add(
          [
            Tables.Row{
              r2,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
                [v0],
                w2,
                z2
              }
            }
          ],
          NodeState.versions(s1)
        ),
        s2v
      ),
      add_new_find(
        r2,
        Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
        [v0],
        w2,
        z2,
        NodeState.versions(s1)
      )(taken_free(NodeState.versions(s1), r2)(ht2))
    )
    +er3r2 = Tables.Table.differ(
      VersionRecord,
      NodeState.versions(s2),
      r3,
      r2
    )(
      taken_free(NodeState.versions(s2), r3)(ht3)
    )(
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Bool,
        y => Maybe.is_some(&2, VersionRecord, y),
        Tables.Table.get(VersionRecord, NodeState.versions(s2), r2),
        Some{
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
            [v0],
            w2,
            z2
          }
        },
        g2r2
      )
    )
    +er2r3 = Strings.String.eq_flip(r3, r2)(er3r2)
    +g3r3 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s3), r3),
      Tables.Table.get(
        VersionRecord,
        VersionRecord.add(
          [
            Tables.Row{
              r3,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          NodeState.versions(s2)
        ),
        r3
      ),
      Some{
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
          [v0],
          w3,
          z3
        }
      },
      Equal.cong(
        Tables.Table<VersionRecord>,
        Maybe<&2, VersionRecord>,
        y => Tables.Table.get(VersionRecord, y, r3),
        NodeState.versions(s3),
        VersionRecord.add(
          [
            Tables.Row{
              r3,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          NodeState.versions(s2)
        ),
        s3v
      ),
      add_new_find(
        r3,
        Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
        [v0],
        w3,
        z3,
        NodeState.versions(s2)
      )(taken_free(NodeState.versions(s2), r3)(ht3))
    )
    +g3r2 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s3), r2),
      Tables.Table.get(VersionRecord, NodeState.versions(s2), r2),
      Some{
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
          [v0],
          w2,
          z2
        }
      },
      Equal.trans(
        Maybe<&2, VersionRecord>,
        Tables.Table.get(VersionRecord, NodeState.versions(s3), r2),
        Tables.Table.get(
          VersionRecord,
          VersionRecord.add(
            [
              Tables.Row{
                r3,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            NodeState.versions(s2)
          ),
          r2
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(s2), r2),
        Equal.cong(
          Tables.Table<VersionRecord>,
          Maybe<&2, VersionRecord>,
          y => Tables.Table.get(VersionRecord, y, r2),
          NodeState.versions(s3),
          VersionRecord.add(
            [
              Tables.Row{
                r3,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            NodeState.versions(s2)
          ),
          s3v
        ),
        add1_other(
          NodeState.versions(s2),
          r3,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          },
          r2
        )(er3r2)
      ),
      g2r2
    )
    +g3v0 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s3), v0),
      Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      Equal.trans(
        Maybe<&2, VersionRecord>,
        Tables.Table.get(VersionRecord, NodeState.versions(s3), v0),
        Tables.Table.get(
          VersionRecord,
          VersionRecord.add(
            [
              Tables.Row{
                r3,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            NodeState.versions(s2)
          ),
          v0
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
        Equal.cong(
          Tables.Table<VersionRecord>,
          Maybe<&2, VersionRecord>,
          y => Tables.Table.get(VersionRecord, y, v0),
          NodeState.versions(s3),
          VersionRecord.add(
            [
              Tables.Row{
                r3,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            NodeState.versions(s2)
          ),
          s3v
        ),
        add1_other(
          NodeState.versions(s2),
          r3,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          },
          v0
        )(er3v0)
      ),
      g2v0
    )
    +hav = Equal.trans(
      Bool,
      Shared.List.has(~String, ~String.eq, Vers.ids(History.of(NodeState.versions(s3), r2)), r3),
      Shared.List.has(
        ~String,
        ~String.eq,
        Vers.ids(
          History.of(
            VersionRecord.add(
              [
                Tables.Row{
                  r3,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                    [v0],
                    w3,
                    z3
                  }
                }
              ],
              NodeState.versions(s2)
            ),
            r2
          )
        ),
        r3
      ),
      False{},
      Equal.cong(
        Tables.Table<VersionRecord>,
        Bool,
        y => Shared.List.has(~String, ~String.eq, Vers.ids(History.of(y, r2)), r3),
        NodeState.versions(s3),
        VersionRecord.add(
          [
            Tables.Row{
              r3,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          NodeState.versions(s2)
        ),
        s3v
      ),
      walk_avoid(
        History.links(
          Tables.Table.keys(
            VersionRecord,
            VersionRecord.add(
              [
                Tables.Row{
                  r3,
                  VersionRecord{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                    [v0],
                    w3,
                    z3
                  }
                }
              ],
              NodeState.versions(s2)
            )
          ),
          VersionRecord.add(
            [
              Tables.Row{
                r3,
                VersionRecord{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            NodeState.versions(s2)
          )
        ),
        [r2],
        [],
        r3,
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
          [v0],
          w3,
          z3
        },
        NodeState.versions(s2)
      )(
        (%Equal.sym(
          Bool,
          String.eq(r2, r3),
          False{},
          er2r3
        ): {
          List.any.if(u => Shared.List.has(~String, ~String.eq, [], r3), _) == False{}: Bool
        }; {==})
      )(
        Bools.Bool.or_false_right(
          VersionRecord.has(NodeState.versions(s2), r3),
          VersionRecord.named(
            Tables.Table.keys(VersionRecord, NodeState.versions(s2)),
            NodeState.versions(s2),
            r3
          )
        )(ht3)
      )
    )
    +hk3 = Equal.trans(
      Bool,
      Shared.List.has(
        ~String,
        ~String.eq,
        Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
        r3
      ),
      Maybe.is_some(&2, VersionRecord, Tables.Table.get(VersionRecord, NodeState.versions(s3), r3)),
      True{},
      Tables.Table.keys_get(VersionRecord, NodeState.versions(s3), r3),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Bool,
        y => Maybe.is_some(&2, VersionRecord, y),
        Tables.Table.get(VersionRecord, NodeState.versions(s3), r3),
        Some{
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        },
        g3r3
      )
    )
    +hbv1 = Equal.cong(
      Maybe<&2, VersionRecord>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        VersionRecord.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(VersionRecord, NodeState.versions(s1), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      g1v0
    )
    +hbv2 = Equal.cong(
      Maybe<&2, VersionRecord>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        VersionRecord.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(VersionRecord, NodeState.versions(s2), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      g2v0
    )
    +hbv3 = Equal.cong(
      Maybe<&2, VersionRecord>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        VersionRecord.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(VersionRecord, NodeState.versions(s3), v0),
      Some{VersionRecord{yb, yp, yw, yt}},
      g3v0
    )
    +hbr2 = Equal.trans(
      Tables.Table<List<&2, U32>>,
      Vers.blobs(NodeState.versions(s3), r2),
      Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
      Tables.Table.set(List<&2, U32>, yb, n1, x1),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Tables.Table<List<&2, U32>>,
        y => Maybe.default(
          &2,
          Tables.Table<List<&2, U32>>,
          VersionRecord.blobs.of(y),
          Tables.Table.new(List<&2, U32>)
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(s3), r2),
        Some{
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
            [v0],
            w2,
            z2
          }
        },
        g3r2
      ),
      Equal.cong(
        Tables.Table<List<&2, U32>>,
        Tables.Table<List<&2, U32>>,
        y => Tables.Table.set(List<&2, U32>, y, n1, x1),
        Vers.blobs(NodeState.versions(s1), v0),
        yb,
        hbv1
      )
    )
    +hbr3 = Equal.trans(
      Tables.Table<List<&2, U32>>,
      Vers.blobs(NodeState.versions(s3), r3),
      Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
      Tables.Table.set(List<&2, U32>, yb, n2, x2),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Tables.Table<List<&2, U32>>,
        y => Maybe.default(
          &2,
          Tables.Table<List<&2, U32>>,
          VersionRecord.blobs.of(y),
          Tables.Table.new(List<&2, U32>)
        ),
        Tables.Table.get(VersionRecord, NodeState.versions(s3), r3),
        Some{
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        },
        g3r3
      ),
      Equal.cong(
        Tables.Table<List<&2, U32>>,
        Tables.Table<List<&2, U32>>,
        y => Tables.Table.set(List<&2, U32>, y, n2, x2),
        Vers.blobs(NodeState.versions(s2), v0),
        yb,
        hbv2
      )
    )
    +hf3 = Equal.trans(
      List<&2, Tables.Row<VersionRecord>>,
      History.of(NodeState.versions(s3), r3),
      History.walk(1n+1n+f, [r3], [], NodeState.versions(s3)),
      Tables.Row{
        r3,
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
          [v0],
          w3,
          z3
        }
      }
        <> (
          Tables.Row{
            v0,
            VersionRecord{yb, yp, yw, yt}
          }
            <> History.walk(f, yp, [v0, r3], NodeState.versions(s3))
        ),
      Equal.cong(
        Nat,
        List<&2, Tables.Row<VersionRecord>>,
        y => History.walk(y, [r3], [], NodeState.versions(s3)),
        History.links(
          Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
          NodeState.versions(s3)
        ),
        1n+1n+f,
        hl
      ),
      hist_two(
        f,
        r3,
        v0,
        Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
        w3,
        z3,
        yb,
        yp,
        yw,
        yt,
        NodeState.versions(s3)
      )(g3r3)(er3v0)(g3v0)
    )
    +hf2 = Equal.trans(
      List<&2, Tables.Row<VersionRecord>>,
      History.of(NodeState.versions(s3), r2),
      History.walk(1n+1n+f, [r2], [], NodeState.versions(s3)),
      Tables.Row{
        r2,
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
          [v0],
          w2,
          z2
        }
      }
        <> (
          Tables.Row{
            v0,
            VersionRecord{yb, yp, yw, yt}
          }
            <> History.walk(f, yp, [v0, r2], NodeState.versions(s3))
        ),
      Equal.cong(
        Nat,
        List<&2, Tables.Row<VersionRecord>>,
        y => History.walk(y, [r2], [], NodeState.versions(s3)),
        History.links(
          Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
          NodeState.versions(s3)
        ),
        1n+1n+f,
        hl
      ),
      hist_two(
        f,
        r2,
        v0,
        Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
        w2,
        z2,
        yb,
        yp,
        yw,
        yt,
        NodeState.versions(s3)
      )(g3r2)(er2v0)(g3v0)
    )
    +hids = Equal.trans(
      Bool,
      Shared.List.has(~String, ~String.eq, Vers.ids(History.of(NodeState.versions(s3), r2)), v0),
      Shared.List.has(
        ~String,
        ~String.eq,
        Vers.ids(
          Tables.Row{
            r2,
            VersionRecord{
              Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
              [v0],
              w2,
              z2
            }
          }
            <> (
              Tables.Row{
                v0,
                VersionRecord{yb, yp, yw, yt}
              }
                <> History.walk(f, yp, [v0, r2], NodeState.versions(s3))
            )
        ),
        v0
      ),
      True{},
      Equal.cong(
        List<&2, Tables.Row<VersionRecord>>,
        Bool,
        y => Shared.List.has(~String, ~String.eq, Vers.ids(y), v0),
        History.of(NodeState.versions(s3), r2),
        Tables.Row{
          r2,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
            [v0],
            w2,
            z2
          }
        }
          <> (
            Tables.Row{
              v0,
              VersionRecord{yb, yp, yw, yt}
            }
              <> History.walk(f, yp, [v0, r2], NodeState.versions(s3))
          ),
        hf2
      ),
      ids_second(
        r2,
        v0,
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s1), v0), n1, x1),
          [v0],
          w2,
          z2
        },
        VersionRecord{yb, yp, yw, yt},
        History.walk(f, yp, [v0, r2], NodeState.versions(s3))
      )(er2v0)
    )
    +hf = Equal.trans(
      Maybe<&2, String>,
      Vers.first_in(
        History.of(NodeState.versions(s3), r3),
        Vers.ids(History.of(NodeState.versions(s3), r2))
      ),
      Vers.first_in(
        Tables.Row{
          r3,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        }
          <> (
            Tables.Row{
              v0,
              VersionRecord{yb, yp, yw, yt}
            }
              <> History.walk(f, yp, [v0, r3], NodeState.versions(s3))
          ),
        Vers.ids(History.of(NodeState.versions(s3), r2))
      ),
      Some{v0},
      Equal.cong(
        List<&2, Tables.Row<VersionRecord>>,
        Maybe<&2, String>,
        y => Vers.first_in(y, Vers.ids(History.of(NodeState.versions(s3), r2))),
        History.of(NodeState.versions(s3), r3),
        Tables.Row{
          r3,
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        }
          <> (
            Tables.Row{
              v0,
              VersionRecord{yb, yp, yw, yt}
            }
              <> History.walk(f, yp, [v0, r3], NodeState.versions(s3))
          ),
        hf3
      ),
      first_two(
        r3,
        v0,
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
          [v0],
          w3,
          z3
        },
        VersionRecord{yb, yp, yw, yt},
        History.walk(f, yp, [v0, r3], NodeState.versions(s3)),
        Vers.ids(History.of(NodeState.versions(s3), r2))
      )(hav)(hids)
    )
    +hmo = Equal.trans(
      Out,
      Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
      Merge.point(Some{r3}, s3, r4, w4, z4, b),
      Out{
        [
          Tables.Row{
            r4,
            VersionRecord{
              Merge.blobs(
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, yb),
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                      []
                    )
                  )
                ),
                Tables.Table.set(List<&2, U32>, yb, n1, x1),
                Tables.Table.set(List<&2, U32>, yb, n2, x2),
                yb
              ),
              [r2, r3],
              w4,
              z4
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s3),
          b,
          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
        ),
        NodeState.marks(s3),
        NodeState.groups(s3),
        NodeState.clashes(s3),
        [Logged.head(b, r4)],
        Merge.answer(Spec.Merge.Merged{r4})
      },
      Equal.cong(
        Maybe<&2, String>,
        Out,
        y => Merge.point(y, s3, r4, w4, z4, b),
        BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s3), c)),
        Some{r3},
        ha
      ),
      Equal.trans(
        Out,
        Merge.point(Some{r3}, s3, r4, w4, z4, b),
        Merge.branch(Some{BranchRecord{r2, o, e, 1n+k}}, s3, r4, w4, z4, r3, b),
        Out{
          [
            Tables.Row{
              r4,
              VersionRecord{
                Merge.blobs(
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, yb),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n1, x1)
                        ),
                        []
                      )
                    )
                  ),
                  Tables.Table.set(List<&2, U32>, yb, n1, x1),
                  Tables.Table.set(List<&2, U32>, yb, n2, x2),
                  yb
                ),
                [r2, r3],
                w4,
                z4
              }
            }
          ],
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s3),
            b,
            BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
          ),
          NodeState.marks(s3),
          NodeState.groups(s3),
          NodeState.clashes(s3),
          [Logged.head(b, r4)],
          Merge.answer(Spec.Merge.Merged{r4})
        },
        Equal.cong(
          Maybe<&2, BranchRecord>,
          Out,
          y => Merge.branch(y, s3, r4, w4, z4, r3, b),
          Tables.Table.get(BranchRecord, NodeState.branches(s3), b),
          Some{BranchRecord{r2, o, e, 1n+k}},
          hb3
        ),
        Equal.trans(
          Out,
          Merge.branch(Some{BranchRecord{r2, o, e, 1n+k}}, s3, r4, w4, z4, r3, b),
          Merge.owner(
            True{},
            VersionRecord.taken(NodeState.versions(s3), r4),
            s3,
            r4,
            w4,
            z4,
            r3,
            b,
            BranchRecord{r2, o, e, 1n+k}
          ),
          Out{
            [
              Tables.Row{
                r4,
                VersionRecord{
                  Merge.blobs(
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, yb),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n2, x2)
                        ),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n1, x1)
                          ),
                          []
                        )
                      )
                    ),
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    Tables.Table.set(List<&2, U32>, yb, n2, x2),
                    yb
                  ),
                  [r2, r3],
                  w4,
                  z4
                }
              }
            ],
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s3),
              b,
              BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
            ),
            NodeState.marks(s3),
            NodeState.groups(s3),
            NodeState.clashes(s3),
            [Logged.head(b, r4)],
            Merge.answer(Spec.Merge.Merged{r4})
          },
          Equal.cong(
            Bool,
            Out,
            y => Merge.owner(
              y,
              VersionRecord.taken(NodeState.versions(s3), r4),
              s3,
              r4,
              w4,
              z4,
              r3,
              b,
              BranchRecord{r2, o, e, 1n+k}
            ),
            Owner.of(s3, BranchRecord{r2, o, e, 1n+k}),
            True{},
            hown
          ),
          Equal.trans(
            Out,
            Merge.owner(
              True{},
              VersionRecord.taken(NodeState.versions(s3), r4),
              s3,
              r4,
              w4,
              z4,
              r3,
              b,
              BranchRecord{r2, o, e, 1n+k}
            ),
            Merge.owner(True{}, False{}, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
            Out{
              [
                Tables.Row{
                  r4,
                  VersionRecord{
                    Merge.blobs(
                      Strings.union(
                        Tables.Table.keys(List<&2, U32>, yb),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n2, x2)
                          ),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n1, x1)
                            ),
                            []
                          )
                        )
                      ),
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      yb
                    ),
                    [r2, r3],
                    w4,
                    z4
                  }
                }
              ],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s3),
                b,
                BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
              ),
              NodeState.marks(s3),
              NodeState.groups(s3),
              NodeState.clashes(s3),
              [Logged.head(b, r4)],
              Merge.answer(Spec.Merge.Merged{r4})
            },
            Equal.cong(
              Bool,
              Out,
              y => Merge.owner(True{}, y, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
              VersionRecord.taken(NodeState.versions(s3), r4),
              False{},
              ht4
            ),
            Equal.trans(
              Out,
              Merge.owner(True{}, False{}, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
              Merge.inside(False{}, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
              Out{
                [
                  Tables.Row{
                    r4,
                    VersionRecord{
                      Merge.blobs(
                        Strings.union(
                          Tables.Table.keys(List<&2, U32>, yb),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n2, x2)
                            ),
                            Strings.union(
                              Tables.Table.keys(
                                List<&2, U32>,
                                Tables.Table.set(List<&2, U32>, yb, n1, x1)
                              ),
                              []
                            )
                          )
                        ),
                        Tables.Table.set(List<&2, U32>, yb, n1, x1),
                        Tables.Table.set(List<&2, U32>, yb, n2, x2),
                        yb
                      ),
                      [r2, r3],
                      w4,
                      z4
                    }
                  }
                ],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s3),
                  b,
                  BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                ),
                NodeState.marks(s3),
                NodeState.groups(s3),
                NodeState.clashes(s3),
                [Logged.head(b, r4)],
                Merge.answer(Spec.Merge.Merged{r4})
              },
              Equal.cong(
                Bool,
                Out,
                y => Merge.inside(y, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
                Shared.List.has(
                  ~String,
                  ~String.eq,
                  Vers.ids(History.of(NodeState.versions(s3), r2)),
                  r3
                ),
                False{},
                hav
              ),
              Equal.trans(
                Out,
                Merge.inside(False{}, s3, r4, w4, z4, r3, b, BranchRecord{r2, o, e, 1n+k}),
                Merge.three(
                  s3,
                  r4,
                  w4,
                  z4,
                  r3,
                  Vers.blobs(NodeState.versions(s3), r2),
                  Vers.blobs(NodeState.versions(s3), r3),
                  Vers.blobs(NodeState.versions(s3), v0),
                  b,
                  BranchRecord{r2, o, e, 1n+k}
                ),
                Out{
                  [
                    Tables.Row{
                      r4,
                      VersionRecord{
                        Merge.blobs(
                          Strings.union(
                            Tables.Table.keys(List<&2, U32>, yb),
                            Strings.union(
                              Tables.Table.keys(
                                List<&2, U32>,
                                Tables.Table.set(List<&2, U32>, yb, n2, x2)
                              ),
                              Strings.union(
                                Tables.Table.keys(
                                  List<&2, U32>,
                                  Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                ),
                                []
                              )
                            )
                          ),
                          Tables.Table.set(List<&2, U32>, yb, n1, x1),
                          Tables.Table.set(List<&2, U32>, yb, n2, x2),
                          yb
                        ),
                        [r2, r3],
                        w4,
                        z4
                      }
                    }
                  ],
                  Tables.Table.set(
                    BranchRecord,
                    NodeState.branches(s3),
                    b,
                    BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                  ),
                  NodeState.marks(s3),
                  NodeState.groups(s3),
                  NodeState.clashes(s3),
                  [Logged.head(b, r4)],
                  Merge.answer(Spec.Merge.Merged{r4})
                },
                Equal.cong(
                  Maybe<&2, String>,
                  Out,
                  y => Merge.three(
                    s3,
                    r4,
                    w4,
                    z4,
                    r3,
                    Vers.blobs(NodeState.versions(s3), r2),
                    Vers.blobs(NodeState.versions(s3), r3),
                    Merge.base(s3, y),
                    b,
                    BranchRecord{r2, o, e, 1n+k}
                  ),
                  Vers.first_in(
                    History.of(NodeState.versions(s3), r3),
                    Vers.ids(History.of(NodeState.versions(s3), r2))
                  ),
                  Some{v0},
                  hf
                ),
                Equal.trans(
                  Out,
                  Merge.three(
                    s3,
                    r4,
                    w4,
                    z4,
                    r3,
                    Vers.blobs(NodeState.versions(s3), r2),
                    Vers.blobs(NodeState.versions(s3), r3),
                    Vers.blobs(NodeState.versions(s3), v0),
                    b,
                    BranchRecord{r2, o, e, 1n+k}
                  ),
                  Merge.three(
                    s3,
                    r4,
                    w4,
                    z4,
                    r3,
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    Vers.blobs(NodeState.versions(s3), r3),
                    Vers.blobs(NodeState.versions(s3), v0),
                    b,
                    BranchRecord{r2, o, e, 1n+k}
                  ),
                  Out{
                    [
                      Tables.Row{
                        r4,
                        VersionRecord{
                          Merge.blobs(
                            Strings.union(
                              Tables.Table.keys(List<&2, U32>, yb),
                              Strings.union(
                                Tables.Table.keys(
                                  List<&2, U32>,
                                  Tables.Table.set(List<&2, U32>, yb, n2, x2)
                                ),
                                Strings.union(
                                  Tables.Table.keys(
                                    List<&2, U32>,
                                    Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                  ),
                                  []
                                )
                              )
                            ),
                            Tables.Table.set(List<&2, U32>, yb, n1, x1),
                            Tables.Table.set(List<&2, U32>, yb, n2, x2),
                            yb
                          ),
                          [r2, r3],
                          w4,
                          z4
                        }
                      }
                    ],
                    Tables.Table.set(
                      BranchRecord,
                      NodeState.branches(s3),
                      b,
                      BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                    ),
                    NodeState.marks(s3),
                    NodeState.groups(s3),
                    NodeState.clashes(s3),
                    [Logged.head(b, r4)],
                    Merge.answer(Spec.Merge.Merged{r4})
                  },
                  Equal.cong(
                    Tables.Table<List<&2, U32>>,
                    Out,
                    y => Merge.three(
                      s3,
                      r4,
                      w4,
                      z4,
                      r3,
                      y,
                      Vers.blobs(NodeState.versions(s3), r3),
                      Vers.blobs(NodeState.versions(s3), v0),
                      b,
                      BranchRecord{r2, o, e, 1n+k}
                    ),
                    Vers.blobs(NodeState.versions(s3), r2),
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    hbr2
                  ),
                  Equal.trans(
                    Out,
                    Merge.three(
                      s3,
                      r4,
                      w4,
                      z4,
                      r3,
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Vers.blobs(NodeState.versions(s3), r3),
                      Vers.blobs(NodeState.versions(s3), v0),
                      b,
                      BranchRecord{r2, o, e, 1n+k}
                    ),
                    Merge.three(
                      s3,
                      r4,
                      w4,
                      z4,
                      r3,
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      Vers.blobs(NodeState.versions(s3), v0),
                      b,
                      BranchRecord{r2, o, e, 1n+k}
                    ),
                    Out{
                      [
                        Tables.Row{
                          r4,
                          VersionRecord{
                            Merge.blobs(
                              Strings.union(
                                Tables.Table.keys(List<&2, U32>, yb),
                                Strings.union(
                                  Tables.Table.keys(
                                    List<&2, U32>,
                                    Tables.Table.set(List<&2, U32>, yb, n2, x2)
                                  ),
                                  Strings.union(
                                    Tables.Table.keys(
                                      List<&2, U32>,
                                      Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                    ),
                                    []
                                  )
                                )
                              ),
                              Tables.Table.set(List<&2, U32>, yb, n1, x1),
                              Tables.Table.set(List<&2, U32>, yb, n2, x2),
                              yb
                            ),
                            [r2, r3],
                            w4,
                            z4
                          }
                        }
                      ],
                      Tables.Table.set(
                        BranchRecord,
                        NodeState.branches(s3),
                        b,
                        BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                      ),
                      NodeState.marks(s3),
                      NodeState.groups(s3),
                      NodeState.clashes(s3),
                      [Logged.head(b, r4)],
                      Merge.answer(Spec.Merge.Merged{r4})
                    },
                    Equal.cong(
                      Tables.Table<List<&2, U32>>,
                      Out,
                      y => Merge.three(
                        s3,
                        r4,
                        w4,
                        z4,
                        r3,
                        Tables.Table.set(List<&2, U32>, yb, n1, x1),
                        y,
                        Vers.blobs(NodeState.versions(s3), v0),
                        b,
                        BranchRecord{r2, o, e, 1n+k}
                      ),
                      Vers.blobs(NodeState.versions(s3), r3),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      hbr3
                    ),
                    Equal.trans(
                      Out,
                      Merge.three(
                        s3,
                        r4,
                        w4,
                        z4,
                        r3,
                        Tables.Table.set(List<&2, U32>, yb, n1, x1),
                        Tables.Table.set(List<&2, U32>, yb, n2, x2),
                        Vers.blobs(NodeState.versions(s3), v0),
                        b,
                        BranchRecord{r2, o, e, 1n+k}
                      ),
                      Merge.three(
                        s3,
                        r4,
                        w4,
                        z4,
                        r3,
                        Tables.Table.set(List<&2, U32>, yb, n1, x1),
                        Tables.Table.set(List<&2, U32>, yb, n2, x2),
                        yb,
                        b,
                        BranchRecord{r2, o, e, 1n+k}
                      ),
                      Out{
                        [
                          Tables.Row{
                            r4,
                            VersionRecord{
                              Merge.blobs(
                                Strings.union(
                                  Tables.Table.keys(List<&2, U32>, yb),
                                  Strings.union(
                                    Tables.Table.keys(
                                      List<&2, U32>,
                                      Tables.Table.set(List<&2, U32>, yb, n2, x2)
                                    ),
                                    Strings.union(
                                      Tables.Table.keys(
                                        List<&2, U32>,
                                        Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                      ),
                                      []
                                    )
                                  )
                                ),
                                Tables.Table.set(List<&2, U32>, yb, n1, x1),
                                Tables.Table.set(List<&2, U32>, yb, n2, x2),
                                yb
                              ),
                              [r2, r3],
                              w4,
                              z4
                            }
                          }
                        ],
                        Tables.Table.set(
                          BranchRecord,
                          NodeState.branches(s3),
                          b,
                          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                        ),
                        NodeState.marks(s3),
                        NodeState.groups(s3),
                        NodeState.clashes(s3),
                        [Logged.head(b, r4)],
                        Merge.answer(Spec.Merge.Merged{r4})
                      },
                      Equal.cong(
                        Tables.Table<List<&2, U32>>,
                        Out,
                        y => Merge.three(
                          s3,
                          r4,
                          w4,
                          z4,
                          r3,
                          Tables.Table.set(List<&2, U32>, yb, n1, x1),
                          Tables.Table.set(List<&2, U32>, yb, n2, x2),
                          y,
                          b,
                          BranchRecord{r2, o, e, 1n+k}
                        ),
                        Vers.blobs(NodeState.versions(s3), v0),
                        yb,
                        hbv3
                      ),
                      Equal.cong(
                        List<&2, String>,
                        Out,
                        y => Merge.result(
                          y,
                          s3,
                          r4,
                          w4,
                          z4,
                          r3,
                          b,
                          Merge.blobs(
                            Strings.union(
                              Tables.Table.keys(List<&2, U32>, yb),
                              Strings.union(
                                Tables.Table.keys(
                                  List<&2, U32>,
                                  Tables.Table.set(List<&2, U32>, yb, n2, x2)
                                ),
                                Strings.union(
                                  Tables.Table.keys(
                                    List<&2, U32>,
                                    Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                  ),
                                  []
                                )
                              )
                            ),
                            Tables.Table.set(List<&2, U32>, yb, n1, x1),
                            Tables.Table.set(List<&2, U32>, yb, n2, x2),
                            yb
                          ),
                          BranchRecord{r2, o, e, 1n+k}
                        ),
                        Merge.clashes(
                          Strings.union(
                            Tables.Table.keys(List<&2, U32>, yb),
                            Strings.union(
                              Tables.Table.keys(
                                List<&2, U32>,
                                Tables.Table.set(List<&2, U32>, yb, n2, x2)
                              ),
                              Strings.union(
                                Tables.Table.keys(
                                  List<&2, U32>,
                                  Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                ),
                                []
                              )
                            )
                          ),
                          Tables.Table.set(List<&2, U32>, yb, n1, x1),
                          Tables.Table.set(List<&2, U32>, yb, n2, x2),
                          yb
                        ),
                        [],
                        clashes_nil(
                          Strings.union(
                            Tables.Table.keys(List<&2, U32>, yb),
                            Strings.union(
                              Tables.Table.keys(
                                List<&2, U32>,
                                Tables.Table.set(List<&2, U32>, yb, n2, x2)
                              ),
                              Strings.union(
                                Tables.Table.keys(
                                  List<&2, U32>,
                                  Tables.Table.set(List<&2, U32>, yb, n1, x1)
                                ),
                                []
                              )
                            )
                          ),
                          yb,
                          n1,
                          x1,
                          n2,
                          x2
                        )(hne)
                      )
                    )
                  )
                )
              )
            )
          )
        )
      )
    )
    +ha4 = ask_step(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}, s4, a4)(hn4)(h4)
    +s4v = view_v(
      s3,
      r4,
      Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
      s4,
      a4,
      Out{
        [
          Tables.Row{
            r4,
            VersionRecord{
              Merge.blobs(
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, yb),
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                      []
                    )
                  )
                ),
                Tables.Table.set(List<&2, U32>, yb, n1, x1),
                Tables.Table.set(List<&2, U32>, yb, n2, x2),
                yb
              ),
              [r2, r3],
              w4,
              z4
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s3),
          b,
          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
        ),
        NodeState.marks(s3),
        NodeState.groups(s3),
        NodeState.clashes(s3),
        [Logged.head(b, r4)],
        Merge.answer(Spec.Merge.Merged{r4})
      }
    )(ha4)(hmo)
    +s4b = view_b(
      s3,
      r4,
      Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
      s4,
      a4,
      Out{
        [
          Tables.Row{
            r4,
            VersionRecord{
              Merge.blobs(
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, yb),
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                      []
                    )
                  )
                ),
                Tables.Table.set(List<&2, U32>, yb, n1, x1),
                Tables.Table.set(List<&2, U32>, yb, n2, x2),
                yb
              ),
              [r2, r3],
              w4,
              z4
            }
          }
        ],
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s3),
          b,
          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
        ),
        NodeState.marks(s3),
        NodeState.groups(s3),
        NodeState.clashes(s3),
        [Logged.head(b, r4)],
        Merge.answer(Spec.Merge.Merged{r4})
      }
    )(ha4)(hmo)
    +hd4 = Equal.trans(
      Maybe<&2, String>,
      BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s4), b)),
      BranchRecord.head.of(
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s3),
            b,
            BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
          ),
          b
        )
      ),
      Some{r4},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, String>,
        y => BranchRecord.head.of(Tables.Table.get(BranchRecord, y, b)),
        NodeState.branches(s4),
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s3),
          b,
          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
        ),
        s4b
      ),
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Maybe<&2, String>,
        y => BranchRecord.head.of(y),
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s3),
            b,
            BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
          ),
          b
        ),
        Some{BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)},
        Tables.Table.get_after_set(
          BranchRecord,
          NodeState.branches(s3),
          b,
          BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
        )
      )
    )
    +hg4 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s4), r4),
      Tables.Table.get(
        VersionRecord,
        VersionRecord.add(
          [
            Tables.Row{
              r4,
              VersionRecord{
                Merge.blobs(
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, yb),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n1, x1)
                        ),
                        []
                      )
                    )
                  ),
                  Tables.Table.set(List<&2, U32>, yb, n1, x1),
                  Tables.Table.set(List<&2, U32>, yb, n2, x2),
                  yb
                ),
                [r2, r3],
                w4,
                z4
              }
            }
          ],
          NodeState.versions(s3)
        ),
        r4
      ),
      Some{
        VersionRecord{
          Merge.blobs(
            Strings.union(
              Tables.Table.keys(List<&2, U32>, yb),
              Strings.union(
                Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                  []
                )
              )
            ),
            Tables.Table.set(List<&2, U32>, yb, n1, x1),
            Tables.Table.set(List<&2, U32>, yb, n2, x2),
            yb
          ),
          [r2, r3],
          w4,
          z4
        }
      },
      Equal.cong(
        Tables.Table<VersionRecord>,
        Maybe<&2, VersionRecord>,
        y => Tables.Table.get(VersionRecord, y, r4),
        NodeState.versions(s4),
        VersionRecord.add(
          [
            Tables.Row{
              r4,
              VersionRecord{
                Merge.blobs(
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, yb),
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n1, x1)
                        ),
                        []
                      )
                    )
                  ),
                  Tables.Table.set(List<&2, U32>, yb, n1, x1),
                  Tables.Table.set(List<&2, U32>, yb, n2, x2),
                  yb
                ),
                [r2, r3],
                w4,
                z4
              }
            }
          ],
          NodeState.versions(s3)
        ),
        s4v
      ),
      add_new_find(
        r4,
        Merge.blobs(
          Strings.union(
            Tables.Table.keys(List<&2, U32>, yb),
            Strings.union(
              Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
              Strings.union(
                Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                []
              )
            )
          ),
          Tables.Table.set(List<&2, U32>, yb, n1, x1),
          Tables.Table.set(List<&2, U32>, yb, n2, x2),
          yb
        ),
        [r2, r3],
        w4,
        z4,
        NodeState.versions(s3)
      )(taken_free(NodeState.versions(s3), r4)(ht4))
    )
    +hns1 = Strings.union_right(
      Tables.Table.keys(List<&2, U32>, yb),
      Strings.union(
        Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
        Strings.union(
          Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
          []
        )
      ),
      n1
    )(
      Strings.union_right(
        Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
        Strings.union(
          Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
          []
        ),
        n1
      )(
        Strings.union_left(
          Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
          [],
          n1
        )(
          Equal.trans(
            Bool,
            Shared.List.has(
              ~String,
              ~String.eq,
              Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
              n1
            ),
            Maybe.is_some(
              &2,
              List<&2, U32>,
              Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1), n1)
            ),
            True{},
            Tables.Table.keys_get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1), n1),
            Equal.cong(
              Maybe<&2, List<&2, U32>>,
              Bool,
              y => Maybe.is_some(&2, List<&2, U32>, y),
              Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1), n1),
              Some{x1},
              Tables.Table.get_after_set(List<&2, U32>, yb, n1, x1)
            )
          )
        )
      )
    )
    +hns2 = Strings.union_right(
      Tables.Table.keys(List<&2, U32>, yb),
      Strings.union(
        Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
        Strings.union(
          Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
          []
        )
      ),
      n2
    )(
      Strings.union_left(
        Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
        Strings.union(
          Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
          []
        ),
        n2
      )(
        Equal.trans(
          Bool,
          Shared.List.has(
            ~String,
            ~String.eq,
            Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
            n2
          ),
          Maybe.is_some(
            &2,
            List<&2, U32>,
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2), n2)
          ),
          True{},
          Tables.Table.keys_get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2), n2),
          Equal.cong(
            Maybe<&2, List<&2, U32>>,
            Bool,
            y => Maybe.is_some(&2, List<&2, U32>, y),
            Tables.Table.get(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2), n2),
            Some{x2},
            Tables.Table.get_after_set(List<&2, U32>, yb, n2, x2)
          )
        )
      )
    )
    (
      Equal.sym(
        Spec.Answer,
        Spec.Answer.Merge{Spec.Merge.Merged{r4}},
        a4,
        Equal.trans(
          Spec.Answer,
          Spec.Answer.Merge{Spec.Merge.Merged{r4}},
          Out.answer(Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b})),
          a4,
          Equal.cong(
            Out,
            Spec.Answer,
            y => Out.answer(y),
            Out{
              [
                Tables.Row{
                  r4,
                  VersionRecord{
                    Merge.blobs(
                      Strings.union(
                        Tables.Table.keys(List<&2, U32>, yb),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n2, x2)
                          ),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n1, x1)
                            ),
                            []
                          )
                        )
                      ),
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      yb
                    ),
                    [r2, r3],
                    w4,
                    z4
                  }
                }
              ],
              Tables.Table.set(
                BranchRecord,
                NodeState.branches(s3),
                b,
                BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
              ),
              NodeState.marks(s3),
              NodeState.groups(s3),
              NodeState.clashes(s3),
              [Logged.head(b, r4)],
              Merge.answer(Spec.Merge.Merged{r4})
            },
            Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
            Equal.sym(
              Out,
              Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
              Out{
                [
                  Tables.Row{
                    r4,
                    VersionRecord{
                      Merge.blobs(
                        Strings.union(
                          Tables.Table.keys(List<&2, U32>, yb),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n2, x2)
                            ),
                            Strings.union(
                              Tables.Table.keys(
                                List<&2, U32>,
                                Tables.Table.set(List<&2, U32>, yb, n1, x1)
                              ),
                              []
                            )
                          )
                        ),
                        Tables.Table.set(List<&2, U32>, yb, n1, x1),
                        Tables.Table.set(List<&2, U32>, yb, n2, x2),
                        yb
                      ),
                      [r2, r3],
                      w4,
                      z4
                    }
                  }
                ],
                Tables.Table.set(
                  BranchRecord,
                  NodeState.branches(s3),
                  b,
                  BranchRecord.moved(BranchRecord{r2, o, e, 1n+k}, r4)
                ),
                NodeState.marks(s3),
                NodeState.groups(s3),
                NodeState.clashes(s3),
                [Logged.head(b, r4)],
                Merge.answer(Spec.Merge.Merged{r4})
              },
              hmo
            )
          ),
          applied_answer(
            s3,
            r4,
            Step.of(s3, r4, w4, z4, Spec.Ask.Merge{Spec.Point.Head{c}, b}),
            s4,
            a4
          )(ha4)
        )
      ),
      (
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          NodeState.content(s4, n1, Spec.Point.Head{b}),
          Blob.find.of(
            VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), Some{r4})),
            n1
          ),
          Some{x1},
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, List<&2, U32>>,
            y => Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), y)),
              n1
            ),
            BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s4), b)),
            Some{r4},
            hd4
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), Some{r4})),
              n1
            ),
            Blob.find.of(
              VersionRecord.blobs.of(
                Some{
                  VersionRecord{
                    Merge.blobs(
                      Strings.union(
                        Tables.Table.keys(List<&2, U32>, yb),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n2, x2)
                          ),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n1, x1)
                            ),
                            []
                          )
                        )
                      ),
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      yb
                    ),
                    [r2, r3],
                    w4,
                    z4
                  }
                }
              ),
              n1
            ),
            Some{x1},
            Equal.cong(
              Maybe<&2, VersionRecord>,
              Maybe<&2, List<&2, U32>>,
              y => Blob.find.of(VersionRecord.blobs.of(y), n1),
              Tables.Table.get(VersionRecord, NodeState.versions(s4), r4),
              Some{
                VersionRecord{
                  Merge.blobs(
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, yb),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n2, x2)
                        ),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n1, x1)
                          ),
                          []
                        )
                      )
                    ),
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    Tables.Table.set(List<&2, U32>, yb, n2, x2),
                    yb
                  ),
                  [r2, r3],
                  w4,
                  z4
                }
              },
              hg4
            ),
            blobs_get(
              Strings.union(
                Tables.Table.keys(List<&2, U32>, yb),
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                    []
                  )
                )
              ),
              n1,
              x1,
              yb,
              n1,
              x1,
              n2,
              x2
            )(pick1(yb, n1, x1, n2, x2)(hne))(hns1)
          )
        ),
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          NodeState.content(s4, n2, Spec.Point.Head{b}),
          Blob.find.of(
            VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), Some{r4})),
            n2
          ),
          Some{x2},
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, List<&2, U32>>,
            y => Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), y)),
              n2
            ),
            BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s4), b)),
            Some{r4},
            hd4
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(
              VersionRecord.blobs.of(VersionRecord.find.of(NodeState.versions(s4), Some{r4})),
              n2
            ),
            Blob.find.of(
              VersionRecord.blobs.of(
                Some{
                  VersionRecord{
                    Merge.blobs(
                      Strings.union(
                        Tables.Table.keys(List<&2, U32>, yb),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n2, x2)
                          ),
                          Strings.union(
                            Tables.Table.keys(
                              List<&2, U32>,
                              Tables.Table.set(List<&2, U32>, yb, n1, x1)
                            ),
                            []
                          )
                        )
                      ),
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      yb
                    ),
                    [r2, r3],
                    w4,
                    z4
                  }
                }
              ),
              n2
            ),
            Some{x2},
            Equal.cong(
              Maybe<&2, VersionRecord>,
              Maybe<&2, List<&2, U32>>,
              y => Blob.find.of(VersionRecord.blobs.of(y), n2),
              Tables.Table.get(VersionRecord, NodeState.versions(s4), r4),
              Some{
                VersionRecord{
                  Merge.blobs(
                    Strings.union(
                      Tables.Table.keys(List<&2, U32>, yb),
                      Strings.union(
                        Tables.Table.keys(
                          List<&2, U32>,
                          Tables.Table.set(List<&2, U32>, yb, n2, x2)
                        ),
                        Strings.union(
                          Tables.Table.keys(
                            List<&2, U32>,
                            Tables.Table.set(List<&2, U32>, yb, n1, x1)
                          ),
                          []
                        )
                      )
                    ),
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    Tables.Table.set(List<&2, U32>, yb, n2, x2),
                    yb
                  ),
                  [r2, r3],
                  w4,
                  z4
                }
              },
              hg4
            ),
            blobs_get(
              Strings.union(
                Tables.Table.keys(List<&2, U32>, yb),
                Strings.union(
                  Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n2, x2)),
                  Strings.union(
                    Tables.Table.keys(List<&2, U32>, Tables.Table.set(List<&2, U32>, yb, n1, x1)),
                    []
                  )
                )
              ),
              n2,
              x2,
              yb,
              n1,
              x1,
              n2,
              x2
            )(pick2(yb, n1, x1, n2, x2)(hne))(hns2)
          )
        )
      )
    )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# mdk_core, once the walks have fuel for two steps
law mdk_core.fuel:
  for s: NodeState
  for s1: NodeState
  for s2: NodeState
  for s3: NodeState
  for s4: NodeState
  for a4: Spec.Answer
  for r1: String
  for w1: String
  for z1: String
  for r2: String
  for w2: String
  for z2: String
  for r3: String
  for w3: String
  for z3: String
  for r4: String
  for w4: String
  for z4: String
  for b: String
  for c: String
  for n1: String
  for n2: String
  for base1: Maybe<&2, String>
  for base2: Maybe<&2, String>
  for x1: List<&2, U32>
  for x2: List<&2, U32>
  for v0: String
  for v1: String
  for v2: String
  for o: String
  for e: Nat
  for k: Nat
  for yb: Tables.Table<List<&2, U32>>
  for yp: List<&2, String>
  for yw: String
  for yt: String
  for w: &f: Nat -> {
    History.links(
      Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
      NodeState.versions(s3)
    )
      == 1n+1n+f: Nat
  }
  {
    Spec.VendNode.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{Resources.Name{n1}, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{Resources.Name{n2}, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{v0, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(s),
      v0
    )
      == Some{VersionRecord{yb, yp, yw, yt}}: Maybe<&2, VersionRecord>
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {NodeState.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
    )

def mdk_core.fuel(
  s,
  s1,
  s2,
  s3,
  s4,
  a4,
  r1,
  w1,
  z1,
  r2,
  w2,
  z2,
  r3,
  w3,
  z3,
  r4,
  w4,
  z4,
  b,
  c,
  n1,
  n2,
  base1,
  base2,
  x1,
  x2,
  v0,
  v1,
  v2,
  o,
  e,
  k,
  yb,
  yp,
  yw,
  yt,
  w
):
  match w:
    case (f, hl):
      hn1 => hn2 => hn3 => hn4 => hne => h1 => h2 => h3 => h4 => hbs => hvs => mdk_fin(
        s,
        s1,
        s2,
        s3,
        s4,
        a4,
        r1,
        w1,
        z1,
        r2,
        w2,
        z2,
        r3,
        w3,
        z3,
        r4,
        w4,
        z4,
        b,
        c,
        n1,
        n2,
        base1,
        base2,
        x1,
        x2,
        v0,
        v1,
        v2,
        o,
        e,
        k,
        yb,
        yp,
        yw,
        yt,
        f
      )(hn1)(hn2)(hn3)(hn4)(hne)(h1)(h2)(h3)(h4)(hbs)(hvs)(hl)
# merge_disjoint_keeps_both, once b's record and v0's version are found
law mdk_core:
  for s: NodeState
  for s1: NodeState
  for s2: NodeState
  for s3: NodeState
  for s4: NodeState
  for a4: Spec.Answer
  for r1: String
  for w1: String
  for z1: String
  for r2: String
  for w2: String
  for z2: String
  for r3: String
  for w3: String
  for z3: String
  for r4: String
  for w4: String
  for z4: String
  for b: String
  for c: String
  for n1: String
  for n2: String
  for base1: Maybe<&2, String>
  for base2: Maybe<&2, String>
  for x1: List<&2, U32>
  for x2: List<&2, U32>
  for v0: String
  for v1: String
  for v2: String
  for o: String
  for e: Nat
  for k: Nat
  for yb: Tables.Table<List<&2, U32>>
  for yp: List<&2, String>
  for yw: String
  for yt: String
  {
    Spec.VendNode.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{Resources.Name{n1}, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{Resources.Name{n2}, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): NodeState
      & Spec.Answer
  } -> {
    Tables.Table.get(
      BranchRecord,
      NodeState.branches(s),
      b
    )
      == Some{BranchRecord{v0, o, e, k}}: Maybe<&2, BranchRecord>
  } -> {
    Tables.Table.get(
      VersionRecord,
      NodeState.versions(s),
      v0
    )
      == Some{VersionRecord{yb, yp, yw, yt}}: Maybe<&2, VersionRecord>
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {NodeState.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
    )

def mdk_core(
  s,
  s1,
  s2,
  s3,
  s4,
  a4,
  r1,
  w1,
  z1,
  r2,
  w2,
  z2,
  r3,
  w3,
  z3,
  r4,
  w4,
  z4,
  b,
  c,
  n1,
  n2,
  base1,
  base2,
  x1,
  x2,
  v0,
  v1,
  v2,
  o,
  e,
  k,
  yb,
  yp,
  yw,
  yt
):
  +hn1 => +hn2 => +hn3 => +hn4 => +hne => +h1 => +h2 => +h3 => +h4 => +hbs => +hvs =>
    +s = s
    +s1 = s1
    +s2 = s2
    +s3 = s3
    +s4 = s4
    +a4 = a4
    +r1 = r1
    +w1 = w1
    +z1 = z1
    +r2 = r2
    +w2 = w2
    +z2 = z2
    +r3 = r3
    +w3 = w3
    +z3 = z3
    +r4 = r4
    +w4 = w4
    +z4 = z4
    +b = b
    +c = c
    +n1 = n1
    +n2 = n2
    +base1 = base1
    +base2 = base2
    +x1 = x1
    +x2 = x2
    +v0 = v0
    +v1 = v1
    +v2 = v2
    +o = o
    +e = e
    +k = k
    +yb = yb
    +yp = yp
    +yw = yw
    +yt = yt
    +s3 = s3
    +r3 = r3
    +s1b = sb_vb(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +hcn = sb_none(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
    +ecb = Tables.Table.differ(
      BranchRecord,
      NodeState.branches(s),
      c,
      b
    )(
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Bool,
        z => Maybe.is_some(&2, BranchRecord, z),
        Tables.Table.get(BranchRecord, NodeState.branches(s), c),
        None{},
        hcn
      )
    )(
      Equal.cong(
        Maybe<&2, BranchRecord>,
        Bool,
        z => Maybe.is_some(&2, BranchRecord, z),
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        Some{BranchRecord{v0, o, e, k}},
        hbs
      )
    )
    +ebc = Strings.String.eq_flip(c, b)(ecb)
    +b1b = Equal.trans(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s1), b),
      Tables.Table.get(
        BranchRecord,
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n}
        ),
        b
      ),
      Some{BranchRecord{v0, o, e, k}},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, BranchRecord>,
        y => Tables.Table.get(BranchRecord, y, b),
        NodeState.branches(s1),
        Tables.Table.set(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n}
        ),
        s1b
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v0, NodeState.self(s), 0n, 0n}
          ),
          b
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(s), b),
        Some{BranchRecord{v0, o, e, k}},
        Tables.Table.set_keeps_other(
          BranchRecord,
          NodeState.branches(s),
          c,
          BranchRecord{v0, NodeState.self(s), 0n, 0n},
          b,
          ecb
        ),
        hbs
      )
    )
    +s2b = ws_vb(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +b2c = Equal.trans(
      Maybe<&2, BranchRecord>,
      Tables.Table.get(BranchRecord, NodeState.branches(s2), c),
      Tables.Table.get(
        BranchRecord,
        Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
        c
      ),
      Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
      Equal.cong(
        Tables.Table<BranchRecord>,
        Maybe<&2, BranchRecord>,
        y => Tables.Table.get(BranchRecord, y, c),
        NodeState.branches(s2),
        Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
        s2b
      ),
      Equal.trans(
        Maybe<&2, BranchRecord>,
        Tables.Table.get(
          BranchRecord,
          Tables.Table.set(BranchRecord, NodeState.branches(s1), b, BranchRecord{r2, o, e, 1n+k}),
          c
        ),
        Tables.Table.get(BranchRecord, NodeState.branches(s1), c),
        Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
        Tables.Table.set_keeps_other(
          BranchRecord,
          NodeState.branches(s1),
          b,
          BranchRecord{r2, o, e, 1n+k},
          c,
          ebc
        ),
        Equal.trans(
          Maybe<&2, BranchRecord>,
          Tables.Table.get(BranchRecord, NodeState.branches(s1), c),
          Tables.Table.get(
            BranchRecord,
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              c,
              BranchRecord{v0, NodeState.self(s), 0n, 0n}
            ),
            c
          ),
          Some{BranchRecord{v0, NodeState.self(s), 0n, 0n}},
          Equal.cong(
            Tables.Table<BranchRecord>,
            Maybe<&2, BranchRecord>,
            y => Tables.Table.get(BranchRecord, y, c),
            NodeState.branches(s1),
            Tables.Table.set(
              BranchRecord,
              NodeState.branches(s),
              c,
              BranchRecord{v0, NodeState.self(s), 0n, 0n}
            ),
            s1b
          ),
          Tables.Table.get_after_set(
            BranchRecord,
            NodeState.branches(s),
            c,
            BranchRecord{v0, NodeState.self(s), 0n, 0n}
          )
        )
      )
    )
    +s3v = ws_vv(
      s2,
      s3,
      r3,
      w3,
      z3,
      n2,
      c,
      base2,
      x2,
      v0,
      NodeState.self(s),
      0n,
      0n,
      v2
    )(hn3)(h3)(b2c)
    +ht3 = new_free(s2, r3)(hn3)
    +g3r3 = Equal.trans(
      Maybe<&2, VersionRecord>,
      Tables.Table.get(VersionRecord, NodeState.versions(s3), r3),
      Tables.Table.get(
        VersionRecord,
        VersionRecord.add(
          [
            Tables.Row{
              r3,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          NodeState.versions(s2)
        ),
        r3
      ),
      Some{
        VersionRecord{
          Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
          [v0],
          w3,
          z3
        }
      },
      Equal.cong(
        Tables.Table<VersionRecord>,
        Maybe<&2, VersionRecord>,
        y => Tables.Table.get(VersionRecord, y, r3),
        NodeState.versions(s3),
        VersionRecord.add(
          [
            Tables.Row{
              r3,
              VersionRecord{
                Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          NodeState.versions(s2)
        ),
        s3v
      ),
      add_new_find(
        r3,
        Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
        [v0],
        w3,
        z3,
        NodeState.versions(s2)
      )(taken_free(NodeState.versions(s2), r3)(ht3))
    )
    +hk3 = Equal.trans(
      Bool,
      Shared.List.has(
        ~String,
        ~String.eq,
        Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
        r3
      ),
      Maybe.is_some(&2, VersionRecord, Tables.Table.get(VersionRecord, NodeState.versions(s3), r3)),
      True{},
      Tables.Table.keys_get(VersionRecord, NodeState.versions(s3), r3),
      Equal.cong(
        Maybe<&2, VersionRecord>,
        Bool,
        y => Maybe.is_some(&2, VersionRecord, y),
        Tables.Table.get(VersionRecord, NodeState.versions(s3), r3),
        Some{
          VersionRecord{
            Tables.Table.set(List<&2, U32>, Vers.blobs(NodeState.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        },
        g3r3
      )
    )
    mdk_core.fuel(
      s,
      s1,
      s2,
      s3,
      s4,
      a4,
      r1,
      w1,
      z1,
      r2,
      w2,
      z2,
      r3,
      w3,
      z3,
      r4,
      w4,
      z4,
      b,
      c,
      n1,
      n2,
      base1,
      base2,
      x1,
      x2,
      v0,
      v1,
      v2,
      o,
      e,
      k,
      yb,
      yp,
      yw,
      yt,
      links_two(
        Tables.Table.keys(VersionRecord, NodeState.versions(s3)),
        NodeState.versions(s3),
        r3
      )(hk3)
    )(hn1)(hn2)(hn3)(hn4)(hne)(h1)(h2)(h3)(h4)(hbs)(hvs)

# merge_disjoint_keeps_both, by b's record (mb) and v0's version (mv)
law mdk_split:
  for mb: Maybe<&2, BranchRecord>
  for mv: Maybe<&2, VersionRecord>
  for s: NodeState
  for s1: NodeState
  for s2: NodeState
  for s3: NodeState
  for s4: NodeState
  for a4: Spec.Answer
  for r1: String
  for w1: String
  for z1: String
  for r2: String
  for w2: String
  for z2: String
  for r3: String
  for w3: String
  for z3: String
  for r4: String
  for w4: String
  for z4: String
  for b: String
  for c: String
  for n1: String
  for n2: String
  for base1: Maybe<&2, String>
  for base2: Maybe<&2, String>
  for x1: List<&2, U32>
  for x2: List<&2, U32>
  for v0: String
  for v1: String
  for v2: String
  {
    Tables.Table.get(BranchRecord, NodeState.branches(s), b) == mb: Maybe<&2, BranchRecord>
  } -> {
    Tables.Table.get(VersionRecord, NodeState.versions(s), v0) == mv: Maybe<&2, VersionRecord>
  } -> {
    Spec.VendNode.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.VendNode.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.VendNode.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{Resources.Name{n1}, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{Resources.Name{n2}, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): NodeState
      & Spec.Answer
  } -> {
    Spec.VendNode.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): NodeState
      & Spec.Answer
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {NodeState.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
    )

def mdk_split(
  mb,
  mv,
  s,
  s1,
  s2,
  s3,
  s4,
  a4,
  r1,
  w1,
  z1,
  r2,
  w2,
  z2,
  r3,
  w3,
  z3,
  r4,
  w4,
  z4,
  b,
  c,
  n1,
  n2,
  base1,
  base2,
  x1,
  x2,
  v0,
  v1,
  v2
):
  match mb mv:
    case None{} y:
      eb => ev => +hn1 => hn2 => hn3 => hn4 => hne => +h1 => h2 => h3 => h4 =>
        Empty.absurd(
          {
            a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
          }
            & (
              {
                NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
              }
                & {
                  NodeState.content(
                    s4,
                    n2,
                    Spec.Point.Head{b}
                  )
                    == Some{x2}: Maybe<&2, List<&2, U32>>
                }
            ),
          Maybes.Maybe.none_ne_some(
            String,
            v0,
            Equal.trans(
              Maybe<&2, String>,
              None{},
              BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
              Some{v0},
              Equal.sym(
                Maybe<&2, String>,
                BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
                None{},
                Equal.cong(
                  Maybe<&2, BranchRecord>,
                  Maybe<&2, String>,
                  y => BranchRecord.head.of(y),
                  Tables.Table.get(BranchRecord, NodeState.branches(s), b),
                  None{},
                  eb
                )
              ),
              sb_head(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
            )
          )
        )
    case Some{BranchRecord{h, o, e, k}} None{}:
      eb => ev => +hn1 => hn2 => hn3 => hn4 => hne => +h1 => h2 => h3 => h4 =>
        Empty.absurd(
          {
            a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
          }
            & (
              {
                NodeState.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
              }
                & {
                  NodeState.content(
                    s4,
                    n2,
                    Spec.Point.Head{b}
                  )
                    == Some{x2}: Maybe<&2, List<&2, U32>>
                }
            ),
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              VersionRecord.has(NodeState.versions(s), v0),
              True{},
              Equal.sym(
                Bool,
                VersionRecord.has(NodeState.versions(s), v0),
                False{},
                Equal.cong(
                  Maybe<&2, VersionRecord>,
                  Bool,
                  y => Maybe.is_some(&2, VersionRecord, y),
                  Tables.Table.get(VersionRecord, NodeState.versions(s), v0),
                  None{},
                  ev
                )
              ),
              sb_has(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
            )
          )
        )
    case Some{BranchRecord{+h, +o, +e, +k}} Some{VersionRecord{yb, yp, yw, yt}}:
      +eb => ev => +hn1 => hn2 => hn3 => hn4 => hne => +h1 => h2 => h3 => h4 =>
        +s = s
        +s1 = s1
        +r1 = r1
        +w1 = w1
        +z1 = z1
        +b = b
        +c = c
        +v0 = v0
        +hv0 = Maybes.Maybe.some_inj(
          String,
          h,
          v0,
          Equal.trans(
            Maybe<&2, String>,
            Some{h},
            BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
            Some{v0},
            Equal.sym(
              Maybe<&2, String>,
              BranchRecord.head.of(Tables.Table.get(BranchRecord, NodeState.branches(s), b)),
              Some{h},
              Equal.cong(
                Maybe<&2, BranchRecord>,
                Maybe<&2, String>,
                y => BranchRecord.head.of(y),
                Tables.Table.get(BranchRecord, NodeState.branches(s), b),
                Some{BranchRecord{h, o, e, k}},
                eb
              )
            ),
            sb_head(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
          )
        )
        mdk_core(
          s,
          s1,
          s2,
          s3,
          s4,
          a4,
          r1,
          w1,
          z1,
          r2,
          w2,
          z2,
          r3,
          w3,
          z3,
          r4,
          w4,
          z4,
          b,
          c,
          n1,
          n2,
          base1,
          base2,
          x1,
          x2,
          v0,
          v1,
          v2,
          o,
          e,
          k,
          yb,
          yp,
          yw,
          yt
        )(hn1)(hn2)(hn3)(hn4)(hne)(h1)(h2)(h3)(h4)((
            %hv0: {Tables.Table.get(BranchRecord, NodeState.branches(s), b) == Some{BranchRecord{_, o, e, k}}: Maybe<&2, BranchRecord>}
            eb))(ev)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a set-group that answers Set has set the group to its members
law sg_set:
  for cycle: Bool
  for s: NodeState
  for g: String
  for ms: List<&2, Spec.Member>
  for x: Nat
  {
    Out.answer(
      SetGroup.on(cycle, s, g, ms)
    )
      == Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}: Spec.Answer
  } -> {
    GroupRecord.members.got(
      Tables.Table.get(GroupRecord, Out.groups(SetGroup.on(cycle, s, g, ms)), g)
    )
      == Some{ms}: Maybe<&2, List<&2, Spec.Member>>
  }

def sg_set(cycle, s, g, ms, x):
  match cycle:
    case True{}:
      ha => Empty.absurd(
        {
          GroupRecord.members.got(
            Tables.Table.get(GroupRecord, Out.groups(SetGroup.on(True{}, s, g, ms)), g)
          )
            == Some{ms}: Maybe<&2, List<&2, Spec.Member>>
        },
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}},
            Spec.Answer.SetGroup{Spec.SetGroup.Set{x}},
            ha
          )
        )
      )
    case False{}:
      ha =>
        +s = s
        +g = g
        +ms = ms
        Equal.cong(
          Maybe<&2, GroupRecord>,
          Maybe<&2, List<&2, Spec.Member>>,
          y => GroupRecord.members.got(y),
          Tables.Table.get(
            GroupRecord,
            Tables.Table.set(
              GroupRecord,
              NodeState.groups(s),
              g,
              GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)}
            ),
            g
          ),
          Some{GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)}},
          Tables.Table.get_after_set(
            GroupRecord,
            NodeState.groups(s),
            g,
            GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)}
          )
        )

# a set-group, whatever it answers, leaves every other group
law sg_other:
  for cycle: Bool
  for s: NodeState
  for g: String
  for h: String
  for ms: List<&2, Spec.Member>
  {
    String.eq(g, h) == False{}: Bool
  } -> {
    GroupRecord.members.got(
      Tables.Table.get(GroupRecord, Out.groups(SetGroup.on(cycle, s, g, ms)), h)
    )
      == GroupRecord.members.got(
        Tables.Table.get(GroupRecord, NodeState.groups(s), h)
      ): Maybe<&2, List<&2, Spec.Member>>
  }

def sg_other(cycle, s, g, h, ms):
  match cycle:
    case True{}:
      e => {==}
    case False{}:
      e =>
        +s = s
        +g = g
        +h = h
        +ms = ms
        Equal.cong(
          Maybe<&2, GroupRecord>,
          Maybe<&2, List<&2, Spec.Member>>,
          y => GroupRecord.members.got(y),
          Tables.Table.get(
            GroupRecord,
            Tables.Table.set(
              GroupRecord,
              NodeState.groups(s),
              g,
              GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)}
            ),
            h
          ),
          Tables.Table.get(GroupRecord, NodeState.groups(s), h),
          Tables.Table.set_keeps_other(
            GroupRecord,
            NodeState.groups(s),
            g,
            GroupRecord{ms, GroupRecord.epoch.next(NodeState.groups(s), g)},
            h,
            e
          )
        )

# set_keeps_others, by whether the request was seen (found)
law keep_others_asked:
  for found: Maybe<&2, Seen>
  for s: NodeState
  for r: String
  for w: String
  for z: String
  for g: String
  for h: String
  for ms: List<&2, Spec.Member>
  for t: NodeState
  for a: Spec.Answer
  {
    VendNode.asked(found, s, r, w, z, Spec.Ask.SetGroup{g, ms}) == (t, a): NodeState & Spec.Answer
  } -> {
    String.eq(g, h) == False{}: Bool
  } -> {
    GroupRecord.members.got(
      Tables.Table.get(GroupRecord, NodeState.groups(t), h)
    )
      == GroupRecord.members.got(
        Tables.Table.get(GroupRecord, NodeState.groups(s), h)
      ): Maybe<&2, List<&2, Spec.Member>>
  }

def keep_others_asked(found, s, r, w, z, g, h, ms, t, a):
  match found:
    case Some{Seen{b, q}}:
      hask => e =>
        +s = s
        +h = h
        %Equal.cong(
          NodeState & Spec.Answer,
          NodeState,
          y => Pair.fst(NodeState, Spec.Answer, y),
          (s, b),
          (t, a),
          hask
        ): {
          GroupRecord.members.got(
            Tables.Table.get(GroupRecord, NodeState.groups(_), h)
          )
            == GroupRecord.members.got(
              Tables.Table.get(GroupRecord, NodeState.groups(s), h)
            ): Maybe<&2, List<&2, Spec.Member>>
        }
        {==}
    case None{}:
      hask => e =>
        +s = s
        +r = r
        +w = w
        +z = z
        +g = g
        +h = h
        +ms = ms
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}),
          t,
          a
        )(
          hask
        ): {
          GroupRecord.members.got(
            Tables.Table.get(GroupRecord, NodeState.groups(_), h)
          )
            == GroupRecord.members.got(
              Tables.Table.get(GroupRecord, NodeState.groups(s), h)
            ): Maybe<&2, List<&2, Spec.Member>>
        }
        %Equal.sym(
          Tables.Table<GroupRecord>,
          NodeState.groups(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}))
            )
          ),
          Out.groups(Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms})),
          groups_after_applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}))
        ): {
          GroupRecord.members.got(
            Tables.Table.get(GroupRecord, _, h)
          )
            == GroupRecord.members.got(
              Tables.Table.get(GroupRecord, NodeState.groups(s), h)
            ): Maybe<&2, List<&2, Spec.Member>>
        }
        sg_other(Cycle.has(NodeState.groups(s), g, ms), s, g, h, ms)(e)

# what the group that mg holds was set to is its members
law got_in:
  for mg: Maybe<&2, GroupRecord>
  for ms: List<&2, Spec.Member>
  {
    GroupRecord.members.got(mg) == Some{ms}: Maybe<&2, List<&2, Spec.Member>>
  } -> {GroupRecord.members.in(mg) == ms: List<&2, Spec.Member>}

def got_in(mg, ms):
  match mg:
    case None{}:
      h => Empty.absurd(
        {GroupRecord.members.in(None{}) == ms: List<&2, Spec.Member>},
        Maybes.Maybe.none_ne_some(List<&2, Spec.Member>, ms, h)
      )
    case Some{GroupRecord{l, e}}:
      h => Maybes.Maybe.some_inj(List<&2, Spec.Member>, l, ms, h)

law among_found.of:
  for m: Spec.Member
  for ms: List<&2, Spec.Member>
  for w: Spec.Member.Among(m, ms)
  {Shared.List.has(~Spec.Member, ~Member.same, ms, m) == True{}: Bool}

def among_found.of(m, ms, w):
  match w:
    case (ys, (zs, e)):
      %Equal.sym(
        List<&2, Spec.Member>,
        ms,
        List.append(&2, Spec.Member, ys, m <> zs),
        e
      ): {Shared.List.has(~Spec.Member, ~Member.same, _, m) == True{}: Bool}
      Shared.List.has_middle(~Spec.Member, ~Member.same, ~member_same_refl, ys, m, zs)

# a member among ms is found in ms
law among_found:
  for m: Spec.Member
  for ms: List<&2, Spec.Member>
  Spec.Member.Among(m, ms) -> {Shared.List.has(~Spec.Member, ~Member.same, ms, m) == True{}: Bool}

def among_found(m, ms):
  w => among_found.of(m, ms, w)

# a member found in ms is among ms, by where it was found
law found_among.of:
  for ms: List<&2, Spec.Member>
  for m: Spec.Member
  for w: &ys: List<
    &2,
    Spec.Member> -> &y: Spec.Member -> &zs: List<
    &2,
    Spec.Member> -> {
    ms == List.append(&2, Spec.Member, ys, y <> zs): List<&2, Spec.Member>
  }
    & {Member.same(y, m) == True{}: Bool}
  Spec.Member.Among(m, ms)

def found_among.of(ms, m, w):
  match w:
    case (ys, (y, (zs, (e1, e2)))):
      (ys, (zs, (
            %member_same_sound(y, m)(e2): {ms == List.append(&2, Spec.Member, ys, _ <> zs): List<&2, Spec.Member>}
            e1)))

law found_among:
  for ms: List<&2, Spec.Member>
  for m: Spec.Member
  {Shared.List.has(~Spec.Member, ~Member.same, ms, m) == True{}: Bool} -> Spec.Member.Among(m, ms)

def found_among(ms, m):
  +ms = ms
  +m = m
  h => found_among.of(ms, m, Shared.List.has_split(~Spec.Member, ~Member.same, ms, m)(h))

law of_found.of:
  for s: NodeState
  for g: String
  for x: Spec.Member
  for w: Spec.Member.Of(s, g, x)
  {
    Shared.List.has(
      ~Spec.Member,
      ~Member.same,
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      x
    )
      == True{}: Bool
  }

def of_found.of(s, g, x, w):
  match w:
    case (+ms, (eg, ha)):
      %Equal.sym(
        List<&2, Spec.Member>,
        GroupRecord.members.in(Tables.Table.get(GroupRecord, NodeState.groups(s), g)),
        ms,
        got_in(Tables.Table.get(GroupRecord, NodeState.groups(s), g), ms)(eg)
      ): {Shared.List.has(~Spec.Member, ~Member.same, _, x) == True{}: Bool}
      among_found(x, ms)(ha)

# a member of g is found among g's members
law of_found:
  for s: NodeState
  for g: String
  for x: Spec.Member
  Spec.Member.Of(
    s,
    g,
    x
  ) -> {
    Shared.List.has(
      ~Spec.Member,
      ~Member.same,
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      x
    )
      == True{}: Bool
  }

def of_found(s, g, x):
  w => of_found.of(s, g, x, w)

# a member found among g's members is a member of g: by what s holds for g (mg)
law of_from_found.at:
  for mg: Maybe<&2, GroupRecord>
  for s: NodeState
  for g: String
  for x: Spec.Member
  {
    Tables.Table.get(GroupRecord, NodeState.groups(s), g) == mg: Maybe<&2, GroupRecord>
  } -> {
    Shared.List.has(~Spec.Member, ~Member.same, GroupRecord.members.in(mg), x) == True{}: Bool
  } -> Spec.Member.Of(s, g, x)

def of_from_found.at(mg, s, g, x):
  match mg:
    case None{}:
      e => h => Empty.absurd(Spec.Member.Of(s, g, x), Shared.Bool.false_ne_true(h))
    case Some{GroupRecord{+ms, ep}}:
      e => h =>
        +s = s
        +g = g
        (
          ms,
          (
            Equal.cong(
              Maybe<&2, GroupRecord>,
              Maybe<&2, List<&2, Spec.Member>>,
              z => GroupRecord.members.got(z),
              Tables.Table.get(GroupRecord, NodeState.groups(s), g),
              Some{GroupRecord{ms, ep}},
              e
            ),
            found_among(ms, x)(h)
          )
        )

law of_from_found:
  for s: NodeState
  for g: String
  for x: Spec.Member
  {
    Shared.List.has(
      ~Spec.Member,
      ~Member.same,
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      x
    )
      == True{}: Bool
  } -> Spec.Member.Of(s, g, x)

def of_from_found(s, g, x):
  +s = s
  +g = g
  h => of_from_found.at(Tables.Table.get(GroupRecord, NodeState.groups(s), g), s, g, x)({==})(h)

# chain_path at a first group h, once the chain is taken apart
law chain_path.pair:
  for s: NodeState
  for g: String
  for h: String
  for r: List<&2, String>
  for m: Spec.Member
  for hc: Spec.Member.Of(s, g, Spec.Member.Group{h}) & Spec.VendNode.Chain(s, h, r, m)
  (
    Spec.VendNode.Chain(
      s,
      h,
      r,
      m
    ) -> {
      Reaches.Reach.path(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        GroupRecord.groups(r),
        GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{h}),
        NodeState.groups(s),
        m
      )
        == True{}: Bool
    }
  ) -> {
    Bool.and(
      Shared.List.has(
        ~Spec.Member,
        ~Member.same,
        GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
        Spec.Member.Group{h}
      ),
      Reaches.Reach.path(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        GroupRecord.groups(r),
        GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{h}),
        NodeState.groups(s),
        m
      )
    )
      == True{}: Bool
  }

def chain_path.pair(s, g, h, r, m, hc):
  match hc:
    case (ho, hr):
      ih =>
        +s = s
        +g = g
        +h = h
        %Equal.sym(
          Bool,
          Shared.List.has(
            ~Spec.Member,
            ~Member.same,
            GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
            Spec.Member.Group{h}
          ),
          True{},
          of_found(s, g, Spec.Member.Group{h})(ho)
        ): {
          Bool.and(
            _,
            Reaches.Reach.path(
              ~Spec.Member,
              ~Tables.Table<GroupRecord>,
              ~Member.same,
              ~GroupRecord.members.of,
              GroupRecord.groups(r),
              GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{h}),
              NodeState.groups(s),
              m
            )
          )
            == True{}: Bool
        }
        ih(hr)

# a chain of groups is a path of their members
law chain_path:
  for ps: List<&2, String>
  for s: NodeState
  for g: String
  for m: Spec.Member
  Spec.VendNode.Chain(
    s,
    g,
    ps,
    m
  ) -> {
    Reaches.Reach.path(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      GroupRecord.groups(ps),
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      NodeState.groups(s),
      m
    )
      == True{}: Bool
  }

def chain_path(ps, s, g, m):
  match ps:
    case Nil{}:
      hc => of_found(s, g, m)(hc)
    case Con{+h, +r}:
      hc =>
        +s = s
        +g = g
        +m = m
        chain_path.pair(s, g, h, r, m, hc)(chain_path(r, s, h, m))

# path_chain, once the rest of the path is a chain
law path_chain.cons:
  for s: NodeState
  for g: String
  for k: String
  for m: Spec.Member
  for ho: Spec.Member.Of(s, g, Spec.Member.Group{k})
  for w: &qs: List<&2, String> -> Spec.VendNode.Chain(s, k, qs, m)
  (&qs: List<&2, String> -> Spec.VendNode.Chain(s, g, qs, m))

def path_chain.cons(s, g, k, m, ho, w):
  match w:
    case (qs, c):
      (k <> qs, (ho, c))

# a path of members from g's members is a chain of groups
law path_chain:
  for ps: List<&2, Spec.Member>
  for s: NodeState
  for g: String
  for m: Spec.Member
  {
    Reaches.Reach.path(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ps,
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      NodeState.groups(s),
      m
    )
      == True{}: Bool
  } -> &qs: List<&2, String> -> Spec.VendNode.Chain(s, g, qs, m)

def path_chain(ps, s, g, m):
  match ps:
    case Nil{}:
      h => ([], of_from_found(s, g, m)(h))
    case Con{Spec.Member.VendNode{n}, +r}:
      +h =>
        +s = s
        +m = m
        Empty.absurd(
          &qs: List<&2, String> -> Spec.VendNode.Chain(s, g, qs, m),
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Reaches.Reach.path(
                ~Spec.Member,
                ~Tables.Table<GroupRecord>,
                ~Member.same,
                ~GroupRecord.members.of,
                r,
                [],
                NodeState.groups(s),
                m
              ),
              True{},
              Equal.sym(
                Bool,
                Reaches.Reach.path(
                  ~Spec.Member,
                  ~Tables.Table<GroupRecord>,
                  ~Member.same,
                  ~GroupRecord.members.of,
                  r,
                  [],
                  NodeState.groups(s),
                  m
                ),
                False{},
                Reaches.Reach.path_empty(
                  ~Spec.Member,
                  ~Tables.Table<GroupRecord>,
                  ~Member.same,
                  ~GroupRecord.members.of,
                  r,
                  NodeState.groups(s),
                  m
                )
              ),
              Bools.Bool.and_true_right(
                Shared.List.has(
                  ~Spec.Member,
                  ~Member.same,
                  GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
                  Spec.Member.VendNode{n}
                ),
                Reaches.Reach.path(
                  ~Spec.Member,
                  ~Tables.Table<GroupRecord>,
                  ~Member.same,
                  ~GroupRecord.members.of,
                  r,
                  [],
                  NodeState.groups(s),
                  m
                )
              )(h)
            )
          )
        )
    case Con{Spec.Member.Group{+k}, +r}:
      +h =>
        +s = s
        +g = g
        +m = m
        path_chain.cons(
          s,
          g,
          k,
          m,
          of_from_found(
            s,
            g,
            Spec.Member.Group{k}
          )(
            Bools.Bool.and_true_left(
              Shared.List.has(
                ~Spec.Member,
                ~Member.same,
                GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
                Spec.Member.Group{k}
              ),
              Reaches.Reach.path(
                ~Spec.Member,
                ~Tables.Table<GroupRecord>,
                ~Member.same,
                ~GroupRecord.members.of,
                r,
                GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{k}),
                NodeState.groups(s),
                m
              )
            )(h)
          ),
          path_chain(
            r,
            s,
            k,
            m
          )(
            Bools.Bool.and_true_right(
              Shared.List.has(
                ~Spec.Member,
                ~Member.same,
                GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
                Spec.Member.Group{k}
              ),
              Reaches.Reach.path(
                ~Spec.Member,
                ~Tables.Table<GroupRecord>,
                ~Member.same,
                ~GroupRecord.members.of,
                r,
                GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{k}),
                NodeState.groups(s),
                m
              )
            )(h)
          )
        )

# inside_has_chain, once the search's path is found
law inside_chain.of:
  for s: NodeState
  for g: String
  for m: Spec.Member
  for w: &ps: List<
    &2,
    Spec.Member> -> {
    Reaches.Reach.path(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ps,
      GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
      NodeState.groups(s),
      m
    )
      == True{}: Bool
  }
    & {
      Reaches.Reach.fits(
        Spec.Member,
        ps,
        List.length(&2, Spec.Member, GroupRecord.all(NodeState.groups(s)))
      )
        == True{}: Bool
    }
  (&qs: List<&2, String> -> Spec.VendNode.Chain(s, g, qs, m))

def inside_chain.of(s, g, m, w):
  match w:
    case (ps, (hp, hf)):
      path_chain(ps, s, g, m)(hp)

# a member that closes a cycle for g, as the search sees it, closes it as the
# spec says
law closer_of:
  for s: NodeState
  for g: String
  for y: Spec.Member
  {
    Bool.or(
      Member.same(y, Spec.Member.Group{g}),
      Reaches.Reach.in(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        ~GroupRecord.all,
        NodeState.groups(s),
        y,
        Spec.Member.Group{g}
      )
    )
      == True{}: Bool
  } -> Spec.Member.Closes(s, g, y)

def closer_of(s, g, y):
  match y:
    case Spec.Member.VendNode{n}:
      h =>
        +s = s
        +g = g
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Reaches.Reach.in(
              ~Spec.Member,
              ~Tables.Table<GroupRecord>,
              ~Member.same,
              ~GroupRecord.members.of,
              ~GroupRecord.all,
              NodeState.groups(s),
              Spec.Member.VendNode{n},
              Spec.Member.Group{g}
            ),
            True{},
            Equal.sym(
              Bool,
              Reaches.Reach.in(
                ~Spec.Member,
                ~Tables.Table<GroupRecord>,
                ~Member.same,
                ~GroupRecord.members.of,
                ~GroupRecord.all,
                NodeState.groups(s),
                Spec.Member.VendNode{n},
                Spec.Member.Group{g}
              ),
              False{},
              Reaches.Reach.go_nil(
                ~Spec.Member,
                ~Tables.Table<GroupRecord>,
                ~Member.same,
                ~GroupRecord.members.of,
                List.length(&2, Spec.Member, GroupRecord.all(NodeState.groups(s))),
                NodeState.groups(s),
                Spec.Member.Group{g}
              )
            ),
            h
          )
        )
    case Spec.Member.Group{h}:
      +h0 => hne =>
        +s = s
        +g = g
        %Strings.String.ne_eq(
          h,
          g
        )(
          hne
        ): {
          Bool.or(
            _,
            Reaches.Reach.in(
              ~Spec.Member,
              ~Tables.Table<GroupRecord>,
              ~Member.same,
              ~GroupRecord.members.of,
              ~GroupRecord.all,
              NodeState.groups(s),
              Spec.Member.Group{h},
              Spec.Member.Group{g}
            )
          )
            == True{}: Bool
        }
        h0

# closes_of for the group h, by whether h is g (b)
law closes_of.at:
  for b: Bool
  for s: NodeState
  for g: String
  for h: String
  {
    String.eq(h, g) == b: Bool
  } -> Spec.Member.Closes(
    s,
    g,
    Spec.Member.Group{h}
  ) -> {
    Bool.or(
      b,
      Reaches.Reach.in(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        ~GroupRecord.all,
        NodeState.groups(s),
        Spec.Member.Group{h},
        Spec.Member.Group{g}
      )
    )
      == True{}: Bool
  }

def closes_of.at(b, s, g, h):
  match b:
    case True{}:
      e => hc => {==}
    case False{}:
      +e => hc =>
        +g = g
        +h = h
        hc(
          q => Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              String.eq(h, g),
              True{},
              Equal.sym(Bool, String.eq(h, g), False{}, e),
              (
                %Equal.sym(String, h, g, q): {String.eq(_, g) == True{}: Bool}
                Strings.String.eq_refl(g))
            )
          )
        )

# a member that closes a cycle as the spec says closes it for the search
law closes_of:
  for s: NodeState
  for g: String
  for y: Spec.Member
  Spec.Member.Closes(
    s,
    g,
    y
  ) -> {
    Bool.or(
      Member.same(y, Spec.Member.Group{g}),
      Reaches.Reach.in(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        ~GroupRecord.all,
        NodeState.groups(s),
        y,
        Spec.Member.Group{g}
      )
    )
      == True{}: Bool
  }

def closes_of(s, g, y):
  match y:
    case Spec.Member.VendNode{n}:
      hc => Empty.absurd(
        {
          Bool.or(
            Member.same(Spec.Member.VendNode{n}, Spec.Member.Group{g}),
            Reaches.Reach.in(
              ~Spec.Member,
              ~Tables.Table<GroupRecord>,
              ~Member.same,
              ~GroupRecord.members.of,
              ~GroupRecord.all,
              NodeState.groups(s),
              Spec.Member.VendNode{n},
              Spec.Member.Group{g}
            )
          )
            == True{}: Bool
        },
        hc
      )
    case Spec.Member.Group{+h}:
      hc =>
        +g = g
        closes_of.at(String.eq(h, g), s, g, h)({==})(hc)

# a set-group that answers Cycle found a member that closes one
law sg_cycle:
  for cycle: Bool
  for s: NodeState
  for g: String
  for ms: List<&2, Spec.Member>
  {
    Out.answer(
      SetGroup.on(cycle, s, g, ms)
    )
      == Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}}: Spec.Answer
  } -> {cycle == True{}: Bool}

def sg_cycle(cycle, s, g, ms):
  match cycle:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Bool.false_ne_true(
          Answer.clash(
            Spec.Answer.SetGroup{Spec.SetGroup.Set{GroupRecord.epoch.next(NodeState.groups(s), g)}},
            Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}},
            h
          )
        )
      )

# cycle_has_closer, once the closing member is found
law closer_found.of:
  for s: NodeState
  for g: String
  for ms: List<&2, Spec.Member>
  for w: &pre: List<
    &2,
    Spec.Member> -> &y: Spec.Member -> &post: List<
    &2,
    Spec.Member> -> {
    ms == List.append(&2, Spec.Member, pre, y <> post): List<&2, Spec.Member>
  }
    & {
      Bool.or(
        Member.same(y, Spec.Member.Group{g}),
        Reaches.Reach.in(
          ~Spec.Member,
          ~Tables.Table<GroupRecord>,
          ~Member.same,
          ~GroupRecord.members.of,
          ~GroupRecord.all,
          NodeState.groups(s),
          y,
          Spec.Member.Group{g}
        )
      )
        == True{}: Bool
    }
  (&m: Spec.Member -> Spec.Member.Among(m, ms) & Spec.Member.Closes(s, g, m))

def closer_found.of(s, g, ms, w):
  match w:
    case (pre, (+y, (post, (e1, e2)))):
      (y, ((pre, (post, e1)), closer_of(s, g, y)(e2)))

# a member among ms that closes a cycle makes the set-group find one
law closer_among.of:
  for s: NodeState
  for g: String
  for ms: List<&2, Spec.Member>
  for m: Spec.Member
  for w: Spec.Member.Among(m, ms)
  Spec.Member.Closes(s, g, m) -> {Cycle.has(NodeState.groups(s), g, ms) == True{}: Bool}

def closer_among.of(s, g, ms, m, w):
  match w:
    case (ys, (zs, e)):
      hc =>
        +s = s
        +g = g
        +m = m
        %Equal.sym(
          List<&2, Spec.Member>,
          ms,
          List.append(&2, Spec.Member, ys, m <> zs),
          e
        ): {Cycle.has(NodeState.groups(s), g, _) == True{}: Bool}
        Reaches.Reach.closes_middle(
          ~Spec.Member,
          ~Tables.Table<GroupRecord>,
          ~Member.same,
          ~GroupRecord.members.of,
          ~GroupRecord.all,
          NodeState.groups(s),
          Spec.Member.Group{g},
          ys,
          m,
          zs
        )(closes_of(s, g, m)(hc))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a member is EQ to itself
law member_order_refl:
  for a: Spec.Member
  {Member.order(a, a) == EQ{}: Cmp}

def member_order_refl(a):
  match a:
    case Spec.Member.VendNode{x}:
      Strings.String.order_refl(x)
    case Spec.Member.Group{x}:
      Strings.String.order_refl(x)

# comparing members the other way round flips the order
law member_order_swap:
  for a: Spec.Member
  for b: Spec.Member
  {Member.order(b, a) == Cmps.Cmp.flip(Member.order(a, b)): Cmp}

def member_order_swap(a, b):
  match a b:
    case Spec.Member.VendNode{x} Spec.Member.VendNode{y}:
      Strings.String.order_swap(x, y, EQ{})
    case Spec.Member.VendNode{x} Spec.Member.Group{y}:
      {==}
    case Spec.Member.Group{x} Spec.Member.VendNode{y}:
      {==}
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      Strings.String.order_swap(x, y, EQ{})

# members that compare EQ are the same
law member_order_sound:
  for a: Spec.Member
  for b: Spec.Member
  {Member.order(a, b) == EQ{}: Cmp} -> {a == b: Spec.Member}

def member_order_sound(a, b):
  match a b:
    case Spec.Member.VendNode{x} Spec.Member.VendNode{y}:
      h => Equal.cong(
        String,
        Spec.Member,
        z => Spec.Member.VendNode{z},
        x,
        y,
        Strings.String.order_sound(x, y)(h)
      )
    case Spec.Member.VendNode{x} Spec.Member.Group{y}:
      h => Empty.absurd(
        {Spec.Member.VendNode{x} == Spec.Member.Group{y}: Spec.Member},
        Cmps.Cmp.ne_eq(LT{}, Unit{}, h)
      )
    case Spec.Member.Group{x} Spec.Member.VendNode{y}:
      h => Empty.absurd(
        {Spec.Member.Group{x} == Spec.Member.VendNode{y}: Spec.Member},
        Cmps.Cmp.ne_eq(GT{}, Unit{}, h)
      )
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      h => Equal.cong(
        String,
        Spec.Member,
        z => Spec.Member.Group{z},
        x,
        y,
        Strings.String.order_sound(x, y)(h)
      )

# a group's stamp is EQ to itself
law grp_stamp_refl:
  for x: GroupRecord
  {GroupRecord.stamp.cmp(x, x) == EQ{}: Cmp}

def grp_stamp_refl(x):
  match x:
    case GroupRecord{ms, e}:
      %Equal.sym(
        Cmp,
        Nat.cmp(e, e),
        EQ{},
        Nats.Nat.cmp_refl(e)
      ): {Cmps.Cmp.then(_, Cmps.List.order(~Spec.Member, ~Member.order, ms, ms)) == EQ{}: Cmp}
      Cmps.List.order_refl(~Spec.Member, ~Member.order, ~member_order_refl, ms)

# comparing group stamps the other way round flips the order
law grp_stamp_swap:
  for x: GroupRecord
  for y: GroupRecord
  {GroupRecord.stamp.cmp(y, x) == Cmps.Cmp.flip(GroupRecord.stamp.cmp(x, y)): Cmp}

def grp_stamp_swap(x, y):
  match x y:
    case GroupRecord{+m1, +e1} GroupRecord{+m2, +e2}:
      %Equal.sym(
        Cmp,
        Cmps.List.order(~Spec.Member, ~Member.order, m2, m1),
        Cmps.Cmp.flip(Cmps.List.order(~Spec.Member, ~Member.order, m1, m2)),
        Cmps.List.order_swap(~Spec.Member, ~Member.order, ~member_order_swap, m1, m2)
      ): {
        Cmps.Cmp.then(
          Nat.cmp(e2, e1),
          _
        )
          == Cmps.Cmp.flip(
            Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.List.order(~Spec.Member, ~Member.order, m1, m2))
          ): Cmp
      }
      %Equal.sym(
        Cmp,
        Nat.cmp(e2, e1),
        Cmps.Cmp.flip(Nat.cmp(e1, e2)),
        Nats.Nat.cmp_swap(e1, e2)
      ): {
        Cmps.Cmp.then(
          _,
          Cmps.Cmp.flip(Cmps.List.order(~Spec.Member, ~Member.order, m1, m2))
        )
          == Cmps.Cmp.flip(
            Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.List.order(~Spec.Member, ~Member.order, m1, m2))
          ): Cmp
      }
      Cmps.Cmp.then_flip(Nat.cmp(e1, e2), Cmps.List.order(~Spec.Member, ~Member.order, m1, m2))

# groups whose stamps compare EQ have the same members
law grp_stamp_eq:
  for x: GroupRecord
  for y: GroupRecord
  {
    GroupRecord.stamp.cmp(x, y) == EQ{}: Cmp
  } -> {GroupRecord.members(x) == GroupRecord.members(y): List<&2, Spec.Member>}

def grp_stamp_eq(x, y):
  match x y:
    case GroupRecord{+m1, e1} GroupRecord{+m2, e2}:
      h => Cmps.List.order_sound(
        ~Spec.Member,
        ~Member.order,
        ~member_order_sound,
        m1,
        m2
      )(
        Cmps.Cmp.then_eq_right(
          Nat.cmp(e1, e2),
          Cmps.List.order(~Spec.Member, ~Member.order, m1, m2)
        )(h)
      )

# a sync's pick for the group h, by the order c0 of the node's own group and
# theirs (x), leaves every other group
law grp_pick_other:
  for c0: Cmp
  for gs: Tables.Table<GroupRecord>
  for ns: List<&2, Logged>
  for h: String
  for x: GroupRecord
  for c: String
  for e: {String.eq(h, c) == False{}: Bool}
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.pick(c0, h, x, Kept{gs, ns})),
      c
    )
      == Tables.Table.get(GroupRecord, gs, c): Maybe<&2, GroupRecord>
  }

def grp_pick_other(c0, gs, ns, h, x, c, e):
  match c0:
    case LT{}:
      match x:
        case GroupRecord{ms, ep}:
          Tables.Table.set_keeps_other(GroupRecord, gs, h, GroupRecord{ms, ep}, c, e)
    case EQ{}:
      {==}
    case GT{}:
      {==}

# a sync's meeting of the group h leaves every other group
law grp_at_other:
  for m: Maybe<&2, GroupRecord>
  for gs: Tables.Table<GroupRecord>
  for ns: List<&2, Logged>
  for h: String
  for x: GroupRecord
  for c: String
  for e: {String.eq(h, c) == False{}: Bool}
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.at(m, h, x, Kept{gs, ns})),
      c
    )
      == Tables.Table.get(GroupRecord, gs, c): Maybe<&2, GroupRecord>
  }

def grp_at_other(m, gs, ns, h, x, c, e):
  match m:
    case None{}:
      grp_pick_other(LT{}, gs, ns, h, x, c, e)
    case Some{mine}:
      +x = x
      grp_pick_other(GroupRecord.stamp.cmp(mine, x), gs, ns, h, x, c, e)

# a sync's pick for the group h, by the order c0 of the node's own group
# (mine) and theirs (x), holds the winner
law grp_pick_same:
  for c0: Cmp
  for mine: GroupRecord
  for gs: Tables.Table<GroupRecord>
  for ns: List<&2, Logged>
  for h: String
  for x: GroupRecord
  for em: {Tables.Table.get(GroupRecord, gs, h) == Some{mine}: Maybe<&2, GroupRecord>}
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.pick(c0, h, x, Kept{gs, ns})),
      h
    )
      == Some{Orders.Order.by(GroupRecord, c0, mine, x)}: Maybe<&2, GroupRecord>
  }

def grp_pick_same(c0, mine, gs, ns, h, x, em):
  match c0:
    case LT{}:
      match x:
        case GroupRecord{ms, ep}:
          Tables.Table.get_after_set(GroupRecord, gs, h, GroupRecord{ms, ep})
    case EQ{}:
      em
    case GT{}:
      em

# a sync's meeting of the group h, whose own group m is, holds the winner
law grp_at_same:
  for m: Maybe<&2, GroupRecord>
  for gs: Tables.Table<GroupRecord>
  for ns: List<&2, Logged>
  for h: String
  for x: GroupRecord
  for em: {Tables.Table.get(GroupRecord, gs, h) == m: Maybe<&2, GroupRecord>}
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.at(m, h, x, Kept{gs, ns})),
      h
    )
      == Some{Orders.Order.pick(~GroupRecord, ~GroupRecord.stamp.cmp, m, x)}: Maybe<&2, GroupRecord>
  }

def grp_at_same(m, gs, ns, h, x, em):
  match m:
    case None{}:
      match x:
        case GroupRecord{ms, ep}:
          Tables.Table.get_after_set(GroupRecord, gs, h, GroupRecord{ms, ep})
    case Some{+mine}:
      +x = x
      grp_pick_same(GroupRecord.stamp.cmp(mine, x), mine, gs, ns, h, x, em)

# a sync's meeting of the group h, by whether h is c (hit), is an order step
law grp_at_find:
  for hit: Bool
  for gs: Tables.Table<GroupRecord>
  for ns: List<&2, Logged>
  for h: String
  for x: GroupRecord
  for c: String
  {
    String.eq(h, c) == hit: Bool
  } -> {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.at(Tables.Table.get(GroupRecord, gs, h), h, x, Kept{gs, ns})),
      c
    )
      == Orders.Order.step(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        hit,
        Some{x},
        Tables.Table.get(GroupRecord, gs, c)
      ): Maybe<&2, GroupRecord>
  }

def grp_at_find(hit, gs, ns, h, x, c):
  match hit:
    case True{}:
      e =>
        +gs = gs
        +h = h
        +x = x
        %Strings.String.eq_sound(
          h,
          c
        )(
          e
        ): {
          Tables.Table.get(
            GroupRecord,
            Kept.groups(Sync.group.at(Tables.Table.get(GroupRecord, gs, h), h, x, Kept{gs, ns})),
            _
          )
            == Some{
              Orders.Order.pick(
                ~GroupRecord,
                ~GroupRecord.stamp.cmp,
                Tables.Table.get(GroupRecord, gs, _),
                x
              )
            }: Maybe<&2, GroupRecord>
        }
        grp_at_same(Tables.Table.get(GroupRecord, gs, h), gs, ns, h, x, {==})
    case False{}:
      e =>
        +gs = gs
        +h = h
        grp_at_other(Tables.Table.get(GroupRecord, gs, h), gs, ns, h, x, c, e)

# a sync's meeting of the group h, with the value f, is an order step
law grp_seen_find:
  for h: String
  for f: Maybe<&2, GroupRecord>
  for k: Kept
  for c: String
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.group.seen(h, f, k)),
      c
    )
      == Orders.Order.step(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        String.eq(h, c),
        f,
        Tables.Table.get(GroupRecord, Kept.groups(k), c)
      ): Maybe<&2, GroupRecord>
  }

def grp_seen_find(h, f, k, c):
  match f k:
    case None{} z:
      +c = c
      Equal.sym(
        Maybe<&2, GroupRecord>,
        Orders.Order.step(
          ~GroupRecord,
          ~GroupRecord.stamp.cmp,
          String.eq(h, c),
          None{},
          Tables.Table.get(GroupRecord, Kept.groups(z), c)
        ),
        Tables.Table.get(GroupRecord, Kept.groups(z), c),
        Orders.Order.step_none(
          ~GroupRecord,
          ~GroupRecord.stamp.cmp,
          String.eq(h, c),
          Tables.Table.get(GroupRecord, Kept.groups(z), c)
        )
      )
    case Some{x} Kept{gs, ns}:
      +h = h
      +c = c
      grp_at_find(String.eq(h, c), gs, ns, h, x, c)({==})

# a sync's group pass is an order fold
law grp_fold_find:
  for ks: List<&2, String>
  for full: Tables.Table<GroupRecord>
  for k: Kept
  for c: String
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.groups(ks, full, k)),
      c
    )
      == Orders.Order.fold(
        ~GroupRecord,
        ~Tables.Table<GroupRecord>,
        ~GroupRecord.stamp.cmp,
        ~(t => k => Tables.Table.get(GroupRecord, t, k)),
        ks,
        full,
        c,
        Tables.Table.get(GroupRecord, Kept.groups(k), c)
      ): Maybe<&2, GroupRecord>
  }

def grp_fold_find(ks, full, k, c):
  match ks:
    case Nil{}:
      {==}
    case Con{+h, r}:
      +full = full
      +k = k
      +c = c
      %grp_seen_find(
        h,
        Tables.Table.get(GroupRecord, full, h),
        k,
        c
      ): {
        Tables.Table.get(
          GroupRecord,
          Kept.groups(
            Sync.groups(r, full, Sync.group.seen(h, Tables.Table.get(GroupRecord, full, h), k))
          ),
          c
        )
          == Orders.Order.fold(
            ~GroupRecord,
            ~Tables.Table<GroupRecord>,
            ~GroupRecord.stamp.cmp,
            ~(t => k => Tables.Table.get(GroupRecord, t, k)),
            r,
            full,
            c,
            _
          ): Maybe<&2, GroupRecord>
      }
      grp_fold_find(r, full, Sync.group.seen(h, Tables.Table.get(GroupRecord, full, h), k), c)

# after a sync's group pass, a group is the winner of the node's own and the
# other node's
law sync_groups_find:
  for full: Tables.Table<GroupRecord>
  for k: Kept
  for c: String
  {
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.groups(Tables.Table.keys(GroupRecord, full), full, k)),
      c
    )
      == Orders.Order.join(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        Tables.Table.get(GroupRecord, Kept.groups(k), c),
        Tables.Table.get(GroupRecord, full, c)
      ): Maybe<&2, GroupRecord>
  }

def sync_groups_find(full, k, c):
  +full = full
  +k = k
  +c = c
  Equal.trans(
    Maybe<&2, GroupRecord>,
    Tables.Table.get(
      GroupRecord,
      Kept.groups(Sync.groups(Tables.Table.keys(GroupRecord, full), full, k)),
      c
    ),
    Orders.Order.fold(
      ~GroupRecord,
      ~Tables.Table<GroupRecord>,
      ~GroupRecord.stamp.cmp,
      ~(t => k => Tables.Table.get(GroupRecord, t, k)),
      Tables.Table.keys(GroupRecord, full),
      full,
      c,
      Tables.Table.get(GroupRecord, Kept.groups(k), c)
    ),
    Orders.Order.join(
      ~GroupRecord,
      ~GroupRecord.stamp.cmp,
      Tables.Table.get(GroupRecord, Kept.groups(k), c),
      Tables.Table.get(GroupRecord, full, c)
    ),
    grp_fold_find(Tables.Table.keys(GroupRecord, full), full, k, c),
    Orders.Order.fold_all(
      ~GroupRecord,
      ~Tables.Table<GroupRecord>,
      ~GroupRecord.stamp.cmp,
      ~(t => k => Tables.Table.get(GroupRecord, t, k)),
      y => grp_stamp_refl(y),
      Tables.Table.keys(GroupRecord, full),
      full,
      c,
      Tables.Table.get(GroupRecord, Kept.groups(k), c),
      h => Tables.Table.none_of(
        GroupRecord,
        Tables.Table.get(GroupRecord, full, c)
      )(
        Equal.trans(
          Bool,
          Maybe.is_some(&2, GroupRecord, Tables.Table.get(GroupRecord, full, c)),
          Shared.List.has(~String, ~String.eq, Tables.Table.keys(GroupRecord, full), c),
          False{},
          Equal.sym(
            Bool,
            Shared.List.has(~String, ~String.eq, Tables.Table.keys(GroupRecord, full), c),
            Maybe.is_some(&2, GroupRecord, Tables.Table.get(GroupRecord, full, c)),
            Tables.Table.keys_get(GroupRecord, full, c)
          ),
          h
        )
      )
    )
  )

# after s takes in o, a group is the winner of s's and o's
law after_sync_find:
  for s: NodeState
  for o: NodeState
  for r: String
  for g: String
  {
    Tables.Table.get(
      GroupRecord,
      NodeState.groups(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      g
    )
      == Orders.Order.join(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        Tables.Table.get(GroupRecord, NodeState.groups(s), g),
        Tables.Table.get(GroupRecord, NodeState.groups(o), g)
      ): Maybe<&2, GroupRecord>
  }

def after_sync_find(s, o, r, g):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, GroupRecord>,
    Tables.Table.get(
      GroupRecord,
      NodeState.groups(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      g
    ),
    Tables.Table.get(GroupRecord, Out.groups(Sync.go(False{}, s, o)), g),
    Orders.Order.join(
      ~GroupRecord,
      ~GroupRecord.stamp.cmp,
      Tables.Table.get(GroupRecord, NodeState.groups(s), g),
      Tables.Table.get(GroupRecord, NodeState.groups(o), g)
    ),
    Equal.cong(
      Tables.Table<GroupRecord>,
      Maybe<&2, GroupRecord>,
      t => Tables.Table.get(GroupRecord, t, g),
      NodeState.groups(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r, Sync.go(False{}, s, o)))
      ),
      Out.groups(Sync.go(False{}, s, o)),
      groups_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    sync_groups_find(NodeState.groups(o), Kept{NodeState.groups(s), []}, g)
  )

# a takes in b, then b takes in that: both hold the same members for g
law groups_conv:
  for a: NodeState
  for b: NodeState
  for r1: String
  for r2: String
  for g: String
  {
    GroupRecord.members.got(
      Tables.Table.get(
        GroupRecord,
        NodeState.groups(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        ),
        g
      )
    )
      == GroupRecord.members.got(
        Tables.Table.get(
          GroupRecord,
          NodeState.groups(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          g
        )
      ): Maybe<&2, List<&2, Spec.Member>>
  }

def groups_conv(a, b, r1, r2, g):
  +a = a
  +b = b
  +r1 = r1
  +g = g
  %Equal.sym(
    Maybe<&2, GroupRecord>,
    Tables.Table.get(
      GroupRecord,
      NodeState.groups(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
      ),
      g
    ),
    Orders.Order.join(
      ~GroupRecord,
      ~GroupRecord.stamp.cmp,
      Tables.Table.get(GroupRecord, NodeState.groups(a), g),
      Tables.Table.get(GroupRecord, NodeState.groups(b), g)
    ),
    after_sync_find(a, b, r1, g)
  ): {
    GroupRecord.members.got(
      _
    )
      == GroupRecord.members.got(
        Tables.Table.get(
          GroupRecord,
          NodeState.groups(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          g
        )
      ): Maybe<&2, List<&2, Spec.Member>>
  }
  %Equal.sym(
    Maybe<&2, GroupRecord>,
    Tables.Table.get(
      GroupRecord,
      NodeState.groups(
        Pair.fst(
          NodeState,
          Spec.Answer,
          VendNode.applied(
            b,
            r2,
            Sync.go(
              False{},
              b,
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
            )
          )
        )
      ),
      g
    ),
    Orders.Order.join(
      ~GroupRecord,
      ~GroupRecord.stamp.cmp,
      Tables.Table.get(GroupRecord, NodeState.groups(b), g),
      Tables.Table.get(
        GroupRecord,
        NodeState.groups(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
        ),
        g
      )
    ),
    after_sync_find(
      b,
      Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b))),
      r2,
      g
    )
  ): {
    GroupRecord.members.got(
      Orders.Order.join(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        Tables.Table.get(GroupRecord, NodeState.groups(a), g),
        Tables.Table.get(GroupRecord, NodeState.groups(b), g)
      )
    )
      == GroupRecord.members.got(_): Maybe<&2, List<&2, Spec.Member>>
  }
  %Equal.sym(
    Maybe<&2, GroupRecord>,
    Tables.Table.get(
      GroupRecord,
      NodeState.groups(
        Pair.fst(NodeState, Spec.Answer, VendNode.applied(a, r1, Sync.go(False{}, a, b)))
      ),
      g
    ),
    Orders.Order.join(
      ~GroupRecord,
      ~GroupRecord.stamp.cmp,
      Tables.Table.get(GroupRecord, NodeState.groups(a), g),
      Tables.Table.get(GroupRecord, NodeState.groups(b), g)
    ),
    after_sync_find(a, b, r1, g)
  ): {
    GroupRecord.members.got(
      Orders.Order.join(
        ~GroupRecord,
        ~GroupRecord.stamp.cmp,
        Tables.Table.get(GroupRecord, NodeState.groups(a), g),
        Tables.Table.get(GroupRecord, NodeState.groups(b), g)
      )
    )
      == GroupRecord.members.got(
        Orders.Order.join(
          ~GroupRecord,
          ~GroupRecord.stamp.cmp,
          Tables.Table.get(GroupRecord, NodeState.groups(b), g),
          _
        )
      ): Maybe<&2, List<&2, Spec.Member>>
  }
  Orders.Order.join_conv(
    ~GroupRecord,
    ~List<&2, Spec.Member>,
    ~GroupRecord.stamp.cmp,
    ~GroupRecord.members,
    y => grp_stamp_refl(y),
    x => y => grp_stamp_swap(x, y),
    x => y => grp_stamp_eq(x, y),
    Tables.Table.get(GroupRecord, NodeState.groups(a), g),
    Tables.Table.get(GroupRecord, NodeState.groups(b), g)
  )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Laws
# ----
def Spec.since_splits(s, e, q, t, a, k):
  h =>
    +s = s
    +e = e
    +q = q
    +k = k
    %h:
      {
        Spec.VendNode.get_changes(
          Pair.fst(NodeState, Spec.Answer, _),
          k,
          None{}
        )
          == List.append(
            &2,
            Spec.Notice,
            Spec.VendNode.get_changes(s, k, None{}),
            Spec.VendNode.get_changes(
              Pair.fst(NodeState, Spec.Answer, _),
              k,
              Some{Spec.VendNode.position(s)}
            )
          ): List<&2, Spec.Notice>
      }
    since_ask(s, e, q, k)

def Spec.retry_is_safe(s, r, w, t1, t2, q, s1, a1):
  h =>
    +s = s
    +r = r
    +w = w
    +t1 = t1
    +q = q
    %h: {
      Spec.VendNode.ask(
        Pair.fst(NodeState, Spec.Answer, _),
        Spec.Envelope{r, w, t2},
        q
      )
        == _: NodeState
        & Spec.Answer
    }
    Equal.trans(
      NodeState & Spec.Answer,
      Spec.VendNode.ask(
        Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q)),
        Spec.Envelope{r, w, t2},
        q
      ),
      (
        Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q)),
        Pair.snd(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q))
      ),
      Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q),
      asked_found(
        Tables.Table.get(
          Seen,
          NodeState.seen(
            Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q))
          ),
          r
        ),
        Pair.fst(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q)),
        r,
        w,
        t2,
        q,
        Pair.snd(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q))
      )(seen_after_ask(s, r, w, t1, q)),
      Lists.Pair.eta(NodeState, Spec.Answer, Spec.VendNode.ask(s, Spec.Envelope{r, w, t1}, q))
    )

def Spec.history_kept(s, e, q, t, a, n, v, x):
  match e n:
    case Spec.Envelope{+r, w, z} Resources.Name{n}:
      h1 => h2 =>
        +s = s
        +q = q
        +n = n
        +v = v
        +x = x
        %h1: {
          NodeState.content(
            Pair.fst(NodeState, Spec.Answer, _),
            n,
            Spec.Point.At{v}
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        }
        kept_asked(Tables.Table.get(Seen, NodeState.seen(s), r), s, r, w, z, q, n, v, x)(h2)

def Spec.none_inside_itself_at_start(n, g):
  {==}

def Spec.write_at_head_is_written(s, r, w, time, n, b, v, x):
  match n:
    case Resources.Name{n}:
      +s = s
      +r = r
      +w = w
      +time = time
      +n = n
      +b = b
      +v = v
      +x = x
      (
        Pair.fst(
          NodeState,
          Spec.Answer,
          Spec.VendNode.ask(
            s,
            Spec.Envelope{r, w, time},
            Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
          )
        ),
        (
          r,
          ho => hh => +hn => Equal.trans(
            NodeState & Spec.Answer,
            Spec.VendNode.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
            ),
            (
              Pair.fst(
                NodeState,
                Spec.Answer,
                Spec.VendNode.ask(
                  s,
                  Spec.Envelope{r, w, time},
                  Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                )
              ),
              Pair.snd(
                NodeState,
                Spec.Answer,
                Spec.VendNode.ask(
                  s,
                  Spec.Envelope{r, w, time},
                  Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                )
              )
            ),
            (
              Pair.fst(
                NodeState,
                Spec.Answer,
                Spec.VendNode.ask(
                  s,
                  Spec.Envelope{r, w, time},
                  Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                )
              ),
              Spec.Answer.Write{Spec.Write.Written{r}}
            ),
            Equal.sym(
              NodeState & Spec.Answer,
              (
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  Spec.VendNode.ask(
                    s,
                    Spec.Envelope{r, w, time},
                    Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                  )
                ),
                Pair.snd(
                  NodeState,
                  Spec.Answer,
                  Spec.VendNode.ask(
                    s,
                    Spec.Envelope{r, w, time},
                    Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                  )
                )
              ),
              Spec.VendNode.ask(
                s,
                Spec.Envelope{r, w, time},
                Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
              ),
              Lists.Pair.eta(
                NodeState,
                Spec.Answer,
                Spec.VendNode.ask(
                  s,
                  Spec.Envelope{r, w, time},
                  Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                )
              )
            ),
            Equal.cong(
              Spec.Answer,
              NodeState & Spec.Answer,
              y => (
                Pair.fst(
                  NodeState,
                  Spec.Answer,
                  Spec.VendNode.ask(
                    s,
                    Spec.Envelope{r, w, time},
                    Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                  )
                ),
                y
              ),
              Pair.snd(
                NodeState,
                Spec.Answer,
                Spec.VendNode.ask(
                  s,
                  Spec.Envelope{r, w, time},
                  Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}
                )
              ),
              Spec.Answer.Write{Spec.Write.Written{r}},
              (
                %Equal.sym(Maybe<&2, Seen>, Tables.Table.get(Seen, NodeState.seen(s), r), None{}, new_found(s, r)(hn)): {Pair.snd(NodeState, Spec.Answer, VendNode.asked(_, s, r, w, time, Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}})) == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
                %Equal.sym(Spec.Answer, Pair.snd(NodeState, Spec.Answer, VendNode.applied(s, r, Step.of(s, r, w, time, Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}))), Out.answer(Step.of(s, r, w, time, Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}})), answer_after_applied(s, r, Step.of(s, r, w, time, Spec.Ask.Write{Resources.Name{n}, b, Some{v}, Spec.Content.Bytes{x}}))): {_ == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
                %Equal.sym(Bool, VersionRecord.taken(NodeState.versions(s), r), False{}, new_free(s, r)(hn)): {Out.answer(Write.free(_, s, r, w, time, n, b, Some{v}, x)) == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
                write_on_head(Tables.Table.get(BranchRecord, NodeState.branches(s), b), s, r, w, time, n, b, v, x)(hh)(ho))
            )
          )
        )
      )

def Spec.read_after_write(s, e, n, b, base, x, t, v):
  match e n:
    case Spec.Envelope{+r, +w, +z} Resources.Name{n}:
      +hn => +h =>
        +s = s
        +n = n
        +b = b
        +base = base
        +x = x
        +t = t
        +v = v
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
          t,
          Spec.Answer.Write{Spec.Write.Written{v}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(hn)(h)
        ):
          {NodeState.content(_, n, Spec.Point.Head{b}) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Tables.Table<VersionRecord>,
          NodeState.versions(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                s,
                r,
                Step.of(
                  s,
                  r,
                  w,
                  z,
                  Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
                )
              )
            )
          ),
          VersionRecord.add(
            Out.versions(
              Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}})
            ),
            NodeState.versions(s)
          ),
          versions_after_applied(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}})
          )
        ):
          {
            Blob.find.of(
              VersionRecord.blobs.of(
                VersionRecord.find.of(
                  _,
                  BranchRecord.head.of(
                    Tables.Table.get(
                      BranchRecord,
                      NodeState.branches(
                        Pair.fst(
                          NodeState,
                          Spec.Answer,
                          VendNode.applied(
                            s,
                            r,
                            Step.of(
                              s,
                              r,
                              w,
                              z,
                              Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
                            )
                          )
                        )
                      ),
                      b
                    )
                  )
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        %Equal.sym(
          Tables.Table<BranchRecord>,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(
                s,
                r,
                Step.of(
                  s,
                  r,
                  w,
                  z,
                  Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
                )
              )
            )
          ),
          Out.branches(
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}})
          ),
          branches_after_applied(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}})
          )
        ):
          {
            Blob.find.of(
              VersionRecord.blobs.of(
                VersionRecord.find.of(
                  VersionRecord.add(
                    Out.versions(
                      Step.of(
                        s,
                        r,
                        w,
                        z,
                        Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}
                      )
                    ),
                    NodeState.versions(s)
                  ),
                  BranchRecord.head.of(Tables.Table.get(BranchRecord, _, b))
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        raw_free(
          VersionRecord.taken(NodeState.versions(s), r),
          s,
          r,
          w,
          z,
          n,
          b,
          base,
          x,
          v
        )(
          {==}
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}}),
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.Write{Resources.Name{n}, b, base, Spec.Content.Bytes{x}},
              t,
              Spec.Answer.Write{Spec.Write.Written{v}}
            )(hn)(h)
          )
        )

def Spec.stale_changes_nothing(s, e, n, b, base, x, t, current):
  match e n:
    case Spec.Envelope{+r, +w, +z} Resources.Name{n}:
      +hn => +h =>
        +s = s
        +n = n
        +b = b
        +base = base
        +x = x
        +t = t
        +current = current
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, x}),
          t,
          Spec.Answer.Write{Spec.Write.Stale{current}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{Resources.Name{n}, b, base, x},
            t,
            Spec.Answer.Write{Spec.Write.Stale{current}}
          )(hn)(h)
        ):
          Spec.VendNode.SameContent(_, s) & {base != Some{current}: Maybe<&2, String>}
        stale_bytes(
          Content.bytes(s, n, x),
          s,
          r,
          w,
          z,
          n,
          b,
          base,
          current
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{Resources.Name{n}, b, base, x}),
            t,
            Spec.Answer.Write{Spec.Write.Stale{current}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.Write{Resources.Name{n}, b, base, x},
              t,
              Spec.Answer.Write{Spec.Write.Stale{current}}
            )(hn)(h)
          )
        )

def Spec.conflict_changes_nothing(s, e, p, b, t, k):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => +h =>
        +s = s
        +p = p
        +b = b
        +t = t
        +k = k
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.Merge{p, b}),
          t,
          Spec.Answer.Merge{Spec.Merge.Conflicted{k}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Merge{p, b},
            t,
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}}
          )(hn)(h)
        ):
          Spec.VendNode.SameContent(
            _,
            s
          )
            & {
              Spec.VendNode.get_changes(
                _,
                Spec.Topic.Conflicts{b},
                Some{Spec.VendNode.position(s)}
              )
                == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
            }
        cf_point(
          Point.version(s, p),
          s,
          r,
          w,
          z,
          b,
          k
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Merge{p, b}),
            t,
            Spec.Answer.Merge{Spec.Merge.Conflicted{k}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.Merge{p, b},
              t,
              Spec.Answer.Merge{Spec.Merge.Conflicted{k}}
            )(hn)(h)
          )
        )

def Spec.epoch_grows(s, e, b, g, t, old, new):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => hep => +h =>
        +s = s
        +b = b
        +g = g
        +t = t
        +new = new
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}),
          t,
          Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.SetOwner{b, g},
            t,
            Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}
          )(hn)(h)
        ):
          {
            Nat.is_lt(old, new) == True{}: Bool
          }
            & {
              BranchRecord.epoch.of(
                Tables.Table.get(BranchRecord, NodeState.branches(_), b)
              )
                == Some{new}: Maybe<&2, Nat>
            }
        %Equal.sym(
          Tables.Table<BranchRecord>,
          NodeState.branches(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}))
            )
          ),
          Out.branches(Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g})),
          branches_after_applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}))
        ):
          {
            Nat.is_lt(old, new) == True{}: Bool
          }
            & {
              BranchRecord.epoch.of(
                Tables.Table.get(BranchRecord, _, b)
              )
                == Some{new}: Maybe<&2, Nat>
            }
        set_owner_lemma(
          Tables.Table.get(BranchRecord, NodeState.branches(s), b),
          s,
          b,
          g,
          old,
          new
        )(
          hep
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}),
            t,
            Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.SetOwner{b, g},
              t,
              Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}
            )(hn)(h)
          )
        )

def Spec.sync_converges(a, b, a1, b1, e1, e2):
  match e1 e2:
    case Spec.Envelope{+r1, +w1, +z1} Spec.Envelope{+r2, w2, z2}:
      +hn1 => hn2 => +h1 => h2 =>
        +a = a
        +b = b
        +a1 = a1
        +b1 = b1
        %sync_state(b, a1, r2, w2, z2, b1)(hn2)(h2): Spec.VendNode.SameContent(a1, _)
        %sync_state(
          a,
          b,
          r1,
          w1,
          z1,
          a1
        )(
          hn1
        )(
          h1
        ): Spec.VendNode.SameContent(
          _,
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(b, r2, Sync.go(False{}, b, _)))
        )
        conv_core(a, b, r1, r2)(sync_clean(a, b, r1, w1, z1, a1)(hn1)(h1))

def Spec.sync_idempotent(s, a, s1, s2, a2, e1, e2):
  match e1 e2:
    case Spec.Envelope{+r1, w1, z1} Spec.Envelope{+r2, w2, z2}:
      hn1 => h1 => h2 =>
        +s = s
        +a = a
        +s1 = s1
        idem_ask(
          Tables.Table.get(Seen, NodeState.seen(s1), r2),
          s,
          a,
          r1,
          s1,
          r2,
          w2,
          z2,
          s2,
          a2
        )(sync_state(s, a, r1, w1, z1, s1)(hn1)(h1))(h2)

def Spec.sync_commutes(s, a, b, s1, s2, s3, s4, e1, e2, e3, e4):
  match e1 e2 e3 e4:
    case Spec.Envelope{
      +r1,
      +w1,
      +z1
    } Spec.Envelope{+r2, +w2, +z2} Spec.Envelope{+r3, w3, z3} Spec.Envelope{+r4, w4, z4}:
      +hn1 => +hn2 => hn3 => hn4 => +h1 => +h2 => h3 => h4 =>
        +s = s
        +a = a
        +b = b
        +s1 = s1
        +s2 = s2
        +s3 = s3
        +s4 = s4
        %sync_state(s1, b, r2, w2, z2, s2)(hn2)(h2): Spec.VendNode.SameContent(_, s4)
        %sync_state(
          s3,
          a,
          r4,
          w4,
          z4,
          s4
        )(
          hn4
        )(
          h4
        ): Spec.VendNode.SameContent(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s1, r2, Sync.go(False{}, s1, b))),
          _
        )
        %sync_state(
          s,
          a,
          r1,
          w1,
          z1,
          s1
        )(
          hn1
        )(
          h1
        ): Spec.VendNode.SameContent(
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(_, r2, Sync.go(False{}, _, b))),
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(s3, r4, Sync.go(False{}, s3, a)))
        )
        %sync_state(
          s,
          b,
          r3,
          w3,
          z3,
          s3
        )(
          hn3
        )(
          h3
        ): Spec.VendNode.SameContent(
          Pair.fst(
            NodeState,
            Spec.Answer,
            VendNode.applied(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          ),
          Pair.fst(NodeState, Spec.Answer, VendNode.applied(_, r4, Sync.go(False{}, _, a)))
        )
        comm_core(s, a, b, r1, r2, r3, r4)((
            %Equal.sym(NodeState, Pair.fst(NodeState, Spec.Answer, VendNode.applied(s, r1, Sync.go(False{}, s, a))), s1, sync_state(s, a, r1, w1, z1, s1)(hn1)(h1)): {Sync.collides(Tables.Table.keys(VersionRecord, NodeState.versions(b)), NodeState.versions(b), NodeState.versions(_)) == False{}: Bool}
            sync_clean(s1, b, r2, w2, z2, s2)(hn2)(h2)))

def Spec.inside_through(s, m, h, g):
  Reaches.Reach.in_through(
    ~Spec.Member,
    ~Tables.Table<GroupRecord>,
    ~Member.same,
    ~GroupRecord.members.of,
    ~GroupRecord.all,
    ~member_same_refl,
    ~member_same_sound,
    ~grp_live,
    NodeState.groups(s),
    Spec.Member.Group{g},
    Spec.Member.Group{h},
    m
  )

def Spec.none_inside_itself_after(s, e, q, t, a, g):
  match e:
    case Spec.Envelope{+r, w, z}:
      h => hl => hg =>
        +s = s
        nia_asked(
          Tables.Table.get(Seen, NodeState.seen(s), r),
          s,
          r,
          w,
          z,
          q,
          t,
          a,
          g
        )(h)(hl)(acyc_all(NodeState.groups(s))(hg))

def Spec.merge_disjoint_keeps_both(
  s,
  s1,
  s2,
  s3,
  s4,
  a4,
  e1,
  e2,
  e3,
  e4,
  b,
  c,
  n1,
  n2,
  base1,
  base2,
  x1,
  x2,
  v0,
  v1,
  v2
):
  match e1 e2 e3 e4 n1 n2:
    case Spec.Envelope{
      r1,
      w1,
      z1
    } Spec.Envelope{
      r2,
      w2,
      z2
    } Spec.Envelope{r3, w3, z3} Spec.Envelope{+r4, w4, z4} Resources.Name{n1} Resources.Name{n2}:
      (
        r4,
        hn1 => hn2 => hn3 => hn4 => hne => h1 => h2 => h3 => h4 =>
          +s = s
          +b = b
          +v0 = v0
          +n1 = n1
          +n2 = n2
          mdk_split(Tables.Table.get(BranchRecord, NodeState.branches(s), b), Tables.Table.get(VersionRecord, NodeState.versions(s), v0), s, s1, s2, s3, s4, a4, r1, w1, z1, r2, w2, z2, r3, w3, z3, r4, w4, z4, b, c, n1, n2, base1, base2, x1, x2, v0, v1, v2)({==})({==})(hn1)(hn2)(hn3)(hn4)(Strings.String.ne_eq(n1, n2)(hq => hne(Equal.cong(String, Resources.Name, z => Resources.Name{z}, n1, n2, hq))))(h1)(h2)(h3)(h4))

def Spec.members_after_set(s, e, g, ms, t, x):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => +h =>
        +s = s
        +g = g
        +ms = ms
        +t = t
        +x = x
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}),
          t,
          Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.SetGroup{g, ms},
            t,
            Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
          )(hn)(h)
        ):
          {
            GroupRecord.members.got(
              Tables.Table.get(GroupRecord, NodeState.groups(_), g)
            )
              == Some{ms}: Maybe<&2, List<&2, Spec.Member>>
          }
        %Equal.sym(
          Tables.Table<GroupRecord>,
          NodeState.groups(
            Pair.fst(
              NodeState,
              Spec.Answer,
              VendNode.applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}))
            )
          ),
          Out.groups(Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms})),
          groups_after_applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}))
        ):
          {
            GroupRecord.members.got(
              Tables.Table.get(GroupRecord, _, g)
            )
              == Some{ms}: Maybe<&2, List<&2, Spec.Member>>
          }
        sg_set(
          Cycle.has(NodeState.groups(s), g, ms),
          s,
          g,
          ms,
          x
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}),
            t,
            Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.SetGroup{g, ms},
              t,
              Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
            )(hn)(h)
          )
        )

def Spec.set_keeps_others(s, e, g, h, ms, t, a):
  match e:
    case Spec.Envelope{+r, w, z}:
      hask => hne =>
        +s = s
        +g = g
        +h = h
        keep_others_asked(
          Tables.Table.get(Seen, NodeState.seen(s), r),
          s,
          r,
          w,
          z,
          g,
          h,
          ms,
          t,
          a
        )(hask)(Strings.String.eq_flip(h, g)(Strings.String.ne_eq(h, g)(hne)))

def Spec.inside_has_chain(s, m, g):
  hi =>
    +s = s
    +g = g
    +m = m
    inside_chain.of(
      s,
      g,
      m,
      Reaches.Reach.go_path(
        ~Spec.Member,
        ~Tables.Table<GroupRecord>,
        ~Member.same,
        ~GroupRecord.members.of,
        ~member_same_refl,
        List.length(&2, Spec.Member, GroupRecord.all(NodeState.groups(s))),
        GroupRecord.members.of(NodeState.groups(s), Spec.Member.Group{g}),
        NodeState.groups(s),
        m
      )(hi)
    )

def Spec.chain_is_inside(s, g, ps, m):
  hc =>
    +s = s
    +g = g
    +ps = ps
    +m = m
    Reaches.Reach.path_in(
      ~Spec.Member,
      ~Tables.Table<GroupRecord>,
      ~Member.same,
      ~GroupRecord.members.of,
      ~GroupRecord.all,
      ~member_same_sound,
      ~grp_live,
      GroupRecord.groups(ps),
      NodeState.groups(s),
      Spec.Member.Group{g},
      m
    )(chain_path(ps, s, g, m)(hc))

def Spec.cycle_has_closer(s, e, g, ms, t):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => +h =>
        +s = s
        +g = g
        +ms = ms
        +t = t
        closer_found.of(
          s,
          g,
          ms,
          Reaches.Reach.closes_split(
            ~Spec.Member,
            ~Tables.Table<GroupRecord>,
            ~Member.same,
            ~GroupRecord.members.of,
            ~GroupRecord.all,
            NodeState.groups(s),
            Spec.Member.Group{g},
            ms
          )(
            sg_cycle(
              Cycle.has(NodeState.groups(s), g, ms),
              s,
              g,
              ms
            )(
              applied_answer(
                s,
                r,
                Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}),
                t,
                Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}}
              )(
                ask_step(
                  s,
                  r,
                  w,
                  z,
                  Spec.Ask.SetGroup{g, ms},
                  t,
                  Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}}
                )(hn)(h)
              )
            )
          )
        )

def Spec.closer_is_cycle(s, e, g, ms, m, t, a):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => ham => hc => +h =>
        +s = s
        +g = g
        +ms = ms
        +t = t
        +a = a
        Equal.trans(
          Spec.Answer,
          a,
          Out.answer(SetGroup.on(Cycle.has(NodeState.groups(s), g, ms), s, g, ms)),
          Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}},
          Equal.sym(
            Spec.Answer,
            Out.answer(Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms})),
            a,
            applied_answer(
              s,
              r,
              Step.of(s, r, w, z, Spec.Ask.SetGroup{g, ms}),
              t,
              a
            )(ask_step(s, r, w, z, Spec.Ask.SetGroup{g, ms}, t, a)(hn)(h))
          ),
          (
            %Equal.sym(Bool, Cycle.has(NodeState.groups(s), g, ms), True{}, closer_among.of(s, g, ms, m, ham)(hc)): {Out.answer(SetGroup.on(_, s, g, ms)) == Spec.Answer.SetGroup{Spec.SetGroup.Cycle{}}: Spec.Answer}
            {==})
        )

def Spec.groups_converge(a, b, a1, b1, e1, e2, g):
  match e1 e2:
    case Spec.Envelope{+r1, w1, z1} Spec.Envelope{+r2, w2, z2}:
      +hn1 => hn2 => +h1 => h2 =>
        +a = a
        +b = b
        +a1 = a1
        +b1 = b1
        +g = g
        %sync_state(
          b,
          a1,
          r2,
          w2,
          z2,
          b1
        )(
          hn2
        )(
          h2
        ): {
          Spec.VendNode.get_members(
            a1,
            g
          )
            == Spec.VendNode.get_members(_, g): Maybe<&2, List<&2, Spec.Member>>
        }
        %sync_state(
          a,
          b,
          r1,
          w1,
          z1,
          a1
        )(
          hn1
        )(
          h1
        ): {
          Spec.VendNode.get_members(
            _,
            g
          )
            == Spec.VendNode.get_members(
              Pair.fst(NodeState, Spec.Answer, VendNode.applied(b, r2, Sync.go(False{}, b, _))),
              g
            ): Maybe<&2, List<&2, Spec.Member>>
        }
        groups_conv(a, b, r1, r2, g)
