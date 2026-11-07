import Base
import ../../shared/bools.bend as Bools
import ../../shared/bytes.bend as Octets
import ../../shared/cmps.bend as Cmps
import ../../shared/lists.bend as Lists
import ../../shared/maybes.bend as Maybes
import ../../shared/nats.bend as Nats
import ../../shared/orders.bend as Orders
import ../../shared/reach.bend as Reaches
import ../../shared/shared.bend as Shared
import ../../shared/strings.bend as Strings
import ../../shared/tables.bend as Tables
import ./spec.bend as Spec

# The pure core of a Vend Node. Every opaque name of the spec is a String,
# compared with String.eq; every collection that is keyed by a name is a
# Table.

# Names
# -----
def Spec.Node():
  String

def Spec.Node.read(t):
  Strings.String.nonempty(t)

def Spec.Node.show(n):
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

def Spec.Name():
  String

def Spec.Name.read(t):
  Strings.String.nonempty(t)

def Spec.Name.show(n):
  n

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
type Ver is Data:
  Ver{blobs: Tables.Table<List<&2, U32>>, parents: List<&2, String>, author: String, time: String}

# a branch: its newest version, its owner group, and the stamp of that head:
# the owner's epoch, then how many heads the owner set in that epoch; its
# name is its key
type Br is Data:
  Br{head: String, owner: String, epoch: Nat, count: Nat}

# a mark: a fixed name for a version of a branch
type MarkAt is Data:
  MarkAt{version: String, message: String}

# an owner group: its members, and how many times they were set
type Grp is Data:
  Grp{members: List<&2, Spec.Member>, epoch: Nat}

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
type St is Data:
  St{
    self: String,
    versions: Tables.Table<Ver>,
    branches: Tables.Table<Br>,
    marks: Tables.Table<Tables.Table<MarkAt>>,
    groups: Tables.Table<Grp>,
    clashes: Tables.Table<Clash>,
    seen: Tables.Table<Seen>,
    log: List<&2, Logged>
  }

def Spec.Node.State():
  St

# what a change does: the versions it adds, the branches, marks, groups and
# clashes after it, its notices, and its answer
type Out is Data:
  Out{
    versions: List<&2, Tables.Row<Ver>>,
    branches: Tables.Table<Br>,
    marks: Tables.Table<Tables.Table<MarkAt>>,
    groups: Tables.Table<Grp>,
    clashes: Tables.Table<Clash>,
    news: List<&2, Logged>,
    answer: Spec.Answer
  }

# Lookups
# -------
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the pure node is the model that the laws are about: an and/or keeps one value for a proof to split on; speed belongs in a later fast node, proven equal to this one

# vs holds the version k
def Ver.has(vs: Tables.Table<Ver>, k: String) -> Bool:
  Maybe.is_some(&2, Ver, Tables.Table.get(Ver, vs, k))

# vs, with v unless vs holds a version with its ID (held)
def Ver.add.put(i: String, v: Ver, vs: Tables.Table<Ver>, held: Bool) -> Tables.Table<Ver>:
  match held:
    case True{}:
      vs
    case False{}:
      Tables.Table.set(Ver, vs, i, v)

# vs, with v unless vs holds a version with its ID
def Ver.add.one(v: Tables.Row<Ver>, +vs: Tables.Table<Ver>) -> Tables.Table<Ver>:
  match v:
    case Tables.Row{+i, x}:
      Ver.add.put(i, x, vs, Ver.has(vs, i))

# vs, with each version of news whose ID vs does not hold
def Ver.add(news: List<&2, Tables.Row<Ver>>, vs: Tables.Table<Ver>) -> Tables.Table<Ver>:
  match news:
    case Nil{}:
      vs
    case Con{v, r}:
      Ver.add(r, Ver.add.one(v, vs))

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
    case Spec.Member.Node{x} Spec.Member.Node{y}:
      String.eq(x, y)
    case Spec.Member.Group{x} Spec.Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

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
def St.self(s: St) -> String:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      k

def St.versions(s: St) -> Tables.Table<Ver>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      vs

def St.branches(s: St) -> Tables.Table<Br>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      bs

def St.marks(s: St) -> Tables.Table<Tables.Table<MarkAt>>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      ms

def St.groups(s: St) -> Tables.Table<Grp>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      gs

def St.clashes(s: St) -> Tables.Table<Clash>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      cs

def St.seen(s: St) -> Tables.Table<Seen>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      ss

def St.log(s: St) -> List<&2, Logged>:
  match s:
    case St{k, vs, bs, ms, gs, cs, ss, l}:
      l

# Reads
# -----

# the head of the branch that m holds
def Br.head.of(m: Maybe<&2, Br>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{Br{h, o, e, c}}:
      Some{h}

# the version that p names in s
def Point.version(s: St, p: Spec.Point) -> Maybe<&2, String>:
  match p:
    case Spec.Point.At{v}:
      Some{v}
    case Spec.Point.Head{b}:
      Br.head.of(Tables.Table.get(Br, St.branches(s), b))
    case Spec.Point.Mark{b, m}:
      MarkAt.find(St.marks(s), b, m)

# the resources of the version that m holds
def Ver.blobs.of(m: Maybe<&2, Ver>) -> Maybe<&2, Tables.Table<List<&2, U32>>>:
  match m:
    case None{}:
      None{}
    case Some{Ver{b, p, a, t}}:
      Some{b}

# the version that m names, among vs
def Ver.find.of(vs: Tables.Table<Ver>, m: Maybe<&2, String>) -> Maybe<&2, Ver>:
  match m:
    case None{}:
      None{}
    case Some{k}:
      Tables.Table.get(Ver, vs, k)

# the bytes of the resource n among the resources that m holds
def Blob.find.of(m: Maybe<&2, Tables.Table<List<&2, U32>>>, n: String) -> Maybe<&2, List<&2, U32>>:
  match m:
    case None{}:
      None{}
    case Some{bs}:
      Tables.Table.get(List<&2, U32>, bs, n)

# the resources of the version k among vs, none when vs does not hold it
def Vers.blobs(vs: Tables.Table<Ver>, k: String) -> Tables.Table<List<&2, U32>>:
  Maybe.default(
    &2,
    Tables.Table<List<&2, U32>>,
    Ver.blobs.of(Tables.Table.get(Ver, vs, k)),
    Tables.Table.new(List<&2, U32>)
  )

# the bytes of the resource n at the point p of s
def St.content(+s: St, n: String, p: Spec.Point) -> Maybe<&2, List<&2, U32>>:
  Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s), Point.version(s, p))), n)

# one step of a walk: the versions it reached, the frontier after it, and the
# versions seen so far
type Walked is Data:
  Walked{reached: List<&2, Tables.Row<Ver>>, next: List<&2, String>, done: List<&2, String>}

# the step of a walk at the version that m holds, with the frontier r after
def History.at(
  +k: String,
  r: List<&2, String>,
  done: List<&2, String>,
  m: Maybe<&2, Ver>
) -> Walked:
  match m:
    case None{}:
      Walked{[], r, k <> done}
    case Some{Ver{b, +p, a, t}}:
      Walked{[Tables.Row{k, Ver{b, p, a, t}}], List.append(&2, String, r, p), k <> done}

# the step of a walk at the key k, skipped when done holds it (was)
def History.next(
  +k: String,
  r: List<&2, String>,
  done: List<&2, String>,
  vs: Tables.Table<Ver>,
  was: Bool
) -> Walked:
  match was:
    case True{}:
      Walked{[], r, done}
    case False{}:
      History.at(k, r, done, Tables.Table.get(Ver, vs, k))

def Walked.reached(w: Walked) -> List<&2, Tables.Row<Ver>>:
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
def History.parents(m: Maybe<&2, Ver>) -> List<&2, String>:
  match m:
    case None{}:
      Nil{}
    case Some{Ver{b, p, a, t}}:
      p

# a version of vs among the keys ks names k as a parent
def Ver.named(ks: List<&2, String>, +vs: Tables.Table<Ver>, +k: String) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{j, r}:
      Bool.or(Strings.has(History.parents(Tables.Table.get(Ver, vs, j)), k), Ver.named(r, vs, k))

# the ID k is taken: vs holds a version with it, or a version that names it as
# a parent, whose version lives on another node
def Ver.taken(+vs: Tables.Table<Ver>, +k: String) -> Bool:
  Bool.or(Ver.has(vs, k), Ver.named(Tables.Table.keys(Ver, vs), vs, k))

# the number of parent links of the versions with the keys ks
def History.links(ks: List<&2, String>, +vs: Tables.Table<Ver>) -> Nat:
  match ks:
    case Nil{}:
      1n
    case Con{k, r}:
      Nat.add(
        1n+List.length(&2, String, History.parents(Tables.Table.get(Ver, vs, k))),
        History.links(r, vs)
      )

# the versions reached from the frontier ks, in that order, without the ones
# in done: one key per step of the fuel f
def History.walk(
  f: Nat,
  ks: List<&2, String>,
  +done: List<&2, String>,
  +vs: Tables.Table<Ver>
) -> List<&2, Tables.Row<Ver>>:
  match f:
    case 0n:
      Nil{}
    case 1n+g:
      match ks:
        case Nil{}:
          Nil{}
        case Con{+k, r}:
          +w = History.next(k, r, done, vs, Strings.has(done, k))
          List.append(
            &2,
            Tables.Row<Ver>,
            Walked.reached(w),
            History.walk(g, Walked.next(w), Walked.done(w), vs)
          )

# the version k and the versions it came from, among vs; fuel for every
# version, once per parent link
def History.of(+vs: Tables.Table<Ver>, k: String) -> List<&2, Tables.Row<Ver>>:
  History.walk(History.links(Tables.Table.keys(Ver, vs), vs), [k], [], vs)

# Groups
# ------

# the members of the group that m holds
def Grp.members.in(m: Maybe<&2, Grp>) -> List<&2, Spec.Member>:
  match m:
    case None{}:
      Nil{}
    case Some{Grp{ms, e}}:
      ms

# the members of the group that m is, among gs; none for a node
def Grp.members.of(gs: Tables.Table<Grp>, m: Spec.Member) -> List<&2, Spec.Member>:
  match m:
    case Spec.Member.Node{n}:
      Nil{}
    case Spec.Member.Group{g}:
      Grp.members.in(Tables.Table.get(Grp, gs, g))

# the groups named ks, as members
def Grp.groups(ks: List<&2, String>) -> List<&2, Spec.Member>:
  match ks:
    case Nil{}:
      []
    case Con{k, r}:
      Spec.Member.Group{k} <> Grp.groups(r)

# the groups of gs, as members: the members that can have members
def Grp.all(gs: Tables.Table<Grp>) -> List<&2, Spec.Member>:
  Grp.groups(Tables.Table.keys(Grp, gs))

# gs with x as the group c; a node has no group to set
def Grp.put(gs: Tables.Table<Grp>, c: Spec.Member, x: Grp) -> Tables.Table<Grp>:
  match c:
    case Spec.Member.Node{n}:
      gs
    case Spec.Member.Group{k}:
      Tables.Table.set(Grp, gs, k, x)

# m is inside the group g of gs: a member of g, or of a group inside g
def Grp.inside(gs: Tables.Table<Grp>, m: Spec.Member, g: String) -> Bool:
  Reaches.Reach.in(
    ~Spec.Member,
    ~Tables.Table<Grp>,
    ~Member.same,
    ~Grp.members.of,
    ~Grp.all,
    gs,
    Spec.Member.Group{g},
    m
  )

# Changes
# -------
# A change reads the state and says what to do (an Out); Node.ask applies it.
# A change never removes a version, and it writes no notice of its own: both
# are Node.ask's.

# nothing changes, and the answer is a
def Out.same(+s: St, a: Spec.Answer) -> Out:
  Out{[], St.branches(s), St.marks(s), St.groups(s), St.clashes(s), [], a}

# the node of s is in the owner group of the branch b
def Owner.of(+s: St, b: Br) -> Bool:
  match b:
    case Br{h, +o, e, c}:
      Bool.or(String.eq(o, St.self(s)), Grp.inside(St.groups(s), Spec.Member.Node{St.self(s)}, o))

# the bytes that x names, for the resource n of s
def Content.bytes(s: St, n: String, x: Spec.Content) -> Maybe<&2, List<&2, U32>>:
  match x:
    case Spec.Content.Bytes{y}:
      Some{y}
    case Spec.Content.Of{v}:
      St.content(s, n, Spec.Point.At{v})

# m names the version k
def Base.is(m: Maybe<&2, String>, k: String) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{j}:
      String.eq(j, k)

# a new head h for the branch b, as its owner
def Br.moved(b: Br, h: String) -> Br:
  match b:
    case Br{old, o, e, c}:
      Br{h, o, e, 1n+c}

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
  +s: St,
  +r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  y: List<&2, U32>,
  br: Br
) -> Out:
  match ok:
    case False{}:
      match br:
        case Br{h, o, e, c}:
          Out.same(s, Write.answer(Spec.Write.Stale{h}))
    case True{}:
      match br:
        case Br{+h, o, e, c}:
          Out{
            [
              Tables.Row{
                r,
                Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, y), [h], w, t}
              }
            ],
            Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [Logged.head(b, r)],
            Write.answer(Spec.Write.Written{r})
          }

# a write of y to n on br, the branch b, as its owner or not
def Write.on(
  owner: Bool,
  +s: St,
  +r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>,
  +br: Br
) -> Out:
  match owner:
    case True{}:
      match br:
        case Br{+h, o, e, c}:
          Write.at(Base.is(base, h), s, r, w, t, n, b, y, Br{h, o, e, c})
    case False{}:
      match br:
        case Br{+h, o, e, c}:
          Out{
            [
              Tables.Row{
                r,
                Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, y), [h], w, t}
              }
            ],
            St.branches(s),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [],
            Write.answer(Spec.Write.Pending{r})
          }

# a write of y to n on the branch b, which m holds when it exists
def Write.branch(
  m: Maybe<&2, Br>,
  +s: St,
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
                Ver{
                  Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, y),
                  [],
                  w,
                  t
                }
              }
            ],
            Tables.Table.set(Br, St.branches(s), b, Br{r, St.self(s), 0n, 0n}),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [Logged.head(b, r)],
            Write.answer(Spec.Write.Written{r})
          }

# a write of y, unless the version ID r is taken
def Write.free(
  taken: Bool,
  +s: St,
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
      Write.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, n, b, base, y)

# a write of the bytes that m holds
def Write.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: St,
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
      Write.free(Ver.taken(St.versions(s), r), s, r, w, t, n, b, base, y)

# the answer to a set-branch
def SetBranch.answer(a: Spec.SetBranch) -> Spec.Answer:
  Spec.Answer.SetBranch{a}

# the branch br set to the resources bs of a version, as its owner or not; r
# is the new version, unless its ID is taken
def SetBranch.on(
  owner: Bool,
  taken: Bool,
  +s: St,
  +r: String,
  w: String,
  t: String,
  +b: String,
  bs: Tables.Table<List<&2, U32>>,
  +br: Br
) -> Out:
  match owner taken:
    case _ True{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"version ID taken"}))
    case False{} False{}:
      match br:
        case Br{h, o, e, c}:
          Out{
            [Tables.Row{r, Ver{bs, [h], w, t}}],
            St.branches(s),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [],
            SetBranch.answer(Spec.SetBranch.Pending{r})
          }
    case True{} False{}:
      match br:
        case Br{+h, o, e, c}:
          Out{
            [Tables.Row{r, Ver{bs, [h], w, t}}],
            Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [Logged.head(b, r)],
            SetBranch.answer(Spec.SetBranch.Restored{r})
          }

# the branch b set to the version k, whose resources bs are; m holds b when
# it exists
def SetBranch.branch(
  m: Maybe<&2, Br>,
  +s: St,
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
        Tables.Table.set(Br, St.branches(s), b, Br{k, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(b, k)],
        SetBranch.answer(Spec.SetBranch.Created{k})
      }
    case Some{+br}:
      SetBranch.on(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, b, bs, br)

# the branch b set to the version k, which m holds when s has it
def SetBranch.version(
  m: Maybe<&2, Ver>,
  +s: St,
  r: String,
  w: String,
  t: String,
  +b: String,
  k: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"no such version"}))
    case Some{Ver{bs, p, a, z}}:
      SetBranch.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, b, k, bs)

# the branch b set to the version that m names
def SetBranch.point(
  m: Maybe<&2, String>,
  +s: St,
  r: String,
  w: String,
  t: String,
  b: String
) -> Out:
  match m:
    case None{}:
      Out.same(s, SetBranch.answer(Spec.SetBranch.Refused{"no such point"}))
    case Some{+k}:
      SetBranch.version(Tables.Table.get(Ver, St.versions(s), k), s, r, w, t, b, k)

# the answer to a create-mark
def CreateMark.answer(a: Spec.CreateMark) -> Spec.Answer:
  Spec.Answer.CreateMark{a}

# the mark m of br with the message x, unless m names a version of br (held)
def CreateMark.free(
  held: Maybe<&2, String>,
  +s: St,
  b: String,
  +m: String,
  x: String,
  br: Br
) -> Out:
  match held:
    case Some{k}:
      Out.same(s, CreateMark.answer(Spec.CreateMark.Taken{}))
    case None{}:
      match br:
        case Br{h, o, e, c}:
          Out{
            [],
            St.branches(s),
            MarkAt.set(St.marks(s), b, m, MarkAt{h, x}),
            St.groups(s),
            St.clashes(s),
            [],
            CreateMark.answer(Spec.CreateMark.Marked{m})
          }

# the mark m with the message x on the branch b, which f holds when it exists
def CreateMark.branch(f: Maybe<&2, Br>, +s: St, +b: String, +m: String, x: String) -> Out:
  match f:
    case None{}:
      Out.same(s, CreateMark.answer(Spec.CreateMark.Refused{"no such branch"}))
    case Some{br}:
      CreateMark.free(MarkAt.find(St.marks(s), b, m), s, b, m, x, br)

# the answer to a set-owner
def SetOwner.answer(a: Spec.SetOwner) -> Spec.Answer:
  Spec.Answer.SetOwner{a}

# the owner group g for br, when the node of s owns br
def SetOwner.on(owner: Bool, +s: St, b: String, g: String, br: Br) -> Out:
  match owner:
    case False{}:
      Out.same(s, SetOwner.answer(Spec.SetOwner.Refused{"not the owner"}))
    case True{}:
      match br:
        case Br{h, o, +e, c}:
          Out{
            [],
            Tables.Table.set(Br, St.branches(s), b, Br{h, g, 1n+e, 0n}),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [],
            SetOwner.answer(Spec.SetOwner.Set{1n+e})
          }

# the owner group g for the branch that f holds
def SetOwner.branch(f: Maybe<&2, Br>, +s: St, b: String, g: String) -> Out:
  match f:
    case None{}:
      Out.same(s, SetOwner.answer(Spec.SetOwner.Refused{"no such branch"}))
    case Some{+br}:
      SetOwner.on(Owner.of(s, br), s, b, g, br)

# the answer to a set-group
def SetGroup.answer(a: Spec.SetGroup) -> Spec.Answer:
  Spec.Answer.SetGroup{a}

# the epoch of the group that m holds, or none
def Grp.epoch.of(m: Maybe<&2, Grp>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Grp{ms, e}}:
      e

# the epoch that the group g gets when it is set next
def Grp.epoch.next(gs: Tables.Table<Grp>, g: String) -> Nat:
  1n+Grp.epoch.of(Tables.Table.get(Grp, gs, g))

# setting the members of the group g to ms closes a cycle: a member of ms is
# g, or has g inside it
def Cycle.has(gs: Tables.Table<Grp>, g: String, ms: List<&2, Spec.Member>) -> Bool:
  Reaches.Reach.closes(
    ~Spec.Member,
    ~Tables.Table<Grp>,
    ~Member.same,
    ~Grp.members.of,
    ~Grp.all,
    gs,
    Spec.Member.Group{g},
    ms
  )

# the group g with the members ms, unless that closes a cycle
def SetGroup.on(cycle: Bool, +s: St, +g: String, ms: List<&2, Spec.Member>) -> Out:
  match cycle:
    case True{}:
      Out.same(s, SetGroup.answer(Spec.SetGroup.Cycle{}))
    case False{}:
      Out{
        [],
        St.branches(s),
        St.marks(s),
        Tables.Table.set(Grp, St.groups(s), g, Grp{ms, Grp.epoch.next(St.groups(s), g)}),
        St.clashes(s),
        [],
        SetGroup.answer(Spec.SetGroup.Set{Grp.epoch.next(St.groups(s), g)})
      }

# the IDs of vs
def Vers.ids(vs: List<&2, Tables.Row<Ver>>) -> List<&2, String>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Tables.Row{i, v}, r}:
      i <> Vers.ids(r)

# the first version of vs whose ID ks holds
def Vers.first_in(vs: List<&2, Tables.Row<Ver>>, +ks: List<&2, String>) -> Maybe<&2, String>:
  match vs:
    case Nil{}:
      None{}
    case Con{Tables.Row{+i, v}, r}:
      List.find.if(String, i, u => Vers.first_in(r, ks), Strings.has(ks, i))

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
  +s: St,
  +r: String,
  w: String,
  t: String,
  f: String,
  +b: String,
  bs: Tables.Table<List<&2, U32>>,
  br: Br
) -> Out:
  match cs:
    case Nil{}:
      match br:
        case Br{+h, o, e, c}:
          Out{
            [Tables.Row{r, Ver{bs, [h, f], w, t}}],
            Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
            [Logged.head(b, r)],
            Merge.answer(Spec.Merge.Merged{r})
          }
    case Con{k, more}:
      match br:
        case Br{h, o, e, c}:
          Out{
            [],
            St.branches(s),
            St.marks(s),
            St.groups(s),
            Tables.Table.set(Clash, St.clashes(s), r, Clash{b, h, f, bs, k <> more}),
            [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}],
            Merge.answer(Spec.Merge.Conflicted{r})
          }

# the merge of the version f into br, from the resources of its head hb, of f
# (fb), and of their base (bb)
def Merge.three(
  s: St,
  r: String,
  w: String,
  t: String,
  f: String,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>,
  b: String,
  br: Br
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
def Merge.base(s: St, m: Maybe<&2, String>) -> Tables.Table<List<&2, U32>>:
  match m:
    case None{}:
      Tables.Table.new(List<&2, U32>)
    case Some{k}:
      Vers.blobs(St.versions(s), k)

# the merge of the version f into br, unless the head already holds f
def Merge.inside(
  held: Bool,
  +s: St,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: Br
) -> Out:
  match held:
    case True{}:
      match br:
        case Br{h, o, e, c}:
          Out.same(s, Merge.answer(Spec.Merge.Merged{h}))
    case False{}:
      match br:
        case Br{+h, o, e, c}:
          hh = History.of(St.versions(s), h)
          Merge.three(
            s,
            r,
            w,
            t,
            f,
            Vers.blobs(St.versions(s), h),
            Vers.blobs(St.versions(s), f),
            Merge.base(s, Vers.first_in(History.of(St.versions(s), f), Vers.ids(hh))),
            b,
            Br{h, o, e, c}
          )

# the merge of the version f into br, as its owner, unless the ID r is taken
def Merge.owner(
  owner: Bool,
  taken: Bool,
  +s: St,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: Br
) -> Out:
  match owner taken:
    case False{} _:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"not the owner"}))
    case True{} True{}:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"version ID taken"}))
    case True{} False{}:
      match br:
        case Br{+h, o, e, c}:
          Merge.inside(
            Strings.has(Vers.ids(History.of(St.versions(s), h)), f),
            s,
            r,
            w,
            t,
            f,
            b,
            Br{h, o, e, c}
          )

# the merge of the version f into the branch that m holds
def Merge.branch(
  m: Maybe<&2, Br>,
  +s: St,
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
      Merge.owner(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, f, b, br)

# the merge of the version that m names into the branch b
def Merge.point(m: Maybe<&2, String>, +s: St, r: String, w: String, t: String, +b: String) -> Out:
  match m:
    case None{}:
      Out.same(s, Merge.answer(Spec.Merge.Refused{"no such point"}))
    case Some{f}:
      Merge.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, f, b)

# the answer to a resolve
def Resolve.answer(a: Spec.Resolve) -> Spec.Answer:
  Spec.Answer.Resolve{a}

# the clash k after its resource n got y: the names that still clash (left),
# and whether the version ID r is taken
def Resolve.done(
  left: List<&2, String>,
  taken: Bool,
  +s: St,
  +r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  y: List<&2, U32>,
  cl: Clash,
  br: Br
) -> Out:
  match left:
    case Nil{}:
      match taken:
        case True{}:
          Out.same(s, Resolve.answer(Spec.Resolve.Refused{"version ID taken"}))
        case False{}:
          match cl br:
            case Clash{+b, h, f, bs, l} Br{h2, o, e, c}:
              Out{
                [Tables.Row{r, Ver{Tables.Table.set(List<&2, U32>, bs, n, y), [h, f], w, t}}],
                Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h2, o, e, c}, r)),
                St.marks(s),
                St.groups(s),
                Tables.Table.del(Clash, St.clashes(s), k),
                [Logged.head(b, r)],
                Resolve.answer(Spec.Resolve.Resolved{r})
              }
    case Con{+x, +more}:
      match cl:
        case Clash{b, h, f, bs, l}:
          Out{
            [],
            St.branches(s),
            St.marks(s),
            St.groups(s),
            Tables.Table.set(
              Clash,
              St.clashes(s),
              k,
              Clash{b, h, f, Tables.Table.set(List<&2, U32>, bs, n, y), x <> more}
            ),
            [],
            Resolve.answer(Spec.Resolve.Left{x <> more})
          }

# the clash k settled for n with the bytes that m holds
def Resolve.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  +cl: Clash,
  br: Br
) -> Out:
  match m:
    case None{}:
      Out.same(s, Resolve.answer(Spec.Resolve.Refused{"no such content"}))
    case Some{y}:
      match cl:
        case Clash{b, h, f, bs, +l}:
          Resolve.done(
            Shared.List.remove(~String, ~String.eq, l, n),
            Ver.taken(St.versions(s), r),
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
  +s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content,
  cl: Clash,
  br: Br
) -> Out:
  match ok:
    case False{}:
      match br:
        case Br{h, o, e, c}:
          Out.same(s, Resolve.answer(Spec.Resolve.Stale{h}))
    case True{}:
      Resolve.bytes(Content.bytes(s, n, x), s, r, w, t, k, n, cl, br)

# the clash k settled for n with x, on the branch that m holds
def Resolve.branch(
  m: Maybe<&2, Br>,
  s: St,
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
    case Some{Br{+h, o, e, c}}:
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
            Br{h, o, e, c}
          )

# the clash k settled for n with x, when n clashes in it (has)
def Resolve.named(
  has: Bool,
  +s: St,
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
            Tables.Table.get(Br, St.branches(s), b),
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
  s: St,
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
      Resolve.named(Strings.has(l, n), s, r, w, t, k, n, x, Clash{b, h, f, bs, l})

# the answer to a sync
def Sync.answer(a: Spec.Sync) -> Spec.Answer:
  Spec.Answer.Sync{a}

# the order of the stamps of the heads of a and b: epoch, then count, then
# the head's ID, so that every node picks the same winner
def Br.stamp.cmp(a: Br, b: Br) -> Cmp:
  match a b:
    case Br{h1, o1, e1, c1} Br{h2, o2, e2, c2}:
      Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))

# both lookups found a version under the same ID, with other resources
def Sync.clash.at(mine: Maybe<&2, Ver>, theirs: Maybe<&2, Ver>) -> Bool:
  match mine theirs:
    case Some{Ver{b1, p1, a1, t1}} Some{Ver{b2, p2, a2, t2}}:
      Bool.not(Tables.Table.same(~List<&2, U32>, ~Octets.Bytes.is_eq, b1, b2))
    case _ _:
      False{}

# a version of os under one of the keys ks has the ID of a version of vs, with
# other resources
def Sync.collides(ks: List<&2, String>, +os: Tables.Table<Ver>, +vs: Tables.Table<Ver>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case Con{+k, r}:
      Bool.or(
        Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)),
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
  Mix{branches: Tables.Table<Br>, clashes: Tables.Table<Clash>, news: List<&2, Logged>}

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
  +vs: Tables.Table<Ver>,
  +h: String,
  b: String,
  +l: String,
  cs: Tables.Table<Clash>
) -> Tables.Table<Clash>:
  +hb = Vers.blobs(vs, h)
  +lb = Vers.blobs(vs, l)
  Sync.lost.if(
    Strings.has(Vers.ids(History.of(vs, h)), l),
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
def Sync.pick(c: Cmp, +b: String, mine: Br, theirs: Br, vs: Tables.Table<Ver>, acc: Mix) -> Mix:
  match c mine theirs acc:
    case LT{} Br{h1, o1, e1, c1} Br{+h, o, e, k} Mix{bs, cs, ns}:
      Mix{
        Tables.Table.set(Br, bs, b, Br{h, o, e, k}),
        Sync.lost(vs, h, b, h1, cs),
        List.append(&2, Logged, ns, [Logged.head(b, h)])
      }
    case GT{} Br{h, o, e, k} Br{h2, o2, e2, c2} Mix{bs, cs, ns}:
      Mix{bs, Sync.lost(vs, h, b, h2, cs), ns}
    case EQ{} m t z:
      z

# the branches after theirs, the branch b, met the one that m holds
def Sync.at(m: Maybe<&2, Br>, +b: String, +theirs: Br, vs: Tables.Table<Ver>, acc: Mix) -> Mix:
  match m:
    case None{}:
      match theirs acc:
        case Br{+h, o, e, k} Mix{bs, cs, ns}:
          Mix{
            Tables.Table.set(Br, bs, b, Br{h, o, e, k}),
            cs,
            List.append(&2, Logged, ns, [Logged.head(b, h)])
          }
    case Some{+mine}:
      Sync.pick(Br.stamp.cmp(mine, theirs), b, mine, theirs, vs, acc)

# the branches after theirs, the branch b, met them
def Sync.meet(acc: Mix, +b: String, theirs: Br, vs: Tables.Table<Ver>) -> Mix:
  match acc:
    case Mix{+bs, cs, ns}:
      Sync.at(Tables.Table.get(Br, bs, b), b, theirs, vs, Mix{bs, cs, ns})

# the branches after the branch b that m holds met them; none when m is empty
def Sync.seen.meet(b: String, m: Maybe<&2, Br>, acc: Mix, vs: Tables.Table<Ver>) -> Mix:
  match m:
    case None{}:
      acc
    case Some{br}:
      Sync.meet(acc, b, br, vs)

# the branches after the branch of each key of ks in full met them
def Sync.branches(
  ks: List<&2, String>,
  +full: Tables.Table<Br>,
  +vs: Tables.Table<Ver>,
  acc: Mix
) -> Mix:
  match ks:
    case Nil{}:
      acc
    case Con{+k, r}:
      Sync.branches(r, full, vs, Sync.seen.meet(k, Tables.Table.get(Br, full, k), acc, vs))

def Mix.branches(m: Mix) -> Tables.Table<Br>:
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
  Kept{groups: Tables.Table<Grp>, news: List<&2, Logged>}

# the groups with x as g, unless that closes a cycle: then they keep their
# own, with a notice of x's members
def Sync.group.put(cycle: Bool, g: String, x: Grp, k: Kept) -> Kept:
  match cycle x k:
    case True{} Grp{ms, e} Kept{gs, ns}:
      Kept{
        gs,
        List.append(&2, Logged, ns, [Logged{Spec.Topic.Groups{}, Spec.Notice.GroupKept{g, ms}}])
      }
    case False{} y Kept{gs, ns}:
      Kept{Tables.Table.set(Grp, gs, g, y), ns}

# the groups with x as g when it is later (and closes no cycle)
def Sync.group.later(later: Bool, +g: String, x: Grp, k: Kept) -> Kept:
  match later x k:
    case False{} y z:
      z
    case True{} Grp{+ms, e} Kept{+gs, ns}:
      Sync.group.put(Cycle.has(gs, g, ms), g, Grp{ms, e}, Kept{gs, ns})

# the groups after their group x, named g, met the group that m holds: the
# later epoch wins
def Sync.group.at(m: Maybe<&2, Grp>, +g: String, x: Grp, k: Kept) -> Kept:
  match m x k:
    case None{} Grp{+ms, e} Kept{+gs, ns}:
      Sync.group.put(Cycle.has(gs, g, ms), g, Grp{ms, e}, Kept{gs, ns})
    case Some{Grp{ns, f}} Grp{ms, +e} z:
      Sync.group.later(Nat.is_lt(f, e), g, Grp{ms, e}, z)

# the groups after the group that vis holds, named g, met them
def Sync.group.seen(+g: String, vis: Maybe<&2, Grp>, k: Kept) -> Kept:
  match vis k:
    case None{} z:
      z
    case Some{x} Kept{+gs, ns}:
      Sync.group.at(Tables.Table.get(Grp, gs, g), g, x, Kept{gs, ns})

# the groups after the group of each key of ks in full met them
def Sync.groups(ks: List<&2, String>, +full: Tables.Table<Grp>, k: Kept) -> Kept:
  match ks:
    case Nil{}:
      k
    case Con{+g, r}:
      Sync.groups(r, full, Sync.group.seen(g, Tables.Table.get(Grp, full, g), k))

def Kept.groups(k: Kept) -> Tables.Table<Grp>:
  match k:
    case Kept{gs, ns}:
      gs

def Kept.news(k: Kept) -> List<&2, Logged>:
  match k:
    case Kept{gs, ns}:
      ns

# s after it took in o, unless their versions collide; it takes in all of o,
# since a position only narrows what the transport sends
def Sync.go(collides: Bool, +s: St, +o: St) -> Out:
  match collides:
    case True{}:
      Out.same(s, Sync.answer(Spec.Sync.Refused{"version ID collision"}))
    case False{}:
      +news = Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o))
      +mix = Sync.branches(
        Tables.Table.keys(Br, St.branches(o)),
        St.branches(o),
        Ver.add(news, St.versions(s)),
        Mix{St.branches(s), St.clashes(s), []}
      )
      +kept = Sync.groups(
        Tables.Table.keys(Grp, St.groups(o)),
        St.groups(o),
        Kept{St.groups(s), []}
      )
      +marked = Sync.marks(
        Tables.Table.keys(Tables.Table<MarkAt>, St.marks(o)),
        St.marks(o),
        Marked{St.marks(s), []}
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
def Step.of(+s: St, r: String, w: String, t: String, q: Spec.Ask) -> Out:
  match q:
    case Spec.Ask.Write{+n, b, base, x}:
      Write.bytes(Content.bytes(s, n, x), s, r, w, t, n, b, base)
    case Spec.Ask.SetBranch{b, p}:
      SetBranch.point(Point.version(s, p), s, r, w, t, b)
    case Spec.Ask.CreateMark{+b, m, x}:
      CreateMark.branch(Tables.Table.get(Br, St.branches(s), b), s, b, m, x)
    case Spec.Ask.Merge{p, b}:
      Merge.point(Point.version(s, p), s, r, w, t, b)
    case Spec.Ask.Resolve{+k, n, x}:
      Resolve.clash(Tables.Table.get(Clash, St.clashes(s), k), s, r, w, t, k, n, x)
    case Spec.Ask.SetOwner{+b, g}:
      SetOwner.branch(Tables.Table.get(Br, St.branches(s), b), s, b, g)
    case Spec.Ask.SetGroup{+g, +ms}:
      SetGroup.on(Cycle.has(St.groups(s), g, ms), s, g, ms)
    case Spec.Ask.Sync{+o, p}:
      Sync.go(
        Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
        s,
        o
      )

# s after out, the answer to the request r: new versions join the ones s
# holds, the answer is kept for retries, and the notices go last
def Node.applied(s: St, r: String, out: Out) -> St & Spec.Answer:
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, +l} Out{nv, nb, nm, ng, nc, news, +a}:
      (
        St{
          k,
          Ver.add(nv, vs),
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
def Node.asked(
  found: Maybe<&2, Seen>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  q: Spec.Ask
) -> St
  & Spec.Answer:
  match found:
    case Some{Seen{a, p}}:
      (s, a)
    case None{}:
      Node.applied(s, r, Step.of(s, r, w, t, q))

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
def Log.of(vs: List<&2, Tables.Row<Ver>>, +n: String) -> List<&2, Tables.Row<Ver>>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Tables.Row{i, Ver{+b, p, a, t}}, r}:
      List.filter.put(
        Tables.Row<Ver>,
        Tables.Row{i, Ver{b, p, a, t}},
        Log.of(r, n),
        Maybe.is_some(&2, List<&2, U32>, Tables.Table.get(List<&2, U32>, b, n))
      )

# the history of the head that m holds, among vs
def Log.history(vs: Tables.Table<Ver>, m: Maybe<&2, String>) -> List<&2, Tables.Row<Ver>>:
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
def Br.epoch.of(m: Maybe<&2, Br>) -> Maybe<&2, Nat>:
  match m:
    case None{}:
      None{}
    case Some{Br{h, o, e, c}}:
      Some{e}

# the node of s owns the branch that m holds
def Owner.in(s: St, m: Maybe<&2, Br>) -> Bool:
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
  Tables.Row<Br>

def Spec.BranchEntry.branch(e):
  match e:
    case Tables.Row{n, b}:
      n

def Spec.BranchEntry.owner(e):
  match e:
    case Tables.Row{n, Br{h, o, x, c}}:
      o

def Spec.BranchEntry.newest(e):
  match e:
    case Tables.Row{n, Br{h, o, x, c}}:
      h

def Spec.LogEntry():
  Tables.Row<Ver>

def Spec.LogEntry.version(e):
  match e:
    case Tables.Row{i, v}:
      i

def Spec.LogEntry.author(e):
  match e:
    case Tables.Row{i, Ver{b, p, a, t}}:
      a

def Spec.LogEntry.time(e):
  match e:
    case Tables.Row{i, Ver{b, p, a, t}}:
      t

def Spec.Node.empty(n):
  St{
    n,
    Tables.Table.new(Ver),
    Tables.Table.new(Br),
    Tables.Table.new(Tables.Table<MarkAt>),
    Tables.Table.new(Grp),
    Tables.Table.new(Clash),
    Tables.Table.new(Seen),
    []
  }

def Spec.Node.position(s):
  List.length(&2, Logged, St.log(s))

def Spec.Node.get_branches(s):
  +s = s
  Tables.Table.rows(Br, Tables.Table.keys(Br, St.branches(s)), St.branches(s))

def Spec.Node.get_log(s, n, b):
  +s = s
  Log.of(Log.history(St.versions(s), Br.head.of(Tables.Table.get(Br, St.branches(s), b))), n)

def Spec.Node.get_content(s, n, p):
  St.content(s, n, p)

def Spec.Node.get_diff(s, n, a, b):
  +s = s
  +n = n
  Diff.of(Piece.of(n), St.content(s, n, a), St.content(s, n, b))

# no format in the core says what an item uses; formats add these
def Spec.Node.get_affects(s, b):
  Nil{}

def Spec.Node.get_impact(s, p):
  Nil{}

def Spec.Node.get_outcome(s, r):
  +s = s
  +r = r
  Outcome.of(
    Tables.Table.get(Seen, St.seen(s), r),
    Ver.taken(St.versions(s), r),
    List.length(&2, Logged, St.log(s))
  )

def Spec.Node.get_changes(s, k, p):
  Logged.pick(k, List.drop(&2, Logged, St.log(s), Maybe.default(&2, Nat, p, 0n)))

def Spec.Node.ask(s, e, q):
  match e:
    case Spec.Envelope{+r, w, t}:
      +s = s
      Node.asked(Tables.Table.get(Seen, St.seen(s), r), s, r, w, t, q)

def Spec.Node.get_epoch(s, b):
  Br.epoch.of(Tables.Table.get(Br, St.branches(s), b))

def Spec.Node.get_head(s, b):
  Br.head.of(Tables.Table.get(Br, St.branches(s), b))

def Spec.Node.is_owner(s, b):
  +s = s
  Owner.in(s, Tables.Table.get(Br, St.branches(s), b))

def Spec.Node.is_inside(s, m, g):
  Grp.inside(St.groups(s), m, g)

# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Lemmas
# ------

# the parts of out
def Out.versions(out: Out) -> List<&2, Tables.Row<Ver>>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nv

def Out.branches(out: Out) -> Tables.Table<Br>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nb

def Out.marks(out: Out) -> Tables.Table<Tables.Table<MarkAt>>:
  match out:
    case Out{nv, nb, nm, ng, nc, news, a}:
      nm

def Out.groups(out: Out) -> Tables.Table<Grp>:
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
def Node.news(
  found: Maybe<&2, Seen>,
  s: St,
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
  for s: St
  for r: String
  for out: Out
  {
    St.log(
      Pair.fst(St, Spec.Answer, Node.applied(s, r, out))
    )
      == List.append(&2, Logged, St.log(s), Out.news(out)): List<&2, Logged>
  }

def applied_log(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a change, or its retry, appends its notices to the log
law asked_log:
  for found: Maybe<&2, Seen>
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    St.log(
      Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q))
    )
      == List.append(&2, Logged, St.log(s), Node.news(found, s, r, w, t, q)): List<&2, Logged>
  }

def asked_log(found, s, r, w, t, q):
  match found:
    case Some{Seen{a, p}}:
      Equal.sym(
        List<&2, Logged>,
        List.append(&2, Logged, St.log(s), []),
        St.log(s),
        Lists.List.append_nil(Logged, St.log(s))
      )
    case None{}:
      +s = s
      +r = r
      applied_log(s, r, Step.of(s, r, w, t, q))

# the notices after a change or a retry split at the position before it
law since_asked:
  for found: Maybe<&2, Seen>
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for k: Spec.Topic
  {
    Spec.Node.get_changes(
      Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q)),
      k,
      None{}
    )
      == List.append(
        &2,
        Spec.Notice,
        Spec.Node.get_changes(s, k, None{}),
        Spec.Node.get_changes(
          Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q)),
          k,
          Some{Spec.Node.position(s)}
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
    St.log(Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q))),
    List.append(&2, Logged, St.log(s), Node.news(found, s, r, w, t, q)),
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
          Logged.pick(k, List.drop(&2, Logged, St.log(s), 0n)),
          Logged.pick(k, List.drop(&2, Logged, _, List.length(&2, Logged, St.log(s))))
        ): List<&2, Spec.Notice>
    }
  since_on(k, St.log(s), Node.news(found, s, r, w, t, q))

# the notices after any change split at the position before it
law since_ask:
  for s: St
  for e: Spec.Envelope
  for q: Spec.Ask
  for k: Spec.Topic
  {
    Spec.Node.get_changes(
      Pair.fst(St, Spec.Answer, Spec.Node.ask(s, e, q)),
      k,
      None{}
    )
      == List.append(
        &2,
        Spec.Notice,
        Spec.Node.get_changes(s, k, None{}),
        Spec.Node.get_changes(
          Pair.fst(St, Spec.Answer, Spec.Node.ask(s, e, q)),
          k,
          Some{Spec.Node.position(s)}
        )
      ): List<&2, Spec.Notice>
  }

def since_ask(s, e, q, k):
  match e:
    case Spec.Envelope{+r, w, t}:
      +s = s
      since_asked(Tables.Table.get(Seen, St.seen(s), r), s, r, w, t, q, k)

# after a change, the node keeps its answer under its request ID
law seen_after_applied:
  for s: St
  for r: String
  for out: Out
  {
    Seen.answer.of(
      Tables.Table.get(Seen, St.seen(Pair.fst(St, Spec.Answer, Node.applied(s, r, out))), r)
    )
      == Some{Pair.snd(St, Spec.Answer, Node.applied(s, r, out))}: Maybe<&2, Spec.Answer>
  }

def seen_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
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
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    Tables.Table.get(Seen, St.seen(s), r) == found: Maybe<&2, Seen>
  } -> {
    Seen.answer.of(
      Tables.Table.get(
        Seen,
        St.seen(Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q))),
        r
      )
    )
      == Some{Pair.snd(St, Spec.Answer, Node.asked(found, s, r, w, t, q))}: Maybe<&2, Spec.Answer>
  }

def seen_after_asked(found, s, r, w, t, q):
  match found:
    case Some{Seen{a, p}}:
      h =>
        +s = s
        +r = r
        %Equal.sym(Maybe<&2, Seen>, Tables.Table.get(Seen, St.seen(s), r), Some{Seen{a, p}}, h):
          {Seen.answer.of(_) == Some{a}: Maybe<&2, Spec.Answer>}
        {==}
    case None{}:
      h =>
        +s = s
        +r = r
        seen_after_applied(s, r, Step.of(s, r, w, t, q))

# after a change of the request r, the node keeps its answer under r
law seen_after_ask:
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  {
    Seen.answer.of(
      Tables.Table.get(
        Seen,
        St.seen(Pair.fst(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t}, q))),
        r
      )
    )
      == Some{
        Pair.snd(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t}, q))
      }: Maybe<&2, Spec.Answer>
  }

def seen_after_ask(s, r, w, t, q):
  +s = s
  +r = r
  seen_after_asked(Tables.Table.get(Seen, St.seen(s), r), s, r, w, t, q)({==})

# a request whose answer the node keeps gets that answer, and changes nothing
law asked_found:
  for found: Maybe<&2, Seen>
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for a: Spec.Answer
  {
    Seen.answer.of(found) == Some{a}: Maybe<&2, Spec.Answer>
  } -> {Node.asked(found, s, r, w, t, q) == (s, a): St & Spec.Answer}

def asked_found(found, s, r, w, t, q, a):
  match found:
    case None{}:
      h => Empty.absurd(
        {Node.asked(None{}, s, r, w, t, q) == (s, a): St & Spec.Answer},
        Maybes.Maybe.none_ne_some(Spec.Answer, a, h)
      )
    case Some{Seen{b, p}}:
      h =>
        %Maybes.Maybe.some_inj(Spec.Answer, b, a, h): {(s, b) == (s, _): St & Spec.Answer}
        {==}

# the versions after a change are its new ones joined to the old
law versions_after_applied:
  for s: St
  for r: String
  for out: Out
  {
    St.versions(
      Pair.fst(St, Spec.Answer, Node.applied(s, r, out))
    )
      == Ver.add(Out.versions(out), St.versions(s)): Tables.Table<Ver>
  }

def versions_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# adding a version keeps one found by another key: by whether the keys are the
# same (hit)
law put_keeps.at:
  for hit: Bool
  for i: String
  for x: Ver
  for vs: Tables.Table<Ver>
  for v: String
  for u: Ver
  {
    String.eq(i, v) == hit: Bool
  } -> {
    Ver.has(vs, i) == False{}: Bool
  } -> {
    Tables.Table.get(Ver, vs, v) == Some{u}: Maybe<&2, Ver>
  } -> {
    Bools.Bool.when(
      Maybe<&2, Ver>,
      hit,
      z => Some{x},
      z => Tables.Table.get(Ver, vs, v)
    )
      == Some{u}: Maybe<&2, Ver>
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
              Maybe<&2, Ver>,
              True{},
              z => Some{x},
              z => Tables.Table.get(Ver, vs, v)
            )
              == Some{u}: Maybe<&2, Ver>
          },
          Shared.Bool.false_ne_true(
            Equal.sym(
              Bool,
              True{},
              False{},
              Equal.trans(
                Bool,
                True{},
                Ver.has(vs, v),
                False{},
                Equal.sym(
                  Bool,
                  Ver.has(vs, v),
                  True{},
                  Equal.cong(
                    Maybe<&2, Ver>,
                    Bool,
                    m => Maybe.is_some(&2, Ver, m),
                    Tables.Table.get(Ver, vs, v),
                    Some{u},
                    hf
                  )
                ),
                Equal.trans(
                  Bool,
                  Ver.has(vs, v),
                  Ver.has(vs, i),
                  False{},
                  Equal.sym(
                    Bool,
                    Ver.has(vs, i),
                    Ver.has(vs, v),
                    Equal.cong(
                      String,
                      Bool,
                      k => Ver.has(vs, k),
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
  for x: Ver
  for vs: Tables.Table<Ver>
  for v: String
  for u: Ver
  {
    Ver.has(vs, i) == held: Bool
  } -> {
    Tables.Table.get(Ver, vs, v) == Some{u}: Maybe<&2, Ver>
  } -> {Tables.Table.get(Ver, Ver.add.put(i, x, vs, held), v) == Some{u}: Maybe<&2, Ver>}

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
          Maybe<&2, Ver>,
          Tables.Table.get(Ver, Tables.Table.set(Ver, vs, i, x), v),
          Bools.Bool.when(
            Maybe<&2, Ver>,
            String.eq(i, v),
            z => Some{x},
            z => Tables.Table.get(Ver, vs, v)
          ),
          Tables.Table.get_set(Ver, vs, i, x, v)
        ):
          {_ == Some{u}: Maybe<&2, Ver>}
        put_keeps.at(String.eq(i, v), i, x, vs, v, u)({==})(hh)(hf)

# adding one version keeps every version that was found
law add_one_keeps:
  for c: Tables.Row<Ver>
  for vs: Tables.Table<Ver>
  for v: String
  for u: Ver
  {
    Tables.Table.get(Ver, vs, v) == Some{u}: Maybe<&2, Ver>
  } -> {Tables.Table.get(Ver, Ver.add.one(c, vs), v) == Some{u}: Maybe<&2, Ver>}

def add_one_keeps(c, vs, v, u):
  match c:
    case Tables.Row{+i, x}:
      +vs = vs
      put_keeps(Ver.has(vs, i), i, x, vs, v, u)({==})

# adding versions keeps every version that was found
law add_keeps:
  for news: List<&2, Tables.Row<Ver>>
  for vs: Tables.Table<Ver>
  for v: String
  for u: Ver
  {
    Tables.Table.get(Ver, vs, v) == Some{u}: Maybe<&2, Ver>
  } -> {Tables.Table.get(Ver, Ver.add(news, vs), v) == Some{u}: Maybe<&2, Ver>}

def add_keeps(news, vs, v, u):
  match news:
    case Nil{}:
      h => h
    case Con{+c, r}:
      h =>
        +vs = vs
        +v = v
        +u = u
        add_keeps(r, Ver.add.one(c, vs), v, u)(add_one_keeps(c, vs, v, u)(h))

# the bytes of a resource of the version that m holds stay, when that version
# stays
law kept_at:
  for m: Maybe<&2, Ver>
  for vs: Tables.Table<Ver>
  for ws: Tables.Table<Ver>
  for v: String
  for n: String
  for x: List<&2, U32>
  {
    Tables.Table.get(Ver, vs, v) == m: Maybe<&2, Ver>
  } -> (
    @u: Ver -> {
      Tables.Table.get(Ver, vs, v) == Some{u}: Maybe<&2, Ver>
    } -> {Tables.Table.get(Ver, ws, v) == Some{u}: Maybe<&2, Ver>}
  ) -> {
    Blob.find.of(Ver.blobs.of(m), n) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {
    Blob.find.of(Ver.blobs.of(Tables.Table.get(Ver, ws, v)), n) == Some{x}: Maybe<&2, List<&2, U32>>
  }

def kept_at(m, vs, ws, v, n, x):
  match m:
    case None{}:
      he => hk => hc => Empty.absurd(
        {
          Blob.find.of(
            Ver.blobs.of(Tables.Table.get(Ver, ws, v)),
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
        %Equal.sym(Maybe<&2, Ver>, Tables.Table.get(Ver, ws, v), Some{u}, hk(u)(he)):
          {Blob.find.of(Ver.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        hc

# a change or a retry keeps every version that existed, with its content
law kept_asked:
  for found: Maybe<&2, Seen>
  for s: St
  for r: String
  for w: String
  for t: String
  for q: Spec.Ask
  for n: String
  for v: String
  for x: List<&2, U32>
  {
    St.content(s, n, Spec.Point.At{v}) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {
    St.content(
      Pair.fst(St, Spec.Answer, Node.asked(found, s, r, w, t, q)),
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
          Tables.Table<Ver>,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r, Step.of(s, r, w, t, q)))),
          Ver.add(Out.versions(Step.of(s, r, w, t, q)), St.versions(s)),
          versions_after_applied(s, r, Step.of(s, r, w, t, q))
        ):
          {
            Blob.find.of(
              Ver.blobs.of(Tables.Table.get(Ver, _, v)),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        kept_at(
          Tables.Table.get(Ver, St.versions(s), v),
          St.versions(s),
          Ver.add(Out.versions(Step.of(s, r, w, t, q)), St.versions(s)),
          v,
          n,
          x
        )({==})(u => add_keeps(Out.versions(Step.of(s, r, w, t, q)), St.versions(s), v, u))(h)

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
  for vs: Tables.Table<Ver>
  for k: String
  {Ver.taken(vs, k) == False{}: Bool} -> {Ver.has(vs, k) == False{}: Bool}

def taken_free(vs, k):
  +vs = vs
  +k = k
  Bools.Bool.or_false_left(Ver.has(vs, k), Ver.named(Tables.Table.keys(Ver, vs), vs, k))

# a new request has no kept answer
law new_found:
  for s: St
  for r: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {Tables.Table.get(Seen, St.seen(s), r) == None{}: Maybe<&2, Seen>}

def new_found(s, r):
  h =>
    +s = s
    +r = r
    Pair.fst(
      {Tables.Table.get(Seen, St.seen(s), r) == None{}: Maybe<&2, Seen>},
      {Ver.taken(St.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, St.seen(s), r),
        Ver.taken(St.versions(s), r),
        List.length(&2, Logged, St.log(s))
      )(h)
    )

# no version has the ID of a new request
law new_free:
  for s: St
  for r: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {Ver.taken(St.versions(s), r) == False{}: Bool}

def new_free(s, r):
  h =>
    +s = s
    +r = r
    Pair.snd(
      {Tables.Table.get(Seen, St.seen(s), r) == None{}: Maybe<&2, Seen>},
      {Ver.taken(St.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, St.seen(s), r),
        Ver.taken(St.versions(s), r),
        List.length(&2, Logged, St.log(s))
      )(h)
    )

# a new request runs its change, and the node keeps its answer
law ask_step:
  for s: St
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  for t: St
  for a: Spec.Answer
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(s, Spec.Envelope{r, w, z}, q) == (t, a): St & Spec.Answer
  } -> {Node.applied(s, r, Step.of(s, r, w, z, q)) == (t, a): St & Spec.Answer}

def ask_step(s, r, w, z, q, t, a):
  hn => h =>
    +s = s
    +r = r
    %new_found(s, r)(hn): {Node.asked(_, s, r, w, z, q) == (t, a): St & Spec.Answer}
    h

# a change whose result is (t, a) answers a
law applied_answer:
  for s: St
  for r: String
  for out: Out
  for t: St
  for a: Spec.Answer
  {Node.applied(s, r, out) == (t, a): St & Spec.Answer} -> {Out.answer(out) == a: Spec.Answer}

def applied_answer(s, r, out, t, a):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, b}:
      h => Equal.cong(
        St & Spec.Answer,
        Spec.Answer,
        x => Pair.snd(St, Spec.Answer, x),
        Node.applied(St{k, vs, bs, ms, gs, cs, ss, l}, r, Out{nv, nb, nm, ng, nc, news, b}),
        (t, a),
        h
      )

# a change whose result is (t, a) leaves the node as t
law applied_state:
  for s: St
  for r: String
  for out: Out
  for t: St
  for a: Spec.Answer
  {
    Node.applied(s, r, out) == (t, a): St & Spec.Answer
  } -> {Pair.fst(St, Spec.Answer, Node.applied(s, r, out)) == t: St}

def applied_state(s, r, out, t, a):
  h => Equal.cong(
    St & Spec.Answer,
    St,
    x => Pair.fst(St, Spec.Answer, x),
    Node.applied(s, r, out),
    (t, a),
    h
  )

# the answer after a change is the change's
law answer_after_applied:
  for s: St
  for r: String
  for out: Out
  {Pair.snd(St, Spec.Answer, Node.applied(s, r, out)) == Out.answer(out): Spec.Answer}

def answer_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# the branches after a change are the change's
law branches_after_applied:
  for s: St
  for r: String
  for out: Out
  {
    St.branches(
      Pair.fst(St, Spec.Answer, Node.applied(s, r, out))
    )
      == Out.branches(out): Tables.Table<Br>
  }

def branches_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# the groups after a change are the change's
law groups_after_applied:
  for s: St
  for r: String
  for out: Out
  {
    St.groups(
      Pair.fst(St, Spec.Answer, Node.applied(s, r, out))
    )
      == Out.groups(out): Tables.Table<Grp>
  }

def groups_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a version whose ID is new is found after it is added
law add_new_find:
  for r: String
  for bl: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w: String
  for z: String
  for vs: Tables.Table<Ver>
  {
    Ver.has(vs, r) == False{}: Bool
  } -> {
    Tables.Table.get(
      Ver,
      Ver.add([Tables.Row{r, Ver{bl, ps, w, z}}], vs),
      r
    )
      == Some{Ver{bl, ps, w, z}}: Maybe<&2, Ver>
  }

def add_new_find(r, bl, ps, w, z, vs):
  hh =>
    +r = r
    +vs = vs
    +bl = bl
    +ps = ps
    +w = w
    +z = z
    %Equal.sym(Bool, Ver.has(vs, r), False{}, hh):
      {
        Tables.Table.get(
          Ver,
          Ver.add.put(r, Ver{bl, ps, w, z}, vs, _),
          r
        )
          == Some{Ver{bl, ps, w, z}}: Maybe<&2, Ver>
      }
    Tables.Table.get_after_set(Ver, vs, r, Ver{bl, ps, w, z})

# a write on the head v of the branch that m holds, as its owner, is written
law write_on_head:
  for m: Maybe<&2, Br>
  for s: St
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for v: String
  for x: List<&2, U32>
  {
    Br.head.of(m) == Some{v}: Maybe<&2, String>
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
    case Some{Br{h, o, e, c}}:
      hh => ho =>
        +s = s
        +r = r
        +v = v
        %Equal.sym(Bool, Owner.of(s, Br{h, o, e, c}), True{}, ho):
          {
            Out.answer(
              Write.on(_, s, r, w, t, n, b, Some{v}, x, Br{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        %Equal.sym(String, h, v, Maybes.Maybe.some_inj(String, h, v, hh)):
          {
            Out.answer(
              Write.at(String.eq(v, _), s, r, w, t, n, b, x, Br{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        %Equal.sym(Bool, String.eq(v, v), True{}, Strings.String.eq_refl(v)):
          {
            Out.answer(
              Write.at(_, s, r, w, t, n, b, x, Br{h, o, e, c})
            )
              == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer
          }
        {==}

# a write as the owner that answers Written: the head holds the bytes
law raw_at:
  for ok: Bool
  for s: St
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
    Ver.taken(St.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.at(ok, s, r, w, z, n, b, x, Br{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Ver.find.of(
          Ver.add(Out.versions(Write.at(ok, s, r, w, z, n, b, x, Br{h, o, e, c})), St.versions(s)),
          Br.head.of(
            Tables.Table.get(Br, Out.branches(Write.at(ok, s, r, w, z, n, b, x, Br{h, o, e, c})), b)
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
            Ver.blobs.of(
              Ver.find.of(
                Ver.add(
                  Out.versions(Write.at(False{}, s, r, w, z, n, b, x, Br{h, o, e, c})),
                  St.versions(s)
                ),
                Br.head.of(
                  Tables.Table.get(
                    Br,
                    Out.branches(Write.at(False{}, s, r, w, z, n, b, x, Br{h, o, e, c})),
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
          Maybe<&2, Br>,
          Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s), b, Br{r, o, e, 1n+c}), b),
          Some{Br{r, o, e, 1n+c}},
          Tables.Table.get_after_set(Br, St.branches(s), b, Br{r, o, e, 1n+c})
        ):
          {
            Blob.find.of(
              Ver.blobs.of(
                Ver.find.of(
                  Ver.add(
                    [
                      Tables.Row{
                        r,
                        Ver{
                          Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
                          [h],
                          w,
                          z
                        }
                      }
                    ],
                    St.versions(s)
                  ),
                  Br.head.of(_)
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        %Equal.sym(
          Maybe<&2, Ver>,
          Tables.Table.get(
            Ver,
            Ver.add(
              [
                Tables.Row{
                  r,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
                    [h],
                    w,
                    z
                  }
                }
              ],
              St.versions(s)
            ),
            r
          ),
          Some{
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          },
          add_new_find(
            r,
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
            [h],
            w,
            z,
            St.versions(s)
          )(taken_free(St.versions(s), r)(hh))
        ):
          {Blob.find.of(Ver.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tables.Table.get_after_set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x)

# a write on a branch, as its owner or not, that answers Written
law raw_on:
  for owner: Bool
  for s: St
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
    Ver.taken(St.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.on(owner, s, r, w, z, n, b, base, x, Br{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Ver.find.of(
          Ver.add(
            Out.versions(Write.on(owner, s, r, w, z, n, b, base, x, Br{h, o, e, c})),
            St.versions(s)
          ),
          Br.head.of(
            Tables.Table.get(
              Br,
              Out.branches(Write.on(owner, s, r, w, z, n, b, base, x, Br{h, o, e, c})),
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
            Ver.blobs.of(
              Ver.find.of(
                Ver.add(
                  Out.versions(Write.on(False{}, s, r, w, z, n, b, base, x, Br{h, o, e, c})),
                  St.versions(s)
                ),
                Br.head.of(
                  Tables.Table.get(
                    Br,
                    Out.branches(Write.on(False{}, s, r, w, z, n, b, base, x, Br{h, o, e, c})),
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
  for m: Maybe<&2, Br>
  for s: St
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for v: String
  {
    Ver.taken(St.versions(s), r) == False{}: Bool
  } -> {
    Out.answer(
      Write.branch(m, s, r, w, z, n, b, base, x)
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Ver.find.of(
          Ver.add(Out.versions(Write.branch(m, s, r, w, z, n, b, base, x)), St.versions(s)),
          Br.head.of(
            Tables.Table.get(Br, Out.branches(Write.branch(m, s, r, w, z, n, b, base, x)), b)
          )
        )
      ),
      n
    )
      == Some{x}: Maybe<&2, List<&2, U32>>
  }

def raw_branch(m, s, r, w, z, n, b, base, x, v):
  match m base:
    case Some{Br{+h, +o, +e, +c}} k:
      +s = s
      raw_on(Owner.of(s, Br{h, o, e, c}), s, r, w, z, n, b, k, x, h, o, e, c, v)
    case None{} Some{k}:
      hh => ha => Empty.absurd(
        {
          Blob.find.of(
            Ver.blobs.of(
              Ver.find.of(
                Ver.add(
                  Out.versions(Write.branch(None{}, s, r, w, z, n, b, Some{k}, x)),
                  St.versions(s)
                ),
                Br.head.of(
                  Tables.Table.get(
                    Br,
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
          Maybe<&2, Br>,
          Tables.Table.get(
            Br,
            Tables.Table.set(Br, St.branches(s), b, Br{r, St.self(s), 0n, 0n}),
            b
          ),
          Some{Br{r, St.self(s), 0n, 0n}},
          Tables.Table.get_after_set(Br, St.branches(s), b, Br{r, St.self(s), 0n, 0n})
        ):
          {
            Blob.find.of(
              Ver.blobs.of(
                Ver.find.of(
                  Ver.add(
                    [
                      Tables.Row{
                        r,
                        Ver{
                          Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
                          [],
                          w,
                          z
                        }
                      }
                    ],
                    St.versions(s)
                  ),
                  Br.head.of(_)
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        %Equal.sym(
          Maybe<&2, Ver>,
          Tables.Table.get(
            Ver,
            Ver.add(
              [
                Tables.Row{
                  r,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
                    [],
                    w,
                    z
                  }
                }
              ],
              St.versions(s)
            ),
            r
          ),
          Some{
            Ver{Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x), [], w, z}
          },
          add_new_find(
            r,
            Tables.Table.set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x),
            [],
            w,
            z,
            St.versions(s)
          )(taken_free(St.versions(s), r)(hh))
        ):
          {Blob.find.of(Ver.blobs.of(_), n) == Some{x}: Maybe<&2, List<&2, U32>>}
        Tables.Table.get_after_set(List<&2, U32>, Tables.Table.new(List<&2, U32>), n, x)

# a write that answers Written, unless its version ID is taken
law raw_free:
  for taken: Bool
  for s: St
  for r: String
  for w: String
  for z: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for v: String
  {
    Ver.taken(St.versions(s), r) == taken: Bool
  } -> {
    Out.answer(
      Write.free(taken, s, r, w, z, n, b, base, x)
    )
      == Spec.Answer.Write{Spec.Write.Written{v}}: Spec.Answer
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Ver.find.of(
          Ver.add(Out.versions(Write.free(taken, s, r, w, z, n, b, base, x)), St.versions(s)),
          Br.head.of(
            Tables.Table.get(Br, Out.branches(Write.free(taken, s, r, w, z, n, b, base, x)), b)
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
            Ver.blobs.of(
              Ver.find.of(
                Ver.add(
                  Out.versions(Write.free(True{}, s, r, w, z, n, b, base, x)),
                  St.versions(s)
                ),
                Br.head.of(
                  Tables.Table.get(
                    Br,
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
        raw_branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, z, n, b, base, x, v)(hh)

# a change that adds no version and keeps the branches and marks keeps the
# content at every point
law same_content_out:
  for s: St
  for r: String
  for cs: Tables.Table<Clash>
  for news: List<&2, Logged>
  for a: Spec.Answer
  for n: String
  for p: Spec.Point
  {
    St.content(
      Pair.fst(
        St,
        Spec.Answer,
        Node.applied(s, r, Out{[], St.branches(s), St.marks(s), St.groups(s), cs, news, a})
      ),
      n,
      p
    )
      == St.content(s, n, p): Maybe<&2, List<&2, U32>>
  }

def same_content_out(s, r, cs, news, a, n, p):
  match s p:
    case St{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.At{v}:
      {==}
    case St{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.Head{b}:
      {==}
    case St{k, vs, bs, ms, gs, c2, ss, l} Spec.Point.Mark{b, m}:
      {==}

# a stale write as the owner: its base is not the head (ok is False)
law stale_at:
  for ok: Bool
  for s: St
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
      Write.at(ok, s, r, w, z, n, b, y, Br{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(s, r, Write.at(ok, s, r, w, z, n, b, y, Br{h, o, e, c}))
    ),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_at(ok, s, r, w, z, n, b, y, h, o, e, c, base, cur):
  match ok:
    case True{}:
      hb => ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.at(True{}, s, r, w, z, n, b, y, Br{h, o, e, c}))
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
            St.clashes(s),
            [],
            Spec.Answer.Write{Spec.Write.Stale{h}},
            n2,
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
  for s: St
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
      Write.on(owner, s, r, w, z, n, b, base, y, Br{h, o, e, c})
    )
      == Spec.Answer.Write{Spec.Write.Stale{cur}}: Spec.Answer
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(s, r, Write.on(owner, s, r, w, z, n, b, base, y, Br{h, o, e, c}))
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
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.on(False{}, s, r, w, z, n, b, base, y, Br{h, o, e, c}))
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
  for m: Maybe<&2, Br>
  for s: St
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
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(s, r, Write.branch(m, s, r, w, z, n, b, base, y))),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_branch(m, s, r, w, z, n, b, base, y, cur):
  match m base:
    case Some{Br{+h, +o, +e, +c}} k:
      +s = s
      stale_on(Owner.of(s, Br{h, o, e, c}), s, r, w, z, n, b, k, y, h, o, e, c, cur)
    case None{} Some{k}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.branch(None{}, s, r, w, z, n, b, Some{k}, y))
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
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.branch(None{}, s, r, w, z, n, b, None{}, y))
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
  for s: St
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
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(s, r, Write.free(taken, s, r, w, z, n, b, base, y))),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_free(taken, s, r, w, z, n, b, base, y, cur):
  match taken:
    case True{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.free(True{}, s, r, w, z, n, b, base, y))
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
      stale_branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, z, n, b, base, y, cur)

# a stale write of the bytes that m holds
law stale_bytes:
  for m: Maybe<&2, List<&2, U32>>
  for s: St
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
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(s, r, Write.bytes(m, s, r, w, z, n, b, base))),
    s
  )
    & {base != Some{cur}: Maybe<&2, String>}

def stale_bytes(m, s, r, w, z, n, b, base, cur):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Write.bytes(None{}, s, r, w, z, n, b, base))
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
      stale_free(Ver.taken(St.versions(s), r), s, r, w, z, n, b, base, y, cur)

# a merge that clashed on the names cl: no content changes, and its one new
# notice on the branch is the conflict
law cf_result:
  for cl: List<&2, String>
  for s: St
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
      Merge.result(cl, s, r, w, z, f, b, bs, Br{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(s, r, Merge.result(cl, s, r, w, z, f, b, bs, Br{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.Node.get_changes(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(s, r, Merge.result(cl, s, r, w, z, f, b, bs, Br{h, o, e, c}))
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.Node.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_result(cl, s, r, w, z, f, b, bs, h, o, e, c, k):
  match cl:
    case Nil{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Merge.result(Nil{}, s, r, w, z, f, b, bs, Br{h, o, e, c}))
          ),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(s, r, Merge.result(Nil{}, s, r, w, z, f, b, bs, Br{h, o, e, c}))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
            Tables.Table.set(Clash, St.clashes(s), r, Clash{b, h, f, bs, x <> more}),
            [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}],
            Spec.Answer.Merge{Spec.Merge.Conflicted{r}},
            n2,
            p2
          ),
          (
            %Equal.sym(List<&2, Logged>, St.log(Pair.fst(St, Spec.Answer, Node.applied(s, r, Out{[], St.branches(s), St.marks(s), St.groups(s), Tables.Table.set(Clash, St.clashes(s), r, Clash{b, h, f, bs, x <> more}), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Spec.Answer.Merge{Spec.Merge.Conflicted{r}}}))), List.append(&2, Logged, St.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}]), applied_log(s, r, Out{[], St.branches(s), St.marks(s), St.groups(s), Tables.Table.set(Clash, St.clashes(s), r, Clash{b, h, f, bs, x <> more}), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Spec.Answer.Merge{Spec.Merge.Conflicted{r}}})):
              {Logged.pick(Spec.Topic.Conflicts{b}, List.drop(&2, Logged, _, List.length(&2, Logged, St.log(s)))) == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>}
            %Equal.sym(List<&2, Logged>, List.drop(&2, Logged, List.append(&2, Logged, St.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}]), List.length(&2, Logged, St.log(s))), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}], Lists.List.drop_after_append(Logged, St.log(s), [Logged{Spec.Topic.Conflicts{b}, Spec.Notice.Conflicted{r}}])):
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
  for s: St
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
      Merge.inside(held, s, r, w, z, f, b, Br{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(s, r, Merge.inside(held, s, r, w, z, f, b, Br{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.Node.get_changes(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(s, r, Merge.inside(held, s, r, w, z, f, b, Br{h, o, e, c}))
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.Node.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_inside(held, s, r, w, z, f, b, h, o, e, c, k):
  match held:
    case True{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Merge.inside(True{}, s, r, w, z, f, b, Br{h, o, e, c}))
          ),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(s, r, Merge.inside(True{}, s, r, w, z, f, b, Br{h, o, e, c}))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
                  History.of(St.versions(s), f),
                  Vers.ids(History.of(St.versions(s), h))
                )
              )
            ),
            Strings.union(
              Tables.Table.keys(List<&2, U32>, Vers.blobs(St.versions(s), f)),
              Strings.union(Tables.Table.keys(List<&2, U32>, Vers.blobs(St.versions(s), h)), [])
            )
          ),
          Vers.blobs(St.versions(s), h),
          Vers.blobs(St.versions(s), f),
          Merge.base(
            s,
            Vers.first_in(History.of(St.versions(s), f), Vers.ids(History.of(St.versions(s), h)))
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
                  History.of(St.versions(s), f),
                  Vers.ids(History.of(St.versions(s), h))
                )
              )
            ),
            Strings.union(
              Tables.Table.keys(List<&2, U32>, Vers.blobs(St.versions(s), f)),
              Strings.union(Tables.Table.keys(List<&2, U32>, Vers.blobs(St.versions(s), h)), [])
            )
          ),
          Vers.blobs(St.versions(s), h),
          Vers.blobs(St.versions(s), f),
          Merge.base(
            s,
            Vers.first_in(History.of(St.versions(s), f), Vers.ids(History.of(St.versions(s), h)))
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
  for s: St
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
      Merge.owner(owner, taken, s, r, w, z, f, b, Br{h, o, e, c})
    )
      == Spec.Answer.Merge{Spec.Merge.Conflicted{k}}: Spec.Answer
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(s, r, Merge.owner(owner, taken, s, r, w, z, f, b, Br{h, o, e, c}))
    ),
    s
  )
    & {
      Spec.Node.get_changes(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(s, r, Merge.owner(owner, taken, s, r, w, z, f, b, Br{h, o, e, c}))
        ),
        Spec.Topic.Conflicts{b},
        Some{Spec.Node.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_owner(owner, taken, s, r, w, z, f, b, h, o, e, c, k):
  match owner taken:
    case False{} _:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Merge.owner(False{}, taken, s, r, w, z, f, b, Br{h, o, e, c}))
          ),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(s, r, Merge.owner(False{}, taken, s, r, w, z, f, b, Br{h, o, e, c}))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
        Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(s, r, Merge.owner(True{}, True{}, s, r, w, z, f, b, Br{h, o, e, c}))
          ),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(s, r, Merge.owner(True{}, True{}, s, r, w, z, f, b, Br{h, o, e, c}))
              ),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
        Strings.has(Vers.ids(History.of(St.versions(s), h)), f),
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
  for m: Maybe<&2, Br>
  for s: St
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
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.branch(m, s, r, w, z, f, b))),
    s
  )
    & {
      Spec.Node.get_changes(
        Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.branch(m, s, r, w, z, f, b))),
        Spec.Topic.Conflicts{b},
        Some{Spec.Node.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_branch(m, s, r, w, z, f, b, k):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.branch(None{}, s, r, w, z, f, b))),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.branch(None{}, s, r, w, z, f, b))),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
    case Some{Br{+h, +o, +e, +c}}:
      +s = s
      +r = r
      cf_owner(
        Owner.of(s, Br{h, o, e, c}),
        Ver.taken(St.versions(s), r),
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
  for s: St
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
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.point(m, s, r, w, z, b))),
    s
  )
    & {
      Spec.Node.get_changes(
        Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.point(m, s, r, w, z, b))),
        Spec.Topic.Conflicts{b},
        Some{Spec.Node.position(s)}
      )
        == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>
    }

def cf_point(m, s, r, w, z, b, k):
  match m:
    case None{}:
      ha => Empty.absurd(
        Spec.Node.SameContent(
          Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.point(None{}, s, r, w, z, b))),
          s
        )
          & {
            Spec.Node.get_changes(
              Pair.fst(St, Spec.Answer, Node.applied(s, r, Merge.point(None{}, s, r, w, z, b))),
              Spec.Topic.Conflicts{b},
              Some{Spec.Node.position(s)}
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
      cf_branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, z, f, b, k)

# a set-owner on the branch b, of epoch e, that answers Set{new}, gives b a
# larger epoch, new
law set_owner_on:
  for own: Bool
  for s: St
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
      SetOwner.on(own, s, b, g, Br{h, o, e, c})
    )
      == Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}: Spec.Answer
  } -> {
    Nat.is_lt(old, new) == True{}: Bool
  }
    & {
      Br.epoch.of(
        Tables.Table.get(Br, Out.branches(SetOwner.on(own, s, b, g, Br{h, o, e, c})), b)
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
              Br.epoch.of(
                Tables.Table.get(Br, Out.branches(SetOwner.on(False{}, s, b, g, Br{h, o, e, c})), b)
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
            %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s), b, Br{h, g, 1n+e, 0n}), b), Some{Br{h, g, 1n+e, 0n}}, Tables.Table.get_after_set(Br, St.branches(s), b, Br{h, g, 1n+e, 0n})):
              {Br.epoch.of(_) == Some{new}: Maybe<&2, Nat>}
            %Equal.cong(Spec.Answer, Nat, x => Answer.epoch(x), Spec.Answer.SetOwner{Spec.SetOwner.Set{1n+e}}, Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}, ha):
              {Some{1n+e} == Some{_}: Maybe<&2, Nat>}
            {==}))

# a set-owner on the branch that m holds, of epoch old, that answers Set{new},
# gives b a larger epoch, new
law set_owner_lemma:
  for m: Maybe<&2, Br>
  for s: St
  for b: String
  for g: String
  for old: Nat
  for new: Nat
  {
    Br.epoch.of(m) == Some{old}: Maybe<&2, Nat>
  } -> {
    Out.answer(
      SetOwner.branch(m, s, b, g)
    )
      == Spec.Answer.SetOwner{Spec.SetOwner.Set{new}}: Spec.Answer
  } -> {
    Nat.is_lt(old, new) == True{}: Bool
  }
    & {
      Br.epoch.of(
        Tables.Table.get(Br, Out.branches(SetOwner.branch(m, s, b, g)), b)
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
              Br.epoch.of(
                Tables.Table.get(Br, Out.branches(SetOwner.branch(None{}, s, b, g)), b)
              )
                == Some{new}: Maybe<&2, Nat>
            },
          Maybes.Maybe.none_ne_some(Nat, old, hep)
        )
    case Some{Br{+h, +o, +e, +c}}:
      hep => ha =>
        +s = s
        set_owner_on(
          Owner.of(s, Br{h, o, e, c}),
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
    case Spec.Member.Node{k}:
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
    case Spec.Member.Node{x} Spec.Member.Node{y}:
      h => Equal.cong(
        String,
        Spec.Member,
        z => Spec.Member.Node{z},
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
    case Spec.Member.Node{x} Spec.Member.Group{y}:
      h => Empty.absurd(
        {Spec.Member.Node{x} == Spec.Member.Group{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.Group{x} Spec.Member.Node{y}:
      h => Empty.absurd(
        {Spec.Member.Group{x} == Spec.Member.Node{y}: Spec.Member},
        Shared.Bool.false_ne_true(h)
      )

# grp_all_has at the first name j, by whether it is k (hit)
law grp_all_has.at:
  for hit: Bool
  for r: List<&2, String>
  for k: String
  (
    {
      Strings.has(r, k) == True{}: Bool
    } -> {
      Reaches.Reach.found(
        ~Spec.Member,
        ~Member.same,
        Grp.groups(r),
        Spec.Member.Group{k}
      )
        == True{}: Bool
    }
  ) -> {
    List.any.if(u => Strings.has(r, k), hit) == True{}: Bool
  } -> {
    Bool.or(
      hit,
      Reaches.Reach.found(~Spec.Member, ~Member.same, Grp.groups(r), Spec.Member.Group{k})
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
    Strings.has(ks, k) == True{}: Bool
  } -> {
    Reaches.Reach.found(
      ~Spec.Member,
      ~Member.same,
      Grp.groups(ks),
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
  for mg: Maybe<&2, Grp>
  for gs: Tables.Table<Grp>
  for k: String
  for q: Spec.Member
  {
    Tables.Table.get(Grp, gs, k) == mg: Maybe<&2, Grp>
  } -> {
    Reaches.Reach.found(~Spec.Member, ~Member.same, Grp.members.in(mg), q) == True{}: Bool
  } -> {
    Reaches.Reach.found(
      ~Spec.Member,
      ~Member.same,
      Grp.all(gs),
      Spec.Member.Group{k}
    )
      == True{}: Bool
  }

def grp_live.at(mg, gs, k, q):
  match mg:
    case None{}:
      e => h => Empty.absurd(
        {
          Reaches.Reach.found(
            ~Spec.Member,
            ~Member.same,
            Grp.all(gs),
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
          Tables.Table.keys(Grp, gs),
          k
        )(
          Equal.trans(
            Bool,
            Strings.has(Tables.Table.keys(Grp, gs), k),
            Maybe.is_some(&2, Grp, Tables.Table.get(Grp, gs, k)),
            True{},
            Tables.Table.keys_get(Grp, gs, k),
            Equal.cong(
              Maybe<&2, Grp>,
              Bool,
              z => Maybe.is_some(&2, Grp, z),
              Tables.Table.get(Grp, gs, k),
              Some{x},
              e
            )
          )
        )

# a member with members is a group of gs
law grp_live:
  for gs: Tables.Table<Grp>
  for p: Spec.Member
  for q: Spec.Member
  {
    Reaches.Reach.found(~Spec.Member, ~Member.same, Grp.members.of(gs, p), q) == True{}: Bool
  } -> {Reaches.Reach.found(~Spec.Member, ~Member.same, Grp.all(gs), p) == True{}: Bool}

def grp_live(gs, p, q):
  match p:
    case Spec.Member.Node{n}:
      h => Empty.absurd(
        {
          Reaches.Reach.found(
            ~Spec.Member,
            ~Member.same,
            Grp.all(gs),
            Spec.Member.Node{n}
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(h)
      )
    case Spec.Member.Group{+k}:
      +gs = gs
      grp_live.at(Tables.Table.get(Grp, gs, k), gs, k, q)({==})

# a set-group that answers Set has its first member inside the group
law sg_on:
  for cycle: Bool
  for s: St
  for g: String
  for m: Spec.Member
  for ms: List<&2, Spec.Member>
  for x: Nat
  {
    Out.answer(
      SetGroup.on(cycle, s, g, m <> ms)
    )
      == Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}: Spec.Answer
  } -> {Grp.inside(Out.groups(SetGroup.on(cycle, s, g, m <> ms)), m, g) == True{}: Bool}

def sg_on(cycle, s, g, m, ms, x):
  match cycle:
    case True{}:
      ha =>
        Empty.absurd(
          {Grp.inside(Out.groups(SetGroup.on(True{}, s, g, m <> ms)), m, g) == True{}: Bool},
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
        +m = m
        +ms = ms
        %Equal.sym(
          Maybe<&2, Grp>,
          Tables.Table.get(
            Grp,
            Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}),
            g
          ),
          Some{Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}},
          Tables.Table.get_after_set(
            Grp,
            St.groups(s),
            g,
            Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}
          )
        ):
          {
            Reaches.Reach.go(
              ~Spec.Member,
              ~Tables.Table<Grp>,
              ~Member.same,
              ~Grp.members.of,
              List.length(
                &2,
                Spec.Member,
                Grp.all(
                  Tables.Table.set(
                    Grp,
                    St.groups(s),
                    g,
                    Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}
                  )
                )
              ),
              Grp.members.in(_),
              Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}),
              m
            )
              == True{}: Bool
          }
        Reaches.Reach.path_go(
          ~Spec.Member,
          ~Tables.Table<Grp>,
          ~Member.same,
          ~Grp.members.of,
          ~Grp.all,
          ~member_same_refl,
          ~member_same_sound,
          ~grp_live,
          [],
          List.length(
            &2,
            Spec.Member,
            Grp.all(
              Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)})
            )
          ),
          m <> ms,
          Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)}),
          m
        )((
            %Equal.sym(Bool, Member.same(m, m), True{}, member_same_refl(m)): {Bool.or(_, Reaches.Reach.found(~Spec.Member, ~Member.same, ms, m)) == True{}: Bool}
            {==}))({==})

# Write.at keeps the groups
def grp_kept.Write.at(
  ok: Bool,
  s: St,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  y: List<&2, U32>,
  br: Br
) -> {Out.groups(Write.at(ok, s, r, w, t, n, b, y, br)) == St.groups(s): Tables.Table<Grp>}:
  match ok:
    case False{}:
      match br:
        case Br{h, o, e, c}:
          {==}
    case True{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# Write.on keeps the groups
def grp_kept.Write.on(
  owner: Bool,
  s: St,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>,
  +br: Br
) -> {
  Out.groups(Write.on(owner, s, r, w, t, n, b, base, y, br)) == St.groups(s): Tables.Table<Grp>
}:
  match owner:
    case True{}:
      match br:
        case Br{+h, o, e, c}:
          grp_kept.Write.at(Base.is(base, h), s, r, w, t, n, b, y, Br{h, o, e, c})
    case False{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# Write.branch keeps the groups
def grp_kept.Write.branch(
  m: Maybe<&2, Br>,
  +s: St,
  r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> {Out.groups(Write.branch(m, s, r, w, t, n, b, base, y)) == St.groups(s): Tables.Table<Grp>}:
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
  +s: St,
  r: String,
  w: String,
  t: String,
  n: String,
  +b: String,
  base: Maybe<&2, String>,
  y: List<&2, U32>
) -> {Out.groups(Write.free(taken, s, r, w, t, n, b, base, y)) == St.groups(s): Tables.Table<Grp>}:
  match taken:
    case True{}:
      {==}
    case False{}:
      grp_kept.Write.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, n, b, base, y)

# Write.bytes keeps the groups
def grp_kept.Write.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  n: String,
  b: String,
  base: Maybe<&2, String>
) -> {Out.groups(Write.bytes(m, s, r, w, t, n, b, base)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      grp_kept.Write.free(Ver.taken(St.versions(s), r), s, r, w, t, n, b, base, y)

# SetBranch.on keeps the groups
def grp_kept.SetBranch.on(
  owner: Bool,
  taken: Bool,
  s: St,
  r: String,
  w: String,
  t: String,
  b: String,
  bs: Tables.Table<List<&2, U32>>,
  +br: Br
) -> {
  Out.groups(SetBranch.on(owner, taken, s, r, w, t, b, bs, br)) == St.groups(s): Tables.Table<Grp>
}:
  match owner taken:
    case _ True{}:
      {==}
    case False{} False{}:
      match br:
        case Br{h, o, e, c}:
          {==}
    case True{} False{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# SetBranch.branch keeps the groups
def grp_kept.SetBranch.branch(
  m: Maybe<&2, Br>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  b: String,
  k: String,
  bs: Tables.Table<List<&2, U32>>
) -> {Out.groups(SetBranch.branch(m, s, r, w, t, b, k, bs)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.SetBranch.on(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, b, bs, br)

# SetBranch.version keeps the groups
def grp_kept.SetBranch.version(
  m: Maybe<&2, Ver>,
  +s: St,
  r: String,
  w: String,
  t: String,
  +b: String,
  k: String
) -> {Out.groups(SetBranch.version(m, s, r, w, t, b, k)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{Ver{bs, p, a, z}}:
      grp_kept.SetBranch.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, b, k, bs)

# SetBranch.point keeps the groups
def grp_kept.SetBranch.point(
  m: Maybe<&2, String>,
  +s: St,
  r: String,
  w: String,
  t: String,
  b: String
) -> {Out.groups(SetBranch.point(m, s, r, w, t, b)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      grp_kept.SetBranch.version(Tables.Table.get(Ver, St.versions(s), k), s, r, w, t, b, k)

# CreateMark.free keeps the groups
def grp_kept.CreateMark.free(
  held: Maybe<&2, String>,
  s: St,
  b: String,
  m: String,
  x: String,
  br: Br
) -> {Out.groups(CreateMark.free(held, s, b, m, x, br)) == St.groups(s): Tables.Table<Grp>}:
  match held:
    case Some{k}:
      {==}
    case None{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# CreateMark.branch keeps the groups
def grp_kept.CreateMark.branch(
  f: Maybe<&2, Br>,
  +s: St,
  +b: String,
  +m: String,
  x: String
) -> {Out.groups(CreateMark.branch(f, s, b, m, x)) == St.groups(s): Tables.Table<Grp>}:
  match f:
    case None{}:
      {==}
    case Some{br}:
      grp_kept.CreateMark.free(MarkAt.find(St.marks(s), b, m), s, b, m, x, br)

# SetOwner.on keeps the groups
def grp_kept.SetOwner.on(
  owner: Bool,
  s: St,
  b: String,
  g: String,
  br: Br
) -> {Out.groups(SetOwner.on(owner, s, b, g, br)) == St.groups(s): Tables.Table<Grp>}:
  match owner:
    case False{}:
      {==}
    case True{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# SetOwner.branch keeps the groups
def grp_kept.SetOwner.branch(
  f: Maybe<&2, Br>,
  +s: St,
  b: String,
  g: String
) -> {Out.groups(SetOwner.branch(f, s, b, g)) == St.groups(s): Tables.Table<Grp>}:
  match f:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.SetOwner.on(Owner.of(s, br), s, b, g, br)

# Merge.result keeps the groups
def grp_kept.Merge.result(
  cs: List<&2, String>,
  s: St,
  r: String,
  w: String,
  t: String,
  f: String,
  b: String,
  bs: Tables.Table<List<&2, U32>>,
  br: Br
) -> {Out.groups(Merge.result(cs, s, r, w, t, f, b, bs, br)) == St.groups(s): Tables.Table<Grp>}:
  match cs:
    case Nil{}:
      match br:
        case Br{h, o, e, c}:
          {==}
    case Con{k, more}:
      match br:
        case Br{h, o, e, c}:
          {==}

# Merge.three keeps the groups
def grp_kept.Merge.three(
  s: St,
  r: String,
  w: String,
  t: String,
  f: String,
  +hb: Tables.Table<List<&2, U32>>,
  +fb: Tables.Table<List<&2, U32>>,
  +bb: Tables.Table<List<&2, U32>>,
  b: String,
  br: Br
) -> {Out.groups(Merge.three(s, r, w, t, f, hb, fb, bb, b, br)) == St.groups(s): Tables.Table<Grp>}:
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
  +s: St,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: Br
) -> {Out.groups(Merge.inside(held, s, r, w, t, f, b, br)) == St.groups(s): Tables.Table<Grp>}:
  match held:
    case True{}:
      match br:
        case Br{h, o, e, c}:
          {==}
    case False{}:
      match br:
        case Br{+h, o, e, c}:
          hh = History.of(St.versions(s), h)
          grp_kept.Merge.three(
            s,
            r,
            w,
            t,
            f,
            Vers.blobs(St.versions(s), h),
            Vers.blobs(St.versions(s), f),
            Merge.base(s, Vers.first_in(History.of(St.versions(s), f), Vers.ids(hh))),
            b,
            Br{h, o, e, c}
          )

# Merge.owner keeps the groups
def grp_kept.Merge.owner(
  owner: Bool,
  taken: Bool,
  +s: St,
  r: String,
  w: String,
  t: String,
  +f: String,
  b: String,
  +br: Br
) -> {
  Out.groups(Merge.owner(owner, taken, s, r, w, t, f, b, br)) == St.groups(s): Tables.Table<Grp>
}:
  match owner taken:
    case False{} _:
      {==}
    case True{} True{}:
      {==}
    case True{} False{}:
      match br:
        case Br{+h, o, e, c}:
          grp_kept.Merge.inside(
            Strings.has(Vers.ids(History.of(St.versions(s), h)), f),
            s,
            r,
            w,
            t,
            f,
            b,
            Br{h, o, e, c}
          )

# Merge.branch keeps the groups
def grp_kept.Merge.branch(
  m: Maybe<&2, Br>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  f: String,
  b: String
) -> {Out.groups(Merge.branch(m, s, r, w, t, f, b)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{+br}:
      grp_kept.Merge.owner(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, f, b, br)

# Merge.point keeps the groups
def grp_kept.Merge.point(
  m: Maybe<&2, String>,
  +s: St,
  r: String,
  w: String,
  t: String,
  +b: String
) -> {Out.groups(Merge.point(m, s, r, w, t, b)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{f}:
      grp_kept.Merge.branch(Tables.Table.get(Br, St.branches(s), b), s, r, w, t, f, b)

# Resolve.done keeps the groups
def grp_kept.Resolve.done(
  left: List<&2, String>,
  taken: Bool,
  s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  y: List<&2, U32>,
  cl: Clash,
  br: Br
) -> {
  Out.groups(
    Resolve.done(left, taken, s, r, w, t, k, n, y, cl, br)
  )
    == St.groups(s): Tables.Table<Grp>
}:
  match left:
    case Nil{}:
      match taken:
        case True{}:
          {==}
        case False{}:
          match cl br:
            case Clash{b, h, f, bs, l} Br{h2, o, e, c}:
              {==}
    case Con{x, more}:
      match cl:
        case Clash{b, h, f, bs, l}:
          {==}

# Resolve.bytes keeps the groups
def grp_kept.Resolve.bytes(
  m: Maybe<&2, List<&2, U32>>,
  +s: St,
  +r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  +cl: Clash,
  br: Br
) -> {Out.groups(Resolve.bytes(m, s, r, w, t, k, n, cl, br)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{y}:
      match cl:
        case Clash{b, h, f, bs, +l}:
          grp_kept.Resolve.done(
            Shared.List.remove(~String, ~String.eq, l, n),
            Ver.taken(St.versions(s), r),
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
  +s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content,
  cl: Clash,
  br: Br
) -> {
  Out.groups(Resolve.fresh(ok, s, r, w, t, k, n, x, cl, br)) == St.groups(s): Tables.Table<Grp>
}:
  match ok:
    case False{}:
      match br:
        case Br{h, o, e, c}:
          {==}
    case True{}:
      grp_kept.Resolve.bytes(Content.bytes(s, n, x), s, r, w, t, k, n, cl, br)

# Resolve.branch keeps the groups
def grp_kept.Resolve.branch(
  m: Maybe<&2, Br>,
  s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> {Out.groups(Resolve.branch(m, s, r, w, t, k, n, x, cl)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{Br{+h, o, e, c}}:
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
            Br{h, o, e, c}
          )

# Resolve.named keeps the groups
def grp_kept.Resolve.named(
  has: Bool,
  +s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  n: String,
  x: Spec.Content,
  +cl: Clash
) -> {Out.groups(Resolve.named(has, s, r, w, t, k, n, x, cl)) == St.groups(s): Tables.Table<Grp>}:
  match has:
    case False{}:
      {==}
    case True{}:
      match cl:
        case Clash{+b, h, f, bs, l}:
          grp_kept.Resolve.branch(
            Tables.Table.get(Br, St.branches(s), b),
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
  s: St,
  r: String,
  w: String,
  t: String,
  k: String,
  +n: String,
  x: Spec.Content
) -> {Out.groups(Resolve.clash(m, s, r, w, t, k, n, x)) == St.groups(s): Tables.Table<Grp>}:
  match m:
    case None{}:
      {==}
    case Some{Clash{b, h, f, bs, +l}}:
      grp_kept.Resolve.named(Strings.has(l, n), s, r, w, t, k, n, x, Clash{b, h, f, bs, l})

# no member of gs is inside itself
def Grp.Acyclic(gs: Tables.Table<Grp>) -> Type:
  @y: Spec.Member -> {
    Reaches.Reach.in(
      ~Spec.Member,
      ~Tables.Table<Grp>,
      ~Member.same,
      ~Grp.members.of,
      ~Grp.all,
      gs,
      y,
      y
    )
      == False{}: Bool
  }

# setting a group elsewhere leaves a member's members
law grp_agree:
  for gs: Tables.Table<Grp>
  for c: Spec.Member
  for x: Grp
  for p: Spec.Member
  {
    Member.same(p, c) == False{}: Bool
  } -> {Grp.members.of(Grp.put(gs, c, x), p) == Grp.members.of(gs, p): List<&2, Spec.Member>}

def grp_agree(gs, c, x, p):
  match c p:
    case Spec.Member.Node{n} q:
      h => {==}
    case Spec.Member.Group{k} Spec.Member.Node{n}:
      h => {==}
    case Spec.Member.Group{+k} Spec.Member.Group{+j}:
      +h =>
        +gs = gs
        +x = x
        %Equal.sym(
          Maybe<&2, Grp>,
          Tables.Table.get(Grp, Tables.Table.set(Grp, gs, k, x), j),
          Bools.Bool.when(
            Maybe<&2, Grp>,
            String.eq(k, j),
            u => Some{x},
            u => Tables.Table.get(Grp, gs, j)
          ),
          Tables.Table.get_set(Grp, gs, k, x, j)
        ):
          {Grp.members.in(_) == Grp.members.in(Tables.Table.get(Grp, gs, j)): List<&2, Spec.Member>}
        %Equal.sym(Bool, String.eq(k, j), False{}, Strings.String.eq_flip(j, k)(h)):
          {
            Grp.members.in(
              Bools.Bool.when(Maybe<&2, Grp>, _, u => Some{x}, u => Tables.Table.get(Grp, gs, j))
            )
              == Grp.members.in(Tables.Table.get(Grp, gs, j)): List<&2, Spec.Member>
          }
        {==}

# acyc_all for one member y
law acyc_all.at:
  for gs: Tables.Table<Grp>
  for y: Spec.Member
  (
    @h: String -> {Grp.inside(gs, Spec.Member.Group{h}, h) == False{}: Bool}
  ) -> {
    Reaches.Reach.in(
      ~Spec.Member,
      ~Tables.Table<Grp>,
      ~Member.same,
      ~Grp.members.of,
      ~Grp.all,
      gs,
      y,
      y
    )
      == False{}: Bool
  }

def acyc_all.at(gs, y):
  match y:
    case Spec.Member.Node{n}:
      a =>
        +gs = gs
        Reaches.Reach.go_nil(
          ~Spec.Member,
          ~Tables.Table<Grp>,
          ~Member.same,
          ~Grp.members.of,
          ~Grp.all,
          ~member_same_refl,
          ~member_same_sound,
          ~grp_live,
          List.length(&2, Spec.Member, Grp.all(gs)),
          gs,
          Spec.Member.Node{n}
        )
    case Spec.Member.Group{h}:
      a => a(h)

# no group of gs inside itself: then no member is
law acyc_all:
  for gs: Tables.Table<Grp>
  (@h: String -> {Grp.inside(gs, Spec.Member.Group{h}, h) == False{}: Bool}) -> Grp.Acyclic(gs)

def acyc_all(gs):
  a => y => acyc_all.at(gs, y)(a)

# setting the group g to ms, when that closes no cycle, keeps gs acyclic
law set_acyclic:
  for gs: Tables.Table<Grp>
  for g: String
  for ms: List<&2, Spec.Member>
  for e: Nat
  Grp.Acyclic(
    gs
  ) -> {
    Cycle.has(gs, g, ms) == False{}: Bool
  } -> Grp.Acyclic(Tables.Table.set(Grp, gs, g, Grp{ms, e}))

def set_acyclic(gs, g, ms, e):
  a => +hc =>
    +gs = gs
    +g = g
    +ms = ms
    +e = e
    y => Reaches.Reach.put_acyclic(
      ~Spec.Member,
      ~Tables.Table<Grp>,
      ~Member.same,
      ~Grp.members.of,
      ~Grp.all,
      ~member_same_refl,
      ~member_same_sound,
      ~grp_live,
      ~Grp,
      ~Grp.put,
      ~grp_agree,
      gs,
      Spec.Member.Group{g},
      Grp{ms, e},
      y
    )(a)((
        %Equal.sym(Maybe<&2, Grp>, Tables.Table.get(Grp, Tables.Table.set(Grp, gs, g, Grp{ms, e}), g), Some{Grp{ms, e}}, Tables.Table.get_after_set(Grp, gs, g, Grp{ms, e})):
          {Reaches.Reach.closes(~Spec.Member, ~Tables.Table<Grp>, ~Member.same, ~Grp.members.of, ~Grp.all, gs, Spec.Member.Group{g}, Grp.members.in(_)) == False{}: Bool}
        hc))

# a sync's put of a group keeps the groups acyclic
law grp_put:
  for c: Bool
  for g: String
  for ms: List<&2, Spec.Member>
  for e: Nat
  for gs: Tables.Table<Grp>
  for ns: List<&2, Logged>
  {
    Cycle.has(gs, g, ms) == c: Bool
  } -> Grp.Acyclic(gs) -> Grp.Acyclic(Kept.groups(Sync.group.put(c, g, Grp{ms, e}, Kept{gs, ns})))

def grp_put(c, g, ms, e, gs, ns):
  match c:
    case True{}:
      hc => a => a
    case False{}:
      hc => a => set_acyclic(gs, g, ms, e)(a)(hc)

law grp_later:
  for lt: Bool
  for g: String
  for x: Grp
  for k: Kept
  Grp.Acyclic(Kept.groups(k)) -> Grp.Acyclic(Kept.groups(Sync.group.later(lt, g, x, k)))

def grp_later(lt, g, x, k):
  match lt x k:
    case False{} y z:
      a => a
    case True{} Grp{+ms, e} Kept{+gs, ns}:
      +g = g
      grp_put(Cycle.has(gs, g, ms), g, ms, e, gs, ns)({==})

law grp_at:
  for m: Maybe<&2, Grp>
  for g: String
  for x: Grp
  for k: Kept
  Grp.Acyclic(Kept.groups(k)) -> Grp.Acyclic(Kept.groups(Sync.group.at(m, g, x, k)))

def grp_at(m, g, x, k):
  match m x k:
    case None{} Grp{+ms, e} Kept{+gs, ns}:
      +g = g
      grp_put(Cycle.has(gs, g, ms), g, ms, e, gs, ns)({==})
    case Some{Grp{ns, f}} Grp{ms, +e} z:
      grp_later(Nat.is_lt(f, e), g, Grp{ms, e}, z)

law grp_seen:
  for g: String
  for vis: Maybe<&2, Grp>
  for k: Kept
  Grp.Acyclic(Kept.groups(k)) -> Grp.Acyclic(Kept.groups(Sync.group.seen(g, vis, k)))

def grp_seen(g, vis, k):
  match vis k:
    case None{} z:
      a => a
    case Some{x} Kept{+gs, ns}:
      +g = g
      grp_at(Tables.Table.get(Grp, gs, g), g, x, Kept{gs, ns})

# a sync's group pass keeps the groups acyclic
law grp_fold:
  for ks: List<&2, String>
  for full: Tables.Table<Grp>
  for k: Kept
  Grp.Acyclic(Kept.groups(k)) -> Grp.Acyclic(Kept.groups(Sync.groups(ks, full, k)))

def grp_fold(ks, full, k):
  match ks:
    case Nil{}:
      a => a
    case Con{+g, r}:
      a =>
        +full = full
        +k = k
        grp_fold(
          r,
          full,
          Sync.group.seen(g, Tables.Table.get(Grp, full, g), k)
        )(grp_seen(g, Tables.Table.get(Grp, full, g), k)(a))

# a set-group keeps the groups acyclic, by whether it closes a cycle
law sg_acyclic:
  for cycle: Bool
  for s: St
  for g: String
  for ms: List<&2, Spec.Member>
  {
    Cycle.has(St.groups(s), g, ms) == cycle: Bool
  } -> Grp.Acyclic(St.groups(s)) -> Grp.Acyclic(Out.groups(SetGroup.on(cycle, s, g, ms)))

def sg_acyclic(cycle, s, g, ms):
  match cycle:
    case True{}:
      hc => a => a
    case False{}:
      hc => a =>
        +s = s
        +g = g
        set_acyclic(St.groups(s), g, ms, Grp.epoch.next(St.groups(s), g))(a)(hc)

# a sync keeps the groups acyclic, by whether its versions collide
law sync_acyclic:
  for c: Bool
  for s: St
  for o: St
  Grp.Acyclic(St.groups(s)) -> Grp.Acyclic(Out.groups(Sync.go(c, s, o)))

def sync_acyclic(c, s, o):
  match c:
    case True{}:
      a => a
    case False{}:
      a =>
        +s = s
        +o = o
        grp_fold(Tables.Table.keys(Grp, St.groups(o)), St.groups(o), Kept{St.groups(s), []})(a)

# every change keeps the groups acyclic
law step_acyclic:
  for s: St
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  Grp.Acyclic(St.groups(s)) -> Grp.Acyclic(Out.groups(Step.of(s, r, w, z, q)))

def step_acyclic(s, r, w, z, q):
  match q:
    case Spec.Ask.Write{+n, b, base, x}:
      a =>
        +s = s
        +r = r
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(Write.bytes(Content.bytes(s, n, x), s, r, w, z, n, b, base)),
          St.groups(s),
          grp_kept.Write.bytes(Content.bytes(s, n, x), s, r, w, z, n, b, base)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.SetBranch{b, p}:
      a =>
        +s = s
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(SetBranch.point(Point.version(s, p), s, r, w, z, b)),
          St.groups(s),
          grp_kept.SetBranch.point(Point.version(s, p), s, r, w, z, b)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.CreateMark{+b, m, x}:
      a =>
        +s = s
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(CreateMark.branch(Tables.Table.get(Br, St.branches(s), b), s, b, m, x)),
          St.groups(s),
          grp_kept.CreateMark.branch(Tables.Table.get(Br, St.branches(s), b), s, b, m, x)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.Merge{p, b}:
      a =>
        +s = s
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(Merge.point(Point.version(s, p), s, r, w, z, b)),
          St.groups(s),
          grp_kept.Merge.point(Point.version(s, p), s, r, w, z, b)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.Resolve{+k, n, x}:
      a =>
        +s = s
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(Resolve.clash(Tables.Table.get(Clash, St.clashes(s), k), s, r, w, z, k, n, x)),
          St.groups(s),
          grp_kept.Resolve.clash(Tables.Table.get(Clash, St.clashes(s), k), s, r, w, z, k, n, x)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.SetOwner{+b, g}:
      a =>
        +s = s
        %Equal.sym(
          Tables.Table<Grp>,
          Out.groups(SetOwner.branch(Tables.Table.get(Br, St.branches(s), b), s, b, g)),
          St.groups(s),
          grp_kept.SetOwner.branch(Tables.Table.get(Br, St.branches(s), b), s, b, g)
        ): Grp.Acyclic(_)
        a
    case Spec.Ask.SetGroup{+g, +ms}:
      a =>
        +s = s
        sg_acyclic(Cycle.has(St.groups(s), g, ms), s, g, ms)({==})(a)
    case Spec.Ask.Sync{+o, p}:
      a =>
        +s = s
        sync_acyclic(
          Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
          s,
          o
        )(a)

# a change keeps every group outside itself, by whether its request was seen
law nia_asked:
  for found: Maybe<&2, Seen>
  for s: St
  for r: String
  for w: String
  for z: String
  for q: Spec.Ask
  for t: St
  for a: Spec.Answer
  for g: String
  {
    Node.asked(found, s, r, w, z, q) == (t, a): St & Spec.Answer
  } -> Grp.Acyclic(
    St.groups(s)
  ) -> {Grp.inside(St.groups(t), Spec.Member.Group{g}, g) == False{}: Bool}

def nia_asked(found, s, r, w, z, q, t, a, g):
  match found:
    case Some{Seen{b, p}}:
      h => ac =>
        +s = s
        %Equal.cong(
          St & Spec.Answer,
          St,
          x => Pair.fst(St, Spec.Answer, x),
          (s, b),
          (t, a),
          h
        ): {Grp.inside(St.groups(_), Spec.Member.Group{g}, g) == False{}: Bool}
        ac(Spec.Member.Group{g})
    case None{}:
      h => ac =>
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
        )(h): {Grp.inside(St.groups(_), Spec.Member.Group{g}, g) == False{}: Bool}
        %Equal.sym(
          Tables.Table<Grp>,
          St.groups(Pair.fst(St, Spec.Answer, Node.applied(s, r, Step.of(s, r, w, z, q)))),
          Out.groups(Step.of(s, r, w, z, q)),
          groups_after_applied(s, r, Step.of(s, r, w, z, q))
        ):
          {Grp.inside(_, Spec.Member.Group{g}, g) == False{}: Bool}
        step_acyclic(s, r, w, z, q)(ac)(Spec.Member.Group{g})

# the node of a state stays across a change
law self_after_applied:
  for s: St
  for r: String
  for out: Out
  {St.self(Pair.fst(St, Spec.Answer, Node.applied(s, r, out))) == St.self(s): String}

def self_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# a change whose result is (t, a), and whose Out is o: the versions of t
law view_v:
  for s: St
  for r: String
  for x: Out
  for t: St
  for a: Spec.Answer
  for o: Out
  {
    Node.applied(s, r, x) == (t, a): St & Spec.Answer
  } -> {
    x == o: Out
  } -> {St.versions(t) == Ver.add(Out.versions(o), St.versions(s)): Tables.Table<Ver>}

def view_v(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<Ver>,
      St.versions(t),
      Ver.add(Out.versions(x), St.versions(s)),
      Ver.add(Out.versions(o), St.versions(s)),
      Equal.trans(
        Tables.Table<Ver>,
        St.versions(t),
        St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r, x))),
        Ver.add(Out.versions(x), St.versions(s)),
        Equal.cong(
          St,
          Tables.Table<Ver>,
          z => St.versions(z),
          t,
          Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
          Equal.sym(
            St,
            Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        versions_after_applied(s, r, x)
      ),
      Equal.cong(Out, Tables.Table<Ver>, z => Ver.add(Out.versions(z), St.versions(s)), x, o, hout)
    )

# ... the branches of t
law view_b:
  for s: St
  for r: String
  for x: Out
  for t: St
  for a: Spec.Answer
  for o: Out
  {
    Node.applied(s, r, x) == (t, a): St & Spec.Answer
  } -> {x == o: Out} -> {St.branches(t) == Out.branches(o): Tables.Table<Br>}

def view_b(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<Br>,
      St.branches(t),
      Out.branches(x),
      Out.branches(o),
      Equal.trans(
        Tables.Table<Br>,
        St.branches(t),
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r, x))),
        Out.branches(x),
        Equal.cong(
          St,
          Tables.Table<Br>,
          z => St.branches(z),
          t,
          Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
          Equal.sym(
            St,
            Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        branches_after_applied(s, r, x)
      ),
      Equal.cong(Out, Tables.Table<Br>, z => Out.branches(z), x, o, hout)
    )

# ... the groups of t
law view_g:
  for s: St
  for r: String
  for x: Out
  for t: St
  for a: Spec.Answer
  for o: Out
  {
    Node.applied(s, r, x) == (t, a): St & Spec.Answer
  } -> {x == o: Out} -> {St.groups(t) == Out.groups(o): Tables.Table<Grp>}

def view_g(s, r, x, t, a, o):
  hask => hout =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      Tables.Table<Grp>,
      St.groups(t),
      Out.groups(x),
      Out.groups(o),
      Equal.trans(
        Tables.Table<Grp>,
        St.groups(t),
        St.groups(Pair.fst(St, Spec.Answer, Node.applied(s, r, x))),
        Out.groups(x),
        Equal.cong(
          St,
          Tables.Table<Grp>,
          z => St.groups(z),
          t,
          Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
          Equal.sym(
            St,
            Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
            t,
            applied_state(s, r, x, t, a)(hask)
          )
        ),
        groups_after_applied(s, r, x)
      ),
      Equal.cong(Out, Tables.Table<Grp>, z => Out.groups(z), x, o, hout)
    )

# ... the node of t
law view_self:
  for s: St
  for r: String
  for x: Out
  for t: St
  for a: Spec.Answer
  {Node.applied(s, r, x) == (t, a): St & Spec.Answer} -> {St.self(t) == St.self(s): String}

def view_self(s, r, x, t, a):
  hask =>
    +s = s
    +r = r
    +x = x
    +t = t
    Equal.trans(
      String,
      St.self(t),
      St.self(Pair.fst(St, Spec.Answer, Node.applied(s, r, x))),
      St.self(s),
      Equal.cong(
        St,
        String,
        z => St.self(z),
        t,
        Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
        Equal.sym(
          St,
          Pair.fst(St, Spec.Answer, Node.applied(s, r, x)),
          t,
          applied_state(s, r, x, t, a)(hask)
        )
      ),
      self_after_applied(s, r, x)
    )

# a change answers what its Out answers, so the version it names
law view_ver:
  for s: St
  for r: String
  for x: Out
  for t: St
  for a: Spec.Answer
  {
    Node.applied(s, r, x) == (t, a): St & Spec.Answer
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
  for s: St
  for r: String
  for w: String
  for t: String
  for b: String
  for bs: Tables.Table<List<&2, U32>>
  for br: Br
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
        case Br{h, o, e, c}:
          {==}
    case True{} False{}:
      match br:
        case Br{h, o, e, c}:
          {==}

# a set-branch that creates c at k
law sb_branch:
  for mb: Maybe<&2, Br>
  for s: St
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for bs: Tables.Table<List<&2, U32>>
  for v: String
  {
    Tables.Table.get(Br, St.branches(s), c) == mb: Maybe<&2, Br>
  } -> {
    Answer.version(
      Out.answer(SetBranch.branch(mb, s, r, w, t, c, k, bs))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
              Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
              St.marks(s),
              St.groups(s),
              St.clashes(s),
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
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
                      Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
                      St.marks(s),
                      St.groups(s),
                      St.clashes(s),
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
                  SetBranch.on(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, c, bs, br)
                )
              ),
              Some{v},
              Equal.sym(
                Maybe<&2, String>,
                Answer.version(
                  Out.answer(
                    SetBranch.on(
                      Owner.of(s, br),
                      Ver.taken(St.versions(s), r),
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
                sb_on_none(Owner.of(s, br), Ver.taken(St.versions(s), r), s, r, w, t, c, bs, br)
              ),
              h
            )
          )
        )

# a set-branch to the version k, which mv holds
law sb_version:
  for mv: Maybe<&2, Ver>
  for s: St
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    Tables.Table.get(Ver, St.versions(s), k) == mv: Maybe<&2, Ver>
  } -> {
    Answer.version(
      Out.answer(SetBranch.version(mv, s, r, w, t, c, k))
    )
      == Some{v}: Maybe<&2, String>
  } -> {
    Ver.has(St.versions(s), k) == True{}: Bool
  }
    & (
      {
        Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
                  Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
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
          Ver.has(St.versions(s), k) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
                        Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
                        St.marks(s),
                        St.groups(s),
                        St.clashes(s),
                        [Logged.head(c, k)],
                        SetBranch.answer(Spec.SetBranch.Created{k})
                      }: Out
                  }
              )
          ),
        Maybes.Maybe.none_ne_some(String, v, h)
      )
    case Some{Ver{bs, ps, a, z}}:
      +e => h =>
        +s = s
        +c = c
        +k = k
        (
          Equal.cong(
            Maybe<&2, Ver>,
            Bool,
            y => Maybe.is_some(&2, Ver, y),
            Tables.Table.get(Ver, St.versions(s), k),
            Some{Ver{bs, ps, a, z}},
            e
          ),
          sb_branch(Tables.Table.get(Br, St.branches(s), c), s, r, w, t, c, k, bs, v)({==})(h)
        )

law sb_point.fin.of:
  for s: St
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    Ver.has(St.versions(s), k) == True{}: Bool
  } -> {
    Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
  } -> {
    k == v: String
  } -> {
    SetBranch.version(
      Tables.Table.get(Ver, St.versions(s), k),
      s,
      r,
      w,
      t,
      c,
      k
    )
      == Out{
        [],
        Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(c, k)],
        SetBranch.answer(Spec.SetBranch.Created{k})
      }: Out
  } -> {
    Some{k} == Some{v}: Maybe<&2, String>
  }
    & (
      {
        Ver.has(St.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
          }
            & {
              SetBranch.version(
                Tables.Table.get(Ver, St.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
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
          Ver.has(St.versions(s), _) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
            }
              & {
                SetBranch.version(
                  Tables.Table.get(Ver, St.versions(s), k),
                  s,
                  r,
                  w,
                  t,
                  c,
                  k
                )
                  == Out{
                    [],
                    Tables.Table.set(Br, St.branches(s), c, Br{_, St.self(s), 0n, 0n}),
                    St.marks(s),
                    St.groups(s),
                    St.clashes(s),
                    [Logged.head(c, _)],
                    SetBranch.answer(Spec.SetBranch.Created{_})
                  }: Out
              }
          )
      )
    ({==}, (hk, (hc, ho)))

# sb_point, once the version k is found to be v
law sb_point.fin:
  for s: St
  for r: String
  for w: String
  for t: String
  for c: String
  for k: String
  for v: String
  {
    Ver.has(St.versions(s), k) == True{}: Bool
  }
    & (
      {
        Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
      }
        & (
          {
            k == v: String
          }
            & {
              SetBranch.version(
                Tables.Table.get(Ver, St.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
                  [Logged.head(c, k)],
                  SetBranch.answer(Spec.SetBranch.Created{k})
                }: Out
            }
        )
    ) -> {Some{k} == Some{v}: Maybe<&2, String>}
    & (
      {
        Ver.has(St.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
          }
            & {
              SetBranch.version(
                Tables.Table.get(Ver, St.versions(s), k),
                s,
                r,
                w,
                t,
                c,
                k
              )
                == Out{
                  [],
                  Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_point.fin.g1(
  s: St,
  r: String,
  w: String,
  t: String,
  c: String,
  k: String,
  v: String,
  x: Pair(
    {Ver.has(St.versions(s), k) == True{}: Bool},
    Pair(
      {Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>},
      Pair(
        {k == v: String},
        {
          SetBranch.version(
            Tables.Table.get(Ver, St.versions(s), k),
            s,
            r,
            w,
            t,
            c,
            k
          )
            == Out{
              [],
              Tables.Table.set(Br, St.branches(s), c, Br{k, St.self(s), 0n, 0n}),
              St.marks(s),
              St.groups(s),
              St.clashes(s),
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
    {Ver.has(St.versions(s), v) == True{}: Bool},
    Pair(
      {Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>},
      {
        SetBranch.version(
          Tables.Table.get(Ver, St.versions(s), k),
          s,
          r,
          w,
          t,
          c,
          k
        )
          == Out{
            [],
            Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
            St.marks(s),
            St.groups(s),
            St.clashes(s),
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
  for s: St
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
        Ver.has(St.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
                  Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
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
              Ver.has(St.versions(s), v) == True{}: Bool
            }
              & (
                {
                  Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
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
                        Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                        St.marks(s),
                        St.groups(s),
                        St.clashes(s),
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
          sb_version(Tables.Table.get(Ver, St.versions(s), k), s, r, w, t, c, k, v)({==})(h)
        )

# a write as the owner that answers Written: its Out
law wr_at:
  for ok: Bool
  for s: St
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
      Out.answer(Write.at(ok, s, r, w, t, n, b, x, Br{h, o, e, c}))
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
      Br{h, o, e, c}
    )
      == Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, t}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
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
            Br{h, o, e, c}
          )
            == Out{
              [
                Tables.Row{
                  r,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
                    [h],
                    w,
                    t
                  }
                }
              ],
              Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
              St.marks(s),
              St.groups(s),
              St.clashes(s),
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
  for s: St
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
      Out.answer(Write.on(owner, s, r, w, t, n, b, base, x, Br{h, o, e, c}))
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
        Br{h, o, e, c}
      )
        == Out{
          [
            Tables.Row{
              r,
              Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, t}
            }
          ],
          Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
          St.marks(s),
          St.groups(s),
          St.clashes(s),
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
              Br{h, o, e, c}
            )
              == Out{
                [
                  Tables.Row{
                    r,
                    Ver{
                      Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
                      [h],
                      w,
                      t
                    }
                  }
                ],
                Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, c}, r)),
                St.marks(s),
                St.groups(s),
                St.clashes(s),
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
  for s: St
  for r: String
  for w: String
  for t: String
  for n: String
  for b: String
  for base: Maybe<&2, String>
  for x: List<&2, U32>
  for br: Br
  {
    Ver.taken(St.versions(s), r) == False{}: Bool
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{br}: Maybe<&2, Br>
  } -> {
    Write.free(
      Ver.taken(St.versions(s), r),
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
      Ver.taken(St.versions(s), r),
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
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s), b),
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
  for a: St
  for o: St
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

# m, else nothing, is m
law or_none:
  for m: Maybe<&2, Ver>
  {Maybe.or(&2, Ver, m, None{}) == m: Maybe<&2, Ver>}

def or_none(m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# a version that a list does not hold is not found in it: by the lookup m
law has_false_find.of:
  for m: Maybe<&2, Ver>
  for vs: Tables.Table<Ver>
  for k: String
  {
    Tables.Table.get(Ver, vs, k) == m: Maybe<&2, Ver>
  } -> {Ver.has(vs, k) == False{}: Bool} -> {Tables.Table.get(Ver, vs, k) == None{}: Maybe<&2, Ver>}

def has_false_find.of(m, vs, k):
  match m:
    case None{}:
      hm => hh => hm
    case Some{u}:
      +hm => hh =>
        +vs = vs
        +k = k
        Empty.absurd(
          {Tables.Table.get(Ver, vs, k) == None{}: Maybe<&2, Ver>},
          Shared.Bool.false_ne_true(
            Equal.sym(
              Bool,
              True{},
              False{},
              Equal.trans(
                Bool,
                True{},
                Ver.has(vs, k),
                False{},
                Equal.sym(
                  Bool,
                  Ver.has(vs, k),
                  True{},
                  Equal.cong(
                    Maybe<&2, Ver>,
                    Bool,
                    x => Maybe.is_some(&2, Ver, x),
                    Tables.Table.get(Ver, vs, k),
                    Some{u},
                    hm
                  )
                ),
                hh
              )
            )
          )
        )

# a version that a list does not hold is not found in it
law has_false_find:
  for vs: Tables.Table<Ver>
  for k: String
  {Ver.has(vs, k) == False{}: Bool} -> {Tables.Table.get(Ver, vs, k) == None{}: Maybe<&2, Ver>}

def has_false_find(vs, k):
  +vs = vs
  +k = k
  has_false_find.of(Tables.Table.get(Ver, vs, k), vs, k)({==})

# add_find when the first new version, under i, is already held: by the lookup
# m of k, when i is k
law add_find.held.of:
  for m: Maybe<&2, Ver>
  for i: String
  for x: Ver
  for r: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Tables.Table.get(Ver, ys, k) == m: Maybe<&2, Ver>
  } -> {
    Ver.has(ys, i) == True{}: Bool
  } -> {
    String.eq(i, k) == True{}: Bool
  } -> {
    Maybe.or(
      &2,
      Ver,
      Tables.Table.get(Ver, ys, k),
      Tables.Table.find_row(Ver, r, k)
    )
      == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Some{x}): Maybe<&2, Ver>
  }

def add_find.held.of(m, i, x, r, ys, k):
  match m:
    case Some{u}:
      hm => hh => he =>
        %Equal.sym(
          Maybe<&2, Ver>,
          Tables.Table.get(Ver, ys, k),
          Some{u},
          hm
        ): {
          Maybe.or(
            &2,
            Ver,
            _,
            Tables.Table.find_row(Ver, r, k)
          )
            == Maybe.or(&2, Ver, _, Some{x}): Maybe<&2, Ver>
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
              Ver,
              Tables.Table.get(Ver, ys, k),
              Tables.Table.find_row(Ver, r, k)
            )
              == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Some{x}): Maybe<&2, Ver>
          },
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Ver.has(ys, i),
              True{},
              Equal.trans(
                Bool,
                False{},
                Ver.has(ys, k),
                Ver.has(ys, i),
                Equal.sym(
                  Bool,
                  Ver.has(ys, k),
                  False{},
                  Equal.cong(
                    Maybe<&2, Ver>,
                    Bool,
                    z => Maybe.is_some(&2, Ver, z),
                    Tables.Table.get(Ver, ys, k),
                    None{},
                    hm
                  )
                ),
                Equal.cong(
                  String,
                  Bool,
                  z => Ver.has(ys, z),
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
  for x: Ver
  for r: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Ver.has(ys, i) == True{}: Bool
  } -> {
    String.eq(i, k) == hit: Bool
  } -> {
    Maybe.or(
      &2,
      Ver,
      Tables.Table.get(Ver, ys, k),
      Tables.Table.find_row(Ver, r, k)
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, ys, k),
        Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.find_row(Ver, r, k))
      ): Maybe<&2, Ver>
  }

def add_find.held(hit, i, x, r, ys, k):
  match hit:
    case False{}:
      hh => he => {==}
    case True{}:
      hh => he =>
        +ys = ys
        +k = k
        add_find.held.of(Tables.Table.get(Ver, ys, k), i, x, r, ys, k)({==})(hh)(he)

# add_find when the first new version, under i, is not held
law add_find.fresh:
  for hit: Bool
  for i: String
  for x: Ver
  for r: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Ver.has(ys, i) == False{}: Bool
  } -> {
    String.eq(i, k) == hit: Bool
  } -> {
    Maybe.or(
      &2,
      Ver,
      Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.get(Ver, ys, k)),
      Tables.Table.find_row(Ver, r, k)
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, ys, k),
        Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.find_row(Ver, r, k))
      ): Maybe<&2, Ver>
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
          Maybe<&2, Ver>,
          Tables.Table.get(Ver, ys, k),
          None{},
          has_false_find(
            ys,
            k
          )(
            Equal.trans(
              Bool,
              Ver.has(ys, k),
              Ver.has(ys, i),
              False{},
              Equal.cong(
                String,
                Bool,
                z => Ver.has(ys, z),
                k,
                i,
                Equal.sym(String, i, k, Strings.String.eq_sound(i, k)(he))
              ),
              hh
            )
          )
        ):
          {Some{x} == Maybe.or(&2, Ver, _, Some{x}): Maybe<&2, Ver>}
        {==}

# add_find, for the first new version, under i
law add_find.one:
  for held: Bool
  for i: String
  for x: Ver
  for r: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Ver.has(ys, i) == held: Bool
  } -> {
    Maybe.or(
      &2,
      Ver,
      Tables.Table.get(Ver, Ver.add.put(i, x, ys, held), k),
      Tables.Table.find_row(Ver, r, k)
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, ys, k),
        Tables.Table.find_row(Ver, Tables.Row{i, x} <> r, k)
      ): Maybe<&2, Ver>
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
          Maybe<&2, Ver>,
          Tables.Table.get(Ver, Tables.Table.set(Ver, ys, i, x), k),
          Bools.Bool.when(
            Maybe<&2, Ver>,
            String.eq(i, k),
            u => Some{x},
            u => Tables.Table.get(Ver, ys, k)
          ),
          Tables.Table.get_set(Ver, ys, i, x, k)
        ):
          {
            Maybe.or(
              &2,
              Ver,
              _,
              Tables.Table.find_row(Ver, r, k)
            )
              == Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, ys, k),
                Bools.Bool.when(
                  Maybe<&2, Ver>,
                  String.eq(i, k),
                  u => Some{x},
                  u => Tables.Table.find_row(Ver, r, k)
                )
              ): Maybe<&2, Ver>
          }
        add_find.fresh(String.eq(i, k), i, x, r, ys, k)(hh)({==})

# a version found after versions are added: the old one when held, else the
# first new one
law add_find:
  for xs: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Tables.Table.get(
      Ver,
      Ver.add(xs, ys),
      k
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, ys, k),
        Tables.Table.find_row(Ver, xs, k)
      ): Maybe<&2, Ver>
  }

def add_find(xs, ys, k):
  match xs:
    case Nil{}:
      Equal.sym(
        Maybe<&2, Ver>,
        Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), None{}),
        Tables.Table.get(Ver, ys, k),
        or_none(Tables.Table.get(Ver, ys, k))
      )
    case Con{Tables.Row{+i, +x}, +r}:
      +ys = ys
      +k = k
      Equal.trans(
        Maybe<&2, Ver>,
        Tables.Table.get(Ver, Ver.add(r, Ver.add.one(Tables.Row{i, x}, ys)), k),
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, Ver.add.one(Tables.Row{i, x}, ys), k),
          Tables.Table.find_row(Ver, r, k)
        ),
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, ys, k),
          Tables.Table.find_row(Ver, Tables.Row{i, x} <> r, k)
        ),
        add_find(r, Ver.add.one(Tables.Row{i, x}, ys), k),
        add_find.one(Ver.has(ys, i), i, x, r, ys, k)({==})
      )

# after a sync, a version is the own one when held, else the other node's
law sync_find:
  for o: Tables.Table<Ver>
  for ys: Tables.Table<Ver>
  for k: String
  {
    Tables.Table.get(
      Ver,
      Ver.add(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys),
      k
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, ys, k),
        Tables.Table.get(Ver, o, k)
      ): Maybe<&2, Ver>
  }

def sync_find(o, ys, k):
  +o = o
  +k = k
  %Tables.Table.rows_find_keys(Ver, o, k):
    {
      Tables.Table.get(
        Ver,
        Ver.add(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys),
        k
      )
        == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), _): Maybe<&2, Ver>
    }
  add_find(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys, k)

# a sync that finds no collision found none at each key it walked
law collides_at.at:
  for hit: Bool
  for j: String
  for r: List<&2, String>
  for os: Tables.Table<Ver>
  for vs: Tables.Table<Ver>
  for k: String
  (
    {
      Sync.collides(r, os, vs) == False{}: Bool
    } -> {
      Strings.has(r, k) == True{}: Bool
    } -> {
      Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{}: Bool
    }
  ) -> {
    String.eq(j, k) == hit: Bool
  } -> {
    Bool.or(
      Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)),
      Sync.collides(r, os, vs)
    )
      == False{}: Bool
  } -> {
    List.any.if(u => Strings.has(r, k), hit) == True{}: Bool
  } -> {Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{}: Bool}

def collides_at.at(hit, j, r, os, vs, k):
  match hit:
    case False{}:
      ih => he => +hc => hn =>
        +j = j
        +os = os
        +vs = vs
        ih(
          Bools.Bool.or_false_right(
            Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)),
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
          Sync.clash.at(Tables.Table.get(Ver, vs, _), Tables.Table.get(Ver, os, _)) == False{}: Bool
        }
        Bools.Bool.or_false_left(
          Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)),
          Sync.collides(r, os, vs)
        )(hc)

law collides_at:
  for ks: List<&2, String>
  for os: Tables.Table<Ver>
  for vs: Tables.Table<Ver>
  for k: String
  {
    Sync.collides(ks, os, vs) == False{}: Bool
  } -> {
    Strings.has(ks, k) == True{}: Bool
  } -> {Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{}: Bool}

def collides_at(ks, os, vs, k):
  match ks:
    case Nil{}:
      hc => hn => Empty.absurd(
        {
          Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{}: Bool
        },
        Shared.Bool.false_ne_true(hn)
      )
    case Con{+j, +r}:
      +os = os
      +vs = vs
      +k = k
      collides_at.at(String.eq(j, k), j, r, os, vs, k)(collides_at(r, os, vs, k))({==})

# when both lookups find a version, they hold the same bytes for each resource
def Compat(mb: Maybe<&2, Ver>, ma: Maybe<&2, Ver>) -> Type:
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
              Ver.blobs.of(Some{u}),
              n
            )
              == Blob.find.of(Ver.blobs.of(Some{v}), n): Maybe<&2, List<&2, U32>>
          }

# compat_of, by the own lookup ma, once the other one found v
law compat_mine:
  for ma: Maybe<&2, Ver>
  for v: Ver
  {Sync.clash.at(ma, Some{v}) == False{}: Bool} -> Compat(Some{v}, ma)

def compat_mine(ma, v):
  match ma v:
    case None{} y:
      h => Unit{}
    case Some{Ver{+ub, up, ua, ut}} Ver{+vb, vp, va, vt}:
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
  for mb: Maybe<&2, Ver>
  for bs: Tables.Table<Ver>
  for as: Tables.Table<Ver>
  for k: String
  {
    Tables.Table.get(Ver, bs, k) == mb: Maybe<&2, Ver>
  } -> {
    Sync.collides(Tables.Table.keys(Ver, bs), bs, as) == False{}: Bool
  } -> Compat(mb, Tables.Table.get(Ver, as, k))

def compat_of.at(mb, bs, as, k):
  match mb:
    case None{}:
      hm => hc => Unit{}
    case Some{v}:
      +hm => hc =>
        +bs = bs
        +as = as
        +k = k
        compat_mine(Tables.Table.get(Ver, as, k), v)((
            %hm: {Sync.clash.at(Tables.Table.get(Ver, as, k), _) == False{}: Bool}
            collides_at(Tables.Table.keys(Ver, bs), bs, as, k)(hc)(Equal.trans(Bool, Strings.has(Tables.Table.keys(Ver, bs), k), Maybe.is_some(&2, Ver, Tables.Table.get(Ver, bs, k)), True{}, Tables.Table.keys_get(Ver, bs, k), Equal.cong(Maybe<&2, Ver>, Bool, z => Maybe.is_some(&2, Ver, z), Tables.Table.get(Ver, bs, k), Some{v}, hm)))))

# when a sync found no collision, versions under the same ID hold the same
# bytes for each resource
law compat_of:
  for bs: Tables.Table<Ver>
  for as: Tables.Table<Ver>
  for k: String
  {
    Sync.collides(Tables.Table.keys(Ver, bs), bs, as) == False{}: Bool
  } -> Compat(Tables.Table.get(Ver, bs, k), Tables.Table.get(Ver, as, k))

def compat_of(bs, as, k):
  +bs = bs
  +k = k
  compat_of.at(Tables.Table.get(Ver, bs, k), bs, as, k)({==})

# after a takes in b, and b takes in that, a resource of a version has the same
# bytes on both
law vb_conv:
  for ma: Maybe<&2, Ver>
  for mb: Maybe<&2, Ver>
  for n: String
  Compat(
    mb,
    ma
  ) -> {
    Blob.find.of(
      Ver.blobs.of(Maybe.or(&2, Ver, ma, mb)),
      n
    )
      == Blob.find.of(
        Ver.blobs.of(Maybe.or(&2, Ver, mb, Maybe.or(&2, Ver, ma, mb))),
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
  for x: Br
  {Br.stamp.cmp(x, x) == EQ{}: Cmp}

def stamp_refl(x):
  match x:
    case Br{h, o, e, c}:
      %Equal.sym(Cmp, Nat.cmp(e, e), EQ{}, Nats.Nat.cmp_refl(e)):
        {Cmps.Cmp.then(_, Cmps.Cmp.then(Nat.cmp(c, c), String.order(h, h))) == EQ{}: Cmp}
      %Equal.sym(Cmp, Nat.cmp(c, c), EQ{}, Nats.Nat.cmp_refl(c)):
        {Cmps.Cmp.then(EQ{}, Cmps.Cmp.then(_, String.order(h, h))) == EQ{}: Cmp}
      Strings.String.order_refl(h)

# comparing stamps the other way round flips the order
law stamp_swap:
  for x: Br
  for y: Br
  {Br.stamp.cmp(y, x) == Cmps.Cmp.flip(Br.stamp.cmp(x, y)): Cmp}

def stamp_swap(x, y):
  match x y:
    case Br{+h1, o1, +e1, +c1} Br{+h2, o2, +e2, +c2}:
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
def Br.head(b: Br) -> String:
  match b:
    case Br{h, o, e, c}:
      h

# branches whose stamps compare EQ have the same head
law stamp_eq_head:
  for x: Br
  for y: Br
  {Br.stamp.cmp(x, y) == EQ{}: Cmp} -> {Br.head(x) == Br.head(y): String}

def stamp_eq_head(x, y):
  match x y:
    case Br{+h1, o1, e1, +c1} Br{+h2, o2, e2, +c2}:
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
  for m: Maybe<&2, Br>
  {Br.head.of(m) == Maybe.map(&2, Br, String, y => Br.head(y), m): Maybe<&2, String>}

def head_of_map(m):
  match m:
    case None{}:
      {==}
    case Some{Br{h, o, e, c}}:
      {==}

# after a takes in b's branch, and b takes in that, both have the same head
law hb_conv:
  for ma: Maybe<&2, Br>
  for mb: Maybe<&2, Br>
  {
    Br.head.of(
      Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)
    )
      == Br.head.of(
        Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
      ): Maybe<&2, String>
  }

def hb_conv(ma, mb):
  +ma = ma
  +mb = mb
  %Equal.sym(
    Maybe<&2, String>,
    Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)),
    Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)),
    head_of_map(Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
  ):
    {
      _
        == Br.head.of(
          Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
        ): Maybe<&2, String>
    }
  %Equal.sym(
    Maybe<&2, String>,
    Br.head.of(
      Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
    ),
    Maybe.map(
      &2,
      Br,
      String,
      y => Br.head(y),
      Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
    ),
    head_of_map(
      Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))
    )
  ):
    {
      Maybe.map(
        &2,
        Br,
        String,
        y => Br.head(y),
        Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)
      )
        == _: Maybe<&2, String>
    }
  Orders.Order.join_conv(
    ~Br,
    ~String,
    ~Br.stamp.cmp,
    ~Br.head,
    y => stamp_refl(y),
    a => b => stamp_swap(a, b),
    a => b => stamp_eq_head(a, b),
    ma,
    mb
  )

# a new branch t of another node, under the key k, where the node had none
law at_new:
  for hit: Bool
  for bs: Tables.Table<Br>
  for k: String
  for t: Br
  for c: String
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(Br, bs, k) == None{}: Maybe<&2, Br>
  } -> {
    Bools.Bool.when(
      Maybe<&2, Br>,
      hit,
      u => Some{t},
      u => Tables.Table.get(Br, bs, c)
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(Br, bs, c)
      ): Maybe<&2, Br>
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
            Orders.Order.pick(Br, Br.stamp.cmp, Tables.Table.get(Br, bs, _), t)
          }: Maybe<&2, Br>
      }; (%Equal.sym(
        Maybe<&2, Br>,
        Tables.Table.get(Br, bs, k),
        None{},
        x1
      ): {Some{t} == Some{Orders.Order.pick(Br, Br.stamp.cmp, _, t)}: Maybe<&2, Br>}; {==}))

# a branch t of another node that wins over the node's mine (LT)
law at_set:
  for hit: Bool
  for bs: Tables.Table<Br>
  for k: String
  for mine: Br
  for t: Br
  for c: String
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(Br, bs, k) == Some{mine}: Maybe<&2, Br>
  } -> {
    Br.stamp.cmp(mine, t) == LT{}: Cmp
  } -> {
    Bools.Bool.when(
      Maybe<&2, Br>,
      hit,
      u => Some{t},
      u => Tables.Table.get(Br, bs, c)
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(Br, bs, c)
      ): Maybe<&2, Br>
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
              ~Br,
              ~Br.stamp.cmp,
              True{},
              Some{t},
              Tables.Table.get(Br, bs, _)
            ): Maybe<&2, Br>
        }
        %Equal.sym(
          Maybe<&2, Br>,
          Tables.Table.get(Br, bs, k),
          Some{mine},
          hm
        ): {Some{t} == Orders.Order.step(~Br, ~Br.stamp.cmp, True{}, Some{t}, _): Maybe<&2, Br>}
        %Equal.sym(
          Cmp,
          Br.stamp.cmp(mine, t),
          LT{},
          hc
        ): {Some{t} == Some{Orders.Order.by(Br, _, mine, t)}: Maybe<&2, Br>}
        {==}

# a branch t of another node that does not win over the node's mine
law at_stay:
  for hit: Bool
  for bs: Tables.Table<Br>
  for k: String
  for mine: Br
  for t: Br
  for c: String
  for c0: Cmp
  {
    String.eq(k, c) == hit: Bool
  } -> {
    Tables.Table.get(Br, bs, k) == Some{mine}: Maybe<&2, Br>
  } -> {
    Br.stamp.cmp(mine, t) == c0: Cmp
  } -> {
    Orders.Order.by(Br, c0, mine, t) == mine: Br
  } -> {
    Tables.Table.get(
      Br,
      bs,
      c
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        hit,
        Some{t},
        Tables.Table.get(Br, bs, c)
      ): Maybe<&2, Br>
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
            Br,
            bs,
            _
          )
            == Orders.Order.step(
              ~Br,
              ~Br.stamp.cmp,
              True{},
              Some{t},
              Tables.Table.get(Br, bs, _)
            ): Maybe<&2, Br>
        }
        %Equal.sym(
          Maybe<&2, Br>,
          Tables.Table.get(Br, bs, k),
          Some{mine},
          hm
        ): {_ == Orders.Order.step(~Br, ~Br.stamp.cmp, True{}, Some{t}, _): Maybe<&2, Br>}
        %Equal.sym(
          Cmp,
          Br.stamp.cmp(mine, t),
          c0,
          hc
        ): {Some{mine} == Some{Orders.Order.by(Br, _, mine, t)}: Maybe<&2, Br>}
        %Equal.sym(
          Br,
          Orders.Order.by(Br, c0, mine, t),
          mine,
          hb
        ): {Some{mine} == Some{_}: Maybe<&2, Br>}
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
  for vs: Tables.Table<Ver>
  for bs: Tables.Table<Br>
  for cs: Tables.Table<Clash>
  for ns: List<&2, Logged>
  for c: String
  {
    Tables.Table.get(Br, bs, k) == Some{Br{mh, mo, me, mk}}: Maybe<&2, Br>
  } -> {
    Br.stamp.cmp(Br{mh, mo, me, mk}, Br{th, to, te, tk}) == c0: Cmp
  } -> {
    Tables.Table.get(
      Br,
      Mix.branches(Sync.pick(c0, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, vs, Mix{bs, cs, ns})),
      c
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        String.eq(k, c),
        Some{Br{th, to, te, tk}},
        Tables.Table.get(Br, bs, c)
      ): Maybe<&2, Br>
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
          Maybe<&2, Br>,
          Tables.Table.get(Br, Tables.Table.set(Br, bs, k, Br{th, to, te, tk}), c),
          Bools.Bool.when(
            Maybe<&2, Br>,
            String.eq(k, c),
            u => Some{Br{th, to, te, tk}},
            u => Tables.Table.get(Br, bs, c)
          ),
          Tables.Table.get_set(Br, bs, k, Br{th, to, te, tk}, c)
        ):
          {
            _
              == Orders.Order.step(
                ~Br,
                ~Br.stamp.cmp,
                String.eq(k, c),
                Some{Br{th, to, te, tk}},
                Tables.Table.get(Br, bs, c)
              ): Maybe<&2, Br>
          }
        at_set(String.eq(k, c), bs, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, c)({==})(hm)(hc)
    case GT{}:
      hm => hc =>
        +k = k
        +c = c
        at_stay(
          String.eq(k, c),
          bs,
          k,
          Br{mh, mo, me, mk},
          Br{th, to, te, tk},
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
          Br{mh, mo, me, mk},
          Br{th, to, te, tk},
          c,
          EQ{}
        )({==})(hm)(hc)({==})

# the branches after another node's t met the branch that m0 holds
law at_find:
  for m0: Maybe<&2, Br>
  for k: String
  for th: String
  for to: String
  for te: Nat
  for tk: Nat
  for vs: Tables.Table<Ver>
  for bs: Tables.Table<Br>
  for cs: Tables.Table<Clash>
  for ns: List<&2, Logged>
  for c: String
  {
    Tables.Table.get(Br, bs, k) == m0: Maybe<&2, Br>
  } -> {
    Tables.Table.get(
      Br,
      Mix.branches(Sync.at(m0, k, Br{th, to, te, tk}, vs, Mix{bs, cs, ns})),
      c
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        String.eq(k, c),
        Some{Br{th, to, te, tk}},
        Tables.Table.get(Br, bs, c)
      ): Maybe<&2, Br>
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
          Maybe<&2, Br>,
          Tables.Table.get(Br, Tables.Table.set(Br, bs, k, Br{th, to, te, tk}), c),
          Bools.Bool.when(
            Maybe<&2, Br>,
            String.eq(k, c),
            u => Some{Br{th, to, te, tk}},
            u => Tables.Table.get(Br, bs, c)
          ),
          Tables.Table.get_set(Br, bs, k, Br{th, to, te, tk}, c)
        ):
          {
            _
              == Orders.Order.step(
                ~Br,
                ~Br.stamp.cmp,
                String.eq(k, c),
                Some{Br{th, to, te, tk}},
                Tables.Table.get(Br, bs, c)
              ): Maybe<&2, Br>
          }
        at_new(String.eq(k, c), bs, k, Br{th, to, te, tk}, c)({==})(hm)
    case Some{Br{+mh, +mo, +me, +mk}}:
      hm =>
        +th = th
        +to = to
        +te = te
        +tk = tk
        pick_find(
          Br.stamp.cmp(Br{mh, mo, me, mk}, Br{th, to, te, tk}),
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
  for f: Maybe<&2, Br>
  for acc: Mix
  for vs: Tables.Table<Ver>
  for c: String
  {
    Tables.Table.get(
      Br,
      Mix.branches(Sync.seen.meet(k, f, acc, vs)),
      c
    )
      == Orders.Order.step(
        ~Br,
        ~Br.stamp.cmp,
        String.eq(k, c),
        f,
        Tables.Table.get(Br, Mix.branches(acc), c)
      ): Maybe<&2, Br>
  }

def seen_find(k, f, acc, vs, c):
  match f acc:
    case None{} Mix{bs, cs, ns}:
      +c = c
      Equal.sym(
        Maybe<&2, Br>,
        Orders.Order.step(~Br, ~Br.stamp.cmp, String.eq(k, c), None{}, Tables.Table.get(Br, bs, c)),
        Tables.Table.get(Br, bs, c),
        Orders.Order.step_none(~Br, ~Br.stamp.cmp, String.eq(k, c), Tables.Table.get(Br, bs, c))
      )
    case Some{Br{th, to, te, tk}} Mix{+bs, cs, ns}:
      +k = k
      at_find(Tables.Table.get(Br, bs, k), k, th, to, te, tk, vs, bs, cs, ns, c)({==})

# a sync's branch pass, as a fold
law brs_fold_find:
  for ks: List<&2, String>
  for full: Tables.Table<Br>
  for vs: Tables.Table<Ver>
  for acc: Mix
  for c: String
  {
    Tables.Table.get(
      Br,
      Mix.branches(Sync.branches(ks, full, vs, acc)),
      c
    )
      == Orders.Order.fold(
        ~Br,
        ~Tables.Table<Br>,
        ~Br.stamp.cmp,
        ~(t => k => Tables.Table.get(Br, t, k)),
        ks,
        full,
        c,
        Tables.Table.get(Br, Mix.branches(acc), c)
      ): Maybe<&2, Br>
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
      %seen_find(k, Tables.Table.get(Br, full, k), acc, vs, c):
        {
          Tables.Table.get(
            Br,
            Mix.branches(
              Sync.branches(r, full, vs, Sync.seen.meet(k, Tables.Table.get(Br, full, k), acc, vs))
            ),
            c
          )
            == Orders.Order.fold(
              ~Br,
              ~Tables.Table<Br>,
              ~Br.stamp.cmp,
              ~(t => k => Tables.Table.get(Br, t, k)),
              r,
              full,
              c,
              _
            ): Maybe<&2, Br>
        }
      brs_fold_find(r, full, vs, Sync.seen.meet(k, Tables.Table.get(Br, full, k), acc, vs), c)

# after a sync's branch pass, a branch is the winner of the node's own and the
# other node's
law sync_branches_find:
  for full: Tables.Table<Br>
  for vs: Tables.Table<Ver>
  for acc: Mix
  for c: String
  {
    Tables.Table.get(
      Br,
      Mix.branches(Sync.branches(Tables.Table.keys(Br, full), full, vs, acc)),
      c
    )
      == Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Tables.Table.get(Br, Mix.branches(acc), c),
        Tables.Table.get(Br, full, c)
      ): Maybe<&2, Br>
  }

def sync_branches_find(full, vs, acc, c):
  +full = full
  +acc = acc
  +c = c
  Equal.trans(
    Maybe<&2, Br>,
    Tables.Table.get(
      Br,
      Mix.branches(Sync.branches(Tables.Table.keys(Br, full), full, vs, acc)),
      c
    ),
    Orders.Order.fold(
      ~Br,
      ~Tables.Table<Br>,
      ~Br.stamp.cmp,
      ~(t => k => Tables.Table.get(Br, t, k)),
      Tables.Table.keys(Br, full),
      full,
      c,
      Tables.Table.get(Br, Mix.branches(acc), c)
    ),
    Orders.Order.join(
      ~Br,
      ~Br.stamp.cmp,
      Tables.Table.get(Br, Mix.branches(acc), c),
      Tables.Table.get(Br, full, c)
    ),
    brs_fold_find(Tables.Table.keys(Br, full), full, vs, acc, c),
    Orders.Order.fold_all(
      ~Br,
      ~Tables.Table<Br>,
      ~Br.stamp.cmp,
      ~(t => k => Tables.Table.get(Br, t, k)),
      y => stamp_refl(y),
      Tables.Table.keys(Br, full),
      full,
      c,
      Tables.Table.get(Br, Mix.branches(acc), c),
      h => Tables.Table.none_of(
        Br,
        Tables.Table.get(Br, full, c)
      )(
        Equal.trans(
          Bool,
          Maybe.is_some(&2, Br, Tables.Table.get(Br, full, c)),
          Strings.has(Tables.Table.keys(Br, full), c),
          False{},
          Equal.sym(
            Bool,
            Strings.has(Tables.Table.keys(Br, full), c),
            Maybe.is_some(&2, Br, Tables.Table.get(Br, full, c)),
            Tables.Table.keys_get(Br, full, c)
          ),
          h
        )
      )
    )
  )

# the order of versions for marks: the smaller version is the greater
def Ver.rev(a: String, b: String) -> Cmp:
  String.order(b, a)

# the version order of marks compares EQ with itself
law rev_refl:
  for a: String
  {Ver.rev(a, a) == EQ{}: Cmp}

def rev_refl(a):
  Strings.String.order_refl(a)

# the version order of marks the other way round is flipped
law rev_swap:
  for a: String
  for b: String
  {Ver.rev(b, a) == Cmps.Cmp.flip(Ver.rev(a, b)): Cmp}

def rev_swap(a, b):
  Strings.String.order_swap(b, a, EQ{})

# versions that the version order of marks calls EQ are equal
law rev_same:
  for a: String
  for b: String
  {Ver.rev(a, b) == EQ{}: Cmp} -> {a == b: String}

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
      Orders.Order.step(~String, ~Ver.rev, hm, f, mv)

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
        ~Ver.rev,
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
        ~Ver.rev,
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
            == Orders.Order.join(~String, ~Ver.rev, _, Some{v}): Maybe<&2, String>
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
            == Orders.Order.join(~String, ~Ver.rev, _, Some{v}): Maybe<&2, String>
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
        ~Ver.rev,
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
              ~Ver.rev,
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
              ~Ver.rev,
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
            ~Ver.rev,
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
            ~Ver.rev,
            ~(t => k => MarkAt.version.of(Tables.Table.get(MarkAt, t, k))),
            r,
            inner,
            qm,
            Orders.Order.step(
              ~String,
              ~Ver.rev,
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
              ~Ver.rev,
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
              ~Ver.rev,
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
        ~Ver.rev,
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
        ~Ver.rev,
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
              Strings.has(Tables.Table.keys(MarkAt, inner), qm),
              False{},
              Equal.sym(
                Bool,
                Strings.has(Tables.Table.keys(MarkAt, inner), qm),
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
        ~Ver.rev,
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
      ~Ver.rev,
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
        ~Ver.rev,
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
              ~Ver.rev,
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
        ~Ver.rev,
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
      ~Ver.rev,
      ~Marks.at,
      Tables.Table.keys(Tables.Table<MarkAt>, full),
      (full, qm),
      qb,
      MarkAt.find(ms, qb, qm)
    ),
    Orders.Order.join(~String, ~Ver.rev, MarkAt.find(ms, qb, qm), MarkAt.find(full, qb, qm)),
    marks_fold_find(Tables.Table.keys(Tables.Table<MarkAt>, full), full, Marked{ms, ns}, qb, qm),
    Orders.Order.fold_all(
      ~String,
      ~(+Sigma<Tables.Table<Tables.Table<MarkAt>>, _ => String>),
      ~Ver.rev,
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
            Strings.has(Tables.Table.keys(Tables.Table<MarkAt>, full), qb),
            False{},
            Equal.sym(
              Bool,
              Strings.has(Tables.Table.keys(Tables.Table<MarkAt>, full), qb),
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
  for s: St
  for r: String
  for out: Out
  {
    St.marks(
      Pair.fst(St, Spec.Answer, Node.applied(s, r, out))
    )
      == Out.marks(out): Tables.Table<Tables.Table<MarkAt>>
  }

def marks_after_applied(s, r, out):
  match s out:
    case St{k, vs, bs, ms, gs, cs, ss, l} Out{nv, nb, nm, ng, nc, news, a}:
      {==}

# mapping the identity changes nothing
law map_id:
  for m: Maybe<&2, String>
  {Maybe.map(&2, String, String, y => y, m) == m: Maybe<&2, String>}

def map_id(m):
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# after a takes in b's mark, and b takes in that, both hold the same version
law mk_conv:
  for ma: Maybe<&2, String>
  for mb: Maybe<&2, String>
  {
    Orders.Order.join(
      ~String,
      ~Ver.rev,
      ma,
      mb
    )
      == Orders.Order.join(
        ~String,
        ~Ver.rev,
        mb,
        Orders.Order.join(~String, ~Ver.rev, ma, mb)
      ): Maybe<&2, String>
  }

def mk_conv(ma, mb):
  +ma = ma
  +mb = mb
  Equal.trans(
    Maybe<&2, String>,
    Orders.Order.join(~String, ~Ver.rev, ma, mb),
    Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~Ver.rev, ma, mb)),
    Orders.Order.join(~String, ~Ver.rev, mb, Orders.Order.join(~String, ~Ver.rev, ma, mb)),
    Equal.sym(
      Maybe<&2, String>,
      Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~Ver.rev, ma, mb)),
      Orders.Order.join(~String, ~Ver.rev, ma, mb),
      map_id(Orders.Order.join(~String, ~Ver.rev, ma, mb))
    ),
    Equal.trans(
      Maybe<&2, String>,
      Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~Ver.rev, ma, mb)),
      Maybe.map(
        &2,
        String,
        String,
        y => y,
        Orders.Order.join(~String, ~Ver.rev, mb, Orders.Order.join(~String, ~Ver.rev, ma, mb))
      ),
      Orders.Order.join(~String, ~Ver.rev, mb, Orders.Order.join(~String, ~Ver.rev, ma, mb)),
      Orders.Order.join_conv(
        ~String,
        ~String,
        ~Ver.rev,
        ~(y => y),
        y => rev_refl(y),
        a => b => rev_swap(a, b),
        a => b => rev_same(a, b),
        ma,
        mb
      ),
      map_id(Orders.Order.join(~String, ~Ver.rev, mb, Orders.Order.join(~String, ~Ver.rev, ma, mb)))
    )
  )

# versions that agree on a resource at each key agree at any version m
law find_any:
  for m: Maybe<&2, String>
  for v1: Tables.Table<Ver>
  for v2: Tables.Table<Ver>
  for n: String
  (
    @k: String -> {
      Blob.find.of(
        Ver.blobs.of(Tables.Table.get(Ver, v1, k)),
        n
      )
        == Blob.find.of(Ver.blobs.of(Tables.Table.get(Ver, v2, k)), n): Maybe<&2, List<&2, U32>>
    }
  ) -> {
    Blob.find.of(
      Ver.blobs.of(Ver.find.of(v1, m)),
      n
    )
      == Blob.find.of(Ver.blobs.of(Ver.find.of(v2, m)), n): Maybe<&2, List<&2, U32>>
  }

def find_any(m, v1, v2, n):
  match m:
    case None{}:
      vv => {==}
    case Some{k}:
      vv => vv(k)

# states whose versions, heads and marks agree hold the same content
law content_eq:
  for s1: St
  for s2: St
  for n: String
  for p: Spec.Point
  (
    @k: String -> {
      Blob.find.of(
        Ver.blobs.of(Tables.Table.get(Ver, St.versions(s1), k)),
        n
      )
        == Blob.find.of(
          Ver.blobs.of(Tables.Table.get(Ver, St.versions(s2), k)),
          n
        ): Maybe<&2, List<&2, U32>>
    }
  ) -> (
    @c: String -> {
      Br.head.of(
        Tables.Table.get(Br, St.branches(s1), c)
      )
        == Br.head.of(Tables.Table.get(Br, St.branches(s2), c)): Maybe<&2, String>
    }
  ) -> (
    @b: String -> @m: String -> {
      MarkAt.find(St.marks(s1), b, m) == MarkAt.find(St.marks(s2), b, m): Maybe<&2, String>
    }
  ) -> {St.content(s1, n, p) == St.content(s2, n, p): Maybe<&2, List<&2, U32>>}

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
            Ver.blobs.of(
              Ver.find.of(St.versions(s1), Br.head.of(Tables.Table.get(Br, St.branches(s1), b)))
            ),
            n
          )
            == Blob.find.of(
              Ver.blobs.of(Ver.find.of(St.versions(s2), _)),
              n
            ): Maybe<&2, List<&2, U32>>
        }
        find_any(
          Br.head.of(Tables.Table.get(Br, St.branches(s1), b)),
          St.versions(s1),
          St.versions(s2),
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
            Ver.blobs.of(Ver.find.of(St.versions(s1), MarkAt.find(St.marks(s1), b, m))),
            n
          )
            == Blob.find.of(
              Ver.blobs.of(Ver.find.of(St.versions(s2), _)),
              n
            ): Maybe<&2, List<&2, U32>>
        }
        find_any(MarkAt.find(St.marks(s1), b, m), St.versions(s1), St.versions(s2), n)(vv)

# after a sync, a version is the own one when held, else the other node's
law after_v:
  for s: St
  for o: St
  for r: String
  for k: String
  {
    Tables.Table.get(
      Ver,
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      k
    )
      == Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, St.versions(s), k),
        Tables.Table.get(Ver, St.versions(o), k)
      ): Maybe<&2, Ver>
  }

def after_v(s, o, r, k):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, Ver>,
    Tables.Table.get(
      Ver,
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      k
    ),
    Tables.Table.get(
      Ver,
      Ver.add(
        Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o)),
        St.versions(s)
      ),
      k
    ),
    Maybe.or(
      &2,
      Ver,
      Tables.Table.get(Ver, St.versions(s), k),
      Tables.Table.get(Ver, St.versions(o), k)
    ),
    Equal.cong(
      Tables.Table<Ver>,
      Maybe<&2, Ver>,
      z => Tables.Table.get(Ver, z, k),
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      Ver.add(
        Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o)),
        St.versions(s)
      ),
      versions_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    sync_find(St.versions(o), St.versions(s), k)
  )

# after a sync, a branch is the winner of the own and the other node's
law after_b:
  for s: St
  for o: St
  for r: String
  for c: String
  {
    Tables.Table.get(
      Br,
      St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      c
    )
      == Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Tables.Table.get(Br, St.branches(s), c),
        Tables.Table.get(Br, St.branches(o), c)
      ): Maybe<&2, Br>
  }

def after_b(s, o, r, c):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, Br>,
    Tables.Table.get(
      Br,
      St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      c
    ),
    Tables.Table.get(
      Br,
      Mix.branches(
        Sync.branches(
          Tables.Table.keys(Br, St.branches(o)),
          St.branches(o),
          Ver.add(
            Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o)),
            St.versions(s)
          ),
          Mix{St.branches(s), St.clashes(s), []}
        )
      ),
      c
    ),
    Orders.Order.join(
      ~Br,
      ~Br.stamp.cmp,
      Tables.Table.get(Br, St.branches(s), c),
      Tables.Table.get(Br, St.branches(o), c)
    ),
    Equal.cong(
      Tables.Table<Br>,
      Maybe<&2, Br>,
      z => Tables.Table.get(Br, z, c),
      St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      Mix.branches(
        Sync.branches(
          Tables.Table.keys(Br, St.branches(o)),
          St.branches(o),
          Ver.add(
            Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o)),
            St.versions(s)
          ),
          Mix{St.branches(s), St.clashes(s), []}
        )
      ),
      branches_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    sync_branches_find(
      St.branches(o),
      Ver.add(
        Tables.Table.rows(Ver, Tables.Table.keys(Ver, St.versions(o)), St.versions(o)),
        St.versions(s)
      ),
      Mix{St.branches(s), St.clashes(s), []},
      c
    )
  )

# after a sync, a mark has the smaller of the own and the other node's versions
law after_m:
  for s: St
  for o: St
  for r: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      qb,
      qm
    )
      == Orders.Order.join(
        ~String,
        ~Ver.rev,
        MarkAt.find(St.marks(s), qb, qm),
        MarkAt.find(St.marks(o), qb, qm)
      ): Maybe<&2, String>
  }

def after_m(s, o, r, qb, qm):
  +s = s
  +o = o
  Equal.trans(
    Maybe<&2, String>,
    MarkAt.find(
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      qb,
      qm
    ),
    MarkAt.find(
      Marked.marks(
        Sync.marks(
          Tables.Table.keys(Tables.Table<MarkAt>, St.marks(o)),
          St.marks(o),
          Marked{St.marks(s), []}
        )
      ),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~Ver.rev,
      MarkAt.find(St.marks(s), qb, qm),
      MarkAt.find(St.marks(o), qb, qm)
    ),
    Equal.cong(
      Tables.Table<Tables.Table<MarkAt>>,
      Maybe<&2, String>,
      z => MarkAt.find(z, qb, qm),
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o)))),
      Marked.marks(
        Sync.marks(
          Tables.Table.keys(Tables.Table<MarkAt>, St.marks(o)),
          St.marks(o),
          Marked{St.marks(s), []}
        )
      ),
      marks_after_applied(s, r, Sync.go(False{}, s, o))
    ),
    marks_sync_find(St.marks(o), St.marks(s), [], qb, qm)
  )

# a takes in b, then b takes in that: a resource of a version agrees
law conv_v:
  for a: St
  for b: St
  for r1: String
  for r2: String
  for n: String
  for k: String
  {
    Sync.collides(
      Tables.Table.keys(Ver, St.versions(b)),
      St.versions(b),
      St.versions(a)
    )
      == False{}: Bool
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Tables.Table.get(
          Ver,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
          k
        )
      ),
      n
    )
      == Blob.find.of(
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
            k
          )
        ),
        n
      ),
      Blob.find.of(
        Ver.blobs.of(
          Maybe.or(
            &2,
            Ver,
            Tables.Table.get(Ver, St.versions(a), k),
            Tables.Table.get(Ver, St.versions(b), k)
          )
        ),
        n
      ),
      Blob.find.of(
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
        Maybe<&2, Ver>,
        Maybe<&2, List<&2, U32>>,
        z => Blob.find.of(Ver.blobs.of(z), n),
        Tables.Table.get(
          Ver,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
          k
        ),
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, St.versions(a), k),
          Tables.Table.get(Ver, St.versions(b), k)
        ),
        after_v(a, b, r1, k)
      ),
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Blob.find.of(
          Ver.blobs.of(
            Maybe.or(
              &2,
              Ver,
              Tables.Table.get(Ver, St.versions(a), k),
              Tables.Table.get(Ver, St.versions(b), k)
            )
          ),
          n
        ),
        Blob.find.of(
          Ver.blobs.of(
            Maybe.or(
              &2,
              Ver,
              Tables.Table.get(Ver, St.versions(b), k),
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(a), k),
                Tables.Table.get(Ver, St.versions(b), k)
              )
            )
          ),
          n
        ),
        Blob.find.of(
          Ver.blobs.of(
            Tables.Table.get(
              Ver,
              St.versions(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
          Tables.Table.get(Ver, St.versions(a), k),
          Tables.Table.get(Ver, St.versions(b), k),
          n
        )(compat_of(St.versions(b), St.versions(a), k)(hc)),
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Blob.find.of(
            Ver.blobs.of(
              Tables.Table.get(
                Ver,
                St.versions(
                  Pair.fst(
                    St,
                    Spec.Answer,
                    Node.applied(
                      b,
                      r2,
                      Sync.go(
                        False{},
                        b,
                        Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
            Ver.blobs.of(
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(b), k),
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(a), k),
                  Tables.Table.get(Ver, St.versions(b), k)
                )
              )
            ),
            n
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(
              Ver.blobs.of(
                Tables.Table.get(
                  Ver,
                  St.versions(
                    Pair.fst(
                      St,
                      Spec.Answer,
                      Node.applied(
                        b,
                        r2,
                        Sync.go(
                          False{},
                          b,
                          Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
              Ver.blobs.of(
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(b), k),
                  Tables.Table.get(
                    Ver,
                    St.versions(
                      Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                    ),
                    k
                  )
                )
              ),
              n
            ),
            Blob.find.of(
              Ver.blobs.of(
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(b), k),
                  Maybe.or(
                    &2,
                    Ver,
                    Tables.Table.get(Ver, St.versions(a), k),
                    Tables.Table.get(Ver, St.versions(b), k)
                  )
                )
              ),
              n
            ),
            Equal.cong(
              Maybe<&2, Ver>,
              Maybe<&2, List<&2, U32>>,
              z => Blob.find.of(Ver.blobs.of(z), n),
              Tables.Table.get(
                Ver,
                St.versions(
                  Pair.fst(
                    St,
                    Spec.Answer,
                    Node.applied(
                      b,
                      r2,
                      Sync.go(
                        False{},
                        b,
                        Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                      )
                    )
                  )
                ),
                k
              ),
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(b), k),
                Tables.Table.get(
                  Ver,
                  St.versions(
                    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                  ),
                  k
                )
              ),
              after_v(
                b,
                Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))),
                r2,
                k
              )
            ),
            Equal.cong(
              Maybe<&2, Ver>,
              Maybe<&2, List<&2, U32>>,
              z => Blob.find.of(
                Ver.blobs.of(Maybe.or(&2, Ver, Tables.Table.get(Ver, St.versions(b), k), z)),
                n
              ),
              Tables.Table.get(
                Ver,
                St.versions(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
                k
              ),
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(a), k),
                Tables.Table.get(Ver, St.versions(b), k)
              ),
              after_v(a, b, r1, k)
            )
          )
        )
      )
    )

# a takes in b, then b takes in that: a branch head agrees
law conv_h:
  for a: St
  for b: St
  for r1: String
  for r2: String
  for c: String
  {
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
        c
      )
    )
      == Br.head.of(
        Tables.Table.get(
          Br,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
        c
      )
    ),
    Br.head.of(
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Tables.Table.get(Br, St.branches(a), c),
        Tables.Table.get(Br, St.branches(b), c)
      )
    ),
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
              )
            )
          )
        ),
        c
      )
    ),
    Equal.cong(
      Maybe<&2, Br>,
      Maybe<&2, String>,
      z => Br.head.of(z),
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
        c
      ),
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Tables.Table.get(Br, St.branches(a), c),
        Tables.Table.get(Br, St.branches(b), c)
      ),
      after_b(a, b, r1, c)
    ),
    Equal.trans(
      Maybe<&2, String>,
      Br.head.of(
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(a), c),
          Tables.Table.get(Br, St.branches(b), c)
        )
      ),
      Br.head.of(
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(b), c),
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(a), c),
            Tables.Table.get(Br, St.branches(b), c)
          )
        )
      ),
      Br.head.of(
        Tables.Table.get(
          Br,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          c
        )
      ),
      hb_conv(Tables.Table.get(Br, St.branches(a), c), Tables.Table.get(Br, St.branches(b), c)),
      Equal.sym(
        Maybe<&2, String>,
        Br.head.of(
          Tables.Table.get(
            Br,
            St.branches(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                  )
                )
              )
            ),
            c
          )
        ),
        Br.head.of(
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(b), c),
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(a), c),
              Tables.Table.get(Br, St.branches(b), c)
            )
          )
        ),
        Equal.trans(
          Maybe<&2, String>,
          Br.head.of(
            Tables.Table.get(
              Br,
              St.branches(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                    )
                  )
                )
              ),
              c
            )
          ),
          Br.head.of(
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(b), c),
              Tables.Table.get(
                Br,
                St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
                c
              )
            )
          ),
          Br.head.of(
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(b), c),
              Orders.Order.join(
                ~Br,
                ~Br.stamp.cmp,
                Tables.Table.get(Br, St.branches(a), c),
                Tables.Table.get(Br, St.branches(b), c)
              )
            )
          ),
          Equal.cong(
            Maybe<&2, Br>,
            Maybe<&2, String>,
            z => Br.head.of(z),
            Tables.Table.get(
              Br,
              St.branches(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    b,
                    r2,
                    Sync.go(
                      False{},
                      b,
                      Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                    )
                  )
                )
              ),
              c
            ),
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(b), c),
              Tables.Table.get(
                Br,
                St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
                c
              )
            ),
            after_b(
              b,
              Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))),
              r2,
              c
            )
          ),
          Equal.cong(
            Maybe<&2, Br>,
            Maybe<&2, String>,
            z => Br.head.of(
              Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(b), c), z)
            ),
            Tables.Table.get(
              Br,
              St.branches(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
              c
            ),
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(a), c),
              Tables.Table.get(Br, St.branches(b), c)
            ),
            after_b(a, b, r1, c)
          )
        )
      )
    )
  )

# a takes in b, then b takes in that: a mark agrees
law conv_m:
  for a: St
  for b: St
  for r1: String
  for r2: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
      qb,
      qm
    )
      == MarkAt.find(
        St.marks(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
      qb,
      qm
    ),
    Orders.Order.join(
      ~String,
      ~Ver.rev,
      MarkAt.find(St.marks(a), qb, qm),
      MarkAt.find(St.marks(b), qb, qm)
    ),
    MarkAt.find(
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            b,
            r2,
            Sync.go(
              False{},
              b,
              Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
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
        ~Ver.rev,
        MarkAt.find(St.marks(a), qb, qm),
        MarkAt.find(St.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        MarkAt.find(St.marks(b), qb, qm),
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(a), qb, qm),
          MarkAt.find(St.marks(b), qb, qm)
        )
      ),
      MarkAt.find(
        St.marks(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              b,
              r2,
              Sync.go(
                False{},
                b,
                Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
              )
            )
          )
        ),
        qb,
        qm
      ),
      mk_conv(MarkAt.find(St.marks(a), qb, qm), MarkAt.find(St.marks(b), qb, qm)),
      Equal.sym(
        Maybe<&2, String>,
        MarkAt.find(
          St.marks(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                b,
                r2,
                Sync.go(
                  False{},
                  b,
                  Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                )
              )
            )
          ),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(b), qb, qm),
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(a), qb, qm),
            MarkAt.find(St.marks(b), qb, qm)
          )
        ),
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            St.marks(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  b,
                  r2,
                  Sync.go(
                    False{},
                    b,
                    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
                  )
                )
              )
            ),
            qb,
            qm
          ),
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(b), qb, qm),
            MarkAt.find(
              St.marks(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
              qb,
              qm
            )
          ),
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(b), qb, qm),
            Orders.Order.join(
              ~String,
              ~Ver.rev,
              MarkAt.find(St.marks(a), qb, qm),
              MarkAt.find(St.marks(b), qb, qm)
            )
          ),
          after_m(
            b,
            Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))),
            r2,
            qb,
            qm
          ),
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, String>,
            z => Orders.Order.join(~String, ~Ver.rev, MarkAt.find(St.marks(b), qb, qm), z),
            MarkAt.find(
              St.marks(Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))),
              qb,
              qm
            ),
            Orders.Order.join(
              ~String,
              ~Ver.rev,
              MarkAt.find(St.marks(a), qb, qm),
              MarkAt.find(St.marks(b), qb, qm)
            ),
            after_m(a, b, r1, qb, qm)
          )
        )
      )
    )
  )

# a takes in b, then b takes in that: both hold the same content
law conv_core:
  for a: St
  for b: St
  for r1: String
  for r2: String
  {
    Sync.collides(
      Tables.Table.keys(Ver, St.versions(b)),
      St.versions(b),
      St.versions(a)
    )
      == False{}: Bool
  } -> Spec.Node.SameContent(
    Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))),
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(
        b,
        r2,
        Sync.go(False{}, b, Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))))
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
      Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b))),
      Pair.fst(
        St,
        Spec.Answer,
        Node.applied(
          b,
          r2,
          Sync.go(
            False{},
            b,
            Pair.fst(St, Spec.Answer, Node.applied(a, r1, Sync.go(False{}, a, b)))
          )
        )
      ),
      n,
      p
    )(
      k => conv_v(a, b, r1, r2, n, k)(hc)
    )(c => conv_h(a, b, r1, r2, c))(qb => qm => conv_m(a, b, r1, r2, qb, qm))

# a sync that answers Synced found no collision
law sync_clean:
  for s: St
  for o: St
  for r: String
  for w: String
  for z: String
  for t: St
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Sync{o, None{}}
    )
      == (t, Spec.Answer.Sync{Spec.Sync.Synced{}}): St
      & Spec.Answer
  } -> {
    Sync.collides(
      Tables.Table.keys(Ver, St.versions(o)),
      St.versions(o),
      St.versions(s)
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
      Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
      s,
      o
    )(
      applied_answer(
        s,
        r,
        Sync.go(
          Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
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
  for s: St
  for o: St
  for r: String
  for w: String
  for z: String
  for t: St
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Sync{o, None{}}
    )
      == (t, Spec.Answer.Sync{Spec.Sync.Synced{}}): St
      & Spec.Answer
  } -> {Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o))) == t: St}

def sync_state(s, o, r, w, z, t):
  +hn => +h =>
    +s = s
    +o = o
    +r = r
    +w = w
    +z = z
    +t = t
    Equal.trans(
      St,
      Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(False{}, s, o))),
      Pair.fst(
        St,
        Spec.Answer,
        Node.applied(
          s,
          r,
          Sync.go(
            Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
            s,
            o
          )
        )
      ),
      t,
      Equal.cong(
        Bool,
        St,
        x => Pair.fst(St, Spec.Answer, Node.applied(s, r, Sync.go(x, s, o))),
        False{},
        Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
        Equal.sym(
          Bool,
          Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
          False{},
          sync_clean(s, o, r, w, z, t)(hn)(h)
        )
      ),
      applied_state(
        s,
        r,
        Sync.go(
          Sync.collides(Tables.Table.keys(Ver, St.versions(o)), St.versions(o), St.versions(s)),
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

# taking in the same version again keeps the first pick
law or_idem:
  for x: Maybe<&2, Ver>
  for y: Maybe<&2, Ver>
  {Maybe.or(&2, Ver, Maybe.or(&2, Ver, x, y), y) == Maybe.or(&2, Ver, x, y): Maybe<&2, Ver>}

def or_idem(x, y):
  match x y:
    case None{} None{}:
      {==}
    case None{} Some{v}:
      {==}
    case Some{u} w:
      {==}

# s takes in a twice: a version is as after once
law idem_v:
  for s: St
  for a: St
  for r1: String
  for r2: String
  for k: String
  {
    Tables.Table.get(
      Ver,
      St.versions(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      k
    )
      == Tables.Table.get(
        Ver,
        St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        k
      ): Maybe<&2, Ver>
  }

def idem_v(s, a, r1, r2, k):
  +s = s
  +a = a
  +r1 = r1
  +k = k
  Equal.trans(
    Maybe<&2, Ver>,
    Tables.Table.get(
      Ver,
      St.versions(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      k
    ),
    Maybe.or(
      &2,
      Ver,
      Tables.Table.get(
        Ver,
        St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        k
      ),
      Tables.Table.get(Ver, St.versions(a), k)
    ),
    Tables.Table.get(
      Ver,
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
      k
    ),
    after_v(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), a, r2, k),
    Equal.trans(
      Maybe<&2, Ver>,
      Maybe.or(
        &2,
        Ver,
        Tables.Table.get(
          Ver,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          k
        ),
        Tables.Table.get(Ver, St.versions(a), k)
      ),
      Maybe.or(
        &2,
        Ver,
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, St.versions(s), k),
          Tables.Table.get(Ver, St.versions(a), k)
        ),
        Tables.Table.get(Ver, St.versions(a), k)
      ),
      Tables.Table.get(
        Ver,
        St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        k
      ),
      Equal.cong(
        Maybe<&2, Ver>,
        Maybe<&2, Ver>,
        z => Maybe.or(&2, Ver, z, Tables.Table.get(Ver, St.versions(a), k)),
        Tables.Table.get(
          Ver,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          k
        ),
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, St.versions(s), k),
          Tables.Table.get(Ver, St.versions(a), k)
        ),
        after_v(s, a, r1, k)
      ),
      Equal.trans(
        Maybe<&2, Ver>,
        Maybe.or(
          &2,
          Ver,
          Maybe.or(
            &2,
            Ver,
            Tables.Table.get(Ver, St.versions(s), k),
            Tables.Table.get(Ver, St.versions(a), k)
          ),
          Tables.Table.get(Ver, St.versions(a), k)
        ),
        Maybe.or(
          &2,
          Ver,
          Tables.Table.get(Ver, St.versions(s), k),
          Tables.Table.get(Ver, St.versions(a), k)
        ),
        Tables.Table.get(
          Ver,
          St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          k
        ),
        or_idem(Tables.Table.get(Ver, St.versions(s), k), Tables.Table.get(Ver, St.versions(a), k)),
        Equal.sym(
          Maybe<&2, Ver>,
          Tables.Table.get(
            Ver,
            St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
            k
          ),
          Maybe.or(
            &2,
            Ver,
            Tables.Table.get(Ver, St.versions(s), k),
            Tables.Table.get(Ver, St.versions(a), k)
          ),
          after_v(s, a, r1, k)
        )
      )
    )
  )

# s takes in a twice: a branch is as after once
law idem_b:
  for s: St
  for a: St
  for r1: String
  for r2: String
  for c: String
  {
    Tables.Table.get(
      Br,
      St.branches(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      c
    )
      == Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        c
      ): Maybe<&2, Br>
  }

def idem_b(s, a, r1, r2, c):
  +s = s
  +a = a
  +r1 = r1
  +c = c
  Equal.trans(
    Maybe<&2, Br>,
    Tables.Table.get(
      Br,
      St.branches(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      c
    ),
    Orders.Order.join(
      ~Br,
      ~Br.stamp.cmp,
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        c
      ),
      Tables.Table.get(Br, St.branches(a), c)
    ),
    Tables.Table.get(
      Br,
      St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
      c
    ),
    after_b(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), a, r2, c),
    Equal.trans(
      Maybe<&2, Br>,
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Tables.Table.get(
          Br,
          St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          c
        ),
        Tables.Table.get(Br, St.branches(a), c)
      ),
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Tables.Table.get(Br, St.branches(a), c)
      ),
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        c
      ),
      Equal.cong(
        Maybe<&2, Br>,
        Maybe<&2, Br>,
        z => Orders.Order.join(~Br, ~Br.stamp.cmp, z, Tables.Table.get(Br, St.branches(a), c)),
        Tables.Table.get(
          Br,
          St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          c
        ),
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        after_b(s, a, r1, c)
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Tables.Table.get(
          Br,
          St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          c
        ),
        Orders.Order.join_idem(
          ~Br,
          ~Br.stamp.cmp,
          y => stamp_refl(y),
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Equal.sym(
          Maybe<&2, Br>,
          Tables.Table.get(
            Br,
            St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
            c
          ),
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          after_b(s, a, r1, c)
        )
      )
    )
  )

# s takes in a twice: a mark is as after once
law idem_m:
  for s: St
  for a: St
  for r1: String
  for r2: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              a
            )
          )
        )
      ),
      qb,
      qm
    )
      == MarkAt.find(
        St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
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
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
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
      ~Ver.rev,
      MarkAt.find(
        St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        qb,
        qm
      ),
      MarkAt.find(St.marks(a), qb, qm)
    ),
    MarkAt.find(
      St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
      qb,
      qm
    ),
    after_m(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), a, r2, qb, qm),
    Equal.trans(
      Maybe<&2, String>,
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        MarkAt.find(
          St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          qb,
          qm
        ),
        MarkAt.find(St.marks(a), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        MarkAt.find(St.marks(a), qb, qm)
      ),
      MarkAt.find(
        St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        qb,
        qm
      ),
      Equal.cong(
        Maybe<&2, String>,
        Maybe<&2, String>,
        z => Orders.Order.join(~String, ~Ver.rev, z, MarkAt.find(St.marks(a), qb, qm)),
        MarkAt.find(
          St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        after_m(s, a, r1, qb, qm)
      ),
      Equal.trans(
        Maybe<&2, String>,
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(s), qb, qm),
            MarkAt.find(St.marks(a), qb, qm)
          ),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        MarkAt.find(
          St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          qb,
          qm
        ),
        Orders.Order.join_idem(
          ~String,
          ~Ver.rev,
          y => rev_refl(y),
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        Equal.sym(
          Maybe<&2, String>,
          MarkAt.find(
            St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
            qb,
            qm
          ),
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(s), qb, qm),
            MarkAt.find(St.marks(a), qb, qm)
          ),
          after_m(s, a, r1, qb, qm)
        )
      )
    )
  )

# s takes in a twice: the content is as after once
law idem_core:
  for s: St
  for a: St
  for r1: String
  for r2: String
  Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(
        Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(False{}, Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), a)
      )
    ),
    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))
  )

def idem_core(s, a, r1, r2):
  +s = s
  +a = a
  +r1 = r1
  +r2 = r2
  +n => p => content_eq(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(
        Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(False{}, Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), a)
      )
    ),
    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
    n,
    p
  )(
    k => Equal.cong(
      Maybe<&2, Ver>,
      Maybe<&2, List<&2, U32>>,
      z => Blob.find.of(Ver.blobs.of(z), n),
      Tables.Table.get(
        Ver,
        St.versions(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                a
              )
            )
          )
        ),
        k
      ),
      Tables.Table.get(
        Ver,
        St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        k
      ),
      idem_v(s, a, r1, r2, k)
    )
  )(
    c => Equal.cong(
      Maybe<&2, Br>,
      Maybe<&2, String>,
      z => Br.head.of(z),
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                a
              )
            )
          )
        ),
        c
      ),
      Tables.Table.get(
        Br,
        St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
        c
      ),
      idem_b(s, a, r1, r2, c)
    )
  )(qb => qm => idem_m(s, a, r1, r2, qb, qm))

# a second sync with a, by whether it found a collision (c)
law idem_go:
  for c: Bool
  for s: St
  for a: St
  for r1: String
  for s1: St
  for r2: String
  {
    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))) == s1: St
  } -> Spec.Node.SameContent(Pair.fst(St, Spec.Answer, Node.applied(s1, r2, Sync.go(c, s1, a))), s1)

def idem_go(c, s, a, r1, s1, r2):
  match c:
    case True{}:
      e =>
        +s1 = s1
        +r2 = r2
        n => p => same_content_out(
          s1,
          r2,
          St.clashes(s1),
          [],
          Sync.answer(Spec.Sync.Refused{"version ID collision"}),
          n,
          p
        )
    case False{}:
      e =>
        +s = s
        +a = a
        +r1 = r1
        +r2 = r2
        %e: Spec.Node.SameContent(
          Pair.fst(St, Spec.Answer, Node.applied(_, r2, Sync.go(False{}, _, a))),
          _
        )
        idem_core(s, a, r1, r2)

# a second sync with a, by whether its request was seen (found)
law idem_ask:
  for found: Maybe<&2, Seen>
  for s: St
  for a: St
  for r1: String
  for s1: St
  for r2: String
  for w2: String
  for z2: String
  for s2: St
  for a2: Spec.Answer
  {
    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))) == s1: St
  } -> {
    Node.asked(found, s1, r2, w2, z2, Spec.Ask.Sync{a, None{}}) == (s2, a2): St & Spec.Answer
  } -> Spec.Node.SameContent(s2, s1)

def idem_ask(found, s, a, r1, s1, r2, w2, z2, s2, a2):
  match found:
    case Some{Seen{b, q}}:
      e => h =>
        +s1 = s1
        %Equal.cong(
          St & Spec.Answer,
          St,
          x => Pair.fst(St, Spec.Answer, x),
          (s1, b),
          (s2, a2),
          h
        ): Spec.Node.SameContent(_, s1)
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
        )(h): Spec.Node.SameContent(_, s1)
        idem_go(
          Sync.collides(Tables.Table.keys(Ver, St.versions(a)), St.versions(a), St.versions(s1)),
          s,
          a,
          r1,
          s1,
          r2
        )(e)

# the stamps of three branches chain
law stamp_chain:
  for x: Br
  for y: Br
  for z: Br
  {Cmps.Cmp.chain(Br.stamp.cmp(x, y), Br.stamp.cmp(y, z), Br.stamp.cmp(x, z)) == True{}: Bool}

def stamp_chain(x, y, z):
  match x y z:
    case Br{+h1, o1, +e1, +c1} Br{+h2, o2, +e2, +c2} Br{+h3, o3, +e3, +c3}:
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
  {Cmps.Cmp.chain(Ver.rev(a, b), Ver.rev(b, c), Ver.rev(a, c)) == True{}: Bool}

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
  for vs: Maybe<&2, Ver>
  for va: Maybe<&2, Ver>
  for vb: Maybe<&2, Ver>
  for n: String
  Compat(
    vb,
    Maybe.or(&2, Ver, vs, va)
  ) -> {
    Blob.find.of(
      Ver.blobs.of(Maybe.or(&2, Ver, Maybe.or(&2, Ver, vs, va), vb)),
      n
    )
      == Blob.find.of(
        Ver.blobs.of(Maybe.or(&2, Ver, Maybe.or(&2, Ver, vs, vb), va)),
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
  for s: St
  for a: St
  for b: St
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for n: String
  for k: String
  {
    Sync.collides(
      Tables.Table.keys(Ver, St.versions(b)),
      St.versions(b),
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))))
    )
      == False{}: Bool
  } -> {
    Blob.find.of(
      Ver.blobs.of(
        Tables.Table.get(
          Ver,
          St.versions(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
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
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                  r2,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
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
        Ver.blobs.of(
          Maybe.or(
            &2,
            Ver,
            Maybe.or(
              &2,
              Ver,
              Tables.Table.get(Ver, St.versions(s), k),
              Tables.Table.get(Ver, St.versions(a), k)
            ),
            Tables.Table.get(Ver, St.versions(b), k)
          )
        ),
        n
      ),
      Blob.find.of(
        Ver.blobs.of(
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
        Maybe<&2, Ver>,
        Maybe<&2, List<&2, U32>>,
        z => Blob.find.of(Ver.blobs.of(z), n),
        Tables.Table.get(
          Ver,
          St.versions(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                  b
                )
              )
            )
          ),
          k
        ),
        Maybe.or(
          &2,
          Ver,
          Maybe.or(
            &2,
            Ver,
            Tables.Table.get(Ver, St.versions(s), k),
            Tables.Table.get(Ver, St.versions(a), k)
          ),
          Tables.Table.get(Ver, St.versions(b), k)
        ),
        Equal.trans(
          Maybe<&2, Ver>,
          Tables.Table.get(
            Ver,
            St.versions(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                  r2,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                    b
                  )
                )
              )
            ),
            k
          ),
          Maybe.or(
            &2,
            Ver,
            Tables.Table.get(
              Ver,
              St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
              k
            ),
            Tables.Table.get(Ver, St.versions(b), k)
          ),
          Maybe.or(
            &2,
            Ver,
            Maybe.or(
              &2,
              Ver,
              Tables.Table.get(Ver, St.versions(s), k),
              Tables.Table.get(Ver, St.versions(a), k)
            ),
            Tables.Table.get(Ver, St.versions(b), k)
          ),
          after_v(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), b, r2, k),
          Equal.cong(
            Maybe<&2, Ver>,
            Maybe<&2, Ver>,
            z => Maybe.or(&2, Ver, z, Tables.Table.get(Ver, St.versions(b), k)),
            Tables.Table.get(
              Ver,
              St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
              k
            ),
            Maybe.or(
              &2,
              Ver,
              Tables.Table.get(Ver, St.versions(s), k),
              Tables.Table.get(Ver, St.versions(a), k)
            ),
            after_v(s, a, r1, k)
          )
        )
      ),
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Blob.find.of(
          Ver.blobs.of(
            Maybe.or(
              &2,
              Ver,
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(s), k),
                Tables.Table.get(Ver, St.versions(a), k)
              ),
              Tables.Table.get(Ver, St.versions(b), k)
            )
          ),
          n
        ),
        Blob.find.of(
          Ver.blobs.of(
            Maybe.or(
              &2,
              Ver,
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(s), k),
                Tables.Table.get(Ver, St.versions(b), k)
              ),
              Tables.Table.get(Ver, St.versions(a), k)
            )
          ),
          n
        ),
        Blob.find.of(
          Ver.blobs.of(
            Tables.Table.get(
              Ver,
              St.versions(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
          Tables.Table.get(Ver, St.versions(s), k),
          Tables.Table.get(Ver, St.versions(a), k),
          Tables.Table.get(Ver, St.versions(b), k),
          n
        )((
            %after_v(s, a, r1, k): Compat(Tables.Table.get(Ver, St.versions(b), k), _)
            compat_of(St.versions(b), St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))), k)(hc))),
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Blob.find.of(
            Ver.blobs.of(
              Tables.Table.get(
                Ver,
                St.versions(
                  Pair.fst(
                    St,
                    Spec.Answer,
                    Node.applied(
                      Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                      r4,
                      Sync.go(
                        False{},
                        Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
            Ver.blobs.of(
              Maybe.or(
                &2,
                Ver,
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(s), k),
                  Tables.Table.get(Ver, St.versions(b), k)
                ),
                Tables.Table.get(Ver, St.versions(a), k)
              )
            ),
            n
          ),
          Equal.cong(
            Maybe<&2, Ver>,
            Maybe<&2, List<&2, U32>>,
            z => Blob.find.of(Ver.blobs.of(z), n),
            Tables.Table.get(
              Ver,
              St.versions(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                      a
                    )
                  )
                )
              ),
              k
            ),
            Maybe.or(
              &2,
              Ver,
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(Ver, St.versions(s), k),
                Tables.Table.get(Ver, St.versions(b), k)
              ),
              Tables.Table.get(Ver, St.versions(a), k)
            ),
            Equal.trans(
              Maybe<&2, Ver>,
              Tables.Table.get(
                Ver,
                St.versions(
                  Pair.fst(
                    St,
                    Spec.Answer,
                    Node.applied(
                      Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                      r4,
                      Sync.go(
                        False{},
                        Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                        a
                      )
                    )
                  )
                ),
                k
              ),
              Maybe.or(
                &2,
                Ver,
                Tables.Table.get(
                  Ver,
                  St.versions(
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))
                  ),
                  k
                ),
                Tables.Table.get(Ver, St.versions(a), k)
              ),
              Maybe.or(
                &2,
                Ver,
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(s), k),
                  Tables.Table.get(Ver, St.versions(b), k)
                ),
                Tables.Table.get(Ver, St.versions(a), k)
              ),
              after_v(
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                a,
                r4,
                k
              ),
              Equal.cong(
                Maybe<&2, Ver>,
                Maybe<&2, Ver>,
                z => Maybe.or(&2, Ver, z, Tables.Table.get(Ver, St.versions(a), k)),
                Tables.Table.get(
                  Ver,
                  St.versions(
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))
                  ),
                  k
                ),
                Maybe.or(
                  &2,
                  Ver,
                  Tables.Table.get(Ver, St.versions(s), k),
                  Tables.Table.get(Ver, St.versions(b), k)
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
  for s: St
  for a: St
  for b: St
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for c: String
  {
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      )
    )
      == Br.head.of(
        Tables.Table.get(
          Br,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      )
    ),
    Br.head.of(
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Tables.Table.get(Br, St.branches(b), c)
      )
    ),
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                a
              )
            )
          )
        ),
        c
      )
    ),
    Equal.cong(
      Maybe<&2, Br>,
      Maybe<&2, String>,
      z => Br.head.of(z),
      Tables.Table.get(
        Br,
        St.branches(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          )
        ),
        c
      ),
      Orders.Order.join(
        ~Br,
        ~Br.stamp.cmp,
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(Br, St.branches(s), c),
          Tables.Table.get(Br, St.branches(a), c)
        ),
        Tables.Table.get(Br, St.branches(b), c)
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(
          Br,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                r2,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                  b
                )
              )
            )
          ),
          c
        ),
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Tables.Table.get(
            Br,
            St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
            c
          ),
          Tables.Table.get(Br, St.branches(b), c)
        ),
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          Tables.Table.get(Br, St.branches(b), c)
        ),
        after_b(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), b, r2, c),
        Equal.cong(
          Maybe<&2, Br>,
          Maybe<&2, Br>,
          z => Orders.Order.join(~Br, ~Br.stamp.cmp, z, Tables.Table.get(Br, St.branches(b), c)),
          Tables.Table.get(
            Br,
            St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
            c
          ),
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          after_b(s, a, r1, c)
        )
      )
    ),
    Equal.trans(
      Maybe<&2, String>,
      Br.head.of(
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          Tables.Table.get(Br, St.branches(b), c)
        )
      ),
      Br.head.of(
        Orders.Order.join(
          ~Br,
          ~Br.stamp.cmp,
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Tables.Table.get(Br, St.branches(s), c),
            Tables.Table.get(Br, St.branches(b), c)
          ),
          Tables.Table.get(Br, St.branches(a), c)
        )
      ),
      Br.head.of(
        Tables.Table.get(
          Br,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  a
                )
              )
            )
          ),
          c
        )
      ),
      (
        %Equal.sym(Maybe<&2, String>, Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(a), c)), Tables.Table.get(Br, St.branches(b), c))), Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(a), c)), Tables.Table.get(Br, St.branches(b), c))), head_of_map(Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(a), c)), Tables.Table.get(Br, St.branches(b), c)))): {_ == Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(b), c)), Tables.Table.get(Br, St.branches(a), c))): Maybe<&2, String>}
        %Equal.sym(Maybe<&2, String>, Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(b), c)), Tables.Table.get(Br, St.branches(a), c))), Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(b), c)), Tables.Table.get(Br, St.branches(a), c))), head_of_map(Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(b), c)), Tables.Table.get(Br, St.branches(a), c)))): {Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(a), c)), Tables.Table.get(Br, St.branches(b), c))) == _: Maybe<&2, String>}
        Orders.Order.join_comm(~Br, ~String, ~Br.stamp.cmp, ~Br.head, x => y => stamp_swap(x, y), x => y => stamp_eq_head(x, y), x => y => z => stamp_chain(x, y, z), Tables.Table.get(Br, St.branches(s), c), Tables.Table.get(Br, St.branches(a), c), Tables.Table.get(Br, St.branches(b), c))),
      Equal.sym(
        Maybe<&2, String>,
        Br.head.of(
          Tables.Table.get(
            Br,
            St.branches(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                    a
                  )
                )
              )
            ),
            c
          )
        ),
        Br.head.of(
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(s), c),
              Tables.Table.get(Br, St.branches(b), c)
            ),
            Tables.Table.get(Br, St.branches(a), c)
          )
        ),
        Equal.cong(
          Maybe<&2, Br>,
          Maybe<&2, String>,
          z => Br.head.of(z),
          Tables.Table.get(
            Br,
            St.branches(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                    a
                  )
                )
              )
            ),
            c
          ),
          Orders.Order.join(
            ~Br,
            ~Br.stamp.cmp,
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(Br, St.branches(s), c),
              Tables.Table.get(Br, St.branches(b), c)
            ),
            Tables.Table.get(Br, St.branches(a), c)
          ),
          Equal.trans(
            Maybe<&2, Br>,
            Tables.Table.get(
              Br,
              St.branches(
                Pair.fst(
                  St,
                  Spec.Answer,
                  Node.applied(
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                    r4,
                    Sync.go(
                      False{},
                      Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                      a
                    )
                  )
                )
              ),
              c
            ),
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Tables.Table.get(
                Br,
                St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))),
                c
              ),
              Tables.Table.get(Br, St.branches(a), c)
            ),
            Orders.Order.join(
              ~Br,
              ~Br.stamp.cmp,
              Orders.Order.join(
                ~Br,
                ~Br.stamp.cmp,
                Tables.Table.get(Br, St.branches(s), c),
                Tables.Table.get(Br, St.branches(b), c)
              ),
              Tables.Table.get(Br, St.branches(a), c)
            ),
            after_b(
              Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
              a,
              r4,
              c
            ),
            Equal.cong(
              Maybe<&2, Br>,
              Maybe<&2, Br>,
              z => Orders.Order.join(
                ~Br,
                ~Br.stamp.cmp,
                z,
                Tables.Table.get(Br, St.branches(a), c)
              ),
              Tables.Table.get(
                Br,
                St.branches(Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))),
                c
              ),
              Orders.Order.join(
                ~Br,
                ~Br.stamp.cmp,
                Tables.Table.get(Br, St.branches(s), c),
                Tables.Table.get(Br, St.branches(b), c)
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
  for s: St
  for a: St
  for b: St
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  for qb: String
  for qm: String
  {
    MarkAt.find(
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              b
            )
          )
        )
      ),
      qb,
      qm
    )
      == MarkAt.find(
        St.marks(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            r2,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
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
      ~Ver.rev,
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        MarkAt.find(St.marks(s), qb, qm),
        MarkAt.find(St.marks(a), qb, qm)
      ),
      MarkAt.find(St.marks(b), qb, qm)
    ),
    MarkAt.find(
      St.marks(
        Pair.fst(
          St,
          Spec.Answer,
          Node.applied(
            Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
            r4,
            Sync.go(
              False{},
              Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
        St.marks(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
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
        ~Ver.rev,
        MarkAt.find(
          St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          qb,
          qm
        ),
        MarkAt.find(St.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        MarkAt.find(St.marks(b), qb, qm)
      ),
      after_m(
        Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
        b,
        r2,
        qb,
        qm
      ),
      Equal.cong(
        Maybe<&2, String>,
        Maybe<&2, String>,
        z => Orders.Order.join(~String, ~Ver.rev, z, MarkAt.find(St.marks(b), qb, qm)),
        MarkAt.find(
          St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a)))),
          qb,
          qm
        ),
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        after_m(s, a, r1, qb, qm)
      )
    ),
    Equal.trans(
      Maybe<&2, String>,
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        MarkAt.find(St.marks(b), qb, qm)
      ),
      Orders.Order.join(
        ~String,
        ~Ver.rev,
        Orders.Order.join(
          ~String,
          ~Ver.rev,
          MarkAt.find(St.marks(s), qb, qm),
          MarkAt.find(St.marks(b), qb, qm)
        ),
        MarkAt.find(St.marks(a), qb, qm)
      ),
      MarkAt.find(
        St.marks(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
              r4,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                a
              )
            )
          )
        ),
        qb,
        qm
      ),
      (
        %map_id(Orders.Order.join(~String, ~Ver.rev, Orders.Order.join(~String, ~Ver.rev, MarkAt.find(St.marks(s), qb, qm), MarkAt.find(St.marks(a), qb, qm)), MarkAt.find(St.marks(b), qb, qm))): {_ == Orders.Order.join(~String, ~Ver.rev, Orders.Order.join(~String, ~Ver.rev, MarkAt.find(St.marks(s), qb, qm), MarkAt.find(St.marks(b), qb, qm)), MarkAt.find(St.marks(a), qb, qm)): Maybe<&2, String>}
        %map_id(Orders.Order.join(~String, ~Ver.rev, Orders.Order.join(~String, ~Ver.rev, MarkAt.find(St.marks(s), qb, qm), MarkAt.find(St.marks(b), qb, qm)), MarkAt.find(St.marks(a), qb, qm))): {Maybe.map(&2, String, String, y => y, Orders.Order.join(~String, ~Ver.rev, Orders.Order.join(~String, ~Ver.rev, MarkAt.find(St.marks(s), qb, qm), MarkAt.find(St.marks(a), qb, qm)), MarkAt.find(St.marks(b), qb, qm))) == _: Maybe<&2, String>}
        Orders.Order.join_comm(~String, ~String, ~Ver.rev, ~(y => y), x => y => rev_swap(x, y), x => y => rev_same(x, y), x => y => z => rev_chain(x, y, z), MarkAt.find(St.marks(s), qb, qm), MarkAt.find(St.marks(a), qb, qm), MarkAt.find(St.marks(b), qb, qm))),
      Equal.sym(
        Maybe<&2, String>,
        MarkAt.find(
          St.marks(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                r4,
                Sync.go(
                  False{},
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
          ~Ver.rev,
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            MarkAt.find(St.marks(s), qb, qm),
            MarkAt.find(St.marks(b), qb, qm)
          ),
          MarkAt.find(St.marks(a), qb, qm)
        ),
        Equal.trans(
          Maybe<&2, String>,
          MarkAt.find(
            St.marks(
              Pair.fst(
                St,
                Spec.Answer,
                Node.applied(
                  Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
                  r4,
                  Sync.go(
                    False{},
                    Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
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
            ~Ver.rev,
            MarkAt.find(
              St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))),
              qb,
              qm
            ),
            MarkAt.find(St.marks(a), qb, qm)
          ),
          Orders.Order.join(
            ~String,
            ~Ver.rev,
            Orders.Order.join(
              ~String,
              ~Ver.rev,
              MarkAt.find(St.marks(s), qb, qm),
              MarkAt.find(St.marks(b), qb, qm)
            ),
            MarkAt.find(St.marks(a), qb, qm)
          ),
          after_m(
            Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
            a,
            r4,
            qb,
            qm
          ),
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, String>,
            z => Orders.Order.join(~String, ~Ver.rev, z, MarkAt.find(St.marks(a), qb, qm)),
            MarkAt.find(
              St.marks(Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b)))),
              qb,
              qm
            ),
            Orders.Order.join(
              ~String,
              ~Ver.rev,
              MarkAt.find(St.marks(s), qb, qm),
              MarkAt.find(St.marks(b), qb, qm)
            ),
            after_m(s, b, r3, qb, qm)
          )
        )
      )
    )
  )

# s takes in a then b, or b then a: both hold the same content
law comm_core:
  for s: St
  for a: St
  for b: St
  for r1: String
  for r2: String
  for r3: String
  for r4: String
  {
    Sync.collides(
      Tables.Table.keys(Ver, St.versions(b)),
      St.versions(b),
      St.versions(Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))))
    )
      == False{}: Bool
  } -> Spec.Node.SameContent(
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(
        Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
        r2,
        Sync.go(False{}, Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), b)
      )
    ),
    Pair.fst(
      St,
      Spec.Answer,
      Node.applied(
        Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
        r4,
        Sync.go(False{}, Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))), a)
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
        St,
        Spec.Answer,
        Node.applied(
          Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
          r2,
          Sync.go(
            False{},
            Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
            b
          )
        )
      ),
      Pair.fst(
        St,
        Spec.Answer,
        Node.applied(
          Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
          r4,
          Sync.go(
            False{},
            Pair.fst(St, Spec.Answer, Node.applied(s, r3, Sync.go(False{}, s, b))),
            a
          )
        )
      ),
      n,
      p
    )(
      k => comm_v(s, a, b, r1, r2, r3, r4, n, k)(hc)
    )(c => comm_h(s, a, b, r1, r2, r3, r4, c))(qb => qm => comm_m(s, a, b, r1, r2, r3, r4, qb, qm))
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a walk step at a version that m holds
law walk_at:
  for m: Maybe<&2, Ver>
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for vs: Tables.Table<Ver>
  for b: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w0: String
  for t0: String
  {
    m == Some{Ver{b, ps, w0, t0}}: Maybe<&2, Ver>
  } -> {
    List.append(
      &2,
      Tables.Row<Ver>,
      Walked.reached(History.at(k, r, done, m)),
      History.walk(
        g,
        Walked.next(History.at(k, r, done, m)),
        Walked.done(History.at(k, r, done, m)),
        vs
      )
    )
      == Tables.Row{k, Ver{b, ps, w0, t0}}
      <> History.walk(g, List.append(&2, String, r, ps), k <> done, vs): List<&2, Tables.Row<Ver>>
  }

def walk_at(m, g, k, r, done, vs, b, ps, w0, t0):
  e =>
    %Equal.sym(
      Maybe<&2, Ver>,
      m,
      Some{Ver{b, ps, w0, t0}},
      e
    ): {
      List.append(
        &2,
        Tables.Row<Ver>,
        Walked.reached(History.at(k, r, done, _)),
        History.walk(
          g,
          Walked.next(History.at(k, r, done, _)),
          Walked.done(History.at(k, r, done, _)),
          vs
        )
      )
        == Tables.Row{k, Ver{b, ps, w0, t0}}
        <> History.walk(g, List.append(&2, String, r, ps), k <> done, vs): List<&2, Tables.Row<Ver>>
    }
    {==}

# a walk step at a version k not yet walked
law walk_one:
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for vs: Tables.Table<Ver>
  for b: Tables.Table<List<&2, U32>>
  for ps: List<&2, String>
  for w0: String
  for t0: String
  {
    Strings.has(done, k) == False{}: Bool
  } -> {
    Tables.Table.get(Ver, vs, k) == Some{Ver{b, ps, w0, t0}}: Maybe<&2, Ver>
  } -> {
    History.walk(
      1n+g,
      k <> r,
      done,
      vs
    )
      == Tables.Row{k, Ver{b, ps, w0, t0}}
      <> History.walk(g, List.append(&2, String, r, ps), k <> done, vs): List<&2, Tables.Row<Ver>>
  }

def walk_one(g, k, r, done, vs, b, ps, w0, t0):
  hd => hg =>
    +k = k
    +r = r
    +done = done
    +vs = vs
    %Equal.sym(
      Bool,
      Strings.has(done, k),
      False{},
      hd
    ): {
      List.append(
        &2,
        Tables.Row<Ver>,
        Walked.reached(History.next(k, r, done, vs, _)),
        History.walk(
          g,
          Walked.next(History.next(k, r, done, vs, _)),
          Walked.done(History.next(k, r, done, vs, _)),
          vs
        )
      )
        == Tables.Row{k, Ver{b, ps, w0, t0}}
        <> History.walk(g, List.append(&2, String, r, ps), k <> done, vs): List<&2, Tables.Row<Ver>>
    }
    walk_at(Tables.Table.get(Ver, vs, k), g, k, r, done, vs, b, ps, w0, t0)(hg)

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
  for vs: Tables.Table<Ver>
  {
    Tables.Table.get(Ver, vs, a) == Some{Ver{xb, [bb], xw, xt}}: Maybe<&2, Ver>
  } -> {
    String.eq(a, bb) == False{}: Bool
  } -> {
    Tables.Table.get(Ver, vs, bb) == Some{Ver{yb, yp, yw, yt}}: Maybe<&2, Ver>
  } -> {
    History.walk(
      1n+1n+f,
      [a],
      [],
      vs
    )
      == Tables.Row{a, Ver{xb, [bb], xw, xt}}
      <> (
        Tables.Row{bb, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs)
      ): List<&2, Tables.Row<Ver>>
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
      List<&2, Tables.Row<Ver>>,
      History.walk(1n+1n+f, [a], [], vs),
      Tables.Row{a, Ver{xb, [bb], xw, xt}} <> History.walk(1n+f, [bb], [a], vs),
      Tables.Row{
        a,
        Ver{xb, [bb], xw, xt}
      }
        <> (Tables.Row{bb, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs)),
      walk_one(1n+f, a, [], [], vs, xb, [bb], xw, xt)({==})(ha),
      Equal.cong(
        List<&2, Tables.Row<Ver>>,
        List<&2, Tables.Row<Ver>>,
        z => Tables.Row{a, Ver{xb, [bb], xw, xt}} <> z,
        History.walk(1n+f, [bb], [a], vs),
        Tables.Row{bb, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [bb, a], vs),
        walk_one(f, bb, [], [a], vs, yb, yp, yw, yt)((
            %Equal.sym(Bool, String.eq(a, bb), False{}, hab): {List.any.if(u => Strings.has([], bb), _) == False{}: Bool}
            {==}))(hb)
      )
    )

# the first version of a, bb, ... that ids holds is bb, when it does not hold a
law first_two:
  for a: String
  for bb: String
  for x: Ver
  for y: Ver
  for rest: List<&2, Tables.Row<Ver>>
  for ids: List<&2, String>
  {
    Strings.has(ids, a) == False{}: Bool
  } -> {
    Strings.has(ids, bb) == True{}: Bool
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
      Strings.has(ids, a),
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
      Strings.has(ids, bb),
      True{},
      hb
    ): {List.find.if(String, bb, u => Vers.first_in(rest, ids), _) == Some{bb}: Maybe<&2, String>}
    {==}

# the IDs of a, bb, ... hold bb
law ids_second:
  for a: String
  for bb: String
  for x: Ver
  for y: Ver
  for rest: List<&2, Tables.Row<Ver>>
  {
    String.eq(a, bb) == False{}: Bool
  } -> {Strings.has(Vers.ids(Tables.Row{a, x} <> (Tables.Row{bb, y} <> rest)), bb) == True{}: Bool}

def ids_second(a, bb, x, y, rest):
  e =>
    +a = a
    +bb = bb
    %Equal.sym(
      Bool,
      String.eq(a, bb),
      False{},
      e
    ): {List.any.if(u => Strings.has(bb <> Vers.ids(rest), bb), _) == True{}: Bool}
    %Equal.sym(
      Bool,
      String.eq(bb, bb),
      True{},
      Strings.String.eq_refl(bb)
    ): {List.any.if(u => Strings.has(Vers.ids(rest), bb), _) == True{}: Bool}
    {==}

# a version found after adding one with another ID is the one found before
law add1_other:
  for vs: Tables.Table<Ver>
  for x: String
  for xv: Ver
  for k: String
  {
    String.eq(x, k) == False{}: Bool
  } -> {
    Tables.Table.get(
      Ver,
      Ver.add([Tables.Row{x, xv}], vs),
      k
    )
      == Tables.Table.get(Ver, vs, k): Maybe<&2, Ver>
  }

def add1_other(vs, x, xv, k):
  e =>
    +vs = vs
    +x = x
    +xv = xv
    +k = k
    Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, Ver.add([Tables.Row{x, xv}], vs), k),
      Maybe.or(
        &2,
        Ver,
        Tables.Table.get(Ver, vs, k),
        Tables.Table.find_row(Ver, [Tables.Row{x, xv}], k)
      ),
      Tables.Table.get(Ver, vs, k),
      add_find([Tables.Row{x, xv}], vs, k),
      (
        %Equal.sym(Bool, String.eq(x, k), False{}, e): {Maybe.or(&2, Ver, Tables.Table.get(Ver, vs, k), Bools.Bool.when(Maybe<&2, Ver>, _, u => Some{xv}, u => Tables.Table.find_row(Ver, [], k))) == Tables.Table.get(Ver, vs, k): Maybe<&2, Ver>}
        or_none(Tables.Table.get(Ver, vs, k)))
    )

# named_at at the first key j, by whether j is k (hit)
law named_at.at:
  for hit: Bool
  for j: String
  for r: List<&2, String>
  for vs: Tables.Table<Ver>
  for x: String
  for k: String
  (
    {
      Strings.has(r, k) == True{}: Bool
    } -> {Strings.has(History.parents(Tables.Table.get(Ver, vs, k)), x) == False{}: Bool}
  ) -> {
    String.eq(j, k) == hit: Bool
  } -> {
    Strings.has(History.parents(Tables.Table.get(Ver, vs, j)), x) == False{}: Bool
  } -> {
    List.any.if(u => Strings.has(r, k), hit) == True{}: Bool
  } -> {Strings.has(History.parents(Tables.Table.get(Ver, vs, k)), x) == False{}: Bool}

def named_at.at(hit, j, r, vs, x, k):
  match hit:
    case True{}:
      ih => e => h0 => hk =>
        %Strings.String.eq_sound(
          j,
          k
        )(e): {Strings.has(History.parents(Tables.Table.get(Ver, vs, _)), x) == False{}: Bool}
        h0
    case False{}:
      ih => e => h0 => hk => ih(hk)

# a version that no version names as a parent is not a parent of a version
# among ks
law named_at:
  for ks: List<&2, String>
  for vs: Tables.Table<Ver>
  for x: String
  for k: String
  {
    Ver.named(ks, vs, x) == False{}: Bool
  } -> {
    Strings.has(ks, k) == True{}: Bool
  } -> {Strings.has(History.parents(Tables.Table.get(Ver, vs, k)), x) == False{}: Bool}

def named_at(ks, vs, x, k):
  match ks:
    case Nil{}:
      hn => hk => Empty.absurd(
        {Strings.has(History.parents(Tables.Table.get(Ver, vs, k)), x) == False{}: Bool},
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
              Strings.has(History.parents(Tables.Table.get(Ver, vs, j)), x),
              Ver.named(r, vs, x)
            )(hn)
          )
        )(
          {==}
        )(
          Bools.Bool.or_false_left(
            Strings.has(History.parents(Tables.Table.get(Ver, vs, j)), x),
            Ver.named(r, vs, x)
          )(hn)
        )

# walk_avoid at a version k that vs holds as m
law avoid_at:
  for mv: Maybe<&2, Ver>
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: Ver
  for v2s: Tables.Table<Ver>
  (
    @ks2: List<
      &2,
      String> -> @d2: List<
      &2,
      String> -> {
      Strings.has(ks2, x) == False{}: Bool
    } -> {
      Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool
    } -> {
      Strings.has(
        Vers.ids(History.walk(g, ks2, d2, Ver.add([Tables.Row{x, xv}], v2s))),
        x
      )
        == False{}: Bool
    }
  ) -> {
    Tables.Table.get(Ver, v2s, k) == mv: Maybe<&2, Ver>
  } -> {
    String.eq(k, x) == False{}: Bool
  } -> {
    Strings.has(r, x) == False{}: Bool
  } -> {
    Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool
  } -> {
    Strings.has(
      Vers.ids(
        List.append(
          &2,
          Tables.Row<Ver>,
          Walked.reached(History.at(k, r, done, mv)),
          History.walk(
            g,
            Walked.next(History.at(k, r, done, mv)),
            Walked.done(History.at(k, r, done, mv)),
            Ver.add([Tables.Row{x, xv}], v2s)
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
    case Some{Ver{b, +ps, a, t}}:
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
            u => Strings.has(
              Vers.ids(
                History.walk(
                  g,
                  List.append(&2, String, r, ps),
                  k <> done,
                  Ver.add([Tables.Row{x, xv}], v2s)
                )
              ),
              x
            ),
            _
          )
            == False{}: Bool
        }
        ih(List.append(&2, String, r, ps))(k <> done)(Strings.has_append_false(r, ps, x)(hr)((
              %e: {Strings.has(History.parents(_), x) == False{}: Bool}
              named_at(Tables.Table.keys(Ver, v2s), v2s, x, k)(hn)(Equal.trans(Bool, Strings.has(Tables.Table.keys(Ver, v2s), k), Maybe.is_some(&2, Ver, Tables.Table.get(Ver, v2s, k)), True{}, Tables.Table.keys_get(Ver, v2s, k), Equal.cong(Maybe<&2, Ver>, Bool, z => Maybe.is_some(&2, Ver, z), Tables.Table.get(Ver, v2s, k), Some{Ver{b, ps, a, t}}, e))))))(hn)

# walk_avoid at a version k, by whether the walk saw it (was)
law avoid_was:
  for was: Bool
  for g: Nat
  for k: String
  for r: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: Ver
  for v2s: Tables.Table<Ver>
  (
    @ks2: List<
      &2,
      String> -> @d2: List<
      &2,
      String> -> {
      Strings.has(ks2, x) == False{}: Bool
    } -> {
      Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool
    } -> {
      Strings.has(
        Vers.ids(History.walk(g, ks2, d2, Ver.add([Tables.Row{x, xv}], v2s))),
        x
      )
        == False{}: Bool
    }
  ) -> {
    Strings.has(k <> r, x) == False{}: Bool
  } -> {
    Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool
  } -> {
    Strings.has(
      Vers.ids(
        List.append(
          &2,
          Tables.Row<Ver>,
          Walked.reached(History.next(k, r, done, Ver.add([Tables.Row{x, xv}], v2s), was)),
          History.walk(
            g,
            Walked.next(History.next(k, r, done, Ver.add([Tables.Row{x, xv}], v2s), was)),
            Walked.done(History.next(k, r, done, Ver.add([Tables.Row{x, xv}], v2s), was)),
            Ver.add([Tables.Row{x, xv}], v2s)
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
            {Strings.has(r, x) == False{}: Bool},
            Strings.has_cons_false(k, r, x)(hk)
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
          Maybe<&2, Ver>,
          Tables.Table.get(Ver, Ver.add([Tables.Row{x, xv}], v2s), k),
          Tables.Table.get(Ver, v2s, k),
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
                {Strings.has(r, x) == False{}: Bool},
                Strings.has_cons_false(k, r, x)(hk)
              )
            )
          )
        ):
          {
            Strings.has(
              Vers.ids(
                List.append(
                  &2,
                  Tables.Row<Ver>,
                  Walked.reached(History.at(k, r, done, _)),
                  History.walk(
                    g,
                    Walked.next(History.at(k, r, done, _)),
                    Walked.done(History.at(k, r, done, _)),
                    Ver.add([Tables.Row{x, xv}], v2s)
                  )
                )
              ),
              x
            )
              == False{}: Bool
          }
        avoid_at(
          Tables.Table.get(Ver, v2s, k),
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
            {Strings.has(r, x) == False{}: Bool},
            Strings.has_cons_false(k, r, x)(hk)
          )
        )(
          Pair.snd(
            {String.eq(k, x) == False{}: Bool},
            {Strings.has(r, x) == False{}: Bool},
            Strings.has_cons_false(k, r, x)(hk)
          )
        )(hn)

# a walk from versions that are not x, after x was added with no version
# naming it as a parent, never reaches x
law walk_avoid:
  for f: Nat
  for ks: List<&2, String>
  for done: List<&2, String>
  for x: String
  for xv: Ver
  for v2s: Tables.Table<Ver>
  {
    Strings.has(ks, x) == False{}: Bool
  } -> {
    Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool
  } -> {
    Strings.has(
      Vers.ids(History.walk(f, ks, done, Ver.add([Tables.Row{x, xv}], v2s))),
      x
    )
      == False{}: Bool
  }

def walk_avoid.g1(
  +f: Nat,
  +ks: List<&2, String>,
  +done: List<&2, String>,
  +x: String,
  +xv: Ver,
  +v2s: Tables.Table<Ver>,
  x1: {Strings.has(ks, x) == False{}: Bool},
  x2: {Ver.named(Tables.Table.keys(Ver, v2s), v2s, x) == False{}: Bool}
) -> {
  Strings.has(
    Vers.ids(History.walk(f, ks, done, Ver.add([Tables.Row{x, xv}], v2s))),
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
            Strings.has(done, head),
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

# a plus one more is one more than a plus
law nat_add_succ:
  for a: Nat
  for b: Nat
  {Nat.add(a, 1n+b) == 1n+Nat.add(a, b): Nat}

def nat_add_succ(a, b):
  match a:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(q, 1n+b), 1n+Nat.add(q, b), nat_add_succ(q, b))

# there is always fuel for one step of a walk
def links_one(ks: List<&2, String>, +vs: Tables.Table<Ver>) -> &y:
  Nat -> {History.links(ks, vs) == 1n+y: Nat}:
  match ks:
    case Nil{}:
      (0n, {==})
    case Con{k, r}:
      (
        Nat.add(
          List.length(&2, String, History.parents(Tables.Table.get(Ver, vs, k))),
          History.links(r, vs)
        ),
        {==}
      )

# links_two, once the rest is found to have fuel for one step
def links_two.of(
  +l: Nat,
  r: List<&2, String>,
  vs: Tables.Table<Ver>,
  w: &y: Nat -> {History.links(r, vs) == 1n+y: Nat}
) -> &f:
  Nat -> {Nat.add(1n+l, History.links(r, vs)) == 1n+1n+f: Nat}:
  match w:
    case (+y, e):
      (Nat.add(l, y), (
          %Equal.sym(Nat, History.links(r, vs), 1n+y, e): {Nat.add(1n+l, _) == 1n+1n+Nat.add(l, y): Nat}
          Equal.cong(Nat, Nat, z => 1n+z, Nat.add(l, 1n+y), 1n+Nat.add(l, y), nat_add_succ(l, y))))

# a walk over some versions has fuel for two steps
def links_two(
  ks: List<&2, String>,
  +vs: Tables.Table<Ver>,
  k: String
) -> {Strings.has(ks, k) == True{}: Bool} -> &f:
  Nat -> {History.links(ks, vs) == 1n+1n+f: Nat}:
  match ks:
    case Nil{}:
      h => Empty.absurd(
        &f: Nat -> {History.links([], vs) == 1n+1n+f: Nat},
        Shared.Bool.false_ne_true(h)
      )
    case Con{j, +r}:
      h => links_two.of(
        List.length(&2, String, History.parents(Tables.Table.get(Ver, vs, j))),
        r,
        vs,
        links_one(r, vs)
      )

# equal bytes, or none, are the same
law same_refl:
  for m: Maybe<&2, List<&2, U32>>
  {Maybes.Maybe.same(~List<&2, U32>, ~Octets.Bytes.is_eq, m, m) == True{}: Bool}

def same_refl(m):
  match m:
    case None{}:
      {==}
    case Some{y}:
      Octets.Bytes.is_eq_refl(y)

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
      same_refl(Tables.Table.get(List<&2, U32>, b0, n1))
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
      same_refl(Tables.Table.get(List<&2, U32>, b0, n2))
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
          same_refl(Tables.Table.get(List<&2, U32>, b0, n))
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
          same_refl(Tables.Table.get(List<&2, U32>, b0, n))
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
      Strings.has(r, q) == True{}: Bool
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
    List.any.if(u => Strings.has(r, q), hit) == True{}: Bool
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
    Strings.has(ns, q) == True{}: Bool
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {
    Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>
  }
    & (
      {
        Ver.has(St.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
          }
            & {
              SetBranch.point(
                Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                s,
                r,
                w,
                z,
                c
              )
                == Out{
                  [],
                  Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
                  [Logged.head(c, v)],
                  SetBranch.answer(Spec.SetBranch.Created{v})
                }: Out
            }
        )
    )

def sb_core.g7(
  +self: String,
  +versions: Tables.Table<Ver>,
  +branches: Tables.Table<Br>,
  +marks: Tables.Table<Tables.Table<MarkAt>>,
  +groups: Tables.Table<Grp>,
  +clashes: Tables.Table<Clash>,
  +seen: Tables.Table<Seen>,
  +log: List<&2, Logged>,
  +t: St,
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
      Ver.taken(versions, r),
      List.length(&2, Logged, log)
    )
      == Spec.Outcome.NotSeen{}: Spec.Outcome
  },
  x1: {
    Node.asked(
      x2,
      St{self, versions, branches, marks, groups, clashes, seen, log},
      r,
      w,
      z,
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): Pair(St, Spec.Answer)
  }
) -> Pair(
  {
    Br.head.of(
      Tables.Table.get(
        Br,
        St.branches(St{self, versions, branches, marks, groups, clashes, seen, log}),
        b
      )
    )
      == Some{v}: Maybe<&2, String>
  },
  Pair(
    {
      Ver.has(
        St.versions(St{self, versions, branches, marks, groups, clashes, seen, log}),
        v
      )
        == True{}: Bool
    },
    Pair(
      {
        Tables.Table.get(
          Br,
          St.branches(St{self, versions, branches, marks, groups, clashes, seen, log}),
          c
        )
          == None{}: Maybe<&2, Br>
      },
      {
        SetBranch.point(
          Br.head.of(
            Tables.Table.get(
              Br,
              St.branches(St{self, versions, branches, marks, groups, clashes, seen, log}),
              b
            )
          ),
          St{self, versions, branches, marks, groups, clashes, seen, log},
          r,
          w,
          z,
          c
        )
          == Out{
            [],
            Tables.Table.set(
              Br,
              St.branches(St{self, versions, branches, marks, groups, clashes, seen, log}),
              c,
              Br{
                v,
                St.self(St{self, versions, branches, marks, groups, clashes, seen, log}),
                0n,
                0n
              }
            ),
            St.marks(St{self, versions, branches, marks, groups, clashes, seen, log}),
            St.groups(St{self, versions, branches, marks, groups, clashes, seen, log}),
            St.clashes(St{self, versions, branches, marks, groups, clashes, seen, log}),
            [Logged.head(c, v)],
            SetBranch.answer(Spec.SetBranch.Created{v})
          }: Out
      }
    )
  )
):
  match t:
    case St{self1, versions1, branches1, marks1, groups1, clashes1, seen1, log1}:
      match x2:
        case None{}:
          sb_point(
            Br.head.of(
              Tables.Table.get(
                Br,
                St.branches(St{self, versions, branches, marks, groups, clashes, seen, log}),
                b
              )
            ),
            St{self, versions, branches, marks, groups, clashes, seen, log},
            r,
            w,
            z,
            c,
            v
          )(
            view_ver(
              St{self, versions, branches, marks, groups, clashes, seen, log},
              r,
              SetBranch.point(
                Br.head.of(Tables.Table.get(Br, branches, b)),
                St{self, versions, branches, marks, groups, clashes, seen, log},
                r,
                w,
                z,
                c
              ),
              St{self1, versions1, branches1, marks1, groups1, clashes1, seen1, log1},
              Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
            )(x1)
          )
        case Some{value}:
          match value:
            case Seen{answer, at}:
              Empty.absurd(
                Pair(
                  {
                    Br.head.of(
                      Tables.Table.get(
                        Br,
                        St.branches(
                          St{self, versions, branches, marks, groups, clashes, seen, log}
                        ),
                        b
                      )
                    )
                      == Some{v}: Maybe<&2, String>
                  },
                  Pair(
                    {
                      Ver.has(
                        St.versions(
                          St{self, versions, branches, marks, groups, clashes, seen, log}
                        ),
                        v
                      )
                        == True{}: Bool
                    },
                    Pair(
                      {
                        Tables.Table.get(
                          Br,
                          St.branches(
                            St{self, versions, branches, marks, groups, clashes, seen, log}
                          ),
                          c
                        )
                          == None{}: Maybe<&2, Br>
                      },
                      {
                        SetBranch.point(
                          Br.head.of(
                            Tables.Table.get(
                              Br,
                              St.branches(
                                St{self, versions, branches, marks, groups, clashes, seen, log}
                              ),
                              b
                            )
                          ),
                          St{self, versions, branches, marks, groups, clashes, seen, log},
                          r,
                          w,
                          z,
                          c
                        )
                          == Out{
                            [],
                            Tables.Table.set(
                              Br,
                              St.branches(
                                St{self, versions, branches, marks, groups, clashes, seen, log}
                              ),
                              c,
                              Br{
                                v,
                                St.self(
                                  St{self, versions, branches, marks, groups, clashes, seen, log}
                                ),
                                0n,
                                0n
                              }
                            ),
                            St.marks(
                              St{self, versions, branches, marks, groups, clashes, seen, log}
                            ),
                            St.groups(
                              St{self, versions, branches, marks, groups, clashes, seen, log}
                            ),
                            St.clashes(
                              St{self, versions, branches, marks, groups, clashes, seen, log}
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
    case St{self, versions, branches, marks, groups, clashes, +seen, log}:
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>}

def sb_head(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>},
    (
      {
        Ver.has(St.versions(s), v) == True{}: Bool
      }
        & (
          {
            Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
          }
            & {
              SetBranch.point(
                Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                s,
                r,
                w,
                z,
                c
              )
                == Out{
                  [],
                  Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                  St.marks(s),
                  St.groups(s),
                  St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {Ver.has(St.versions(s), v) == True{}: Bool}

def sb_has(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {Ver.has(St.versions(s), v) == True{}: Bool},
    (
      {
        Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
      }
        & {
          SetBranch.point(
            Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
            s,
            r,
            w,
            z,
            c
          )
            == Out{
              [],
              Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
              St.marks(s),
              St.groups(s),
              St.clashes(s),
              [Logged.head(c, v)],
              SetBranch.answer(Spec.SetBranch.Created{v})
            }: Out
        }
    ),
    Pair.snd(
      {Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>},
      (
        {
          Ver.has(St.versions(s), v) == True{}: Bool
        }
          & (
            {
              Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
            }
              & {
                SetBranch.point(
                  Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                  s,
                  r,
                  w,
                  z,
                  c
                )
                  == Out{
                    [],
                    Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                    St.marks(s),
                    St.groups(s),
                    St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>}

def sb_none(s, t, r, w, z, b, c, v):
  hn => h => Pair.fst(
    {Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>},
    {
      SetBranch.point(
        Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
        s,
        r,
        w,
        z,
        c
      )
        == Out{
          [],
          Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
          St.marks(s),
          St.groups(s),
          St.clashes(s),
          [Logged.head(c, v)],
          SetBranch.answer(Spec.SetBranch.Created{v})
        }: Out
    },
    Pair.snd(
      {Ver.has(St.versions(s), v) == True{}: Bool},
      (
        {
          Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
        }
          & {
            SetBranch.point(
              Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
              s,
              r,
              w,
              z,
              c
            )
              == Out{
                [],
                Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                St.marks(s),
                St.groups(s),
                St.clashes(s),
                [Logged.head(c, v)],
                SetBranch.answer(Spec.SetBranch.Created{v})
              }: Out
          }
      ),
      Pair.snd(
        {Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>},
        (
          {
            Ver.has(St.versions(s), v) == True{}: Bool
          }
            & (
              {
                Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
              }
                & {
                  SetBranch.point(
                    Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                    s,
                    r,
                    w,
                    z,
                    c
                  )
                    == Out{
                      [],
                      Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                      St.marks(s),
                      St.groups(s),
                      St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {
    SetBranch.point(
      Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
      s,
      r,
      w,
      z,
      c
    )
      == Out{
        [],
        Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(c, v)],
        SetBranch.answer(Spec.SetBranch.Created{v})
      }: Out
  }

def sb_out(s, t, r, w, z, b, c, v):
  hn => h => Pair.snd(
    {Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>},
    {
      SetBranch.point(
        Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
        s,
        r,
        w,
        z,
        c
      )
        == Out{
          [],
          Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
          St.marks(s),
          St.groups(s),
          St.clashes(s),
          [Logged.head(c, v)],
          SetBranch.answer(Spec.SetBranch.Created{v})
        }: Out
    },
    Pair.snd(
      {Ver.has(St.versions(s), v) == True{}: Bool},
      (
        {
          Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
        }
          & {
            SetBranch.point(
              Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
              s,
              r,
              w,
              z,
              c
            )
              == Out{
                [],
                Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                St.marks(s),
                St.groups(s),
                St.clashes(s),
                [Logged.head(c, v)],
                SetBranch.answer(Spec.SetBranch.Created{v})
              }: Out
          }
      ),
      Pair.snd(
        {Br.head.of(Tables.Table.get(Br, St.branches(s), b)) == Some{v}: Maybe<&2, String>},
        (
          {
            Ver.has(St.versions(s), v) == True{}: Bool
          }
            & (
              {
                Tables.Table.get(Br, St.branches(s), c) == None{}: Maybe<&2, Br>
              }
                & {
                  SetBranch.point(
                    Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                    s,
                    r,
                    w,
                    z,
                    c
                  )
                    == Out{
                      [],
                      Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
                      St.marks(s),
                      St.groups(s),
                      St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {St.versions(t) == St.versions(s): Tables.Table<Ver>}

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
        Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {
    St.branches(
      t
    )
      == Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}): Tables.Table<Br>
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
        Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {St.groups(t) == St.groups(s): Tables.Table<Grp>}

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
        Tables.Table.set(Br, St.branches(s), c, Br{v, St.self(s), 0n, 0n}),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
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
  for s: St
  for t: St
  for r: String
  for w: String
  for z: String
  for b: String
  for c: String
  for v: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): St
      & Spec.Answer
  } -> {St.self(t) == St.self(s): String}

def sb_vself.g4(
  +s: St,
  t: St,
  +r: String,
  w: String,
  z: String,
  b: String,
  c: String,
  v: String,
  +x2: Maybe<&2, Seen>,
  hx2: {x2 == Tables.Table.get(Seen, St.seen(s), r): Maybe<&2, Seen>},
  x: {
    Outcome.of(
      x2,
      Ver.taken(St.versions(s), r),
      List.length(&2, Logged, St.log(s))
    )
      == Spec.Outcome.NotSeen{}: Spec.Outcome
  },
  x1: {
    Node.asked(
      x2,
      s,
      r,
      w,
      z,
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (t, Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}): Pair(St, Spec.Answer)
  }
) -> {St.self(t) == St.self(s): String}:
  match x2:
    case None{}:
      view_self(
        s,
        r,
        SetBranch.point(Br.head.of(Tables.Table.get(Br, St.branches(s), b)), s, r, w, z, c),
        t,
        Spec.Answer.SetBranch{Spec.SetBranch.Created{v}}
      )(x1)
    case Some{value}:
      match value:
        case Seen{answer, at}:
          Empty.absurd(
            {St.self(t) == St.self(s): String},
            {
              (%x: {\{Spec.Outcome.Applied: f0 => Unit; \{Spec.Outcome.NotSeen: Empty; \{}}}: Spec.Outcome -> Type}(
                _
              ); Unit{}): Empty
            }
          )

def sb_vself(s, t, r, w, z, b, c, v):
  +s = s
  +r = r
  x => x1 => sb_vself.g4(s, t, r, w, z, b, c, v, Tables.Table.get(Seen, St.seen(s), r), {==}, x, x1)

# a write on the branch b, at its head h, that answers Written: the write as
# the owner it was
law ws_core:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {
    Owner.of(s, Br{h, o, e, k}) == True{}: Bool
  }
    & {
      Write.on(
        Owner.of(s, Br{h, o, e, k}),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        x,
        Br{h, o, e, k}
      )
        == Out{
          [
            Tables.Row{
              r,
              Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
            }
          ],
          Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
          St.marks(s),
          St.groups(s),
          St.clashes(s),
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
    +red = wr_reduce(s, r, w, z, n, b, base, x, Br{h, o, e, k})(new_free(s, r)(hn))(hb)
    wr_on(
      Owner.of(s, Br{h, o, e, k}),
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
            Write.on(Owner.of(s, Br{h, o, e, k}), s, r, w, z, n, b, base, x, Br{h, o, e, k})
          )
        ),
        Answer.version(
          Out.answer(Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}))
        ),
        Some{v},
        Equal.cong(
          Out,
          Maybe<&2, String>,
          y => Answer.version(Out.answer(y)),
          Write.on(Owner.of(s, Br{h, o, e, k}), s, r, w, z, n, b, base, x, Br{h, o, e, k}),
          Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
          Equal.sym(
            Out,
            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
            Write.on(Owner.of(s, Br{h, o, e, k}), s, r, w, z, n, b, base, x, Br{h, o, e, k}),
            red
          )
        ),
        view_ver(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
          t,
          Spec.Answer.Write{Spec.Write.Written{v}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(hn)(hask)
        )
      )
    )

# ... its Out
law ws_out:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {
    Step.of(
      s,
      r,
      w,
      z,
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
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
      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
      Write.on(Owner.of(s, Br{h, o, e, k}), s, r, w, z, n, b, base, x, Br{h, o, e, k}),
      Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      },
      wr_reduce(s, r, w, z, n, b, base, x, Br{h, o, e, k})(new_free(s, r)(hn))(hb),
      Pair.snd(
        {Owner.of(s, Br{h, o, e, k}) == True{}: Bool},
        {
          Write.on(
            Owner.of(s, Br{h, o, e, k}),
            s,
            r,
            w,
            z,
            n,
            b,
            base,
            x,
            Br{h, o, e, k}
          )
            == Out{
              [
                Tables.Row{
                  r,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x),
                    [h],
                    w,
                    z
                  }
                }
              ],
              Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
              St.marks(s),
              St.groups(s),
              St.clashes(s),
              [Logged.head(b, r)],
              Write.answer(Spec.Write.Written{r})
            }: Out
        },
        ws_core(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb)
      )
    )

# ... it was the owner's
law ws_own:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {Owner.of(s, Br{h, o, e, k}) == True{}: Bool}

def ws_own(s, t, r, w, z, n, b, base, x, h, o, e, k, v):
  hn => hask => hb => Pair.fst(
    {Owner.of(s, Br{h, o, e, k}) == True{}: Bool},
    {
      Write.on(
        Owner.of(s, Br{h, o, e, k}),
        s,
        r,
        w,
        z,
        n,
        b,
        base,
        x,
        Br{h, o, e, k}
      )
        == Out{
          [
            Tables.Row{
              r,
              Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
            }
          ],
          Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
          St.marks(s),
          St.groups(s),
          St.clashes(s),
          [Logged.head(b, r)],
          Write.answer(Spec.Write.Written{r})
        }: Out
    },
    ws_core(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb)
  )

# ... the versions after it
law ws_vv:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {
    St.versions(
      t
    )
      == Ver.add(
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        St.versions(s)
      ): Tables.Table<Ver>
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
      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the branches after it
law ws_vb:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {
    St.branches(t) == Tables.Table.set(Br, St.branches(s), b, Br{r, o, e, 1n+k}): Tables.Table<Br>
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
      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the groups after it
law ws_vg:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {St.groups(t) == St.groups(s): Tables.Table<Grp>}

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
      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}},
      Out{
        [
          Tables.Row{
            r,
            Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s), h), n, x), [h], w, z}
          }
        ],
        Tables.Table.set(Br, St.branches(s), b, Br.moved(Br{h, o, e, k}, r)),
        St.marks(s),
        St.groups(s),
        St.clashes(s),
        [Logged.head(b, r)],
        Write.answer(Spec.Write.Written{r})
      }
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )(ws_out(s, t, r, w, z, n, b, base, x, h, o, e, k, v)(hn)(hask)(hb))

# ... the node after it
law ws_vself:
  for s: St
  for t: St
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
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r, w, z},
      Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}
    )
      == (t, Spec.Answer.Write{Spec.Write.Written{v}}): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{h, o, e, k}}: Maybe<&2, Br>
  } -> {St.self(t) == St.self(s): String}

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
      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
      t,
      Spec.Answer.Write{Spec.Write.Written{v}}
    )(
      ask_step(
        s,
        r,
        w,
        z,
        Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
        t,
        Spec.Answer.Write{Spec.Write.Written{v}}
      )(hn)(hask)
    )

# neq_ver, by whether a is b (hit)
law neq_ver.at:
  for hit: Bool
  for vs: Tables.Table<Ver>
  for a: String
  for b: String
  {
    String.eq(a, b) == hit: Bool
  } -> {
    Ver.has(vs, a) == False{}: Bool
  } -> {Ver.has(vs, b) == True{}: Bool} -> {hit == False{}: Bool}

def neq_ver.at(hit, vs, a, b):
  match hit:
    case True{}:
      e => ha => hb =>
        +vs = vs
        +a = a
        +b = b
        Empty.absurd(
          {True{} == False{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Ver.has(vs, a),
              True{},
              Equal.sym(Bool, Ver.has(vs, a), False{}, ha),
              Equal.trans(
                Bool,
                Ver.has(vs, a),
                Ver.has(vs, b),
                True{},
                Equal.cong(
                  String,
                  Bool,
                  z => Ver.has(vs, z),
                  a,
                  b,
                  Strings.String.eq_sound(a, b)(e)
                ),
                hb
              )
            )
          )
        )
    case False{}:
      e => ha => hb => {==}

# a version ID that vs lacks is not one that it holds
law neq_ver:
  for vs: Tables.Table<Ver>
  for a: String
  for b: String
  {
    Ver.has(vs, a) == False{}: Bool
  } -> {Ver.has(vs, b) == True{}: Bool} -> {String.eq(a, b) == False{}: Bool}

def neq_ver(vs, a, b):
  +a = a
  +b = b
  neq_ver.at(String.eq(a, b), vs, a, b)({==})

# neq_br, by whether c is b (hit)
law neq_br.at:
  for hit: Bool
  for bs: Tables.Table<Br>
  for c: String
  for b: String
  for x: Br
  {
    String.eq(c, b) == hit: Bool
  } -> {
    Tables.Table.get(Br, bs, c) == None{}: Maybe<&2, Br>
  } -> {Tables.Table.get(Br, bs, b) == Some{x}: Maybe<&2, Br>} -> {hit == False{}: Bool}

def neq_br.at(hit, bs, c, b, x):
  match hit:
    case True{}:
      e => hc => hb =>
        +bs = bs
        +c = c
        +b = b
        Empty.absurd(
          {True{} == False{}: Bool},
          Maybes.Maybe.none_ne_some(
            Br,
            x,
            Equal.trans(
              Maybe<&2, Br>,
              None{},
              Tables.Table.get(Br, bs, c),
              Some{x},
              Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, bs, c), None{}, hc),
              Equal.trans(
                Maybe<&2, Br>,
                Tables.Table.get(Br, bs, c),
                Tables.Table.get(Br, bs, b),
                Some{x},
                Equal.cong(
                  String,
                  Maybe<&2, Br>,
                  z => Tables.Table.get(Br, bs, z),
                  c,
                  b,
                  Strings.String.eq_sound(c, b)(e)
                ),
                hb
              )
            )
          )
        )
    case False{}:
      e => hc => hb => {==}

# a branch name that bs lacks is not one that it holds
law neq_br:
  for bs: Tables.Table<Br>
  for c: String
  for b: String
  for x: Br
  {
    Tables.Table.get(Br, bs, c) == None{}: Maybe<&2, Br>
  } -> {Tables.Table.get(Br, bs, b) == Some{x}: Maybe<&2, Br>} -> {String.eq(c, b) == False{}: Bool}

def neq_br(bs, c, b, x):
  +c = c
  +b = b
  neq_br.at(String.eq(c, b), bs, c, b, x)({==})

# neq_str, by whether a is b (hit)
law neq_str.at:
  for hit: Bool
  for a: String
  for b: String
  {String.eq(a, b) == hit: Bool} -> {a != b: String} -> {hit == False{}: Bool}

def neq_str.at(hit, a, b):
  match hit:
    case True{}:
      e => hne => Empty.absurd({True{} == False{}: Bool}, hne(Strings.String.eq_sound(a, b)(e)))
    case False{}:
      e => hne => {==}

# different names do not compare equal
law neq_str:
  for a: String
  for b: String
  {a != b: String} -> {String.eq(a, b) == False{}: Bool}

def neq_str(a, b):
  +a = a
  +b = b
  neq_str.at(String.eq(a, b), a, b)({==})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- the law is about the owner check as the node runs it; a proof does not run
# merge_disjoint_keeps_both, once the walks of the merge have fuel f for two
# steps
law mdk_fin:
  for s: St
  for s1: St
  for s2: St
  for s3: St
  for s4: St
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
    Spec.Node.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{n1, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{n2, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{v0, o, e, k}}: Maybe<&2, Br>
  } -> {
    Tables.Table.get(Ver, St.versions(s), v0) == Some{Ver{yb, yp, yw, yt}}: Maybe<&2, Ver>
  } -> {
    History.links(Tables.Table.keys(Ver, St.versions(s3)), St.versions(s3)) == 1n+1n+f: Nat
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
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
    +ecb = neq_br(St.branches(s), c, b, Br{v0, o, e, k})(hcn)(hbs)
    +ebc = Strings.String.eq_flip(c, b)(ecb)
    +b1b = Equal.trans(
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s1), b),
      Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}), b),
      Some{Br{v0, o, e, k}},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, Br>,
        y => Tables.Table.get(Br, y, b),
        St.branches(s1),
        Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
        s1b
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
          b
        ),
        Tables.Table.get(Br, St.branches(s), b),
        Some{Br{v0, o, e, k}},
        Tables.Table.set_keeps_other(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}, b, ecb),
        hbs
      )
    )
    +s2v = ws_vv(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2b = ws_vb(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2g = ws_vg(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +s2s = ws_vself(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +own = ws_own(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +b2c = Equal.trans(
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s2), c),
      Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}), c),
      Some{Br{v0, St.self(s), 0n, 0n}},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, Br>,
        y => Tables.Table.get(Br, y, c),
        St.branches(s2),
        Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}),
        s2b
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}), c),
        Tables.Table.get(Br, St.branches(s1), c),
        Some{Br{v0, St.self(s), 0n, 0n}},
        Tables.Table.set_keeps_other(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}, c, ebc),
        Equal.trans(
          Maybe<&2, Br>,
          Tables.Table.get(Br, St.branches(s1), c),
          Tables.Table.get(
            Br,
            Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
            c
          ),
          Some{Br{v0, St.self(s), 0n, 0n}},
          Equal.cong(
            Tables.Table<Br>,
            Maybe<&2, Br>,
            y => Tables.Table.get(Br, y, c),
            St.branches(s1),
            Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
            s1b
          ),
          Tables.Table.get_after_set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n})
        )
      )
    )
    +s3v = ws_vv(s2, s3, r3, w3, z3, n2, c, base2, x2, v0, St.self(s), 0n, 0n, v2)(hn3)(h3)(b2c)
    +s3b = ws_vb(s2, s3, r3, w3, z3, n2, c, base2, x2, v0, St.self(s), 0n, 0n, v2)(hn3)(h3)(b2c)
    +s3g = ws_vg(s2, s3, r3, w3, z3, n2, c, base2, x2, v0, St.self(s), 0n, 0n, v2)(hn3)(h3)(b2c)
    +s3s = ws_vself(s2, s3, r3, w3, z3, n2, c, base2, x2, v0, St.self(s), 0n, 0n, v2)(hn3)(h3)(b2c)
    +ha = Equal.trans(
      Maybe<&2, String>,
      Br.head.of(Tables.Table.get(Br, St.branches(s3), c)),
      Br.head.of(
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
          c
        )
      ),
      Some{r3},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, String>,
        y => Br.head.of(Tables.Table.get(Br, y, c)),
        St.branches(s3),
        Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
        s3b
      ),
      Equal.cong(
        Maybe<&2, Br>,
        Maybe<&2, String>,
        y => Br.head.of(y),
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
          c
        ),
        Some{Br{r3, St.self(s), 0n, 1n+0n}},
        Tables.Table.get_after_set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n})
      )
    )
    +hb3 = Equal.trans(
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s3), b),
      Tables.Table.get(
        Br,
        Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
        b
      ),
      Some{Br{r2, o, e, 1n+k}},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, Br>,
        y => Tables.Table.get(Br, y, b),
        St.branches(s3),
        Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
        s3b
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}),
          b
        ),
        Tables.Table.get(Br, St.branches(s2), b),
        Some{Br{r2, o, e, 1n+k}},
        Tables.Table.set_keeps_other(Br, St.branches(s2), c, Br{r3, St.self(s), 0n, 1n+0n}, b, ecb),
        Equal.trans(
          Maybe<&2, Br>,
          Tables.Table.get(Br, St.branches(s2), b),
          Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}), b),
          Some{Br{r2, o, e, 1n+k}},
          Equal.cong(
            Tables.Table<Br>,
            Maybe<&2, Br>,
            y => Tables.Table.get(Br, y, b),
            St.branches(s2),
            Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}),
            s2b
          ),
          Tables.Table.get_after_set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k})
        )
      )
    )
    +s31 = Equal.trans(String, St.self(s3), St.self(s2), St.self(s1), s3s, s2s)
    +g31 = Equal.trans(Tables.Table<Grp>, St.groups(s3), St.groups(s2), St.groups(s1), s3g, s2g)
    +hown = Equal.trans(
      Bool,
      Owner.of(s3, Br{r2, o, e, 1n+k}),
      Bool.or(
        String.eq(o, St.self(s1)),
        Grp.inside(St.groups(s3), Spec.Member.Node{St.self(s1)}, o)
      ),
      True{},
      Equal.cong(
        String,
        Bool,
        y => Bool.or(String.eq(o, y), Grp.inside(St.groups(s3), Spec.Member.Node{y}, o)),
        St.self(s3),
        St.self(s1),
        s31
      ),
      Equal.trans(
        Bool,
        Bool.or(
          String.eq(o, St.self(s1)),
          Grp.inside(St.groups(s3), Spec.Member.Node{St.self(s1)}, o)
        ),
        Owner.of(s1, Br{v0, o, e, k}),
        True{},
        Equal.cong(
          Tables.Table<Grp>,
          Bool,
          y => Bool.or(String.eq(o, St.self(s1)), Grp.inside(y, Spec.Member.Node{St.self(s1)}, o)),
          St.groups(s3),
          St.groups(s1),
          g31
        ),
        own
      )
    )
    +ht4 = new_free(s3, r4)(hn4)
    +ht2 = new_free(s1, r2)(hn2)
    +ht3 = new_free(s2, r3)(hn3)
    +g1v0 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s1), v0),
      Tables.Table.get(Ver, St.versions(s), v0),
      Some{Ver{yb, yp, yw, yt}},
      Equal.cong(
        Tables.Table<Ver>,
        Maybe<&2, Ver>,
        y => Tables.Table.get(Ver, y, v0),
        St.versions(s1),
        St.versions(s),
        s1v
      ),
      hvs
    )
    +hv1 = Equal.cong(
      Maybe<&2, Ver>,
      Bool,
      y => Maybe.is_some(&2, Ver, y),
      Tables.Table.get(Ver, St.versions(s1), v0),
      Some{Ver{yb, yp, yw, yt}},
      g1v0
    )
    +er2v0 = neq_ver(St.versions(s1), r2, v0)(taken_free(St.versions(s1), r2)(ht2))(hv1)
    +g2v0 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s2), v0),
      Tables.Table.get(Ver, St.versions(s1), v0),
      Some{Ver{yb, yp, yw, yt}},
      Equal.trans(
        Maybe<&2, Ver>,
        Tables.Table.get(Ver, St.versions(s2), v0),
        Tables.Table.get(
          Ver,
          Ver.add(
            [
              Tables.Row{
                r2,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
                  [v0],
                  w2,
                  z2
                }
              }
            ],
            St.versions(s1)
          ),
          v0
        ),
        Tables.Table.get(Ver, St.versions(s1), v0),
        Equal.cong(
          Tables.Table<Ver>,
          Maybe<&2, Ver>,
          y => Tables.Table.get(Ver, y, v0),
          St.versions(s2),
          Ver.add(
            [
              Tables.Row{
                r2,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
                  [v0],
                  w2,
                  z2
                }
              }
            ],
            St.versions(s1)
          ),
          s2v
        ),
        add1_other(
          St.versions(s1),
          r2,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
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
      Maybe<&2, Ver>,
      Bool,
      y => Maybe.is_some(&2, Ver, y),
      Tables.Table.get(Ver, St.versions(s2), v0),
      Some{Ver{yb, yp, yw, yt}},
      g2v0
    )
    +er3v0 = neq_ver(St.versions(s2), r3, v0)(taken_free(St.versions(s2), r3)(ht3))(hv2)
    +g2r2 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s2), r2),
      Tables.Table.get(
        Ver,
        Ver.add(
          [
            Tables.Row{
              r2,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
                [v0],
                w2,
                z2
              }
            }
          ],
          St.versions(s1)
        ),
        r2
      ),
      Some{
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1), [v0], w2, z2}
      },
      Equal.cong(
        Tables.Table<Ver>,
        Maybe<&2, Ver>,
        y => Tables.Table.get(Ver, y, r2),
        St.versions(s2),
        Ver.add(
          [
            Tables.Row{
              r2,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
                [v0],
                w2,
                z2
              }
            }
          ],
          St.versions(s1)
        ),
        s2v
      ),
      add_new_find(
        r2,
        Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
        [v0],
        w2,
        z2,
        St.versions(s1)
      )(taken_free(St.versions(s1), r2)(ht2))
    )
    +er3r2 = neq_ver(
      St.versions(s2),
      r3,
      r2
    )(
      taken_free(St.versions(s2), r3)(ht3)
    )(
      Equal.cong(
        Maybe<&2, Ver>,
        Bool,
        y => Maybe.is_some(&2, Ver, y),
        Tables.Table.get(Ver, St.versions(s2), r2),
        Some{
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
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
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s3), r3),
      Tables.Table.get(
        Ver,
        Ver.add(
          [
            Tables.Row{
              r3,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          St.versions(s2)
        ),
        r3
      ),
      Some{
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2), [v0], w3, z3}
      },
      Equal.cong(
        Tables.Table<Ver>,
        Maybe<&2, Ver>,
        y => Tables.Table.get(Ver, y, r3),
        St.versions(s3),
        Ver.add(
          [
            Tables.Row{
              r3,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          St.versions(s2)
        ),
        s3v
      ),
      add_new_find(
        r3,
        Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
        [v0],
        w3,
        z3,
        St.versions(s2)
      )(taken_free(St.versions(s2), r3)(ht3))
    )
    +g3r2 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s3), r2),
      Tables.Table.get(Ver, St.versions(s2), r2),
      Some{
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1), [v0], w2, z2}
      },
      Equal.trans(
        Maybe<&2, Ver>,
        Tables.Table.get(Ver, St.versions(s3), r2),
        Tables.Table.get(
          Ver,
          Ver.add(
            [
              Tables.Row{
                r3,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            St.versions(s2)
          ),
          r2
        ),
        Tables.Table.get(Ver, St.versions(s2), r2),
        Equal.cong(
          Tables.Table<Ver>,
          Maybe<&2, Ver>,
          y => Tables.Table.get(Ver, y, r2),
          St.versions(s3),
          Ver.add(
            [
              Tables.Row{
                r3,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            St.versions(s2)
          ),
          s3v
        ),
        add1_other(
          St.versions(s2),
          r3,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
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
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s3), v0),
      Tables.Table.get(Ver, St.versions(s2), v0),
      Some{Ver{yb, yp, yw, yt}},
      Equal.trans(
        Maybe<&2, Ver>,
        Tables.Table.get(Ver, St.versions(s3), v0),
        Tables.Table.get(
          Ver,
          Ver.add(
            [
              Tables.Row{
                r3,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            St.versions(s2)
          ),
          v0
        ),
        Tables.Table.get(Ver, St.versions(s2), v0),
        Equal.cong(
          Tables.Table<Ver>,
          Maybe<&2, Ver>,
          y => Tables.Table.get(Ver, y, v0),
          St.versions(s3),
          Ver.add(
            [
              Tables.Row{
                r3,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            St.versions(s2)
          ),
          s3v
        ),
        add1_other(
          St.versions(s2),
          r3,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
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
      Strings.has(Vers.ids(History.of(St.versions(s3), r2)), r3),
      Strings.has(
        Vers.ids(
          History.of(
            Ver.add(
              [
                Tables.Row{
                  r3,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                    [v0],
                    w3,
                    z3
                  }
                }
              ],
              St.versions(s2)
            ),
            r2
          )
        ),
        r3
      ),
      False{},
      Equal.cong(
        Tables.Table<Ver>,
        Bool,
        y => Strings.has(Vers.ids(History.of(y, r2)), r3),
        St.versions(s3),
        Ver.add(
          [
            Tables.Row{
              r3,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          St.versions(s2)
        ),
        s3v
      ),
      walk_avoid(
        History.links(
          Tables.Table.keys(
            Ver,
            Ver.add(
              [
                Tables.Row{
                  r3,
                  Ver{
                    Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                    [v0],
                    w3,
                    z3
                  }
                }
              ],
              St.versions(s2)
            )
          ),
          Ver.add(
            [
              Tables.Row{
                r3,
                Ver{
                  Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                  [v0],
                  w3,
                  z3
                }
              }
            ],
            St.versions(s2)
          )
        ),
        [r2],
        [],
        r3,
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2), [v0], w3, z3},
        St.versions(s2)
      )(
        (%Equal.sym(
          Bool,
          String.eq(r2, r3),
          False{},
          er2r3
        ): {List.any.if(u => Strings.has([], r3), _) == False{}: Bool}; {==})
      )(
        Bools.Bool.or_false_right(
          Ver.has(St.versions(s2), r3),
          Ver.named(Tables.Table.keys(Ver, St.versions(s2)), St.versions(s2), r3)
        )(ht3)
      )
    )
    +hk3 = Equal.trans(
      Bool,
      Strings.has(Tables.Table.keys(Ver, St.versions(s3)), r3),
      Maybe.is_some(&2, Ver, Tables.Table.get(Ver, St.versions(s3), r3)),
      True{},
      Tables.Table.keys_get(Ver, St.versions(s3), r3),
      Equal.cong(
        Maybe<&2, Ver>,
        Bool,
        y => Maybe.is_some(&2, Ver, y),
        Tables.Table.get(Ver, St.versions(s3), r3),
        Some{
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        },
        g3r3
      )
    )
    +hbv1 = Equal.cong(
      Maybe<&2, Ver>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        Ver.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(Ver, St.versions(s1), v0),
      Some{Ver{yb, yp, yw, yt}},
      g1v0
    )
    +hbv2 = Equal.cong(
      Maybe<&2, Ver>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        Ver.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(Ver, St.versions(s2), v0),
      Some{Ver{yb, yp, yw, yt}},
      g2v0
    )
    +hbv3 = Equal.cong(
      Maybe<&2, Ver>,
      Tables.Table<List<&2, U32>>,
      y => Maybe.default(
        &2,
        Tables.Table<List<&2, U32>>,
        Ver.blobs.of(y),
        Tables.Table.new(List<&2, U32>)
      ),
      Tables.Table.get(Ver, St.versions(s3), v0),
      Some{Ver{yb, yp, yw, yt}},
      g3v0
    )
    +hbr2 = Equal.trans(
      Tables.Table<List<&2, U32>>,
      Vers.blobs(St.versions(s3), r2),
      Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
      Tables.Table.set(List<&2, U32>, yb, n1, x1),
      Equal.cong(
        Maybe<&2, Ver>,
        Tables.Table<List<&2, U32>>,
        y => Maybe.default(
          &2,
          Tables.Table<List<&2, U32>>,
          Ver.blobs.of(y),
          Tables.Table.new(List<&2, U32>)
        ),
        Tables.Table.get(Ver, St.versions(s3), r2),
        Some{
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
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
        Vers.blobs(St.versions(s1), v0),
        yb,
        hbv1
      )
    )
    +hbr3 = Equal.trans(
      Tables.Table<List<&2, U32>>,
      Vers.blobs(St.versions(s3), r3),
      Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
      Tables.Table.set(List<&2, U32>, yb, n2, x2),
      Equal.cong(
        Maybe<&2, Ver>,
        Tables.Table<List<&2, U32>>,
        y => Maybe.default(
          &2,
          Tables.Table<List<&2, U32>>,
          Ver.blobs.of(y),
          Tables.Table.new(List<&2, U32>)
        ),
        Tables.Table.get(Ver, St.versions(s3), r3),
        Some{
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
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
        Vers.blobs(St.versions(s2), v0),
        yb,
        hbv2
      )
    )
    +hf3 = Equal.trans(
      List<&2, Tables.Row<Ver>>,
      History.of(St.versions(s3), r3),
      History.walk(1n+1n+f, [r3], [], St.versions(s3)),
      Tables.Row{
        r3,
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2), [v0], w3, z3}
      }
        <> (Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r3], St.versions(s3))),
      Equal.cong(
        Nat,
        List<&2, Tables.Row<Ver>>,
        y => History.walk(y, [r3], [], St.versions(s3)),
        History.links(Tables.Table.keys(Ver, St.versions(s3)), St.versions(s3)),
        1n+1n+f,
        hl
      ),
      hist_two(
        f,
        r3,
        v0,
        Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
        w3,
        z3,
        yb,
        yp,
        yw,
        yt,
        St.versions(s3)
      )(g3r3)(er3v0)(g3v0)
    )
    +hf2 = Equal.trans(
      List<&2, Tables.Row<Ver>>,
      History.of(St.versions(s3), r2),
      History.walk(1n+1n+f, [r2], [], St.versions(s3)),
      Tables.Row{
        r2,
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1), [v0], w2, z2}
      }
        <> (Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r2], St.versions(s3))),
      Equal.cong(
        Nat,
        List<&2, Tables.Row<Ver>>,
        y => History.walk(y, [r2], [], St.versions(s3)),
        History.links(Tables.Table.keys(Ver, St.versions(s3)), St.versions(s3)),
        1n+1n+f,
        hl
      ),
      hist_two(
        f,
        r2,
        v0,
        Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
        w2,
        z2,
        yb,
        yp,
        yw,
        yt,
        St.versions(s3)
      )(g3r2)(er2v0)(g3v0)
    )
    +hids = Equal.trans(
      Bool,
      Strings.has(Vers.ids(History.of(St.versions(s3), r2)), v0),
      Strings.has(
        Vers.ids(
          Tables.Row{
            r2,
            Ver{
              Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
              [v0],
              w2,
              z2
            }
          }
            <> (
              Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r2], St.versions(s3))
            )
        ),
        v0
      ),
      True{},
      Equal.cong(
        List<&2, Tables.Row<Ver>>,
        Bool,
        y => Strings.has(Vers.ids(y), v0),
        History.of(St.versions(s3), r2),
        Tables.Row{
          r2,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1),
            [v0],
            w2,
            z2
          }
        }
          <> (
            Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r2], St.versions(s3))
          ),
        hf2
      ),
      ids_second(
        r2,
        v0,
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s1), v0), n1, x1), [v0], w2, z2},
        Ver{yb, yp, yw, yt},
        History.walk(f, yp, [v0, r2], St.versions(s3))
      )(er2v0)
    )
    +hf = Equal.trans(
      Maybe<&2, String>,
      Vers.first_in(History.of(St.versions(s3), r3), Vers.ids(History.of(St.versions(s3), r2))),
      Vers.first_in(
        Tables.Row{
          r3,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        }
          <> (
            Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r3], St.versions(s3))
          ),
        Vers.ids(History.of(St.versions(s3), r2))
      ),
      Some{v0},
      Equal.cong(
        List<&2, Tables.Row<Ver>>,
        Maybe<&2, String>,
        y => Vers.first_in(y, Vers.ids(History.of(St.versions(s3), r2))),
        History.of(St.versions(s3), r3),
        Tables.Row{
          r3,
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
            [v0],
            w3,
            z3
          }
        }
          <> (
            Tables.Row{v0, Ver{yb, yp, yw, yt}} <> History.walk(f, yp, [v0, r3], St.versions(s3))
          ),
        hf3
      ),
      first_two(
        r3,
        v0,
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2), [v0], w3, z3},
        Ver{yb, yp, yw, yt},
        History.walk(f, yp, [v0, r3], St.versions(s3)),
        Vers.ids(History.of(St.versions(s3), r2))
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
            Ver{
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
        Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
        St.marks(s3),
        St.groups(s3),
        St.clashes(s3),
        [Logged.head(b, r4)],
        Merge.answer(Spec.Merge.Merged{r4})
      },
      Equal.cong(
        Maybe<&2, String>,
        Out,
        y => Merge.point(y, s3, r4, w4, z4, b),
        Br.head.of(Tables.Table.get(Br, St.branches(s3), c)),
        Some{r3},
        ha
      ),
      Equal.trans(
        Out,
        Merge.point(Some{r3}, s3, r4, w4, z4, b),
        Merge.branch(Some{Br{r2, o, e, 1n+k}}, s3, r4, w4, z4, r3, b),
        Out{
          [
            Tables.Row{
              r4,
              Ver{
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
          Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
          St.marks(s3),
          St.groups(s3),
          St.clashes(s3),
          [Logged.head(b, r4)],
          Merge.answer(Spec.Merge.Merged{r4})
        },
        Equal.cong(
          Maybe<&2, Br>,
          Out,
          y => Merge.branch(y, s3, r4, w4, z4, r3, b),
          Tables.Table.get(Br, St.branches(s3), b),
          Some{Br{r2, o, e, 1n+k}},
          hb3
        ),
        Equal.trans(
          Out,
          Merge.branch(Some{Br{r2, o, e, 1n+k}}, s3, r4, w4, z4, r3, b),
          Merge.owner(
            True{},
            Ver.taken(St.versions(s3), r4),
            s3,
            r4,
            w4,
            z4,
            r3,
            b,
            Br{r2, o, e, 1n+k}
          ),
          Out{
            [
              Tables.Row{
                r4,
                Ver{
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
            Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
            St.marks(s3),
            St.groups(s3),
            St.clashes(s3),
            [Logged.head(b, r4)],
            Merge.answer(Spec.Merge.Merged{r4})
          },
          Equal.cong(
            Bool,
            Out,
            y => Merge.owner(
              y,
              Ver.taken(St.versions(s3), r4),
              s3,
              r4,
              w4,
              z4,
              r3,
              b,
              Br{r2, o, e, 1n+k}
            ),
            Owner.of(s3, Br{r2, o, e, 1n+k}),
            True{},
            hown
          ),
          Equal.trans(
            Out,
            Merge.owner(
              True{},
              Ver.taken(St.versions(s3), r4),
              s3,
              r4,
              w4,
              z4,
              r3,
              b,
              Br{r2, o, e, 1n+k}
            ),
            Merge.owner(True{}, False{}, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
            Out{
              [
                Tables.Row{
                  r4,
                  Ver{
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
              Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
              St.marks(s3),
              St.groups(s3),
              St.clashes(s3),
              [Logged.head(b, r4)],
              Merge.answer(Spec.Merge.Merged{r4})
            },
            Equal.cong(
              Bool,
              Out,
              y => Merge.owner(True{}, y, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
              Ver.taken(St.versions(s3), r4),
              False{},
              ht4
            ),
            Equal.trans(
              Out,
              Merge.owner(True{}, False{}, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
              Merge.inside(False{}, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
              Out{
                [
                  Tables.Row{
                    r4,
                    Ver{
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
                Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                St.marks(s3),
                St.groups(s3),
                St.clashes(s3),
                [Logged.head(b, r4)],
                Merge.answer(Spec.Merge.Merged{r4})
              },
              Equal.cong(
                Bool,
                Out,
                y => Merge.inside(y, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
                Strings.has(Vers.ids(History.of(St.versions(s3), r2)), r3),
                False{},
                hav
              ),
              Equal.trans(
                Out,
                Merge.inside(False{}, s3, r4, w4, z4, r3, b, Br{r2, o, e, 1n+k}),
                Merge.three(
                  s3,
                  r4,
                  w4,
                  z4,
                  r3,
                  Vers.blobs(St.versions(s3), r2),
                  Vers.blobs(St.versions(s3), r3),
                  Vers.blobs(St.versions(s3), v0),
                  b,
                  Br{r2, o, e, 1n+k}
                ),
                Out{
                  [
                    Tables.Row{
                      r4,
                      Ver{
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
                  Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                  St.marks(s3),
                  St.groups(s3),
                  St.clashes(s3),
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
                    Vers.blobs(St.versions(s3), r2),
                    Vers.blobs(St.versions(s3), r3),
                    Merge.base(s3, y),
                    b,
                    Br{r2, o, e, 1n+k}
                  ),
                  Vers.first_in(
                    History.of(St.versions(s3), r3),
                    Vers.ids(History.of(St.versions(s3), r2))
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
                    Vers.blobs(St.versions(s3), r2),
                    Vers.blobs(St.versions(s3), r3),
                    Vers.blobs(St.versions(s3), v0),
                    b,
                    Br{r2, o, e, 1n+k}
                  ),
                  Merge.three(
                    s3,
                    r4,
                    w4,
                    z4,
                    r3,
                    Tables.Table.set(List<&2, U32>, yb, n1, x1),
                    Vers.blobs(St.versions(s3), r3),
                    Vers.blobs(St.versions(s3), v0),
                    b,
                    Br{r2, o, e, 1n+k}
                  ),
                  Out{
                    [
                      Tables.Row{
                        r4,
                        Ver{
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
                    Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                    St.marks(s3),
                    St.groups(s3),
                    St.clashes(s3),
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
                      Vers.blobs(St.versions(s3), r3),
                      Vers.blobs(St.versions(s3), v0),
                      b,
                      Br{r2, o, e, 1n+k}
                    ),
                    Vers.blobs(St.versions(s3), r2),
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
                      Vers.blobs(St.versions(s3), r3),
                      Vers.blobs(St.versions(s3), v0),
                      b,
                      Br{r2, o, e, 1n+k}
                    ),
                    Merge.three(
                      s3,
                      r4,
                      w4,
                      z4,
                      r3,
                      Tables.Table.set(List<&2, U32>, yb, n1, x1),
                      Tables.Table.set(List<&2, U32>, yb, n2, x2),
                      Vers.blobs(St.versions(s3), v0),
                      b,
                      Br{r2, o, e, 1n+k}
                    ),
                    Out{
                      [
                        Tables.Row{
                          r4,
                          Ver{
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
                      Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                      St.marks(s3),
                      St.groups(s3),
                      St.clashes(s3),
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
                        Vers.blobs(St.versions(s3), v0),
                        b,
                        Br{r2, o, e, 1n+k}
                      ),
                      Vers.blobs(St.versions(s3), r3),
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
                        Vers.blobs(St.versions(s3), v0),
                        b,
                        Br{r2, o, e, 1n+k}
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
                        Br{r2, o, e, 1n+k}
                      ),
                      Out{
                        [
                          Tables.Row{
                            r4,
                            Ver{
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
                        Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                        St.marks(s3),
                        St.groups(s3),
                        St.clashes(s3),
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
                          Br{r2, o, e, 1n+k}
                        ),
                        Vers.blobs(St.versions(s3), v0),
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
                          Br{r2, o, e, 1n+k}
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
            Ver{
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
        Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
        St.marks(s3),
        St.groups(s3),
        St.clashes(s3),
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
            Ver{
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
        Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
        St.marks(s3),
        St.groups(s3),
        St.clashes(s3),
        [Logged.head(b, r4)],
        Merge.answer(Spec.Merge.Merged{r4})
      }
    )(ha4)(hmo)
    +hd4 = Equal.trans(
      Maybe<&2, String>,
      Br.head.of(Tables.Table.get(Br, St.branches(s4), b)),
      Br.head.of(
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
          b
        )
      ),
      Some{r4},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, String>,
        y => Br.head.of(Tables.Table.get(Br, y, b)),
        St.branches(s4),
        Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
        s4b
      ),
      Equal.cong(
        Maybe<&2, Br>,
        Maybe<&2, String>,
        y => Br.head.of(y),
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
          b
        ),
        Some{Br.moved(Br{r2, o, e, 1n+k}, r4)},
        Tables.Table.get_after_set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4))
      )
    )
    +hg4 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s4), r4),
      Tables.Table.get(
        Ver,
        Ver.add(
          [
            Tables.Row{
              r4,
              Ver{
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
          St.versions(s3)
        ),
        r4
      ),
      Some{
        Ver{
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
        Tables.Table<Ver>,
        Maybe<&2, Ver>,
        y => Tables.Table.get(Ver, y, r4),
        St.versions(s4),
        Ver.add(
          [
            Tables.Row{
              r4,
              Ver{
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
          St.versions(s3)
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
        St.versions(s3)
      )(taken_free(St.versions(s3), r4)(ht4))
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
            Strings.has(
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
          Strings.has(
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
                  Ver{
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
              Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
              St.marks(s3),
              St.groups(s3),
              St.clashes(s3),
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
                    Ver{
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
                Tables.Table.set(Br, St.branches(s3), b, Br.moved(Br{r2, o, e, 1n+k}, r4)),
                St.marks(s3),
                St.groups(s3),
                St.clashes(s3),
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
          St.content(s4, n1, Spec.Point.Head{b}),
          Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), Some{r4})), n1),
          Some{x1},
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, List<&2, U32>>,
            y => Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), y)), n1),
            Br.head.of(Tables.Table.get(Br, St.branches(s4), b)),
            Some{r4},
            hd4
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), Some{r4})), n1),
            Blob.find.of(
              Ver.blobs.of(
                Some{
                  Ver{
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
              Maybe<&2, Ver>,
              Maybe<&2, List<&2, U32>>,
              y => Blob.find.of(Ver.blobs.of(y), n1),
              Tables.Table.get(Ver, St.versions(s4), r4),
              Some{
                Ver{
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
          St.content(s4, n2, Spec.Point.Head{b}),
          Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), Some{r4})), n2),
          Some{x2},
          Equal.cong(
            Maybe<&2, String>,
            Maybe<&2, List<&2, U32>>,
            y => Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), y)), n2),
            Br.head.of(Tables.Table.get(Br, St.branches(s4), b)),
            Some{r4},
            hd4
          ),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Blob.find.of(Ver.blobs.of(Ver.find.of(St.versions(s4), Some{r4})), n2),
            Blob.find.of(
              Ver.blobs.of(
                Some{
                  Ver{
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
              Maybe<&2, Ver>,
              Maybe<&2, List<&2, U32>>,
              y => Blob.find.of(Ver.blobs.of(y), n2),
              Tables.Table.get(Ver, St.versions(s4), r4),
              Some{
                Ver{
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
  for s: St
  for s1: St
  for s2: St
  for s3: St
  for s4: St
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
    History.links(Tables.Table.keys(Ver, St.versions(s3)), St.versions(s3)) == 1n+1n+f: Nat
  }
  {
    Spec.Node.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{n1, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{n2, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{v0, o, e, k}}: Maybe<&2, Br>
  } -> {
    Tables.Table.get(Ver, St.versions(s), v0) == Some{Ver{yb, yp, yw, yt}}: Maybe<&2, Ver>
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
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
  for s: St
  for s1: St
  for s2: St
  for s3: St
  for s4: St
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
    Spec.Node.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{n1, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{n2, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): St
      & Spec.Answer
  } -> {
    Tables.Table.get(Br, St.branches(s), b) == Some{Br{v0, o, e, k}}: Maybe<&2, Br>
  } -> {
    Tables.Table.get(Ver, St.versions(s), v0) == Some{Ver{yb, yp, yw, yt}}: Maybe<&2, Ver>
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
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
    +ecb = neq_br(St.branches(s), c, b, Br{v0, o, e, k})(hcn)(hbs)
    +ebc = Strings.String.eq_flip(c, b)(ecb)
    +b1b = Equal.trans(
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s1), b),
      Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}), b),
      Some{Br{v0, o, e, k}},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, Br>,
        y => Tables.Table.get(Br, y, b),
        St.branches(s1),
        Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
        s1b
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(
          Br,
          Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
          b
        ),
        Tables.Table.get(Br, St.branches(s), b),
        Some{Br{v0, o, e, k}},
        Tables.Table.set_keeps_other(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}, b, ecb),
        hbs
      )
    )
    +s2b = ws_vb(s1, s2, r2, w2, z2, n1, b, base1, x1, v0, o, e, k, v1)(hn2)(h2)(b1b)
    +b2c = Equal.trans(
      Maybe<&2, Br>,
      Tables.Table.get(Br, St.branches(s2), c),
      Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}), c),
      Some{Br{v0, St.self(s), 0n, 0n}},
      Equal.cong(
        Tables.Table<Br>,
        Maybe<&2, Br>,
        y => Tables.Table.get(Br, y, c),
        St.branches(s2),
        Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}),
        s2b
      ),
      Equal.trans(
        Maybe<&2, Br>,
        Tables.Table.get(Br, Tables.Table.set(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}), c),
        Tables.Table.get(Br, St.branches(s1), c),
        Some{Br{v0, St.self(s), 0n, 0n}},
        Tables.Table.set_keeps_other(Br, St.branches(s1), b, Br{r2, o, e, 1n+k}, c, ebc),
        Equal.trans(
          Maybe<&2, Br>,
          Tables.Table.get(Br, St.branches(s1), c),
          Tables.Table.get(
            Br,
            Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
            c
          ),
          Some{Br{v0, St.self(s), 0n, 0n}},
          Equal.cong(
            Tables.Table<Br>,
            Maybe<&2, Br>,
            y => Tables.Table.get(Br, y, c),
            St.branches(s1),
            Tables.Table.set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n}),
            s1b
          ),
          Tables.Table.get_after_set(Br, St.branches(s), c, Br{v0, St.self(s), 0n, 0n})
        )
      )
    )
    +s3v = ws_vv(s2, s3, r3, w3, z3, n2, c, base2, x2, v0, St.self(s), 0n, 0n, v2)(hn3)(h3)(b2c)
    +ht3 = new_free(s2, r3)(hn3)
    +g3r3 = Equal.trans(
      Maybe<&2, Ver>,
      Tables.Table.get(Ver, St.versions(s3), r3),
      Tables.Table.get(
        Ver,
        Ver.add(
          [
            Tables.Row{
              r3,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          St.versions(s2)
        ),
        r3
      ),
      Some{
        Ver{Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2), [v0], w3, z3}
      },
      Equal.cong(
        Tables.Table<Ver>,
        Maybe<&2, Ver>,
        y => Tables.Table.get(Ver, y, r3),
        St.versions(s3),
        Ver.add(
          [
            Tables.Row{
              r3,
              Ver{
                Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
                [v0],
                w3,
                z3
              }
            }
          ],
          St.versions(s2)
        ),
        s3v
      ),
      add_new_find(
        r3,
        Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
        [v0],
        w3,
        z3,
        St.versions(s2)
      )(taken_free(St.versions(s2), r3)(ht3))
    )
    +hk3 = Equal.trans(
      Bool,
      Strings.has(Tables.Table.keys(Ver, St.versions(s3)), r3),
      Maybe.is_some(&2, Ver, Tables.Table.get(Ver, St.versions(s3), r3)),
      True{},
      Tables.Table.keys_get(Ver, St.versions(s3), r3),
      Equal.cong(
        Maybe<&2, Ver>,
        Bool,
        y => Maybe.is_some(&2, Ver, y),
        Tables.Table.get(Ver, St.versions(s3), r3),
        Some{
          Ver{
            Tables.Table.set(List<&2, U32>, Vers.blobs(St.versions(s2), v0), n2, x2),
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
      links_two(Tables.Table.keys(Ver, St.versions(s3)), St.versions(s3), r3)(hk3)
    )(hn1)(hn2)(hn3)(hn4)(hne)(h1)(h2)(h3)(h4)(hbs)(hvs)

# merge_disjoint_keeps_both, by b's record (mb) and v0's version (mv)
law mdk_split:
  for mb: Maybe<&2, Br>
  for mv: Maybe<&2, Ver>
  for s: St
  for s1: St
  for s2: St
  for s3: St
  for s4: St
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
    Tables.Table.get(Br, St.branches(s), b) == mb: Maybe<&2, Br>
  } -> {
    Tables.Table.get(Ver, St.versions(s), v0) == mv: Maybe<&2, Ver>
  } -> {
    Spec.Node.get_outcome(s, r1) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s1, r2) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s2, r3) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    Spec.Node.get_outcome(s3, r4) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {
    String.eq(n1, n2) == False{}: Bool
  } -> {
    Spec.Node.ask(
      s,
      Spec.Envelope{r1, w1, z1},
      Spec.Ask.SetBranch{c, Spec.Point.Head{b}}
    )
      == (s1, Spec.Answer.SetBranch{Spec.SetBranch.Created{v0}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s1,
      Spec.Envelope{r2, w2, z2},
      Spec.Ask.Write{n1, b, base1, Spec.Content.Bytes{x1}}
    )
      == (s2, Spec.Answer.Write{Spec.Write.Written{v1}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s2,
      Spec.Envelope{r3, w3, z3},
      Spec.Ask.Write{n2, c, base2, Spec.Content.Bytes{x2}}
    )
      == (s3, Spec.Answer.Write{Spec.Write.Written{v2}}): St
      & Spec.Answer
  } -> {
    Spec.Node.ask(
      s3,
      Spec.Envelope{r4, w4, z4},
      Spec.Ask.Merge{Spec.Point.Head{c}, b}
    )
      == (s4, a4): St
      & Spec.Answer
  } -> {
    a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
  }
    & (
      {
        St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
      }
        & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
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
                St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
              }
                & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
            ),
          Maybes.Maybe.none_ne_some(
            String,
            v0,
            Equal.trans(
              Maybe<&2, String>,
              None{},
              Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
              Some{v0},
              Equal.sym(
                Maybe<&2, String>,
                Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
                None{},
                Equal.cong(
                  Maybe<&2, Br>,
                  Maybe<&2, String>,
                  y => Br.head.of(y),
                  Tables.Table.get(Br, St.branches(s), b),
                  None{},
                  eb
                )
              ),
              sb_head(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
            )
          )
        )
    case Some{Br{h, o, e, k}} None{}:
      eb => ev => +hn1 => hn2 => hn3 => hn4 => hne => +h1 => h2 => h3 => h4 =>
        Empty.absurd(
          {
            a4 == Spec.Answer.Merge{Spec.Merge.Merged{r4}}: Spec.Answer
          }
            & (
              {
                St.content(s4, n1, Spec.Point.Head{b}) == Some{x1}: Maybe<&2, List<&2, U32>>
              }
                & {St.content(s4, n2, Spec.Point.Head{b}) == Some{x2}: Maybe<&2, List<&2, U32>>}
            ),
          Shared.Bool.false_ne_true(
            Equal.trans(
              Bool,
              False{},
              Ver.has(St.versions(s), v0),
              True{},
              Equal.sym(
                Bool,
                Ver.has(St.versions(s), v0),
                False{},
                Equal.cong(
                  Maybe<&2, Ver>,
                  Bool,
                  y => Maybe.is_some(&2, Ver, y),
                  Tables.Table.get(Ver, St.versions(s), v0),
                  None{},
                  ev
                )
              ),
              sb_has(s, s1, r1, w1, z1, b, c, v0)(hn1)(h1)
            )
          )
        )
    case Some{Br{+h, +o, +e, +k}} Some{Ver{yb, yp, yw, yt}}:
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
            Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
            Some{v0},
            Equal.sym(
              Maybe<&2, String>,
              Br.head.of(Tables.Table.get(Br, St.branches(s), b)),
              Some{h},
              Equal.cong(
                Maybe<&2, Br>,
                Maybe<&2, String>,
                y => Br.head.of(y),
                Tables.Table.get(Br, St.branches(s), b),
                Some{Br{h, o, e, k}},
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
            %hv0: {Tables.Table.get(Br, St.branches(s), b) == Some{Br{_, o, e, k}}: Maybe<&2, Br>}
            eb))(ev)
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
        Spec.Node.get_changes(
          Pair.fst(St, Spec.Answer, _),
          k,
          None{}
        )
          == List.append(
            &2,
            Spec.Notice,
            Spec.Node.get_changes(s, k, None{}),
            Spec.Node.get_changes(Pair.fst(St, Spec.Answer, _), k, Some{Spec.Node.position(s)})
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
      Spec.Node.ask(Pair.fst(St, Spec.Answer, _), Spec.Envelope{r, w, t2}, q) == _: St & Spec.Answer
    }
    Equal.trans(
      St & Spec.Answer,
      Spec.Node.ask(
        Pair.fst(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q)),
        Spec.Envelope{r, w, t2},
        q
      ),
      (
        Pair.fst(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q)),
        Pair.snd(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q))
      ),
      Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q),
      asked_found(
        Tables.Table.get(
          Seen,
          St.seen(Pair.fst(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q))),
          r
        ),
        Pair.fst(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q)),
        r,
        w,
        t2,
        q,
        Pair.snd(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q))
      )(seen_after_ask(s, r, w, t1, q)),
      Lists.Pair.eta(St, Spec.Answer, Spec.Node.ask(s, Spec.Envelope{r, w, t1}, q))
    )

def Spec.history_kept(s, e, q, t, a, n, v, x):
  match e:
    case Spec.Envelope{+r, w, z}:
      h1 => h2 =>
        +s = s
        +q = q
        +n = n
        +v = v
        +x = x
        %h1: {
          St.content(
            Pair.fst(St, Spec.Answer, _),
            n,
            Spec.Point.At{v}
          )
            == Some{x}: Maybe<&2, List<&2, U32>>
        }
        kept_asked(Tables.Table.get(Seen, St.seen(s), r), s, r, w, z, q, n, v, x)(h2)

def Spec.none_inside_itself_at_start(n, g):
  {==}

def Spec.write_at_head_is_written(s, r, w, time, n, b, v, x):
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
      St,
      Spec.Answer,
      Spec.Node.ask(
        s,
        Spec.Envelope{r, w, time},
        Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
      )
    ),
    (
      r,
      ho => hh => +hn => Equal.trans(
        St & Spec.Answer,
        Spec.Node.ask(
          s,
          Spec.Envelope{r, w, time},
          Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
        ),
        (
          Pair.fst(
            St,
            Spec.Answer,
            Spec.Node.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
            )
          ),
          Pair.snd(
            St,
            Spec.Answer,
            Spec.Node.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
            )
          )
        ),
        (
          Pair.fst(
            St,
            Spec.Answer,
            Spec.Node.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
            )
          ),
          Spec.Answer.Write{Spec.Write.Written{r}}
        ),
        Equal.sym(
          St & Spec.Answer,
          (
            Pair.fst(
              St,
              Spec.Answer,
              Spec.Node.ask(
                s,
                Spec.Envelope{r, w, time},
                Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
              )
            ),
            Pair.snd(
              St,
              Spec.Answer,
              Spec.Node.ask(
                s,
                Spec.Envelope{r, w, time},
                Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
              )
            )
          ),
          Spec.Node.ask(
            s,
            Spec.Envelope{r, w, time},
            Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
          ),
          Lists.Pair.eta(
            St,
            Spec.Answer,
            Spec.Node.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
            )
          )
        ),
        Equal.cong(
          Spec.Answer,
          St & Spec.Answer,
          y => (
            Pair.fst(
              St,
              Spec.Answer,
              Spec.Node.ask(
                s,
                Spec.Envelope{r, w, time},
                Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
              )
            ),
            y
          ),
          Pair.snd(
            St,
            Spec.Answer,
            Spec.Node.ask(
              s,
              Spec.Envelope{r, w, time},
              Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}
            )
          ),
          Spec.Answer.Write{Spec.Write.Written{r}},
          (
            %Equal.sym(Maybe<&2, Seen>, Tables.Table.get(Seen, St.seen(s), r), None{}, new_found(s, r)(hn)): {Pair.snd(St, Spec.Answer, Node.asked(_, s, r, w, time, Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}})) == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
            %Equal.sym(Spec.Answer, Pair.snd(St, Spec.Answer, Node.applied(s, r, Step.of(s, r, w, time, Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}))), Out.answer(Step.of(s, r, w, time, Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}})), answer_after_applied(s, r, Step.of(s, r, w, time, Spec.Ask.Write{n, b, Some{v}, Spec.Content.Bytes{x}}))): {_ == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
            %Equal.sym(Bool, Ver.taken(St.versions(s), r), False{}, new_free(s, r)(hn)): {Out.answer(Write.free(_, s, r, w, time, n, b, Some{v}, x)) == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
            write_on_head(Tables.Table.get(Br, St.branches(s), b), s, r, w, time, n, b, v, x)(hh)(ho))
        )
      )
    )
  )

def Spec.read_after_write(s, e, n, b, base, x, t, v):
  match e:
    case Spec.Envelope{+r, +w, +z}:
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
          Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
          t,
          Spec.Answer.Write{Spec.Write.Written{v}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(hn)(h)
        ):
          {St.content(_, n, Spec.Point.Head{b}) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.sym(
          Tables.Table<Ver>,
          St.versions(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                s,
                r,
                Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
              )
            )
          ),
          Ver.add(
            Out.versions(Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})),
            St.versions(s)
          ),
          versions_after_applied(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
          )
        ):
          {
            Blob.find.of(
              Ver.blobs.of(
                Ver.find.of(
                  _,
                  Br.head.of(
                    Tables.Table.get(
                      Br,
                      St.branches(
                        Pair.fst(
                          St,
                          Spec.Answer,
                          Node.applied(
                            s,
                            r,
                            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
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
          Tables.Table<Br>,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(
                s,
                r,
                Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
              )
            )
          ),
          Out.branches(Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})),
          branches_after_applied(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
          )
        ):
          {
            Blob.find.of(
              Ver.blobs.of(
                Ver.find.of(
                  Ver.add(
                    Out.versions(
                      Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}})
                    ),
                    St.versions(s)
                  ),
                  Br.head.of(Tables.Table.get(Br, _, b))
                )
              ),
              n
            )
              == Some{x}: Maybe<&2, List<&2, U32>>
          }
        raw_free(
          Ver.taken(St.versions(s), r),
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
            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}}),
            t,
            Spec.Answer.Write{Spec.Write.Written{v}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.Write{n, b, base, Spec.Content.Bytes{x}},
              t,
              Spec.Answer.Write{Spec.Write.Written{v}}
            )(hn)(h)
          )
        )

def Spec.stale_changes_nothing(s, e, n, b, base, x, t, current):
  match e:
    case Spec.Envelope{+r, +w, +z}:
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
          Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, x}),
          t,
          Spec.Answer.Write{Spec.Write.Stale{current}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.Write{n, b, base, x},
            t,
            Spec.Answer.Write{Spec.Write.Stale{current}}
          )(hn)(h)
        ):
          Spec.Node.SameContent(_, s) & {base != Some{current}: Maybe<&2, String>}
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
            Step.of(s, r, w, z, Spec.Ask.Write{n, b, base, x}),
            t,
            Spec.Answer.Write{Spec.Write.Stale{current}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.Write{n, b, base, x},
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
          Spec.Node.SameContent(
            _,
            s
          )
            & {
              Spec.Node.get_changes(
                _,
                Spec.Topic.Conflicts{b},
                Some{Spec.Node.position(s)}
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
            & {Br.epoch.of(Tables.Table.get(Br, St.branches(_), b)) == Some{new}: Maybe<&2, Nat>}
        %Equal.sym(
          Tables.Table<Br>,
          St.branches(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}))
            )
          ),
          Out.branches(Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g})),
          branches_after_applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetOwner{b, g}))
        ):
          {
            Nat.is_lt(old, new) == True{}: Bool
          }
            & {Br.epoch.of(Tables.Table.get(Br, _, b)) == Some{new}: Maybe<&2, Nat>}
        set_owner_lemma(
          Tables.Table.get(Br, St.branches(s), b),
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

def Spec.inside_after_set(s, e, g, m, ms, t, x):
  match e:
    case Spec.Envelope{+r, +w, +z}:
      +hn => +h =>
        +s = s
        +g = g
        +m = m
        +ms = ms
        +t = t
        +x = x
        %applied_state(
          s,
          r,
          Step.of(s, r, w, z, Spec.Ask.SetGroup{g, m <> ms}),
          t,
          Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
        )(
          ask_step(
            s,
            r,
            w,
            z,
            Spec.Ask.SetGroup{g, m <> ms},
            t,
            Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
          )(hn)(h)
        ):
          {Grp.inside(St.groups(_), m, g) == True{}: Bool}
        %Equal.sym(
          Tables.Table<Grp>,
          St.groups(
            Pair.fst(
              St,
              Spec.Answer,
              Node.applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, m <> ms}))
            )
          ),
          Out.groups(Step.of(s, r, w, z, Spec.Ask.SetGroup{g, m <> ms})),
          groups_after_applied(s, r, Step.of(s, r, w, z, Spec.Ask.SetGroup{g, m <> ms}))
        ):
          {Grp.inside(_, m, g) == True{}: Bool}
        sg_on(
          Cycle.has(St.groups(s), g, m <> ms),
          s,
          g,
          m,
          ms,
          x
        )(
          applied_answer(
            s,
            r,
            Step.of(s, r, w, z, Spec.Ask.SetGroup{g, m <> ms}),
            t,
            Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
          )(
            ask_step(
              s,
              r,
              w,
              z,
              Spec.Ask.SetGroup{g, m <> ms},
              t,
              Spec.Answer.SetGroup{Spec.SetGroup.Set{x}}
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
        %sync_state(b, a1, r2, w2, z2, b1)(hn2)(h2): Spec.Node.SameContent(a1, _)
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
        ): Spec.Node.SameContent(
          _,
          Pair.fst(St, Spec.Answer, Node.applied(b, r2, Sync.go(False{}, b, _)))
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
          Tables.Table.get(Seen, St.seen(s1), r2),
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
        %sync_state(s1, b, r2, w2, z2, s2)(hn2)(h2): Spec.Node.SameContent(_, s4)
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
        ): Spec.Node.SameContent(
          Pair.fst(St, Spec.Answer, Node.applied(s1, r2, Sync.go(False{}, s1, b))),
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
        ): Spec.Node.SameContent(
          Pair.fst(St, Spec.Answer, Node.applied(_, r2, Sync.go(False{}, _, b))),
          Pair.fst(St, Spec.Answer, Node.applied(s3, r4, Sync.go(False{}, s3, a)))
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
        ): Spec.Node.SameContent(
          Pair.fst(
            St,
            Spec.Answer,
            Node.applied(
              Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
              r2,
              Sync.go(
                False{},
                Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))),
                b
              )
            )
          ),
          Pair.fst(St, Spec.Answer, Node.applied(_, r4, Sync.go(False{}, _, a)))
        )
        comm_core(s, a, b, r1, r2, r3, r4)((
            %Equal.sym(St, Pair.fst(St, Spec.Answer, Node.applied(s, r1, Sync.go(False{}, s, a))), s1, sync_state(s, a, r1, w1, z1, s1)(hn1)(h1)): {Sync.collides(Tables.Table.keys(Ver, St.versions(b)), St.versions(b), St.versions(_)) == False{}: Bool}
            sync_clean(s1, b, r2, w2, z2, s2)(hn2)(h2)))

def Spec.inside_through(s, m, h, g):
  Reaches.Reach.in_through(
    ~Spec.Member,
    ~Tables.Table<Grp>,
    ~Member.same,
    ~Grp.members.of,
    ~Grp.all,
    ~member_same_refl,
    ~member_same_sound,
    ~grp_live,
    St.groups(s),
    Spec.Member.Group{g},
    Spec.Member.Group{h},
    m
  )

def Spec.none_inside_itself_after(s, e, q, t, a, g):
  match e:
    case Spec.Envelope{+r, w, z}:
      h => hg =>
        +s = s
        nia_asked(
          Tables.Table.get(Seen, St.seen(s), r),
          s,
          r,
          w,
          z,
          q,
          t,
          a,
          g
        )(h)(acyc_all(St.groups(s))(hg))

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
  match e1 e2 e3 e4:
    case Spec.Envelope{
      r1,
      w1,
      z1
    } Spec.Envelope{r2, w2, z2} Spec.Envelope{r3, w3, z3} Spec.Envelope{+r4, w4, z4}:
      (
        r4,
        hn1 => hn2 => hn3 => hn4 => hne => h1 => h2 => h3 => h4 =>
          +s = s
          +b = b
          +v0 = v0
          +n1 = n1
          +n2 = n2
          mdk_split(Tables.Table.get(Br, St.branches(s), b), Tables.Table.get(Ver, St.versions(s), v0), s, s1, s2, s3, s4, a4, r1, w1, z1, r2, w2, z2, r3, w3, z3, r4, w4, z4, b, c, n1, n2, base1, base2, x1, x2, v0, v1, v2)({==})({==})(hn1)(hn2)(hn3)(hn4)(neq_str(n1, n2)(hne))(h1)(h2)(h3)(h4))
