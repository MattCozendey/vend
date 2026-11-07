import Base
import ../../shared/bools.bend as Bools
import ../../shared/bytes.bend as Octets
import ../../shared/cmps.bend as Cmps
import ../../shared/lists.bend as Lists
import ../../shared/maybes.bend as Maybes
import ../../shared/nats.bend as Nats
import ../../shared/orders.bend as Orders
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

# one level of a search: whether m is in it, and the members of its groups
type Level is Data:
  Level{found: Bool, next: List<&2, Spec.Member>}

# the level l, with one more member: whether it is m (hit), and its own
# members (ms)
def Level.add(hit: Bool, ms: List<&2, Spec.Member>, l: Level) -> Level:
  match l:
    case Level{found, next}:
      Level{Bool.or(hit, found), List.append(&2, Spec.Member, ms, next)}

# the level xs: m is one of them, and the members of the groups among them
def Level.of(xs: List<&2, Spec.Member>, +gs: Tables.Table<Grp>, +m: Spec.Member) -> Level:
  match xs:
    case Nil{}:
      Level{False{}, []}
    case Con{+x, r}:
      Level.add(Member.same(x, m), Grp.members.of(gs, x), Level.of(r, gs, m))

def Level.found(l: Level) -> Bool:
  match l:
    case Level{found, next}:
      found

def Level.next(l: Level) -> List<&2, Spec.Member>:
  match l:
    case Level{found, next}:
      next

# m is in the level xs, or in a level below it: one level per step of the fuel
# f
def Inside.go(f: Nat, xs: List<&2, Spec.Member>, +gs: Tables.Table<Grp>, +m: Spec.Member) -> Bool:
  match f:
    case 0n:
      Level.found(Level.of(xs, gs, m))
    case 1n+g:
      +l = Level.of(xs, gs, m)
      Bool.or(Level.found(l), Inside.go(g, Level.next(l), gs, m))

# m is inside the group g of gs: a member of g, or of a group inside g; as
# deep as gs has groups
def Grp.inside(+gs: Tables.Table<Grp>, m: Spec.Member, g: String) -> Bool:
  Inside.go(
    List.length(&2, String, Tables.Table.keys(Grp, gs)),
    Grp.members.of(gs, Spec.Member.Group{g}),
    gs,
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
      Write.free(Ver.has(St.versions(s), r), s, r, w, t, n, b, base, y)

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
      SetBranch.on(Owner.of(s, br), Ver.has(St.versions(s), r), s, r, w, t, b, bs, br)

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

# the member x is the group g, or a group with g inside it
def Cycle.at(gs: Tables.Table<Grp>, +g: String, x: Spec.Member) -> Bool:
  match x:
    case Spec.Member.Node{n}:
      False{}
    case Spec.Member.Group{+h}:
      Bool.or(String.eq(h, g), Grp.inside(gs, Spec.Member.Group{g}, h))

# the epoch that the group g gets when it is set next
def Grp.epoch.next(gs: Tables.Table<Grp>, g: String) -> Nat:
  1n+Grp.epoch.of(Tables.Table.get(Grp, gs, g))

# a member of ms is the group g, or a group with g inside it
def Cycle.has(+gs: Tables.Table<Grp>, +g: String, ms: List<&2, Spec.Member>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{x, r}:
      Bool.or(Cycle.at(gs, g, x), Cycle.has(gs, g, r))

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
      Maybes.Maybe.if(String, i, u => Vers.first_in(r, ks), Strings.has(ks, i))

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
      Merge.owner(Owner.of(s, br), Ver.has(St.versions(s), r), s, r, w, t, f, b, br)

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
            Strings.drop(l, n),
            Ver.has(St.versions(s), r),
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
      Lists.List.cons_if(
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
      Lists.List.cons_if(Spec.Notice, n, Logged.pick(k, r), Topic.same(t, k))

# the versions of vs that hold the resource n
def Log.of(vs: List<&2, Tables.Row<Ver>>, +n: String) -> List<&2, Tables.Row<Ver>>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{Tables.Row{i, Ver{+b, p, a, t}}, r}:
      Lists.List.cons_if(
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
    Ver.has(St.versions(s), r),
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
          Lists.List.cons_if(
            Spec.Notice,
            n,
            _,
            Topic.same(t, k)
          )
            == List.append(
              &2,
              Spec.Notice,
              Lists.List.cons_if(Spec.Notice, n, Logged.pick(k, r), Topic.same(t, k)),
              Logged.pick(k, ys)
            ): List<&2, Spec.Notice>
        }
      Lists.List.cons_if_append(
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
          Bools.Bool.false_ne_true(
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
      {Ver.has(St.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, St.seen(s), r),
        Ver.has(St.versions(s), r),
        List.length(&2, Logged, St.log(s))
      )(h)
    )

# no version has the ID of a new request
law new_free:
  for s: St
  for r: String
  {
    Spec.Node.get_outcome(s, r) == Spec.Outcome.NotSeen{}: Spec.Outcome
  } -> {Ver.has(St.versions(s), r) == False{}: Bool}

def new_free(s, r):
  h =>
    +s = s
    +r = r
    Pair.snd(
      {Tables.Table.get(Seen, St.seen(s), r) == None{}: Maybe<&2, Seen>},
      {Ver.has(St.versions(s), r) == False{}: Bool},
      outcome_new(
        Tables.Table.get(Seen, St.seen(s), r),
        Ver.has(St.versions(s), r),
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
    Ver.has(St.versions(s), r) == False{}: Bool
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
        Bools.Bool.false_ne_true(
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
          )(hh)
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
    Ver.has(St.versions(s), r) == False{}: Bool
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
        Bools.Bool.false_ne_true(
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
    Ver.has(St.versions(s), r) == False{}: Bool
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
        Bools.Bool.false_ne_true(
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
          )(hh)
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
    Ver.has(St.versions(s), r) == taken: Bool
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
          heq => Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
      stale_free(Ver.has(St.versions(s), r), s, r, w, z, n, b, base, y, cur)

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
        Bools.Bool.false_ne_true(
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
              {Lists.List.cons_if(Spec.Notice, Spec.Notice.Conflicted{r}, [], _) == [Spec.Notice.Conflicted{k}]: List<&2, Spec.Notice>}
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Bools.Bool.false_ne_true(
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
        Ver.has(St.versions(s), r),
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
        Bools.Bool.false_ne_true(
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
          Bools.Bool.false_ne_true(
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

# a level with a member that is m holds m
law found_add_true:
  for ms: List<&2, Spec.Member>
  for l: Level
  {Level.found(Level.add(True{}, ms, l)) == True{}: Bool}

def found_add_true(ms, l):
  match l:
    case Level{f, n}:
      {==}

# a level that starts with m holds m
law level_head:
  for m: Spec.Member
  for ms: List<&2, Spec.Member>
  for gs: Tables.Table<Grp>
  {Level.found(Level.of(m <> ms, gs, m)) == True{}: Bool}

def level_head(m, ms, gs):
  +m = m
  +gs = gs
  %Equal.sym(Bool, Member.same(m, m), True{}, member_same_refl(m)):
    {Level.found(Level.add(_, Grp.members.of(gs, m), Level.of(ms, gs, m))) == True{}: Bool}
  found_add_true(Grp.members.of(gs, m), Level.of(ms, gs, m))

# a search that starts with m finds m
law inside_head:
  for f: Nat
  for m: Spec.Member
  for ms: List<&2, Spec.Member>
  for gs: Tables.Table<Grp>
  {Inside.go(f, m <> ms, gs, m) == True{}: Bool}

def inside_head(f, m, ms, gs):
  match f:
    case 0n:
      level_head(m, ms, gs)
    case 1n+g:
      %Equal.sym(Bool, Level.found(Level.of(m <> ms, gs, m)), True{}, level_head(m, ms, gs)):
        {Bool.or(_, Inside.go(g, Level.next(Level.of(m <> ms, gs, m)), gs, m)) == True{}: Bool}
      {==}

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
          Bools.Bool.false_ne_true(
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
            Inside.go(
              List.length(
                &2,
                String,
                Tables.Table.keys(
                  Grp,
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
        inside_head(
          List.length(
            &2,
            String,
            Tables.Table.keys(
              Grp,
              Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)})
            )
          ),
          m,
          ms,
          Tables.Table.set(Grp, St.groups(s), g, Grp{m <> ms, Grp.epoch.next(St.groups(s), g)})
        )

# a sync that answers Synced found no collision
law sync_free:
  for c: Bool
  for a: St
  for o: St
  {Out.answer(Sync.go(c, a, o)) == Spec.Answer.Sync{Spec.Sync.Synced{}} : Spec.Answer} -> {c == False{} : Bool}

def sync_free(c, a, o):
  match c:
    case True{}:
      h => Empty.absurd({True{} == False{} : Bool}, Bools.Bool.false_ne_true(Answer.clash(Spec.Answer.Sync{Spec.Sync.Refused{"version ID collision"}}, Spec.Answer.Sync{Spec.Sync.Synced{}}, h)))
    case False{}:
      h => {==}

# m, else nothing, is m
law or_none:
  for m: Maybe<&2, Ver>
  {Maybe.or(&2, Ver, m, None{}) == m : Maybe<&2, Ver>}

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
  {Tables.Table.get(Ver, vs, k) == m : Maybe<&2, Ver>} -> {Ver.has(vs, k) == False{} : Bool} -> {Tables.Table.get(Ver, vs, k) == None{} : Maybe<&2, Ver>}

def has_false_find.of(m, vs, k):
  match m:
    case None{}:
      hm => hh => hm
    case Some{u}:
      +hm => hh =>
        +vs = vs
        +k = k
        Empty.absurd(
          {Tables.Table.get(Ver, vs, k) == None{} : Maybe<&2, Ver>},
          Bools.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, Equal.trans(Bool, True{}, Ver.has(vs, k), False{}, Equal.sym(Bool, Ver.has(vs, k), True{}, Equal.cong(Maybe<&2, Ver>, Bool, x => Maybe.is_some(&2, Ver, x), Tables.Table.get(Ver, vs, k), Some{u}, hm)), hh)))
        )

# a version that a list does not hold is not found in it
law has_false_find:
  for vs: Tables.Table<Ver>
  for k: String
  {Ver.has(vs, k) == False{} : Bool} -> {Tables.Table.get(Ver, vs, k) == None{} : Maybe<&2, Ver>}

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
  {Tables.Table.get(Ver, ys, k) == m : Maybe<&2, Ver>} -> {Ver.has(ys, i) == True{} : Bool} -> {String.eq(i, k) == True{} : Bool} -> {Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Some{x}) : Maybe<&2, Ver>}

def add_find.held.of(m, i, x, r, ys, k):
  match m:
    case Some{u}:
      hm => hh => he =>
        %Equal.sym(Maybe<&2, Ver>, Tables.Table.get(Ver, ys, k), Some{u}, hm) : {Maybe.or(&2, Ver, _, Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, _, Some{x}) : Maybe<&2, Ver>}
        {==}
    case None{}:
      +hm => +hh => he =>
        +ys = ys
        +i = i
        +k = k
        Empty.absurd(
          {Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Some{x}) : Maybe<&2, Ver>},
          Bools.Bool.false_ne_true(
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
                Equal.sym(Bool, Ver.has(ys, k), False{}, Equal.cong(Maybe<&2, Ver>, Bool, z => Maybe.is_some(&2, Ver, z), Tables.Table.get(Ver, ys, k), None{}, hm)),
                Equal.cong(String, Bool, z => Ver.has(ys, z), k, i, Equal.sym(String, i, k, Strings.String.eq_sound(i, k)(he)))
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
  {Ver.has(ys, i) == True{} : Bool} -> {String.eq(i, k) == hit : Bool} -> {Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.find_row(Ver, r, k))) : Maybe<&2, Ver>}

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
  {Ver.has(ys, i) == False{} : Bool} -> {String.eq(i, k) == hit : Bool} -> {Maybe.or(&2, Ver, Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.get(Ver, ys, k)), Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Bools.Bool.when(Maybe<&2, Ver>, hit, u => Some{x}, u => Tables.Table.find_row(Ver, r, k))) : Maybe<&2, Ver>}

def add_find.fresh(hit, i, x, r, ys, k):
  match hit:
    case False{}:
      hh => he => {==}
    case True{}:
      hh => he =>
        +ys = ys
        +k = k
        +i = i
        %Equal.sym(Maybe<&2, Ver>, Tables.Table.get(Ver, ys, k), None{}, has_false_find(ys, k)(Equal.trans(Bool, Ver.has(ys, k), Ver.has(ys, i), False{}, Equal.cong(String, Bool, z => Ver.has(ys, z), k, i, Equal.sym(String, i, k, Strings.String.eq_sound(i, k)(he))), hh))) :
          {Some{x} == Maybe.or(&2, Ver, _, Some{x}) : Maybe<&2, Ver>}
        {==}

# add_find, for the first new version, under i
law add_find.one:
  for held: Bool
  for i: String
  for x: Ver
  for r: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {Ver.has(ys, i) == held : Bool} -> {Maybe.or(&2, Ver, Tables.Table.get(Ver, Ver.add.put(i, x, ys, held), k), Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, Tables.Row{i, x} <> r, k)) : Maybe<&2, Ver>}

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
        %Equal.sym(Maybe<&2, Ver>, Tables.Table.get(Ver, Tables.Table.set(Ver, ys, i, x), k), Bools.Bool.when(Maybe<&2, Ver>, String.eq(i, k), u => Some{x}, u => Tables.Table.get(Ver, ys, k)), Tables.Table.get_set(Ver, ys, i, x, k)) :
          {Maybe.or(&2, Ver, _, Tables.Table.find_row(Ver, r, k)) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Bools.Bool.when(Maybe<&2, Ver>, String.eq(i, k), u => Some{x}, u => Tables.Table.find_row(Ver, r, k))) : Maybe<&2, Ver>}
        add_find.fresh(String.eq(i, k), i, x, r, ys, k)(hh)({==})

# a version found after versions are added: the old one when held, else the
# first new one
law add_find:
  for xs: List<&2, Tables.Row<Ver>>
  for ys: Tables.Table<Ver>
  for k: String
  {Tables.Table.get(Ver, Ver.add(xs, ys), k) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, xs, k)) : Maybe<&2, Ver>}

def add_find(xs, ys, k):
  match xs:
    case Nil{}:
      Equal.sym(Maybe<&2, Ver>, Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), None{}), Tables.Table.get(Ver, ys, k), or_none(Tables.Table.get(Ver, ys, k)))
    case Con{Tables.Row{+i, +x}, +r}:
      +ys = ys
      +k = k
      Equal.trans(
        Maybe<&2, Ver>,
        Tables.Table.get(Ver, Ver.add(r, Ver.add.one(Tables.Row{i, x}, ys)), k),
        Maybe.or(&2, Ver, Tables.Table.get(Ver, Ver.add.one(Tables.Row{i, x}, ys), k), Tables.Table.find_row(Ver, r, k)),
        Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.find_row(Ver, Tables.Row{i, x} <> r, k)),
        add_find(r, Ver.add.one(Tables.Row{i, x}, ys), k),
        add_find.one(Ver.has(ys, i), i, x, r, ys, k)({==})
      )

# after a sync, a version is the own one when held, else the other node's
law sync_find:
  for o: Tables.Table<Ver>
  for ys: Tables.Table<Ver>
  for k: String
  {Tables.Table.get(Ver, Ver.add(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys), k) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), Tables.Table.get(Ver, o, k)) : Maybe<&2, Ver>}

def sync_find(o, ys, k):
  +o = o
  +ys = ys
  +k = k
  %Tables.Table.rows_find_keys(Ver, o, k) :
    {Tables.Table.get(Ver, Ver.add(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys), k) == Maybe.or(&2, Ver, Tables.Table.get(Ver, ys, k), _) : Maybe<&2, Ver>}
  add_find(Tables.Table.rows(Ver, Tables.Table.keys(Ver, o), o), ys, k)

# a sync that finds no collision found none at each key it walked
law collides_at.at:
  for hit: Bool
  for j: String
  for r: List<&2, String>
  for os: Tables.Table<Ver>
  for vs: Tables.Table<Ver>
  for k: String
  ({Sync.collides(r, os, vs) == False{} : Bool} -> {Strings.has(r, k) == True{} : Bool} -> {Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{} : Bool}) -> {String.eq(j, k) == hit : Bool} -> {Bool.or(Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)), Sync.collides(r, os, vs)) == False{} : Bool} -> {List.any.if(u => Strings.has(r, k), hit) == True{} : Bool} -> {Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{} : Bool}

def collides_at.at(hit, j, r, os, vs, k):
  match hit:
    case False{}:
      ih => he => +hc => hn =>
        +j = j
        +os = os
        +vs = vs
        ih(Bools.Bool.or_false_right(Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)), Sync.collides(r, os, vs))(hc))(hn)
    case True{}:
      ih => he => +hc => hn =>
        +j = j
        +k = k
        +os = os
        +vs = vs
        %Strings.String.eq_sound(j, k)(he) : {Sync.clash.at(Tables.Table.get(Ver, vs, _), Tables.Table.get(Ver, os, _)) == False{} : Bool}
        Bools.Bool.or_false_left(Sync.clash.at(Tables.Table.get(Ver, vs, j), Tables.Table.get(Ver, os, j)), Sync.collides(r, os, vs))(hc)

law collides_at:
  for ks: List<&2, String>
  for os: Tables.Table<Ver>
  for vs: Tables.Table<Ver>
  for k: String
  {Sync.collides(ks, os, vs) == False{} : Bool} -> {Strings.has(ks, k) == True{} : Bool} -> {Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{} : Bool}

def collides_at(ks, os, vs, k):
  match ks:
    case Nil{}:
      hc => hn => Empty.absurd({Sync.clash.at(Tables.Table.get(Ver, vs, k), Tables.Table.get(Ver, os, k)) == False{} : Bool}, Bools.Bool.false_ne_true(hn))
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
          @n: String -> {Blob.find.of(Ver.blobs.of(Some{u}), n) == Blob.find.of(Ver.blobs.of(Some{v}), n) : Maybe<&2, List<&2, U32>>}

# compat_of, by the own lookup ma, once the other one found v
law compat_mine:
  for ma: Maybe<&2, Ver>
  for v: Ver
  {Sync.clash.at(ma, Some{v}) == False{} : Bool} -> Compat(Some{v}, ma)

def compat_mine(ma, v):
  match ma v:
    case None{} y:
      h => Unit{}
    case Some{Ver{+ub, up, ua, ut}} Ver{+vb, vp, va, vt}:
      +h =>
        n => Tables.Table.same_sound(~List<&2, U32>, ~Octets.Bytes.is_eq, x => y => Octets.Bytes.is_eq_sound(x, y), ub, vb, n)(Bools.Bool.not_false(Tables.Table.same(~List<&2, U32>, ~Octets.Bytes.is_eq, ub, vb))(h))

# compat_of, by the other lookup mb
law compat_of.at:
  for mb: Maybe<&2, Ver>
  for bs: Tables.Table<Ver>
  for as: Tables.Table<Ver>
  for k: String
  {Tables.Table.get(Ver, bs, k) == mb : Maybe<&2, Ver>} -> {Sync.collides(Tables.Table.keys(Ver, bs), bs, as) == False{} : Bool} -> Compat(mb, Tables.Table.get(Ver, as, k))

def compat_of.at(mb, bs, as, k):
  match mb:
    case None{}:
      hm => hc => Unit{}
    case Some{+v}:
      +hm => hc =>
        +bs = bs
        +as = as
        +k = k
        compat_mine(Tables.Table.get(Ver, as, k), v)(
          (
            %hm : {Sync.clash.at(Tables.Table.get(Ver, as, k), _) == False{} : Bool}
            collides_at(Tables.Table.keys(Ver, bs), bs, as, k)(hc)(
              Equal.trans(Bool, Strings.has(Tables.Table.keys(Ver, bs), k), Maybe.is_some(&2, Ver, Tables.Table.get(Ver, bs, k)), True{}, Tables.Table.keys_get(Ver, bs, k), Equal.cong(Maybe<&2, Ver>, Bool, z => Maybe.is_some(&2, Ver, z), Tables.Table.get(Ver, bs, k), Some{v}, hm))
            )
          )
        )

# when a sync found no collision, versions under the same ID hold the same
# bytes for each resource
law compat_of:
  for bs: Tables.Table<Ver>
  for as: Tables.Table<Ver>
  for k: String
  {Sync.collides(Tables.Table.keys(Ver, bs), bs, as) == False{} : Bool} -> Compat(Tables.Table.get(Ver, bs, k), Tables.Table.get(Ver, as, k))

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
  Compat(mb, ma) -> {Blob.find.of(Ver.blobs.of(Maybe.or(&2, Ver, ma, mb)), n) == Blob.find.of(Ver.blobs.of(Maybe.or(&2, Ver, mb, Maybe.or(&2, Ver, ma, mb))), n) : Maybe<&2, List<&2, U32>>}

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
  {Br.stamp.cmp(x, x) == EQ{} : Cmp}

def stamp_refl(x):
  match x:
    case Br{+h, o, +e, +c}:
      %Equal.sym(Cmp, Nat.cmp(e, e), EQ{}, Nats.Nat.cmp_refl(e)) :
        {Cmps.Cmp.then(_, Cmps.Cmp.then(Nat.cmp(c, c), String.order(h, h))) == EQ{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(c, c), EQ{}, Nats.Nat.cmp_refl(c)) :
        {Cmps.Cmp.then(EQ{}, Cmps.Cmp.then(_, String.order(h, h))) == EQ{} : Cmp}
      Strings.String.order_refl(h)

# comparing stamps the other way round flips the order
law stamp_swap:
  for x: Br
  for y: Br
  {Br.stamp.cmp(y, x) == Cmps.Cmp.flip(Br.stamp.cmp(x, y)) : Cmp}

def stamp_swap(x, y):
  match x y:
    case Br{+h1, o1, +e1, +c1} Br{+h2, o2, +e2, +c2}:
      %Equal.sym(Cmp, String.order(h2, h1), Cmps.Cmp.flip(String.order(h1, h2)), Strings.String.order_swap(h1, h2, EQ{})) :
        {Cmps.Cmp.then(Nat.cmp(e2, e1), Cmps.Cmp.then(Nat.cmp(c2, c1), _)) == Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))) : Cmp}
      %Equal.sym(Cmp, Nat.cmp(c2, c1), Cmps.Cmp.flip(Nat.cmp(c1, c2)), Nats.Nat.cmp_swap(c1, c2)) :
        {Cmps.Cmp.then(Nat.cmp(e2, e1), Cmps.Cmp.then(_, Cmps.Cmp.flip(String.order(h1, h2)))) == Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))) : Cmp}
      %Equal.sym(Cmp, Nat.cmp(e2, e1), Cmps.Cmp.flip(Nat.cmp(e1, e2)), Nats.Nat.cmp_swap(e1, e2)) :
        {Cmps.Cmp.then(_, Cmps.Cmp.then(Cmps.Cmp.flip(Nat.cmp(c1, c2)), Cmps.Cmp.flip(String.order(h1, h2)))) == Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))) : Cmp}
      %Equal.sym(Cmp, Cmps.Cmp.then(Cmps.Cmp.flip(Nat.cmp(c1, c2)), Cmps.Cmp.flip(String.order(h1, h2))), Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2))), Cmps.Cmp.then_flip(Nat.cmp(c1, c2), String.order(h1, h2))) :
        {Cmps.Cmp.then(Cmps.Cmp.flip(Nat.cmp(e1, e2)), _) == Cmps.Cmp.flip(Cmps.Cmp.then(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))) : Cmp}
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
  {Br.stamp.cmp(x, y) == EQ{} : Cmp} -> {Br.head(x) == Br.head(y) : String}

def stamp_eq_head(x, y):
  match x y:
    case Br{+h1, o1, +e1, +c1} Br{+h2, o2, +e2, +c2}:
      h => Strings.String.order_sound(h1, h2)(Cmps.Cmp.then_eq_right(Nat.cmp(c1, c2), String.order(h1, h2))(Cmps.Cmp.then_eq_right(Nat.cmp(e1, e2), Cmps.Cmp.then(Nat.cmp(c1, c2), String.order(h1, h2)))(h)))

# the head of the branch that m holds is its head mapped
law head_of_map:
  for m: Maybe<&2, Br>
  {Br.head.of(m) == Maybe.map(&2, Br, String, y => Br.head(y), m) : Maybe<&2, String>}

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
  {Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)) == Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))) : Maybe<&2, String>}

def hb_conv(ma, mb):
  +ma = ma
  +mb = mb
  %Equal.sym(Maybe<&2, String>, Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)), Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)), head_of_map(Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))) :
    {_ == Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))) : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, String>, Br.head.of(Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))), Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb))), head_of_map(Orders.Order.join(~Br, ~Br.stamp.cmp, mb, Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)))) :
    {Maybe.map(&2, Br, String, y => Br.head(y), Orders.Order.join(~Br, ~Br.stamp.cmp, ma, mb)) == _ : Maybe<&2, String>}
  Orders.Order.join_conv(~Br, ~String, ~Br.stamp.cmp, ~Br.head, y => stamp_refl(y), a => b => stamp_swap(a, b), a => b => stamp_eq_head(a, b), ma, mb)

# a branch looked up after a branch t of another node met it, when the step
# is for the name looked up (hit)
def Brs.step(hit: Bool, f: Maybe<&2, Br>, m: Maybe<&2, Br>) -> Maybe<&2, Br>:
  match hit:
    case False{}:
      m
    case True{}:
      Orders.Order.join(~Br, ~Br.stamp.cmp, m, f)

# the branch named c after each branch of ks in full met m
def Brs.fold(ks: List<&2, String>, +full: Tables.Table<Br>, +c: String, m: Maybe<&2, Br>) -> Maybe<&2, Br>:
  match ks:
    case Nil{}:
      m
    case Con{+k, r}:
      Brs.fold(r, full, c, Brs.step(String.eq(k, c), Tables.Table.get(Br, full, k), m))

# a step with no branch found changes nothing
law brs_step_none:
  for hit: Bool
  for m: Maybe<&2, Br>
  {Brs.step(hit, None{}, m) == m : Maybe<&2, Br>}

def brs_step_none(hit, m):
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# a new branch t of another node, under the key k, where the node had none
law at_new:
  for hit: Bool
  for bs: Tables.Table<Br>
  for k: String
  for t: Br
  for c: String
  {String.eq(k, c) == hit : Bool} -> {Tables.Table.get(Br, bs, k) == None{} : Maybe<&2, Br>} -> {Bools.Bool.when(Maybe<&2, Br>, hit, u => Some{t}, u => Tables.Table.get(Br, bs, c)) == Brs.step(hit, Some{t}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}

def at_new(hit, bs, k, t, c):
  match hit:
    case False{}:
      x => x1 => {==}
    case True{}:
      x => x1 => (%Strings.String.eq_sound(k, c)(x) : {Some{t} == Some{Orders.Order.pick(Br, Br.stamp.cmp, Tables.Table.get(Br, bs, _), t)} : Maybe<&2, Br>}; (%Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, bs, k), None{}, x1) : {Some{t} == Some{Orders.Order.pick(Br, Br.stamp.cmp, _, t)} : Maybe<&2, Br>}; {==}))

# a branch t of another node that wins over the node's mine (LT)
law at_set:
  for hit: Bool
  for bs: Tables.Table<Br>
  for k: String
  for mine: Br
  for t: Br
  for c: String
  {String.eq(k, c) == hit : Bool} -> {Tables.Table.get(Br, bs, k) == Some{mine} : Maybe<&2, Br>} -> {Br.stamp.cmp(mine, t) == LT{} : Cmp} -> {Bools.Bool.when(Maybe<&2, Br>, hit, u => Some{t}, u => Tables.Table.get(Br, bs, c)) == Brs.step(hit, Some{t}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}

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
        %Strings.String.eq_sound(k, c)(he) : {Some{t} == Brs.step(True{}, Some{t}, Tables.Table.get(Br, bs, _)) : Maybe<&2, Br>}
        %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, bs, k), Some{mine}, hm) : {Some{t} == Brs.step(True{}, Some{t}, _) : Maybe<&2, Br>}
        %Equal.sym(Cmp, Br.stamp.cmp(mine, t), LT{}, hc) : {Some{t} == Some{Orders.Order.by(Br, _, mine, t)} : Maybe<&2, Br>}
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
  {String.eq(k, c) == hit : Bool} -> {Tables.Table.get(Br, bs, k) == Some{mine} : Maybe<&2, Br>} -> {Br.stamp.cmp(mine, t) == c0 : Cmp} -> {Orders.Order.by(Br, c0, mine, t) == mine : Br} -> {Tables.Table.get(Br, bs, c) == Brs.step(hit, Some{t}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}

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
        %Strings.String.eq_sound(k, c)(he) : {Tables.Table.get(Br, bs, _) == Brs.step(True{}, Some{t}, Tables.Table.get(Br, bs, _)) : Maybe<&2, Br>}
        %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, bs, k), Some{mine}, hm) : {_ == Brs.step(True{}, Some{t}, _) : Maybe<&2, Br>}
        %Equal.sym(Cmp, Br.stamp.cmp(mine, t), c0, hc) : {Some{mine} == Some{Orders.Order.by(Br, _, mine, t)} : Maybe<&2, Br>}
        %Equal.sym(Br, Orders.Order.by(Br, c0, mine, t), mine, hb) : {Some{mine} == Some{_} : Maybe<&2, Br>}
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
  {Tables.Table.get(Br, bs, k) == Some{Br{mh, mo, me, mk}} : Maybe<&2, Br>} -> {Br.stamp.cmp(Br{mh, mo, me, mk}, Br{th, to, te, tk}) == c0 : Cmp} -> {Tables.Table.get(Br, Mix.branches(Sync.pick(c0, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, vs, Mix{bs, cs, ns})), c) == Brs.step(String.eq(k, c), Some{Br{th, to, te, tk}}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}

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
        %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, Tables.Table.set(Br, bs, k, Br{th, to, te, tk}), c), Bools.Bool.when(Maybe<&2, Br>, String.eq(k, c), u => Some{Br{th, to, te, tk}}, u => Tables.Table.get(Br, bs, c)), Tables.Table.get_set(Br, bs, k, Br{th, to, te, tk}, c)) :
          {_ == Brs.step(String.eq(k, c), Some{Br{th, to, te, tk}}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}
        at_set(String.eq(k, c), bs, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, c)({==})(hm)(hc)
    case GT{}:
      hm => hc =>
        +k = k
        +c = c
        at_stay(String.eq(k, c), bs, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, c, GT{})({==})(hm)(hc)({==})
    case EQ{}:
      hm => hc =>
        +k = k
        +c = c
        at_stay(String.eq(k, c), bs, k, Br{mh, mo, me, mk}, Br{th, to, te, tk}, c, EQ{})({==})(hm)(hc)({==})

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
  {Tables.Table.get(Br, bs, k) == m0 : Maybe<&2, Br>} -> {Tables.Table.get(Br, Mix.branches(Sync.at(m0, k, Br{th, to, te, tk}, vs, Mix{bs, cs, ns})), c) == Brs.step(String.eq(k, c), Some{Br{th, to, te, tk}}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}

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
        %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, Tables.Table.set(Br, bs, k, Br{th, to, te, tk}), c), Bools.Bool.when(Maybe<&2, Br>, String.eq(k, c), u => Some{Br{th, to, te, tk}}, u => Tables.Table.get(Br, bs, c)), Tables.Table.get_set(Br, bs, k, Br{th, to, te, tk}, c)) :
          {_ == Brs.step(String.eq(k, c), Some{Br{th, to, te, tk}}, Tables.Table.get(Br, bs, c)) : Maybe<&2, Br>}
        at_new(String.eq(k, c), bs, k, Br{th, to, te, tk}, c)({==})(hm)
    case Some{Br{+mh, +mo, +me, +mk}}:
      hm =>
        +th = th
        +to = to
        +te = te
        +tk = tk
        pick_find(Br.stamp.cmp(Br{mh, mo, me, mk}, Br{th, to, te, tk}), k, mh, mo, me, mk, th, to, te, tk, vs, bs, cs, ns, c)(hm)({==})

# one step of a sync's branch pass, for the branch f of another node, named k
law seen_find:
  for k: String
  for f: Maybe<&2, Br>
  for acc: Mix
  for vs: Tables.Table<Ver>
  for c: String
  {Tables.Table.get(Br, Mix.branches(Sync.seen.meet(k, f, acc, vs)), c) == Brs.step(String.eq(k, c), f, Tables.Table.get(Br, Mix.branches(acc), c)) : Maybe<&2, Br>}

def seen_find(k, f, acc, vs, c):
  match f acc:
    case None{} Mix{+bs, cs, ns}:
      +k = k
      +c = c
      Equal.sym(Maybe<&2, Br>, Brs.step(String.eq(k, c), None{}, Tables.Table.get(Br, bs, c)), Tables.Table.get(Br, bs, c), brs_step_none(String.eq(k, c), Tables.Table.get(Br, bs, c)))
    case Some{Br{+th, +to, +te, +tk}} Mix{+bs, cs, ns}:
      +k = k
      at_find(Tables.Table.get(Br, bs, k), k, th, to, te, tk, vs, bs, cs, ns, c)({==})

# a sync's branch pass, as a fold
law brs_fold_find:
  for ks: List<&2, String>
  for full: Tables.Table<Br>
  for vs: Tables.Table<Ver>
  for acc: Mix
  for c: String
  {Tables.Table.get(Br, Mix.branches(Sync.branches(ks, full, vs, acc)), c) == Brs.fold(ks, full, c, Tables.Table.get(Br, Mix.branches(acc), c)) : Maybe<&2, Br>}

def brs_fold_find(ks, full, vs, acc, c):
  match ks:
    case Nil{}:
      {==}
    case Con{+k, r}:
      +full = full
      +vs = vs
      +c = c
      +acc = acc
      %seen_find(k, Tables.Table.get(Br, full, k), acc, vs, c) :
        {Tables.Table.get(Br, Mix.branches(Sync.branches(r, full, vs, Sync.seen.meet(k, Tables.Table.get(Br, full, k), acc, vs))), c) == Brs.fold(r, full, c, _) : Maybe<&2, Br>}
      brs_fold_find(r, full, vs, Sync.seen.meet(k, Tables.Table.get(Br, full, k), acc, vs), c)

# a fold over names that miss c changes nothing: at the first name k
law brs_none.at:
  for hit: Bool
  for k: String
  for r: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  ({Strings.has(r, c) == False{} : Bool} -> {Brs.fold(r, full, c, m) == m : Maybe<&2, Br>}) -> {String.eq(k, c) == hit : Bool} -> {List.any.if(u => Strings.has(r, c), hit) == False{} : Bool} -> {Brs.fold(r, full, c, Brs.step(hit, Tables.Table.get(Br, full, k), m)) == m : Maybe<&2, Br>}

def brs_none.at(hit, k, r, full, c, m):
  match hit:
    case False{}:
      ih => he => hn => ih(hn)
    case True{}:
      ih => he => hn => Empty.absurd({Brs.fold(r, full, c, Brs.step(True{}, Tables.Table.get(Br, full, k), m)) == m : Maybe<&2, Br>}, Bools.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, hn)))

law brs_none:
  for ks: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  {Strings.has(ks, c) == False{} : Bool} -> {Brs.fold(ks, full, c, m) == m : Maybe<&2, Br>}

def brs_none(ks, full, c, m):
  match ks:
    case Nil{}:
      h => {==}
    case Con{+k, +r}:
      +full = full
      +c = c
      +m = m
      brs_none.at(String.eq(k, c), k, r, full, c, m)(brs_none(r, full, c, m))({==})

# once joined, a fold keeps the join: at the first name k
law brs_idem.at:
  for hit: Bool
  for k: String
  for r: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  {Brs.fold(r, full, c, Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c))) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>} -> {String.eq(k, c) == hit : Bool} -> {Brs.fold(r, full, c, Brs.step(hit, Tables.Table.get(Br, full, k), Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)))) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def brs_idem.at(hit, k, r, full, c, m):
  match hit:
    case False{}:
      ih => he => ih
    case True{}:
      ih => he =>
        +full = full
        +c = c
        +m = m
        %Equal.sym(String, k, c, Strings.String.eq_sound(k, c)(he)) :
          {Brs.fold(r, full, c, Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)), Tables.Table.get(Br, full, _))) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}
        %Equal.sym(Maybe<&2, Br>, Orders.Order.join(~Br, ~Br.stamp.cmp, Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)), Tables.Table.get(Br, full, c)), Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)), Orders.Order.join_idem(~Br, ~Br.stamp.cmp, y => stamp_refl(y), m, Tables.Table.get(Br, full, c))) :
          {Brs.fold(r, full, c, _) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}
        ih

law brs_idem:
  for ks: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  {Brs.fold(ks, full, c, Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c))) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def brs_idem(ks, full, c, m):
  match ks:
    case Nil{}:
      {==}
    case Con{+k, +r}:
      +full = full
      +c = c
      +m = m
      brs_idem.at(String.eq(k, c), k, r, full, c, m)(brs_idem(r, full, c, m))({==})

# a fold over names with c joins the branch of c: at the first name k
law brs_some.at:
  for hit: Bool
  for k: String
  for r: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  ({Strings.has(r, c) == True{} : Bool} -> {Brs.fold(r, full, c, m) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}) -> {String.eq(k, c) == hit : Bool} -> {List.any.if(u => Strings.has(r, c), hit) == True{} : Bool} -> {Brs.fold(r, full, c, Brs.step(hit, Tables.Table.get(Br, full, k), m)) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def brs_some.at(hit, k, r, full, c, m):
  match hit:
    case False{}:
      ih => he => hn => ih(hn)
    case True{}:
      ih => he => hn =>
        +full = full
        +c = c
        +m = m
        %Equal.sym(String, k, c, Strings.String.eq_sound(k, c)(he)) :
          {Brs.fold(r, full, c, Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, _))) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}
        brs_idem(r, full, c, m)

law brs_some:
  for ks: List<&2, String>
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  {Strings.has(ks, c) == True{} : Bool} -> {Brs.fold(ks, full, c, m) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def brs_some(ks, full, c, m):
  match ks:
    case Nil{}:
      h => Empty.absurd({Brs.fold(Nil{}, full, c, m) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}, Bools.Bool.false_ne_true(h))
    case Con{+k, +r}:
      +full = full
      +c = c
      +m = m
      brs_some.at(String.eq(k, c), k, r, full, c, m)(brs_some(r, full, c, m))({==})

# the fold over all names of full, by whether full has c (held)
law brs_all.at:
  for held: Bool
  for full: Tables.Table<Br>
  for c: String
  for m: Maybe<&2, Br>
  {Strings.has(Tables.Table.keys(Br, full), c) == held : Bool} -> {Brs.fold(Tables.Table.keys(Br, full), full, c, m) == Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def brs_all.at(held, full, c, m):
  match held:
    case True{}:
      h =>
        +full = full
        brs_some(Tables.Table.keys(Br, full), full, c, m)(h)
    case False{}:
      +h =>
        +full = full
        +c = c
        +m = m
        Equal.trans(
          Maybe<&2, Br>,
          Brs.fold(Tables.Table.keys(Br, full), full, c, m),
          m,
          Orders.Order.join(~Br, ~Br.stamp.cmp, m, Tables.Table.get(Br, full, c)),
          brs_none(Tables.Table.keys(Br, full), full, c, m)(h),
          (
            %Equal.sym(Maybe<&2, Br>, Tables.Table.get(Br, full, c), None{}, Tables.Table.none_of(Br, Tables.Table.get(Br, full, c))(Equal.trans(Bool, Maybe.is_some(&2, Br, Tables.Table.get(Br, full, c)), Strings.has(Tables.Table.keys(Br, full), c), False{}, Equal.sym(Bool, Strings.has(Tables.Table.keys(Br, full), c), Maybe.is_some(&2, Br, Tables.Table.get(Br, full, c)), Tables.Table.keys_get(Br, full, c)), h))) :
              {m == Orders.Order.join(~Br, ~Br.stamp.cmp, m, _) : Maybe<&2, Br>}
            {==}
          )
        )

# after a sync's branch pass, a branch is the winner of the node's own and the
# other node's
law sync_branches_find:
  for full: Tables.Table<Br>
  for vs: Tables.Table<Ver>
  for acc: Mix
  for c: String
  {Tables.Table.get(Br, Mix.branches(Sync.branches(Tables.Table.keys(Br, full), full, vs, acc)), c) == Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, Mix.branches(acc), c), Tables.Table.get(Br, full, c)) : Maybe<&2, Br>}

def sync_branches_find(full, vs, acc, c):
  +full = full
  +acc = acc
  +c = c
  Equal.trans(
    Maybe<&2, Br>,
    Tables.Table.get(Br, Mix.branches(Sync.branches(Tables.Table.keys(Br, full), full, vs, acc)), c),
    Brs.fold(Tables.Table.keys(Br, full), full, c, Tables.Table.get(Br, Mix.branches(acc), c)),
    Orders.Order.join(~Br, ~Br.stamp.cmp, Tables.Table.get(Br, Mix.branches(acc), c), Tables.Table.get(Br, full, c)),
    brs_fold_find(Tables.Table.keys(Br, full), full, vs, acc, c),
    brs_all.at(Strings.has(Tables.Table.keys(Br, full), c), full, c, Tables.Table.get(Br, Mix.branches(acc), c))({==})
  )

# the order of versions for marks: the smaller version is the greater
def Ver.rev(a: String, b: String) -> Cmp:
  String.order(b, a)

# a mark's version after another node's version f met mv, when the step is
# for the mark looked up (hit)
def Marks.step(hit: Bool, f: Maybe<&2, String>, mv: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case False{}:
      mv
    case True{}:
      Orders.Order.join(~String, ~Ver.rev, mv, f)

# the version order of marks compares EQ with itself
law rev_refl:
  for a: String
  {Ver.rev(a, a) == EQ{} : Cmp}

def rev_refl(a):
  Strings.String.order_refl(a)

# the version order of marks the other way round is flipped
law rev_swap:
  for a: String
  for b: String
  {Ver.rev(b, a) == Cmps.Cmp.flip(Ver.rev(a, b)) : Cmp}

def rev_swap(a, b):
  Strings.String.order_swap(b, a, EQ{})

# versions that the version order of marks calls EQ are equal
law rev_same:
  for a: String
  for b: String
  {Ver.rev(a, b) == EQ{} : Cmp} -> {a == b : String}

def rev_same(a, b):
  h =>
    +a = a
    +b = b
    Equal.sym(String, b, a, Strings.String.order_sound(b, a)(h))

# a mark step with no version found changes nothing
law marks_step_none:
  for hit: Bool
  for mv: Maybe<&2, String>
  {Marks.step(hit, None{}, mv) == mv : Maybe<&2, String>}

def marks_step_none(hit, mv):
  match hit:
    case False{}:
      {==}
    case True{}:
      {==}

# a "less than" that is true is LT
law is_lt_true:
  for c: Cmp
  {Cmp.is_lt(c) == True{} : Bool} -> {c == LT{} : Cmp}

def is_lt_true(c):
  match c:
    case LT{}:
      h => {==}
    case EQ{}:
      h => Empty.absurd({EQ{} == LT{} : Cmp}, Bools.Bool.false_ne_true(h))
    case GT{}:
      h => Empty.absurd({GT{} == LT{} : Cmp}, Bools.Bool.false_ne_true(h))

# the marks of a branch after a set: by whether the set was on that branch
law marks_of_set:
  for hit: Bool
  for ms: Tables.Table<Tables.Table<MarkAt>>
  for b: String
  for x: Tables.Table<MarkAt>
  for qb: String
  {String.eq(b, qb) == hit : Bool} -> {Marks.of(Tables.Table.set(Tables.Table<MarkAt>, ms, b, x), qb) == Bools.Bool.when(Tables.Table<MarkAt>, hit, u => x, u => Marks.of(ms, qb)) : Tables.Table<MarkAt>}

def marks_of_set(hit, ms, b, x, qb):
  match hit:
    case True{}:
      +he =>
        +ms = ms
        +b = b
        +x = x
        +qb = qb
        %Equal.sym(Maybe<&2, Tables.Table<MarkAt>>, Tables.Table.get(Tables.Table<MarkAt>, Tables.Table.set(Tables.Table<MarkAt>, ms, b, x), qb), Bools.Bool.when(Maybe<&2, Tables.Table<MarkAt>>, String.eq(b, qb), u => Some{x}, u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)), Tables.Table.get_set(Tables.Table<MarkAt>, ms, b, x, qb)) :
          {Maybe.default(&2, Tables.Table<MarkAt>, _, Tables.Table.new(MarkAt)) == x : Tables.Table<MarkAt>}
        %Equal.sym(Bool, String.eq(b, qb), True{}, he) :
          {Maybe.default(&2, Tables.Table<MarkAt>, Bools.Bool.when(Maybe<&2, Tables.Table<MarkAt>>, _, u => Some{x}, u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)), Tables.Table.new(MarkAt)) == x : Tables.Table<MarkAt>}
        {==}
    case False{}:
      +he =>
        +ms = ms
        +b = b
        +x = x
        +qb = qb
        %Equal.sym(Maybe<&2, Tables.Table<MarkAt>>, Tables.Table.get(Tables.Table<MarkAt>, Tables.Table.set(Tables.Table<MarkAt>, ms, b, x), qb), Bools.Bool.when(Maybe<&2, Tables.Table<MarkAt>>, String.eq(b, qb), u => Some{x}, u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)), Tables.Table.get_set(Tables.Table<MarkAt>, ms, b, x, qb)) :
          {Maybe.default(&2, Tables.Table<MarkAt>, _, Tables.Table.new(MarkAt)) == Marks.of(ms, qb) : Tables.Table<MarkAt>}
        %Equal.sym(Bool, String.eq(b, qb), False{}, he) :
          {Maybe.default(&2, Tables.Table<MarkAt>, Bools.Bool.when(Maybe<&2, Tables.Table<MarkAt>>, _, u => Some{x}, u => Tables.Table.get(Tables.Table<MarkAt>, ms, qb)), Tables.Table.new(MarkAt)) == Marks.of(ms, qb) : Tables.Table<MarkAt>}
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
  {String.eq(m, qm) == hit : Bool} -> {MarkAt.version.of(Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm)) == Bools.Bool.when(Maybe<&2, String>, hit, u => Some{v}, u => MarkAt.find(ms, b, qm)) : Maybe<&2, String>}

def mark_set_find.name(hit, ms, b, m, v, t, qm):
  +ms = ms
  +b = b
  +m = m
  +v = v
  +t = t
  +qm = qm
  match hit:
    case True{}:
      he =>
        %Equal.sym(Maybe<&2, MarkAt>, Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm), Bools.Bool.when(Maybe<&2, MarkAt>, String.eq(m, qm), u => Some{MarkAt{v, t}}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)), Tables.Table.get_set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}, qm)) :
          {MarkAt.version.of(_) == Some{v} : Maybe<&2, String>}
        %Equal.sym(Bool, String.eq(m, qm), True{}, he) :
          {MarkAt.version.of(Bools.Bool.when(Maybe<&2, MarkAt>, _, u => Some{MarkAt{v, t}}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm))) == Some{v} : Maybe<&2, String>}
        {==}
    case False{}:
      he =>
        %Equal.sym(Maybe<&2, MarkAt>, Tables.Table.get(MarkAt, Tables.Table.set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}), qm), Bools.Bool.when(Maybe<&2, MarkAt>, String.eq(m, qm), u => Some{MarkAt{v, t}}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm)), Tables.Table.get_set(MarkAt, Marks.of(ms, b), m, MarkAt{v, t}, qm)) :
          {MarkAt.version.of(_) == MarkAt.find(ms, b, qm) : Maybe<&2, String>}
        %Equal.sym(Bool, String.eq(m, qm), False{}, he) :
          {MarkAt.version.of(Bools.Bool.when(Maybe<&2, MarkAt>, _, u => Some{MarkAt{v, t}}, u => Tables.Table.get(MarkAt, Marks.of(ms, b), qm))) == MarkAt.find(ms, b, qm) : Maybe<&2, String>}
        {==}

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
            %Equal.sym(Bool, Ver.has(St.versions(s), r), False{}, new_free(s, r)(hn)): {Out.answer(Write.free(_, s, r, w, time, n, b, Some{v}, x)) == Spec.Answer.Write{Spec.Write.Written{r}}: Spec.Answer}
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
          Ver.has(St.versions(s), r),
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
