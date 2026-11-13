import Base
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/shared/shared.bend as Shared

# Words
# -----
# A request is named by its writer and the id that the writer gave it
# (Ledgers.Id). A store, or a branch of it, is a line (Ledgers.Line): the hash
# of the request that started the store, and the name of the branch (none: the
# store itself). A path names a resource. Content is words.

# the writer of the request id i
def Id.writer(i: Ledgers.Id) -> String:
  match i:
    case Ledgers.Id{a, r}:
      a

# Nodes
# -----

# a Vend Node
law VendNode:
  Data

# what Vend Nodes share about a history: a request, a ballot, or the proof that
# an owner lied
law Change:
  Data

# what a writer asks for
type Request is Data:
  Request.Start{owners: List<&2, String>}
  Request.Write{branch: Ledgers.Line, path: String, words: Maybe<&2, List<&2, U32>>}
  Request.Merge{from: Ledgers.Line, into: Ledgers.Line}
  Request.Resolve{merge: Ledgers.Id, path: String, words: Maybe<&2, List<&2, U32>>}
  Request.Mark{branch: Ledgers.Line, name: String, version: Nat}
  Request.Move{branch: Ledgers.Line, to: Ledgers.Line, version: Nat}
  Request.Group{store: Hashes.Hash, name: String, members: List<&2, String>}
  Request.Own{line: Ledgers.Line, group: String}

# Start: a new store, with these owner nodes. Write: the words of a resource (none
# deletes it). Merge: one branch into another. Resolve: the words of a resource
# that clashed in a merge. Mark: a name for a version. Move: a new version of a
# branch equal to a version of another line. Group: the members of an owner
# group, nodes or groups. Own: the owner group of a store or a branch; on a new
# branch name, it creates the branch.

# the words that name the request r of the id i
law Request.code:
  for i: Ledgers.Id
  for r: Request
  List<&2, U32>

# what a node does next
type Deed is Data:
  Deed.Connect{writer: String}
  Deed.Leave{writer: String}
  Deed.Ask{id: Ledgers.Id, request: Request}
  Deed.Sync{from: VendNode}
  Deed.Mount{address: String, branch: Ledgers.Line, held: List<&2, U32>}
  Deed.Unmount{address: String}
  Deed.Work{}
  Deed.Drop{}
  Deed.Stop{force: Bool}

# Connect, Leave: a writer connects or leaves. Ask: a writer sends a request.
# Sync: the node takes in what another node holds. Mount: a resource that holds
# these words is mounted to a branch. Unmount: it is unmounted. Work: the node
# goes on with its work (it votes, decides and fetches). Drop: it lets go of the
# content that it does not need. Stop: it is asked to stop.

# n after the deed d
law VendNode.does:
  for n: VendNode
  for d: Deed
  VendNode

# the name of n
law VendNode.name:
  for n: VendNode
  String

# the writers connected to n
law VendNode.writers:
  for n: VendNode
  List<&2, String>

# the addresses of the resources mounted to n
law VendNode.mounts:
  for n: VendNode
  List<&2, String>

# n has stopped
law VendNode.stopped:
  for n: VendNode
  Bool

# n holds the change c
law VendNode.holds:
  for n: VendNode
  for c: Change
  Bool

# the hashes of the parts of content that n holds
law VendNode.parts:
  for n: VendNode
  List<&2, Hashes.Hash>

# the words of the part of content whose hash is h, if n holds it
law VendNode.part:
  for n: VendNode
  for h: Hashes.Hash
  Maybe<&2, List<&2, U32>>

# the words of the resource at the path p in version k of the line c (none
# inside: no such resource), or nothing while n does not hold them
law VendNode.read:
  for n: VendNode
  for c: Ledgers.Line
  for k: Nat
  for p: String
  Maybe<&2, Maybe<&2, List<&2, U32>>>

# the words that the writer w reads at the path p of the newest version of the
# branch b, its own requests included, even those not decided yet
law VendNode.view:
  for n: VendNode
  for w: String
  for b: Ledgers.Line
  for p: String
  Maybe<&2, Maybe<&2, List<&2, U32>>>

# Questions
# ---------

# the final reply to a request. Pending is no reply yet
type Status is Data:
  Status.Written{}
  Status.Conflicted{merge: Ledgers.Id}
  Status.Stale{}
  Status.Refused{}

# a question about a store or a branch
type Question is Data:
  Question.Status{line: Ledgers.Line, id: Ledgers.Id}
  Question.Request{line: Ledgers.Line, id: Ledgers.Id}
  Question.Version{line: Ledgers.Line, n: Nat}
  Question.Content{line: Ledgers.Line, n: Nat}
  Question.Group{line: Ledgers.Line, n: Nat}
  Question.Owners{line: Ledgers.Line, n: Nat}
  Question.Members{store: Hashes.Hash, group: String, n: Nat}
  Question.Nodes{store: Hashes.Hash, group: String, n: Nat}
  Question.IsGroup{store: Hashes.Hash, name: String, n: Nat}
  Question.Mark{line: Ledgers.Line, mark: String}
  Question.Count{line: Ledgers.Line}
  Question.Clashes{line: Ledgers.Line, id: Ledgers.Id}
  Question.Affects{
    line: Ledgers.Line,
    from: Nat,
    to: Nat,
    uses: List<&2, String>,
    build: List<&2, String>
  }

# Status: what became of the request id. Request: what the request id asked
# for. Version: the request whose decision made version n. Content: the hash of
# the whole content of version n. Group: the nodes of the owner group that
# decides version n. Owners: the nodes whose ballots decided version n.
# Members: the members of a group at version n of the store. Nodes: the nodes of
# a group at version n of the store. IsGroup: whether a name is a group there.
# Mark: the version that a mark names. Count: how many versions the line has.
# Clashes: the paths that clash in the merge id. Affects: the paths that changed
# from version from to version to among those that uses reaches through imports,
# in the build of these conditions.

# a reply to a question
type Reply is Data:
  Reply.Status{status: Status}
  Reply.Ask{request: Request}
  Reply.Id{id: Ledgers.Id}
  Reply.Hash{hash: Hashes.Hash}
  Reply.Names{names: List<&2, String>}
  Reply.Number{n: Nat}
  Reply.Yes{yes: Bool}

# the reply r is of the kind that the question q asks for
def Reply.fits(q: Question, r: Reply) -> Bool:
  match q r:
    case Question.Status{c, i} Reply.Status{s}:
      True{}
    case Question.Request{c, i} Reply.Ask{x}:
      True{}
    case Question.Version{c, k} Reply.Id{i}:
      True{}
    case Question.Content{c, k} Reply.Hash{h}:
      True{}
    case Question.Group{c, k} Reply.Names{ns}:
      True{}
    case Question.Owners{c, k} Reply.Names{ns}:
      True{}
    case Question.Members{s, g, k} Reply.Names{ns}:
      True{}
    case Question.Nodes{s, g, k} Reply.Names{ns}:
      True{}
    case Question.IsGroup{s, g, k} Reply.Yes{y}:
      True{}
    case Question.Mark{c, m} Reply.Number{k}:
      True{}
    case Question.Count{c} Reply.Number{k}:
      True{}
    case Question.Clashes{c, i} Reply.Names{ns}:
      True{}
    case Question.Affects{c, a, b, us, bs} Reply.Names{ns}:
      True{}
    case _ _:
      False{}

# the status b follows a: the same, or Written after Conflicted
def Status.follows(a: Status, b: Status) -> Bool:
  match a b:
    case Status.Written{} Status.Written{}:
      True{}
    case Status.Conflicted{i} Status.Written{}:
      True{}
    case Status.Conflicted{i} Status.Conflicted{j}:
      Ledgers.Id.is_eq(i, j)
    case Status.Stale{} Status.Stale{}:
      True{}
    case Status.Refused{} Status.Refused{}:
      True{}
    case _ _:
      False{}

# the reply b to q moves forward from the reply a: a count only grows, a status
# only moves from Conflicted to Written, and every other reply stays the same
def Reply.Moves(q: Question, a: Reply, b: Reply) -> Type:
  match q a b:
    case Question.Count{c} Reply.Number{x} Reply.Number{y}:
      {Nat.is_le(x, y) == True{}: Bool}
    case _ Reply.Status{x} Reply.Status{y}:
      {Status.follows(x, y) == True{}: Bool}
    case _ x y:
      {x == y: Reply}

# the reply of n to q, or nothing (Unknown) while n does not hold enough
# changes to know it
law VendNode.answer:
  for n: VendNode
  for q: Question
  Maybe<&2, Reply>

# Liars
# -----

# a vote: who cast it, the step it is for, and what it chose
type Ballot is Data:
  Ballot{voter: String, step: List<&2, U32>, choice: List<&2, U32>}

# the ballot that the change c is, if it is one
law Change.ballot:
  for c: Change
  Maybe<&2, Ballot>

# the voters that n has proven to be liars
law VendNode.liars:
  for n: VendNode
  List<&2, String>

# n names no liar
def VendNode.Honest(n: VendNode) -> Type:
  {VendNode.liars(n) == []: List<&2, String>}

# Formats
# -------

# a change from one content to another
law Diff:
  Data

# the items that the words ws of the resource at the path p are read as, in its
# format: functions and types for code, nested formats in their own, lines for
# unknown text, one whole part otherwise
law Format.items:
  for p: String
  for ws: List<&2, U32>
  List<&2, List<&2, U32>>

# the paths that the resource at p, of the words ws, imports in the build of
# the conditions bs, aliases followed
law Format.imports:
  for p: String
  for ws: List<&2, U32>
  for bs: List<&2, String>
  List<&2, String>

# the change from a to b of the resource at p, in its format
law Format.diff:
  for p: String
  for a: List<&2, U32>
  for b: List<&2, U32>
  Diff

# a after the change x, in the format of the resource at p (none: x does not
# apply to a)
law Format.apply:
  for p: String
  for a: List<&2, U32>
  for x: Diff
  Maybe<&2, List<&2, U32>>

# the merge of ours and theirs, two changes of base (none inside: no resource),
# in the format of the resource at p; nothing when they clash
law Format.merge:
  for p: String
  for base: Maybe<&2, List<&2, U32>>
  for ours: Maybe<&2, List<&2, U32>>
  for theirs: Maybe<&2, List<&2, U32>>
  Maybe<&2, Maybe<&2, List<&2, U32>>>

# Helpers of the laws
# -------------------

# the writers after the deed d, from ws
def Deed.writers(d: Deed, ws: List<&2, String>) -> List<&2, String>:
  match d:
    case Deed.Connect{+w}:
      w <> Shared.List.remove(~String, ~String.eq, ws, w)
    case Deed.Leave{w}:
      Shared.List.remove(~String, ~String.eq, ws, w)
    case _:
      ws

# the mounts after the deed d, from ms
def Deed.mounts(d: Deed, ms: List<&2, String>) -> List<&2, String>:
  match d:
    case Deed.Mount{+a, b, h}:
      a <> Shared.List.remove(~String, ~String.eq, ms, a)
    case Deed.Unmount{a}:
      Shared.List.remove(~String, ~String.eq, ms, a)
    case _:
      ms

# whether a node has stopped after the deed d: it had, or d is a stop that is
# forced or finds no writer and no mount
def Deed.stopped(d: Deed, s: Bool, ws: List<&2, String>, ms: List<&2, String>) -> Bool:
  match d:
    case Deed.Stop{f}:
      Bool.or(s, Bool.or(f, Bool.and(List.is_empty(&2, String, ws), List.is_empty(&2, String, ms))))
    case _:
      s

# no hash is twice in hs
def Distinct(hs: List<&2, Hashes.Hash>) -> Type:
  match hs:
    case Nil{}:
      Unit
    case Con{+h, r}:
      {List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, r, h) == False{}: Bool} & Distinct(r)

# ps is a chain of imports from a to b, in version k of the line c at n, in
# the build of the conditions bs
def Imports(
  n: VendNode,
  c: Ledgers.Line,
  k: Nat,
  bs: List<&2, String>,
  a: String,
  ps: List<&2, String>,
  b: String
) -> Type:
  match ps:
    case Nil{}:
      {a == b: String}
    case Con{q, rest}:
      Exists(
        List<&2, U32>,
        ws => {
          VendNode.read(n, c, k, a) == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        }
          & (
            {
              List.contains(~String, ~String.eq, Format.imports(a, ws, bs), q) == True{}: Bool
            }
              & Imports(n, c, k, bs, q, rest, b)
          )
      )

# the path p is reached from one of the paths us through imports
def Reaches(
  n: VendNode,
  c: Ledgers.Line,
  k: Nat,
  bs: List<&2, String>,
  us: List<&2, String>,
  p: String
) -> Type:
  Exists(
    String,
    u => {
      List.contains(~String, ~String.eq, us, u) == True{}: Bool
    }
      & Exists(List<&2, String>, ps => Imports(n, c, k, bs, u, ps, p))
  )

# the resource at p differs from version a to version b of c at n
def Changed(n: VendNode, c: Ledgers.Line, a: Nat, b: Nat, p: String) -> Type:
  Exists(
    Maybe<&2, List<&2, U32>>,
    x => Exists(
      Maybe<&2, List<&2, U32>>,
      y => {
        VendNode.read(n, c, a, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      }
        & (
          {
            VendNode.read(n, c, b, p) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
          }
            & ({x == y: Maybe<&2, List<&2, U32>>} -> Empty)
        )
    )
  )

# version k of c is the decision of the request i, which asked for r
def Made(n: VendNode, c: Ledgers.Line, k: Nat, i: Ledgers.Id, r: Request) -> Type:
  {
    VendNode.answer(n, Question.Version{c, k}) == Some{Reply.Id{i}}: Maybe<&2, Reply>
  }
    & {VendNode.answer(n, Question.Request{c, i}) == Some{Reply.Ask{r}}: Maybe<&2, Reply>}

# Laws of the backbone
# --------------------

# A reply fits its question.
# Asked for version 3, a node replies with a request id, never with a hash.
law VendNode.answer_fits:
  for n: VendNode
  for q: Question
  for r: Reply
  {VendNode.answer(n, q) == Some{r}: Maybe<&2, Reply>} -> {Reply.fits(q, r) == True{}: Bool}

# Two nodes that hold the same changes give the same replies, whatever the
# order in which they got them.
# Two nodes that took in requests r1 and r2, in either order, reply the same
# content for a branch.
law VendNode.same_changes:
  for n1: VendNode
  for n2: VendNode
  for q: Question
  (@c: Change -> {VendNode.holds(n1, c) == VendNode.holds(n2, c): Bool})
    -> {VendNode.answer(n1, q) == VendNode.answer(n2, q): Maybe<&2, Reply>}

# A node never loses a change that it holds.
# A request that a node took in stays held after any later deed, a drop
# included.
law VendNode.keeps:
  for n: VendNode
  for d: Deed
  for c: Change
  {VendNode.holds(n, c) == True{}: Bool} -> {VendNode.holds(VendNode.does(n, d), c) == True{}: Bool}

# Replies only move forward, while the node names no liar: Unknown may become a
# reply, a count may grow, a Conflicted request may become Written, and no
# other reply changes.
# Version 3 of a branch, once known, stays the same. A request that is
# Conflicted turns Written once its clashes are resolved.
law VendNode.answer_moves_forward:
  for n: VendNode
  for d: Deed
  for q: Question
  for a: Reply
  VendNode.Honest(VendNode.does(n, d))
    -> {VendNode.answer(n, q) == Some{a}: Maybe<&2, Reply>}
    -> Exists(
      Reply,
      b => {
        VendNode.answer(VendNode.does(n, d), q) == Some{b}: Maybe<&2, Reply>
      }
        & Reply.Moves(q, a, b)
    )

# The changes of two nodes always join: a node that takes in all that another
# node holds then holds the changes of both, while it names no liar.
# Two nodes that each took in different requests both hold all of them after
# one syncs from the other.
law VendNode.sync_joins:
  for n: VendNode
  for m: VendNode
  for c: Change
  VendNode.Honest(VendNode.does(n, Deed.Sync{m}))
    -> {VendNode.holds(m, c) == True{}: Bool}
    -> {VendNode.holds(VendNode.does(n, Deed.Sync{m}), c) == True{}: Bool}

# Laws of a node
# --------------

# A node keeps its name.
# A node named "a" is named "a" after any deed.
law VendNode.name_stays:
  for n: VendNode
  for d: Deed
  {VendNode.name(VendNode.does(n, d)) == VendNode.name(n): String}

# The writers of a node are exactly those that connected and did not leave.
# After "w connects", w is a writer; after "w leaves", it is not; no other deed
# changes the writers.
law VendNode.writers_are:
  for n: VendNode
  for d: Deed
  {
    Shared.List.same_set(
      ~String,
      ~String.eq,
      VendNode.writers(VendNode.does(n, d)),
      Deed.writers(d, VendNode.writers(n))
    )
      == True{}: Bool
  }

# The mounts of a node are exactly the resources mounted and not unmounted.
# After "mount the folder f", f is mounted; after "unmount f", it is not.
law VendNode.mounts_are:
  for n: VendNode
  for d: Deed
  {
    Shared.List.same_set(
      ~String,
      ~String.eq,
      VendNode.mounts(VendNode.does(n, d)),
      Deed.mounts(d, VendNode.mounts(n))
    )
      == True{}: Bool
  }

# A node stops only when asked, and then only when forced or when no resource
# is mounted and no writer is connected; a stopped node stays stopped.
# A node with a connected writer refuses a stop that is not forced.
law VendNode.stops:
  for n: VendNode
  for d: Deed
  {
    VendNode.stopped(
      VendNode.does(n, d)
    )
      == Deed.stopped(d, VendNode.stopped(n), VendNode.writers(n), VendNode.mounts(n)): Bool
  }

# Laws of a store
# ---------------

# A connected writer that starts a store whose only owner is the node gets the
# store at once: its root is the hash of the start request, and its first
# version is that request.
# The writer w asks Start{["a"]} as request "s1" of node "a": after the node
# works, version 0 of the store of root SHA-256(code of s1) is s1.
law VendNode.starts:
  for n: VendNode
  for i: Ledgers.Id
  {VendNode.stopped(n) == False{}: Bool}
    -> {List.contains(~String, ~String.eq, VendNode.writers(n), Id.writer(i)) == True{}: Bool}
    -> {
      VendNode.answer(
        VendNode.does(
          VendNode.does(n, Deed.Ask{i, Request.Start{[VendNode.name(n)]}}),
          Deed.Work{}
        ),
        Question.Version{
          Ledgers.Line{Hashes.Sha.hash(Request.code(i, Request.Start{[VendNode.name(n)]})), None{}},
          0n
        }
      )
        == Some{Reply.Id{i}}: Maybe<&2, Reply>
    }

# Two requests have one code only when they are the same, so no other request
# starts a store of the same root (as far as SHA-256 is not broken).
# Start{["a"]} of id s1 and Start{["a"]} of id s2 have different codes.
law Request.code_names:
  for i: Ledgers.Id
  for r: Request
  for j: Ledgers.Id
  for s: Request
  {
    Request.code(i, r) == Request.code(j, s): List<&2, U32>
  } -> {i == j: Ledgers.Id}
    & {r == s: Request}

# A part is always the words of its hash: a node gives the right words for a
# hash, or nothing, never other words.
# Asked for the part of hash H, a node gives words whose SHA-256 is H, or it
# does not hold that part.
law VendNode.part_is:
  for n: VendNode
  for h: Hashes.Hash
  for ws: List<&2, U32>
  {
    VendNode.part(n, h) == Some{ws}: Maybe<&2, List<&2, U32>>
  } -> {Hashes.Sha.hash(ws) == h: Hashes.Hash}

# A node holds a part exactly when it lists its hash, and it lists each hash
# once: content is stored once by hash, however many versions share it.
# Two versions that share a file hold its part once.
law VendNode.parts_once:
  for n: VendNode
  Distinct(
    VendNode.parts(n)
  )
    & (
      @h: Hashes.Hash -> {
        Maybe.is_some(
          &2,
          List<&2, U32>,
          VendNode.part(n, h)
        )
          == List.contains(~Hashes.Hash, ~Hashes.Hash.is_eq, VendNode.parts(n), h): Bool
      }
    )

# A node of the owner group of a line can read every resource of the newest
# version of the line: the owners keep all of it, so it is never lost.
# An owner of main, whose newest version is 7, reads every file of version 7
# without fetching.
law VendNode.owners_keep:
  for n: VendNode
  for c: Ledgers.Line
  for k: Nat
  for ns: List<&2, String>
  for p: String
  {VendNode.answer(n, Question.Count{c}) == Some{Reply.Number{1n+k}}: Maybe<&2, Reply>}
    -> {VendNode.answer(n, Question.Group{c, k}) == Some{Reply.Names{ns}}: Maybe<&2, Reply>}
    -> {List.contains(~String, ~String.eq, ns, VendNode.name(n)) == True{}: Bool}
    -> {Maybe.is_some(&2, Maybe<&2, List<&2, U32>>, VendNode.read(n, c, k, p)) == True{}: Bool}

# A branch exists only when the owner group of its store decided it: some
# version of the store is a request that owns the branch.
# The branch "dev" of a store exists only after the store decided Own{dev, g}.
law VendNode.branches_decided:
  for n: VendNode
  for r: Hashes.Hash
  for b: String
  for x: Reply
  {VendNode.answer(n, Question.Count{Ledgers.Line{r, Some{b}}}) == Some{x}: Maybe<&2, Reply>}
    -> Exists(
      Nat,
      k => Exists(
        Ledgers.Id,
        i => Exists(
          String,
          g => Made(n, Ledgers.Line{r, None{}}, k, i, Request.Own{Ledgers.Line{r, Some{b}}, g})
        )
      )
    )

# A read never changes to other words, while the node names no liar: only a
# drop may make it unknown again.
# The file a.txt of version 3 reads "hi" for good, or is not held.
law VendNode.read_stays:
  for n: VendNode
  for d: Deed
  for c: Ledgers.Line
  for k: Nat
  for p: String
  for x: Maybe<&2, List<&2, U32>>
  VendNode.Honest(VendNode.does(n, d))
    -> {VendNode.read(n, c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {
      VendNode.read(VendNode.does(n, d), c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
      | {VendNode.read(VendNode.does(n, d), c, k, p) == None{}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# Two nodes that hold the same changes never read different words.
# Two nodes that both hold version 3 of main read the same a.txt, or one of them
# does not hold it.
law VendNode.reads_agree:
  for n1: VendNode
  for n2: VendNode
  for c: Ledgers.Line
  for k: Nat
  for p: String
  for x: Maybe<&2, List<&2, U32>>
  for y: Maybe<&2, List<&2, U32>>
  (@ch: Change -> {VendNode.holds(n1, ch) == VendNode.holds(n2, ch): Bool})
    -> {VendNode.read(n1, c, k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {VendNode.read(n2, c, k, p) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>}
    -> {x == y: Maybe<&2, List<&2, U32>>}

# Laws of a writer
# ----------------

# A request counts once, however often and wherever it is sent: it makes at
# most one version of a line.
# A writer that sends request w7 to two nodes, twice each, gets one version.
law VendNode.counts_once:
  for n: VendNode
  for c: Ledgers.Line
  for i: Ledgers.Id
  for a: Nat
  for b: Nat
  {VendNode.answer(n, Question.Version{c, a}) == Some{Reply.Id{i}}: Maybe<&2, Reply>}
    -> {VendNode.answer(n, Question.Version{c, b}) == Some{Reply.Id{i}}: Maybe<&2, Reply>}
    -> {a == b: Nat}

# A node that alone decides the next version of a branch writes a new request
# of a connected writer at once.
# Node a, the only owner of main at version 6, gets a write of a.txt from a
# connected writer: after it works, the write is Written as version 6.
law VendNode.decides_alone:
  for n: VendNode
  for b: Ledgers.Line
  for k: Nat
  for i: Ledgers.Id
  for p: String
  for ws: Maybe<&2, List<&2, U32>>
  {VendNode.stopped(n) == False{}: Bool}
    -> {List.contains(~String, ~String.eq, VendNode.writers(n), Id.writer(i)) == True{}: Bool}
    -> {VendNode.answer(n, Question.Count{b}) == Some{Reply.Number{k}}: Maybe<&2, Reply>}
    -> {
      VendNode.answer(
        n,
        Question.Group{b, k}
      )
        == Some{Reply.Names{[VendNode.name(n)]}}: Maybe<&2, Reply>
    }
    -> {VendNode.answer(n, Question.Status{b, i}) == None{}: Maybe<&2, Reply>}
    -> {
      VendNode.answer(
        VendNode.does(VendNode.does(n, Deed.Ask{i, Request.Write{b, p, ws}}), Deed.Work{}),
        Question.Version{b, k}
      )
        == Some{Reply.Id{i}}: Maybe<&2, Reply>
    }
      & {
        VendNode.answer(
          VendNode.does(VendNode.does(n, Deed.Ask{i, Request.Write{b, p, ws}}), Deed.Work{}),
          Question.Status{b, i}
        )
          == Some{Reply.Status{Status.Written{}}}: Maybe<&2, Reply>
      }

# A request that is Written made a version.
# A write answered Written is version k of its branch, for some k.
law VendNode.written_made:
  for n: VendNode
  for c: Ledgers.Line
  for i: Ledgers.Id
  {
    VendNode.answer(
      n,
      Question.Status{c, i}
    )
      == Some{Reply.Status{Status.Written{}}}: Maybe<&2, Reply>
  }
    -> Exists(
      Nat,
      k => {VendNode.answer(n, Question.Version{c, k}) == Some{Reply.Id{i}}: Maybe<&2, Reply>}
    )

# A version made by a write holds the written words at its path, and the words
# of the version before at every other path.
# Writing "hi" to a.txt makes version 4, whose a.txt is "hi" and whose b.txt is
# that of version 3.
law VendNode.write_writes:
  for n: VendNode
  for c: Ledgers.Line
  for k: Nat
  for i: Ledgers.Id
  for p: String
  for ws: Maybe<&2, List<&2, U32>>
  for q: String
  for x: Maybe<&2, List<&2, U32>>
  for y: Maybe<&2, List<&2, U32>>
  Made(n, c, 1n+k, i, Request.Write{c, p, ws})
    -> (
      {
        VendNode.read(n, c, 1n+k, p) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
      } -> {x == ws: Maybe<&2, List<&2, U32>>}
    )
      & (
        (
          {String.eq(p, q) == False{}: Bool}
        ) -> {
          VendNode.read(n, c, 1n+k, q) == Some{x}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        } -> {
          VendNode.read(n, c, k, q) == Some{y}: Maybe<&2, Maybe<&2, List<&2, U32>>>
        } -> {x == y: Maybe<&2, List<&2, U32>>}
      )

# A writer reads its own write at once, before it is decided.
# A connected writer that writes "hi" to a.txt of main reads "hi" there next.
law VendNode.reads_own:
  for n: VendNode
  for i: Ledgers.Id
  for b: Ledgers.Line
  for p: String
  for ws: Maybe<&2, List<&2, U32>>
  {VendNode.stopped(n) == False{}: Bool}
    -> {List.contains(~String, ~String.eq, VendNode.writers(n), Id.writer(i)) == True{}: Bool}
    -> {
      VendNode.view(
        VendNode.does(n, Deed.Ask{i, Request.Write{b, p, ws}}),
        Id.writer(i),
        b,
        p
      )
        == Some{ws}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }

# What a writer reads depends only on the changes that the node holds, so it
# reads its own writes on any node that holds them.
# A writer that wrote to node a, then switched to node b that synced from a,
# reads its write on b.
law VendNode.views_agree:
  for n1: VendNode
  for n2: VendNode
  for w: String
  for b: Ledgers.Line
  for p: String
  (@ch: Change -> {VendNode.holds(n1, ch) == VendNode.holds(n2, ch): Bool})
    -> {
      VendNode.view(n1, w, b, p) == VendNode.view(n2, w, b, p): Maybe<&2, Maybe<&2, List<&2, U32>>>
    }

# A writer is told only about changes to what its work uses.
# Work that uses main.c, which imports util.h, is told about util.h and never
# about an unrelated readme.
law VendNode.affects_only:
  for n: VendNode
  for c: Ledgers.Line
  for a: Nat
  for b: Nat
  for us: List<&2, String>
  for bs: List<&2, String>
  for ps: List<&2, String>
  for p: String
  {VendNode.answer(n, Question.Affects{c, a, b, us, bs}) == Some{Reply.Names{ps}}: Maybe<&2, Reply>}
    -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}
    -> Changed(n, c, a, b, p) & Reaches(n, c, b, bs, us, p)

# And it is told about each of them.
# Work that uses main.c is told when util.h, which main.c imports, changes.
law VendNode.affects_all:
  for n: VendNode
  for c: Ledgers.Line
  for a: Nat
  for b: Nat
  for us: List<&2, String>
  for bs: List<&2, String>
  for ps: List<&2, String>
  for p: String
  {VendNode.answer(n, Question.Affects{c, a, b, us, bs}) == Some{Reply.Names{ps}}: Maybe<&2, Reply>}
    -> Changed(n, c, a, b, p)
    -> Reaches(n, c, b, bs, us, p)
    -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}

# Laws of an owner group
# ----------------------

# A version is decided by a majority of the nodes of its owner group, each by a
# ballot that the node holds.
# A group of 5 nodes decides version 4 with ballots of 3 of them.
law VendNode.majority_decides:
  for n: VendNode
  for c: Ledgers.Line
  for k: Nat
  for os: List<&2, String>
  for gs: List<&2, String>
  {VendNode.answer(n, Question.Owners{c, k}) == Some{Reply.Names{os}}: Maybe<&2, Reply>}
    -> {VendNode.answer(n, Question.Group{c, k}) == Some{Reply.Names{gs}}: Maybe<&2, Reply>}
    -> {
      Shared.List.within(~String, ~String.eq, os, gs) == True{}: Bool
    }
      & (
        {
          Nat.is_lt(
            List.length(&2, String, gs),
            Nat.add(List.length(&2, String, os), List.length(&2, String, os))
          )
            == True{}: Bool
        }
          & (
            @v: String -> {
              List.contains(~String, ~String.eq, os, v) == True{}: Bool
            } -> Exists(
              Change,
              ch => {
                VendNode.holds(n, ch) == True{}: Bool
              }
                & Exists(
                  List<&2, U32>,
                  s => Exists(
                    List<&2, U32>,
                    x => {Change.ballot(ch) == Some{Ballot{v, s, x}}: Maybe<&2, Ballot>}
                  )
                )
            )
          )
      )

# The nodes of a group are the members that are nodes, and the nodes of the
# members that are groups.
# A group of the node a and the group g, where g holds b and c, has the nodes a,
# b and c.
law VendNode.group_nodes:
  for n: VendNode
  for s: Hashes.Hash
  for g: String
  for k: Nat
  for ms: List<&2, String>
  for v: String
  {VendNode.answer(n, Question.Members{s, g, k}) == Some{Reply.Names{ms}}: Maybe<&2, Reply>}
    -> {List.contains(~String, ~String.eq, ms, v) == True{}: Bool}
    -> (
      {
        VendNode.answer(n, Question.IsGroup{s, v, k}) == Some{Reply.Yes{False{}}}: Maybe<&2, Reply>
      } -> Exists(
        List<&2, String>,
        ns => {
          VendNode.answer(n, Question.Nodes{s, g, k}) == Some{Reply.Names{ns}}: Maybe<&2, Reply>
        }
          & {List.contains(~String, ~String.eq, ns, v) == True{}: Bool}
      )
    )
      & (
        {
          VendNode.answer(n, Question.IsGroup{s, v, k}) == Some{Reply.Yes{True{}}}: Maybe<&2, Reply>
        } -> @x: String -> Exists(
          List<&2, String>,
          vs => {
            VendNode.answer(n, Question.Nodes{s, v, k}) == Some{Reply.Names{vs}}: Maybe<&2, Reply>
          }
            & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
        ) -> Exists(
          List<&2, String>,
          ns => {
            VendNode.answer(n, Question.Nodes{s, g, k}) == Some{Reply.Names{ns}}: Maybe<&2, Reply>
          }
            & {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
        )
      )

# And a group has no other nodes.
# The group of a and g, where g holds b and c, has no node d.
law VendNode.group_nodes_only:
  for n: VendNode
  for s: Hashes.Hash
  for g: String
  for k: Nat
  for ns: List<&2, String>
  for x: String
  {VendNode.answer(n, Question.Nodes{s, g, k}) == Some{Reply.Names{ns}}: Maybe<&2, Reply>}
    -> {List.contains(~String, ~String.eq, ns, x) == True{}: Bool}
    -> Exists(
      List<&2, String>,
      ms => {
        VendNode.answer(n, Question.Members{s, g, k}) == Some{Reply.Names{ms}}: Maybe<&2, Reply>
      }
        & Exists(
          String,
          v => {
            List.contains(~String, ~String.eq, ms, v) == True{}: Bool
          }
            & (
              (
                {
                  String.eq(v, x) == True{}: Bool
                }
                  & {
                    VendNode.answer(
                      n,
                      Question.IsGroup{s, v, k}
                    )
                      == Some{Reply.Yes{False{}}}: Maybe<&2, Reply>
                  }
              )
                | (
                  {
                    VendNode.answer(
                      n,
                      Question.IsGroup{s, v, k}
                    )
                      == Some{Reply.Yes{True{}}}: Maybe<&2, Reply>
                  }
                    & Exists(
                      List<&2, String>,
                      vs => {
                        VendNode.answer(
                          n,
                          Question.Nodes{s, v, k}
                        )
                          == Some{Reply.Names{vs}}: Maybe<&2, Reply>
                      }
                        & {List.contains(~String, ~String.eq, vs, x) == True{}: Bool}
                    )
                )
            )
        )
    )

# A node never signs two ballots that contradict each other: it never names
# itself a liar.
# Node a, restarted any number of times, is never named a liar by itself.
law VendNode.never_lies:
  for n: VendNode
  {List.contains(~String, ~String.eq, VendNode.liars(n), VendNode.name(n)) == False{}: Bool}

# A node names a voter a liar only when it holds two ballots of that voter for
# the same step with different choices.
# An owner that signed once is never named a liar.
law VendNode.liars_are:
  for n: VendNode
  for v: String
  {List.contains(~String, ~String.eq, VendNode.liars(n), v) == True{}: Bool}
    -> Exists(
      Change,
      a => Exists(
        Change,
        b => {
          VendNode.holds(n, a) == True{}: Bool
        }
          & (
            {
              VendNode.holds(n, b) == True{}: Bool
            }
              & Exists(
                List<&2, U32>,
                s => Exists(
                  List<&2, U32>,
                  x => Exists(
                    List<&2, U32>,
                    y => {
                      Change.ballot(a) == Some{Ballot{v, s, x}}: Maybe<&2, Ballot>
                    }
                      & (
                        {
                          Change.ballot(b) == Some{Ballot{v, s, y}}: Maybe<&2, Ballot>
                        }
                          & ({x == y: List<&2, U32>} -> Empty)
                      )
                  )
                )
              )
          )
      )
    )

# And a node that holds two ballots of one voter for the same step, with
# different choices, names that voter a liar.
# Every node that holds both "version 4 is A" and "version 4 is B" of one owner
# names that owner a liar.
law VendNode.liars_found:
  for n: VendNode
  for a: Change
  for b: Change
  for v: String
  for s: List<&2, U32>
  for x: List<&2, U32>
  for y: List<&2, U32>
  {VendNode.holds(n, a) == True{}: Bool}
    -> {VendNode.holds(n, b) == True{}: Bool}
    -> {Change.ballot(a) == Some{Ballot{v, s, x}}: Maybe<&2, Ballot>}
    -> {Change.ballot(b) == Some{Ballot{v, s, y}}: Maybe<&2, Ballot>}
    -> ({x == y: List<&2, U32>} -> Empty)
    -> {List.contains(~String, ~String.eq, VendNode.liars(n), v) == True{}: Bool}

# Laws of a branch
# ----------------

# A move records a new version equal to the version that it points at.
# Moving main to version 5 of dev makes a version of main whose content is that
# of version 5 of dev.
law VendNode.move_equals:
  for n: VendNode
  for c: Ledgers.Line
  for k: Nat
  for i: Ledgers.Id
  for t: Ledgers.Line
  for v: Nat
  for h: Hashes.Hash
  for h2: Hashes.Hash
  Made(n, c, k, i, Request.Move{c, t, v})
    -> {VendNode.answer(n, Question.Content{c, k}) == Some{Reply.Hash{h}}: Maybe<&2, Reply>}
    -> {VendNode.answer(n, Question.Content{t, v}) == Some{Reply.Hash{h2}}: Maybe<&2, Reply>}
    -> {h == h2: Hashes.Hash}

# A mark that is Written names its version for good.
# The mark v1 of main, set on version 5, names version 5.
law VendNode.mark_names:
  for n: VendNode
  for c: Ledgers.Line
  for i: Ledgers.Id
  for m: String
  for v: Nat
  {
    VendNode.answer(
      n,
      Question.Status{c, i}
    )
      == Some{Reply.Status{Status.Written{}}}: Maybe<&2, Reply>
  }
    -> {
      VendNode.answer(
        n,
        Question.Request{c, i}
      )
        == Some{Reply.Ask{Request.Mark{c, m, v}}}: Maybe<&2, Reply>
    }
    -> {VendNode.answer(n, Question.Mark{c, m}) == Some{Reply.Number{v}}: Maybe<&2, Reply>}

# A merge turns Written only once each resource that clashed in it is resolved.
# A merge whose a.txt clashed is Written only after a Resolve of a.txt for it is
# decided.
law VendNode.merge_resolved:
  for n: VendNode
  for c: Ledgers.Line
  for i: Ledgers.Id
  for f: Ledgers.Line
  for ps: List<&2, String>
  for p: String
  {
    VendNode.answer(
      n,
      Question.Status{c, i}
    )
      == Some{Reply.Status{Status.Written{}}}: Maybe<&2, Reply>
  }
    -> {
      VendNode.answer(
        n,
        Question.Request{c, i}
      )
        == Some{Reply.Ask{Request.Merge{f, c}}}: Maybe<&2, Reply>
    }
    -> {VendNode.answer(n, Question.Clashes{c, i}) == Some{Reply.Names{ps}}: Maybe<&2, Reply>}
    -> {List.contains(~String, ~String.eq, ps, p) == True{}: Bool}
    -> Exists(
      Nat,
      k => Exists(
        Ledgers.Id,
        j => Exists(Maybe<&2, List<&2, U32>>, ws => Made(n, c, k, j, Request.Resolve{i, p, ws}))
      )
    )

# Laws of a resource
# ------------------

# The items of a resource are its words, in order: reading a resource in its
# format loses nothing.
# The functions and types of a C file, one after another, are the file.
law Format.items_whole:
  for p: String
  for ws: List<&2, U32>
  {List.concat(&2, U32, Format.items(p, ws)) == ws: List<&2, U32>}

# A diff applies: a after the diff from a to b is b.
# The diff from "hi" to "hello", applied to "hi", gives "hello".
law Format.apply_diff:
  for p: String
  for a: List<&2, U32>
  for b: List<&2, U32>
  {Format.apply(p, a, Format.diff(p, a, b)) == Some{b}: Maybe<&2, List<&2, U32>>}

# A merge never loses a change made on only one side: when ours did not change,
# it is theirs.
# Base "hi", ours "hi", theirs "hello": the merge is "hello".
law Format.merge_theirs:
  for p: String
  for base: Maybe<&2, List<&2, U32>>
  for theirs: Maybe<&2, List<&2, U32>>
  {Format.merge(p, base, base, theirs) == Some{theirs}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# And when theirs did not change, it is ours.
# Base "hi", ours "hello", theirs "hi": the merge is "hello".
law Format.merge_ours:
  for p: String
  for base: Maybe<&2, List<&2, U32>>
  for ours: Maybe<&2, List<&2, U32>>
  {Format.merge(p, base, ours, base) == Some{ours}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# And when both made the same change, it is that change.
# Base "hi", ours "hello", theirs "hello": the merge is "hello".
law Format.merge_same:
  for p: String
  for base: Maybe<&2, List<&2, U32>>
  for both: Maybe<&2, List<&2, U32>>
  {Format.merge(p, base, both, both) == Some{both}: Maybe<&2, Maybe<&2, List<&2, U32>>>}

# Mounting records what the resource held as a change of the node to the branch.
# Mounting a folder that holds a.txt "hi" to main makes the node read "hi" there.
law VendNode.mount_records:
  for n: VendNode
  for a: String
  for b: Ledgers.Line
  for ws: List<&2, U32>
  {VendNode.stopped(n) == False{}: Bool}
    -> {
      VendNode.view(
        VendNode.does(n, Deed.Mount{a, b, ws}),
        VendNode.name(n),
        b,
        a
      )
        == Some{Some{ws}}: Maybe<&2, Maybe<&2, List<&2, U32>>>
    }
