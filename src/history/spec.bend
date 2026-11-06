import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ../store/spec.bend as Store
import ../views/text/spec.bend as Text

# The history: an append-only DAG of versions. Each node is one version of
# one resource and names its parents. On one machine, compare-and-swap keeps
# each resource a single chain; across machines, chains may fork and a merge
# node joins them. A node's id is the BLAKE3 hash of its encoding, so a node
# means the same everywhere, and two histories sync by taking the union of
# their nodes.

# What a version holds: content, as the store root of its bytes, or the
# resource is gone.
type Body is Data:
  Has{root: Store.Ref}
  Gone{}

# One version of the resource name, after its parents (none for the first,
# several for a merge). from: the name this resource moved from, on the
# first version after a move that the endpoint reported.
type Node is Data:
  Node{
    name: Shared.Name,
    parents: List<&2, Shared.Bytes()>,
    body: Body,
    from: Maybe<&2, Shared.Name>
  }

# the bytes of a name: its text as UTF-8, framed
def Name.encode(n: Shared.Name) -> Shared.Bytes():
  Store.Bytes.framed(Text.Text.encode(Shared.Name.show(n)))

# the bytes of ids, framed, after their number
def Ids.encode(xs: List<&2, Shared.Bytes()>) -> Shared.Bytes():
  +xs = xs
  List.append(&2, U32, Store.Leb.of(List.length(&2, Shared.Bytes(), xs)), Store.Bytes.frame_all(xs))

# the bytes of a body: 0 then the root, or 1 for Gone
def Body.encode(b: Body) -> Shared.Bytes():
  match b:
    case Has{r}:
      0 <> Store.Ref.encode(r)
    case Gone{}:
      [1]

# the bytes of a moved-from name: 0 for none, or 1 then the name
def From.encode(f: Maybe<&2, Shared.Name>) -> Shared.Bytes():
  match f:
    case None{}:
      [0]
    case Some{m}:
      1 <> Name.encode(m)

# the bytes that a node's id hashes: name, parents, body, then moved-from;
# each part frames itself, so distinct nodes give distinct bytes
def Node.encode(n: Node) -> Shared.Bytes():
  match n:
    case Node{m, ps, b, f}:
      List.append(
        &2,
        U32,
        Name.encode(m),
        List.append(&2, U32, Ids.encode(ps), List.append(&2, U32, Body.encode(b), From.encode(f)))
      )

# the id of n
def Node.id(n: Node) -> Shared.Bytes():
  Hash.Hash.blake3(Node.encode(n))

# The nodes by the hex of their id, and the heads of each resource by the
# text of its name. The heads of a resource are its nodes that no other node
# has as a parent, in ascending byte order of their ids.
type History is Data:
  History{nodes: Map<&2, Maybe<&2, Node>>, heads: Map<&2, List<&2, Shared.Bytes()>>}

# a history with no nodes
def History.new() -> History:
  History{Map.new(&2, Maybe<&2, Node>), Map.new(&2, List<&2, Shared.Bytes()>)}

# the node of the found pair
def History.get.got(r: Map<&2, Maybe<&2, Node>> & Maybe<&2, Node>) -> Maybe<&2, Node>:
  (m, v) = r
  v

# the node with id x, or None
def History.get(h: History, x: Shared.Bytes()) -> Maybe<&2, Node>:
  match h:
    case History{ns, hs}:
      History.get.got(Map.get(Maybe<&2, Node>, None{}, ns, Hash.Hash.hex(x)))

# the heads of the found pair
def History.heads.got(
  r: Map<&2, List<&2, Shared.Bytes()>> & List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  (m, v) = r
  v

# the heads of the resource n: none when it has no version yet
def History.heads(h: History, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  match h:
    case History{ns, hs}:
      History.heads.got(Map.get(List<&2, Shared.Bytes()>, [], hs, Shared.Name.show(n)))

# xs and ys are the same ids in the same order
law Ids.is_eq:
  for xs: List<&2, Shared.Bytes()>
  for ys: List<&2, Shared.Bytes()>
  Bool

# Committing
# ----------

# Why a commit is refused: the heads it met.
type Refused is Data:
  Refused{now: List<&2, Shared.Bytes()>}

# A finished commit: the history after it, and the new node's id.
type Committed is Data:
  Committed{history: History, id: Shared.Bytes()}

# h with a new version of n whose parents are the heads the writer saw,
# expect; refused when they are not the heads of n now. With one head this
# appends to the chain; with several it is a merge.
law History.commit:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  Result<&2, &2, Refused, Committed>

# a commit is refused exactly when the writer did not see the heads of now
law commit_refused:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  {
    Result.is_fail(
      &2,
      &2,
      Refused,
      Committed,
      History.commit(h, n, expect, body, from)
    )
      == Bool.not(Ids.is_eq(expect, History.heads(h, n))): Bool
  }

# a commit adds exactly its node, under its id
law commit_node:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  for g: History
  for x: Shared.Bytes()
  for c: {
    History.commit(
      h,
      n,
      expect,
      body,
      from
    )
      == Done{Committed{g, x}}: Result<&2, &2, Refused, Committed>
  }
  {History.get(g, x) == Some{Node{n, expect, body, from}}: Maybe<&2, Node>} &
    {x == Node.id(Node{n, expect, body, from}): Shared.Bytes()}

# after a commit, its node is the one head of its resource
law commit_head:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  for g: History
  for x: Shared.Bytes()
  for c: {
    History.commit(
      h,
      n,
      expect,
      body,
      from
    )
      == Done{Committed{g, x}}: Result<&2, &2, Refused, Committed>
  }
  {History.heads(g, n) == [x]: List<&2, Shared.Bytes()>}

# a commit is append-only: every node stays
law commit_keeps:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  for g: History
  for x: Shared.Bytes()
  for y: Shared.Bytes()
  for v: Node
  for c: {
    History.commit(
      h,
      n,
      expect,
      body,
      from
    )
      == Done{Committed{g, x}}: Result<&2, &2, Refused, Committed>
  }
  for o: {History.get(h, y) == Some{v}: Maybe<&2, Node>}
  {History.get(g, y) == Some{v}: Maybe<&2, Node>}

# a commit touches only the heads of its own resource
law commit_frames:
  for h: History
  for n: Shared.Name
  for expect: List<&2, Shared.Bytes()>
  for body: Body
  for from: Maybe<&2, Shared.Name>
  for g: History
  for x: Shared.Bytes()
  for m: Shared.Name
  for c: {
    History.commit(
      h,
      n,
      expect,
      body,
      from
    )
      == Done{Committed{g, x}}: Result<&2, &2, Refused, Committed>
  }
  for d: {String.eq(Shared.Name.show(m), Shared.Name.show(n)) == False{}: Bool}
  {History.heads(g, m) == History.heads(h, m): List<&2, Shared.Bytes()>}

# Sync
# ----
# Two histories join by the union of their nodes; the heads of a resource
# are then the ids among both sides' heads that are no ancestor of another.
# Join is a semilattice, so machines can sync in any order, any number of
# times, and agree.

# h and g hold the same nodes and the same heads
def History.Same(h: History, g: History) -> Type:
  (@x: Shared.Bytes() -> {History.get(h, x) == History.get(g, x): Maybe<&2, Node>}) &
    (@n: Shared.Name -> {History.heads(h, n) == History.heads(g, n): List<&2, Shared.Bytes()>})

# the union of h and g
law History.join:
  for h: History
  for g: History
  History

# a join keeps every node of both sides
law join_keeps:
  for h: History
  for g: History
  for x: Shared.Bytes()
  for v: Node
  for o: {Maybe.or(&2, Node, History.get(h, x), History.get(g, x)) == Some{v}: Maybe<&2, Node>}
  {History.get(History.join(h, g), x) == Some{v}: Maybe<&2, Node>}

# a join adds no node that neither side had
law join_adds_nothing:
  for h: History
  for g: History
  for x: Shared.Bytes()
  for o: {Maybe.or(&2, Node, History.get(h, x), History.get(g, x)) == None{}: Maybe<&2, Node>}
  {History.get(History.join(h, g), x) == None{}: Maybe<&2, Node>}

# the order of a join does not matter
law join_commutes:
  for h: History
  for g: History
  History.Same(History.join(h, g), History.join(g, h))

# the grouping of joins does not matter
law join_associates:
  for a: History
  for b: History
  for c: History
  History.Same(History.join(History.join(a, b), c), History.join(a, History.join(b, c)))

# joining a history with itself changes nothing
law join_idempotent:
  for h: History
  History.Same(History.join(h, h), h)
