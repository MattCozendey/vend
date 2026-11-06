import Base
import ../hash/spec.bend as Hash
import ../shared.bend as Shared
import ../store/spec.bend as Store
import ../views/text/spec.bend as Text

# The history: an append-only DAG of versions. Each node is one version of
# one resource and names its parents. Lines (src/lines) choose which
# versions a working copy follows; where lines or machines write apart, a
# resource forks, and a merge node joins the forks. A node's id is the
# BLAKE3 hash of its encoding, so a node means the same everywhere, and two
# histories sync by taking the union of their nodes.

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

# the bytes of a name: its space, then its path, each as UTF-8 and framed
def Name.encode(n: Shared.Name) -> Shared.Bytes():
  match n:
    case Shared.Name{sp, p}:
      List.append(
        &2,
        U32,
        Store.Bytes.framed(Text.Text.encode(sp)),
        Store.Bytes.framed(Text.Text.encode(p))
      )

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

# The nodes by the hex of their id, and the tips of each resource by the
# text of its name. The tips of a resource are its nodes that no node of it
# has as a parent, in ascending byte order of their ids. Several tips mean
# the resource forked: two lines, or two machines, wrote it apart.
type History is Data:
  History{nodes: Map<&2, Maybe<&2, Node>>, tips: Map<&2, List<&2, Shared.Bytes()>>}

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
    case History{ns, ts}:
      History.get.got(Map.get(Maybe<&2, Node>, None{}, ns, Hash.Hash.hex(x)))

# h holds a node with id x
def History.has(h: History, x: Shared.Bytes()) -> Bool:
  Maybe.is_some(&2, Node, History.get(h, x))

# the tips of the found pair
def History.tips.got(
  r: Map<&2, List<&2, Shared.Bytes()>> & List<&2, Shared.Bytes()>
) -> List<&2, Shared.Bytes()>:
  (m, v) = r
  v

# the tips of the resource n: none when it has no version yet
def History.tips(h: History, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  match h:
    case History{ns, ts}:
      History.tips.got(Map.get(List<&2, Shared.Bytes()>, [], ts, Shared.Name.show(n)))

# xs and ys are the same ids in the same order
def Ids.is_eq(xs: List<&2, Shared.Bytes()>, ys: List<&2, Shared.Bytes()>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      List.all.if(u => Ids.is_eq(xt, yt), Shared.Bytes.is_eq(x, y))
    case _ _:
      False{}

# xs holds the id x
def Ids.has(xs: List<&2, Shared.Bytes()>, x: Shared.Bytes()) -> Bool:
  List.contains(~Shared.Bytes(), ~Shared.Bytes.is_eq, xs, x)

# every id of xs is a node of h
def Ids.all_in(+h: History, xs: List<&2, Shared.Bytes()>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      List.all.if(u => Ids.all_in(h, t), History.has(h, x))

# the resource of v
def Node.name(v: Node) -> Shared.Name:
  match v:
    case Node{n, ps, b, f}:
      n

# the parents of v
def Node.parents(v: Node) -> List<&2, Shared.Bytes()>:
  match v:
    case Node{n, ps, b, f}:
      ps

# Adding
# ------
# The history only grows. Which version a working copy follows, and who may
# move it forward, belongs to lines (src/lines), not to the history: two
# lines that write one resource apart simply fork it here.

# Why an add is refused: a parent that the history does not hold.
type Missing is Data:
  Missing{parent: Shared.Bytes()}

# A finished add: the history after it, and the id of the node.
type Added is Data:
  Added{history: History, id: Shared.Bytes()}

# h with the node v, or the parent of v that h lacks; a node that h holds
# already changes nothing
law History.add:
  for h: History
  for v: Node
  Result<&2, &2, Missing, Added>

# an add is refused exactly when a parent of the node is missing
law add_refused:
  for h: History
  for v: Node
  {
    Result.is_fail(
      &2,
      &2,
      Missing,
      Added,
      History.add(h, v)
    )
      == Bool.not(Ids.all_in(h, Node.parents(v))): Bool
  }

# an add keeps exactly its node, under its id
law add_node:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Missing, Added>}
  {History.get(g, x) == Some{v}: Maybe<&2, Node>} & {x == Node.id(v): Shared.Bytes()}

# an add keeps every node
law add_keeps:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for y: Shared.Bytes()
  for w: Node
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Missing, Added>}
  for o: {History.get(h, y) == Some{w}: Maybe<&2, Node>}
  {History.get(g, y) == Some{w}: Maybe<&2, Node>}

# adding a node that the history holds changes nothing
law add_idempotent:
  for h: History
  for v: Node
  for o: {History.get(h, Node.id(v)) == Some{v}: Maybe<&2, Node>}
  {History.add(h, v) == Done{Added{h, Node.id(v)}}: Result<&2, &2, Missing, Added>}

# after an add, the node is a tip of its resource, and none of its parents
# is
law add_tips:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for p: Shared.Bytes()
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Missing, Added>}
  for q: {Ids.has(Node.parents(v), p) == True{}: Bool}
  {Ids.has(History.tips(g, Node.name(v)), x) == True{}: Bool} &
    {Ids.has(History.tips(g, Node.name(v)), p) == False{}: Bool}

# an add touches only the tips of its own resource
law add_frames:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for m: Shared.Name
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Missing, Added>}
  for d: {String.eq(Shared.Name.show(m), Shared.Name.show(Node.name(v))) == False{}: Bool}
  {History.tips(g, m) == History.tips(h, m): List<&2, Shared.Bytes()>}

# Sync
# ----
# Two histories join by the union of their nodes; the tips of a resource
# are then the ids among the tips of both sides that are no ancestor of
# another. Join is a semilattice, so machines can sync in any order, any
# number of times, and agree.

# h and g hold the same nodes and the same tips
def History.Same(h: History, g: History) -> Type:
  (@x: Shared.Bytes() -> {History.get(h, x) == History.get(g, x): Maybe<&2, Node>}) &
    (@n: Shared.Name -> {History.tips(h, n) == History.tips(g, n): List<&2, Shared.Bytes()>})

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
