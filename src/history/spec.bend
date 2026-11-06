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

# Who wrote a version. Agent: a writer through a front, by the name the
# front gives (the CLI reads it from the environment variable
# BEND_VER_AGENT; the MCP front uses its client's name). Outside: an edit
# the endpoint saw that no front made (an editor, a formatter, a build).
type Author is Data:
  Agent{name: String}
  Outside{}

# One version of the resource name, after its parents (none for the first,
# several for a merge). from: the name this resource moved from, on the
# first version after a move that the endpoint reported. author: who wrote
# it; part of the id, so two writers of the same content make two nodes.
type Node is Data:
  Node{
    name: Shared.Name,
    parents: List<&2, Shared.Bytes()>,
    body: Body,
    from: Maybe<&2, Shared.Name>,
    author: Author
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

# the bytes of an author: 0 for Outside, or 1 then the agent's name as
# UTF-8, framed
def Author.encode(a: Author) -> Shared.Bytes():
  match a:
    case Outside{}:
      [0]
    case Agent{n}:
      1 <> Store.Bytes.framed(Text.Text.encode(n))

# the bytes that a node's id hashes: name, parents, body, moved-from, then
# author; each part frames itself, so distinct nodes give distinct bytes
def Node.encode(n: Node) -> Shared.Bytes():
  match n:
    case Node{m, ps, b, f, a}:
      List.append(
        &2,
        U32,
        Name.encode(m),
        List.append(
          &2,
          U32,
          Ids.encode(ps),
          List.append(
            &2,
            U32,
            Body.encode(b),
            List.append(&2, U32, From.encode(f), Author.encode(a))
          )
        )
      )

# the id of n
def Node.id(n: Node) -> Shared.Bytes():
  Hash.Hash.blake3(Node.encode(n))

# a and b are the same node: they have the same bytes
def Node.same(a: Node, b: Node) -> Bool:
  Shared.Bytes.is_eq(Node.encode(a), Node.encode(b))

# distinct nodes have distinct bytes, so Node.same is equality
law node_encode_injective:
  for a: Node
  for b: Node
  for e: {Node.encode(a) == Node.encode(b): Shared.Bytes()}
  {a == b: Node}

# The nodes by the hex of their id, and the tips of each resource by the
# text of its name. The tips of a resource are its nodes that no node of it
# has as a parent, in ascending byte order of their ids. Several tips mean
# the resource forked: two lines, or two machines, wrote it apart.
type History is Data:
  History{nodes: Shared.Table<Node>, tips: Shared.Table<List<&2, Shared.Bytes()>>}

# a history with no nodes
def History.new() -> History:
  History{Shared.Table.new(Node), Shared.Table.new(List<&2, Shared.Bytes()>)}

# the node with id x, or None
def History.get(h: History, x: Shared.Bytes()) -> Maybe<&2, Node>:
  match h:
    case History{ns, ts}:
      Shared.Table.get(Node, ns, Hash.Hash.hex(x))

# h holds a node with id x
def History.has(h: History, x: Shared.Bytes()) -> Bool:
  Maybe.is_some(&2, Node, History.get(h, x))

# the other node that m holds where v belongs, if any
def History.collides.of(m: Maybe<&2, Node>, v: Node) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{w}:
      Bool.not(Node.same(w, v))

# h holds another node under the id of v
def History.collides(h: History, +v: Node) -> Bool:
  History.collides.of(History.get(h, Node.id(v)), v)

# the tips of the resource n: none when it has no version yet
def History.tips(h: History, n: Shared.Name) -> List<&2, Shared.Bytes()>:
  match h:
    case History{ns, ts}:
      Maybe.default(
        &2,
        List<&2, Shared.Bytes()>,
        Shared.Table.get(List<&2, Shared.Bytes()>, ts, Shared.Name.show(n)),
        []
      )

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

# who wrote v
def Node.author(v: Node) -> Author:
  match v:
    case Node{n, ps, b, f, a}:
      a

# the resource of v
def Node.name(v: Node) -> Shared.Name:
  match v:
    case Node{n, ps, b, f, a}:
      n

# the parents of v
def Node.parents(v: Node) -> List<&2, Shared.Bytes()>:
  match v:
    case Node{n, ps, b, f, a}:
      ps

# h is well formed: every node it holds sits under its own id, so what
# get finds for x is a node whose id has the hex of x. History.new is well
# formed and add keeps it so (new_ok, add_ok), so every history the core
# builds is. Only laws about where a node sits need it.
def History.Ok(h: History) -> Type:
  @x: Shared.Bytes() -> @v: Node -> {
    History.get(h, x) == Some{v}: Maybe<&2, Node>
  } -> {Hash.Hash.hex(Node.id(v)) == Hash.Hash.hex(x): String}

# Adding
# ------
# The history only grows. Which version a working copy follows, and who may
# move it forward, belongs to lines (src/lines), not to the history: two
# lines that write one resource apart simply fork it here.

# Why an add is refused. Missing: a parent that the history does not hold.
# Collides: the history holds another node a under the id of the new node
# b (two nodes, one hash); it never keeps both, so it names them.
type Refusal is Data:
  Missing{parent: Shared.Bytes()}
  Collides{a: Node, b: Node}

# A finished add: the history after it, and the id of the node.
type Added is Data:
  Added{history: History, id: Shared.Bytes()}

# h with the node v; or the parent of v that h lacks; or the other node
# that h holds under the id of v. A node that h holds already changes
# nothing.
law History.add:
  for h: History
  for v: Node
  Result<&2, &2, Refusal, Added>

# an add is refused exactly when a parent of the node is missing, or the
# history holds another node under its id
law add_refused:
  for h: History
  for v: Node
  {
    Result.is_fail(
      &2,
      &2,
      Refusal,
      Added,
      History.add(h, v)
    )
      == Bool.or(Bool.not(Ids.all_in(h, Node.parents(v))), History.collides(h, v)): Bool
  }

# an add keeps exactly its node, under its id
law add_node:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Refusal, Added>}
  {History.get(g, x) == Some{v}: Maybe<&2, Node>} & {x == Node.id(v): Shared.Bytes()}

# a refused add for a collision, in a well-formed history, names another
# node with the same id
law add_collides:
  for h: History
  for v: Node
  for a: Node
  for b: Node
  for k: History.Ok(h)
  for c: {History.add(h, v) == Fail{Collides{a, b}}: Result<&2, &2, Refusal, Added>}
  {Node.same(a, b) == False{}: Bool} & {Node.id(a) == Node.id(b): Shared.Bytes()}

# an add keeps every node
law add_keeps:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for y: Shared.Bytes()
  for w: Node
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Refusal, Added>}
  for o: {History.get(h, y) == Some{w}: Maybe<&2, Node>}
  {History.get(g, y) == Some{w}: Maybe<&2, Node>}

# adding a node that the history holds, with its parents, changes nothing
law add_idempotent:
  for h: History
  for v: Node
  for p: {Ids.all_in(h, Node.parents(v)) == True{}: Bool}
  for o: {History.get(h, Node.id(v)) == Some{v}: Maybe<&2, Node>}
  {History.add(h, v) == Done{Added{h, Node.id(v)}}: Result<&2, &2, Refusal, Added>}

# after an add of a node that h did not hold, the node is a tip of its
# resource, and none of its parents is (a node that h held already changes
# nothing, and may have children)
law add_tips:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for p: Shared.Bytes()
  for n: {History.has(h, Node.id(v)) == False{}: Bool}
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Refusal, Added>}
  for q: {Ids.has(Node.parents(v), p) == True{}: Bool}
  {Ids.has(History.tips(g, Node.name(v)), x) == True{}: Bool} &
    {Ids.has(History.tips(g, Node.name(v)), p) == False{}: Bool}

# a new history is well formed
law new_ok:
  History.Ok(History.new())

# an add keeps a history well formed
law add_ok:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for k: History.Ok(h)
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Refusal, Added>}
  History.Ok(g)

# an add touches only the tips of its own resource
law add_frames:
  for h: History
  for v: Node
  for g: History
  for x: Shared.Bytes()
  for m: Shared.Name
  for a: {History.add(h, v) == Done{Added{g, x}}: Result<&2, &2, Refusal, Added>}
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
