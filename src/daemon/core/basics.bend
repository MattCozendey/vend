import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ../replica/impl.bend as Replicas
import ../shared/requests.bend as Requests

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Ledgers.Id. A store is named by
# the request that started it. A line is a store itself (no branch) or one of
# its branches.

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# a and b are the same member
def Member.is_eq(a: Requests.Member, b: Requests.Member) -> Bool:
  match a b:
    case Requests.Member.Node{x} Requests.Member.Node{y}:
      String.eq(x, y)
    case Requests.Member.Group{x} Requests.Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument
# Codes
# -----

# the owners that the change c gives its chain, when it sets them
def Change.owners(c: Requests.Change) -> Maybe<&2, List<&2, String>>:
  match c:
    case Requests.Change.Own{g, at, os}:
      Some{os}
    case _:
      None{}

# The state
# ---------

# Requests.Content
# -------
# The content of a line is a tree in key spaces: the first word of a key says
# which. 0: the root of a resource's content (none: removed). 2 (in a store's
# tree): a group's members. 3: a merge's clash, open or settled. 4: the version
# vector, the newest version of each other line that the content came from. 5
# (in a store's tree): the first tip of each of its branches. 6: the line's
# owner group. 7 (in a store's tree): the names of its groups.

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the key of the members of the group g
def Key.group(g: String) -> List<&2, U32>:
  2 <> Codes.Code.text(g, [])

# the key of a line's owner group
def Key.owner() -> List<&2, U32>:
  [6]

# the key of the names of a store's groups
def Key.groups() -> List<&2, U32>:
  [7]

# the key of the clash of the resource n
def Key.clash(n: Resources.Name) -> List<&2, U32>:
  3 <> Resources.Name.code(n, [])

# the key of the line c in a version vector
def Key.vector(c: Ledgers.Chain) -> List<&2, U32>:
  4 <> Ledgers.Chain.code(c, [])

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
def Res.root(s: Replicas.Node<Requests.Ask>, h: Maybe<&2, Hashes.Hash>, n: Resources.Name) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.res(n)), ws => Res.read(ws))

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the content of the bytes b: the root of their rope
def Content.of(b: Texts.Bytes()) -> Requests.Content:
  Requests.Content.Root{Ropes.Put.root(Replicas.Bytes.rope(b))}

# the members of the group g in the store tree whose root is h, if g is there
def Members.in(s: Replicas.Node<Requests.Ask>, h: Maybe<&2, Hashes.Hash>, g: String) -> Maybe<&2, List<&2, Requests.Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Requests.Member>,
    Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.group(g)),
    ws => Replicas.Read.whole(List<&2, Requests.Member>, Requests.Members.code.read(ws))
  )

# the line of the request i of the change q
def Ask.chain(i: Ledgers.Id, q: Requests.Ask) -> Ledgers.Chain:
  Replicas.Arrival.chain(i, Requests.Ask.arrival(q))

# Ancestry
# --------
# A version came from the versions before it on its line, by number, and from
# those that its version vector names, at their numbers or before.

# the newest place of the line c that the content whose root is h came from
def Node.vector(s: Replicas.Node<Requests.Ask>, h: Maybe<&2, Hashes.Hash>, +c: Ledgers.Chain) -> Maybe<&2, Replicas.Place>:
  Maybe.bind(&2, List<&2, U32>, Replicas.Place, Replicas.Node.get(~Requests.Ask.machine(), s, h, Key.vector(c)), ws => Replicas.Place.read(c, ws))

# the version at the place px, whose content has the root hx, came from the
# one at the place pv
def Place.from(s: Replicas.Node<Requests.Ask>, +px: Replicas.Place, hx: Maybe<&2, Hashes.Hash>, +pv: Replicas.Place) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Replicas.Place.chain(px), Replicas.Place.chain(pv)),
    u => Replicas.Place.covers(px, pv),
    u => Replicas.Place.covered(Node.vector(s, hx, Replicas.Place.chain(pv)), pv)
  )

# Node.has once the places of x (mx) and of v (mv) and the root of x (mr) are
# known
def Has.of(
  s: Replicas.Node<Requests.Ask>,
  mx: Maybe<&2, Replicas.Place>,
  mv: Maybe<&2, Replicas.Place>,
  mr: Maybe<&2, Maybe<&2, Hashes.Hash>>
) -> Bool:
  match mx mv mr:
    case Some{px} Some{pv} Some{hx}:
      Place.from(s, px, hx, pv)
    case a b c:
      False{}

# x is v, or a version that v came from
def Node.has(+s: Replicas.Node<Requests.Ask>, +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Has.of(s, Replicas.Node.place(~Requests.Ask.machine(), s, x), Replicas.Node.place(~Requests.Ask.machine(), s, v), Replicas.Node.root(~Requests.Ask.machine(), s, x)),
    Ledgers.Id.is_eq(x, v)
  )

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(+s: Replicas.Node<Requests.Ask>, +x: Ledgers.Id, +y: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )
