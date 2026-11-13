import Base
import ../resource/formats.bend as Formats
import ../resource/resources.bend as Resources
import ../writer/requests.bend as Requests
import ./replica.bend as Replicas
import ./shared/ledger.bend as Ledgers
import ./shared/rope.bend as Ropes
import ./shared/shared/shared/code.bend as Codes
import ./shared/shared/shared/hash.bend as Hashes
import ./shared/shared/shared/shared.bend as Shared
import ./shared/shared/text.bend as Texts
import ./shared/tree.bend as Trees

# The ledger and the kernel of Vend
# ---------------------------------

# a ledger for the requests of Vend
def Led() -> Type:
  Replicas.Led(Requests.Ask.machine())

# what the ledger d is kept as
def L(d: Led()) -> Data:
  Replicas.Led.L(Requests.Ask.machine(), d)

# a kernel for the requests of Vend, on the ledger d
def Kern(-d: Led()) -> Type:
  Replicas.Kernel(Requests.Ask.machine(), d)

# Names
# -----

# a branch: the root of its store, and its name
type Branch is Data:
  Branch{store: Hashes.Hash, name: String}

# the line of the branch b
def Branch.line(b: Branch) -> Ledgers.Line:
  match b:
    case Branch{st, n}:
      Ledgers.Line{st, Some{n}}

# a version of a branch, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{branch: Branch, version: Ledgers.Id}
  Point.Head{branch: Branch}
  Point.Mark{branch: Branch, mark: String}

# Resources in a tree
# -------------------

# a and b are the same resource, or both none: the same format and content
def Res.same(a: Maybe<&2, Requests.Res>, b: Maybe<&2, Requests.Res>) -> Bool:
  Shared.Maybe.is_eq(
    ~Requests.Res,
    ~(x => y => Codes.Code.is_eq(~Requests.Res, ~Requests.Res.code, x, y)),
    a,
    b
  )

# the key of the resource n
def Key.res(n: Resources.Name) -> List<&2, U32>:
  0 <> Resources.Name.code(n, [])

# the value of the resource m in a tree (none: it is not there; the key goes)
def Res.value(m: Maybe<&2, Requests.Res>) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(&2, Requests.Res, List<&2, U32>, m, x => Some{Requests.Res.code(x, [])})

# the resource in the value m, if any
def Res.found(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Requests.Res>:
  Codes.Code.whole.of(~Requests.Res, ~Requests.Res.code, ~Requests.Res.code.read, m)

# the root of the content of the resource n in the tree whose root is h, or
# that it is not there (none: l lacks a node of the tree)
def Res.find(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Requests.Res>,
    Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the bytes under the rope root r (none: l lacks a node)
def Root.bytes(~d: Led(), l: L(d), r: Ropes.Root) -> Maybe<&2, Texts.Bytes()>:
  Ropes.Rope.bytes(~L(d), ~Replicas.Led.fetch(~Requests.Ask.machine(), ~d), l, r)

# the root of the bytes of the resource x
def Res.root(x: Requests.Res) -> Ropes.Root:
  match x:
    case Requests.Res{f, r}:
      r

# the hash of the format of the resource x
def Res.format.hash(x: Requests.Res) -> Hashes.Hash:
  match x:
    case Requests.Res{f, r}:
      f

# the bytes of the resource m (none: it is not there, or l lacks a node)
def Res.bytes(~d: Led(), l: L(d), m: Maybe<&2, Requests.Res>) -> Maybe<&2, Texts.Bytes()>:
  Maybe.bind(&2, Requests.Res, Texts.Bytes(), m, x => Root.bytes(~d, l, Res.root(x)))

# the format that the ledger holds under the hash h (none: l lacks it, or it
# is not the code of a format)
def Format.at(~d: Led(), l: L(d), h: Hashes.Hash) -> Maybe<&2, Formats.Format>:
  Codes.Code.whole.of(
    ~Formats.Format,
    ~Formats.Format.code,
    ~Formats.Format.code.read,
    Replicas.Led.fetch(~Requests.Ask.machine(), ~d)(l)(h)
  )

# the format of the resource x
def Res.format(~d: Led(), l: L(d), x: Requests.Res) -> Maybe<&2, Formats.Format>:
  Format.at(~d, l, Res.format.hash(x))

# Versions
# --------
# A version is a request that its branch took. Its content is the root that
# the log of the branch holds for its number.

# The rules of the kernel
# -----------------------
# What each change does to its line (README). A rule reads the ledger and the
# tip of its own line, and nothing else: content of another line comes with
# the change (Requests.Source), so no rule reads the history of a line. A rule
# waits for what the ledger lacks (none), and refuses only on what it knows.
# The owners of a line keep each part of what they decide: a rule waits for
# the bytes and the trees that its result holds.

# the act that takes the tree p as the content, after the nodes ns, with the
# owners vs if any
def Act.put(
  vs: Maybe<&2, List<&2, String>>,
  ns: List<&2, List<&2, U32>>,
  p: Maybe<&2, Trees.Edit>
) -> Maybe<&2, Replicas.Act>:
  match p:
    case None{}:
      None{}
    case Some{+x}:
      Some{
        Replicas.Act.Taken{
          vs,
          Trees.Edit.root(x),
          List.append(&2, List<&2, U32>, ns, Trees.Edit.nodes(x))
        }
      }

# l holds the resource m: its format and its bytes (a resource that is not
# there needs none)
def Res.kept(~d: Led(), +l: L(d), m: Maybe<&2, Requests.Res>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{+x}:
      List.all.if(
        u => Maybe.is_some(&2, Texts.Bytes(), Root.bytes(~d, l, Res.root(x))),
        Maybe.is_some(&2, Formats.Format, Res.format(~d, l, x))
      )

# the binding x is not a resource, or l holds its format and its bytes
def Res.held(~d: Led(), l: L(d), x: Trees.Binding) -> Bool:
  match x:
    case Trees.Binding{Con{0, r}, v}:
      Res.kept(~d, l, Codes.Code.whole.read(~Requests.Res, ~Requests.Res.code, ~Requests.Res.code.read, v))
    case _:
      True{}

# l holds the format and the bytes of each resource among the bindings xs
def Res.all_held(~d: Led(), +l: L(d), xs: List<&2, Trees.Binding>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, rest}:
      List.all.if(u => Res.all_held(~d, l, rest), Res.held(~d, l, x))

# the bindings of the tree whose root is h whose keys start with p (none: l
# lacks a node of the tree)
def Tree.range(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, p: List<&2, U32>) -> Maybe<&2, List<&2, Trees.Binding>>:
  Replicas.Tree.range(~Requests.Ask.machine(), ~d, l, h, p)

# l holds the whole of the tree whose root is h: each of its nodes, and the
# format and the bytes of each of its resources. A clear def: it reads each
# resource
def Tree.kept(~d: Led(), +l: L(d), h: Maybe<&2, Hashes.Hash>) -> Bool:
  Maybe.default(
    &2,
    Bool,
    Maybe.bind(
      &2,
      List<&2, Trees.Binding>,
      Bool,
      Tree.range(~d, l, h, []),
      bs => Some{Res.all_held(~d, l, bs)}
    ),
    False{}
  )

# l holds each node of the tree whose root is h
def Tree.whole(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>) -> Bool:
  Maybe.is_some(&2, List<&2, Trees.Binding>, Tree.range(~d, l, h, []))

# k when l holds the whole of the tree whose root is h, else wait
def Tree.when_kept(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  k: Unit -> Maybe<&2, Replicas.Act>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(Maybe<&2, Replicas.Act>, Tree.kept(~d, l, h), k, u => None{})

# the root that the content x gives the resource n at the tip t: a root, or
# what a version of the same line held (none: wait for that version, or for a
# node)
def Content.find(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  x: Requests.Content
) -> Maybe<&2, Maybe<&2, Requests.Res>>:
  match x:
    case Requests.Content.New{r}:
      Some{Some{r}}
    case Requests.Content.Of{i}:
      Maybe.bind(
        &2,
        Maybe<&2, Hashes.Hash>,
        Maybe<&2, Requests.Res>,
        Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i),
        h => Res.find(~d, l, h, n)
      )

# the root of the content of the base m of a write, at the tip t (none: the
# line did not take the base yet). A resource with no base starts from the
# empty tree
def Base.root(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Id>
) -> Maybe<&2, Maybe<&2, Hashes.Hash>>:
  match m:
    case None{}:
      Some{None{}}
    case Some{i}:
      Replicas.Tip.version(~Requests.Ask.machine(), ~d, l, t, i)

# the act that sets the resource n to the root new in the content of the tip
# t, once l holds its bytes (none: wait for them)
def Res.set(
  ~d: Led(),
  +l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  +new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Res.kept(~d, l, new),
    u => Act.put(
      None{},
      [],
      Replicas.Tree.put(
        ~Requests.Ask.machine(),
        ~d,
        l,
        Replicas.Tip.content(t),
        Key.res(n),
        Res.value(new)
      )
    ),
    u => None{}
  )

# Write.act once the resource holds ours at the tip, held at the base and
# gets new: taken when ours is what the base held, else stale
def Write.act.of(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  n: Resources.Name,
  ours: Maybe<&2, Requests.Res>,
  held: Maybe<&2, Requests.Res>,
  new: Maybe<&2, Requests.Res>
) -> Maybe<&2, Replicas.Act>:
  Shared.Bool.when(
    Maybe<&2, Replicas.Act>,
    Res.same(ours, held),
    u => Res.set(~d, l, t, n, new),
    u => Some{Replicas.Act.Stale{}}
  )

# what a write of the resource n since base, with the content x, does at the
# tip t of a branch: it is taken when n holds at t what it held at base, and
# then n holds x; else it is stale. So two writers that change one resource
# are a conflict, and the second is refused
def Write.act(
  ~d: Led(),
  +l: L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Requests.Content
) -> Maybe<&2, Replicas.Act>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Replicas.Act,
    Res.find(~d, l, Replicas.Tip.content(t), n),
    ours => Maybe.bind(
      &2,
      Maybe<&2, Hashes.Hash>,
      Replicas.Act,
      Base.root(~d, l, t, base),
      h => Maybe.bind(
        &2,
        Maybe<&2, Requests.Res>,
        Replicas.Act,
        Res.find(~d, l, h, n),
        held => Maybe.bind(
          &2,
          Maybe<&2, Requests.Res>,
          Replicas.Act,
          Content.find(~d, l, t, n, x),
          new => Write.act.of(~d, l, t, n, ours, held, new)
        )
      )
    )
  )

# the root of the tree of the source s
def Source.root(s: Requests.Source) -> Maybe<&2, Hashes.Hash>:
  match s:
    case Requests.Source{v, h}:
      h

# what a move to the source s does: the branch takes it, and its content is
# the tree of s, the same tree (none: wait for the whole tree)
def Move.act(~d: Led(), l: L(d), s: Requests.Source) -> Maybe<&2, Replicas.Act>:
  +h = Source.root(s)
  Tree.when_kept(~d, l, h, u => Some{Replicas.Act.Taken{None{}, h, []}})

# the first tip of a new branch whose content is h, at the tip t of its
# store: it starts with no log, and the owners of the store own it
def Branch.tip(t: Replicas.Tip, h: Maybe<&2, Hashes.Hash>) -> Replicas.Tip:
  Replicas.Tip{h, None{}, 0, Replicas.Tip.voters(t)}

# what a new branch b from the source m does, at the tip t of its store: the
# store opens the branch, empty or with the tree of the source (none: wait for
# the whole tree)
def Branch.act(
  ~d: Led(),
  l: L(d),
  +t: Replicas.Tip,
  +b: String,
  m: Maybe<&2, Requests.Source>
) -> Maybe<&2, Replicas.Act>:
  match m:
    case None{}:
      Some{Replicas.Act.Opens{b, Branch.tip(t, None{}), []}}
    case Some{s}:
      +h = Source.root(s)
      Tree.when_kept(~d, l, h, u => Some{Replicas.Act.Opens{b, Branch.tip(t, h), []}})

# what a first key k of the node n does, at the tip t of a store: the content
# of the store holds the key for the node
def Key.act(~d: Led(), l: L(d), t: Replicas.Tip, n: String, k: Hashes.Hash) -> Maybe<&2, Replicas.Act>:
  Act.put(
    None{},
    [],
    Replicas.Tree.put(
      ~Requests.Ask.machine(),
      ~d,
      l,
      Replicas.Tip.content(t),
      Requests.Key.seal(n),
      Some{Hashes.Hash.code(k, [])}
    )
  )

# Clashes
# -------

# the key of the open clashes of the merge of the request k: the resources
# that still clash after it. So what a merge left is one read, and no walk
def Key.clashes(k: Ledgers.Id) -> List<&2, U32>:
  3 <> Ledgers.Id.code(k, [])

# the value of the open clashes ns of a merge (none: no clash is open; the
# key goes)
def Clash.value(ns: List<&2, Resources.Name>) -> Maybe<&2, List<&2, U32>>:
  match ns:
    case Nil{}:
      None{}
    case Con{n, rest}:
      Some{Codes.Code.list(~Resources.Name, ~Resources.Name.code, n <> rest, [])}

# the resources that still clash after the merge k, in the tree h (none: l
# lacks a node, so a read cannot tell)
def Clash.names(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  k: Ledgers.Id
) -> Maybe<&2, List<&2, Resources.Name>>:
  Maybe.map(
    &2,
    Maybe<&2, List<&2, Resources.Name>>,
    List<&2, Resources.Name>,
    m => Maybe.default(&2, List<&2, Resources.Name>, m, []),
    Replicas.Tip.known(
      ~List<&2, Resources.Name>,
      ~(ns => r => Codes.Code.list(~Resources.Name, ~Resources.Name.code, ns, r)),
      ~(ws => Codes.Code.list.read(~Resources.Name, ~Resources.Name.code.read, ws)),
      Replicas.Tree.find(~Requests.Ask.machine(), ~d, l, h, Key.clashes(k))
    )
  )

# a resource of the tree h still clashes after the merge k
def Clash.left(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, k: Ledgers.Id) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => Bool.not(List.is_empty(&2, Resources.Name, ns)),
    Clash.names(~d, l, h, k)
  )

# the resources ns, with n when it is not among them
def Clash.put(+n: Resources.Name, +ns: List<&2, Resources.Name>) -> List<&2, Resources.Name>:
  Shared.Bool.when(
    List<&2, Resources.Name>,
    List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    u => ns,
    u => n <> ns
  )

# the clash that the merge k opened in the resource n is open in the tree h
def Clash.open(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  k: Ledgers.Id
) -> Maybe<&2, Bool>:
  Maybe.map(
    &2,
    List<&2, Resources.Name>,
    Bool,
    ns => List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
    Clash.names(~d, l, h, k)
  )

# Answers
# -------

# what a node answers to a change (README, Vend Writer). Written: its branch
# took it, and it is a version. Conflicted: a merge, or a resolve of one,
# after which resources still clash (the merge). Pending: its owners did not
# decide it yet. Stale: its owners refused it at their newest version.
# Refused: its ID names another change
type Answer is Data:
  Answer.Written{}
  Answer.Conflicted{merge: Ledgers.Id}
  Answer.Pending{}
  Answer.Stale{}
  Answer.Refused{}

# Written, or Conflicted while a resource still clashes after the merge k;
# Pending while l lacks a node of the clashes
def Answer.merged.of(m: Maybe<&2, Bool>, +k: Ledgers.Id) -> Answer:
  match m:
    case None{}:
      Answer.Pending{}
    case Some{c}:
      Shared.Bool.when(Answer, c, u => Answer.Conflicted{k}, u => Answer.Written{})

# Answer.merged.of, once l tells whether a resource of the tree h still
# clashes after the merge k
def Answer.merged(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, +k: Ledgers.Id) -> Answer:
  Answer.merged.of(Clash.left(~d, l, h, k), k)

# the answer to the change q of the request i, which its branch took, when
# the content of the branch is h
def Answer.taken(
  ~d: Led(),
  l: L(d),
  h: Maybe<&2, Hashes.Hash>,
  i: Ledgers.Id,
  q: Requests.Ask
) -> Answer:
  match q:
    case Requests.Ask.On{st, b, Requests.Change.Merge{v, base}}:
      Answer.merged(~d, l, h, i)
    case Requests.Ask.On{st, b, Requests.Change.Resolve{k, n, x}}:
      Answer.merged(~d, l, h, k)
    case _:
      Answer.Written{}

# the answer to the request i of the change q, whose entry has the hash a, by
# the outcome o of its ID at the tip t of its line: Pending while there is
# none; Refused when the ID names another entry
def Answer.out(
  ~d: Led(),
  l: L(d),
  t: Replicas.Tip,
  i: Ledgers.Id,
  q: Requests.Ask,
  a: Hashes.Hash,
  o: Maybe<&2, Replicas.Out>
) -> Answer:
  match o:
    case None{}:
      Answer.Pending{}
    case Some{Replicas.Out.Stale{x}}:
      Shared.Bool.when(Answer, Hashes.Hash.is_eq(x, a), u => Answer.Stale{}, u => Answer.Refused{})
    case Some{Replicas.Out.Taken{x, n}}:
      Shared.Bool.when(
        Answer,
        Hashes.Hash.is_eq(x, a),
        u => Answer.taken(~d, l, Replicas.Tip.content(t), i, q),
        u => Answer.Refused{}
      )

# the answer to the request i of the change q on a line whose newest tip is m
# (none: the line has no start yet)
def Answer.at(
  ~d: Led(),
  +l: L(d),
  +i: Ledgers.Id,
  q: Requests.Ask,
  a: Hashes.Hash,
  m: Maybe<&2, Replicas.Tip>
) -> Answer:
  match m:
    case None{}:
      Answer.Pending{}
    case Some{+t}:
      Answer.out(~d, l, t, i, q, a, Replicas.Tip.out(~Requests.Ask.machine(), ~d, l, t, i))

# the answer to the request i of the change q, by how it arrives: a store
# that starts is Written at once
def Answer.of(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  i: Ledgers.Id,
  +q: Requests.Ask,
  a: Hashes.Hash,
  w: Replicas.Arrival
) -> Answer:
  match w:
    case Replicas.Arrival.Starts{vs}:
      Answer.Written{}
    case Replicas.Arrival.Waits{c}:
      Answer.at(~d, l, i, q, a, Replicas.Line.head(~Requests.Ask.machine(), ~d, ~kern, l, c))

# what a node whose ledger is l answers to the change q of the request i, at
# the time (none: the ledger does not hold the request)
def Node.answer(
  ~d: Led(),
  ~kern: Kern(d),
  +l: L(d),
  +i: Ledgers.Id,
  +time: String,
  +q: Requests.Ask
) -> Maybe<&2, Answer>:
  Shared.Maybe.when(
    Answer,
    Replicas.Led.has(~Requests.Ask.machine(), ~d, l, Ledgers.Entry.Ask{i, time, q}),
    u => Some{
      Answer.of(
        ~d,
        ~kern,
        l,
        i,
        q,
        Ledgers.Name.hash(
          Replicas.Entry.name(~Requests.Ask.machine(), Ledgers.Entry.Ask{i, time, q})
        ),
        Requests.Ask.arrival(q)
      )
    }
  )

# the answer m may come after the answer a: Pending may become any answer;
# Stale and Refused are final; a taken change stays taken (Written and
# Conflicted may follow each other: a merge is Conflicted while resources
# clash, and it is the same merge)
def Answer.follows(a: Answer, m: Maybe<&2, Answer>) -> Bool:
  match a m:
    case Answer.Pending{} Some{b}:
      True{}
    case Answer.Written{} Some{Answer.Written{}}:
      True{}
    case Answer.Written{} Some{Answer.Conflicted{k}}:
      True{}
    case Answer.Conflicted{k} Some{Answer.Written{}}:
      True{}
    case Answer.Conflicted{k} Some{Answer.Conflicted{k2}}:
      Ledgers.Id.is_eq(k, k2)
    case Answer.Stale{} Some{Answer.Stale{}}:
      True{}
    case Answer.Refused{} Some{Answer.Refused{}}:
      True{}
    case x y:
      False{}

# that a read of the clashes of a merge that told in the first ledger and tree
# tells in the second
def Answer.Known(~d: Led(), l: L(d), h: Maybe<&2, Hashes.Hash>, l2: L(d), h2: Maybe<&2, Hashes.Hash>) -> Type:
  @k: Ledgers.Id -> {Maybe.is_some(&2, Bool, Clash.left(~d, l, h, k)) == True{}: Bool} -> {
    Maybe.is_some(&2, Bool, Clash.left(~d, l2, h2, k)) == True{}: Bool
  }

# what Replicas.Line.get_grows says of the ledger d and the kernel kern: what
# the log of a line holds under a key, it holds for good
def Answer.Stays(~d: Led(), ~kern: Kern(d)) -> Type:
  @c: Ledgers.Line -> @key: List<&2, U32> -> Shared.Read.Stable(
    L(d),
    a => b => Replicas.Led.Later(~Requests.Ask.machine(), ~d, a, b),
    List<&2, U32>,
    l => Replicas.Line.get(~Requests.Ask.machine(), ~d, ~kern, l, c, key)
  )
