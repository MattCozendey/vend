import Base
import ../../shared.bend as Shared
import ../shared/formats.bend as Formats
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/reach.bend as Reaches
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts

# The pure core of a Vend Node: what it holds, what it answers, and the laws
# about both. transport/spec.bend carries it over IO as the public API
# (README, Public API).
#
# A node is a ledger of Vend's changes (Ledgers): it holds requests and votes,
# nodes sync by joining what they hold, and each line (a branch or an owner
# group) is a chain of steps that its owners decided. A store is the root
# chain that makes its lines, so two nodes never make one line twice. Every
# answer is read from the state alone.

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Ledgers.Id. A store is named by
# the request that started it.

# a line of a store: a branch, or an owner group
type Line is Data:
  Line.branch{name: String}
  Line.group{name: String}

# a member of an owner group: a node, or another group of its store
type Member is Data:
  Member.node{name: String}
  Member.group{name: String}

# new content: bytes, or what an old version held
type Content is Data:
  Content.bytes{bytes: Texts.Bytes()}
  Content.of{version: Ledgers.Id}

# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.at{version: Ledgers.Id}
  Point.head{store: Ledgers.Id, branch: String}
  Point.mark{store: Ledgers.Id, branch: String, mark: String}

# Requests
# --------
# A request is data alone: a point becomes a version before it is asked for,
# so that a request sent again, to any node, is the same request.

# a change of a line, or of its store (Ask.on)
type Change is Data:
  Change.make{line: Line, at: Maybe<&2, Ledgers.Id>, members: List<&2, Member>}
  Change.own{owners: List<&2, String>}
  Change.write{name: Resources.Name, base: Maybe<&2, Ledgers.Id>, content: Content}
  Change.resolve{conflict: Ledgers.Id, name: Resources.Name, content: Content}
  Change.merge{from: Ledgers.Id}
  Change.move{to: Ledgers.Id}
  Change.mark{mark: String, message: String}
  Change.members{members: List<&2, Member>}

# a change that a writer asks for: a store that starts with its first owners,
# or a change of a line of a store (none: of the store itself)
type Ask is Data:
  Ask.start{owners: List<&2, String>}
  Ask.on{store: Ledgers.Id, line: Maybe<&2, Line>, change: Change}

# who asks for a change, and when
type Envelope is Data:
  Envelope{id: String, writer: String, time: String}

# the request of e
def Envelope.of(e: Envelope) -> Ledgers.Id:
  match e:
    case Envelope{r, w, t}:
      Ledgers.Id{w, r}

# the time of e
def Envelope.time(e: Envelope) -> String:
  match e:
    case Envelope{r, w, t}:
      t

# Equality
# --------

# a and b are the same member
def Member.is_eq(a: Member, b: Member) -> Bool:
  match a b:
    case Member.node{x} Member.node{y}:
      String.eq(x, y)
    case Member.group{x} Member.group{y}:
      String.eq(x, y)
    case _ _:
      False{}

# Codes
# -----
# A request is sent and stored as its code (Codes); two requests are the same
# exactly when their codes are.

# the request i, then r
def Id.code(i: Ledgers.Id, r: List<&2, U32>) -> List<&2, U32>:
  match i:
    case Ledgers.Id{w, q}:
      Codes.Code.text(w, Codes.Code.text(q, r))

# a request ID
def Id.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ledgers.Id>>:
  Codes.Code.two.read(
    ~String,
    ~String,
    ~Ledgers.Id,
    ~Codes.Code.text.read,
    ~Codes.Code.text.read,
    w => q => Ledgers.Id{w, q},
    ts
  )

# the version m, if any (where a line starts, or the base of a write), then r
def Base.code(m: Maybe<&2, Ledgers.Id>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Ledgers.Id, ~Id.code, m, r)

# a version, if any
def Base.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Ledgers.Id>>>:
  Codes.Code.maybe.read(~Ledgers.Id, ~Id.code.read, ts)

# the resource n, then r
def Name.code(n: Resources.Name, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Resources.Name{t}:
      Codes.Code.text(t, r)

# a resource name
def Name.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Resources.Name>>:
  Codes.Code.one.read(~String, ~Resources.Name, ~Codes.Code.text.read, n => Resources.Name{n}, ts)

# the bytes b, then r
def Bytes.code(b: Texts.Bytes(), r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~U32, ~Codes.Code.token, b, r)

# bytes
def Bytes.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Texts.Bytes()>>:
  Codes.Code.list.read(~U32, ~Codes.Code.token.read, ts)

# the nodes os, then r
def Owners.code(os: List<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~String, ~Codes.Code.text, os, r)

# nodes
def Owners.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, String>>>:
  Codes.Code.list.read(~String, ~Codes.Code.text.read, ts)

# the text t with the tag k, then r
def Tag.text(k: U32, t: String, r: List<&2, U32>) -> List<&2, U32>:
  k <> Codes.Code.text(t, r)

# the line l, then r
def Line.code(l: Line, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Line.branch{n}:
      Tag.text(0, n, r)
    case Line.group{n}:
      Tag.text(1, n, r)

# a line
def Line.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Line>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Line>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~String, ~Line, ~Codes.Code.text.read, n => Line.branch{n}, r),
        u => Codes.Code.one.read(~String, ~Line, ~Codes.Code.text.read, n => Line.group{n}, r)
      )

# the line m, if any (none: the store), then r
def Target.code(m: Maybe<&2, Line>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Line, ~Line.code, m, r)

# a line, if any
def Target.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Line>>>:
  Codes.Code.maybe.read(~Line, ~Line.code.read, ts)

# the member l, then r
def Member.code(l: Member, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Member.node{n}:
      Tag.text(0, n, r)
    case Member.group{n}:
      Tag.text(1, n, r)

# a member
def Member.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Member>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Member>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.node{n}, r),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.group{n}, r)
      )

# the members ms, then r
def Members.code(ms: List<&2, Member>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Member, ~Member.code, ms, r)

# members
def Members.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Member>>>:
  Codes.Code.list.read(~Member, ~Member.code.read, ts)

# the content c, then r
def Content.code(c: Content, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Content.bytes{b}:
      0 <> Bytes.code(b, r)
    case Content.of{v}:
      1 <> Id.code(v, r)

# a content
def Content.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Content>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Content>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~Texts.Bytes(),
          ~Content,
          ~Bytes.code.read,
          b => Content.bytes{b},
          r
        ),
        u => Codes.Code.one.read(~Ledgers.Id, ~Content, ~Id.code.read, v => Content.of{v}, r)
      )

# the change c, then r
def Change.code(c: Change, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Change.make{l, at, ms}:
      0 <> Line.code(l, Base.code(at, Members.code(ms, r)))
    case Change.own{os}:
      1 <> Owners.code(os, r)
    case Change.write{n, base, x}:
      2 <> Name.code(n, Base.code(base, Content.code(x, r)))
    case Change.resolve{k, n, x}:
      3 <> Id.code(k, Name.code(n, Content.code(x, r)))
    case Change.merge{v}:
      4 <> Id.code(v, r)
    case Change.move{v}:
      5 <> Id.code(v, r)
    case Change.mark{m, t}:
      6 <> Codes.Code.text(m, Codes.Code.text(t, r))
    case Change.members{ms}:
      7 <> Members.code(ms, r)

# a change whose tag is x, from the tokens r after it
def Change.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Change>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Change>>,
    U32.is_eq(x, 0),
    u => Codes.Code.three.read(
      ~Line,
      ~Maybe<&2, Ledgers.Id>,
      ~List<&2, Member>,
      ~Change,
      ~Line.code.read,
      ~Base.code.read,
      ~Members.code.read,
      l => a => ms => Change.make{l, a, ms},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Change>>,
      U32.is_eq(x, 1),
      u => Codes.Code.one.read(
        ~List<&2, String>,
        ~Change,
        ~Owners.code.read,
        os => Change.own{os},
        r
      ),
      u => Shared.Bool.when(
        Maybe<&2, Codes.Read<Change>>,
        U32.is_eq(x, 2),
        u => Codes.Code.three.read(
          ~Resources.Name,
          ~Maybe<&2, Ledgers.Id>,
          ~Content,
          ~Change,
          ~Name.code.read,
          ~Base.code.read,
          ~Content.code.read,
          n => b => c => Change.write{n, b, c},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Change>>,
          U32.is_eq(x, 3),
          u => Codes.Code.three.read(
            ~Ledgers.Id,
            ~Resources.Name,
            ~Content,
            ~Change,
            ~Id.code.read,
            ~Name.code.read,
            ~Content.code.read,
            k => n => c => Change.resolve{k, n, c},
            r
          ),
          u => Shared.Bool.when(
            Maybe<&2, Codes.Read<Change>>,
            U32.is_eq(x, 4),
            u => Codes.Code.one.read(~Ledgers.Id, ~Change, ~Id.code.read, v => Change.merge{v}, r),
            u => Shared.Bool.when(
              Maybe<&2, Codes.Read<Change>>,
              U32.is_eq(x, 5),
              u => Codes.Code.one.read(~Ledgers.Id, ~Change, ~Id.code.read, v => Change.move{v}, r),
              u => Shared.Bool.when(
                Maybe<&2, Codes.Read<Change>>,
                U32.is_eq(x, 6),
                u => Codes.Code.two.read(
                  ~String,
                  ~String,
                  ~Change,
                  ~Codes.Code.text.read,
                  ~Codes.Code.text.read,
                  m => n => Change.mark{m, n},
                  r
                ),
                u => Codes.Code.one.read(
                  ~List<&2, Member>,
                  ~Change,
                  ~Members.code.read,
                  ms => Change.members{ms},
                  r
                )
              )
            )
          )
        )
      )
    )
  )

# a change
def Change.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Change>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, r}:
      Change.code.read.of(x, r)

# the request q, then r
def Ask.code(q: Ask, r: List<&2, U32>) -> List<&2, U32>:
  match q:
    case Ask.start{os}:
      0 <> Owners.code(os, r)
    case Ask.on{st, l, c}:
      1 <> Id.code(st, Target.code(l, Change.code(c, r)))

# a request
def Ask.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ask>>:
  match ts:
    case Nil{}:
      None{}
    case Con{x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Ask>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~List<&2, String>,
          ~Ask,
          ~Owners.code.read,
          os => Ask.start{os},
          r
        ),
        u => Codes.Code.three.read(
          ~Ledgers.Id,
          ~Maybe<&2, Line>,
          ~Change,
          ~Ask,
          ~Id.code.read,
          ~Target.code.read,
          ~Change.code.read,
          s => l => c => Ask.on{s, l, c},
          r
        )
      )

# a and b are the same request: they have the same code
def Ask.is_eq(a: Ask, b: Ask) -> Bool:
  Codes.Code.is_eq(~Ask, ~Ask.code, a, b)

# Lines
# -----

# the key of the line l below its store: prefix-free
def Line.key(l: Line) -> List<&2, Bool>:
  match l:
    case Line.branch{n}:
      False{} <> Tries.Trie.text(n)
    case Line.group{n}:
      True{} <> Tries.Trie.text(n)

# the chain of the line l of the store r (none: the store's own chain)
def Line.chain(r: Ledgers.Id, l: Maybe<&2, Line>) -> Ledgers.Chain:
  match l:
    case None{}:
      Ledgers.Chain{r, None{}}
    case Some{x}:
      Ledgers.Chain{r, Some{Line.key(x)}}

# the owners that the change c gives its chain, when it sets them
def Change.owners(c: Change) -> Maybe<&2, List<&2, String>>:
  match c:
    case Change.own{os}:
      Some{os}
    case _:
      None{}

# the line that the change c makes, when it makes one
def Change.makes(c: Change) -> Maybe<&2, List<&2, Bool>>:
  match c:
    case Change.make{l, at, ms}:
      Some{Line.key(l)}
    case _:
      None{}

# what the ledger reads of q
def Ask.view(q: Ask) -> Ledgers.View:
  match q:
    case Ask.start{os}:
      Ledgers.View.root{os}
    case Ask.on{r, l, +c}:
      Ledgers.View.on{Line.chain(r, l), Change.owners(c), Change.makes(c)}

# The state
# ---------

# what a node holds
def State() -> Data:
  Ledgers.State(Ask)

# a node that holds nothing yet
def Node.empty() -> State():
  Ledgers.State.empty(~Ask)

# what a holder of a and of b holds: a sync
def Node.join(a: State(), b: State()) -> State():
  Ledgers.State.join(~Ask, ~Ask.is_eq, a, b)

# what a holder of r lacks of s: what a sync from s to r sends
def Node.missing(s: State(), r: State()) -> State():
  Ledgers.State.missing(~Ask, ~Ask.is_eq, s, r)

# no entry of t contradicts one of s
def Node.agrees(s: State(), t: State()) -> Bool:
  Ledgers.State.agrees(~Ask, ~Ask.is_eq, s, t)

# the steps of the line l of the store r (none: the store's own steps)
def Node.steps(s: State(), r: Ledgers.Id, l: Maybe<&2, Line>) -> List<&2, Ledgers.Step<Ask>>:
  Ledgers.State.chain(~Ask, ~Ask.view, s, Line.chain(r, l))

# the requests that the steps xs took, in order: the versions of their line
def Steps.taken(xs: List<&2, Ledgers.Step<Ask>>) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{Ledgers.Step{i, True{}, t, q, ms}, r}:
      i <> Steps.taken(r)
    case Con{Ledgers.Step{i, False{}, t, q, ms}, r}:
      Steps.taken(r)

# the versions of the branch b of the store r, in order
def Node.versions(s: State(), r: Ledgers.Id, b: String) -> List<&2, Ledgers.Id>:
  Steps.taken(Node.steps(s, r, Some{Line.branch{b}}))

# the last of xs, if any
def Ids.last(xs: List<&2, Ledgers.Id>) -> Maybe<&2, Ledgers.Id>:
  List.last(&2, Ledgers.Id, xs)

# the newest version of the branch b of the store r, if b exists
def Node.head(s: State(), r: Ledgers.Id, b: String) -> Maybe<&2, Ledgers.Id>:
  Ids.last(Node.versions(s, r, b))

# the owners at the tip of the line l of the store r
def Node.owners(s: State(), r: Ledgers.Id, l: Maybe<&2, Line>) -> List<&2, String>:
  Ledgers.Tip.owners_of(Ledgers.State.tip(~Ask, ~Ask.view, s, Line.chain(r, l)))

# Versions
# --------

# the version before v in xs, after prev; none when v is first or not there
def Ids.before(
  xs: List<&2, Ledgers.Id>,
  prev: Maybe<&2, Ledgers.Id>,
  +v: Ledgers.Id
) -> Maybe<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Id>,
        Ledgers.Id.is_eq(x, v),
        u => prev,
        u => Ids.before(r, Some{x}, v)
      )

# the versions of the line whose versions hold a version of q: the line that q
# changes, or the line that it makes
def Ask.line(s: State(), q: Ask) -> List<&2, Ledgers.Id>:
  match q:
    case Ask.on{r, Some{l}, c}:
      Steps.taken(Node.steps(s, r, Some{l}))
    case Ask.on{r, None{}, Change.make{l, at, ms}}:
      Steps.taken(Node.steps(s, r, Some{l}))
    case _:
      []

# the version before v on its line, whose change is q
def Version.before.of(s: State(), v: Ledgers.Id, q: Ask) -> Maybe<&2, Ledgers.Id>:
  Ids.before(Ask.line(s, q), None{}, v)

# the request of v, when there is one
def State.asked.of(s: State(), v: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Ledgers.Asked<Ask>>:
  match v:
    case None{}:
      None{}
    case Some{i}:
      Ledgers.State.asked(~Ask, s, i)

# the versions that the change c names besides the one before it
def Change.refs(c: Change) -> List<&2, Ledgers.Id>:
  match c:
    case Change.move{to}:
      [to]
    case Change.merge{from}:
      [from]
    case Change.make{l, Some{at}, ms}:
      [at]
    case _:
      []

# the versions that v came from, when s holds its request r
def Version.parents.of(
  s: State(),
  v: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Ask>>
) -> List<&2, Ledgers.Id>:
  match r:
    case Some{Ledgers.Asked{t, Ask.on{st, l, +c}}}:
      List.append(
        &2,
        Ledgers.Id,
        Maybe.default(
          &2,
          List<&2, Ledgers.Id>,
          Maybe.map(
            &2,
            Ledgers.Id,
            List<&2, Ledgers.Id>,
            x => [x],
            Version.before.of(s, v, Ask.on{st, l, c})
          ),
          []
        ),
        Change.refs(c)
      )
    case _:
      []

# the versions that v came from
def Version.parents(s: State(), v: Ledgers.Id) -> List<&2, Ledgers.Id>:
  +s = s
  +v = v
  Version.parents.of(s, v, Ledgers.State.asked(~Ask, s, v))

# the requests among the cells cs
def Entry.ids(cs: List<&2, Ledgers.Cell<Ledgers.Entry<Ask>>>) -> List<&2, Ledgers.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Ledgers.one{Ledgers.Entry.ask{i, t, q}}, r}:
      i <> Entry.ids(r)
    case Con{c, r}:
      Entry.ids(r)

# every request that s holds
def State.versions(s: State()) -> List<&2, Ledgers.Id>:
  Entry.ids(Tries.Trie.values(Ledgers.Cell<Ledgers.Entry<Ask>>, s))

# x is v (held), or a version that v came from
def Version.is_from.if(held: Bool, s: State(), x: Ledgers.Id, v: Ledgers.Id) -> Bool:
  match held:
    case True{}:
      True{}
    case False{}:
      Reaches.Reach.in(
        ~Ledgers.Id,
        ~State(),
        ~Ledgers.Id.is_eq,
        ~Version.parents,
        ~State.versions,
        s,
        v,
        x
      )

# x is v, or a version that v came from
def Node.has(s: State(), +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  Version.is_from.if(Ledgers.Id.is_eq(x, v), s, x, v)

# the first version of xs that v came from
def Version.base.go(+s: State(), xs: List<&2, Ledgers.Id>, +v: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{+x, r}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Id>,
        Node.has(s, v, x),
        u => Some{x},
        u => Version.base.go(s, r, v)
      )

# the versions of xs up to v
def Ids.upto(xs: List<&2, Ledgers.Id>, +v: Ledgers.Id) -> List<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      x
        <> Shared.Bool.when(
          List<&2, Ledgers.Id>,
          Ledgers.Id.is_eq(x, v),
          u => [],
          u => Ids.upto(r, v)
        )

# the base of a merge of from into a line whose versions are xs and whose head
# was ours: the newest version of the line up to ours that from came from
def Version.base(
  s: State(),
  xs: List<&2, Ledgers.Id>,
  ours: Maybe<&2, Ledgers.Id>,
  from: Ledgers.Id
) -> Maybe<&2, Ledgers.Id>:
  match ours:
    case None{}:
      None{}
    case Some{o}:
      Version.base.go(s, List.reverse(&2, Ledgers.Id, Ids.upto(xs, o)), from)

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(+s: State(), +x: Ledgers.Id, +y: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )

# Submodules
# ----------
# A submodule is a resource whose bytes point to a child (Format.module): the
# space of the child's resources, the branch that it follows, and its version,
# on lines of their own. Never a node: any node that has the version can serve
# it. A merge of two pointers takes the newer one when one came from the other
# (Node.forward).

# a pointer to a child
type Pointer is Data:
  Pointer{space: String, branch: String, version: Ledgers.Id}

# the version of the child that p points to
def Pointer.version(p: Pointer) -> Ledgers.Id:
  match p:
    case Pointer{sp, b, v}:
      v

# the bytes of the pointer p (Texts.Text.cuts_after_join reads them back)
def Pointer.show(p: Pointer) -> Texts.Bytes():
  match p:
    case Pointer{sp, b, Ledgers.Id{w, r}}:
      Texts.Bytes.of_text(Texts.Text.join([sp, b, w], Chr{10}, r))

# the pointer of the lines that a text cut into (m)
def Pointer.read.of(m: Maybe<&2, Texts.Parts>) -> Maybe<&2, Pointer>:
  match m:
    case Some{Texts.Parts{Con{sp, Con{b, Con{w, Nil{}}}}, r}}:
      Some{Pointer{sp, b, Ledgers.Id{w, r}}}
    case _:
      None{}

# the pointer in the bytes b
def Pointer.read(b: Texts.Bytes()) -> Maybe<&2, Pointer>:
  Pointer.read.of(Texts.Text.cuts(3n, Texts.Bytes.to_text(b), 10))

# Content
# -------
# The bytes of a resource at a version, found one resource at a time: a write
# or a resolve of it holds them, a move or a make at a point takes them from
# its target, a merge merges its base, the version before it and the one merged
# in, and every other change keeps the version before it.

# what a merge keeps of a resource: its bytes or none, or a clash
type Pick is Data:
  Pick.take{bytes: Maybe<&2, Texts.Bytes()>}
  Pick.clash{}

# the merge of a resource's bytes, when all three hold it
def Pick.bytes(m: Formats.Merged) -> Pick:
  match m:
    case Formats.Merged.clean{x}:
      Pick.take{Some{x}}
    case Formats.Merged.clash{}:
      Pick.clash{}

# the merge of the submodules px and py: the one at the newer version m, if any
def Pick.module(m: Maybe<&2, Ledgers.Id>, px: Pointer, +py: Pointer) -> Pick:
  match m:
    case None{}:
      Pick.clash{}
    case Some{k}:
      Pick.take{
        Some{
          Pointer.show(
            Shared.Bool.when(Pointer, Ledgers.Id.is_eq(k, Pointer.version(py)), u => py, u => px)
          )
        }
      }

# the merge of two submodules that point as x and y
def Pick.pointers(s: State(), x: Maybe<&2, Pointer>, y: Maybe<&2, Pointer>) -> Pick:
  match x y:
    case Some{+px} Some{+py}:
      Pick.module(Node.forward(s, Pointer.version(px), Pointer.version(py)), px, py)
    case _ _:
      Pick.clash{}

# the merge of x and y, two changes of b, in the format f
def Pick.format(
  f: Formats.Format,
  s: State(),
  b: Texts.Bytes(),
  x: Texts.Bytes(),
  y: Texts.Bytes()
) -> Pick:
  match f:
    case Formats.Format.leaf{Formats.Leaf.module{}}:
      Pick.pointers(s, Pointer.read(x), Pointer.read(y))
    case g:
      Pick.bytes(Formats.Format.merge(g, b, x, y))

# the merge of a resource that the base, ours and theirs hold or not, when
# both sides changed it, in the format f
def Pick.both(
  f: Formats.Format,
  s: State(),
  b: Maybe<&2, Texts.Bytes()>,
  o: Maybe<&2, Texts.Bytes()>,
  t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  match o t:
    case Some{x} Some{y}:
      Pick.format(f, s, Maybe.default(&2, Texts.Bytes(), b, []), x, y)
    case _ _:
      Pick.clash{}

# a and b hold the same bytes, or both none
def Bytes.same(a: Maybe<&2, Texts.Bytes()>, b: Maybe<&2, Texts.Bytes()>) -> Bool:
  Shared.Maybe.is_eq(~Texts.Bytes(), ~Shared.List.is_eq(~U32, ~U32.is_eq), a, b)

# what a merge of the base b, ours o and theirs t keeps of a resource in the
# format f: theirs when ours is the base, ours when theirs is the base or both
# agree, else both merged
def Pick.merge(
  f: Formats.Format,
  s: State(),
  +b: Maybe<&2, Texts.Bytes()>,
  +o: Maybe<&2, Texts.Bytes()>,
  +t: Maybe<&2, Texts.Bytes()>
) -> Pick:
  Shared.Bool.when(
    Pick,
    Bytes.same(o, b),
    u => Pick.take{t},
    u => Shared.Bool.when(
      Pick,
      List.any.if(v => Bytes.same(o, t), Bytes.same(t, b)),
      w => Pick.take{o},
      w => Pick.both(f, s, b, o, t)
    )
  )

# the bytes of a merge: ours on a clash
def Pick.kept(p: Pick, o: Maybe<&2, Texts.Bytes()>) -> Maybe<&2, Texts.Bytes()>:
  match p:
    case Pick.take{x}:
      x
    case Pick.clash{}:
      o

# where the bytes of a resource come from: a step and what comes before it,
# the steps of a list (newest first), or the steps before the version v,
# whose change is q, on its line (walked only when a read reaches them)
type Src is Data:
  Src.cons{step: Ledgers.Step<Ask>, rest: Src}
  Src.steps{steps: List<&2, Ledgers.Step<Ask>>}
  Src.before{version: Ledgers.Id, ask: Ask}

# the version v, whose request is r, and what comes before it
def Src.at(+v: Ledgers.Id, r: Maybe<&2, Ledgers.Asked<Ask>>) -> Src:
  match r:
    case None{}:
      Src.steps{[]}
    case Some{Ledgers.Asked{t, +q}}:
      Src.cons{Ledgers.Step{v, True{}, t, q, []}, Src.before{v, q}}

# the version v of s (if any) and what comes before it
def Src.of(s: State(), v: Maybe<&2, Ledgers.Id>) -> Src:
  match v:
    case None{}:
      Src.steps{[]}
    case Some{+i}:
      Src.at(i, Ledgers.State.asked(~Ask, s, i))

# the steps of xs that took a request before v, newest first, after acc
def Steps.before(
  xs: List<&2, Ledgers.Step<Ask>>,
  +v: Ledgers.Id,
  +acc: List<&2, Ledgers.Step<Ask>>
) -> List<&2, Ledgers.Step<Ask>>:
  match xs:
    case Nil{}:
      []
    case Con{Ledgers.Step{+i, +k, t, q, ms}, r}:
      Shared.Bool.when(
        List<&2, Ledgers.Step<Ask>>,
        Ledgers.Id.is_eq(i, v),
        u => acc,
        u => Steps.before(
          r,
          v,
          Shared.Bool.when(
            List<&2, Ledgers.Step<Ask>>,
            k,
            w => Ledgers.Step{i, k, t, q, ms} <> acc,
            w => acc
          )
        )
      )

# the steps of the line whose versions hold a version of q: the line that q
# changes, or the line that it makes
def Ask.steps(s: State(), q: Ask) -> List<&2, Ledgers.Step<Ask>>:
  match q:
    case Ask.on{r, Some{l}, c}:
      Node.steps(s, r, Some{l})
    case Ask.on{r, None{}, Change.make{l, at, ms}}:
      Node.steps(s, r, Some{l})
    case _:
      []

# bend-lint: expect-begin bend-lint-rules/performance/deep_call_in_fork@information -- a merge reads its line once; the walks are linear
# the bytes of the resource n from src; f steps at most
def Res.go(+f: Nat, +s: State(), src: Src, +n: Resources.Name) -> Maybe<&2, Texts.Bytes()>:
  match f src:
    case 0n w:
      None{}
    case 1n+e Src.steps{Nil{}}:
      None{}
    case 1n+e Src.steps{Con{st, r}}:
      Res.go(e, s, Src.cons{st, Src.steps{r}}, n)
    case 1n+e Src.before{v, q}:
      Res.go(e, s, Src.steps{Steps.before(Ask.steps(s, q), v, [])}, n)
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.write{m, base, Content.bytes{x}}}, ms},
      rest
    }:
      Shared.Bool.when(
        Maybe<&2, Texts.Bytes()>,
        Resources.Name.is_eq(m, n),
        u => Some{x},
        u => Res.go(e, s, rest, n)
      )
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.write{m, base, Content.of{+w}}}, ms},
      rest
    }:
      Shared.Bool.when(
        Maybe<&2, Texts.Bytes()>,
        Resources.Name.is_eq(m, n),
        u => Res.go(e, s, Src.at(w, Ledgers.State.asked(~Ask, s, w)), n),
        u => Res.go(e, s, rest, n)
      )
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.resolve{c, m, Content.bytes{x}}}, ms},
      rest
    }:
      Shared.Bool.when(
        Maybe<&2, Texts.Bytes()>,
        Resources.Name.is_eq(m, n),
        u => Some{x},
        u => Res.go(e, s, rest, n)
      )
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.resolve{c, m, Content.of{+w}}}, ms},
      rest
    }:
      Shared.Bool.when(
        Maybe<&2, Texts.Bytes()>,
        Resources.Name.is_eq(m, n),
        u => Res.go(e, s, Src.at(w, Ledgers.State.asked(~Ask, s, w)), n),
        u => Res.go(e, s, rest, n)
      )
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.move{+to}}, ms}, rest}:
      Res.go(e, s, Src.at(to, Ledgers.State.asked(~Ask, s, to)), n)
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.make{ml, Some{+to}, mm}}, ms},
      rest
    }:
      Res.go(e, s, Src.at(to, Ledgers.State.asked(~Ask, s, to)), n)
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.make{ml, None{}, mm}}, ms}, rest}:
      None{}
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.merge{+from}}, ms}, rest}:
      +xs = Steps.taken(Ask.steps(s, Ask.on{st, l, Change.merge{from}}))
      ours = Ids.before(xs, None{}, i)
      base = Version.base(s, xs, ours, from)
      +o = Res.go(e, s, rest, n)
      bs fs = Res.go(
        e,
        s,
        Src.of(s, base),
        n
      ) Res.go(e, s, Src.at(from, Ledgers.State.asked(~Ask, s, from)), n)
      Pick.kept(Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, bs, o, fs), o)
    case 1n+e Src.cons{st, rest}:
      Res.go(e, s, rest, n)
# bend-lint: expect-end bend-lint-rules/performance/deep_call_in_fork@information

# enough steps for any walk back through the versions of s: two for each entry
def State.fuel(s: State()) -> Nat:
  1n+Nat.double(Tries.Trie.size(Ledgers.Cell<Ledgers.Entry<Ask>>, s))

# the bytes of the resource n at the version v of s
def Res.of(+s: State(), n: Resources.Name, v: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Texts.Bytes()>:
  Res.go(State.fuel(s), s, Src.of(s, v), n)

# the step k (taken or not, whose change is q) names the mark m
def Mark.names(k: Bool, q: Ask, m: String) -> Bool:
  match k q:
    case True{} Ask.on{st, l, Change.mark{x, t}}:
      String.eq(x, m)
    case w a:
      False{}

# the version that the first mark m of the steps xs names: the version before
# it, after prev
def Mark.first(
  xs: List<&2, Ledgers.Step<Ask>>,
  +prev: Maybe<&2, Ledgers.Id>,
  +m: String
) -> Maybe<&2, Ledgers.Id>:
  match xs:
    case Nil{}:
      None{}
    case Con{Ledgers.Step{i, +k, t, q, ms}, r}:
      Shared.Bool.when(
        Maybe<&2, Ledgers.Id>,
        Mark.names(k, q, m),
        u => prev,
        u => Mark.first(r, Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev), m)
      )

# the request i is a version: a step took it
def Node.is_version(s: State(), i: Ledgers.Id) -> Bool:
  Shared.Maybe.is_eq(
    ~Bool,
    ~Shared.Bool.is_eq,
    Ledgers.Status.verdict(Ledgers.State.status(~Ask, ~Ask.view, s, i)),
    Some{True{}}
  )

# the version at the point p, if there is one
def Node.version(s: State(), p: Point) -> Maybe<&2, Ledgers.Id>:
  match p:
    case Point.at{+v}:
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.is_version(s, v), u => Some{v}, u => None{})
    case Point.head{r, b}:
      Node.head(s, r, b)
    case Point.mark{r, b, m}:
      Mark.first(Node.steps(s, r, Some{Line.branch{b}}), None{}, m)

# the bytes of the resource n at the point p, if it is there
def Node.content(+s: State(), n: Resources.Name, p: Point) -> Maybe<&2, Texts.Bytes()>:
  Res.of(s, n, Node.version(s, p))

# a version that changed a resource, as Node.log lists it
type LogEntry is Data:
  LogEntry{version: Ledgers.Id, time: String}

# the version x, when it changed the resource (held), then rest
def Log.at(
  held: Bool,
  x: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Ask>>,
  rest: List<&2, LogEntry>
) -> List<&2, LogEntry>:
  match held r:
    case True{} Some{Ledgers.Asked{t, q}}:
      LogEntry{x, t} <> rest
    case h m:
      rest

# the versions of xs, after prev, that changed the resource n
def Log.of(
  +s: State(),
  +n: Resources.Name,
  xs: List<&2, Ledgers.Id>,
  prev: Maybe<&2, Ledgers.Id>
) -> List<&2, LogEntry>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      Log.at(
        Bool.not(Bytes.same(Res.of(s, n, Some{x}), Res.of(s, n, prev))),
        x,
        Ledgers.State.asked(~Ask, s, x),
        Log.of(s, n, r, Some{x})
      )

# the versions of the branch b of the store r that changed the resource n
def Node.log(+s: State(), n: Resources.Name, r: Ledgers.Id, b: String) -> List<&2, LogEntry>:
  Log.of(s, n, Node.versions(s, r, b), None{})

# what changed in the resource n from the point a to the point b
def Node.diff(+s: State(), +n: Resources.Name, a: Point, b: Point) -> List<&2, Formats.Change>:
  Formats.Format.changes(
    Formats.Format.of(Resources.Name.path(n)),
    Maybe.default(&2, Texts.Bytes(), Node.content(s, n, a), []),
    Maybe.default(&2, Texts.Bytes(), Node.content(s, n, b), [])
  )

# Names
# -----

# the texts of the resources from src; f steps at most
def Res.names(+f: Nat, +s: State(), src: Src) -> List<&2, String>:
  match f src:
    case 0n w:
      []
    case 1n+e Src.steps{Nil{}}:
      []
    case 1n+e Src.steps{Con{st, r}}:
      Res.names(e, s, Src.cons{st, Src.steps{r}})
    case 1n+e Src.before{v, q}:
      Res.names(e, s, Src.steps{Steps.before(Ask.steps(s, q), v, [])})
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.move{+to}}, ms}, rest}:
      Res.names(e, s, Src.at(to, Ledgers.State.asked(~Ask, s, to)))
    case 1n+e Src.cons{
      Ledgers.Step{i, k, t, Ask.on{st, l, Change.make{ml, Some{+to}, mm}}, ms},
      rest
    }:
      Res.names(e, s, Src.at(to, Ledgers.State.asked(~Ask, s, to)))
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.make{ml, None{}, mm}}, ms}, rest}:
      []
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.merge{+from}}, ms}, rest}:
      fs os = Res.names(
        e,
        s,
        Src.at(from, Ledgers.State.asked(~Ask, s, from))
      ) Res.names(e, s, rest)
      Shared.List.union(~String, ~String.eq, fs, os)
    case 1n+e Src.cons{Ledgers.Step{i, k, t, Ask.on{st, l, Change.write{m, base, c}}, ms}, rest}:
      Shared.List.union(~String, ~String.eq, [Resources.Name.show(m)], Res.names(e, s, rest))
    case 1n+e Src.cons{st, rest}:
      Res.names(e, s, rest)

# the texts of the resources at the version v of s
def Res.of.names(+s: State(), v: Maybe<&2, Ledgers.Id>) -> List<&2, String>:
  Res.names(State.fuel(s), s, Src.of(s, v))

# p is a clash
def Pick.is_clash(p: Pick) -> Bool:
  match p:
    case Pick.take{x}:
      False{}
    case Pick.clash{}:
      True{}

# the resources of the names ns that clash when from merges into ours over base
def Res.clashes(
  +s: State(),
  ns: List<&2, String>,
  +base: Maybe<&2, Ledgers.Id>,
  +ours: Maybe<&2, Ledgers.Id>,
  +from: Ledgers.Id
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{t, r}:
      +n = {Resources.Name{t}: Resources.Name}
      List.filter.put(
        Resources.Name,
        n,
        Res.clashes(s, r, base, ours, from),
        Pick.is_clash(
          Pick.merge(
            Formats.Format.of(Resources.Name.path(n)),
            s,
            Res.of(s, n, base),
            Res.of(s, n, ours),
            Res.of(s, n, Some{from})
          )
        )
      )

# Conflicts
# ---------

# the resources that clash at the merge k, whose request is r
def Merge.clashes(
  +s: State(),
  k: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.merge{+from}}}}:
      +xs = Ask.line(s, Ask.on{st, l, Change.merge{from}})
      +ours = Ids.before(xs, None{}, k)
      Res.clashes(
        s,
        Shared.List.union(~String, ~String.eq, Res.of.names(s, Some{from}), Res.of.names(s, ours)),
        Version.base(s, xs, ours, from),
        ours,
        from
      )
    case _:
      []

# the text that the request r settles of k
def Merge.settles(r: Maybe<&2, Ledgers.Asked<Ask>>, k: Ledgers.Id) -> List<&2, String>:
  match r:
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.resolve{j, n, c}}}}:
      List.filter.put(String, Resources.Name.show(n), [], Ledgers.Id.is_eq(j, k))
    case _:
      []

# the texts that the resolves of k among xs settle
def Merge.settled(+s: State(), xs: List<&2, Ledgers.Id>, +k: Ledgers.Id) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      List.append(
        &2,
        String,
        Merge.settles(Ledgers.State.asked(~Ask, s, x), k),
        Merge.settled(s, r, k)
      )

# the names of ns whose texts ts does not hold
def Names.unsettled(
  ns: List<&2, Resources.Name>,
  +ts: List<&2, String>
) -> List<&2, Resources.Name>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Resources.Name,
        n,
        Names.unsettled(r, ts),
        Bool.not(List.contains(~String, ~String.eq, ts, Resources.Name.show(n)))
      )

# the resources that still clash after the merge k, whose request is r
def Merge.left(
  +s: State(),
  +k: Ledgers.Id,
  +r: Maybe<&2, Ledgers.Asked<Ask>>
) -> List<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, +q}}:
      Names.unsettled(Merge.clashes(s, k, r), Merge.settled(s, Ask.line(s, q), k))
    case None{}:
      []

# the resources that still clash after the merge k
def Node.conflict(+s: State(), +k: Ledgers.Id) -> List<&2, Resources.Name>:
  Merge.left(s, k, Ledgers.State.asked(~Ask, s, k))

# Groups
# ------

# the members that the change of q sets, else found
def Group.set(q: Ask, found: Maybe<&2, List<&2, Member>>) -> Maybe<&2, List<&2, Member>>:
  match q:
    case Ask.on{st, l, Change.make{ml, at, ms}}:
      Some{ms}
    case Ask.on{st, l, Change.members{ms}}:
      Some{ms}
    case _:
      found

# the members that the last step of xs that sets them sets, else found
def Group.last(
  xs: List<&2, Ledgers.Step<Ask>>,
  found: Maybe<&2, List<&2, Member>>
) -> Maybe<&2, List<&2, Member>>:
  match xs:
    case Nil{}:
      found
    case Con{Ledgers.Step{i, True{}, t, q, ms}, r}:
      Group.last(r, Group.set(q, found))
    case Con{Ledgers.Step{i, False{}, t, q, ms}, r}:
      Group.last(r, found)

# the members of the group g of the store r, if g exists
def Node.members(s: State(), r: Ledgers.Id, g: String) -> Maybe<&2, List<&2, Member>>:
  Group.last(Node.steps(s, r, Some{Line.group{g}}), None{})

# the groups of a store, as a graph
type Groups is Data:
  Groups{state: State(), store: Ledgers.Id}

# the members of m in the groups g, when it is a group
def Group.succ(g: Groups, m: Member) -> List<&2, Member>:
  match g m:
    case Groups{s, r} Member.node{n}:
      []
    case Groups{+s, +r} Member.group{h}:
      Maybe.default(&2, List<&2, Member>, Node.members(s, r, h), [])

# the groups that the steps xs of a store make, as members
def Group.made(xs: List<&2, Ledgers.Step<Ask>>) -> List<&2, Member>:
  match xs:
    case Nil{}:
      []
    case Con{
      Ledgers.Step{i, True{}, t, Ask.on{st, None{}, Change.make{Line.group{h}, at, ms}}, os},
      r
    }:
      Member.group{h} <> Group.made(r)
    case Con{x, r}:
      Group.made(r)

# every group of the groups g, as a member
def Group.all(g: Groups) -> List<&2, Member>:
  match g:
    case Groups{s, r}:
      Group.made(Node.steps(s, r, None{}))

# m is a member of the group g of the store r, or of a group inside g
def Node.is_inside(s: State(), r: Ledgers.Id, m: Member, g: String) -> Bool:
  Reaches.Reach.in(
    ~Member,
    ~Groups,
    ~Member.is_eq,
    ~Group.succ,
    ~Group.all,
    Groups{s, r},
    Member.group{g},
    m
  )

# the nodes among the members ms
def Group.nodes.of(ms: List<&2, Member>) -> List<&2, String>:
  match ms:
    case Nil{}:
      []
    case Con{Member.node{n}, r}:
      n <> Group.nodes.of(r)
    case Con{Member.group{g}, r}:
      Group.nodes.of(r)

# the nodes that some group of gs names
def Group.named(+g: Groups, gs: List<&2, Member>) -> List<&2, String>:
  match gs:
    case Nil{}:
      []
    case Con{m, r}:
      Shared.List.union(~String, ~String.eq, Group.nodes.of(Group.succ(g, m)), Group.named(g, r))

# the nodes of ns that are inside the group h of the store r
def Group.inside(+s: State(), +r: Ledgers.Id, ns: List<&2, String>, +h: String) -> List<&2, String>:
  match ns:
    case Nil{}:
      []
    case Con{+n, rest}:
      List.filter.put(
        String,
        n,
        Group.inside(s, r, rest, h),
        Node.is_inside(s, r, Member.node{n}, h)
      )

# the nodes inside the group g of the store r: what a set-owner to g asks for
def Node.nodes(+s: State(), +r: Ledgers.Id, g: String) -> List<&2, String>:
  +gs = {Groups{s, r}: Groups}
  Group.inside(s, r, Group.named(gs, Group.all(gs)), g)

# the member m of a new set of the group g makes g contain itself
def Group.loops(s: State(), r: Ledgers.Id, +g: String, m: Member) -> Bool:
  match m:
    case Member.node{n}:
      False{}
    case Member.group{+h}:
      List.any.if(u => Node.is_inside(s, r, Member.group{g}, h), String.eq(h, g))

# some member of ms makes the group g of the store r contain itself
def Group.loops.any(+s: State(), +r: Ledgers.Id, +g: String, ms: List<&2, Member>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{m, rest}:
      List.any.if(u => Group.loops.any(s, r, g, rest), Group.loops(s, r, g, m))

# Judging
# -------
# The owners of a line give each request one verdict, once, at the tip: take
# it, or refuse it as stale. They wait while a version it names is not decided
# yet.

# no text of xs comes twice
def Names.distinct(+xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, r}:
      List.all.if(u => Names.distinct(r), Bool.not(List.contains(~String, ~String.eq, r, x)))

# the verdict that the status st of a version gives a request that names it:
# take it when it is a version, refuse it when it never will be, else wait
def Judge.ready.of(st: Ledgers.Status) -> Maybe<&2, Bool>:
  match st:
    case Ledgers.Status.done{k}:
      Some{k}
    case Ledgers.Status.refused{}:
      Some{False{}}
    case _:
      None{}

# the verdict of the version v, for a request that names it
def Judge.ready(s: State(), v: Ledgers.Id) -> Maybe<&2, Bool>:
  Judge.ready.of(Ledgers.State.status(~Ask, ~Ask.view, s, v))

# the verdict of the version m, if any
def Judge.ready_maybe(s: State(), m: Maybe<&2, Ledgers.Id>) -> Maybe<&2, Bool>:
  match m:
    case None{}:
      Some{True{}}
    case Some{v}:
      Judge.ready(s, v)

# the verdict m, then k when m takes
def Judge.then(m: Maybe<&2, Bool>, k: Unit -> Maybe<&2, Bool>) -> Maybe<&2, Bool>:
  match m:
    case Some{True{}}:
      k(Unit{})
    case Some{False{}}:
      Some{False{}}
    case None{}:
      None{}

# the verdict on the content c: its version must be one
def Judge.content(s: State(), c: Content) -> Maybe<&2, Bool>:
  match c:
    case Content.bytes{x}:
      Some{True{}}
    case Content.of{w}:
      Judge.ready(s, w)

# the verdict on a write of the resource n since base, with the content c, at
# the tip of the steps xs: take it when n holds at the head what it held at
# base
def Judge.write(
  +s: State(),
  +n: Resources.Name,
  +base: Maybe<&2, Ledgers.Id>,
  c: Content,
  xs: List<&2, Ledgers.Step<Ask>>
) -> Maybe<&2, Bool>:
  Judge.then(
    Judge.ready_maybe(s, base),
    u => Judge.then(
      Judge.content(s, c),
      w => Some{Bytes.same(Res.of(s, n, Ids.last(Steps.taken(xs))), Res.of(s, n, base))}
    )
  )

# the request k is a merge on the branch b of the store r
def Merge.is_on(m: Maybe<&2, Ledgers.Asked<Ask>>, r: Ledgers.Id, b: String) -> Bool:
  match m:
    case Some{Ledgers.Asked{t, Ask.on{st, Some{Line.branch{x}}, Change.merge{f}}}}:
      Bool.and(Ledgers.Id.is_eq(st, r), String.eq(x, b))
    case _:
      False{}

# the verdict on the change c of the line l of the store r, at the tip of the
# steps xs
def Judge.change(
  +s: State(),
  r: Ledgers.Id,
  l: Maybe<&2, Line>,
  c: Change,
  xs: List<&2, Ledgers.Step<Ask>>
) -> Maybe<&2, Bool>:
  match l c:
    case None{} Change.make{Line.branch{b}, at, ms}:
      Judge.ready_maybe(s, at)
    case None{} Change.make{Line.group{g}, at, ms}:
      Some{Bool.not(Group.loops.any(s, r, g, ms))}
    case w Change.own{+os}:
      Some{List.all.if(u => Names.distinct(os), Bool.not(List.is_empty(&2, String, os)))}
    case Some{Line.branch{b}} Change.write{n, base, c2}:
      Judge.write(s, n, base, c2, xs)
    case Some{Line.branch{+b}} Change.resolve{+k, n, c2}:
      Judge.then(
        Judge.ready(s, k),
        u => Judge.then(
          Judge.content(s, c2),
          w => Some{
            List.all.if(
              v => List.contains(~Resources.Name, ~Resources.Name.is_eq, Node.conflict(s, k), n),
              Merge.is_on(Ledgers.State.asked(~Ask, s, k), r, b)
            )
          }
        )
      )
    case Some{Line.branch{b}} Change.merge{from}:
      Judge.ready(s, from)
    case Some{Line.branch{b}} Change.move{to}:
      Judge.ready(s, to)
    case Some{Line.branch{b}} Change.mark{m, t}:
      Some{Maybe.is_none(&2, Ledgers.Id, Mark.first(xs, None{}, m))}
    case Some{Line.group{g}} Change.members{ms}:
      Some{Bool.not(Group.loops.any(s, r, g, ms))}
    case w c3:
      Some{False{}}

# the verdict of the owners on q at the tip of the steps xs of its line (none:
# wait)
def Node.judge(s: State(), q: Ask, xs: List<&2, Ledgers.Step<Ask>>) -> Maybe<&2, Bool>:
  match q:
    case Ask.start{os}:
      Some{True{}}
    case Ask.on{r, l, c}:
      s = s
      xs = xs
      Judge.change(s, r, l, c, xs)

# Changes
# -------

# s, after the node n took in the request q of e, and voted on it when it owns
# its line
def Node.ask(n: String, s: State(), +e: Envelope, q: Ask) -> State():
  Ledgers.State.ask(
    ~Ask,
    ~Ask.is_eq,
    ~Ask.view,
    ~Node.judge,
    n,
    s,
    Envelope.of(e),
    Envelope.time(e),
    q
  )

# s, after the node n voted at the tip of each line that it owns
def Node.vote(n: String, s: State()) -> State():
  Ledgers.State.vote(~Ask, ~Ask.is_eq, ~Ask.view, ~Node.judge, n, s)

# Answers
# -------

# where a request is (README, Public API). Written: its version. Conflicted: a
# merge or a resolve after which resources still clash (the merge). Stale: its
# owners refused it at their tip. Refused: it is contradicted.
type Answer is Data:
  Answer.written{version: Ledgers.Id}
  Answer.conflicted{merge: Ledgers.Id}
  Answer.pending{}
  Answer.stale{}
  Answer.refused{}
  Answer.not_seen{}

# Written i, or Conflicted k while the merge k still clashes
def Answer.left(s: State(), i: Ledgers.Id, +k: Ledgers.Id) -> Answer:
  Shared.Bool.when(
    Answer,
    List.is_empty(&2, Resources.Name, Node.conflict(s, k)),
    u => Answer.written{i},
    u => Answer.conflicted{k}
  )

# the answer to the request i, which a step took, whose request is r
def Answer.taken(s: State(), +i: Ledgers.Id, r: Maybe<&2, Ledgers.Asked<Ask>>) -> Answer:
  match r:
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.merge{f}}}}:
      Answer.left(s, i, i)
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.resolve{k, n, c}}}}:
      Answer.left(s, i, k)
    case _:
      Answer.written{i}

# the answer to the request i, whose status is st
def Answer.of(+s: State(), +i: Ledgers.Id, st: Ledgers.Status) -> Answer:
  match st:
    case Ledgers.Status.done{True{}}:
      Answer.taken(s, i, Ledgers.State.asked(~Ask, s, i))
    case Ledgers.Status.done{False{}}:
      Answer.stale{}
    case Ledgers.Status.pending{}:
      Answer.pending{}
    case Ledgers.Status.refused{}:
      Answer.refused{}
    case Ledgers.Status.not_seen{}:
      Answer.not_seen{}

# where the request i is
def Node.answer(+s: State(), +i: Ledgers.Id) -> Answer:
  Answer.of(s, i, Ledgers.State.status(~Ask, ~Ask.view, s, i))

# Listings
# --------

# a branch: its store and its name
type Branch is Data:
  Branch{store: Ledgers.Id, name: String}

# a and b are the same branch
def Branch.is_eq(a: Branch, b: Branch) -> Bool:
  match a b:
    case Branch{r1, n1} Branch{r2, n2}:
      Bool.and(Ledgers.Id.is_eq(r1, r2), String.eq(n1, n2))

# a branch, as Node.branches lists it
type BranchEntry is Data:
  BranchEntry{branch: Branch, owners: List<&2, String>, head: Ledgers.Id}

# the stores among the cells cs
def Store.ids(cs: List<&2, Ledgers.Cell<Ledgers.Entry<Ask>>>) -> List<&2, Ledgers.Id>:
  match cs:
    case Nil{}:
      []
    case Con{Ledgers.one{Ledgers.Entry.ask{i, t, Ask.start{os}}}, r}:
      i <> Store.ids(r)
    case Con{c, r}:
      Store.ids(r)

# the branches that the steps xs of a store make
def Branch.made(xs: List<&2, Ledgers.Step<Ask>>) -> List<&2, String>:
  match xs:
    case Nil{}:
      []
    case Con{
      Ledgers.Step{i, True{}, t, Ask.on{st, None{}, Change.make{Line.branch{b}, at, ms}}, os},
      r
    }:
      b <> Branch.made(r)
    case Con{x, r}:
      Branch.made(r)

# the branch b of the store r, at its head m, then rest
def Branch.at(
  +r: Ledgers.Id,
  +b: String,
  s: State(),
  m: Maybe<&2, Ledgers.Id>,
  rest: List<&2, BranchEntry>
) -> List<&2, BranchEntry>:
  match m:
    case None{}:
      rest
    case Some{h}:
      BranchEntry{Branch{r, b}, Node.owners(s, r, Some{Line.branch{b}}), h} <> rest

# the branches of the names bs of the store r
def Branch.of(+s: State(), +r: Ledgers.Id, bs: List<&2, String>) -> List<&2, BranchEntry>:
  match bs:
    case Nil{}:
      []
    case Con{+b, rest}:
      Branch.at(r, b, s, Node.head(s, r, b), Branch.of(s, r, rest))

# the branches of the stores rs
def Branch.all(+s: State(), rs: List<&2, Ledgers.Id>) -> List<&2, BranchEntry>:
  match rs:
    case Nil{}:
      []
    case Con{+r, rest}:
      List.append(
        &2,
        BranchEntry,
        Branch.of(s, r, Branch.made(Node.steps(s, r, None{}))),
        Branch.all(s, rest)
      )

# every branch
def Node.branches(+s: State()) -> List<&2, BranchEntry>:
  Branch.all(s, Store.ids(Tries.Trie.values(Ledgers.Cell<Ledgers.Entry<Ask>>, s)))

# the branches es
def Branch.names(es: List<&2, BranchEntry>) -> List<&2, Branch>:
  match es:
    case Nil{}:
      []
    case Con{BranchEntry{b, os, h}, r}:
      b <> Branch.names(r)

# the versions of the branch b
def Branch.versions(s: State(), b: Branch) -> List<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      Node.versions(s, r, n)

# the head of the branch b, if b exists
def Branch.head(s: State(), b: Branch) -> Maybe<&2, Ledgers.Id>:
  match b:
    case Branch{r, n}:
      Node.head(s, r, n)

# Uses
# ----

# the resources of the texts ts
def Names.of(ts: List<&2, String>) -> List<&2, Resources.Name>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Resources.Name{t} <> Names.of(r)

# the resources of the branch b at its head
def Node.resources(+s: State(), b: Branch) -> List<&2, Resources.Name>:
  Names.of(Res.of.names(s, Branch.head(s, b)))

# a branch at its head h, with its resources: the graph of its imports
type Uses is Data:
  Uses{state: State(), head: Maybe<&2, Ledgers.Id>, names: List<&2, Resources.Name>}

# the resources of the branch of g
def Uses.nodes(g: Uses) -> List<&2, Resources.Name>:
  match g:
    case Uses{s, h, ns}:
      ns

# the bytes m, as a list of one item or none
def Uses.items(m: Maybe<&2, Texts.Bytes()>) -> List<&2, Texts.Bytes()>:
  match m:
    case None{}:
      []
    case Some{b}:
      [b]

# the resources that the edges es of the resource n name
def Uses.named(es: List<&2, Formats.Edge>, +n: Resources.Name) -> List<&2, Resources.Name>:
  match es:
    case Nil{}:
      []
    case Con{Formats.Edge{t, a, cs}, r}:
      Resources.Name.at(n, Texts.Bytes.to_text(t)) <> Uses.named(r, n)

# what the resource n imports at the version h of s, as its format reads it
def Uses.targets(
  s: State(),
  h: Maybe<&2, Ledgers.Id>,
  +n: Resources.Name
) -> List<&2, Resources.Name>:
  Uses.named(
    Formats.Format.uses(Formats.Format.of(Resources.Name.path(n)), Uses.items(Res.of(s, n, h))),
    n
  )

# what n imports in g, when it is a resource of g
def Uses.succ(g: Uses, n: Resources.Name) -> List<&2, Resources.Name>:
  match g:
    case Uses{s, h, ns}:
      +n = n
      Shared.Bool.when(
        List<&2, Resources.Name>,
        List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n),
        u => Uses.targets(s, h, n),
        u => []
      )

# the resources that the resource u of the branch b imports, at its head
def Node.imports(+s: State(), b: Branch, u: Resources.Name) -> List<&2, Resources.Name>:
  Uses.targets(s, Branch.head(s, b), u)

# the resource u of the branch b uses c: c is reached from u through the
# imports of the resources of b, at any depth
def Node.uses(+s: State(), +b: Branch, u: Resources.Name, c: Resources.Name) -> Bool:
  Reaches.Reach.in(
    ~Resources.Name,
    ~Uses,
    ~Resources.Name.is_eq,
    ~Uses.succ,
    ~Uses.nodes,
    Uses{s, Branch.head(s, b), Node.resources(s, b)},
    u,
    c
  )

# Touches
# -------

# a change elsewhere that touches what a branch uses: the version wrote the
# resource changed, and the resource used of the branch is that resource or
# uses it (Node.touches)
type Touch is Data:
  Touch{version: Ledgers.Id, changed: Resources.Name, branch: Branch, used: Resources.Name}

# a and b are the same touch
def Touch.is_eq(a: Touch, b: Touch) -> Bool:
  match a b:
    case Touch{v1, c1, b1, u1} Touch{v2, c2, b2, u2}:
      Bool.and(
        Ledgers.Id.is_eq(v1, v2),
        Bool.and(
          Resources.Name.is_eq(c1, c2),
          Bool.and(Branch.is_eq(b1, b2), Resources.Name.is_eq(u1, u2))
        )
      )

# the resource that the request r wrote: of a write or a resolve
def Wrote.of(r: Maybe<&2, Ledgers.Asked<Ask>>) -> Maybe<&2, Resources.Name>:
  match r:
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.write{m, base, c}}}}:
      Some{m}
    case Some{Ledgers.Asked{t, Ask.on{st, l, Change.resolve{k, m, c}}}}:
      Some{m}
    case _:
      None{}

# the resource that the version v wrote, when it is a write or a resolve
def Node.wrote(s: State(), v: Ledgers.Id) -> Maybe<&2, Resources.Name>:
  Wrote.of(Ledgers.State.asked(~Ask, s, v))

# the versions of the branches es
def Touch.versions.of(+s: State(), es: List<&2, Branch>) -> List<&2, Ledgers.Id>:
  match es:
    case Nil{}:
      []
    case Con{b, r}:
      List.append(&2, Ledgers.Id, Branch.versions(s, b), Touch.versions.of(s, r))

# the versions of every branch
def Touch.versions(+s: State()) -> List<&2, Ledgers.Id>:
  Touch.versions.of(s, Branch.names(Node.branches(s)))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- it runs only after the branch is known, so the head is there and both sides are needed
# the branch b lacks the version v
def Touch.lacks(+s: State(), +b: Branch, +v: Ledgers.Id) -> Bool:
  Bool.and(
    Maybe.is_some(&2, Ledgers.Id, Branch.head(s, b)),
    Bool.not(Node.has(s, Maybe.default(&2, Ledgers.Id, Branch.head(s, b), v), v))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the touch t holds: its branch is a branch and lacks its version, which is a
# version of a branch and wrote the resource changed, and the resource used is
# of the branch, and is the one changed or uses it; each part runs only when
# the ones before it hold, from the cheapest
def Node.touches(s: State(), t: Touch) -> Bool:
  match t:
    case Touch{+v, +c, +b, +u}:
      +s = s
      List.all.if(
        w => List.all.if(
          w => List.all.if(
            w => List.all.if(
              w => List.all.if(
                w => List.any.if(w => Node.uses(s, b, u, c), Resources.Name.is_eq(u, c)),
                List.contains(~Resources.Name, ~Resources.Name.is_eq, Node.resources(s, b), u)
              ),
              Shared.Maybe.is_eq(~Resources.Name, ~Resources.Name.is_eq, Node.wrote(s, v), Some{c})
            ),
            Touch.lacks(s, b, v)
          ),
          List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Touch.versions(s), v)
        ),
        List.contains(~Branch, ~Branch.is_eq, Branch.names(Node.branches(s)), b)
      )

# the touches of the version v that wrote c, on the branch b, one for each of
# its resources us
def Touch.each(
  us: List<&2, Resources.Name>,
  +v: Ledgers.Id,
  +c: Resources.Name,
  +b: Branch
) -> List<&2, Touch>:
  match us:
    case Nil{}:
      []
    case Con{u, r}:
      Touch{v, c, b, u} <> Touch.each(r, v, c, b)

# the touches of the version v that wrote the resource m (if any), on the
# branch b, one for each of its resources us
def Touch.of(
  m: Maybe<&2, Resources.Name>,
  v: Ledgers.Id,
  b: Branch,
  us: List<&2, Resources.Name>
) -> List<&2, Touch>:
  match m:
    case None{}:
      []
    case Some{c}:
      Touch.each(us, v, c, b)

# a branch of s, with its resources
type Affects is Data:
  Affects{state: State(), branch: Branch, resources: List<&2, Resources.Name>}

# the touches of the version v on the branch of g
def Affects.at(g: Affects, v: Ledgers.Id) -> List<&2, Touch>:
  match g:
    case Affects{s, b, us}:
      +v = v
      Touch.of(Node.wrote(s, v), v, b, us)

# the touch t is of the branch of g, and holds
def Affects.keeps(g: Affects, t: Touch) -> Bool:
  match g t:
    case Affects{s, b, us} Touch{v, c, +tb, u}:
      List.all.if(w => Node.touches(s, Touch{v, c, tb, u}), Branch.is_eq(tb, b))

# the touches that may hold of the branch b
def Affects.cands(+s: State(), +b: Branch) -> List<&2, Touch>:
  Shared.List.flat(
    ~Ledgers.Id,
    ~Touch,
    ~Affects,
    ~Affects.at,
    Touch.versions(s),
    Affects{s, b, Node.resources(s, b)}
  )

# the changes elsewhere that touch what the branch b uses, at any depth
def Node.affects(+s: State(), +b: Branch) -> List<&2, Touch>:
  Shared.List.keep(
    ~Touch,
    ~Affects,
    ~Affects.keeps,
    Affects.cands(s, b),
    Affects{s, b, Node.resources(s, b)}
  )

# the version of a point of s
type Impact is Data:
  Impact{state: State(), version: Maybe<&2, Ledgers.Id>}

# the touch t is of the version of g, or of a version that it came from, and
# holds
def Impact.keeps(g: Impact, t: Touch) -> Bool:
  match g t:
    case Impact{+s, +m} Touch{+v, c, b, u}:
      List.all.if(
        w => Node.touches(s, Touch{v, c, b, u}),
        List.all.if(
          w => Node.has(s, Maybe.default(&2, Ledgers.Id, m, v), v),
          Maybe.is_some(&2, Ledgers.Id, m)
        )
      )

# the touches that may hold of the branches es
def Impact.cands(+s: State(), es: List<&2, Branch>) -> List<&2, Touch>:
  match es:
    case Nil{}:
      []
    case Con{b, r}:
      List.append(&2, Touch, Affects.cands(s, b), Impact.cands(s, r))

# what the changes up to the point p touch elsewhere
def Node.impact(+s: State(), p: Point) -> List<&2, Touch>:
  Shared.List.keep(
    ~Touch,
    ~Impact,
    ~Impact.keeps,
    Impact.cands(s, Branch.names(Node.branches(s))),
    Impact{s, Node.version(s, p)}
  )

# Notices
# -------

# what a subscription or a poll follows: the versions or the conflicts of a
# branch, the changes elsewhere that touch it, or the groups of a store
type Topic is Data:
  Topic.versions{branch: Branch}
  Topic.conflicts{branch: Branch}
  Topic.affects{branch: Branch}
  Topic.groups{store: Ledgers.Id}

# an event of a topic. GroupCycle: the group is inside itself, as syncs can
# leave groups; a set-group settles it
type Notice is Data:
  Notice.versioned{branch: Branch, version: Ledgers.Id}
  Notice.conflicted{branch: Branch, version: Ledgers.Id}
  Notice.touched{touch: Touch}
  Notice.group_cycle{store: Ledgers.Id, group: String}

# a and b are the same notice
def Notice.is_eq(a: Notice, b: Notice) -> Bool:
  match a b:
    case Notice.versioned{b1, v1} Notice.versioned{b2, v2}:
      Bool.and(Branch.is_eq(b1, b2), Ledgers.Id.is_eq(v1, v2))
    case Notice.conflicted{b1, v1} Notice.conflicted{b2, v2}:
      Bool.and(Branch.is_eq(b1, b2), Ledgers.Id.is_eq(v1, v2))
    case Notice.touched{t1} Notice.touched{t2}:
      Touch.is_eq(t1, t2)
    case Notice.group_cycle{r1, g1} Notice.group_cycle{r2, g2}:
      Bool.and(Ledgers.Id.is_eq(r1, r2), String.eq(g1, g2))
    case _ _:
      False{}

# the versions xs of the branch b, as notices
def Notice.versions(+b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{x, r}:
      Notice.versioned{b, x} <> Notice.versions(b, r)

# the merges of the branch b among xs that clashed, as notices
def Notice.conflicts(+s: State(), +b: Branch, xs: List<&2, Ledgers.Id>) -> List<&2, Notice>:
  match xs:
    case Nil{}:
      []
    case Con{+x, r}:
      List.filter.put(
        Notice,
        Notice.conflicted{b, x},
        Notice.conflicts(s, b, r),
        Bool.not(
          List.is_empty(&2, Resources.Name, Merge.clashes(s, x, Ledgers.State.asked(~Ask, s, x)))
        )
      )

# the touches ts, as notices
def Notice.touches(ts: List<&2, Touch>) -> List<&2, Notice>:
  match ts:
    case Nil{}:
      []
    case Con{t, r}:
      Notice.touched{t} <> Notice.touches(r)

# the groups of gs of the store r inside themselves, as notices
def Notice.cycles(+s: State(), +r: Ledgers.Id, gs: List<&2, Member>) -> List<&2, Notice>:
  match gs:
    case Nil{}:
      []
    case Con{Member.group{+g}, rest}:
      List.filter.put(
        Notice,
        Notice.group_cycle{r, g},
        Notice.cycles(s, r, rest),
        Node.is_inside(s, r, Member.group{g}, g)
      )
    case Con{m, rest}:
      Notice.cycles(s, r, rest)

# the notices of the topic t in s
def Notice.all(+s: State(), t: Topic) -> List<&2, Notice>:
  match t:
    case Topic.versions{+b}:
      Notice.versions(b, Branch.versions(s, b))
    case Topic.conflicts{+b}:
      Notice.conflicts(s, b, Branch.versions(s, b))
    case Topic.affects{b}:
      Notice.touches(Node.affects(s, b))
    case Topic.groups{+r}:
      Notice.cycles(s, r, Group.all(Groups{s, r}))

# the notices of ns that old does not hold
def Notice.new(ns: List<&2, Notice>, +old: List<&2, Notice>) -> List<&2, Notice>:
  match ns:
    case Nil{}:
      []
    case Con{+n, r}:
      List.filter.put(
        Notice,
        n,
        Notice.new(r, old),
        Bool.not(List.contains(~Notice, ~Notice.is_eq, old, n))
      )

# the notices of the topic t in s that since does not have
def Node.notices(s: State(), +t: Topic, since: State()) -> List<&2, Notice>:
  Notice.new(Notice.all(s, t), Notice.all(since, t))

# Laws
# ----

# s with the request q of e, before any vote: what a node holds once it takes
# q in
def Node.taken(s: State(), +e: Envelope, q: Ask) -> State():
  Ledgers.State.put(
    ~Ask,
    ~Ask.is_eq,
    s,
    Ledgers.Slot.ask(Envelope.of(e)),
    Ledgers.Entry.ask{Envelope.of(e), Envelope.time(e), q}
  )

# the sole owner n of the tip of a branch takes in a write of a resource that
# did not change since its base: the write is Written, and its version holds
# the bytes
law Node.write_written:
  for +n: String
  for +s: State()
  for +e: Envelope
  for +r: Ledgers.Id
  for +b: String
  for +name: Resources.Name
  for +base: Maybe<&2, Ledgers.Id>
  for +x: Texts.Bytes()
  for +h: Nat
  {
    Tries.Trie.get(
      Ledgers.Cell<Ledgers.Entry<Ask>>,
      s,
      Ledgers.Slot.ask(Envelope.of(e))
    )
      == None{}: Maybe<&2, Ledgers.Cell<Ledgers.Entry<Ask>>>
  }
    -> {
      Ledgers.State.tip(
        ~Ask,
        ~Ask.view,
        Node.taken(
          s,
          e,
          Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
        ),
        Line.chain(r, Some{Line.branch{b}})
      )
        == Some{Ledgers.Tip{h, [n]}}: Maybe<&2, Ledgers.Tip>
    }
    -> {
      Tries.Trie.get(
        Ledgers.Cell<Ledgers.Entry<Ask>>,
        Node.taken(
          s,
          e,
          Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
        ),
        Ledgers.Slot.vote(Line.chain(r, Some{Line.branch{b}}), h, n)
      )
        == None{}: Maybe<&2, Ledgers.Cell<Ledgers.Entry<Ask>>>
    }
    -> {
      Ledgers.Steps.verdict(
        ~Ask,
        Node.steps(
          Node.taken(
            s,
            e,
            Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
          ),
          r,
          Some{Line.branch{b}}
        ),
        Envelope.of(e)
      )
        == None{}: Maybe<&2, Bool>
    }
    -> {
      Judge.ready_maybe(
        Node.taken(
          s,
          e,
          Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
        ),
        base
      )
        == Some{True{}}: Maybe<&2, Bool>
    }
    -> {
      Bytes.same(
        Res.of(
          Node.taken(
            s,
            e,
            Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
          ),
          name,
          Ids.last(
            Steps.taken(
              Node.steps(
                Node.taken(
                  s,
                  e,
                  Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
                ),
                r,
                Some{Line.branch{b}}
              )
            )
          )
        ),
        Res.of(
          Node.taken(
            s,
            e,
            Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
          ),
          name,
          base
        )
      )
        == True{}: Bool
    }
    -> {
      Node.answer(
        Node.ask(
          n,
          s,
          e,
          Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
        ),
        Envelope.of(e)
      )
        == Answer.written{Envelope.of(e)}: Answer
    }
      & {
        Node.content(
          Node.ask(
            n,
            s,
            e,
            Ask.on{r, Some{Line.branch{b}}, Change.write{name, base, Content.bytes{x}}}
          ),
          name,
          Point.at{Envelope.of(e)}
        )
          == Some{x}: Maybe<&2, Texts.Bytes()>
      }
