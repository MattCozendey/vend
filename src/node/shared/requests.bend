import Base
import ../../shared/replica.bend as Replicas
import ../../shared/shared/ledger.bend as Ledgers
import ../../shared/shared/rope.bend as Ropes
import ../../shared/shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/shared/shared.bend as Shared
import ./shared/resources.bend as Resources

# Requests
# --------
# What a writer asks of a Vend Node: the changes, the requests that carry
# them, their codes, and the machine that a replica runs them on.

# a member of an owner group: a node, or another group of its store
type Member is Data:
  Member.Node{name: String}
  Member.Group{name: String}

# a version of a store, named from inside the store: the branch that made it
# (none: the store itself), and the request that made it
type Ref is Data:
  Ref{branch: Maybe<&2, String>, id: Ledgers.Id}

# content that a change takes from a version: the version that it is said to
# be of, and the root of the tree. A change carries the root, so its line
# never reads another line; the version is a claim, which a reader can check
type Source is Data:
  Source{version: Ref, root: Maybe<&2, Hashes.Hash>}

# what a resource is: the hash of its format, which the ledger holds as data
# (Formats.Format.code), and the root of the rope of its bytes. A resource
# carries its format, so every node reads it the same way, whatever its name
type Res is Data:
  Res{format: Hashes.Hash, root: Ropes.Root}

# new content: a resource that a node holds, or what an old version held. A
# change names its content and does not carry it, so a change of a huge
# resource is small
type Content is Data:
  Content.New{res: Res}
  Content.Of{version: Ledgers.Id}

# a change of a branch, or of its store (Ask.on). Key: the store gives the
# node the key that signs its first ballot in the store (again after the node
# lost its secret: a new chain of keys). Branch: the store makes the
# branch, at a version if any. Group: the store makes the group, or replaces
# its members. Own: the line's owner group is group, whose nodes, in the tree
# of the step at of the store (a store reads its own tree), are owners
type Change is Data:
  Change.Branch{name: String, at: Maybe<&2, Source>}
  Change.Group{name: String, members: List<&2, Member>}
  Change.Own{group: String, at: Maybe<&2, Source>, owners: List<&2, String>}
  Change.Write{name: Resources.Name, base: Maybe<&2, Ledgers.Id>, content: Content}
  Change.Resolve{conflict: Ledgers.Id, name: Resources.Name, content: Content}
  Change.Merge{from: Source, base: Maybe<&2, Source>}
  Change.Move{to: Source}
  Change.Mark{mark: String, message: String}
  Change.Key{node: String, key: Hashes.Hash}

# a change that a writer asks for: a store that starts with its first owners,
# or a change of a branch of a store (none: of the store itself)
type Ask is Data:
  Ask.Start{owners: List<&2, Replicas.Voter>}
  Ask.On{store: Hashes.Hash, branch: Maybe<&2, String>, change: Change}

# the version m, if any (where a line starts, or the base of a write), then r
def Base.code(m: Maybe<&2, Ledgers.Id>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Ledgers.Id, ~Ledgers.Id.code, m, r)

# a version, if any
def Base.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Ledgers.Id>>>:
  Codes.Code.maybe.read(~Ledgers.Id, ~Ledgers.Id.code.read, ts)

# the text t with the tag k, then r
def Tag.text(k: U32, t: String, r: List<&2, U32>) -> List<&2, U32>:
  k <> Codes.Code.text(t, r)

# the branch m, if any (none: the store), then r
def Target.code(m: Maybe<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~String, ~Codes.Code.text, m, r)

# a branch, if any
def Target.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, String>>>:
  Codes.Code.maybe.read(~String, ~Codes.Code.text.read, ts)

# the version v, then r
def Ref.code(v: Ref, r: List<&2, U32>) -> List<&2, U32>:
  match v:
    case Ref{b, i}:
      Target.code(b, Ledgers.Id.code(i, r))

# a version
def Ref.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ref>>:
  Codes.Code.two.read(
    ~Maybe<&2, String>,
    ~Ledgers.Id,
    ~Ref,
    ~Target.code.read,
    ~Ledgers.Id.code.read,
    b => i => Ref{b, i},
    ts
  )

# a version reads back
def Ref.code_read(
  v: Ref,
  r: List<&2, U32>
) -> {Ref.code.read(Ref.code(v, r)) == Some{Codes.Read{v, r}}: Maybe<&2, Codes.Read<Ref>>}:
  match v:
    case Ref{b, i}:
      Codes.Code.two_read(
        ~Maybe<&2, String>,
        ~Ledgers.Id,
        ~Ref,
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        ~Ledgers.Id.codec(),
        x => y => Ref{x, y},
        b,
        i,
        r
      )

# the code of versions
def Ref.codec() -> Codes.Codec(Ref):
  (Ref.code, (Ref.code.read, v => r => Ref.code_read(v, r)))

# the source s, then r
def Source.code(s: Source, r: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Source{v, h}:
      Ref.code(v, Codes.Code.maybe(~Hashes.Hash, ~Hashes.Hash.code, h, r))

# a source
def Source.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Source>>:
  Codes.Code.two.read(
    ~Ref,
    ~Maybe<&2, Hashes.Hash>,
    ~Source,
    ~Ref.code.read,
    ~(m => Codes.Code.maybe.read(~Hashes.Hash, ~Hashes.Hash.code.read, m)),
    v => h => Source{v, h},
    ts
  )

# a source reads back
def Source.code_read(
  s: Source,
  r: List<&2, U32>
) -> {Source.code.read(Source.code(s, r)) == Some{Codes.Read{s, r}}: Maybe<&2, Codes.Read<Source>>}:
  match s:
    case Source{v, h}:
      Codes.Code.two_read(
        ~Ref,
        ~Maybe<&2, Hashes.Hash>,
        ~Source,
        ~Ref.codec(),
        ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        x => y => Source{x, y},
        v,
        h,
        r
      )

# the code of sources
def Source.codec() -> Codes.Codec(Source):
  (Source.code, (Source.code.read, s => r => Source.code_read(s, r)))

# the source m, if any, then r
def At.code(m: Maybe<&2, Source>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.maybe(~Source, ~Source.code, m, r)

# a source, if any
def At.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Maybe<&2, Source>>>:
  Codes.Code.maybe.read(~Source, ~Source.code.read, ts)

# the member l, then r
def Member.code(l: Member, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Member.Node{n}:
      Tag.text(0, n, r)
    case Member.Group{n}:
      Tag.text(1, n, r)

# a member
def Member.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Member>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Member>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~String, ~Member, ~Codes.Code.text.read, n => Member.Node{n}, r),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Member>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(
            ~String,
            ~Member,
            ~Codes.Code.text.read,
            n => Member.Group{n},
            r
          ),
          u => None{}
        )
      )

# the members ms, then r
def Members.code(ms: List<&2, Member>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Member, ~Member.code, ms, r)

# members
def Members.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Member>>>:
  Codes.Code.list.read(~Member, ~Member.code.read, ts)

# the resource x, then r
def Res.code(x: Res, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Res{f, t}:
      Hashes.Hash.code(f, Ropes.Root.code(t, r))

# a resource
def Res.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Res>>:
  Codes.Code.two.read(
    ~Hashes.Hash,
    ~Ropes.Root,
    ~Res,
    ~Hashes.Hash.code.read,
    ~Ropes.Root.code.read,
    f => t => Res{f, t},
    ts
  )

# a resource reads back
def Res.code_read(
  x: Res,
  r: List<&2, U32>
) -> {Res.code.read(Res.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Res>>}:
  match x:
    case Res{f, t}:
      Codes.Code.two_read(
        ~Hashes.Hash,
        ~Ropes.Root,
        ~Res,
        ~Hashes.Hash.codec(),
        ~Ropes.Root.codec(),
        a => b => Res{a, b},
        f,
        t,
        r
      )

# the code of resources
def Res.codec() -> Codes.Codec(Res):
  (Res.code, (Res.code.read, x => r => Res.code_read(x, r)))

# the content c, then r
def Content.code(c: Content, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Content.New{x}:
      0 <> Res.code(x, r)
    case Content.Of{v}:
      1 <> Ledgers.Id.code(v, r)

# a content
def Content.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Content>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Content>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(~Res, ~Content, ~Res.code.read, x => Content.New{x}, r),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Content>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(
            ~Ledgers.Id,
            ~Content,
            ~Ledgers.Id.code.read,
            v => Content.Of{v},
            r
          ),
          u => None{}
        )
      )

# the change c, then r
def Change.code(c: Change, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Change.Branch{n, at}:
      0 <> Codes.Code.text(n, At.code(at, r))
    case Change.Own{g, at, os}:
      1 <> Codes.Code.text(g, At.code(at, Ledgers.Voters.code(os, r)))
    case Change.Write{n, base, x}:
      2 <> Resources.Name.code(n, Base.code(base, Content.code(x, r)))
    case Change.Resolve{k, n, x}:
      3 <> Ledgers.Id.code(k, Resources.Name.code(n, Content.code(x, r)))
    case Change.Merge{v, b}:
      4 <> Source.code(v, At.code(b, r))
    case Change.Move{v}:
      5 <> Source.code(v, r)
    case Change.Mark{m, t}:
      6 <> Codes.Code.text(m, Codes.Code.text(t, r))
    case Change.Group{g, ms}:
      7 <> Codes.Code.text(g, Members.code(ms, r))
    case Change.Key{n, k}:
      8 <> Codes.Code.text(n, Hashes.Hash.code(k, r))

# a change whose tag is x, from the tokens r after it
def Change.code.read.of(+x: U32, +r: List<&2, U32>) -> Maybe<&2, Codes.Read<Change>>:
  Shared.Bool.when(
    Maybe<&2, Codes.Read<Change>>,
    U32.is_eq(x, 0),
    u => Codes.Code.two.read(
      ~String,
      ~Maybe<&2, Source>,
      ~Change,
      ~Codes.Code.text.read,
      ~At.code.read,
      n => a => Change.Branch{n, a},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Change>>,
      U32.is_eq(x, 1),
      u => Codes.Code.three.read(
        ~String,
        ~Maybe<&2, Source>,
        ~List<&2, String>,
        ~Change,
        ~Codes.Code.text.read,
        ~At.code.read,
        ~Ledgers.Voters.code.read,
        g => a => os => Change.Own{g, a, os},
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
          ~Resources.Name.code.read,
          ~Base.code.read,
          ~Content.code.read,
          n => b => c => Change.Write{n, b, c},
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
            ~Ledgers.Id.code.read,
            ~Resources.Name.code.read,
            ~Content.code.read,
            k => n => c => Change.Resolve{k, n, c},
            r
          ),
          u => Shared.Bool.when(
            Maybe<&2, Codes.Read<Change>>,
            U32.is_eq(x, 4),
            u => Codes.Code.two.read(
              ~Source,
              ~Maybe<&2, Source>,
              ~Change,
              ~Source.code.read,
              ~At.code.read,
              v => b => Change.Merge{v, b},
              r
            ),
            u => Shared.Bool.when(
              Maybe<&2, Codes.Read<Change>>,
              U32.is_eq(x, 5),
              u => Codes.Code.one.read(
                ~Source,
                ~Change,
                ~Source.code.read,
                v => Change.Move{v},
                r
              ),
              u => Shared.Bool.when(
                Maybe<&2, Codes.Read<Change>>,
                U32.is_eq(x, 6),
                u => Codes.Code.two.read(
                  ~String,
                  ~String,
                  ~Change,
                  ~Codes.Code.text.read,
                  ~Codes.Code.text.read,
                  m => n => Change.Mark{m, n},
                  r
                ),
                u => Shared.Bool.when(
                  Maybe<&2, Codes.Read<Change>>,
                  U32.is_eq(x, 8),
                  u => Codes.Code.two.read(
                    ~String,
                    ~Hashes.Hash,
                    ~Change,
                    ~Codes.Code.text.read,
                    ~Hashes.Hash.code.read,
                    n => k => Change.Key{n, k},
                    r
                  ),
                  u => Shared.Bool.when(
                    Maybe<&2, Codes.Read<Change>>,
                    U32.is_eq(x, 7),
                    u => Codes.Code.two.read(
                      ~String,
                      ~List<&2, Member>,
                      ~Change,
                      ~Codes.Code.text.read,
                      ~Members.code.read,
                      g => ms => Change.Group{g, ms},
                      r
                    ),
                    u => None{}
                  )
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
    case Ask.Start{os}:
      0 <> Codes.Code.list(~Replicas.Voter, ~Replicas.Voter.code, os, r)
    case Ask.On{st, l, c}:
      1 <> Hashes.Hash.code(st, Target.code(l, Change.code(c, r)))

# a request
def Ask.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ask>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Ask>>,
        U32.is_eq(x, 0),
        u => Codes.Code.one.read(
          ~List<&2, Replicas.Voter>,
          ~Ask,
          ~(m => Codes.Code.list.read(~Replicas.Voter, ~Replicas.Voter.code.read, m)),
          os => Ask.Start{os},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Ask>>,
          U32.is_eq(x, 1),
          u => Codes.Code.three.read(
            ~Hashes.Hash,
            ~Maybe<&2, String>,
            ~Change,
            ~Ask,
            ~Hashes.Hash.code.read,
            ~Target.code.read,
            ~Change.code.read,
            s => l => c => Ask.On{s, l, c},
            r
          ),
          u => None{}
        )
      )

# a member reads back
def Member.code_read(
  x: Member,
  r: List<&2, U32>
) -> {Member.code.read(Member.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Member>>}:
  match x:
    case Member.Node{n}:
      Codes.Code.one_read(~String, ~Member, ~Codes.Code.text.codec(), a => Member.Node{a}, n, r)
    case Member.Group{n}:
      Codes.Code.one_read(~String, ~Member, ~Codes.Code.text.codec(), a => Member.Group{a}, n, r)

# the code of members
def Member.codec() -> Codes.Codec(Member):
  (Member.code, (Member.code.read, x => r => Member.code_read(x, r)))

# a content reads back
def Content.code_read(
  x: Content,
  r: List<&2, U32>
) -> {
  Content.code.read(Content.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Content>>
}:
  match x:
    case Content.New{b}:
      Codes.Code.one_read(~Res, ~Content, ~Res.codec(), a => Content.New{a}, b, r)
    case Content.Of{v}:
      Codes.Code.one_read(~Ledgers.Id, ~Content, ~Ledgers.Id.codec(), a => Content.Of{a}, v, r)

# the code of contents
def Content.codec() -> Codes.Codec(Content):
  (Content.code, (Content.code.read, x => r => Content.code_read(x, r)))

# a change reads back
def Change.code_read(
  x: Change,
  r: List<&2, U32>
) -> {Change.code.read(Change.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Change>>}:
  match x:
    case Change.Branch{n, at}:
      Codes.Code.two_read(
        ~String,
        ~Maybe<&2, Source>,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Source, ~Source.codec()),
        a => b => Change.Branch{a, b},
        n,
        at,
        r
      )
    case Change.Group{g, ms}:
      Codes.Code.two_read(
        ~String,
        ~List<&2, Member>,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.list.codec(~Member, ~Member.codec()),
        a => b => Change.Group{a, b},
        g,
        ms,
        r
      )
    case Change.Own{g, at, os}:
      Codes.Code.three_read(
        ~String,
        ~Maybe<&2, Source>,
        ~List<&2, String>,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Source, ~Source.codec()),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => b => c => Change.Own{a, b, c},
        g,
        at,
        os,
        r
      )
    case Change.Write{n, base, c}:
      Codes.Code.three_read(
        ~Resources.Name,
        ~Maybe<&2, Ledgers.Id>,
        ~Content,
        ~Change,
        ~Resources.Name.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Content.codec(),
        a => b => c => Change.Write{a, b, c},
        n,
        base,
        c,
        r
      )
    case Change.Resolve{k, n, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Resources.Name,
        ~Content,
        ~Change,
        ~Ledgers.Id.codec(),
        ~Resources.Name.codec(),
        ~Content.codec(),
        a => b => c => Change.Resolve{a, b, c},
        k,
        n,
        c,
        r
      )
    case Change.Merge{v, b}:
      Codes.Code.two_read(
        ~Source,
        ~Maybe<&2, Source>,
        ~Change,
        ~Source.codec(),
        ~Codes.Code.maybe.codec(~Source, ~Source.codec()),
        x => y => Change.Merge{x, y},
        v,
        b,
        r
      )
    case Change.Move{v}:
      Codes.Code.one_read(~Source, ~Change, ~Source.codec(), a => Change.Move{a}, v, r)
    case Change.Mark{m, n}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Change.Mark{a, b},
        m,
        n,
        r
      )
    case Change.Key{n, k}:
      Codes.Code.two_read(
        ~String,
        ~Hashes.Hash,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Hashes.Hash.codec(),
        a => b => Change.Key{a, b},
        n,
        k,
        r
      )

# the code of changes
def Change.codec() -> Codes.Codec(Change):
  (Change.code, (Change.code.read, x => r => Change.code_read(x, r)))

# a request reads back
def Ask.code_read(
  x: Ask,
  r: List<&2, U32>
) -> {Ask.code.read(Ask.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Ask>>}:
  match x:
    case Ask.Start{os}:
      Codes.Code.one_read(
        ~List<&2, Replicas.Voter>,
        ~Ask,
        ~Codes.Code.list.codec(~Replicas.Voter, ~Replicas.Voter.codec()),
        a => Ask.Start{a},
        os,
        r
      )
    case Ask.On{st, l, c}:
      Codes.Code.three_read(
        ~Hashes.Hash,
        ~Maybe<&2, String>,
        ~Change,
        ~Ask,
        ~Hashes.Hash.codec(),
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        ~Change.codec(),
        a => b => c => Ask.On{a, b, c},
        st,
        l,
        c,
        r
      )

# the code of requests
def Ask.codec() -> Codes.Codec(Ask):
  (Ask.code, (Ask.code.read, x => r => Ask.code_read(x, r)))

# how the request q arrives at a node
def Ask.arrival(q: Ask) -> Replicas.Arrival:
  match q:
    case Ask.Start{os}:
      Replicas.Arrival.Starts{os}
    case Ask.On{r, l, c}:
      Replicas.Arrival.Waits{Ledgers.Line{r, l}}

# the change q is one of who decides: a first key of a node, a group, the
# owners of a line, or a new branch. The owners of a store decide these, so an
# owner casts for one only when a writer connected to it asked for it
def Ask.governs(q: Ask) -> Bool:
  match q:
    case Ask.On{r, l, Change.Key{n, k}}:
      True{}
    case Ask.On{r, l, Change.Group{g, ms}}:
      True{}
    case Ask.On{r, l, Change.Own{g, at, os}}:
      True{}
    case Ask.On{r, l, Change.Branch{b, at}}:
      True{}
    case x:
      False{}

# the key of the first key of the node n in a store
def Key.seal(n: String) -> List<&2, U32>:
  8 <> Codes.Code.text(n, [])

# the machine of Vend: its requests, their code (two requests are the same
# when their codes are), how one arrives, whether it changes who decides, and
# the key of a node's first key
def Ask.machine() -> Replicas.Machine():
  (Ask, (Ask.codec(), (Ask.arrival, (Ask.governs, Key.seal))))
