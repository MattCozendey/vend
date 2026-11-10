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

# Names
# -----
# A node, writer, branch, group, mark, request ID and time are texts. A
# request, and the version that it made, is a Ledgers.Id. A store is named by
# the request that started it. A line is a store itself (no branch) or one of
# its branches.

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a member of an owner group: a node, or another group of its store
type Member is Data:
  Member.Node{name: String}
  Member.Group{name: String}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# new content: what a node holds under a root (the root of the rope of its
# bytes: Content.of), or what an old version held. A change names its content
# and does not carry it, so a change of a huge resource is small
type Content is Data:
  Content.Root{root: Ropes.Root}
  Content.Of{version: Ledgers.Id}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a version, the newest version of a branch, or a mark of a branch
type Point is Data:
  Point.At{version: Ledgers.Id}
  Point.Head{store: Ledgers.Id, branch: String}
  Point.Mark{store: Ledgers.Id, branch: String, mark: String}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a change of a branch, or of its store (Ask.on). Key: the store gives the
# node the key that signs its first ballot in the store (again after the node
# lost its secret: a new chain of keys). Branch: the store makes the
# branch, at a version if any. Group: the store makes the group, or replaces
# its members. Own: the line's owner group is group, whose nodes, in the tree
# of the step at of the store (a store reads its own tree), are owners
type Change is Data:
  Change.Branch{name: String, at: Maybe<&2, Ledgers.Id>}
  Change.Group{name: String, members: List<&2, Member>}
  Change.Own{group: String, at: Maybe<&2, Ledgers.Id>, owners: List<&2, String>}
  Change.Write{name: Resources.Name, base: Maybe<&2, Ledgers.Id>, content: Content}
  Change.Resolve{conflict: Ledgers.Id, name: Resources.Name, content: Content}
  Change.Merge{from: Ledgers.Id}
  Change.Move{to: Ledgers.Id}
  Change.Mark{mark: String, message: String}
  Change.Key{node: String, key: Hashes.Hash}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# bend-lint: expect-begin bend-lint-rules/layout/case@warning -- a constructor is PascalCase, as in Base (Some, Con): the rule reads a constructor as a law
# a change that a writer asks for: a store that starts with its first owners,
# or a change of a branch of a store (none: of the store itself)
type Ask is Data:
  Ask.Start{owners: List<&2, Replicas.Owner>}
  Ask.On{store: Ledgers.Id, branch: Maybe<&2, String>, change: Change}
# bend-lint: expect-end bend-lint-rules/layout/case@warning

# a and b are the same member
def Member.is_eq(a: Member, b: Member) -> Bool:
  match a b:
    case Member.Node{x} Member.Node{y}:
      String.eq(x, y)
    case Member.Group{x} Member.Group{y}:
      String.eq(x, y)
    case _ _:
      False{}

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

# the content c, then r
def Content.code(c: Content, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Content.Root{x}:
      0 <> Ropes.Root.code(x, r)
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
        u => Codes.Code.one.read(
          ~Ropes.Root,
          ~Content,
          ~Ropes.Root.code.read,
          x => Content.Root{x},
          r
        ),
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
      0 <> Codes.Code.text(n, Base.code(at, r))
    case Change.Own{g, at, os}:
      1 <> Codes.Code.text(g, Base.code(at, Ledgers.Owners.code(os, r)))
    case Change.Write{n, base, x}:
      2 <> Resources.Name.code(n, Base.code(base, Content.code(x, r)))
    case Change.Resolve{k, n, x}:
      3 <> Ledgers.Id.code(k, Resources.Name.code(n, Content.code(x, r)))
    case Change.Merge{v}:
      4 <> Ledgers.Id.code(v, r)
    case Change.Move{v}:
      5 <> Ledgers.Id.code(v, r)
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
      ~Maybe<&2, Ledgers.Id>,
      ~Change,
      ~Codes.Code.text.read,
      ~Base.code.read,
      n => a => Change.Branch{n, a},
      r
    ),
    u => Shared.Bool.when(
      Maybe<&2, Codes.Read<Change>>,
      U32.is_eq(x, 1),
      u => Codes.Code.three.read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Change,
        ~Codes.Code.text.read,
        ~Base.code.read,
        ~Ledgers.Owners.code.read,
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
            u => Codes.Code.one.read(
              ~Ledgers.Id,
              ~Change,
              ~Ledgers.Id.code.read,
              v => Change.Merge{v},
              r
            ),
            u => Shared.Bool.when(
              Maybe<&2, Codes.Read<Change>>,
              U32.is_eq(x, 5),
              u => Codes.Code.one.read(
                ~Ledgers.Id,
                ~Change,
                ~Ledgers.Id.code.read,
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
      0 <> Codes.Code.list(~Replicas.Owner, ~Replicas.Owner.code, os, r)
    case Ask.On{st, l, c}:
      1 <> Ledgers.Id.code(st, Target.code(l, Change.code(c, r)))

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
          ~List<&2, Replicas.Owner>,
          ~Ask,
          ~(m => Codes.Code.list.read(~Replicas.Owner, ~Replicas.Owner.code.read, m)),
          os => Ask.Start{os},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Ask>>,
          U32.is_eq(x, 1),
          u => Codes.Code.three.read(
            ~Ledgers.Id,
            ~Maybe<&2, String>,
            ~Change,
            ~Ask,
            ~Ledgers.Id.code.read,
            ~Target.code.read,
            ~Change.code.read,
            s => l => c => Ask.On{s, l, c},
            r
          ),
          u => None{}
        )
      )

# a and b are the same request: they have the same code
def Ask.is_eq(a: Ask, b: Ask) -> Bool:
  Codes.Code.is_eq(~Ask, ~Ask.code, a, b)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument
# Codes
# -----

# a member reads back
def Member.code_read(
  x: Member,
  r: List<&2, U32>
) -> {
  Member.code.read(
    Member.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Member>>
}:
  match x:
    case Member.Node{n}:
      Codes.Code.one_read(
        ~String,
        ~Member,
        ~Codes.Code.text.codec(),
        a => Member.Node{a},
        n,
        r
      )
    case Member.Group{n}:
      Codes.Code.one_read(
        ~String,
        ~Member,
        ~Codes.Code.text.codec(),
        a => Member.Group{a},
        n,
        r
      )

# the code of members
def Member.codec() -> Codes.Codec(Member):
  (Member.code, (Member.code.read, x => r => Member.code_read(x, r)))

# a content reads back
def Content.code_read(
  x: Content,
  r: List<&2, U32>
) -> {
  Content.code.read(
    Content.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Content>>
}:
  match x:
    case Content.Root{b}:
      Codes.Code.one_read(
        ~Ropes.Root,
        ~Content,
        ~Ropes.Root.codec(),
        a => Content.Root{a},
        b,
        r
      )
    case Content.Of{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Content,
        ~Ledgers.Id.codec(),
        a => Content.Of{a},
        v,
        r
      )

# the code of contents
def Content.codec() -> Codes.Codec(Content):
  (Content.code, (Content.code.read, x => r => Content.code_read(x, r)))

# a change reads back
def Change.code_read(
  x: Change,
  r: List<&2, U32>
) -> {
  Change.code.read(
    Change.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Change>>
}:
  match x:
    case Change.Branch{n, at}:
      Codes.Code.two_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
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
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
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
    case Change.Merge{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Change,
        ~Ledgers.Id.codec(),
        a => Change.Merge{a},
        v,
        r
      )
    case Change.Move{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Change,
        ~Ledgers.Id.codec(),
        a => Change.Move{a},
        v,
        r
      )
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
) -> {
  Ask.code.read(
    Ask.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Ask>>
}:
  match x:
    case Ask.Start{os}:
      Codes.Code.one_read(
        ~List<&2, Replicas.Owner>,
        ~Ask,
        ~Codes.Code.list.codec(~Replicas.Owner, ~Replicas.Owner.codec()),
        a => Ask.Start{a},
        os,
        r
      )
    case Ask.On{st, l, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Maybe<&2, String>,
        ~Change,
        ~Ask,
        ~Ledgers.Id.codec(),
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

# the laws of Spec.Ask.is_eq: two requests are the same exactly when their codes
# are
def Ask.laws() -> Shared.Eq.Laws(Ask, Ask.is_eq):
  Codes.Code.eq_laws(~Ask, ~Ask.codec())
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# how the request q arrives at a node
def Ask.arrival(q: Ask) -> Replicas.Arrival:
  match q:
    case Ask.Start{os}:
      Replicas.Arrival.Starts{os}
    case Ask.On{r, l, c}:
      Replicas.Arrival.Waits{r, l}

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

# the machine of Vend: its requests, when two are the same, how one arrives,
# whether it changes who decides, and the key of a node's first key
def Ask.machine() -> Replicas.Machine():
  (Ask, (Ask.is_eq, (Ask.laws(), (Ask.arrival, (Ask.governs, Key.seal)))))

# the owners that the change c gives its chain, when it sets them
def Change.owners(c: Change) -> Maybe<&2, List<&2, String>>:
  match c:
    case Change.Own{g, at, os}:
      Some{os}
    case _:
      None{}

# The state
# ---------

# Content
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
  s: Replicas.Node<Ask>,
  h: Maybe<&2, Hashes.Hash>,
  n: Resources.Name
) -> Maybe<&2, Maybe<&2, Ropes.Root>>:
  Maybe.bind(
    &2,
    Maybe<&2, List<&2, U32>>,
    Maybe<&2, Ropes.Root>,
    Replicas.Node.find(~Ask.machine(), s, h, Key.res(n)),
    m => Some{Res.found(m)}
  )

# the root of the content of the resource n in the tree whose root is h (none:
# it is not there)
def Res.root(s: Replicas.Node<Ask>, h: Maybe<&2, Hashes.Hash>, n: Resources.Name) -> Maybe<&2, Ropes.Root>:
  Maybe.bind(&2, List<&2, U32>, Ropes.Root, Replicas.Node.get(~Ask.machine(), s, h, Key.res(n)), ws => Res.read(ws))

# a and b are the same root, or both none: the same content
def Roots.same(a: Maybe<&2, Ropes.Root>, b: Maybe<&2, Ropes.Root>) -> Bool:
  Shared.Maybe.is_eq(~Ropes.Root, ~Ropes.Root.is_eq, a, b)

# the content of the bytes b: the root of their rope
def Content.of(b: Texts.Bytes()) -> Content:
  Content.Root{Ropes.Put.root(Replicas.Bytes.rope(b))}

# the members of the group g in the store tree whose root is h, if g is there
def Members.in(s: Replicas.Node<Ask>, h: Maybe<&2, Hashes.Hash>, g: String) -> Maybe<&2, List<&2, Member>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, Member>,
    Replicas.Node.get(~Ask.machine(), s, h, Key.group(g)),
    ws => Replicas.Read.whole(List<&2, Member>, Members.code.read(ws))
  )

# the line of the request i of the change q
def Ask.chain(i: Ledgers.Id, q: Ask) -> Ledgers.Chain:
  Replicas.Arrival.chain(i, Ask.arrival(q))

# Ancestry
# --------
# A version came from the versions before it on its line, by number, and from
# those that its version vector names, at their numbers or before.

# the newest place of the line c that the content whose root is h came from
def Node.vector(s: Replicas.Node<Ask>, h: Maybe<&2, Hashes.Hash>, +c: Ledgers.Chain) -> Maybe<&2, Replicas.Place>:
  Maybe.bind(&2, List<&2, U32>, Replicas.Place, Replicas.Node.get(~Ask.machine(), s, h, Key.vector(c)), ws => Replicas.Place.read(c, ws))

# the version at the place px, whose content has the root hx, came from the
# one at the place pv
def Place.from(s: Replicas.Node<Ask>, +px: Replicas.Place, hx: Maybe<&2, Hashes.Hash>, +pv: Replicas.Place) -> Bool:
  Shared.Bool.when(
    Bool,
    Ledgers.Chain.is_eq(Replicas.Place.chain(px), Replicas.Place.chain(pv)),
    u => Replicas.Place.covers(px, pv),
    u => Replicas.Place.covered(Node.vector(s, hx, Replicas.Place.chain(pv)), pv)
  )

# Node.has once the places of x (mx) and of v (mv) and the root of x (mr) are
# known
def Has.of(
  s: Replicas.Node<Ask>,
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
def Node.has(+s: Replicas.Node<Ask>, +v: Ledgers.Id, +x: Ledgers.Id) -> Bool:
  List.any.if(
    u => Has.of(s, Replicas.Node.place(~Ask.machine(), s, x), Replicas.Node.place(~Ask.machine(), s, v), Replicas.Node.root(~Ask.machine(), s, x)),
    Ledgers.Id.is_eq(x, v)
  )

# the newer of the versions x and y: y when it came from x, else x when it came
# from y, else none
def Node.forward(+s: Replicas.Node<Ask>, +x: Ledgers.Id, +y: Ledgers.Id) -> Maybe<&2, Ledgers.Id>:
  Shared.Bool.when(
    Maybe<&2, Ledgers.Id>,
    Node.has(s, y, x),
    u => Some{y},
    u => Shared.Bool.when(Maybe<&2, Ledgers.Id>, Node.has(s, x, y), w => Some{x}, w => None{})
  )
