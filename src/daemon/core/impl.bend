import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/rope.bend as Ropes
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./spec.bend as Spec

# The proofs of the core's laws.

# Codes
# -----

# a member reads back
def Member.code_read(
  x: Spec.Member,
  r: List<&2, U32>
) -> {
  Spec.Member.code.read(
    Spec.Member.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Member>>
}:
  match x:
    case Spec.Member.Node{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.Node{a},
        n,
        r
      )
    case Spec.Member.Group{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.Group{a},
        n,
        r
      )

# the code of members
def Member.codec() -> Codes.Codec(Spec.Member):
  (Spec.Member.code, (Spec.Member.code.read, x => r => Member.code_read(x, r)))

# a content reads back
def Content.code_read(
  x: Spec.Content,
  r: List<&2, U32>
) -> {
  Spec.Content.code.read(
    Spec.Content.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Content>>
}:
  match x:
    case Spec.Content.Root{b}:
      Codes.Code.one_read(
        ~Ropes.Root,
        ~Spec.Content,
        ~Ropes.Root.codec(),
        a => Spec.Content.Root{a},
        b,
        r
      )
    case Spec.Content.Of{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Content,
        ~Ledgers.Id.codec(),
        a => Spec.Content.Of{a},
        v,
        r
      )

# the code of contents
def Content.codec() -> Codes.Codec(Spec.Content):
  (Spec.Content.code, (Spec.Content.code.read, x => r => Content.code_read(x, r)))

# a change reads back
def Change.code_read(
  x: Spec.Change,
  r: List<&2, U32>
) -> {
  Spec.Change.code.read(
    Spec.Change.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Change>>
}:
  match x:
    case Spec.Change.Branch{n, at}:
      Codes.Code.two_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        a => b => Spec.Change.Branch{a, b},
        n,
        at,
        r
      )
    case Spec.Change.Group{g, ms}:
      Codes.Code.two_read(
        ~String,
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => b => Spec.Change.Group{a, b},
        g,
        ms,
        r
      )
    case Spec.Change.Own{g, at, os}:
      Codes.Code.three_read(
        ~String,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, String>,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => b => c => Spec.Change.Own{a, b, c},
        g,
        at,
        os,
        r
      )
    case Spec.Change.Write{n, base, c}:
      Codes.Code.three_read(
        ~Resources.Name,
        ~Maybe<&2, Ledgers.Id>,
        ~Spec.Content,
        ~Spec.Change,
        ~Resources.Name.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Content.codec(),
        a => b => c => Spec.Change.Write{a, b, c},
        n,
        base,
        c,
        r
      )
    case Spec.Change.Resolve{k, n, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Resources.Name,
        ~Spec.Content,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        ~Resources.Name.codec(),
        ~Content.codec(),
        a => b => c => Spec.Change.Resolve{a, b, c},
        k,
        n,
        c,
        r
      )
    case Spec.Change.Merge{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        a => Spec.Change.Merge{a},
        v,
        r
      )
    case Spec.Change.Move{v}:
      Codes.Code.one_read(
        ~Ledgers.Id,
        ~Spec.Change,
        ~Ledgers.Id.codec(),
        a => Spec.Change.Move{a},
        v,
        r
      )
    case Spec.Change.Mark{m, n}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Spec.Change.Mark{a, b},
        m,
        n,
        r
      )

# the code of changes
def Change.codec() -> Codes.Codec(Spec.Change):
  (Spec.Change.code, (Spec.Change.code.read, x => r => Change.code_read(x, r)))

# a request reads back
def Ask.code_read(
  x: Spec.Ask,
  r: List<&2, U32>
) -> {
  Spec.Ask.code.read(Spec.Ask.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Ask>>
}:
  match x:
    case Spec.Ask.Start{os}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Ask,
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => Spec.Ask.Start{a},
        os,
        r
      )
    case Spec.Ask.On{st, l, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Maybe<&2, String>,
        ~Spec.Change,
        ~Spec.Ask,
        ~Ledgers.Id.codec(),
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        ~Change.codec(),
        a => b => c => Spec.Ask.On{a, b, c},
        st,
        l,
        c,
        r
      )

# the code of requests
def Ask.codec() -> Codes.Codec(Spec.Ask):
  (Spec.Ask.code, (Spec.Ask.code.read, x => r => Ask.code_read(x, r)))

# the laws of Spec.Ask.is_eq: two requests are the same exactly when their codes
# are
def Ask.laws() -> Shared.Eq.Laws(Spec.Ask, Spec.Ask.is_eq):
  Codes.Code.eq_laws(~Spec.Ask, ~Ask.codec())

def Spec.Ask.same():
  Ask.laws()

# Owners
# ------

# owners that fit the nodes ns are ns
def Fits.same(
  +os: List<&2, String>,
  +ns: List<&2, String>
) -> {Spec.Own.fits(os, ns) == True{}: Bool} -> {os == ns: List<&2, String>}:
  e => Shared.Eq.sound(
    ~List<&2, String>,
    ~Ledgers.Owners.is_eq,
    Ledgers.Owners.laws(),
    os,
    ns
  )(
    Shared.List.all.if_rest(
      Bool.not(List.is_empty(&2, String, os)),
      u => Ledgers.Owners.is_eq(os, ns)
    )(e)
  )

# Own.takes_inside for a branch, once whether its step is the store's is known
# (m)
def Takes.at(
  +os: List<&2, String>,
  +ns: List<&2, String>,
  m: Maybe<&2, Bool>
) -> {
  Maybe.bind(
    &2,
    Bool,
    Bool,
    m,
    k => Some{List.all.if(u => Spec.Own.fits(os, ns), k)}
  )
    == Some{True{}}: Maybe<&2, Bool>
} -> {os == ns: List<&2, String>}:
  match m:
    case None{}:
      e => Empty.absurd({os == ns: List<&2, String>}, Shared.Maybe.none_ne_some(Bool, True{}, e))
    case Some{k}:
      e => Fits.same(os, ns)(
        Shared.List.all.if_rest(
          k,
          u => Spec.Own.fits(os, ns)
        )(
          Shared.Maybe.some_inj(
            Bool,
            List.all.if(u => Spec.Own.fits(os, ns), k),
            True{},
            e
          )
        )
      )

def Spec.Own.takes_inside(s, r, l, g, at, os, h):
  Takes.at(os, Spec.Group.nodes(s, Spec.Own.tree(s, l, at, h), g), Spec.Own.ok(s, r, l, at))
