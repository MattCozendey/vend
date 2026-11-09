import Base
import ../../shared.bend as Shared
import ../shared/ledger2.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/text.bend as Texts
import ./spec2.bend as Spec

# The proofs of the core's laws.

# Codes
# -----

# a request ID reads back
def Id.code_read(
  x: Ledgers.Id,
  r: List<&2, U32>
) -> {
  Spec.Id.code.read(Spec.Id.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Ledgers.Id>>
}:
  match x:
    case Ledgers.Id{w, q}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Ledgers.Id,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Ledgers.Id{a, b},
        w,
        q,
        r
      )

# the code of request IDs
def Id.codec() -> Codes.Codec(Ledgers.Id):
  (Spec.Id.code, (Spec.Id.code.read, x => r => Id.code_read(x, r)))

# a resource name reads back
def Name.code_read(
  x: Resources.Name,
  r: List<&2, U32>
) -> {
  Spec.Name.code.read(
    Spec.Name.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Resources.Name>>
}:
  match x:
    case Resources.Name{n}:
      Codes.Code.one_read(
        ~String,
        ~Resources.Name,
        ~Codes.Code.text.codec(),
        a => Resources.Name{a},
        n,
        r
      )

# the code of resource names
def Name.codec() -> Codes.Codec(Resources.Name):
  (Spec.Name.code, (Spec.Name.code.read, x => r => Name.code_read(x, r)))

# a line reads back
def Line.code_read(
  x: Spec.Line,
  r: List<&2, U32>
) -> {
  Spec.Line.code.read(
    Spec.Line.code(x, r)
  )
    == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Spec.Line>>
}:
  match x:
    case Spec.Line.branch{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Line,
        ~Codes.Code.text.codec(),
        a => Spec.Line.branch{a},
        n,
        r
      )
    case Spec.Line.group{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Line,
        ~Codes.Code.text.codec(),
        a => Spec.Line.group{a},
        n,
        r
      )

# the code of lines
def Line.codec() -> Codes.Codec(Spec.Line):
  (Spec.Line.code, (Spec.Line.code.read, x => r => Line.code_read(x, r)))

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
    case Spec.Member.node{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.node{a},
        n,
        r
      )
    case Spec.Member.group{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Member,
        ~Codes.Code.text.codec(),
        a => Spec.Member.group{a},
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
    case Spec.Content.bytes{b}:
      Codes.Code.one_read(
        ~Texts.Bytes(),
        ~Spec.Content,
        ~Codes.Code.words.codec(),
        a => Spec.Content.bytes{a},
        b,
        r
      )
    case Spec.Content.of{v}:
      Codes.Code.one_read(~Ledgers.Id, ~Spec.Content, ~Id.codec(), a => Spec.Content.of{a}, v, r)

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
    case Spec.Change.make{l, at, ms}:
      Codes.Code.three_read(
        ~Spec.Line,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Line.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Id.codec()),
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => b => c => Spec.Change.make{a, b, c},
        l,
        at,
        ms,
        r
      )
    case Spec.Change.own{os}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Change,
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => Spec.Change.own{a},
        os,
        r
      )
    case Spec.Change.write{n, base, c}:
      Codes.Code.three_read(
        ~Resources.Name,
        ~Maybe<&2, Ledgers.Id>,
        ~Spec.Content,
        ~Spec.Change,
        ~Name.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Id.codec()),
        ~Content.codec(),
        a => b => c => Spec.Change.write{a, b, c},
        n,
        base,
        c,
        r
      )
    case Spec.Change.resolve{k, n, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Resources.Name,
        ~Spec.Content,
        ~Spec.Change,
        ~Id.codec(),
        ~Name.codec(),
        ~Content.codec(),
        a => b => c => Spec.Change.resolve{a, b, c},
        k,
        n,
        c,
        r
      )
    case Spec.Change.merge{v}:
      Codes.Code.one_read(~Ledgers.Id, ~Spec.Change, ~Id.codec(), a => Spec.Change.merge{a}, v, r)
    case Spec.Change.move{v}:
      Codes.Code.one_read(~Ledgers.Id, ~Spec.Change, ~Id.codec(), a => Spec.Change.move{a}, v, r)
    case Spec.Change.mark{m, n}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Spec.Change,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Spec.Change.mark{a, b},
        m,
        n,
        r
      )
    case Spec.Change.members{ms}:
      Codes.Code.one_read(
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => Spec.Change.members{a},
        ms,
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
    case Spec.Ask.start{os}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Ask,
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => Spec.Ask.start{a},
        os,
        r
      )
    case Spec.Ask.on{st, l, c}:
      Codes.Code.three_read(
        ~Ledgers.Id,
        ~Maybe<&2, Spec.Line>,
        ~Spec.Change,
        ~Spec.Ask,
        ~Id.codec(),
        ~Codes.Code.maybe.codec(~Spec.Line, ~Line.codec()),
        ~Change.codec(),
        a => b => c => Spec.Ask.on{a, b, c},
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
