import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/trie.bend as Tries
import ../shared/shared/text.bend as Texts
import ./spec.bend as Spec

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

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners take a write whose base is ready and whose resource did not change
def Write.takes(
  +s: Spec.State(),
  r: Ledgers.Id,
  b: String,
  +name: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Texts.Bytes(),
  xs: List<&2, Ledgers.Step<Spec.Ask>>
) -> {
  Spec.Judge.ready_maybe(s, base) == Some{True{}}: Maybe<&2, Bool>
} -> {
  Spec.Bytes.same(
    Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
    Spec.Res.of(s, name, base)
  )
    == True{}: Bool
} -> {
  Spec.Node.judge(
    s,
    Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}},
    xs
  )
    == Some{True{}}: Maybe<&2, Bool>
}:
  hr => hc =>
    +same1 = Spec.Bytes.same(
      Spec.Res.of(s, name, Spec.Ids.last(Spec.Steps.taken(xs))),
      Spec.Res.of(s, name, base)
    )
    %Equal.sym(Maybe<&2, Bool>, Spec.Judge.ready_maybe(s, base), Some{True{}}, hr):
      {
        Spec.Judge.then(
          _,
          u => Spec.Judge.then(Spec.Judge.content(s, Spec.Content.bytes{x}), w => Some{same1})
        )
          == Some{True{}}: Maybe<&2, Bool>
      }
    %Equal.sym(Bool, same1, True{}, hc):
      {Some{_} == Some{True{}}: Maybe<&2, Bool>}
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.Node.write_written(n, s, e, r, b, name, base, x, h):
  +h1 => ht => hg => hv => hr => hc =>
    +ask1 = Spec.Node.ask(
      n,
      s,
      e,
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }
    )
    +taken1 = Spec.Node.taken(
      s,
      e,
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }
    )
    +hs = Ledgers.State.ask_decides(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      },
      Spec.Line.chain(r, Some{Spec.Line.branch{b}}),
      None{},
      None{},
      h,
      True{}
    )(
      h1
    )(
      {==}
    )(
      ht
    )(
      hg
    )(
      hv
    )(
      Write.takes(
        taken1,
        r,
        b,
        name,
        base,
        x,
        Spec.Node.steps(taken1, r, Some{Spec.Line.branch{b}})
      )(hr)(hc)
    )
    +ha = Ledgers.State.ask_holds(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }
    )(h1)
    ((
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Answer.of(ask1, Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, ask1, Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Answer.taken(ask1, Spec.Envelope.of(e), _) == Spec.Answer.written{Spec.Envelope.of(e)}: Spec.Answer}
        {==}), (
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, Spec.Envelope.of(e)), Ledgers.Status.done{True{}}, hs):
          {Spec.Res.of(ask1, name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{Spec.Envelope.of(e)}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, ask1, Spec.Envelope.of(e)), Some{Ledgers.Asked{Spec.Envelope.time(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}}, ha):
          {Spec.Res.go(Spec.State.fuel(ask1), ask1, Spec.Src.at(Spec.Envelope.of(e), _), name) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Bool, Resources.Name.is_eq(name, name), True{}, Resources.Name.is_eq_refl(name)):
          {Shared.Bool.when(Maybe<&2, Texts.Bytes()>, _, u => Some{x}, u => Spec.Res.go(Nat.double(Tries.Trie.size(Ledgers.Cell<Ledgers.Entry<Spec.Ask>>, ask1)), ask1, Spec.Src.before{Spec.Envelope.of(e), Spec.Ask.on{r, Some{Spec.Line.branch{b}}, Spec.Change.write{name, base, Spec.Content.bytes{x}}}}, name)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        {==}))
