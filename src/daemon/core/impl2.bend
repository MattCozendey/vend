import Base
import ../../shared.bend as Shared
import ../shared/ledger2.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
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

# Writes
# ------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the value of a resource that holds the bytes x reads back as x
def Res.read_code(
  x: Texts.Bytes()
) -> {Spec.Res.read(Spec.Res.code(Some{x})) == Some{x}: Maybe<&2, Texts.Bytes()>}:
  %Equal.sym(
    Maybe<&2, Codes.Read<Maybe<&2, Texts.Bytes()>>>,
    Codes.Code.maybe.read(~Texts.Bytes(), ~Codes.Code.words.read, Spec.Res.code(Some{x})),
    Some{Codes.Read{Some{x}, []}},
    Codes.Code.maybe_read(
      ~Texts.Bytes(),
      ~Codes.Code.words,
      ~Codes.Code.words.read,
      Codes.Codec.laws(Texts.Bytes(), Codes.Code.words.codec()),
      Some{x},
      []
    )
  ): {Spec.Res.of.read(_) == Some{x}: Maybe<&2, Texts.Bytes()>}
  {==}

# a node's trees hold the words ds exactly when its ledger does
def Holds.same(
  ds: List<&2, List<&2, U32>>,
  s: Spec.State()
) -> {
  Trees.Tree.holds(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    ds
  )
    == Ledgers.Data.holds(~Spec.Ask, s, ds): Bool
}:
  match ds:
    case Nil{}:
      {==}
    case Con{ws, rest}:
      %Equal.sym(
        Bool,
        Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s, rest),
        Ledgers.Data.holds(~Spec.Ask, s, rest),
        Holds.same(rest, s)
      ):
        {
          List.all.if(
            u => _,
            Trees.Tree.has(~Spec.State(), ~Spec.Store.fetch, s, ws)
          )
            == List.all.if(
              u => Ledgers.Data.holds(~Spec.Ask, s, rest),
              Ledgers.Data.has(~Spec.Ask, s, ws)
            ): Bool
        }
      {==}

# the trees of a node hold the nodes ns when its ledger holds ns, then nothing
def Holds.of(
  +ns: List<&2, List<&2, U32>>,
  s: Spec.State()
) -> {
  Ledgers.Data.holds(~Spec.Ask, s, List.append(&2, List<&2, U32>, ns, [])) == True{}: Bool
} -> {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s, ns) == True{}: Bool}:
  hd =>
    +ds = List.append(&2, List<&2, U32>, ns, [])
    %Shared.List.append_nil(
      List<&2, U32>,
      ns
    ): {Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s, _) == True{}: Bool}
    %Equal.sym(
      Bool,
      Trees.Tree.holds(~Spec.State(), ~Spec.Store.fetch, s, ds),
      Ledgers.Data.holds(~Spec.Ask, s, ds),
      Holds.same(ds, s)
    ): {_ == True{}: Bool}
    hd

# the owners take a write whose base is ready and whose resource did not change
# since it, with the new subtree p
def Write.verdict(
  p: Trees.Put,
  +s: Spec.State(),
  +name: Resources.Name,
  base: Maybe<&2, Ledgers.Id>,
  x: Texts.Bytes(),
  h: Maybe<&2, Hashes.Hash>
) -> {
  Spec.Judge.ready_maybe(s, base) == Some{True{}}: Maybe<&2, Bool>
} -> {
  Spec.Bytes.same(
    Spec.Res.get(s, h, name),
    Spec.Res.get(s, Spec.Node.root_of(s, base), name)
  )
    == True{}: Bool
} -> {
  Trees.Tree.set(
    ~Spec.State(),
    ~Spec.Store.fetch,
    s,
    h,
    Spec.Key.res(name),
    Spec.Res.code(Some{x})
  )
    == Some{p}: Maybe<&2, Trees.Put>
} -> {
  Spec.Judge.write(
    s,
    name,
    base,
    Spec.Content.bytes{x},
    h
  )
    == Some{
      Ledgers.Verdict{
        True{},
        Some{Trees.Put.root(p)},
        List.append(&2, List<&2, U32>, Trees.Put.nodes(p), [])
      }
    }: Maybe<&2, Ledgers.Verdict>
}:
  match p:
    case Trees.Put{h2, ws}:
      hb => hs => hp =>
        +v = {
          Some{
            Ledgers.Verdict{True{}, Some{h2}, List.append(&2, List<&2, U32>, ws, [])}
          }: Maybe<&2, Ledgers.Verdict>
        }
        +same1 = Spec.Bytes.same(
          Spec.Res.get(s, h, name),
          Spec.Res.get(s, Spec.Node.root_of(s, base), name)
        )
        %Equal.sym(Maybe<&2, Bool>, Spec.Judge.ready_maybe(s, base), Some{True{}}, hb):
          {
            Spec.Judge.then(
              _,
              h,
              u => Spec.Judge.then(
                Spec.Judge.content(s, Spec.Content.bytes{x}),
                h,
                w => Spec.Judge.when(
                  same1,
                  h,
                  y => Spec.Work.take(
                    Spec.Work.set(
                      Spec.Work{s, h, []},
                      Spec.Key.res(name),
                      Spec.Res.code(Spec.Content.bytes(s, name, Spec.Content.bytes{x}))
                    )
                  )
                )
              )
            )
              == v: Maybe<&2, Ledgers.Verdict>
          }
        %Equal.sym(Bool, same1, True{}, hs):
          {
            Spec.Judge.when(
              _,
              h,
              y => Spec.Work.take(
                Spec.Work.set(Spec.Work{s, h, []}, Spec.Key.res(name), Spec.Res.code(Some{x}))
              )
            )
              == v: Maybe<&2, Ledgers.Verdict>
          }
        %Equal.sym(
          Maybe<&2, Trees.Put>,
          Trees.Tree.set(
            ~Spec.State(),
            ~Spec.Store.fetch,
            s,
            h,
            Spec.Key.res(name),
            Spec.Res.code(Some{x})
          ),
          Some{Trees.Put{h2, ws}},
          hp
        ): {Spec.Work.take(Spec.Work.of(s, [], _)) == v: Maybe<&2, Ledgers.Verdict>}
        {==}

def Spec.Node.write_written(n, s, e, r, b, name, base, x, ep, h, last, p):
  +h1 => +ht => +ho => +hg => +hw => hb => hs => +hp => hf =>
    +q = {
      Spec.Ask.on{
        r,
        Some{Spec.Line.branch{b}},
        Spec.Change.write{name, base, Spec.Content.bytes{x}}
      }: Spec.Ask
    }
    +i = Spec.Envelope.of(e)
    +t = Spec.Envelope.time(e)
    +s1 = Spec.Node.taken(s, e, q)
    +c = Spec.Line.chain(r, Some{Spec.Line.branch{b}})
    +root = Spec.Judge.root(
      s1,
      c,
      Ledgers.Line.head(~Spec.Ask, ~Spec.Ask.view, s1, c, ep, [n], last)
    )
    +ask1 = Spec.Node.ask(n, s, e, q)
    +ds = List.append(&2, List<&2, U32>, Trees.Put.nodes(p), [])
    +hv = Write.verdict(p, s1, name, base, x, root)(hb)(hs)(hp)
    +hst = Ledgers.State.ask_decides(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      i,
      t,
      q,
      c,
      None{},
      None{},
      ep,
      h,
      last,
      True{},
      Some{Trees.Put.root(p)},
      ds
    )(h1)({==})(ht)(ho)(hg)(hw)(hv)
    +hdc = Ledgers.State.ask_decided(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      i,
      t,
      q,
      c,
      None{},
      None{},
      ep,
      h,
      last,
      True{},
      Some{Trees.Put.root(p)},
      ds
    )(h1)({==})(ht)(ho)(hg)(hw)(hv)
    +hd = Ledgers.State.ask_data(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      i,
      t,
      q,
      c,
      None{},
      None{},
      ep,
      h,
      last,
      True{},
      Some{Trees.Put.root(p)},
      ds
    )(h1)({==})(ht)(ho)(hg)(hw)(hv)(hf)
    +ha = Ledgers.State.ask_holds(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Ask.laws(),
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      s,
      i,
      t,
      q
    )(h1)
    +hgs = Trees.Tree.get_set(
      ~Spec.State(),
      ~Spec.Store.fetch,
      s1,
      ask1,
      root,
      Spec.Key.res(name),
      Spec.Res.code(Some{x}),
      p
    )(hp)(Holds.of(Trees.Put.nodes(p), ask1)(hd))
    ((
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, i), Ledgers.Status.done{True{}}, hst):
          {Spec.Answer.of(ask1, i, _) == Spec.Answer.written{i}: Spec.Answer}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, ask1, i), Some{Ledgers.Asked{t, q}}, ha):
          {Spec.Answer.taken(ask1, i, _) == Spec.Answer.written{i}: Spec.Answer}
        {==}), (
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, i), Ledgers.Status.done{True{}}, hst):
          {Spec.Res.at(ask1, name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{i}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, ask1, i), Some{Ledgers.Vote{i, True{}, Ledgers.View.on{c, None{}, None{}}, Some{Trees.Put.root(p)}}}, hdc):
          {Spec.Res.get(ask1, Shared.Maybe.then(Maybe<&2, Hashes.Hash>, Hashes.Hash, Shared.Maybe.then(Ledgers.Vote, Maybe<&2, Hashes.Hash>, Shared.Maybe.then(Ledgers.Vote, Ledgers.Vote, _, y => Spec.Vote.taken(y)), y => Some{Ledgers.Vote.result_of(Some{y})}), g => g), name) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, ask1, Some{Trees.Put.root(p)}, Spec.Key.res(name)), Some{Spec.Res.code(Some{x})}, hgs): {Shared.Maybe.then(List<&2, U32>, Texts.Bytes(), _, ws => Spec.Res.read(ws)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        Res.read_code(x)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
