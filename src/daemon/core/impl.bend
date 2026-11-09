import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/text.bend as Texts
import ../shared/tree.bend as Trees
import ./spec.bend as Spec

# The proofs of the core's laws.

# Codes
# -----

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
    case Spec.Line.Branch{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Line,
        ~Codes.Code.text.codec(),
        a => Spec.Line.Branch{a},
        n,
        r
      )
    case Spec.Line.Group{n}:
      Codes.Code.one_read(
        ~String,
        ~Spec.Line,
        ~Codes.Code.text.codec(),
        a => Spec.Line.Group{a},
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
    case Spec.Content.Bytes{b}:
      Codes.Code.one_read(
        ~Texts.Bytes(),
        ~Spec.Content,
        ~Codes.Code.words.codec(),
        a => Spec.Content.Bytes{a},
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
    case Spec.Change.Make{l, at, ms}:
      Codes.Code.three_read(
        ~Spec.Line,
        ~Maybe<&2, Ledgers.Id>,
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Line.codec(),
        ~Codes.Code.maybe.codec(~Ledgers.Id, ~Ledgers.Id.codec()),
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => b => c => Spec.Change.Make{a, b, c},
        l,
        at,
        ms,
        r
      )
    case Spec.Change.Own{os}:
      Codes.Code.one_read(
        ~List<&2, String>,
        ~Spec.Change,
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        a => Spec.Change.Own{a},
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
    case Spec.Change.Members{ms}:
      Codes.Code.one_read(
        ~List<&2, Spec.Member>,
        ~Spec.Change,
        ~Codes.Code.list.codec(~Spec.Member, ~Member.codec()),
        a => Spec.Change.Members{a},
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
        ~Maybe<&2, Spec.Line>,
        ~Spec.Change,
        ~Spec.Ask,
        ~Ledgers.Id.codec(),
        ~Codes.Code.maybe.codec(~Spec.Line, ~Line.codec()),
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
    Spec.Content.Bytes{x},
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
                Spec.Judge.content(s, Spec.Content.Bytes{x}),
                h,
                w => Spec.Judge.when(
                  same1,
                  h,
                  y => Spec.Work.take(
                    Spec.Work.set(
                      Spec.Work{s, h, []},
                      Spec.Key.res(name),
                      Spec.Res.code(Spec.Content.bytes(s, name, Spec.Content.Bytes{x}))
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
  +h1 => +ht => +ho => +hg => +hw => hb => hs => +hp => +hf =>
    +q = {
      Spec.Ask.On{
        r,
        Some{Spec.Line.Branch{b}},
        Spec.Change.Write{name, base, Spec.Content.Bytes{x}}
      }: Spec.Ask
    }
    +i = Spec.Envelope.of(e)
    +t = Spec.Envelope.time(e)
    +s1 = Spec.Node.taken(s, e, q)
    +c = Spec.Line.chain(r, Some{Spec.Line.Branch{b}})
    +root = Spec.Judge.root(
      s1,
      c,
      Ledgers.Line.head(~Spec.Ask, ~Spec.Ask.view, s1, c, ep, [n], last)
    )
    +ask1 = Spec.Node.ask(n, s, e, q)
    +ds = List.append(&2, List<&2, U32>, Trees.Put.nodes(p), [])
    +hv = Write.verdict(p, s1, name, base, x, root)(hb)(hs)(hp)
    +hst = Pair.fst(
      {
        Ledgers.State.status(
          ~Spec.Ask,
          ~Spec.Ask.view,
          ask1,
          i
        )
          == Ledgers.Status.Done{True{}}: Ledgers.Status
      },
      {
        Ledgers.State.decided(
          ~Spec.Ask,
          ~Spec.Ask.view,
          ask1,
          i
        )
          == Some{
            Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}
          }: Maybe<&2, Ledgers.Vote>
      }
        & {Ledgers.Data.holds(~Spec.Ask, ask1, ds) == True{}: Bool},
      Ledgers.State.ask_sole(
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
    )
    +hdc = Pair.fst(
      {
        Ledgers.State.decided(
          ~Spec.Ask,
          ~Spec.Ask.view,
          ask1,
          i
        )
          == Some{
            Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}
          }: Maybe<&2, Ledgers.Vote>
      },
      {Ledgers.Data.holds(~Spec.Ask, ask1, ds) == True{}: Bool},
      Pair.snd(
        {
          Ledgers.State.status(
            ~Spec.Ask,
            ~Spec.Ask.view,
            ask1,
            i
          )
            == Ledgers.Status.Done{True{}}: Ledgers.Status
        },
        {
          Ledgers.State.decided(
            ~Spec.Ask,
            ~Spec.Ask.view,
            ask1,
            i
          )
            == Some{
              Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}
            }: Maybe<&2, Ledgers.Vote>
        }
          & {Ledgers.Data.holds(~Spec.Ask, ask1, ds) == True{}: Bool},
        Ledgers.State.ask_sole(
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
      )
    )
    +hd = Pair.snd(
      {
        Ledgers.State.decided(
          ~Spec.Ask,
          ~Spec.Ask.view,
          ask1,
          i
        )
          == Some{
            Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}
          }: Maybe<&2, Ledgers.Vote>
      },
      {Ledgers.Data.holds(~Spec.Ask, ask1, ds) == True{}: Bool},
      Pair.snd(
        {
          Ledgers.State.status(
            ~Spec.Ask,
            ~Spec.Ask.view,
            ask1,
            i
          )
            == Ledgers.Status.Done{True{}}: Ledgers.Status
        },
        {
          Ledgers.State.decided(
            ~Spec.Ask,
            ~Spec.Ask.view,
            ask1,
            i
          )
            == Some{
              Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}
            }: Maybe<&2, Ledgers.Vote>
        }
          & {Ledgers.Data.holds(~Spec.Ask, ask1, ds) == True{}: Bool},
        Ledgers.State.ask_sole(
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
      )
    )
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
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, i), Ledgers.Status.Done{True{}}, hst):
          {Spec.Answer.of(ask1, i, _) == Spec.Answer.Written{i}: Spec.Answer}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Spec.Ask>>, Ledgers.State.asked(~Spec.Ask, ask1, i), Some{Ledgers.Asked{t, q}}, ha):
          {Spec.Answer.taken(ask1, i, _) == Spec.Answer.Written{i}: Spec.Answer}
        {==}), (
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, i), Ledgers.Status.Done{True{}}, hst):
          {Spec.Res.at(ask1, name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{i}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, ask1, i), Some{Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}}, hdc):
          {Spec.Res.get(ask1, Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Maybe.bind(&2, Ledgers.Vote, Maybe<&2, Hashes.Hash>, Maybe.bind(&2, Ledgers.Vote, Ledgers.Vote, _, y => Spec.Vote.taken(y)), y => Some{Ledgers.Vote.result_of(Some{y})}), g => g), name) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, ask1, Some{Trees.Put.root(p)}, Spec.Key.res(name)), Some{Spec.Res.code(Some{x})}, hgs): {Maybe.bind(&2, List<&2, U32>, Texts.Bytes(), _, ws => Spec.Res.read(ws)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        Res.read_code(x)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Kept reads
# ----------
# What a node reads of a version stays as its state grows.

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the root of the version v stays
def Root.kept(
  +s: Spec.State(),
  s2: Spec.State(),
  +v: Ledgers.Id,
  -r: Maybe<&2, Hashes.Hash>,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool}
) -> {
  Spec.Node.root(s, v) == Some{r}: Maybe<&2, Maybe<&2, Hashes.Hash>>
} -> {Spec.Node.root(s2, v) == Some{r}: Maybe<&2, Maybe<&2, Hashes.Hash>>}:
  Shared.Maybe.bind_kept(
    Ledgers.Vote,
    Maybe<&2, Hashes.Hash>,
    Spec.Version.vote(s, v),
    Spec.Version.vote(s2, v),
    x => Some{Ledgers.Vote.result_of(Some{x})},
    x => Some{Ledgers.Vote.result_of(Some{x})},
    r,
    a => Shared.Maybe.bind_kept(
      Ledgers.Vote,
      Ledgers.Vote,
      Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s, v),
      Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, v),
      x => Spec.Vote.taken(x),
      x => Spec.Vote.taken(x),
      a,
      b => Ledgers.State.decided_grows(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        ~Ask.laws(),
        ~Spec.Ask.view,
        s,
        s2,
        v,
        b
      )(gr),
      b => h => h
    ),
    a => h => h
  )

# the resource n of the tree h stays
def Res.kept(
  +s: Spec.State(),
  s2: Spec.State(),
  +h: Maybe<&2, Hashes.Hash>,
  +n: Resources.Name,
  -x: Texts.Bytes(),
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool}
) -> {
  Spec.Res.get(s, h, n) == Some{x}: Maybe<&2, Texts.Bytes()>
} -> {Spec.Res.get(s2, h, n) == Some{x}: Maybe<&2, Texts.Bytes()>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Texts.Bytes(),
    Spec.Node.get(s, h, Spec.Key.res(n)),
    Spec.Node.get(s2, h, Spec.Key.res(n)),
    ws => Spec.Res.read(ws),
    ws => Spec.Res.read(ws),
    x,
    w => Trees.Tree.get_grows(
      ~Spec.State(),
      ~Spec.Store.fetch,
      ~Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq),
      ~(
        a => b => k => y => Ledgers.State.data_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          a,
          b,
          k,
          y
        )
      ),
      s,
      s2,
      h,
      Spec.Key.res(n),
      w
    )(gr),
    w => e => e
  )

# a version stays a version, once its status is known (st)
def Version.kept.at(
  s: Spec.State(),
  s2: Spec.State(),
  v: Ledgers.Id,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  st: Ledgers.Status,
  e: {Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, v) == st: Ledgers.Status}
) -> {
  Shared.Maybe.is_eq(
    ~Bool,
    ~Shared.Bool.is_eq,
    Ledgers.Status.verdict(st),
    Some{True{}}
  )
    == True{}: Bool
} -> {Spec.Node.is_version(s2, v) == True{}: Bool}:
  match st:
    case Ledgers.Status.Done{True{}}:
      h =>
        %Equal.sym(
          Ledgers.Status,
          Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s2, v),
          Ledgers.Status.Done{True{}},
          Ledgers.State.status_grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            ~Spec.Ask.view,
            s,
            s2,
            v,
            True{}
          )(gr)(e)
        ): {
          Shared.Maybe.is_eq(
            ~Bool,
            ~Shared.Bool.is_eq,
            Ledgers.Status.verdict(_),
            Some{True{}}
          )
            == True{}: Bool
        }
        {==}
    case Ledgers.Status.Done{False{}}:
      h => Empty.absurd({Spec.Node.is_version(s2, v) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Ledgers.Status.Pending{}:
      h => Empty.absurd({Spec.Node.is_version(s2, v) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Ledgers.Status.Refused{}:
      h => Empty.absurd({Spec.Node.is_version(s2, v) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Ledgers.Status.NotSeen{}:
      h => Empty.absurd({Spec.Node.is_version(s2, v) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# the content of a version stays, once its root is known (m)
def Content.kept.root(
  +s: Spec.State(),
  +s2: Spec.State(),
  v: Ledgers.Id,
  +n: Resources.Name,
  -x: Texts.Bytes(),
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  m: Maybe<&2, Maybe<&2, Hashes.Hash>>,
  e: {Spec.Node.root(s, v) == m: Maybe<&2, Maybe<&2, Hashes.Hash>>}
) -> {
  Spec.Res.get(
    s,
    Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, m, g => g),
    n
  )
    == Some{x}: Maybe<&2, Texts.Bytes()>
} -> {Spec.Res.get(s2, Spec.Node.root_of(s2, Some{v}), n) == Some{x}: Maybe<&2, Texts.Bytes()>}:
  match m:
    case None{}:
      h => Empty.absurd(
        {Spec.Res.get(s2, Spec.Node.root_of(s2, Some{v}), n) == Some{x}: Maybe<&2, Texts.Bytes()>},
        Shared.Maybe.none_ne_some(
          Texts.Bytes(),
          x,
          Equal.trans(
            Maybe<&2, Texts.Bytes()>,
            None{},
            Spec.Res.get(s, None{}, n),
            Some{x},
            Equal.cong(
              Maybe<&2, List<&2, U32>>,
              Maybe<&2, Texts.Bytes()>,
              g => Maybe.bind(&2, List<&2, U32>, Texts.Bytes(), g, ws => Spec.Res.read(ws)),
              None{},
              Spec.Node.get(s, None{}, Spec.Key.res(n)),
              Equal.sym(
                Maybe<&2, List<&2, U32>>,
                Spec.Node.get(s, None{}, Spec.Key.res(n)),
                None{},
                Trees.Tree.get.go_empty(
                  ~Spec.State(),
                  ~Spec.Store.fetch,
                  s,
                  Trees.Tree.path(Spec.Key.res(n)),
                  Spec.Key.res(n)
                )
              )
            ),
            h
          )
        )
      )
    case Some{r}:
      h =>
        %Equal.sym(
          Maybe<&2, Maybe<&2, Hashes.Hash>>,
          Spec.Node.root(s2, v),
          Some{r},
          Root.kept(s, s2, v, r, gr)(e)
        ): {
          Spec.Res.get(
            s2,
            Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, _, g => g),
            n
          )
            == Some{x}: Maybe<&2, Texts.Bytes()>
        }
        Res.kept(s, s2, r, n, x, gr)(h)

# the content of a version stays, once whether it is a version is known (b)
def Content.kept.at(
  +s: Spec.State(),
  +s2: Spec.State(),
  n: Resources.Name,
  +v: Ledgers.Id,
  -x: Texts.Bytes(),
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  b: Bool,
  e: {Spec.Node.is_version(s, v) == b: Bool}
) -> {
  Spec.Res.at(
    s,
    n,
    Shared.Bool.when(Maybe<&2, Ledgers.Id>, b, u => Some{v}, u => None{})
  )
    == Some{x}: Maybe<&2, Texts.Bytes()>
} -> {Spec.Node.content(s2, n, Spec.Point.At{v}) == Some{x}: Maybe<&2, Texts.Bytes()>}:
  match b:
    case False{}:
      h => Empty.absurd(
        {Spec.Node.content(s2, n, Spec.Point.At{v}) == Some{x}: Maybe<&2, Texts.Bytes()>},
        Shared.Maybe.none_ne_some(Texts.Bytes(), x, h)
      )
    case True{}:
      h =>
        %Equal.sym(
          Bool,
          Spec.Node.is_version(s2, v),
          True{},
          Version.kept.at(
            s,
            s2,
            v,
            gr,
            Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, v),
            {==}
          )(e)
        ): {
          Spec.Res.at(
            s2,
            n,
            Shared.Bool.when(Maybe<&2, Ledgers.Id>, _, u => Some{v}, u => None{})
          )
            == Some{x}: Maybe<&2, Texts.Bytes()>
        }
        Content.kept.root(s, s2, v, n, x, gr, Spec.Node.root(s, v), {==})(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.Node.content_kept(s, s2, n, v, x):
  +gr => Content.kept.at(s, s2, n, v, x, gr, Spec.Node.is_version(s, v), {==})

# Answers
# -------

# the answer a is Written or Conflicted: a step took its request
def Answer.is_taken(a: Spec.Answer) -> Bool:
  match a:
    case Spec.Answer.Written{v}:
      True{}
    case Spec.Answer.Conflicted{k}:
      True{}
    case _:
      False{}

# the answer a is Stale
def Answer.is_stale(a: Spec.Answer) -> Bool:
  match a:
    case Spec.Answer.Stale{}:
      True{}
    case _:
      False{}

# the answer a is Refused
def Answer.is_refused(a: Spec.Answer) -> Bool:
  match a:
    case Spec.Answer.Refused{}:
      True{}
    case _:
      False{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# answers that f tells apart are not the same
def Answer.differ(
  ~f: Spec.Answer -> Bool,
  a: Spec.Answer,
  b: Spec.Answer,
  ha: {f(a) == False{}: Bool},
  hb: {f(b) == True{}: Bool},
  e: {a == b: Spec.Answer}
) -> Empty:
  Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      f(a),
      True{},
      Equal.sym(Bool, f(a), False{}, ha),
      Equal.trans(Bool, f(a), f(b), True{}, Equal.cong(Spec.Answer, Bool, x => f(x), a, b, e), hb)
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Written or Conflicted, by whether the merge still clashes (b)
def Answer.left_taken.at(
  b: Bool,
  i: Ledgers.Id,
  k: Ledgers.Id
) -> {
  Answer.is_taken(
    Shared.Bool.when(Spec.Answer, b, u => Spec.Answer.Written{i}, u => Spec.Answer.Conflicted{k})
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the answer to a taken request is Written or Conflicted
def Answer.taken_taken(
  s: Spec.State(),
  +i: Ledgers.Id,
  r: Maybe<&2, Ledgers.Asked<Spec.Ask>>
) -> {Answer.is_taken(Spec.Answer.taken(s, i, r)) == True{}: Bool}:
  match r:
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Merge{f}}}}:
      Answer.left_taken.at(List.is_empty(&2, Resources.Name, Spec.Node.conflict(s, i)), i, i)
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Resolve{+k, n, c}}}}:
      Answer.left_taken.at(List.is_empty(&2, Resources.Name, Spec.Node.conflict(s, k)), i, k)
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Make{a, b, c}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Own{a}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Write{a, b, c}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Move{a}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Mark{a, b}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.On{st, l, Spec.Change.Members{a}}}}:
      {==}
    case Some{Ledgers.Asked{t, Spec.Ask.Start{a}}}:
      {==}
    case None{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a Stale answer stays, once the status is known (st)
def Answer.stale_kept.at(
  +s: Spec.State(),
  s2: Spec.State(),
  +i: Ledgers.Id,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  st: Ledgers.Status,
  e: {Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, i) == st: Ledgers.Status}
) -> {
  Spec.Answer.of(s, i, st) == Spec.Answer.Stale{}: Spec.Answer
} -> {Spec.Node.answer(s2, i) == Spec.Answer.Stale{}: Spec.Answer}:
  match st:
    case Ledgers.Status.Done{False{}}:
      h =>
        %Equal.sym(
          Ledgers.Status,
          Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s2, i),
          Ledgers.Status.Done{False{}},
          Ledgers.State.status_grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            ~Spec.Ask.view,
            s,
            s2,
            i,
            False{}
          )(gr)(e)
        ): {Spec.Answer.of(s2, i, _) == Spec.Answer.Stale{}: Spec.Answer}
        {==}
    case Ledgers.Status.Done{True{}}:
      h => Empty.absurd(
        {Spec.Node.answer(s2, i) == Spec.Answer.Stale{}: Spec.Answer},
        Answer.differ(
          ~Answer.is_taken,
          Spec.Answer.Stale{},
          Spec.Answer.taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
          {==},
          Answer.taken_taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
          Equal.sym(
            Spec.Answer,
            Spec.Answer.taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
            Spec.Answer.Stale{},
            h
          )
        )
      )
    case Ledgers.Status.Pending{}:
      h => Empty.absurd(
        {Spec.Node.answer(s2, i) == Spec.Answer.Stale{}: Spec.Answer},
        Answer.differ(~Answer.is_stale, Spec.Answer.Pending{}, Spec.Answer.Stale{}, {==}, {==}, h)
      )
    case Ledgers.Status.Refused{}:
      h => Empty.absurd(
        {Spec.Node.answer(s2, i) == Spec.Answer.Stale{}: Spec.Answer},
        Answer.differ(~Answer.is_stale, Spec.Answer.Refused{}, Spec.Answer.Stale{}, {==}, {==}, h)
      )
    case Ledgers.Status.NotSeen{}:
      h => Empty.absurd(
        {Spec.Node.answer(s2, i) == Spec.Answer.Stale{}: Spec.Answer},
        Answer.differ(~Answer.is_stale, Spec.Answer.NotSeen{}, Spec.Answer.Stale{}, {==}, {==}, h)
      )

# a Refused answer stays after any sync, once the status is known (st)
def Answer.refused_kept.at(
  +s: Spec.State(),
  t: Spec.State(),
  +i: Ledgers.Id,
  st: Ledgers.Status,
  e: {Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, i) == st: Ledgers.Status}
) -> {
  Spec.Answer.of(s, i, st) == Spec.Answer.Refused{}: Spec.Answer
} -> {Spec.Node.answer(Spec.Node.join(s, t), i) == Spec.Answer.Refused{}: Spec.Answer}:
  match st:
    case Ledgers.Status.Refused{}:
      h =>
        %Equal.sym(
          Ledgers.Status,
          Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, Spec.Node.join(s, t), i),
          Ledgers.Status.Refused{},
          Ledgers.State.refused_kept(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, s, t, i)(e)
        ): {Spec.Answer.of(Spec.Node.join(s, t), i, _) == Spec.Answer.Refused{}: Spec.Answer}
        {==}
    case Ledgers.Status.Done{True{}}:
      h => Empty.absurd(
        {Spec.Node.answer(Spec.Node.join(s, t), i) == Spec.Answer.Refused{}: Spec.Answer},
        Answer.differ(
          ~Answer.is_taken,
          Spec.Answer.Refused{},
          Spec.Answer.taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
          {==},
          Answer.taken_taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
          Equal.sym(
            Spec.Answer,
            Spec.Answer.taken(s, i, Ledgers.State.asked(~Spec.Ask, s, i)),
            Spec.Answer.Refused{},
            h
          )
        )
      )
    case Ledgers.Status.Done{False{}}:
      h => Empty.absurd(
        {Spec.Node.answer(Spec.Node.join(s, t), i) == Spec.Answer.Refused{}: Spec.Answer},
        Answer.differ(~Answer.is_refused, Spec.Answer.Stale{}, Spec.Answer.Refused{}, {==}, {==}, h)
      )
    case Ledgers.Status.Pending{}:
      h => Empty.absurd(
        {Spec.Node.answer(Spec.Node.join(s, t), i) == Spec.Answer.Refused{}: Spec.Answer},
        Answer.differ(
          ~Answer.is_refused,
          Spec.Answer.Pending{},
          Spec.Answer.Refused{},
          {==},
          {==},
          h
        )
      )
    case Ledgers.Status.NotSeen{}:
      h => Empty.absurd(
        {Spec.Node.answer(Spec.Node.join(s, t), i) == Spec.Answer.Refused{}: Spec.Answer},
        Answer.differ(
          ~Answer.is_refused,
          Spec.Answer.NotSeen{},
          Spec.Answer.Refused{},
          {==},
          {==},
          h
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
def Spec.Node.version_kept(s, s2, v):
  +gr => Version.kept.at(s, s2, v, gr, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, v), {==})

def Spec.Node.stale_kept(s, s2, i):
  +gr => Answer.stale_kept.at(
    s,
    s2,
    i,
    gr,
    Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, i),
    {==}
  )

def Spec.Node.refused_kept(s, t, i):
  Answer.refused_kept.at(s, t, i, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, i), {==})

# Histories
# ---------

# Steps.taken_prefix after the first step x of both
def Steps.taken_prefix.at(
  x: Ledgers.Vote,
  xr: List<&2, Ledgers.Vote>,
  yr: List<&2, Ledgers.Vote>,
  ih: {
    List.take(
      &2,
      Ledgers.Id,
      Spec.Steps.taken(yr),
      List.length(&2, Ledgers.Id, Spec.Steps.taken(xr))
    )
      == Spec.Steps.taken(xr): List<&2, Ledgers.Id>
  }
) -> {
  List.take(
    &2,
    Ledgers.Id,
    Spec.Steps.taken(x <> yr),
    List.length(&2, Ledgers.Id, Spec.Steps.taken(x <> xr))
  )
    == Spec.Steps.taken(x <> xr): List<&2, Ledgers.Id>
}:
  match x:
    case Ledgers.Vote{i, True{}, w, h}:
      %ih: {
        i
          <> List.take(
            &2,
            Ledgers.Id,
            Spec.Steps.taken(yr),
            List.length(&2, Ledgers.Id, Spec.Steps.taken(xr))
          )
          == i
          <> _: List<&2, Ledgers.Id>
      }
      {==}
    case Ledgers.Vote{i, False{}, w, h}:
      ih

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the versions of steps that start longer steps start the versions of those
def Steps.taken_prefix(
  xs: List<&2, Ledgers.Vote>,
  ys: List<&2, Ledgers.Vote>
) -> {
  List.take(&2, Ledgers.Vote, ys, List.length(&2, Ledgers.Vote, xs)) == xs: List<&2, Ledgers.Vote>
} -> {
  List.take(
    &2,
    Ledgers.Id,
    Spec.Steps.taken(ys),
    List.length(&2, Ledgers.Id, Spec.Steps.taken(xs))
  )
    == Spec.Steps.taken(xs): List<&2, Ledgers.Id>
}:
  match xs ys:
    case Nil{} y:
      e => Shared.List.take_zero(Ledgers.Id, Spec.Steps.taken(y))
    case Con{x, xr} Nil{}:
      e => Empty.absurd(
        {
          List.take(
            &2,
            Ledgers.Id,
            [],
            List.length(&2, Ledgers.Id, Spec.Steps.taken(x <> xr))
          )
            == Spec.Steps.taken(x <> xr): List<&2, Ledgers.Id>
        },
        Shared.Bool.false_ne_true(
          Equal.cong(
            List<&2, Ledgers.Vote>,
            Bool,
            l => List.is_empty(&2, Ledgers.Vote, l),
            x <> xr,
            [],
            Equal.sym(List<&2, Ledgers.Vote>, [], x <> xr, e)
          )
        )
      )
    case Con{+x, +xr} Con{y, +yr}:
      +e =>
        %Equal.sym(
          Ledgers.Vote,
          y,
          x,
          Shared.List.head_eq(
            Ledgers.Vote,
            y,
            x,
            List.take(&2, Ledgers.Vote, yr, List.length(&2, Ledgers.Vote, xr)),
            xr,
            e
          )
        ): {
          List.take(
            &2,
            Ledgers.Id,
            Spec.Steps.taken(_ <> yr),
            List.length(&2, Ledgers.Id, Spec.Steps.taken(x <> xr))
          )
            == Spec.Steps.taken(x <> xr): List<&2, Ledgers.Id>
        }
        Steps.taken_prefix.at(
          x,
          xr,
          yr,
          Steps.taken_prefix(
            xr,
            yr
          )(
            Shared.List.tail_eq(
              Ledgers.Vote,
              y,
              x,
              List.take(&2, Ledgers.Vote, yr, List.length(&2, Ledgers.Vote, xr)),
              xr,
              e
            )
          )
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a listing that starts with xs, once the listing m of the grown state is known
def Steps.of_bind(
  xs: List<&2, Ledgers.Vote>,
  m: Maybe<&2, List<&2, Ledgers.Vote>>
) -> {
  Maybe.bind(
    &2,
    List<&2, Ledgers.Vote>,
    List<&2, Ledgers.Vote>,
    m,
    ys => Some{List.take(&2, Ledgers.Vote, ys, List.length(&2, Ledgers.Vote, xs))}
  )
    == Some{xs}: Maybe<&2, List<&2, Ledgers.Vote>>
} -> {
  List.take(
    &2,
    Ledgers.Vote,
    Maybe.default(&2, List<&2, Ledgers.Vote>, m, []),
    List.length(&2, Ledgers.Vote, xs)
  )
    == xs: List<&2, Ledgers.Vote>
}:
  match m:
    case None{}:
      h => Empty.absurd(
        {
          List.take(
            &2,
            Ledgers.Vote,
            [],
            List.length(&2, Ledgers.Vote, xs)
          )
            == xs: List<&2, Ledgers.Vote>
        },
        Shared.Maybe.none_ne_some(List<&2, Ledgers.Vote>, xs, h)
      )
    case Some{ys}:
      h => Shared.Maybe.some_inj(
        List<&2, Ledgers.Vote>,
        List.take(&2, Ledgers.Vote, ys, List.length(&2, Ledgers.Vote, xs)),
        xs,
        h
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the versions grow at their end, once the listing m of the line is known
def Versions.grow.at(
  s: Spec.State(),
  +s2: Spec.State(),
  +c: Ledgers.Chain,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  m: Maybe<&2, List<&2, Ledgers.Vote>>,
  e: {Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s, c) == m: Maybe<&2, List<&2, Ledgers.Vote>>}
) -> {
  List.take(
    &2,
    Ledgers.Id,
    Spec.Steps.taken(
      Maybe.default(
        &2,
        List<&2, Ledgers.Vote>,
        Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c),
        []
      )
    ),
    List.length(&2, Ledgers.Id, Spec.Steps.taken(Maybe.default(&2, List<&2, Ledgers.Vote>, m, [])))
  )
    == Spec.Steps.taken(Maybe.default(&2, List<&2, Ledgers.Vote>, m, [])): List<&2, Ledgers.Id>
}:
  match m:
    case None{}:
      Shared.List.take_zero(
        Ledgers.Id,
        Spec.Steps.taken(
          Maybe.default(
            &2,
            List<&2, Ledgers.Vote>,
            Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c),
            []
          )
        )
      )
    case Some{+xs}:
      Steps.taken_prefix(
        xs,
        Maybe.default(
          &2,
          List<&2, Ledgers.Vote>,
          Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c),
          []
        )
      )(
        Steps.of_bind(
          xs,
          Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c)
        )(
          Ledgers.Line.steps_grow(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            ~Spec.Ask.view,
            s,
            s2,
            c,
            xs
          )(gr)(e)
        )
      )

def Spec.Node.versions_grow(s, s2, r, b):
  +gr => Versions.grow.at(
    s,
    s2,
    Spec.Line.chain(r, Some{Spec.Line.Branch{b}}),
    gr,
    Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s, Spec.Line.chain(r, Some{Spec.Line.Branch{b}})),
    {==}
  )
