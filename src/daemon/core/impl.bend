import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/resources.bend as Resources
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

def Spec.Ask.same():
  Ask.laws()

# Slots
# -----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a slot that keeps a and holds nothing: a holds nothing
def Cell.keeps_none(
  a: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    a,
    None{}
  )
    == True{}: Bool
} -> {a == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}:
  match a:
    case None{}:
      h => {==}
    case Some{Cells.One{x}}:
      h => Empty.absurd(
        {Some{Cells.One{x}} == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Cells.Many{}}:
      h => Empty.absurd(
        {Some{Cells.Many{}} == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )

# a slot that keeps a contradiction holds it
def Cell.keeps_many(
  b: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    Some{Cells.Many{}},
    b
  )
    == True{}: Bool
} -> {b == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}:
  match b:
    case None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Cells.One{x}}:
      h => Empty.absurd(
        {Some{Cells.One{x}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )
    case Some{Cells.Many{}}:
      h => {==}

# what a state that grows from s holds at the slot k keeps what s holds there
def Slot.kept(
  +s: Spec.State(),
  +s2: Spec.State(),
  +k: List<&2, Bool>,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool}
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    Ledgers.State.get(~Spec.Ask, s, k),
    Ledgers.State.get(~Spec.Ask, s2, k)
  )
    == True{}: Bool
}:
  Tries.Trie.keeps_get(
    ~Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    ~Cells.Cell.keeps(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
    ~Cells.Cell.none_kept(~Ledgers.Entry<Spec.Ask>, ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq)),
    s,
    s2,
    k
  )(gr)

# the entry x of the slot k stays as the state grows
def Slot.one_kept(
  +s: Spec.State(),
  +s2: Spec.State(),
  +k: List<&2, Bool>,
  +x: Ledgers.Entry<Spec.Ask>,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  e: {
    Ledgers.State.get(~Spec.Ask, s, k) == Some{Cells.One{x}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Ledgers.State.get(~Spec.Ask, s2, k) == Some{Cells.One{x}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
}:
  Cells.Cell.keeps_value(
    ~Ledgers.Entry<Spec.Ask>,
    ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
    ~Ledgers.Entry.laws(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws()),
    x,
    Ledgers.State.get(~Spec.Ask, s2, k)
  )(
    %e: {
      Cells.Cell.keeps(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
        _,
        Ledgers.State.get(~Spec.Ask, s2, k)
      )
        == True{}: Bool
    }
    Slot.kept(s, s2, k, gr)
  )

# a contradiction in the slot k stays as the state grows
def Slot.many_kept(
  +s: Spec.State(),
  +s2: Spec.State(),
  +k: List<&2, Bool>,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  e: {
    Ledgers.State.get(~Spec.Ask, s, k) == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Ledgers.State.get(~Spec.Ask, s2, k) == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
}:
  Cell.keeps_many(Ledgers.State.get(~Spec.Ask, s2, k))(
    %e: {
      Cells.Cell.keeps(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
        _,
        Ledgers.State.get(~Spec.Ask, s2, k)
      )
        == True{}: Bool
    }
    Slot.kept(s, s2, k, gr)
  )

# a slot that is empty once the state grew was empty
def Slot.none_before(
  +s: Spec.State(),
  +s2: Spec.State(),
  +k: List<&2, Bool>,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  e: {Ledgers.State.get(~Spec.Ask, s2, k) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}
) -> {Ledgers.State.get(~Spec.Ask, s, k) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>}:
  Cell.keeps_none(Ledgers.State.get(~Spec.Ask, s, k))(
    %e: {
      Cells.Cell.keeps(
        ~Ledgers.Entry<Spec.Ask>,
        ~Ledgers.Entry.is_eq(~Spec.Ask, ~Spec.Ask.is_eq),
        Ledgers.State.get(~Spec.Ask, s, k),
        _
      )
        == True{}: Bool
    }
    Slot.kept(s, s2, k, gr)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# the facts of the last step of the line that q changes grow the state
def Land.grows(
  +s: Spec.State(),
  q: Spec.Ask
) -> {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, Spec.Node.land(s, q)) == True{}: Bool}:
  match q:
    case Spec.Ask.Start{os}:
      Ledgers.State.grows_refl(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), s)
    case Spec.Ask.On{r, l, c}:
      Ledgers.Land.of.grows(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        ~Ask.laws(),
        s,
        Ledgers.Line.tip(~Spec.Ask, ~Spec.Ask.view, s, Spec.Line.chain(r, l))
      )

# a node that does not hold a request's ID takes the request in
def Ask.fresh(
  n: String,
  s: Spec.State(),
  e: Spec.Envelope,
  q: Spec.Ask
) -> {
  Ledgers.State.get(
    ~Spec.Ask,
    s,
    Ledgers.Slot.ask(Spec.Envelope.of(e))
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
} -> {
  Spec.Node.ask(
    n,
    s,
    e,
    q
  )
    == Ledgers.State.ask(
      ~Spec.Ask,
      ~Spec.Ask.is_eq,
      ~Spec.Ask.view,
      ~Spec.Node.judge,
      n,
      Spec.Node.land(s, q),
      Spec.Envelope.of(e),
      Spec.Envelope.time(e),
      q
    ): Spec.State()
}:
  h =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
      Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(Spec.Envelope.of(e))),
      None{},
      h
    ): {
      Spec.Node.ask.at(
        n,
        s,
        e,
        q,
        _
      )
        == Ledgers.State.ask(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Spec.Ask.view,
          ~Spec.Node.judge,
          n,
          Spec.Node.land(s, q),
          Spec.Envelope.of(e),
          Spec.Envelope.time(e),
          q
        ): Spec.State()
    }
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
    +s0 = Spec.Node.land(s, q)
    +s1 = Spec.Node.taken(s, e, q)
    +c = Spec.Line.chain(r, Some{Spec.Line.Branch{b}})
    +root = Spec.Judge.root(
      s1,
      c,
      Ledgers.Line.head(~Spec.Ask, ~Spec.Ask.view, s1, c, ep, [n], last)
    )
    +ask1 = Ledgers.State.ask(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.judge, n, s0, i, t, q)
    +hfr = Equal.sym(
      Spec.State(),
      Spec.Node.ask(n, s, e, q),
      ask1,
      Ask.fresh(n, s, e, q)(Slot.none_before(s, s0, Ledgers.Slot.ask(i), Land.grows(s, q), h1))
    )
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
        s0,
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
          s0,
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
          s0,
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
      s0,
      i,
      t,
      q
    )(h1)
    +hcell = Slot.one_kept(
      s1,
      ask1,
      Ledgers.Slot.ask(i),
      Ledgers.Entry.Ask{i, t, q},
      (
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, Ledgers.State.get(~Spec.Ask, s0, Ledgers.Slot.ask(i)), None{}, h1):
          {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s1, Ledgers.State.ask.fresh(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.judge, n, s0, i, t, q, _)) == True{}: Bool}
        Ledgers.Vote.ask.grows(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), ~Spec.Ask.view, ~Spec.Node.judge, n, s1, i, q, Spec.Ask.view(q))
      ),
      Ledgers.State.put_get(~Spec.Ask, ~Spec.Ask.is_eq, s0, Ledgers.Slot.ask(i), Ledgers.Entry.Ask{i, t, q})(h1)
    )
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
        %hfr: {Spec.Node.answer(_, e, q) == Some{Spec.Answer.Written{i}}: Maybe<&2, Spec.Answer>}
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>, Ledgers.State.get(~Spec.Ask, ask1, Ledgers.Slot.ask(i)), Some{Cells.One{Ledgers.Entry.Ask{i, t, q}}}, hcell):
          {Spec.Answer.held(ask1, i, q, _) == Some{Spec.Answer.Written{i}}: Maybe<&2, Spec.Answer>}
        %Equal.sym(Bool, Spec.Ask.is_eq(q, q), True{}, Shared.Eq.refl(~Spec.Ask, ~Spec.Ask.is_eq, Ask.laws(), q)):
          {Some{Shared.Bool.when(Spec.Answer, _, u => Spec.Answer.of(ask1, i, q, Ledgers.Status.of.view(Spec.Ask.view(q), Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, ask1, i))), u => Spec.Answer.Refused{})} == Some{Spec.Answer.Written{i}}: Maybe<&2, Spec.Answer>}
        %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, ask1, i), Some{Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}}, hdc):
          {Some{Spec.Answer.of(ask1, i, q, Ledgers.Status.of.view(Spec.Ask.view(q), _))} == Some{Spec.Answer.Written{i}}: Maybe<&2, Spec.Answer>}
        {==}), (
        %hfr: {Spec.Node.content(_, name, Spec.Point.At{i}) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Ledgers.Status, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, ask1, i), Ledgers.Status.Done{True{}}, hst):
          {Spec.Res.at(ask1, name, Shared.Bool.when(Maybe<&2, Ledgers.Id>, Shared.Maybe.is_eq(~Bool, ~Shared.Bool.is_eq, Ledgers.Status.verdict(_), Some{True{}}), u => Some{i}, u => None{})) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, ask1, i), Some{Ledgers.Vote{i, True{}, Ledgers.View.On{c, None{}, None{}}, Some{Trees.Put.root(p)}}}, hdc):
          {Spec.Res.get(ask1, Maybe.bind(&2, Maybe<&2, Hashes.Hash>, Hashes.Hash, Maybe.bind(&2, Ledgers.Vote, Maybe<&2, Hashes.Hash>, Maybe.bind(&2, Ledgers.Vote, Ledgers.Vote, _, y => Spec.Vote.taken(y)), y => Some{Ledgers.Vote.result_of(Some{y})}), g => g), name) == Some{x}: Maybe<&2, Texts.Bytes()>}
        %Equal.sym(Maybe<&2, List<&2, U32>>, Trees.Tree.get(~Spec.State(), ~Spec.Store.fetch, ask1, Some{Trees.Put.root(p)}, Spec.Key.res(name)), Some{Spec.Res.code(Some{x})}, hgs): {Maybe.bind(&2, List<&2, U32>, Texts.Bytes(), _, ws => Spec.Res.read(ws)) == Some{x}: Maybe<&2, Texts.Bytes()>}
        Res.read_code(x)))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Asks
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Node.ask_grows once the cell m of the request's ID is known
def Ask.grows.at(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, Spec.Node.ask.at(n, s, e, q, m)) == True{}: Bool}:
  match m:
    case Some{x}:
      Ledgers.State.grows_refl(~Spec.Ask, ~Spec.Ask.is_eq, ~Ask.laws(), s)
    case None{}:
      +s0 = Spec.Node.land(s, q)
      Ledgers.State.grows_trans(
        ~Spec.Ask,
        ~Spec.Ask.is_eq,
        ~Ask.laws(),
        s,
        s0,
        Ledgers.State.ask(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Spec.Ask.view,
          ~Spec.Node.judge,
          n,
          s0,
          Spec.Envelope.of(e),
          Spec.Envelope.time(e),
          q
        )
      )(
        Land.grows(s, q)
      )(
        Ledgers.State.ask_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          ~Spec.Ask.view,
          ~Spec.Node.judge,
          n,
          s0,
          Spec.Envelope.of(e),
          Spec.Envelope.time(e),
          q
        )
      )

def Spec.Node.ask_grows(n, s, e, q):
  Ask.grows.at(n, s, e, q, Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(Spec.Envelope.of(e))))

# a ledger that took in the request i holds its slot, once the cell m of the
# slot before is known
def Ask.held.fresh(
  +n: String,
  +s: Spec.State(),
  +i: Ledgers.Id,
  +t: String,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  +em: {
    Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(i)) == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(
      ~Spec.Ask,
      Ledgers.State.ask.fresh(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.judge, n, s, i, t, q, m),
      Ledgers.Slot.ask(i)
    )
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
        Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(i)),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
      {==}
    case None{}:
      +s1 = Ledgers.State.put(~Spec.Ask, ~Spec.Ask.is_eq, s, Ledgers.Slot.ask(i), Ledgers.Entry.Ask{i, t, q})
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
        Ledgers.State.get(
          ~Spec.Ask,
          Ledgers.Vote.ask(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.judge, n, s1, i, q, Spec.Ask.view(q)),
          Ledgers.Slot.ask(i)
        ),
        Some{Cells.One{Ledgers.Entry.Ask{i, t, q}}},
        Slot.one_kept(
          s1,
          Ledgers.Vote.ask(~Spec.Ask, ~Spec.Ask.is_eq, ~Spec.Ask.view, ~Spec.Node.judge, n, s1, i, q, Spec.Ask.view(q)),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, t, q},
          Ledgers.Vote.ask.grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            ~Spec.Ask.view,
            ~Spec.Node.judge,
            n,
            s1,
            i,
            q,
            Spec.Ask.view(q)
          ),
          Ledgers.State.put_get(~Spec.Ask, ~Spec.Ask.is_eq, s, Ledgers.Slot.ask(i), Ledgers.Entry.Ask{i, t, q})(em)
        )
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
      {==}

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  em: {
    Ledgers.State.get(
      ~Spec.Ask,
      s,
      Ledgers.Slot.ask(Spec.Envelope.of(e))
    )
      == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(~Spec.Ask, Spec.Node.ask.at(n, s, e, q, m), Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
        Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(Spec.Envelope.of(e))),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, _) == True{}: Bool}
      {==}
    case None{}:
      +s0 = Spec.Node.land(s, q)
      Ask.held.fresh(
        n,
        s0,
        Spec.Envelope.of(e),
        Spec.Envelope.time(e),
        q,
        Ledgers.State.get(~Spec.Ask, s0, Ledgers.Slot.ask(Spec.Envelope.of(e))),
        {==}
      )

# a node that took in the request of e holds its slot
def Ask.held(
  +n: String,
  +s: Spec.State(),
  +e: Spec.Envelope,
  +q: Spec.Ask
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Spec.Ask>>,
    Ledgers.State.get(~Spec.Ask, Spec.Node.ask(n, s, e, q), Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )
    == True{}: Bool
}:
  Ask.held.at(n, s, e, q, Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(Spec.Envelope.of(e))), {==})

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  m: String,
  s: Spec.State(),
  e: Spec.Envelope,
  q: Spec.Ask,
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, c) == True{}: Bool
} -> {Spec.Node.ask.at(m, s, e, q, c) == s: Spec.State()}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Spec.Node.ask.at(m, s, e, q, None{}) == s: Spec.State()},
        Shared.Bool.false_ne_true(h)
      )

def Spec.Node.ask_once(n, m, s, e, q, e2, q2):
  +h =>
    +a = Spec.Node.ask(n, s, e, q)
    Ask.once.at(
      m,
      a,
      e2,
      q2,
      Ledgers.State.get(~Spec.Ask, a, Ledgers.Slot.ask(Spec.Envelope.of(e2)))
    )(
      %Equal.sym(Ledgers.Id, Spec.Envelope.of(e2), Spec.Envelope.of(e), h): {
        Maybe.is_some(
          &2,
          Cells.Cell<Ledgers.Entry<Spec.Ask>>,
          Ledgers.State.get(~Spec.Ask, a, Ledgers.Slot.ask(_))
        )
          == True{}: Bool
      }
      Ask.held(n, s, e, q)
    )

# a slot that holds a cell has an answer
def Held.some(
  s: Spec.State(),
  i: Ledgers.Id,
  q: Spec.Ask,
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>, c) == True{}: Bool
} -> {Maybe.is_some(&2, Spec.Answer, Spec.Answer.held(s, i, q, c)) == True{}: Bool}:
  match c:
    case None{}:
      h => h
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, q2}}}:
      h => {==}
    case Some{Cells.One{Ledgers.Entry.Vote{v}}}:
      h => {==}
    case Some{Cells.One{Ledgers.Entry.At{w}}}:
      h => {==}
    case Some{Cells.One{Ledgers.Entry.Data{ws}}}:
      h => {==}
    case Some{Cells.Many{}}:
      h => {==}

def Spec.Node.ask_seen(n, s, e, q):
  +a = Spec.Node.ask(n, s, e, q)
  Held.some(
    a,
    Spec.Envelope.of(e),
    q,
    Ledgers.State.get(~Spec.Ask, a, Ledgers.Slot.ask(Spec.Envelope.of(e)))
  )(Ask.held(n, s, e, q))
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

def Spec.Node.version_kept(s, s2, v):
  +gr => Version.kept.at(s, s2, v, gr, Ledgers.State.status(~Spec.Ask, ~Spec.Ask.view, s, v), {==})


# Answers
# -------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Written or Conflicted comes after Written or Conflicted, by whether the merge
# still clashes before (b1) and after (b2)
def Left.follows(
  b1: Bool,
  b2: Bool,
  i: Ledgers.Id,
  k: Ledgers.Id
) -> {
  Spec.Answer.follows(
    Shared.Bool.when(Spec.Answer, b1, u => Spec.Answer.Written{i}, u => Spec.Answer.Conflicted{k}),
    Some{
      Shared.Bool.when(Spec.Answer, b2, u => Spec.Answer.Written{i}, u => Spec.Answer.Conflicted{k})
    }
  )
    == True{}: Bool
}:
  match b1 b2:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# the answer to a taken change comes after the answer to a taken change
def Taken.follows(
  s: Spec.State(),
  s2: Spec.State(),
  +i: Ledgers.Id,
  q: Spec.Ask
) -> {
  Spec.Answer.follows(Spec.Answer.taken(s, i, q), Some{Spec.Answer.taken(s2, i, q)}) == True{}: Bool
}:
  match q:
    case Spec.Ask.On{st, l, Spec.Change.Merge{f}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(s, i)),
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(s2, i)),
        i,
        i
      )
    case Spec.Ask.On{st, l, Spec.Change.Resolve{+k, n, c}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(s, k)),
        List.is_empty(&2, Resources.Name, Spec.Node.conflict(s2, k)),
        i,
        k
      )
    case Spec.Ask.On{st, l, Spec.Change.Make{a, b, c}}:
      {==}
    case Spec.Ask.On{st, l, Spec.Change.Own{a}}:
      {==}
    case Spec.Ask.On{st, l, Spec.Change.Write{a, b, c}}:
      {==}
    case Spec.Ask.On{st, l, Spec.Change.Move{a}}:
      {==}
    case Spec.Ask.On{st, l, Spec.Change.Mark{a, b}}:
      {==}
    case Spec.Ask.On{st, l, Spec.Change.Members{a}}:
      {==}
    case Spec.Ask.Start{a}:
      {==}

# the answer to a request that s holds comes before its answer in a state that
# grows from s, once its view v and the vote d that decided it in s are known
def Of.follows.at(
  +s: Spec.State(),
  +s2: Spec.State(),
  +i: Ledgers.Id,
  +q: Spec.Ask,
  v: Ledgers.View,
  d: Maybe<&2, Ledgers.Vote>,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  ed: {Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s, i) == d: Maybe<&2, Ledgers.Vote>}
) -> {
  Spec.Answer.follows(
    Spec.Answer.of(s, i, q, Ledgers.Status.of.view(v, d)),
    Some{
      Spec.Answer.of(
        s2,
        i,
        q,
        Ledgers.Status.of.view(v, Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, i))
      )
    }
  )
    == True{}: Bool
}:
  match v d:
    case Ledgers.View.Root{ms} w:
      Taken.follows(s, s2, i, q)
    case Ledgers.View.On{c, o, mk} None{}:
      {==}
    case Ledgers.View.On{c, o, mk} Some{Ledgers.Vote{j, True{}, u, r}}:
      %Equal.sym(
        Maybe<&2, Ledgers.Vote>,
        Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, i),
        Some{Ledgers.Vote{j, True{}, u, r}},
        Ledgers.State.decided_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          ~Spec.Ask.view,
          s,
          s2,
          i,
          Ledgers.Vote{j, True{}, u, r}
        )(gr)(ed)
      ): {
        Spec.Answer.follows(
          Spec.Answer.taken(s, i, q),
          Some{Spec.Answer.of(s2, i, q, Ledgers.Status.of.view(Ledgers.View.On{c, o, mk}, _))}
        )
          == True{}: Bool
      }
      Taken.follows(s, s2, i, q)
    case Ledgers.View.On{c, o, mk} Some{Ledgers.Vote{j, False{}, u, r}}:
      %Equal.sym(
        Maybe<&2, Ledgers.Vote>,
        Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, i),
        Some{Ledgers.Vote{j, False{}, u, r}},
        Ledgers.State.decided_grows(
          ~Spec.Ask,
          ~Spec.Ask.is_eq,
          ~Ask.laws(),
          ~Spec.Ask.view,
          s,
          s2,
          i,
          Ledgers.Vote{j, False{}, u, r}
        )(gr)(ed)
      ): {
        Spec.Answer.follows(
          Spec.Answer.Stale{},
          Some{Spec.Answer.of(s2, i, q, Ledgers.Status.of.view(Ledgers.View.On{c, o, mk}, _))}
        )
          == True{}: Bool
      }
      {==}

# Node.answer_kept for a slot that holds the request q2, by whether q2 is the
# change asked for (b)
def Kept.same(
  +s: Spec.State(),
  +s2: Spec.State(),
  +i: Ledgers.Id,
  +q2: Spec.Ask,
  -a: Spec.Answer,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  b: Bool
) -> {
  Some{
    Shared.Bool.when(
      Spec.Answer,
      b,
      u => Spec.Answer.of(
        s,
        i,
        q2,
        Ledgers.Status.of.view(Spec.Ask.view(q2), Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s, i))
      ),
      u => Spec.Answer.Refused{}
    )
  }
    == Some{a}: Maybe<&2, Spec.Answer>
} -> {
  Spec.Answer.follows(
    a,
    Some{
      Shared.Bool.when(
        Spec.Answer,
        b,
        u => Spec.Answer.of(
          s2,
          i,
          q2,
          Ledgers.Status.of.view(
            Spec.Ask.view(q2),
            Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, i)
          )
        ),
        u => Spec.Answer.Refused{}
      )
    }
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      h =>
        %Shared.Maybe.some_inj(
          Spec.Answer,
          Spec.Answer.of(
            s,
            i,
            q2,
            Ledgers.Status.of.view(Spec.Ask.view(q2), Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s, i))
          ),
          a,
          h
        ): {
          Spec.Answer.follows(
            _,
            Some{
              Spec.Answer.of(
                s2,
                i,
                q2,
                Ledgers.Status.of.view(
                  Spec.Ask.view(q2),
                  Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s2, i)
                )
              )
            }
          )
            == True{}: Bool
        }
        Of.follows.at(
          s,
          s2,
          i,
          q2,
          Spec.Ask.view(q2),
          Ledgers.State.decided(~Spec.Ask, ~Spec.Ask.view, s, i),
          gr,
          {==}
        )
    case False{}:
      h =>
        %Shared.Maybe.some_inj(Spec.Answer, Spec.Answer.Refused{}, a, h):
          {Spec.Answer.follows(_, Some{Spec.Answer.Refused{}}) == True{}: Bool}
        {==}

# Node.answer_kept once the cell c of the request's slot in s is known
def Kept.at(
  +s: Spec.State(),
  +s2: Spec.State(),
  +i: Ledgers.Id,
  +q: Spec.Ask,
  -a: Spec.Answer,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
  ec: {
    Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(i)) == c: Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>
  }
) -> {
  Spec.Answer.held(s, i, q, c) == Some{a}: Maybe<&2, Spec.Answer>
} -> {
  Spec.Answer.follows(
    a,
    Spec.Answer.held(s2, i, q, Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)))
  )
    == True{}: Bool
}:
  match c:
    case None{}:
      h => Empty.absurd(
        {
          Spec.Answer.follows(
            a,
            Spec.Answer.held(s2, i, q, Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)))
          )
            == True{}: Bool
        },
        Shared.Maybe.none_ne_some(Spec.Answer, a, h)
      )
    case Some{Cells.Many{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)),
          Some{Cells.Many{}},
          Slot.many_kept(s, s2, Ledgers.Slot.ask(i), gr, ec)
        ): {Spec.Answer.follows(a, Spec.Answer.held(s2, i, q, _)) == True{}: Bool}
        %Shared.Maybe.some_inj(Spec.Answer, Spec.Answer.Refused{}, a, h):
          {Spec.Answer.follows(_, Some{Spec.Answer.Refused{}}) == True{}: Bool}
        {==}
    case Some{Cells.One{Ledgers.Entry.Vote{v}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)),
          Some{Cells.One{Ledgers.Entry.Vote{v}}},
          Slot.one_kept(s, s2, Ledgers.Slot.ask(i), Ledgers.Entry.Vote{v}, gr, ec)
        ): {Spec.Answer.follows(a, Spec.Answer.held(s2, i, q, _)) == True{}: Bool}
        %Shared.Maybe.some_inj(Spec.Answer, Spec.Answer.Refused{}, a, h):
          {Spec.Answer.follows(_, Some{Spec.Answer.Refused{}}) == True{}: Bool}
        {==}
    case Some{Cells.One{Ledgers.Entry.At{w}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)),
          Some{Cells.One{Ledgers.Entry.At{w}}},
          Slot.one_kept(s, s2, Ledgers.Slot.ask(i), Ledgers.Entry.At{w}, gr, ec)
        ): {Spec.Answer.follows(a, Spec.Answer.held(s2, i, q, _)) == True{}: Bool}
        %Shared.Maybe.some_inj(Spec.Answer, Spec.Answer.Refused{}, a, h):
          {Spec.Answer.follows(_, Some{Spec.Answer.Refused{}}) == True{}: Bool}
        {==}
    case Some{Cells.One{Ledgers.Entry.Data{ws}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)),
          Some{Cells.One{Ledgers.Entry.Data{ws}}},
          Slot.one_kept(s, s2, Ledgers.Slot.ask(i), Ledgers.Entry.Data{ws}, gr, ec)
        ): {Spec.Answer.follows(a, Spec.Answer.held(s2, i, q, _)) == True{}: Bool}
        %Shared.Maybe.some_inj(Spec.Answer, Spec.Answer.Refused{}, a, h):
          {Spec.Answer.follows(_, Some{Spec.Answer.Refused{}}) == True{}: Bool}
        {==}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Spec.Ask>>>,
          Ledgers.State.get(~Spec.Ask, s2, Ledgers.Slot.ask(i)),
          Some{Cells.One{Ledgers.Entry.Ask{j, t, q2}}},
          Slot.one_kept(s, s2, Ledgers.Slot.ask(i), Ledgers.Entry.Ask{j, t, q2}, gr, ec)
        ): {Spec.Answer.follows(a, Spec.Answer.held(s2, i, q, _)) == True{}: Bool}
        Kept.same(s, s2, i, q2, a, gr, Spec.Ask.is_eq(q2, q))(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

def Spec.Node.answer_kept(s, s2, e, q, a):
  +gr => h => Kept.at(
    s,
    s2,
    Spec.Envelope.of(e),
    q,
    a,
    gr,
    Ledgers.State.get(~Spec.Ask, s, Ledgers.Slot.ask(Spec.Envelope.of(e))),
    {==}
  )(h)

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

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the steps of a line start its steps in a state that grows, once the listing m
# of the line is known
def Steps.grow.at(
  s: Spec.State(),
  +s2: Spec.State(),
  +c: Ledgers.Chain,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  m: Maybe<&2, List<&2, Ledgers.Vote>>,
  e: {Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s, c) == m: Maybe<&2, List<&2, Ledgers.Vote>>}
) -> {
  List.take(
    &2,
    Ledgers.Vote,
    Maybe.default(
      &2,
      List<&2, Ledgers.Vote>,
      Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c),
      []
    ),
    List.length(&2, Ledgers.Vote, Maybe.default(&2, List<&2, Ledgers.Vote>, m, []))
  )
    == Maybe.default(&2, List<&2, Ledgers.Vote>, m, []): List<&2, Ledgers.Vote>
}:
  match m:
    case None{}:
      Shared.List.take_zero(
        Ledgers.Vote,
        Maybe.default(
          &2,
          List<&2, Ledgers.Vote>,
          Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s2, c),
          []
        )
      )
    case Some{+xs}:
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

def Spec.Node.versions_grow(s, s2, r, b):
  +gr =>
    +c = Spec.Line.chain(r, Some{Spec.Line.Branch{b}})
    Steps.taken_prefix(
      Spec.Node.steps(s, r, Some{Spec.Line.Branch{b}}),
      Spec.Node.steps(s2, r, Some{Spec.Line.Branch{b}})
    )(Steps.grow.at(s, s2, c, gr, Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s, c), {==}))

# Marks
# -----

# what a step says of a mark stays, once its request a in s is known
def At.kept.at(
  +s: Spec.State(),
  +s2: Spec.State(),
  +i: Ledgers.Id,
  k: Bool,
  m: String,
  -b: Bool,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  a: Maybe<&2, Ledgers.Asked<Spec.Ask>>,
  ea: {Ledgers.State.asked(~Spec.Ask, s, i) == a: Maybe<&2, Ledgers.Asked<Spec.Ask>>}
) -> {
  Spec.Mark.at(k, a, m) == Some{b}: Maybe<&2, Bool>
} -> {Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s2, i), m) == Some{b}: Maybe<&2, Bool>}:
  match k a:
    case False{} w:
      h => h
    case True{} None{}:
      h => Empty.absurd(
        {Spec.Mark.at(True{}, Ledgers.State.asked(~Spec.Ask, s2, i), m) == Some{b}: Maybe<&2, Bool>},
        Shared.Maybe.none_ne_some(Bool, b, h)
      )
    case True{} Some{z}:
      h =>
        %Equal.sym(
          Maybe<&2, Ledgers.Asked<Spec.Ask>>,
          Ledgers.State.asked(~Spec.Ask, s2, i),
          Some{z},
          Ledgers.State.read_grows(
            ~Spec.Ask,
            ~Spec.Ask.is_eq,
            ~Ask.laws(),
            ~Ledgers.Asked<Spec.Ask>,
            x => Ledgers.Asked.of(~Spec.Ask, x),
            {==},
            s,
            s2,
            Ledgers.Slot.ask(i),
            z
          )(gr)(ea)
        ): {Spec.Mark.at(True{}, _, m) == Some{b}: Maybe<&2, Bool>}
        h

# Mark.kept.go at the first step, once what it says of the mark in s is known
# (t0); ih is Mark.kept.go of the steps after it
def Mark.kept.at(
  +s: Spec.State(),
  +s2: Spec.State(),
  +i: Ledgers.Id,
  +k: Bool,
  +m: String,
  -v: Ledgers.Id,
  gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  +prev: Maybe<&2, Ledgers.Id>,
  +xr: List<&2, Ledgers.Vote>,
  +yr: List<&2, Ledgers.Vote>,
  t0: Maybe<&2, Bool>,
  et: {Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s, i), m) == t0: Maybe<&2, Bool>},
  ih: {
    Spec.Mark.first(
      s,
      xr,
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, u => Some{i}, u => prev),
      m
    )
      == Some{v}: Maybe<&2, Ledgers.Id>
  } -> {
    Spec.Mark.first(
      s2,
      yr,
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, u => Some{i}, u => prev),
      m
    )
      == Some{v}: Maybe<&2, Ledgers.Id>
  }
) -> {
  Spec.Mark.pick(
    t0,
    prev,
    u => Spec.Mark.first(
      s,
      xr,
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev),
      m
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Id>
} -> {
  Spec.Mark.pick(
    Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s2, i), m),
    prev,
    u => Spec.Mark.first(
      s2,
      yr,
      Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev),
      m
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Id>
}:
  match t0:
    case None{}:
      h => Empty.absurd(
        {
          Spec.Mark.pick(
            Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s2, i), m),
            prev,
            u => Spec.Mark.first(
              s2,
              yr,
              Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev),
              m
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Id>
        },
        Shared.Maybe.none_ne_some(Ledgers.Id, v, h)
      )
    case Some{True{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Bool>,
          Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s2, i), m),
          Some{True{}},
          At.kept.at(s, s2, i, k, m, True{}, gr, Ledgers.State.asked(~Spec.Ask, s, i), {==})(et)
        ): {
          Spec.Mark.pick(
            _,
            prev,
            u => Spec.Mark.first(
              s2,
              yr,
              Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev),
              m
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Id>
        }
        h
    case Some{False{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Bool>,
          Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s2, i), m),
          Some{False{}},
          At.kept.at(s, s2, i, k, m, False{}, gr, Ledgers.State.asked(~Spec.Ask, s, i), {==})(et)
        ): {
          Spec.Mark.pick(
            _,
            prev,
            u => Spec.Mark.first(
              s2,
              yr,
              Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, w => Some{i}, w => prev),
              m
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Id>
        }
        ih(h)

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the version that the first mark m of the steps xs names is the one that it
# names in steps that start with xs, of a state that grows
def Mark.kept.go(
  +s: Spec.State(),
  +s2: Spec.State(),
  +m: String,
  -v: Ledgers.Id,
  +gr: {Ledgers.State.grows(~Spec.Ask, ~Spec.Ask.is_eq, s, s2) == True{}: Bool},
  xs: List<&2, Ledgers.Vote>,
  ys: List<&2, Ledgers.Vote>,
  +prev: Maybe<&2, Ledgers.Id>
) -> {
  List.take(&2, Ledgers.Vote, ys, List.length(&2, Ledgers.Vote, xs)) == xs: List<&2, Ledgers.Vote>
} -> {
  Spec.Mark.first(s, xs, prev, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Spec.Mark.first(s2, ys, prev, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
  match xs ys:
    case Nil{} y:
      e => h => Empty.absurd(
        {Spec.Mark.first(s2, y, prev, m) == Some{v}: Maybe<&2, Ledgers.Id>},
        Shared.Maybe.none_ne_some(Ledgers.Id, v, h)
      )
    case Con{x, xr} Nil{}:
      e => h => Empty.absurd(
        {Spec.Mark.first(s2, [], prev, m) == Some{v}: Maybe<&2, Ledgers.Id>},
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
    case Con{Ledgers.Vote{+i, +k, +w, +hh}, +xr} Con{y, +yr}:
      +e => h =>
        %Equal.sym(
          Ledgers.Vote,
          y,
          Ledgers.Vote{i, k, w, hh},
          Shared.List.head_eq(
            Ledgers.Vote,
            y,
            Ledgers.Vote{i, k, w, hh},
            List.take(&2, Ledgers.Vote, yr, List.length(&2, Ledgers.Vote, xr)),
            xr,
            e
          )
        ): {Spec.Mark.first(s2, _ <> yr, prev, m) == Some{v}: Maybe<&2, Ledgers.Id>}
        Mark.kept.at(
          s,
          s2,
          i,
          k,
          m,
          v,
          gr,
          prev,
          xr,
          yr,
          Spec.Mark.at(k, Ledgers.State.asked(~Spec.Ask, s, i), m),
          {==},
          Mark.kept.go(
            s,
            s2,
            m,
            v,
            gr,
            xr,
            yr,
            Shared.Bool.when(Maybe<&2, Ledgers.Id>, k, u => Some{i}, u => prev)
          )(
            Shared.List.tail_eq(
              Ledgers.Vote,
              y,
              Ledgers.Vote{i, k, w, hh},
              List.take(&2, Ledgers.Vote, yr, List.length(&2, Ledgers.Vote, xr)),
              xr,
              e
            )
          )
        )(h)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

def Spec.Node.mark_kept(s, s2, r, b, m, v):
  +gr =>
    +c = Spec.Line.chain(r, Some{Spec.Line.Branch{b}})
    Mark.kept.go(
      s,
      s2,
      m,
      v,
      gr,
      Spec.Node.steps(s, r, Some{Spec.Line.Branch{b}}),
      Spec.Node.steps(s2, r, Some{Spec.Line.Branch{b}}),
      None{}
    )(Steps.grow.at(s, s2, c, gr, Ledgers.Line.steps(~Spec.Ask, ~Spec.Ask.view, s, c), {==}))
