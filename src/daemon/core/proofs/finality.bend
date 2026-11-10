# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/resources.bend as Resources
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/shared/text.bend as Texts
import ../basics.bend as Basics
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
# bend-lint: expect-next bend-lint-rules/no_unused/imports@warning -- its proofs of laws are used here
import ./lines.bend as ProofLines
import ./trees.bend as ProofTrees

# Finality
# --------
# What a node knows of a line stays, whatever the node does next.

# an outcome that a line holds, it holds in a node that keeps its logs
def Chain.out.kept(
  a: Basics.Node,
  b: Basics.Node,
  +c: Ledgers.Chain,
  +i: Ledgers.Id,
  -o: Basics.Out,
  hk: Spec.Node.Keeps(a, b)
) -> {
  Basics.Chain.out(a, c, i) == Some{o}: Maybe<&2, Basics.Out>
} -> {Basics.Chain.out(b, c, i) == Some{o}: Maybe<&2, Basics.Out>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Basics.Out,
    Basics.Line.get(a, c, Basics.Log.out(i)),
    Basics.Line.get(b, c, Basics.Log.out(i)),
    ws => Basics.Out.read(ws),
    ws => Basics.Out.read(ws),
    o,
    w => hk(c)(Basics.Log.out(i))(w),
    w => e => e
  )

# the version of a number that a line holds, it holds in a node that keeps
# its logs
def Chain.version.kept(
  a: Basics.Node,
  b: Basics.Node,
  +c: Ledgers.Chain,
  +n: U32,
  -x: Basics.Version,
  hk: Spec.Node.Keeps(a, b)
) -> {
  Basics.Chain.version(a, c, n) == Some{x}: Maybe<&2, Basics.Version>
} -> {Basics.Chain.version(b, c, n) == Some{x}: Maybe<&2, Basics.Version>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Basics.Version,
    Basics.Line.get(a, c, Basics.Log.version(n)),
    Basics.Line.get(b, c, Basics.Log.version(n)),
    ws => Basics.Version.read(ws),
    ws => Basics.Version.read(ws),
    x,
    w => hk(c)(Basics.Log.version(n))(w),
    w => e => e
  )

# a mark that a line holds, it holds in a node that keeps its logs
def Chain.mark.kept(
  a: Basics.Node,
  b: Basics.Node,
  +c: Ledgers.Chain,
  +m: String,
  -v: Ledgers.Id,
  hk: Spec.Node.Keeps(a, b)
) -> {
  Basics.Chain.mark(a, c, m) == Some{v}: Maybe<&2, Ledgers.Id>
} -> {Basics.Chain.mark(b, c, m) == Some{v}: Maybe<&2, Ledgers.Id>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Ledgers.Id,
    Basics.Line.get(a, c, Basics.Log.mark(m)),
    Basics.Line.get(b, c, Basics.Log.mark(m)),
    ws => Basics.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    ws => Basics.Read.whole(Ledgers.Id, Ledgers.Id.code.read(ws)),
    v,
    w => hk(c)(Basics.Log.mark(m))(w),
    w => e => e
  )

# the line of a request that a node holds, a node that grew holds
def Chain.of.kept(
  +a: Basics.Node,
  b: Basics.Node,
  +i: Ledgers.Id,
  -c: Ledgers.Chain,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Basics.Node.chain_of(a, i) == Some{c}: Maybe<&2, Ledgers.Chain>
} -> {Basics.Node.chain_of(b, i) == Some{c}: Maybe<&2, Ledgers.Chain>}:
  Shared.Maybe.bind_kept(
    Ledgers.Asked<Basics.Ask>,
    Ledgers.Chain,
    Basics.Node.asked(a, i),
    Basics.Node.asked(b, i),
    x => Some{Basics.Ask.chain(i, Basics.Asked.ask(x))},
    x => Some{Basics.Ask.chain(i, Basics.Asked.ask(x))},
    c,
    x => Ledgers.State.read_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      ~Ledgers.Asked<Basics.Ask>,
      m => Ledgers.Asked.of(~Basics.Ask, m),
      {==},
      Basics.State.ledger(a),
      Basics.State.ledger(b),
      Ledgers.Slot.ask(i),
      x
    )(g),
    x => e => e
  )

# an outcome that a node knows, a node that grew and keeps its logs knows
def Out.kept(
  +a: Basics.Node,
  +b: Basics.Node,
  +i: Ledgers.Id,
  -o: Basics.Out,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  hk: Spec.Node.Keeps(a, b)
) -> {
  Basics.Node.out(a, i) == Some{o}: Maybe<&2, Basics.Out>
} -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Basics.Out>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Basics.Out,
    Basics.Node.chain_of(a, i),
    Basics.Node.chain_of(b, i),
    c => Basics.Chain.out(a, c, i),
    c => Basics.Chain.out(b, c, i),
    o,
    c => Chain.of.kept(a, b, i, c, g),
    +c => Chain.out.kept(a, b, c, i, o, hk)
  )

# the version of an outcome, in a node that keeps the logs
def Out.on.kept(
  a: Basics.Node,
  b: Basics.Node,
  c: Ledgers.Chain,
  o: Basics.Out,
  -x: Basics.Version,
  hk: Spec.Node.Keeps(a, b)
) -> {
  Basics.Out.on(a, c, o) == Some{x}: Maybe<&2, Basics.Version>
} -> {Basics.Out.on(b, c, o) == Some{x}: Maybe<&2, Basics.Version>}:
  match o:
    case Basics.Out.Stale{}:
      e => e
    case Basics.Out.Taken{n}:
      Chain.version.kept(a, b, c, n, x, hk)

# the version that a request made on a line, in a node that keeps the logs
def Chain.made.kept(
  +a: Basics.Node,
  +b: Basics.Node,
  +c: Ledgers.Chain,
  +v: Ledgers.Id,
  -x: Basics.Version,
  hk1: Spec.Node.Keeps(a, b),
  hk2: Spec.Node.Keeps(a, b)
) -> {
  Basics.Chain.made(a, c, v) == Some{x}: Maybe<&2, Basics.Version>
} -> {Basics.Chain.made(b, c, v) == Some{x}: Maybe<&2, Basics.Version>}:
  Shared.Maybe.bind_kept(
    Basics.Out,
    Basics.Version,
    Basics.Chain.out(a, c, v),
    Basics.Chain.out(b, c, v),
    o => Basics.Out.on(a, c, o),
    o => Basics.Out.on(b, c, o),
    x,
    o => Chain.out.kept(a, b, c, v, o, hk1),
    o => Out.on.kept(a, b, c, o, x, hk2)
  )

# the version that a request made, in a node that grew and keeps the logs
def Made.kept(
  +a: Basics.Node,
  +b: Basics.Node,
  +v: Ledgers.Id,
  -x: Basics.Version,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  hk1: Spec.Node.Keeps(a, b),
  hk2: Spec.Node.Keeps(a, b)
) -> {
  Basics.Node.made(a, v) == Some{x}: Maybe<&2, Basics.Version>
} -> {Basics.Node.made(b, v) == Some{x}: Maybe<&2, Basics.Version>}:
  Shared.Maybe.bind_kept(
    Ledgers.Chain,
    Basics.Version,
    Basics.Node.chain_of(a, v),
    Basics.Node.chain_of(b, v),
    +c => Basics.Chain.made(a, c, v),
    +c => Basics.Chain.made(b, c, v),
    x,
    c => Chain.of.kept(a, b, v, c, g),
    +c => Chain.made.kept(a, b, c, v, x, hk1, hk2)
  )

def Spec.Node.out_final(n, evs, s, i, o):
  Out.kept(
    s,
    Spec.Node.after(n, evs, s),
    i,
    o,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Node.made_final(n, evs, s, v, x):
  Made.kept(
    s,
    Spec.Node.after(n, evs, s),
    v,
    x,
    Spec.Node.after_grows(n, evs, s),
    Spec.Node.after_keeps(n, evs, s),
    Spec.Node.after_keeps(n, evs, s)
  )

def Spec.Chain.version_final(n, evs, s, c, k, x):
  Chain.version.kept(s, Spec.Node.after(n, evs, s), c, k, x, Spec.Node.after_keeps(n, evs, s))

def Spec.Chain.mark_final(n, evs, s, c, m, v):
  Chain.mark.kept(s, Spec.Node.after(n, evs, s), c, m, v, Spec.Node.after_keeps(n, evs, s))

def Spec.Chain.start_final(n, evs, s, r, b, v):
  Spec.Node.after_keeps(n, evs, s)(Ledgers.Chain{r, None{}})(Basics.Log.start(b))(v)

# the answer b may come after the answer a, if there is an a
def Follows.opt(ma: Maybe<&2, Reading.Answer>, mb: Maybe<&2, Reading.Answer>) -> Bool:
  match ma:
    case None{}:
      True{}
    case Some{x}:
      Reading.Answer.follows(x, mb)

# Written or Conflicted may come after Written or Conflicted
def Left.follows(
  ba: Bool,
  bb: Bool,
  i: Ledgers.Id,
  k: Ledgers.Id
) -> {
  Reading.Answer.follows(
    Shared.Bool.when(
      Reading.Answer,
      ba,
      u => Reading.Answer.Written{i},
      u => Reading.Answer.Conflicted{k}
    ),
    Some{
      Shared.Bool.when(
        Reading.Answer,
        bb,
        u => Reading.Answer.Written{i},
        u => Reading.Answer.Conflicted{k}
      )
    }
  )
    == True{}: Bool
}:
  match ba bb:
    case True{} True{}:
      Ledgers.Id.is_eq_refl(i)
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      Ledgers.Id.is_eq_refl(k)

# the answer to a taken change may come after the answer to it
def Taken.follows(
  a: Basics.Node,
  b: Basics.Node,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> {
  Reading.Answer.follows(
    Reading.Answer.taken(a, i, q),
    Some{Reading.Answer.taken(b, i, q)}
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Branch{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Group{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Own{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Write{x, y, z}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Resolve{+k, y, z}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(a, k)),
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(b, k)),
        i,
        k
      )
    case Basics.Ask.On{st, l, Basics.Change.Merge{f}}:
      Left.follows(
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(a, i)),
        List.is_empty(&2, Resources.Name, Reading.Node.conflict(b, i)),
        i,
        i
      )
    case Basics.Ask.On{st, l, Basics.Change.Move{x}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Mark{x, y}}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, Basics.Change.Key{x, y}}:
      Ledgers.Id.is_eq_refl(i)

# Asked.follows once the outcome oa of the request is known
def Of.follows(
  a: Basics.Node,
  b: Basics.Node,
  i: Ledgers.Id,
  q: Basics.Ask,
  oa: Maybe<&2, Basics.Out>
) -> {
  Basics.Node.out(a, i) == oa: Maybe<&2, Basics.Out>
} -> (
  @o: Basics.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Basics.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Basics.Out>}
) -> {
  Reading.Answer.follows(
    Reading.Answer.of(a, i, q, Basics.Node.out(a, i)),
    Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
  )
    == True{}: Bool
}:
  match oa:
    case None{}:
      eo => ho =>
        %Equal.sym(
          Maybe<&2, Basics.Out>,
          Basics.Node.out(a, i),
          None{},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        {==}
    case Some{Basics.Out.Stale{}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Basics.Out>,
          Basics.Node.out(a, i),
          Some{Basics.Out.Stale{}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Basics.Out>,
          Basics.Node.out(b, i),
          Some{Basics.Out.Stale{}},
          ho(Basics.Out.Stale{})(eo)
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, Some{Basics.Out.Stale{}}),
            Some{Reading.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        {==}
    case Some{Basics.Out.Taken{k}}:
      +eo => ho =>
        %Equal.sym(
          Maybe<&2, Basics.Out>,
          Basics.Node.out(a, i),
          Some{Basics.Out.Taken{k}},
          eo
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, _),
            Some{Reading.Answer.of(b, i, q, Basics.Node.out(b, i))}
          )
            == True{}: Bool
        }
        %Equal.sym(
          Maybe<&2, Basics.Out>,
          Basics.Node.out(b, i),
          Some{Basics.Out.Taken{k}},
          ho(Basics.Out.Taken{k})(eo)
        ): {
          Reading.Answer.follows(
            Reading.Answer.of(a, i, q, Some{Basics.Out.Taken{k}}),
            Some{Reading.Answer.of(b, i, q, _)}
          )
            == True{}: Bool
        }
        Taken.follows(a, b, i, q)

# the answer to a request that a node holds may come after the answer to it
def Asked.follows(
  +a: Basics.Node,
  b: Basics.Node,
  +i: Ledgers.Id,
  q: Basics.Ask,
  ho: @o: Basics.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Basics.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Basics.Out>}
) -> {
  Reading.Answer.follows(
    Reading.Answer.asked(a, i, q),
    Some{Reading.Answer.asked(b, i, q)}
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      Ledgers.Id.is_eq_refl(i)
    case Basics.Ask.On{st, l, ch}:
      Of.follows(a, b, i, Basics.Ask.On{st, l, ch}, Basics.Node.out(a, i))({==})(ho)

# Held.follows once whether the held change is the one asked is known (bq)
def Held.follows.if(
  bq: Bool,
  -x: Reading.Answer,
  -y: Reading.Answer,
  h: {Reading.Answer.follows(x, Some{y}) == True{}: Bool}
) -> {
  Reading.Answer.follows(
    Shared.Bool.when(Reading.Answer, bq, u => x, u => Reading.Answer.Refused{}),
    Some{Shared.Bool.when(Reading.Answer, bq, u => y, u => Reading.Answer.Refused{})}
  )
    == True{}: Bool
}:
  match bq:
    case True{}:
      h
    case False{}:
      {==}

# the answer of a node that holds the same cell may come after the answer
def Held.follows(
  a: Basics.Node,
  b: Basics.Node,
  i: Ledgers.Id,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  ho: @o: Basics.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Basics.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Basics.Out>}
) -> {
  Follows.opt(Reading.Answer.held(a, i, q, m), Reading.Answer.held(b, i, q, m)) == True{}: Bool
}:
  match m:
    case None{}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Ask{j, t, +q2}}}:
      Held.follows.if(
        Basics.Ask.is_eq(q2, q),
        Reading.Answer.asked(a, i, q2),
        Reading.Answer.asked(b, i, q2),
        Asked.follows(a, b, i, q2, ho)
      )
    case Some{Cells.One{Ledgers.Entry.Vote{v}}}:
      {==}
    case Some{Cells.One{Ledgers.Entry.Data{d}}}:
      {==}
    case Some{Cells.Many{}}:
      {==}

# a cell that is kept is the same cell
def Cell.kept.eq(
  c: Cells.Cell<Ledgers.Entry<Basics.Ask>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    Some{c},
    mb
  )
    == True{}: Bool
} -> {mb == Some{c}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}:
  match c mb:
    case Cells.One{x} y:
      Cells.Cell.keeps_value(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
        ~Ledgers.Entry.laws(~Basics.Ask, ~Basics.Ask.is_eq, ~Basics.Ask.laws()),
        x,
        y
      )
    case Cells.Many{} Some{Cells.Many{}}:
      h => {==}
    case Cells.Many{} Some{Cells.One{y}}:
      h => Empty.absurd(
        {
          Some{Cells.One{y}} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
        },
        Shared.Bool.false_ne_true(h)
      )
    case Cells.Many{} None{}:
      h => Empty.absurd(
        {None{} == Some{Cells.Many{}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>},
        Shared.Bool.false_ne_true(h)
      )

# Node.answer_follows once the cell ma of the request's ID is known
def Answer.follows.at(
  a: Basics.Node,
  b: Basics.Node,
  i: Ledgers.Id,
  q: Basics.Ask,
  -x: Reading.Answer,
  ma: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  mb: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  ho: @o: Basics.Out -> {
    Basics.Node.out(a, i) == Some{o}: Maybe<&2, Basics.Out>
  } -> {Basics.Node.out(b, i) == Some{o}: Maybe<&2, Basics.Out>}
) -> {
  Cells.Cell.keeps(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    ma,
    mb
  )
    == True{}: Bool
} -> {
  Reading.Answer.held(a, i, q, ma) == Some{x}: Maybe<&2, Reading.Answer>
} -> {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, mb)) == True{}: Bool}:
  match ma:
    case None{}:
      ek => e => Empty.absurd(
        {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, mb)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Reading.Answer, x, e)
      )
    case Some{+c}:
      ek => e =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
          mb,
          Some{c},
          Cell.kept.eq(c, mb)(ek)
        ): {Reading.Answer.follows(x, Reading.Answer.held(b, i, q, _)) == True{}: Bool}
        %e: {Follows.opt(_, Reading.Answer.held(b, i, q, Some{c})) == True{}: Bool}
        Held.follows(a, b, i, q, Some{c}, ho)

def Spec.Node.answer_follows(n, evs, s, e, q, x):
  Answer.follows.at(
    s,
    Spec.Node.after(n, evs, s),
    Basics.Envelope.of(e),
    q,
    x,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.ask(Basics.Envelope.of(e))),
    Ledgers.State.get(
      ~Basics.Ask,
      Basics.State.ledger(Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    ),
    o => Out.kept(
      s,
      Spec.Node.after(n, evs, s),
      Basics.Envelope.of(e),
      o,
      Spec.Node.after_grows(n, evs, s),
      Spec.Node.after_keeps(n, evs, s)
    )
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      ~Cells.Cell.keeps(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      ~Cells.Cell.none_kept(
        ~Ledgers.Entry<Basics.Ask>,
        ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq)
      ),
      Basics.State.ledger(s),
      Basics.State.ledger(Spec.Node.after(n, evs, s)),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    )(Spec.Node.after_grows(n, evs, s))
  )

# Drafts
# ------

# one of two drafts that are there
def When.some(
  b: Bool,
  -x: Maybe<&2, Reading.Draft>,
  -y: Maybe<&2, Reading.Draft>,
  hx: {Maybe.is_some(&2, Reading.Draft, x) == True{}: Bool},
  hy: {Maybe.is_some(&2, Reading.Draft, y) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Shared.Bool.when(Maybe<&2, Reading.Draft>, b, u => x, u => y)
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a draft that is there stays, with a write or not
def Draft.with.some(
  -found: Maybe<&2, Reading.Draft>,
  -k: List<&2, Bool>,
  m: Maybe<&2, Basics.Content>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Reading.Draft, Reading.Draft.with(found, k, m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{c}:
      h => {==}

# a draft that is there stays, after one more request
def Draft.of.some(
  w: String,
  r: Ledgers.Id,
  b: String,
  n: Resources.Name,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  -found: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, i, a, found)) == True{}: Bool}:
  match i a:
    case Ledgers.Id{w2, q2} Some{Ledgers.Asked{t, q}}:
      +h => When.some(
        String.eq(w2, w),
        Reading.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        ),
        found,
        Draft.with.some(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        )(h),
        h
      )
    case Ledgers.Id{w2, q2} None{}:
      h => h

# a draft that is there stays, after more requests
def Last.some(
  +s: Basics.Node,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  found: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool
} -> {
  Maybe.is_some(&2, Reading.Draft, Reading.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool
}:
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => Last.some(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Basics.Node.asked(s, i), found)
      )(Draft.of.some(w, r, b, n, i, Basics.Node.asked(s, i), found)(h))

# a write of the writer w to the resource gives a draft
def Draft.of.hit(
  w: String,
  -r: Ledgers.Id,
  -b: String,
  -n: Resources.Name,
  -q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  -found: Maybe<&2, Reading.Draft>,
  ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>}
) -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Reading.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, Some{Ledgers.Asked{t, q}}, found)
  )
    == True{}: Bool
}:
  %Equal.sym(
    Bool,
    String.eq(w, w),
    True{},
    Texts.String.eq_refl(w)
  ): {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Shared.Bool.when(
        Maybe<&2, Reading.Draft>,
        _,
        u => Reading.Draft.with(
          found,
          List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)),
          Reading.Draft.content(r, b, n, q)
        ),
        u => found
      )
    )
      == True{}: Bool
  }
  %Equal.sym(
    Maybe<&2, Basics.Content>,
    Reading.Draft.content(r, b, n, q),
    Some{c},
    ec
  ): {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Reading.Draft.with(found, List.append(&2, Bool, Tries.Trie.text(t), Tries.Trie.text(q2)), _)
    )
      == True{}: Bool
  }
  {==}

# Last.hit once whether the first request is the one looked for is known (bh)
def Last.hit.if(
  +s: Basics.Node,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  +i: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  found: Maybe<&2, Reading.Draft>,
  q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  bh: Bool,
  ebh: {Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}) == bh: Bool},
  ea: {
    Basics.Node.asked(
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Basics.Ask>>
  },
  ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}) == True{}: Bool
  } -> {
    Maybe.is_some(
      &2,
      Reading.Draft,
      Reading.Draft.last(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Basics.Node.asked(s, i), found)
      )
    )
      == True{}: Bool
  }
) -> {
  List.any.if(
    u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, Ledgers.Id{w, q2}),
    bh
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Reading.Draft,
    Reading.Draft.last(
      s,
      w,
      r,
      b,
      n,
      rest,
      Reading.Draft.of(w, r, b, n, i, Basics.Node.asked(s, i), found)
    )
  )
    == True{}: Bool
}:
  match bh:
    case False{}:
      h => ih(h)
    case True{}:
      h => Last.some(
        s,
        w,
        r,
        b,
        n,
        rest,
        Reading.Draft.of(w, r, b, n, i, Basics.Node.asked(s, i), found)
      )(
        %Equal.sym(Ledgers.Id, i, Ledgers.Id{w, q2}, Ledgers.Id.is_eq_sound(i, Ledgers.Id{w, q2})(ebh)): {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, _, Basics.Node.asked(s, _), found)) == True{}: Bool}
        %Equal.sym(Maybe<&2, Ledgers.Asked<Basics.Ask>>, Basics.Node.asked(s, Ledgers.Id{w, q2}), Some{Ledgers.Asked{t, q}}, ea): {Maybe.is_some(&2, Reading.Draft, Reading.Draft.of(w, r, b, n, Ledgers.Id{w, q2}, _, found)) == True{}: Bool}
        Draft.of.hit(w, r, b, n, q2, t, q, c, found, ec))

# a write of the writer w among requests gives a draft
def Last.hit(
  +s: Basics.Node,
  +w: String,
  +r: Ledgers.Id,
  +b: String,
  +n: Resources.Name,
  qs: List<&2, Ledgers.Id>,
  +found: Maybe<&2, Reading.Draft>,
  +q2: String,
  -t: String,
  -q: Basics.Ask,
  -c: Basics.Content,
  +ea: {
    Basics.Node.asked(
      s,
      Ledgers.Id{w, q2}
    )
      == Some{Ledgers.Asked{t, q}}: Maybe<&2, Ledgers.Asked<Basics.Ask>>
  },
  +ec: {Reading.Draft.content(r, b, n, q) == Some{c}: Maybe<&2, Basics.Content>}
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, Ledgers.Id{w, q2}) == True{}: Bool
} -> {
  Maybe.is_some(&2, Reading.Draft, Reading.Draft.last(s, w, r, b, n, qs, found)) == True{}: Bool
}:
  match qs:
    case Nil{}:
      h => Empty.absurd(
        {Maybe.is_some(&2, Reading.Draft, found) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Con{+i, +rest}:
      Last.hit.if(
        s,
        w,
        r,
        b,
        n,
        i,
        rest,
        found,
        q2,
        t,
        q,
        c,
        Ledgers.Id.is_eq(i, Ledgers.Id{w, q2}),
        {==},
        ea,
        ec,
        Last.hit(
          s,
          w,
          r,
          b,
          n,
          rest,
          Reading.Draft.of(w, r, b, n, i, Basics.Node.asked(s, i), found),
          q2,
          t,
          q,
          c,
          ea,
          ec
        )
      )

# the content of a draft that is there is there
def What.some(
  m: Maybe<&2, Reading.Draft>
) -> {
  Maybe.is_some(&2, Reading.Draft, m) == True{}: Bool
} -> {Maybe.is_some(&2, Basics.Content, Reading.Draft.what(m)) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{Reading.Draft{k, c}}:
      h => {==}

def Spec.Node.draft_some(s, w, r, b, n, q2, t, q, c):
  hc => ea => ec => What.some(
    Reading.Draft.last(s, w, r, b, n, Sealing.Wait.of(s, Basics.Line.chain(r, Some{b})), None{})
  )(
    Last.hit(
      s,
      w,
      r,
      b,
      n,
      Sealing.Wait.of(s, Basics.Line.chain(r, Some{b})),
      None{},
      q2,
      t,
      q,
      c,
      ea,
      ec
    )(hc)
  )
