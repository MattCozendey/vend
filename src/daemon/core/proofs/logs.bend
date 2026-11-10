# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/tree.bend as Trees
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../stepping.bend as Stepping
import ../voting.bend as Voting
import ./trees.bend as ProofTrees

# Asks
# ----

# a slot that holds a cell holds one in a node that grew
def Slot.held_kept(
  +a: Basics.Node,
  +b: Basics.Node,
  +k: List<&2, Bool>,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(a), k)
  )
    == True{}: Bool
} -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(b), k)
  )
    == True{}: Bool
}:
  Cells.Cell.keeps_some(
    ~Ledgers.Entry<Basics.Ask>,
    ~Ledgers.Entry.is_eq(~Basics.Ask, ~Basics.Ask.is_eq),
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(a), k),
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(b), k)
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
      Basics.State.ledger(a),
      Basics.State.ledger(b),
      k
    )(g)
  )

# a node that took in a new request of e holds its slot
def Ask.held.new(
  +n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  +q: Basics.Ask,
  +em: {
    Ledgers.State.get(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    )
      == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(
      ~Basics.Ask,
      Basics.State.ledger(Voting.Node.ask.new(n, s, e, q)),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  +i = Basics.Envelope.of(e)
  +c = Basics.Ask.chain(i, q)
  +k = Ledgers.Slot.ask(i)
  +en = {Ledgers.Entry.Ask{i, Basics.Envelope.time(e), q}: Ledgers.Entry<Basics.Ask>}
  +l0 = Ledgers.State.put(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), k, en)
  +s0 = Basics.State.led(s, l0)
  +s1 = Sealing.Node.arrive(s0, i, q)
  %Equal.sym(
    Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), k),
    None{},
    em
  ): {
    Maybe.is_some(
      &2,
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(
          Voting.Node.step(
            n,
            Sealing.Node.arrive(
              Basics.State.led(
                s,
                Ledgers.State.add.of(
                  ~Basics.Ask,
                  ~Basics.Ask.is_eq,
                  Basics.State.ledger(s),
                  k,
                  en,
                  _
                )
              ),
              i,
              q
            ),
            c
          )
        ),
        k
      )
    )
      == True{}: Bool
  }
  Slot.held_kept(
    s0,
    Voting.Node.step(n, s1, c),
    k,
    ProofTrees.Grows.trans(
      s0,
      s1,
      Voting.Node.step(n, s1, c)
    )(ProofTrees.Arrive.grows(s0, i, q))(ProofTrees.Step.grows(n, s1, c))
  )(
    %Equal.sym(Ledgers.State(Basics.Ask), Basics.State.ledger(s0), l0, ProofTrees.Led.led(s, l0)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, Ledgers.State.get(~Basics.Ask, _, k)) == True{}: Bool}
    %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, l0, k), Some{Cells.One{en}}, Ledgers.State.put_get(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), k, en)(em)): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _) == True{}: Bool}
    {==})

# a node that took in the request of e holds its slot, once the cell m of the
# slot before is known
def Ask.held.at(
  n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  em: {
    Ledgers.State.get(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    )
      == m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
  }
) -> {
  Maybe.is_some(
    &2,
    Cells.Cell<Ledgers.Entry<Basics.Ask>>,
    Ledgers.State.get(
      ~Basics.Ask,
      Basics.State.ledger(Voting.Node.ask.at(n, s, e, q, m)),
      Ledgers.Slot.ask(Basics.Envelope.of(e))
    )
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      %Equal.sym(
        Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
        Ledgers.State.get(
          ~Basics.Ask,
          Basics.State.ledger(s),
          Ledgers.Slot.ask(Basics.Envelope.of(e))
        ),
        Some{x},
        em
      ): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _) == True{}: Bool}
      {==}
    case None{}:
      Ask.held.new(
        n,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
        e,
        q,
        (
          %Equal.sym(Ledgers.State(Basics.Ask), Basics.State.ledger(Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e)))), Basics.State.ledger(s), ProofTrees.Led.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e)))): {Ledgers.State.get(~Basics.Ask, _, Ledgers.Slot.ask(Basics.Envelope.of(e))) == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
          em)
      )

# a request whose slot holds a cell changes nothing
def Ask.once.at(
  m: String,
  s: Basics.Node,
  e: Basics.Envelope,
  q: Basics.Ask,
  c: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> {
  Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, c) == True{}: Bool
} -> {Voting.Node.ask.at(m, s, e, q, c) == s: Basics.Node}:
  match c:
    case Some{x}:
      h => {==}
    case None{}:
      h => Empty.absurd(
        {Voting.Node.ask.at(m, s, e, q, None{}) == s: Basics.Node},
        Shared.Bool.false_ne_true(h)
      )

def Spec.Node.ask_once(n, m, s, e, q, e2, q2):
  h =>
    +a = Voting.Node.ask(n, s, e, q)
    Ask.once.at(
      m,
      a,
      e2,
      q2,
      Ledgers.State.get(
        ~Basics.Ask,
        Basics.State.ledger(a),
        Ledgers.Slot.ask(Basics.Envelope.of(e2))
      )
    )(
      %Equal.sym(Ledgers.Id, Basics.Envelope.of(e2), Basics.Envelope.of(e), h): {Maybe.is_some(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, Ledgers.State.get(~Basics.Ask, Basics.State.ledger(a), Ledgers.Slot.ask(_))) == True{}: Bool}
      Ask.held.at(n, s, e, q, Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.ask(Basics.Envelope.of(e))), {==}))

# Logs
# ----
# A log only gains keys: a key that a log holds, other than the owners and the
# count, holds the same value after any step.

# a read of a tree stays in a node that grew
def Get.grows(
  +a: Basics.Node,
  +b: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Basics.Node.get(a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Node.get(b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Equal.trans(
    Maybe<&2, List<&2, U32>>,
    Basics.Node.get(b, h, k),
    Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, b, h, k),
    Some{v},
    ProofTrees.Get.is(b, h, k),
    Trees.Tree.get_grows(
      ~Basics.Node,
      ~Basics.Store.fetch,
      ~Reading.Node.grows,
      ~(
        x => y => hh => w => Ledgers.State.data_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~ProofTrees.Ask.laws(),
          Basics.State.ledger(x),
          Basics.State.ledger(y),
          hh,
          w
        )
      ),
      a,
      b,
      h,
      k,
      v
    )(
      g
    )(
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, a, h, k),
        Basics.Node.get(a, h, k),
        Some{v},
        Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(a, h, k),
          Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, a, h, k),
          ProofTrees.Get.is(a, h, k)
        ),
        e
      )
    )
  )

# Set.kept once whether the node holds the new nodes is known (b)
def Set.kept.if(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +k2: List<&2, U32>,
  v: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {
    Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ws), ws) == b: Bool
  },
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Basics.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>},
  em: {Basics.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Spec.Work.Reads(
  k2,
  v,
  Judging.Work.put(
    Shared.Maybe.when(Basics.Node, b, u => Some{Basics.State.keep(s, ws)}),
    Some{hh},
    ws,
    ns
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      +sk = Basics.State.keep(s, ws)
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Basics.Node.get(sk, Some{hh}, k2),
        Basics.Node.get(sk, h, k2),
        Some{v},
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(sk, Some{hh}, k2),
          Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, sk, Some{hh}, k2),
          Basics.Node.get(sk, h, k2),
          ProofTrees.Get.is(sk, Some{hh}, k2),
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, sk, Some{hh}, k2),
            Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, sk, h, k2),
            Basics.Node.get(sk, h, k2),
            Trees.Tree.get_other(
              ~Basics.Node,
              ~Basics.Store.fetch,
              ~Reading.Node.grows,
              ~(
                p => q => g => w => Ledgers.State.data_grows(
                  ~Basics.Ask,
                  ~Basics.Ask.is_eq,
                  ~ProofTrees.Ask.laws(),
                  Basics.State.ledger(p),
                  Basics.State.ledger(q),
                  g,
                  w
                )
              ),
              s,
              sk,
              h,
              k,
              x,
              Trees.Put{hh, ws},
              k2
            )(
              ProofTrees.Grows.keep(s, ws)
            )(
              hne
            )(
              Equal.trans(
                Maybe<&2, Trees.Put>,
                Trees.Tree.set(~Basics.Node, ~Basics.Store.fetch, s, h, k, x),
                Basics.Node.set(s, h, k, x),
                Some{Trees.Put{hh, ws}},
                Equal.sym(
                  Maybe<&2, Trees.Put>,
                  Basics.Node.set(s, h, k, x),
                  Trees.Tree.set(~Basics.Node, ~Basics.Store.fetch, s, h, k, x),
                  ProofTrees.Set.is(s, h, k, x)
                ),
                em
              )
            )(eb),
            Equal.sym(
              Maybe<&2, List<&2, U32>>,
              Basics.Node.get(sk, h, k2),
              Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, sk, h, k2),
              ProofTrees.Get.is(sk, h, k2)
            )
          )
        ),
        Get.grows(s, sk, h, k2, v, ProofTrees.Grows.keep(s, ws))(hget)
      )

# Set.kept once the new subtree m is known
def Set.kept.of(
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  em: {Basics.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>},
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Basics.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(k2, v, Judging.Work.of(s, ns, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, +ws}}:
      Set.kept.if(
        s,
        h,
        ns,
        k,
        x,
        k2,
        v,
        hh,
        ws,
        Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ws), ws),
        {==},
        hne,
        hget,
        em
      )

# a key set in a tree keeps the value of each other key
def Set.kept(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool},
  hget: {Basics.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(k2, v, Judging.Work.set(Judging.Work{s, h, ns}, k, x)):
  Set.kept.of(s, h, ns, k, x, k2, v, Basics.Node.set(s, h, k, x), {==}, hne, hget)

# that the log of the run m, if any, reads the key k2 as v
def Run.Keeps(k2: List<&2, U32>, v: List<&2, U32>, m: Maybe<&2, Stepping.Run>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{Stepping.Run{s2, t2, ns}}:
      {Basics.Node.get(s2, Basics.Tip.log(t2), k2) == Some{v}: Maybe<&2, List<&2, U32>>}

# the run of a new log that keeps a key keeps it
def Run.of.keeps(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Judging.Work>
) -> Spec.Work.Reads(k2, v, m) -> Run.Keeps(k2, v, Stepping.Run.of(c, m)):
  match m:
    case None{}:
      w => Unit{}
    case Some{Judging.Work{s2, l, ns}}:
      w => w

# a key set in a run's log keeps the value of each other key
def Log.kept(
  r: Stepping.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Run.log(r, k, x)):
  match r:
    case Stepping.Run{+s, Basics.Tip{c, +l}, +ns}:
      hr => Run.of.keeps(
        k2,
        v,
        c,
        Judging.Work.set(Judging.Work{s, l, ns}, k, x)
      )(Set.kept(s, l, ns, k, x, k2, v, hne, hr))

# a key that a tree does not hold is not a key that it holds, once whether
# they are the same is known (b)
def Keys.differ.if(
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == b: Bool},
  e1: {Basics.Node.get(s, h, k) == None{}: Maybe<&2, List<&2, U32>>},
  e2: {Basics.Node.get(s, h, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Maybe.none_ne_some(
          List<&2, U32>,
          v,
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            None{},
            Basics.Node.get(s, h, k),
            Some{v},
            Equal.sym(Maybe<&2, List<&2, U32>>, Basics.Node.get(s, h, k), None{}, e1),
            (
              %Equal.sym(List<&2, U32>, k, k2, Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), k, k2)(eb)): {Basics.Node.get(s, h, _) == Some{v}: Maybe<&2, List<&2, U32>>}
              e2)
          )
        )
      )

# Add.kept when the log does not hold the new key
def Add.new.kept(
  +s: Basics.Node,
  c: Maybe<&2, Hashes.Hash>,
  +l: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  em: {Basics.Node.get(s, l, k) == None{}: Maybe<&2, List<&2, U32>>},
  +hr: {Basics.Node.get(s, l, k2) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Run.Keeps(k2, v, Stepping.Run.log(Stepping.Run{s, Basics.Tip{c, l}, ns}, k, x)):
  Log.kept(
    Stepping.Run{s, Basics.Tip{c, l}, ns},
    k,
    x,
    k2,
    v,
    Keys.differ.if(s, l, k, k2, v, Shared.List.is_eq(~U32, ~U32.is_eq, k, k2), {==}, em, hr)
  )(hr)

# Add.kept once the value m of the new key is known
def Add.at.kept(
  r: Stepping.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Basics.Node.get(
    Stepping.Run.state(r),
    Basics.Tip.log(Stepping.Run.tip(r)),
    k
  )
    == m: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Run.add.at(r, k, x, m)):
  match r m:
    case Stepping.Run{s, Basics.Tip{c, l}, ns} Some{old}:
      em => hr => Unit{}
    case Stepping.Run{+s, Basics.Tip{+c, +l}, +ns} None{}:
      em => hr => Add.new.kept(s, c, l, ns, k, x, k2, v, em, hr)

# a new key in a run's log keeps the value of each key that the log holds
def Add.kept(
  +r: Stepping.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Run.add(r, k, x)):
  Add.at.kept(
    r,
    k,
    x,
    k2,
    v,
    Basics.Node.get(Stepping.Run.state(r), Basics.Tip.log(Stepping.Run.tip(r)), k)
  )({==})

# a run, then a run from it that keeps a key, keeps it
def Keeps.bind(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Stepping.Run>,
  -f: Stepping.Run -> Maybe<&2, Stepping.Run>
) -> Run.Keeps(
  k2,
  v,
  m
) -> (
  @r: Stepping.Run -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, f(r))
) -> Run.Keeps(k2, v, Maybe.bind(&2, Stepping.Run, Stepping.Run, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{r}:
      hm => hf => hf(r)(hm)

# one of two runs, each of which keeps a key that the run r keeps
def Keeps.when(
  -k2: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Stepping.Run,
  b: Bool,
  -mx: Maybe<&2, Stepping.Run>,
  -my: Maybe<&2, Stepping.Run>,
  hx: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, mx),
  hy: Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, my)
) -> Run.Keeps(
  k2,
  v,
  Some{r}
) -> Run.Keeps(k2, v, Shared.Bool.when(Maybe<&2, Stepping.Run>, b, u => mx, u => my)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new owners keep each other key of a run's log
def Owners.kept(
  r: Stepping.Run,
  m: Maybe<&2, List<&2, String>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Run.owners(r, m)):
  match m:
    case None{}:
      hr => hr
    case Some{os}:
      hr => Log.kept(r, Basics.Log.owners(), Ledgers.Owners.code(os, []), k2, v, n0)(hr)

# a taken request keeps each key of a run's log, other than the owners and
# the count
def Taken.kept(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.taken(r, i, own)):
  +n = Basics.Line.count(Stepping.Run.state(r), Stepping.Run.tip(r))
  hr => Keeps.bind(
    k2,
    v,
    Stepping.Run.add(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n})),
    +r1 => Maybe.bind(
      &2,
      Stepping.Run,
      Stepping.Run,
      Stepping.Run.add(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))})
      ),
      r2 => Maybe.bind(
        &2,
        Stepping.Run,
        Stepping.Run,
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own)
      )
    )
  )(
    Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n}), k2, v)(hr)
  )(
    +r1 => h1 => Keeps.bind(
      k2,
      v,
      Stepping.Run.add(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))})
      ),
      r2 => Maybe.bind(
        &2,
        Stepping.Run,
        Stepping.Run,
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own)
      )
    )(
      Add.kept(
        r1,
        Basics.Log.version(n),
        Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))}),
        k2,
        v
      )(h1)
    )(
      +r2 => h2 => Keeps.bind(
        k2,
        v,
        Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
        r3 => Stepping.Run.owners(r3, own)
      )(
        Log.kept(r2, Basics.Log.count(), [U32.inc(n)], k2, v, n1)(h2)
      )(r3 => h3 => Owners.kept(r3, own, k2, v, n0)(h3))
    )
  )

# a run over a node that grew keeps each key of its log
def Over.kept(
  r: Stepping.Run,
  s2: Basics.Node,
  -h: Maybe<&2, Hashes.Hash>,
  -ds: List<&2, List<&2, U32>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  g: {Reading.Node.grows(Stepping.Run.state(r), s2) == True{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Some{Stepping.Run.over(r, s2, h, ds)}):
  match r:
    case Stepping.Run{s, t, ns}:
      hr => Get.grows(s, s2, Basics.Tip.log(t), k2, v, g)(hr)

# a judged request keeps each key of a run's log, other than the owners and
# the count
def Judged.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  m: Maybe<&2, Basics.Verdict>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> {
  ProofTrees.Verdict.after(Stepping.Run.state(r), m) == True{}: Bool
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.judged(r, i, own, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Basics.Verdict.Stale{}}:
      g => hr => Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)(hr)
    case Some{Basics.Verdict.Taken{h, ds, +s2}}:
      g => hr => Taken.kept(
        Stepping.Run.over(r, s2, h, ds),
        i,
        own,
        k2,
        v,
        n0,
        n1
      )(Over.kept(r, s2, h, ds, k2, v, g)(hr))

# a mark on a version keeps each key of a run's log, other than the owners
# and the count
def Marked.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +m: String,
  x: Maybe<&2, Basics.Version>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.marked(r, i, m, x)):
  match x:
    case None{}:
      hr => Unit{}
    case Some{+y}:
      hr => Keeps.bind(
        k2,
        v,
        Stepping.Run.add(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(y), [])),
        r2 => Stepping.Step.taken(r2, i, None{})
      )(
        Add.kept(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(y), []), k2, v)(hr)
      )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v, n0, n1)(h2))

# a request for a mark keeps each key of a run's log, other than the owners
# and the count
def Mark.kept(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +m: String,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.mark(r, i, m)):
  +s = Stepping.Run.state(r)
  +t = Stepping.Run.tip(r)
  +n = Basics.Line.count(s, t)
  Keeps.when(
    k2,
    v,
    r,
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Basics.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Stepping.Step.marked(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    Stepping.Step.stale(r, i),
    Marked.kept(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1)), k2, v, n0, n1),
    Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)
  )

# the first tip of a new branch keeps each key of a run's log, other than the
# owners and the count
def Branch.made.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +b: String,
  m: Maybe<&2, Judging.Made>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> {
  ProofTrees.Made.after(Stepping.Run.state(r), m) == True{}: Bool
} -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Branch.made(r, i, b, m)):
  match m:
    case None{}:
      g => hr => Unit{}
    case Some{Judging.Made{+t, ds, +s2}}:
      g => hr =>
        +r1 = {Stepping.Run.over(r, s2, Basics.Tip.content(Stepping.Run.tip(r)), ds): Stepping.Run}
        Keeps.bind(
          k2,
          v,
          Stepping.Run.add(r1, Basics.Log.start(b), Hashes.Hash.code(Basics.Tip.hash(t), [])),
          r2 => Stepping.Step.taken(r2, i, None{})
        )(
          Add.kept(
            r1,
            Basics.Log.start(b),
            Hashes.Hash.code(Basics.Tip.hash(t), []),
            k2,
            v
          )(Over.kept(r, s2, Basics.Tip.content(Stepping.Run.tip(r)), ds, k2, v, g)(hr))
        )(r2 => h2 => Taken.kept(r2, i, None{}, k2, v, n0, n1)(h2))

# a request for a branch keeps each key of a run's log, other than the owners
# and the count, once it is known whether its version is one
def Branch.ready.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Bool>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Branch.ready(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{False{}}:
      Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)
    case Some{True{}}:
      Keeps.when(
        k2,
        v,
        r,
        Trees.Tree.whole(
          ~Basics.Node,
          ~Basics.Store.fetch,
          Stepping.Run.state(r),
          Basics.Node.root_of(Stepping.Run.state(r), at)
        ),
        Stepping.Branch.made(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          )
        ),
        None{},
        Branch.made.kept(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          ),
          k2,
          v,
          n0,
          n1
        )(
          ProofTrees.Grown.make.first(
            Stepping.Run.state(r),
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          )(ProofTrees.Grown.make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at))
        ),
        hr => Unit{}
      )

# a request for a branch keeps each key of a run's log, other than the owners
# and the count
def Branch.new.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Branch.new(r, i, st, b, at, m)):
  match m:
    case None{}:
      hr => Unit{}
    case Some{Some{x}}:
      Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)
    case Some{None{}}:
      Branch.ready.kept(
        r,
        i,
        st,
        b,
        at,
        Judging.Judge.ready_maybe(Stepping.Run.state(r), at),
        k2,
        v,
        n0,
        n1
      )

# On.kept once it is known how the line takes the change (w)
def On.of.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.on.of(r, i, st, l, ch, w)):
  match w:
    case Stepping.Route.Mark{a}:
      hr => Mark.kept(r, i, a, k2, v, n0, n1)(hr)
    case Stepping.Route.Branch{+a, b}:
      Branch.new.kept(
        r,
        i,
        st,
        a,
        b,
        Basics.Node.find(
          Stepping.Run.state(r),
          Basics.Tip.log(Stepping.Run.tip(r)),
          Basics.Log.start(a)
        ),
        k2,
        v,
        n0,
        n1
      )
    case Stepping.Route.Judge{}:
      hr => Judged.kept(
        r,
        i,
        Basics.Change.owners(ch),
        Judging.Judge.change(
          Stepping.Run.state(r),
          st,
          l,
          ch,
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        ),
        k2,
        v,
        n0,
        n1
      )(
        ProofTrees.Verdict.change(
          Stepping.Run.state(r),
          st,
          l,
          ch,
          Basics.Tip.content(Stepping.Run.tip(r)),
          Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
        )
      )(hr)

# a change of a line keeps each key of a run's log, other than the owners and
# the count
def On.kept(
  +r: Stepping.Run,
  i: Ledgers.Id,
  +st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.on(r, i, st, l, ch)):
  On.of.kept(r, i, st, l, ch, Stepping.Route.of(l, ch), k2, v, n0, n1)

# a request keeps each key of a run's log, other than the owners and the count
def Change.kept(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  q: Basics.Ask,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.change(r, c, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      hr => Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)(hr)
    case Basics.Ask.On{+st, +l, ch}:
      Keeps.when(
        k2,
        v,
        r,
        Ledgers.Chain.is_eq(Basics.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Stepping.Step.stale(r, i),
        On.kept(r, i, st, l, ch, k2, v, n0, n1),
        Add.kept(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}), k2, v)
      )

# a request that the node holds or not keeps each key of a run's log
def Asked.kept(
  r: Stepping.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  a: Maybe<&2, Ledgers.Asked<Basics.Ask>>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.asked(r, c, i, a)):
  match a:
    case None{}:
      hr => Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.kept(r, c, i, q, k2, v, n0, n1)

# a request that the log holds or not keeps each key of a run's log
def Fresh.kept(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  o: Maybe<&2, Basics.Out>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, Some{r}) -> Run.Keeps(k2, v, Stepping.Step.fresh(r, c, i, o)):
  match o:
    case Some{x}:
      hr => hr
    case None{}:
      Asked.kept(r, c, i, Basics.Node.asked(Stepping.Run.state(r), i), k2, v, n0, n1)

# the requests of a step keep each key of a run's log, other than the owners
# and the count
def All.kept(
  +c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Stepping.Run>,
  +k2: List<&2, U32>,
  +v: List<&2, U32>,
  +n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  +n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> Run.Keeps(k2, v, m) -> Run.Keeps(k2, v, Stepping.Step.all(c, qs, m)):
  match qs:
    case Nil{}:
      h => h
    case Con{+i, rest}:
      h => All.kept(
        c,
        rest,
        Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, i)),
        k2,
        v,
        n0,
        n1
      )(
        Keeps.bind(
          k2,
          v,
          m,
          r => Stepping.Step.one(r, c, i)
        )(
          h
        )(
          +r => hr => Fresh.kept(
            r,
            c,
            i,
            Basics.Line.out(Stepping.Run.state(r), Stepping.Run.tip(r), i),
            k2,
            v,
            n0,
            n1
          )(hr)
        )
      )

# a log only gains keys: a key that the log of a tip holds, other than the
# owners and the count, holds the same value after a step
def Run.kept(
  s: Basics.Node,
  c: Ledgers.Chain,
  t: Basics.Tip,
  qs: List<&2, Ledgers.Id>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  n0: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k2) == False{}: Bool},
  n1: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k2) == False{}: Bool}
) -> {
  Basics.Node.get(s, Basics.Tip.log(t), k2) == Some{v}: Maybe<&2, List<&2, U32>>
} -> Run.Keeps(k2, v, Stepping.Step.run(s, c, t, qs)):
  match t:
    case Basics.Tip{c0, l}:
      h => All.kept(c, qs, Some{Stepping.Run{s, Basics.Tip{c0, l}, []}}, k2, v, n0, n1)(h)
