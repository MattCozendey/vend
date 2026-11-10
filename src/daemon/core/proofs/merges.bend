# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/formats.bend as Formats
import ../../shared/ledger.bend as Ledgers
import ../../shared/resources.bend as Resources
import ../../shared/rope.bend as Ropes
import ../../shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/shared/text.bend as Texts
import ../../shared/tree.bend as Trees
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../stepping.bend as Stepping
import ../voting.bend as Voting
import ./logs.bend as ProofLogs
import ./trees.bend as ProofTrees

# Moves
# -----
# A move sets only keys of the version vector, so each resource of its target
# reads the same after it (Spec.Move.reads).

# the key of a resource is not the key of a line in the version vector
def Vector.apart(
  c: Ledgers.Chain,
  n: Resources.Name
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.vector(c), Basics.Key.res(n)) == False{}: Bool
}:
  {==}

# Vector.add keeps a resource, once it is known whether the vector covers the
# place (b)
def Vector.add.reads.if(
  s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +c: Ledgers.Chain,
  p: Basics.Place,
  +n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: {Basics.Node.get(s, h, Basics.Key.res(n)) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Judging.Work>,
    b,
    u => Some{Judging.Work{s, h, ns}},
    u => Judging.Work.set(Judging.Work{s, h, ns}, Basics.Key.vector(c), Basics.Place.code(p))
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      ProofLogs.Set.kept(
        s,
        h,
        ns,
        Basics.Key.vector(c),
        Basics.Place.code(p),
        Basics.Key.res(n),
        v,
        Vector.apart(c, n),
        hget
      )

# a new entry of the version vector keeps a resource
def Vector.add.reads(
  w: Judging.Work,
  +c: Ledgers.Chain,
  +p: Basics.Place,
  n: Resources.Name,
  v: List<&2, U32>
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Basics.Key.res(n), v, Judging.Vector.add(w, c, p)):
  match w:
    case Judging.Work{+s, +h, ns}:
      hget => Vector.add.reads.if(
        s,
        h,
        ns,
        c,
        p,
        n,
        v,
        Basics.Place.covered(Basics.Node.vector(s, h, c), p),
        hget
      )

# Vector.add.if keeps a resource, once it is known whether the place is of
# the line (b)
def Vector.add.if.reads.at(
  w: Judging.Work,
  +p: Basics.Place,
  n: Resources.Name,
  v: List<&2, U32>,
  b: Bool,
  hget: Spec.Work.Reads(Basics.Key.res(n), v, Some{w})
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Shared.Bool.when(
    Maybe<&2, Judging.Work>,
    b,
    u => Some{w},
    u => Judging.Vector.add(w, Basics.Place.chain(p), p)
  )
):
  match b:
    case True{}:
      hget
    case False{}:
      Vector.add.reads(w, Basics.Place.chain(p), p, n, v)(hget)

# an entry of the version vector, if any, keeps a resource
def Vector.add.if.reads(
  w: Judging.Work,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Place>,
  n: Resources.Name,
  v: List<&2, U32>
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Basics.Key.res(n), v, Judging.Vector.add.if(w, c, m)):
  match m:
    case None{}:
      hget => hget
    case Some{+p}:
      hget => Vector.add.if.reads.at(
        w,
        p,
        n,
        v,
        Ledgers.Chain.is_eq(Basics.Place.chain(p), c),
        hget
      )

# a work that reads a key, after a step that keeps the read
def Reads.bind(
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  m: Maybe<&2, Judging.Work>,
  -f: Judging.Work -> Maybe<&2, Judging.Work>
) -> Spec.Work.Reads(
  k,
  v,
  m
) -> (
  @w: Judging.Work -> Spec.Work.Reads(k, v, Some{w}) -> Spec.Work.Reads(k, v, f(w))
) -> Spec.Work.Reads(k, v, Maybe.bind(&2, Judging.Work, Judging.Work, m, f)):
  match m:
    case None{}:
      hm => hf => Unit{}
    case Some{w}:
      hm => hf => hf(w)(hm)

# the entries of some bindings keep a resource
def Vector.adds.reads(
  bs: List<&2, Trees.Binding>,
  +c: Ledgers.Chain,
  +m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  m
) -> Spec.Work.Reads(Basics.Key.res(n), v, Judging.Vector.adds(bs, c, m)):
  match bs:
    case Nil{}:
      hm => hm
    case Con{+b, r}:
      hm => Vector.adds.reads(
        r,
        c,
        Maybe.bind(
          &2,
          Judging.Work,
          Judging.Work,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b))
        ),
        n,
        v
      )(
        Reads.bind(
          Basics.Key.res(n),
          v,
          m,
          w => Judging.Vector.add.if(w, c, Judging.Vector.entry(b))
        )(hm)(+w => hw => Vector.add.if.reads(w, c, Judging.Vector.entry(b), n, v)(hw))
      )

# the version vector of a version, joined in, keeps a resource
def Vector.joined.reads(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  +v: List<&2, U32>
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  m
) -> Spec.Work.Reads(Basics.Key.res(n), v, Judging.Vector.joined(s, c, x, m)):
  hm => Reads.bind(
    Basics.Key.res(n),
    v,
    Judging.Vector.adds(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, Basics.Node.root_of(s, Some{x})),
      c,
      m
    ),
    w => Judging.Vector.add.if(w, c, Basics.Node.place(s, x))
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, Basics.Node.root_of(s, Some{x})),
      c,
      m,
      n,
      v
    )(hm)
  )(+w => hw => Vector.add.if.reads(w, c, Basics.Node.place(s, x), n, v)(hw))

def Spec.Move.reads(s, c, to, h, n, v):
  hget => Vector.joined.reads(
    s,
    c,
    to,
    Judging.Vector.adds(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, h),
      c,
      Some{Judging.Work{s, Basics.Node.root_of(s, Some{to}), []}}
    ),
    n,
    v
  )(
    Vector.adds.reads(
      Trees.Tree.list(~Basics.Node, ~Basics.Store.fetch, s, h),
      c,
      Some{Judging.Work{s, Basics.Node.root_of(s, Some{to}), []}},
      n,
      v
    )(hget)
  )

# Whole merges
# ------------
# A merge sets the key of each resource that it merges. A set of another key
# keeps what a key reads, so what the merge of one resource takes is what the
# whole merge gives for it (Spec.Merge.keeps).

# the words after the first one
def Words.rest(ws: List<&2, U32>) -> List<&2, U32>:
  match ws:
    case Nil{}:
      []
    case Con{w, r}:
      r

# the text that a read gave, "" without one
def Read.text(m: Maybe<&2, Codes.Read<String>>) -> String:
  match m:
    case Some{Codes.Read{t, r}}:
      t
    case None{}:
      ""

# texts with the same code are the same
def Text.same(
  t1: String,
  t2: String,
  e: {Codes.Code.text(t1, []) == Codes.Code.text(t2, []): List<&2, U32>}
) -> {t1 == t2: String}:
  Equal.trans(
    String,
    t1,
    Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
    t2,
    Equal.sym(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      t1,
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t1, [])),
        Some{Codes.Read{t1, []}},
        Codes.Code.text_read(t1, [])
      )
    ),
    Equal.trans(
      String,
      Read.text(Codes.Code.text.read(Codes.Code.text(t1, []))),
      Read.text(Codes.Code.text.read(Codes.Code.text(t2, []))),
      t2,
      Equal.cong(
        List<&2, U32>,
        String,
        ws => Read.text(Codes.Code.text.read(ws)),
        Codes.Code.text(t1, []),
        Codes.Code.text(t2, []),
        e
      ),
      Equal.cong(
        Maybe<&2, Codes.Read<String>>,
        String,
        Read.text,
        Codes.Code.text.read(Codes.Code.text(t2, [])),
        Some{Codes.Read{t2, []}},
        Codes.Code.text_read(t2, [])
      )
    )
  )

# Res.apart once it is known whether the keys are the same (b)
def Res.apart.at(
  +t1: String,
  +t2: String,
  +b: Bool,
  eb: {
    Shared.List.is_eq(
      ~U32,
      ~U32.is_eq,
      Basics.Key.res(Resources.Name{t1}),
      Basics.Key.res(Resources.Name{t2})
    )
      == b: Bool
  },
  hf: {String.eq(t1, t2) == False{}: Bool}
) -> {b == False{}: Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      Empty.absurd(
        {True{} == False{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            String.eq(t1, t2),
            True{},
            Equal.sym(Bool, String.eq(t1, t2), False{}, hf),
            Equal.trans(
              Bool,
              String.eq(t1, t2),
              String.eq(t2, t2),
              True{},
              Equal.cong(
                String,
                Bool,
                z => String.eq(z, t2),
                t1,
                t2,
                Text.same(
                  t1,
                  t2,
                  Equal.cong(
                    List<&2, U32>,
                    List<&2, U32>,
                    Words.rest,
                    Basics.Key.res(Resources.Name{t1}),
                    Basics.Key.res(Resources.Name{t2}),
                    Shared.List.is_eq_sound(
                      ~U32,
                      ~U32.is_eq,
                      ~Shared.U32.laws(),
                      Basics.Key.res(Resources.Name{t1}),
                      Basics.Key.res(Resources.Name{t2})
                    )(eb)
                  )
                )
              ),
              Texts.String.eq_refl(t2)
            )
          )
        )
      )

# resources that are not the same have keys that are not the same
def Res.apart(
  +m: Resources.Name,
  +n: Resources.Name
) -> {
  Resources.Name.is_eq(m, n) == False{}: Bool
} -> {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      hf => Res.apart.at(
        t1,
        t2,
        Shared.List.is_eq(
          ~U32,
          ~U32.is_eq,
          Basics.Key.res(Resources.Name{t1}),
          Basics.Key.res(Resources.Name{t2})
        ),
        {==},
        hf
      )

# resources that are the same are equal
def Name.sound(
  +m: Resources.Name,
  +n: Resources.Name
) -> {Resources.Name.is_eq(m, n) == True{}: Bool} -> {m == n: Resources.Name}:
  match m n:
    case Resources.Name{t1} Resources.Name{t2}:
      e => Equal.cong(
        String,
        Resources.Name,
        z => Resources.Name{z},
        t1,
        t2,
        Texts.String.eq_sound(t1, t2)(e)
      )

# the key of a clash is not the key of a resource
def Clash.apart(
  m: Resources.Name,
  n: Resources.Name
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.clash(m), Basics.Key.res(n)) == False{}: Bool}:
  {==}

# a work that reads a key, after a read that gives the next step
def Reads.with(
  -A: Data,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  +ma: Maybe<&2, A>,
  -f: A -> Maybe<&2, Judging.Work>
) -> (
  @a: A -> Spec.Work.Reads(k, v, f(a))
) -> Spec.Work.Reads(k, v, Maybe.bind(&2, A, Judging.Work, ma, f)):
  match ma:
    case None{}:
      hf => Unit{}
    case Some{a}:
      hf => hf(a)

# a set of another key keeps what a work reads
def Set.kept.work(
  +w: Judging.Work,
  k: List<&2, U32>,
  x: List<&2, U32>,
  k2: List<&2, U32>,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, k, k2) == False{}: Bool}
) -> Spec.Work.Reads(k2, v, Some{w}) -> Spec.Work.Reads(k2, v, Judging.Work.set(w, k, x)):
  match w:
    case Judging.Work{s, h, ns}:
      hget => ProofLogs.Set.kept(s, h, ns, k, x, k2, v, hne, hget)

# Keep.reads once it is known whether the node holds the new data (b)
def Keep.reads.if(
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  old: List<&2, List<&2, U32>>,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +b: Bool,
  hget: {Basics.Node.get(s, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Work.Reads(
  k,
  v,
  Judging.Work.put(
    Shared.Maybe.when(Basics.Node, b, u => Some{Basics.State.keep(s, ns)}),
    h,
    ns,
    old
  )
):
  match b:
    case False{}:
      Unit{}
    case True{}:
      ProofLogs.Get.grows(s, Basics.State.keep(s, ns), h, k, v, ProofTrees.Grows.keep(s, ns))(hget)

# new data keeps what a work reads
def Keep.reads(
  +w: Judging.Work,
  +ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> Spec.Work.Reads(k, v, Some{w}) -> Spec.Work.Reads(k, v, Judging.Work.keep(w, ns)):
  match w:
    case Judging.Work{s, h, old}:
      hget => Keep.reads.if(
        s,
        h,
        old,
        ns,
        k,
        v,
        Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ns), ns),
        hget
      )

# Set.read once it is known whether the node holds the new nodes (b)
def Set.read.if(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  +ws: List<&2, List<&2, U32>>,
  +b: Bool,
  eb: {
    Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ws), ws) == b: Bool
  },
  em: {Basics.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>}
) -> Spec.Work.Reads(
  k,
  x,
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
      Equal.trans(
        Maybe<&2, List<&2, U32>>,
        Basics.Node.get(Basics.State.keep(s, ws), Some{hh}, k),
        Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ws), Some{hh}, k),
        Some{x},
        ProofTrees.Get.is(Basics.State.keep(s, ws), Some{hh}, k),
        Trees.Tree.get_set(
          ~Basics.Node,
          ~Basics.Store.fetch,
          s,
          Basics.State.keep(s, ws),
          h,
          k,
          x,
          Trees.Put{hh, ws}
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
        )(eb)
      )

# Set.read once the new subtree m is known
def Set.read.of(
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  ns: List<&2, List<&2, U32>>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  +m: Maybe<&2, Trees.Put>,
  em: {Basics.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>}
) -> Spec.Work.Reads(k, x, Judging.Work.of(s, ns, m)):
  match m:
    case None{}:
      Unit{}
    case Some{Trees.Put{hh, ws}}:
      Set.read.if(
        s,
        h,
        ns,
        k,
        x,
        hh,
        ws,
        Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s, ws), ws),
        {==},
        em
      )

# a key that a work sets, it reads
def Set.read(
  +w: Judging.Work,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> Spec.Work.Reads(k, x, Judging.Work.set(w, k, x)):
  match w:
    case Judging.Work{s, h, ns}:
      Set.read.of(s, h, ns, k, x, Basics.Node.set(s, h, k, x), {==})

# the merge of one resource m, of the trees hb (base), ho (ours) and ht
# (theirs), on the work w: one step of Spec.Merge.all
def Merge.step(
  +s: Basics.Node,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  w: Judging.Work
) -> Maybe<&2, Judging.Work>:
  Maybe.bind(
    &2,
    Maybe<&2, Ropes.Root>,
    Judging.Work,
    Basics.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Judging.Work,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Judging.Work,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )

# what the merge of another resource puts keeps what a work reads for n
def Merge.put.other(
  f: Ledgers.Id,
  +m: Resources.Name,
  +n: Resources.Name,
  +o2: Maybe<&2, Ropes.Root>,
  +p: Judging.Pick,
  +w: Judging.Work,
  +v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Basics.Key.res(n), v, Judging.Merge.put(f, m, o2, p, w)):
  match p:
    case Judging.Pick.Take{mm}:
      Set.kept.work(w, Basics.Key.res(m), Basics.Res.code(mm), Basics.Key.res(n), v, hne)
    case Judging.Pick.Make{y}:
      hget => Reads.bind(
        Basics.Key.res(n),
        v,
        Judging.Work.keep(w, Ropes.Put.nodes(Basics.Bytes.rope(y))),
        w2 => Judging.Work.set(
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(y))})
        )
      )(
        Keep.reads(w, Ropes.Put.nodes(Basics.Bytes.rope(y)), Basics.Key.res(n), v)(hget)
      )(
        w2 => hw => Set.kept.work(
          w2,
          Basics.Key.res(m),
          Basics.Res.code(Some{Ropes.Put.root(Basics.Bytes.rope(y))}),
          Basics.Key.res(n),
          v,
          hne
        )(hw)
      )
    case Judging.Pick.Clash{}:
      hget => Reads.bind(
        Basics.Key.res(n),
        v,
        Judging.Work.set(w, Basics.Key.res(m), Basics.Res.code(o2)),
        y => Judging.Work.set(y, Basics.Key.clash(m), Judging.Clash.code(f))
      )(
        Set.kept.work(w, Basics.Key.res(m), Basics.Res.code(o2), Basics.Key.res(n), v, hne)(hget)
      )(
        y => hy => Set.kept.work(
          y,
          Basics.Key.clash(m),
          Judging.Clash.code(f),
          Basics.Key.res(n),
          v,
          Clash.apart(m, n)
        )(hy)
      )

# the merge of another resource keeps what a work reads for n
def Merge.step.other(
  +s: Basics.Node,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Resources.Name,
  n: Resources.Name,
  w: Judging.Work,
  v: List<&2, U32>,
  hne: {Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Key.res(m), Basics.Key.res(n)) == False{}: Bool}
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  v,
  Some{w}
) -> Spec.Work.Reads(Basics.Key.res(n), v, Merge.step(s, f, hb, ho, ht, m, w)):
  hget => Reads.with(
    Maybe<&2, Ropes.Root>,
    Basics.Key.res(n),
    v,
    Basics.Res.find(s, hb, m),
    b => Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Judging.Work,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Judging.Work,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )
  )(
    b => Reads.with(
      Maybe<&2, Ropes.Root>,
      Basics.Key.res(n),
      v,
      Basics.Res.find(s, ho, m),
      o => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Judging.Work,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )
    )(
      +o => Reads.with(
        Maybe<&2, Ropes.Root>,
        Basics.Key.res(n),
        v,
        Basics.Res.find(s, ht, m),
        x => Judging.Merge.one(s, f, m, b, o, x, w)
      )(
        x => Reads.with(
          Judging.Pick,
          Basics.Key.res(n),
          v,
          Judging.Pick.merge(Formats.Format.of(Resources.Name.path(m)), s, b, o, x),
          p => Judging.Merge.put(f, m, o, p, w)
        )(p => Merge.put.other(f, m, n, o, p, w, v, hne)(hget))
      )
    )
  )

# the merge of the resource n gives what its pick takes
def Merge.step.same(
  s: Basics.Node,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  w: Judging.Work,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Spec.Work.Reads(Basics.Key.res(n), Basics.Res.code(x), Merge.step(s, f, hb, ho, ht, n, w)):
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, hb, n),
    Some{b},
    eb
  ): Spec.Work.Reads(
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Judging.Work,
      _,
      b1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Judging.Work,
        Basics.Res.find(s, ho, n),
        o1 => Maybe.bind(
          &2,
          Maybe<&2, Ropes.Root>,
          Judging.Work,
          Basics.Res.find(s, ht, n),
          x1 => Judging.Merge.one(s, f, n, b1, o1, x1, w)
        )
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, ho, n),
    Some{o},
    eo
  ): Spec.Work.Reads(
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Judging.Work,
      _,
      o1 => Maybe.bind(
        &2,
        Maybe<&2, Ropes.Root>,
        Judging.Work,
        Basics.Res.find(s, ht, n),
        x1 => Judging.Merge.one(s, f, n, b, o1, x1, w)
      )
    )
  )
  %Equal.sym(
    Maybe<&2, Maybe<&2, Ropes.Root>>,
    Basics.Res.find(s, ht, n),
    Some{t},
    et
  ): Spec.Work.Reads(
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(
      &2,
      Maybe<&2, Ropes.Root>,
      Judging.Work,
      _,
      x1 => Judging.Merge.one(s, f, n, b, o, x1, w)
    )
  )
  %Equal.sym(
    Maybe<&2, Judging.Pick>,
    Judging.Pick.merge(Formats.Format.of(Resources.Name.path(n)), s, b, o, t),
    Some{Judging.Pick.Take{x}},
    ep
  ): Spec.Work.Reads(
    Basics.Key.res(n),
    Basics.Res.code(x),
    Maybe.bind(&2, Judging.Pick, Judging.Work, _, p => Judging.Merge.put(f, n, o, p, w))
  )
  Set.read(w, Basics.Key.res(n), Basics.Res.code(x))

# Merge.step.same on the work m, if any
def Merge.step.takes(
  s: Basics.Node,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Judging.Work>,
  n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, n, w))
):
  match m:
    case None{}:
      Unit{}
    case Some{w}:
      Merge.step.same(s, f, hb, ho, ht, n, b, o, t, x, w, eb, eo, et, ep)

# one step of a merge keeps what the work reads for n, once it is known
# whether the step is of n (same)
def Merge.step.keeps(
  s: Basics.Node,
  f: Ledgers.Id,
  hb: Maybe<&2, Hashes.Hash>,
  ho: Maybe<&2, Hashes.Hash>,
  ht: Maybe<&2, Hashes.Hash>,
  +m1: Resources.Name,
  m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  b: Maybe<&2, Ropes.Root>,
  o: Maybe<&2, Ropes.Root>,
  t: Maybe<&2, Ropes.Root>,
  x: Maybe<&2, Ropes.Root>,
  eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool}
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  m
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
):
  match same:
    case True{}:
      hm =>
        %Equal.sym(
          Resources.Name,
          m1,
          n,
          Name.sound(m1, n)(es)
        ): Spec.Work.Reads(
          Basics.Key.res(n),
          Basics.Res.code(x),
          Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, _, w))
        )
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep)
    case False{}:
      hm => Reads.bind(
        Basics.Key.res(n),
        Basics.Res.code(x),
        m,
        w => Merge.step(s, f, hb, ho, ht, m1, w)
      )(
        hm
      )(
        w => hw => Merge.step.other(
          s,
          f,
          hb,
          ho,
          ht,
          m1,
          n,
          w,
          Basics.Res.code(x),
          Res.apart(m1, n)(es)
        )(hw)
      )

# the merge of more resources keeps what the work reads for n
def Merge.all.keeps(
  +s: Basics.Node,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  m
) -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(s, f, ns, hb, ho, ht, m)
):
  match ns:
    case Nil{}:
      hm => hm
    case Con{m1, r}:
      hm => Merge.all.keeps(
        s,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep
      )(
        Merge.step.keeps(
          s,
          f,
          hb,
          ho,
          ht,
          m1,
          m,
          n,
          b,
          o,
          t,
          x,
          eb,
          eo,
          et,
          ep,
          Resources.Name.is_eq(m1, n),
          {==}
        )(hm)
      )

# Merge.all.takes at the first resource m1, once it is known whether it is n
def Merge.all.takes.at(
  +s: Basics.Node,
  +f: Ledgers.Id,
  +m1: Resources.Name,
  r: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  },
  +same: Bool,
  es: {Resources.Name.is_eq(m1, n) == same: Bool},
  ih: {
    List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n) == True{}: Bool
  } -> Spec.Work.Reads(
    Basics.Key.res(n),
    Basics.Res.code(x),
    Judging.Merge.all(
      s,
      f,
      r,
      hb,
      ho,
      ht,
      Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
    )
  )
) -> {
  List.any.if(
    u => List.contains(~Resources.Name, ~Resources.Name.is_eq, r, n),
    same
  )
    == True{}: Bool
} -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(
    s,
    f,
    r,
    hb,
    ho,
    ht,
    Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w))
  )
):
  match same:
    case True{}:
      e => Merge.all.keeps(
        s,
        f,
        r,
        hb,
        ho,
        ht,
        Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep
      )(
        %Equal.sym(Resources.Name, m1, n, Name.sound(m1, n)(es)): Spec.Work.Reads(Basics.Key.res(n), Basics.Res.code(x), Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, _, w)))
        Merge.step.takes(s, f, hb, ho, ht, m, n, b, o, t, x, eb, eo, et, ep))
    case False{}:
      e => ih(e)

# a merge of the resources ns, with n among them, gives what the pick of n
# takes
def Merge.all.takes(
  +s: Basics.Node,
  +f: Ledgers.Id,
  +ns: List<&2, Resources.Name>,
  +hb: Maybe<&2, Hashes.Hash>,
  +ho: Maybe<&2, Hashes.Hash>,
  +ht: Maybe<&2, Hashes.Hash>,
  +m: Maybe<&2, Judging.Work>,
  +n: Resources.Name,
  +b: Maybe<&2, Ropes.Root>,
  +o: Maybe<&2, Ropes.Root>,
  +t: Maybe<&2, Ropes.Root>,
  +x: Maybe<&2, Ropes.Root>,
  +eb: {Basics.Res.find(s, hb, n) == Some{b}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +eo: {Basics.Res.find(s, ho, n) == Some{o}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +et: {Basics.Res.find(s, ht, n) == Some{t}: Maybe<&2, Maybe<&2, Ropes.Root>>},
  +ep: {
    Judging.Pick.merge(
      Formats.Format.of(Resources.Name.path(n)),
      s,
      b,
      o,
      t
    )
      == Some{Judging.Pick.Take{x}}: Maybe<&2, Judging.Pick>
  }
) -> {
  List.contains(~Resources.Name, ~Resources.Name.is_eq, ns, n) == True{}: Bool
} -> Spec.Work.Reads(
  Basics.Key.res(n),
  Basics.Res.code(x),
  Judging.Merge.all(s, f, ns, hb, ho, ht, m)
):
  match ns:
    case Nil{}:
      e => Empty.absurd(
        Spec.Work.Reads(Basics.Key.res(n), Basics.Res.code(x), m),
        Shared.Bool.false_ne_true(e)
      )
    case Con{m1, r}:
      Merge.all.takes.at(
        s,
        f,
        m1,
        r,
        hb,
        ho,
        ht,
        m,
        n,
        b,
        o,
        t,
        x,
        eb,
        eo,
        et,
        ep,
        Resources.Name.is_eq(m1, n),
        {==},
        Merge.all.takes(
          s,
          f,
          r,
          hb,
          ho,
          ht,
          Maybe.bind(&2, Judging.Work, Judging.Work, m, w => Merge.step(s, f, hb, ho, ht, m1, w)),
          n,
          b,
          o,
          t,
          x,
          eb,
          eo,
          et,
          ep
        )
      )

def Spec.Merge.keeps(s, c, from, h, n, b, o, t, x):
  ec => eb => eo => et => ep => Vector.joined.reads(
    s,
    c,
    from,
    Judging.Merge.all(
      s,
      from,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
      h,
      Basics.Node.root_of(s, Some{from}),
      Some{Judging.Work{s, h, []}}
    ),
    n,
    Basics.Res.code(x)
  )(
    Merge.all.takes(
      s,
      from,
      Judging.Merge.names(s, h, Basics.Node.root_of(s, Some{from})),
      Basics.Node.root_of(s, Judging.Merge.base(s, c, from, h)),
      h,
      Basics.Node.root_of(s, Some{from}),
      Some{Judging.Work{s, h, []}},
      n,
      b,
      o,
      t,
      x,
      eb,
      eo,
      et,
      ep
    )(ec)
  )

def Spec.Resolve.reads(s, h, n, m):
  Reads.bind(
    Basics.Key.res(n),
    Basics.Res.code(m),
    Judging.Work.set(Judging.Work{s, h, []}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Judging.Work.set(y, Basics.Key.clash(n), [])
  )(
    Set.read(Judging.Work{s, h, []}, Basics.Key.res(n), Basics.Res.code(m))
  )(
    y => hy => Set.kept.work(
      y,
      Basics.Key.clash(n),
      [],
      Basics.Key.res(n),
      Basics.Res.code(m),
      Clash.apart(n, n)
    )(hy)
  )

def Spec.Resolve.shuts(s, h, n, m):
  Reads.with(
    Judging.Work,
    Basics.Key.clash(n),
    [],
    Judging.Work.set(Judging.Work{s, h, []}, Basics.Key.res(n), Basics.Res.code(m)),
    y => Judging.Work.set(y, Basics.Key.clash(n), [])
  )(y => Set.read(y, Basics.Key.clash(n), []))

# the code of a count is not empty
def Count.full(
  n: Nat,
  r: List<&2, U32>
) -> {Shared.List.is_eq(~U32, ~U32.is_eq, [], Codes.Code.count(n, r)) == False{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Spec.Clash.shut(s, h, n, f):
  match f:
    case Ledgers.Id{w, q}:
      e =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(s, h, Basics.Key.clash(n)),
          Some{[]},
          e
        ): {
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            _,
            Some{Judging.Clash.code(Ledgers.Id{w, q})}
          )
            == False{}: Bool
        }
        Count.full(
          Codes.Code.length(w),
          Codes.Code.chars(w, Codes.Code.count(Codes.Code.length(q), Codes.Code.chars(q, [])))
        )

# Outcomes
# --------
# A step gives each of its requests an outcome (Spec.Step.run_outs), and only
# the requests of a step leave the requests that wait (Spec.Wait.left_keeps).

# a key that a run sets in its log, it reads
def Add.reads.log(
  r: Stepping.Run,
  +k: List<&2, U32>,
  +x: List<&2, U32>
) -> ProofLogs.Run.Keeps(k, x, Stepping.Run.log(r, k, x)):
  match r:
    case Stepping.Run{+s, Basics.Tip{c, +l}, +ns}:
      ProofLogs.Run.of.keeps(
        k,
        x,
        c,
        Judging.Work.set(Judging.Work{s, l, ns}, k, x)
      )(Set.read(Judging.Work{s, l, ns}, k, x))

# Add.reads once the value m of the key in the log is known
def Add.reads.at(
  r: Stepping.Run,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> ProofLogs.Run.Keeps(k, x, Stepping.Run.add.at(r, k, x, m)):
  match m:
    case Some{old}:
      Unit{}
    case None{}:
      Add.reads.log(r, k, x)

# a new key of the log of a run reads back
def Add.reads(
  +r: Stepping.Run,
  +k: List<&2, U32>,
  x: List<&2, U32>
) -> ProofLogs.Run.Keeps(k, x, Stepping.Run.add(r, k, x)):
  Add.reads.at(
    r,
    k,
    x,
    Basics.Node.get(Stepping.Run.state(r), Basics.Tip.log(Stepping.Run.tip(r)), k)
  )

# a log that reads the outcome key of i as v holds an outcome of i
def Outs.of(
  i: Ledgers.Id,
  v: List<&2, U32>,
  +m: Maybe<&2, Stepping.Run>
) -> ProofLogs.Run.Keeps(Basics.Log.out(i), v, m) -> Spec.Run.Outs(m, i):
  match m:
    case None{}:
      h => Unit{}
    case Some{Stepping.Run{s, t, ns}}:
      h =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(s, Basics.Tip.log(t), Basics.Log.out(i)),
          Some{v},
          h
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# each run that f gives has an outcome of i: so has the run after a step
def Outs.all(
  +m: Maybe<&2, Stepping.Run>,
  -f: Stepping.Run -> Maybe<&2, Stepping.Run>,
  -i: Ledgers.Id,
  hf: @r: Stepping.Run -> Spec.Run.Outs(f(r), i)
) -> Spec.Run.Outs(Maybe.bind(&2, Stepping.Run, Stepping.Run, m, f), i):
  match m:
    case None{}:
      Unit{}
    case Some{r}:
      hf(r)

# one of two runs, each with an outcome of i
def Outs.when(
  +b: Bool,
  -mx: Maybe<&2, Stepping.Run>,
  -my: Maybe<&2, Stepping.Run>,
  -i: Ledgers.Id,
  hx: Spec.Run.Outs(mx, i),
  hy: Spec.Run.Outs(my, i)
) -> Spec.Run.Outs(Shared.Bool.when(Maybe<&2, Stepping.Run>, b, u => mx, u => my), i):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that is refused as stale has an outcome
def Stale.outs(+r: Stepping.Run, +i: Ledgers.Id) -> Spec.Run.Outs(Stepping.Step.stale(r, i), i):
  Outs.of(
    i,
    Basics.Out.words(Basics.Out.Stale{}),
    Stepping.Run.add(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{}))
  )(Add.reads(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Stale{})))

# a request that is taken has an outcome
def Taken.outs(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +own: Maybe<&2, List<&2, String>>
) -> Spec.Run.Outs(Stepping.Step.taken(r, i, own), i):
  +n = Basics.Line.count(Stepping.Run.state(r), Stepping.Run.tip(r))
  Outs.of(
    i,
    Basics.Out.words(Basics.Out.Taken{n}),
    Stepping.Step.taken(r, i, own)
  )(
    ProofLogs.Keeps.bind(
      Basics.Log.out(i),
      Basics.Out.words(Basics.Out.Taken{n}),
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
      Add.reads(r, Basics.Log.out(i), Basics.Out.words(Basics.Out.Taken{n}))
    )(
      +r1 => h1 => ProofLogs.Keeps.bind(
        Basics.Log.out(i),
        Basics.Out.words(Basics.Out.Taken{n}),
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
        ProofLogs.Add.kept(
          r1,
          Basics.Log.version(n),
          Basics.Version.words(Basics.Version{i, Basics.Tip.content(Stepping.Run.tip(r1))}),
          Basics.Log.out(i),
          Basics.Out.words(Basics.Out.Taken{n})
        )(h1)
      )(
        +r2 => h2 => ProofLogs.Keeps.bind(
          Basics.Log.out(i),
          Basics.Out.words(Basics.Out.Taken{n}),
          Stepping.Run.log(r2, Basics.Log.count(), [U32.inc(n)]),
          r3 => Stepping.Run.owners(r3, own)
        )(
          ProofLogs.Log.kept(
            r2,
            Basics.Log.count(),
            [U32.inc(n)],
            Basics.Log.out(i),
            Basics.Out.words(Basics.Out.Taken{n}),
            {==}
          )(h2)
        )(
          r3 => h3 => ProofLogs.Owners.kept(
            r3,
            own,
            Basics.Log.out(i),
            Basics.Out.words(Basics.Out.Taken{n}),
            {==}
          )(h3)
        )
      )
    )
  )

# a judged request has an outcome
def Judged.outs(
  r: Stepping.Run,
  i: Ledgers.Id,
  own: Maybe<&2, List<&2, String>>,
  +m: Maybe<&2, Basics.Verdict>
) -> Spec.Run.Outs(Stepping.Step.judged(r, i, own, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Basics.Verdict.Stale{}}:
      Stale.outs(r, i)
    case Some{Basics.Verdict.Taken{h, ds, s2}}:
      Taken.outs(Stepping.Run.over(r, s2, h, ds), i, own)

# a mark on a version has an outcome
def Marked.outs(
  r: Stepping.Run,
  i: Ledgers.Id,
  m: String,
  +v: Maybe<&2, Basics.Version>
) -> Spec.Run.Outs(Stepping.Step.marked(r, i, m, v), i):
  match v:
    case None{}:
      Unit{}
    case Some{x}:
      Outs.all(
        Stepping.Run.add(r, Basics.Log.mark(m), Ledgers.Id.code(Basics.Version.id(x), [])),
        r2 => Stepping.Step.taken(r2, i, None{}),
        i,
        r2 => Taken.outs(r2, i, None{})
      )

# a request for a mark has an outcome
def Mark.outs(
  +r: Stepping.Run,
  +i: Ledgers.Id,
  +m: String
) -> Spec.Run.Outs(Stepping.Step.mark(r, i, m), i):
  +s = Stepping.Run.state(r)
  +t = Stepping.Run.tip(r)
  +n = Basics.Line.count(s, t)
  Outs.when(
    List.all.if(
      u => Maybe.is_none(&2, Ledgers.Id, Basics.Line.mark(s, t, m)),
      Bool.not(U32.is_eq(n, 0))
    ),
    Stepping.Step.marked(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    Stepping.Step.stale(r, i),
    i,
    Marked.outs(r, i, m, Basics.Line.version(s, t, U32.sub(n, 1))),
    Stale.outs(r, i)
  )

# the first tip of a new branch has an outcome
def Branch.made.outs(
  +r: Stepping.Run,
  i: Ledgers.Id,
  b: String,
  +m: Maybe<&2, Judging.Made>
) -> Spec.Run.Outs(Stepping.Branch.made(r, i, b, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Judging.Made{t, ds, s2}}:
      Outs.all(
        Stepping.Run.add(
          Stepping.Run.over(r, s2, Basics.Tip.content(Stepping.Run.tip(r)), ds),
          Basics.Log.start(b),
          Hashes.Hash.code(Basics.Tip.hash(t), [])
        ),
        r2 => Stepping.Step.taken(r2, i, None{}),
        i,
        r2 => Taken.outs(r2, i, None{})
      )

# a request for a branch has an outcome, once it is known whether its version
# is one
def Branch.ready.outs(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +b: String,
  +at: Maybe<&2, Ledgers.Id>,
  +m: Maybe<&2, Bool>
) -> Spec.Run.Outs(Stepping.Branch.ready(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{False{}}:
      Stale.outs(r, i)
    case Some{True{}}:
      Outs.when(
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
        i,
        Branch.made.outs(
          r,
          i,
          b,
          Judging.Make.first(
            Judging.Make.branch(Stepping.Run.state(r), Basics.Line.chain(st, Some{b}), at),
            Basics.Line.owners(Stepping.Run.state(r), Stepping.Run.tip(r))
          )
        ),
        Unit{}
      )

# a request for a branch has an outcome
def Branch.new.outs(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  b: String,
  +at: Maybe<&2, Ledgers.Id>,
  m: Maybe<&2, Maybe<&2, List<&2, U32>>>
) -> Spec.Run.Outs(Stepping.Branch.new(r, i, st, b, at, m), i):
  match m:
    case None{}:
      Unit{}
    case Some{Some{x}}:
      Stale.outs(r, i)
    case Some{None{}}:
      Branch.ready.outs(r, i, st, b, at, Judging.Judge.ready_maybe(Stepping.Run.state(r), at))

# On.outs once it is known how the line takes the change (w)
def On.of.outs(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change,
  w: Stepping.Route
) -> Spec.Run.Outs(Stepping.Step.on.of(r, i, st, l, ch, w), i):
  match w:
    case Stepping.Route.Mark{a}:
      Mark.outs(r, i, a)
    case Stepping.Route.Branch{+a, b}:
      Branch.new.outs(
        r,
        i,
        st,
        a,
        b,
        Basics.Node.find(
          Stepping.Run.state(r),
          Basics.Tip.log(Stepping.Run.tip(r)),
          Basics.Log.start(a)
        )
      )
    case Stepping.Route.Judge{}:
      Judged.outs(
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
        )
      )

# a change of a line has an outcome
def On.outs(
  +r: Stepping.Run,
  i: Ledgers.Id,
  st: Ledgers.Id,
  +l: Maybe<&2, String>,
  +ch: Basics.Change
) -> Spec.Run.Outs(Stepping.Step.on(r, i, st, l, ch), i):
  On.of.outs(r, i, st, l, ch, Stepping.Route.of(l, ch))

# a request of a run has an outcome
def Change.outs(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  +q: Basics.Ask
) -> Spec.Run.Outs(Stepping.Step.change(r, c, i, q), i):
  match q:
    case Basics.Ask.Start{os}:
      Stale.outs(r, i)
    case Basics.Ask.On{st, l, ch}:
      Outs.when(
        Ledgers.Chain.is_eq(Basics.Line.chain(st, l), c),
        Stepping.Step.on(r, i, st, l, ch),
        Stepping.Step.stale(r, i),
        i,
        On.outs(r, i, st, l, ch),
        Stale.outs(r, i)
      )

# a request that the node holds or not, of a run, has an outcome
def Asked.outs(
  r: Stepping.Run,
  c: Ledgers.Chain,
  i: Ledgers.Id,
  +a: Maybe<&2, Ledgers.Asked<Basics.Ask>>
) -> Spec.Run.Outs(Stepping.Step.asked(r, c, i, a), i):
  match a:
    case None{}:
      Unit{}
    case Some{Ledgers.Asked{t, q}}:
      Change.outs(r, c, i, q)

# a run whose log reads the outcome key of i has an outcome of i
def Outs.self(
  +r: Stepping.Run,
  i: Ledgers.Id,
  ws: List<&2, U32>
) -> {
  Basics.Node.get(
    Stepping.Run.state(r),
    Basics.Tip.log(Stepping.Run.tip(r)),
    Basics.Log.out(i)
  )
    == Some{ws}: Maybe<&2, List<&2, U32>>
} -> Spec.Run.Outs(Some{r}, i):
  match r:
    case Stepping.Run{s, t, ns}:
      eg =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(s, Basics.Tip.log(t), Basics.Log.out(i)),
          Some{ws},
          eg
        ): {Maybe.is_some(&2, List<&2, U32>, _) == True{}: Bool}
        {==}

# One.outs once the outcome o that the words ws read as is known
def One.outs.read(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  ws: List<&2, U32>,
  +o: Maybe<&2, Basics.Out>,
  eg: {
    Basics.Node.get(
      Stepping.Run.state(r),
      Basics.Tip.log(Stepping.Run.tip(r)),
      Basics.Log.out(i)
    )
      == Some{ws}: Maybe<&2, List<&2, U32>>
  }
) -> Spec.Run.Outs(Stepping.Step.fresh(r, c, i, o), i):
  match o:
    case Some{x}:
      Outs.self(r, i, ws)(eg)
    case None{}:
      Asked.outs(r, c, i, Basics.Node.asked(Stepping.Run.state(r), i))

# One.outs once what the log holds for the request is known (g)
def One.outs.at(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Basics.Node.get(
      Stepping.Run.state(r),
      Basics.Tip.log(Stepping.Run.tip(r)),
      Basics.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> Spec.Run.Outs(
  Stepping.Step.fresh(
    r,
    c,
    i,
    Maybe.bind(&2, List<&2, U32>, Basics.Out, g, ws => Basics.Out.read(ws))
  ),
  i
):
  match g:
    case None{}:
      Asked.outs(r, c, i, Basics.Node.asked(Stepping.Run.state(r), i))
    case Some{+ws}:
      One.outs.read(r, c, i, ws, Basics.Out.read(ws), eg)

# a request has an outcome after its step
def One.outs(
  +r: Stepping.Run,
  c: Ledgers.Chain,
  +i: Ledgers.Id
) -> Spec.Run.Outs(Stepping.Step.one(r, c, i), i):
  One.outs.at(
    r,
    c,
    i,
    Basics.Node.get(Stepping.Run.state(r), Basics.Tip.log(Stepping.Run.tip(r)), Basics.Log.out(i)),
    {==}
  )

# no run gives no run
def All.none(
  c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>
) -> {Stepping.Step.all(c, qs, None{}) == None{}: Maybe<&2, Stepping.Run>}:
  match qs:
    case Nil{}:
      {==}
    case Con{i, rest}:
      All.none(c, rest)

# a run reads what its log holds
def Keeps.self(
  +r: Stepping.Run,
  k: List<&2, U32>,
  v: List<&2, U32>
) -> {
  Basics.Node.get(
    Stepping.Run.state(r),
    Basics.Tip.log(Stepping.Run.tip(r)),
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
} -> ProofLogs.Run.Keeps(k, v, Some{r}):
  match r:
    case Stepping.Run{s, t, ns}:
      e => e

# Outs.kept once what the log of the run holds for the request is known (g)
def Outs.kept.at(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +r: Stepping.Run,
  +i: Ledgers.Id,
  g: Maybe<&2, List<&2, U32>>,
  eg: {
    Basics.Node.get(
      Stepping.Run.state(r),
      Basics.Tip.log(Stepping.Run.tip(r)),
      Basics.Log.out(i)
    )
      == g: Maybe<&2, List<&2, U32>>
  }
) -> {
  Maybe.is_some(&2, List<&2, U32>, g) == True{}: Bool
} -> Spec.Run.Outs(Stepping.Step.all(c, qs, Some{r}), i):
  match g:
    case None{}:
      h => Empty.absurd(
        Spec.Run.Outs(Stepping.Step.all(c, qs, Some{r}), i),
        Shared.Bool.false_ne_true(h)
      )
    case Some{+v}:
      h => Outs.of(
        i,
        v,
        Stepping.Step.all(c, qs, Some{r})
      )(
        ProofLogs.All.kept(
          c,
          qs,
          Some{r},
          Basics.Log.out(i),
          v,
          {==},
          {==}
        )(Keeps.self(r, Basics.Log.out(i), v)(eg))
      )

# an outcome that a run has, it has after more requests
def Outs.kept(
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Stepping.Run>,
  +i: Ledgers.Id
) -> Spec.Run.Outs(m, i) -> Spec.Run.Outs(Stepping.Step.all(c, qs, m), i):
  match m:
    case None{}:
      h =>
        %Equal.sym(
          Maybe<&2, Stepping.Run>,
          Stepping.Step.all(c, qs, None{}),
          None{},
          All.none(c, qs)
        ): Spec.Run.Outs(_, i)
        Unit{}
    case Some{Stepping.Run{s, t, ns}}:
      h => Outs.kept.at(
        c,
        qs,
        Stepping.Run{s, t, ns},
        i,
        Basics.Node.get(s, Basics.Tip.log(t), Basics.Log.out(i)),
        {==}
      )(h)

# All.outs at the first request j, once it is known whether it is i
def All.outs.at(
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  rest: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Stepping.Run>,
  +i: Ledgers.Id,
  +same: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i) == True{}: Bool
  } -> Spec.Run.Outs(
    Stepping.Step.all(
      c,
      rest,
      Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, j))
    ),
    i
  )
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rest, i), same) == True{}: Bool
} -> Spec.Run.Outs(
  Stepping.Step.all(
    c,
    rest,
    Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, j))
  ),
  i
):
  match same:
    case True{}:
      e => Outs.kept(
        c,
        rest,
        Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, j)),
        i
      )(
        %Equal.sym(Ledgers.Id, j, i, Ledgers.Id.is_eq_sound(j, i)(es)): Spec.Run.Outs(Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, _)), i)
        Outs.all(m, r => Stepping.Step.one(r, c, i), i, r => One.outs(r, c, i)))
    case False{}:
      e => ih(e)

# each request of a step has an outcome after it
def All.outs(
  +c: Ledgers.Chain,
  +qs: List<&2, Ledgers.Id>,
  +m: Maybe<&2, Stepping.Run>,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, qs, i) == True{}: Bool
} -> Spec.Run.Outs(Stepping.Step.all(c, qs, m), i):
  match qs:
    case Nil{}:
      e => Empty.absurd(Spec.Run.Outs(m, i), Shared.Bool.false_ne_true(e))
    case Con{j, rest}:
      All.outs.at(
        c,
        j,
        rest,
        m,
        i,
        Ledgers.Id.is_eq(j, i),
        {==},
        All.outs(
          c,
          rest,
          Maybe.bind(&2, Stepping.Run, Stepping.Run, m, r => Stepping.Step.one(r, c, j)),
          i
        )
      )

def Spec.Step.run_outs(s, c, t, qs, i):
  All.outs(c, qs, Some{Stepping.Run{s, t, []}}, i)

# Wait.left_keeps at the first request j, once it is known whether it is i
# (same) and whether a step ran it (d)
def Left.keeps.at(
  j: Ledgers.Id,
  ks: List<&2, Ledgers.Id>,
  rs: List<&2, Ledgers.Id>,
  done: Tries.Trie<Unit>,
  i: Ledgers.Id,
  +same: Bool,
  +d: Bool,
  es: {Ledgers.Id.is_eq(j, i) == same: Bool},
  ed: {Tries.Trie.has(Unit, done, Ledgers.Id.key(j)) == d: Bool},
  hd: {Tries.Trie.has(Unit, done, Ledgers.Id.key(i)) == False{}: Bool},
  ih: {
    List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i) == True{}: Bool
  } -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool}
) -> {
  List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, rs, i), same) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    List.filter.put(Ledgers.Id, j, ks, Bool.not(d)),
    i
  )
    == True{}: Bool
}:
  match same d:
    case True{} False{}:
      e =>
        %Equal.sym(
          Bool,
          Ledgers.Id.is_eq(j, i),
          True{},
          es
        ): {
          List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i), _) == True{}: Bool
        }
        {==}
    case True{} True{}:
      e => Empty.absurd(
        {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, ks, i) == True{}: Bool},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Tries.Trie.has(Unit, done, Ledgers.Id.key(i)),
            True{},
            Equal.sym(Bool, Tries.Trie.has(Unit, done, Ledgers.Id.key(i)), False{}, hd),
            (
              %Ledgers.Id.is_eq_sound(j, i)(es): {Tries.Trie.has(Unit, done, Ledgers.Id.key(_)) == True{}: Bool}
              ed)
          )
        )
      )
    case False{} False{}:
      e => Shared.List.contains_cons(~Ledgers.Id, ~Ledgers.Id.is_eq, j, ks, i)(ih(e))
    case False{} True{}:
      e => ih(e)

def Spec.Wait.left_keeps(ws, done, i):
  match ws:
    case Nil{}:
      e => hd => e
    case Con{j, rs}:
      e => +hd => Left.keeps.at(
        j,
        Sealing.Wait.left(rs, done),
        rs,
        done,
        i,
        Ledgers.Id.is_eq(j, i),
        Tries.Trie.has(Unit, done, Ledgers.Id.key(j)),
        {==},
        {==},
        hd,
        e2 => Spec.Wait.left_keeps(rs, done, i)(e2)(hd)
      )(e)

# Plan.follow_allowed once it is known whether the rules allow the vote (b)
def Follow.allowed.at(
  s: Basics.Node,
  c: Ledgers.Chain,
  t: Basics.Tip,
  th: Maybe<&2, Hashes.Hash>,
  v: Ledgers.Vote,
  from: List<&2, String>,
  b: Bool
) -> {
  Maybe.is_some(
    &2,
    Stepping.Run,
    Sealing.Plan.run(
      Shared.Bool.when(
        Sealing.Plan,
        b,
        u => Sealing.Plan.copy(s, c, t, th, Some{v}, from),
        u => Sealing.Plan{[], None{}, []}
      )
    )
  )
    == True{}: Bool
} -> {b == True{}: Bool}:
  match b:
    case True{}:
      e => {==}
    case False{}:
      e => e

def Spec.Plan.follow_allowed(s, c, w, t, th, os, v, from):
  Follow.allowed.at(s, c, t, th, v, from, Voting.Vote.allowed(s, w, os, v, from))
