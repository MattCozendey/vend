# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/rope.bend as Ropes
import ../../shared/shared/shared/code.bend as Codes
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/seal.bend as Seals
import ../../shared/shared/shared/trie.bend as Tries
import ../../shared/tree.bend as Trees
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../stepping.bend as Stepping
import ../voting.bend as Voting
import ./lines.bend as ProofLines
import ./logs.bend as ProofLogs
import ./trees.bend as ProofTrees
import ../../shared/shared/store.bend as Stores

# Agreement
# ---------

# a step that the owners decided at a place in a, they decided in a node that
# grew, with the owners that it reads
def Decide.up(
  +a: Basics.Node,
  +u: Basics.Node,
  +t: Basics.Tip,
  +w: Ledgers.Where,
  v: Ledgers.Vote,
  +g: {Reading.Node.grows(a, u) == True{}: Bool}
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Basics.State.ledger(a),
    w,
    Basics.Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Basics.State.ledger(u),
    w,
    Basics.Tip.owners(t)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
}:
  e =>
    Ledgers.State.decide_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~ProofTrees.Ask.laws(),
      Basics.State.ledger(a),
      Basics.State.ledger(u),
      w,
      Basics.Tip.owners(t),
      v
    )(g)(e)

# Scan.elim at a round, once what it decides is known (m)
def Scan.elim.at(
  -R: Type,
  -s: Basics.Node,
  -c: Ledgers.Chain,
  -n: U32,
  -os: List<&2, String>,
  -p: Nat,
  -v: Ledgers.Vote,
  r: Nat,
  m: Maybe<&2, Ledgers.Vote>,
  rec: {
    Voting.Height.decide(s, c, n, os, p) == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> (
    @q: Nat -> {
      Ledgers.State.decide(
        ~Basics.Ask,
        Basics.State.ledger(s),
        Ledgers.Where{c, n, q},
        os
      )
        == Some{v}: Maybe<&2, Ledgers.Vote>
    } -> R
  ) -> R
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Basics.State.ledger(s),
    Ledgers.Where{c, n, r},
    os
  )
    == m: Maybe<&2, Ledgers.Vote>
} -> {
  Voting.Vote.first(
    m,
    u => Voting.Height.decide(s, c, n, os, p)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => rec(e)(f)
    case Some{x}:
      em => e => f => f(
        r
      )(
        Equal.trans(
          Maybe<&2, Ledgers.Vote>,
          Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, n, r}, os),
          Some{x},
          Some{v},
          em,
          e
        )
      )

# a step that a height decides in a round up to k is decided in some round
def Scan.elim(
  -R: Type,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +n: U32,
  +os: List<&2, String>,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Voting.Height.decide(s, c, n, os, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @q: Nat -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, n, q},
      os
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match k:
    case 0n:
      e => f => f(0n)(e)
    case 1n+(+p):
      Scan.elim.at(
        R,
        s,
        c,
        n,
        os,
        p,
        v,
        1n+p,
        Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, n, 1n+p}, os),
        Scan.elim(R, s, c, n, os, p, v)
      )({==})

# a head is at its own height
def Level.refl(h: Basics.Head) -> {Voting.Heads.level(Some{h}, Some{h}) == True{}: Bool}:
  match h:
    case Basics.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)

# the step that the owners in the tip of the head h decided next on the line
# c, in a round up to k, if they did
def Advance.found(
  +s: Basics.Node,
  c: Ledgers.Chain,
  +h: Basics.Head,
  k: Nat
) -> Maybe<&2, Ledgers.Vote>:
  Maybe.bind(
    &2,
    Basics.Tip,
    Ledgers.Vote,
    Basics.Head.tip(s, h),
    t => Voting.Height.decide(s, c, Sealing.Head.next(h), Basics.Tip.owners(t), k)
  )

# the step that the owners in the tip of the head h decided next on the line
# c, in a round of which the node holds a ballot, if they did
def Advance.vote(+s: Basics.Node, +c: Ledgers.Chain, +h: Basics.Head) -> Maybe<&2, Ledgers.Vote>:
  Advance.found(s, c, h, Sealing.Round.seen(s, c, Sealing.Head.next(h)))

# the head h after the step m: one height up, at the tip that the step names
# (no step, or one that names no tip: h)
def Head.step(h: Basics.Head, m: Maybe<&2, Ledgers.Vote>) -> Basics.Head:
  match h m:
    case Basics.Head{r, b, n, th} Some{Ledgers.Vote{before, qs, Some{x}}}:
      Basics.Head{r, b, U32.inc(n), Some{x}}
    case x y:
      x

# that the head of the line c in the node s2, when it is not at the height of
# h, is x
def Moves(s2: Basics.Node, c: Ledgers.Chain, h: Basics.Head, x: Basics.Head) -> Type:
  {
    Voting.Heads.level(Some{h}, Basics.Node.head_of(s2, c)) == False{}: Bool
  } -> {Basics.Node.head_of(s2, c) == Some{x}: Maybe<&2, Basics.Head>}

# a node whose head is h did not move it
def Moves.stay(
  -s: Basics.Node,
  -c: Ledgers.Chain,
  h: Basics.Head,
  -x: Basics.Head,
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>}
) -> Moves(s, c, h, x):
  hl => Empty.absurd(
    {Basics.Node.head_of(s, c) == Some{x}: Maybe<&2, Basics.Head>},
    Shared.Bool.false_ne_true(
      Equal.trans(
        Bool,
        False{},
        Voting.Heads.level(Some{h}, Some{h}),
        True{},
        Equal.trans(
          Bool,
          False{},
          Voting.Heads.level(Some{h}, Basics.Node.head_of(s, c)),
          Voting.Heads.level(Some{h}, Some{h}),
          Equal.sym(Bool, Voting.Heads.level(Some{h}, Basics.Node.head_of(s, c)), False{}, hl),
          Equal.cong(
            Maybe<&2, Basics.Head>,
            Bool,
            m => Voting.Heads.level(Some{h}, m),
            Basics.Node.head_of(s, c),
            Some{h},
            em
          )
        ),
        Level.refl(h)
      )
    )
  )

# one of two nodes, each with its head moved to x or not at all
def Moves.when(
  b: Bool,
  -sx: Basics.Node,
  -sy: Basics.Node,
  -c: Ledgers.Chain,
  -h: Basics.Head,
  -x: Basics.Head,
  hx: Moves(sx, c, h, x),
  hy: Moves(sy, c, h, x)
) -> Moves(Shared.Bool.when(Basics.Node, b, u => sx, u => sy), c, h, x):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# the head of a line, after it is set
def Head.at_set(
  b0: Basics.Node,
  +c: Ledgers.Chain,
  hd: Basics.Head
) -> {Basics.Node.head_of(Sealing.State.head(b0, c, hd), c) == Some{hd}: Maybe<&2, Basics.Head>}:
  Equal.trans(
    Maybe<&2, Basics.Head>,
    Basics.Node.head_of(Sealing.State.head(b0, c, hd), c),
    Bool.pick(
      Maybe<&2, Basics.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Basics.Node.head_of(b0, c)
    ),
    Some{hd},
    ProofLines.Head.of_set(b0, c, hd, c),
    ProofLines.Pick.of(
      Maybe<&2, Basics.Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      Some{hd},
      Basics.Node.head_of(b0, c),
      Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
    )
  )

# Advance.moved moves the head to hd, or not at all
def Advance.moved.moves(
  +s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +c: Ledgers.Chain,
  hd: Basics.Head,
  qs: List<&2, Ledgers.Id>,
  h: Basics.Head,
  -x: Basics.Head,
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  ex: {hd == x: Basics.Head}
) -> Moves(Voting.Advance.moved(s, m, c, hd, qs), c, h, x):
  match m:
    case None{}:
      Moves.stay(s, c, h, x, em)
    case Some{+s3}:
      hl =>
        %ex: {
          Basics.Node.head_of(
            Sealing.State.moved(Basics.State.led(s, Basics.State.ledger(s3)), c, hd, qs),
            c
          )
            == Some{_}: Maybe<&2, Basics.Head>
        }
        Head.at_set(
          Sealing.Wait.set(
            Basics.State.led(s, Basics.State.ledger(s3)),
            c,
            Sealing.Wait.left(
              Sealing.Wait.of(Basics.State.led(s, Basics.State.ledger(s3)), c),
              Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
            )
          ),
          c,
          hd
        )

# Advance.ran.moves once whether the run gives the tip that the step names is
# known (bq)
def Advance.ran.moves.if(
  s: Basics.Node,
  s2: Basics.Node,
  +t2: Basics.Tip,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  h: Basics.Head,
  -x: Basics.Head,
  bq: Bool,
  ebq: {Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}) == bq: Bool},
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  ex: {
    Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}) == True{}: Bool
  } -> {Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}} == x: Basics.Head}
) -> Moves(
  Shared.Bool.when(
    Basics.Node,
    bq,
    u => Voting.Advance.moved(
      s,
      Judging.State.put(s2, [Basics.Tip.words(t2)]),
      c,
      Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}},
      qs
    ),
    u => s
  ),
  c,
  h,
  x
):
  match bq:
    case True{}:
      Advance.moved.moves(
        s,
        Judging.State.put(s2, [Basics.Tip.words(t2)]),
        c,
        Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}},
        qs,
        h,
        x,
        em,
        ex(ebq)
      )
    case False{}:
      Moves.stay(s, c, h, x, em)

# a checked step moves the head to the tip that the step names, or not at all
def Advance.ran.moves(
  s: Basics.Node,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>,
  h: Basics.Head,
  -x: Basics.Head,
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  ex: @t2: Basics.Tip -> {
    Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}) == True{}: Bool
  } -> {Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}} == x: Basics.Head}
) -> Moves(Voting.Advance.ran(s, c, r, br, next, after, qs, m), c, h, x):
  match m:
    case None{}:
      Moves.stay(s, c, h, x, em)
    case Some{Stepping.Run{s2, +t2}}:
      Advance.ran.moves.if(
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        after,
        qs,
        h,
        x,
        Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}),
        {==},
        em,
        ex(t2)
      )

# Node.advance moves the head by the decided step m, or not at all
def Advance.step.moves(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  t: Basics.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
} -> Moves(Voting.Advance.step(s, c, h, t, m), c, h, Head.step(h, m)):
  match h m:
    case Basics.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, +after}}:
      +em => Moves.when(
        Sealing.Root.same(before, th),
        Voting.Advance.ran(s, c, r, br, next, after, qs, Stepping.Step.run(s, c, t, qs)),
        s,
        c,
        Basics.Head{r, br, next, th},
        Head.step(Basics.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
        Advance.ran.moves(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Stepping.Step.run(s, c, t, qs),
          Basics.Head{r, br, next, th},
          Head.step(Basics.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em,
          t2 => er =>
            %Equal.sym(Maybe<&2, Hashes.Hash>, after, Some{Basics.Tip.hash(t2)}, Shared.Maybe.is_eq_sound(~Hashes.Hash, ~Hashes.Hash.is_eq, x => y => Hashes.Hash.is_eq_sound(x, y), after, Some{Basics.Tip.hash(t2)})(er)): {Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}} == Head.step(Basics.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, _}}): Basics.Head}
            {==}),
        Moves.stay(
          s,
          c,
          Basics.Head{r, br, next, th},
          Head.step(Basics.Head{r, br, next, th}, Some{Ledgers.Vote{before, qs, after}}),
          em
        )
      )
    case Basics.Head{+r, +br, +next, +th} None{}:
      em => Moves.stay(s, c, Basics.Head{r, br, next, th}, Basics.Head{r, br, next, th}, em)

# Node.advance moves the head by the step decided at the head h, whose tip is
# m, or not at all
def Advance.at.moves(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {
  Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
} -> {
  Basics.Head.tip(s, h) == m: Maybe<&2, Basics.Tip>
} -> Moves(Voting.Advance.at(s, c, h, m), c, h, Head.step(h, Advance.vote(s, c, h))):
  match m:
    case None{}:
      em => et => Moves.stay(s, c, h, Head.step(h, Advance.vote(s, c, h)), em)
    case Some{+t}:
      em => et =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Advance.vote(s, c, h),
          Voting.Height.decide(
            s,
            c,
            Sealing.Head.next(h),
            Basics.Tip.owners(t),
            Sealing.Round.seen(s, c, Sealing.Head.next(h))
          ),
          Equal.cong(
            Maybe<&2, Basics.Tip>,
            Maybe<&2, Ledgers.Vote>,
            mt => Maybe.bind(
              &2,
              Basics.Tip,
              Ledgers.Vote,
              mt,
              t1 => Voting.Height.decide(
                s,
                c,
                Sealing.Head.next(h),
                Basics.Tip.owners(t1),
                Sealing.Round.seen(s, c, Sealing.Head.next(h))
              )
            ),
            Basics.Head.tip(s, h),
            Some{t},
            et
          )
        ): Moves(
          Voting.Advance.step(
            s,
            c,
            h,
            t,
            Voting.Height.decide(
              s,
              c,
              Sealing.Head.next(h),
              Basics.Tip.owners(t),
              Sealing.Round.seen(s, c, Sealing.Head.next(h))
            )
          ),
          c,
          h,
          Head.step(h, _)
        )
        Advance.step.moves(
          s,
          c,
          h,
          t,
          Voting.Height.decide(
            s,
            c,
            Sealing.Head.next(h),
            Basics.Tip.owners(t),
            Sealing.Round.seen(s, c, Sealing.Head.next(h))
          )
        )(em)

# a head moves only to the tip that the owners in its tip decided next
def Advance.decided(
  +s: Basics.Node,
  c: Ledgers.Chain,
  +h: Basics.Head
) -> {
  Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
} -> {
  Voting.Heads.level(Some{h}, Basics.Node.head_of(Voting.Node.advance(s, c), c)) == False{}: Bool
} -> {
  Basics.Node.head_of(
    Voting.Node.advance(s, c),
    c
  )
    == Some{Head.step(h, Advance.vote(s, c, h))}: Maybe<&2, Basics.Head>
}:
  +em =>
    %Equal.sym(
      Maybe<&2, Basics.Head>,
      Basics.Node.head_of(s, c),
      Some{h},
      em
    ): Moves(Voting.Advance.head(s, c, _), c, h, Head.step(h, Advance.vote(s, c, h)))
    Advance.at.moves(s, c, h, Basics.Head.tip(s, h))(em)({==})

# Found.elim once the tip m of the head is known
def Found.elim.at(
  -R: Type,
  +s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head,
  k: Nat,
  -v: Ledgers.Vote,
  m: Maybe<&2, Basics.Tip>
) -> {
  Basics.Head.tip(s, h) == m: Maybe<&2, Basics.Tip>
} -> {
  Maybe.bind(
    &2,
    Basics.Tip,
    Ledgers.Vote,
    m,
    t => Voting.Height.decide(s, c, Sealing.Head.next(h), Basics.Tip.owners(t), k)
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Basics.Tip -> @q: Nat -> {
    Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>
  } -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, Sealing.Head.next(h), q},
      Basics.Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  match m:
    case None{}:
      em => e => f => Empty.absurd(R, Shared.Maybe.none_ne_some(Ledgers.Vote, v, e))
    case Some{+t}:
      em => e => f => Scan.elim(
        R,
        s,
        c,
        Sealing.Head.next(h),
        Basics.Tip.owners(t),
        k,
        v
      )(e)(q => d => f(t)(q)(em)(d))

# a step that a node found at a head is decided at the head's tip, in some
# round
def Found.elim(
  -R: Type,
  +s: Basics.Node,
  c: Ledgers.Chain,
  +h: Basics.Head,
  k: Nat,
  -v: Ledgers.Vote
) -> {
  Advance.found(s, c, h, k) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> (
  @t: Basics.Tip -> @q: Nat -> {
    Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>
  } -> {
    Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(s),
      Ledgers.Where{c, Sealing.Head.next(h), q},
      Basics.Tip.owners(t)
    )
      == Some{v}: Maybe<&2, Ledgers.Vote>
  } -> R
) -> R:
  Found.elim.at(R, s, c, h, k, v, Basics.Head.tip(s, h))({==})

# Writes
# ------

# the value of a resource reads back
def Res.round(
  m: Maybe<&2, Ropes.Root>
) -> {Basics.Res.read(Basics.Res.code(m)) == m: Maybe<&2, Ropes.Root>}:
  %Equal.sym(
    Maybe<&2, Codes.Read<Maybe<&2, Ropes.Root>>>,
    Codes.Code.maybe.read(
      ~Ropes.Root,
      ~Ropes.Root.code.read,
      Codes.Code.maybe(~Ropes.Root, ~Ropes.Root.code, m, [])
    ),
    Some{Codes.Read{m, []}},
    Codes.Code.maybe_read(
      ~Ropes.Root,
      ~Ropes.Root.code,
      ~Ropes.Root.code.read,
      x => r => Ropes.Root.code_read(x, r),
      m,
      []
    )
  ): {Basics.Res.of.read(_) == m: Maybe<&2, Ropes.Root>}
  {==}

# the verdict m takes
def Verdict.took(m: Maybe<&2, Judging.Verdict>) -> Bool:
  match m:
    case Some{Judging.Verdict.Taken{Judging.Work{s2, h}}}:
      True{}
    case x:
      False{}

# the tree of the verdict m
def Took.root(m: Maybe<&2, Judging.Verdict>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Judging.Verdict.Taken{Judging.Work{s2, h}}}:
      h
    case x:
      None{}

# the node of the verdict m, or d when it takes nothing
def Took.node(m: Maybe<&2, Judging.Verdict>, d: Basics.Node) -> Basics.Node:
  match m:
    case Some{Judging.Verdict.Taken{Judging.Work{s2, h}}}:
      s2
    case x:
      d

# a verdict that takes, after a verdict, is the verdict of what comes next
def Then.took(
  m: Maybe<&2, Bool>,
  -k: Unit -> Maybe<&2, Judging.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Basics.Node
) -> {
  Judging.Judge.then(m, k) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
} -> {k(Unit{}) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>}:
  match m:
    case Some{True{}}:
      e => e
    case Some{False{}}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Judging.Verdict>,
            Bool,
            v => Verdict.took(v),
            Judging.Judge.refuse(),
            Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}},
            e
          )
        )
      )
    case None{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>},
        Shared.Maybe.none_ne_some(Judging.Verdict, Judging.Verdict.Taken{Judging.Work{s3, h2}}, e)
      )

# a verdict that takes, under a condition, is the verdict of what comes next
def When.took(
  b: Bool,
  -k: Unit -> Maybe<&2, Judging.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Basics.Node
) -> {
  Judging.Judge.when(b, k) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
} -> {k(Unit{}) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>}:
  match b:
    case True{}:
      e => e
    case False{}:
      e => Empty.absurd(
        {k(Unit{}) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Judging.Verdict>,
            Bool,
            v => Verdict.took(v),
            Judging.Judge.refuse(),
            Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}},
            e
          )
        )
      )

# Set.reads once the node m2 that the put of the new subtree gives is known
def Set.reads.put(
  +s: Basics.Node,
  +h: Maybe<&2, Hashes.Hash>,
  +k: List<&2, U32>,
  +x: List<&2, U32>,
  +hh: Hashes.Hash,
  ws: List<&2, List<&2, U32>>,
  m2: Maybe<&2, Basics.Node>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Basics.Node,
  hp: @y: Basics.Node -> {
    m2 == Some{y}: Maybe<&2, Basics.Node>
  } -> {Stores.Store.holds(~Basics.Node, ~Basics.Store.fetch, y, ws) == True{}: Bool}
) -> {
  Basics.Node.set(s, h, k, x) == Some{Trees.Put{hh, ws}}: Maybe<&2, Trees.Put>
} -> {
  Judging.Work.take(
    Judging.Work.on(m2, Some{hh})
  )
    == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
} -> {Basics.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m2:
    case None{}:
      es => e => Empty.absurd(
        {Basics.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Judging.Verdict, Judging.Verdict.Taken{Judging.Work{s3, h2}}, e)
      )
    case Some{+sk}:
      es => +e =>
        %Equal.cong(
          Maybe<&2, Judging.Verdict>,
          Basics.Node,
          v => Took.node(v, s3),
          Some{Judging.Verdict.Taken{Judging.Work{sk, Some{hh}}}},
          Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}},
          e
        ): {Basics.Node.get(_, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        %Equal.cong(
          Maybe<&2, Judging.Verdict>,
          Maybe<&2, Hashes.Hash>,
          v => Took.root(v),
          Some{Judging.Verdict.Taken{Judging.Work{sk, Some{hh}}}},
          Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}},
          e
        ): {Basics.Node.get(sk, _, k) == Some{x}: Maybe<&2, List<&2, U32>>}
        Equal.trans(
          Maybe<&2, List<&2, U32>>,
          Basics.Node.get(sk, Some{hh}, k),
          Trees.Tree.get(~Basics.Node, ~Basics.Store.fetch, sk, Some{hh}, k),
          Some{x},
          ProofTrees.Get.is(sk, Some{hh}, k),
          Trees.Tree.get_set(
            ~Basics.Node,
            ~Basics.Store.fetch,
            s,
            sk,
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
              es
            )
          )(hp(sk)({==}))
        )

# a key set in a tree, when the verdict takes the new tree, reads back in a
# node that holds the new nodes
def Set.reads(
  +s: Basics.Node,
  h: Maybe<&2, Hashes.Hash>,
  k: List<&2, U32>,
  x: List<&2, U32>,
  m: Maybe<&2, Trees.Put>,
  -h2: Maybe<&2, Hashes.Hash>,
  s3: Basics.Node
) -> {
  Basics.Node.set(s, h, k, x) == m: Maybe<&2, Trees.Put>
} -> {
  Judging.Work.take(
    Judging.Work.of(s, m)
  )
    == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
} -> {Basics.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>}:
  match m:
    case None{}:
      es => e => Empty.absurd(
        {Basics.Node.get(s3, h2, k) == Some{x}: Maybe<&2, List<&2, U32>>},
        Shared.Maybe.none_ne_some(Judging.Verdict, Judging.Verdict.Taken{Judging.Work{s3, h2}}, e)
      )
    case Some{Trees.Put{hh, +ws}}:
      Set.reads.put(
        s,
        h,
        k,
        x,
        hh,
        ws,
        Judging.State.put(s, ws),
        h2,
        s3,
        y => ey => ProofLines.Put.holds(s, ws, y)(ey)
      )

# a verdict that takes, after a read, is the verdict of what comes next
def With.took(
  -A: Data,
  ma: Maybe<&2, A>,
  -k: A -> Maybe<&2, Judging.Verdict>,
  -kk: Maybe<&2, Judging.Verdict>,
  -h2: Maybe<&2, Hashes.Hash>,
  -s3: Basics.Node
) -> (
  @a: A -> {
    k(a) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
  } -> {kk == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>}
) -> {
  Maybe.bind(
    &2,
    A,
    Judging.Verdict,
    ma,
    k
  )
    == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>
} -> {kk == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>}:
  match ma:
    case None{}:
      hk => e => Empty.absurd(
        {kk == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>},
        Shared.Maybe.none_ne_some(Judging.Verdict, Judging.Verdict.Taken{Judging.Work{s3, h2}}, e)
      )
    case Some{a}:
      hk => e => hk(a)(e)

def Spec.Judge.write_reads(s, n, base, c, h, h2, s3, m):
  e => ec =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Basics.Node.get(s3, h2, Basics.Key.res(n)),
      Some{Basics.Res.code(m)},
      Set.reads(s, h, Basics.Key.res(n), Basics.Res.code(m), Basics.Node.set(s, h, Basics.Key.res(n), Basics.Res.code(m)), h2, s3)(
        {==}
      )(
        With.took(
          Maybe<&2, Ropes.Root>,
          Basics.Res.find(s, h, n),
          a1 => Maybe.bind(
            &2,
            Maybe<&2, Ropes.Root>,
            Judging.Verdict,
            Basics.Res.find(s, Basics.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Judging.Verdict,
              Judging.Content.find(s, n, c),
              m1 => Judging.Judge.when(
                Basics.Roots.same(a1, b1),
                x => Judging.Work.take(
                  Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))
                )
              )
            )
          ),
          Judging.Work.take(
            Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
          ),
          h2,
          s3
        )(
          +a => With.took(
            Maybe<&2, Ropes.Root>,
            Basics.Res.find(s, Basics.Node.root_of(s, base), n),
            b1 => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Judging.Verdict,
              Judging.Content.find(s, n, c),
              m1 => Judging.Judge.when(
                Basics.Roots.same(a, b1),
                x => Judging.Work.take(
                  Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))
                )
              )
            ),
            Judging.Work.take(
              Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
            ),
            h2,
            s3
          )(
            +b => ex => When.took(Basics.Roots.same(a, b), x => Judging.Work.take(
                Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m))
              ), h2, s3)(
              %ec: {Maybe.bind(&2, Maybe<&2, Ropes.Root>, Judging.Verdict, _, m1 => Judging.Judge.when(Basics.Roots.same(a, b), x => Judging.Work.take(Judging.Work.set(Judging.Work{s, h}, Basics.Key.res(n), Basics.Res.code(m1))))) == Some{Judging.Verdict.Taken{Judging.Work{s3, h2}}}: Maybe<&2, Judging.Verdict>}
              ex)
          )
        )(
          Then.took(Judging.Judge.content(s, c), w => Maybe.bind(
              &2,
              Maybe<&2, Ropes.Root>,
              Judging.Verdict,
              Basics.Res.find(s, h, n),
              a1 => Maybe.bind(
                &2,
                Maybe<&2, Ropes.Root>,
                Judging.Verdict,
                Basics.Res.find(s, Basics.Node.root_of(s, base), n),
                b1 => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Judging.Verdict,
                  Judging.Content.find(s, n, c),
                  m1 => Judging.Judge.when(
                    Basics.Roots.same(a1, b1),
                    x => Judging.Work.take(
                      Judging.Work.set(
                        Judging.Work{s, h},
                        Basics.Key.res(n),
                        Basics.Res.code(m1)
                      )
                    )
                  )
                )
              )
            ), h2, s3)(
            Then.took(Judging.Judge.ready_maybe(s, base), u => Judging.Judge.then(
                Judging.Judge.content(s, c),
                w => Maybe.bind(
                  &2,
                  Maybe<&2, Ropes.Root>,
                  Judging.Verdict,
                  Basics.Res.find(s, h, n),
                  a1 => Maybe.bind(
                    &2,
                    Maybe<&2, Ropes.Root>,
                    Judging.Verdict,
                    Basics.Res.find(s, Basics.Node.root_of(s, base), n),
                    b1 => Maybe.bind(
                      &2,
                      Maybe<&2, Ropes.Root>,
                      Judging.Verdict,
                      Judging.Content.find(s, n, c),
                      m1 => Judging.Judge.when(
                        Basics.Roots.same(a1, b1),
                        x => Judging.Work.take(
                          Judging.Work.set(
                            Judging.Work{s, h},
                            Basics.Key.res(n),
                            Basics.Res.code(m1)
                          )
                        )
                      )
                    )
                  )
                )
              ), h2, s3)(e)
          )
        )
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Ropes.Root,
        _,
        ws => Basics.Res.read(ws)
      )
        == m: Maybe<&2, Ropes.Root>
    }
    Res.round(m)

# Merges
# ------
def Spec.Pick.merge_theirs(f, s, b, o, t):
  e =>
    %Equal.sym(
      Bool,
      Basics.Roots.same(o, b),
      True{},
      e
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        _,
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), Basics.Roots.same(t, b)),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{t}}: Maybe<&2, Judging.Pick>
    }
    {==}

def Spec.Pick.merge_ours(f, s, b, o, t):
  e1 => e2 =>
    %Equal.sym(
      Bool,
      Basics.Roots.same(o, b),
      False{},
      e1
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        _,
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), Basics.Roots.same(t, b)),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>
    }
    %Equal.sym(
      Bool,
      Basics.Roots.same(t, b),
      True{},
      e2
    ): {
      Shared.Bool.when(
        Maybe<&2, Judging.Pick>,
        False{},
        u => Some{Judging.Pick.Take{t}},
        u => Shared.Bool.when(
          Maybe<&2, Judging.Pick>,
          List.any.if(v => Basics.Roots.same(o, t), _),
          w => Some{Judging.Pick.Take{o}},
          w => Judging.Pick.both(f, s, b, o, t)
        )
      )
        == Some{Judging.Pick.Take{o}}: Maybe<&2, Judging.Pick>
    }
    {==}

# Seals
# -----

# Seal.accept_fits once whether the ballot fits is known (f)
def Accept.fits.if(
  f: Bool,
  -x: Basics.Node,
  -s2: Basics.Node
) -> {
  Shared.Maybe.when(Basics.Node, f, u => Some{x}) == Some{s2}: Maybe<&2, Basics.Node>
} -> {f == True{}: Bool}:
  match f:
    case True{}:
      e => {==}
    case False{}:
      e => Empty.absurd({False{} == True{}: Bool}, Shared.Maybe.none_ne_some(Basics.Node, s2, e))

def Spec.Seal.accept_fits(s, b, c, s2):
  ec => ea => Accept.fits.if(
    Sealing.Seal.fits(c, b),
    Basics.State.keyed(
      Basics.State.led(
        s,
        Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
      ),
      Sealing.Keys.saw(
        Sealing.Keys.set(
          Basics.State.keys(s),
          Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
          Sealing.Keychain.next(c, b)
        ),
        Sealing.Ballot.at(b)
      )
    ),
    s2
  )(
    %ec: {Sealing.Seal.accept.at(s, b, _) == Some{s2}: Maybe<&2, Basics.Node>}
    ea)

# a place is the same as itself
def Prev.refl(m: Maybe<&2, Ledgers.Where>) -> {Sealing.Prev.same(m, m) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{w}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), Ledgers.Where.code(w, []))

def Spec.Seal.fits_own(seed, x, last, k, n, f):
  Shared.List.all.if_both(
    Sealing.Prev.same(last, last),
    u => Ledgers.Ballot.sealed(Seals.Seal.public(seed), Ledgers.Ballot.make(seed, x, last, k))
  )(Prev.refl(last))(Ledgers.Ballot.sealed_make(seed, x, last, k))

# a head that no step moves is at its own height
def Level.none(
  x: Basics.Head
) -> {Voting.Heads.level(Some{x}, Some{Head.step(x, None{})}) == True{}: Bool}:
  match x:
    case Basics.Head{r, b, n, t}:
      Shared.Eq.refl(~U32, ~U32.is_eq, Shared.U32.laws(), n)
