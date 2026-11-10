# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/shared/text.bend as Texts
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../voting.bend as Voting
import ./agreement.bend as ProofAgreement
import ./lines.bend as ProofLines

# that the rounds of each height of the line c decide one step in s
def Line.One(s: Basics.Node, c: Ledgers.Chain) -> Type:
  @x: Basics.Head -> @t: Basics.Tip -> {
    Basics.Head.tip(s, x) == Some{t}: Maybe<&2, Basics.Tip>
  } -> Voting.Height.One(s, c, Sealing.Head.next(x), Basics.Line.owners(s, t))

# that the rounds of each of k heights of the line c decide one step in s (one
# witness for each step of a history: a proof uses each once)
def Line.Ones(k: Nat, s: Basics.Node, c: Ledgers.Chain) -> Type:
  match k:
    case 0n:
      Unit
    case 1n+p:
      Line.Ones(p, s, c) & Line.One(s, c)

# Histories
# ---------

# In.grows once the tip m of the head in a is known
def In.grows.at(
  +a: Basics.Node,
  +u: Basics.Node,
  c: Ledgers.Chain,
  +x: Basics.Head,
  r: Nat,
  v: Ledgers.Vote,
  m: Maybe<&2, Basics.Tip>,
  +g: {Reading.Node.grows(a, u) == True{}: Bool}
) -> {
  Basics.Head.tip(a, x) == m: Maybe<&2, Basics.Tip>
} -> {
  Maybe.bind(
    &2,
    Basics.Tip,
    Ledgers.Vote,
    m,
    t => Ledgers.State.decide(
      ~Basics.Ask,
      Basics.State.ledger(a),
      Ledgers.Where{c, Sealing.Head.next(x), r},
      Basics.Line.owners(a, t)
    )
  )
    == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  match m:
    case None{}:
      em => e => Empty.absurd(
        {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>},
        Shared.Maybe.none_ne_some(Ledgers.Vote, v, e)
      )
    case Some{t}:
      em => e =>
        %Equal.sym(
          Maybe<&2, Basics.Tip>,
          Basics.Head.tip(u, x),
          Some{t},
          ProofLines.Head.tip.grows(a, u, x, t, g)(em)
        ): {
          Maybe.bind(
            &2,
            Basics.Tip,
            Ledgers.Vote,
            _,
            t1 => Ledgers.State.decide(
              ~Basics.Ask,
              Basics.State.ledger(u),
              Ledgers.Where{c, Sealing.Head.next(x), r},
              Basics.Line.owners(u, t1)
            )
          )
            == Some{v}: Maybe<&2, Ledgers.Vote>
        }
        ProofAgreement.Decide.up(a, u, t, Ledgers.Where{c, Sealing.Head.next(x), r}, v, g)(e)

# a step that the owners decided at a head in a round, in a, they decided in
# a node that grew
def In.grows(
  +a: Basics.Node,
  u: Basics.Node,
  c: Ledgers.Chain,
  +x: Basics.Head,
  r: Nat,
  v: Ledgers.Vote,
  g: {Reading.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Advance.in(a, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>
} -> {Spec.Advance.in(u, c, x, r) == Some{v}: Maybe<&2, Ledgers.Vote>}:
  In.grows.at(a, u, c, x, r, v, Basics.Head.tip(a, x), g)({==})

# Moved.grows once the step va that a holds at the head is known
def Moved.grows.at(
  a: Basics.Node,
  u: Basics.Node,
  c: Ledgers.Chain,
  x: Basics.Head,
  -y: Basics.Head,
  r: Nat,
  va: Maybe<&2, Ledgers.Vote>,
  g: {Reading.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Advance.in(a, c, x, r) == va: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Head.moved(x, va) == Some{y}: Maybe<&2, Basics.Head>
} -> {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Basics.Head>}:
  match va:
    case None{}:
      ea => e => Empty.absurd(
        {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Basics.Head>},
        Shared.Maybe.none_ne_some(Basics.Head, y, e)
      )
    case Some{v}:
      ea => e =>
        %Equal.sym(
          Maybe<&2, Ledgers.Vote>,
          Spec.Advance.in(u, c, x, r),
          Some{v},
          In.grows(a, u, c, x, r, v, g)(ea)
        ): {Spec.Head.moved(x, _) == Some{y}: Maybe<&2, Basics.Head>}
        e

# a head that a decided step moves in a, it moves the same in a node that grew
def Moved.grows(
  +a: Basics.Node,
  u: Basics.Node,
  +c: Ledgers.Chain,
  +x: Basics.Head,
  -y: Basics.Head,
  +r: Nat,
  g: {Reading.Node.grows(a, u) == True{}: Bool}
) -> {
  Spec.Head.moved(x, Spec.Advance.in(a, c, x, r)) == Some{y}: Maybe<&2, Basics.Head>
} -> {Spec.Head.moved(x, Spec.Advance.in(u, c, x, r)) == Some{y}: Maybe<&2, Basics.Head>}:
  Moved.grows.at(a, u, c, x, y, r, Spec.Advance.in(a, c, x, r), g)({==})

def Spec.Line.at_grows(rs, a, u, c, h, x):
  match rs:
    case Nil{}:
      g => e => e
    case Con{r, +rest}:
      +g => Shared.Maybe.bind_kept(
        Basics.Head,
        Basics.Head,
        Spec.Line.at(rest, a, c, h),
        Spec.Line.at(rest, u, c, h),
        +z => Spec.Head.moved(z, Spec.Advance.in(a, c, z, r)),
        +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r)),
        x,
        +z => Spec.Line.at_grows(rest, a, u, c, h, z)(g),
        +z => Moved.grows(a, u, c, z, x, r, g)
      )

# Step.same once what the two rounds decide is known (w1, w2)
def Step.same.at(
  u: Basics.Node,
  c: Ledgers.Chain,
  z: Basics.Head,
  r1: Nat,
  r2: Nat,
  t: Basics.Tip,
  -x: Basics.Head,
  -y: Basics.Head,
  w1: Maybe<&2, Ledgers.Vote>,
  w2: Maybe<&2, Ledgers.Vote>,
  one: Voting.Height.One(u, c, Sealing.Head.next(z), Basics.Line.owners(u, t))
) -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Basics.State.ledger(u),
    Ledgers.Where{c, Sealing.Head.next(z), r1},
    Basics.Line.owners(u, t)
  )
    == w1: Maybe<&2, Ledgers.Vote>
} -> {
  Ledgers.State.decide(
    ~Basics.Ask,
    Basics.State.ledger(u),
    Ledgers.Where{c, Sealing.Head.next(z), r2},
    Basics.Line.owners(u, t)
  )
    == w2: Maybe<&2, Ledgers.Vote>
} -> {
  Spec.Head.moved(z, w1) == Some{x}: Maybe<&2, Basics.Head>
} -> {Spec.Head.moved(z, w2) == Some{y}: Maybe<&2, Basics.Head>} -> {x == y: Basics.Head}:
  match w1 w2:
    case None{} b:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Basics.Head},
        Shared.Maybe.none_ne_some(Basics.Head, x, k1)
      )
    case Some{v1} None{}:
      e1 => e2 => k1 => k2 => Empty.absurd(
        {x == y: Basics.Head},
        Shared.Maybe.none_ne_some(Basics.Head, y, k2)
      )
    case Some{+v1} Some{v2}:
      e1 => e2 => k1 => k2 => Shared.Maybe.some_inj(
        Basics.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Basics.Head>,
          Some{x},
          Spec.Head.moved(z, Some{v1}),
          Some{y},
          Equal.sym(Maybe<&2, Basics.Head>, Spec.Head.moved(z, Some{v1}), Some{x}, k1),
          Equal.trans(
            Maybe<&2, Basics.Head>,
            Spec.Head.moved(z, Some{v1}),
            Spec.Head.moved(z, Some{v2}),
            Some{y},
            Equal.cong(
              Ledgers.Vote,
              Maybe<&2, Basics.Head>,
              v => Spec.Head.moved(z, Some{v}),
              v1,
              v2,
              one(r1)(r2)(v1)(v2)(e1)(e2)
            ),
            k2
          )
        )
      )

# the steps of two rounds at one head move it the same, once the tip m of
# the head is known
def Step.same(
  +u: Basics.Node,
  +c: Ledgers.Chain,
  +z: Basics.Head,
  +r1: Nat,
  +r2: Nat,
  -x: Basics.Head,
  -y: Basics.Head,
  m: Maybe<&2, Basics.Tip>,
  one: Line.One(u, c)
) -> {
  Basics.Head.tip(u, z) == m: Maybe<&2, Basics.Tip>
} -> {
  Spec.Head.moved(
    z,
    Maybe.bind(
      &2,
      Basics.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Basics.Ask,
        Basics.State.ledger(u),
        Ledgers.Where{c, Sealing.Head.next(z), r1},
        Basics.Line.owners(u, t)
      )
    )
  )
    == Some{x}: Maybe<&2, Basics.Head>
} -> {
  Spec.Head.moved(
    z,
    Maybe.bind(
      &2,
      Basics.Tip,
      Ledgers.Vote,
      m,
      t => Ledgers.State.decide(
        ~Basics.Ask,
        Basics.State.ledger(u),
        Ledgers.Where{c, Sealing.Head.next(z), r2},
        Basics.Line.owners(u, t)
      )
    )
  )
    == Some{y}: Maybe<&2, Basics.Head>
} -> {x == y: Basics.Head}:
  match m:
    case None{}:
      em => k1 => k2 => Empty.absurd(
        {x == y: Basics.Head},
        Shared.Maybe.none_ne_some(Basics.Head, x, k1)
      )
    case Some{+t}:
      em => k1 => k2 =>
        Step.same.at(
          u,
          c,
          z,
          r1,
          r2,
          t,
          x,
          y,
          Ledgers.State.decide(
            ~Basics.Ask,
            Basics.State.ledger(u),
            Ledgers.Where{c, Sealing.Head.next(z), r1},
            Basics.Line.owners(u, t)
          ),
          Ledgers.State.decide(
            ~Basics.Ask,
            Basics.State.ledger(u),
            Ledgers.Where{c, Sealing.Head.next(z), r2},
            Basics.Line.owners(u, t)
          ),
          one(z)(t)(em)
        )({==})({==})(k1)(k2)

# At.same for one more step of each history, once the heads before are known
def At.same.step(
  +u: Basics.Node,
  c: Ledgers.Chain,
  r1: Nat,
  r2: Nat,
  -x: Basics.Head,
  -y: Basics.Head,
  m1: Maybe<&2, Basics.Head>,
  m2: Maybe<&2, Basics.Head>,
  one: Line.One(u, c),
  ih: @z1: Basics.Head -> @z2: Basics.Head -> {
    m1 == Some{z1}: Maybe<&2, Basics.Head>
  } -> {m2 == Some{z2}: Maybe<&2, Basics.Head>} -> {z1 == z2: Basics.Head}
) -> {
  Maybe.bind(
    &2,
    Basics.Head,
    Basics.Head,
    m1,
    +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r1))
  )
    == Some{x}: Maybe<&2, Basics.Head>
} -> {
  Maybe.bind(
    &2,
    Basics.Head,
    Basics.Head,
    m2,
    +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r2))
  )
    == Some{y}: Maybe<&2, Basics.Head>
} -> {x == y: Basics.Head}:
  match m1 m2:
    case None{} b:
      k1 => k2 => Empty.absurd({x == y: Basics.Head}, Shared.Maybe.none_ne_some(Basics.Head, x, k1))
    case Some{z1} None{}:
      k1 => k2 => Empty.absurd({x == y: Basics.Head}, Shared.Maybe.none_ne_some(Basics.Head, y, k2))
    case Some{+z1} Some{z2}:
      k1 => k2 =>
        Step.same(
          u,
          c,
          z1,
          r1,
          r2,
          x,
          y,
          Basics.Head.tip(u, z1),
          one
        )(
          {==}
        )(
          k1
        )(
          Equal.trans(
            Maybe<&2, Basics.Head>,
            Spec.Head.moved(z1, Spec.Advance.in(u, c, z1, r2)),
            Spec.Head.moved(z2, Spec.Advance.in(u, c, z2, r2)),
            Some{y},
            Equal.cong(
              Basics.Head,
              Maybe<&2, Basics.Head>,
              +z => Spec.Head.moved(z, Spec.Advance.in(u, c, z, r2)),
              z1,
              z2,
              ih(z1)(z2)({==})({==})
            ),
            k2
          )
        )

# At.same for one more step of each history, with the witness of each step
def At.same.con(
  +u: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  r1: Nat,
  r2: Nat,
  t1: List<&2, Nat>,
  t2: List<&2, Nat>,
  -x: Basics.Head,
  -y: Basics.Head,
  ones: Line.Ones(List.length(&2, Nat, t1), u, c) & Line.One(u, c),
  ih: @z1: Basics.Head -> @z2: Basics.Head -> Line.Ones(
    List.length(&2, Nat, t1),
    u,
    c
  ) -> {
    Spec.Line.at(t1, u, c, h) == Some{z1}: Maybe<&2, Basics.Head>
  } -> {Spec.Line.at(t2, u, c, h) == Some{z2}: Maybe<&2, Basics.Head>} -> {z1 == z2: Basics.Head}
) -> {
  Spec.Line.at(r1 <> t1, u, c, h) == Some{x}: Maybe<&2, Basics.Head>
} -> {Spec.Line.at(r2 <> t2, u, c, h) == Some{y}: Maybe<&2, Basics.Head>} -> {x == y: Basics.Head}:
  match ones:
    case Tuple{rest, one}:
      At.same.step(
        u,
        c,
        r1,
        r2,
        x,
        y,
        Spec.Line.at(t1, u, c, h),
        Spec.Line.at(t2, u, c, h),
        one,
        z1 => z2 => ih(z1)(z2)(rest)
      )

# in one node, the same number of decided steps from one head give one head,
# whatever the round of each step
def At.same(
  rs1: List<&2, Nat>,
  rs2: List<&2, Nat>,
  +u: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  x: Basics.Head,
  y: Basics.Head
) -> Line.Ones(List.length(&2, Nat, rs1), u, c)
  -> {List.length(&2, Nat, rs1) == List.length(&2, Nat, rs2): Nat}
  -> {Spec.Line.at(rs1, u, c, h) == Some{x}: Maybe<&2, Basics.Head>}
  -> {Spec.Line.at(rs2, u, c, h) == Some{y}: Maybe<&2, Basics.Head>}
  -> {x == y: Basics.Head}:
  match rs1 rs2:
    case Nil{} Nil{}:
      ones => el => e1 => e2 => Shared.Maybe.some_inj(
        Basics.Head,
        x,
        y,
        Equal.trans(
          Maybe<&2, Basics.Head>,
          Some{x},
          Some{h},
          Some{y},
          Equal.sym(Maybe<&2, Basics.Head>, Some{h}, Some{x}, e1),
          e2
        )
      )
    case Nil{} Con{r2, t2}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Basics.Head},
        Shared.Nat.zero_ne_succ(List.length(&2, Nat, t2), el)
      )
    case Con{r1, t1} Nil{}:
      ones => el => e1 => e2 => Empty.absurd(
        {x == y: Basics.Head},
        Shared.Nat.zero_ne_succ(
          List.length(&2, Nat, t1),
          Equal.sym(Nat, 1n+List.length(&2, Nat, t1), 0n, el)
        )
      )
    case Con{+r1, +t1} Con{r2, +t2}:
      ones => el =>
        At.same.con(
          u,
          c,
          h,
          r1,
          r2,
          t1,
          t2,
          x,
          y,
          ones,
          z1 => z2 => rest => At.same(
            t1,
            t2,
            u,
            c,
            h,
            z1,
            z2
          )(rest)(Shared.Nat.succ_inj(List.length(&2, Nat, t1), List.length(&2, Nat, t2), el))
        )

# a step that changes the height of a head moves it one height up
def Moved.step(
  h: Basics.Head,
  v: Ledgers.Vote
) -> {
  Voting.Heads.level(Some{h}, Some{ProofAgreement.Head.step(h, Some{v})}) == False{}: Bool
} -> {
  Spec.Head.moved(h, Some{v}) == Some{ProofAgreement.Head.step(h, Some{v})}: Maybe<&2, Basics.Head>
}:
  match h v:
    case Basics.Head{r, b, n, th} Ledgers.Vote{before, qs, Some{y}}:
      e => {==}
    case Basics.Head{r, b, n, th} Ledgers.Vote{before, qs, None{}}:
      e => Empty.absurd(
        {None{} == Some{Basics.Head{r, b, n, th}}: Maybe<&2, Basics.Head>},
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Voting.Heads.level(Some{Basics.Head{r, b, n, th}}, Some{Basics.Head{r, b, n, th}}),
            True{},
            Equal.sym(
              Bool,
              Voting.Heads.level(Some{Basics.Head{r, b, n, th}}, Some{Basics.Head{r, b, n, th}}),
              False{},
              e
            ),
            ProofAgreement.Level.refl(Basics.Head{r, b, n, th})
          )
        )
      )

# Node.advance_at once the step m that the node found at the head is known
def Advance.at.one(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  ProofAgreement.Advance.vote(s, c, h) == m: Maybe<&2, Ledgers.Vote>
} -> {
  Voting.Heads.level(Some{h}, Some{ProofAgreement.Head.step(h, m)}) == False{}: Bool
} -> Exists(
  Nat,
  q => {Spec.Line.at([q], s, c, h) == Some{ProofAgreement.Head.step(h, m)}: Maybe<&2, Basics.Head>}
):
  match m:
    case None{}:
      em => hl => Empty.absurd(
        Exists(
          Nat,
          q => {
            Spec.Line.at(
              [q],
              s,
              c,
              h
            )
              == Some{ProofAgreement.Head.step(h, None{})}: Maybe<&2, Basics.Head>
          }
        ),
        Shared.Bool.false_ne_true(
          Equal.trans(
            Bool,
            False{},
            Voting.Heads.level(Some{h}, Some{ProofAgreement.Head.step(h, None{})}),
            True{},
            Equal.sym(
              Bool,
              Voting.Heads.level(Some{h}, Some{ProofAgreement.Head.step(h, None{})}),
              False{},
              hl
            ),
            ProofAgreement.Level.none(h)
          )
        )
      )
    case Some{v}:
      em => hl =>
        ProofAgreement.Found.elim(
          Exists(
            Nat,
            q => {
              Spec.Line.at(
                [q],
                s,
                c,
                h
              )
                == Some{ProofAgreement.Head.step(h, Some{v})}: Maybe<&2, Basics.Head>
            }
          ),
          s,
          c,
          h,
          Sealing.Round.seen(s, c, Sealing.Head.next(h)),
          v
        )(em)(t => q => et => d => Tuple{q, (
              %Equal.sym(Maybe<&2, Basics.Tip>, Basics.Head.tip(s, h), Some{t}, et): {Spec.Head.moved(h, Maybe.bind(&2, Basics.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, Sealing.Head.next(h), q}, Basics.Line.owners(s, t1)))) == Some{ProofAgreement.Head.step(h, Some{v})}: Maybe<&2, Basics.Head>}
              %Equal.sym(Maybe<&2, Ledgers.Vote>, Ledgers.State.decide(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, Sealing.Head.next(h), q}, Basics.Line.owners(s, t)), Some{v}, d): {Spec.Head.moved(h, _) == Some{ProofAgreement.Head.step(h, Some{v})}: Maybe<&2, Basics.Head>}
              Moved.step(h, v)(hl))})

def Spec.Node.advance_at(s, c, h):
  +eh => +hl =>
    %Equal.sym(
      Maybe<&2, Basics.Head>,
      Basics.Node.head_of(Voting.Node.advance(s, c), c),
      Some{ProofAgreement.Head.step(h, ProofAgreement.Advance.vote(s, c, h))},
      ProofAgreement.Advance.decided(s, c, h)(eh)(hl)
    ): Exists(Nat, q => {Spec.Line.at([q], s, c, h) == _: Maybe<&2, Basics.Head>})
    Advance.at.one(s, c, h, ProofAgreement.Advance.vote(s, c, h))({==})(
      %ProofAgreement.Advance.decided(s, c, h)(eh)(hl): {Voting.Heads.level(Some{h}, _) == False{}: Bool}
      hl)

def Spec.Node.read_draft(s, w, r, b, n, c):
  e =>
    %Equal.sym(
      Maybe<&2, Basics.Content>,
      Reading.Node.draft(s, w, r, b, n),
      Some{c},
      e
    ): {
      Reading.Read.of(
        s,
        n,
        _,
        Basics.Point.Head{r, b}
      )
        == Basics.Root.bytes(s, Judging.Content.root(s, n, c)): Maybe<&2, Texts.Bytes()>
    }
    {==}
