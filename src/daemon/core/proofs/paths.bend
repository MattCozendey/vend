# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/rope.bend as Ropes
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/trie.bend as Tries
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../reading.bend as Reading
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../stepping.bend as Stepping
import ../voting.bend as Voting
import ./agreement.bend as ProofAgreement
import ./histories.bend as ProofHistories
import ./lines.bend as ProofLines
import ./rounds.bend as ProofRounds
import ./trees.bend as ProofTrees
import ../../replica/impl.bend as Replicas

# Paths
# -----
# Every head is on the decided chain. A node sets a head in four places: a
# step that it checked (Advance.moved), and three that set only a head with no
# tip (Open.at, First.at, Follow.new). So a head that is some decided steps
# from a head with a tip stays so, one more step at a time, whatever the node
# does (Spec.Node.after_on).

# a head one height up has a tip
def Up.held(
  z: Replicas.Head,
  y: Hashes.Hash
) -> {Spec.Head.held(Some{Spec.Head.up(z, y)}) == True{}: Bool}:
  match z:
    case Replicas.Head{r, b, n, th}:
      {==}

# Moved.held once the tip m that the step names is known
def Moved.held.at(
  z: Replicas.Head,
  m: Maybe<&2, Hashes.Hash>,
  -h: Replicas.Head
) -> {
  Maybe.bind(
    &2,
    Hashes.Hash,
    Replicas.Head,
    m,
    y => Some{Spec.Head.up(z, y)}
  )
    == Some{h}: Maybe<&2, Replicas.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Spec.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Head, h, e)
      )
    case Some{y}:
      e =>
        %e: {Spec.Head.held(_) == True{}: Bool}
        Up.held(z, y)

# a head that a step moved has a tip
def Moved.held(
  z: Replicas.Head,
  va: Maybe<&2, Ledgers.Vote>,
  -h: Replicas.Head
) -> {
  Spec.Head.moved(z, va) == Some{h}: Maybe<&2, Replicas.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  Moved.held.at(z, Spec.Vote.tip(va), h)

# Held.at for one more step, once the head m before it is known
def Held.at.step(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Nat,
  -h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    Replicas.Head,
    m,
    +x => Spec.Head.moved(x, Spec.Advance.in(s, c, x, r))
  )
    == Some{h}: Maybe<&2, Replicas.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match m:
    case None{}:
      e => Empty.absurd(
        {Spec.Head.held(Some{h}) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Head, h, e)
      )
    case Some{+z}:
      e => Moved.held(z, Spec.Advance.in(s, c, z, r), h)(e)

# a head that is some decided steps from a head with a tip has a tip
def Held.at(
  rs: List<&2, Nat>,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h0: Replicas.Head,
  -h: Replicas.Head
) -> {
  Spec.Head.held(Some{h0}) == True{}: Bool
} -> {
  Spec.Line.at(rs, s, c, h0) == Some{h}: Maybe<&2, Replicas.Head>
} -> {Spec.Head.held(Some{h}) == True{}: Bool}:
  match rs:
    case Nil{}:
      t0 => e =>
        %e: {Spec.Head.held(_) == True{}: Bool}
        t0
    case Con{r, rest}:
      t0 => e => Held.at.step(s, c, r, h, Spec.Line.at(rest, s, c, h0))(e)

# a node is on its own paths
def Path.refl(-s: Replicas.Node<Basics.Ask>) -> Spec.Node.On(s, s):
  c => h0 => t0 => ra => ra

# paths compose
def Path.trans(
  -a: Replicas.Node<Basics.Ask>,
  -b: Replicas.Node<Basics.Ask>,
  -d: Replicas.Node<Basics.Ask>,
  h1: Spec.Node.On(a, b),
  h2: Spec.Node.On(b, d)
) -> Spec.Node.On(a, d):
  +c => +h0 => +t0 => ra => h2(c)(h0)(t0)(h1(c)(h0)(t0)(ra))

# one of two nodes, each on the paths of s
def Path.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: Spec.Node.On(s, x),
  hy: Spec.Node.On(s, y)
) -> Spec.Node.On(s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a line whose head is the same in a node that grew is where it was
def Reach.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h0: Replicas.Head,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Replicas.Node.head_of(~Basics.Ask.machine(), b, c): Maybe<&2, Replicas.Head>},
  ra: Spec.Line.Reach(a, c, h0)
) -> Spec.Line.Reach(b, c, h0):
  match ra:
    case Tuple{+rs, Tuple{+h, Tuple{e1, e2}}}:
      Tuple{
        rs,
        Tuple{
          h,
          Tuple{
            Equal.trans(
              Maybe<&2, Replicas.Head>,
              Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
              Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
              Some{h},
              Equal.sym(
                Maybe<&2, Replicas.Head>,
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
                eh
              ),
              e1
            ),
            Spec.Line.at_grows(rs, a, b, c, h0, h)(g)(e2)
          }
        }
      }

# a node that grew, with the same heads, is on the paths
def Path.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b): Tries.Trie<Replicas.Head>}
) -> Spec.Node.On(a, b):
  +c => +h0 => t0 => ra => Reach.same(
    a,
    b,
    c,
    h0,
    g,
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b),
      eh
    ),
    ra
  )

# the head of another line, after the head of the line c is set
def Head.other(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain,
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == False{}: Bool}
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), 
    a,
    c2
  )
    == Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2): Maybe<&2, Replicas.Head>
}:
  Equal.trans(
    Maybe<&2, Replicas.Head>,
    Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
    Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
    Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2),
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c2)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      eh
    ),
    Equal.sym(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2),
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
      Equal.trans(
        Maybe<&2, Replicas.Head>,
        Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2),
        Bool.pick(
          Maybe<&2, Replicas.Head>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
        ),
        Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
        ProofLines.Head.of_set(b0, c, hd, c2),
        ProofLines.Pick.of(
          Maybe<&2, Replicas.Head>,
          False{},
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{hd},
          Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
          ebs
        )
      )
    )
  )

# the head of a line with the key of the line c, after the head of c is set
def Head.this(
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == True{}: Bool}
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2) == Some{hd}: Maybe<&2, Replicas.Head>}:
  Equal.trans(
    Maybe<&2, Replicas.Head>,
    Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2),
    Bool.pick(
      Maybe<&2, Replicas.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
    ),
    Some{hd},
    ProofLines.Head.of_set(b0, c, hd, c2),
    ProofLines.Pick.of(
      Maybe<&2, Replicas.Head>,
      True{},
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
      ebs
    )
  )

# lines with the same key have the same head
def Head.keyed(
  a: Replicas.Node<Basics.Ask>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), a, c2) == Replicas.Node.head_of(~Basics.Ask.machine(), a, c): Maybe<&2, Replicas.Head>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Replicas.Head>,
    kk => Tries.Trie.get(Replicas.Head, Replicas.State.heads(~Basics.Ask.machine(), a), kk),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# lines with the same key have the same decided steps
def In.key(
  s: Replicas.Node<Basics.Ask>,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  x: Replicas.Head,
  r: Nat,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Spec.Advance.in(s, c2, x, r) == Spec.Advance.in(s, c, x, r): Maybe<&2, Ledgers.Vote>}:
  Equal.cong(
    List<&2, Bool>,
    Maybe<&2, Ledgers.Vote>,
    kk => Maybe.bind(
      &2,
      Replicas.Tip,
      Ledgers.Vote,
      Replicas.Head.tip(~Basics.Ask.machine(), s, x),
      t => Ledgers.Bucket.decide(
        ~Basics.Ask,
        Ledgers.State.under(
          ~Basics.Ask,
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          List.append(
            &2,
            Bool,
            List.append(&2, Bool, False{} <> True{} <> kk, Ledgers.Word.key(Sealing.Head.next(x))),
            Ledgers.Round.key(r, [False{}])
          )
        ),
        Replicas.Tip.owners(t)
      )
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# no line with the key of c is some decided steps from a head with a tip, when
# the head of c has no tip
def Path.set.no(
  +a: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  nh: {Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool},
  t0: {Spec.Head.held(Some{h0}) == True{}: Bool},
  ra: Spec.Line.Reach(a, c2, h0)
) -> Empty:
  match ra:
    case Tuple{rs, Tuple{h, Tuple{e1, e2}}}:
      Shared.Bool.false_ne_true(
        Equal.trans(
          Bool,
          False{},
          Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)),
          True{},
          Equal.sym(Bool, Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)), False{}, nh),
          Equal.trans(
            Bool,
            Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)),
            Spec.Head.held(Some{h}),
            True{},
            Equal.cong(
              Maybe<&2, Replicas.Head>,
              Bool,
              Spec.Head.held,
              Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
              Some{h},
              Equal.trans(
                Maybe<&2, Replicas.Head>,
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
                Some{h},
                Equal.sym(
                  Maybe<&2, Replicas.Head>,
                  Replicas.Node.head_of(~Basics.Ask.machine(), a, c2),
                  Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
                  Head.keyed(a, c2, c, ek)
                ),
                e1
              )
            ),
            Held.at(rs, a, c2, h0, h)(t0)(e2)
          )
        )
      )

# Path.set for the line c2, once it is known whether it has the key of c (bs)
def Path.set.if(
  +a: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +hd: Replicas.Head,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  bs: Bool,
  ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  nh: {Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool},
  t0: {Spec.Head.held(Some{h0}) == True{}: Bool},
  ra: Spec.Line.Reach(a, c2, h0)
) -> Spec.Line.Reach(Sealing.State.head(b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Empty.absurd(
        Spec.Line.Reach(Sealing.State.head(b0, c, hd), c2, h0),
        Path.set.no(a, c, c2, h0, ProofRounds.Key.same(c2, c)(ebs), nh, t0, ra)
      )
    case False{}:
      Reach.same(
        a,
        Sealing.State.head(b0, c, hd),
        c2,
        h0,
        ProofTrees.Grows.to(
          a,
          b0,
          Sealing.State.head(b0, c, hd),
          ProofTrees.Led.head(b0, c, hd),
          g
        ),
        Head.other(a, b0, c, hd, c2, eh, ebs),
        ra
      )

# a node b0 with a new head hd of the line c is on the paths of a, when b0
# grew from a with the same heads, and the head of c in a has no tip
def Path.set(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  hd: Replicas.Head,
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  nh: {Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), a, c)) == False{}: Bool}
) -> Spec.Node.On(a, Sealing.State.head(b0, c, hd)):
  +c2 => +h0 => t0 => ra => Path.set.if(
    a,
    b0,
    c,
    hd,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    nh,
    t0,
    ra
  )

# Path.moved for a line with the key of c: one more decided step
def Path.moved.yes(
  +s: Replicas.Node<Basics.Ask>,
  +n: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  hd: Replicas.Head,
  +q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  +ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>},
  +gn: {Reading.Node.grows(s, n) == True{}: Bool},
  en: {Replicas.Node.head_of(~Basics.Ask.machine(), n, c2) == Some{hd}: Maybe<&2, Replicas.Head>},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>},
  ra: Spec.Line.Reach(s, c2, h0)
) -> Spec.Line.Reach(n, c2, h0):
  match ra:
    case Tuple{+rs, Tuple{h2, Tuple{e1, e2}}}:
      Tuple{
        q <> rs,
        Tuple{
          hd,
          Tuple{
            en,
            Equal.trans(
              Maybe<&2, Replicas.Head>,
              Spec.Line.at(q <> rs, n, c2, h0),
              Spec.Head.moved(h2, Spec.Advance.in(n, c2, h2, q)),
              Some{hd},
              Equal.cong(
                Maybe<&2, Replicas.Head>,
                Maybe<&2, Replicas.Head>,
                m => Maybe.bind(
                  &2,
                  Replicas.Head,
                  Replicas.Head,
                  m,
                  +z => Spec.Head.moved(z, Spec.Advance.in(n, c2, z, q))
                ),
                Spec.Line.at(rs, n, c2, h0),
                Some{h2},
                Spec.Line.at_grows(rs, s, n, c2, h0, h2)(gn)(e2)
              ),
              Equal.trans(
                Maybe<&2, Replicas.Head>,
                Spec.Head.moved(h2, Spec.Advance.in(n, c2, h2, q)),
                Spec.Head.moved(h, Spec.Advance.in(n, c2, h, q)),
                Some{hd},
                Equal.cong(
                  Replicas.Head,
                  Maybe<&2, Replicas.Head>,
                  +z => Spec.Head.moved(z, Spec.Advance.in(n, c2, z, q)),
                  h2,
                  h,
                  Shared.Maybe.some_inj(
                    Replicas.Head,
                    h2,
                    h,
                    Equal.trans(
                      Maybe<&2, Replicas.Head>,
                      Some{h2},
                      Replicas.Node.head_of(~Basics.Ask.machine(), s, c2),
                      Some{h},
                      Equal.sym(Maybe<&2, Replicas.Head>, Replicas.Node.head_of(~Basics.Ask.machine(), s, c2), Some{h2}, e1),
                      Equal.trans(
                        Maybe<&2, Replicas.Head>,
                        Replicas.Node.head_of(~Basics.Ask.machine(), s, c2),
                        Replicas.Node.head_of(~Basics.Ask.machine(), s, c),
                        Some{h},
                        Head.keyed(s, c2, c, ek),
                        em
                      )
                    )
                  )
                ),
                Equal.trans(
                  Maybe<&2, Replicas.Head>,
                  Spec.Head.moved(h, Spec.Advance.in(n, c2, h, q)),
                  Spec.Head.moved(h, Some{v}),
                  Some{hd},
                  Equal.cong(
                    Maybe<&2, Ledgers.Vote>,
                    Maybe<&2, Replicas.Head>,
                    w => Spec.Head.moved(h, w),
                    Spec.Advance.in(n, c2, h, q),
                    Some{v},
                    Equal.trans(
                      Maybe<&2, Ledgers.Vote>,
                      Spec.Advance.in(n, c2, h, q),
                      Spec.Advance.in(n, c, h, q),
                      Some{v},
                      In.key(n, c2, c, h, q, ek),
                      ProofHistories.In.grows(s, n, c, h, q, v, gn)(ein)
                    )
                  ),
                  emv
                )
              )
            )
          }
        }
      }

# Path.moved for the line c2, once it is known whether it has the key of c
def Path.moved.if(
  +s: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +hd: Replicas.Head,
  q: Nat,
  v: Ledgers.Vote,
  +c2: Ledgers.Chain,
  h0: Replicas.Head,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Reading.Node.grows(s, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>},
  ra: Spec.Line.Reach(s, c2, h0)
) -> Spec.Line.Reach(Sealing.State.head(b0, c, hd), c2, h0):
  match bs:
    case True{}:
      Path.moved.yes(
        s,
        Sealing.State.head(b0, c, hd),
        c,
        h,
        hd,
        q,
        v,
        c2,
        h0,
        ProofRounds.Key.same(c2, c)(ebs),
        ProofTrees.Grows.to(
          s,
          b0,
          Sealing.State.head(b0, c, hd),
          ProofTrees.Led.head(b0, c, hd),
          g
        ),
        Head.this(b0, c, hd, c2, ebs),
        em,
        ein,
        emv,
        ra
      )
    case False{}:
      Reach.same(
        s,
        Sealing.State.head(b0, c, hd),
        c2,
        h0,
        ProofTrees.Grows.to(
          s,
          b0,
          Sealing.State.head(b0, c, hd),
          ProofTrees.Led.head(b0, c, hd),
          g
        ),
        Head.other(s, b0, c, hd, c2, eh, ebs),
        ra
      )

# a head moved over the step v that the owners decided at it, in the round
# q, is one more decided step on its path
def Path.moved(
  +s: Replicas.Node<Basics.Ask>,
  +s3: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  hd: Replicas.Head,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g3: {Reading.Node.grows(s, s3) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>}
) -> Spec.Node.On(s, Sealing.State.moved(Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)), c, hd, qs)):
  +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +ws = Sealing.Wait.left(
    Sealing.Wait.of(x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Sealing.Wait.set(x, c, ws)
  +c2 => +h0 => t0 => ra => Path.moved.if(
    s,
    b0,
    c,
    h,
    hd,
    q,
    v,
    c2,
    h0,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    ProofTrees.Grows.to(s, x, b0, ProofTrees.Led.wait(x, c, ws), ProofTrees.Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Replicas.Head>,
      Replicas.State.heads(~Basics.Ask.machine(), s),
      Replicas.State.heads(~Basics.Ask.machine(), x),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      ProofLines.Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
      ProofLines.Heads.wait(x, c, ws)
    ),
    em,
    ein,
    emv,
    ra
  )

# Advance.moved is on the paths, once the node m that the put gives is known
def Advance.moved.path(
  +s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  hd: Replicas.Head,
  t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  q: Nat,
  v: Ledgers.Vote,
  g2: {Reading.Node.grows(s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  ein: {Spec.Advance.in(s, c, h, q) == Some{v}: Maybe<&2, Ledgers.Vote>},
  emv: {Spec.Head.moved(h, Some{v}) == Some{hd}: Maybe<&2, Replicas.Head>}
) -> {
  Judging.State.put(s2, [Replicas.Tip.words(t2)]) == m: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> Spec.Node.On(s, Voting.Advance.moved(s, m, c, hd, qs)):
  match m:
    case None{}:
      e2 => Path.refl(s)
    case Some{+s3}:
      e2 => Path.moved(
        s,
        s3,
        c,
        h,
        hd,
        qs,
        q,
        v,
        ProofTrees.Grows.trans(
          s,
          s2,
          s3
        )(g2)(ProofLines.Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)),
        em,
        ein,
        emv
      )

# Advance.ran is on the paths, once it is known whether the run gives the tip
# that the step names (bq)
def Advance.ran.path.if(
  s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  c: Ledgers.Chain,
  +r: Ledgers.Id,
  +br: Maybe<&2, String>,
  +next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  +qs: List<&2, Ledgers.Id>,
  q: Nat,
  bq: Bool,
  ebq: {Sealing.Root.same(after, Some{Replicas.Tip.hash(t2)}) == bq: Bool},
  g2: {Reading.Node.grows(s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{Replicas.Head{r, br, next, th}}: Maybe<&2, Replicas.Head>},
  ein: {
    Spec.Advance.in(
      s,
      c,
      Replicas.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> Spec.Node.On(
  s,
  Shared.Bool.when(
    Replicas.Node<Basics.Ask>,
    bq,
    u => Voting.Advance.moved(
      s,
      Judging.State.put(s2, [Replicas.Tip.words(t2)]),
      c,
      Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
      qs
    ),
    u => s
  )
):
  match bq:
    case True{}:
      Advance.moved.path(
        s,
        s2,
        Judging.State.put(s2, [Replicas.Tip.words(t2)]),
        c,
        Replicas.Head{r, br, next, th},
        Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
        t2,
        qs,
        q,
        Ledgers.Vote{before, qs, after},
        g2,
        em,
        ein,
        Equal.cong(
          Maybe<&2, Hashes.Hash>,
          Maybe<&2, Replicas.Head>,
          a => Maybe.bind(
            &2,
            Hashes.Hash,
            Replicas.Head,
            a,
            y => Some{Spec.Head.up(Replicas.Head{r, br, next, th}, y)}
          ),
          after,
          Some{Replicas.Tip.hash(t2)},
          Shared.Maybe.is_eq_sound(
            ~Hashes.Hash,
            ~Hashes.Hash.is_eq,
            Hashes.Hash.is_eq_sound,
            after,
            Some{Replicas.Tip.hash(t2)}
          )(ebq)
        )
      )({==})
    case False{}:
      Path.refl(s)

# a checked step is on the paths
def Advance.ran.path(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  th: Maybe<&2, Hashes.Hash>,
  before: Maybe<&2, Hashes.Hash>,
  +after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>,
  q: Nat,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{Replicas.Head{r, br, next, th}}: Maybe<&2, Replicas.Head>},
  ein: {
    Spec.Advance.in(
      s,
      c,
      Replicas.Head{r, br, next, th},
      q
    )
      == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>
  }
) -> {
  ProofTrees.Run.after(s, m) == True{}: Bool
} -> Spec.Node.On(s, Voting.Advance.ran(s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => Path.refl(s)
    case Some{Stepping.Run{s2, +t2}}:
      ga => Advance.ran.path.if(
        s,
        s2,
        t2,
        c,
        r,
        br,
        next,
        th,
        before,
        after,
        qs,
        q,
        Sealing.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        {==},
        ga,
        em,
        ein
      )

# Node.advance is on the paths, once the decided step m is known
def Advance.step.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>}
  -> {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
  -> {
    Voting.Height.decide(
      s,
      c,
      Sealing.Head.next(h),
      Replicas.Tip.owners(t),
      Sealing.Round.seen(s, c, Sealing.Head.next(h))
    )
      == m: Maybe<&2, Ledgers.Vote>
  }
  -> Spec.Node.On(s, Voting.Advance.step(s, c, h, t, m)):
  match h m:
    case Replicas.Head{r, br, +next, +th} Some{Ledgers.Vote{+before, +qs, after}}:
      em => et => ed => Path.when(
        Sealing.Root.same(before, th),
        s,
        Voting.Advance.ran(s, c, r, br, next, after, qs, Stepping.Step.run(s, c, t, qs)),
        s,
        ProofAgreement.Scan.elim(
          Spec.Node.On(
            s,
            Voting.Advance.ran(s, c, r, br, next, after, qs, Stepping.Step.run(s, c, t, qs))
          ),
          s,
          c,
          next,
          Replicas.Tip.owners(t),
          Sealing.Round.seen(s, c, next),
          Ledgers.Vote{before, qs, after}
        )(
          ed
        )(
          q => d => Advance.ran.path(
            s,
            c,
            r,
            br,
            next,
            th,
            before,
            after,
            qs,
            Stepping.Step.run(s, c, t, qs),
            q,
            em,
            (
              %Equal.sym(Maybe<&2, Replicas.Tip>, Replicas.Head.tip(~Basics.Ask.machine(), s, Replicas.Head{r, br, next, th}), Some{t}, et): {Maybe.bind(&2, Replicas.Tip, Ledgers.Vote, _, t1 => Ledgers.State.decide(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, next, q}, Replicas.Tip.owners(t1))) == Some{Ledgers.Vote{before, qs, after}}: Maybe<&2, Ledgers.Vote>}
              d)
          )(ProofTrees.Run.grows(s, c, t, qs))
        ),
        Path.refl(s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => ed => Path.refl(s)

# Node.advance is on the paths, at the head h whose tip is m
def Advance.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
} -> Spec.Node.On(s, Voting.Advance.at(s, c, h, m)):
  match m:
    case None{}:
      em => et => Path.refl(s)
    case Some{+t}:
      em => et => Advance.step.path(
        s,
        c,
        h,
        t,
        Voting.Height.decide(
          s,
          c,
          Sealing.Head.next(h),
          Replicas.Tip.owners(t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )(em)(et)({==})

# a node's ballot keeps its logs
def Cast.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Voting.Node.cast(n, s, c)):
  Path.same(
    s,
    Voting.Node.cast(n, s, c),
    ProofTrees.Cast.grows(n, s, c),
    ProofLines.Cast.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  )

# Advances.kept once the head m is known
def Advances.at.path(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.On(s, Voting.Advances.at(f, s, c, m)):
  match f m:
    case 0n x:
      em => Path.refl(s)
    case 1n+p None{}:
      em => Path.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Voting.Advance.at(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Path.when(
          Voting.Heads.level(Some{h}, m1),
          s,
          s1,
          Voting.Advances.at(p, s1, c, m1),
          Advance.at.path(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Path.trans(
            s,
            s1,
            Voting.Advances.at(p, s1, c, m1),
            Advance.at.path(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
            Advances.at.path(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step is on the paths
def Advances.path(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Voting.Node.advances(f, s, c)):
  Advances.at.path(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==})

# what a node does at a head is on the paths
def Step.head.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Voting.Step.head(n, s, c)):
  +s1 = Voting.Node.advances(4294967295n, s, c)
  +s2 = Voting.Node.cast(n, s1, c)
  s3 = Voting.Node.advances(4294967295n, s2, c)
  Path.trans(
    s,
    s1,
    s3,
    Advances.path(4294967295n, s, c),
    Path.trans(s1, s2, s3, Cast.path(n, s1, c), Advances.path(4294967295n, s2, c))
  )

# a head with no tip is not held
def Held.not(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>}
) -> {Spec.Head.held(Replicas.Node.head_of(~Basics.Ask.machine(), s, c)) == Spec.Head.held(m): Bool}:
  Equal.cong(Maybe<&2, Replicas.Head>, Bool, Spec.Head.held, Replicas.Node.head_of(~Basics.Ask.machine(), s, c), m, em)

# a branch that opens is on the paths, once the head m of the line is known
def Open.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.On(s, Sealing.Open.at(s, c, m)):
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        Replicas.Head{
          r,
          Some{b},
          0,
          Sealing.Branch.first(s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
        },
        ProofTrees.Grows.refl(s),
        {==},
        Held.not(s, c, Some{Replicas.Head{r, Some{b}, n, None{}}}, em)
      )
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      em => Path.refl(s)
    case None{}:
      em => Path.refl(s)

# what a node does on a line is on the paths
def Step.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Voting.Node.step(n, s, c)):
  s1 = Sealing.Node.open(s, c)
  Path.trans(
    s,
    s1,
    Voting.Step.head(n, s1, c),
    Open.at.path(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==}),
    Step.head.path(n, s1, c)
  )

# a pass to the next round is on the paths
def Pass.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.On(s, Voting.Node.pass(n, s, c)):
  +s1 = Voting.Pass.head(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Path.trans(
    s,
    s1,
    Voting.Node.step(n, s1, c),
    Path.same(
      s,
      s1,
      ProofTrees.Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      ProofLines.Pass.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
    ),
    Step.path(n, s1, c)
  )

# a first head is on the paths, once the head m of the line is known
def First.at.path(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.On(s, Sealing.First.at(s, c, h, m)):
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      em => Path.refl(s)
    case Some{Replicas.Head{+r, +b, +n, None{}}}:
      em => Path.set(
        s,
        s,
        c,
        h,
        ProofTrees.Grows.refl(s),
        {==},
        Held.not(s, c, Some{Replicas.Head{r, b, n, None{}}}, em)
      )
    case None{}:
      em => Path.set(s, s, c, h, ProofTrees.Grows.refl(s), {==}, Held.not(s, c, None{}, em))

# a first head on a node that grew from a, which grew from s, is on the paths
def Start.head.path(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  ProofTrees.State.after(a, m) == True{}: Bool
} -> Spec.Node.On(s, Sealing.Start.head(s, m, c, h)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Path.trans(
          s,
          x,
          Sealing.State.first(x, c, h),
          Path.same(
            s,
            x,
            ProofTrees.Grows.back(s, s3, ProofTrees.Grows.trans(s, a, s3)(g)(e)),
            ProofLines.Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          ),
          First.at.path(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c))({==})
        )

# Start.path once the content m of the store is known
def Start.with.path(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Judging.Work>
) -> {
  ProofTrees.Work.after(s, m) == True{}: Bool
} -> Spec.Node.On(s, Sealing.Start.with(s, i, os, m)):
  match m:
    case None{}:
      e => Path.refl(s)
    case Some{Judging.Work{+s2, +c}}:
      e =>
        +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
        Start.head.path(
          s,
          s2,
          Judging.State.put(s2, [Replicas.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}},
          e
        )(ProofTrees.Put.grows(s2, [Replicas.Tip.words(t)]))

# a store that starts is on the paths
def Start.path(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Basics.Owner>
) -> Spec.Node.On(s, Sealing.Node.start(s, i, os)):
  Start.with.path(
    s,
    i,
    Basics.Owner.names(os),
    Sealing.Seal.firsts(os, Some{Judging.Work{s, None{}}})
  )(ProofTrees.Firsts.after(s, os, Some{Judging.Work{s, None{}}})(ProofTrees.Grows.refl(s)))

# a line that a node starts to follow is on the paths
def Follow.new.path(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.On(s, Sealing.Follow.new(s, r, l, m)):
  match m:
    case Some{h}:
      em => Path.refl(s)
    case None{}:
      em => Path.set(
        s,
        s,
        Replicas.Line.chain(r, l),
        Replicas.Head{r, l, 0, None{}},
        ProofTrees.Grows.refl(s),
        {==},
        Held.not(s, Replicas.Line.chain(r, l), None{}, em)
      )

# a new request is on the paths
def Arrive.path(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> Spec.Node.On(s, Sealing.Node.arrive(s, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      Start.path(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Sealing.Node.follow(s, r, l)
      Path.trans(
        s,
        s1,
        Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
        Follow.new.path(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Path.same(
          s1,
          Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
          ProofTrees.Grows.to(
            s1,
            s1,
            Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
            ProofTrees.Led.waits(s1, Replicas.Line.chain(r, l), i),
            ProofTrees.Grows.refl(s1)
          ),
          ProofLines.Heads.waits(s1, Replicas.Line.chain(r, l), i)
        )
      )

# a new request is on the paths
def Ask.new.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> Spec.Node.On(s, Voting.Node.ask.new(n, s, e, q)):
  +i = Replicas.Envelope.of(e)
  c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Replicas.State.ledger(~Basics.Ask.machine(), s),
    i,
    Replicas.Envelope.time(e),
    q
  )
  +s0 = Replicas.State.led(~Basics.Ask.machine(), s, l0)
  s1 = Sealing.Node.arrive(s0, i, q)
  Path.trans(
    s,
    s0,
    Voting.Node.step(n, s1, c),
    Path.same(
      s,
      s0,
      ProofTrees.Grows.led(
        s,
        l0,
        Ledgers.State.add_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~Basics.Ask.laws(),
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, Replicas.Envelope.time(e), q}
        )
      ),
      ProofLines.Heads.led(s, l0)
    ),
    Path.trans(s0, s1, Voting.Node.step(n, s1, c), Arrive.path(s0, i, q), Step.path(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Spec.Node.On(s, Voting.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Path.refl(s)
    case None{}:
      Path.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Voting.Node.ask.new(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        ),
        Path.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          ProofTrees.Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            ProofTrees.Grows.refl(s)
          ),
          ProofLines.Heads.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
        ),
        Ask.new.path(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask is on the paths
def Ask.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask
) -> Spec.Node.On(s, Voting.Node.ask(n, s, e, q)):
  Ask.at.path(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e)))
  )

# the new requests among cells are on the paths
def Take.asks.path(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>
) -> Spec.Node.On(s, Voting.Take.asks(cs, old, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Replicas.Node<Basics.Ask>,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Sealing.Node.arrive(s, i, q),
        u => s
      )
      Path.trans(
        s,
        s1,
        Voting.Take.asks(rest, old, s1),
        Path.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Sealing.Node.arrive(s, i, q),
          s,
          Arrive.path(s, i, q),
          Path.refl(s)
        ),
        Take.asks.path(rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.path(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.path(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.path(rest, old, s)

# Node.take is on the paths
def Take.path(
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.On(s, Voting.Node.take(s, t)):
  +sent = Voting.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), sent)
  +s1 = Replicas.State.led(~Basics.Ask.machine(), s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  Path.trans(
    s,
    s1,
    Sealing.Sealed.take(bs, s2),
    Path.same(
      s,
      s1,
      ProofTrees.Grows.led(
        s,
        l1,
        Ledgers.State.take_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~Basics.Ask.laws(),
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          sent
        )
      ),
      ProofLines.Heads.led(s, l1)
    ),
    Path.trans(
      s1,
      s2,
      Sealing.Sealed.take(bs, s2),
      Take.asks.path(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
      Path.same(
        s2,
        Sealing.Sealed.take(bs, s2),
        ProofTrees.Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2),
        ProofLines.Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines is on the paths
def Steps.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Spec.Node.On(s, Voting.Node.steps(n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      s1 = Voting.Node.step(n, s, c)
      Path.trans(s, s1, Voting.Node.steps(n, rest, s1), Step.path(n, s, c), Steps.path(n, rest, s1))

# an adoption is on the paths, once the request m is known
def Adopt.ask.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Reading.Request>
) -> Spec.Node.On(s, Reading.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Reading.Request{e, q}}:
      Ask.path(n, s, e, q)

# an adoption is on the paths, once the head m of the line is known
def Adopt.head.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Spec.Node.On(s, Reading.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.path(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line is on the paths
def Adopt.at.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Spec.Node.On(s, Reading.Adopt.at(n, s, c)):
  Adopt.head.path(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, is on the paths
def Adopt.maybe.path(
  n: String,
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.On(s, Reading.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Adopt.at.path(n, s, c)

# the adoption of each of some lines is on the paths
def Adopts.path(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Replicas.Node<Basics.Ask>
) -> Spec.Node.On(s, Reading.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Path.refl(s)
    case Con{+c, rest}:
      Path.trans(
        s,
        Reading.Adopt.at(n, s, c),
        Reading.Node.adopts(n, rest, Reading.Adopt.at(n, s, c)),
        Adopt.at.path(n, s, c),
        Adopts.path(n, rest, Reading.Adopt.at(n, s, c))
      )

# more rounds of a sync, path
def More.path(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> Spec.Node.On(s, Reading.Sync.more(f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Path.refl(s)
    case 1n+(p):
      Path.when(
        Reading.Lines.level(cs, s, Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))),
        s,
        Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
        Reading.Sync.more(
          p,
          n,
          cs,
          k,
          bs,
          pd,
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
        ),
        Path.trans(
          s,
          Sealing.Sealed.each(k, bs, pd, s),
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
          Path.same(
            s,
            Sealing.Sealed.each(k, bs, pd, s),
            ProofTrees.Each.grows(k, bs, pd, s),
            ProofLines.Each.heads(k, bs, pd, s)
          ),
          Steps.path(n, cs, Sealing.Sealed.each(k, bs, pd, s))
        ),
        Path.trans(
          s,
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
          Reading.Sync.more(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          ),
          Path.trans(
            s,
            Sealing.Sealed.each(k, bs, pd, s),
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
            Path.same(
              s,
              Sealing.Sealed.each(k, bs, pd, s),
              ProofTrees.Each.grows(k, bs, pd, s),
              ProofLines.Each.heads(k, bs, pd, s)
            ),
            Steps.path(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          ),
          More.path(
            p,
            n,
            cs,
            k,
            bs,
            pd,
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          )
        )
      )

# a sync is on the paths
def Sync.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.On(s, Reading.Node.sync(n, s, t)):
  +s1 = Voting.Node.take(s, t)
  +cs = Voting.Sync.lines(s, s1, t)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Replicas.State.ledger(~Basics.Ask.machine(), s))
    )
  )
  +s2 = Voting.Node.steps(n, cs, s1)
  s3 = Reading.Sync.more(
    List.length(&2, Ledgers.Ballot, bs),
    n,
    cs,
    List.length(&2, Ledgers.Ballot, bs),
    bs,
    Sealing.Pending.of(bs),
    s2
  )
  Path.trans(
    s,
    s1,
    Reading.Node.adopts(n, cs, s3),
    Take.path(s, t),
    Path.trans(
      s1,
      s2,
      Reading.Node.adopts(n, cs, s3),
      Steps.path(n, cs, s1),
      Path.trans(
        s2,
        s3,
        Reading.Node.adopts(n, cs, s3),
        More.path(
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Sealing.Pending.of(bs),
          s2
        ),
        Adopts.path(n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node is on the paths
def Consent.path(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.On(s, Voting.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Path.refl(s)
    case Some{c}:
      Path.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Voting.Node.step(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Path.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          ProofTrees.Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            ProofTrees.Grows.refl(s)
          ),
          ProofLines.Heads.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.path(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does is on the paths
def Does.path(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Spec.Deed
) -> Spec.Node.On(s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Path.trans(
        s,
        Voting.Node.ask(n, s, e, q),
        Reading.Adopt.at(
          n,
          Voting.Node.ask(n, s, e, q),
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
        ),
        Ask.path(n, s, e, q),
        Adopt.at.path(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
      )
    case Spec.Deed.Take{t}:
      Take.path(s, t)
    case Spec.Deed.Sync{t}:
      Sync.path(n, s, t)
    case Spec.Deed.Keep{+b}:
      Path.same(
        s,
        Basics.Node.keep(s, b),
        ProofTrees.Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b))),
        ProofLines.Heads.led(
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Basics.Bytes.rope(b)),
            Replicas.State.ledger(~Basics.Ask.machine(), s)
          )
        )
      )
    case Spec.Deed.Consent{+i}:
      Path.trans(
        s,
        Voting.Node.consent(n, s, i),
        Reading.Adopt.maybe(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i)),
        Consent.path(n, s, i, Basics.Node.chain_of(s, i)),
        Adopt.maybe.path(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i))
      )
    case Spec.Deed.Pass{+c}:
      Path.trans(
        s,
        Voting.Node.pass(n, s, c),
        Reading.Adopt.at(n, Voting.Node.pass(n, s, c), c),
        Pass.path(n, s, c),
        Adopt.at.path(n, Voting.Node.pass(n, s, c), c)
      )
    case Spec.Deed.Pass{c}:
      Pass.path(n, s, c)

def Spec.Node.after_on(n, evs, s):
  match evs:
    case Nil{}:
      Path.refl(s)
    case Con{+ev, rest}:
      s1 = Spec.Node.does(n, s, ev)
      Path.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1),
        Does.path(n, s, ev),
        Spec.Node.after_on(n, rest, s1)
      )
