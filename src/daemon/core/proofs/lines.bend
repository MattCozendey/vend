# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
# bend-lint: expect-file bend-lint-rules/performance/unused_result@information -- this file holds only proofs: an unused binder is a premise of a proof's own type, and a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/rope.bend as Ropes
import ../../shared/shared/shared/cell.bend as Cells
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
import ./logs.bend as ProofLogs
import ./trees.bend as ProofTrees

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  +a: Basics.Node,
  b: Basics.Node,
  +x: Hashes.Hash,
  -t: Basics.Tip,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Basics.Tip.at(a, x) == Some{t}: Maybe<&2, Basics.Tip>
} -> {Basics.Tip.at(b, x) == Some{t}: Maybe<&2, Basics.Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Basics.Tip,
    Basics.Store.fetch(a, x),
    Basics.Store.fetch(b, x),
    ws => Basics.Tip.read(ws),
    ws => Basics.Tip.read(ws),
    t,
    w => Ledgers.State.data_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~ProofTrees.Ask.laws(),
      Basics.State.ledger(a),
      Basics.State.ledger(b),
      x,
      w
    )(g),
    w => e => e
  )

# the tip of a head, in a node that grew
def Head.tip.grows(
  a: Basics.Node,
  b: Basics.Node,
  h: Basics.Head,
  -t: Basics.Tip,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Basics.Head.tip(a, h) == Some{t}: Maybe<&2, Basics.Tip>
} -> {Basics.Head.tip(b, h) == Some{t}: Maybe<&2, Basics.Tip>}:
  match h:
    case Basics.Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Basics.Tip,
        th,
        th,
        x => Basics.Tip.at(a, x),
        x => Basics.Tip.at(b, x),
        t,
        x => e => e,
        +x => Tip.at.grows(a, b, x, t, g)
      )

# what the log of a head holds, in a node that grew
def Head.get.grows(
  +a: Basics.Node,
  +b: Basics.Node,
  +h: Basics.Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Basics.Head.get(a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Head.get(b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Basics.Tip,
    List<&2, U32>,
    Basics.Head.tip(a, h),
    Basics.Head.tip(b, h),
    t => Basics.Node.get(a, Basics.Tip.log(t), k),
    t => Basics.Node.get(b, Basics.Tip.log(t), k),
    v,
    t => Head.tip.grows(a, b, h, t, g),
    t => ProofLogs.Get.grows(a, b, Basics.Tip.log(t), k, v, g)
  )

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  +a: Basics.Node,
  b: Basics.Node,
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Basics.Node.head_of(a, c) == Basics.Node.head_of(b, c): Maybe<&2, Basics.Head>}
) -> {
  Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Line.get(b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Basics.Head,
    List<&2, U32>,
    Basics.Node.head_of(a, c),
    Basics.Node.head_of(b, c),
    h => Basics.Head.get(a, h, k),
    h => Basics.Head.get(b, h, k),
    v,
    h => e => Equal.trans(
      Maybe<&2, Basics.Head>,
      Basics.Node.head_of(b, c),
      Basics.Node.head_of(a, c),
      Some{h},
      Equal.sym(Maybe<&2, Basics.Head>, Basics.Node.head_of(a, c), Basics.Node.head_of(b, c), eh),
      e
    ),
    +h => Head.get.grows(a, b, h, k, v, g)
  )

# a node keeps its own logs
def Kept.refl(-s: Basics.Node) -> Spec.Node.Keeps(s, s):
  c => k => v => n0 => n1 => e => e

# keeping composes
def Kept.trans(
  -a: Basics.Node,
  -b: Basics.Node,
  -d: Basics.Node,
  h1: Spec.Node.Keeps(a, b),
  h2: Spec.Node.Keeps(b, d)
) -> Spec.Node.Keeps(a, d):
  +c => +k => +v => +n0 => +n1 => e => h2(c)(k)(v)(n0)(n1)(h1(c)(k)(v)(n0)(n1)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  b: Bool,
  -s: Basics.Node,
  -x: Basics.Node,
  -y: Basics.Node,
  hx: Spec.Node.Keeps(s, x),
  hy: Spec.Node.Keeps(s, y)
) -> Spec.Node.Keeps(s, Shared.Bool.when(Basics.Node, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  a: Basics.Node,
  b: Basics.Node,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Basics.State.heads(a) == Basics.State.heads(b): Tries.Trie<Basics.Head>}
) -> Spec.Node.Keeps(a, b):
  +c => k => v => n0 => n1 => Line.same(
    a,
    b,
    c,
    k,
    v,
    g,
    Equal.cong(
      Tries.Trie<Basics.Head>,
      Maybe<&2, Basics.Head>,
      hs => Tries.Trie.get(Basics.Head, hs, Ledgers.Chain.key(c)),
      Basics.State.heads(a),
      Basics.State.heads(b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  s: Basics.Node,
  l: Ledgers.State(Basics.Ask)
) -> {Basics.State.heads(s) == Basics.State.heads(Basics.State.led(s, l)): Tries.Trie<Basics.Head>}:
  match s:
    case Basics.Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  s: Basics.Node,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  Basics.State.heads(s) == Basics.State.heads(Sealing.Wait.set(s, c, qs)): Tries.Trie<Basics.Head>
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  b0: Basics.Node,
  c: Ledgers.Chain,
  hd: Basics.Head,
  c2: Ledgers.Chain
) -> {
  Basics.Node.head_of(
    Sealing.State.head(b0, c, hd),
    c2
  )
    == Bool.pick(
      Maybe<&2, Basics.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Basics.Node.head_of(b0, c2)
    ): Maybe<&2, Basics.Head>
}:
  match b0:
    case Basics.Node{l, hs, ws, ks}:
      Tries.Trie.get_set(Basics.Head, hs, Ledgers.Chain.key(c), hd, Ledgers.Chain.key(c2))

# a pick, once what it picks by is known
def Pick.of(
  -A: Data,
  b: Bool,
  -p: Bool,
  -x: A,
  -y: A,
  eb: {p == b: Bool}
) -> {Bool.pick(A, p, x, y) == Bool.pick(A, b, x, y): A}:
  %eb: {Bool.pick(A, p, x, y) == Bool.pick(A, _, x, y): A}
  {==}

# what a line holds, once its head m is known
def Line.get.of(
  -a: Basics.Node,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Basics.Head>,
  em: {Basics.Node.head_of(a, c) == m: Maybe<&2, Basics.Head>}
) -> {
  Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Basics.Head,
    List<&2, U32>,
    m,
    h => Basics.Head.get(a, h, k)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {
      Maybe.bind(
        &2,
        Basics.Head,
        List<&2, U32>,
        _,
        h => Basics.Head.get(a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  +a: Basics.Node,
  +b0: Basics.Node,
  +c: Ledgers.Chain,
  +hd: Basics.Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Basics.State.heads(a) == Basics.State.heads(b0): Tries.Trie<Basics.Head>},
  cov: {
    Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Basics.Head.get(Sealing.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Basics.Line.get(a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Line.get(Sealing.State.head(b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Basics.Head>,
          Basics.Node.head_of(Sealing.State.head(b0, c, hd), c2),
          Some{hd},
          Equal.trans(
            Maybe<&2, Basics.Head>,
            Basics.Node.head_of(Sealing.State.head(b0, c, hd), c2),
            Bool.pick(
              Maybe<&2, Basics.Head>,
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Basics.Node.head_of(b0, c2)
            ),
            Some{hd},
            Head.of_set(b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Basics.Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Basics.Node.head_of(b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Basics.Head,
            List<&2, U32>,
            _,
            h => Basics.Head.get(Sealing.State.head(b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Basics.Line.get(a, c, k),
            Basics.Line.get(a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Basics.Head,
                List<&2, U32>,
                Tries.Trie.get(Basics.Head, Basics.State.heads(a), kk),
                h => Basics.Head.get(a, h, k)
              ),
              Ledgers.Chain.key(c),
              Ledgers.Chain.key(c2),
              Equal.sym(
                List<&2, Bool>,
                Ledgers.Chain.key(c2),
                Ledgers.Chain.key(c),
                Shared.List.is_eq_sound(
                  ~Bool,
                  ~Shared.Bool.is_eq,
                  ~Shared.Bool.laws(),
                  Ledgers.Chain.key(c2),
                  Ledgers.Chain.key(c)
                )(ebs)
              )
            ),
            e
          )
        )
    case False{}:
      Line.same(
        a,
        Sealing.State.head(b0, c, hd),
        c2,
        k,
        v,
        ProofTrees.Grows.to(
          a,
          b0,
          Sealing.State.head(b0, c, hd),
          ProofTrees.Led.head(b0, c, hd),
          g
        ),
        Equal.trans(
          Maybe<&2, Basics.Head>,
          Basics.Node.head_of(a, c2),
          Basics.Node.head_of(b0, c2),
          Basics.Node.head_of(Sealing.State.head(b0, c, hd), c2),
          Equal.cong(
            Tries.Trie<Basics.Head>,
            Maybe<&2, Basics.Head>,
            hs => Tries.Trie.get(Basics.Head, hs, Ledgers.Chain.key(c2)),
            Basics.State.heads(a),
            Basics.State.heads(b0),
            eh
          ),
          Equal.sym(
            Maybe<&2, Basics.Head>,
            Basics.Node.head_of(Sealing.State.head(b0, c, hd), c2),
            Basics.Node.head_of(b0, c2),
            Equal.trans(
              Maybe<&2, Basics.Head>,
              Basics.Node.head_of(Sealing.State.head(b0, c, hd), c2),
              Bool.pick(
                Maybe<&2, Basics.Head>,
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Basics.Node.head_of(b0, c2)
              ),
              Basics.Node.head_of(b0, c2),
              Head.of_set(b0, c, hd, c2),
              Pick.of(
                Maybe<&2, Basics.Head>,
                False{},
                Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
                Some{hd},
                Basics.Node.head_of(b0, c2),
                ebs
              )
            )
          )
        )
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  a: Basics.Node,
  b0: Basics.Node,
  +c: Ledgers.Chain,
  hd: Basics.Head,
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Basics.State.heads(a) == Basics.State.heads(b0): Tries.Trie<Basics.Head>},
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k) == False{}: Bool
  } -> {
    Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Basics.Head.get(Sealing.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(a, Sealing.State.head(b0, c, hd)):
  +c2 => +k => +v => n0 => n1 => Head.put.kept.if(
    a,
    b0,
    c,
    hd,
    c2,
    k,
    v,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    g,
    eh,
    cover(k)(v)(n0)(n1)
  )

# one of two nodes, each with the heads of s
def Heads.when(
  b: Bool,
  -s: Basics.Node,
  -x: Basics.Node,
  -y: Basics.Node,
  hx: {Basics.State.heads(s) == Basics.State.heads(x): Tries.Trie<Basics.Head>},
  hy: {Basics.State.heads(s) == Basics.State.heads(y): Tries.Trie<Basics.Head>}
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Shared.Bool.when(Basics.Node, b, u => x, u => y)): Tries.Trie<Basics.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  s: Basics.Node,
  ks: Basics.Keys
) -> {
  Basics.State.heads(s) == Basics.State.heads(Basics.State.keyed(s, ks)): Tries.Trie<Basics.Head>
}:
  match s:
    case Basics.Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(s: Basics.Node, m: Maybe<&2, Basics.Node>) -> Tries.Trie<Basics.Head>:
  match m:
    case None{}:
      Basics.State.heads(s)
    case Some{s2}:
      Basics.State.heads(s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  b: Bool,
  -s: Basics.Node,
  -x: Basics.Node,
  hx: {Basics.State.heads(s) == Basics.State.heads(x): Tries.Trie<Basics.Head>}
) -> {
  Basics.State.heads(
    s
  )
    == Heads.of(s, Shared.Maybe.when(Basics.Node, b, u => Some{x})): Tries.Trie<Basics.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  +s: Basics.Node,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Basics.Keychain>
) -> {
  Basics.State.heads(s) == Heads.of(s, Sealing.Seal.accept.at(s, b, m)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(
        Sealing.Seal.fits(c, b),
        s,
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
        Equal.trans(
          Tries.Trie<Basics.Head>,
          Basics.State.heads(s),
          Basics.State.heads(
            Basics.State.led(
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
            )
          ),
          Basics.State.heads(
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
            )
          ),
          Heads.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
          ),
          Heads.keyed(
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
          )
        )
      )

# the node m, if any, else s, has the heads of s when m has
def Default.heads(
  -s: Basics.Node,
  m: Maybe<&2, Basics.Node>
) -> {
  Basics.State.heads(s) == Heads.of(s, m): Tries.Trie<Basics.Head>
} -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Maybe.default(&2, Basics.Node, m, s)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  +s: Basics.Node,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Basics.Keychain>
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Sealing.Cast.seal(s, w, n, a0, m)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Basics.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Sealing.Seal.secret(Sealing.Keys.seed(Basics.State.keys(s)), Sealing.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Sealing.Seal.secret(
            Sealing.Keys.seed(Basics.State.keys(s)),
            Sealing.Where.store(w),
            U32.inc(j)
          )
        )
      )
      Default.heads(
        s,
        Sealing.Seal.accept(s, b)
      )(
        Accept.at.heads(
          s,
          b,
          Sealing.Seal.chain(s, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )

# a ballot keeps the heads
def Cast.vote.heads(
  +s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Sealing.Cast.vote(s, m, w, n, a0)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = Basics.State.led(s, Basics.State.ledger(s3))
      Equal.trans(
        Tries.Trie<Basics.Head>,
        Basics.State.heads(s),
        Basics.State.heads(s4),
        Basics.State.heads(
          Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
        ),
        Heads.led(s, Basics.State.ledger(s3)),
        Cast.seal.heads(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  -s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  -k: Basics.Node -> Basics.Node,
  ih: @s2: Basics.Node -> {
    Basics.State.heads(s2) == Basics.State.heads(k(s2)): Tries.Trie<Basics.Head>
  }
) -> {
  Basics.State.heads(s) == Heads.of(s, m): Tries.Trie<Basics.Head>
} -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(
      Maybe.default(
        &2,
        Basics.Node,
        Maybe.bind(&2, Basics.Node, Basics.Node, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<Basics.Head>,
        Basics.State.heads(s),
        Basics.State.heads(s2),
        Basics.State.heads(k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  f: Nat,
  +s: Basics.Node,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Sealing.Sealed.follow(f, s, p, r, n, mb)): Tries.Trie<Basics.Head>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.heads(
        s,
        Sealing.Seal.accept(s, b),
        +s2 => Sealing.Sealed.follow(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n)),
        +s2 => Follow.heads(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n))
      )(
        Accept.at.heads(
          s,
          b,
          Sealing.Seal.chain(s, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the heads
def Each.heads(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Basics.Node
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Sealing.Sealed.each(f, bs, p, s)): Tries.Trie<Basics.Head>
}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, rest}:
      s1 = Sealing.Sealed.follow(
        f,
        s,
        p,
        Sealing.Ballot.store(b),
        Sealing.Ballot.node(b),
        Sealing.Pending.next(s, p, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
      )
      Equal.trans(
        Tries.Trie<Basics.Head>,
        Basics.State.heads(s),
        Basics.State.heads(s1),
        Basics.State.heads(Sealing.Sealed.each(f, rest, p, s1)),
        Follow.heads(
          f,
          s,
          p,
          Sealing.Ballot.store(b),
          Sealing.Ballot.node(b),
          Sealing.Pending.next(s, p, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        ),
        Each.heads(f, rest, p, s1)
      )

# a vote keeps the heads
def Cast.put.heads(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Stepping.Run>,
  s: Basics.Node
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Sealing.Cast.put(n, w, th, qs, from, m, s)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{s2, +t2, ns}}:
      Cast.vote.heads(
        s,
        Judging.State.put(s2, [Basics.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Basics.Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  +n: String,
  +s: Basics.Node,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {
  Basics.State.heads(s) == Basics.State.heads(Voting.Pass.to(n, s, w, os)): Tries.Trie<Basics.Head>
}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Basics.Ask, Basics.State.ledger(s), Ledgers.Where{c, h, r}, n)
          ),
          List.contains(~String, ~String.eq, os, n)
        ),
        s,
        Sealing.Cast.seal(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Voting.Last.below(n, s, c, h, r)},
          Sealing.Seal.chain(s, Sealing.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        s,
        Cast.seal.heads(
          s,
          Ledgers.Where{c, h, r},
          n,
          Ledgers.Act.Pass{Voting.Last.below(n, s, c, h, r)},
          Sealing.Seal.chain(s, Sealing.Where.store(Ledgers.Where{c, h, r}), n)
        ),
        {==}
      )

# a node that joins a round keeps the heads
def Round.join.heads(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Voting.Round.join(n, s, c, h, os)): Tries.Trie<Basics.Head>
}:
  +top = Sealing.Round.seen(s, c, h)
  k = top
  Heads.when(
    Nat.is_lt(Voting.Round.mine(n, s, c, h, k), top),
    s,
    Voting.Pass.to(n, s, Ledgers.Where{c, h, top}, os),
    s,
    Pass.to.heads(n, s, Ledgers.Where{c, h, top}, os),
    {==}
  )

# a ballot in the node's round keeps the heads
def Cast.round.heads(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Basics.Tip
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Voting.Cast.round(n, s, c, next, th, t)): Tries.Trie<Basics.Head>
}:
  +os = Basics.Line.owners(s, t)
  +r = Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))
  +w = {Ledgers.Where{c, next, r}: Ledgers.Where}
  +p = Voting.Plan.of(
    n,
    s,
    c,
    w,
    t,
    th,
    os,
    Sealing.Owners.turn(os, U32.add(next, U32.from_nat(r)))
  )
  Heads.when(
    Sealing.Cast.may(n, s, w, t, Sealing.Plan.asks(p)),
    s,
    Sealing.Cast.put(n, w, th, Sealing.Plan.asks(p), Sealing.Plan.from(p), Sealing.Plan.run(p), s),
    s,
    Cast.put.heads(n, w, th, Sealing.Plan.asks(p), Sealing.Plan.from(p), Sealing.Plan.run(p), s),
    {==}
  )

# Node.cast keeps the heads, at the head h whose tip is m
def Cast.at.heads(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Voting.Cast.at(n, s, c, h, m)): Tries.Trie<Basics.Head>
}:
  match h m:
    case Basics.Head{r, b, +next, th} Some{+t}:
      s1 = Voting.Round.join(n, s, c, next, Basics.Line.owners(s, t))
      Equal.trans(
        Tries.Trie<Basics.Head>,
        Basics.State.heads(s),
        Basics.State.heads(s1),
        Basics.State.heads(Voting.Cast.round(n, s1, c, next, th, t)),
        Round.join.heads(n, s, c, next, Basics.Line.owners(s, t)),
        Cast.round.heads(n, s1, c, next, th, t)
      )
    case Basics.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {
  Basics.State.heads(
    s
  )
    == Basics.State.heads(Voting.Pass.at(n, s, c, h, m)): Tries.Trie<Basics.Head>
}:
  match h m:
    case Basics.Head{r, b, +next, th} Some{t}:
      Pass.to.heads(
        n,
        s,
        Ledgers.Where{c, next, 1n+Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))},
        Basics.Line.owners(s, t)
      )
    case Basics.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.State.heads(s) == Basics.State.heads(Voting.Pass.head(n, s, c, m)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(n, s, c, h, Basics.Head.tip(s, h))

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.State.heads(s) == Basics.State.heads(Voting.Cast.head(n, s, c, m)): Tries.Trie<Basics.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(n, s, c, h, Basics.Head.tip(s, h))

# a node's ballot keeps its logs
def Cast.kept(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.cast(n, s, c)):
  Kept.same(
    s,
    Voting.Node.cast(n, s, c),
    ProofTrees.Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Basics.Node.head_of(s, c))
  )

# the words of a tip read as the tip
def Tip.round(
  t: Basics.Tip
) -> {Basics.Tip.read(Basics.Tip.words(t)) == Some{t}: Maybe<&2, Basics.Tip>}:
  match t:
    case Basics.Tip{c, l}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Basics.Tip>>,
        Codes.Code.two.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~Basics.Tip,
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          ~Codes.Codec.dec(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          ),
          x => y => Basics.Tip{x, y},
          Codes.Codec.enc(
            Maybe<&2, Hashes.Hash>,
            Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
          )(
            c
          )(
            Codes.Codec.enc(
              Maybe<&2, Hashes.Hash>,
              Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())
            )(l)([])
          )
        ),
        Some{Codes.Read{Basics.Tip{c, l}, []}},
        Codes.Code.two_read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~Basics.Tip,
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          x => y => Basics.Tip{x, y},
          c,
          l,
          []
        )
      ): {Basics.Read.whole(Basics.Tip, _) == Some{Basics.Tip{c, l}}: Maybe<&2, Basics.Tip>}
      {==}

# Put.holds once whether the node holds the data is known (b)
def Put.holds.if(
  -s2: Basics.Node,
  -ds: List<&2, List<&2, U32>>,
  -s3: Basics.Node,
  b: Bool,
  eb: {
    Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s2, ds), ds) == b: Bool
  }
) -> {
  Shared.Maybe.when(
    Basics.Node,
    b,
    u => Some{Basics.State.keep(s2, ds)}
  )
    == Some{s3}: Maybe<&2, Basics.Node>
} -> {Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Basics.Node, s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Basics.Node,
          Basics.State.keep(s2, ds),
          s3,
          e
        ): {Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  s2: Basics.Node,
  +ds: List<&2, List<&2, U32>>,
  -s3: Basics.Node
) -> {
  Judging.State.put(s2, ds) == Some{s3}: Maybe<&2, Basics.Node>
} -> {Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, s3, ds) == True{}: Bool}:
  Put.holds.if(
    s2,
    ds,
    s3,
    Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, Basics.State.keep(s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  s2: Basics.Node,
  ds: List<&2, List<&2, U32>>,
  -s3: Basics.Node,
  e: {Judging.State.put(s2, ds) == Some{s3}: Maybe<&2, Basics.Node>}
) -> {Reading.Node.grows(s2, s3) == True{}: Bool}:
  %e: {ProofTrees.State.after(s2, _) == True{}: Bool}
  ProofTrees.Put.grows(s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  s2: Basics.Node,
  +t2: Basics.Tip,
  +s3: Basics.Node
) -> {
  Judging.State.put(s2, [Basics.Tip.words(t2)]) == Some{s3}: Maybe<&2, Basics.Node>
} -> {Basics.Tip.at(s3, Basics.Tip.hash(t2)) == Some{t2}: Maybe<&2, Basics.Tip>}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Basics.Store.fetch(s3, Hashes.Sha.hash(Basics.Tip.words(t2))),
      Some{Basics.Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Basics.Store.fetch(s3, Hashes.Sha.hash(Basics.Tip.words(t2))),
        Some{Basics.Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Trees.Tree.has(~Basics.Node, ~Basics.Store.fetch, s3, Basics.Tip.words(t2)),
          u => Trees.Tree.holds(~Basics.Node, ~Basics.Store.fetch, s3, [])
        )(Put.holds(s2, [Basics.Tip.words(t2)], s3)(e))
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Basics.Tip,
        _,
        ws => Basics.Tip.read(ws)
      )
        == Some{t2}: Maybe<&2, Basics.Tip>
    }
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  -s: Basics.Node,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Basics.Head,
  -t: Basics.Tip,
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  et: {Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>}
) -> {
  Basics.Line.get(s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Node.get(s, Basics.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Basics.Tip,
        List<&2, U32>,
        _,
        t1 => Basics.Node.get(s, Basics.Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    Line.get.of(s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  +s3: Basics.Node,
  +b: Basics.Node,
  +t2: Basics.Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Reading.Node.grows(s3, b) == True{}: Bool},
  e3: {Basics.Tip.at(s3, Basics.Tip.hash(t2)) == Some{t2}: Maybe<&2, Basics.Tip>},
  v3: {Basics.Node.get(s3, Basics.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Basics.Head.get(
    b,
    Basics.Head{r, br, nx, Some{Basics.Tip.hash(t2)}},
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Basics.Tip>,
    Basics.Tip.at(b, Basics.Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(s3, b, Basics.Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Basics.Tip,
      List<&2, U32>,
      _,
      t1 => Basics.Node.get(b, Basics.Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  ProofLogs.Get.grows(s3, b, Basics.Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  +s: Basics.Node,
  +s3: Basics.Node,
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Basics.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Basics.Head,
  t: Basics.Tip,
  g3: {Reading.Node.grows(s, s3) == True{}: Bool},
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  et: {Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>},
  e3: {Basics.Tip.at(s3, Basics.Tip.hash(t2)) == Some{t2}: Maybe<&2, Basics.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k) == False{}: Bool
  } -> {
    Basics.Node.get(s, Basics.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Basics.Node.get(s3, Basics.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(
  s,
  Sealing.State.moved(
    Basics.State.led(s, Basics.State.ledger(s3)),
    c,
    Basics.Head{r, br, nx, Some{Basics.Tip.hash(t2)}},
    qs
  )
):
  +x = Basics.State.led(s, Basics.State.ledger(s3))
  +ws = Sealing.Wait.left(
    Sealing.Wait.of(x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Sealing.Wait.set(x, c, ws)
  +hd = {Basics.Head{r, br, nx, Some{Basics.Tip.hash(t2)}}: Basics.Head}
  Head.put.kept(
    s,
    b0,
    c,
    hd,
    ProofTrees.Grows.to(s, x, b0, ProofTrees.Led.wait(x, c, ws), ProofTrees.Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Basics.Head>,
      Basics.State.heads(s),
      Basics.State.heads(x),
      Basics.State.heads(b0),
      Heads.led(s, Basics.State.ledger(s3)),
      Heads.wait(x, c, ws)
    ),
    +k => +v => n0 => n1 => e => Moved.cover(
      s3,
      Sealing.State.head(b0, c, hd),
      t2,
      k,
      v,
      r,
      br,
      nx,
      ProofTrees.Grows.to(
        s3,
        s3,
        Sealing.State.head(b0, c, hd),
        Equal.trans(
          Ledgers.State(Basics.Ask),
          Basics.State.ledger(Sealing.State.head(b0, c, hd)),
          Basics.State.ledger(b0),
          Basics.State.ledger(s3),
          ProofTrees.Led.head(b0, c, hd),
          Equal.trans(
            Ledgers.State(Basics.Ask),
            Basics.State.ledger(b0),
            Basics.State.ledger(x),
            Basics.State.ledger(s3),
            ProofTrees.Led.wait(x, c, ws),
            ProofTrees.Led.led(s, Basics.State.ledger(s3))
          )
        ),
        ProofTrees.Grows.refl(s3)
      ),
      e3,
      kk(k)(v)(n0)(n1)(Line.read.at(s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  +s: Basics.Node,
  +s2: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Basics.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Basics.Head,
  t: Basics.Tip,
  g2: {Reading.Node.grows(s, s2) == True{}: Bool},
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  et: {Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k) == False{}: Bool
  } -> {
    Basics.Node.get(s, Basics.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Basics.Node.get(s2, Basics.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Judging.State.put(s2, [Basics.Tip.words(t2)]) == m: Maybe<&2, Basics.Node>
} -> Spec.Node.Keeps(
  s,
  Voting.Advance.moved(s, m, c, Basics.Head{r, br, nx, Some{Basics.Tip.hash(t2)}}, qs)
):
  match m:
    case None{}:
      e2 => Kept.refl(s)
    case Some{+s3}:
      +e2 => Moved.kept(
        s,
        s3,
        c,
        r,
        br,
        nx,
        t2,
        qs,
        h,
        t,
        ProofTrees.Grows.trans(s, s2, s3)(g2)(Put.grew(s2, [Basics.Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(s2, t2, s3)(e2),
        +k => +v => n0 => n1 => e => ProofLogs.Get.grows(
          s2,
          s3,
          Basics.Tip.log(t2),
          k,
          v,
          Put.grew(s2, [Basics.Tip.words(t2)], s3, e2)
        )(kk(k)(v)(n0)(n1)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  s: Basics.Node,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>,
  h: Basics.Head,
  t: Basics.Tip,
  em: {Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>},
  et: {Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>}
) -> {
  ProofTrees.Run.after(s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.owners(), k) == False{}: Bool
  } -> {
    Shared.List.is_eq(~U32, ~U32.is_eq, Basics.Log.count(), k) == False{}: Bool
  } -> {
    Basics.Node.get(s, Basics.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> ProofLogs.Run.Keeps(k, v, m)
) -> Spec.Node.Keeps(s, Voting.Advance.ran(s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(s)
    case Some{Stepping.Run{+s2, +t2, ns}}:
      ga => rk => Kept.when(
        Sealing.Root.same(after, Some{Basics.Tip.hash(t2)}),
        s,
        Voting.Advance.moved(
          s,
          Judging.State.put(s2, [Basics.Tip.words(t2)]),
          c,
          Basics.Head{r, br, U32.inc(next), Some{Basics.Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(
          s,
          s2,
          Judging.State.put(s2, [Basics.Tip.words(t2)]),
          c,
          r,
          br,
          U32.inc(next),
          t2,
          qs,
          h,
          t,
          ga,
          em,
          et,
          rk
        )({==}),
        Kept.refl(s)
      )

# Node.advance keeps the logs, once the decided step m is known
def Advance.step.kept(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  h: Basics.Head,
  +t: Basics.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
} -> {
  Basics.Head.tip(s, h) == Some{t}: Maybe<&2, Basics.Tip>
} -> Spec.Node.Keeps(s, Voting.Advance.step(s, c, h, t, m)):
  match h m:
    case Basics.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, after}}:
      +em => +et => Kept.when(
        Sealing.Root.same(before, th),
        s,
        Voting.Advance.ran(s, c, r, br, next, after, qs, Stepping.Step.run(s, c, t, qs)),
        s,
        Advance.ran.kept(
          s,
          c,
          r,
          br,
          next,
          after,
          qs,
          Stepping.Step.run(s, c, t, qs),
          Basics.Head{r, br, next, th},
          t,
          em,
          et
        )(
          ProofTrees.Run.grows(s, c, t, qs)
        )(+k => +v => +n0 => +n1 => ProofLogs.Run.kept(s, c, t, qs, k, v, n0, n1)),
        Kept.refl(s)
      )
    case Basics.Head{r, br, next, th} None{}:
      em => et => Kept.refl(s)

# Node.advance keeps the logs, at the head h whose tip is m
def Advance.at.kept(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +h: Basics.Head,
  m: Maybe<&2, Basics.Tip>
) -> {
  Basics.Node.head_of(s, c) == Some{h}: Maybe<&2, Basics.Head>
} -> {
  Basics.Head.tip(s, h) == m: Maybe<&2, Basics.Tip>
} -> Spec.Node.Keeps(s, Voting.Advance.at(s, c, h, m)):
  match m:
    case None{}:
      em => et => Kept.refl(s)
    case Some{+t}:
      em => et => Advance.step.kept(
        s,
        c,
        h,
        t,
        Voting.Height.decide(
          s,
          c,
          Sealing.Head.next(h),
          Basics.Line.owners(s, t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )(em)(et)

# Advances.kept once the head m is known
def Advances.at.kept(
  f: Nat,
  +s: Basics.Node,
  +c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.Node.head_of(s, c) == m: Maybe<&2, Basics.Head>
} -> Spec.Node.Keeps(s, Voting.Advances.at(f, s, c, m)):
  match f m:
    case 0n x:
      em => Kept.refl(s)
    case 1n+p None{}:
      em => Kept.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Voting.Advance.at(s, c, h, Basics.Head.tip(s, h))
        +m1 = Basics.Node.head_of(s1, c)
        Kept.when(
          Voting.Heads.level(Some{h}, m1),
          s,
          s1,
          Voting.Advances.at(p, s1, c, m1),
          Advance.at.kept(s, c, h, Basics.Head.tip(s, h))(em)({==}),
          Kept.trans(
            s,
            s1,
            Voting.Advances.at(p, s1, c, m1),
            Advance.at.kept(s, c, h, Basics.Head.tip(s, h))(em)({==}),
            Advances.at.kept(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step keeps the logs
def Advances.kept(
  f: Nat,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.advances(f, s, c)):
  Advances.at.kept(f, s, c, Basics.Node.head_of(s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Step.head(n, s, c)):
  +s1 = Voting.Node.advances(4294967295n, s, c)
  +s2 = Voting.Node.cast(n, s1, c)
  s3 = Voting.Node.advances(4294967295n, s2, c)
  Kept.trans(
    s,
    s1,
    s3,
    Advances.kept(4294967295n, s, c),
    Kept.trans(s1, s2, s3, Cast.kept(n, s1, c), Advances.kept(4294967295n, s2, c))
  )

# a line with no head holds nothing
def Cover.none(
  -a: Basics.Node,
  -c: Ledgers.Chain,
  -b: Basics.Node,
  -hd: Basics.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Basics.Node.head_of(a, c) == None{}: Maybe<&2, Basics.Head>}
) -> {
  Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Basics.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  -a: Basics.Node,
  -c: Ledgers.Chain,
  -b: Basics.Node,
  -hd: Basics.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Basics.Node.head_of(a, c) == Some{Basics.Head{r, br, n, None{}}}: Maybe<&2, Basics.Head>}
) -> {
  Basics.Line.get(a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Basics.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Basics.Head.get(b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(a, c, k, v, Some{Basics.Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  +s: Basics.Node,
  c: Ledgers.Chain,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.Node.head_of(s, c) == m: Maybe<&2, Basics.Head>
} -> Spec.Node.Keeps(s, Sealing.Open.at(s, c, m)):
  match m:
    case Some{Basics.Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Basics.Head{
            r,
            Some{b},
            0,
            Sealing.Branch.first(s, b, Basics.Node.tip(s, Ledgers.Chain{r, None{}}))
          }: Basics.Head
        }
        Head.put.kept(
          s,
          s,
          c,
          hd,
          ProofTrees.Grows.refl(s),
          {==},
          k => v => n0 => n1 => Cover.wait(
            s,
            c,
            Sealing.State.head(s, c, hd),
            hd,
            k,
            v,
            r,
            Some{b},
            n,
            em
          )
        )
    case Some{Basics.Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Basics.Head{r, None{}, n, t}}:
      em => Kept.refl(s)
    case None{}:
      em => Kept.refl(s)

# what a node does on a line keeps the logs
def Step.kept(
  n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.step(n, s, c)):
  s1 = Sealing.Node.open(s, c)
  Kept.trans(
    s,
    s1,
    Voting.Step.head(n, s1, c),
    Open.at.kept(s, c, Basics.Node.head_of(s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  +n: String,
  +s: Basics.Node,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.pass(n, s, c)):
  +s1 = Voting.Pass.head(n, s, c, Basics.Node.head_of(s, c))
  Kept.trans(
    s,
    s1,
    Voting.Node.step(n, s1, c),
    Kept.same(
      s,
      s1,
      ProofTrees.Pass.head.grows(n, s, c, Basics.Node.head_of(s, c)),
      Pass.head.heads(n, s, c, Basics.Node.head_of(s, c))
    ),
    Step.kept(n, s1, c)
  )

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  +s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.Node.head_of(s, c) == m: Maybe<&2, Basics.Head>
} -> Spec.Node.Keeps(s, Sealing.First.at(s, c, h, m)):
  match m:
    case Some{Basics.Head{r, b, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Basics.Head{r, b, n, None{}}}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        ProofTrees.Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.wait(s, c, Sealing.State.head(s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        ProofTrees.Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.none(s, c, Sealing.State.head(s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  +s: Basics.Node,
  a: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +c: Ledgers.Chain,
  h: Basics.Head,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  ProofTrees.State.after(a, m) == True{}: Bool
} -> Spec.Node.Keeps(s, Sealing.Start.head(s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+s3}:
      e =>
        +x = Basics.State.led(s, Basics.State.ledger(s3))
        Kept.trans(
          s,
          x,
          Sealing.State.first(x, c, h),
          Kept.same(
            s,
            x,
            ProofTrees.Grows.back(s, s3, ProofTrees.Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Basics.State.ledger(s3))
          ),
          First.at.kept(x, c, h, Basics.Node.head_of(x, c))({==})
        )

# the first tip of a store keeps the logs
def Start.put.kept(
  s: Basics.Node,
  +i: Ledgers.Id,
  c: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Judging.Work>
) -> {
  ProofTrees.Work.after(s, m) == True{}: Bool
} -> Spec.Node.Keeps(s, Sealing.Start.put(s, i, c, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{Judging.Work{+s2, l, ns}}:
      e =>
        +t = {Basics.Tip{c, l}: Basics.Tip}
        Start.head.kept(
          s,
          s2,
          Judging.State.put(s2, [Basics.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Basics.Head{i, None{}, 0, Some{Basics.Tip.hash(t)}},
          e
        )(ProofTrees.Put.grows(s2, [Basics.Tip.words(t)]))

# Start.kept once the content m of the store is known
def Start.with.kept(
  +s: Basics.Node,
  i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Judging.Work>
) -> {
  ProofTrees.Work.after(s, m) == True{}: Bool
} -> Spec.Node.Keeps(s, Sealing.Start.with(s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+w}:
      e => Start.put.kept(
        s,
        i,
        Judging.Work.root(w),
        Judging.Log.first(w, os)
      )(ProofTrees.Log.first.after(s, w, os)(e))

# a store that starts keeps the logs
def Start.kept(
  +s: Basics.Node,
  i: Ledgers.Id,
  +os: List<&2, Basics.Owner>
) -> Spec.Node.Keeps(s, Sealing.Node.start(s, i, os)):
  Start.with.kept(
    s,
    i,
    Basics.Owner.names(os),
    Sealing.Seal.firsts(os, Some{Judging.Work{s, None{}, []}})
  )(ProofTrees.Firsts.after(s, os, Some{Judging.Work{s, None{}, []}})(ProofTrees.Grows.refl(s)))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  +s: Basics.Node,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Basics.Head>
) -> {
  Basics.Node.head_of(s, Basics.Line.chain(r, l)) == m: Maybe<&2, Basics.Head>
} -> Spec.Node.Keeps(s, Sealing.Follow.new(s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(s)
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        Basics.Line.chain(r, l),
        Basics.Head{r, l, 0, None{}},
        ProofTrees.Grows.refl(s),
        {==},
        k => v => n0 => n1 => Cover.none(
          s,
          Basics.Line.chain(r, l),
          Sealing.State.head(s, Basics.Line.chain(r, l), Basics.Head{r, l, 0, None{}}),
          Basics.Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  s: Basics.Node,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  Basics.State.heads(s) == Basics.State.heads(Sealing.State.wait(s, c, i)): Tries.Trie<Basics.Head>
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# a new request keeps the logs
def Arrive.kept(
  +s: Basics.Node,
  +i: Ledgers.Id,
  q: Basics.Ask
) -> Spec.Node.Keeps(s, Sealing.Node.arrive(s, i, q)):
  match q:
    case Basics.Ask.Start{os}:
      Start.kept(s, i, os)
    case Basics.Ask.On{+r, +l, c}:
      +s1 = Sealing.Node.follow(s, r, l)
      Kept.trans(
        s,
        s1,
        Sealing.State.wait(s1, Basics.Line.chain(r, l), i),
        Follow.new.kept(s, r, l, Basics.Node.head_of(s, Basics.Line.chain(r, l)))({==}),
        Kept.same(
          s1,
          Sealing.State.wait(s1, Basics.Line.chain(r, l), i),
          ProofTrees.Grows.to(
            s1,
            s1,
            Sealing.State.wait(s1, Basics.Line.chain(r, l), i),
            ProofTrees.Led.waits(s1, Basics.Line.chain(r, l), i),
            ProofTrees.Grows.refl(s1)
          ),
          Heads.waits(s1, Basics.Line.chain(r, l), i)
        )
      )

# a new request keeps the logs
def Ask.new.kept(
  n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  +q: Basics.Ask
) -> Spec.Node.Keeps(s, Voting.Node.ask.new(n, s, e, q)):
  +i = Basics.Envelope.of(e)
  c = Basics.Ask.chain(i, q)
  +l0 = Ledgers.State.ask(
    ~Basics.Ask,
    ~Basics.Ask.is_eq,
    Basics.State.ledger(s),
    i,
    Basics.Envelope.time(e),
    q
  )
  +s0 = Basics.State.led(s, l0)
  s1 = Sealing.Node.arrive(s0, i, q)
  Kept.trans(
    s,
    s0,
    Voting.Node.step(n, s1, c),
    Kept.same(
      s,
      s0,
      ProofTrees.Grows.led(
        s,
        l0,
        Ledgers.State.add_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~ProofTrees.Ask.laws(),
          Basics.State.ledger(s),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, Basics.Envelope.time(e), q}
        )
      ),
      Heads.led(s, l0)
    ),
    Kept.trans(s0, s1, Voting.Node.step(n, s1, c), Arrive.kept(s0, i, q), Step.kept(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.kept(
  n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Spec.Node.Keeps(s, Voting.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(s)
    case None{}:
      Kept.trans(
        s,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
        Voting.Node.ask.new(
          n,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          e,
          q
        ),
        Kept.same(
          s,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          ProofTrees.Grows.to(
            s,
            s,
            Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
            ProofTrees.Grows.refl(s)
          ),
          Heads.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e)))
        ),
        Ask.new.kept(
          n,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), Basics.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask keeps the logs
def Ask.kept(
  n: String,
  +s: Basics.Node,
  +e: Basics.Envelope,
  q: Basics.Ask
) -> Spec.Node.Keeps(s, Voting.Node.ask(n, s, e, q)):
  Ask.at.kept(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Basics.State.ledger(s), Ledgers.Slot.ask(Basics.Envelope.of(e)))
  )

# the new requests among cells keep the logs
def Take.asks.kept(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Basics.Node
) -> Spec.Node.Keeps(s, Voting.Take.asks(cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{Cells.One{Ledgers.Entry.Ask{+i, t, +q}}, rest}:
      s1 = Shared.Bool.when(
        Basics.Node,
        Maybe.is_none(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
        ),
        u => Sealing.Node.arrive(s, i, q),
        u => s
      )
      Kept.trans(
        s,
        s1,
        Voting.Take.asks(rest, old, s1),
        Kept.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          s,
          Sealing.Node.arrive(s, i, q),
          s,
          Arrive.kept(s, i, q),
          Kept.refl(s)
        ),
        Take.asks.kept(rest, old, s1)
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.kept(rest, old, s)
    case Con{Cells.Many{}, rest}:
      Take.asks.kept(rest, old, s)

# Node.take keeps the logs
def Take.kept(
  +s: Basics.Node,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.Keeps(s, Voting.Node.take(s, t)):
  +sent = Voting.Take.clean(
    Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, t),
    Ledgers.State.empty(~Basics.Ask)
  )
  +l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent)
  +s1 = Basics.State.led(s, l1)
  +cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Basics.State.ledger(s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
    )
  )
  Kept.trans(
    s,
    s1,
    Sealing.Sealed.take(bs, s2),
    Kept.same(
      s,
      s1,
      ProofTrees.Grows.led(
        s,
        l1,
        Ledgers.State.take_grows(
          ~Basics.Ask,
          ~Basics.Ask.is_eq,
          ~ProofTrees.Ask.laws(),
          Basics.State.ledger(s),
          sent
        )
      ),
      Heads.led(s, l1)
    ),
    Kept.trans(
      s1,
      s2,
      Sealing.Sealed.take(bs, s2),
      Take.asks.kept(cs, Basics.State.ledger(s), s1),
      Kept.same(
        s2,
        Sealing.Sealed.take(bs, s2),
        ProofTrees.Each.grows(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2),
        Each.heads(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2)
      )
    )
  )

# what a node does on each of some lines keeps the logs
def Steps.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Basics.Node
) -> Spec.Node.Keeps(s, Voting.Node.steps(n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      s1 = Voting.Node.step(n, s, c)
      Kept.trans(s, s1, Voting.Node.steps(n, rest, s1), Step.kept(n, s, c), Steps.kept(n, rest, s1))

# an adoption keeps the logs, once the request m is known
def Adopt.ask.kept(
  n: String,
  s: Basics.Node,
  m: Maybe<&2, Reading.Request>
) -> Spec.Node.Keeps(s, Reading.Adopt.ask(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Reading.Request{e, q}}:
      Ask.kept(n, s, e, q)

# an adoption keeps the logs, once the head m of the line is known
def Adopt.head.kept(
  n: String,
  +s: Basics.Node,
  m: Maybe<&2, Basics.Head>
) -> Spec.Node.Keeps(s, Reading.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Basics.Head{r, b, next, t}}:
      Adopt.ask.kept(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  n: String,
  +s: Basics.Node,
  c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Reading.Adopt.at(n, s, c)):
  Adopt.head.kept(n, s, Basics.Node.head_of(s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  n: String,
  s: Basics.Node,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Reading.Adopt.maybe(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Adopt.at.kept(n, s, c)

# the adoption of each of some lines keeps the logs
def Adopts.kept(
  +n: String,
  cs: List<&2, Ledgers.Chain>,
  +s: Basics.Node
) -> Spec.Node.Keeps(s, Reading.Node.adopts(n, cs, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
    case Con{+c, rest}:
      Kept.trans(
        s,
        Reading.Adopt.at(n, s, c),
        Reading.Node.adopts(n, rest, Reading.Adopt.at(n, s, c)),
        Adopt.at.kept(n, s, c),
        Adopts.kept(n, rest, Reading.Adopt.at(n, s, c))
      )

# more rounds of a sync, kept
def More.kept(
  f: Nat,
  +n: String,
  +cs: List<&2, Ledgers.Chain>,
  +k: Nat,
  +bs: List<&2, Ledgers.Ballot>,
  +pd: Tries.Trie<Ledgers.Ballot>,
  +s: Basics.Node
) -> Spec.Node.Keeps(s, Reading.Sync.more(f, n, cs, k, bs, pd, s)):
  match f:
    case 0n:
      Kept.refl(s)
    case 1n+(p):
      Kept.when(
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
        Kept.trans(
          s,
          Sealing.Sealed.each(k, bs, pd, s),
          Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
          Kept.same(
            s,
            Sealing.Sealed.each(k, bs, pd, s),
            ProofTrees.Each.grows(k, bs, pd, s),
            Each.heads(k, bs, pd, s)
          ),
          Steps.kept(n, cs, Sealing.Sealed.each(k, bs, pd, s))
        ),
        Kept.trans(
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
          Kept.trans(
            s,
            Sealing.Sealed.each(k, bs, pd, s),
            Voting.Node.steps(n, cs, Sealing.Sealed.each(k, bs, pd, s)),
            Kept.same(
              s,
              Sealing.Sealed.each(k, bs, pd, s),
              ProofTrees.Each.grows(k, bs, pd, s),
              Each.heads(k, bs, pd, s)
            ),
            Steps.kept(n, cs, Sealing.Sealed.each(k, bs, pd, s))
          ),
          More.kept(
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

# a sync keeps the logs
def Sync.kept(
  +n: String,
  +s: Basics.Node,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.Keeps(s, Reading.Node.sync(n, s, t)):
  +s1 = Voting.Node.take(s, t)
  +cs = Voting.Sync.lines(s, s1, t)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
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
  Kept.trans(
    s,
    s1,
    Reading.Node.adopts(n, cs, s3),
    Take.kept(s, t),
    Kept.trans(
      s1,
      s2,
      Reading.Node.adopts(n, cs, s3),
      Steps.kept(n, cs, s1),
      Kept.trans(
        s2,
        s3,
        Reading.Node.adopts(n, cs, s3),
        More.kept(
          List.length(&2, Ledgers.Ballot, bs),
          n,
          cs,
          List.length(&2, Ledgers.Ballot, bs),
          bs,
          Sealing.Pending.of(bs),
          s2
        ),
        Adopts.kept(n, cs, s3)
      )
    )
  )

# a request that a writer asks again at a node only grows it
def Consent.grows(
  +n: String,
  +s: Basics.Node,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> {Reading.Node.grows(s, Voting.Consent.at(n, s, i, m)) == True{}: Bool}:
  match m:
    case None{}:
      ProofTrees.Grows.refl(s)
    case Some{+c}:
      ProofTrees.Grows.trans(
        s,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
        Voting.Node.step(n, Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)), c)
      )(
        ProofTrees.Grows.to(
          s,
          s,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
          ProofTrees.Led.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
          ProofTrees.Grows.refl(s)
        )
      )(
        ProofTrees.Step.grows(
          n,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
          c
        )
      )

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  n: String,
  +s: Basics.Node,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Voting.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Kept.trans(
        s,
        Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
        Voting.Node.step(n, Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)), c),
        Kept.same(
          s,
          Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
          ProofTrees.Grows.to(
            s,
            s,
            Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)),
            ProofTrees.Grows.refl(s)
          ),
          Heads.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i))
        ),
        Step.kept(n, Basics.State.keyed(s, Sealing.Keys.mark(Basics.State.keys(s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  +n: String,
  +s: Basics.Node,
  ev: Spec.Deed
) -> {Reading.Node.grows(s, Spec.Node.does(n, s, ev)) == True{}: Bool}:
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      ProofTrees.Grows.trans(
        s,
        Voting.Node.ask(n, s, e, q),
        Reading.Adopt.at(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Basics.Envelope.of(e), q))
      )(
        ProofTrees.Ask.grows(n, s, e, q)
      )(
        ProofTrees.Adopt.at.grows(
          n,
          Voting.Node.ask(n, s, e, q),
          Basics.Ask.chain(Basics.Envelope.of(e), q)
        )
      )
    case Spec.Deed.Take{t}:
      ProofTrees.Take.grows(s, t)
    case Spec.Deed.Sync{t}:
      ProofTrees.Sync.grows(n, s, t)
    case Spec.Deed.Keep{b}:
      ProofTrees.Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b)))
    case Spec.Deed.Consent{+i}:
      ProofTrees.Grows.trans(
        s,
        Voting.Node.consent(n, s, i),
        Reading.Adopt.maybe(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i))
      )(
        Consent.grows(n, s, i, Basics.Node.chain_of(s, i))
      )(ProofTrees.Adopt.maybe.grows(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i)))
    case Spec.Deed.Pass{+c}:
      ProofTrees.Grows.trans(
        s,
        Voting.Node.pass(n, s, c),
        Reading.Adopt.at(n, Voting.Node.pass(n, s, c), c)
      )(ProofTrees.Pass.grows(n, s, c))(ProofTrees.Adopt.at.grows(n, Voting.Node.pass(n, s, c), c))

def Spec.Node.after_grows(n, evs, s):
  match evs:
    case Nil{}:
      ProofTrees.Grows.refl(s)
    case Con{+ev, +rest}:
      +s1 = Spec.Node.does(n, s, ev)
      ProofTrees.Grows.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1)
      )(Does.grows(n, s, ev))(Spec.Node.after_grows(n, rest, s1))

# what a node does keeps the logs
def Does.kept(
  +n: String,
  +s: Basics.Node,
  ev: Spec.Deed
) -> Spec.Node.Keeps(s, Spec.Node.does(n, s, ev)):
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      Kept.trans(
        s,
        Voting.Node.ask(n, s, e, q),
        Reading.Adopt.at(
          n,
          Voting.Node.ask(n, s, e, q),
          Basics.Ask.chain(Basics.Envelope.of(e), q)
        ),
        Ask.kept(n, s, e, q),
        Adopt.at.kept(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Basics.Envelope.of(e), q))
      )
    case Spec.Deed.Take{t}:
      Take.kept(s, t)
    case Spec.Deed.Sync{t}:
      Sync.kept(n, s, t)
    case Spec.Deed.Keep{+b}:
      Kept.same(
        s,
        Basics.Node.keep(s, b),
        ProofTrees.Grows.keep(s, Ropes.Put.nodes(Basics.Bytes.rope(b))),
        Heads.led(
          s,
          Ledgers.State.put_datas(
            ~Basics.Ask,
            ~Basics.Ask.is_eq,
            Ropes.Put.nodes(Basics.Bytes.rope(b)),
            Basics.State.ledger(s)
          )
        )
      )
    case Spec.Deed.Consent{+i}:
      Kept.trans(
        s,
        Voting.Node.consent(n, s, i),
        Reading.Adopt.maybe(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i)),
        Consent.kept(n, s, i, Basics.Node.chain_of(s, i)),
        Adopt.maybe.kept(n, Voting.Node.consent(n, s, i), Basics.Node.chain_of(s, i))
      )
    case Spec.Deed.Pass{+c}:
      Kept.trans(
        s,
        Voting.Node.pass(n, s, c),
        Reading.Adopt.at(n, Voting.Node.pass(n, s, c), c),
        Pass.kept(n, s, c),
        Adopt.at.kept(n, Voting.Node.pass(n, s, c), c)
      )
    case Spec.Deed.Pass{c}:
      Pass.kept(n, s, c)

def Spec.Node.after_keeps(n, evs, s):
  match evs:
    case Nil{}:
      Kept.refl(s)
    case Con{+ev, rest}:
      s1 = Spec.Node.does(n, s, ev)
      Kept.trans(
        s,
        s1,
        Spec.Node.after(n, rest, s1),
        Does.kept(n, s, ev),
        Spec.Node.after_keeps(n, rest, s1)
      )
