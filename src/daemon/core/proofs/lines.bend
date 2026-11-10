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
import ../../shared/shared/store.bend as Stores
import ../../replica/impl.bend as Replicas

# Lines
# -----
# The log of a line, as a node knows it, only gains keys: a key that it holds,
# other than the owners and the count, holds the same value after the node
# takes in a request, or what another node sent, or does a sync.

# a tip that a node holds, a node that grew from it holds
def Tip.at.grows(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  +x: Hashes.Hash,
  -t: Replicas.Tip,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Replicas.Tip.at(~Basics.Ask.machine(), a, x) == Some{t}: Maybe<&2, Replicas.Tip>
} -> {Replicas.Tip.at(~Basics.Ask.machine(), b, x) == Some{t}: Maybe<&2, Replicas.Tip>}:
  Shared.Maybe.bind_kept(
    List<&2, U32>,
    Replicas.Tip,
    Replicas.Store.fetch(~Basics.Ask.machine(), a, x),
    Replicas.Store.fetch(~Basics.Ask.machine(), b, x),
    ws => Replicas.Tip.read(ws),
    ws => Replicas.Tip.read(ws),
    t,
    w => Ledgers.State.data_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~Basics.Ask.laws(),
      Replicas.State.ledger(~Basics.Ask.machine(), a),
      Replicas.State.ledger(~Basics.Ask.machine(), b),
      x,
      w
    )(g),
    w => e => e
  )

# the tip of a head, in a node that grew
def Head.tip.grows(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  h: Replicas.Head,
  -t: Replicas.Tip,
  g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Replicas.Head.tip(~Basics.Ask.machine(), a, h) == Some{t}: Maybe<&2, Replicas.Tip>
} -> {Replicas.Head.tip(~Basics.Ask.machine(), b, h) == Some{t}: Maybe<&2, Replicas.Tip>}:
  match h:
    case Replicas.Head{r, br, n, th}:
      Shared.Maybe.bind_kept(
        Hashes.Hash,
        Replicas.Tip,
        th,
        th,
        x => Replicas.Tip.at(~Basics.Ask.machine(), a, x),
        x => Replicas.Tip.at(~Basics.Ask.machine(), b, x),
        t,
        x => e => e,
        +x => Tip.at.grows(a, b, x, t, g)
      )

# what the log of a head holds, in a node that grew
def Head.get.grows(
  +a: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +h: Replicas.Head,
  k: List<&2, U32>,
  v: List<&2, U32>,
  +g: {Reading.Node.grows(a, b) == True{}: Bool}
) -> {
  Replicas.Head.get(~Basics.Ask.machine(), a, h, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, h, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Replicas.Tip,
    List<&2, U32>,
    Replicas.Head.tip(~Basics.Ask.machine(), a, h),
    Replicas.Head.tip(~Basics.Ask.machine(), b, h),
    t => Replicas.Node.get(~Basics.Ask.machine(), a, Replicas.Tip.log(t), k),
    t => Replicas.Node.get(~Basics.Ask.machine(), b, Replicas.Tip.log(t), k),
    v,
    t => Head.tip.grows(a, b, h, t, g),
    t => ProofLogs.Get.grows(a, b, Replicas.Tip.log(t), k, v, g)
  )

# a line whose head is the same in a node that grew holds what it held
def Line.same(
  +a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Replicas.Node.head_of(~Basics.Ask.machine(), b, c): Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Line.get(~Basics.Ask.machine(), b, c, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  Shared.Maybe.bind_kept(
    Replicas.Head,
    List<&2, U32>,
    Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
    Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
    h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k),
    h => Replicas.Head.get(~Basics.Ask.machine(), b, h, k),
    v,
    h => e => Equal.trans(
      Maybe<&2, Replicas.Head>,
      Replicas.Node.head_of(~Basics.Ask.machine(), b, c),
      Replicas.Node.head_of(~Basics.Ask.machine(), a, c),
      Some{h},
      Equal.sym(Maybe<&2, Replicas.Head>, Replicas.Node.head_of(~Basics.Ask.machine(), a, c), Replicas.Node.head_of(~Basics.Ask.machine(), b, c), eh),
      e
    ),
    +h => Head.get.grows(a, b, h, k, v, g)
  )

# a node keeps its own logs
def Kept.refl(-s: Replicas.Node<Basics.Ask>) -> Spec.Node.Keeps(s, s):
  c => k => v => e => e

# keeping composes
def Kept.trans(
  -a: Replicas.Node<Basics.Ask>,
  -b: Replicas.Node<Basics.Ask>,
  -d: Replicas.Node<Basics.Ask>,
  h1: Spec.Node.Keeps(a, b),
  h2: Spec.Node.Keeps(b, d)
) -> Spec.Node.Keeps(a, d):
  +c => +k => +v => e => h2(c)(k)(v)(h1(c)(k)(v)(e))

# one of two nodes, each of which keeps the logs of s
def Kept.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: Spec.Node.Keeps(s, x),
  hy: Spec.Node.Keeps(s, y)
) -> Spec.Node.Keeps(s, Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a node that grew, with the same heads, keeps the logs
def Kept.same(
  a: Replicas.Node<Basics.Ask>,
  b: Replicas.Node<Basics.Ask>,
  g: {Reading.Node.grows(a, b) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b): Tries.Trie<Replicas.Head>}
) -> Spec.Node.Keeps(a, b):
  +c => k => v => Line.same(
    a,
    b,
    c,
    k,
    v,
    g,
    Equal.cong(
      Tries.Trie<Replicas.Head>,
      Maybe<&2, Replicas.Head>,
      hs => Tries.Trie.get(Replicas.Head, hs, Ledgers.Chain.key(c)),
      Replicas.State.heads(~Basics.Ask.machine(), a),
      Replicas.State.heads(~Basics.Ask.machine(), b),
      eh
    )
  )

# a new ledger keeps the heads
def Heads.led(
  s: Replicas.Node<Basics.Ask>,
  l: Ledgers.State(Basics.Ask)
) -> {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.State.led(~Basics.Ask.machine(), s, l)): Tries.Trie<Replicas.Head>}:
  match s:
    case Replicas.Node{old, hs, ws, ks}:
      {==}

# new waiting requests keep the heads
def Heads.wait(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  qs: List<&2, Ledgers.Id>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Wait.set(s, c, qs)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# the head of a line, after the head of the line c is set
def Head.of_set(
  b0: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  hd: Replicas.Head,
  c2: Ledgers.Chain
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), 
    Sealing.State.head(b0, c, hd),
    c2
  )
    == Bool.pick(
      Maybe<&2, Replicas.Head>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      Some{hd},
      Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2)
    ): Maybe<&2, Replicas.Head>
}:
  match b0:
    case Replicas.Node{l, hs, ws, ks}:
      Tries.Trie.get_set(Replicas.Head, hs, Ledgers.Chain.key(c), hd, Ledgers.Chain.key(c2))

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
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -m: Maybe<&2, Replicas.Head>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == m: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {
  Maybe.bind(
    &2,
    Replicas.Head,
    List<&2, U32>,
    m,
    h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  e =>
    %em: {
      Maybe.bind(
        &2,
        Replicas.Head,
        List<&2, U32>,
        _,
        h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    e

# Head.put.kept once whether c2 is the line c is known (bs)
def Head.put.kept.if(
  +a: Replicas.Node<Basics.Ask>,
  +b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +hd: Replicas.Head,
  +c2: Ledgers.Chain,
  k: List<&2, U32>,
  v: List<&2, U32>,
  bs: Bool,
  +ebs: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == bs: Bool},
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  cov: {
    Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Head.get(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c2, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Line.get(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  match bs:
    case True{}:
      e =>
        %Equal.sym(
          Maybe<&2, Replicas.Head>,
          Replicas.Node.head_of(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), c2),
          Some{hd},
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
            Head.of_set(b0, c, hd, c2),
            Pick.of(
              Maybe<&2, Replicas.Head>,
              True{},
              Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
              Some{hd},
              Replicas.Node.head_of(~Basics.Ask.machine(), b0, c2),
              ebs
            )
          )
        ): {
          Maybe.bind(
            &2,
            Replicas.Head,
            List<&2, U32>,
            _,
            h => Replicas.Head.get(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), h, k)
          )
            == Some{v}: Maybe<&2, List<&2, U32>>
        }
        cov(
          Equal.trans(
            Maybe<&2, List<&2, U32>>,
            Replicas.Line.get(~Basics.Ask.machine(), a, c, k),
            Replicas.Line.get(~Basics.Ask.machine(), a, c2, k),
            Some{v},
            Equal.cong(
              List<&2, Bool>,
              Maybe<&2, List<&2, U32>>,
              kk => Maybe.bind(
                &2,
                Replicas.Head,
                List<&2, U32>,
                Tries.Trie.get(Replicas.Head, Replicas.State.heads(~Basics.Ask.machine(), a), kk),
                h => Replicas.Head.get(~Basics.Ask.machine(), a, h, k)
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
              Head.of_set(b0, c, hd, c2),
              Pick.of(
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
      )

# a node b0 with a new head hd of the line c keeps the logs of a, when b0 grew
# from a with the same heads, and hd holds what the line c holds in a
def Head.put.kept(
  a: Replicas.Node<Basics.Ask>,
  b0: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  hd: Replicas.Head,
  g: {Reading.Node.grows(a, b0) == True{}: Bool},
  eh: {Replicas.State.heads(~Basics.Ask.machine(), a) == Replicas.State.heads(~Basics.Ask.machine(), b0): Tries.Trie<Replicas.Head>},
  cover: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Head.get(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd), hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(a, Sealing.State.head(b0, c, hd)):
  +c2 => +k => +v => Head.put.kept.if(
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
    cover(k)(v)
  )

# one of two nodes, each with the heads of s
def Heads.when(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  -y: Replicas.Node<Basics.Ask>,
  hx: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), x): Tries.Trie<Replicas.Head>},
  hy: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), y): Tries.Trie<Replicas.Head>}
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Shared.Bool.when(Replicas.Node<Basics.Ask>, b, u => x, u => y)): Tries.Trie<Replicas.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# new keys keep the heads
def Heads.keyed(
  s: Replicas.Node<Basics.Ask>,
  ks: Replicas.Keys
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Replicas.State.keyed(~Basics.Ask.machine(), s, ks)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, old}:
      {==}

# the heads of the node m, if any, else of s
def Heads.of(s: Replicas.Node<Basics.Ask>, m: Maybe<&2, Replicas.Node<Basics.Ask>>) -> Tries.Trie<Replicas.Head>:
  match m:
    case None{}:
      Replicas.State.heads(~Basics.Ask.machine(), s)
    case Some{s2}:
      Replicas.State.heads(~Basics.Ask.machine(), s2)

# a node that is kept when b holds has the heads of s, when it has
def Heads.some.if(
  b: Bool,
  -s: Replicas.Node<Basics.Ask>,
  -x: Replicas.Node<Basics.Ask>,
  hx: {Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), x): Tries.Trie<Replicas.Head>}
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Heads.of(s, Shared.Maybe.when(Replicas.Node<Basics.Ask>, b, u => Some{x})): Tries.Trie<Replicas.Head>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the heads
def Accept.at.heads(
  +s: Replicas.Node<Basics.Ask>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Replicas.Keychain>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, Sealing.Seal.accept.at(s, b, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Heads.some.if(
        Sealing.Seal.fits(c, b),
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), 
          Replicas.State.led(~Basics.Ask.machine(), 
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Sealing.Keys.saw(
            Sealing.Keys.set(
              Replicas.State.keys(~Basics.Ask.machine(), s),
              Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
              Sealing.Keychain.next(c, b)
            ),
            Sealing.Ballot.at(b)
          )
        ),
        Equal.trans(
          Tries.Trie<Replicas.Head>,
          Replicas.State.heads(~Basics.Ask.machine(), s),
          Replicas.State.heads(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            )
          ),
          Replicas.State.heads(~Basics.Ask.machine(), 
            Replicas.State.keyed(~Basics.Ask.machine(), 
              Replicas.State.led(~Basics.Ask.machine(), 
                s,
                Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
              ),
              Sealing.Keys.saw(
                Sealing.Keys.set(
                  Replicas.State.keys(~Basics.Ask.machine(), s),
                  Sealing.Seal.slot(Sealing.Ballot.store(b), Sealing.Ballot.node(b)),
                  Sealing.Keychain.next(c, b)
                ),
                Sealing.Ballot.at(b)
              )
            )
          ),
          Heads.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
          ),
          Heads.keyed(
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Sealing.Keys.saw(
              Sealing.Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
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
  -s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, m): Tries.Trie<Replicas.Head>
} -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Maybe.default(&2, Replicas.Node<Basics.Ask>, m, s)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => e

# a sealed ballot keeps the heads
def Cast.seal.heads(
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  n: String,
  a0: Ledgers.Act,
  m: Maybe<&2, Replicas.Keychain>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Cast.seal(s, w, n, a0, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Replicas.Keychain{+j, last, key, f}}:
      +b = Ledgers.Ballot.make(
        Sealing.Seal.secret(Sealing.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)), Sealing.Where.store(w), j),
        Ledgers.Signed{w, n, a0},
        last,
        Seals.Seal.public(
          Sealing.Seal.secret(
            Sealing.Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s)),
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
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +w: Ledgers.Where,
  +n: String,
  a0: Ledgers.Act
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Cast.vote(s, m, w, n, a0)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+s3}:
      +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
      Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s4),
        Replicas.State.heads(~Basics.Ask.machine(), 
          Sealing.Cast.seal(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
        ),
        Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
        Cast.seal.heads(s4, w, n, a0, Sealing.Seal.chain(s4, Sealing.Where.store(w), n))
      )

# the ballots that a chain leads to keep the heads, when each one more does
def Follow.step.heads(
  -s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  -k: Replicas.Node<Basics.Ask> -> Replicas.Node<Basics.Ask>,
  ih: @s2: Replicas.Node<Basics.Ask> -> {
    Replicas.State.heads(~Basics.Ask.machine(), s2) == Replicas.State.heads(~Basics.Ask.machine(), k(s2)): Tries.Trie<Replicas.Head>
  }
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Heads.of(s, m): Tries.Trie<Replicas.Head>
} -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), 
      Maybe.default(
        &2,
        Replicas.Node<Basics.Ask>,
        Maybe.bind(&2, Replicas.Node<Basics.Ask>, Replicas.Node<Basics.Ask>, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s2),
        Replicas.State.heads(~Basics.Ask.machine(), k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the heads
def Follow.heads(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Sealed.follow(f, s, p, r, n, mb)): Tries.Trie<Replicas.Head>
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
  +s: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Sealed.each(f, bs, p, s)): Tries.Trie<Replicas.Head>
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
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s1),
        Replicas.State.heads(~Basics.Ask.machine(), Sealing.Sealed.each(f, rest, p, s1)),
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
  s: Replicas.Node<Basics.Ask>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Sealing.Cast.put(n, w, th, qs, from, m, s)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{Stepping.Run{s2, +t2}}:
      Cast.vote.heads(
        s,
        Judging.State.put(s2, [Replicas.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}
      )

# a pass keeps the heads
def Pass.to.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  os: List<&2, String>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Voting.Pass.to(n, s, w, os)): Tries.Trie<Replicas.Head>
}:
  match w:
    case Ledgers.Where{+c, +h, +r}:
      Heads.when(
        List.all.if(
          u => Maybe.is_none(
            &2,
            Maybe<&2, Ledgers.Last>,
            Ledgers.State.passed(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Where{c, h, r}, n)
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
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: U32,
  os: List<&2, String>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Voting.Round.join(n, s, c, h, os)): Tries.Trie<Replicas.Head>
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
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +next: U32,
  +th: Maybe<&2, Hashes.Hash>,
  +t: Replicas.Tip
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Voting.Cast.round(n, s, c, next, th, t)): Tries.Trie<Replicas.Head>
}:
  +os = Replicas.Tip.owners(t)
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
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Voting.Cast.at(n, s, c, h, m)): Tries.Trie<Replicas.Head>
}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{+t}:
      s1 = Voting.Round.join(n, s, c, next, Replicas.Tip.owners(t))
      Equal.trans(
        Tries.Trie<Replicas.Head>,
        Replicas.State.heads(~Basics.Ask.machine(), s),
        Replicas.State.heads(~Basics.Ask.machine(), s1),
        Replicas.State.heads(~Basics.Ask.machine(), Voting.Cast.round(n, s1, c, next, th, t)),
        Round.join.heads(n, s, c, next, Replicas.Tip.owners(t)),
        Cast.round.heads(n, s1, c, next, th, t)
      )
    case Replicas.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, at the head h whose tip is m
def Pass.at.heads(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), 
    s
  )
    == Replicas.State.heads(~Basics.Ask.machine(), Voting.Pass.at(n, s, c, h, m)): Tries.Trie<Replicas.Head>
}:
  match h m:
    case Replicas.Head{r, b, +next, th} Some{t}:
      Pass.to.heads(
        n,
        s,
        Ledgers.Where{c, next, 1n+Voting.Round.mine(n, s, c, next, Sealing.Round.seen(s, c, next))},
        Replicas.Tip.owners(t)
      )
    case Replicas.Head{r, b, next, th} None{}:
      {==}

# Node.pass keeps the heads, once the head m is known
def Pass.head.heads(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Voting.Pass.head(n, s, c, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Pass.at.heads(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# Node.cast keeps the heads, once the head m is known
def Cast.head.heads(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Voting.Cast.head(n, s, c, m)): Tries.Trie<Replicas.Head>
}:
  match m:
    case None{}:
      {==}
    case Some{+h}:
      Cast.at.heads(n, s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))

# a node's ballot keeps its logs
def Cast.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.cast(n, s, c)):
  Kept.same(
    s,
    Voting.Node.cast(n, s, c),
    ProofTrees.Cast.grows(n, s, c),
    Cast.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  )

# the words of a tip read as the tip
def Tip.round(
  t: Replicas.Tip
) -> {Replicas.Tip.read(Replicas.Tip.words(t)) == Some{t}: Maybe<&2, Replicas.Tip>}:
  match t:
    case Replicas.Tip{+c, +l, +n, +os}:
      %Equal.sym(
        Maybe<&2, Codes.Read<Replicas.Tip>>,
        Codes.Code.four.read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Replicas.Tip,
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
          ~Codes.Codec.dec(U32, Codes.Code.token.codec()),
          ~Codes.Codec.dec(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec())),
          x => y => z => w => Replicas.Tip{x, y, z, w},
          Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(c)(
            Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()))(l)(
              Codes.Codec.enc(U32, Codes.Code.token.codec())(n)(Codes.Codec.enc(List<&2, String>, Codes.Code.list.codec(~String, ~Codes.Code.text.codec()))(os)([]))
            )
          )
        ),
        Some{Codes.Read{Replicas.Tip{c, l, n, os}, []}},
        Codes.Code.four_read(
          ~Maybe<&2, Hashes.Hash>,
          ~Maybe<&2, Hashes.Hash>,
          ~U32,
          ~List<&2, String>,
          ~Replicas.Tip,
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
          ~Codes.Code.token.codec(),
          ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
          x => y => z => w => Replicas.Tip{x, y, z, w},
          c,
          l,
          n,
          os,
          []
        )
      ): {Replicas.Read.whole(Replicas.Tip, _) == Some{Replicas.Tip{c, l, n, os}}: Maybe<&2, Replicas.Tip>}
      {==}

# Put.holds once whether the node holds the data is known (b)
def Put.holds.if(
  -s2: Replicas.Node<Basics.Ask>,
  -ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>,
  b: Bool,
  eb: {
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s2, ds), ds) == b: Bool
  }
) -> {
  Shared.Maybe.when(
    Replicas.Node<Basics.Ask>,
    b,
    u => Some{Replicas.State.keep(~Basics.Ask.machine(), s2, ds)}
  )
    == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool}:
  match b:
    case False{}:
      e => Empty.absurd(
        {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool},
        Shared.Maybe.none_ne_some(Replicas.Node<Basics.Ask>, s3, e)
      )
    case True{}:
      e =>
        %Shared.Maybe.some_inj(
          Replicas.Node<Basics.Ask>,
          Replicas.State.keep(~Basics.Ask.machine(), s2, ds),
          s3,
          e
        ): {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), _, ds) == True{}: Bool}
        eb

# a node that a put gives holds the data
def Put.holds(
  s2: Replicas.Node<Basics.Ask>,
  +ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>
) -> {
  Judging.State.put(s2, ds) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, ds) == True{}: Bool}:
  Put.holds.if(
    s2,
    ds,
    s3,
    Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), Replicas.State.keep(~Basics.Ask.machine(), s2, ds), ds),
    {==}
  )

# a node that a put gives grew
def Put.grew(
  s2: Replicas.Node<Basics.Ask>,
  ds: List<&2, List<&2, U32>>,
  -s3: Replicas.Node<Basics.Ask>,
  e: {Judging.State.put(s2, ds) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>}
) -> {Reading.Node.grows(s2, s3) == True{}: Bool}:
  %e: {ProofTrees.State.after(s2, _) == True{}: Bool}
  ProofTrees.Put.grows(s2, ds)

# a node that the put of a tip gives holds the tip under its hash
def Tip.put.at(
  s2: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  +s3: Replicas.Node<Basics.Ask>
) -> {
  Judging.State.put(s2, [Replicas.Tip.words(t2)]) == Some{s3}: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Replicas.Store.fetch(~Basics.Ask.machine(), s3, Hashes.Sha.hash(Replicas.Tip.words(t2))),
      Some{Replicas.Tip.words(t2)},
      Shared.Maybe.is_eq_sound(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
        Replicas.Store.fetch(~Basics.Ask.machine(), s3, Hashes.Sha.hash(Replicas.Tip.words(t2))),
        Some{Replicas.Tip.words(t2)}
      )(
        Shared.List.all.if_hit(
          Stores.Store.has(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, Replicas.Tip.words(t2)),
          u => Stores.Store.holds(~Replicas.Node<Basics.Ask>, ~Replicas.Store.fetch(~Basics.Ask.machine()), s3, [])
        )(Put.holds(s2, [Replicas.Tip.words(t2)], s3)(e))
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        Replicas.Tip,
        _,
        ws => Replicas.Tip.read(ws)
      )
        == Some{t2}: Maybe<&2, Replicas.Tip>
    }
    Tip.round(t2)

# what a line holds is what the log of its tip holds
def Line.read.at(
  -s: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -h: Replicas.Head,
  -t: Replicas.Tip,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), s, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e =>
    %et: {
      Maybe.bind(
        &2,
        Replicas.Tip,
        List<&2, U32>,
        _,
        t1 => Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t1), k)
      )
        == Some{v}: Maybe<&2, List<&2, U32>>
    }
    Line.get.of(s, c, k, v, Some{h}, em)(e)

# a head at the tip t2 holds what the log of t2 holds, in a node that grew
# from one that holds the tip
def Moved.cover(
  +s3: Replicas.Node<Basics.Ask>,
  +b: Replicas.Node<Basics.Ask>,
  +t2: Replicas.Tip,
  k: List<&2, U32>,
  v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -nx: U32,
  +g: {Reading.Node.grows(s3, b) == True{}: Bool},
  e3: {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>},
  v3: {Replicas.Node.get(~Basics.Ask.machine(), s3, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Replicas.Head.get(~Basics.Ask.machine(), 
    b,
    Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}},
    k
  )
    == Some{v}: Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Replicas.Tip>,
    Replicas.Tip.at(~Basics.Ask.machine(), b, Replicas.Tip.hash(t2)),
    Some{t2},
    Tip.at.grows(s3, b, Replicas.Tip.hash(t2), t2, g)(e3)
  ): {
    Maybe.bind(
      &2,
      Replicas.Tip,
      List<&2, U32>,
      _,
      t1 => Replicas.Node.get(~Basics.Ask.machine(), b, Replicas.Tip.log(t1), k)
    )
      == Some{v}: Maybe<&2, List<&2, U32>>
  }
  ProofLogs.Get.grows(s3, b, Replicas.Tip.log(t2), k, v, g)(v3)

# a head moved to the tip t2 keeps the logs, when the log of t2 holds what
# the log of the tip t of the head before holds
def Moved.kept(
  +s: Replicas.Node<Basics.Ask>,
  +s3: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  t: Replicas.Tip,
  g3: {Reading.Node.grows(s, s3) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>},
  e3: {Replicas.Tip.at(~Basics.Ask.machine(), s3, Replicas.Tip.hash(t2)) == Some{t2}: Maybe<&2, Replicas.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Node.get(~Basics.Ask.machine(), s3, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> Spec.Node.Keeps(
  s,
  Sealing.State.moved(
    Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
    c,
    Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}},
    qs
  )
):
  +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
  +ws = Sealing.Wait.left(
    Sealing.Wait.of(x, c),
    Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
  )
  +b0 = Sealing.Wait.set(x, c, ws)
  +hd = {Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}}: Replicas.Head}
  Head.put.kept(
    s,
    b0,
    c,
    hd,
    ProofTrees.Grows.to(s, x, b0, ProofTrees.Led.wait(x, c, ws), ProofTrees.Grows.back(s, s3, g3)),
    Equal.trans(
      Tries.Trie<Replicas.Head>,
      Replicas.State.heads(~Basics.Ask.machine(), s),
      Replicas.State.heads(~Basics.Ask.machine(), x),
      Replicas.State.heads(~Basics.Ask.machine(), b0),
      Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3)),
      Heads.wait(x, c, ws)
    ),
    +k => +v => e => Moved.cover(
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
          Replicas.State.ledger(~Basics.Ask.machine(), Sealing.State.head(b0, c, hd)),
          Replicas.State.ledger(~Basics.Ask.machine(), b0),
          Replicas.State.ledger(~Basics.Ask.machine(), s3),
          ProofTrees.Led.head(b0, c, hd),
          Equal.trans(
            Ledgers.State(Basics.Ask),
            Replicas.State.ledger(~Basics.Ask.machine(), b0),
            Replicas.State.ledger(~Basics.Ask.machine(), x),
            Replicas.State.ledger(~Basics.Ask.machine(), s3),
            ProofTrees.Led.wait(x, c, ws),
            ProofTrees.Led.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          )
        ),
        ProofTrees.Grows.refl(s3)
      ),
      e3,
      kk(k)(v)(Line.read.at(s, c, k, v, h, t, em, et)(e))
    )
  )

# Advance.moved keeps the logs, once the node m that the put gives is known
def Advance.moved.kept(
  +s: Replicas.Node<Basics.Ask>,
  +s2: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  nx: U32,
  +t2: Replicas.Tip,
  qs: List<&2, Ledgers.Id>,
  h: Replicas.Head,
  t: Replicas.Tip,
  g2: {Reading.Node.grows(s, s2) == True{}: Bool},
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>},
  kk: @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> {Replicas.Node.get(~Basics.Ask.machine(), s2, Replicas.Tip.log(t2), k) == Some{v}: Maybe<&2, List<&2, U32>>}
) -> {
  Judging.State.put(s2, [Replicas.Tip.words(t2)]) == m: Maybe<&2, Replicas.Node<Basics.Ask>>
} -> Spec.Node.Keeps(
  s,
  Voting.Advance.moved(s, m, c, Replicas.Head{r, br, nx, Some{Replicas.Tip.hash(t2)}}, qs)
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
        ProofTrees.Grows.trans(s, s2, s3)(g2)(Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)),
        em,
        et,
        Tip.put.at(s2, t2, s3)(e2),
        +k => +v => e => ProofLogs.Get.grows(
          s2,
          s3,
          Replicas.Tip.log(t2),
          k,
          v,
          Put.grew(s2, [Replicas.Tip.words(t2)], s3, e2)
        )(kk(k)(v)(e))
      )

# a checked step keeps the logs
def Advance.ran.kept(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  r: Ledgers.Id,
  br: Maybe<&2, String>,
  next: U32,
  after: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  m: Maybe<&2, Stepping.Run>,
  h: Replicas.Head,
  t: Replicas.Tip,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>},
  et: {Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>}
) -> {
  ProofTrees.Run.after(s, m) == True{}: Bool
} -> (
  @k: List<
    &2,
    U32> -> @v: List<
    &2,
    U32> -> {
    Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), k) == Some{v}: Maybe<&2, List<&2, U32>>
  } -> ProofLogs.Run.Keeps(k, v, m)
) -> Spec.Node.Keeps(s, Voting.Advance.ran(s, c, r, br, next, after, qs, m)):
  match m:
    case None{}:
      ga => rk => Kept.refl(s)
    case Some{Stepping.Run{+s2, +t2}}:
      ga => rk => Kept.when(
        Sealing.Root.same(after, Some{Replicas.Tip.hash(t2)}),
        s,
        Voting.Advance.moved(
          s,
          Judging.State.put(s2, [Replicas.Tip.words(t2)]),
          c,
          Replicas.Head{r, br, U32.inc(next), Some{Replicas.Tip.hash(t2)}},
          qs
        ),
        s,
        Advance.moved.kept(
          s,
          s2,
          Judging.State.put(s2, [Replicas.Tip.words(t2)]),
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
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  +t: Replicas.Tip,
  m: Maybe<&2, Ledgers.Vote>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == Some{t}: Maybe<&2, Replicas.Tip>
} -> Spec.Node.Keeps(s, Voting.Advance.step(s, c, h, t, m)):
  match h m:
    case Replicas.Head{+r, +br, +next, +th} Some{Ledgers.Vote{before, +qs, after}}:
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
          Replicas.Head{r, br, next, th},
          t,
          em,
          et
        )(
          ProofTrees.Run.grows(s, c, t, qs)
        )(+k => +v => ProofLogs.Run.kept(s, c, t, qs, k, v)),
        Kept.refl(s)
      )
    case Replicas.Head{r, br, next, th} None{}:
      em => et => Kept.refl(s)

# Node.advance keeps the logs, at the head h whose tip is m
def Advance.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  +h: Replicas.Head,
  m: Maybe<&2, Replicas.Tip>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == Some{h}: Maybe<&2, Replicas.Head>
} -> {
  Replicas.Head.tip(~Basics.Ask.machine(), s, h) == m: Maybe<&2, Replicas.Tip>
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
          Replicas.Tip.owners(t),
          Sealing.Round.seen(s, c, Sealing.Head.next(h))
        )
      )(em)(et)

# Advances.kept once the head m is known
def Advances.at.kept(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.Keeps(s, Voting.Advances.at(f, s, c, m)):
  match f m:
    case 0n x:
      em => Kept.refl(s)
    case 1n+p None{}:
      em => Kept.refl(s)
    case 1n+(+p) Some{+h}:
      +em =>
        +s1 = Voting.Advance.at(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))
        +m1 = Replicas.Node.head_of(~Basics.Ask.machine(), s1, c)
        Kept.when(
          Voting.Heads.level(Some{h}, m1),
          s,
          s1,
          Voting.Advances.at(p, s1, c, m1),
          Advance.at.kept(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
          Kept.trans(
            s,
            s1,
            Voting.Advances.at(p, s1, c, m1),
            Advance.at.kept(s, c, h, Replicas.Head.tip(~Basics.Ask.machine(), s, h))(em)({==}),
            Advances.at.kept(p, s1, c, m1)({==})
          )
        )

# a head that moves over each decided step keeps the logs
def Advances.kept(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.advances(f, s, c)):
  Advances.at.kept(f, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==})

# what a node does at a head keeps the logs
def Step.head.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
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
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -b: Replicas.Node<Basics.Ask>,
  -hd: Replicas.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == None{}: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(List<&2, U32>, v, Line.get.of(a, c, k, v, None{}, em)(e))
  )

# a line whose head has no tip holds nothing
def Cover.wait(
  -a: Replicas.Node<Basics.Ask>,
  -c: Ledgers.Chain,
  -b: Replicas.Node<Basics.Ask>,
  -hd: Replicas.Head,
  -k: List<&2, U32>,
  -v: List<&2, U32>,
  -r: Ledgers.Id,
  -br: Maybe<&2, String>,
  -n: U32,
  em: {Replicas.Node.head_of(~Basics.Ask.machine(), a, c) == Some{Replicas.Head{r, br, n, None{}}}: Maybe<&2, Replicas.Head>}
) -> {
  Replicas.Line.get(~Basics.Ask.machine(), a, c, k) == Some{v}: Maybe<&2, List<&2, U32>>
} -> {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>}:
  e => Empty.absurd(
    {Replicas.Head.get(~Basics.Ask.machine(), b, hd, k) == Some{v}: Maybe<&2, List<&2, U32>>},
    Shared.Maybe.none_ne_some(
      List<&2, U32>,
      v,
      Line.get.of(a, c, k, v, Some{Replicas.Head{r, br, n, None{}}}, em)(e)
    )
  )

# a line that opens keeps the logs, once its head m is known
def Open.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.Keeps(s, Sealing.Open.at(s, c, m)):
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      +em =>
        +hd = {
          Replicas.Head{
            r,
            Some{b},
            0,
            Sealing.Branch.first(s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))
          }: Replicas.Head
        }
        Head.put.kept(
          s,
          s,
          c,
          hd,
          ProofTrees.Grows.refl(s),
          {==},
          k => v => Cover.wait(
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
    case Some{Replicas.Head{r, Some{b}, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Replicas.Head{r, None{}, n, t}}:
      em => Kept.refl(s)
    case None{}:
      em => Kept.refl(s)

# what a node does on a line keeps the logs
def Step.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.step(n, s, c)):
  s1 = Sealing.Node.open(s, c)
  Kept.trans(
    s,
    s1,
    Voting.Step.head(n, s1, c),
    Open.at.kept(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))({==}),
    Step.head.kept(n, s1, c)
  )

# a pass to the next round keeps the logs
def Pass.kept(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Voting.Node.pass(n, s, c)):
  +s1 = Voting.Pass.head(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
  Kept.trans(
    s,
    s1,
    Voting.Node.step(n, s1, c),
    Kept.same(
      s,
      s1,
      ProofTrees.Pass.head.grows(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c)),
      Pass.head.heads(n, s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))
    ),
    Step.kept(n, s1, c)
  )

# a first head keeps the logs, once the head m of its line is known
def First.at.kept(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, c) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.Keeps(s, Sealing.First.at(s, c, h, m)):
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      em => Kept.refl(s)
    case Some{Replicas.Head{r, b, n, None{}}}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        ProofTrees.Grows.refl(s),
        {==},
        k => v => Cover.wait(s, c, Sealing.State.head(s, c, h), h, k, v, r, b, n, em)
      )
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        c,
        h,
        ProofTrees.Grows.refl(s),
        {==},
        k => v => Cover.none(s, c, Sealing.State.head(s, c, h), h, k, v, em)
      )

# a first head on a node that grew from a, which grew from s, keeps the logs
def Start.head.kept(
  +s: Replicas.Node<Basics.Ask>,
  a: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  g: {Reading.Node.grows(s, a) == True{}: Bool}
) -> {
  ProofTrees.State.after(a, m) == True{}: Bool
} -> Spec.Node.Keeps(s, Sealing.Start.head(s, m, c, h)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{+s3}:
      e =>
        +x = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
        Kept.trans(
          s,
          x,
          Sealing.State.first(x, c, h),
          Kept.same(
            s,
            x,
            ProofTrees.Grows.back(s, s3, ProofTrees.Grows.trans(s, a, s3)(g)(e)),
            Heads.led(s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
          ),
          First.at.kept(x, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), x, c))({==})
        )

# Start.kept once the content m of the store is known
def Start.with.kept(
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  m: Maybe<&2, Judging.Work>
) -> {
  ProofTrees.Work.after(s, m) == True{}: Bool
} -> Spec.Node.Keeps(s, Sealing.Start.with(s, i, os, m)):
  match m:
    case None{}:
      e => Kept.refl(s)
    case Some{Judging.Work{+s2, +c}}:
      e =>
        +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
        Start.head.kept(
          s,
          s2,
          Judging.State.put(s2, [Replicas.Tip.words(t)]),
          Ledgers.Chain{i, None{}},
          Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}},
          e
        )(ProofTrees.Put.grows(s2, [Replicas.Tip.words(t)]))

# a store that starts keeps the logs
def Start.kept(
  +s: Replicas.Node<Basics.Ask>,
  i: Ledgers.Id,
  +os: List<&2, Basics.Owner>
) -> Spec.Node.Keeps(s, Sealing.Node.start(s, i, os)):
  Start.with.kept(
    s,
    i,
    Basics.Owner.names(os),
    Sealing.Seal.firsts(os, Some{Judging.Work{s, None{}}})
  )(ProofTrees.Firsts.after(s, os, Some{Judging.Work{s, None{}}})(ProofTrees.Grows.refl(s)))

# a line that a node follows keeps the logs, once its head m is known
def Follow.new.kept(
  +s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> {
  Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)) == m: Maybe<&2, Replicas.Head>
} -> Spec.Node.Keeps(s, Sealing.Follow.new(s, r, l, m)):
  match m:
    case Some{h}:
      em => Kept.refl(s)
    case None{}:
      +em => Head.put.kept(
        s,
        s,
        Replicas.Line.chain(r, l),
        Replicas.Head{r, l, 0, None{}},
        ProofTrees.Grows.refl(s),
        {==},
        k => v => Cover.none(
          s,
          Replicas.Line.chain(r, l),
          Sealing.State.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}}),
          Replicas.Head{r, l, 0, None{}},
          k,
          v,
          em
        )
      )

# a request that waits keeps the heads
def Heads.waits(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  i: Ledgers.Id
) -> {
  Replicas.State.heads(~Basics.Ask.machine(), s) == Replicas.State.heads(~Basics.Ask.machine(), Sealing.State.wait(s, c, i)): Tries.Trie<Replicas.Head>
}:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      {==}

# a new request keeps the logs
def Arrive.kept(
  +s: Replicas.Node<Basics.Ask>,
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
        Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
        Follow.new.kept(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))({==}),
        Kept.same(
          s1,
          Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
          ProofTrees.Grows.to(
            s1,
            s1,
            Sealing.State.wait(s1, Replicas.Line.chain(r, l), i),
            ProofTrees.Led.waits(s1, Replicas.Line.chain(r, l), i),
            ProofTrees.Grows.refl(s1)
          ),
          Heads.waits(s1, Replicas.Line.chain(r, l), i)
        )
      )

# a new request keeps the logs
def Ask.new.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  +q: Basics.Ask
) -> Spec.Node.Keeps(s, Voting.Node.ask.new(n, s, e, q)):
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
          ~Basics.Ask.laws(),
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          Ledgers.Slot.ask(i),
          Ledgers.Entry.Ask{i, Replicas.Envelope.time(e), q}
        )
      ),
      Heads.led(s, l0)
    ),
    Kept.trans(s0, s1, Voting.Node.step(n, s1, c), Arrive.kept(s0, i, q), Step.kept(n, s1, c))
  )

# Node.ask_keeps once the cell m of the request's ID is known
def Ask.at.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask,
  m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
) -> Spec.Node.Keeps(s, Voting.Node.ask.at(n, s, e, q, m)):
  match m:
    case Some{x}:
      Kept.refl(s)
    case None{}:
      Kept.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
        Voting.Node.ask.new(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        ),
        Kept.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          ProofTrees.Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
            ProofTrees.Grows.refl(s)
          ),
          Heads.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e)))
        ),
        Ask.new.kept(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), Replicas.Envelope.of(e))),
          e,
          q
        )
      )

# Node.ask keeps the logs
def Ask.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +e: Replicas.Envelope,
  q: Basics.Ask
) -> Spec.Node.Keeps(s, Voting.Node.ask(n, s, e, q)):
  Ask.at.kept(
    n,
    s,
    e,
    q,
    Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.ask(Replicas.Envelope.of(e)))
  )

# the new requests among cells keep the logs
def Take.asks.kept(
  cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Replicas.Node<Basics.Ask>
) -> Spec.Node.Keeps(s, Voting.Take.asks(cs, old, s)):
  match cs:
    case Nil{}:
      Kept.refl(s)
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
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.Keeps(s, Voting.Node.take(s, t)):
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
          ~Basics.Ask.laws(),
          Replicas.State.ledger(~Basics.Ask.machine(), s),
          sent
        )
      ),
      Heads.led(s, l1)
    ),
    Kept.trans(
      s1,
      s2,
      Sealing.Sealed.take(bs, s2),
      Take.asks.kept(cs, Replicas.State.ledger(~Basics.Ask.machine(), s), s1),
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
  +s: Replicas.Node<Basics.Ask>
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
  s: Replicas.Node<Basics.Ask>,
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
  +s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Head>
) -> Spec.Node.Keeps(s, Reading.Adopt.head(n, s, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{Replicas.Head{r, b, next, t}}:
      Adopt.ask.kept(n, s, Reading.Node.adoption(s, r, b))

# the adoption of a line keeps the logs
def Adopt.at.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain
) -> Spec.Node.Keeps(s, Reading.Adopt.at(n, s, c)):
  Adopt.head.kept(n, s, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the adoption of a line, if any, keeps the logs
def Adopt.maybe.kept(
  n: String,
  s: Replicas.Node<Basics.Ask>,
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
  +s: Replicas.Node<Basics.Ask>
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
  +s: Replicas.Node<Basics.Ask>
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
  +s: Replicas.Node<Basics.Ask>,
  +t: Ledgers.State(Basics.Ask)
) -> Spec.Node.Keeps(s, Reading.Node.sync(n, s, t)):
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
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> {Reading.Node.grows(s, Voting.Consent.at(n, s, i, m)) == True{}: Bool}:
  match m:
    case None{}:
      ProofTrees.Grows.refl(s)
    case Some{+c}:
      ProofTrees.Grows.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Voting.Node.step(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )(
        ProofTrees.Grows.to(
          s,
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          ProofTrees.Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          ProofTrees.Grows.refl(s)
        )
      )(
        ProofTrees.Step.grows(
          n,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          c
        )
      )

# a request that a writer asks again at a node keeps the logs
def Consent.kept(
  n: String,
  +s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  m: Maybe<&2, Ledgers.Chain>
) -> Spec.Node.Keeps(s, Voting.Consent.at(n, s, i, m)):
  match m:
    case None{}:
      Kept.refl(s)
    case Some{c}:
      Kept.trans(
        s,
        Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
        Voting.Node.step(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c),
        Kept.same(
          s,
          Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
          ProofTrees.Grows.to(
            s,
            s,
            Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            ProofTrees.Led.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)),
            ProofTrees.Grows.refl(s)
          ),
          Heads.keyed(s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i))
        ),
        Step.kept(n, Replicas.State.keyed(~Basics.Ask.machine(), s, Sealing.Keys.mark(Replicas.State.keys(~Basics.Ask.machine(), s), i)), c)
      )

# what a node does only grows it
def Does.grows(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  ev: Spec.Deed
) -> {Reading.Node.grows(s, Spec.Node.does(n, s, ev)) == True{}: Bool}:
  match ev:
    case Spec.Deed.Ask{+e, +q}:
      ProofTrees.Grows.trans(
        s,
        Voting.Node.ask(n, s, e, q),
        Reading.Adopt.at(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
      )(
        ProofTrees.Ask.grows(n, s, e, q)
      )(
        ProofTrees.Adopt.at.grows(
          n,
          Voting.Node.ask(n, s, e, q),
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
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
  +s: Replicas.Node<Basics.Ask>,
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
          Basics.Ask.chain(Replicas.Envelope.of(e), q)
        ),
        Ask.kept(n, s, e, q),
        Adopt.at.kept(n, Voting.Node.ask(n, s, e, q), Basics.Ask.chain(Replicas.Envelope.of(e), q))
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
            Replicas.State.ledger(~Basics.Ask.machine(), s)
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
