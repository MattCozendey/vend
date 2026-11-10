# bend-lint: expect-file bend-lint-rules/language/reused_binder@warning -- this file holds only proofs: a second use sits in a rewrite motive or an erased argument, and the checker accepts it
# bend-lint: expect-file bend-lint-rules/performance/eager_branch@information -- this file holds only proofs: a proof does not run
import Base
import ../../../shared.bend as Shared
import ../../shared/ledger.bend as Ledgers
import ../../shared/shared/shared/cell.bend as Cells
import ../../shared/shared/shared/hash.bend as Hashes
import ../../shared/shared/shared/trie.bend as Tries
import ../basics.bend as Basics
import ../judging.bend as Judging
import ../sealing.bend as Sealing
import ../spec.bend as Spec
import ../voting.bend as Voting
import ./rounds.bend as ProofRounds
import ./trees.bend as ProofTrees

# Waits
# -----
# A request that a node takes in waits on its line: a pending write goes with
# its writer to another node (Spec.Node.take_waits).

# a new ledger keeps the waiting requests
def Waiting.led(
  s: Basics.Node,
  l: Ledgers.State(Basics.Ask)
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Basics.State.led(s, l)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Basics.Node{old, hs, ws, ks}:
      {==}

# new keys keep the waiting requests
def Waiting.keyed(
  s: Basics.Node,
  ks: Basics.Keys
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Basics.State.keyed(s, ks)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Basics.Node{l, hs, ws, old}:
      {==}

# the waiting requests of the node m, if any, else of s
def Waiting.of(s: Basics.Node, m: Maybe<&2, Basics.Node>) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match m:
    case None{}:
      Basics.State.waiting(s)
    case Some{s2}:
      Basics.State.waiting(s2)

# a node that is kept when b holds has the waiting requests of s, when it has
def Waiting.some.if(
  b: Bool,
  -s: Basics.Node,
  -x: Basics.Node,
  hx: {Basics.State.waiting(s) == Basics.State.waiting(x): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {
  Basics.State.waiting(
    s
  )
    == Waiting.of(
      s,
      Shared.Maybe.when(Basics.Node, b, u => Some{x})
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match b:
    case True{}:
      hx
    case False{}:
      {==}

# a ballot that a node accepts keeps the waiting requests
def Accept.at.waiting(
  +s: Basics.Node,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Basics.Keychain>
) -> {
  Basics.State.waiting(
    s
  )
    == Waiting.of(s, Sealing.Seal.accept.at(s, b, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      Waiting.some.if(
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
          Tries.Trie<List<&2, Ledgers.Id>>,
          Basics.State.waiting(s),
          Basics.State.waiting(
            Basics.State.led(
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
            )
          ),
          Basics.State.waiting(
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
          Waiting.led(
            s,
            Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Basics.State.ledger(s), b)
          ),
          Waiting.keyed(
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

# the ballots that a chain leads to keep the waiting requests, when each one more does
def Follow.step.waiting(
  -s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  -k: Basics.Node -> Basics.Node,
  ih: @s2: Basics.Node -> {
    Basics.State.waiting(s2) == Basics.State.waiting(k(s2)): Tries.Trie<List<&2, Ledgers.Id>>
  }
) -> {
  Basics.State.waiting(s) == Waiting.of(s, m): Tries.Trie<List<&2, Ledgers.Id>>
} -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(
      Maybe.default(
        &2,
        Basics.Node,
        Maybe.bind(&2, Basics.Node, Basics.Node, m, s2 => Some{k(s2)}),
        s
      )
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      e => {==}
    case Some{s2}:
      e => Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Basics.State.waiting(s),
        Basics.State.waiting(s2),
        Basics.State.waiting(k(s2)),
        e,
        ih(s2)
      )

# the ballots that a chain leads to keep the waiting requests
def Follow.waiting(
  f: Nat,
  +s: Basics.Node,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(
      Sealing.Sealed.follow(f, s, p, r, n, mb)
    ): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match f mb:
    case 0n x:
      {==}
    case 1n+g None{}:
      {==}
    case 1n+(+g) Some{+b}:
      Follow.step.waiting(
        s,
        Sealing.Seal.accept(s, b),
        +s2 => Sealing.Sealed.follow(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n)),
        +s2 => Follow.waiting(g, s2, p, r, n, Sealing.Pending.next(s2, p, r, n))
      )(
        Accept.at.waiting(
          s,
          b,
          Sealing.Seal.chain(s, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        )
      )

# the ballots that the chains of some ballots lead to keep the waiting requests
def Each.waiting(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Basics.Node
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.Sealed.each(f, bs, p, s)): Tries.Trie<List<&2, Ledgers.Id>>
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
        Tries.Trie<List<&2, Ledgers.Id>>,
        Basics.State.waiting(s),
        Basics.State.waiting(s1),
        Basics.State.waiting(Sealing.Sealed.each(f, rest, p, s1)),
        Follow.waiting(
          f,
          s,
          p,
          Sealing.Ballot.store(b),
          Sealing.Ballot.node(b),
          Sealing.Pending.next(s, p, Sealing.Ballot.store(b), Sealing.Ballot.node(b))
        ),
        Each.waiting(f, rest, p, s1)
      )

# a new head keeps the waiting requests
def Waiting.head(
  +s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.State.head(s, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match s:
    case Basics.Node{l, hs, ws, ks}:
      {==}

# a first head keeps the waiting requests
def First.at.waiting(
  s: Basics.Node,
  c: Ledgers.Chain,
  h: Basics.Head,
  +m: Maybe<&2, Basics.Head>
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.First.at(s, c, h, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{Basics.Head{r, b, n, Some{t}}}:
      {==}
    case Some{Basics.Head{r, b, n, None{}}}:
      Waiting.head(s, c, h)
    case None{}:
      Waiting.head(s, c, h)

# the first head of a store keeps the waiting requests
def Start.head.waiting(
  +s: Basics.Node,
  m: Maybe<&2, Basics.Node>,
  +c: Ledgers.Chain,
  h: Basics.Head
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.Start.head(s, m, c, h)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{+s2}:
      Equal.trans(
        Tries.Trie<List<&2, Ledgers.Id>>,
        Basics.State.waiting(s),
        Basics.State.waiting(Basics.State.led(s, Basics.State.ledger(s2))),
        Basics.State.waiting(
          Sealing.State.first(Basics.State.led(s, Basics.State.ledger(s2)), c, h)
        ),
        Waiting.led(s, Basics.State.ledger(s2)),
        First.at.waiting(
          Basics.State.led(s, Basics.State.ledger(s2)),
          c,
          h,
          Basics.Node.head_of(Basics.State.led(s, Basics.State.ledger(s2)), c)
        )
      )

# a store that starts keeps the waiting requests, once its content m is known
def Start.with.waiting(
  s: Basics.Node,
  +i: Ledgers.Id,
  +os: List<&2, String>,
  +m: Maybe<&2, Judging.Work>
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.Start.with(s, i, os, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case None{}:
      {==}
    case Some{Judging.Work{s2, +c, ns}}:
      Start.head.waiting(
        s,
        Judging.State.put(s2, [Basics.Tip.words(Basics.Tip{c, None{}, 0, os})]),
        Ledgers.Chain{i, None{}},
        Basics.Head{i, None{}, 0, Some{Basics.Tip.hash(Basics.Tip{c, None{}, 0, os})}}
      )

# a line that a node starts to follow keeps the waiting requests
def Follow.new.waiting(
  s: Basics.Node,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  +m: Maybe<&2, Basics.Head>
) -> {
  Basics.State.waiting(
    s
  )
    == Basics.State.waiting(Sealing.Follow.new(s, r, l, m)): Tries.Trie<List<&2, Ledgers.Id>>
}:
  match m:
    case Some{h}:
      {==}
    case None{}:
      Waiting.head(s, Basics.Line.chain(r, l), Basics.Head{r, l, 0, None{}})

# nodes with the same waiting requests have the same ones on each line
def Wait.same(
  a: Basics.Node,
  b: Basics.Node,
  c: Ledgers.Chain,
  e: {Basics.State.waiting(a) == Basics.State.waiting(b): Tries.Trie<List<&2, Ledgers.Id>>}
) -> {Sealing.Wait.of(a, c) == Sealing.Wait.of(b, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    Tries.Trie<List<&2, Ledgers.Id>>,
    List<&2, Ledgers.Id>,
    ws => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c)),
      []
    ),
    Basics.State.waiting(a),
    Basics.State.waiting(b),
    e
  )

# lines with the same key have the same waiting requests
def Wait.keyed(
  s: Basics.Node,
  c2: Ledgers.Chain,
  c: Ledgers.Chain,
  ek: {Ledgers.Chain.key(c2) == Ledgers.Chain.key(c): List<&2, Bool>}
) -> {Sealing.Wait.of(s, c2) == Sealing.Wait.of(s, c): List<&2, Ledgers.Id>}:
  Equal.cong(
    List<&2, Bool>,
    List<&2, Ledgers.Id>,
    kk => Maybe.default(
      &2,
      List<&2, Ledgers.Id>,
      Tries.Trie.get(List<&2, Ledgers.Id>, Basics.State.waiting(s), kk),
      []
    ),
    Ledgers.Chain.key(c2),
    Ledgers.Chain.key(c),
    ek
  )

# the default of a pick is the pick of the defaults
def Wait.pick(
  +b: Bool,
  v: List<&2, Ledgers.Id>,
  m: Maybe<&2, List<&2, Ledgers.Id>>
) -> {
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Bool.pick(Maybe<&2, List<&2, Ledgers.Id>>, b, Some{v}, m),
    []
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      v,
      Maybe.default(&2, List<&2, Ledgers.Id>, m, [])
    ): List<&2, Ledgers.Id>
}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the requests that wait on a line, after some requests wait on the line c
def Wait.set.of(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +x: Ledgers.Id,
  +r: List<&2, Ledgers.Id>,
  +c2: Ledgers.Chain
) -> {
  Sealing.Wait.of(
    Sealing.Wait.set(s, c, x <> r),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      x <> r,
      Sealing.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  match s:
    case Basics.Node{l, hs, +ws, ks}:
      %Equal.sym(
        Maybe<&2, List<&2, Ledgers.Id>>,
        Tries.Trie.get(
          List<&2, Ledgers.Id>,
          Tries.Trie.set(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c), x <> r),
          Ledgers.Chain.key(c2)
        ),
        Bool.pick(
          Maybe<&2, List<&2, Ledgers.Id>>,
          Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
          Some{x <> r},
          Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
        ),
        Tries.Trie.get_set(
          List<&2, Ledgers.Id>,
          ws,
          Ledgers.Chain.key(c),
          x <> r,
          Ledgers.Chain.key(c2)
        )
      ): {
        Maybe.default(
          &2,
          List<&2, Ledgers.Id>,
          _,
          []
        )
          == Bool.pick(
            List<&2, Ledgers.Id>,
            Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
            x <> r,
            Maybe.default(
              &2,
              List<&2, Ledgers.Id>,
              Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2)),
              []
            )
          ): List<&2, Ledgers.Id>
      }
      Wait.pick(
        Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
        x <> r,
        Tries.Trie.get(List<&2, Ledgers.Id>, ws, Ledgers.Chain.key(c2))
      )

# Wait.wait for any requests ys that waited on the line c
def Wait.wait.at(
  s: Basics.Node,
  c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain,
  +ys: List<&2, Ledgers.Id>
) -> {
  Sealing.Wait.of(
    Sealing.Wait.set(s, c, List.append(&2, Ledgers.Id, ys, [j])),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, ys, [j]),
      Sealing.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  match ys:
    case Nil{}:
      Wait.set.of(s, c, j, [], c2)
    case Con{x, r}:
      Wait.set.of(s, c, x, List.append(&2, Ledgers.Id, r, [j]), c2)

# the requests that wait on a line, after one more waits on the line c
def Wait.wait(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  c2: Ledgers.Chain
) -> {
  Sealing.Wait.of(
    Sealing.State.wait(s, c, j),
    c2
  )
    == Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Sealing.Wait.of(s, c), [j]),
      Sealing.Wait.of(s, c2)
    ): List<&2, Ledgers.Id>
}:
  Wait.wait.at(s, c, j, c2, Sealing.Wait.of(s, c))

# Wait.keeps once it is known whether the line has the key of c (b)
def Wait.keeps.if(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  +b: Bool,
  eb: {Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)) == b: Bool},
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Bool.pick(
      List<&2, Ledgers.Id>,
      b,
      List.append(&2, Ledgers.Id, Sealing.Wait.of(s, c), [j]),
      Sealing.Wait.of(s, c2)
    ),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      Shared.List.contains_left(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(s, c), [j], i, (
          %Wait.keyed(s, c2, c, ProofRounds.Key.same(c2, c)(eb)): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))
    case False{}:
      h

# a request that waits on a line waits there after one more waits on a line
def Wait.keeps(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +j: Ledgers.Id,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(Sealing.State.wait(s, c, j), c2),
    i
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Sealing.Wait.of(Sealing.State.wait(s, c, j), c2),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Sealing.Wait.of(s, c), [j]),
      Sealing.Wait.of(s, c2)
    ),
    Wait.wait(s, c, j, c2)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
  Wait.keeps.if(
    s,
    c,
    j,
    c2,
    i,
    Tries.Trie.same_key(Ledgers.Chain.key(c2), Ledgers.Chain.key(c)),
    {==},
    h
  )

# a list of one is a member of itself
def Contains.one(
  j: Ledgers.Id
) -> {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [j], j) == True{}: Bool}:
  %Equal.sym(
    Bool,
    Ledgers.Id.is_eq(j, j),
    True{},
    Ledgers.Id.is_eq_refl(j)
  ): {List.any.if(u => List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, [], j), _) == True{}: Bool}
  {==}

# a request waits on its line once it waits there
def Wait.adds(
  +s: Basics.Node,
  +c: Ledgers.Chain,
  +j: Ledgers.Id
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(Sealing.State.wait(s, c, j), c),
    j
  )
    == True{}: Bool
}:
  %Equal.sym(
    List<&2, Ledgers.Id>,
    Sealing.Wait.of(Sealing.State.wait(s, c, j), c),
    Bool.pick(
      List<&2, Ledgers.Id>,
      Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
      List.append(&2, Ledgers.Id, Sealing.Wait.of(s, c), [j]),
      Sealing.Wait.of(s, c)
    ),
    Wait.wait(s, c, j, c)
  ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, j) == True{}: Bool}
  %Equal.sym(
    Bool,
    Tries.Trie.same_key(Ledgers.Chain.key(c), Ledgers.Chain.key(c)),
    True{},
    Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Ledgers.Chain.key(c))
  ): {
    List.contains(
      ~Ledgers.Id,
      ~Ledgers.Id.is_eq,
      Bool.pick(
        List<&2, Ledgers.Id>,
        _,
        List.append(&2, Ledgers.Id, Sealing.Wait.of(s, c), [j]),
        Sealing.Wait.of(s, c)
      ),
      j
    )
      == True{}: Bool
  }
  Shared.List.contains_right(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(s, c),
    [j],
    j,
    Contains.one(j)
  )

# a request that waits on a line waits there after a request arrives
def Arrive.waits(
  +s: Basics.Node,
  +j: Ledgers.Id,
  +q: Basics.Ask,
  +c2: Ledgers.Chain,
  i: Ledgers.Id,
  h: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(s, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(Sealing.Node.arrive(s, j, q), c2),
    i
  )
    == True{}: Bool
}:
  match q:
    case Basics.Ask.Start{os}:
      %Wait.same(
        s,
        Sealing.Node.start(s, j, os),
        c2,
        Start.with.waiting(
          s,
          j,
          Basics.Owner.names(os),
          Sealing.Seal.firsts(os, Some{Judging.Work{s, None{}, []}})
        )
      ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
      h
    case Basics.Ask.On{r, l, ch}:
      Wait.keeps(Sealing.Node.follow(s, r, l), Basics.Line.chain(r, l), j, c2, i, (
          %Wait.same(s, Sealing.Node.follow(s, r, l), c2, Follow.new.waiting(s, r, l, Basics.Node.head_of(s, Basics.Line.chain(r, l)))): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
          h))

# one of two nodes, on each of which the request i waits on the line c2
def Contains.when(
  +b: Bool,
  -x: Basics.Node,
  -y: Basics.Node,
  -c2: Ledgers.Chain,
  -i: Ledgers.Id,
  hx: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(x, c2), i) == True{}: Bool},
  hy: {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(y, c2), i) == True{}: Bool}
) -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(Shared.Bool.when(Basics.Node, b, u => x, u => y), c2),
    i
  )
    == True{}: Bool
}:
  match b:
    case True{}:
      hx
    case False{}:
      hy

# a request that waits on a line waits there after more requests arrive
def Take.asks.waits(
  +cs: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Basics.Node,
  +c2: Ledgers.Chain,
  +i: Ledgers.Id
) -> {
  List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(s, c2), i) == True{}: Bool
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(Voting.Take.asks(cs, old, s), c2),
    i
  )
    == True{}: Bool
}:
  match cs:
    case Nil{}:
      h => h
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      +h => Take.asks.waits(
        rest,
        old,
        Shared.Bool.when(
          Basics.Node,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Sealing.Node.arrive(s, j, q),
          u => s
        ),
        c2,
        i
      )(
        Contains.when(
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          Sealing.Node.arrive(s, j, q),
          s,
          c2,
          i,
          Arrive.waits(s, j, q, c2, i, h),
          h
        )
      )
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.waits(rest, old, s, c2, i)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.waits(rest, old, s, c2, i)
    case Con{Cells.Many{}, rest}:
      Take.asks.waits(rest, old, s, c2, i)

# a new request among the cells that a node takes in waits on its line
def Take.asks.adds(
  +pre: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  post: List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
  +old: Ledgers.State(Basics.Ask),
  +s: Basics.Node,
  +i: Ledgers.Id,
  time: String,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  ch: Basics.Change
) -> {
  Ledgers.State.get(
    ~Basics.Ask,
    old,
    Ledgers.Slot.ask(i)
  )
    == None{}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>
} -> {
  List.contains(
    ~Ledgers.Id,
    ~Ledgers.Id.is_eq,
    Sealing.Wait.of(
      Voting.Take.asks(
        List.append(
          &2,
          Cells.Cell<Ledgers.Entry<Basics.Ask>>,
          pre,
          Cells.One{Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}} <> post
        ),
        old,
        s
      ),
      Basics.Line.chain(r, l)
    ),
    i
  )
    == True{}: Bool
}:
  match pre:
    case Nil{}:
      e => Take.asks.waits(
        post,
        old,
        Shared.Bool.when(
          Basics.Node,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i))
          ),
          u => Sealing.Node.arrive(s, i, Basics.Ask.On{r, l, ch}),
          u => s
        ),
        Basics.Line.chain(r, l),
        i
      )(
        %Equal.sym(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(i)), None{}, e): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, Sealing.Wait.of(Shared.Bool.when(Basics.Node, Maybe.is_none(&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>, _), u => Sealing.Node.arrive(s, i, Basics.Ask.On{r, l, ch}), u => s), Basics.Line.chain(r, l)), i) == True{}: Bool}
        Wait.adds(Sealing.Node.follow(s, r, l), Basics.Line.chain(r, l), i))
    case Con{Cells.One{Ledgers.Entry.Ask{j, t, q}}, rest}:
      e => Take.asks.adds(
        rest,
        post,
        old,
        Shared.Bool.when(
          Basics.Node,
          Maybe.is_none(
            &2,
            Cells.Cell<Ledgers.Entry<Basics.Ask>>,
            Ledgers.State.get(~Basics.Ask, old, Ledgers.Slot.ask(j))
          ),
          u => Sealing.Node.arrive(s, j, q),
          u => s
        ),
        i,
        time,
        r,
        l,
        ch
      )(e)
    case Con{Cells.One{Ledgers.Entry.Vote{v}}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)
    case Con{Cells.One{Ledgers.Entry.Data{d}}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)
    case Con{Cells.Many{}, rest}:
      Take.asks.adds(rest, post, old, s, i, time, r, l, ch)

def Spec.Node.take_holds(s, t, k, e):
  +sent = Voting.Node.reads(t)
  +l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent)
  es => eb =>
    Ledgers.State.one_grows(
      ~Basics.Ask,
      ~Basics.Ask.is_eq,
      ~ProofTrees.Ask.laws(),
      Basics.State.ledger(Basics.State.led(s, l1)),
      Basics.State.ledger(Voting.Node.take(s, t)),
      k,
      e
    )(ProofTrees.Take.tail(s, t))(
      %Equal.sym(Ledgers.State(Basics.Ask), Basics.State.ledger(Basics.State.led(s, l1)), l1, ProofTrees.Led.led(s, l1)): {Ledgers.State.get(~Basics.Ask, _, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>}
      Equal.trans(Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>, Ledgers.State.get(~Basics.Ask, l1, k), Ledgers.State.get(~Basics.Ask, sent, k), Some{Cells.One{e}}, Ledgers.State.take_get(~Basics.Ask, Basics.State.ledger(s), sent, k)(eb), es))

def Spec.Node.take_waits(s, t, i, time, r, l, ch):
  +sent = Voting.Node.reads(t)
  l1 = Ledgers.State.take(~Basics.Ask, Basics.State.ledger(s), sent)
  +s1 = Basics.State.led(s, l1)
  cs = Tries.Trie.values(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent)
  +s2 = Voting.Take.asks(cs, Basics.State.ledger(s), s1)
  +bs = Voting.Ballots.of(
    Tries.Trie.values(
      Cells.Cell<Ledgers.Entry<Basics.Ask>>,
      Ledgers.State.missing(~Basics.Ask, ~Basics.Ask.is_eq, t, Basics.State.ledger(s))
    )
  )
  cell = {
    Cells.One{
      Ledgers.Entry.Ask{i, time, Basics.Ask.On{r, l, ch}}
    }: Cells.Cell<Ledgers.Entry<Basics.Ask>>
  }
  es => eb =>
    %Wait.same(
      s2,
      Sealing.Sealed.take(bs, s2),
      Basics.Line.chain(r, l),
      Each.waiting(List.length(&2, Ledgers.Ballot, bs), bs, Sealing.Pending.of(bs), s2)
    ): {List.contains(~Ledgers.Id, ~Ledgers.Id.is_eq, _, i) == True{}: Bool}
    %Equal.sym(
      List<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>,
      cs,
      List.append(
        &2,
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        Tries.Trie.before(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
        cell <> Tries.Trie.after(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i))
      ),
      Tries.Trie.values_around(
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        sent,
        Ledgers.Slot.ask(i),
        cell
      )(es)
    ): {
      List.contains(
        ~Ledgers.Id,
        ~Ledgers.Id.is_eq,
        Sealing.Wait.of(Voting.Take.asks(_, Basics.State.ledger(s), s1), Basics.Line.chain(r, l)),
        i
      )
        == True{}: Bool
    }
    Take.asks.adds(
      Tries.Trie.before(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
      Tries.Trie.after(Cells.Cell<Ledgers.Entry<Basics.Ask>>, sent, Ledgers.Slot.ask(i)),
      Basics.State.ledger(s),
      s1,
      i,
      time,
      r,
      l,
      ch
    )(eb)
