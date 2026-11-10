import Base
import ../../shared.bend as Shared
import ../shared/ledger.bend as Ledgers
import ../shared/shared/shared/cell.bend as Cells
import ../shared/shared/shared/code.bend as Codes
import ../shared/shared/shared/hash.bend as Hashes
import ../shared/shared/shared/seal.bend as Seals
import ../shared/shared/shared/trie.bend as Tries
import ./basics.bend as Basics
import ./judging.bend as Judging
import ./stepping.bend as Stepping
import ../replica/impl.bend as Replicas

# The node
# --------
# A node takes in requests and what other nodes send, casts its ballot for the
# next step of each line that it owns, and moves each head along the steps
# that are decided.

# Seals
# -----
# A node signs each ballot. Its ballots in one store are a chain: each names
# the place of the one before it and the key of the next one, so a key signs
# once (Seals). The store gives a node the first key of its chain (a first
# owner's in the request that starts the store, then by a Key change). A node
# keeps a ballot only when it is the next of its chain and the key of the
# chain signs it, so a ledger holds no ballot that its node did not check.

# the place of the ballot b
def Ballot.at(b: Ledgers.Ballot) -> Ledgers.Where:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      w

# the node of the ballot b
def Ballot.node(b: Ledgers.Ballot) -> String:
  match b:
    case Ledgers.Ballot{Ledgers.Signed{w, n, a}, l}:
      n

# the place of the ballot before b in its chain
def Ballot.prev(b: Ledgers.Ballot) -> Maybe<&2, Ledgers.Where>:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      p

# the key of the ballot after b in its chain
def Ballot.next(b: Ledgers.Ballot) -> Hashes.Hash:
  match b:
    case Ledgers.Ballot{x, Ledgers.Link{p, k, z}}:
      k

# the store of the place w
def Where.store(w: Ledgers.Where) -> Ledgers.Id:
  match w:
    case Ledgers.Where{Ledgers.Chain{r, k}, h, z}:
      r

# the line of the place w
def Where.line(w: Ledgers.Where) -> Ledgers.Chain:
  match w:
    case Ledgers.Where{c, h, z}:
      c

# the store of the ballot b
def Ballot.store(b: Ledgers.Ballot) -> Ledgers.Id:
  Where.store(Ballot.at(b))

# the key of the chain of the node n in the store r
def Seal.slot(r: Ledgers.Id, n: String) -> List<&2, Bool>:
  List.append(&2, Bool, Ledgers.Id.key(r), Tries.Trie.text(n))

# a and b are the same place, or both none
def Prev.same(a: Maybe<&2, Ledgers.Where>, b: Maybe<&2, Ledgers.Where>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      Codes.Code.is_eq(~Ledgers.Where, ~Ledgers.Where.code, x, y)
    case x y:
      False{}

# the key in the value m, if any
def Seal.read(m: Maybe<&2, List<&2, U32>>) -> Maybe<&2, Hashes.Hash>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    Hashes.Hash,
    m,
    ws => Replicas.Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
  )

# the first key that the store r gave the node n, as s knows the store
def Seal.first(+s: Replicas.Node<Basics.Ask>, r: Ledgers.Id, n: String) -> Maybe<&2, Hashes.Hash>:
  Seal.read(
    Replicas.Node.get(~Basics.Ask.machine(), 
      s,
      Maybe.bind(
        &2,
        Replicas.Tip,
        Hashes.Hash,
        Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}),
        t => Replicas.Tip.content(t)
      ),
      Replicas.Kernel.seal(Stepping.Ask.kernel())(n)
    )
  )

# the chain c, when it starts from the first key m; else a new chain from m
# (none: the store gave the node no key)
def Keychain.from(
  m: Maybe<&2, Hashes.Hash>,
  c: Maybe<&2, Replicas.Keychain>
) -> Maybe<&2, Replicas.Keychain>:
  match m c:
    case None{} y:
      None{}
    case Some{k} None{}:
      Some{Replicas.Keychain{0, None{}, k, k}}
    case Some{+k} Some{Replicas.Keychain{n, l, x, +f}}:
      Some{
        Shared.Bool.when(
          Replicas.Keychain,
          Hashes.Hash.is_eq(f, k),
          u => Replicas.Keychain{n, l, x, f},
          u => Replicas.Keychain{0, None{}, k, k}
        )
      }

# the chains of the keys ks
def Keys.chains(ks: Replicas.Keys) -> Tries.Trie<Replicas.Keychain>:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      cs

# the secret seed of the keys ks
def Keys.seed(ks: Replicas.Keys) -> Hashes.Hash:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      seed

# ks, with the request i asked at this node
def Keys.mark(ks: Replicas.Keys, i: Ledgers.Id) -> Replicas.Keys:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      Replicas.Keys{seed, cs, Tries.Trie.set(Unit, as, Ledgers.Id.key(i), Unit{}), rs}

# the request i was asked at this node
def Keys.asked(ks: Replicas.Keys, i: Ledgers.Id) -> Bool:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      Tries.Trie.has(Unit, as, Ledgers.Id.key(i))

# ks with the chain c at the key k
def Keys.set(ks: Replicas.Keys, k: List<&2, Bool>, c: Replicas.Keychain) -> Replicas.Keys:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      Replicas.Keys{seed, Tries.Trie.set(Replicas.Keychain, cs, k, c), as, rs}

# the highest round, in the rounds rs, of the height h of the line c (0: the
# first round)
def Rounds.at(rs: Tries.Trie<Nat>, c: Ledgers.Chain, h: U32) -> Nat:
  Maybe.default(&2, Nat, Tries.Trie.get(Nat, rs, Ledgers.Slot.height(c, h)), 0n)

# the rounds of the keys ks
def Keys.rounds(ks: Replicas.Keys) -> Tries.Trie<Nat>:
  match ks:
    case Replicas.Keys{seed, cs, as, rs}:
      rs

# ks, which saw a ballot at the place w: the highest round of its height
def Keys.saw(ks: Replicas.Keys, w: Ledgers.Where) -> Replicas.Keys:
  match ks w:
    case Replicas.Keys{seed, cs, as, +rs} Ledgers.Where{+c, +h, +r}:
      Replicas.Keys{
        seed,
        cs,
        as,
        Shared.Bool.when(
          Tries.Trie<Nat>,
          Nat.is_lt(Rounds.at(rs, c, h), r),
          u => Tries.Trie.set(Nat, rs, Ledgers.Slot.height(c, h), r),
          u => rs
        )
      }

# the highest round of the height h of the line c of which s holds a ballot
def Round.seen(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h: U32) -> Nat:
  Rounds.at(Keys.rounds(Replicas.State.keys(~Basics.Ask.machine(), s)), c, h)

# the chain of the node n in the store r, as s knows it
def Seal.chain(+s: Replicas.Node<Basics.Ask>, +r: Ledgers.Id, +n: String) -> Maybe<&2, Replicas.Keychain>:
  Keychain.from(
    Seal.first(s, r, n),
    Tries.Trie.get(Replicas.Keychain, Keys.chains(Replicas.State.keys(~Basics.Ask.machine(), s)), Seal.slot(r, n))
  )

# the ballot b is the next of the chain c, and the key of c signs it
def Seal.fits(c: Replicas.Keychain, +b: Ledgers.Ballot) -> Bool:
  match c:
    case Replicas.Keychain{n, last, key, f}:
      List.all.if(u => Ledgers.Ballot.sealed(key, b), Prev.same(Ballot.prev(b), last))

# the chain c after its next ballot b
def Keychain.next(c: Replicas.Keychain, +b: Ledgers.Ballot) -> Replicas.Keychain:
  match c:
    case Replicas.Keychain{n, last, key, f}:
      Replicas.Keychain{U32.inc(n), Some{Ballot.at(b)}, Ballot.next(b), f}

# Seal.accept once the chain m of the ballot's node is known
def Seal.accept.at(
  +s: Replicas.Node<Basics.Ask>,
  +b: Ledgers.Ballot,
  m: Maybe<&2, Replicas.Keychain>
) -> Maybe<&2, Replicas.Node<Basics.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{+c}:
      Shared.Maybe.when(
        Replicas.Node<Basics.Ask>,
        Seal.fits(c, b),
        u => Some{
          Replicas.State.keyed(~Basics.Ask.machine(), 
            Replicas.State.led(~Basics.Ask.machine(), 
              s,
              Ledgers.State.keep(~Basics.Ask, ~Basics.Ask.is_eq, Replicas.State.ledger(~Basics.Ask.machine(), s), b)
            ),
            Keys.saw(
              Keys.set(
                Replicas.State.keys(~Basics.Ask.machine(), s),
                Seal.slot(Ballot.store(b), Ballot.node(b)),
                Keychain.next(c, b)
              ),
              Ballot.at(b)
            )
          )
        }
      )

# s with the ballot b, when it is the next of its node's chain in its store
# and the key of the chain signs it (none: not now)
def Seal.accept(+s: Replicas.Node<Basics.Ask>, +b: Ledgers.Ballot) -> Maybe<&2, Replicas.Node<Basics.Ask>>:
  Seal.accept.at(s, b, Seal.chain(s, Ballot.store(b), Ballot.node(b)))

# the secret of the ballot of the number j of a node in the store r, from the
# node's seed
def Seal.secret(seed: Hashes.Hash, r: Ledgers.Id, j: U32) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, Ledgers.Id.code(r, [j])))

# the key of the place m, if any
def Prev.key(m: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  match m:
    case None{}:
      [False{}]
    case Some{w}:
      True{} <> Ledgers.Slot.vote(w, "")

# the key of where the ballot after the one at last waits, for the node n in
# the store r
def Seal.link(r: Ledgers.Id, n: String, last: Maybe<&2, Ledgers.Where>) -> List<&2, Bool>:
  List.append(&2, Bool, Seal.slot(r, n), Prev.key(last))

# the ballots bs, each at the key of where it waits in its chain
def Pending.of(bs: List<&2, Ledgers.Ballot>) -> Tries.Trie<Ledgers.Ballot>:
  match bs:
    case Nil{}:
      Tries.Trie.new(Ledgers.Ballot)
    case Con{+b, r}:
      Tries.Trie.set(
        Ledgers.Ballot,
        Pending.of(r),
        Seal.link(Ballot.store(b), Ballot.node(b), Ballot.prev(b)),
        b
      )

# the last place of the chain c
def Keychain.last(c: Replicas.Keychain) -> Maybe<&2, Ledgers.Where>:
  match c:
    case Replicas.Keychain{n, last, key, f}:
      last

# the ballot of p that is the next of the chain of the node n in the store r
def Pending.next(
  s: Replicas.Node<Basics.Ask>,
  p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String
) -> Maybe<&2, Ledgers.Ballot>:
  Maybe.bind(
    &2,
    Replicas.Keychain,
    Ledgers.Ballot,
    Seal.chain(s, r, n),
    c => Tries.Trie.get(Ledgers.Ballot, p, Seal.link(r, n, Keychain.last(c)))
  )

# s with each ballot of p that the chain of the node n in the store r leads
# to, from the ballot mb, f ballots at most
def Sealed.follow(
  f: Nat,
  +s: Replicas.Node<Basics.Ask>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +r: Ledgers.Id,
  +n: String,
  mb: Maybe<&2, Ledgers.Ballot>
) -> Replicas.Node<Basics.Ask>:
  match f mb:
    case 1n+g Some{b}:
      Maybe.default(
        &2,
        Replicas.Node<Basics.Ask>,
        Maybe.bind(
          &2,
          Replicas.Node<Basics.Ask>,
          Replicas.Node<Basics.Ask>,
          Seal.accept(s, b),
          +s2 => Some{Sealed.follow(g, s2, p, r, n, Pending.next(s2, p, r, n))}
        ),
        s
      )
    case x y:
      s

# s with the ballots of p that the chains of the ballots bs lead to
def Sealed.each(
  +f: Nat,
  bs: List<&2, Ledgers.Ballot>,
  +p: Tries.Trie<Ledgers.Ballot>,
  +s: Replicas.Node<Basics.Ask>
) -> Replicas.Node<Basics.Ask>:
  match bs:
    case Nil{}:
      s
    case Con{+b, rest}:
      Sealed.each(
        f,
        rest,
        p,
        Sealed.follow(
          f,
          s,
          p,
          Ballot.store(b),
          Ballot.node(b),
          Pending.next(s, p, Ballot.store(b), Ballot.node(b))
        )
      )

# s with each ballot of bs that its node's chain leads to and its key signs:
# the cost is about that of the ballots, in any order
def Sealed.take(+bs: List<&2, Ledgers.Ballot>, s: Replicas.Node<Basics.Ask>) -> Replicas.Node<Basics.Ask>:
  Sealed.each(List.length(&2, Ledgers.Ballot, bs), bs, Pending.of(bs), s)

# the height of the next step of the head h
def Head.next(h: Replicas.Head) -> U32:
  match h:
    case Replicas.Head{r, b, n, t}:
      n

# s with the head h of the line c
def State.head(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, h: Replicas.Head) -> Replicas.Node<Basics.Ask>:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      Replicas.Node{l, Tries.Trie.set(Replicas.Head, hs, Ledgers.Chain.key(c), h), ws, ks}

# the requests of the line c that wait for a step, in the order that the node
# took them in
def Wait.of(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain) -> List<&2, Ledgers.Id>:
  Maybe.default(
    &2,
    List<&2, Ledgers.Id>,
    Tries.Trie.get(List<&2, Ledgers.Id>, Replicas.State.waiting(~Basics.Ask.machine(), s), Ledgers.Chain.key(c)),
    []
  )

# ws with the requests qs waiting at the key k: a line with no waiting request
# has no entry, so the lines that wait are read without a walk of every line
def Wait.put(
  ws: Tries.Trie<List<&2, Ledgers.Id>>,
  k: List<&2, Bool>,
  qs: List<&2, Ledgers.Id>
) -> Tries.Trie<List<&2, Ledgers.Id>>:
  match qs:
    case Nil{}:
      Tries.Trie.drop(List<&2, Ledgers.Id>, ws, k)
    case Con{i, r}:
      Tries.Trie.set(List<&2, Ledgers.Id>, ws, k, Con{i, r})

# s with the requests qs waiting on the line c
def Wait.set(s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, qs: List<&2, Ledgers.Id>) -> Replicas.Node<Basics.Ask>:
  match s:
    case Replicas.Node{l, hs, ws, ks}:
      Replicas.Node{l, hs, Wait.put(ws, Ledgers.Chain.key(c), qs), ks}

# s with the request i waiting on the line c, after those that wait
def State.wait(+s: Replicas.Node<Basics.Ask>, +c: Ledgers.Chain, i: Ledgers.Id) -> Replicas.Node<Basics.Ask>:
  Wait.set(s, c, List.append(&2, Ledgers.Id, Wait.of(s, c), [i]))

# the requests of qs whose keys done does not hold
def Wait.left(qs: List<&2, Ledgers.Id>, +done: Tries.Trie<Unit>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(
        Ledgers.Id,
        i,
        Wait.left(r, done),
        Bool.not(Tries.Trie.has(Unit, done, Ledgers.Id.key(i)))
      )

# s at the head h of the line c, after a step that ran the requests qs: they
# wait no more
def State.moved(
  +s: Replicas.Node<Basics.Ask>,
  +c: Ledgers.Chain,
  h: Replicas.Head,
  qs: List<&2, Ledgers.Id>
) -> Replicas.Node<Basics.Ask>:
  State.head(
    Wait.set(
      s,
      c,
      Wait.left(
        Wait.of(s, c),
        Tries.Trie.put_keys(~Ledgers.Id, ~Ledgers.Id.key, qs, Tries.Trie.new(Unit))
      )
    ),
    c,
    h
  )

# State.first once the head m of the line is known
def First.at(
  s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  h: Replicas.Head,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node<Basics.Ask>:
  match m:
    case Some{Replicas.Head{r, b, n, Some{t}}}:
      s
    case x:
      State.head(s, c, h)

# s with the first head h of the line c, when the line has no tip: a line
# that has a tip moves only by a step
def State.first(+s: Replicas.Node<Basics.Ask>, +c: Ledgers.Chain, h: Replicas.Head) -> Replicas.Node<Basics.Ask>:
  First.at(s, c, h, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# the state m with the first head h of the line c, else s
def Start.head(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  c: Ledgers.Chain,
  h: Replicas.Head
) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{s2}:
      State.first(Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s2)), c, h)

# w with the first key of each first owner of os
def Seal.firsts(os: List<&2, Replicas.Owner>, m: Maybe<&2, Replicas.Work<Basics.Ask>>) -> Maybe<&2, Replicas.Work<Basics.Ask>>:
  match os:
    case Nil{}:
      m
    case Con{Replicas.Owner{n, k}, r}:
      Seal.firsts(
        r,
        Maybe.bind(
          &2,
          Replicas.Work<Basics.Ask>,
          Replicas.Work<Basics.Ask>,
          m,
          w => Replicas.Work.set(~Basics.Ask.machine(), w, Replicas.Kernel.seal(Stepping.Ask.kernel())(n), Hashes.Hash.code(k, []))
        )
      )

# Node.start once the content m of the store is known: its first tip has no
# log and no version, and its owners are the first owners os
def Start.with(
  s: Replicas.Node<Basics.Ask>,
  +i: Ledgers.Id,
  os: List<&2, String>,
  m: Maybe<&2, Replicas.Work<Basics.Ask>>
) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{Replicas.Work{s2, c}}:
      +t = {Replicas.Tip{c, None{}, 0, os}: Replicas.Tip}
      Start.head(
        s,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t)]),
        Ledgers.Chain{i, None{}},
        Replicas.Head{i, None{}, 0, Some{Replicas.Tip.hash(t)}}
      )

# s, which follows the store that the request i starts with the first owners
# os: its content holds their first keys
def Node.start(+s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, +os: List<&2, Replicas.Owner>) -> Replicas.Node<Basics.Ask>:
  Start.with(s, i, Replicas.Owner.names(os), Seal.firsts(os, Some{Replicas.Work{s, None{}}}))

# the first tip of the branch b of a store whose tip is m, if the store made
# b: the log of the store holds it, written once, so every node opens the
# branch at the same tip (Chain.start_final)
def Branch.first(s: Replicas.Node<Basics.Ask>, b: String, m: Maybe<&2, Replicas.Tip>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{t}:
      Maybe.bind(
        &2,
        List<&2, U32>,
        Hashes.Hash,
        Replicas.Node.get(~Basics.Ask.machine(), s, Replicas.Tip.log(t), Replicas.Log.start(b)),
        ws => Replicas.Read.whole(Hashes.Hash, Hashes.Hash.code.read(ws))
      )

# Node.open once the head m of the line is known
def Open.at(+s: Replicas.Node<Basics.Ask>, c: Ledgers.Chain, m: Maybe<&2, Replicas.Head>) -> Replicas.Node<Basics.Ask>:
  match m:
    case Some{Replicas.Head{+r, Some{+b}, n, None{}}}:
      State.head(
        s,
        c,
        Replicas.Head{r, Some{b}, 0, Branch.first(s, b, Replicas.Node.tip(~Basics.Ask.machine(), s, Ledgers.Chain{r, None{}}))}
      )
    case x:
      s

# s, which follows the line c: a branch that the node waits for opens at its
# first tip, once the store that the node follows made it
def Node.open(+s: Replicas.Node<Basics.Ask>, +c: Ledgers.Chain) -> Replicas.Node<Basics.Ask>:
  Open.at(s, c, Replicas.Node.head_of(~Basics.Ask.machine(), s, c))

# s, which follows the line l of the store r, when the head m says that it
# does not yet
def Follow.new(
  s: Replicas.Node<Basics.Ask>,
  +r: Ledgers.Id,
  +l: Maybe<&2, String>,
  m: Maybe<&2, Replicas.Head>
) -> Replicas.Node<Basics.Ask>:
  match m:
    case Some{h}:
      s
    case None{}:
      State.head(s, Replicas.Line.chain(r, l), Replicas.Head{r, l, 0, None{}})

# s, which follows the line l of the store r
def Node.follow(+s: Replicas.Node<Basics.Ask>, +r: Ledgers.Id, +l: Maybe<&2, String>) -> Replicas.Node<Basics.Ask>:
  Follow.new(s, r, l, Replicas.Node.head_of(~Basics.Ask.machine(), s, Replicas.Line.chain(r, l)))

# s, once it holds the new request i, which arrives as a: a store starts, or
# the request waits on its line
def Arrive.at(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, a: Replicas.Arrival) -> Replicas.Node<Basics.Ask>:
  match a:
    case Replicas.Arrival.Starts{os}:
      Node.start(s, i, os)
    case Replicas.Arrival.Waits{+r, +l}:
      State.wait(Node.follow(s, r, l), Replicas.Line.chain(r, l), i)

# s, once it holds the new request i of the change q
def Node.arrive(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, q: Basics.Ask) -> Replicas.Node<Basics.Ask>:
  Arrive.at(s, i, Replicas.Kernel.arrival(Stepping.Ask.kernel())(q))

# a and b are the same root
def Root.same(a: Maybe<&2, Hashes.Hash>, b: Maybe<&2, Hashes.Hash>) -> Bool:
  Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, a, b)

# the node n may cast a ballot at the place w of a line at the tip t, for the
# requests qs: there is a request, n is an owner, and n cast none there
def Cast.may(
  +n: String,
  +s: Replicas.Node<Basics.Ask>,
  w: Ledgers.Where,
  t: Replicas.Tip,
  qs: List<&2, Ledgers.Id>
) -> Bool:
  List.all.if(
    u => List.all.if(
      v => Maybe.is_none(
        &2,
        Cells.Cell<Ledgers.Entry<Basics.Ask>>,
        Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.vote(w, n))
      ),
      List.contains(~String, ~String.eq, Replicas.Tip.owners(t), n)
    ),
    Bool.not(List.is_empty(&2, Ledgers.Id, qs))
  )

# s with the node n's ballot for the act a at the place w, sealed as the next
# of the node's chain m (none: the store gave the node no key)
def Cast.seal(
  +s: Replicas.Node<Basics.Ask>,
  +w: Ledgers.Where,
  n: String,
  a: Ledgers.Act,
  m: Maybe<&2, Replicas.Keychain>
) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{Replicas.Keychain{+j, last, key, f}}:
      +seed = Keys.seed(Replicas.State.keys(~Basics.Ask.machine(), s))
      +r = Where.store(w)
      Maybe.default(
        &2,
        Replicas.Node<Basics.Ask>,
        Seal.accept(
          s,
          Ledgers.Ballot.make(
            Seal.secret(seed, r, j),
            Ledgers.Signed{w, n, a},
            last,
            Seals.Seal.public(Seal.secret(seed, r, U32.inc(j)))
          )
        ),
        s
      )

# the state m with the node n's ballot for the act a at the place w, else s
def Cast.vote(
  s: Replicas.Node<Basics.Ask>,
  m: Maybe<&2, Replicas.Node<Basics.Ask>>,
  +w: Ledgers.Where,
  +n: String,
  a: Ledgers.Act
) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{s3}:
      +s4 = Replicas.State.led(~Basics.Ask.machine(), s, Replicas.State.ledger(~Basics.Ask.machine(), s3))
      Cast.seal(s4, w, n, a, Seal.chain(s4, Where.store(w), n))

# s with the node n's vote at the place w for the step that ran qs from the
# tip of the hash th, which the passes of the nodes from allow, when the run m
# is there: the run's nodes, its tip, and the ballot
def Cast.put(
  n: String,
  w: Ledgers.Where,
  th: Maybe<&2, Hashes.Hash>,
  qs: List<&2, Ledgers.Id>,
  from: List<&2, String>,
  m: Maybe<&2, Replicas.Run<Basics.Ask>>,
  s: Replicas.Node<Basics.Ask>
) -> Replicas.Node<Basics.Ask>:
  match m:
    case None{}:
      s
    case Some{Replicas.Run{s2, +t2}}:
      Cast.vote(
        s,
        Replicas.State.put(~Basics.Ask.machine(), s2, [Replicas.Tip.words(t2)]),
        w,
        n,
        Ledgers.Act.Vote{Ledgers.Vote{th, qs, Some{Replicas.Tip.hash(t2)}}, from}
      )

# the node s may cast for the request i, which it holds as m: any request,
# but one of who decides only when it was asked at s
def Cast.mine.of(s: Replicas.Node<Basics.Ask>, i: Ledgers.Id, m: Maybe<&2, Ledgers.Asked<Basics.Ask>>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{Ledgers.Asked{t, q}}:
      List.any.if(u => Keys.asked(Replicas.State.keys(~Basics.Ask.machine(), s), i), Bool.not(Replicas.Kernel.governs(Stepping.Ask.kernel())(q)))

# the requests of qs that the node s may cast for
def Cast.mine(+s: Replicas.Node<Basics.Ask>, qs: List<&2, Ledgers.Id>) -> List<&2, Ledgers.Id>:
  match qs:
    case Nil{}:
      []
    case Con{+i, r}:
      List.filter.put(Ledgers.Id, i, Cast.mine(s, r), Cast.mine.of(s, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i)))

# the owner whose turn it is to propose the step at the height h, among the
# owners os: each in turn, by the height. One owner proposes a step and the
# others cast for the same step, so the owners do not split over what waits
# at each of them
def Owners.turn(+os: List<&2, String>, h: U32) -> Maybe<&2, String>:
  List.get(&2, String, os, U32.to_nat(U32.mod(h, U32.from_nat(List.length(&2, String, os)))))

# the step in the cell m of a ballot, if it holds one
def Cast.step(m: Maybe<&2, Cells.Cell<Ledgers.Entry<Basics.Ask>>>) -> Maybe<&2, Ledgers.Vote>:
  match m:
    case Some{Cells.One{Ledgers.Entry.Vote{b}}}:
      Ledgers.Ballot.vote(b)
    case x:
      None{}

# the step that the node p cast at the place w, if s holds its ballot
def Cast.of(s: Replicas.Node<Basics.Ask>, w: Ledgers.Where, p: String) -> Maybe<&2, Ledgers.Vote>:
  Cast.step(Ledgers.State.get(~Basics.Ask, Replicas.State.ledger(~Basics.Ask.machine(), s), Ledgers.Slot.vote(w, p)))

# what a node casts for: the requests of a step, its own run of them (none:
# it cannot run them now), and the nodes whose passes allow the step
type Plan is Data:
  Plan{asks: List<&2, Ledgers.Id>, run: Maybe<&2, Replicas.Run<Basics.Ask>>, from: List<&2, String>}

# the requests of the plan p
def Plan.asks(p: Plan) -> List<&2, Ledgers.Id>:
  match p:
    case Plan{qs, m, from}:
      qs

# the run of the plan p
def Plan.run(p: Plan) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match p:
    case Plan{qs, m, from}:
      m

# the nodes whose passes allow the step of the plan p
def Plan.from(p: Plan) -> List<&2, String>:
  match p:
    case Plan{qs, m, from}:
      from

# the plan of an owner that proposes freely, on the line c at the tip t: the
# requests that wait at it, that it may cast for and that can run now
def Plan.own(+s: Replicas.Node<Basics.Ask>, +c: Ledgers.Chain, t: Replicas.Tip, from: List<&2, String>) -> Plan:
  +p = Stepping.Step.some(c, Cast.mine(s, Wait.of(s, c)), Replicas.Run{s, t})
  Plan{Replicas.Picked.asks(~Basics.Ask.machine(), p), Some{Replicas.Picked.run(~Basics.Ask.machine(), p)}, from}

# the node s may cast for each request of qs
def Cast.all_mine(+s: Replicas.Node<Basics.Ask>, qs: List<&2, Ledgers.Id>) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{+i, r}:
      List.all.if(u => Cast.all_mine(s, r), Cast.mine.of(s, i, Replicas.Node.asked(~Basics.Ask.machine(), s, i)))

# the run m, when it gives the tip of the hash after
def Plan.fit(after: Maybe<&2, Hashes.Hash>, m: Maybe<&2, Replicas.Run<Basics.Ask>>) -> Maybe<&2, Replicas.Run<Basics.Ask>>:
  match m:
    case None{}:
      None{}
    case Some{Replicas.Run{s2, +t2}}:
      Shared.Maybe.when(
        Replicas.Run<Basics.Ask>,
        Root.same(after, Some{Replicas.Tip.hash(t2)}),
        u => Some{Replicas.Run{s2, t2}}
      )

# the plan for a step m that another ballot names, on the line c at the tip t
# of the hash th: when the step starts from this tip, the node may cast for
# each of its requests, and the node's own run of them gives the same tip
def Plan.copy(
  +s: Replicas.Node<Basics.Ask>,
  c: Ledgers.Chain,
  t: Replicas.Tip,
  th: Maybe<&2, Hashes.Hash>,
  m: Maybe<&2, Ledgers.Vote>,
  from: List<&2, String>
) -> Plan:
  match m:
    case None{}:
      Plan{[], None{}, []}
    case Some{Ledgers.Vote{before, +qs, after}}:
      Shared.Bool.when(
        Plan,
        List.all.if(u => Cast.all_mine(s, qs), Root.same(before, th)),
        u => Plan{qs, Plan.fit(after, Stepping.Step.run(s, c, t, qs)), from},
        u => Plan{[], None{}, []}
      )
