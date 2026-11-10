import Base
import ./shared/quorum.bend as Quorums
import ./shared/shared/cell.bend as Cells
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/seal.bend as Seals
import ./shared/shared/shared.bend as Shared
import ./shared/shared/trie.bend as Tries
import ./shared/store.bend as Stores
import ./shared/text.bend as Texts

# Ledgers
# =======
# A ledger is what nodes replicate: requests, ballots, data and proofs of
# lies, each in the slot that its own content names. A holder takes in what
# it lacks and never changes what it holds (State.take), so every ledger only
# grows, and holders of the same entries hold the same state, in any order
# and any number of times.
#
# A line is a store, or a line below it. Its owners cast one ballot each for
# the step at each round of each height; what a majority of them cast in one
# round stays as the ledger grows (State.decide_grows). When that is a step,
# and what a step means, is the caller's: the ledger does not read a line's
# state.

# Names
# -----

# a request: the writer that made it and the ID that the writer gave it
type Id is Data:
  Id{writer: String, request: String}

# a line: the request that started its store, and its key below the store
# (none: the store itself). Keys below one store are prefix-free.
type Chain is Data:
  Chain{root: Id, sub: Maybe<&2, List<&2, Bool>>}

# a place on a line: a height, and a round of the decision at that height
type Where is Data:
  Where{chain: Chain, height: U32, round: Nat}

# a ballot for a step: the requests that it decides, in order, and the hash of
# what the line holds before and after it
type Vote is Data:
  Vote{before: Maybe<&2, Hashes.Hash>, asks: List<&2, Id>, after: Maybe<&2, Hashes.Hash>}

# the last vote of a node at a height: its round, and the step
type Last is Data:
  Last{round: Nat, vote: Vote}

# what a node does at a place. Vote: it casts for a step; in a round after
# the first, with the nodes whose passes allow that step. Pass: it leaves the
# rounds below this one (it casts no vote there any more), and names its last
# vote at the height, if any
type Act is Data:
  Act.Vote{vote: Vote, from: List<&2, String>}
  Act.Pass{last: Maybe<&2, Last>}

# what a node signs with a ballot: the place, its own name, and what it does
type Signed is Data:
  Signed{at: Where, node: String, act: Act}

# how a ballot is sealed. A node's ballots in one store are a chain: each
# names the place of the one before it (none: the first), and the key of the
# next one, so each key signs once
type Link is Data:
  Link{prev: Maybe<&2, Where>, next: Hashes.Hash, seal: Seals.Seal}

# a ballot of a node: what it signs, and how it is sealed
type Ballot is Data:
  Ballot{signed: Signed, link: Link}

# the proof that a node lied: a key, and two ballots that the key signs. A key
# signs one ballot only, so only the owner of the key can make one
type Lie is Data:
  Lie{key: Hashes.Hash, one: Ballot, two: Ballot}

# a request of a change, with its time; a ballot of a node; data; or the proof
# that a node lied
type Entry<-Q: Data> is Data:
  Entry.Ask{id: Id, time: String, ask: Q}
  Entry.Vote{ballot: Ballot}
  Entry.Data{words: List<&2, U32>}
  Entry.Lie{lie: Lie}

# Codes
# -----
# Ledger values are sent and stored as their codes (Codes).

# the request i, then r
def Id.code(i: Id, r: List<&2, U32>) -> List<&2, U32>:
  match i:
    case Id{w, q}:
      Codes.Code.text(w, Codes.Code.text(q, r))

# a request ID
def Id.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Id>>:
  Codes.Code.two.read(
    ~String,
    ~String,
    ~Id,
    ~Codes.Code.text.read,
    ~Codes.Code.text.read,
    w => q => Id{w, q},
    ts
  )

# the nodes os, then r
def Owners.code(os: List<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~String, ~Codes.Code.text, os, r)

# nodes
def Owners.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, String>>>:
  Codes.Code.list.read(~String, ~Codes.Code.text.read, ts)

# the bit b, then r
def Bit.code(b: Bool, r: List<&2, U32>) -> List<&2, U32>:
  Bool.pick(U32, b, 1, 0) <> r

# a bit
def Bit.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Bool>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Bool>>,
        U32.is_eq(x, 0),
        u => Some{Codes.Read{False{}, r}},
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Bool>>,
          U32.is_eq(x, 1),
          u => Some{Codes.Read{True{}, r}},
          u => None{}
        )
      )

# the bits k, then r
def Bits.code(k: List<&2, Bool>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~Bool, ~Bit.code, k, r)

# bits
def Bits.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, Bool>>>:
  Codes.Code.list.read(~Bool, ~Bit.code.read, ts)

# the line c, then r
def Chain.code(c: Chain, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Chain{i, k}:
      Id.code(i, Codes.Code.maybe(~List<&2, Bool>, ~Bits.code, k, r))

# a line
def Chain.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Chain>>:
  Codes.Code.two.read(
    ~Id,
    ~Maybe<&2, List<&2, Bool>>,
    ~Chain,
    ~Id.code.read,
    ~(m => Codes.Code.maybe.read(~List<&2, Bool>, ~Bits.code.read, m)),
    i => k => Chain{i, k},
    ts
  )

# a request ID reads back
def Id.code_read(
  x: Id,
  r: List<&2, U32>
) -> {Id.code.read(Id.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Id>>}:
  match x:
    case Id{w, q}:
      Codes.Code.two_read(
        ~String,
        ~String,
        ~Id,
        ~Codes.Code.text.codec(),
        ~Codes.Code.text.codec(),
        a => b => Id{a, b},
        w,
        q,
        r
      )

# the code of request IDs
def Id.codec() -> Codes.Codec(Id):
  (Id.code, (Id.code.read, x => r => Id.code_read(x, r)))

# the key of i
def Id.key(i: Id) -> List<&2, Bool>:
  match i:
    case Id{w, r}:
      List.append(&2, Bool, Tries.Trie.text(w), Tries.Trie.text(r))

# the key of the line c
def Chain.key(c: Chain) -> List<&2, Bool>:
  match c:
    case Chain{i, None{}}:
      List.append(&2, Bool, Id.key(i), [False{}])
    case Chain{i, Some{k}}:
      List.append(&2, Bool, Id.key(i), True{} <> k)

# the key of a height: its 32 bits, highest first, so keys are in
# the order of numbers
def Word.key(x: U32) -> List<&2, Bool>:
  Tries.Trie.word(32n, x)

# the slot of the request i
def Slot.ask(i: Id) -> List<&2, Bool>:
  False{} <> False{} <> Id.key(i)

# the start of the slots of ballots
def Slot.ballots() -> List<&2, Bool>:
  [False{}, True{}]

# the start of the slots of the ballots of the line c
def Slot.votes(c: Chain) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.ballots(), Chain.key(c))

# the start of the slots of the ballots of the height h of the line c, of
# every round
def Slot.height(c: Chain, h: U32) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.votes(c), Word.key(h))

# the key of the round r below a height: r times True, then False
def Round.key(r: Nat, rest: List<&2, Bool>) -> List<&2, Bool>:
  match r:
    case 0n:
      False{} <> rest
    case 1n+p:
      True{} <> Round.key(p, rest)

# the start of the slots of the bucket of the votes of the round r of the
# height h of the line c
def Slot.bucket(c: Chain, h: U32, r: Nat) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.height(c, h), Round.key(r, [False{}]))

# the start of the slots of the passes to the round r of the height h of the
# line c
def Slot.passes(c: Chain, h: U32, r: Nat) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.height(c, h), Round.key(r, [True{}]))

# the slot of the node n's ballot in a bucket, below the bucket
def Slot.ballot(n: String) -> List<&2, Bool>:
  Tries.Trie.text(n)

# the slot of the node n's ballot at the place w
def Slot.vote(w: Where, n: String) -> List<&2, Bool>:
  match w:
    case Where{c, h, r}:
      List.append(&2, Bool, Slot.bucket(c, h, r), Slot.ballot(n))

# the slot of the node n's pass to the place w
def Slot.pass(w: Where, n: String) -> List<&2, Bool>:
  match w:
    case Where{c, h, r}:
      List.append(&2, Bool, Slot.passes(c, h, r), Slot.ballot(n))

# the start of the slots of the lies of the nodes in the store r
def Slot.lies(r: Id) -> List<&2, Bool>:
  True{} <> False{} <> Id.key(r)

# the start of the slots of the lies of the node n in the store r
def Slot.liar(r: Id, n: String) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.lies(r), Tries.Trie.text(n))

# the key of the hash h: its 256 bits
def Hash.key(h: Hashes.Hash) -> List<&2, Bool>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      List.append(
        &2,
        Bool,
        Word.key(a),
        List.append(
          &2,
          Bool,
          Word.key(b),
          List.append(
            &2,
            Bool,
            Word.key(c),
            List.append(
              &2,
              Bool,
              Word.key(d),
              List.append(
                &2,
                Bool,
                Word.key(e),
                List.append(&2, Bool, Word.key(f), List.append(&2, Bool, Word.key(g), Word.key(i)))
              )
            )
          )
        )
      )

# the start of the slots of data
def Slot.datas() -> List<&2, Bool>:
  [True{}, True{}, True{}, True{}]

# the slot of the data whose hash is h
def Slot.data(h: Hashes.Hash) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.datas(), Hash.key(h))

# a and b are the same request
def Id.is_eq(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same keys below a root
def Sub.is_eq(a: Maybe<&2, List<&2, Bool>>, b: Maybe<&2, List<&2, Bool>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, Bool>, ~Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq), a, b)

# a and b are the same line
def Chain.is_eq(a: Chain, b: Chain) -> Bool:
  match a b:
    case Chain{i1, k1} Chain{i2, k2}:
      List.all.if(u => Sub.is_eq(k1, k2), Id.is_eq(i1, i2))

# a and b are the same owners
def Owners.is_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  Shared.List.is_eq(~String, ~String.eq, a, b)

# Id.is_eq is True for a request and itself
def Id.is_eq_refl(a: Id) -> {Id.is_eq(a, a) == True{}: Bool}:
  match a:
    case Id{+w, +r}:
      Shared.Bool.and_both(
        String.eq(w, w),
        String.eq(r, r)
      )(Texts.String.eq_refl(w))(Texts.String.eq_refl(r))

# a = b, from the two halves of an and that compares them
def Eq.both(
  -A: Data,
  -B: Data,
  -T: Data,
  mk: A -> B -> T,
  x1: A,
  x2: A,
  y1: B,
  y2: B,
  ex: {x1 == x2: A},
  ey: {y1 == y2: B}
) -> {mk(x1)(y1) == mk(x2)(y2): T}:
  %ex: {mk(x1)(y1) == mk(_)(y2): T}
  %ey: {mk(x1)(y1) == mk(x1)(_): T}
  {==}

# Id.is_eq is True only for equal requests
def Id.is_eq_sound(a: Id, b: Id) -> {Id.is_eq(a, b) == True{}: Bool} -> {a == b: Id}:
  match a b:
    case Id{+w1, +r1} Id{+w2, +r2}:
      +h =>
        +x = String.eq(w1, w2)
        +y = String.eq(r1, r2)
        Eq.both(
          String,
          String,
          Id,
          p => q => Id{p, q},
          w1,
          w2,
          r1,
          r2,
          Texts.String.eq_sound(w1, w2)(Shared.Bool.and_true_left(x, y)(h)),
          Texts.String.eq_sound(r1, r2)(Shared.Bool.and_true_right(x, y)(h))
        )

# the laws of Owners.is_eq
def Owners.laws() -> Shared.Eq.Laws(List<&2, String>, Owners.is_eq):
  Shared.List.laws(~String, ~String.eq, ~Texts.String.laws())

# a = b, from the three parts of an and that compares them
def Eq.three(
  -A: Data,
  -B: Data,
  -C: Data,
  -T: Data,
  mk: A -> B -> C -> T,
  x1: A,
  x2: A,
  y1: B,
  y2: B,
  z1: C,
  z2: C,
  ex: {x1 == x2: A},
  ey: {y1 == y2: B},
  ez: {z1 == z2: C}
) -> {mk(x1)(y1)(z1) == mk(x2)(y2)(z2): T}:
  %ex: {mk(x1)(y1)(z1) == mk(_)(y2)(z2): T}
  %ey: {mk(x1)(y1)(z1) == mk(x1)(_)(z2): T}
  %ez: {mk(x1)(y1)(z1) == mk(x1)(y1)(_): T}
  {==}

# the code of a root: a hash, if any
def Root.codec() -> Codes.Codec(Maybe<&2, Hashes.Hash>):
  Codes.Code.maybe.codec(~Hashes.Hash, ~Hashes.Hash.codec())

# the ballot v, then r
def Vote.code(v: Vote, r: List<&2, U32>) -> List<&2, U32>:
  match v:
    case Vote{b, qs, a}:
      Codes.Codec.enc(
        Maybe<&2, Hashes.Hash>,
        Root.codec()
      )(
        b
      )(
        Codes.Codec.enc(
          List<&2, Id>,
          Codes.Code.list.codec(~Id, ~Id.codec())
        )(qs)(Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Root.codec())(a)(r))
      )

# a ballot
def Vote.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Vote>>:
  Codes.Code.three.read(
    ~Maybe<&2, Hashes.Hash>,
    ~List<&2, Id>,
    ~Maybe<&2, Hashes.Hash>,
    ~Vote,
    ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Root.codec()),
    ~Codes.Codec.dec(List<&2, Id>, Codes.Code.list.codec(~Id, ~Id.codec())),
    ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Root.codec()),
    b => qs => a => Vote{b, qs, a},
    ts
  )

# a ballot reads back
def Vote.code_read(
  v: Vote,
  r: List<&2, U32>
) -> {Vote.code.read(Vote.code(v, r)) == Some{Codes.Read{v, r}}: Maybe<&2, Codes.Read<Vote>>}:
  match v:
    case Vote{b, qs, a}:
      Codes.Code.three_read(
        ~Maybe<&2, Hashes.Hash>,
        ~List<&2, Id>,
        ~Maybe<&2, Hashes.Hash>,
        ~Vote,
        ~Root.codec(),
        ~Codes.Code.list.codec(~Id, ~Id.codec()),
        ~Root.codec(),
        x => y => z => Vote{x, y, z},
        b,
        qs,
        a,
        r
      )

# the code of ballots
def Vote.codec() -> Codes.Codec(Vote):
  (Vote.code, (Vote.code.read, x => r => Vote.code_read(x, r)))

# a and b are the same ballot: they have the same code
def Vote.is_eq(a: Vote, b: Vote) -> Bool:
  Codes.Code.is_eq(~Vote, ~Vote.code, a, b)

# the laws of Vote.is_eq
def Vote.laws() -> Shared.Eq.Laws(Vote, Vote.is_eq):
  Codes.Code.eq_laws(~Vote, ~Vote.codec())

# Vote.is_eq is True for a ballot and itself
def Vote.is_eq_refl(a: Vote) -> {Vote.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Vote, ~Vote.is_eq, Vote.laws(), a)

# Vote.is_eq is True only for equal ballots
def Vote.is_eq_sound(a: Vote, b: Vote) -> {Vote.is_eq(a, b) == True{}: Bool} -> {a == b: Vote}:
  Shared.Eq.sound(~Vote, ~Vote.is_eq, Vote.laws(), a, b)

# a bit reads back
def Bit.code_read(
  b: Bool,
  r: List<&2, U32>
) -> {Bit.code.read(Bit.code(b, r)) == Some{Codes.Read{b, r}}: Maybe<&2, Codes.Read<Bool>>}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# the code of bits
def Bits.codec() -> Codes.Codec(List<&2, Bool>):
  Codes.Code.list.codec(~Bool, ~(Bit.code, (Bit.code.read, b => r => Bit.code_read(b, r))))

# a line reads back
def Chain.code_read(
  c: Chain,
  r: List<&2, U32>
) -> {Chain.code.read(Chain.code(c, r)) == Some{Codes.Read{c, r}}: Maybe<&2, Codes.Read<Chain>>}:
  match c:
    case Chain{i, k}:
      Codes.Code.two_read(
        ~Id,
        ~Maybe<&2, List<&2, Bool>>,
        ~Chain,
        ~Id.codec(),
        ~Codes.Code.maybe.codec(~List<&2, Bool>, ~Bits.codec()),
        a => b => Chain{a, b},
        i,
        k,
        r
      )

# the code of lines
def Chain.codec() -> Codes.Codec(Chain):
  (Chain.code, (Chain.code.read, c => r => Chain.code_read(c, r)))

# the place w, then r
def Where.code(w: Where, r: List<&2, U32>) -> List<&2, U32>:
  match w:
    case Where{c, h, k}:
      Chain.code(c, Codes.Code.token(h, Codes.Code.count(k, r)))

# a place
def Where.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Where>>:
  Codes.Code.three.read(
    ~Chain,
    ~U32,
    ~Nat,
    ~Where,
    ~Chain.code.read,
    ~Codes.Code.token.read,
    ~Codes.Code.count.read,
    c => h => k => Where{c, h, k},
    ts
  )

# a place reads back
def Where.code_read(
  w: Where,
  r: List<&2, U32>
) -> {Where.code.read(Where.code(w, r)) == Some{Codes.Read{w, r}}: Maybe<&2, Codes.Read<Where>>}:
  match w:
    case Where{c, h, k}:
      Codes.Code.three_read(
        ~Chain,
        ~U32,
        ~Nat,
        ~Where,
        ~Chain.codec(),
        ~Codes.Code.token.codec(),
        ~(Codes.Code.count, (Codes.Code.count.read, x => y => Codes.Code.count_read(x, y))),
        a => b => d => Where{a, b, d},
        c,
        h,
        k,
        r
      )

# the code of places
def Where.codec() -> Codes.Codec(Where):
  (Where.code, (Where.code.read, w => r => Where.code_read(w, r)))

# the last vote l, then r
def Last.code(l: Last, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Last{k, v}:
      Codes.Code.count(k, Vote.code(v, r))

# a last vote
def Last.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Last>>:
  Codes.Code.two.read(
    ~Nat,
    ~Vote,
    ~Last,
    ~Codes.Code.count.read,
    ~Vote.code.read,
    k => v => Last{k, v},
    ts
  )

# a last vote reads back
def Last.code_read(
  l: Last,
  r: List<&2, U32>
) -> {Last.code.read(Last.code(l, r)) == Some{Codes.Read{l, r}}: Maybe<&2, Codes.Read<Last>>}:
  match l:
    case Last{k, v}:
      Codes.Code.two_read(
        ~Nat,
        ~Vote,
        ~Last,
        ~(Codes.Code.count, (Codes.Code.count.read, x => y => Codes.Code.count_read(x, y))),
        ~Vote.codec(),
        a => b => Last{a, b},
        k,
        v,
        r
      )

# the code of last votes
def Last.codec() -> Codes.Codec(Last):
  (Last.code, (Last.code.read, l => r => Last.code_read(l, r)))

# what a node does, then r
def Act.code(a: Act, r: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Act.Vote{v, from}:
      0 <> Vote.code(v, Owners.code(from, r))
    case Act.Pass{l}:
      1 <> Codes.Code.maybe(~Last, ~Last.code, l, r)

# what a node does
def Act.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Act>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Act>>,
        U32.is_eq(x, 0),
        u => Codes.Code.two.read(
          ~Vote,
          ~List<&2, String>,
          ~Act,
          ~Vote.code.read,
          ~Owners.code.read,
          v => from => Act.Vote{v, from},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Act>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(
            ~Maybe<&2, Last>,
            ~Act,
            ~(m => Codes.Code.maybe.read(~Last, ~Last.code.read, m)),
            l => Act.Pass{l},
            r
          ),
          u => None{}
        )
      )

# what a node does reads back
def Act.code_read(
  a: Act,
  r: List<&2, U32>
) -> {Act.code.read(Act.code(a, r)) == Some{Codes.Read{a, r}}: Maybe<&2, Codes.Read<Act>>}:
  match a:
    case Act.Vote{v, from}:
      Codes.Code.two_read(
        ~Vote,
        ~List<&2, String>,
        ~Act,
        ~Vote.codec(),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        x => y => Act.Vote{x, y},
        v,
        from,
        r
      )
    case Act.Pass{l}:
      Codes.Code.one_read(
        ~Maybe<&2, Last>,
        ~Act,
        ~Codes.Code.maybe.codec(~Last, ~Last.codec()),
        x => Act.Pass{x},
        l,
        r
      )

# the code of what a node does
def Act.codec() -> Codes.Codec(Act):
  (Act.code, (Act.code.read, a => r => Act.code_read(a, r)))

# what a node signs, then r
def Signed.code(x: Signed, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Signed{w, n, a}:
      Where.code(w, Codes.Code.text(n, Act.code(a, r)))

# what a node signs
def Signed.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Signed>>:
  Codes.Code.three.read(
    ~Where,
    ~String,
    ~Act,
    ~Signed,
    ~Where.code.read,
    ~Codes.Code.text.read,
    ~Act.code.read,
    w => n => a => Signed{w, n, a},
    ts
  )

# what a node signs reads back
def Signed.code_read(
  x: Signed,
  r: List<&2, U32>
) -> {Signed.code.read(Signed.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Signed>>}:
  match x:
    case Signed{w, n, a}:
      Codes.Code.three_read(
        ~Where,
        ~String,
        ~Act,
        ~Signed,
        ~Where.codec(),
        ~Codes.Code.text.codec(),
        ~Act.codec(),
        b => c => d => Signed{b, c, d},
        w,
        n,
        a,
        r
      )

# the code of what a node signs
def Signed.codec() -> Codes.Codec(Signed):
  (Signed.code, (Signed.code.read, x => r => Signed.code_read(x, r)))

# the link l, then r
def Link.code(l: Link, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Link{p, k, z}:
      Codes.Code.maybe(~Where, ~Where.code, p, Hashes.Hash.code(k, Seals.Seal.code(z, r)))

# a link
def Link.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Link>>:
  Codes.Code.three.read(
    ~Maybe<&2, Where>,
    ~Hashes.Hash,
    ~Seals.Seal,
    ~Link,
    ~(m => Codes.Code.maybe.read(~Where, ~Where.code.read, m)),
    ~Hashes.Hash.code.read,
    ~Seals.Seal.code.read,
    p => k => z => Link{p, k, z},
    ts
  )

# a link reads back
def Link.code_read(
  l: Link,
  r: List<&2, U32>
) -> {Link.code.read(Link.code(l, r)) == Some{Codes.Read{l, r}}: Maybe<&2, Codes.Read<Link>>}:
  match l:
    case Link{p, k, z}:
      Codes.Code.three_read(
        ~Maybe<&2, Where>,
        ~Hashes.Hash,
        ~Seals.Seal,
        ~Link,
        ~Codes.Code.maybe.codec(~Where, ~Where.codec()),
        ~Hashes.Hash.codec(),
        ~Seals.Seal.codec(),
        a => b => c => Link{a, b, c},
        p,
        k,
        z,
        r
      )

# the code of links
def Link.codec() -> Codes.Codec(Link):
  (Link.code, (Link.code.read, l => r => Link.code_read(l, r)))

# the ballot b, then r
def Ballot.code(b: Ballot, r: List<&2, U32>) -> List<&2, U32>:
  match b:
    case Ballot{x, l}:
      Signed.code(x, Link.code(l, r))

# a ballot
def Ballot.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Ballot>>:
  Codes.Code.two.read(
    ~Signed,
    ~Link,
    ~Ballot,
    ~Signed.code.read,
    ~Link.code.read,
    x => l => Ballot{x, l},
    ts
  )

# a ballot reads back
def Ballot.code_read(
  b: Ballot,
  r: List<&2, U32>
) -> {Ballot.code.read(Ballot.code(b, r)) == Some{Codes.Read{b, r}}: Maybe<&2, Codes.Read<Ballot>>}:
  match b:
    case Ballot{x, l}:
      Codes.Code.two_read(
        ~Signed,
        ~Link,
        ~Ballot,
        ~Signed.codec(),
        ~Link.codec(),
        a => c => Ballot{a, c},
        x,
        l,
        r
      )

# the code of ballots
def Ballot.codec() -> Codes.Codec(Ballot):
  (Ballot.code, (Ballot.code.read, b => r => Ballot.code_read(b, r)))

# a and b are the same ballot: they have the same code
def Ballot.is_eq(a: Ballot, b: Ballot) -> Bool:
  Codes.Code.is_eq(~Ballot, ~Ballot.code, a, b)

# the laws of Ballot.is_eq
def Ballot.laws() -> Shared.Eq.Laws(Ballot, Ballot.is_eq):
  Codes.Code.eq_laws(~Ballot, ~Ballot.codec())

# Ballot.is_eq is True for a ballot and itself
def Ballot.is_eq_refl(a: Ballot) -> {Ballot.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Ballot, ~Ballot.is_eq, Ballot.laws(), a)

# Ballot.is_eq is True only for equal ballots
def Ballot.is_eq_sound(
  a: Ballot,
  b: Ballot
) -> {Ballot.is_eq(a, b) == True{}: Bool} -> {a == b: Ballot}:
  Shared.Eq.sound(~Ballot, ~Ballot.is_eq, Ballot.laws(), a, b)

# the lie l, then r
def Lie.code(l: Lie, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Lie{k, a, b}:
      Hashes.Hash.code(k, Ballot.code(a, Ballot.code(b, r)))

# a lie
def Lie.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Lie>>:
  Codes.Code.three.read(
    ~Hashes.Hash,
    ~Ballot,
    ~Ballot,
    ~Lie,
    ~Hashes.Hash.code.read,
    ~Ballot.code.read,
    ~Ballot.code.read,
    k => a => b => Lie{k, a, b},
    ts
  )

# a lie reads back
def Lie.code_read(
  l: Lie,
  r: List<&2, U32>
) -> {Lie.code.read(Lie.code(l, r)) == Some{Codes.Read{l, r}}: Maybe<&2, Codes.Read<Lie>>}:
  match l:
    case Lie{k, a, b}:
      Codes.Code.three_read(
        ~Hashes.Hash,
        ~Ballot,
        ~Ballot,
        ~Lie,
        ~Hashes.Hash.codec(),
        ~Ballot.codec(),
        ~Ballot.codec(),
        x => y => z => Lie{x, y, z},
        k,
        a,
        b,
        r
      )

# the code of lies
def Lie.codec() -> Codes.Codec(Lie):
  (Lie.code, (Lie.code.read, l => r => Lie.code_read(l, r)))

# a and b are the same lie: they have the same code
def Lie.is_eq(a: Lie, b: Lie) -> Bool:
  Codes.Code.is_eq(~Lie, ~Lie.code, a, b)

# the laws of Lie.is_eq
def Lie.laws() -> Shared.Eq.Laws(Lie, Lie.is_eq):
  Codes.Code.eq_laws(~Lie, ~Lie.codec())

# the first ballot of the lie l
def Lie.one(l: Lie) -> Ballot:
  match l:
    case Lie{k, a, b}:
      a

# the start of the slots of the lies of the node of the ballot b in its store
def Ballot.liar(b: Ballot) -> List<&2, Bool>:
  match b:
    case Ballot{Signed{Where{Chain{r, c}, h, z}, n, a}, l}:
      Slot.liar(r, n)

# the slot of the lie l: below the lies of the node of its first ballot, the
# hash of its code. Its own content names it, as for data: two proofs against
# one node are in two slots, and the same proof is one cell
def Slot.lie(+l: Lie) -> List<&2, Bool>:
  List.append(&2, Bool, Ballot.liar(Lie.one(l)), Hash.key(Hashes.Sha.hash(Lie.code(l, []))))

# the step that the ballot b is for
def Ballot.vote(b: Ballot) -> Maybe<&2, Vote>:
  match b:
    case Ballot{Signed{w, n, Act.Vote{v, from}}, l}:
      Some{v}
    case Ballot{Signed{w, n, Act.Pass{p}}, l}:
      None{}

# the last vote that the ballot b names, when it is a pass
def Ballot.pass(b: Ballot) -> Maybe<&2, Maybe<&2, Last>>:
  match b:
    case Ballot{Signed{w, n, Act.Pass{p}}, l}:
      Some{p}
    case Ballot{Signed{w, n, Act.Vote{v, from}}, l}:
      None{}

# what the ballot b does
def Ballot.act(b: Ballot) -> Act:
  match b:
    case Ballot{Signed{w, n, a}, l}:
      a

# the ballot b is the ballot of the node n in the round r of the height whose
# slots start with hk. A cell counts only as what its ballot says: the keys of
# two places can meet in one slot, and a ballot is never read as one of a place
# or a node that it does not name
def Ballot.is(b: Ballot, hk: List<&2, Bool>, r: Nat, n: String) -> Bool:
  match b:
    case Ballot{Signed{Where{c, h, r2}, n2, a}, l}:
      List.all.if(
        u => List.all.if(u2 => Tries.Trie.same_key(Slot.height(c, h), hk), Nat.is_eq(r2, r)),
        String.eq(n2, n)
      )

# the cell of the vote m of a ballot: void when the ballot is not a vote
def Ballot.cell(m: Maybe<&2, Vote>) -> Cells.Cell<Vote>:
  match m:
    case Some{v}:
      Cells.One{v}
    case None{}:
      Cells.Many{}

# what a seal of a ballot signs: the hash of what the node signs, the place of
# its ballot before, and the key of its next one
def Ballot.digest(x: Signed, p: Maybe<&2, Where>, k: Hashes.Hash) -> Hashes.Hash:
  Hashes.Sha.hash(Signed.code(x, Codes.Code.maybe(~Where, ~Where.code, p, Hashes.Hash.code(k, []))))

# the ballot of x that the secret seed seals, after the ballot at p, with k as
# the key of the next one
def Ballot.make(seed: Hashes.Hash, +x: Signed, +p: Maybe<&2, Where>, +k: Hashes.Hash) -> Ballot:
  Ballot{x, Link{p, k, Seals.Seal.sign(seed, Ballot.digest(x, p, k))}}

# the key signs the ballot b
def Ballot.sealed(key: Hashes.Hash, b: Ballot) -> Bool:
  match b:
    case Ballot{x, Link{p, k, z}}:
      Seals.Seal.check(key, Ballot.digest(x, p, k), z)

# a ballot that a seed seals is signed by the key of the seed
def Ballot.sealed_make(
  seed: Hashes.Hash,
  x: Signed,
  p: Maybe<&2, Where>,
  k: Hashes.Hash
) -> {Ballot.sealed(Seals.Seal.public(seed), Ballot.make(seed, x, p, k)) == True{}: Bool}:
  Seals.Seal.check_sign(seed, Ballot.digest(x, p, k))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.Ask{i1, t1, q1} Entry.Ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.Vote{v1} Entry.Vote{v2}:
      Ballot.is_eq(v1, v2)
    case Entry.Data{d1} Entry.Data{d2}:
      Shared.List.is_eq(~U32, ~U32.is_eq, d1, d2)
    case Entry.Lie{l1} Entry.Lie{l2}:
      Lie.is_eq(l1, l2)
    case _ _:
      False{}

# Entry.is_eq is True for an entry and itself
def Entry.is_eq_refl(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>
) -> {Entry.is_eq(~Q, ~same, a, a) == True{}: Bool}:
  match a:
    case Entry.Ask{+i, +t, +q}:
      +st = String.eq(t, t)
      Shared.Bool.and_both(
        Id.is_eq(i, i),
        Bool.and(st, same(q, q))
      )(
        Id.is_eq_refl(i)
      )(
        Shared.Bool.and_both(
          st,
          same(q, q)
        )(Texts.String.eq_refl(t))(Shared.Eq.refl(~Q, ~same, laws, q))
      )
    case Entry.Vote{v}:
      Ballot.is_eq_refl(v)
    case Entry.Data{d}:
      Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), d)
    case Entry.Lie{l}:
      Shared.Eq.refl(~Lie, ~Lie.is_eq, Lie.laws(), l)

# Entry.is_eq is True only for equal entries
def Entry.is_eq_sound(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>,
  b: Entry<Q>
) -> {Entry.is_eq(~Q, ~same, a, b) == True{}: Bool} -> {a == b: Entry<Q>}:
  match a b:
    case Entry.Ask{+i1, +t1, +q1} Entry.Ask{+i2, +t2, +q2}:
      +h =>
        +x = Id.is_eq(i1, i2)
        +y = String.eq(t1, t2)
        +z = same(q1, q2)
        +r = Shared.Bool.and_true_right(x, Bool.and(y, z))(h)
        Eq.three(
          Id,
          String,
          Q,
          Entry<Q>,
          p => u => w => Entry.Ask{p, u, w},
          i1,
          i2,
          t1,
          t2,
          q1,
          q2,
          Id.is_eq_sound(i1, i2)(Shared.Bool.and_true_left(x, Bool.and(y, z))(h)),
          Texts.String.eq_sound(t1, t2)(Shared.Bool.and_true_left(y, z)(r)),
          Shared.Eq.sound(~Q, ~same, laws, q1, q2)(Shared.Bool.and_true_right(y, z)(r))
        )
    case Entry.Vote{v1} Entry.Vote{v2}:
      h =>
        %Ballot.is_eq_sound(v1, v2)(h): {Entry.Vote{v1} == Entry.Vote{_}: Entry<Q>}
        {==}
    case Entry.Data{d1} Entry.Data{d2}:
      h =>
        %Shared.List.is_eq_sound(
          ~U32,
          ~U32.is_eq,
          ~Shared.U32.laws(),
          d1,
          d2
        )(h): {Entry.Data{d1} == Entry.Data{_}: Entry<Q>}
        {==}
    case Entry.Lie{l1} Entry.Lie{l2}:
      h =>
        %Shared.Eq.sound(
          ~Lie,
          ~Lie.is_eq,
          Lie.laws(),
          l1,
          l2
        )(h): {Entry.Lie{l1} == Entry.Lie{_}: Entry<Q>}
        {==}
    case Entry.Ask{i, t, q} Entry.Vote{v}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Vote{v}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Ask{i, t, q} Entry.Data{d}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Data{d}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Vote{v} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Vote{v} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Vote{v} Entry.Data{d}:
      h => Empty.absurd({Entry.Vote{v} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Data{d} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Data{d} Entry.Vote{v}:
      h => Empty.absurd({Entry.Data{d} == Entry.Vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Ask{i, t, q} Entry.Lie{l}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Lie{l}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Vote{v} Entry.Lie{l}:
      h => Empty.absurd({Entry.Vote{v} == Entry.Lie{l}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.Lie{l}:
      h => Empty.absurd({Entry.Data{d} == Entry.Lie{l}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Lie{l} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Lie{l} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Lie{l} Entry.Vote{v}:
      h => Empty.absurd({Entry.Lie{l} == Entry.Vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Lie{l} Entry.Data{d}:
      h => Empty.absurd({Entry.Lie{l} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))

# the laws of Entry.is_eq, by the laws of same
def Entry.laws(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same)
) -> Shared.Eq.Laws(Entry<Q>, Entry.is_eq(~Q, ~same)):
  (a => Entry.is_eq_refl(~Q, ~same, ~laws, a), a => b => Entry.is_eq_sound(~Q, ~same, ~laws, a, b))

# The state
# ---------

# what a ledger of changes Q holds: the cell of each slot
def State(-Q: Data) -> Data:
  Tries.Trie<Cells.Cell<Entry<Q>>>

# a ledger that holds nothing yet
def State.empty(~Q: Data) -> State(Q):
  Tries.Trie.new(Cells.Cell<Entry<Q>>)

# what a holder of a and of b holds: a sync
def State.join(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q), b: State(Q)) -> State(Q):
  Tries.Trie.union(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    a,
    b
  )

# what a holder of r lacks of s: what a sync from s to r sends
def State.missing(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), r: State(Q)) -> State(Q):
  Tries.Trie.minus(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.is_eq(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    s,
    r
  )

# what a holder of s keeps of t: the entries of t in the slots where s holds
# nothing. A holder checks what it receives against what it holds, so it never
# loses or changes an entry.
def State.take(~Q: Data, s: State(Q), t: State(Q)) -> State(Q):
  Tries.Trie.take(~Cells.Cell<Entry<Q>>, s, t)

# no entry of t contradicts one of s
def State.agrees(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), t: State(Q)) -> Bool:
  Tries.Trie.all2(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => True{}),
    s,
    t
  )

# the cell of the slot k in s
def State.get(~Q: Data, s: State(Q), k: List<&2, Bool>) -> Maybe<&2, Cells.Cell<Entry<Q>>>:
  Tries.Trie.get(Cells.Cell<Entry<Q>>, s, k)

# the slots of s that start with k, under the rest of their keys
def State.under(~Q: Data, s: State(Q), k: List<&2, Bool>) -> State(Q):
  Tries.Trie.under(Cells.Cell<Entry<Q>>, s, k)

# s with the data of t in place of its own: what a holder of s keeps of a run
# on t, which may add data only
def State.with_data(~Q: Data, s: State(Q), t: State(Q)) -> State(Q):
  Tries.Trie.graft(Cells.Cell<Entry<Q>>, Slot.datas(), s, t)

# s with the data of t added: the data of s, and those of t in the slots of data
# that s leaves empty. It grows s, whatever t holds (State.add_data_of_grows)
def State.add_data_of(~Q: Data, +s: State(Q), t: State(Q)) -> State(Q):
  State.with_data(~Q, s, Tries.Trie.union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t))

# a ledger that holds only the entry e, in the slot k
def State.one(~Q: Data, k: List<&2, Bool>, e: Entry<Q>) -> State(Q):
  Tries.Trie.one(Cells.Cell<Entry<Q>>, k, Cells.One{e})

# s with the entry e in the slot k
def State.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  e: Entry<Q>
) -> State(Q):
  State.join(~Q, ~same, s, State.one(~Q, k, e))

# the entry of the slot k of s, when every holder agrees on it
def State.entry(~Q: Data, s: State(Q), k: List<&2, Bool>) -> Maybe<&2, Entry<Q>>:
  Cells.Cell.value(Entry<Q>, State.get(~Q, s, k))

# a request that a ledger holds: its time and change
type Asked<-Q: Data> is Data:
  Asked{time: String, ask: Q}

# the request in the entry m
def Asked.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Asked<Q>>:
  match m:
    case Some{Entry.Ask{i, t, q}}:
      Some{Asked{t, q}}
    case _:
      None{}

# the request i, when s holds it
def State.asked(~Q: Data, s: State(Q), i: Id) -> Maybe<&2, Asked<Q>>:
  Asked.of(~Q, State.entry(~Q, s, Slot.ask(i)))

# the ballot in the cell m, when it is the ballot of the node n in the round r
# of the height whose slots start with hk (Ballot.is)
def Cell.ballot(
  ~Q: Data,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String
) -> Maybe<&2, Ballot>:
  match m:
    case Some{Cells.One{Entry.Vote{+b}}}:
      Shared.Maybe.when(Ballot, Ballot.is(b, hk, r, n), u => Some{b})
    case x:
      None{}

# the ballot of a cell of a bucket, for the node n in the round r of the
# height whose slots start with hk: its vote, void when the cell holds
# anything else, none when it is empty
def Entry.ballot(
  ~Q: Data,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String
) -> Maybe<&2, Cells.Cell<Vote>>:
  match m:
    case None{}:
      None{}
    case Some{c}:
      Some{
        Ballot.cell(
          Maybe.bind(&2, Ballot, Vote, Cell.ballot(~Q, Some{c}, hk, r, n), b => Ballot.vote(b))
        )
      }

# the ballots of the nodes ms in the bucket b of the round r of the height
# whose slots start with hk, each read once
def Bucket.ballots(
  ~Q: Data,
  +b: State(Q),
  +hk: List<&2, Bool>,
  +r: Nat,
  ms: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Vote>>>:
  match ms:
    case Nil{}:
      []
    case Con{+m, rest}:
      Entry.ballot(
        ~Q,
        State.get(~Q, b, Slot.ballot(m)),
        hk,
        r,
        m
      )
        <> Bucket.ballots(~Q, b, hk, r, rest)

# what the ballots of ms in the bucket b decide
def Bucket.decide(
  ~Q: Data,
  b: State(Q),
  hk: List<&2, Bool>,
  r: Nat,
  ms: List<&2, String>
) -> Maybe<&2, Vote>:
  Quorums.Quorum.major(~Vote, ~Vote.is_eq, Bucket.ballots(~Q, b, hk, r, ms))

# the step that a majority of the owners ms cast at the place w of s, if one
# did
def State.decide(~Q: Data, s: State(Q), w: Where, ms: List<&2, String>) -> Maybe<&2, Vote>:
  match w:
    case Where{+c, +h, +r}:
      Bucket.decide(~Q, State.under(~Q, s, Slot.bucket(c, h, r)), Slot.height(c, h), r, ms)

# Data
# ----
# Data is held under its hash: a read gives it only when it hashes to the key
# (State.data_hash), so data that does not match is never believed, and the
# same data is held once.

# the words in the entry m, when it is data
def Data.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{Entry.Data{ws}}:
      Some{ws}
    case _:
      None{}

# the words ws, when they hash to h
def Data.check(h: Hashes.Hash, +ws: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  Shared.Maybe.when(List<&2, U32>, Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h), u => Some{ws})

# the data of s whose hash is h, when s holds it
def State.data(~Q: Data, s: State(Q), +h: Hashes.Hash) -> Maybe<&2, List<&2, U32>>:
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, U32>,
    Data.of(~Q, State.entry(~Q, s, Slot.data(h))),
    ws => Data.check(h, ws)
  )

# s with the data ws, once the cell m under its key k is known
def Data.put.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case None{}:
      State.put(~Q, ~same, s, k, Entry.Data{ws})
    case Some{x}:
      s

# s with the data ws, under its hash (unchanged when the slot is held)
def State.put_data(~Q: Data, ~same: Q -> Q -> Bool, +s: State(Q), +ws: List<&2, U32>) -> State(Q):
  +k = Slot.data(Hashes.Sha.hash(ws))
  Data.put.of(~Q, ~same, s, k, ws, State.get(~Q, s, k))

# s with the data ws, each under its hash
def State.put_datas(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ds: List<&2, List<&2, U32>>,
  s: State(Q)
) -> State(Q):
  match ds:
    case Nil{}:
      s
    case Con{ws, r}:
      State.put_datas(~Q, ~same, r, State.put_data(~Q, ~same, s, ws))

# s with the data ws under its key k, once the cell m there is known (none:
# the slot holds anything else than ws)
def Data.add.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> Maybe<&2, State(Q)>:
  match m:
    case None{}:
      Some{State.put(~Q, ~same, s, k, Entry.Data{ws})}
    case Some{Cells.One{Entry.Data{ws2}}}:
      Shared.Maybe.when(State(Q), Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws), u => Some{s})
    case Some{c}:
      None{}

# s with the data ws, when it then holds ws under its hash (none: the slot
# holds anything else). It hashes ws once: the words that the slot holds are
# compared with ws, not hashed
def State.add_data(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +ws: List<&2, U32>
) -> Maybe<&2, State(Q)>:
  +k = Slot.data(Hashes.Sha.hash(ws))
  Data.add.of(~Q, ~same, s, k, ws, State.get(~Q, s, k))

# s with the data ds, when it then holds each of them under its hash, in one
# pass (State.add_datas_plain)
def State.add_datas(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ds: List<&2, List<&2, U32>>,
  s: State(Q)
) -> Maybe<&2, State(Q)>:
  match ds:
    case Nil{}:
      Some{s}
    case Con{ws, r}:
      Maybe.bind(
        &2,
        State(Q),
        State(Q),
        State.add_data(~Q, ~same, s, ws),
        s2 => State.add_datas(~Q, ~same, r, s2)
      )

# s with the data ds, when it then holds each of them under its hash: each
# put, then each read back
def State.add_datas.plain(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +ds: List<&2, List<&2, U32>>,
  s: State(Q)
) -> Maybe<&2, State(Q)>:
  +s2 = State.put_datas(~Q, ~same, ds, s)
  Shared.Maybe.when(
    State(Q),
    Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), s2, ds),
    u => Some{s2}
  )

# Changes
# -------

# s with the entry e in the slot k, once the cell m there is known: a slot
# that holds a cell stays as it is
def State.add.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  e: Entry<Q>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case None{}:
      State.put(~Q, ~same, s, k, e)
    case Some{x}:
      s

# s with the entry e in the slot k, when the slot is empty
def State.add(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  e: Entry<Q>
) -> State(Q):
  State.add.of(~Q, ~same, s, k, e, State.get(~Q, s, k))

# s with the request i of the change q at the time t: a request ID that s
# holds counts once
def State.ask(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), +i: Id, t: String, q: Q) -> State(Q):
  State.add(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})

# the slot of the ballot b: a vote in the bucket of its place, a pass among
# the passes to its place
def Slot.of(b: Ballot) -> List<&2, Bool>:
  match b:
    case Ballot{Signed{w, n, Act.Vote{v, from}}, l}:
      Slot.vote(w, n)
    case Ballot{Signed{w, n, Act.Pass{p}}, l}:
      Slot.pass(w, n)

# s with the ballot b in its slot: a node casts one vote at a place, and one
# pass to a place
def State.keep(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), +b: Ballot) -> State(Q):
  State.add(~Q, ~same, s, Slot.of(b), Entry.Vote{b})

# the last vote in the cell m of a pass, if it holds the pass of the node n to
# the round r of the height whose slots start with hk
def Passed.of(
  ~Q: Data,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String
) -> Maybe<&2, Maybe<&2, Last>>:
  Maybe.bind(&2, Ballot, Maybe<&2, Last>, Cell.ballot(~Q, m, hk, r, n), b => Ballot.pass(b))

# the last vote that the node n named when it passed to the place w, if s
# holds its pass
def State.passed(~Q: Data, s: State(Q), w: Where, +n: String) -> Maybe<&2, Maybe<&2, Last>>:
  match w:
    case Where{+c, +h, +r}:
      Passed.of(~Q, State.get(~Q, s, Slot.pass(Where{c, h, r}, n)), Slot.height(c, h), r, n)

# the count of True at the start of the key k
def Spine.count(k: List<&2, Bool>) -> Nat:
  match k:
    case Con{True{}, r}:
      1n+Spine.count(r)
    case x:
      0n

# one more than the count of True at the start of each key of t, at least (0:
# t holds nothing). It walks only the keys that start with True
def Spine.depth(-V: Data, t: Tries.Trie<V>) -> Nat:
  match t:
    case Tries.Tip{}:
      0n
    case Tries.Leaf{k, v}:
      1n+Spine.count(k)
    case Tries.Bin{h, z, o}:
      1n+Spine.depth(V, o)

# the highest round of the height h of the line c in which s holds a ballot
# (0: the first round, or none). It reads the ledger, so no ballot that s
# holds is in a round above it (State.round_top)
def State.round(~Q: Data, s: State(Q), c: Chain, h: U32) -> Nat:
  Shared.Nat.before(Spine.depth(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.height(c, h))))

# s holds a proof that the node of the ballot b lied in its store: a cell
# below the lies of that node. It reads one key, whatever s holds
def State.blames(~Q: Data, s: State(Q), b: Ballot) -> Bool:
  Bool.not(Tries.Trie.is_tip(Cells.Cell<Entry<Q>>, State.under(~Q, s, Ballot.liar(b))))

# Laws
# ----

# a part of a ledger that is a tip holds no cell
def Under.lacks(
  ~Q: Data,
  u: State(Q),
  k: List<&2, Bool>
) -> {
  Bool.not(Tries.Trie.is_tip(Cells.Cell<Entry<Q>>, u)) == False{}: Bool
} -> {State.get(~Q, u, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}:
  match u:
    case Tries.Tip{}:
      e => {==}
    case Tries.Leaf{p, v}:
      e => Empty.absurd(
        {State.get(~Q, Tries.Leaf{p, v}, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )
    case Tries.Bin{h, z, o}:
      e => Empty.absurd(
        {State.get(~Q, Tries.Bin{h, z, o}, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, e))
      )

# a part of a ledger that holds a cell is not a tip
def Under.held(
  ~Q: Data,
  u: State(Q),
  k: List<&2, Bool>,
  -c: Cells.Cell<Entry<Q>>
) -> {
  State.get(~Q, u, k) == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {Bool.not(Tries.Trie.is_tip(Cells.Cell<Entry<Q>>, u)) == True{}: Bool}:
  match u:
    case Tries.Tip{}:
      e => Empty.absurd(
        {False{} == True{}: Bool},
        Shared.Maybe.none_ne_some(Cells.Cell<Entry<Q>>, c, e)
      )
    case Tries.Leaf{p, v}:
      e => {==}
    case Tries.Bin{h, z, o}:
      e => {==}

# a ledger that does not blame the node of a ballot holds no cell below the
# lies of that node
def State.blames_lacks(
  ~Q: Data,
  +s: State(Q),
  +b: Ballot,
  +k: List<&2, Bool>
) -> {
  State.blames(~Q, s, b) == False{}: Bool
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Ballot.liar(b), k)
  )
    == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  e =>
    %Tries.Trie.get_under(
      Cells.Cell<Entry<Q>>,
      s,
      Ballot.liar(b),
      k
    ): {_ == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    Under.lacks(~Q, State.under(~Q, s, Ballot.liar(b)), k)(e)

# a ledger that holds a cell below the lies of the node of a ballot blames
# that node
def State.blames_held(
  ~Q: Data,
  +s: State(Q),
  +b: Ballot,
  +k: List<&2, Bool>,
  -c: Cells.Cell<Entry<Q>>
) -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Ballot.liar(b), k)
  )
    == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {State.blames(~Q, s, b) == True{}: Bool}:
  e => Under.held(
    ~Q,
    State.under(~Q, s, Ballot.liar(b)),
    k,
    c
  )(
    Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.under(~Q, s, Ballot.liar(b)), k),
      State.get(~Q, s, List.append(&2, Bool, Ballot.liar(b), k)),
      Some{c},
      Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s, Ballot.liar(b), k),
      e
    )
  )

# a sync is the same either way round
law State.join_comm:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  for b: State(Q)
  {State.join(~Q, ~same, a, b) == State.join(~Q, ~same, b, a): State(Q)}

def State.join_comm(ty, same, laws, a, b):
  Tries.Trie.union_comm(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => y => Cells.Cell.join_comm(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        x,
        y
      )
    ),
    a,
    b
  )

# syncs group either way
law State.join_assoc:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  for b: State(Q)
  for c: State(Q)
  {
    State.join(
      ~Q,
      ~same,
      State.join(~Q, ~same, a, b),
      c
    )
      == State.join(~Q, ~same, a, State.join(~Q, ~same, b, c)): State(Q)
  }

def State.join_assoc(ty, same, laws, a, b, c):
  Tries.Trie.union_assoc(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => y => z => Cells.Cell.join_assoc(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        x,
        y,
        z
      )
    ),
    a,
    b,
    c
  )

# a sync with itself changes nothing
law State.join_idem:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for a: State(Q)
  {State.join(~Q, ~same, a, a) == a: State(Q)}

def State.join_idem(ty, same, laws, a):
  Tries.Trie.union_idem(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => Cells.Cell.join_idem(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        x
      )
    ),
    a
  )

# what a sync from s sends to r is enough: r with it is r with all of s
law State.missing_join:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for s: State(Q)
  for r: State(Q)
  {
    State.join(
      ~Q,
      ~same,
      r,
      State.missing(~Q, ~same, s, r)
    )
      == State.join(~Q, ~same, r, s): State(Q)
  }

def State.missing_join(ty, same, laws, s, r):
  Tries.Trie.union_minus(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~Cells.Cell.is_eq(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => Cells.Cell.join_idem(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        x
      )
    ),
    ~(
      (
        x => Cells.Cell.is_eq_refl(
          ~Entry<ty>,
          ~Entry.is_eq(~ty, ~same),
          ~Entry.laws(~ty, ~same, ~laws),
          x
        ),
        x => y => Cells.Cell.is_eq_sound(
          ~Entry<ty>,
          ~Entry.is_eq(~ty, ~same),
          ~Entry.laws(~ty, ~same, ~laws),
          x,
          y
        )
      )
    ),
    s,
    r
  )

# s2 keeps every cell of s
def State.grows(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), s2: State(Q)) -> Bool:
  Tries.Trie.keeps(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    s,
    s2
  )

# t holds the data of s
def State.holds_data(~Q: Data, ~same: Q -> Q -> Bool, +s: State(Q), t: State(Q)) -> Bool:
  State.grows(~Q, ~same, s, State.with_data(~Q, s, t))

# a and b hold the same ballots: each one keeps what the other holds in each
# slot of a ballot
def State.same_ballots(~Q: Data, ~same: Q -> Q -> Bool, a: State(Q), b: State(Q)) -> Bool:
  +x = State.under(~Q, a, Slot.ballots())
  +y = State.under(~Q, b, Slot.ballots())
  List.all.if(u => State.grows(~Q, ~same, y, x), State.grows(~Q, ~same, x, y))

# a sync that agrees grows a state
def State.grows_join(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  t: State(Q)
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {State.grows(~Q, ~same, s, State.join(~Q, ~same, s, t)) == True{}: Bool}:
  Tries.Trie.all2_join(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~Cells.Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => True{}),
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(
      x => Tries.Trie.all(
        ~Cells.Cell<Entry<Q>>,
        ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})),
        x
      )
    ),
    ~(
      a => b => Cells.Cell.keeps_join(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        a,
        b
      )
    ),
    ~(
      m => Cells.Cell.keeps_refl(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        m
      )
    ),
    s,
    t
  )

# a holder that takes anything in only grows its state: it keeps every cell
# that it holds, whatever it receives
law State.take_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for s: State(Q)
  for t: State(Q)
  {State.grows(~Q, ~same, s, State.take(~Q, s, t)) == True{}: Bool}

def State.take_grows(ty, same, laws, s, t):
  Tries.Trie.take_keeps(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => Tries.Trie.all(
        ~Cells.Cell<Entry<ty>>,
        ~(m => Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same), m, None{})),
        x
      )
    ),
    ~Cells.Cell.none_kept(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      m => Cells.Cell.keeps_refl(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        m
      )
    ),
    s,
    t
  )

# what a holder takes of a state that agrees with its own is their sync: the
# holders of states that agree end with the same state, in any order
law State.take_join:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for s: State(Q)
  for t: State(Q)
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {State.take(~Q, s, t) == State.join(~Q, ~same, s, t): State(Q)}

def State.take_join(ty, same, s, t):
  Tries.Trie.take_union(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~Cells.Cell.agrees(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(x => True{}),
    ~(a => b => Cells.Cell.take_join(~Entry<ty>, ~Entry.is_eq(~ty, ~same), a, b)),
    s,
    t
  )

# a holder that is behind (t keeps all that s holds) holds, after it takes t
# in, all that t holds: catching up loses nothing and contradicts nothing
law State.take_all:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for s: State(Q)
  for t: State(Q)
  {State.grows(~Q, ~same, s, t) == True{}: Bool}
    -> {State.grows(~Q, ~same, t, State.take(~Q, s, t)) == True{}: Bool}

def State.take_all(ty, same, laws, s, t):
  Tries.Trie.take_keeps_right(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => Tries.Trie.all(
        ~Cells.Cell<Entry<ty>>,
        ~(m => Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same), m, None{})),
        x
      )
    ),
    ~Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    ~(
      x => Tries.Trie.all(
        ~Cells.Cell<Entry<ty>>,
        ~(m => Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same), m, None{})),
        x
      )
    ),
    ~(
      a => b => Cells.Cell.take_keeps(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        a,
        b
      )
    ),
    ~(
      m => Cells.Cell.keeps_refl(
        ~Entry<ty>,
        ~Entry.is_eq(~ty, ~same),
        ~Entry.laws(~ty, ~same, ~laws),
        m
      )
    ),
    s,
    t
  )

# what a sync sends is enough: a holder that takes in what it lacks of s holds
# what it would hold had it taken all of s
law State.take_missing:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for r: State(Q)
  for s: State(Q)
  {State.take(~Q, r, State.missing(~Q, ~same, s, r)) == State.take(~Q, r, s): State(Q)}

def State.take_missing(ty, same, r, s):
  Tries.Trie.take_minus(
    ~Cells.Cell<Entry<ty>>,
    ~Cells.Cell.is_eq(~Entry<ty>, ~Entry.is_eq(~ty, ~same)),
    r,
    s
  )

# a read f of the entry of a slot stays (f gives nothing of no entry)
def State.read_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~W: Data,
  f: Maybe<&2, Entry<Q>> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  +s: State(Q),
  +s2: State(Q),
  +k: List<&2, Bool>,
  -w: W
) -> {
  State.grows(~Q, ~same, s, s2) == True{}: Bool
} -> {
  f(State.entry(~Q, s, k)) == Some{w}: Maybe<&2, W>
} -> {f(State.entry(~Q, s2, k)) == Some{w}: Maybe<&2, W>}:
  gr => Cells.Cell.read_kept(
    ~Entry<Q>,
    ~W,
    ~Entry.is_eq(~Q, ~same),
    ~Entry.laws(~Q, ~same, ~laws),
    f,
    fnone,
    State.get(~Q, s, k),
    State.get(~Q, s2, k),
    w
  )(
    Tries.Trie.keeps_get(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      s,
      s2,
      k
    )(gr)
  )

# the cell of a vote is kept as itself
def Ballot.cell_refl(
  m: Maybe<&2, Vote>
) -> {
  Cells.Cell.keeps(~Vote, ~Vote.is_eq, Some{Ballot.cell(m)}, Some{Ballot.cell(m)}) == True{}: Bool
}:
  match m:
    case Some{v}:
      Vote.is_eq_refl(v)
    case None{}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the ballot of a cell is kept in a cell that keeps it
def Ballot.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Maybe<&2, Cells.Cell<Entry<Q>>>,
  b: Maybe<&2, Cells.Cell<Entry<Q>>>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String
) -> {
  Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), a, b) == True{}: Bool
} -> {
  Cells.Cell.keeps(
    ~Vote,
    ~Vote.is_eq,
    Entry.ballot(~Q, a, hk, r, n),
    Entry.ballot(~Q, b, hk, r, n)
  )
    == True{}: Bool
}:
  match a:
    case None{}:
      k => {==}
    case Some{+c}:
      k =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          b,
          Some{c},
          Cells.Cell.keeps_held(
            ~Entry<Q>,
            ~Entry.is_eq(~Q, ~same),
            ~Entry.laws(~Q, ~same, ~laws),
            c,
            b
          )(k)
        ): {
          Cells.Cell.keeps(
            ~Vote,
            ~Vote.is_eq,
            Entry.ballot(~Q, Some{c}, hk, r, n),
            Entry.ballot(~Q, _, hk, r, n)
          )
            == True{}: Bool
        }
        Ballot.cell_refl(
          Maybe.bind(&2, Ballot, Vote, Cell.ballot(~Q, Some{c}, hk, r, n), x => Ballot.vote(x))
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the ballots of ms in the bucket at p are kept in a state that grows
def Ballots.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +p: List<&2, Bool>,
  +hk: List<&2, Bool>,
  +j: Nat,
  ms: List<&2, String>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<Vote>>,
    ~Maybe<&2, Cells.Cell<Vote>>,
    ~Cells.Cell.keeps(~Vote, ~Vote.is_eq),
    Bucket.ballots(~Q, State.under(~Q, s, p), hk, j, ms),
    Bucket.ballots(~Q, State.under(~Q, s2, p), hk, j, ms)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +k = Slot.ballot(m)
      +b1 = State.get(~Q, State.under(~Q, s, p), k)
      +b2 = State.get(~Q, State.under(~Q, s2, p), k)
      Shared.Bool.and_both(
        Cells.Cell.keeps(
          ~Vote,
          ~Vote.is_eq,
          Entry.ballot(~Q, b1, hk, j, m),
          Entry.ballot(~Q, b2, hk, j, m)
        ),
        Shared.List.all2(
          ~Maybe<&2, Cells.Cell<Vote>>,
          ~Maybe<&2, Cells.Cell<Vote>>,
          ~Cells.Cell.keeps(~Vote, ~Vote.is_eq),
          Bucket.ballots(~Q, State.under(~Q, s, p), hk, j, r),
          Bucket.ballots(~Q, State.under(~Q, s2, p), hk, j, r)
        )
      )(Ballot.grows(~Q, ~same, ~laws, b1, b2, hk, j, m)(
          %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.under(~Q, s, p), k), State.get(~Q, s, List.append(&2, Bool, p, k)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s, p, k)):
            {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), _, b2) == True{}: Bool}
          %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.under(~Q, s2, p), k), State.get(~Q, s2, List.append(&2, Bool, p, k)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s2, p, k)):
            {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, s, List.append(&2, Bool, p, k)), _) == True{}: Bool}
          Tries.Trie.keeps_get(~Cells.Cell<Entry<Q>>, ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, s2, List.append(&2, Bool, p, k))(gr)))(
        Ballots.grows(~Q, ~same, ~laws, s, s2, p, hk, j, r, gr)
      )

# what a majority of the owners cast at a place stays as the state grows: it
# is final
law State.decide_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +s2: State(Q)
  for +w: Where
  for +ms: List<&2, String>
  for +v: Vote
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {State.decide(~Q, s, w, ms) == Some{v}: Maybe<&2, Vote>}
    -> {State.decide(~Q, s2, w, ms) == Some{v}: Maybe<&2, Vote>}

def State.decide_grows(ty, same, laws, s, s2, w, ms, v):
  match w:
    case Where{+c, +h, +r}:
      +p = Slot.bucket(c, h, r)
      +hk = Slot.height(c, h)
      b1 = Bucket.ballots(~ty, State.under(~ty, s, p), hk, r, ms)
      b2 = Bucket.ballots(~ty, State.under(~ty, s2, p), hk, r, ms)
      +gr => hd =>
        Quorums.Quorum.major_kept(
          ~Vote,
          ~Vote.is_eq,
          ~Vote.laws(),
          b1,
          b2,
          v
        )(Ballots.grows(~ty, ~same, ~laws, s, s2, p, hk, r, ms, gr))(hd)

# a state grows to itself
def State.grows_refl(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q)
) -> {State.grows(~Q, ~same, s, s) == True{}: Bool}:
  Tries.Trie.all2_refl(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(
      x => Tries.Trie.all(
        ~Cells.Cell<Entry<Q>>,
        ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})),
        x
      )
    ),
    ~(
      m => Cells.Cell.keeps_refl(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        m
      )
    ),
    s
  )

# growth composes
def State.grows_trans(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s1: State(Q),
  s2: State(Q),
  s3: State(Q)
) -> {
  State.grows(~Q, ~same, s1, s2) == True{}: Bool
} -> {
  State.grows(~Q, ~same, s2, s3) == True{}: Bool
} -> {State.grows(~Q, ~same, s1, s3) == True{}: Bool}:
  Tries.Trie.keeps_trans(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(
      x => y => z => Cells.Cell.keeps_trans(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        x,
        y,
        z
      )
    ),
    s1,
    s2,
    s3
  )

# a put at an empty slot grows the state
def State.grows_put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +k: List<&2, Bool>,
  +e: Entry<Q>
) -> {
  State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {State.grows(~Q, ~same, s, State.put(~Q, ~same, s, k, e)) == True{}: Bool}:
  h => State.grows_join(
    ~Q,
    ~same,
    ~laws,
    s,
    State.one(~Q, k, e)
  )(
    Tries.Trie.all2_one(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      ~(x => True{}),
      ~(y => {==}),
      ~(a => Cells.Cell.agrees_none(~Entry<Q>, ~Entry.is_eq(~Q, ~same), a)),
      ~(x => {==}),
      s,
      k,
      Cells.One{e}
    )(h)
  )

# a put at an empty slot holds the entry there
def State.put_get(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  +e: Entry<Q>
) -> {
  State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  State.get(
    ~Q,
    State.put(~Q, ~same, s, k, e),
    k
  )
    == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  h =>
    +one1 = State.one(~Q, k, e)
    +get1 = State.get(~Q, s, k)
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.put(~Q, ~same, s, k, e), k),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        get1,
        State.get(~Q, one1, k)
      ),
      Tries.Trie.get_union(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        s,
        one1,
        k
      )
    ): {_ == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, get1, None{}, h):
      {
        Shared.Maybe.join(
          ~Cells.Cell<Entry<Q>>,
          ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
          _,
          State.get(~Q, one1, k)
        )
          == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>
      }
    Tries.Trie.get_one(Cells.Cell<Entry<Q>>, k, Cells.One{e})

# putting data grows the state
law State.put_data_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +ws: List<&2, U32>
  {State.grows(~Q, ~same, s, State.put_data(~Q, ~same, s, ws)) == True{}: Bool}

# State.put_data_grows once the cell m under the key is known
def Data.put.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, k) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {State.grows(~Q, ~same, s, Data.put.of(~Q, ~same, s, k, ws, m)) == True{}: Bool}:
  match m:
    case None{}:
      State.grows_put(~Q, ~same, ~laws, s, k, Entry.Data{ws})(em)
    case Some{x}:
      State.grows_refl(~Q, ~same, ~laws, s)

def State.put_data_grows(ty, same, laws, s, ws):
  +k = Slot.data(Hashes.Sha.hash(ws))
  Data.put.grows(~ty, ~same, ~laws, s, k, ws, State.get(~ty, s, k), {==})

# data, one after the other, grow the state
def State.put_datas_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ds: List<&2, List<&2, U32>>,
  +s: State(Q)
) -> {State.grows(~Q, ~same, s, State.put_datas(~Q, ~same, ds, s)) == True{}: Bool}:
  match ds:
    case Nil{}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case Con{+ws, +r}:
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        State.put_data(~Q, ~same, s, ws),
        State.put_datas(~Q, ~same, r, State.put_data(~Q, ~same, s, ws))
      )(
        State.put_data_grows(~Q, ~same, ~laws, s, ws)
      )(State.put_datas_grows(~Q, ~same, ~laws, r, State.put_data(~Q, ~same, s, ws)))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Data.check_hash once the hash check (ok) is known
def Data.check_hash.at(
  h: Hashes.Hash,
  ws: List<&2, U32>,
  -x: List<&2, U32>,
  ok: Bool,
  e: {Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h) == ok: Bool}
) -> {
  Shared.Maybe.when(List<&2, U32>, ok, u => Some{ws}) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Hashes.Sha.hash(x) == h: Hashes.Hash}:
  match ok:
    case True{}:
      d =>
        %Shared.Maybe.some_inj(List<&2, U32>, ws, x, d): {Hashes.Sha.hash(_) == h: Hashes.Hash}
        Hashes.Hash.is_eq_sound(Hashes.Sha.hash(ws), h)(e)
    case False{}:
      d => Empty.absurd(
        {Hashes.Sha.hash(x) == h: Hashes.Hash},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, d)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# data read under a hash hashes to it
def Data.check_hash(
  +h: Hashes.Hash,
  +ws: List<&2, U32>,
  -x: List<&2, U32>
) -> {
  Data.check(h, ws) == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Hashes.Sha.hash(x) == h: Hashes.Hash}:
  Data.check_hash.at(h, ws, x, Hashes.Hash.is_eq(Hashes.Sha.hash(ws), h), {==})

# what a ledger holds under a hash hashes to it: no data is believed under a
# key that it does not match
law State.data_hash:
  for ~Q: Data
  for s: State(Q)
  for +h: Hashes.Hash
  for -x: List<&2, U32>
  {
    State.data(~Q, s, h) == Some{x}: Maybe<&2, List<&2, U32>>
  } -> {Hashes.Sha.hash(x) == h: Hashes.Hash}

# State.data_hash once the data m under the key is known
def Data.then_hash(
  ~Q: Data,
  h: Hashes.Hash,
  -x: List<&2, U32>,
  m: Maybe<&2, List<&2, U32>>
) -> {
  Maybe.bind(
    &2,
    List<&2, U32>,
    List<&2, U32>,
    m,
    ws => Data.check(h, ws)
  )
    == Some{x}: Maybe<&2, List<&2, U32>>
} -> {Hashes.Sha.hash(x) == h: Hashes.Hash}:
  match m:
    case Some{ws}:
      Data.check_hash(h, ws, x)
    case None{}:
      d => Empty.absurd(
        {Hashes.Sha.hash(x) == h: Hashes.Hash},
        Shared.Maybe.none_ne_some(List<&2, U32>, x, d)
      )

def State.data_hash(ty, s, h, x):
  Data.then_hash(~ty, h, x, Data.of(~ty, State.entry(~ty, s, Slot.data(h))))

# data stays as the state grows
law State.data_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +s2: State(Q)
  for +h: Hashes.Hash
  for +x: List<&2, U32>
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {State.data(~Q, s, h) == Some{x}: Maybe<&2, List<&2, U32>>}
    -> {State.data(~Q, s2, h) == Some{x}: Maybe<&2, List<&2, U32>>}

def State.data_grows(ty, same, laws, s, s2, h, x):
  +gr => Shared.Maybe.bind_kept(
    List<&2, U32>,
    List<&2, U32>,
    Data.of(~ty, State.entry(~ty, s, Slot.data(h))),
    Data.of(~ty, State.entry(~ty, s2, Slot.data(h))),
    ws => Data.check(h, ws),
    ws => Data.check(h, ws),
    x,
    y => State.read_grows(
      ~ty,
      ~same,
      ~laws,
      ~List<&2, U32>,
      m => Data.of(~ty, m),
      {==},
      s,
      s2,
      Slot.data(h),
      y
    )(gr),
    y => d => d
  )

# data put where its slot is empty reads back
law State.put_data_get:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for +s: State(Q)
  for +ws: List<&2, U32>
  {State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    -> {
      State.data(
        ~Q,
        State.put_data(~Q, ~same, s, ws),
        Hashes.Sha.hash(ws)
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }

def State.put_data_get(ty, same, s, ws):
  +h0 =>
    +k = Slot.data(Hashes.Sha.hash(ws))
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<ty>>>, State.get(~ty, s, k), None{}, h0):
      {
        State.data(
          ~ty,
          Data.put.of(~ty, ~same, s, k, ws, _),
          Hashes.Sha.hash(ws)
        )
          == Some{ws}: Maybe<&2, List<&2, U32>>
      }
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<ty>>>,
      State.get(~ty, State.put(~ty, ~same, s, k, Entry.Data{ws}), k),
      Some{Cells.One{Entry.Data{ws}}},
      State.put_get(~ty, ~same, s, k, Entry.Data{ws})(h0)
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        List<&2, U32>,
        Data.of(~ty, Cells.Cell.value(Entry<ty>, _)),
        y => Data.check(Hashes.Sha.hash(ws), y)
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), Hashes.Sha.hash(ws)),
      True{},
      Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws))
    ):
      {Shared.Maybe.when(List<&2, U32>, _, u => Some{ws}) == Some{ws}: Maybe<&2, List<&2, U32>>}
    {==}

# an entry added to a state only grows it
law State.add_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +k: List<&2, Bool>
  for +e: Entry<Q>
  {State.grows(~Q, ~same, s, State.add(~Q, ~same, s, k, e)) == True{}: Bool}

# State.add_grows once the cell m of the slot is known
def State.add.of.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  k: List<&2, Bool>,
  e: Entry<Q>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, k) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {State.grows(~Q, ~same, s, State.add.of(~Q, ~same, s, k, e, m)) == True{}: Bool}:
  match m:
    case None{}:
      State.grows_put(~Q, ~same, ~laws, s, k, e)(em)
    case Some{x}:
      State.grows_refl(~Q, ~same, ~laws, s)

def State.add_grows(ty, same, laws, s, k, e):
  State.add.of.grows(~ty, ~same, ~laws, s, k, e, State.get(~ty, s, k), {==})

# a holder that lacks the data ws, and takes it in, holds it under its hash:
# a part that a node asks another node for, it then holds
law State.take_data:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for +s: State(Q)
  for +ws: List<&2, U32>
  {State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    -> {
      State.data(
        ~Q,
        State.take(~Q, s, State.put_data(~Q, ~same, State.empty(~Q), ws)),
        Hashes.Sha.hash(ws)
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }

def State.take_data(ty, same, s, ws):
  e =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<ty>>>,
      State.get(
        ~ty,
        State.take(~ty, s, State.put_data(~ty, ~same, State.empty(~ty), ws)),
        Slot.data(Hashes.Sha.hash(ws))
      ),
      Some{Cells.One{Entry.Data{ws}}},
      Equal.trans(
        Maybe<&2, Cells.Cell<Entry<ty>>>,
        State.get(
          ~ty,
          State.take(~ty, s, State.put_data(~ty, ~same, State.empty(~ty), ws)),
          Slot.data(Hashes.Sha.hash(ws))
        ),
        Shared.Maybe.join(
          ~Cells.Cell<Entry<ty>>,
          ~(x => y => x),
          State.get(~ty, s, Slot.data(Hashes.Sha.hash(ws))),
          State.get(
            ~ty,
            State.put_data(~ty, ~same, State.empty(~ty), ws),
            Slot.data(Hashes.Sha.hash(ws))
          )
        ),
        Some{Cells.One{Entry.Data{ws}}},
        Tries.Trie.get_union(
          ~Cells.Cell<Entry<ty>>,
          ~(x => y => x),
          s,
          State.put_data(~ty, ~same, State.empty(~ty), ws),
          Slot.data(Hashes.Sha.hash(ws))
        ),
        (
          %Equal.sym(Maybe<&2, Cells.Cell<Entry<ty>>>, State.get(~ty, s, Slot.data(Hashes.Sha.hash(ws))), None{}, e): {Shared.Maybe.join(~Cells.Cell<Entry<ty>>, ~(x => y => x), _, State.get(~ty, State.put_data(~ty, ~same, State.empty(~ty), ws), Slot.data(Hashes.Sha.hash(ws)))) == Some{Cells.One{Entry.Data{ws}}}: Maybe<&2, Cells.Cell<Entry<ty>>>}
          Equal.trans(Maybe<&2, Cells.Cell<Entry<ty>>>, Tries.Trie.get(Cells.Cell<Entry<ty>>, Tries.Trie.set(Cells.Cell<Entry<ty>>, Tries.Trie.new(Cells.Cell<Entry<ty>>), Slot.data(Hashes.Sha.hash(ws)), Cells.One{Entry.Data{ws}}), Slot.data(Hashes.Sha.hash(ws))), Bool.pick(Maybe<&2, Cells.Cell<Entry<ty>>>, Tries.Trie.same_key(Slot.data(Hashes.Sha.hash(ws)), Slot.data(Hashes.Sha.hash(ws))), Some{Cells.One{Entry.Data{ws}}}, None{}), Some{Cells.One{Entry.Data{ws}}}, Tries.Trie.get_set(Cells.Cell<Entry<ty>>, Tries.Trie.new(Cells.Cell<Entry<ty>>), Slot.data(Hashes.Sha.hash(ws)), Cells.One{Entry.Data{ws}}, Slot.data(Hashes.Sha.hash(ws))), (
            %Equal.sym(Bool, Tries.Trie.same_key(Slot.data(Hashes.Sha.hash(ws)), Slot.data(Hashes.Sha.hash(ws))), True{}, Shared.List.is_eq_refl(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws(), Slot.data(Hashes.Sha.hash(ws)))): {Bool.pick(Maybe<&2, Cells.Cell<Entry<ty>>>, _, Some{Cells.One{Entry.Data{ws}}}, None{}) == Some{Cells.One{Entry.Data{ws}}}: Maybe<&2, Cells.Cell<Entry<ty>>>}
            {==})))
      )
    ): {
      Maybe.bind(
        &2,
        List<&2, U32>,
        List<&2, U32>,
        Data.of(~ty, Cells.Cell.value(Entry<ty>, _)),
        w2 => Data.check(Hashes.Sha.hash(ws), w2)
      )
        == Some{ws}: Maybe<&2, List<&2, U32>>
    }
    %Equal.sym(
      Bool,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), Hashes.Sha.hash(ws)),
      True{},
      Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws))
    ): {Shared.Maybe.when(List<&2, U32>, _, u => Some{ws}) == Some{ws}: Maybe<&2, List<&2, U32>>}
    {==}

# a cell that a ledger holds, it holds as it grows
def State.held_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  +s2: State(Q),
  +k: List<&2, Bool>,
  c: Cells.Cell<Entry<Q>>
) -> {
  State.grows(~Q, ~same, s, s2) == True{}: Bool
} -> {
  State.get(~Q, s, k) == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {State.get(~Q, s2, k) == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>}:
  gr => eg =>
    Cells.Cell.keeps_held(
      ~Entry<Q>,
      ~Entry.is_eq(~Q, ~same),
      ~Entry.laws(~Q, ~same, ~laws),
      c,
      State.get(~Q, s2, k)
    )(
      %eg: {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), _, State.get(~Q, s2, k)) == True{}: Bool}
      Tries.Trie.keeps_get(~Cells.Cell<Entry<Q>>, ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, s2, k)(gr))

# an entry that a ledger holds, it holds as it grows
law State.one_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +s2: State(Q)
  for +k: List<&2, Bool>
  for +e: Entry<Q>
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {State.get(~Q, s, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    -> {State.get(~Q, s2, k) == Some{Cells.One{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>}

def State.one_grows(ty, same, laws, s, s2, k, e):
  State.held_grows(~ty, ~same, ~laws, s, s2, k, Cells.One{e})

# a holder that lacks the slot k, and takes in a ledger t, holds what t holds
# in k
law State.take_get:
  for ~Q: Data
  for +s: State(Q)
  for +t: State(Q)
  for +k: List<&2, Bool>
  {State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    -> {
      State.get(~Q, State.take(~Q, s, t), k) == State.get(~Q, t, k): Maybe<&2, Cells.Cell<Entry<Q>>>
    }

def State.take_get(ty, s, t, k):
  e =>
    Equal.trans(
      Maybe<&2, Cells.Cell<Entry<ty>>>,
      State.get(~ty, State.take(~ty, s, t), k),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<ty>>,
        ~(x => y => x),
        State.get(~ty, s, k),
        State.get(~ty, t, k)
      ),
      State.get(~ty, t, k),
      Tries.Trie.get_union(~Cells.Cell<Entry<ty>>, ~(x => y => x), s, t, k),
      (
        %Equal.sym(Maybe<&2, Cells.Cell<Entry<ty>>>, State.get(~ty, s, k), None{}, e): {Shared.Maybe.join(~Cells.Cell<Entry<ty>>, ~(x => y => x), _, State.get(~ty, t, k)) == State.get(~ty, t, k): Maybe<&2, Cells.Cell<Entry<ty>>>}
        {==})
    )

# a ledger holds the data that the slot of its hash holds
def State.has_held(
  ~Q: Data,
  s: State(Q),
  +ws: List<&2, U32>
) -> {
  State.get(
    ~Q,
    s,
    Slot.data(Hashes.Sha.hash(ws))
  )
    == Some{Cells.One{Entry.Data{ws}}}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), s, ws) == True{}: Bool}:
  eg =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
      Some{Cells.One{Entry.Data{ws}}},
      eg
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Maybe.bind(
          &2,
          List<&2, U32>,
          List<&2, U32>,
          Data.of(~Q, Cells.Cell.value(Entry<Q>, _)),
          y => Data.check(Hashes.Sha.hash(ws), y)
        ),
        Some{ws}
      )
        == True{}: Bool
    }
    %Equal.sym(
      Bool,
      Hashes.Hash.is_eq(Hashes.Sha.hash(ws), Hashes.Sha.hash(ws)),
      True{},
      Hashes.Hash.is_eq_refl(Hashes.Sha.hash(ws))
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Shared.Maybe.when(List<&2, U32>, _, u => Some{ws}),
        Some{ws}
      )
        == True{}: Bool
    }
    Shared.List.is_eq_refl(~U32, ~U32.is_eq, ~Shared.U32.laws(), ws)

# State.has_other once the hash check (ok) is known
def State.has_other.at(
  ws: List<&2, U32>,
  ws2: List<&2, U32>,
  ok: Bool
) -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws) == False{}: Bool
} -> {
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    Shared.Maybe.when(List<&2, U32>, ok, u => Some{ws2}),
    Some{ws}
  )
    == False{}: Bool
}:
  match ok:
    case True{}:
      e => e
    case False{}:
      e => {==}

# a ledger does not hold the data ws when the slot of its hash holds other
# words
def State.has_other(
  ~Q: Data,
  s: State(Q),
  +ws: List<&2, U32>,
  +ws2: List<&2, U32>
) -> {
  State.get(
    ~Q,
    s,
    Slot.data(Hashes.Sha.hash(ws))
  )
    == Some{Cells.One{Entry.Data{ws2}}}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws) == False{}: Bool
} -> {Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), s, ws) == False{}: Bool}:
  eg => ne =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
      Some{Cells.One{Entry.Data{ws2}}},
      eg
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Maybe.bind(
          &2,
          List<&2, U32>,
          List<&2, U32>,
          Data.of(~Q, Cells.Cell.value(Entry<Q>, _)),
          y => Data.check(Hashes.Sha.hash(ws), y)
        ),
        Some{ws}
      )
        == False{}: Bool
    }
    State.has_other.at(ws, ws2, Hashes.Hash.is_eq(Hashes.Sha.hash(ws2), Hashes.Sha.hash(ws)))(ne)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a ledger does not hold the data ws when the slot of its hash holds no data
def State.has_none(
  ~Q: Data,
  s: State(Q),
  ws: List<&2, U32>,
  c: Cells.Cell<Entry<Q>>
) -> {
  State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Data.of(~Q, Cells.Cell.value(Entry<Q>, Some{c})) == None{}: Maybe<&2, List<&2, U32>>
} -> {Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), s, ws) == False{}: Bool}:
  eg => en =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
      Some{c},
      eg
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Maybe.bind(
          &2,
          List<&2, U32>,
          List<&2, U32>,
          Data.of(~Q, Cells.Cell.value(Entry<Q>, _)),
          y => Data.check(Hashes.Sha.hash(ws), y)
        ),
        Some{ws}
      )
        == False{}: Bool
    }
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      Data.of(~Q, Cells.Cell.value(Entry<Q>, Some{c})),
      None{},
      en
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        Maybe.bind(&2, List<&2, U32>, List<&2, U32>, _, y => Data.check(Hashes.Sha.hash(ws), y)),
        Some{ws}
      )
        == False{}: Bool
    }
    {==}

# the plain put of the data ws and then r is the plain put of r, when the
# state t after the puts holds ws
def State.add_datas_plain.hit(
  ~Q: Data,
  -x: Maybe<&2, State(Q)>,
  t: State(Q),
  ws: List<&2, U32>,
  r: List<&2, List<&2, U32>>
) -> {
  Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws) == True{}: Bool
} -> {
  x
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), t, r),
      u => Some{t}
    ): Maybe<&2, State(Q)>
} -> {
  x
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws <> r),
      u => Some{t}
    ): Maybe<&2, State(Q)>
}:
  eh => ex =>
    %Equal.sym(
      Bool,
      Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws),
      True{},
      eh
    ): {
      x
        == Shared.Maybe.when(
          State(Q),
          List.all.if(
            u => Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), t, r),
            _
          ),
          u => Some{t}
        ): Maybe<&2, State(Q)>
    }
    ex

# the plain put of the data ws and then r gives nothing, when the state t
# after the puts does not hold ws
def State.add_datas_plain.miss(
  ~Q: Data,
  t: State(Q),
  ws: List<&2, U32>,
  r: List<&2, List<&2, U32>>
) -> {
  Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws) == False{}: Bool
} -> {
  None{}
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws <> r),
      u => Some{t}
    ): Maybe<&2, State(Q)>
}:
  eh =>
    %Equal.sym(
      Bool,
      Stores.Store.has(~State(Q), ~(l => h => State.data(~Q, l, h)), t, ws),
      False{},
      eh
    ): {
      None{}
        == Shared.Maybe.when(
          State(Q),
          List.all.if(
            u => Stores.Store.holds(~State(Q), ~(l => h => State.data(~Q, l, h)), t, r),
            _
          ),
          u => Some{t}
        ): Maybe<&2, State(Q)>
    }
    {==}

# State.add_datas_plain where the slot of the first data ws holds the words
# ws2, once their comparison (b) is known
def State.add_datas_plain.same(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +ws: List<&2, U32>,
  ws2: List<&2, U32>,
  +r: List<&2, List<&2, U32>>,
  b: Bool,
  eb: {Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws) == b: Bool},
  eg: {
    State.get(
      ~Q,
      State.put_datas(~Q, ~same, r, s),
      Slot.data(Hashes.Sha.hash(ws))
    )
      == Some{Cells.One{Entry.Data{ws2}}}: Maybe<&2, Cells.Cell<Entry<Q>>>
  },
  ih: {
    State.add_datas(~Q, ~same, r, s) == State.add_datas.plain(~Q, ~same, r, s): Maybe<&2, State(Q)>
  }
) -> {
  Maybe.bind(
    &2,
    State(Q),
    State(Q),
    Shared.Maybe.when(State(Q), b, u => Some{s}),
    s2 => State.add_datas(~Q, ~same, r, s2)
  )
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(
        ~State(Q),
        ~(l => h => State.data(~Q, l, h)),
        State.put_datas(~Q, ~same, r, s),
        ws <> r
      ),
      u => Some{State.put_datas(~Q, ~same, r, s)}
    ): Maybe<&2, State(Q)>
}:
  match b:
    case True{}:
      +t = State.put_datas(~Q, ~same, r, s)
      State.add_datas_plain.hit(
        ~Q,
        State.add_datas(~Q, ~same, r, s),
        t,
        ws,
        r
      )(State.has_held(~Q, t, ws)(
          %Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), ws2, ws)(eb): {State.get(~Q, t, Slot.data(Hashes.Sha.hash(ws))) == Some{Cells.One{Entry.Data{_}}}: Maybe<&2, Cells.Cell<Entry<Q>>>}
          eg))(ih)
    case False{}:
      +t = State.put_datas(~Q, ~same, r, s)
      State.add_datas_plain.miss(~Q, t, ws, r)(State.has_other(~Q, t, ws, ws2)(eg)(eb))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# State.add_datas_plain where the slot of the first data ws holds a cell c
# that is not data
def State.add_datas_plain.other(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +ws: List<&2, U32>,
  +r: List<&2, List<&2, U32>>,
  +c: Cells.Cell<Entry<Q>>,
  em: {
    State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == Some{c}: Maybe<&2, Cells.Cell<Entry<Q>>>
  },
  en: {Data.of(~Q, Cells.Cell.value(Entry<Q>, Some{c})) == None{}: Maybe<&2, List<&2, U32>>}
) -> {
  None{}
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(
        ~State(Q),
        ~(l => h => State.data(~Q, l, h)),
        State.put_datas(~Q, ~same, r, s),
        ws <> r
      ),
      u => Some{State.put_datas(~Q, ~same, r, s)}
    ): Maybe<&2, State(Q)>
}:
  +t = State.put_datas(~Q, ~same, r, s)
  State.add_datas_plain.miss(
    ~Q,
    t,
    ws,
    r
  )(
    State.has_none(
      ~Q,
      t,
      ws,
      c
    )(
      State.held_grows(
        ~Q,
        ~same,
        ~laws,
        s,
        t,
        Slot.data(Hashes.Sha.hash(ws)),
        c
      )(State.put_datas_grows(~Q, ~same, ~laws, r, s))(em)
    )(en)
  )

# State.add_datas_plain for the first data ws, once the cell m of its slot is
# known
def State.add_datas_plain.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +ws: List<&2, U32>,
  +r: List<&2, List<&2, U32>>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == m: Maybe<&2, Cells.Cell<Entry<Q>>>},
  ih: {
    State.add_datas(
      ~Q,
      ~same,
      r,
      Data.put.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, m)
    )
      == State.add_datas.plain(
        ~Q,
        ~same,
        r,
        Data.put.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, m)
      ): Maybe<&2, State(Q)>
  }
) -> {
  Maybe.bind(
    &2,
    State(Q),
    State(Q),
    Data.add.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, m),
    s2 => State.add_datas(~Q, ~same, r, s2)
  )
    == Shared.Maybe.when(
      State(Q),
      Stores.Store.holds(
        ~State(Q),
        ~(l => h => State.data(~Q, l, h)),
        State.put_datas(
          ~Q,
          ~same,
          r,
          Data.put.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, m)
        ),
        ws <> r
      ),
      u => Some{
        State.put_datas(
          ~Q,
          ~same,
          r,
          Data.put.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, m)
        )
      }
    ): Maybe<&2, State(Q)>
}:
  match m:
    case None{}:
      +k = Slot.data(Hashes.Sha.hash(ws))
      +p = State.put(~Q, ~same, s, k, Entry.Data{ws})
      +t = State.put_datas(~Q, ~same, r, p)
      State.add_datas_plain.hit(
        ~Q,
        State.add_datas(~Q, ~same, r, p),
        t,
        ws,
        r
      )(
        State.has_held(
          ~Q,
          t,
          ws
        )(
          State.held_grows(
            ~Q,
            ~same,
            ~laws,
            p,
            t,
            k,
            Cells.One{Entry.Data{ws}}
          )(
            State.put_datas_grows(~Q, ~same, ~laws, r, p)
          )(State.put_get(~Q, ~same, s, k, Entry.Data{ws})(em))
        )
      )(ih)
    case Some{Cells.One{Entry.Data{+ws2}}}:
      State.add_datas_plain.same(
        ~Q,
        ~same,
        s,
        ws,
        ws2,
        r,
        Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws),
        {==},
        State.held_grows(
          ~Q,
          ~same,
          ~laws,
          s,
          State.put_datas(~Q, ~same, r, s),
          Slot.data(Hashes.Sha.hash(ws)),
          Cells.One{Entry.Data{ws2}}
        )(State.put_datas_grows(~Q, ~same, ~laws, r, s))(em),
        ih
      )
    case Some{Cells.One{Entry.Ask{i, t, q}}}:
      State.add_datas_plain.other(
        ~Q,
        ~same,
        ~laws,
        s,
        ws,
        r,
        Cells.One{Entry.Ask{i, t, q}},
        em,
        {==}
      )
    case Some{Cells.One{Entry.Vote{b}}}:
      State.add_datas_plain.other(~Q, ~same, ~laws, s, ws, r, Cells.One{Entry.Vote{b}}, em, {==})
    case Some{Cells.One{Entry.Lie{l}}}:
      State.add_datas_plain.other(~Q, ~same, ~laws, s, ws, r, Cells.One{Entry.Lie{l}}, em, {==})
    case Some{Cells.Many{}}:
      State.add_datas_plain.other(~Q, ~same, ~laws, s, ws, r, Cells.Many{}, em, {==})

# the one-pass put is the plain one: each of the data put, then each read
# back under its hash
law State.add_datas_plain:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +ds: List<&2, List<&2, U32>>
  for +s: State(Q)
  {
    State.add_datas(
      ~Q,
      ~same,
      ds,
      s
    )
      == State.add_datas.plain(~Q, ~same, ds, s): Maybe<&2, State(Q)>
  }

def State.add_datas_plain(ty, same, laws, ds, s):
  match ds:
    case Nil{}:
      {==}
    case Con{+ws, +r}:
      State.add_datas_plain.at(
        ~ty,
        ~same,
        ~laws,
        s,
        ws,
        r,
        State.get(~ty, s, Slot.data(Hashes.Sha.hash(ws))),
        {==},
        State.add_datas_plain(~ty, ~same, ~laws, r, State.put_data(~ty, ~same, s, ws))
      )

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a trie that holds a key that starts with the key of the round r goes down
# more than r steps of True
def Spine.above(
  -V: Data,
  r: Nat,
  t: Tries.Trie<V>,
  tail: List<&2, Bool>,
  y: List<&2, Bool>,
  -x: V
) -> {
  Tries.Trie.get(V, t, List.append(&2, Bool, Round.key(r, tail), y)) == Some{x}: Maybe<&2, V>
} -> {Nat.is_lt(r, Spine.depth(V, t)) == True{}: Bool}:
  match r t:
    case 0n Tries.Tip{}:
      e => Empty.absurd({Nat.is_lt(0n, 0n) == True{}: Bool}, Shared.Maybe.none_ne_some(V, x, e))
    case 0n Tries.Leaf{k, v}:
      e => {==}
    case 0n Tries.Bin{h, z, o}:
      e => {==}
    case 1n+p Tries.Tip{}:
      e => Empty.absurd({Nat.is_lt(1n+p, 0n) == True{}: Bool}, Shared.Maybe.none_ne_some(V, x, e))
    case 1n+p Tries.Leaf{Nil{}, v}:
      e => Empty.absurd({Nat.is_lt(1n+p, 1n) == True{}: Bool}, Shared.Maybe.none_ne_some(V, x, e))
    case 1n+p Tries.Leaf{Con{False{}, k}, v}:
      e => Empty.absurd({Nat.is_lt(1n+p, 1n) == True{}: Bool}, Shared.Maybe.none_ne_some(V, x, e))
    case 1n+p Tries.Leaf{Con{True{}, k}, v}:
      e => Spine.above(V, p, Tries.Leaf{k, v}, tail, y, x)(e)
    case 1n+p Tries.Bin{h, z, o}:
      e => Spine.above(V, p, o, tail, y, x)(e)
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# no ballot that a ledger holds at a height is in a round above the round
# that it reads there: a slot below the key of the round r, with a cell
def State.round_top(
  ~Q: Data,
  +s: State(Q),
  c: Chain,
  h: U32,
  +r: Nat,
  +tail: List<&2, Bool>,
  +y: List<&2, Bool>,
  -x: Cells.Cell<Entry<Q>>
) -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, List.append(&2, Bool, Slot.height(c, h), Round.key(r, tail)), y)
  )
    == Some{x}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {Nat.is_le(r, State.round(~Q, s, c, h)) == True{}: Bool}:
  e =>
    +hk = Slot.height(c, h)
    Shared.Nat.lt_before(
      r,
      Spine.depth(Cells.Cell<Entry<Q>>, State.under(~Q, s, hk))
    )(
      Spine.above(
        Cells.Cell<Entry<Q>>,
        r,
        State.under(~Q, s, hk),
        tail,
        y,
        x
      )(
        Equal.trans(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.under(~Q, s, hk), List.append(&2, Bool, Round.key(r, tail), y)),
          State.get(~Q, s, List.append(&2, Bool, hk, List.append(&2, Bool, Round.key(r, tail), y))),
          Some{x},
          Tries.Trie.get_under(
            Cells.Cell<Entry<Q>>,
            s,
            hk,
            List.append(&2, Bool, Round.key(r, tail), y)
          ),
          (
            %Shared.List.append_assoc(Bool, hk, Round.key(r, tail), y): {State.get(~Q, s, _) == Some{x}: Maybe<&2, Cells.Cell<Entry<Q>>>}
            e)
        )
      )
    )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Cell.kept once it is known whether the slot k is the slot of b (same_k)
def Cell.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  b: Ballot,
  +k: List<&2, Bool>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String,
  same_k: Bool,
  es: {Tries.Trie.same_key(k, Slot.of(b)) == same_k: Bool},
  e0: {State.get(~Q, s, Slot.of(b)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {
  Cell.ballot(
    ~Q,
    Shared.Maybe.join(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      State.get(~Q, s, k),
      Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, same_k, Some{Cells.One{Entry.Vote{b}}}, None{})
    ),
    hk,
    r,
    n
  )
    == Shared.Maybe.join(
      ~Ballot,
      ~(x => y => x),
      Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n),
      Shared.Maybe.when(Ballot, List.all.if(u => Ballot.is(b, hk, r, n), same_k), u => Some{b})
    ): Maybe<&2, Ballot>
}:
  match same_k:
    case False{}:
      %Tries.Trie.none_join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        State.get(~Q, s, k)
      ): {
        Cell.ballot(
          ~Q,
          _,
          hk,
          r,
          n
        )
          == Shared.Maybe.join(
            ~Ballot,
            ~(x => y => x),
            Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n),
            None{}
          ): Maybe<&2, Ballot>
      }
      Tries.Trie.none_join(~Ballot, ~(x => y => x), Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n))
    case True{}:
      %Equal.sym(
        List<&2, Bool>,
        k,
        Slot.of(b),
        Tries.Trie.same_key_sound(k, Slot.of(b))(es)
      ): {
        Cell.ballot(
          ~Q,
          Shared.Maybe.join(
            ~Cells.Cell<Entry<Q>>,
            ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
            State.get(~Q, s, _),
            Some{Cells.One{Entry.Vote{b}}}
          ),
          hk,
          r,
          n
        )
          == Shared.Maybe.join(
            ~Ballot,
            ~(x => y => x),
            Cell.ballot(~Q, State.get(~Q, s, _), hk, r, n),
            Shared.Maybe.when(Ballot, Ballot.is(b, hk, r, n), u => Some{b})
          ): Maybe<&2, Ballot>
      }
      %Equal.sym(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        State.get(~Q, s, Slot.of(b)),
        None{},
        e0
      ): {
        Cell.ballot(
          ~Q,
          Shared.Maybe.join(
            ~Cells.Cell<Entry<Q>>,
            ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
            _,
            Some{Cells.One{Entry.Vote{b}}}
          ),
          hk,
          r,
          n
        )
          == Shared.Maybe.join(
            ~Ballot,
            ~(x => y => x),
            Cell.ballot(~Q, _, hk, r, n),
            Shared.Maybe.when(Ballot, Ballot.is(b, hk, r, n), u => Some{b})
          ): Maybe<&2, Ballot>
      }
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a read of the slot k after b is kept in its empty slot: the old read, joined
# with b when k is the slot of b and b is the ballot asked for (Ballot.is)
def Cell.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +b: Ballot,
  +k: List<&2, Bool>,
  hk: List<&2, Bool>,
  r: Nat,
  n: String
) -> {
  State.get(~Q, s, Slot.of(b)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Cell.ballot(
    ~Q,
    State.get(~Q, State.keep(~Q, ~same, s, b), k),
    hk,
    r,
    n
  )
    == Shared.Maybe.join(
      ~Ballot,
      ~(x => y => x),
      Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n),
      Shared.Maybe.when(
        Ballot,
        List.all.if(u => Ballot.is(b, hk, r, n), Tries.Trie.same_key(k, Slot.of(b))),
        u => Some{b}
      )
    ): Maybe<&2, Ballot>
}:
  +e0 =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, s, Slot.of(b)),
      None{},
      e0
    ): {
      Cell.ballot(
        ~Q,
        State.get(~Q, State.add.of(~Q, ~same, s, Slot.of(b), Entry.Vote{b}, _), k),
        hk,
        r,
        n
      )
        == Shared.Maybe.join(
          ~Ballot,
          ~(x => y => x),
          Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n),
          Shared.Maybe.when(
            Ballot,
            List.all.if(u => Ballot.is(b, hk, r, n), Tries.Trie.same_key(k, Slot.of(b))),
            u => Some{b}
          )
        ): Maybe<&2, Ballot>
    }
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.put(~Q, ~same, s, Slot.of(b), Entry.Vote{b}), k),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        State.get(~Q, s, k),
        State.get(~Q, State.one(~Q, Slot.of(b), Entry.Vote{b}), k)
      ),
      Tries.Trie.get_union(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        s,
        State.one(~Q, Slot.of(b), Entry.Vote{b}),
        k
      )
    ): {
      Cell.ballot(
        ~Q,
        _,
        hk,
        r,
        n
      )
        == Shared.Maybe.join(
          ~Ballot,
          ~(x => y => x),
          Cell.ballot(~Q, State.get(~Q, s, k), hk, r, n),
          Shared.Maybe.when(
            Ballot,
            List.all.if(u => Ballot.is(b, hk, r, n), Tries.Trie.same_key(k, Slot.of(b))),
            u => Some{b}
          )
        ): Maybe<&2, Ballot>
    }
    Cell.kept.at(~Q, ~same, s, b, k, hk, r, n, Tries.Trie.same_key(k, Slot.of(b)), {==}, e0)

# a read of a pass reads the key of its height only: two heights with one key
# read the same pass
def State.passed_key(
  ~Q: Data,
  s: State(Q),
  c: Chain,
  h: U32,
  c2: Chain,
  h2: U32,
  r: Nat,
  n: String
) -> {
  Slot.height(c, h) == Slot.height(c2, h2): List<&2, Bool>
} -> {
  State.passed(
    ~Q,
    s,
    Where{c, h, r},
    n
  )
    == State.passed(~Q, s, Where{c2, h2, r}, n): Maybe<&2, Maybe<&2, Last>>
}:
  e =>
    %Equal.sym(
      List<&2, Bool>,
      Slot.height(c, h),
      Slot.height(c2, h2),
      e
    ): {
      Passed.of(
        ~Q,
        State.get(
          ~Q,
          s,
          List.append(&2, Bool, List.append(&2, Bool, _, Round.key(r, [True{}])), Slot.ballot(n))
        ),
        _,
        r,
        n
      )
        == State.passed(~Q, s, Where{c2, h2, r}, n): Maybe<&2, Maybe<&2, Last>>
    }
    {==}

# State.passed_round once the cell m of the pass is known
def State.passed_round.at(
  ~Q: Data,
  s: State(Q),
  c: Chain,
  h: U32,
  r: Nat,
  n: String,
  -l: Maybe<&2, Last>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  State.get(~Q, s, Slot.pass(Where{c, h, r}, n)) == m: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Passed.of(~Q, m, Slot.height(c, h), r, n) == Some{l}: Maybe<&2, Maybe<&2, Last>>
} -> {Nat.is_le(r, State.round(~Q, s, c, h)) == True{}: Bool}:
  match m:
    case None{}:
      em => ep => Empty.absurd(
        {Nat.is_le(r, State.round(~Q, s, c, h)) == True{}: Bool},
        Shared.Maybe.none_ne_some(Maybe<&2, Last>, l, ep)
      )
    case Some{x}:
      em => ep => State.round_top(~Q, s, c, h, r, [True{}], Slot.ballot(n), x)(em)

# a pass that a ledger holds at a height is in a round up to the round that it
# reads there
def State.passed_round(
  ~Q: Data,
  +s: State(Q),
  +c: Chain,
  +h: U32,
  +r: Nat,
  +n: String,
  -l: Maybe<&2, Last>
) -> {
  State.passed(~Q, s, Where{c, h, r}, n) == Some{l}: Maybe<&2, Maybe<&2, Last>>
} -> {Nat.is_le(r, State.round(~Q, s, c, h)) == True{}: Bool}:
  State.passed_round.at(~Q, s, c, h, r, n, l, State.get(~Q, s, Slot.pass(Where{c, h, r}, n)))({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# a ledger with the data of t reads the data of t
def State.with_data_data(
  ~Q: Data,
  s: State(Q),
  t: State(Q),
  h: Hashes.Hash
) -> {
  State.data(~Q, State.with_data(~Q, s, t), h) == State.data(~Q, t, h): Maybe<&2, List<&2, U32>>
}:
  %Equal.sym(
    Maybe<&2, Cells.Cell<Entry<Q>>>,
    State.get(~Q, State.with_data(~Q, s, t), Slot.data(h)),
    Bool.pick(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      Tries.Trie.leads(Slot.datas(), Slot.data(h)),
      State.get(~Q, t, Slot.data(h)),
      State.get(~Q, s, Slot.data(h))
    ),
    Tries.Trie.get_graft(Cells.Cell<Entry<Q>>, Slot.datas(), s, t, Slot.data(h))
  ): {
    Maybe.bind(
      &2,
      List<&2, U32>,
      List<&2, U32>,
      Data.of(~Q, Cells.Cell.value(Entry<Q>, _)),
      ws => Data.check(h, ws)
    )
      == State.data(~Q, t, h): Maybe<&2, List<&2, U32>>
  }
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# a ledger with the data of t reads s at a slot that is not of data
def State.with_data_other(
  ~Q: Data,
  s: State(Q),
  t: State(Q),
  k: List<&2, Bool>
) -> {
  Tries.Trie.leads(Slot.datas(), k) == False{}: Bool
} -> {
  State.get(
    ~Q,
    State.with_data(~Q, s, t),
    k
  )
    == State.get(~Q, s, k): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  e =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.with_data(~Q, s, t), k),
      Bool.pick(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        Tries.Trie.leads(Slot.datas(), k),
        State.get(~Q, t, k),
        State.get(~Q, s, k)
      ),
      Tries.Trie.get_graft(Cells.Cell<Entry<Q>>, Slot.datas(), s, t, k)
    ): {_ == State.get(~Q, s, k): Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(
      Bool,
      Tries.Trie.leads(Slot.datas(), k),
      False{},
      e
    ): {
      Bool.pick(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        _,
        State.get(~Q, t, k),
        State.get(~Q, s, k)
      )
        == State.get(~Q, s, k): Maybe<&2, Cells.Cell<Entry<Q>>>
    }
    {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# State.with_data_grows at the slot k, once it is known whether it is of data
# (l)
def State.with_data_grows.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  t: State(Q),
  k: List<&2, Bool>,
  l: Bool
) -> {
  State.grows(~Q, ~same, s, t) == True{}: Bool
} -> {
  Cells.Cell.keeps(
    ~Entry<Q>,
    ~Entry.is_eq(~Q, ~same),
    State.get(~Q, s, k),
    Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, l, State.get(~Q, t, k), State.get(~Q, s, k))
  )
    == True{}: Bool
}:
  match l:
    case True{}:
      gr => Tries.Trie.keeps_get(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        s,
        t,
        k
      )(gr)
    case False{}:
      gr => Cells.Cell.keeps_refl(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        State.get(~Q, s, k)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# a ledger with the data of a ledger that grew from it grew
def State.with_data_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q)
) -> {
  State.grows(~Q, ~same, s, t) == True{}: Bool
} -> {State.grows(~Q, ~same, s, State.with_data(~Q, s, t)) == True{}: Bool}:
  +gr => Tries.Trie.all2_of_get(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => Tries.Trie.all(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x)),
    ~(x => f => Tries.Trie.all_of_get(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x, f)),
    s,
    State.with_data(~Q, s, t),
    +k =>
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.with_data(~Q, s, t), k), Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, Tries.Trie.leads(Slot.datas(), k), State.get(~Q, t, k), State.get(~Q, s, k)), Tries.Trie.get_graft(Cells.Cell<Entry<Q>>, Slot.datas(), s, t, k)): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, s, k), _) == True{}: Bool}
      State.with_data_grows.at(~Q, ~same, ~laws, s, t, k, Tries.Trie.leads(Slot.datas(), k))(gr))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a cell, then the cell that a union keeps first, keeps the first cell
def Union.first_keeps(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Maybe<&2, Cells.Cell<Entry<Q>>>,
  b: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), a, Shared.Maybe.join(~Cells.Cell<Entry<Q>>, ~(x => y => x), a, b)) == True{}: Bool}:
  match a b:
    case None{} y:
      {==}
    case Some{+x} None{}:
      Cells.Cell.keeps_refl(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), Some{x})
    case Some{+x} Some{y}:
      Cells.Cell.keeps_refl(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), Some{x})

# a union that keeps the cells of s first grows s
def Union.first_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q)
) -> {State.grows(~Q, ~same, s, Tries.Trie.union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t)) == True{}: Bool}:
  Tries.Trie.all2_of_get(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => Tries.Trie.all(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x)),
    ~(x => f => Tries.Trie.all_of_get(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x, f)),
    s,
    Tries.Trie.union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t),
    +k =>
      %Equal.sym(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        Tries.Trie.get(Cells.Cell<Entry<Q>>, Tries.Trie.union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t), k),
        Shared.Maybe.join(~Cells.Cell<Entry<Q>>, ~(x => y => x), Tries.Trie.get(Cells.Cell<Entry<Q>>, s, k), Tries.Trie.get(Cells.Cell<Entry<Q>>, t, k)),
        Tries.Trie.get_union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t, k)
      ): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, s, k), _) == True{}: Bool}
      Union.first_keeps(~Q, ~same, ~laws, State.get(~Q, s, k), State.get(~Q, t, k))
  )

# s with the data of t added grows s, whatever t holds
def State.add_data_of_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q)
) -> {State.grows(~Q, ~same, s, State.add_data_of(~Q, s, t)) == True{}: Bool}:
  State.with_data_grows(~Q, ~same, ~laws, s, Tries.Trie.union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t))(Union.first_grows(~Q, ~same, ~laws, s, t))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a ledger that holds the data of s reads each data that s reads
def State.holds_data_data(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +h: Hashes.Hash,
  w: List<&2, U32>
) -> {
  State.holds_data(~Q, ~same, s, t) == True{}: Bool
} -> {
  State.data(~Q, s, h) == Some{w}: Maybe<&2, List<&2, U32>>
} -> {State.data(~Q, t, h) == Some{w}: Maybe<&2, List<&2, U32>>}:
  g => e =>
    Equal.trans(
      Maybe<&2, List<&2, U32>>,
      State.data(~Q, t, h),
      State.data(~Q, State.with_data(~Q, s, t), h),
      Some{w},
      Equal.sym(
        Maybe<&2, List<&2, U32>>,
        State.data(~Q, State.with_data(~Q, s, t), h),
        State.data(~Q, t, h),
        State.with_data_data(~Q, s, t, h)
      ),
      State.data_grows(~Q, ~same, ~laws, s, State.with_data(~Q, s, t), h, w)(g)(e)
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# State.holds_data_with at the slot k, once it is known whether it is of data
# (l)
def State.holds_data_with.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  t: State(Q),
  k: List<&2, Bool>,
  l: Bool
) -> {
  Cells.Cell.keeps(
    ~Entry<Q>,
    ~Entry.is_eq(~Q, ~same),
    State.get(~Q, t, k),
    Bool.pick(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      l,
      Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, l, State.get(~Q, t, k), State.get(~Q, s, k)),
      State.get(~Q, t, k)
    )
  )
    == True{}: Bool
}:
  match l:
    case True{}:
      Cells.Cell.keeps_refl(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        State.get(~Q, t, k)
      )
    case False{}:
      Cells.Cell.keeps_refl(
        ~Entry<Q>,
        ~Entry.is_eq(~Q, ~same),
        ~Entry.laws(~Q, ~same, ~laws),
        State.get(~Q, t, k)
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof: it does not run
# s with the data of t holds the data of t
def State.holds_data_with(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q)
) -> {State.holds_data(~Q, ~same, t, State.with_data(~Q, s, t)) == True{}: Bool}:
  +w = State.with_data(~Q, s, t)
  Tries.Trie.all2_of_get(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => Tries.Trie.all(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x)),
    ~(x => f => Tries.Trie.all_of_get(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), x, f)),
    t,
    State.with_data(~Q, t, w),
    +k =>
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.with_data(~Q, t, w), k), Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, Tries.Trie.leads(Slot.datas(), k), State.get(~Q, w, k), State.get(~Q, t, k)), Tries.Trie.get_graft(Cells.Cell<Entry<Q>>, Slot.datas(), t, w, k)): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, t, k), _) == True{}: Bool}
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, w, k), Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, Tries.Trie.leads(Slot.datas(), k), State.get(~Q, t, k), State.get(~Q, s, k)), Tries.Trie.get_graft(Cells.Cell<Entry<Q>>, Slot.datas(), s, t, k)): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, t, k), Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, Tries.Trie.leads(Slot.datas(), k), _, State.get(~Q, t, k))) == True{}: Bool}
      State.holds_data_with.at(~Q, ~same, ~laws, s, t, k, Tries.Trie.leads(Slot.datas(), k)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# Ballots
# -------
# A ledger keeps its ballots in the slots that start with Slot.ballots. Each
# change of a node that is not a ballot it accepts writes elsewhere, so it
# keeps the same ballots (State.same_ballots), and what a node holds of the
# rounds reads only that part.

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run

# the slot of a lie is not the slot of a ballot
def Slot.lie_other(x: Lie) -> {Tries.Trie.leads(Slot.ballots(), Slot.lie(x)) == False{}: Bool}:
  match x:
    case Lie{k, Ballot{Signed{Where{Chain{r, c}, h, z}, n, a}, l}, b}:
      {==}

# a ledger holds the same ballots as itself
def State.same_ballots_refl(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: State(Q)
) -> {State.same_ballots(~Q, ~same, a, a) == True{}: Bool}:
  x = State.under(~Q, a, Slot.ballots())
  %Equal.sym(
    Bool,
    State.grows(~Q, ~same, x, x),
    True{},
    State.grows_refl(~Q, ~same, ~laws, x)
  ): {List.all.if(u => _, _) == True{}: Bool}
  {==}

# the same ballots compose
def State.same_ballots_trans(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: State(Q),
  b: State(Q),
  c: State(Q)
) -> {
  State.same_ballots(~Q, ~same, a, b) == True{}: Bool
} -> {
  State.same_ballots(~Q, ~same, b, c) == True{}: Bool
} -> {State.same_ballots(~Q, ~same, a, c) == True{}: Bool}:
  +eab => +ebc =>
    +x = State.under(~Q, a, Slot.ballots())
    +y = State.under(~Q, b, Slot.ballots())
    +z = State.under(~Q, c, Slot.ballots())
    Shared.List.all.if_both(
      State.grows(~Q, ~same, x, z),
      u => State.grows(~Q, ~same, z, x)
    )(
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        x,
        y,
        z
      )(
        Shared.List.all.if_hit(State.grows(~Q, ~same, x, y), u => State.grows(~Q, ~same, y, x))(eab)
      )(
        Shared.List.all.if_hit(State.grows(~Q, ~same, y, z), u => State.grows(~Q, ~same, z, y))(ebc)
      )
    )(
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        z,
        y,
        x
      )(
        Shared.List.all.if_rest(
          State.grows(~Q, ~same, y, z),
          u => State.grows(~Q, ~same, z, y)
        )(ebc)
      )(
        Shared.List.all.if_rest(
          State.grows(~Q, ~same, x, y),
          u => State.grows(~Q, ~same, y, x)
        )(eab)
      )
    )

# two ledgers with the same ballots read the same slot of a ballot
def State.same_ballots_get(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +a: State(Q),
  +b: State(Q),
  +r: List<&2, Bool>
) -> {
  State.same_ballots(~Q, ~same, a, b) == True{}: Bool
} -> {
  State.get(
    ~Q,
    a,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  +e =>
    +x = State.under(~Q, a, Slot.ballots())
    +y = State.under(~Q, b, Slot.ballots())
    %Tries.Trie.get_under(
      Cells.Cell<Entry<Q>>,
      a,
      Slot.ballots(),
      r
    ): {
      _
        == State.get(
          ~Q,
          b,
          List.append(&2, Bool, Slot.ballots(), r)
        ): Maybe<&2, Cells.Cell<Entry<Q>>>
    }
    %Tries.Trie.get_under(
      Cells.Cell<Entry<Q>>,
      b,
      Slot.ballots(),
      r
    ): {State.get(~Q, x, r) == _: Maybe<&2, Cells.Cell<Entry<Q>>>}
    Cells.Cell.keeps_both(
      ~Entry<Q>,
      ~Entry.is_eq(~Q, ~same),
      ~Entry.laws(~Q, ~same, ~laws),
      State.get(~Q, x, r),
      State.get(~Q, y, r)
    )(
      Tries.Trie.keeps_get(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        x,
        y,
        r
      )(Shared.List.all.if_hit(State.grows(~Q, ~same, x, y), u => State.grows(~Q, ~same, y, x))(e))
    )(
      Tries.Trie.keeps_get(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        y,
        x,
        r
      )(Shared.List.all.if_rest(State.grows(~Q, ~same, x, y), u => State.grows(~Q, ~same, y, x))(e))
    )

# a ledger that keeps what a holds in each slot of a ballot, read the same
# way at each such slot (f), grew in its ballots from a
def State.grows_ballots_of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +a: State(Q),
  +b: State(Q),
  f: @r: List<
    &2,
    Bool> -> {
    State.get(
      ~Q,
      a,
      List.append(&2, Bool, Slot.ballots(), r)
    )
      == State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
  }
) -> {
  State.grows(
    ~Q,
    ~same,
    State.under(~Q, a, Slot.ballots()),
    State.under(~Q, b, Slot.ballots())
  )
    == True{}: Bool
}:
  x = State.under(~Q, a, Slot.ballots())
  y = State.under(~Q, b, Slot.ballots())
  Tries.Trie.all2_of_get(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(t => Tries.Trie.all(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), t)),
    ~(t => g => Tries.Trie.all_of_get(~Cells.Cell<Entry<Q>>, ~(m => Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), m, None{})), t, g)),
    x,
    y,
    +r =>
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, y, r), State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, b, Slot.ballots(), r)): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, x, r), _) == True{}: Bool}
      %f(r): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, x, r), _) == True{}: Bool}
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, x, r), State.get(~Q, a, List.append(&2, Bool, Slot.ballots(), r)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, a, Slot.ballots(), r)): {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), _, State.get(~Q, a, List.append(&2, Bool, Slot.ballots(), r))) == True{}: Bool}
      Cells.Cell.keeps_refl(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), State.get(~Q, a, List.append(&2, Bool, Slot.ballots(), r))))

# two ledgers that read the same at each slot of a ballot hold the same
# ballots (f and g: the same fact, once for each way)
def State.same_ballots_of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +a: State(Q),
  +b: State(Q),
  f: @r: List<
    &2,
    Bool> -> {
    State.get(
      ~Q,
      a,
      List.append(&2, Bool, Slot.ballots(), r)
    )
      == State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
  },
  g: @r: List<
    &2,
    Bool> -> {
    State.get(
      ~Q,
      a,
      List.append(&2, Bool, Slot.ballots(), r)
    )
      == State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
  }
) -> {State.same_ballots(~Q, ~same, a, b) == True{}: Bool}:
  Shared.List.all.if_both(
    State.grows(~Q, ~same, State.under(~Q, a, Slot.ballots()), State.under(~Q, b, Slot.ballots())),
    u => State.grows(
      ~Q,
      ~same,
      State.under(~Q, b, Slot.ballots()),
      State.under(~Q, a, Slot.ballots())
    )
  )(
    State.grows_ballots_of(~Q, ~same, ~laws, a, b, f)
  )(
    State.grows_ballots_of(
      ~Q,
      ~same,
      ~laws,
      b,
      a,
      +r => Equal.sym(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        State.get(~Q, a, List.append(&2, Bool, Slot.ballots(), r)),
        State.get(~Q, b, List.append(&2, Bool, Slot.ballots(), r)),
        g(r)
      )
    )
  )

# a put in a slot that is not of a ballot reads as before in each slot of a
# ballot
def State.put_ballots_at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  e: Entry<Q>,
  +r: List<&2, Bool>
) -> {
  Tries.Trie.leads(Slot.ballots(), k) == False{}: Bool
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.put(~Q, ~same, s, k, e),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  el =>
    +q = List.append(&2, Bool, Slot.ballots(), r)
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.put(~Q, ~same, s, k, e), q),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        State.get(~Q, s, q),
        State.get(~Q, State.one(~Q, k, e), q)
      ),
      Tries.Trie.get_union(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        s,
        State.one(~Q, k, e),
        q
      )
    ): {State.get(~Q, s, q) == _: Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(
      Bool,
      Tries.Trie.same_key(q, k),
      False{},
      Tries.Trie.leads_other(Slot.ballots(), r, k)(el)
    ): {
      State.get(
        ~Q,
        s,
        q
      )
        == Shared.Maybe.join(
          ~Cells.Cell<Entry<Q>>,
          ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
          State.get(~Q, s, q),
          Bool.pick(Maybe<&2, Cells.Cell<Entry<Q>>>, _, Some{Cells.One{e}}, None{})
        ): Maybe<&2, Cells.Cell<Entry<Q>>>
    }
    Tries.Trie.none_join(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      State.get(~Q, s, q)
    )

# State.add_ballots_at once the cell m of the slot is known
def State.add_ballots_at.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  e: Entry<Q>,
  r: List<&2, Bool>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Tries.Trie.leads(Slot.ballots(), k) == False{}: Bool
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.add.of(~Q, ~same, s, k, e, m),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match m:
    case None{}:
      State.put_ballots_at(~Q, ~same, s, k, e, r)
    case Some{x}:
      el => {==}

# an add in a slot that is not of a ballot reads as before in each slot of a
# ballot
def State.add_ballots_at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  e: Entry<Q>,
  r: List<&2, Bool>
) -> {
  Tries.Trie.leads(Slot.ballots(), k) == False{}: Bool
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.add(~Q, ~same, s, k, e),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  State.add_ballots_at.of(~Q, ~same, s, k, e, r, State.get(~Q, s, k))

# State.put_data_ballots_at once the cell m of the slot is known
def State.put_data_ballots_at.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  r: List<&2, Bool>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Tries.Trie.leads(Slot.ballots(), k) == False{}: Bool
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      Data.put.of(~Q, ~same, s, k, ws, m),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match m:
    case None{}:
      State.put_ballots_at(~Q, ~same, s, k, Entry.Data{ws}, r)
    case Some{x}:
      el => {==}

# data reads as before in each slot of a ballot
def State.put_datas_ballots_at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ds: List<&2, List<&2, U32>>,
  +s: State(Q),
  +r: List<&2, Bool>
) -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.put_datas(~Q, ~same, ds, s),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match ds:
    case Nil{}:
      {==}
    case Con{+ws, rest}:
      +k = Slot.data(Hashes.Sha.hash(ws))
      Equal.trans(
        Maybe<&2, Cells.Cell<Entry<Q>>>,
        State.get(~Q, s, List.append(&2, Bool, Slot.ballots(), r)),
        State.get(~Q, State.put_data(~Q, ~same, s, ws), List.append(&2, Bool, Slot.ballots(), r)),
        State.get(
          ~Q,
          State.put_datas(~Q, ~same, rest, State.put_data(~Q, ~same, s, ws)),
          List.append(&2, Bool, Slot.ballots(), r)
        ),
        State.put_data_ballots_at.of(~Q, ~same, s, k, ws, r, State.get(~Q, s, k))({==}),
        State.put_datas_ballots_at(~Q, ~same, rest, State.put_data(~Q, ~same, s, ws), r)
      )

# State.add_datas_ballots_at once the data m that the slot holds is known
def State.add_data_ballots_at.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  r: List<&2, Bool>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  -s2: State(Q)
) -> {
  Tries.Trie.leads(Slot.ballots(), k) == False{}: Bool
} -> {
  Data.add.of(~Q, ~same, s, k, ws, m) == Some{s2}: Maybe<&2, State(Q)>
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(~Q, s2, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match m:
    case None{}:
      el => ea =>
        %Shared.Maybe.some_inj(
          State(Q),
          State.put(~Q, ~same, s, k, Entry.Data{ws}),
          s2,
          ea
        ): {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              _,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        }
        State.put_ballots_at(~Q, ~same, s, k, Entry.Data{ws}, r)(el)
    case Some{Cells.One{Entry.Data{ws2}}}:
      el => ea =>
        %Shared.Maybe.some_inj(
          State(Q),
          s,
          s2,
          Shared.Maybe.when_rest(
            State(Q),
            Shared.List.is_eq(~U32, ~U32.is_eq, ws2, ws),
            u => Some{s},
            s2
          )(ea)
        ): {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              _,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        }
        {==}
    case Some{Cells.One{Entry.Ask{i, t, q}}}:
      el => ea => Empty.absurd(
        {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              s2,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        },
        Shared.Maybe.none_ne_some(State(Q), s2, ea)
      )
    case Some{Cells.One{Entry.Vote{b}}}:
      el => ea => Empty.absurd(
        {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              s2,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        },
        Shared.Maybe.none_ne_some(State(Q), s2, ea)
      )
    case Some{Cells.One{Entry.Lie{x}}}:
      el => ea => Empty.absurd(
        {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              s2,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        },
        Shared.Maybe.none_ne_some(State(Q), s2, ea)
      )
    case Some{Cells.Many{}}:
      el => ea => Empty.absurd(
        {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              s2,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        },
        Shared.Maybe.none_ne_some(State(Q), s2, ea)
      )

# data added reads as before in each slot of a ballot
def State.add_datas_ballots_at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ds: List<&2, List<&2, U32>>,
  +s: State(Q),
  +r: List<&2, Bool>,
  -s2: State(Q)
) -> {
  State.add_datas(~Q, ~same, ds, s) == Some{s2}: Maybe<&2, State(Q)>
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(~Q, s2, List.append(&2, Bool, Slot.ballots(), r)): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match ds:
    case Nil{}:
      ea =>
        %Shared.Maybe.some_inj(
          State(Q),
          s,
          s2,
          ea
        ): {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              _,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        }
        {==}
    case Con{+ws, rest}:
      ea => Shared.Maybe.bind_some(
        State(Q),
        State(Q),
        {
          State.get(
            ~Q,
            s,
            List.append(&2, Bool, Slot.ballots(), r)
          )
            == State.get(
              ~Q,
              s2,
              List.append(&2, Bool, Slot.ballots(), r)
            ): Maybe<&2, Cells.Cell<Entry<Q>>>
        },
        State.add_data(~Q, ~same, s, ws),
        x => State.add_datas(~Q, ~same, rest, x),
        s2
      )(ea)(
        +s1 => e1 => e2 =>
          +k = Slot.data(Hashes.Sha.hash(ws))
          Equal.trans(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, s, List.append(&2, Bool, Slot.ballots(), r)), State.get(~Q, s1, List.append(&2, Bool, Slot.ballots(), r)), State.get(~Q, s2, List.append(&2, Bool, Slot.ballots(), r)), State.add_data_ballots_at.of(~Q, ~same, s, k, ws, r, State.get(~Q, s, k), s1)({==})(e1), State.add_datas_ballots_at(~Q, ~same, rest, s1, r, s2)(e2)))

# a take of a ledger that holds no ballot reads as before in each slot of a
# ballot
def State.take_ballots_at(
  ~Q: Data,
  +s: State(Q),
  t: State(Q),
  r: List<&2, Bool>
) -> {
  State.get(
    ~Q,
    t,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.take(~Q, s, t),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  +q = List.append(&2, Bool, Slot.ballots(), r)
  et =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.take(~Q, s, t), q),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~(x => y => x),
        State.get(~Q, s, q),
        State.get(~Q, t, q)
      ),
      Tries.Trie.get_union(~Cells.Cell<Entry<Q>>, ~(x => y => x), s, t, q)
    ): {State.get(~Q, s, q) == _: Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, t, q),
      None{},
      et
    ): {
      State.get(
        ~Q,
        s,
        q
      )
        == Shared.Maybe.join(
          ~Cells.Cell<Entry<Q>>,
          ~(x => y => x),
          State.get(~Q, s, q),
          _
        ): Maybe<&2, Cells.Cell<Entry<Q>>>
    }
    Tries.Trie.none_join(~Cells.Cell<Entry<Q>>, ~(x => y => x), State.get(~Q, s, q))

# a ledger with the data of t reads as before in each slot of a ballot
def State.with_data_ballots_at(
  ~Q: Data,
  s: State(Q),
  t: State(Q),
  r: List<&2, Bool>
) -> {
  State.get(
    ~Q,
    s,
    List.append(&2, Bool, Slot.ballots(), r)
  )
    == State.get(
      ~Q,
      State.with_data(~Q, s, t),
      List.append(&2, Bool, Slot.ballots(), r)
    ): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  Equal.sym(
    Maybe<&2, Cells.Cell<Entry<Q>>>,
    State.get(~Q, State.with_data(~Q, s, t), List.append(&2, Bool, Slot.ballots(), r)),
    State.get(~Q, s, List.append(&2, Bool, Slot.ballots(), r)),
    State.with_data_other(~Q, s, t, List.append(&2, Bool, Slot.ballots(), r))({==})
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
