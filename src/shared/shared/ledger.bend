import Base
import ./shared/quorum.bend as Quorums
import ./shared/shared/cell.bend as Cells
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/seal.bend as Seals
import ./shared/shared/shared.bend as Shared
import ./shared/shared/trie.bend as Tries
import ./shared/text.bend as Texts

# Ledgers
# =======
# A ledger is what nodes replicate: requests, ballots and data, each in the
# slot that its own content names. A holder takes in what it lacks and never
# changes what it holds (State.take), so every ledger only grows, and holders
# of the same entries hold the same state, in any order and any number of
# times.
#
# A line is a store, or a line below it. Its owners cast one ballot each for
# the step at each round of each height; a step is what a majority of them
# cast in one round; it stays as the ledger grows (State.decide_grows). What
# a step means is the caller's: the ledger does not read a line's state.

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

# a request of a change, with its time; a ballot of a node; or data
type Entry<-Q: Data> is Data:
  Entry.Ask{id: Id, time: String, ask: Q}
  Entry.Vote{ballot: Ballot}
  Entry.Data{words: List<&2, U32>}

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

# the start of the slots of the ballots of the line c
def Slot.votes(c: Chain) -> List<&2, Bool>:
  False{} <> True{} <> Chain.key(c)

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

# the slot of the data whose hash is h
def Slot.data(h: Hashes.Hash) -> List<&2, Bool>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      True{}
        <> True{}
        <> True{}
        <> True{}
        <> List.append(
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
                  List.append(
                    &2,
                    Bool,
                    Word.key(f),
                    List.append(&2, Bool, Word.key(g), Word.key(i))
                  )
                )
              )
            )
          )
        )

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

# the ballot of a cell of a bucket: a vote, void when it holds anything else,
# none when it is empty
def Entry.ballot(~Q: Data, m: Maybe<&2, Cells.Cell<Entry<Q>>>) -> Maybe<&2, Cells.Cell<Vote>>:
  match m:
    case None{}:
      None{}
    case Some{Cells.One{Entry.Vote{b}}}:
      Some{Ballot.cell(Ballot.vote(b))}
    case Some{c}:
      Some{Cells.Many{}}

# the ballots of the nodes ms in the bucket b, each read once
def Bucket.ballots(
  ~Q: Data,
  +b: State(Q),
  ms: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Vote>>>:
  match ms:
    case Nil{}:
      []
    case Con{m, r}:
      Entry.ballot(~Q, State.get(~Q, b, Slot.ballot(m))) <> Bucket.ballots(~Q, b, r)

# what the ballots of ms in the bucket b decide
def Bucket.decide(~Q: Data, b: State(Q), ms: List<&2, String>) -> Maybe<&2, Vote>:
  Quorums.Quorum.major(~Vote, ~Vote.is_eq, Bucket.ballots(~Q, b, ms))

# the bucket of the place w in s
def State.bucket(~Q: Data, s: State(Q), w: Where) -> State(Q):
  match w:
    case Where{c, h, r}:
      State.under(~Q, s, Slot.bucket(c, h, r))

# the step that the owners ms decide at the place w of s, if they did
def State.decide(~Q: Data, s: State(Q), w: Where, ms: List<&2, String>) -> Maybe<&2, Vote>:
  Bucket.decide(~Q, State.bucket(~Q, s, w), ms)

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

# the last vote in the cell m of a pass, if it holds a pass
def Passed.of(~Q: Data, m: Maybe<&2, Cells.Cell<Entry<Q>>>) -> Maybe<&2, Maybe<&2, Last>>:
  match m:
    case Some{Cells.One{Entry.Vote{b}}}:
      Ballot.pass(b)
    case x:
      None{}

# the last vote that the node n named when it passed to the place w, if s
# holds its pass
def State.passed(~Q: Data, s: State(Q), w: Where, n: String) -> Maybe<&2, Maybe<&2, Last>>:
  Passed.of(~Q, State.get(~Q, s, Slot.pass(w, n)))

# Laws
# ----

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

# the ballot of one entry is kept as itself
def Ballot.refl(
  ~Q: Data,
  e: Entry<Q>
) -> {
  Cells.Cell.keeps(
    ~Vote,
    ~Vote.is_eq,
    Entry.ballot(~Q, Some{Cells.One{e}}),
    Entry.ballot(~Q, Some{Cells.One{e}})
  )
    == True{}: Bool
}:
  match e:
    case Entry.Vote{v}:
      Ballot.cell_refl(Ballot.vote(v))
    case Entry.Ask{i, t, q}:
      {==}
    case Entry.Data{d}:
      {==}

# a cell kept from many gives a void ballot
def Ballot.many_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  b: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), Some{Cells.Many{}}, b) == True{}: Bool
} -> {
  Cells.Cell.keeps(~Vote, ~Vote.is_eq, Some{Cells.Many{}}, Entry.ballot(~Q, b)) == True{}: Bool
}:
  match b:
    case Some{Cells.Many{}}:
      k => {==}
    case Some{Cells.One{e}}:
      k => Empty.absurd(
        {
          Cells.Cell.keeps(
            ~Vote,
            ~Vote.is_eq,
            Some{Cells.Many{}},
            Entry.ballot(~Q, Some{Cells.One{e}})
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(k)
      )
    case None{}:
      k => Empty.absurd(
        {Cells.Cell.keeps(~Vote, ~Vote.is_eq, Some{Cells.Many{}}, None{}) == True{}: Bool},
        Shared.Bool.false_ne_true(k)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the ballot of a cell is kept in a cell that keeps it
def Ballot.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Maybe<&2, Cells.Cell<Entry<Q>>>,
  b: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), a, b) == True{}: Bool
} -> {
  Cells.Cell.keeps(~Vote, ~Vote.is_eq, Entry.ballot(~Q, a), Entry.ballot(~Q, b)) == True{}: Bool
}:
  match a:
    case None{}:
      k => {==}
    case Some{Cells.One{+e}}:
      k =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          b,
          Some{Cells.One{e}},
          Cells.Cell.keeps_value(
            ~Entry<Q>,
            ~Entry.is_eq(~Q, ~same),
            ~Entry.laws(~Q, ~same, ~laws),
            e,
            b
          )(k)
        ): {
          Cells.Cell.keeps(
            ~Vote,
            ~Vote.is_eq,
            Entry.ballot(~Q, Some{Cells.One{e}}),
            Entry.ballot(~Q, _)
          )
            == True{}: Bool
        }
        Ballot.refl(~Q, e)
    case Some{Cells.Many{}}:
      k => Ballot.many_kept(~Q, ~same, b, k)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the ballots of ms in the bucket at p are kept in a state that grows
def Ballots.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +p: List<&2, Bool>,
  ms: List<&2, String>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Shared.List.all2(
    ~Maybe<&2, Cells.Cell<Vote>>,
    ~Maybe<&2, Cells.Cell<Vote>>,
    ~Cells.Cell.keeps(~Vote, ~Vote.is_eq),
    Bucket.ballots(~Q, State.under(~Q, s, p), ms),
    Bucket.ballots(~Q, State.under(~Q, s2, p), ms)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{m, +r}:
      +k = Slot.ballot(m)
      +b1 = State.get(~Q, State.under(~Q, s, p), k)
      +b2 = State.get(~Q, State.under(~Q, s2, p), k)
      Shared.Bool.and_both(
        Cells.Cell.keeps(~Vote, ~Vote.is_eq, Entry.ballot(~Q, b1), Entry.ballot(~Q, b2)),
        Shared.List.all2(
          ~Maybe<&2, Cells.Cell<Vote>>,
          ~Maybe<&2, Cells.Cell<Vote>>,
          ~Cells.Cell.keeps(~Vote, ~Vote.is_eq),
          Bucket.ballots(~Q, State.under(~Q, s, p), r),
          Bucket.ballots(~Q, State.under(~Q, s2, p), r)
        )
      )(Ballot.grows(~Q, ~same, ~laws, b1, b2)(
          %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.under(~Q, s, p), k), State.get(~Q, s, List.append(&2, Bool, p, k)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s, p, k)):
            {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), _, b2) == True{}: Bool}
          %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, State.under(~Q, s2, p), k), State.get(~Q, s2, List.append(&2, Bool, p, k)), Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s2, p, k)):
            {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), State.get(~Q, s, List.append(&2, Bool, p, k)), _) == True{}: Bool}
          Tries.Trie.keeps_get(~Cells.Cell<Entry<Q>>, ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, s2, List.append(&2, Bool, p, k))(gr)))(
        Ballots.grows(~Q, ~same, ~laws, s, s2, p, r, gr)
      )

# what the owners decide at a place stays decided as the state grows: a step
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
    case Where{c, h, r}:
      +p = Slot.bucket(c, h, r)
      b1 = Bucket.ballots(~ty, State.under(~ty, s, p), ms)
      b2 = Bucket.ballots(~ty, State.under(~ty, s2, p), ms)
      +gr => hd =>
        Quorums.Quorum.major_kept(
          ~Vote,
          ~Vote.is_eq,
          ~Vote.laws(),
          b1,
          b2,
          v
        )(Ballots.grows(~ty, ~same, ~laws, s, s2, p, ms, gr))(hd)

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
  gr => eg =>
    Cells.Cell.keeps_value(
      ~Entry<ty>,
      ~Entry.is_eq(~ty, ~same),
      ~Entry.laws(~ty, ~same, ~laws),
      e,
      State.get(~ty, s2, k)
    )(
      %eg: {Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same), _, State.get(~ty, s2, k)) == True{}: Bool}
      Tries.Trie.keeps_get(~Cells.Cell<Entry<ty>>, ~Cells.Cell.keeps(~Entry<ty>, ~Entry.is_eq(~ty, ~same)), ~Cells.Cell.none_kept(~Entry<ty>, ~Entry.is_eq(~ty, ~same)), s, s2, k)(gr))

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
