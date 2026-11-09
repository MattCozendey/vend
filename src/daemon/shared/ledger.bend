import Base
import ../../shared.bend as Shared
import ./shared/quorum.bend as Quorums
import ./shared/shared/code.bend as Codes
import ./shared/shared/cell.bend as Cells
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/trie.bend as Tries
import ./shared/text.bend as Texts

# Ledgers
# =======
# A ledger holds entries in slots: the requests that writers make, the votes
# of nodes, and facts that say where a decision is. Ledgers sync by joining
# what they hold, so every ledger that took in the same entries holds the
# same state, in any order and any number of times.
#
# A line (a store's root, or a line that its root made) is a list of epochs;
# the owners of an epoch are fixed. A step of an epoch is the decision of its
# owners' ballots in the bucket of its height (Quorum.decide). Heights and
# epochs are 32-bit, so a bucket is one key away: no read walks a line.
#
# Facts (where a request was decided, where an epoch began, where a line was
# made) are written by the nodes that see a decision, and checked against the
# bucket that they name whenever they are read, so a wrong fact is ignored,
# never believed.
#
# What a change Q means is the caller's. A ledger reads of a change only its
# View, compares changes with same, and asks judge for a verdict.

# Names
# -----

# a request: the writer that made it and the ID that the writer gave it. A
# version is the request that made it.
type Id is Data:
  Id{writer: String, request: String}

# a line: the request that started its store, and its key below the store's
# root line (none for the root). Keys below one root are prefix-free.
type Chain is Data:
  Chain{root: Id, sub: Maybe<&2, List<&2, Bool>>}

# what a ledger reads of a change: it starts a store with its first owners;
# or it changes the line on, gives it owners (if any: a new epoch) and, on a
# root, makes the line below it of that key (if any)
type View is Data:
  View.Root{owners: List<&2, String>}
  View.On{chain: Chain, owners: Maybe<&2, List<&2, String>>, makes: Maybe<&2, List<&2, Bool>>}

# a vote for a request, whose change has the view: its owners take it, or
# refuse it as stale, and the hash of what the line holds after it (result)
type Vote is Data:
  Vote{id: Id, takes: Bool, view: View, result: Maybe<&2, Hashes.Hash>}

# what a judge says of a request: take it or refuse it, and the hash of what
# the line holds after
type Verdict is Data:
  Verdict{takes: Bool, result: Maybe<&2, Hashes.Hash>, data: List<&2, List<&2, U32>>}

# a place on a line: an epoch and a height in it
type Where is Data:
  Where{chain: Chain, epoch: U32, height: U32}

# a request of a change, with its time; a vote of a node; or a fact
type Entry<-Q: Data> is Data:
  Entry.Ask{id: Id, time: String, ask: Q}
  Entry.Vote{vote: Vote}
  Entry.At{at: Where}
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
) -> {
  Id.code.read(Id.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Id>>
}:
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


# Keys
# ----

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

# the key of an epoch or a height: its 32 bits, highest first, so keys are in
# the order of numbers
def Word.key(x: U32) -> List<&2, Bool>:
  Tries.Trie.word(32n, x)

# the number of a key of 32 bits, highest first, after acc
def Word.of_key(k: List<&2, Bool>, acc: U32) -> U32:
  match k:
    case Nil{}:
      acc
    case Con{False{}, r}:
      Word.of_key(r, U32.shl(acc))
    case Con{True{}, r}:
      Word.of_key(r, U32.or(U32.shl(acc), 1))

# the slot of the request i
def Slot.ask(i: Id) -> List<&2, Bool>:
  False{} <> False{} <> Id.key(i)

# the start of the slots of the votes of the epoch e of the line c
def Slot.votes(c: Chain, e: U32) -> List<&2, Bool>:
  False{} <> True{} <> List.append(&2, Bool, Chain.key(c), Word.key(e))

# the start of the slots of the bucket of the height h, in the epoch e of c
def Slot.bucket(c: Chain, e: U32, h: U32) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.votes(c, e), Word.key(h))

# the slot of the node n's ballot in a bucket, below the bucket
def Slot.ballot(n: String) -> List<&2, Bool>:
  Tries.Trie.text(n)

# the slot of the node n's ballot at the place w
def Slot.vote(w: Where, n: String) -> List<&2, Bool>:
  match w:
    case Where{c, e, h}:
      List.append(&2, Bool, Slot.bucket(c, e, h), Slot.ballot(n))

# the slot of the fact where the request i was decided
def Slot.where(i: Id) -> List<&2, Bool>:
  True{} <> False{} <> Id.key(i)

# the start of the slots of the facts where the epochs of the line c began
def Slot.epochs(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> False{} <> Chain.key(c)

# the slot of the fact where the epoch e of the line c began
def Slot.epoch(c: Chain, e: U32) -> List<&2, Bool>:
  List.append(&2, Bool, Slot.epochs(c), Word.key(e))

# the slot of the fact where the line c was made
def Slot.made(c: Chain) -> List<&2, Bool>:
  True{} <> True{} <> True{} <> False{} <> Chain.key(c)

# the slot of the data whose hash is h
def Slot.data(h: Hashes.Hash) -> List<&2, Bool>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      True{} <> True{} <> True{} <> True{} <> List.append(&2, Bool, Word.key(a), Word.key(b))

# Equality
# --------

# a and b are the same request
def Id.is_eq(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same keys below a root
def Sub.is_eq(a: Maybe<&2, List<&2, Bool>>, b: Maybe<&2, List<&2, Bool>>) -> Bool:
  Shared.Maybe.is_eq(~List<&2, Bool>, ~Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq), a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same line
def Chain.is_eq(a: Chain, b: Chain) -> Bool:
  match a b:
    case Chain{i1, k1} Chain{i2, k2}:
      Bool.and(Id.is_eq(i1, i2), Sub.is_eq(k1, k2))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a and b are the same owners
def Owners.is_eq(a: List<&2, String>, b: List<&2, String>) -> Bool:
  Shared.List.is_eq(~String, ~String.eq, a, b)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same views
def View.is_eq(a: View, b: View) -> Bool:
  match a b:
    case View.Root{x} View.Root{y}:
      Owners.is_eq(x, y)
    case View.On{c1, o1, m1} View.On{c2, o2, m2}:
      Bool.and(
        Chain.is_eq(c1, c2),
        Bool.and(Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq, o1, o2), Sub.is_eq(m1, m2))
      )
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a and b are the same vote
def Vote.is_eq(a: Vote, b: Vote) -> Bool:
  match a b:
    case Vote{i1, k1, v1, r1} Vote{i2, k2, v2, r2}:
      Bool.and(
        Id.is_eq(i1, i2),
        Bool.and(
          Shared.Bool.is_eq(k1, k2),
          Bool.and(View.is_eq(v1, v2), Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, r1, r2))
        )
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a and b are the same place
def Where.is_eq(a: Where, b: Where) -> Bool:
  match a b:
    case Where{c1, e1, h1} Where{c2, e2, h2}:
      Bool.and(Chain.is_eq(c1, c2), Bool.and(U32.is_eq(e1, e2), U32.is_eq(h1, h2)))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.Ask{i1, t1, q1} Entry.Ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.Vote{v1} Entry.Vote{v2}:
      Vote.is_eq(v1, v2)
    case Entry.At{w1} Entry.At{w2}:
      Where.is_eq(w1, w2)
    case Entry.Data{d1} Entry.Data{d2}:
      Shared.List.is_eq(~U32, ~U32.is_eq, d1, d2)
    case _ _:
      False{}

# Laws of equality
# ----------------

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

# the laws of Sub.is_eq
def Sub.laws() -> Shared.Eq.Laws(Maybe<&2, List<&2, Bool>>, Sub.is_eq):
  Shared.Maybe.laws(
    ~List<&2, Bool>,
    ~Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq),
    ~Shared.List.laws(~Bool, ~Shared.Bool.is_eq, ~Shared.Bool.laws())
  )

# the laws of Owners.is_eq
def Owners.laws() -> Shared.Eq.Laws(List<&2, String>, Owners.is_eq):
  Shared.List.laws(~String, ~String.eq, ~Texts.String.laws())

# Chain.is_eq is True for a line and itself
def Chain.is_eq_refl(a: Chain) -> {Chain.is_eq(a, a) == True{}: Bool}:
  match a:
    case Chain{+i, +k}:
      Shared.Bool.and_both(
        Id.is_eq(i, i),
        Sub.is_eq(k, k)
      )(Id.is_eq_refl(i))(Shared.Eq.refl(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), k))

# Chain.is_eq is True only for equal lines
def Chain.is_eq_sound(a: Chain, b: Chain) -> {Chain.is_eq(a, b) == True{}: Bool} -> {a == b: Chain}:
  match a b:
    case Chain{+i1, +k1} Chain{+i2, +k2}:
      +h =>
        +x = Id.is_eq(i1, i2)
        +y = Sub.is_eq(k1, k2)
        Eq.both(
          Id,
          Maybe<&2, List<&2, Bool>>,
          Chain,
          p => q => Chain{p, q},
          i1,
          i2,
          k1,
          k2,
          Id.is_eq_sound(i1, i2)(Shared.Bool.and_true_left(x, y)(h)),
          Shared.Eq.sound(
            ~Maybe<&2, List<&2, Bool>>,
            ~Sub.is_eq,
            Sub.laws(),
            k1,
            k2
          )(Shared.Bool.and_true_right(x, y)(h))
        )

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

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# View.is_eq is True for a view and itself
def View.is_eq_refl(a: View) -> {View.is_eq(a, a) == True{}: Bool}:
  match a:
    case View.Root{x}:
      Shared.Eq.refl(~List<&2, String>, ~Owners.is_eq, Owners.laws(), x)
    case View.On{+c, +o, +m}:
      +mo = Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq, o, o)
      Shared.Bool.and_both(
        Chain.is_eq(c, c),
        Bool.and(mo, Sub.is_eq(m, m))
      )(
        Chain.is_eq_refl(c)
      )(
        Shared.Bool.and_both(
          mo,
          Sub.is_eq(m, m)
        )(
          Shared.Maybe.is_eq_refl(~List<&2, String>, ~Owners.is_eq, ~Owners.laws(), o)
        )(Shared.Eq.refl(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), m))
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# View.is_eq is True only for equal views
def View.is_eq_sound(a: View, b: View) -> {View.is_eq(a, b) == True{}: Bool} -> {a == b: View}:
  match a b:
    case View.Root{x} View.Root{y}:
      h =>
        %Shared.Eq.sound(
          ~List<&2, String>,
          ~Owners.is_eq,
          Owners.laws(),
          x,
          y
        )(h): {View.Root{x} == View.Root{_}: View}
        {==}
    case View.On{+c1, +o1, +m1} View.On{+c2, +o2, +m2}:
      +h =>
        +x = Chain.is_eq(c1, c2)
        +mo = Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq, o1, o2)
        +mm = Sub.is_eq(m1, m2)
        +r = Shared.Bool.and_true_right(x, Bool.and(mo, mm))(h)
        Eq.three(
          Chain,
          Maybe<&2, List<&2, String>>,
          Maybe<&2, List<&2, Bool>>,
          View,
          p => q => w => View.On{p, q, w},
          c1,
          c2,
          o1,
          o2,
          m1,
          m2,
          Chain.is_eq_sound(c1, c2)(Shared.Bool.and_true_left(x, Bool.and(mo, mm))(h)),
          Shared.Eq.sound(
            ~Maybe<&2, List<&2, String>>,
            ~Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq),
            Shared.Maybe.laws(~List<&2, String>, ~Owners.is_eq, ~Owners.laws()),
            o1,
            o2
          )(Shared.Bool.and_true_left(mo, mm)(r)),
          Shared.Eq.sound(
            ~Maybe<&2, List<&2, Bool>>,
            ~Sub.is_eq,
            Sub.laws(),
            m1,
            m2
          )(Shared.Bool.and_true_right(mo, mm)(r))
        )
    case View.Root{x} View.On{c, o, m}:
      h => Empty.absurd({View.Root{x} == View.On{c, o, m}: View}, Shared.Bool.false_ne_true(h))
    case View.On{c, o, m} View.Root{x}:
      h => Empty.absurd({View.On{c, o, m} == View.Root{x}: View}, Shared.Bool.false_ne_true(h))

# Vote.is_eq is True for a vote and itself
def Vote.is_eq_refl(a: Vote) -> {Vote.is_eq(a, a) == True{}: Bool}:
  match a:
    case Vote{+i, +k, +v, +r}:
      +bk = Shared.Bool.is_eq(k, k)
      +bv = View.is_eq(v, v)
      +br = Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, r, r)
      Shared.Bool.and_both(
        Id.is_eq(i, i),
        Bool.and(bk, Bool.and(bv, br))
      )(
        Id.is_eq_refl(i)
      )(
        Shared.Bool.and_both(
          bk,
          Bool.and(bv, br)
        )(
          Shared.Bool.is_eq_refl(k)
        )(
          Shared.Bool.and_both(
            bv,
            br
          )(
            View.is_eq_refl(v)
          )(Shared.Maybe.is_eq_refl(~Hashes.Hash, ~Hashes.Hash.is_eq, ~Hashes.Hash.laws(), r))
        )
      )

# Vote.is_eq is True only for equal votes
def Vote.is_eq_sound(a: Vote, b: Vote) -> {Vote.is_eq(a, b) == True{}: Bool} -> {a == b: Vote}:
  match a b:
    case Vote{+i1, +k1, +v1, +r1} Vote{+i2, +k2, +v2, +r2}:
      +h =>
        +x = Id.is_eq(i1, i2)
        +y = Shared.Bool.is_eq(k1, k2)
        +z = View.is_eq(v1, v2)
        +w = Shared.Maybe.is_eq(~Hashes.Hash, ~Hashes.Hash.is_eq, r1, r2)
        +ra = Shared.Bool.and_true_right(x, Bool.and(y, Bool.and(z, w)))(h)
        +rb = Shared.Bool.and_true_right(y, Bool.and(z, w))(ra)
        %Id.is_eq_sound(i1, i2)(Shared.Bool.and_true_left(x, Bool.and(y, Bool.and(z, w)))(h)):
          {Vote{i1, k1, v1, r1} == Vote{_, k2, v2, r2}: Vote}
        %Shared.Bool.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(y, Bool.and(z, w))(ra)):
          {Vote{i1, k1, v1, r1} == Vote{i1, _, v2, r2}: Vote}
        %View.is_eq_sound(v1, v2)(Shared.Bool.and_true_left(z, w)(rb)):
          {Vote{i1, k1, v1, r1} == Vote{i1, k1, _, r2}: Vote}
        %Shared.Maybe.is_eq_sound(
          ~Hashes.Hash,
          ~Hashes.Hash.is_eq,
          x => y => Hashes.Hash.is_eq_sound(x, y),
          r1,
          r2
        )(Shared.Bool.and_true_right(z, w)(rb)):
          {Vote{i1, k1, v1, r1} == Vote{i1, k1, v1, _}: Vote}
        {==}

# the laws of Vote.is_eq
def Vote.laws() -> Shared.Eq.Laws(Vote, Vote.is_eq):
  (a => Vote.is_eq_refl(a), a => b => Vote.is_eq_sound(a, b))

# Where.is_eq is True for a place and itself
def Where.is_eq_refl(a: Where) -> {Where.is_eq(a, a) == True{}: Bool}:
  match a:
    case Where{+c, +e, +h}:
      +ue = U32.is_eq(e, e)
      Shared.Bool.and_both(
        Chain.is_eq(c, c),
        Bool.and(ue, U32.is_eq(h, h))
      )(
        Chain.is_eq_refl(c)
      )(
        Shared.Bool.and_both(
          ue,
          U32.is_eq(h, h)
        )(Shared.U32.is_eq_refl(e))(Shared.U32.is_eq_refl(h))
      )

# Where.is_eq is True only for equal places
def Where.is_eq_sound(a: Where, b: Where) -> {Where.is_eq(a, b) == True{}: Bool} -> {a == b: Where}:
  match a b:
    case Where{+c1, +e1, +h1} Where{+c2, +e2, +h2}:
      +q =>
        +x = Chain.is_eq(c1, c2)
        +y = U32.is_eq(e1, e2)
        +z = U32.is_eq(h1, h2)
        +r = Shared.Bool.and_true_right(x, Bool.and(y, z))(q)
        Eq.three(
          Chain,
          U32,
          U32,
          Where,
          p => u => w => Where{p, u, w},
          c1,
          c2,
          e1,
          e2,
          h1,
          h2,
          Chain.is_eq_sound(c1, c2)(Shared.Bool.and_true_left(x, Bool.and(y, z))(q)),
          Shared.U32.is_eq_sound(e1, e2)(Shared.Bool.and_true_left(y, z)(r)),
          Shared.U32.is_eq_sound(h1, h2)(Shared.Bool.and_true_right(y, z)(r))
        )

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
      Vote.is_eq_refl(v)
    case Entry.At{w}:
      Where.is_eq_refl(w)
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
        %Vote.is_eq_sound(v1, v2)(h): {Entry.Vote{v1} == Entry.Vote{_}: Entry<Q>}
        {==}
    case Entry.At{w1} Entry.At{w2}:
      h =>
        %Where.is_eq_sound(w1, w2)(h): {Entry.At{w1} == Entry.At{_}: Entry<Q>}
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
    case Entry.Ask{i, t, q} Entry.At{w}:
      h => Empty.absurd({Entry.Ask{i, t, q} == Entry.At{w}: Entry<Q>}, Shared.Bool.false_ne_true(h))
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
    case Entry.Vote{v} Entry.At{w}:
      h => Empty.absurd({Entry.Vote{v} == Entry.At{w}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Vote{v} Entry.Data{d}:
      h => Empty.absurd({Entry.Vote{v} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.At{w} Entry.Ask{i, t, q}:
      h => Empty.absurd({Entry.At{w} == Entry.Ask{i, t, q}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.At{w} Entry.Vote{v}:
      h => Empty.absurd({Entry.At{w} == Entry.Vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.At{w} Entry.Data{d}:
      h => Empty.absurd({Entry.At{w} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Data{d} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Data{d} Entry.Vote{v}:
      h => Empty.absurd({Entry.Data{d} == Entry.Vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.At{w}:
      h => Empty.absurd({Entry.Data{d} == Entry.At{w}: Entry<Q>}, Shared.Bool.false_ne_true(h))

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

# the place in the entry m, when it is a fact
def Where.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Where>:
  match m:
    case Some{Entry.At{w}}:
      Some{w}
    case _:
      None{}

# Buckets
# -------

# the ballot of a cell of a bucket: a vote, void when it holds anything else,
# none when it is empty
def Entry.ballot(~Q: Data, m: Maybe<&2, Cells.Cell<Entry<Q>>>) -> Maybe<&2, Cells.Cell<Vote>>:
  match m:
    case None{}:
      None{}
    case Some{Cells.One{Entry.Vote{v}}}:
      Some{Cells.One{v}}
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
  Quorums.Quorum.decide_fast(~Vote, ~Vote.is_eq, Bucket.ballots(~Q, b, ms))

# the bucket b of owners ms is decided
def Bucket.decided(~Q: Data, ms: List<&2, String>, b: State(Q)) -> Bool:
  Maybe.is_some(&2, Vote, Bucket.decide(~Q, b, ms))

# the bucket of the place w in s
def State.bucket(~Q: Data, s: State(Q), w: Where) -> State(Q):
  match w:
    case Where{c, e, h}:
      State.under(~Q, s, Slot.bucket(c, e, h))

# what the owners ms decide at the place w of s
def State.decide(~Q: Data, s: State(Q), w: Where, ms: List<&2, String>) -> Maybe<&2, Vote>:
  Bucket.decide(~Q, State.bucket(~Q, s, w), ms)

# Epochs
# ------
# Each read is a chain of reads (Maybe.then, Maybe.when), so that a read that
# a sync keeps is built of reads that it keeps (Maybe.bind_kept).

# the owners of a view that starts a store
def Root.owners.view(v: View) -> Maybe<&2, List<&2, String>>:
  match v:
    case View.Root{ms}:
      Some{ms}
    case _:
      None{}

# the owners of the request a, when it starts a store
def Root.owners.ask(~Q: Data, ~view: Q -> View, a: Asked<Q>) -> Maybe<&2, List<&2, String>>:
  match a:
    case Asked{t, q}:
      Root.owners.view(view(q))

# the owners of the root line of r: those of the request that starts it
def Root.owners(~Q: Data, ~view: Q -> View, s: State(Q), r: Id) -> Maybe<&2, List<&2, String>>:
  Maybe.bind(
    &2,
    Asked<Q>,
    List<&2, String>,
    State.asked(~Q, s, r),
    a => Root.owners.ask(~Q, ~view, a)
  )

# the owners that the vote v gives the line c, when it takes a request of c
# that gives it owners
def Owners.of(c: Chain, v: Vote) -> Maybe<&2, List<&2, String>>:
  match v:
    case Vote{i, True{}, View.On{c2, Some{os}, mk}, r}:
      Shared.Maybe.when(List<&2, String>, Chain.is_eq(c2, c), u => Some{os})
    case _:
      None{}

# the owners of the epoch after e of c, whose owners are ms, from the fact w
# where it began: the owners that the step there gives
def Epoch.at(
  ~Q: Data,
  s: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>,
  w: Where
) -> Maybe<&2, List<&2, String>>:
  match w:
    case Where{c2, e2, h}:
      Shared.Maybe.when(
        List<&2, String>,
        Bool.and(Chain.is_eq(c2, c), U32.is_eq(e2, e)),
        u => Maybe.bind(
          &2,
          Vote,
          List<&2, String>,
          State.decide(~Q, s, Where{c, e, h}, ms),
          v => Owners.of(c, v)
        )
      )

# the owners of the epoch after e of c, whose owners are ms
def Epoch.next(
  ~Q: Data,
  +s: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>
) -> Maybe<&2, List<&2, String>>:
  Maybe.bind(
    &2,
    Where,
    List<&2, String>,
    Where.of(~Q, State.entry(~Q, s, Slot.epoch(c, U32.inc(e)))),
    w => Epoch.at(~Q, s, c, e, ms, w)
  )

# the owners of the epoch n after cur of c, whose owners are m
def Epoch.up(
  ~Q: Data,
  n: Nat,
  +s: State(Q),
  +c: Chain,
  +cur: U32,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, List<&2, String>>:
  match n:
    case 0n:
      m
    case 1n+p:
      Maybe.bind(
        &2,
        List<&2, String>,
        List<&2, String>,
        m,
        ms => Epoch.up(~Q, p, s, c, U32.inc(cur), Epoch.next(~Q, s, c, cur, ms))
      )

# the owners of the epoch e of the root line of r
def Root.at(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +r: Id,
  e: U32
) -> Maybe<&2, List<&2, String>>:
  Epoch.up(~Q, U32.to_nat(e), s, Chain{r, None{}}, 0, Root.owners(~Q, ~view, s, r))

# the owners ms, when the vote v makes the line of the key k
def Made.vote(k: List<&2, Bool>, ms: List<&2, String>, v: Vote) -> Maybe<&2, List<&2, String>>:
  match v:
    case Vote{i, True{}, View.On{c, o, Some{k2}}, r}:
      Shared.Maybe.when(
        List<&2, String>,
        Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, k2, k),
        u => Some{ms}
      )
    case _:
      None{}

# the first owners of the line of the key k below the root of r, from the
# fact w where it was made: the owners of the root's epoch there
def Made.at(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +r: Id,
  k: List<&2, Bool>,
  w: Where
) -> Maybe<&2, List<&2, String>>:
  match w:
    case Where{+c2, +e, h}:
      Shared.Maybe.when(
        List<&2, String>,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Maybe.bind(
          &2,
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          +ms => Maybe.bind(
            &2,
            Vote,
            List<&2, String>,
            State.decide(~Q, s, Where{c2, e, h}, ms),
            v => Made.vote(k, ms, v)
          )
        )
      )

# the owners of the first epoch of the line c
def Line.first(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, List<&2, String>>:
  match c:
    case Chain{r, None{}}:
      Root.owners(~Q, ~view, s, r)
    case Chain{+r, Some{+k}}:
      Maybe.bind(
        &2,
        Where,
        List<&2, String>,
        Where.of(~Q, State.entry(~Q, s, Slot.made(Chain{r, Some{k}}))),
        w => Made.at(~Q, ~view, s, r, k, w)
      )

# the vote that made the line of the key k below the root of r, from the fact
# w where it was made
def Made.vote_at(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +r: Id,
  k: List<&2, Bool>,
  w: Where
) -> Maybe<&2, Vote>:
  match w:
    case Where{+c2, +e, h}:
      Shared.Maybe.when(
        Vote,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Maybe.bind(
          &2,
          List<&2, String>,
          Vote,
          Root.at(~Q, ~view, s, r, e),
          +ms => Maybe.bind(
            &2,
            Vote,
            Vote,
            State.decide(~Q, s, Where{c2, e, h}, ms),
            +v => Maybe.bind(&2, List<&2, String>, Vote, Made.vote(k, ms, v), u => Some{v})
          )
        )
      )

# the owners of the epoch e of the line c
def Line.owners(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: Chain,
  e: U32
) -> Maybe<&2, List<&2, String>>:
  Epoch.up(~Q, U32.to_nat(e), s, c, 0, Line.first(~Q, ~view, s, c))

# the epoch of a line now, and its owners
type Now is Data:
  Now{epoch: U32, owners: List<&2, String>}

# the epoch of c now, from cur whose owners are ms and the owners m of the
# epoch after it; f epochs at most
def Epoch.last(
  ~Q: Data,
  f: Nat,
  +s: State(Q),
  +c: Chain,
  cur: U32,
  ms: List<&2, String>,
  m: Maybe<&2, List<&2, String>>
) -> Now:
  match f m:
    case 1n+p Some{+os}:
      +up = U32.inc(cur)
      Epoch.last(~Q, p, s, c, up, os, Epoch.next(~Q, s, c, up, os))
    case g w:
      Now{cur, ms}

# the epoch of the line c now, from the owners m of its first epoch
def Line.now.of(
  ~Q: Data,
  +s: State(Q),
  +c: Chain,
  m: Maybe<&2, List<&2, String>>
) -> Maybe<&2, Now>:
  match m:
    case Some{+ms}:
      Some{
        Epoch.last(
          ~Q,
          Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.epochs(c))),
          s,
          c,
          0,
          ms,
          Epoch.next(~Q, s, c, 0, ms)
        )
      }
    case None{}:
      None{}

# the epoch of the line c now, if the line exists: a step for each new epoch
def Line.now(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, Now>:
  Line.now.of(~Q, s, c, Line.first(~Q, ~view, s, c))

# Tips
# ----

# the end of a line: its epoch, its owners, the height that its owners vote
# at next, and the place of its last step in the epoch, if any
type Tip is Data:
  Tip{epoch: U32, owners: List<&2, String>, next: U32, last: Maybe<&2, Where>}

# the tip of the epoch e of c, whose owners are ms, from the highest key of a
# decided bucket m
def Tip.of(c: Chain, +e: U32, ms: List<&2, String>, m: Maybe<&2, List<&2, Bool>>) -> Tip:
  match m:
    case Some{k}:
      +h = Word.of_key(k, 0)
      Tip{e, ms, U32.inc(h), Some{Where{c, e, h}}}
    case None{}:
      Tip{e, ms, 0, None{}}

# the highest decided height of the epoch e of c, whose owners are ms
def Line.top(
  ~Q: Data,
  s: State(Q),
  c: Chain,
  e: U32,
  ms: List<&2, String>
) -> Maybe<&2, List<&2, Bool>>:
  Tries.Trie.top(
    ~Cells.Cell<Entry<Q>>,
    ~List<&2, String>,
    ~(os => b => Bucket.decided(~Q, os, b)),
    32n,
    State.under(~Q, s, Slot.votes(c, e)),
    ms
  )

# the tip of c, once the epoch now (m) is known
def Line.tip.of(~Q: Data, s: State(Q), +c: Chain, m: Maybe<&2, Now>) -> Maybe<&2, Tip>:
  match m:
    case Some{Now{+e, +ms}}:
      Some{Tip.of(c, e, ms, Line.top(~Q, s, c, e, ms))}
    case None{}:
      None{}

# the tip of the line c, if it exists: a descent of 32 heights, not a walk
def Line.tip(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, Tip>:
  Line.tip.of(~Q, s, c, Line.now(~Q, ~view, s, c))

# the vote of the last step of the line c before the tip, in the epoch e whose
# owners are ms and whose last step is at last; when e has none, the step where
# e began (the head that a judge reads)
def Line.head(
  ~Q: Data,
  ~view: Q -> View,
  +s: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>,
  last: Maybe<&2, Where>
) -> Maybe<&2, Vote>:
  match last:
    case Some{w}:
      State.decide(~Q, s, w, ms)
    case None{}:
      Shared.Maybe.when(
        Vote,
        Bool.not(U32.is_eq(e, 0)),
        u => Maybe.bind(
          &2,
          Where,
          Vote,
          Where.of(~Q, State.entry(~Q, s, Slot.epoch(c, e))),
          w => Maybe.bind(
            &2,
            List<&2, String>,
            Vote,
            Line.owners(~Q, ~view, s, c, U32.sub(e, 1)),
            ps => State.decide(~Q, s, w, ps)
          )
        )
      )

# Listings
# --------
# The steps of a line, in order, read from decided votes alone: in each epoch,
# the decided heights from 0 up to the first one that is not decided, or up to
# the first step that gives the line new owners; the next epoch has those
# owners. Decisions never change, so a listing only grows at its end.

# the start of the slots of the votes of the line c, in every epoch
def Slot.line_votes(c: Chain) -> List<&2, Bool>:
  False{} <> True{} <> Chain.key(c)

# the steps of the epoch e of c, whose owners are ms, from the height h, whose
# decision is m; f steps at most
def Epoch.steps(
  ~Q: Data,
  f: Nat,
  +s: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  h: U32,
  m: Maybe<&2, Vote>
) -> List<&2, Vote>:
  match f m:
    case 1n+p Some{+v}:
      +up = U32.inc(h)
      v
        <> Shared.Bool.when(
          List<&2, Vote>,
          Maybe.is_none(&2, List<&2, String>, Owners.of(c, v)),
          u => Epoch.steps(~Q, p, s, c, e, ms, up, State.decide(~Q, s, Where{c, e, up}, ms)),
          u => []
        )
    case g w:
      []

# the steps of the epoch e of c, whose owners are ms
def Epoch.list(~Q: Data, +s: State(Q), +c: Chain, +e: U32, +ms: List<&2, String>) -> List<&2, Vote>:
  Epoch.steps(
    ~Q,
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.votes(c, e))),
    s,
    c,
    e,
    ms,
    0,
    State.decide(~Q, s, Where{c, e, 0}, ms)
  )

# the owners that the last of the steps vs gives the line c, if any
def Steps.next(c: Chain, vs: List<&2, Vote>) -> Maybe<&2, List<&2, String>>:
  match vs:
    case Nil{}:
      None{}
    case Con{v, Nil{}}:
      Owners.of(c, v)
    case Con{v, Con{w, r}}:
      Steps.next(c, Con{w, r})

# the steps vs of the epoch cur of c, then those after, when the last of vs
# gives the owners m; f epochs at most
def Line.steps.go(
  ~Q: Data,
  f: Nat,
  +s: State(Q),
  +c: Chain,
  cur: U32,
  vs: List<&2, Vote>,
  m: Maybe<&2, List<&2, String>>
) -> List<&2, Vote>:
  match f m:
    case 1n+p Some{os}:
      +up = U32.inc(cur)
      +ws = Epoch.list(~Q, s, c, up, os)
      List.append(&2, Vote, vs, Line.steps.go(~Q, p, s, c, up, ws, Steps.next(c, ws)))
    case g w:
      vs

# the steps of the line c from its first epoch, whose steps are vs; f epochs
# at most
def Line.steps.of(~Q: Data, f: Nat, s: State(Q), +c: Chain, +vs: List<&2, Vote>) -> List<&2, Vote>:
  Line.steps.go(~Q, f, s, c, 0, vs, Steps.next(c, vs))

# the steps of the line c, in order (none: the line does not exist)
def Line.steps(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, List<&2, Vote>>:
  Maybe.bind(
    &2,
    List<&2, String>,
    List<&2, Vote>,
    Line.first(~Q, ~view, s, c),
    ms => Some{
      Line.steps.of(
        ~Q,
        Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
        s,
        c,
        Epoch.list(~Q, s, c, 0, ms)
      )
    }
  )

# Status
# ------

# the vote v, when it is for the request i
def Vote.for(i: Id, v: Vote) -> Maybe<&2, Vote>:
  match v:
    case Vote{+j, k, u, r}:
      Shared.Maybe.when(Vote, Id.is_eq(j, i), w => Some{Vote{j, k, u, r}})

# the vote that decided i at the place w, when the step there is for i
def Where.at(~Q: Data, ~view: Q -> View, +s: State(Q), i: Id, w: Where) -> Maybe<&2, Vote>:
  match w:
    case Where{+c, +e, h}:
      Maybe.bind(
        &2,
        List<&2, String>,
        Vote,
        Line.owners(~Q, ~view, s, c, e),
        ms => Maybe.bind(
          &2,
          Vote,
          Vote,
          State.decide(~Q, s, Where{c, e, h}, ms),
          v => Vote.for(i, v)
        )
      )

# the vote that decided the request i, when s holds where and it checks
def State.decided(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Maybe<&2, Vote>:
  Maybe.bind(
    &2,
    Where,
    Vote,
    Where.of(~Q, State.entry(~Q, s, Slot.where(i))),
    w => Where.at(~Q, ~view, s, i, w)
  )

# the place where the request i was decided, when s holds it and it checks
def State.place(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Maybe<&2, Where>:
  Maybe.bind(
    &2,
    Where,
    Where,
    Where.of(~Q, State.entry(~Q, s, Slot.where(i))),
    +w => Maybe.bind(&2, Vote, Where, Where.at(~Q, ~view, s, i, w), u => Some{w})
  )

# where a request is. Done: a step decided it, and took it or refused it as
# stale. Pending: no step decided it yet. Refused: it is contradicted. NotSeen:
# the ledger does not hold it.
type Status is Data:
  Status.Done{takes: Bool}
  Status.Pending{}
  Status.Refused{}
  Status.NotSeen{}

# the status of a request whose change has the view v, decided by the vote m
def Status.of.view(v: View, m: Maybe<&2, Vote>) -> Status:
  match v m:
    case View.Root{ms} w:
      Status.Done{True{}}
    case View.On{c, o, mk} Some{Vote{j, k, u, r}}:
      Status.Done{k}
    case View.On{c, o, mk} None{}:
      Status.Pending{}

# the status of the request i, whose cell is m
def Status.of(
  ~Q: Data,
  ~view: Q -> View,
  s: State(Q),
  i: Id,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> Status:
  match m:
    case None{}:
      Status.NotSeen{}
    case Some{Cells.Many{}}:
      Status.Refused{}
    case Some{Cells.One{Entry.Ask{j, t, q}}}:
      Status.of.view(view(q), State.decided(~Q, ~view, s, i))
    case Some{Cells.One{e}}:
      Status.NotSeen{}

# where the request i is
def State.status(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Status:
  Status.of(~Q, ~view, s, i, State.get(~Q, s, Slot.ask(i)))

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

# Changes
# -------

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

# s holds the words ws under their hash
def Data.has(~Q: Data, s: State(Q), +ws: List<&2, U32>) -> Bool:
  Shared.Maybe.is_eq(
    ~List<&2, U32>,
    ~Shared.List.is_eq(~U32, ~U32.is_eq),
    State.data(~Q, s, Hashes.Sha.hash(ws)),
    Some{ws}
  )

# s holds each of the words ds under their hash
def Data.holds(~Q: Data, +s: State(Q), ds: List<&2, List<&2, U32>>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{ws, r}:
      List.all.if(u => Data.holds(~Q, s, r), Data.has(~Q, s, ws))

# each of the words ds, put one after the other into s, finds its slot empty
# or holding it already: s holds no other words under their hashes
def Data.fresh(~Q: Data, ~same: Q -> Q -> Bool, ds: List<&2, List<&2, U32>>, +s: State(Q)) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{+ws, r}:
      List.all.if(
        u => Data.fresh(~Q, ~same, r, State.put_data(~Q, ~same, s, ws)),
        List.any.if(
          u => Data.has(~Q, s, ws),
          Maybe.is_none(&2, Cells.Cell<Entry<Q>>, State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))))
        )
      )

# the epoch of the place w
def Where.epoch(w: Where) -> U32:
  match w:
    case Where{c, e, h}:
      e

# Fact.put once the cell m of the slot is known
def Fact.put.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  w: Where,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case None{}:
      State.put(~Q, ~same, s, k, Entry.At{w})
    case Some{x}:
      s

# s with the fact w in the slot k, unless the slot holds something already
def Fact.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  w: Where
) -> State(Q):
  Fact.put.of(~Q, ~same, s, k, w, State.get(~Q, s, k))

# s with the facts of a step at w that takes (k) a request of the view v: where
# the epoch after it begins, when it gives owners; where the line that it
# makes was made
def Settle.view(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +w: Where,
  k: Bool,
  v: View
) -> State(Q):
  match k v:
    case True{} View.On{+c, Some{os}, mk}:
      Fact.put(~Q, ~same, s, Slot.epoch(c, U32.inc(Where.epoch(w))), w)
    case True{} View.On{Chain{r, b}, None{}, Some{key}}:
      Fact.put(~Q, ~same, s, Slot.made(Chain{r, Some{key}}), w)
    case x y:
      s

# s with the facts of the decision m at w
def Settle.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +w: Where,
  m: Maybe<&2, Vote>
) -> State(Q):
  match m:
    case Some{Vote{i, k, v, r}}:
      Settle.view(~Q, ~same, Fact.put(~Q, ~same, s, Slot.where(i), w), w, k, v)
    case None{}:
      s

# s with the facts of what the owners ms decide at w, if anything
def State.settle(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +w: Where,
  ms: List<&2, String>
) -> State(Q):
  Settle.of(~Q, ~same, s, w, State.decide(~Q, s, w, ms))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# the node n may vote at w, whose owners are ms: it is one, and has not voted
def Vote.may(~Q: Data, +n: String, s: State(Q), w: Where, ms: List<&2, String>) -> Bool:
  Bool.and(
    List.contains(~String, ~String.eq, ms, n),
    Maybe.is_none(&2, Cells.Cell<Entry<Q>>, State.get(~Q, s, Slot.vote(w, n)))
  )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the result of the vote m, if any (none: nothing)
def Vote.result_of(m: Maybe<&2, Vote>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case Some{Vote{i, k, v, r}}:
      r
    case None{}:
      None{}

# the verdict on the request q, whose view is v, after the step head: refused
# when it makes a line that exists (changing nothing), else judge's (none: wait)
def Vote.verdict(
  ~Q: Data,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +s: State(Q),
  q: Q,
  v: View,
  +head: Maybe<&2, Vote>
) -> Maybe<&2, Verdict>:
  match v:
    case View.On{Chain{r, b}, o, Some{m}}:
      Shared.Bool.when(
        Maybe<&2, Verdict>,
        Maybe.is_none(&2, List<&2, String>, Line.first(~Q, ~view, s, Chain{r, Some{m}})),
        u => judge(s, q, head),
        u => Some{Verdict{False{}, Vote.result_of(head), []}}
      )
    case w:
      judge(s, q, head)

# s with the vote for i of the view v (when held), with the verdict m (none:
# no vote)
def Vote.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  held: Bool,
  m: Maybe<&2, Verdict>,
  s: State(Q),
  k: List<&2, Bool>,
  i: Id,
  v: View
) -> State(Q):
  match held m:
    case True{} Some{Verdict{x, r, ds}}:
      State.put(~Q, ~same, State.put_datas(~Q, ~same, ds, s), k, Entry.Vote{Vote{i, x, v, r}})
    case h w:
      s

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# s after the node n votes for the request i of q, whose view v changes the
# line c, at the tip m of c, when it may; then the facts of what is decided
def Vote.cast(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  +s: State(Q),
  +c: Chain,
  +i: Id,
  q: Q,
  +v: View,
  m: Maybe<&2, Tip>
) -> State(Q):
  match m:
    case None{}:
      s
    case Some{Tip{+e, +ms, h, last}}:
      +w = {Where{c, e, h}: Where}
      State.settle(
        ~Q,
        ~same,
        Vote.put(
          ~Q,
          ~same,
          Bool.and(
            Vote.may(~Q, n, s, w, ms),
            Maybe.is_none(&2, Vote, State.decided(~Q, ~view, s, i))
          ),
          Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, ms, last)),
          s,
          Slot.vote(w, n),
          i,
          v
        ),
        w,
        ms
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# s after the node n votes for the request i of q, whose view is v
def Vote.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  +s: State(Q),
  i: Id,
  q: Q,
  v: View
) -> State(Q):
  match v:
    case View.Root{ms}:
      s
    case View.On{+c, o, mk}:
      Vote.cast(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        s,
        c,
        i,
        q,
        View.On{c, o, mk},
        Line.tip(~Q, ~view, s, c)
      )

# s after the node n took in the request i of q at the time t, whose cell in s
# is m: a request that s holds already changes nothing
def State.ask.fresh(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  s: State(Q),
  +i: Id,
  t: String,
  +q: Q,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> State(Q):
  match m:
    case Some{x}:
      s
    case None{}:
      Vote.ask(
        ~Q,
        ~same,
        ~view,
        ~judge,
        n,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
        i,
        q,
        view(q)
      )

# s, after the node n took in the request i of q at the time t: the request,
# and n's vote on it when n owns its line and judge gives a verdict
def State.ask(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  q: Q
) -> State(Q):
  State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, State.get(~Q, s, Slot.ask(i)))

# s, after the node n votes for each request of the cells cs
def Vote.all(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  cs: List<&2, Cells.Cell<Entry<Q>>>,
  +n: String,
  s: State(Q)
) -> State(Q):
  match cs:
    case Nil{}:
      s
    case Con{Cells.One{Entry.Ask{i, t, +q}}, r}:
      Vote.all(
        ~Q,
        ~same,
        ~view,
        ~judge,
        r,
        n,
        Vote.ask(~Q, ~same, ~view, ~judge, n, s, i, q, view(q))
      )
    case Con{c, r}:
      Vote.all(~Q, ~same, ~view, ~judge, r, n, s)

# s, after the node n votes, at the tip of each line that it owns, for each
# request that s holds: what a node does when a sync brings what a request
# waited for
def State.vote(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  +s: State(Q)
) -> State(Q):
  Vote.all(~Q, ~same, ~view, ~judge, Tries.Trie.values(Cells.Cell<Entry<Q>>, s), n, s)

# Syncs
# -----

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

# Kept reads
# ----------
# What a holder reads stays when its state grows (State.grows): a sync that
# agrees grows a state (State.grows_join), and so does a node's own write.

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
      Vote.is_eq_refl(v)
    case Entry.Ask{i, t, q}:
      {==}
    case Entry.At{w}:
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
    case Where{c, e, h}:
      +p = Slot.bucket(c, e, h)
      +b1 = Bucket.ballots(~ty, State.under(~ty, s, p), ms)
      +b2 = Bucket.ballots(~ty, State.under(~ty, s2, p), ms)
      +gr => hd =>
        %Equal.sym(
          Maybe<&2, Vote>,
          Quorums.Quorum.decide_fast(~Vote, ~Vote.is_eq, b2),
          Quorums.Quorum.decide(~Vote, ~Vote.is_eq, b2),
          Quorums.Quorum.decide_fast_eq(~Vote, ~Vote.is_eq, ~Vote.laws(), b2)
        ): {_ == Some{v}: Maybe<&2, Vote>}
        Quorums.Quorum.decide_kept(~Vote, ~Vote.is_eq, ~Vote.laws(), b1, b2, v)(Ballots.grows(~ty, ~same, ~laws, s, s2, p, ms, gr))(
          Equal.trans(
            Maybe<&2, Vote>,
            Quorums.Quorum.decide(~Vote, ~Vote.is_eq, b1),
            Quorums.Quorum.decide_fast(~Vote, ~Vote.is_eq, b1),
            Some{v},
            Equal.sym(
              Maybe<&2, Vote>,
              Quorums.Quorum.decide_fast(~Vote, ~Vote.is_eq, b1),
              Quorums.Quorum.decide(~Vote, ~Vote.is_eq, b1),
              Quorums.Quorum.decide_fast_eq(~Vote, ~Vote.is_eq, ~Vote.laws(), b1)
            ),
            hd
          )
        )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners of a root line stay
def Root.owners.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  s2: State(Q),
  +r: Id,
  gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Root.owners(~Q, ~view, s, r) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Root.owners(~Q, ~view, s2, r) == Some{a}: Maybe<&2, List<&2, String>>}:
  Shared.Maybe.bind_kept(
    Asked<Q>,
    List<&2, String>,
    State.asked(~Q, s, r),
    State.asked(~Q, s2, r),
    x => Root.owners.ask(~Q, ~view, x),
    x => Root.owners.ask(~Q, ~view, x),
    a,
    x => State.read_grows(
      ~Q,
      ~same,
      ~laws,
      ~Asked<Q>,
      m => Asked.of(~Q, m),
      {==},
      s,
      s2,
      Slot.ask(r),
      x
    )(gr),
    x => h => h
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners of the epoch after e, from the fact w, stay
def Epoch.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  s2: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  w: Where,
  gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Epoch.at(~Q, s, c, e, ms, w) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Epoch.at(~Q, s2, c, e, ms, w) == Some{a}: Maybe<&2, List<&2, String>>}:
  match w:
    case Where{c2, e2, h}:
      +p = {Where{c, e, h}: Where}
      Shared.Maybe.when_kept(
        List<&2, String>,
        Bool.and(Chain.is_eq(c2, c), U32.is_eq(e2, e)),
        u => Maybe.bind(
          &2,
          Vote,
          List<&2, String>,
          State.decide(~Q, s, p, ms),
          v => Owners.of(c, v)
        ),
        u => Maybe.bind(
          &2,
          Vote,
          List<&2, String>,
          State.decide(~Q, s2, p, ms),
          v => Owners.of(c, v)
        ),
        a,
        Shared.Maybe.bind_kept(
          Vote,
          List<&2, String>,
          State.decide(~Q, s, p, ms),
          State.decide(~Q, s2, p, ms),
          v => Owners.of(c, v),
          v => Owners.of(c, v),
          a,
          x => State.decide_grows(~Q, ~same, ~laws, s, s2, p, ms, x)(gr),
          x => h => h
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners of the epoch after e stay
def Epoch.next.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  ms: List<&2, String>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Epoch.next(~Q, s, c, e, ms) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Epoch.next(~Q, s2, c, e, ms) == Some{a}: Maybe<&2, List<&2, String>>}:
  +k = Slot.epoch(c, U32.inc(e))
  Shared.Maybe.bind_kept(
    Where,
    List<&2, String>,
    Where.of(~Q, State.entry(~Q, s, k)),
    Where.of(~Q, State.entry(~Q, s2, k)),
    w => Epoch.at(~Q, s, c, e, ms, w),
    w => Epoch.at(~Q, s2, c, e, ms, w),
    a,
    x => State.read_grows(~Q, ~same, ~laws, ~Where, m => Where.of(~Q, m), {==}, s, s2, k, x)(gr),
    w => Epoch.at.kept(~Q, ~same, ~laws, s, s2, c, e, ms, w, gr, a)
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the owners of the epoch n after cur stay, when those of cur do (hm)
def Epoch.up.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  n: Nat,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +cur: U32,
  m: Maybe<&2, List<&2, String>>,
  -m2: Maybe<&2, List<&2, String>>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  hm: @x: List<
    &2,
    String> -> {
    m == Some{x}: Maybe<&2, List<&2, String>>
  } -> {m2 == Some{x}: Maybe<&2, List<&2, String>>},
  a: List<&2, String>
) -> {
  Epoch.up(~Q, n, s, c, cur, m) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Epoch.up(~Q, n, s2, c, cur, m2) == Some{a}: Maybe<&2, List<&2, String>>}:
  match n:
    case 0n:
      hm(a)
    case 1n+p:
      up = U32.inc(cur)
      Shared.Maybe.bind_kept(
        List<&2, String>,
        List<&2, String>,
        m,
        m2,
        ms => Epoch.up(~Q, p, s, c, up, Epoch.next(~Q, s, c, cur, ms)),
        ms => Epoch.up(~Q, p, s2, c, up, Epoch.next(~Q, s2, c, cur, ms)),
        a,
        hm,
        +ms => Epoch.up.kept(
          ~Q,
          ~same,
          ~laws,
          p,
          s,
          s2,
          c,
          up,
          Epoch.next(~Q, s, c, cur, ms),
          Epoch.next(~Q, s2, c, cur, ms),
          gr,
          x => Epoch.next.kept(~Q, ~same, ~laws, s, s2, c, cur, ms, gr, x),
          a
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# the owners of an epoch of a root line stay
def Root.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  +r: Id,
  e: U32,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Root.at(~Q, ~view, s, r, e) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Root.at(~Q, ~view, s2, r, e) == Some{a}: Maybe<&2, List<&2, String>>}:
  Epoch.up.kept(
    ~Q,
    ~same,
    ~laws,
    U32.to_nat(e),
    s,
    s2,
    Chain{r, None{}},
    0,
    Root.owners(~Q, ~view, s, r),
    Root.owners(~Q, ~view, s2, r),
    gr,
    x => Root.owners.kept(~Q, ~same, ~laws, ~view, s, s2, r, gr, x),
    a
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the first owners of a line, from the fact w where it was made, stay
def Made.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  +r: Id,
  k: List<&2, Bool>,
  w: Where,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Made.at(~Q, ~view, s, r, k, w) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Made.at(~Q, ~view, s2, r, k, w) == Some{a}: Maybe<&2, List<&2, String>>}:
  match w:
    case Where{+c2, +e, h}:
      +p = {Where{c2, e, h}: Where}
      Shared.Maybe.when_kept(
        List<&2, String>,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Maybe.bind(
          &2,
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          ms => Maybe.bind(
            &2,
            Vote,
            List<&2, String>,
            State.decide(~Q, s, p, ms),
            v => Made.vote(k, ms, v)
          )
        ),
        u => Maybe.bind(
          &2,
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s2, r, e),
          ms => Maybe.bind(
            &2,
            Vote,
            List<&2, String>,
            State.decide(~Q, s2, p, ms),
            v => Made.vote(k, ms, v)
          )
        ),
        a,
        Shared.Maybe.bind_kept(
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          Root.at(~Q, ~view, s2, r, e),
          ms => Maybe.bind(
            &2,
            Vote,
            List<&2, String>,
            State.decide(~Q, s, p, ms),
            v => Made.vote(k, ms, v)
          ),
          ms => Maybe.bind(
            &2,
            Vote,
            List<&2, String>,
            State.decide(~Q, s2, p, ms),
            v => Made.vote(k, ms, v)
          ),
          a,
          x => Root.at.kept(~Q, ~same, ~laws, ~view, s, s2, r, e, gr, x),
          +ms => Shared.Maybe.bind_kept(
            Vote,
            List<&2, String>,
            State.decide(~Q, s, p, ms),
            State.decide(~Q, s2, p, ms),
            v => Made.vote(k, ms, v),
            v => Made.vote(k, ms, v),
            a,
            x => State.decide_grows(~Q, ~same, ~laws, s, s2, p, ms, x)(gr),
            x => h0 => h0
          )
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners of the first epoch of a line stay
def Line.first.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  c: Chain,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Line.first(~Q, ~view, s, c) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Line.first(~Q, ~view, s2, c) == Some{a}: Maybe<&2, List<&2, String>>}:
  match c:
    case Chain{r, None{}}:
      Root.owners.kept(~Q, ~same, ~laws, ~view, s, s2, r, gr, a)
    case Chain{+r, Some{+k}}:
      +slot = Slot.made(Chain{r, Some{k}})
      Shared.Maybe.bind_kept(
        Where,
        List<&2, String>,
        Where.of(~Q, State.entry(~Q, s, slot)),
        Where.of(~Q, State.entry(~Q, s2, slot)),
        w => Made.at(~Q, ~view, s, r, k, w),
        w => Made.at(~Q, ~view, s2, r, k, w),
        a,
        x => State.read_grows(
          ~Q,
          ~same,
          ~laws,
          ~Where,
          m => Where.of(~Q, m),
          {==},
          s,
          s2,
          slot,
          x
        )(gr),
        w => Made.at.kept(~Q, ~same, ~laws, ~view, s, s2, r, k, w, gr, a)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the owners of an epoch of a line stay
def Line.owners.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  e: U32,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: List<&2, String>
) -> {
  Line.owners(~Q, ~view, s, c, e) == Some{a}: Maybe<&2, List<&2, String>>
} -> {Line.owners(~Q, ~view, s2, c, e) == Some{a}: Maybe<&2, List<&2, String>>}:
  Epoch.up.kept(
    ~Q,
    ~same,
    ~laws,
    U32.to_nat(e),
    s,
    s2,
    c,
    0,
    Line.first(~Q, ~view, s, c),
    Line.first(~Q, ~view, s2, c),
    gr,
    x => Line.first.kept(~Q, ~same, ~laws, ~view, s, s2, c, gr, x),
    a
  )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the vote that decided i at the place w stays
def Where.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  i: Id,
  w: Where,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool},
  a: Vote
) -> {
  Where.at(~Q, ~view, s, i, w) == Some{a}: Maybe<&2, Vote>
} -> {Where.at(~Q, ~view, s2, i, w) == Some{a}: Maybe<&2, Vote>}:
  match w:
    case Where{+c, +e, h}:
      +p = {Where{c, e, h}: Where}
      Shared.Maybe.bind_kept(
        List<&2, String>,
        Vote,
        Line.owners(~Q, ~view, s, c, e),
        Line.owners(~Q, ~view, s2, c, e),
        ms => Maybe.bind(&2, Vote, Vote, State.decide(~Q, s, p, ms), v => Vote.for(i, v)),
        ms => Maybe.bind(&2, Vote, Vote, State.decide(~Q, s2, p, ms), v => Vote.for(i, v)),
        a,
        x => Line.owners.kept(~Q, ~same, ~laws, ~view, s, s2, c, e, gr, x),
        +ms => Shared.Maybe.bind_kept(
          Vote,
          Vote,
          State.decide(~Q, s, p, ms),
          State.decide(~Q, s2, p, ms),
          v => Vote.for(i, v),
          v => Vote.for(i, v),
          a,
          x => State.decide_grows(~Q, ~same, ~laws, s, s2, p, ms, x)(gr),
          x => h0 => h0
        )
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the vote that decided a request stays as the state grows
law State.decided_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +s2: State(Q)
  for +i: Id
  for +a: Vote
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {State.decided(~Q, ~view, s, i) == Some{a}: Maybe<&2, Vote>}
    -> {State.decided(~Q, ~view, s2, i) == Some{a}: Maybe<&2, Vote>}

def State.decided_grows(ty, same, laws, view, s, s2, i, a):
  +gr =>
    +k = Slot.where(i)
    Shared.Maybe.bind_kept(
      Where,
      Vote,
      Where.of(~ty, State.entry(~ty, s, k)),
      Where.of(~ty, State.entry(~ty, s2, k)),
      w => Where.at(~ty, ~view, s, i, w),
      w => Where.at(~ty, ~view, s2, i, w),
      a,
      x => State.read_grows(
        ~ty,
        ~same,
        ~laws,
        ~Where,
        m => Where.of(~ty, m),
        {==},
        s,
        s2,
        k,
        x
      )(gr),
      w => Where.at.kept(~ty, ~same, ~laws, ~view, s, s2, i, w, gr, a)
    )

# the verdict of a status, if it is done
def Status.verdict(st: Status) -> Maybe<&2, Bool>:
  match st:
    case Status.Done{k}:
      Some{k}
    case _:
      None{}

# st is refused
def Status.is_refused(st: Status) -> Bool:
  match st:
    case Status.Refused{}:
      True{}
    case _:
      False{}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a status that is not done is not done with k
def Status.not_done(
  st: Status,
  -k: Bool,
  h: {Status.verdict(st) == None{}: Maybe<&2, Bool>}
) -> {st == Status.Done{k}: Status} -> Empty:
  d => Shared.Maybe.none_ne_some(
    Bool,
    k,
    Equal.trans(
      Maybe<&2, Bool>,
      None{},
      Status.verdict(st),
      Some{k},
      Equal.sym(Maybe<&2, Bool>, Status.verdict(st), None{}, h),
      Equal.cong(Status, Maybe<&2, Bool>, x => Status.verdict(x), st, Status.Done{k}, d)
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a status that is not refused is not refused
def Status.not_refused(
  st: Status,
  h: {Status.is_refused(st) == False{}: Bool}
) -> {st == Status.Refused{}: Status} -> Empty:
  d => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Status.is_refused(st),
      True{},
      Equal.sym(Bool, Status.is_refused(st), False{}, h),
      Equal.cong(Status, Bool, x => Status.is_refused(x), st, Status.Refused{}, d)
    )
  )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Status.kept once the view v of the request and the vote dm that decided it are known
def Status.kept.view(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  s: State(Q),
  s2: State(Q),
  i: Id,
  -k: Bool,
  v: View,
  dm: Maybe<&2, Vote>,
  edm: {State.decided(~Q, ~view, s, i) == dm: Maybe<&2, Vote>},
  gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Status.of.view(v, dm) == Status.Done{k}: Status
} -> {Status.of.view(v, State.decided(~Q, ~view, s2, i)) == Status.Done{k}: Status}:
  match v dm:
    case View.Root{ms} w:
      h => h
    case View.On{c, o, mk} Some{x}:
      h =>
        %Equal.sym(
          Maybe<&2, Vote>,
          State.decided(~Q, ~view, s2, i),
          Some{x},
          State.decided_grows(~Q, ~same, ~laws, ~view, s, s2, i, x)(gr)(edm)
        ): {Status.of.view(View.On{c, o, mk}, _) == Status.Done{k}: Status}
        h
    case View.On{c, o, mk} None{}:
      h => Empty.absurd(
        {
          Status.of.view(
            View.On{c, o, mk},
            State.decided(~Q, ~view, s2, i)
          )
            == Status.Done{k}: Status
        },
        Status.not_done(Status.Pending{}, k, {==})(h)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# Status.kept once the cell m of the request is known
def Status.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  +i: Id,
  -k: Bool,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, Slot.ask(i)) == m: Maybe<&2, Cells.Cell<Entry<Q>>>},
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Status.of(~Q, ~view, s, i, m) == Status.Done{k}: Status
} -> {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status}:
  match m:
    case None{}:
      h => Empty.absurd(
        {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status},
        Status.not_done(Status.NotSeen{}, k, {==})(h)
      )
    case Some{Cells.Many{}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status},
        Status.not_done(Status.Refused{}, k, {==})(h)
      )
    case Some{Cells.One{Entry.Ask{j, t0, +q}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, s2, Slot.ask(i)),
          Some{Cells.One{Entry.Ask{j, t0, q}}},
          Cells.Cell.keeps_value(
            ~Entry<Q>,
            ~Entry.is_eq(~Q, ~same),
            ~Entry.laws(~Q, ~same, ~laws),
            Entry.Ask{j, t0, q},
            State.get(~Q, s2, Slot.ask(i))
          )(
            %em: {Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same), _, State.get(~Q, s2, Slot.ask(i))) == True{}: Bool}
            Tries.Trie.keeps_get(~Cells.Cell<Entry<Q>>, ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), ~Cells.Cell.none_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, s2, Slot.ask(i))(gr))
        ): {Status.of(~Q, ~view, s2, i, _) == Status.Done{k}: Status}
        Status.kept.view(
          ~Q,
          ~same,
          ~laws,
          ~view,
          s,
          s2,
          i,
          k,
          view(q),
          State.decided(~Q, ~view, s, i),
          {==},
          gr
        )(h)
    case Some{Cells.One{Entry.Vote{v}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status},
        Status.not_done(Status.NotSeen{}, k, {==})(h)
      )
    case Some{Cells.One{Entry.At{w}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status},
        Status.not_done(Status.NotSeen{}, k, {==})(h)
      )
    case Some{Cells.One{Entry.Data{d}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status},
        Status.not_done(Status.NotSeen{}, k, {==})(h)
      )

# a request that is done stays done, with the same verdict, as the state grows
law State.status_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +s2: State(Q)
  for +i: Id
  for -k: Bool
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {State.status(~Q, ~view, s, i) == Status.Done{k}: Status}
    -> {State.status(~Q, ~view, s2, i) == Status.Done{k}: Status}

def State.status_grows(ty, same, laws, view, s, s2, i, k):
  gr => Status.kept.at(
    ~ty,
    ~same,
    ~laws,
    ~view,
    s,
    s2,
    i,
    k,
    State.get(~ty, s, Slot.ask(i)),
    {==},
    gr
  )

# the status of a request of the view v is never refused
def Status.view_not_refused(
  v: View,
  dm: Maybe<&2, Vote>
) -> {Status.is_refused(Status.of.view(v, dm)) == False{}: Bool}:
  match v dm:
    case View.Root{ms} w:
      {==}
    case View.On{c, o, mk} Some{Vote{j, k, u, r}}:
      {==}
    case View.On{c, o, mk} None{}:
      {==}

# a request that is many stays refused, whatever else a sync brings (m2)
def Refused.many(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  s: State(Q),
  i: Id,
  m2: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Status.of(
    ~Q,
    ~view,
    s,
    i,
    Shared.Maybe.join(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      Some{Cells.Many{}},
      m2
    )
  )
    == Status.Refused{}: Status
}:
  match m2:
    case None{}:
      {==}
    case Some{x}:
      {==}

# State.refused_kept once the cell m of the request is known
def Refused.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, Slot.ask(i)) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {
  Status.of(~Q, ~view, s, i, m) == Status.Refused{}: Status
} -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status}:
  match m:
    case Some{Cells.Many{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.join(~Q, ~same, s, t), Slot.ask(i)),
          Shared.Maybe.join(
            ~Cells.Cell<Entry<Q>>,
            ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
            State.get(~Q, s, Slot.ask(i)),
            State.get(~Q, t, Slot.ask(i))
          ),
          Tries.Trie.get_union(
            ~Cells.Cell<Entry<Q>>,
            ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
            s,
            t,
            Slot.ask(i)
          )
        ): {Status.of(~Q, ~view, State.join(~Q, ~same, s, t), i, _) == Status.Refused{}: Status}
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, s, Slot.ask(i)),
          Some{Cells.Many{}},
          em
        ):
          {
            Status.of(
              ~Q,
              ~view,
              State.join(~Q, ~same, s, t),
              i,
              Shared.Maybe.join(
                ~Cells.Cell<Entry<Q>>,
                ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
                _,
                State.get(~Q, t, Slot.ask(i))
              )
            )
              == Status.Refused{}: Status
          }
        Refused.many(
          ~Q,
          ~same,
          ~view,
          State.join(~Q, ~same, s, t),
          i,
          State.get(~Q, t, Slot.ask(i))
        )
    case None{}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status},
        Status.not_refused(Status.NotSeen{}, {==})(h)
      )
    case Some{Cells.One{Entry.Ask{j, t0, +q}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status},
        Status.not_refused(
          Status.of.view(view(q), State.decided(~Q, ~view, s, i)),
          Status.view_not_refused(view(q), State.decided(~Q, ~view, s, i))
        )(h)
      )
    case Some{Cells.One{Entry.Vote{v}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status},
        Status.not_refused(Status.NotSeen{}, {==})(h)
      )
    case Some{Cells.One{Entry.At{w}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status},
        Status.not_refused(Status.NotSeen{}, {==})(h)
      )
    case Some{Cells.One{Entry.Data{d}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status},
        Status.not_refused(Status.NotSeen{}, {==})(h)
      )

# a refused request stays refused after any sync: a contradiction is final
law State.refused_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  {State.status(~Q, ~view, s, i) == Status.Refused{}: Status}
    -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.Refused{}: Status}

def State.refused_kept(ty, same, view, s, t, i):
  Refused.kept.at(~ty, ~same, ~view, s, t, i, State.get(~ty, s, Slot.ask(i)), {==})

# Writes
# ------
# A node's own writes only add entries that agree with what it holds, so each
# write grows the state, and every kept read stays through it.

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

# a fact put at k grows the state, once the cell m there is known
def Fact.put.of.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  k: List<&2, Bool>,
  w: Where,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, k) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {State.grows(~Q, ~same, s, Fact.put.of(~Q, ~same, s, k, w, m)) == True{}: Bool}:
  match m:
    case None{}:
      State.grows_put(~Q, ~same, ~laws, s, k, Entry.At{w})(em)
    case Some{x}:
      State.grows_refl(~Q, ~same, ~laws, s)

# a fact put grows the state
def Fact.put.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +k: List<&2, Bool>,
  w: Where
) -> {State.grows(~Q, ~same, s, Fact.put(~Q, ~same, s, k, w)) == True{}: Bool}:
  Fact.put.of.grows(~Q, ~same, ~laws, s, k, w, State.get(~Q, s, k), {==})

# the facts of a step grow the state
def Settle.view.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  s: State(Q),
  +w: Where,
  k: Bool,
  v: View
) -> {State.grows(~Q, ~same, s, Settle.view(~Q, ~same, s, w, k, v)) == True{}: Bool}:
  match k v:
    case True{} View.On{+c, Some{os}, mk}:
      Fact.put.grows(~Q, ~same, ~laws, s, Slot.epoch(c, U32.inc(Where.epoch(w))), w)
    case True{} View.On{Chain{r, b}, None{}, Some{key}}:
      Fact.put.grows(~Q, ~same, ~laws, s, Slot.made(Chain{r, Some{key}}), w)
    case True{} View.On{Chain{r, b}, None{}, None{}}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case True{} View.Root{ms}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case False{} y:
      State.grows_refl(~Q, ~same, ~laws, s)

# the facts of a decision grow the state
def Settle.of.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +w: Where,
  m: Maybe<&2, Vote>
) -> {State.grows(~Q, ~same, s, Settle.of(~Q, ~same, s, w, m)) == True{}: Bool}:
  match m:
    case Some{Vote{+i, +k, +v, r}}:
      +s1 = Fact.put(~Q, ~same, s, Slot.where(i), w)
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        s1,
        Settle.view(~Q, ~same, s1, w, k, v)
      )(
        Fact.put.grows(~Q, ~same, ~laws, s, Slot.where(i), w)
      )(Settle.view.grows(~Q, ~same, ~laws, s1, w, k, v))
    case None{}:
      State.grows_refl(~Q, ~same, ~laws, s)

# a put at k keeps what s holds at a key apart from k
def State.put_apart(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  +e: Entry<Q>,
  +k2: List<&2, Bool>
) -> {
  Tries.Trie.apart(k, k2) == True{}: Bool
} -> {
  State.get(
    ~Q,
    State.put(~Q, ~same, s, k, e),
    k2
  )
    == State.get(~Q, s, k2): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  ap =>
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.put(~Q, ~same, s, k, e), k2),
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        State.get(~Q, s, k2),
        State.get(~Q, State.one(~Q, k, e), k2)
      ),
      Tries.Trie.get_union(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        s,
        State.one(~Q, k, e),
        k2
      )
    ): {_ == State.get(~Q, s, k2): Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.one(~Q, k, e), k2),
      None{},
      Tries.Trie.get_one_apart(Cells.Cell<Entry<Q>>, k, k2, Cells.One{e})(ap)
    ): {
      Shared.Maybe.join(
        ~Cells.Cell<Entry<Q>>,
        ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
        State.get(~Q, s, k2),
        _
      )
        == State.get(~Q, s, k2): Maybe<&2, Cells.Cell<Entry<Q>>>
    }
    Shared.Maybe.join_none(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      State.get(~Q, s, k2)
    )

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

# a key that does not start as the slots of data do
def Slot.off_data(k: List<&2, Bool>) -> Bool:
  match k:
    case Con{False{}, r}:
      True{}
    case Con{True{}, Con{False{}, r}}:
      True{}
    case Con{True{}, Con{True{}, Con{False{}, r}}}:
      True{}
    case Con{True{}, Con{True{}, Con{True{}, Con{False{}, r}}}}:
      True{}
    case _:
      False{}

# a key that does not start as the slots of data do is apart from each of them
def Slot.data_apart(
  h: Hashes.Hash,
  k: List<&2, Bool>
) -> {Slot.off_data(k) == True{}: Bool} -> {Tries.Trie.apart(Slot.data(h), k) == True{}: Bool}:
  match h k:
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{False{}, r}:
      e => {==}
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{False{}, r}}:
      e => {==}
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{True{}, Con{False{}, r}}}:
      e => {==}
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{True{}, Con{True{}, Con{False{}, r}}}}:
      e => {==}
    case Hashes.Hash{a, b, c, d, f, g, i, j} Nil{}:
      e => e
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Nil{}}:
      e => e
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{True{}, Nil{}}}:
      e => e
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{True{}, Con{True{}, Nil{}}}}:
      e => e
    case Hashes.Hash{a, b, c, d, f, g, i, j} Con{True{}, Con{True{}, Con{True{}, Con{True{}, r}}}}:
      e => Empty.absurd(
        {
          Tries.Trie.apart(
            Slot.data(Hashes.Hash{a, b, c, d, f, g, i, j}),
            True{} <> True{} <> True{} <> True{} <> r
          )
            == True{}: Bool
        },
        Shared.Bool.false_ne_true(e)
      )

# Data.put.of keeps each slot apart from k
def Data.put_keeps.of(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  k: List<&2, Bool>,
  ws: List<&2, U32>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  k2: List<&2, Bool>
) -> {
  Tries.Trie.apart(k, k2) == True{}: Bool
} -> {
  State.get(
    ~Q,
    Data.put.of(~Q, ~same, s, k, ws, m),
    k2
  )
    == State.get(~Q, s, k2): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match m:
    case None{}:
      State.put_apart(~Q, ~same, s, k, Entry.Data{ws}, k2)
    case Some{x}:
      ap => {==}

# data keeps each slot that does not start as the slots of data do
def State.put_data_keeps(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +ws: List<&2, U32>,
  +k: List<&2, Bool>
) -> {
  Slot.off_data(k) == True{}: Bool
} -> {
  State.get(
    ~Q,
    State.put_data(~Q, ~same, s, ws),
    k
  )
    == State.get(~Q, s, k): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  e => Data.put_keeps.of(
    ~Q,
    ~same,
    s,
    Slot.data(Hashes.Sha.hash(ws)),
    ws,
    State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
    k
  )(Slot.data_apart(Hashes.Sha.hash(ws), k)(e))

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# data, one after the other, keeps each slot that does not start as the slots
# of data do
def State.put_datas_keeps(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ds: List<&2, List<&2, U32>>,
  +s: State(Q),
  +k: List<&2, Bool>
) -> {
  Slot.off_data(k) == True{}: Bool
} -> {
  State.get(
    ~Q,
    State.put_datas(~Q, ~same, ds, s),
    k
  )
    == State.get(~Q, s, k): Maybe<&2, Cells.Cell<Entry<Q>>>
}:
  match ds:
    case Nil{}:
      e => {==}
    case Con{+ws, r}:
      +e =>
        Equal.trans(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.put_datas(~Q, ~same, r, State.put_data(~Q, ~same, s, ws)), k),
          State.get(~Q, State.put_data(~Q, ~same, s, ws), k),
          State.get(~Q, s, k),
          State.put_datas_keeps(~Q, ~same, r, State.put_data(~Q, ~same, s, ws), k)(e),
          State.put_data_keeps(~Q, ~same, s, ws, k)(e)
        )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

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

# a vote put where held says the slot is empty grows the state
def Vote.put.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  held: Bool,
  m: Maybe<&2, Verdict>,
  +s: State(Q),
  +k: List<&2, Bool>,
  +i: Id,
  +v: View,
  ko: {Slot.off_data(k) == True{}: Bool},
  hf: {held == True{}: Bool} -> {State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {State.grows(~Q, ~same, s, Vote.put(~Q, ~same, held, m, s, k, i, v)) == True{}: Bool}:
  match held m:
    case True{} Some{Verdict{+x, +r, +ds}}:
      +sd = State.put_datas(~Q, ~same, ds, s)
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        sd,
        State.put(~Q, ~same, sd, k, Entry.Vote{Vote{i, x, v, r}})
      )(
        State.put_datas_grows(~Q, ~same, ~laws, ds, s)
      )(
        State.grows_put(
          ~Q,
          ~same,
          ~laws,
          sd,
          k,
          Entry.Vote{Vote{i, x, v, r}}
        )(
          Equal.trans(
            Maybe<&2, Cells.Cell<Entry<Q>>>,
            State.get(~Q, sd, k),
            State.get(~Q, s, k),
            None{},
            State.put_datas_keeps(~Q, ~same, ds, s, k)(ko),
            hf({==})
          )
        )
      )
    case True{} None{}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case False{} w:
      State.grows_refl(~Q, ~same, ~laws, s)

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# a node's vote, and the facts of what it decides, grow the state
def Vote.cast.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  +s: State(Q),
  +c: Chain,
  +i: Id,
  q: Q,
  +v: View,
  m: Maybe<&2, Tip>
) -> {
  State.grows(
    ~Q,
    ~same,
    s,
    Vote.cast(~Q, ~same, ~view, ~judge, n, s, c, i, q, v, m)
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case Some{Tip{+e, +ms, h, last}}:
      +w = {Where{c, e, h}: Where}
      +k = Slot.vote(w, n)
      +held = Bool.and(
        Vote.may(~Q, n, s, w, ms),
        Maybe.is_none(&2, Vote, State.decided(~Q, ~view, s, i))
      )
      +verdict = Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, ms, last))
      +s1 = Vote.put(~Q, ~same, held, verdict, s, k, i, v)
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        s1,
        State.settle(~Q, ~same, s1, w, ms)
      )(
        Vote.put.grows(
          ~Q,
          ~same,
          ~laws,
          held,
          verdict,
          s,
          k,
          i,
          v,
          {==},
          hd => Shared.Maybe.is_none_eq(
            Cells.Cell<Entry<Q>>,
            State.get(~Q, s, k)
          )(
            Shared.Bool.and_true_right(
              List.contains(~String, ~String.eq, ms, n),
              Maybe.is_none(&2, Cells.Cell<Entry<Q>>, State.get(~Q, s, k))
            )(
              Shared.Bool.and_true_left(
                Vote.may(~Q, n, s, w, ms),
                Maybe.is_none(&2, Vote, State.decided(~Q, ~view, s, i))
              )(hd)
            )
          )
        )
      )(Settle.of.grows(~Q, ~same, ~laws, s1, w, State.decide(~Q, s1, w, ms)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a node's vote on a request grows the state
def Vote.ask.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  +s: State(Q),
  i: Id,
  q: Q,
  v: View
) -> {State.grows(~Q, ~same, s, Vote.ask(~Q, ~same, ~view, ~judge, n, s, i, q, v)) == True{}: Bool}:
  match v:
    case View.Root{ms}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case View.On{+c, o, mk}:
      Vote.cast.grows(
        ~Q,
        ~same,
        ~laws,
        ~view,
        ~judge,
        n,
        s,
        c,
        i,
        q,
        View.On{c, o, mk},
        Line.tip(~Q, ~view, s, c)
      )

# State.ask grows the state, once the cell m of the request is known
def State.ask.grows.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  +s: State(Q),
  +i: Id,
  +t: String,
  +q: Q,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, Slot.ask(i)) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {
  State.grows(
    ~Q,
    ~same,
    s,
    State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, m)
  )
    == True{}: Bool
}:
  match m:
    case Some{x}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case None{}:
      +s1 = State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        s1,
        Vote.ask(~Q, ~same, ~view, ~judge, n, s1, i, q, view(q))
      )(
        State.grows_put(~Q, ~same, ~laws, s, Slot.ask(i), Entry.Ask{i, t, q})(em)
      )(Vote.ask.grows(~Q, ~same, ~laws, ~view, ~judge, n, s1, i, q, view(q)))

# a node that takes in a request only grows its state: nothing it held
# changes, so every kept read stays
law State.ask_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>
  for n: String
  for +s: State(Q)
  for +i: Id
  for t: String
  for +q: Q
  {State.grows(~Q, ~same, s, State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q)) == True{}: Bool}

def State.ask_grows(ty, same, laws, view, judge, n, s, i, t, q):
  State.ask.grows.at(
    ~ty,
    ~same,
    ~laws,
    ~view,
    ~judge,
    n,
    s,
    i,
    t,
    q,
    State.get(~ty, s, Slot.ask(i)),
    {==}
  )

# a node that takes in a fresh request holds it
law State.ask_holds:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>
  for +n: String
  for +s: State(Q)
  for +i: Id
  for +t: String
  for +q: Q
  {State.get(~Q, s, Slot.ask(i)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    -> {
      State.asked(
        ~Q,
        State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q),
        i
      )
        == Some{Asked{t, q}}: Maybe<&2, Asked<Q>>
    }

def State.ask_holds(ty, same, laws, view, judge, n, s, i, t, q):
  +h =>
    +s1 = State.put(~ty, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<ty>>>, State.get(~ty, s, Slot.ask(i)), None{}, h):
      {
        State.asked(
          ~ty,
          State.ask.fresh(~ty, ~same, ~view, ~judge, n, s, i, t, q, _),
          i
        )
          == Some{Asked{t, q}}: Maybe<&2, Asked<ty>>
      }
    State.read_grows(
      ~ty,
      ~same,
      ~laws,
      ~Asked<ty>,
      m => Asked.of(~ty, m),
      {==},
      s1,
      Vote.ask(~ty, ~same, ~view, ~judge, n, s1, i, q, view(q)),
      Slot.ask(i),
      Asked{t, q}
    )(Vote.ask.grows(~ty, ~same, ~laws, ~view, ~judge, n, s1, i, q, view(q)))(
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<ty>>>, State.get(~ty, s1, Slot.ask(i)), Some{Cells.One{Entry.Ask{i, t, q}}}, State.put_get(~ty, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})(h)): {Asked.of(~ty, Cells.Cell.value(Entry<ty>, _)) == Some{Asked{t, q}}: Maybe<&2, Asked<ty>>}
      {==})

# Landing
# -------
# A sole owner's vote at the tip of its line decides the request at once.

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners [n] hold n
def Owners.has(n: String) -> {List.contains(~String, ~String.eq, [n], n) == True{}: Bool}:
  %Equal.sym(Bool, String.eq(n, n), True{}, Texts.String.eq_refl(n)):
    {List.any.if(u => List.contains(~String, ~String.eq, [], n), _) == True{}: Bool}
  {==}

# the sole owner n's vote for i at the tip: the vote put there, then the
# facts of what it decides, when n has not voted there, i has no fact of where
# it was decided, and the verdict is k
def Cast.puts(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  s: State(Q),
  c: Chain,
  i: Id,
  q: Q,
  v: View,
  e: U32,
  h: U32,
  last: Maybe<&2, Where>,
  k: Bool,
  r: Maybe<&2, Hashes.Hash>,
  ds: List<&2, List<&2, U32>>
) -> {
  State.get(~Q, s, Slot.vote(Where{c, e, h}, n)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  State.get(~Q, s, Slot.where(i)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Vote.verdict(
    ~Q,
    ~view,
    ~judge,
    s,
    q,
    v,
    Line.head(~Q, ~view, s, c, e, [n], last)
  )
    == Some{Verdict{k, r, ds}}: Maybe<&2, Verdict>
} -> {
  Vote.cast(
    ~Q,
    ~same,
    ~view,
    ~judge,
    n,
    s,
    c,
    i,
    q,
    v,
    Some{Tip{e, [n], h, last}}
  )
    == State.settle(
      ~Q,
      ~same,
      State.put(
        ~Q,
        ~same,
        State.put_datas(~Q, ~same, ds, s),
        Slot.vote(Where{c, e, h}, n),
        Entry.Vote{Vote{i, k, v, r}}
      ),
      Where{c, e, h},
      [n]
    ): State(Q)
}:
  hg => hw => hv =>
    +w = {Where{c, e, h}: Where}
    +sk = Slot.vote(w, n)
    +rhs = State.settle(
      ~Q,
      ~same,
      State.put(~Q, ~same, State.put_datas(~Q, ~same, ds, s), sk, Entry.Vote{Vote{i, k, v, r}}),
      w,
      [n]
    )
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, s, sk), None{}, hg):
      {
        State.settle(
          ~Q,
          ~same,
          Vote.put(
            ~Q,
            ~same,
            Bool.and(
              Bool.and(
                List.contains(~String, ~String.eq, [n], n),
                Maybe.is_none(&2, Cells.Cell<Entry<Q>>, _)
              ),
              Maybe.is_none(&2, Vote, State.decided(~Q, ~view, s, i))
            ),
            Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, [n], last)),
            s,
            sk,
            i,
            v
          ),
          w,
          [n]
        )
          == rhs: State(Q)
      }
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, s, Slot.where(i)), None{}, hw):
      {
        State.settle(
          ~Q,
          ~same,
          Vote.put(
            ~Q,
            ~same,
            Bool.and(
              Bool.and(List.contains(~String, ~String.eq, [n], n), True{}),
              Maybe.is_none(
                &2,
                Vote,
                Maybe.bind(
                  &2,
                  Where,
                  Vote,
                  Where.of(~Q, Cells.Cell.value(Entry<Q>, _)),
                  x => Where.at(~Q, ~view, s, i, x)
                )
              )
            ),
            Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, [n], last)),
            s,
            sk,
            i,
            v
          ),
          w,
          [n]
        )
          == rhs: State(Q)
      }
    %Equal.sym(Bool, List.contains(~String, ~String.eq, [n], n), True{}, Owners.has(n)):
      {
        State.settle(
          ~Q,
          ~same,
          Vote.put(
            ~Q,
            ~same,
            Bool.and(Bool.and(_, True{}), True{}),
            Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, [n], last)),
            s,
            sk,
            i,
            v
          ),
          w,
          [n]
        )
          == rhs: State(Q)
      }
    %Equal.sym(
      Maybe<&2, Verdict>,
      Vote.verdict(~Q, ~view, ~judge, s, q, v, Line.head(~Q, ~view, s, c, e, [n], last)),
      Some{Verdict{k, r, ds}},
      hv
    ):
      {
        State.settle(
          ~Q,
          ~same,
          Vote.put(~Q, ~same, True{}, _, s, sk, i, v),
          w,
          [n]
        )
          == rhs: State(Q)
      }
    {==}

# the sole owner n's vote x, put at its slot of the bucket at w, decides w
def Decide.one_put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +w: Where,
  +n: String,
  +x: Vote
) -> {
  State.get(~Q, s, Slot.vote(w, n)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  State.decide(
    ~Q,
    State.put(~Q, ~same, s, Slot.vote(w, n), Entry.Vote{x}),
    w,
    [n]
  )
    == Some{x}: Maybe<&2, Vote>
}:
  match w:
    case Where{+c, +e, +h}:
      hg =>
        +p = Slot.bucket(c, e, h)
        +s1 = State.put(~Q, ~same, s, Slot.vote(Where{c, e, h}, n), Entry.Vote{x})
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.under(~Q, s1, p), Slot.ballot(n)),
          State.get(~Q, s1, List.append(&2, Bool, p, Slot.ballot(n))),
          Tries.Trie.get_under(Cells.Cell<Entry<Q>>, s1, p, Slot.ballot(n))
        ): {
          Quorums.Quorum.decide_fast(
            ~Vote,
            ~Vote.is_eq,
            [Entry.ballot(~Q, _)]
          )
            == Some{x}: Maybe<&2, Vote>
        }
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, s1, Slot.vote(Where{c, e, h}, n)),
          Some{Cells.One{Entry.Vote{x}}},
          State.put_get(~Q, ~same, s, Slot.vote(Where{c, e, h}, n), Entry.Vote{x})(hg)
        ): {
          Quorums.Quorum.decide_fast(
            ~Vote,
            ~Vote.is_eq,
            [Entry.ballot(~Q, _)]
          )
            == Some{x}: Maybe<&2, Vote>
        }
        Equal.trans(
          Maybe<&2, Vote>,
          Quorums.Quorum.decide_fast(~Vote, ~Vote.is_eq, [Some{Cells.One{x}}]),
          Quorums.Quorum.decide(~Vote, ~Vote.is_eq, [Some{Cells.One{x}}]),
          Some{x},
          Quorums.Quorum.decide_fast_eq(~Vote, ~Vote.is_eq, ~Vote.laws(), [Some{Cells.One{x}}]),
          Quorums.Quorum.decide_one(~Vote, ~Vote.is_eq, ~Vote.laws(), x)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the fact where i was decided, put after the step at w decides it, gives it
def Decided.after(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  h: U32,
  +n: String,
  +i: Id,
  k: Bool,
  v: View,
  r: Maybe<&2, Hashes.Hash>
) -> {
  State.get(~Q, s2, Slot.where(i)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {
  Line.owners(~Q, ~view, s2, c, e) == Some{[n]}: Maybe<&2, List<&2, String>>
} -> {
  State.decide(~Q, s2, Where{c, e, h}, [n]) == Some{Vote{i, k, v, r}}: Maybe<&2, Vote>
} -> {
  State.decided(
    ~Q,
    ~view,
    State.put(~Q, ~same, s2, Slot.where(i), Entry.At{Where{c, e, h}}),
    i
  )
    == Some{Vote{i, k, v, r}}: Maybe<&2, Vote>
}:
  +hw2 => ho2 => hd =>
    +w = {Where{c, e, h}: Where}
    +x = {Vote{i, k, v, r}: Vote}
    +s3 = State.put(~Q, ~same, s2, Slot.where(i), Entry.At{w})
    +gr = State.grows_put(~Q, ~same, ~laws, s2, Slot.where(i), Entry.At{w})(hw2)
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, s3, Slot.where(i)),
      Some{Cells.One{Entry.At{w}}},
      State.put_get(~Q, ~same, s2, Slot.where(i), Entry.At{w})(hw2)
    ): {
      Maybe.bind(
        &2,
        Where,
        Vote,
        Where.of(~Q, Cells.Cell.value(Entry<Q>, _)),
        y => Where.at(~Q, ~view, s3, i, y)
      )
        == Some{x}: Maybe<&2, Vote>
    }
    %Equal.sym(
      Maybe<&2, List<&2, String>>,
      Line.owners(~Q, ~view, s3, c, e),
      Some{[n]},
      Line.owners.kept(~Q, ~same, ~laws, ~view, s2, s3, c, e, gr, [n])(ho2)
    ): {
      Maybe.bind(
        &2,
        List<&2, String>,
        Vote,
        _,
        ms => Maybe.bind(&2, Vote, Vote, State.decide(~Q, s3, w, ms), u => Vote.for(i, u))
      )
        == Some{x}: Maybe<&2, Vote>
    }
    %Equal.sym(
      Maybe<&2, Vote>,
      State.decide(~Q, s3, w, [n]),
      Some{x},
      State.decide_grows(~Q, ~same, ~laws, s2, s3, w, [n], x)(gr)(hd)
    ): {Maybe.bind(&2, Vote, Vote, _, u => Vote.for(i, u)) == Some{x}: Maybe<&2, Vote>}
    %Equal.sym(Bool, Id.is_eq(i, i), True{}, Id.is_eq_refl(i)):
      {Shared.Maybe.when(Vote, _, u => Some{x}) == Some{x}: Maybe<&2, Vote>}
    {==}

# what a sole owner n at the tip of the line c needs to take the request q (id
# i, time t) at once, then C: q is new and on c, the tip of c is at epoch e
# and height h with n its only owner, n has not voted there, no fact says
# where i is, and the judge gives the verdict k, r, ds at the head
def State.Sole(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  n: String,
  s: State(Q),
  i: Id,
  t: String,
  q: Q,
  c: Chain,
  o: Maybe<&2, List<&2, String>>,
  mk: Maybe<&2, List<&2, Bool>>,
  e: U32,
  h: U32,
  last: Maybe<&2, Where>,
  k: Bool,
  r: Maybe<&2, Hashes.Hash>,
  ds: List<&2, List<&2, U32>>,
  C: Type
) -> Type:
  {State.get(~Q, s, Slot.ask(i)) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
  -> {view(q) == View.On{c, o, mk}: View}
  -> {
    Line.tip(
      ~Q,
      ~view,
      State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
      c
    )
      == Some{Tip{e, [n], h, last}}: Maybe<&2, Tip>
  }
  -> {
    Line.owners(
      ~Q,
      ~view,
      State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
      c,
      e
    )
      == Some{[n]}: Maybe<&2, List<&2, String>>
  }
  -> {
    State.get(
      ~Q,
      State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
      Slot.vote(Where{c, e, h}, n)
    )
      == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
  }
  -> {
    State.get(
      ~Q,
      State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
      Slot.where(i)
    )
      == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
  }
  -> {
    Vote.verdict(
      ~Q,
      ~view,
      ~judge,
      State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
      q,
      View.On{c, o, mk},
      Line.head(
        ~Q,
        ~view,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q}),
        c,
        e,
        [n],
        last
      )
    )
      == Some{Verdict{k, r, ds}}: Maybe<&2, Verdict>
  }
  -> C

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a node that owns the tip of a line alone decides a request at once when it
# takes it in: when it has not voted there, no fact says where the request
# was decided, and judge gives the verdict k there, the request is done with k
def State.ask_decides(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  ~view: Ty -> View,
  ~judge: State(Ty) -> Ty -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  +s: State(Ty),
  +i: Id,
  t: String,
  +q: Ty,
  +c: Chain,
  o: Maybe<&2, List<&2, String>>,
  mk: Maybe<&2, List<&2, Bool>>,
  +e: U32,
  +h: U32,
  last: Maybe<&2, Where>,
  +k: Bool,
  +r: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> State.Sole(
  ~Ty,
  ~same,
  ~view,
  ~judge,
  n,
  s,
  i,
  t,
  q,
  c,
  o,
  mk,
  e,
  h,
  last,
  k,
  r,
  ds,
  {
    State.status(
      ~Ty,
      ~view,
      State.ask(~Ty, ~same, ~view, ~judge, n, s, i, t, q),
      i
    )
      == Status.Done{k}: Status
  }
):
  +h1 => +h2 => ht => ho => +hg => +hw => hv =>
    +v = {View.On{c, o, mk}: View}
    +w = {Where{c, e, h}: Where}
    +x = {Vote{i, k, v, r}: Vote}
    +a = {Entry.Ask{i, t, q}: Entry<Ty>}
    +s1 = State.put(~Ty, ~same, s, Slot.ask(i), a)
    +sd = State.put_datas(~Ty, ~same, ds, s1)
    +s2 = State.put(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x})
    +hgd = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, sd, Slot.vote(w, n)),
      State.get(~Ty, s1, Slot.vote(w, n)),
      None{},
      State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.vote(w, n))({==}),
      hg
    )
    +hw2 = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, s2, Slot.where(i)),
      State.get(~Ty, s1, Slot.where(i)),
      None{},
      Equal.trans(
        Maybe<&2, Cells.Cell<Entry<Ty>>>,
        State.get(~Ty, s2, Slot.where(i)),
        State.get(~Ty, sd, Slot.where(i)),
        State.get(~Ty, s1, Slot.where(i)),
        State.put_apart(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x}, Slot.where(i))({==}),
        State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.where(i))({==})
      ),
      hw
    )
    +s3 = State.put(~Ty, ~same, s2, Slot.where(i), Entry.At{w})
    +gr12 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      sd,
      s2
    )(
      State.put_datas_grows(~Ty, ~same, ~laws, ds, s1)
    )(State.grows_put(~Ty, ~same, ~laws, sd, Slot.vote(w, n), Entry.Vote{x})(hgd))
    +gr13 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      s2,
      s3
    )(gr12)(State.grows_put(~Ty, ~same, ~laws, s2, Slot.where(i), Entry.At{w})(hw2))
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s, Slot.ask(i)), None{}, h1):
      {
        State.status(
          ~Ty,
          ~view,
          State.ask.fresh(~Ty, ~same, ~view, ~judge, n, s, i, t, q, _),
          i
        )
          == Status.Done{k}: Status
      }
    %Equal.sym(View, view(q), v, h2):
      {
        State.status(
          ~Ty,
          ~view,
          Vote.ask(~Ty, ~same, ~view, ~judge, n, s1, i, q, _),
          i
        )
          == Status.Done{k}: Status
      }
    %Equal.sym(Maybe<&2, Tip>, Line.tip(~Ty, ~view, s1, c), Some{Tip{e, [n], h, last}}, ht):
      {
        State.status(
          ~Ty,
          ~view,
          Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, _),
          i
        )
          == Status.Done{k}: Status
      }
    %Equal.sym(
      State(Ty),
      Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, Some{Tip{e, [n], h, last}}),
      State.settle(~Ty, ~same, s2, w, [n]),
      Cast.puts(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, e, h, last, k, r, ds)(hg)(hw)(hv)
    ): {State.status(~Ty, ~view, _, i) == Status.Done{k}: Status}
    %Equal.sym(
      Maybe<&2, Vote>,
      State.decide(~Ty, s2, w, [n]),
      Some{x},
      Decide.one_put(~Ty, ~same, sd, w, n, x)(hgd)
    ):
      {State.status(~Ty, ~view, Settle.of(~Ty, ~same, s2, w, _), i) == Status.Done{k}: Status}
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s2, Slot.where(i)), None{}, hw2):
      {
        State.status(
          ~Ty,
          ~view,
          Settle.view(~Ty, ~same, Fact.put.of(~Ty, ~same, s2, Slot.where(i), w, _), w, k, v),
          i
        )
          == Status.Done{k}: Status
      }
    State.status_grows(
      ~Ty,
      ~same,
      ~laws,
      ~view,
      s3,
      Settle.view(~Ty, ~same, s3, w, k, v),
      i,
      k
    )(Settle.view.grows(~Ty, ~same, ~laws, s3, w, k, v))(
      %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s3, Slot.ask(i)), Some{Cells.One{a}}, Cells.Cell.keeps_value(~Entry<Ty>, ~Entry.is_eq(~Ty, ~same), ~Entry.laws(~Ty, ~same, ~laws), a, State.get(~Ty, s3, Slot.ask(i)))(
        %State.put_get(~Ty, ~same, s, Slot.ask(i), a)(h1):
          {Cells.Cell.keeps(~Entry<Ty>, ~Entry.is_eq(~Ty, ~same), _, State.get(~Ty, s3, Slot.ask(i))) == True{}: Bool}
        Tries.Trie.keeps_get(~Cells.Cell<Entry<Ty>>, ~Cells.Cell.keeps(~Entry<Ty>, ~Entry.is_eq(~Ty, ~same)), ~Cells.Cell.none_kept(~Entry<Ty>, ~Entry.is_eq(~Ty, ~same)), s1, s3, Slot.ask(i))(gr13))): {Status.of(~Ty, ~view, s3, i, _) == Status.Done{k}: Status}
      %Equal.sym(View, view(q), v, h2): {Status.of.view(_, State.decided(~Ty, ~view, s3, i)) == Status.Done{k}: Status}
      %Equal.sym(Maybe<&2, Vote>, State.decided(~Ty, ~view, s3, i), Some{x}, Decided.after(~Ty, ~same, ~laws, ~view, s2, c, e, h, n, i, k, v, r)(hw2)(Line.owners.kept(~Ty, ~same, ~laws, ~view, s1, s2, c, e, gr12, [n])(ho))(Decide.one_put(~Ty, ~same, sd, w, n, x)(hgd))): {Status.of.view(v, _) == Status.Done{k}: Status}
      {==})
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a sole owner's take-in of a fresh request decides it with its verdict: the
# vote that decided it is its vote, with the verdict's result
def State.ask_decided(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  ~view: Ty -> View,
  ~judge: State(Ty) -> Ty -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  s: State(Ty),
  +i: Id,
  t: String,
  +q: Ty,
  +c: Chain,
  o: Maybe<&2, List<&2, String>>,
  mk: Maybe<&2, List<&2, Bool>>,
  +e: U32,
  +h: U32,
  last: Maybe<&2, Where>,
  +k: Bool,
  +r: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> State.Sole(
  ~Ty,
  ~same,
  ~view,
  ~judge,
  n,
  s,
  i,
  t,
  q,
  c,
  o,
  mk,
  e,
  h,
  last,
  k,
  r,
  ds,
  {
    State.decided(
      ~Ty,
      ~view,
      State.ask(~Ty, ~same, ~view, ~judge, n, s, i, t, q),
      i
    )
      == Some{Vote{i, k, View.On{c, o, mk}, r}}: Maybe<&2, Vote>
  }
):
  +h1 => +h2 => ht => ho => +hg => +hw => hv =>
    +v = {View.On{c, o, mk}: View}
    +w = {Where{c, e, h}: Where}
    +x = {Vote{i, k, v, r}: Vote}
    +a = {Entry.Ask{i, t, q}: Entry<Ty>}
    +s1 = State.put(~Ty, ~same, s, Slot.ask(i), a)
    +sd = State.put_datas(~Ty, ~same, ds, s1)
    +s2 = State.put(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x})
    +hgd = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, sd, Slot.vote(w, n)),
      State.get(~Ty, s1, Slot.vote(w, n)),
      None{},
      State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.vote(w, n))({==}),
      hg
    )
    +hw2 = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, s2, Slot.where(i)),
      State.get(~Ty, s1, Slot.where(i)),
      None{},
      Equal.trans(
        Maybe<&2, Cells.Cell<Entry<Ty>>>,
        State.get(~Ty, s2, Slot.where(i)),
        State.get(~Ty, sd, Slot.where(i)),
        State.get(~Ty, s1, Slot.where(i)),
        State.put_apart(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x}, Slot.where(i))({==}),
        State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.where(i))({==})
      ),
      hw
    )
    +s3 = State.put(~Ty, ~same, s2, Slot.where(i), Entry.At{w})
    +gr12 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      sd,
      s2
    )(
      State.put_datas_grows(~Ty, ~same, ~laws, ds, s1)
    )(State.grows_put(~Ty, ~same, ~laws, sd, Slot.vote(w, n), Entry.Vote{x})(hgd))
    +gr13 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      s2,
      s3
    )(gr12)(State.grows_put(~Ty, ~same, ~laws, s2, Slot.where(i), Entry.At{w})(hw2))
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s, Slot.ask(i)), None{}, h1):
      {
        State.decided(
          ~Ty,
          ~view,
          State.ask.fresh(~Ty, ~same, ~view, ~judge, n, s, i, t, q, _),
          i
        )
          == Some{x}: Maybe<&2, Vote>
      }
    %Equal.sym(View, view(q), v, h2):
      {
        State.decided(
          ~Ty,
          ~view,
          Vote.ask(~Ty, ~same, ~view, ~judge, n, s1, i, q, _),
          i
        )
          == Some{x}: Maybe<&2, Vote>
      }
    %Equal.sym(Maybe<&2, Tip>, Line.tip(~Ty, ~view, s1, c), Some{Tip{e, [n], h, last}}, ht):
      {
        State.decided(
          ~Ty,
          ~view,
          Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, _),
          i
        )
          == Some{x}: Maybe<&2, Vote>
      }
    %Equal.sym(
      State(Ty),
      Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, Some{Tip{e, [n], h, last}}),
      State.settle(~Ty, ~same, s2, w, [n]),
      Cast.puts(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, e, h, last, k, r, ds)(hg)(hw)(hv)
    ): {State.decided(~Ty, ~view, _, i) == Some{x}: Maybe<&2, Vote>}
    %Equal.sym(
      Maybe<&2, Vote>,
      State.decide(~Ty, s2, w, [n]),
      Some{x},
      Decide.one_put(~Ty, ~same, sd, w, n, x)(hgd)
    ):
      {State.decided(~Ty, ~view, Settle.of(~Ty, ~same, s2, w, _), i) == Some{x}: Maybe<&2, Vote>}
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s2, Slot.where(i)), None{}, hw2):
      {
        State.decided(
          ~Ty,
          ~view,
          Settle.view(~Ty, ~same, Fact.put.of(~Ty, ~same, s2, Slot.where(i), w, _), w, k, v),
          i
        )
          == Some{x}: Maybe<&2, Vote>
      }
    State.decided_grows(
      ~Ty,
      ~same,
      ~laws,
      ~view,
      s3,
      Settle.view(~Ty, ~same, s3, w, k, v),
      i,
      x
    )(
      Settle.view.grows(~Ty, ~same, ~laws, s3, w, k, v)
    )(
      Decided.after(
        ~Ty,
        ~same,
        ~laws,
        ~view,
        s2,
        c,
        e,
        h,
        n,
        i,
        k,
        v,
        r
      )(
        hw2
      )(
        Line.owners.kept(~Ty, ~same, ~laws, ~view, s1, s2, c, e, gr12, [n])(ho)
      )(Decide.one_put(~Ty, ~same, sd, w, n, x)(hgd))
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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

# Listings only grow
# ------------------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# the slots below a key grow in number as the state grows
def State.size_under_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +k: List<&2, Bool>,
  gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Nat.is_le(
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, k)),
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, k))
  )
    == True{}: Bool
}:
  Tries.Trie.keeps_size(
    ~Cells.Cell<Entry<Q>>,
    ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
    ~(x => y => Cells.Cell.keeps_some(~Entry<Q>, ~Entry.is_eq(~Q, ~same), x, y)),
    State.under(~Q, s, k),
    State.under(~Q, s2, k)
  )(
    Tries.Trie.keeps_under(
      ~Cells.Cell<Entry<Q>>,
      ~Cells.Cell.keeps(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
      s,
      s2,
      k
    )(gr)
  )

# a list m that is none is not some
def Maybe.none_of_some(
  -A: Data,
  -m: Maybe<&2, A>,
  -x: A,
  bn: {Maybe.is_none(&2, A, m) == True{}: Bool},
  e: {m == Some{x}: Maybe<&2, A>}
) -> {False{} == True{}: Bool}:
  %e: {Maybe.is_none(&2, A, _) == True{}: Bool}
  bn

# the owners that steps after a step that gives none give
def Steps.next_tail(
  c: Chain,
  -v: Vote,
  ts: List<&2, Vote>,
  -os: List<&2, String>,
  bn: {Maybe.is_none(&2, List<&2, String>, Owners.of(c, v)) == True{}: Bool}
) -> {
  Steps.next(c, v <> ts) == Some{os}: Maybe<&2, List<&2, String>>
} -> {Steps.next(c, ts) == Some{os}: Maybe<&2, List<&2, String>>}:
  match ts:
    case Nil{}:
      e => Empty.absurd(
        {Steps.next(c, []) == Some{os}: Maybe<&2, List<&2, String>>},
        Shared.Bool.false_ne_true(Maybe.none_of_some(List<&2, String>, Owners.of(c, v), os, bn, e))
      )
    case Con{w, r}:
      e => e

# a step v, then the steps T1 when b, starts v, then the steps T2 when b, when
# T1 starts T2
def Epoch.starts.at(
  -v: Vote,
  -t1: List<&2, Vote>,
  -t2: List<&2, Vote>,
  b: Bool,
  ih: {List.take(&2, Vote, t2, List.length(&2, Vote, t1)) == t1: List<&2, Vote>}
) -> {
  List.take(
    &2,
    Vote,
    v <> Shared.Bool.when(List<&2, Vote>, b, u => t2, u => []),
    List.length(&2, Vote, v <> Shared.Bool.when(List<&2, Vote>, b, u => t1, u => []))
  )
    == v
    <> Shared.Bool.when(List<&2, Vote>, b, u => t1, u => []): List<&2, Vote>
}:
  match b:
    case True{}:
      %Equal.sym(
        List<&2, Vote>,
        List.take(&2, Vote, t2, List.length(&2, Vote, t1)),
        t1,
        ih
      ): {v <> _ == v <> t1: List<&2, Vote>}
      {==}
    case False{}:
      {==}

# the steps of an epoch, from the height h, start those of a state that grows
# from it, with at least as many steps (f2), when the decision there is kept
def Epoch.steps_starts(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  f: Nat,
  f2: Nat,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  +h: U32,
  m: Maybe<&2, Vote>,
  m2: Maybe<&2, Vote>,
  hm: @x: Vote -> {m == Some{x}: Maybe<&2, Vote>} -> {m2 == Some{x}: Maybe<&2, Vote>},
  hf: {Nat.is_le(f, f2) == True{}: Bool},
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  List.take(
    &2,
    Vote,
    Epoch.steps(~Q, f2, s2, c, e, ms, h, m2),
    List.length(&2, Vote, Epoch.steps(~Q, f, s, c, e, ms, h, m))
  )
    == Epoch.steps(~Q, f, s, c, e, ms, h, m): List<&2, Vote>
}:
  match f f2 m m2:
    case 0n g2 w w2:
      Shared.List.take_zero(Vote, Epoch.steps(~Q, g2, s2, c, e, ms, h, w2))
    case 1n+p g2 None{} w2:
      Shared.List.take_zero(Vote, Epoch.steps(~Q, g2, s2, c, e, ms, h, w2))
    case 1n+p 0n Some{v} w2:
      Empty.absurd(
        {
          List.take(
            &2,
            Vote,
            Epoch.steps(~Q, 0n, s2, c, e, ms, h, w2),
            List.length(&2, Vote, Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}))
          )
            == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
        },
        Shared.Bool.false_ne_true(hf)
      )
    case 1n+p 1n+p2 Some{v} None{}:
      Empty.absurd(
        {
          List.take(
            &2,
            Vote,
            Epoch.steps(~Q, 1n+p2, s2, c, e, ms, h, None{}),
            List.length(&2, Vote, Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}))
          )
            == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
        },
        Shared.Maybe.none_ne_some(Vote, v, hm(v)({==}))
      )
    case 1n+(+p) 1n+(+p2) Some{+v} Some{v2}:
      %Equal.sym(
        Vote,
        v2,
        v,
        Shared.Maybe.some_inj(Vote, v2, v, hm(v)({==}))
      ): {
        List.take(
          &2,
          Vote,
          Epoch.steps(~Q, 1n+p2, s2, c, e, ms, h, Some{_}),
          List.length(&2, Vote, Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}))
        )
          == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
      }
      Epoch.starts.at(
        v,
        Epoch.steps(
          ~Q,
          p,
          s,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s, Where{c, e, U32.inc(h)}, ms)
        ),
        Epoch.steps(
          ~Q,
          p2,
          s2,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s2, Where{c, e, U32.inc(h)}, ms)
        ),
        Maybe.is_none(&2, List<&2, String>, Owners.of(c, v)),
        Epoch.steps_starts(
          ~Q,
          ~same,
          ~laws,
          p,
          p2,
          s,
          s2,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s, Where{c, e, U32.inc(h)}, ms),
          State.decide(~Q, s2, Where{c, e, U32.inc(h)}, ms),
          x => State.decide_grows(~Q, ~same, ~laws, s, s2, Where{c, e, U32.inc(h)}, ms, x)(gr),
          hf,
          gr
        )
      )

# a step v, then the steps T1 when b, ends the steps of a state that grows,
# when it gives owners: then the steps T2 are T1
def Epoch.cut.at(
  c: Chain,
  v: Vote,
  t1: List<&2, Vote>,
  -t2: List<&2, Vote>,
  -os: List<&2, String>,
  b: Bool,
  eb: {Maybe.is_none(&2, List<&2, String>, Owners.of(c, v)) == b: Bool},
  ih: {Steps.next(c, t1) == Some{os}: Maybe<&2, List<&2, String>>} -> {t2 == t1: List<&2, Vote>}
) -> {
  Steps.next(
    c,
    v <> Shared.Bool.when(List<&2, Vote>, b, u => t1, u => [])
  )
    == Some{os}: Maybe<&2, List<&2, String>>
} -> {
  v
    <> Shared.Bool.when(List<&2, Vote>, b, u => t2, u => [])
    == v
    <> Shared.Bool.when(List<&2, Vote>, b, u => t1, u => []): List<&2, Vote>
}:
  match b:
    case True{}:
      e =>
        %Equal.sym(
          List<&2, Vote>,
          t2,
          t1,
          ih(Steps.next_tail(c, v, t1, os, eb, e))
        ): {v <> _ == v <> t1: List<&2, Vote>}
        {==}
    case False{}:
      e => {==}

# the steps of an epoch that end where the line gets new owners are the steps
# of a state that grows from it, with at least as many steps (f2)
def Epoch.steps_cut(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  f: Nat,
  f2: Nat,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  +h: U32,
  m: Maybe<&2, Vote>,
  m2: Maybe<&2, Vote>,
  -os: List<&2, String>,
  hm: @x: Vote -> {m == Some{x}: Maybe<&2, Vote>} -> {m2 == Some{x}: Maybe<&2, Vote>},
  hf: {Nat.is_le(f, f2) == True{}: Bool},
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Steps.next(c, Epoch.steps(~Q, f, s, c, e, ms, h, m)) == Some{os}: Maybe<&2, List<&2, String>>
} -> {
  Epoch.steps(~Q, f2, s2, c, e, ms, h, m2) == Epoch.steps(~Q, f, s, c, e, ms, h, m): List<&2, Vote>
}:
  match f f2 m m2:
    case 0n g2 w w2:
      e2 => Empty.absurd(
        {Epoch.steps(~Q, g2, s2, c, e, ms, h, w2) == []: List<&2, Vote>},
        Shared.Maybe.none_ne_some(List<&2, String>, os, e2)
      )
    case 1n+p g2 None{} w2:
      e2 => Empty.absurd(
        {Epoch.steps(~Q, g2, s2, c, e, ms, h, w2) == []: List<&2, Vote>},
        Shared.Maybe.none_ne_some(List<&2, String>, os, e2)
      )
    case 1n+p 0n Some{v} w2:
      e2 => Empty.absurd(
        {
          Epoch.steps(
            ~Q,
            0n,
            s2,
            c,
            e,
            ms,
            h,
            w2
          )
            == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
        },
        Shared.Bool.false_ne_true(hf)
      )
    case 1n+p 1n+p2 Some{v} None{}:
      e2 => Empty.absurd(
        {
          Epoch.steps(
            ~Q,
            1n+p2,
            s2,
            c,
            e,
            ms,
            h,
            None{}
          )
            == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
        },
        Shared.Maybe.none_ne_some(Vote, v, hm(v)({==}))
      )
    case 1n+(+p) 1n+(+p2) Some{+v} Some{v2}:
      %Equal.sym(
        Vote,
        v2,
        v,
        Shared.Maybe.some_inj(Vote, v2, v, hm(v)({==}))
      ): {
        Steps.next(
          c,
          Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v})
        )
          == Some{os}: Maybe<&2, List<&2, String>>
      } -> {
        Epoch.steps(
          ~Q,
          1n+p2,
          s2,
          c,
          e,
          ms,
          h,
          Some{_}
        )
          == Epoch.steps(~Q, 1n+p, s, c, e, ms, h, Some{v}): List<&2, Vote>
      }
      Epoch.cut.at(
        c,
        v,
        Epoch.steps(
          ~Q,
          p,
          s,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s, Where{c, e, U32.inc(h)}, ms)
        ),
        Epoch.steps(
          ~Q,
          p2,
          s2,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s2, Where{c, e, U32.inc(h)}, ms)
        ),
        os,
        Maybe.is_none(&2, List<&2, String>, Owners.of(c, v)),
        {==},
        Epoch.steps_cut(
          ~Q,
          ~same,
          ~laws,
          p,
          p2,
          s,
          s2,
          c,
          e,
          ms,
          U32.inc(h),
          State.decide(~Q, s, Where{c, e, U32.inc(h)}, ms),
          State.decide(~Q, s2, Where{c, e, U32.inc(h)}, ms),
          os,
          x => State.decide_grows(~Q, ~same, ~laws, s, s2, Where{c, e, U32.inc(h)}, ms, x)(gr),
          hf,
          gr
        )
      )

# the steps of an epoch start those of a state that grows from it
def Epoch.list_starts(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  List.take(
    &2,
    Vote,
    Epoch.list(~Q, s2, c, e, ms),
    List.length(&2, Vote, Epoch.list(~Q, s, c, e, ms))
  )
    == Epoch.list(~Q, s, c, e, ms): List<&2, Vote>
}:
  Epoch.steps_starts(
    ~Q,
    ~same,
    ~laws,
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.votes(c, e))),
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.votes(c, e))),
    s,
    s2,
    c,
    e,
    ms,
    0,
    State.decide(~Q, s, Where{c, e, 0}, ms),
    State.decide(~Q, s2, Where{c, e, 0}, ms),
    x => State.decide_grows(~Q, ~same, ~laws, s, s2, Where{c, e, 0}, ms, x)(gr),
    State.size_under_grows(~Q, ~same, ~laws, s, s2, Slot.votes(c, e), gr),
    gr
  )

# the steps of an epoch that end where the line gets new owners are those of a
# state that grows from it
def Epoch.list_cut(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  -os: List<&2, String>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Steps.next(c, Epoch.list(~Q, s, c, e, ms)) == Some{os}: Maybe<&2, List<&2, String>>
} -> {Epoch.list(~Q, s2, c, e, ms) == Epoch.list(~Q, s, c, e, ms): List<&2, Vote>}:
  Epoch.steps_cut(
    ~Q,
    ~same,
    ~laws,
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.votes(c, e))),
    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.votes(c, e))),
    s,
    s2,
    c,
    e,
    ms,
    0,
    State.decide(~Q, s, Where{c, e, 0}, ms),
    State.decide(~Q, s2, Where{c, e, 0}, ms),
    os,
    x => State.decide_grows(~Q, ~same, ~laws, s, s2, Where{c, e, 0}, ms, x)(gr),
    State.size_under_grows(~Q, ~same, ~laws, s, s2, Slot.votes(c, e), gr),
    gr
  )

# the steps of a line from an epoch, whose steps are vs, start with vs
def Line.steps.go_starts(
  ~Q: Data,
  f: Nat,
  +s: State(Q),
  +c: Chain,
  +cur: U32,
  vs: List<&2, Vote>,
  m: Maybe<&2, List<&2, String>>
) -> {
  List.take(
    &2,
    Vote,
    Line.steps.go(~Q, f, s, c, cur, vs, m),
    List.length(&2, Vote, vs)
  )
    == vs: List<&2, Vote>
}:
  match f m:
    case 1n+p Some{+os}:
      Shared.List.take_append(
        Vote,
        vs,
        Line.steps.go(
          ~Q,
          p,
          s,
          c,
          U32.inc(cur),
          Epoch.list(~Q, s, c, U32.inc(cur), os),
          Steps.next(c, Epoch.list(~Q, s, c, U32.inc(cur), os))
        )
      )
    case 0n w:
      Shared.List.take_length(Vote, vs)
    case 1n+p None{}:
      Shared.List.take_length(Vote, vs)

# the steps of a line from an epoch, whose steps are vs, start those of a state
# that grows from it, whose steps there are vs2, when vs starts vs2 and is vs2
# once it gives new owners
def Line.steps.go_grow(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  f: Nat,
  +f2: Nat,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  +cur: U32,
  vs: List<&2, Vote>,
  +vs2: List<&2, Vote>,
  m: Maybe<&2, List<&2, String>>,
  +m2: Maybe<&2, List<&2, String>>,
  hp: {List.take(&2, Vote, vs2, List.length(&2, Vote, vs)) == vs: List<&2, Vote>},
  cut: @os: List<
    &2,
    String> -> {
    Steps.next(c, vs) == Some{os}: Maybe<&2, List<&2, String>>
  } -> {vs2 == vs: List<&2, Vote>},
  +em: {m == Steps.next(c, vs): Maybe<&2, List<&2, String>>},
  em2: {m2 == Steps.next(c, vs2): Maybe<&2, List<&2, String>>},
  hf: {Nat.is_le(f, f2) == True{}: Bool},
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  List.take(
    &2,
    Vote,
    Line.steps.go(~Q, f2, s2, c, cur, vs2, m2),
    List.length(&2, Vote, Line.steps.go(~Q, f, s, c, cur, vs, m))
  )
    == Line.steps.go(~Q, f, s, c, cur, vs, m): List<&2, Vote>
}:
  match f f2 m m2:
    case 0n g2 w w2:
      Shared.List.prefix_trans(
        Vote,
        vs,
        vs2,
        Line.steps.go(~Q, g2, s2, c, cur, vs2, w2)
      )(hp)(Line.steps.go_starts(~Q, g2, s2, c, cur, vs2, w2))
    case 1n+p g2 None{} w2:
      Shared.List.prefix_trans(
        Vote,
        vs,
        vs2,
        Line.steps.go(~Q, g2, s2, c, cur, vs2, w2)
      )(hp)(Line.steps.go_starts(~Q, g2, s2, c, cur, vs2, w2))
    case 1n+p 0n Some{os} w2:
      Empty.absurd(
        {
          List.take(
            &2,
            Vote,
            Line.steps.go(~Q, 0n, s2, c, cur, vs2, w2),
            List.length(&2, Vote, Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}))
          )
            == Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}): List<&2, Vote>
        },
        Shared.Bool.false_ne_true(hf)
      )
    case 1n+p 1n+p2 Some{+os} None{}:
      Empty.absurd(
        {
          List.take(
            &2,
            Vote,
            Line.steps.go(~Q, 1n+p2, s2, c, cur, vs2, None{}),
            List.length(&2, Vote, Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}))
          )
            == Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}): List<&2, Vote>
        },
        Shared.Maybe.none_ne_some(
          List<&2, String>,
          os,
          Equal.trans(
            Maybe<&2, List<&2, String>>,
            None{},
            Steps.next(c, vs),
            Some{os},
            Equal.trans(
              Maybe<&2, List<&2, String>>,
              None{},
              Steps.next(c, vs2),
              Steps.next(c, vs),
              em2,
              Equal.cong(
                List<&2, Vote>,
                Maybe<&2, List<&2, String>>,
                l => Steps.next(c, l),
                vs2,
                vs,
                cut(os)(Equal.sym(Maybe<&2, List<&2, String>>, Some{os}, Steps.next(c, vs), em))
              )
            ),
            Equal.sym(Maybe<&2, List<&2, String>>, Some{os}, Steps.next(c, vs), em)
          )
        )
      )
    case 1n+(+p) 1n+(+p2) Some{+os} Some{os2}:
      +e1 = cut(os)(Equal.sym(Maybe<&2, List<&2, String>>, Some{os}, Steps.next(c, vs), em))
      eo = Shared.Maybe.some_inj(
        List<&2, String>,
        os2,
        os,
        Equal.trans(
          Maybe<&2, List<&2, String>>,
          Some{os2},
          Steps.next(c, vs),
          Some{os},
          Equal.trans(
            Maybe<&2, List<&2, String>>,
            Some{os2},
            Steps.next(c, vs2),
            Steps.next(c, vs),
            em2,
            Equal.cong(
              List<&2, Vote>,
              Maybe<&2, List<&2, String>>,
              l => Steps.next(c, l),
              vs2,
              vs,
              e1
            )
          ),
          Equal.sym(Maybe<&2, List<&2, String>>, Some{os}, Steps.next(c, vs), em)
        )
      )
      %Equal.sym(
        List<&2, Vote>,
        vs2,
        vs,
        e1
      ): {
        List.take(
          &2,
          Vote,
          Line.steps.go(~Q, 1n+p2, s2, c, cur, _, Some{os2}),
          List.length(&2, Vote, Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}))
        )
          == Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}): List<&2, Vote>
      }
      %Equal.sym(
        List<&2, String>,
        os2,
        os,
        eo
      ): {
        List.take(
          &2,
          Vote,
          Line.steps.go(~Q, 1n+p2, s2, c, cur, vs, Some{_}),
          List.length(&2, Vote, Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}))
        )
          == Line.steps.go(~Q, 1n+p, s, c, cur, vs, Some{os}): List<&2, Vote>
      }
      +up = U32.inc(cur)
      +ws = Epoch.list(~Q, s, c, up, os)
      +ws2 = Epoch.list(~Q, s2, c, up, os)
      Shared.List.take_append_both(
        Vote,
        vs,
        Line.steps.go(~Q, p, s, c, up, ws, Steps.next(c, ws)),
        Line.steps.go(~Q, p2, s2, c, up, ws2, Steps.next(c, ws2)),
        Line.steps.go_grow(
          ~Q,
          ~same,
          ~laws,
          p,
          p2,
          s,
          s2,
          c,
          up,
          ws,
          ws2,
          Steps.next(c, ws),
          Steps.next(c, ws2),
          Epoch.list_starts(~Q, ~same, ~laws, s, s2, c, up, os, gr),
          o2 => Epoch.list_cut(~Q, ~same, ~laws, s, s2, c, up, os, o2, gr),
          {==},
          {==},
          hf,
          gr
        )
      )

# the steps of a line whose first owners are m start those of a state that
# grows from it, whose first owners are m2, when m2 keeps m
def Line.steps_grow.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +s2: State(Q),
  +c: Chain,
  -xs: List<&2, Vote>,
  m: Maybe<&2, List<&2, String>>,
  m2: Maybe<&2, List<&2, String>>,
  hm: @ms: List<
    &2,
    String> -> {
    m == Some{ms}: Maybe<&2, List<&2, String>>
  } -> {m2 == Some{ms}: Maybe<&2, List<&2, String>>},
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {
  Maybe.bind(
    &2,
    List<&2, String>,
    List<&2, Vote>,
    m,
    ms => Some{
      Line.steps.of(
        ~Q,
        Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
        s,
        c,
        Epoch.list(~Q, s, c, 0, ms)
      )
    }
  )
    == Some{xs}: Maybe<&2, List<&2, Vote>>
} -> {
  Maybe.bind(
    &2,
    List<&2, Vote>,
    List<&2, Vote>,
    Maybe.bind(
      &2,
      List<&2, String>,
      List<&2, Vote>,
      m2,
      ms => Some{
        Line.steps.of(
          ~Q,
          Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
          s2,
          c,
          Epoch.list(~Q, s2, c, 0, ms)
        )
      }
    ),
    ys => Some{List.take(&2, Vote, ys, List.length(&2, Vote, xs))}
  )
    == Some{xs}: Maybe<&2, List<&2, Vote>>
}:
  match m:
    case None{}:
      e => Empty.absurd(
        {
          Maybe.bind(
            &2,
            List<&2, Vote>,
            List<&2, Vote>,
            Maybe.bind(
              &2,
              List<&2, String>,
              List<&2, Vote>,
              m2,
              ms => Some{
                Line.steps.of(
                  ~Q,
                  Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
                  s2,
                  c,
                  Epoch.list(~Q, s2, c, 0, ms)
                )
              }
            ),
            ys => Some{List.take(&2, Vote, ys, List.length(&2, Vote, xs))}
          )
            == Some{xs}: Maybe<&2, List<&2, Vote>>
        },
        Shared.Maybe.none_ne_some(List<&2, Vote>, xs, e)
      )
    case Some{+ms}:
      e =>
        %Shared.Maybe.some_inj(
          List<&2, Vote>,
          Line.steps.of(
            ~Q,
            Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
            s,
            c,
            Epoch.list(~Q, s, c, 0, ms)
          ),
          xs,
          e
        ): {
          Maybe.bind(
            &2,
            List<&2, Vote>,
            List<&2, Vote>,
            Maybe.bind(
              &2,
              List<&2, String>,
              List<&2, Vote>,
              m2,
              ms => Some{
                Line.steps.of(
                  ~Q,
                  Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
                  s2,
                  c,
                  Epoch.list(~Q, s2, c, 0, ms)
                )
              }
            ),
            ys => Some{List.take(&2, Vote, ys, List.length(&2, Vote, _))}
          )
            == Some{_}: Maybe<&2, List<&2, Vote>>
        }
        %Equal.sym(
          Maybe<&2, List<&2, String>>,
          m2,
          Some{ms},
          hm(ms)({==})
        ): {
          Maybe.bind(
            &2,
            List<&2, Vote>,
            List<&2, Vote>,
            Maybe.bind(
              &2,
              List<&2, String>,
              List<&2, Vote>,
              _,
              ms => Some{
                Line.steps.of(
                  ~Q,
                  Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
                  s2,
                  c,
                  Epoch.list(~Q, s2, c, 0, ms)
                )
              }
            ),
            ys => Some{
              List.take(
                &2,
                Vote,
                ys,
                List.length(
                  &2,
                  Vote,
                  Line.steps.of(
                    ~Q,
                    Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
                    s,
                    c,
                    Epoch.list(~Q, s, c, 0, ms)
                  )
                )
              )
            }
          )
            == Some{
              Line.steps.of(
                ~Q,
                Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
                s,
                c,
                Epoch.list(~Q, s, c, 0, ms)
              )
            }: Maybe<&2, List<&2, Vote>>
        }
        %Equal.sym(
          List<&2, Vote>,
          List.take(
            &2,
            Vote,
            Line.steps.of(
              ~Q,
              Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
              s2,
              c,
              Epoch.list(~Q, s2, c, 0, ms)
            ),
            List.length(
              &2,
              Vote,
              Line.steps.of(
                ~Q,
                Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
                s,
                c,
                Epoch.list(~Q, s, c, 0, ms)
              )
            )
          ),
          Line.steps.of(
            ~Q,
            Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
            s,
            c,
            Epoch.list(~Q, s, c, 0, ms)
          ),
          Line.steps.go_grow(
            ~Q,
            ~same,
            ~laws,
            Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
            Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s2, Slot.line_votes(c))),
            s,
            s2,
            c,
            0,
            Epoch.list(~Q, s, c, 0, ms),
            Epoch.list(~Q, s2, c, 0, ms),
            Steps.next(c, Epoch.list(~Q, s, c, 0, ms)),
            Steps.next(c, Epoch.list(~Q, s2, c, 0, ms)),
            Epoch.list_starts(~Q, ~same, ~laws, s, s2, c, 0, ms, gr),
            o => Epoch.list_cut(~Q, ~same, ~laws, s, s2, c, 0, ms, o, gr),
            {==},
            {==},
            State.size_under_grows(~Q, ~same, ~laws, s, s2, Slot.line_votes(c), gr),
            gr
          )
        ): {
          Some{
            _
          }
            == Some{
              Line.steps.of(
                ~Q,
                Tries.Trie.size(Cells.Cell<Entry<Q>>, State.under(~Q, s, Slot.line_votes(c))),
                s,
                c,
                Epoch.list(~Q, s, c, 0, ms)
              )
            }: Maybe<&2, List<&2, Vote>>
        }
        {==}

# a line's listing only grows at its end: the steps of a line start the steps
# of that line in any state that grows from it
law Line.steps_grow:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +s2: State(Q)
  for +c: Chain
  for xs: List<&2, Vote>
  {State.grows(~Q, ~same, s, s2) == True{}: Bool}
    -> {Line.steps(~Q, ~view, s, c) == Some{xs}: Maybe<&2, List<&2, Vote>>}
    -> {
      Maybe.bind(
        &2,
        List<&2, Vote>,
        List<&2, Vote>,
        Line.steps(~Q, ~view, s2, c),
        ys => Some{List.take(&2, Vote, ys, List.length(&2, Vote, xs))}
      )
        == Some{xs}: Maybe<&2, List<&2, Vote>>
    }

def Line.steps_grow(ty, same, laws, view, s, s2, c, xs):
  +gr => Line.steps_grow.at(
    ~ty,
    ~same,
    ~laws,
    ~view,
    s,
    s2,
    c,
    xs,
    Line.first(~ty, ~view, s, c),
    Line.first(~ty, ~view, s2, c),
    ms => Line.first.kept(~ty, ~same, ~laws, ~view, s, s2, c, gr, ms),
    gr
  )

# votes for the requests of the cells cs grow the state
def Vote.all.grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  cs: List<&2, Cells.Cell<Entry<Q>>>,
  +n: String,
  +s: State(Q)
) -> {State.grows(~Q, ~same, s, Vote.all(~Q, ~same, ~view, ~judge, cs, n, s)) == True{}: Bool}:
  match cs:
    case Nil{}:
      State.grows_refl(~Q, ~same, ~laws, s)
    case Con{Cells.One{Entry.Ask{+i, t, +q}}, +r}:
      +s1 = Vote.ask(~Q, ~same, ~view, ~judge, n, s, i, q, view(q))
      State.grows_trans(
        ~Q,
        ~same,
        ~laws,
        s,
        s1,
        Vote.all(~Q, ~same, ~view, ~judge, r, n, s1)
      )(
        Vote.ask.grows(~Q, ~same, ~laws, ~view, ~judge, n, s, i, q, view(q))
      )(Vote.all.grows(~Q, ~same, ~laws, ~view, ~judge, r, n, s1))
    case Con{Cells.One{Entry.Vote{x}}, r}:
      Vote.all.grows(~Q, ~same, ~laws, ~view, ~judge, r, n, s)
    case Con{Cells.One{Entry.At{w}}, r}:
      Vote.all.grows(~Q, ~same, ~laws, ~view, ~judge, r, n, s)
    case Con{Cells.One{Entry.Data{ws}}, r}:
      Vote.all.grows(~Q, ~same, ~laws, ~view, ~judge, r, n, s)
    case Con{Cells.Many{}, r}:
      Vote.all.grows(~Q, ~same, ~laws, ~view, ~judge, r, n, s)

# a node's votes only grow its state
law State.vote_grows:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>
  for +n: String
  for +s: State(Q)
  {State.grows(~Q, ~same, s, State.vote(~Q, ~same, ~view, ~judge, n, s)) == True{}: Bool}

def State.vote_grows(ty, same, laws, view, judge, n, s):
  Vote.all.grows(
    ~ty,
    ~same,
    ~laws,
    ~view,
    ~judge,
    Tries.Trie.values(Cells.Cell<Entry<ty>>, s),
    n,
    s
  )

# a state that grows keeps what it holds
def Data.has_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  s2: State(Q),
  +ws: List<&2, U32>,
  gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {Data.has(~Q, s, ws) == True{}: Bool} -> {Data.has(~Q, s2, ws) == True{}: Bool}:
  e =>
    %Equal.sym(
      Maybe<&2, List<&2, U32>>,
      State.data(~Q, s2, Hashes.Sha.hash(ws)),
      Some{ws},
      State.data_grows(
        ~Q,
        ~same,
        ~laws,
        s,
        s2,
        Hashes.Sha.hash(ws),
        ws
      )(
        gr
      )(
        Shared.Maybe.is_eq_sound(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          x => y => Shared.List.is_eq_sound(~U32, ~U32.is_eq, ~Shared.U32.laws(), x, y),
          State.data(~Q, s, Hashes.Sha.hash(ws)),
          Some{ws}
        )(e)
      )
    ): {
      Shared.Maybe.is_eq(
        ~List<&2, U32>,
        ~Shared.List.is_eq(~U32, ~U32.is_eq),
        _,
        Some{ws}
      )
        == True{}: Bool
    }
    Shared.Maybe.is_eq_refl(
      ~List<&2, U32>,
      ~Shared.List.is_eq(~U32, ~U32.is_eq),
      ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
      Some{ws}
    )

# a state that grows keeps all that it holds
def Data.holds_grows(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +s2: State(Q),
  ds: List<&2, List<&2, U32>>,
  +gr: {State.grows(~Q, ~same, s, s2) == True{}: Bool}
) -> {Data.holds(~Q, s, ds) == True{}: Bool} -> {Data.holds(~Q, s2, ds) == True{}: Bool}:
  match ds:
    case Nil{}:
      e => {==}
    case Con{+ws, +r}:
      +e =>
        %Equal.sym(
          Bool,
          Data.has(~Q, s2, ws),
          True{},
          Data.has_grows(
            ~Q,
            ~same,
            ~laws,
            s,
            s2,
            ws,
            gr
          )(Shared.List.all.if_hit(Data.has(~Q, s, ws), u => Data.holds(~Q, s, r))(e))
        ): {List.all.if(u => Data.holds(~Q, s2, r), _) == True{}: Bool}
        Data.holds_grows(
          ~Q,
          ~same,
          ~laws,
          s,
          s2,
          r,
          gr
        )(Shared.List.all.if_rest(Data.has(~Q, s, ws), u => Data.holds(~Q, s, r))(e))

# words put where their slot (whose cell is m) is empty, or holds them, are held
def Data.put_has(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +ws: List<&2, U32>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {
  List.any.if(u => Data.has(~Q, s, ws), Maybe.is_none(&2, Cells.Cell<Entry<Q>>, m)) == True{}: Bool
} -> {Data.has(~Q, State.put_data(~Q, ~same, s, ws), ws) == True{}: Bool}:
  match m:
    case None{}:
      f =>
        %Equal.sym(
          Maybe<&2, List<&2, U32>>,
          State.data(~Q, State.put_data(~Q, ~same, s, ws), Hashes.Sha.hash(ws)),
          Some{ws},
          State.put_data_get(~Q, ~same, s, ws)(em)
        ): {
          Shared.Maybe.is_eq(
            ~List<&2, U32>,
            ~Shared.List.is_eq(~U32, ~U32.is_eq),
            _,
            Some{ws}
          )
            == True{}: Bool
        }
        Shared.Maybe.is_eq_refl(
          ~List<&2, U32>,
          ~Shared.List.is_eq(~U32, ~U32.is_eq),
          ~Shared.List.laws(~U32, ~U32.is_eq, ~Shared.U32.laws()),
          Some{ws}
        )
    case Some{x}:
      f =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
          Some{x},
          em
        ): {
          Data.has(
            ~Q,
            Data.put.of(~Q, ~same, s, Slot.data(Hashes.Sha.hash(ws)), ws, _),
            ws
          )
            == True{}: Bool
        }
        f

# words put one after the other, each finding its slot empty or holding it,
# are all held
def State.put_datas_holds(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ds: List<&2, List<&2, U32>>,
  +s: State(Q)
) -> {
  Data.fresh(~Q, ~same, ds, s) == True{}: Bool
} -> {Data.holds(~Q, State.put_datas(~Q, ~same, ds, s), ds) == True{}: Bool}:
  match ds:
    case Nil{}:
      e => {==}
    case Con{+ws, +r}:
      +e =>
        +s1 = State.put_data(~Q, ~same, s, ws)
        +sn = State.put_datas(~Q, ~same, r, s1)
        +hit = List.any.if(
          u => Data.has(~Q, s, ws),
          Maybe.is_none(&2, Cells.Cell<Entry<Q>>, State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))))
        )
        %Equal.sym(
          Bool,
          Data.has(~Q, sn, ws),
          True{},
          Data.has_grows(
            ~Q,
            ~same,
            ~laws,
            s1,
            sn,
            ws,
            State.put_datas_grows(~Q, ~same, ~laws, r, s1)
          )(
            Data.put_has(
              ~Q,
              ~same,
              s,
              ws,
              State.get(~Q, s, Slot.data(Hashes.Sha.hash(ws))),
              {==}
            )(Shared.List.all.if_hit(hit, u => Data.fresh(~Q, ~same, r, s1))(e))
          )
        ): {List.all.if(u => Data.holds(~Q, sn, r), _) == True{}: Bool}
        State.put_datas_holds(
          ~Q,
          ~same,
          ~laws,
          r,
          s1
        )(Shared.List.all.if_rest(hit, u => Data.fresh(~Q, ~same, r, s1))(e))

# a sole owner's take-in of a fresh request holds the data of its verdict:
# each node of the verdict reads back, when the state held no other words
# under their hashes
def State.ask_data(
  ~Ty: Data,
  ~same: Ty -> Ty -> Bool,
  ~laws: Shared.Eq.Laws(Ty, same),
  ~view: Ty -> View,
  ~judge: State(Ty) -> Ty -> Maybe<&2, Vote> -> Maybe<&2, Verdict>,
  +n: String,
  s: State(Ty),
  +i: Id,
  t: String,
  +q: Ty,
  +c: Chain,
  o: Maybe<&2, List<&2, String>>,
  mk: Maybe<&2, List<&2, Bool>>,
  +e: U32,
  +h: U32,
  last: Maybe<&2, Where>,
  +k: Bool,
  +r: Maybe<&2, Hashes.Hash>,
  +ds: List<&2, List<&2, U32>>
) -> State.Sole(
  ~Ty,
  ~same,
  ~view,
  ~judge,
  n,
  s,
  i,
  t,
  q,
  c,
  o,
  mk,
  e,
  h,
  last,
  k,
  r,
  ds,
  {
    Data.fresh(
      ~Ty,
      ~same,
      ds,
      State.put(~Ty, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})
    )
      == True{}: Bool
  } -> {Data.holds(~Ty, State.ask(~Ty, ~same, ~view, ~judge, n, s, i, t, q), ds) == True{}: Bool}
):
  +h1 => +h2 => ht => ho => +hg => +hw => hv => hf =>
    +v = {View.On{c, o, mk}: View}
    +w = {Where{c, e, h}: Where}
    +x = {Vote{i, k, v, r}: Vote}
    +a = {Entry.Ask{i, t, q}: Entry<Ty>}
    +s1 = State.put(~Ty, ~same, s, Slot.ask(i), a)
    +sd = State.put_datas(~Ty, ~same, ds, s1)
    +s2 = State.put(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x})
    +hgd = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, sd, Slot.vote(w, n)),
      State.get(~Ty, s1, Slot.vote(w, n)),
      None{},
      State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.vote(w, n))({==}),
      hg
    )
    +hw2 = Equal.trans(
      Maybe<&2, Cells.Cell<Entry<Ty>>>,
      State.get(~Ty, s2, Slot.where(i)),
      State.get(~Ty, s1, Slot.where(i)),
      None{},
      Equal.trans(
        Maybe<&2, Cells.Cell<Entry<Ty>>>,
        State.get(~Ty, s2, Slot.where(i)),
        State.get(~Ty, sd, Slot.where(i)),
        State.get(~Ty, s1, Slot.where(i)),
        State.put_apart(~Ty, ~same, sd, Slot.vote(w, n), Entry.Vote{x}, Slot.where(i))({==}),
        State.put_datas_keeps(~Ty, ~same, ds, s1, Slot.where(i))({==})
      ),
      hw
    )
    +s3 = State.put(~Ty, ~same, s2, Slot.where(i), Entry.At{w})
    +gr12 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      sd,
      s2
    )(
      State.put_datas_grows(~Ty, ~same, ~laws, ds, s1)
    )(State.grows_put(~Ty, ~same, ~laws, sd, Slot.vote(w, n), Entry.Vote{x})(hgd))
    +gr13 = State.grows_trans(
      ~Ty,
      ~same,
      ~laws,
      s1,
      s2,
      s3
    )(gr12)(State.grows_put(~Ty, ~same, ~laws, s2, Slot.where(i), Entry.At{w})(hw2))
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Ty>>>, State.get(~Ty, s, Slot.ask(i)), None{}, h1):
      {
        Data.holds(
          ~Ty,
          State.ask.fresh(~Ty, ~same, ~view, ~judge, n, s, i, t, q, _),
          ds
        )
          == True{}: Bool
      }
    %Equal.sym(View, view(q), v, h2):
      {Data.holds(~Ty, Vote.ask(~Ty, ~same, ~view, ~judge, n, s1, i, q, _), ds) == True{}: Bool}
    %Equal.sym(Maybe<&2, Tip>, Line.tip(~Ty, ~view, s1, c), Some{Tip{e, [n], h, last}}, ht):
      {
        Data.holds(
          ~Ty,
          Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, _),
          ds
        )
          == True{}: Bool
      }
    %Equal.sym(
      State(Ty),
      Vote.cast(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, Some{Tip{e, [n], h, last}}),
      State.settle(~Ty, ~same, s2, w, [n]),
      Cast.puts(~Ty, ~same, ~view, ~judge, n, s1, c, i, q, v, e, h, last, k, r, ds)(hg)(hw)(hv)
    ): {Data.holds(~Ty, _, ds) == True{}: Bool}
    Data.holds_grows(
      ~Ty,
      ~same,
      ~laws,
      sd,
      State.settle(~Ty, ~same, s2, w, [n]),
      ds,
      State.grows_trans(
        ~Ty,
        ~same,
        ~laws,
        sd,
        s2,
        State.settle(~Ty, ~same, s2, w, [n])
      )(
        State.grows_put(~Ty, ~same, ~laws, sd, Slot.vote(w, n), Entry.Vote{x})(hgd)
      )(Settle.of.grows(~Ty, ~same, ~laws, s2, w, State.decide(~Ty, s2, w, [n])))
    )(State.put_datas_holds(~Ty, ~same, ~laws, ds, s1)(hf))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# a sole owner at the tip of a line takes a new request at once: it is decided
# with its verdict, and the state holds the verdict's data
law State.ask_sole:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for ~judge: State(Q) -> Q -> Maybe<&2, Vote> -> Maybe<&2, Verdict>
  for +n: String
  for +s: State(Q)
  for +i: Id
  for +t: String
  for +q: Q
  for +c: Chain
  for +o: Maybe<&2, List<&2, String>>
  for +mk: Maybe<&2, List<&2, Bool>>
  for +e: U32
  for +h: U32
  for +last: Maybe<&2, Where>
  for +k: Bool
  for +r: Maybe<&2, Hashes.Hash>
  for +ds: List<&2, List<&2, U32>>
  State.Sole(
    ~Q,
    ~same,
    ~view,
    ~judge,
    n,
    s,
    i,
    t,
    q,
    c,
    o,
    mk,
    e,
    h,
    last,
    k,
    r,
    ds,
    {
      Data.fresh(
        ~Q,
        ~same,
        ds,
        State.put(~Q, ~same, s, Slot.ask(i), Entry.Ask{i, t, q})
      )
        == True{}: Bool
    } -> (
      {
        State.status(
          ~Q,
          ~view,
          State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q),
          i
        )
          == Status.Done{k}: Status
      }
        & {
          State.decided(
            ~Q,
            ~view,
            State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q),
            i
          )
            == Some{Vote{i, k, View.On{c, o, mk}, r}}: Maybe<&2, Vote>
        }
        & {Data.holds(~Q, State.ask(~Q, ~same, ~view, ~judge, n, s, i, t, q), ds) == True{}: Bool}
    )
  )

def State.ask_sole(ty, same, laws, view, judge, n, s, i, t, q, c, o, mk, e, h, last, k, r, ds):
  +h1 => +hv => +ht => +ho => +hg => +hw => +hd => hf =>
    (
      State.ask_decides(
        ~ty,
        ~same,
        ~laws,
        ~view,
        ~judge,
        n,
        s,
        i,
        t,
        q,
        c,
        o,
        mk,
        e,
        h,
        last,
        k,
        r,
        ds
      )(h1)(hv)(ht)(ho)(hg)(hw)(hd),
      State.ask_decided(
        ~ty,
        ~same,
        ~laws,
        ~view,
        ~judge,
        n,
        s,
        i,
        t,
        q,
        c,
        o,
        mk,
        e,
        h,
        last,
        k,
        r,
        ds
      )(h1)(hv)(ht)(ho)(hg)(hw)(hd),
      State.ask_data(
        ~ty,
        ~same,
        ~laws,
        ~view,
        ~judge,
        n,
        s,
        i,
        t,
        q,
        c,
        o,
        mk,
        e,
        h,
        last,
        k,
        r,
        ds
      )(h1)(hv)(ht)(ho)(hg)(hw)(hd)(hf)
    )
