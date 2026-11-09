import Base
import ../../shared.bend as Shared
import ./shared/cell.bend as Cells
import ./shared/quorum.bend as Quorums
import ./shared/text.bend as Texts
import ./shared/shared/trie.bend as Tries

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
  View.root{owners: List<&2, String>}
  View.on{chain: Chain, owners: Maybe<&2, List<&2, String>>, makes: Maybe<&2, List<&2, Bool>>}

# a vote for a request, whose change has the view: its owners take it, or
# refuse it as stale
type Vote is Data:
  Vote{id: Id, takes: Bool, view: View}

# a place on a line: an epoch and a height in it
type Where is Data:
  Where{chain: Chain, epoch: U32, height: U32}

# a request of a change, with its time; a vote of a node; or a fact
type Entry<-Q: Data> is Data:
  Entry.ask{id: Id, time: String, ask: Q}
  Entry.vote{vote: Vote}
  Entry.at{at: Where}

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
  True{} <> True{} <> True{} <> Chain.key(c)

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
    case View.root{x} View.root{y}:
      Owners.is_eq(x, y)
    case View.on{c1, o1, m1} View.on{c2, o2, m2}:
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
    case Vote{i1, k1, v1} Vote{i2, k2, v2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(Shared.Bool.is_eq(k1, k2), View.is_eq(v1, v2)))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# a and b are the same place
def Where.is_eq(a: Where, b: Where) -> Bool:
  match a b:
    case Where{c1, e1, h1} Where{c2, e2, h2}:
      Bool.and(Chain.is_eq(c1, c2), Bool.and(U32.is_eq(e1, e2), U32.is_eq(h1, h2)))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.ask{i1, t1, q1} Entry.ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.vote{v1} Entry.vote{v2}:
      Vote.is_eq(v1, v2)
    case Entry.at{w1} Entry.at{w2}:
      Where.is_eq(w1, w2)
    case _ _:
      False{}

# Laws of equality
# ----------------

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Id.is_eq is True for a request and itself
def Id.is_eq_refl(a: Id) -> {Id.is_eq(a, a) == True{}: Bool}:
  match a:
    case Id{+w, +r}:
      Shared.Bool.and_both(String.eq(w, w), String.eq(r, r))(Texts.String.eq_refl(w))(Texts.String.eq_refl(r))

# a = b, from the two halves of an and that compares them
def Eq.both(
  -A: Data,
  -B: Data,
  -T: Data,
  mk: A -> B -> T,
  +x1: A,
  x2: A,
  +y1: B,
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

# the laws of Id.is_eq
def Id.laws() -> Shared.Eq.Laws(Id, Id.is_eq):
  (
    a => Id.is_eq_refl(a),
    a => b => Id.is_eq_sound(a, b)
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
      Shared.Bool.and_both(Id.is_eq(i, i), Sub.is_eq(k, k))(Id.is_eq_refl(i))(Shared.Eq.refl(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), k))

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
          Shared.Eq.sound(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), k1, k2)(Shared.Bool.and_true_right(x, y)(h))
        )

# the laws of Chain.is_eq
def Chain.laws() -> Shared.Eq.Laws(Chain, Chain.is_eq):
  (a => Chain.is_eq_refl(a), a => b => Chain.is_eq_sound(a, b))

# a = b, from the three parts of an and that compares them
def Eq.three(
  -A: Data,
  -B: Data,
  -C: Data,
  -T: Data,
  mk: A -> B -> C -> T,
  +x1: A,
  x2: A,
  +y1: B,
  y2: B,
  +z1: C,
  z2: C,
  ex: {x1 == x2: A},
  ey: {y1 == y2: B},
  ez: {z1 == z2: C}
) -> {mk(x1)(y1)(z1) == mk(x2)(y2)(z2): T}:
  %ex: {mk(x1)(y1)(z1) == mk(_)(y2)(z2): T}
  %ey: {mk(x1)(y1)(z1) == mk(x1)(_)(z2): T}
  %ez: {mk(x1)(y1)(z1) == mk(x1)(y1)(_): T}
  {==}

# View.is_eq is True for a view and itself
def View.is_eq_refl(a: View) -> {View.is_eq(a, a) == True{}: Bool}:
  match a:
    case View.root{x}:
      Shared.Eq.refl(~List<&2, String>, ~Owners.is_eq, Owners.laws(), x)
    case View.on{+c, +o, +m}:
      +mo = Shared.Maybe.is_eq(~List<&2, String>, ~Owners.is_eq, o, o)
      Shared.Bool.and_both(
        Chain.is_eq(c, c),
        Bool.and(mo, Sub.is_eq(m, m))
      )(Chain.is_eq_refl(c))(
        Shared.Bool.and_both(mo, Sub.is_eq(m, m))(
          Shared.Maybe.is_eq_refl(~List<&2, String>, ~Owners.is_eq, ~Owners.laws(), o)
        )(Shared.Eq.refl(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), m))
      )

# View.is_eq is True only for equal views
def View.is_eq_sound(a: View, b: View) -> {View.is_eq(a, b) == True{}: Bool} -> {a == b: View}:
  match a b:
    case View.root{+x} View.root{+y}:
      h =>
        %Shared.Eq.sound(~List<&2, String>, ~Owners.is_eq, Owners.laws(), x, y)(h): {View.root{x} == View.root{_}: View}
        {==}
    case View.on{+c1, +o1, +m1} View.on{+c2, +o2, +m2}:
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
          p => q => w => View.on{p, q, w},
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
          Shared.Eq.sound(~Maybe<&2, List<&2, Bool>>, ~Sub.is_eq, Sub.laws(), m1, m2)(Shared.Bool.and_true_right(mo, mm)(r))
        )
    case View.root{x} View.on{c, o, m}:
      h => Empty.absurd({View.root{x} == View.on{c, o, m}: View}, Shared.Bool.false_ne_true(h))
    case View.on{c, o, m} View.root{x}:
      h => Empty.absurd({View.on{c, o, m} == View.root{x}: View}, Shared.Bool.false_ne_true(h))

# the laws of View.is_eq
def View.laws() -> Shared.Eq.Laws(View, View.is_eq):
  (a => View.is_eq_refl(a), a => b => View.is_eq_sound(a, b))

# Vote.is_eq is True for a vote and itself
def Vote.is_eq_refl(a: Vote) -> {Vote.is_eq(a, a) == True{}: Bool}:
  match a:
    case Vote{+i, +k, +v}:
      +bk = Shared.Bool.is_eq(k, k)
      Shared.Bool.and_both(Id.is_eq(i, i), Bool.and(bk, View.is_eq(v, v)))(Id.is_eq_refl(i))(
        Shared.Bool.and_both(bk, View.is_eq(v, v))(Shared.Bool.is_eq_refl(k))(View.is_eq_refl(v))
      )

# Vote.is_eq is True only for equal votes
def Vote.is_eq_sound(a: Vote, b: Vote) -> {Vote.is_eq(a, b) == True{}: Bool} -> {a == b: Vote}:
  match a b:
    case Vote{+i1, +k1, +v1} Vote{+i2, +k2, +v2}:
      +h =>
        +x = Id.is_eq(i1, i2)
        +y = Shared.Bool.is_eq(k1, k2)
        +z = View.is_eq(v1, v2)
        +r = Shared.Bool.and_true_right(x, Bool.and(y, z))(h)
        Eq.three(
          Id,
          Bool,
          View,
          Vote,
          p => q => w => Vote{p, q, w},
          i1,
          i2,
          k1,
          k2,
          v1,
          v2,
          Id.is_eq_sound(i1, i2)(Shared.Bool.and_true_left(x, Bool.and(y, z))(h)),
          Shared.Bool.is_eq_sound(k1, k2)(Shared.Bool.and_true_left(y, z)(r)),
          View.is_eq_sound(v1, v2)(Shared.Bool.and_true_right(y, z)(r))
        )

# the laws of Vote.is_eq
def Vote.laws() -> Shared.Eq.Laws(Vote, Vote.is_eq):
  (a => Vote.is_eq_refl(a), a => b => Vote.is_eq_sound(a, b))

# Where.is_eq is True for a place and itself
def Where.is_eq_refl(a: Where) -> {Where.is_eq(a, a) == True{}: Bool}:
  match a:
    case Where{+c, +e, +h}:
      +ue = U32.is_eq(e, e)
      Shared.Bool.and_both(Chain.is_eq(c, c), Bool.and(ue, U32.is_eq(h, h)))(Chain.is_eq_refl(c))(
        Shared.Bool.and_both(ue, U32.is_eq(h, h))(Shared.U32.is_eq_refl(e))(Shared.U32.is_eq_refl(h))
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
    case Entry.ask{+i, +t, +q}:
      +st = String.eq(t, t)
      Shared.Bool.and_both(Id.is_eq(i, i), Bool.and(st, same(q, q)))(Id.is_eq_refl(i))(
        Shared.Bool.and_both(st, same(q, q))(Texts.String.eq_refl(t))(Shared.Eq.refl(~Q, ~same, laws, q))
      )
    case Entry.vote{v}:
      Vote.is_eq_refl(v)
    case Entry.at{w}:
      Where.is_eq_refl(w)

# Entry.is_eq is True only for equal entries
def Entry.is_eq_sound(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  a: Entry<Q>,
  b: Entry<Q>
) -> {Entry.is_eq(~Q, ~same, a, b) == True{}: Bool} -> {a == b: Entry<Q>}:
  match a b:
    case Entry.ask{+i1, +t1, +q1} Entry.ask{+i2, +t2, +q2}:
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
          p => u => w => Entry.ask{p, u, w},
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
    case Entry.vote{+v1} Entry.vote{+v2}:
      h =>
        %Vote.is_eq_sound(v1, v2)(h): {Entry.vote{v1} == Entry.vote{_}: Entry<Q>}
        {==}
    case Entry.at{+w1} Entry.at{+w2}:
      h =>
        %Where.is_eq_sound(w1, w2)(h): {Entry.at{w1} == Entry.at{_}: Entry<Q>}
        {==}
    case Entry.ask{i, t, q} Entry.vote{v}:
      h => Empty.absurd({Entry.ask{i, t, q} == Entry.vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.ask{i, t, q} Entry.at{w}:
      h => Empty.absurd({Entry.ask{i, t, q} == Entry.at{w}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.vote{v} Entry.ask{i, t, q}:
      h => Empty.absurd({Entry.vote{v} == Entry.ask{i, t, q}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.vote{v} Entry.at{w}:
      h => Empty.absurd({Entry.vote{v} == Entry.at{w}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.at{w} Entry.ask{i, t, q}:
      h => Empty.absurd({Entry.at{w} == Entry.ask{i, t, q}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.at{w} Entry.vote{v}:
      h => Empty.absurd({Entry.at{w} == Entry.vote{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))

# the laws of Entry.is_eq, by the laws of same
def Entry.laws(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same)
) -> Shared.Eq.Laws(Entry<Q>, Entry.is_eq(~Q, ~same)):
  (a => Entry.is_eq_refl(~Q, ~same, ~laws, a), a => b => Entry.is_eq_sound(~Q, ~same, ~laws, a, b))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

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
  Cells.Cell.agrees(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s, t)

# the cell of the slot k in s
def State.get(~Q: Data, s: State(Q), k: List<&2, Bool>) -> Maybe<&2, Cells.Cell<Entry<Q>>>:
  Tries.Trie.get(Cells.Cell<Entry<Q>>, s, k)

# the slots of s that start with k, under the rest of their keys
def State.under(~Q: Data, s: State(Q), k: List<&2, Bool>) -> State(Q):
  Tries.Trie.under(Cells.Cell<Entry<Q>>, s, k)

# a ledger that holds only the entry e, in the slot k
def State.one(~Q: Data, k: List<&2, Bool>, e: Entry<Q>) -> State(Q):
  Tries.Trie.one(Cells.Cell<Entry<Q>>, k, Cells.one{e})

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
    case Some{Entry.ask{i, t, q}}:
      Some{Asked{t, q}}
    case _:
      None{}

# the request i, when s holds it
def State.asked(~Q: Data, s: State(Q), i: Id) -> Maybe<&2, Asked<Q>>:
  Asked.of(~Q, State.entry(~Q, s, Slot.ask(i)))

# the place in the entry m, when it is a fact
def Where.of(~Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, Where>:
  match m:
    case Some{Entry.at{w}}:
      Some{w}
    case _:
      None{}

# Buckets
# -------

# the ballot of a cell of a bucket: a vote, void when it holds anything else,
# none when it is empty
def Entry.ballot(~Q: Data, m: Maybe<&2, Cells.Cell<Entry<Q>>>) -> Quorums.Ballot(Vote):
  match m:
    case None{}:
      None{}
    case Some{Cells.one{Entry.vote{v}}}:
      Some{Some{v}}
    case Some{c}:
      Some{None{}}

# the ballots of the nodes ms in the bucket b, each read once
def Bucket.ballots(~Q: Data, +b: State(Q), ms: List<&2, String>) -> List<&2, Quorums.Ballot(Vote)>:
  match ms:
    case Nil{}:
      []
    case Con{m, r}:
      Entry.ballot(~Q, State.get(~Q, b, Slot.ballot(m))) <> Bucket.ballots(~Q, b, r)

# what the ballots of ms in the bucket b decide
def Bucket.decide(~Q: Data, b: State(Q), ms: List<&2, String>) -> Maybe<&2, Vote>:
  Quorums.Quorum.decide(~Vote, ~Vote.is_eq, Bucket.ballots(~Q, b, ms))

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
# a sync keeps is built of reads that it keeps (Maybe.then_kept).

# the owners of a view that starts a store
def Root.owners.view(v: View) -> Maybe<&2, List<&2, String>>:
  match v:
    case View.root{ms}:
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
  Shared.Maybe.then(Asked<Q>, List<&2, String>, State.asked(~Q, s, r), a => Root.owners.ask(~Q, ~view, a))

# the owners that the vote v gives the line c, when it takes a request of c
# that gives it owners
def Owners.of(+c: Chain, v: Vote) -> Maybe<&2, List<&2, String>>:
  match v:
    case Vote{i, True{}, View.on{c2, Some{os}, mk}}:
      Shared.Maybe.when(List<&2, String>, Chain.is_eq(c2, c), u => Some{os})
    case _:
      None{}

# the owners of the epoch after e of c, whose owners are ms, from the fact w
# where it began: the owners that the step there gives
def Epoch.at(~Q: Data, s: State(Q), +c: Chain, +e: U32, ms: List<&2, String>, w: Where) -> Maybe<&2, List<&2, String>>:
  match w:
    case Where{c2, e2, h}:
      Shared.Maybe.when(
        List<&2, String>,
        Bool.and(Chain.is_eq(c2, c), U32.is_eq(e2, e)),
        u => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, s, Where{c, e, h}, ms), v => Owners.of(c, v))
      )

# the owners of the epoch after e of c, whose owners are ms
def Epoch.next(~Q: Data, +s: State(Q), +c: Chain, +e: U32, ms: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  Shared.Maybe.then(
    Where,
    List<&2, String>,
    Where.of(~Q, State.entry(~Q, s, Slot.epoch(c, U32.inc(e)))),
    w => Epoch.at(~Q, s, c, e, ms, w)
  )

# the owners of the epoch n after cur of c, whose owners are m
def Epoch.up(~Q: Data, n: Nat, +s: State(Q), +c: Chain, +cur: U32, m: Maybe<&2, List<&2, String>>) -> Maybe<&2, List<&2, String>>:
  match n:
    case 0n:
      m
    case 1n+p:
      Shared.Maybe.then(List<&2, String>, List<&2, String>, m, ms => Epoch.up(~Q, p, s, c, U32.inc(cur), Epoch.next(~Q, s, c, cur, ms)))

# the owners of the epoch e of the root line of r
def Root.at(~Q: Data, ~view: Q -> View, +s: State(Q), +r: Id, e: U32) -> Maybe<&2, List<&2, String>>:
  Epoch.up(~Q, U32.to_nat(e), s, Chain{r, None{}}, 0, Root.owners(~Q, ~view, s, r))

# the owners ms, when the vote v makes the line of the key k
def Made.vote(+k: List<&2, Bool>, ms: List<&2, String>, v: Vote) -> Maybe<&2, List<&2, String>>:
  match v:
    case Vote{i, True{}, View.on{c, o, Some{k2}}}:
      Shared.Maybe.when(List<&2, String>, Shared.List.is_eq(~Bool, ~Shared.Bool.is_eq, k2, k), u => Some{ms})
    case _:
      None{}

# the first owners of the line of the key k below the root of r, from the
# fact w where it was made: the owners of the root's epoch there
def Made.at(~Q: Data, ~view: Q -> View, +s: State(Q), +r: Id, +k: List<&2, Bool>, w: Where) -> Maybe<&2, List<&2, String>>:
  match w:
    case Where{+c2, +e, h}:
      Shared.Maybe.when(
        List<&2, String>,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Shared.Maybe.then(
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          +ms => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, s, Where{c2, e, h}, ms), v => Made.vote(k, ms, v))
        )
      )

# the owners of the first epoch of the line c
def Line.first(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain) -> Maybe<&2, List<&2, String>>:
  match c:
    case Chain{r, None{}}:
      Root.owners(~Q, ~view, s, r)
    case Chain{+r, Some{+k}}:
      Shared.Maybe.then(
        Where,
        List<&2, String>,
        Where.of(~Q, State.entry(~Q, s, Slot.made(Chain{r, Some{k}}))),
        w => Made.at(~Q, ~view, s, r, k, w)
      )

# the owners of the epoch e of the line c
def Line.owners(~Q: Data, ~view: Q -> View, +s: State(Q), +c: Chain, e: U32) -> Maybe<&2, List<&2, String>>:
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

# Status
# ------

# the vote v, when it is for the request i
def Vote.for(+i: Id, v: Vote) -> Maybe<&2, Vote>:
  match v:
    case Vote{+j, k, u}:
      Shared.Maybe.when(Vote, Id.is_eq(j, i), w => Some{Vote{j, k, u}})

# the vote that decided i at the place w, when the step there is for i
def Where.at(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id, w: Where) -> Maybe<&2, Vote>:
  match w:
    case Where{+c, +e, h}:
      Shared.Maybe.then(
        List<&2, String>,
        Vote,
        Line.owners(~Q, ~view, s, c, e),
        ms => Shared.Maybe.then(Vote, Vote, State.decide(~Q, s, Where{c, e, h}, ms), v => Vote.for(i, v))
      )

# the vote that decided the request i, when s holds where and it checks
def State.decided(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Maybe<&2, Vote>:
  Shared.Maybe.then(Where, Vote, Where.of(~Q, State.entry(~Q, s, Slot.where(i))), w => Where.at(~Q, ~view, s, i, w))

# where a request is. Done: a step decided it, and took it or refused it as
# stale. Pending: no step decided it yet. Refused: it is contradicted. NotSeen:
# the ledger does not hold it.
type Status is Data:
  Status.done{takes: Bool}
  Status.pending{}
  Status.refused{}
  Status.not_seen{}

# the status of a request whose change has the view v, decided by the vote m
def Status.of.view(v: View, m: Maybe<&2, Vote>) -> Status:
  match v m:
    case View.root{ms} w:
      Status.done{True{}}
    case View.on{c, o, mk} Some{Vote{j, k, u}}:
      Status.done{k}
    case View.on{c, o, mk} None{}:
      Status.pending{}

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
      Status.not_seen{}
    case Some{Cells.many{}}:
      Status.refused{}
    case Some{Cells.one{Entry.ask{j, t, q}}}:
      Status.of.view(view(q), State.decided(~Q, ~view, s, i))
    case Some{Cells.one{e}}:
      Status.not_seen{}

# where the request i is
def State.status(~Q: Data, ~view: Q -> View, +s: State(Q), +i: Id) -> Status:
  Status.of(~Q, ~view, s, i, State.get(~Q, s, Slot.ask(i)))

# Changes
# -------

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
      State.put(~Q, ~same, s, k, Entry.at{w})
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
    case True{} View.on{+c, Some{os}, mk}:
      Fact.put(~Q, ~same, s, Slot.epoch(c, U32.inc(Where.epoch(w))), w)
    case True{} View.on{Chain{r, b}, None{}, Some{key}}:
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
    case Some{Vote{i, k, v}}:
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

# the verdict on the request q, whose view is v, after the step at last:
# refused when it makes a line that exists, else judge's (none: wait)
def Vote.verdict(
  ~Q: Data,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  +s: State(Q),
  q: Q,
  v: View,
  last: Maybe<&2, Where>
) -> Maybe<&2, Bool>:
  match v:
    case View.on{Chain{r, b}, o, Some{m}}:
      Shared.Bool.when(
        Maybe<&2, Bool>,
        Maybe.is_none(&2, List<&2, String>, Line.first(~Q, ~view, s, Chain{r, Some{m}})),
        u => judge(s, q, last),
        u => Some{False{}}
      )
    case w:
      judge(s, q, last)

# s with the vote for i of the view v (when held), with the verdict m (none:
# no vote)
def Vote.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  held: Bool,
  m: Maybe<&2, Bool>,
  s: State(Q),
  k: List<&2, Bool>,
  i: Id,
  v: View
) -> State(Q):
  match held m:
    case True{} Some{x}:
      State.put(~Q, ~same, s, k, Entry.vote{Vote{i, x, v}})
    case h w:
      s

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a proof's statement, or code that the laws split on, keeps each and/or as one value
# s after the node n votes for the request i of q, whose view v changes the
# line c, at the tip m of c, when it may; then the facts of what is decided
def Vote.cast(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  +n: String,
  +s: State(Q),
  c: Chain,
  +i: Id,
  q: Q,
  +v: View,
  m: Maybe<&2, Tip>
) -> State(Q):
  match m:
    case None{}:
      s
    case Some{Tip{e, +ms, h, last}}:
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
          Vote.verdict(~Q, ~view, ~judge, s, q, v, last),
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
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  i: Id,
  q: Q,
  v: View
) -> State(Q):
  match v:
    case View.root{ms}:
      s
    case View.on{+c, o, mk}:
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
        View.on{c, o, mk},
        Line.tip(~Q, ~view, s, c)
      )

# s after the node n took in the request i of q at the time t, whose cell in s
# is m: a request that s holds already changes nothing
def State.ask.fresh(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~view: Q -> View,
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
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
        State.put(~Q, ~same, s, Slot.ask(i), Entry.ask{i, t, q}),
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
  ~judge: State(Q) -> Q -> Maybe<&2, Where> -> Maybe<&2, Bool>,
  n: String,
  +s: State(Q),
  +i: Id,
  t: String,
  q: Q
) -> State(Q):
  State.ask.fresh(~Q, ~same, ~view, ~judge, n, s, i, t, q, State.get(~Q, s, Slot.ask(i)))

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
    ~(x => Cells.Cell.join_idem(~Entry<ty>, ~Entry.is_eq(~ty, ~same), ~Entry.laws(~ty, ~same, ~laws), x)),
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
    ~(x => Cells.Cell.join_idem(~Entry<ty>, ~Entry.is_eq(~ty, ~same), ~Entry.laws(~ty, ~same, ~laws), x)),
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
# What a holder reads stays when it syncs with a holder that agrees with it:
# a sync that contradicts nothing only adds.

# a read f of the entry of a slot stays (f gives nothing of no entry)
def State.read_kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~W: Data,
  f: Maybe<&2, Entry<Q>> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  +s: State(Q),
  t: State(Q),
  +k: List<&2, Bool>,
  -w: W
) -> {
  State.agrees(~Q, ~same, s, t) == True{}: Bool
} -> {
  f(State.entry(~Q, s, k)) == Some{w}: Maybe<&2, W>
} -> {f(State.entry(~Q, State.join(~Q, ~same, s, t), k)) == Some{w}: Maybe<&2, W>}:
  Cells.Cell.through(~Entry<Q>, ~W, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), f, fnone, s, t, k, w)

# a cell that is many joined with anything gives a void ballot
def Ballot.many(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>
) -> {
  Entry.ballot(
    ~Q,
    Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), Some{Cells.many{}}, m)
  )
    == Some{None{}}: Quorums.Ballot(Vote)
}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

# the ballot of one entry is kept as itself
def Ballot.refl(
  ~Q: Data,
  e: Entry<Q>
) -> {
  Quorums.Quorum.kept(~Vote, ~Vote.is_eq, Entry.ballot(~Q, Some{Cells.one{e}}), Entry.ballot(~Q, Some{Cells.one{e}}))
    == True{}: Bool
}:
  match e:
    case Entry.vote{v}:
      Vote.is_eq_refl(v)
    case Entry.ask{i, t, q}:
      {==}
    case Entry.at{w}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the ballot at the slot k of b1 (its cell m) is kept in b1 joined with b2
def Ballot.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +b1: State(Q),
  +b2: State(Q),
  +k: List<&2, Bool>,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  em: {State.get(~Q, b1, k) == m: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> {
  State.agrees(~Q, ~same, b1, b2) == True{}: Bool
} -> {
  Quorums.Quorum.kept(
    ~Vote,
    ~Vote.is_eq,
    Entry.ballot(~Q, m),
    Entry.ballot(~Q, State.get(~Q, State.join(~Q, ~same, b1, b2), k))
  )
    == True{}: Bool
}:
  match m:
    case None{}:
      ag => {==}
    case Some{Cells.many{}}:
      ag =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.join(~Q, ~same, b1, b2), k),
          Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), State.get(~Q, b1, k), State.get(~Q, b2, k)),
          Tries.Trie.get_union(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), b1, b2, k)
        ): {Quorums.Quorum.kept(~Vote, ~Vote.is_eq, Some{None{}}, Entry.ballot(~Q, _)) == True{}: Bool}
        %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, b1, k), Some{Cells.many{}}, em):
          {
            Quorums.Quorum.kept(
              ~Vote,
              ~Vote.is_eq,
              Some{None{}},
              Entry.ballot(~Q, Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), _, State.get(~Q, b2, k)))
            )
              == True{}: Bool
          }
        %Equal.sym(
          Quorums.Ballot(Vote),
          Entry.ballot(~Q, Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), Some{Cells.many{}}, State.get(~Q, b2, k))),
          Some{None{}},
          Ballot.many(~Q, ~same, State.get(~Q, b2, k))
        ): {Quorums.Quorum.kept(~Vote, ~Vote.is_eq, Some{None{}}, _) == True{}: Bool}
        {==}
    case Some{Cells.one{e}}:
      ag =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.join(~Q, ~same, b1, b2), k),
          Some{Cells.one{e}},
          Cells.Cell.agrees_kept(~Entry<Q>, ~Entry.is_eq(~Q, ~same), ~Entry.laws(~Q, ~same, ~laws), b1, b2, k, e)(ag)(em)
        ): {
          Quorums.Quorum.kept(~Vote, ~Vote.is_eq, Entry.ballot(~Q, Some{Cells.one{e}}), Entry.ballot(~Q, _))
            == True{}: Bool
        }
        Ballot.refl(~Q, e)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the ballots of ms in b1 are kept in b1 joined with b2, when they agree
def Ballots.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +b1: State(Q),
  +b2: State(Q),
  ms: List<&2, String>,
  +ag: {State.agrees(~Q, ~same, b1, b2) == True{}: Bool}
) -> {
  Quorums.Quorum.keeps(
    ~Vote,
    ~Vote.is_eq,
    Bucket.ballots(~Q, b1, ms),
    Bucket.ballots(~Q, State.join(~Q, ~same, b1, b2), ms)
  )
    == True{}: Bool
}:
  match ms:
    case Nil{}:
      {==}
    case Con{+m, +r}:
      +k = Slot.ballot(m)
      Shared.Bool.and_both(
        Quorums.Quorum.kept(
          ~Vote,
          ~Vote.is_eq,
          Entry.ballot(~Q, State.get(~Q, b1, k)),
          Entry.ballot(~Q, State.get(~Q, State.join(~Q, ~same, b1, b2), k))
        ),
        Quorums.Quorum.keeps(
          ~Vote,
          ~Vote.is_eq,
          Bucket.ballots(~Q, b1, r),
          Bucket.ballots(~Q, State.join(~Q, ~same, b1, b2), r)
        )
      )(Ballot.kept.at(~Q, ~same, ~laws, b1, b2, k, State.get(~Q, b1, k), {==})(ag))(
        Ballots.kept(~Q, ~same, ~laws, b1, b2, r, ag)
      )

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# what the owners decide at a place stays decided after a sync that agrees:
# a step is final
law State.decide_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for +s: State(Q)
  for +t: State(Q)
  for +w: Where
  for +ms: List<&2, String>
  for +v: Vote
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {State.decide(~Q, s, w, ms) == Some{v}: Maybe<&2, Vote>}
    -> {State.decide(~Q, State.join(~Q, ~same, s, t), w, ms) == Some{v}: Maybe<&2, Vote>}

def State.decide_kept(ty, same, laws, s, t, w, ms, v):
  match w:
    case Where{c, e, h}:
      +p = Slot.bucket(c, e, h)
      +ag => h0 =>
        %Equal.sym(
          State(ty),
          State.under(~ty, State.join(~ty, ~same, s, t), p),
          State.join(~ty, ~same, State.under(~ty, s, p), State.under(~ty, t, p)),
          Tries.Trie.under_union(~Cells.Cell<Entry<ty>>, ~Cells.Cell.join(~Entry<ty>, ~Entry.is_eq(~ty, ~same)), s, t, p)
        ): {Bucket.decide(~ty, _, ms) == Some{v}: Maybe<&2, Vote>}
        Quorums.Quorum.decide_kept(
          ~Vote,
          ~Vote.is_eq,
          ~Vote.laws(),
          Bucket.ballots(~ty, State.under(~ty, s, p), ms),
          Bucket.ballots(~ty, State.join(~ty, ~same, State.under(~ty, s, p), State.under(~ty, t, p)), ms),
          v
        )(
          Ballots.kept(
            ~ty,
            ~same,
            ~laws,
            State.under(~ty, s, p),
            State.under(~ty, t, p),
            ms,
            Cells.Cell.agrees_under(~Entry<ty>, ~Entry.is_eq(~ty, ~same), s, t, p)(ag)
          )
        )(h0)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# the owners of a root line stay
def Root.owners.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +r: Id,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Root.owners(~Q, ~view, s, r) == Some{a}: Maybe<&2, List<&2, String>>} -> {Root.owners(~Q, ~view, State.join(~Q, ~same, s, t), r) == Some{a}: Maybe<&2, List<&2, String>>}:
  Shared.Maybe.then_kept(
    Asked<Q>,
    List<&2, String>,
    State.asked(~Q, s, r),
    State.asked(~Q, State.join(~Q, ~same, s, t), r),
    x => Root.owners.ask(~Q, ~view, x),
    x => Root.owners.ask(~Q, ~view, x),
    a,
    x => State.read_kept(~Q, ~same, ~laws, ~Asked<Q>, m => Asked.of(~Q, m), {==}, s, t, Slot.ask(r), x)(ag),
    x => h => h
  )

# the owners of the epoch after e, from the fact w, stay
def Epoch.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  w: Where,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Epoch.at(~Q, s, c, e, ms, w) == Some{a}: Maybe<&2, List<&2, String>>} -> {Epoch.at(~Q, State.join(~Q, ~same, s, t), c, e, ms, w) == Some{a}: Maybe<&2, List<&2, String>>}:
  match w:
    case Where{c2, e2, +h}:
      +p = {Where{c, e, h}: Where}
      Shared.Maybe.when_kept(
        List<&2, String>,
        Bool.and(Chain.is_eq(c2, c), U32.is_eq(e2, e)),
        u => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, s, p, ms), v => Owners.of(c, v)),
        u => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, State.join(~Q, ~same, s, t), p, ms), v => Owners.of(c, v)),
        a,
        Shared.Maybe.then_kept(
          Vote,
          List<&2, String>,
          State.decide(~Q, s, p, ms),
          State.decide(~Q, State.join(~Q, ~same, s, t), p, ms),
          v => Owners.of(c, v),
          v => Owners.of(c, v),
          a,
          x => State.decide_kept(~Q, ~same, ~laws, s, t, p, ms, x)(ag),
          x => h => h
        )
      )

# the owners of the epoch after e stay
def Epoch.next.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  +s: State(Q),
  +t: State(Q),
  +c: Chain,
  +e: U32,
  +ms: List<&2, String>,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Epoch.next(~Q, s, c, e, ms) == Some{a}: Maybe<&2, List<&2, String>>} -> {Epoch.next(~Q, State.join(~Q, ~same, s, t), c, e, ms) == Some{a}: Maybe<&2, List<&2, String>>}:
  +k = Slot.epoch(c, U32.inc(e))
  Shared.Maybe.then_kept(
    Where,
    List<&2, String>,
    Where.of(~Q, State.entry(~Q, s, k)),
    Where.of(~Q, State.entry(~Q, State.join(~Q, ~same, s, t), k)),
    w => Epoch.at(~Q, s, c, e, ms, w),
    w => Epoch.at(~Q, State.join(~Q, ~same, s, t), c, e, ms, w),
    a,
    x => State.read_kept(~Q, ~same, ~laws, ~Where, m => Where.of(~Q, m), {==}, s, t, k, x)(ag),
    w => Epoch.at.kept(~Q, ~same, ~laws, s, t, c, e, ms, w, ag, a)
  )

# the owners of the epoch n after cur stay, when those of cur do (hm)
def Epoch.up.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  n: Nat,
  +s: State(Q),
  +t: State(Q),
  +c: Chain,
  +cur: U32,
  m: Maybe<&2, List<&2, String>>,
  -m2: Maybe<&2, List<&2, String>>,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  hm: @x: List<&2, String> -> {m == Some{x}: Maybe<&2, List<&2, String>>} -> {m2 == Some{x}: Maybe<&2, List<&2, String>>},
  +a: List<&2, String>
) -> {Epoch.up(~Q, n, s, c, cur, m) == Some{a}: Maybe<&2, List<&2, String>>} -> {Epoch.up(~Q, n, State.join(~Q, ~same, s, t), c, cur, m2) == Some{a}: Maybe<&2, List<&2, String>>}:
  match n:
    case 0n:
      hm(a)
    case 1n+p:
      +up = U32.inc(cur)
      Shared.Maybe.then_kept(
        List<&2, String>,
        List<&2, String>,
        m,
        m2,
        ms => Epoch.up(~Q, p, s, c, up, Epoch.next(~Q, s, c, cur, ms)),
        ms => Epoch.up(~Q, p, State.join(~Q, ~same, s, t), c, up, Epoch.next(~Q, State.join(~Q, ~same, s, t), c, cur, ms)),
        a,
        hm,
        +ms => Epoch.up.kept(
          ~Q, ~same, ~laws,
          p,
          s,
          t,
          c,
          up,
          Epoch.next(~Q, s, c, cur, ms),
          Epoch.next(~Q, State.join(~Q, ~same, s, t), c, cur, ms),
          ag,
          x => Epoch.next.kept(~Q, ~same, ~laws, s, t, c, cur, ms, ag, x),
          a
        )
      )

# the owners of an epoch of a root line stay
def Root.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +r: Id,
  e: U32,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Root.at(~Q, ~view, s, r, e) == Some{a}: Maybe<&2, List<&2, String>>} -> {Root.at(~Q, ~view, State.join(~Q, ~same, s, t), r, e) == Some{a}: Maybe<&2, List<&2, String>>}:
  Epoch.up.kept(
    ~Q, ~same, ~laws,
    U32.to_nat(e),
    s,
    t,
    Chain{r, None{}},
    0,
    Root.owners(~Q, ~view, s, r),
    Root.owners(~Q, ~view, State.join(~Q, ~same, s, t), r),
    ag,
    x => Root.owners.kept(~Q, ~same, ~laws, ~view, s, t, r, ag, x),
    a
  )

# the first owners of a line, from the fact w where it was made, stay
def Made.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +r: Id,
  +k: List<&2, Bool>,
  w: Where,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Made.at(~Q, ~view, s, r, k, w) == Some{a}: Maybe<&2, List<&2, String>>} -> {Made.at(~Q, ~view, State.join(~Q, ~same, s, t), r, k, w) == Some{a}: Maybe<&2, List<&2, String>>}:
  match w:
    case Where{+c2, +e, +h}:
      +p = {Where{c2, e, h}: Where}
      Shared.Maybe.when_kept(
        List<&2, String>,
        Chain.is_eq(c2, Chain{r, None{}}),
        u => Shared.Maybe.then(
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          ms => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, s, p, ms), v => Made.vote(k, ms, v))
        ),
        u => Shared.Maybe.then(
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, State.join(~Q, ~same, s, t), r, e),
          ms => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, State.join(~Q, ~same, s, t), p, ms), v => Made.vote(k, ms, v))
        ),
        a,
        Shared.Maybe.then_kept(
          List<&2, String>,
          List<&2, String>,
          Root.at(~Q, ~view, s, r, e),
          Root.at(~Q, ~view, State.join(~Q, ~same, s, t), r, e),
          ms => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, s, p, ms), v => Made.vote(k, ms, v)),
          ms => Shared.Maybe.then(Vote, List<&2, String>, State.decide(~Q, State.join(~Q, ~same, s, t), p, ms), v => Made.vote(k, ms, v)),
          a,
          x => Root.at.kept(~Q, ~same, ~laws, ~view, s, t, r, e, ag, x),
          +ms => Shared.Maybe.then_kept(
            Vote,
            List<&2, String>,
            State.decide(~Q, s, p, ms),
            State.decide(~Q, State.join(~Q, ~same, s, t), p, ms),
            v => Made.vote(k, ms, v),
            v => Made.vote(k, ms, v),
            a,
            x => State.decide_kept(~Q, ~same, ~laws, s, t, p, ms, x)(ag),
            x => h0 => h0
          )
        )
      )

# the owners of the first epoch of a line stay
def Line.first.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  c: Chain,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Line.first(~Q, ~view, s, c) == Some{a}: Maybe<&2, List<&2, String>>} -> {Line.first(~Q, ~view, State.join(~Q, ~same, s, t), c) == Some{a}: Maybe<&2, List<&2, String>>}:
  match c:
    case Chain{r, None{}}:
      Root.owners.kept(~Q, ~same, ~laws, ~view, s, t, r, ag, a)
    case Chain{+r, Some{+k}}:
      +slot = Slot.made(Chain{r, Some{k}})
      Shared.Maybe.then_kept(
        Where,
        List<&2, String>,
        Where.of(~Q, State.entry(~Q, s, slot)),
        Where.of(~Q, State.entry(~Q, State.join(~Q, ~same, s, t), slot)),
        w => Made.at(~Q, ~view, s, r, k, w),
        w => Made.at(~Q, ~view, State.join(~Q, ~same, s, t), r, k, w),
        a,
        x => State.read_kept(~Q, ~same, ~laws, ~Where, m => Where.of(~Q, m), {==}, s, t, slot, x)(ag),
        w => Made.at.kept(~Q, ~same, ~laws, ~view, s, t, r, k, w, ag, a)
      )

# the owners of an epoch of a line stay
def Line.owners.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +c: Chain,
  e: U32,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: List<&2, String>
) -> {Line.owners(~Q, ~view, s, c, e) == Some{a}: Maybe<&2, List<&2, String>>} -> {Line.owners(~Q, ~view, State.join(~Q, ~same, s, t), c, e) == Some{a}: Maybe<&2, List<&2, String>>}:
  Epoch.up.kept(
    ~Q, ~same, ~laws,
    U32.to_nat(e),
    s,
    t,
    c,
    0,
    Line.first(~Q, ~view, s, c),
    Line.first(~Q, ~view, State.join(~Q, ~same, s, t), c),
    ag,
    x => Line.first.kept(~Q, ~same, ~laws, ~view, s, t, c, ag, x),
    a
  )

# the vote that decided i at the place w stays
def Where.at.kept(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  w: Where,
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool},
  +a: Vote
) -> {Where.at(~Q, ~view, s, i, w) == Some{a}: Maybe<&2, Vote>} -> {Where.at(~Q, ~view, State.join(~Q, ~same, s, t), i, w) == Some{a}: Maybe<&2, Vote>}:
  match w:
    case Where{+c, +e, +h}:
      +p = {Where{c, e, h}: Where}
      Shared.Maybe.then_kept(
        List<&2, String>,
        Vote,
        Line.owners(~Q, ~view, s, c, e),
        Line.owners(~Q, ~view, State.join(~Q, ~same, s, t), c, e),
        ms => Shared.Maybe.then(Vote, Vote, State.decide(~Q, s, p, ms), v => Vote.for(i, v)),
        ms => Shared.Maybe.then(Vote, Vote, State.decide(~Q, State.join(~Q, ~same, s, t), p, ms), v => Vote.for(i, v)),
        a,
        x => Line.owners.kept(~Q, ~same, ~laws, ~view, s, t, c, e, ag, x),
        +ms => Shared.Maybe.then_kept(
          Vote,
          Vote,
          State.decide(~Q, s, p, ms),
          State.decide(~Q, State.join(~Q, ~same, s, t), p, ms),
          v => Vote.for(i, v),
          v => Vote.for(i, v),
          a,
          x => State.decide_kept(~Q, ~same, ~laws, s, t, p, ms, x)(ag),
          x => h0 => h0
        )
      )

# the vote that decided a request stays after a sync that agrees
law State.decided_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  for +a: Vote
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {State.decided(~Q, ~view, s, i) == Some{a}: Maybe<&2, Vote>}
    -> {State.decided(~Q, ~view, State.join(~Q, ~same, s, t), i) == Some{a}: Maybe<&2, Vote>}

def State.decided_kept(ty, same, laws, view, s, t, i, a):
  +ag =>
    +k = Slot.where(i)
    Shared.Maybe.then_kept(
      Where,
      Vote,
      Where.of(~ty, State.entry(~ty, s, k)),
      Where.of(~ty, State.entry(~ty, State.join(~ty, ~same, s, t), k)),
      w => Where.at(~ty, ~view, s, i, w),
      w => Where.at(~ty, ~view, State.join(~ty, ~same, s, t), i, w),
      a,
      x => State.read_kept(~ty, ~same, ~laws, ~Where, m => Where.of(~ty, m), {==}, s, t, k, x)(ag),
      w => Where.at.kept(~ty, ~same, ~laws, ~view, s, t, i, w, ag, a)
    )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the verdict of a status, if it is done
def Status.verdict(st: Status) -> Maybe<&2, Bool>:
  match st:
    case Status.done{k}:
      Some{k}
    case _:
      None{}

# st is refused
def Status.is_refused(st: Status) -> Bool:
  match st:
    case Status.refused{}:
      True{}
    case _:
      False{}

# a status that is not done is not done with k
def Status.not_done(
  st: Status,
  -k: Bool,
  h: {Status.verdict(st) == None{}: Maybe<&2, Bool>}
) -> {st == Status.done{k}: Status} -> Empty:
  d => Shared.Maybe.none_ne_some(
    Bool,
    k,
    Equal.trans(
      Maybe<&2, Bool>,
      None{},
      Status.verdict(st),
      Some{k},
      Equal.sym(Maybe<&2, Bool>, Status.verdict(st), None{}, h),
      Equal.cong(Status, Maybe<&2, Bool>, x => Status.verdict(x), st, Status.done{k}, d)
    )
  )

# a status that is not refused is not refused
def Status.not_refused(st: Status, h: {Status.is_refused(st) == False{}: Bool}) -> {st == Status.refused{}: Status} -> Empty:
  d => Shared.Bool.false_ne_true(
    Equal.trans(
      Bool,
      False{},
      Status.is_refused(st),
      True{},
      Equal.sym(Bool, Status.is_refused(st), False{}, h),
      Equal.cong(Status, Bool, x => Status.is_refused(x), st, Status.refused{}, d)
    )
  )

# Status.kept once the view v of the request and the vote dm that decided it are known
def Status.kept.view(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -k: Bool,
  v: View,
  dm: Maybe<&2, Vote>,
  +edm: {State.decided(~Q, ~view, s, i) == dm: Maybe<&2, Vote>},
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Status.of.view(v, dm) == Status.done{k}: Status
} -> {Status.of.view(v, State.decided(~Q, ~view, State.join(~Q, ~same, s, t), i)) == Status.done{k}: Status}:
  match v dm:
    case View.root{ms} w:
      h => h
    case View.on{c, o, mk} Some{+x}:
      h =>
        %Equal.sym(
          Maybe<&2, Vote>,
          State.decided(~Q, ~view, State.join(~Q, ~same, s, t), i),
          Some{x},
          State.decided_kept(~Q, ~same, ~laws, ~view, s, t, i, x)(ag)(edm)
        ): {Status.of.view(View.on{c, o, mk}, _) == Status.done{k}: Status}
        h
    case View.on{c, o, mk} None{}:
      h => Empty.absurd(
        {Status.of.view(View.on{c, o, mk}, State.decided(~Q, ~view, State.join(~Q, ~same, s, t), i)) == Status.done{k}: Status},
        Status.not_done(Status.pending{}, k, {==})(h)
      )

# Status.kept once the cell m of the request is known
def Status.kept.at(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~view: Q -> View,
  +s: State(Q),
  +t: State(Q),
  +i: Id,
  -k: Bool,
  m: Maybe<&2, Cells.Cell<Entry<Q>>>,
  +em: {State.get(~Q, s, Slot.ask(i)) == m: Maybe<&2, Cells.Cell<Entry<Q>>>},
  +ag: {State.agrees(~Q, ~same, s, t) == True{}: Bool}
) -> {
  Status.of(~Q, ~view, s, i, m) == Status.done{k}: Status
} -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}:
  match m:
    case None{}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status},
        Status.not_done(Status.not_seen{}, k, {==})(h)
      )
    case Some{Cells.many{}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status},
        Status.not_done(Status.refused{}, k, {==})(h)
      )
    case Some{Cells.one{Entry.ask{j, t0, q}}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.join(~Q, ~same, s, t), Slot.ask(i)),
          Some{Cells.one{Entry.ask{j, t0, q}}},
          Cells.Cell.agrees_kept(
            ~Entry<Q>,
            ~Entry.is_eq(~Q, ~same),
            ~Entry.laws(~Q, ~same, ~laws),
            s,
            t,
            Slot.ask(i),
            Entry.ask{j, t0, q}
          )(ag)(em)
        ): {Status.of(~Q, ~view, State.join(~Q, ~same, s, t), i, _) == Status.done{k}: Status}
        Status.kept.view(~Q, ~same, ~laws, ~view, s, t, i, k, view(q), State.decided(~Q, ~view, s, i), {==}, ag)(h)
    case Some{Cells.one{Entry.vote{v}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status},
        Status.not_done(Status.not_seen{}, k, {==})(h)
      )
    case Some{Cells.one{Entry.at{w}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status},
        Status.not_done(Status.not_seen{}, k, {==})(h)
      )

# a request that is done stays done, with the same verdict, after a sync that
# agrees
law State.status_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~laws: Shared.Eq.Laws(Q, same)
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  for -k: Bool
  {State.agrees(~Q, ~same, s, t) == True{}: Bool}
    -> {State.status(~Q, ~view, s, i) == Status.done{k}: Status}
    -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.done{k}: Status}

def State.status_kept(ty, same, laws, view, s, t, i, k):
  ag => Status.kept.at(~ty, ~same, ~laws, ~view, s, t, i, k, State.get(~ty, s, Slot.ask(i)), {==}, ag)

# the status of a request of the view v is never refused
def Status.view_not_refused(v: View, dm: Maybe<&2, Vote>) -> {Status.is_refused(Status.of.view(v, dm)) == False{}: Bool}:
  match v dm:
    case View.root{ms} w:
      {==}
    case View.on{c, o, mk} Some{Vote{j, k, u}}:
      {==}
    case View.on{c, o, mk} None{}:
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
    Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), Some{Cells.many{}}, m2)
  )
    == Status.refused{}: Status
}:
  match m2:
    case None{}:
      {==}
    case Some{x}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
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
  Status.of(~Q, ~view, s, i, m) == Status.refused{}: Status
} -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}:
  match m:
    case Some{Cells.many{}}:
      h =>
        %Equal.sym(
          Maybe<&2, Cells.Cell<Entry<Q>>>,
          State.get(~Q, State.join(~Q, ~same, s, t), Slot.ask(i)),
          Tries.Trie.pick(
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
        ): {Status.of(~Q, ~view, State.join(~Q, ~same, s, t), i, _) == Status.refused{}: Status}
        %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, State.get(~Q, s, Slot.ask(i)), Some{Cells.many{}}, em):
          {
            Status.of(
              ~Q,
              ~view,
              State.join(~Q, ~same, s, t),
              i,
              Tries.Trie.pick(
                ~Cells.Cell<Entry<Q>>,
                ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)),
                _,
                State.get(~Q, t, Slot.ask(i))
              )
            )
              == Status.refused{}: Status
          }
        Refused.many(~Q, ~same, ~view, State.join(~Q, ~same, s, t), i, State.get(~Q, t, Slot.ask(i)))
    case None{}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status},
        Status.not_refused(Status.not_seen{}, {==})(h)
      )
    case Some{Cells.one{Entry.ask{j, t0, +q}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status},
        Status.not_refused(
          Status.of.view(view(q), State.decided(~Q, ~view, s, i)),
          Status.view_not_refused(view(q), State.decided(~Q, ~view, s, i))
        )(h)
      )
    case Some{Cells.one{Entry.vote{v}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status},
        Status.not_refused(Status.not_seen{}, {==})(h)
      )
    case Some{Cells.one{Entry.at{w}}}:
      h => Empty.absurd(
        {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status},
        Status.not_refused(Status.not_seen{}, {==})(h)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a refused request stays refused after any sync: a contradiction is final
law State.refused_kept:
  for ~Q: Data
  for ~same: Q -> Q -> Bool
  for ~view: Q -> View
  for +s: State(Q)
  for +t: State(Q)
  for +i: Id
  {State.status(~Q, ~view, s, i) == Status.refused{}: Status}
    -> {State.status(~Q, ~view, State.join(~Q, ~same, s, t), i) == Status.refused{}: Status}

def State.refused_kept(ty, same, view, s, t, i):
  Refused.kept.at(~ty, ~same, ~view, s, t, i, State.get(~ty, s, Slot.ask(i)), {==})

# Writes
# ------
# A node's own writes only add entries that agree with what it holds: each
# write grows the state (Grows), so every kept read stays through it.

# s2 is s joined with entries that agree with it
def Grows(~Q: Data, ~same: Q -> Q -> Bool, s: State(Q), s2: State(Q)) -> Type:
  &t: State(Q) -> {State.agrees(~Q, ~same, s, t) == True{}: Bool} & {s2 == State.join(~Q, ~same, s, t): State(Q)}

# a state grows to itself
def Grows.self(~Q: Data, ~same: Q -> Q -> Bool, +s: State(Q)) -> Grows(~Q, ~same, s, s):
  (
    Tries.tip{},
    (
      Cells.Cell.agrees_tip(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s),
      Equal.sym(
        State(Q),
        State.join(~Q, ~same, s, Tries.tip{}),
        s,
        Tries.Trie.union_tip(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s)
      )
    )
  )

# a put at an empty slot grows the state
def Grows.put(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  s: State(Q),
  +k: List<&2, Bool>,
  +e: Entry<Q>,
  h: {State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>}
) -> Grows(~Q, ~same, s, State.put(~Q, ~same, s, k, e)):
  (State.one(~Q, k, e), (Cells.Cell.agrees_one(~Entry<Q>, ~Entry.is_eq(~Q, ~same), s, k, Cells.one{e})(h), {==}))

# a put at an empty slot holds the entry there
def State.put_get(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  +s: State(Q),
  +k: List<&2, Bool>,
  +e: Entry<Q>
) -> {
  State.get(~Q, s, k) == None{}: Maybe<&2, Cells.Cell<Entry<Q>>>
} -> {State.get(~Q, State.put(~Q, ~same, s, k, e), k) == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>}:
  h =>
    +one1 = State.one(~Q, k, e)
    +get1 = State.get(~Q, s, k)
    %Equal.sym(
      Maybe<&2, Cells.Cell<Entry<Q>>>,
      State.get(~Q, State.put(~Q, ~same, s, k, e), k),
      Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), get1, State.get(~Q, one1, k)),
      Tries.Trie.get_union(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), s, one1, k)
    ): {_ == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>}
    %Equal.sym(Maybe<&2, Cells.Cell<Entry<Q>>>, get1, None{}, h):
      {
        Tries.Trie.pick(~Cells.Cell<Entry<Q>>, ~Cells.Cell.join(~Entry<Q>, ~Entry.is_eq(~Q, ~same)), _, State.get(~Q, one1, k))
          == Some{Cells.one{e}}: Maybe<&2, Cells.Cell<Entry<Q>>>
      }
    Tries.Trie.get_one(Cells.Cell<Entry<Q>>, k, Cells.one{e})

# a read f of a slot stays through growth
def Grows.read(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same),
  ~W: Data,
  f: Maybe<&2, Entry<Q>> -> Maybe<&2, W>,
  fnone: {f(None{}) == None{}: Maybe<&2, W>},
  +s: State(Q),
  -s2: State(Q),
  +k: List<&2, Bool>,
  -w: W,
  g: Grows(~Q, ~same, s, s2)
) -> {f(State.entry(~Q, s, k)) == Some{w}: Maybe<&2, W>} -> {f(State.entry(~Q, s2, k)) == Some{w}: Maybe<&2, W>}:
  match g:
    case (t, (ag, eq)):
      %Equal.sym(State(Q), s2, State.join(~Q, ~same, s, t), eq):
        {f(State.entry(~Q, s, k)) == Some{w}: Maybe<&2, W>} -> {f(State.entry(~Q, _, k)) == Some{w}: Maybe<&2, W>}
      State.read_kept(~Q, ~same, ~laws, ~W, f, fnone, s, t, k, w)(ag)
