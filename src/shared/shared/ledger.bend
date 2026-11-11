import Base
import ./shared/quorum.bend as Quorums
import ./shared/shared/cell.bend as Cells
import ./shared/shared/code.bend as Codes
import ./shared/shared/hash.bend as Hashes
import ./shared/shared/seal.bend as Seals
import ./shared/shared/shared.bend as Shared
import ./shared/text.bend as Texts

# Ledgers
# =======
# A ledger is what the replicas of a machine hold in common: requests,
# ballots, proofs of lies and data. Each entry is under the name that its own
# content gives it, so an entry cannot be put under another name, and two
# entries share a name only when they are the same entry. A ledger only gains
# entries: what it holds under a name, it holds for good.

# Names
# -----

# a request: its author, and the ID that the author gave it
type Id is Data:
  Id{author: String, request: String}

# a line: its root, and its name below the root (none: the root line itself).
# The root is the hash of the request that started the line, so two requests
# never start one line
type Line is Data:
  Line{root: Hashes.Hash, sub: Maybe<&2, String>}

# a place on a line: a height, and a round of the decision at that height
type Place is Data:
  Place{line: Line, height: U32, round: Nat}

# a step of a line: the requests that it decides, in order, each by the hash
# of its entry, and the hash of what the line holds before and after it
type Step is Data:
  Step{before: Maybe<&2, Hashes.Hash>, asks: List<&2, Hashes.Hash>, after: Maybe<&2, Hashes.Hash>}

# the last vote of a voter at a height: its round, and the step
type Last is Data:
  Last{round: Nat, step: Step}

# what a voter casts at a place. Vote: for a step; in a round after the first,
# with the voters whose passes allow that step. Pass: it leaves the rounds
# below this one (it casts no vote there any more), and names its last vote at
# the height, if any
type Cast is Data:
  Cast.Vote{step: Step, from: List<&2, String>}
  Cast.Pass{last: Maybe<&2, Last>}

# what a voter signs with a ballot: the place, its own name, and what it casts
type Signed is Data:
  Signed{at: Place, voter: String, cast: Cast}

# how a ballot is sealed. The ballots of a voter under one root are a chain:
# each names the place of the one before it (none: the first), and the key of
# the next one, so each key signs once
type Link is Data:
  Link{prev: Maybe<&2, Place>, next: Hashes.Hash, seal: Seals.Seal}

# a ballot of a voter: what it signs, and how it is sealed
type Ballot is Data:
  Ballot{signed: Signed, link: Link}

# the proof that a voter lied: a key, and two ballots that the key signs. A key
# signs one ballot only, so only the owner of the key can make one
type Lie is Data:
  Lie{key: Hashes.Hash, one: Ballot, two: Ballot}

# an entry: a request of a change, with its time; a ballot of a voter; data;
# or the proof that a voter lied
type Entry<-Q: Data> is Data:
  Entry.Ask{id: Id, time: String, ask: Q}
  Entry.Ballot{ballot: Ballot}
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

# the voters os, then r
def Voters.code(os: List<&2, String>, r: List<&2, U32>) -> List<&2, U32>:
  Codes.Code.list(~String, ~Codes.Code.text, os, r)

# voters
def Voters.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<List<&2, String>>>:
  Codes.Code.list.read(~String, ~Codes.Code.text.read, ts)

# the line c, then r
def Line.code(c: Line, r: List<&2, U32>) -> List<&2, U32>:
  match c:
    case Line{i, k}:
      Hashes.Hash.code(i, Codes.Code.maybe(~String, ~Codes.Code.text, k, r))

# a line
def Line.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Line>>:
  Codes.Code.two.read(
    ~Hashes.Hash,
    ~Maybe<&2, String>,
    ~Line,
    ~Hashes.Hash.code.read,
    ~(m => Codes.Code.maybe.read(~String, ~Codes.Code.text.read, m)),
    i => k => Line{i, k},
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

# a and b are the same request
def Id.is_eq(a: Id, b: Id) -> Bool:
  match a b:
    case Id{w1, r1} Id{w2, r2}:
      Bool.and(String.eq(w1, w2), String.eq(r1, r2))

# a and b are the same keys below a root
def Sub.is_eq(a: Maybe<&2, String>, b: Maybe<&2, String>) -> Bool:
  Shared.Maybe.is_eq(~String, ~String.eq, a, b)

# a and b are the same line
def Line.is_eq(a: Line, b: Line) -> Bool:
  match a b:
    case Line{i1, k1} Line{i2, k2}:
      List.all.if(u => Sub.is_eq(k1, k2), Hashes.Hash.is_eq(i1, i2))

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
def Step.code(v: Step, r: List<&2, U32>) -> List<&2, U32>:
  match v:
    case Step{b, qs, a}:
      Codes.Codec.enc(
        Maybe<&2, Hashes.Hash>,
        Root.codec()
      )(
        b
      )(
        Codes.Codec.enc(
          List<&2, Hashes.Hash>,
          Codes.Code.list.codec(~Hashes.Hash, ~Hashes.Hash.codec())
        )(qs)(Codes.Codec.enc(Maybe<&2, Hashes.Hash>, Root.codec())(a)(r))
      )

# a ballot
def Step.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Step>>:
  Codes.Code.three.read(
    ~Maybe<&2, Hashes.Hash>,
    ~List<&2, Hashes.Hash>,
    ~Maybe<&2, Hashes.Hash>,
    ~Step,
    ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Root.codec()),
    ~Codes.Codec.dec(List<&2, Hashes.Hash>, Codes.Code.list.codec(~Hashes.Hash, ~Hashes.Hash.codec())),
    ~Codes.Codec.dec(Maybe<&2, Hashes.Hash>, Root.codec()),
    b => qs => a => Step{b, qs, a},
    ts
  )

# a ballot reads back
def Step.code_read(
  v: Step,
  r: List<&2, U32>
) -> {Step.code.read(Step.code(v, r)) == Some{Codes.Read{v, r}}: Maybe<&2, Codes.Read<Step>>}:
  match v:
    case Step{b, qs, a}:
      Codes.Code.three_read(
        ~Maybe<&2, Hashes.Hash>,
        ~List<&2, Hashes.Hash>,
        ~Maybe<&2, Hashes.Hash>,
        ~Step,
        ~Root.codec(),
        ~Codes.Code.list.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        ~Root.codec(),
        x => y => z => Step{x, y, z},
        b,
        qs,
        a,
        r
      )

# the code of ballots
def Step.codec() -> Codes.Codec(Step):
  (Step.code, (Step.code.read, x => r => Step.code_read(x, r)))

# a and b are the same ballot: they have the same code
def Step.is_eq(a: Step, b: Step) -> Bool:
  Codes.Code.is_eq(~Step, ~Step.code, a, b)

# the laws of Step.is_eq
def Step.laws() -> Shared.Eq.Laws(Step, Step.is_eq):
  Codes.Code.eq_laws(~Step, ~Step.codec())

# Step.is_eq is True for a ballot and itself
def Step.is_eq_refl(a: Step) -> {Step.is_eq(a, a) == True{}: Bool}:
  Shared.Eq.refl(~Step, ~Step.is_eq, Step.laws(), a)

# Step.is_eq is True only for equal ballots
def Step.is_eq_sound(a: Step, b: Step) -> {Step.is_eq(a, b) == True{}: Bool} -> {a == b: Step}:
  Shared.Eq.sound(~Step, ~Step.is_eq, Step.laws(), a, b)

# a line reads back
def Line.code_read(
  c: Line,
  r: List<&2, U32>
) -> {Line.code.read(Line.code(c, r)) == Some{Codes.Read{c, r}}: Maybe<&2, Codes.Read<Line>>}:
  match c:
    case Line{i, k}:
      Codes.Code.two_read(
        ~Hashes.Hash,
        ~Maybe<&2, String>,
        ~Line,
        ~Hashes.Hash.codec(),
        ~Codes.Code.maybe.codec(~String, ~Codes.Code.text.codec()),
        a => b => Line{a, b},
        i,
        k,
        r
      )

# the code of lines
def Line.codec() -> Codes.Codec(Line):
  (Line.code, (Line.code.read, c => r => Line.code_read(c, r)))

# the place w, then r
def Place.code(w: Place, r: List<&2, U32>) -> List<&2, U32>:
  match w:
    case Place{c, h, k}:
      Line.code(c, Codes.Code.token(h, Codes.Code.count(k, r)))

# a place
def Place.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Place>>:
  Codes.Code.three.read(
    ~Line,
    ~U32,
    ~Nat,
    ~Place,
    ~Line.code.read,
    ~Codes.Code.token.read,
    ~Codes.Code.count.read,
    c => h => k => Place{c, h, k},
    ts
  )

# a place reads back
def Place.code_read(
  w: Place,
  r: List<&2, U32>
) -> {Place.code.read(Place.code(w, r)) == Some{Codes.Read{w, r}}: Maybe<&2, Codes.Read<Place>>}:
  match w:
    case Place{c, h, k}:
      Codes.Code.three_read(
        ~Line,
        ~U32,
        ~Nat,
        ~Place,
        ~Line.codec(),
        ~Codes.Code.token.codec(),
        ~(Codes.Code.count, (Codes.Code.count.read, x => y => Codes.Code.count_read(x, y))),
        a => b => d => Place{a, b, d},
        c,
        h,
        k,
        r
      )

# the code of places
def Place.codec() -> Codes.Codec(Place):
  (Place.code, (Place.code.read, w => r => Place.code_read(w, r)))

# the last vote l, then r
def Last.code(l: Last, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Last{k, v}:
      Codes.Code.count(k, Step.code(v, r))

# a last vote
def Last.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Last>>:
  Codes.Code.two.read(
    ~Nat,
    ~Step,
    ~Last,
    ~Codes.Code.count.read,
    ~Step.code.read,
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
        ~Step,
        ~Last,
        ~(Codes.Code.count, (Codes.Code.count.read, x => y => Codes.Code.count_read(x, y))),
        ~Step.codec(),
        a => b => Last{a, b},
        k,
        v,
        r
      )

# the code of last votes
def Last.codec() -> Codes.Codec(Last):
  (Last.code, (Last.code.read, l => r => Last.code_read(l, r)))

# what a voter casts, then r
def Cast.code(a: Cast, r: List<&2, U32>) -> List<&2, U32>:
  match a:
    case Cast.Vote{v, from}:
      0 <> Step.code(v, Voters.code(from, r))
    case Cast.Pass{l}:
      1 <> Codes.Code.maybe(~Last, ~Last.code, l, r)

# what a voter casts
def Cast.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Cast>>:
  match ts:
    case Nil{}:
      None{}
    case Con{+x, +r}:
      Shared.Bool.when(
        Maybe<&2, Codes.Read<Cast>>,
        U32.is_eq(x, 0),
        u => Codes.Code.two.read(
          ~Step,
          ~List<&2, String>,
          ~Cast,
          ~Step.code.read,
          ~Voters.code.read,
          v => from => Cast.Vote{v, from},
          r
        ),
        u => Shared.Bool.when(
          Maybe<&2, Codes.Read<Cast>>,
          U32.is_eq(x, 1),
          u => Codes.Code.one.read(
            ~Maybe<&2, Last>,
            ~Cast,
            ~(m => Codes.Code.maybe.read(~Last, ~Last.code.read, m)),
            l => Cast.Pass{l},
            r
          ),
          u => None{}
        )
      )

# what a voter casts reads back
def Cast.code_read(
  a: Cast,
  r: List<&2, U32>
) -> {Cast.code.read(Cast.code(a, r)) == Some{Codes.Read{a, r}}: Maybe<&2, Codes.Read<Cast>>}:
  match a:
    case Cast.Vote{v, from}:
      Codes.Code.two_read(
        ~Step,
        ~List<&2, String>,
        ~Cast,
        ~Step.codec(),
        ~Codes.Code.list.codec(~String, ~Codes.Code.text.codec()),
        x => y => Cast.Vote{x, y},
        v,
        from,
        r
      )
    case Cast.Pass{l}:
      Codes.Code.one_read(
        ~Maybe<&2, Last>,
        ~Cast,
        ~Codes.Code.maybe.codec(~Last, ~Last.codec()),
        x => Cast.Pass{x},
        l,
        r
      )

# the code of what a voter casts
def Cast.codec() -> Codes.Codec(Cast):
  (Cast.code, (Cast.code.read, a => r => Cast.code_read(a, r)))

# what a voter signs, then r
def Signed.code(x: Signed, r: List<&2, U32>) -> List<&2, U32>:
  match x:
    case Signed{w, n, a}:
      Place.code(w, Codes.Code.text(n, Cast.code(a, r)))

# what a voter signs
def Signed.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Signed>>:
  Codes.Code.three.read(
    ~Place,
    ~String,
    ~Cast,
    ~Signed,
    ~Place.code.read,
    ~Codes.Code.text.read,
    ~Cast.code.read,
    w => n => a => Signed{w, n, a},
    ts
  )

# what a voter signs reads back
def Signed.code_read(
  x: Signed,
  r: List<&2, U32>
) -> {Signed.code.read(Signed.code(x, r)) == Some{Codes.Read{x, r}}: Maybe<&2, Codes.Read<Signed>>}:
  match x:
    case Signed{w, n, a}:
      Codes.Code.three_read(
        ~Place,
        ~String,
        ~Cast,
        ~Signed,
        ~Place.codec(),
        ~Codes.Code.text.codec(),
        ~Cast.codec(),
        b => c => d => Signed{b, c, d},
        w,
        n,
        a,
        r
      )

# the code of what a voter signs
def Signed.codec() -> Codes.Codec(Signed):
  (Signed.code, (Signed.code.read, x => r => Signed.code_read(x, r)))

# the link l, then r
def Link.code(l: Link, r: List<&2, U32>) -> List<&2, U32>:
  match l:
    case Link{p, k, z}:
      Codes.Code.maybe(~Place, ~Place.code, p, Hashes.Hash.code(k, Seals.Seal.code(z, r)))

# a link
def Link.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Link>>:
  Codes.Code.three.read(
    ~Maybe<&2, Place>,
    ~Hashes.Hash,
    ~Seals.Seal,
    ~Link,
    ~(m => Codes.Code.maybe.read(~Place, ~Place.code.read, m)),
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
        ~Maybe<&2, Place>,
        ~Hashes.Hash,
        ~Seals.Seal,
        ~Link,
        ~Codes.Code.maybe.codec(~Place, ~Place.codec()),
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

# the step that the ballot b is for
def Ballot.step(b: Ballot) -> Maybe<&2, Step>:
  match b:
    case Ballot{Signed{w, n, Cast.Vote{v, from}}, l}:
      Some{v}
    case Ballot{Signed{w, n, Cast.Pass{p}}, l}:
      None{}

# the last vote that the ballot b names, when it is a pass
def Ballot.pass(b: Ballot) -> Maybe<&2, Maybe<&2, Last>>:
  match b:
    case Ballot{Signed{w, n, Cast.Pass{p}}, l}:
      Some{p}
    case Ballot{Signed{w, n, Cast.Vote{v, from}}, l}:
      None{}

# what the ballot b does
def Ballot.cast(b: Ballot) -> Cast:
  match b:
    case Ballot{Signed{w, n, a}, l}:
      a

# what a seal of a ballot signs: the hash of what the voter signs, the place of
# its ballot before, and the key of its next one
def Ballot.digest(x: Signed, p: Maybe<&2, Place>, k: Hashes.Hash) -> Hashes.Hash:
  Hashes.Sha.hash(Signed.code(x, Codes.Code.maybe(~Place, ~Place.code, p, Hashes.Hash.code(k, []))))

# the ballot of x that the secret seed seals, after the ballot at p, with k as
# the key of the next one
def Ballot.make(seed: Hashes.Hash, +x: Signed, +p: Maybe<&2, Place>, +k: Hashes.Hash) -> Ballot:
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
  p: Maybe<&2, Place>,
  k: Hashes.Hash
) -> {Ballot.sealed(Seals.Seal.public(seed), Ballot.make(seed, x, p, k)) == True{}: Bool}:
  Seals.Seal.check_sign(seed, Ballot.digest(x, p, k))

# a and b are the same entry, when same compares changes
def Entry.is_eq(~Q: Data, ~same: Q -> Q -> Bool, a: Entry<Q>, b: Entry<Q>) -> Bool:
  match a b:
    case Entry.Ask{i1, t1, q1} Entry.Ask{i2, t2, q2}:
      Bool.and(Id.is_eq(i1, i2), Bool.and(String.eq(t1, t2), same(q1, q2)))
    case Entry.Ballot{v1} Entry.Ballot{v2}:
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
    case Entry.Ballot{v}:
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
    case Entry.Ballot{v1} Entry.Ballot{v2}:
      h =>
        %Ballot.is_eq_sound(v1, v2)(h): {Entry.Ballot{v1} == Entry.Ballot{_}: Entry<Q>}
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
    case Entry.Ask{i, t, q} Entry.Ballot{v}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Ballot{v}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Ask{i, t, q} Entry.Data{d}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Data{d}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Ballot{v} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Ballot{v} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Ballot{v} Entry.Data{d}:
      h => Empty.absurd({Entry.Ballot{v} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Data{d} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Data{d} Entry.Ballot{v}:
      h => Empty.absurd({Entry.Data{d} == Entry.Ballot{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Ask{i, t, q} Entry.Lie{l}:
      h => Empty.absurd(
        {Entry.Ask{i, t, q} == Entry.Lie{l}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Ballot{v} Entry.Lie{l}:
      h => Empty.absurd({Entry.Ballot{v} == Entry.Lie{l}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Data{d} Entry.Lie{l}:
      h => Empty.absurd({Entry.Data{d} == Entry.Lie{l}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Lie{l} Entry.Ask{i, t, q}:
      h => Empty.absurd(
        {Entry.Lie{l} == Entry.Ask{i, t, q}: Entry<Q>},
        Shared.Bool.false_ne_true(h)
      )
    case Entry.Lie{l} Entry.Ballot{v}:
      h => Empty.absurd({Entry.Lie{l} == Entry.Ballot{v}: Entry<Q>}, Shared.Bool.false_ne_true(h))
    case Entry.Lie{l} Entry.Data{d}:
      h => Empty.absurd({Entry.Lie{l} == Entry.Data{d}: Entry<Q>}, Shared.Bool.false_ne_true(h))

# the laws of Entry.is_eq, by the laws of same
def Entry.laws(
  ~Q: Data,
  ~same: Q -> Q -> Bool,
  ~laws: Shared.Eq.Laws(Q, same)
) -> Shared.Eq.Laws(Entry<Q>, Entry.is_eq(~Q, ~same)):
  (a => Entry.is_eq_refl(~Q, ~same, ~laws, a), a => b => Entry.is_eq_sound(~Q, ~same, ~laws, a, b))

# Entries by name
# ---------------
# The name of an entry is its kind and the hash of its content. So entries of
# two kinds never share a name, and no entry can be put under the name of
# another: a ledger gives a name to an entry, a sender does not.

# the name of an entry: its kind, and the hash of its content
type Name is Data:
  Name.Ask{hash: Hashes.Hash}
  Name.Ballot{hash: Hashes.Hash}
  Name.Data{hash: Hashes.Hash}
  Name.Lie{hash: Hashes.Hash}

# the hash of the name n
def Name.hash(n: Name) -> Hashes.Hash:
  match n:
    case Name.Ask{h}:
      h
    case Name.Ballot{h}:
      h
    case Name.Data{h}:
      h
    case Name.Lie{h}:
      h

# a and b are the same name
def Name.is_eq(a: Name, b: Name) -> Bool:
  match a b:
    case Name.Ask{x} Name.Ask{y}:
      Hashes.Hash.is_eq(x, y)
    case Name.Ballot{x} Name.Ballot{y}:
      Hashes.Hash.is_eq(x, y)
    case Name.Data{x} Name.Data{y}:
      Hashes.Hash.is_eq(x, y)
    case Name.Lie{x} Name.Lie{y}:
      Hashes.Hash.is_eq(x, y)
    case _ _:
      False{}

# the name that the content of e gives it, when c is the code of changes. Data
# is under the hash of its words, so a tree or a rope finds its nodes
def Entry.name(~Q: Data, ~c: Codes.Codec(Q), e: Entry<Q>) -> Name:
  match e:
    case Entry.Ask{i, t, q}:
      Name.Ask{Hashes.Sha.hash(Id.code(i, Codes.Code.text(t, Codes.Codec.enc(Q, c)(q)([]))))}
    case Entry.Ballot{b}:
      Name.Ballot{Hashes.Sha.hash(Ballot.code(b, []))}
    case Entry.Data{ws}:
      Name.Data{Hashes.Sha.hash(ws)}
    case Entry.Lie{x}:
      Name.Lie{Hashes.Sha.hash(Lie.code(x, []))}

# a and b are the same entry, when c is the code of changes: two changes are
# the same when their codes are
def Entry.same(~Q: Data, ~c: Codes.Codec(Q), a: Entry<Q>, b: Entry<Q>) -> Bool:
  Entry.is_eq(~Q, ~Codes.Code.is_eq(~Q, ~Codes.Codec.enc(Q, c)), a, b)

# that a and b do not clash: when they have one name, they are one entry. Two
# entries clash only when two contents have one hash
def Entry.Agrees(~Q: Data, ~c: Codes.Codec(Q), a: Entry<Q>, b: Entry<Q>) -> Type:
  {Entry.name(~Q, ~c, a) == Entry.name(~Q, ~c, b): Name} -> {a == b: Entry<Q>}

# Ballots
# -------

# a and b are the same place
def Place.is_eq(a: Place, b: Place) -> Bool:
  match a b:
    case Place{c1, h1, r1} Place{c2, h2, r2}:
      List.all.if(u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2)), Line.is_eq(c1, c2))

# the place of the ballot b
def Ballot.at(b: Ballot) -> Place:
  match b:
    case Ballot{Signed{w, n, a}, l}:
      w

# the voter of the ballot b
def Ballot.voter(b: Ballot) -> String:
  match b:
    case Ballot{Signed{w, n, a}, l}:
      n

# the root of the line of the ballot b
def Ballot.root(b: Ballot) -> Hashes.Hash:
  match b:
    case Ballot{Signed{Place{Line{r, s}, h, k}, n, a}, l}:
      r

# b is a ballot of the voter at the place w
def Ballot.is_at(b: Ballot, w: Place, voter: String) -> Bool:
  match b:
    case Ballot{Signed{w2, n, a}, l}:
      List.all.if(u => String.eq(n, voter), Place.is_eq(w2, w))

# the vote of the ballot b, with the voters whose passes allow it, when it is
# a vote
def Ballot.vote(b: Ballot) -> Maybe<&2, Cast>:
  match b:
    case Ballot{Signed{w, n, Cast.Vote{v, from}}, l}:
      Some{Cast.Vote{v, from}}
    case Ballot{Signed{w, n, Cast.Pass{p}}, l}:
      None{}

# the first ballot of the lie x
def Lie.first(x: Lie) -> Ballot:
  match x:
    case Lie{k, a, b}:
      a

# a and b are the same cast: they have the same code
def Cast.is_eq(a: Cast, b: Cast) -> Bool:
  Codes.Code.is_eq(~Cast, ~Cast.code, a, b)

# a and b are the same last vote, or both none
def Last.is_eq(a: Maybe<&2, Last>, b: Maybe<&2, Last>) -> Bool:
  Shared.Maybe.is_eq(~Last, ~(x => y => Codes.Code.is_eq(~Last, ~Last.code, x, y)), a, b)

# what the ballots bs hold of the part that of reads: nothing, one value, or
# many when two ballots hold different ones
def Ballots.cell(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ballot -> Maybe<&2, B>,
  bs: List<&2, Ballot>
) -> Maybe<&2, Cells.Cell<B>>:
  match bs:
    case Nil{}:
      None{}
    case Con{b, rest}:
      Shared.Maybe.join(
        ~Cells.Cell<B>,
        ~Cells.Cell.join(~B, ~same),
        Maybe.bind(&2, B, Cells.Cell<B>, of(b), x => Some{Cells.One{x}}),
        Ballots.cell(~B, ~same, ~of, rest)
      )

# Ledgers
# -------
# A ledger is a way to keep entries (Ledger.Ops), with the proof that it obeys
# the laws of a ledger (Ledger.Laws). A def that needs a ledger takes one as
# a template, so it holds for every way to keep entries, and costs what that
# way costs. A ledger is what Ledger.get gives: the laws state each other
# operation by it.

# the operations of a ledger kept as L, for changes of Q: the ledger that
# holds nothing; the entry under a name; a ledger with one more entry; the
# entries of one ledger whose names another lacks; the ballots of a voter at a
# place; a round that no ballot at a height of a line is above; the voters
# that the ledger holds a proof of a lie against, under a root; a height that
# no ballot of a line is above; the requests of an author; and the ledger
# without the entry of a name
def Ledger.Ops(-Q: Data, -L: Data) -> Type:
  L
    & (
      (L -> Name -> Maybe<&2, Entry<Q>>)
        & (
          (L -> Entry<Q> -> L)
            & (
              (L -> L -> List<&2, Entry<Q>>)
                & (
                  (L -> Place -> String -> List<&2, Ballot>)
                    & (
                      (L -> Line -> U32 -> Nat)
                        & (
                          (L -> Hashes.Hash -> List<&2, String>)
                            & (
                              (L -> Line -> Nat)
                                & ((L -> String -> List<&2, Entry<Q>>) & (L -> Name -> L))
                            )
                        )
                    )
                )
            )
        )
    )

# a way to keep entries: what a ledger is kept as, and its operations
def Ledger.Kind(-Q: Data) -> Type:
  &L: Data -> Ledger.Ops(Q, L)

# what a ledger of the kind k is kept as
def Kind.L(-Q: Data, k: Ledger.Kind(Q)) -> Data:
  match k:
    case Tuple{l, ops}:
      l

# the ledger of the kind k that holds nothing
def Kind.empty(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k):
  match k:
    case Tuple{l, Tuple{e, ops}}:
      e

# the entry that a ledger of the kind k holds under a name
def Kind.get(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Name -> Maybe<&2, Entry<Q>>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, ops}}}:
      g

# a ledger of the kind k with one more entry
def Kind.add(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Entry<Q> -> Kind.L(Q, k):
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, ops}}}}:
      a

# the entries of a ledger of the kind k whose names another lacks
def Kind.missing(
  -Q: Data,
  k: Ledger.Kind(Q)
) -> Kind.L(Q, k) -> Kind.L(Q, k) -> List<&2, Entry<Q>>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, ops}}}}}:
      m

# the ballots of a voter at a place, in a ledger of the kind k
def Kind.ballots(
  -Q: Data,
  k: Ledger.Kind(Q)
) -> Kind.L(Q, k) -> Place -> String -> List<&2, Ballot>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, ops}}}}}}:
      b

# a round that no ballot at a height of a line is above, in a ledger of the
# kind k
def Kind.rounds(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Line -> U32 -> Nat:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, x}}}}}}}:
      r

# the liars under a root, in a ledger of the kind k
def Kind.liars(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Hashes.Hash -> List<&2, String>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, rest}}}}}}}}:
      x

# a height that no ballot of a line is above, in a ledger of the kind k
def Kind.heights(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Line -> Nat:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, dr}}}}}}}}}}:
      hs

# the requests of an author, in a ledger of the kind k; the cost is that of
# those requests
def Kind.asks(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> String -> List<&2, Entry<Q>>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, dr}}}}}}}}}}:
      as

# a ledger of the kind k without the entry of a name: a node that lets go of
# what it no longer uses
def Kind.drop(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Name -> Kind.L(Q, k):
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, dr}}}}}}}}}}:
      dr

# the ledger l of the kind k holds the entry e, when c is the code of changes
def Kind.has(~Q: Data, ~c: Codes.Codec(Q), ~k: Ledger.Kind(Q), l: Kind.L(Q, k), +e: Entry<Q>) -> Bool:
  Shared.Maybe.is_eq(
    ~Entry<Q>,
    ~Entry.same(~Q, ~c),
    Kind.get(Q, k)(l)(Entry.name(~Q, ~c, e)),
    Some{e}
  )

# that the ledger b of the kind k holds each entry that a holds, under the
# same name: a ledger that grows from a
def Kind.Grows(-Q: Data, -k: Ledger.Kind(Q), -a: Kind.L(Q, k), -b: Kind.L(Q, k)) -> Type:
  @n: Name -> @e: Entry<Q> -> {
    Kind.get(Q, k)(a)(n) == Some{e}: Maybe<&2, Entry<Q>>
  } -> {Kind.get(Q, k)(b)(n) == Some{e}: Maybe<&2, Entry<Q>>}

# the entries of the ledger a: those that a ledger that holds nothing lacks
def Kind.entries(~Q: Data, ~k: Ledger.Kind(Q), a: Kind.L(Q, k)) -> List<&2, Entry<Q>>:
  Kind.missing(Q, k)(a)(Kind.empty(Q, k))

# the ledger b holds each entry that a holds: a check, so a law can use it as
# often as it needs
def Kind.grows(~Q: Data, ~c: Codes.Codec(Q), ~k: Ledger.Kind(Q), a: Kind.L(Q, k), +b: Kind.L(Q, k)) -> Bool:
  Shared.List.holds(
    ~Entry<Q>,
    ~Kind.L(Q, k),
    ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
    Kind.entries(~Q, ~k, a),
    b
  )

# The laws of a ledger
# --------------------
# Each is a proposition about a kind k, when c is the code of changes.

# a ledger that holds nothing gives nothing
def Laws.GetEmpty(-Q: Data, -k: Ledger.Kind(Q)) -> Type:
  @n: Name -> {Kind.get(Q, k)(Kind.empty(Q, k))(n) == None{}: Maybe<&2, Entry<Q>>}

# a ledger with one more entry holds what it held, and the entry under its
# name when it held nothing there: it never loses or changes an entry
def Laws.GetAdd(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @e: Entry<Q> -> @n: Name -> {
    Kind.get(Q, k)(Kind.add(Q, k)(l)(e))(n)
      == Maybe.or(
        &2,
        Entry<Q>,
        Kind.get(Q, k)(l)(n),
        Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})
      ): Maybe<&2, Entry<Q>>
  }

# an entry is under the name that its own content gives it: no data is held
# under a hash that it does not match, and no entry under the name of another
def Laws.GetNamed(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @n: Name -> @e: Entry<Q> -> {
    Kind.get(Q, k)(l)(n) == Some{e}: Maybe<&2, Entry<Q>>
  } -> {Entry.name(~Q, ~c, e) == n: Name}

# two entries that do not clash give the same ledger in either order
def Laws.AddComm(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @a: Entry<Q> -> @b: Entry<Q> -> Entry.Agrees(~Q, ~c, a, b) -> {
    Kind.add(Q, k)(Kind.add(Q, k)(l)(a))(b) == Kind.add(Q, k)(Kind.add(Q, k)(l)(b))(a): Kind.L(Q, k)
  }

# an entry added twice is added once
def Laws.AddTwice(-Q: Data, -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @e: Entry<Q> -> {
    Kind.add(Q, k)(Kind.add(Q, k)(l)(e))(e) == Kind.add(Q, k)(l)(e): Kind.L(Q, k)
  }

# a sync sends each entry of s that r lacks, and no other
def Laws.Missing(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @s: Kind.L(Q, k) -> @r: Kind.L(Q, k) -> @e: Entry<Q> -> {
    List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.missing(Q, k)(s)(r), e)
      == Bool.and(
        Kind.has(~Q, ~c, ~k, s, e),
        Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(r)(Entry.name(~Q, ~c, e)))
      ): Bool
  }

# the ballots of a voter at a place are the ballots of the ledger that name
# them, and no other
def Laws.Ballots(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @w: Place -> @voter: String -> @b: Ballot -> {
    List.contains(~Ballot, ~Ballot.is_eq, Kind.ballots(Q, k)(l)(w)(voter), b)
      == Bool.and(Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}), Ballot.is_at(b, w, voter)): Bool
  }

# no ballot that a ledger holds is in a round above its bound, and the bound
# is the round of a ballot that it holds, or 0: a walk of the rounds of a
# height costs the rounds that have ballots
def Laws.Rounds(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  (
    @l: Kind.L(Q, k) -> @b: Ballot -> @line: Line -> @h: U32 -> @r: Nat -> @voter: String -> {
      Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}) == True{}: Bool
    } -> {
      Ballot.is_at(b, Place{line, h, r}, voter) == True{}: Bool
    } -> {Nat.is_le(r, Kind.rounds(Q, k)(l)(line)(h)) == True{}: Bool}
  )
    & (
      @l: Kind.L(Q, k) -> @line: Line -> @h: U32 -> {
        Nat.is_eq(Kind.rounds(Q, k)(l)(line)(h), 0n) == False{}: Bool
      } -> Exists(
        Ballot,
        b => {
          Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}) == True{}: Bool
        }
          & {
            Ballot.is_at(b, Place{line, h, Kind.rounds(Q, k)(l)(line)(h)}, Ballot.voter(b)) == True{}: Bool
          }
      )
    )

# no ballot that a ledger holds on a line is at a height above its bound, and
# the bound is the height of a ballot that it holds on the line, or 0
def Laws.Heights(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  (
    @l: Kind.L(Q, k) -> @b: Ballot -> @line: Line -> @h: U32 -> @r: Nat -> @voter: String -> {
      Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}) == True{}: Bool
    } -> {
      Ballot.is_at(b, Place{line, h, r}, voter) == True{}: Bool
    } -> {Nat.is_le(U32.to_nat(h), Kind.heights(Q, k)(l)(line)) == True{}: Bool}
  )
    & (
      @l: Kind.L(Q, k) -> @line: Line -> {
        Nat.is_eq(Kind.heights(Q, k)(l)(line), 0n) == False{}: Bool
      } -> Exists(
        Ballot,
        b => {
          Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}) == True{}: Bool
        }
          & Exists(
            U32,
            h => Exists(
              Nat,
              r => {
                Ballot.is_at(b, Place{line, h, r}, Ballot.voter(b)) == True{}: Bool
              }
                & {U32.to_nat(h) == Kind.heights(Q, k)(l)(line): Nat}
            )
          )
      )
    )

# e is a request of the author
def Entry.is_by(-Q: Data, e: Entry<Q>, author: String) -> Bool:
  match e:
    case Entry.Ask{Id{w, r}, t, q}:
      String.eq(w, author)
    case _:
      False{}

# the requests of an author are the requests of the ledger that name it, and
# no other entry
def Laws.Asks(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @author: String -> @e: Entry<Q> -> {
    List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.asks(Q, k)(l)(author), e)
      == Bool.and(Kind.has(~Q, ~c, ~k, l, e), Entry.is_by(Q, e, author)): Bool
  }

# a ledger without the entry of a name holds nothing there, and all else that
# it held
def Laws.Drop(-Q: Data, -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @n: Name -> @m: Name -> {
    Kind.get(Q, k)(Kind.drop(Q, k)(l)(n))(m)
      == Shared.Bool.when(
        Maybe<&2, Entry<Q>>,
        Name.is_eq(n, m),
        u => None{},
        u => Kind.get(Q, k)(l)(m)
      ): Maybe<&2, Entry<Q>>
  }

# a voter is a liar under a root only when the ledger holds a proof of a lie
# whose first ballot is of that voter under that root
def Laws.LiarsSound(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @r: Hashes.Hash -> @voter: String -> {
    List.contains(~String, ~String.eq, Kind.liars(Q, k)(l)(r), voter) == True{}: Bool
  } -> Exists(
    Lie,
    x => {
      Kind.has(~Q, ~c, ~k, l, Entry.Lie{x}) == True{}: Bool
    }
      & (
        {
          Hashes.Hash.is_eq(Ballot.root(Lie.first(x)), r) == True{}: Bool
        }
          & {String.eq(Ballot.voter(Lie.first(x)), voter) == True{}: Bool}
      )
  )

# and each proof of a lie that a ledger holds names its voter a liar
def Laws.LiarsComplete(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @x: Lie -> {
    Kind.has(~Q, ~c, ~k, l, Entry.Lie{x}) == True{}: Bool
  } -> {
    List.contains(
      ~String,
      ~String.eq,
      Kind.liars(Q, k)(l)(Ballot.root(Lie.first(x))),
      Ballot.voter(Lie.first(x))
    )
      == True{}: Bool
  }

# the laws of a ledger of the kind k, when c is the code of changes
def Ledger.Laws(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  Laws.GetEmpty(Q, k)
    & (
      Laws.GetAdd(Q, c, k)
        & (
          Laws.GetNamed(Q, c, k)
            & (
              Laws.AddComm(Q, c, k)
                & (
                  Laws.AddTwice(Q, k)
                    & (
                      Laws.Missing(Q, c, k)
                        & (
                          Laws.Ballots(Q, c, k)
                            & (
                              Laws.Rounds(Q, c, k)
                                & (
                                  Laws.Heights(Q, c, k)
                                    & (
                                      Laws.Asks(Q, c, k)
                                        & (
                                          Laws.Drop(Q, k)
                                            & (Laws.LiarsSound(Q, c, k) & Laws.LiarsComplete(Q, c, k))
                                        )
                                    )
                                )
                            )
                        )
                    )
                )
            )
        )
    )

# a ledger for changes of Q, whose code is c: a way to keep entries, and the
# proof that it obeys the laws
def Ledger(-Q: Data, -c: Codes.Codec(Q)) -> Type:
  &k: Ledger.Kind(Q) -> Ledger.Laws(Q, c, k)

# the kind of the ledger d
def Ledger.kind(-Q: Data, -c: Codes.Codec(Q), d: Ledger(Q, c)) -> Ledger.Kind(Q):
  match d:
    case Tuple{k, laws}:
      k

# the laws of the ledger d
def Ledger.laws(
  -Q: Data,
  -c: Codes.Codec(Q),
  d: Ledger(Q, c)
) -> Ledger.Laws(Q, c, Ledger.kind(Q, c, d)):
  match d:
    case Tuple{k, laws}:
      laws

# Reads
# -----
# What a ledger answers, by its operations alone. A voter casts one vote at a
# place, and one pass to it. A ledger that holds two different ones counts
# neither: what a place decides is a function of the entries, not of the order
# in which they came.

# l with each entry of es, in order
def Kind.adds(~Q: Data, ~k: Ledger.Kind(Q), es: List<&2, Entry<Q>>, l: Kind.L(Q, k)) -> Kind.L(Q, k):
  match es:
    case Nil{}:
      l
    case Con{e, rest}:
      Kind.adds(~Q, ~k, rest, Kind.add(Q, k)(l)(e))

# the words in the entry m, when it is data
def Entry.words(-Q: Data, m: Maybe<&2, Entry<Q>>) -> Maybe<&2, List<&2, U32>>:
  match m:
    case Some{Entry.Data{ws}}:
      Some{ws}
    case _:
      None{}

# the data of a ledger of the kind k whose hash is h. It hashes nothing: a
# ledger holds data under its hash only (Laws.GetNamed)
def Kind.data(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Hashes.Hash -> Maybe<&2, List<&2, U32>>:
  l => h => Entry.words(Q, Kind.get(Q, k)(l)(Name.Data{h}))

# the step that the voter cast at the place w, in the ledger l: one step, or
# many when it cast two
def Kind.cell(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  w: Place,
  voter: String
) -> Maybe<&2, Cells.Cell<Step>>:
  Ballots.cell(~Step, ~Step.is_eq, ~Ballot.step, Kind.ballots(Q, k)(l)(w)(voter))

# the step that the voter cast at the place w, when it cast one
def Kind.voted(~Q: Data, ~k: Ledger.Kind(Q), l: Kind.L(Q, k), w: Place, voter: String) -> Maybe<&2, Step>:
  Cells.Cell.value(Step, Kind.cell(~Q, ~k, l, w, voter))

# the vote of the voter at the place w, with the voters whose passes allow it,
# when it cast one
def Kind.cast(~Q: Data, ~k: Ledger.Kind(Q), l: Kind.L(Q, k), w: Place, voter: String) -> Maybe<&2, Cast>:
  Cells.Cell.value(
    Cast,
    Ballots.cell(~Cast, ~Cast.is_eq, ~Ballot.vote, Kind.ballots(Q, k)(l)(w)(voter))
  )

# the last vote that the voter named when it passed to the place w, when l
# holds one pass of it
def Kind.passed(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  w: Place,
  voter: String
) -> Maybe<&2, Maybe<&2, Last>>:
  Cells.Cell.value(
    Maybe<&2, Last>,
    Ballots.cell(~Maybe<&2, Last>, ~Last.is_eq, ~Ballot.pass, Kind.ballots(Q, k)(l)(w)(voter))
  )

# the cell of each of the voters at the place w
def Kind.cells(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  +l: Kind.L(Q, k),
  +w: Place,
  voters: List<&2, String>
) -> List<&2, Maybe<&2, Cells.Cell<Step>>>:
  match voters:
    case Nil{}:
      []
    case Con{v, rest}:
      Kind.cell(~Q, ~k, l, w, v) <> Kind.cells(~Q, ~k, l, w, rest)

# the step that a majority of the voters cast at the place w of l, if one did
def Kind.tally(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  w: Place,
  voters: List<&2, String>
) -> Maybe<&2, Step>:
  Quorums.Quorum.major(~Step, ~Step.is_eq, Kind.cells(~Q, ~k, l, w, voters))

# the law of a ledger that it gives nothing when it holds nothing
def Laws.get_empty(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledger.Kind(Q),
  laws: Ledger.Laws(Q, c, k)
) -> Laws.GetEmpty(Q, k):
  match laws:
    case Tuple{ge, rest}:
      ge

# the law of a ledger that it holds an entry under its name only
def Laws.get_named(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledger.Kind(Q),
  laws: Ledger.Laws(Q, c, k)
) -> Laws.GetNamed(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, Tuple{gn, rest}}}:
      gn

# the law of a ledger that a sync sends the entries that the other lacks
def Laws.missing(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledger.Kind(Q),
  laws: Ledger.Laws(Q, c, k)
) -> Laws.Missing(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, Tuple{gn, Tuple{ac, Tuple{at, Tuple{ms, rest}}}}}}:
      ms

# the law of a ledger that it gives the ballots of a voter at a place
def Laws.ballots(
  -Q: Data,
  -c: Codes.Codec(Q),
  -k: Ledger.Kind(Q),
  laws: Ledger.Laws(Q, c, k)
) -> Laws.Ballots(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, Tuple{gn, Tuple{ac, Tuple{at, Tuple{ms, Tuple{bl, rest}}}}}}}:
      bl

# Entry.same is True for an entry and itself
def Entry.same_refl(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  e: Entry<Q>
) -> {Entry.same(~Q, ~c, e, e) == True{}: Bool}:
  Entry.is_eq_refl(
    ~Q,
    ~Codes.Code.is_eq(~Q, ~Codes.Codec.enc(Q, c)),
    ~Codes.Code.eq_laws(~Q, ~c),
    e
  )

# Entry.same is True only for equal entries
def Entry.same_sound(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  a: Entry<Q>,
  b: Entry<Q>
) -> {Entry.same(~Q, ~c, a, b) == True{}: Bool} -> {a == b: Entry<Q>}:
  Entry.is_eq_sound(
    ~Q,
    ~Codes.Code.is_eq(~Q, ~Codes.Codec.enc(Q, c)),
    ~Codes.Code.eq_laws(~Q, ~c),
    a,
    b
  )

# a ledger that gives an entry under a name holds it
def Kind.has_of_get(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  gn: Laws.GetNamed(Q, c, k),
  l: Kind.L(Q, k),
  n: Name,
  +e: Entry<Q>,
  +g: {Kind.get(Q, k)(l)(n) == Some{e}: Maybe<&2, Entry<Q>>}
) -> {Kind.has(~Q, ~c, ~k, l, e) == True{}: Bool}:
  %Equal.sym(
    Name,
    Entry.name(~Q, ~c, e),
    n,
    gn(l)(n)(e)(g)
  ): {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.get(Q, k)(l)(_), Some{e}) == True{}: Bool}
  %Equal.sym(
    Maybe<&2, Entry<Q>>,
    Kind.get(Q, k)(l)(n),
    Some{e},
    g
  ): {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), _, Some{e}) == True{}: Bool}
  Entry.same_refl(~Q, ~c, e)

# a ledger that holds an entry gives it under its name
def Kind.get_of_has(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  n: Name,
  +e: Entry<Q>,
  ne: {Entry.name(~Q, ~c, e) == n: Name},
  h: {Kind.has(~Q, ~c, ~k, l, e) == True{}: Bool}
) -> {Kind.get(Q, k)(l)(n) == Some{e}: Maybe<&2, Entry<Q>>}:
  %ne: {Kind.get(Q, k)(l)(_) == Some{e}: Maybe<&2, Entry<Q>>}
  Shared.Maybe.is_eq_sound(
    ~Entry<Q>,
    ~Entry.same(~Q, ~c),
    x => y => Entry.same_sound(~Q, ~c, x, y),
    Kind.get(Q, k)(l)(Entry.name(~Q, ~c, e)),
    Some{e}
  )(h)

# the entries of a ledger include each entry that it holds
def Kind.entries_have(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ge: Laws.GetEmpty(Q, k),
  ms: Laws.Missing(Q, c, k),
  +l: Kind.L(Q, k),
  +e: Entry<Q>,
  h: {Kind.has(~Q, ~c, ~k, l, e) == True{}: Bool}
) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, l), e) == True{}: Bool}:
  Equal.trans(
    Bool,
    List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, l), e),
    Bool.and(
      Kind.has(~Q, ~c, ~k, l, e),
      Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)))
    ),
    True{},
    ms(l)(Kind.empty(Q, k))(e),
    Shared.Bool.and_both(
      Kind.has(~Q, ~c, ~k, l, e),
      Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)))
    )(h)(
      Equal.cong(
        Maybe<&2, Entry<Q>>,
        Bool,
        m => Maybe.is_none(&2, Entry<Q>, m),
        Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)),
        None{},
        ge(Entry.name(~Q, ~c, e))
      )
    )
  )

# Kind.holds_member at the first entry x, by whether it is m (s)
def Kind.holds_member.at(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  s: Bool,
  +x: Entry<Q>,
  r: List<&2, Entry<Q>>,
  +b: Kind.L(Q, k),
  +m: Entry<Q>,
  es: {Entry.same(~Q, ~c, x, m) == s: Bool},
  hx: {Kind.has(~Q, ~c, ~k, b, x) == True{}: Bool},
  hr: {
    Shared.List.holds(
      ~Entry<Q>,
      ~Kind.L(Q, k),
      ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
      r,
      b
    )
      == True{}: Bool
  },
  kr: {
    List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, m), s) == True{}: Bool
  },
  ih: {
    Shared.List.holds(
      ~Entry<Q>,
      ~Kind.L(Q, k),
      ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
      r,
      b
    )
      == True{}: Bool
  } -> {
    List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, m) == True{}: Bool
  } -> {Kind.has(~Q, ~c, ~k, b, m) == True{}: Bool}
) -> {Kind.has(~Q, ~c, ~k, b, m) == True{}: Bool}:
  match s:
    case True{}:
      %Entry.same_sound(~Q, ~c, x, m)(es): {Kind.has(~Q, ~c, ~k, b, _) == True{}: Bool}
      hx
    case False{}:
      ih(hr)(kr)

# a ledger holds each entry that the check lists: it holds each member of a list that it holds
def Kind.holds_member(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  xs: List<&2, Entry<Q>>,
  +b: Kind.L(Q, k),
  +m: Entry<Q>
) -> {
  Shared.List.holds(
    ~Entry<Q>,
    ~Kind.L(Q, k),
    ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
    xs,
    b
  )
    == True{}: Bool
} -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), xs, m) == True{}: Bool
} -> {Kind.has(~Q, ~c, ~k, b, m) == True{}: Bool}:
  match xs:
    case Nil{}:
      h => kc =>
        Empty.absurd({Kind.has(~Q, ~c, ~k, b, m) == True{}: Bool}, Shared.Bool.false_ne_true(kc))
    case Con{+x, +r}:
      +h => kc =>
        Kind.holds_member.at(
          ~Q,
          ~c,
          ~k,
          Entry.same(~Q, ~c, x, m),
          x,
          r,
          b,
          m,
          {==},
          Shared.List.all.if_hit(
            Kind.has(~Q, ~c, ~k, b, x),
            u => Shared.List.holds(
              ~Entry<Q>,
              ~Kind.L(Q, k),
              ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
              r,
              b
            )
          )(h),
          Shared.List.all.if_rest(
            Kind.has(~Q, ~c, ~k, b, x),
            u => Shared.List.holds(
              ~Entry<Q>,
              ~Kind.L(Q, k),
              ~(l => e => Kind.has(~Q, ~c, ~k, l, e)),
              r,
              b
            )
          )(h),
          kc,
          Kind.holds_member(~Q, ~c, ~k, r, b, m)
        )

# a ledger that the check says grows from a holds an entry that a holds under
# a name, under that name, by the laws of a
def Kind.grows_get.go(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  +a: Kind.L(Q, k),
  +b: Kind.L(Q, k),
  h: {Kind.grows(~Q, ~c, ~k, a, b) == True{}: Bool},
  +n: Name,
  +e: Entry<Q>,
  +g: {Kind.get(Q, k)(a)(n) == Some{e}: Maybe<&2, Entry<Q>>}
) -> {Kind.get(Q, k)(b)(n) == Some{e}: Maybe<&2, Entry<Q>>}:
  Kind.get_of_has(
    ~Q,
    ~c,
    ~k,
    b,
    n,
    e,
    Laws.get_named(Q, c, k, laws)(a)(n)(e)(g),
    Kind.holds_member(
      ~Q,
      ~c,
      ~k,
      Kind.entries(~Q, ~k, a),
      b,
      e
    )(h)(
      Kind.entries_have(
        ~Q,
        ~c,
        ~k,
        Laws.get_empty(Q, c, k, laws),
        Laws.missing(Q, c, k, laws),
        a,
        e,
        Kind.has_of_get(~Q, ~c, ~k, Laws.get_named(Q, c, k, laws), a, n, e, g)
      )
    )
  )

# a ledger that the check says grows from a holds each entry that a holds
law Kind.grows_get:
  for ~Q: Data
  for ~c: Codes.Codec(Q)
  for ~k: Ledger.Kind(Q)
  for ~laws: Ledger.Laws(Q, c, k)
  for a: Kind.L(Q, k)
  for b: Kind.L(Q, k)
  {Kind.grows(~Q, ~c, ~k, a, b) == True{}: Bool} -> Kind.Grows(Q, k, a, b)

def Kind.grows_get(q, c, k, laws, a, b):
  h => n => e => g => Kind.grows_get.go(~q, ~c, ~k, ~laws, a, b, h, n, e, g)
