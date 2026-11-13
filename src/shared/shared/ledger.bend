import Base
import ./shared/quorum.bend as Quorums
import ./shared/shared/code.bend as Codes
import ./shared/shared/crit.bend as Crits
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

# the place of the ballot before b in its chain (none: b is the first)
def Ballot.prev(b: Ballot) -> Maybe<&2, Place>:
  match b:
    case Ballot{x, Link{p, k, z}}:
      p

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

# the key that signs the ballot b: the one key that its seal shows for what
# it signs (none: its seal does not read)
def Ballot.signer(b: Ballot) -> Maybe<&2, Hashes.Hash>:
  match b:
    case Ballot{x, Link{p, k, z}}:
      Seals.Seal.signer(Ballot.digest(x, p, k), z)

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

# what the ballots bs agree on, of the part that of reads: nothing when no
# ballot holds it, or two ballots hold different ones
def Ballots.agreed(
  ~B: Data,
  ~same: B -> B -> Bool,
  ~of: Ballot -> Maybe<&2, B>,
  bs: List<&2, Ballot>
) -> Maybe<&2, B>:
  Shared.List.agreed(~B, ~same, Shared.List.filter_map(~Ballot, ~B, ~of, bs))

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
# no ballot of a line is above; the requests of an author; the ledger
# without the entry of a name; and the ballots that a key signs
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
                                & (
                                  (L -> String -> List<&2, Entry<Q>>)
                                    & ((L -> Name -> L) & (L -> Hashes.Hash -> List<&2, Ballot>))
                                )
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
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, Tuple{dr, af}}}}}}}}}}}:
      hs

# the requests of an author, in a ledger of the kind k; the cost is that of
# those requests
def Kind.asks(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> String -> List<&2, Entry<Q>>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, Tuple{dr, af}}}}}}}}}}}:
      as

# a ledger of the kind k without the entry of a name: a node that lets go of
# what it no longer uses
def Kind.drop(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Name -> Kind.L(Q, k):
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, Tuple{dr, af}}}}}}}}}}}:
      dr

# the ballots that a key signs, in a ledger of the kind k
def Kind.signed(-Q: Data, k: Ledger.Kind(Q)) -> Kind.L(Q, k) -> Hashes.Hash -> List<&2, Ballot>:
  match k:
    case Tuple{l, Tuple{e, Tuple{g, Tuple{a, Tuple{m, Tuple{b, Tuple{r, Tuple{x, Tuple{hs, Tuple{as, Tuple{dr, af}}}}}}}}}}}:
      af

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

# the ballots that a key signs are the ballots of the ledger that it seals,
# and no other: a key signs one ballot, so two of them are a lie, found in one
# read
def Laws.Signed(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @key: Hashes.Hash -> @b: Ballot -> {
    List.contains(~Ballot, ~Ballot.is_eq, Kind.signed(Q, k)(l)(key), b)
      == Bool.and(Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}), Ballot.sealed(key, b)): Bool
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
                                            & (Laws.LiarsSound(Q, c, k) & (Laws.LiarsComplete(Q, c, k) & Laws.Signed(Q, c, k)))
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

# the step that the voter cast at the place w, when it cast one
def Kind.voted(~Q: Data, ~k: Ledger.Kind(Q), l: Kind.L(Q, k), w: Place, voter: String) -> Maybe<&2, Step>:
  Ballots.agreed(~Step, ~Step.is_eq, ~Ballot.step, Kind.ballots(Q, k)(l)(w)(voter))

# the vote of the voter at the place w, with the voters whose passes allow it,
# when it cast one
def Kind.cast(~Q: Data, ~k: Ledger.Kind(Q), l: Kind.L(Q, k), w: Place, voter: String) -> Maybe<&2, Cast>:
  Ballots.agreed(~Cast, ~Cast.is_eq, ~Ballot.vote, Kind.ballots(Q, k)(l)(w)(voter))

# the last vote that the voter named when it passed to the place w, when l
# holds one pass of it
def Kind.passed(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  w: Place,
  voter: String
) -> Maybe<&2, Maybe<&2, Last>>:
  Ballots.agreed(~Maybe<&2, Last>, ~Last.is_eq, ~Ballot.pass, Kind.ballots(Q, k)(l)(w)(voter))

# the step that each of the voters cast at the place w, when it cast one
def Kind.votes(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  +l: Kind.L(Q, k),
  +w: Place,
  voters: List<&2, String>
) -> List<&2, Maybe<&2, Step>>:
  match voters:
    case Nil{}:
      []
    case Con{v, rest}:
      Kind.voted(~Q, ~k, l, w, v) <> Kind.votes(~Q, ~k, l, w, rest)

# the step that a majority of the voters cast at the place w of l, if one did
def Kind.tally(
  ~Q: Data,
  ~k: Ledger.Kind(Q),
  l: Kind.L(Q, k),
  w: Place,
  voters: List<&2, String>
) -> Maybe<&2, Step>:
  Quorums.Quorum.major(~Step, ~Step.is_eq, Kind.votes(~Q, ~k, l, w, voters))

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

# Growth as a check
# -----------------
# Kind.grows from what each entry gives (Kind.grows_core), and the checks it
# keeps: from itself, through a ledger between, and by one more entry.

# the law of a ledger with one more entry, of the laws
def Laws.get_add(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q), laws: Ledger.Laws(Q, c, k)) -> Laws.GetAdd(Q, c, k):
  match laws:
    case Tuple{ge, Tuple{ga, rest}}:
      ga

# the entries ps, each in ks, are each in ks with one more entry
def Kind.within_cons(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ps: List<&2, Entry<Q>>,
  +x: Entry<Q>,
  +ks: List<&2, Entry<Q>>
) -> {Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), ps, ks) == True{}: Bool}
  -> {Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), ps, x <> ks) == True{}: Bool}:
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +r}:
      +h => Shared.Bool.and_both(
        List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), x <> ks, p),
        Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, x <> ks)
      )(
        Shared.List.contains_cons(
          ~Entry<Q>,
          ~Entry.same(~Q, ~c),
          x,
          ks,
          p
        )(
          Shared.Bool.and_true_left(
            List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), ks, p),
            Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, ks)
          )(h)
        )
      )(
        Kind.within_cons(
          ~Q,
          ~c,
          r,
          x,
          ks
        )(
          Shared.Bool.and_true_right(
            List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), ks, p),
            Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, ks)
          )(h)
        )
      )

# an entry is in a list that it starts
def Kind.contains_head(~Q: Data, ~c: Codes.Codec(Q), +x: Entry<Q>, r: List<&2, Entry<Q>>) -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), x <> r, x) == True{}: Bool
}:
  %Equal.sym(
    Bool,
    Entry.same(~Q, ~c, x, x),
    True{},
    Entry.is_eq_refl(~Q, ~Codes.Code.is_eq(~Q, ~Codes.Codec.enc(Q, c)), ~Codes.Code.eq_laws(~Q, ~c), x)
  ): {List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, x), _) == True{}: Bool}
  {==}

# each entry of a list is in it
def Kind.within_refl(~Q: Data, ~c: Codes.Codec(Q), ks: List<&2, Entry<Q>>) -> {
  Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), ks, ks) == True{}: Bool
}:
  match ks:
    case Nil{}:
      {==}
    case Con{+x, +r}:
      Shared.Bool.and_both(
        List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), x <> r, x),
        Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, x <> r)
      )(Kind.contains_head(~Q, ~c, x, r))(Kind.within_cons(~Q, ~c, r, x, r)(Kind.within_refl(~Q, ~c, r)))

# a ledger holds each of its entries
def Kind.has_of_entries(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ms: Laws.Missing(Q, c, k),
  +l: Kind.L(Q, k),
  +e: Entry<Q>
) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, l), e) == True{}: Bool}
  -> {Kind.has(~Q, ~c, ~k, l, e) == True{}: Bool}:
  h => Shared.Bool.and_true_left(
    Kind.has(~Q, ~c, ~k, l, e),
    Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)))
  )(
    Equal.trans(
      Bool,
      Bool.and(
        Kind.has(~Q, ~c, ~k, l, e),
        Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)))
      ),
      List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, l), e),
      True{},
      Equal.sym(
        Bool,
        List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, l), e),
        Bool.and(
          Kind.has(~Q, ~c, ~k, l, e),
          Maybe.is_none(&2, Entry<Q>, Kind.get(Q, k)(Kind.empty(Q, k))(Entry.name(~Q, ~c, e)))
        ),
        ms(l)(Kind.empty(Q, k))(e)
      ),
      h
    )
  )

# Kind.grows_core over the entries xs of A(x)
def Kind.grows_core.go(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  ~X: Data,
  ~A: X -> Kind.L(Q, k),
  ~B: X -> Kind.L(Q, k),
  ~f: @x: X -> @e: Entry<Q> -> {Kind.has(~Q, ~c, ~k, A(x), e) == True{}: Bool}
    -> {Kind.has(~Q, ~c, ~k, B(x), e) == True{}: Bool},
  +x: X,
  xs: List<&2, Entry<Q>>
) -> {Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), xs, Kind.entries(~Q, ~k, A(x))) == True{}: Bool}
  -> {
    Shared.List.holds(~Entry<Q>, ~Kind.L(Q, k), ~(l => e => Kind.has(~Q, ~c, ~k, l, e)), xs, B(x)) == True{}: Bool
  }:
  match xs:
    case Nil{}:
      h => {==}
    case Con{+y, +r}:
      +h => Shared.List.all.if_both(
        Kind.has(~Q, ~c, ~k, B(x), y),
        u => Shared.List.holds(~Entry<Q>, ~Kind.L(Q, k), ~(l => e => Kind.has(~Q, ~c, ~k, l, e)), r, B(x))
      )(
        f(
          x
        )(
          y
        )(
          Kind.has_of_entries(
            ~Q,
            ~c,
            ~k,
            Laws.missing(Q, c, k, laws),
            A(x),
            y
          )(
            Shared.Bool.and_true_left(
              List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, A(x)), y),
              Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, Kind.entries(~Q, ~k, A(x)))
            )(h)
          )
        )
      )(
        Kind.grows_core.go(
          ~Q,
          ~c,
          ~k,
          ~laws,
          ~X,
          ~A,
          ~B,
          ~f,
          x,
          r
        )(
          Shared.Bool.and_true_right(
            List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Kind.entries(~Q, ~k, A(x)), y),
            Shared.List.within(~Entry<Q>, ~Entry.same(~Q, ~c), r, Kind.entries(~Q, ~k, A(x)))
          )(h)
        )
      )

# the check that B(x) grows from A(x), when B(x) holds each entry that A(x)
# holds (f)
def Kind.grows_core(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  ~X: Data,
  ~A: X -> Kind.L(Q, k),
  ~B: X -> Kind.L(Q, k),
  ~f: @x: X -> @e: Entry<Q> -> {Kind.has(~Q, ~c, ~k, A(x), e) == True{}: Bool}
    -> {Kind.has(~Q, ~c, ~k, B(x), e) == True{}: Bool},
  +x: X
) -> {Kind.grows(~Q, ~c, ~k, A(x), B(x)) == True{}: Bool}:
  Kind.grows_core.go(
    ~Q,
    ~c,
    ~k,
    ~laws,
    ~X,
    ~A,
    ~B,
    ~f,
    x,
    Kind.entries(~Q, ~k, A(x))
  )(Kind.within_refl(~Q, ~c, Kind.entries(~Q, ~k, A(x))))

# a ledger grows from itself
def Kind.grows_refl(~Q: Data, ~c: Codes.Codec(Q), ~k: Ledger.Kind(Q), ~laws: Ledger.Laws(Q, c, k), +a: Kind.L(Q, k)) -> {
  Kind.grows(~Q, ~c, ~k, a, a) == True{}: Bool
}:
  Kind.grows_core(~Q, ~c, ~k, ~laws, ~Kind.L(Q, k), ~(l => l), ~(l => l), ~(l => e => h => h), a)

# a ledger that grows from a holds each entry that a holds
def Kind.grows_has(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  +a: Kind.L(Q, k),
  +b: Kind.L(Q, k),
  +g: {Kind.grows(~Q, ~c, ~k, a, b) == True{}: Bool},
  +e: Entry<Q>
) -> {Kind.has(~Q, ~c, ~k, a, e) == True{}: Bool} -> {Kind.has(~Q, ~c, ~k, b, e) == True{}: Bool}:
  h => Kind.holds_member(
    ~Q,
    ~c,
    ~k,
    Kind.entries(~Q, ~k, a),
    b,
    e
  )(g)(Kind.entries_have(~Q, ~c, ~k, Laws.get_empty(Q, c, k, laws), Laws.missing(Q, c, k, laws), a, e, h))

# three ledgers, each grown from the one before
def Kind.Chain(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Data:
  +Sigma<Kind.L(Q, k), a => +Sigma<Kind.L(Q, k), b => +Sigma<Kind.L(Q, k), c2 => +Sigma<
    {Kind.grows(~Q, ~c, ~k, a, b) == True{}: Bool},
    g1 => {Kind.grows(~Q, ~c, ~k, b, c2) == True{}: Bool}>>>>

# the first ledger of a chain
def Kind.Chain.first(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q), x: Kind.Chain(Q, c, k)) -> Kind.L(Q, k):
  match x:
    case Tuple{a, rest}:
      a

# the last ledger of a chain
def Kind.Chain.last(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q), x: Kind.Chain(Q, c, k)) -> Kind.L(Q, k):
  match x:
    case Tuple{a, Tuple{b, Tuple{c2, r}}}:
      c2

# the last ledger of a chain holds each entry that the first holds
def Kind.Chain.has(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  x: Kind.Chain(Q, c, k),
  +e: Entry<Q>
) -> {Kind.has(~Q, ~c, ~k, Kind.Chain.first(Q, c, k, x), e) == True{}: Bool}
  -> {Kind.has(~Q, ~c, ~k, Kind.Chain.last(Q, c, k, x), e) == True{}: Bool}:
  match x:
    case Tuple{+a, Tuple{+b, Tuple{+c2, Tuple{+g1, +g2}}}}:
      h => Kind.grows_has(~Q, ~c, ~k, ~laws, b, c2, g2, e)(Kind.grows_has(~Q, ~c, ~k, ~laws, a, b, g1, e)(h))

# growth is transitive
def Kind.grows_trans(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  +a: Kind.L(Q, k),
  +b: Kind.L(Q, k),
  +c2: Kind.L(Q, k),
  +g1: {Kind.grows(~Q, ~c, ~k, a, b) == True{}: Bool},
  +g2: {Kind.grows(~Q, ~c, ~k, b, c2) == True{}: Bool}
) -> {Kind.grows(~Q, ~c, ~k, a, c2) == True{}: Bool}:
  Kind.grows_core(
    ~Q,
    ~c,
    ~k,
    ~laws,
    ~Kind.Chain(Q, c, k),
    ~(x => Kind.Chain.first(Q, c, k, x)),
    ~(x => Kind.Chain.last(Q, c, k, x)),
    ~(x => e => h => Kind.Chain.has(~Q, ~c, ~k, ~laws, x, e)(h)),
    Tuple{a, Tuple{b, Tuple{c2, Tuple{g1, g2}}}}
  )

# what a ledger holds, it holds with one more entry, once the entry under the
# name is known (m)
def Kind.add_has.at(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  +e: Entry<Q>,
  m: Maybe<&2, Entry<Q>>,
  -w: Maybe<&2, Entry<Q>>
) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), m, Some{e}) == True{}: Bool}
  -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Maybe.or(&2, Entry<Q>, m, w), Some{e}) == True{}: Bool}:
  match m:
    case None{}:
      h => Empty.absurd(
        {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Maybe.or(&2, Entry<Q>, None{}, w), Some{e}) == True{}: Bool},
        Shared.Bool.false_ne_true(h)
      )
    case Some{y}:
      h => h

# the ledger p.l with the entry p.x
def Kind.Plus(-Q: Data, -k: Ledger.Kind(Q)) -> Data:
  +Sigma<Kind.L(Q, k), l => Entry<Q>>

# the ledger of p
def Kind.Plus.base(-Q: Data, -k: Ledger.Kind(Q), p: Kind.Plus(Q, k)) -> Kind.L(Q, k):
  match p:
    case Tuple{l, x}:
      l

# the ledger of p with its entry
def Kind.Plus.added(-Q: Data, k: Ledger.Kind(Q), p: Kind.Plus(Q, k)) -> Kind.L(Q, k):
  match p:
    case Tuple{l, x}:
      Kind.add(Q, k)(l)(x)

# what a ledger holds, it holds with one more entry
def Kind.add_has(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  p: Kind.Plus(Q, k),
  +e: Entry<Q>
) -> {Kind.has(~Q, ~c, ~k, Kind.Plus.base(Q, k, p), e) == True{}: Bool}
  -> {Kind.has(~Q, ~c, ~k, Kind.Plus.added(Q, k, p), e) == True{}: Bool}:
  match p:
    case Tuple{+l, +x}:
      h =>
        %Equal.sym(
          Maybe<&2, Entry<Q>>,
          Kind.get(Q, k)(Kind.add(Q, k)(l)(x))(Entry.name(~Q, ~c, e)),
          Maybe.or(
            &2,
            Entry<Q>,
            Kind.get(Q, k)(l)(Entry.name(~Q, ~c, e)),
            Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, e)), u => Some{x})
          ),
          Laws.get_add(Q, c, k, laws)(l)(x)(Entry.name(~Q, ~c, e))
        ): {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), _, Some{e}) == True{}: Bool}
        Kind.add_has.at(
          ~Q,
          ~c,
          e,
          Kind.get(Q, k)(l)(Entry.name(~Q, ~c, e)),
          Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, e)), u => Some{x})
        )(h)

# a ledger grows by one more entry
def Kind.grows_add(
  ~Q: Data,
  ~c: Codes.Codec(Q),
  ~k: Ledger.Kind(Q),
  ~laws: Ledger.Laws(Q, c, k),
  +l: Kind.L(Q, k),
  +x: Entry<Q>
) -> {Kind.grows(~Q, ~c, ~k, l, Kind.add(Q, k)(l)(x)) == True{}: Bool}:
  Kind.grows_core(
    ~Q,
    ~c,
    ~k,
    ~laws,
    ~Kind.Plus(Q, k),
    ~(p => Kind.Plus.base(Q, k, p)),
    ~(p => Kind.Plus.added(Q, k, p)),
    ~(p => e => h => Kind.add_has(~Q, ~c, ~k, ~laws, p, e)(h)),
    Tuple{l, x}
  )

# Books
# =====
# A way to keep entries (a Ledger.Kind): a dict of the entries by name, and,
# for each question that a ledger answers often, a dict from a key that
# starts with what the question names to the name of an entry. A number in a
# key is a Crits.Key.ord, so the greatest round or height under a prefix is
# the last key there (Crits.Crit.last). Each index holds exactly the keys of
# the entries (Book.ok), so a drop takes an entry out of each, and a sync
# sends the difference of two dicts of entries.

# the code of the name n, then r
def Name.code(n: Name, r: List<&2, U32>) -> List<&2, U32>:
  match n:
    case Name.Ask{h}:
      0 <> Hashes.Hash.code(h, r)
    case Name.Ballot{h}:
      1 <> Hashes.Hash.code(h, r)
    case Name.Data{h}:
      2 <> Hashes.Hash.code(h, r)
    case Name.Lie{h}:
      3 <> Hashes.Hash.code(h, r)

# the key of the name n among the entries of a book
def Name.key(n: Name) -> List<&2, U32>:
  Name.code(n, [])

# a book: the entries by name, and the names of the entries by their keys
# for the ballots of a voter at a place, the rounds of ballots at a height,
# the heights of ballots on a line, the proofs of lies under a root, the
# requests of an author, and the ballots that a key signs
type Book<-Q: Data> is Data:
  Book{
    entries: Crits.Dict(Entry<Q>),
    ballots: Crits.Dict(Name),
    rounds: Crits.Dict(Name),
    heights: Crits.Dict(Name),
    liars: Crits.Dict(Name),
    asks: Crits.Dict(Name),
    signed: Crits.Dict(Name)
  }

# the keys of an entry in each index of a book (none: it is not in that one)
type Keys is Data:
  Keys{
    ballot: Maybe<&2, List<&2, U32>>,
    round: Maybe<&2, List<&2, U32>>,
    height: Maybe<&2, List<&2, U32>>,
    liar: Maybe<&2, List<&2, U32>>,
    ask: Maybe<&2, List<&2, U32>>,
    signer: Maybe<&2, List<&2, U32>>
  }

# the root of the line c
def Line.root(c: Line) -> Hashes.Hash:
  match c:
    case Line{r, s}:
      r

# the keys of the ballot b, of the name n
def Ballot.keys(b: Ballot, +n: Name) -> Keys:
  match b:
    case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+p, +k, +z}}:
      Keys{
        Some{Place.code(Place{line, h, r}, Codes.Code.text(voter, Name.key(n)))},
        Some{Line.code(line, h <> Crits.Key.ord(r, Name.key(n)))},
        Some{Line.code(line, Crits.Key.ord(U32.to_nat(h), Name.key(n)))},
        None{},
        None{},
        Maybe.map(
          &2,
          Hashes.Hash,
          List<&2, U32>,
          key => Hashes.Hash.code(key, Name.key(n)),
          Ballot.signer(Ballot{Signed{Place{line, h, r}, voter, a}, Link{p, k, z}})
        )
      }

# the keys of the entry e, of the name n
def Entry.keys(-Q: Data, e: Entry<Q>, +n: Name) -> Keys:
  match e:
    case Entry.Ballot{b}:
      Ballot.keys(b, n)
    case Entry.Lie{+x}:
      Keys{
        None{},
        None{},
        None{},
        Some{Hashes.Hash.code(Ballot.root(Lie.first(x)), Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n)))},
        None{},
        None{}
      }
    case Entry.Ask{Id{w, q}, t, a}:
      Keys{None{}, None{}, None{}, None{}, Some{Codes.Code.text(w, Name.key(n))}, None{}}
    case Entry.Data{ws}:
      Keys{None{}, None{}, None{}, None{}, None{}, None{}}

# the key of an index, of the keys ks: 0 ballots, 1 rounds, 2 heights, 3
# liars, 4 asks, 5 signed
def Keys.at(ks: Keys, i: Nat) -> Maybe<&2, List<&2, U32>>:
  match ks i:
    case Keys{b, r, h, l, a, f} 0n:
      b
    case Keys{b, r, h, l, a, f} 1n:
      r
    case Keys{b, r, h, l, a, f} 2n:
      h
    case Keys{b, r, h, l, a, f} 3n:
      l
    case Keys{b, r, h, l, a, f} 4n:
      a
    case Keys{b, r, h, l, a, f} x:
      f

# the index i of the book b (Keys.at)
def Book.index(-Q: Data, b: Book<Q>, i: Nat) -> Crits.Dict(Name):
  match b i:
    case Book{es, bs, rs, hs, ls, as, fs} 0n:
      bs
    case Book{es, bs, rs, hs, ls, as, fs} 1n:
      rs
    case Book{es, bs, rs, hs, ls, as, fs} 2n:
      hs
    case Book{es, bs, rs, hs, ls, as, fs} 3n:
      ls
    case Book{es, bs, rs, hs, ls, as, fs} 4n:
      as
    case Book{es, bs, rs, hs, ls, as, fs} x:
      fs

# the entries of the book b
def Book.entries(-Q: Data, b: Book<Q>) -> Crits.Dict(Entry<Q>):
  match b:
    case Book{es, bs, rs, hs, ls, as, fs}:
      es

# a book with no entry
def Book.new(~Q: Data) -> Book<Q>:
  Book{
    Crits.Dict.new(~Entry<Q>),
    Crits.Dict.new(~Name),
    Crits.Dict.new(~Name),
    Crits.Dict.new(~Name),
    Crits.Dict.new(~Name),
    Crits.Dict.new(~Name),
    Crits.Dict.new(~Name)
  }

# the index d with the key m, if any, for the name n
def Index.put(d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>, +n: Name) -> Crits.Dict(Name):
  match m:
    case None{}:
      d
    case Some{k}:
      Crits.Dict.set(~Name, d, k, n)

# the index d without the key m, if any
def Index.drop(d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>) -> Crits.Dict(Name):
  match m:
    case None{}:
      d
    case Some{k}:
      Crits.Dict.drop(~Name, d, k)

# the book b with the entry e under the name n, and its keys ks in each index
def Book.put(~Q: Data, b: Book<Q>, e: Entry<Q>, +n: Name, +ks: Keys) -> Book<Q>:
  match b:
    case Book{es, bs, rs, hs, ls, as, fs}:
      Book{
        Crits.Dict.set(~Entry<Q>, es, Name.key(n), e),
        Index.put(bs, Keys.at(ks, 0n), n),
        Index.put(rs, Keys.at(ks, 1n), n),
        Index.put(hs, Keys.at(ks, 2n), n),
        Index.put(ls, Keys.at(ks, 3n), n),
        Index.put(as, Keys.at(ks, 4n), n),
        Index.put(fs, Keys.at(ks, 5n), n)
      }

# the book b without the entry of the name n and its keys ks in each index
def Book.take(~Q: Data, b: Book<Q>, +n: Name, +ks: Keys) -> Book<Q>:
  match b:
    case Book{es, bs, rs, hs, ls, as, fs}:
      Book{
        Crits.Dict.drop(~Entry<Q>, es, Name.key(n)),
        Index.drop(bs, Keys.at(ks, 0n)),
        Index.drop(rs, Keys.at(ks, 1n)),
        Index.drop(hs, Keys.at(ks, 2n)),
        Index.drop(ls, Keys.at(ks, 3n)),
        Index.drop(as, Keys.at(ks, 4n)),
        Index.drop(fs, Keys.at(ks, 5n))
      }

# the entry that the book b holds under the name n
def Book.get(-Q: Data, b: Book<Q>, n: Name) -> Maybe<&2, Entry<Q>>:
  Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(n))

# the book b with the entry e, when it holds nothing under its name; else b,
# which keeps what it holds, when c is the code of changes
def Book.add(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>) -> Book<Q>:
  +n = Entry.name(~Q, ~c, e)
  Shared.Bool.when(
    Book<Q>,
    Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, n)),
    u => b,
    u => Book.put(~Q, b, e, n, Entry.keys(Q, e, n))
  )

# Book.drop once the entry m of the name n is known
def Book.drop.at(~Q: Data, b: Book<Q>, +n: Name, m: Maybe<&2, Entry<Q>>) -> Book<Q>:
  match m:
    case None{}:
      b
    case Some{e}:
      Book.take(~Q, b, n, Entry.keys(Q, e, n))

# the book b without the entry of the name n, in each of its dicts
def Book.drop(~Q: Data, +b: Book<Q>, +n: Name) -> Book<Q>:
  Book.drop.at(~Q, b, n, Book.get(Q, b, n))

# the entries of s whose names r lacks
def Book.missing(~Q: Data, s: Book<Q>, r: Book<Q>) -> List<&2, Entry<Q>>:
  Crits.Dict.values(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, s), Book.entries(Q, r)))

# the names in the index d under the keys that start with the words p
def Index.under(d: Crits.Dict(Name), +p: List<&2, U32>) -> List<&2, Name>:
  Crits.Binds.values(Name, Crits.Crit.entries(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)))

# the entries of the book b of the names ns
def Book.named(-Q: Data, +b: Book<Q>, ns: List<&2, Name>) -> List<&2, Entry<Q>>:
  match ns:
    case Nil{}:
      []
    case Con{n, rest}:
      Shared.Maybe.cons(Entry<Q>, Book.get(Q, b, n), Book.named(Q, b, rest))

# the ballots among the entries es
def Entries.ballots(-Q: Data, es: List<&2, Entry<Q>>) -> List<&2, Ballot>:
  match es:
    case Nil{}:
      []
    case Con{Entry.Ballot{x}, rest}:
      x <> Entries.ballots(Q, rest)
    case Con{e, rest}:
      Entries.ballots(Q, rest)

# the voters of the first ballots of the lies among the entries es
def Entries.liars(-Q: Data, es: List<&2, Entry<Q>>) -> List<&2, String>:
  match es:
    case Nil{}:
      []
    case Con{Entry.Lie{x}, rest}:
      Ballot.voter(Lie.first(x)) <> Entries.liars(Q, rest)
    case Con{e, rest}:
      Entries.liars(Q, rest)

# the ballots of the voter at the place w
def Book.ballots(-Q: Data, +b: Book<Q>, +w: Place, +voter: String) -> List<&2, Ballot>:
  Entries.ballots(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, [])))))

# the number at the front of the words of the last key m, after its first n
# words (0: none)
def Index.number(m: Maybe<&2, Crits.Bind<Name>>, +n: Nat) -> Nat:
  match m:
    case None{}:
      0n
    case Some{Crits.Bind{k, x}}:
      Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, k, n)), 0n)

# the greatest number in the keys of the index d under the prefix p, which
# a Key.ord follows (0: none)
def Index.last(d: Crits.Dict(Name), +p: List<&2, U32>) -> Nat:
  Index.number(
    Crits.Crit.last(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)),
    List.length(&2, U32, p)
  )

# a round that no ballot at the height h of the line is above
def Book.rounds(-Q: Data, b: Book<Q>, +line: Line, +h: U32) -> Nat:
  Index.last(Book.index(Q, b, 1n), Line.code(line, [h]))

# a height that no ballot of the line is above
def Book.heights(-Q: Data, b: Book<Q>, +line: Line) -> Nat:
  Index.last(Book.index(Q, b, 2n), Line.code(line, []))

# the voters that the book b holds a proof of a lie against, under the root r
def Book.liars(-Q: Data, +b: Book<Q>, +r: Hashes.Hash) -> List<&2, String>:
  Entries.liars(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 3n), Hashes.Hash.code(r, []))))

# the ballots that the key signs
def Book.signed(-Q: Data, +b: Book<Q>, key: Hashes.Hash) -> List<&2, Ballot>:
  Entries.ballots(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))))

# the requests of the author
def Book.asks(-Q: Data, +b: Book<Q>, +author: String) -> List<&2, Entry<Q>>:
  Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, [])))

# The one shape of a book

# the index d holds the name n under the key m, if any
def Index.holds(d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>, +n: Name) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{k}:
      Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k), Some{n})

# each index of the book b holds the name n under the keys ks
def Book.indexed(-Q: Data, +b: Book<Q>, +ks: Keys, +n: Name) -> Bool:
  Bool.and(
    Bool.and(Index.holds(Book.index(Q, b, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b, 1n), Keys.at(ks, 1n), n)),
    Bool.and(
      Bool.and(Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)),
      Bool.and(Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n), Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n))
    )
  )

# each of the entries es of the book b is under the key of its name, and
# each index holds its keys
def Book.ok.entries(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, es: List<&2, Crits.Bind<Entry<Q>>>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{Crits.Bind{k, +e}, rest}:
      +n = Entry.name(~Q, ~c, e)
      Bool.and(
        Bool.and(Crits.Key.is_eq(Name.key(n), k), Book.indexed(Q, b, Entry.keys(Q, e, n), n)),
        Book.ok.entries(~Q, ~c, b, rest)
      )

# the key k of the index i of the book b is a key of the entry of the name n
def Book.ok.key(-Q: Data, m: Maybe<&2, Entry<Q>>, +i: Nat, +k: List<&2, U32>, +n: Name) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{e}:
      Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, Keys.at(Entry.keys(Q, e, n), i), Some{k})

# each key ks of the index i of the book b is a key of the entry it names
def Book.ok.index(-Q: Data, +b: Book<Q>, +i: Nat, ks: List<&2, Crits.Bind<Name>>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{Crits.Bind{+k, +n}, rest}:
      Bool.and(Book.ok.key(Q, Book.get(Q, b, n), i, k, n), Book.ok.index(Q, b, i, rest))

# the index i of the book b holds only keys of its entries
def Book.ok.at(-Q: Data, +b: Book<Q>, +i: Nat) -> Bool:
  Book.ok.index(Q, b, i, Crits.Dict.entries(Name, Book.index(Q, b, i)))

# the book b is in its one shape, when c is the code of changes: each entry is
# under the key of its name, each index holds the keys of each entry, and no
# other key
def Book.ok(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>) -> Bool:
  Bool.and(
    Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))),
    Bool.and(
      Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)),
      Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))
    )
  )

# Laws of books

# a new book is in its one shape
law Book.ok_new:
  for ~Q: Data
  for ~c: Codes.Codec(Q)
  {Book.ok(~Q, ~c, Book.new(~Q)) == True{}: Bool}

def Book.ok_new(Q, c):
  {==}

# The keys of books

# what follows from b True and from b False follows
def Book.by(-T: Type, b: Bool) -> ({b == True{}: Bool} -> T) -> ({b == False{}: Bool} -> T) -> T:
  match b:
    case True{}:
      t => f => t({==})
    case False{}:
      t => f => f({==})

# a pick on a True test is its first
def Book.pick_true(-A: Type, c: Bool, -a: A, -b: A) -> {c == True{}: Bool} -> {Bool.pick(A, c, a, b) == a: A}:
  match c:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({b == a: A}, Shared.Bool.false_ne_true(h))

# a pick on a False test is its second
def Book.pick_false(-A: Type, c: Bool, -a: A, -b: A) -> {c == False{}: Bool} -> {Bool.pick(A, c, a, b) == b: A}:
  match c:
    case True{}:
      h => Empty.absurd({a == b: A}, Shared.Bool.true_ne_false(h))
    case False{}:
      h => {==}

# Name.is_eq is True for a name and itself
def Name.is_eq_refl(n: Name) -> {Name.is_eq(n, n) == True{}: Bool}:
  match n:
    case Name.Ask{h}:
      Hashes.Hash.is_eq_refl(h)
    case Name.Ballot{h}:
      Hashes.Hash.is_eq_refl(h)
    case Name.Data{h}:
      Hashes.Hash.is_eq_refl(h)
    case Name.Lie{h}:
      Hashes.Hash.is_eq_refl(h)

# words whose first words differ differ
def Book.head_ne(+x: U32, +y: U32, -xs: List<&2, U32>, -ys: List<&2, U32>) -> {U32.is_eq(x, y) == False{}: Bool} -> {
  x <> xs == y <> ys: List<&2, U32>
} -> Empty:
  hf => e =>
    Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        U32.is_eq(x, y),
        False{},
        Equal.trans(
          Bool,
          True{},
          U32.is_eq(x, x),
          U32.is_eq(x, y),
          Equal.sym(Bool, U32.is_eq(x, x), True{}, Shared.U32.is_eq_refl(x)),
          Equal.cong(List<&2, U32>, Bool, l => U32.is_eq(x, Shared.List.head_or(U32, l, x)), x <> xs, y <> ys, e)
        ),
        hf
      )
    )

# names with the same key are the same
def Name.key_inj(a: Name, b: Name) -> {Name.key(a) == Name.key(b): List<&2, U32>} -> {a == b: Name}:
  match a b:
    case Name.Ask{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}} Name.Ask{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}:
      e =>
        Equal.cong(
          List<&2, U32>,
          Name,
          l => Name.Ask{Codes.Code.read_value(Hashes.Hash, Hashes.Hash.code.read(List.drop(&2, U32, l, 1n)), Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7})},
          Name.key(Name.Ask{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}}),
          Name.key(Name.Ask{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}),
          e
        )
    case Name.Ask{+x} Name.Ballot{+y}:
      e => Empty.absurd({Name.Ask{x} == Name.Ballot{y}: Name}, Book.head_ne(0, 1, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Ask{+x} Name.Data{+y}:
      e => Empty.absurd({Name.Ask{x} == Name.Data{y}: Name}, Book.head_ne(0, 2, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Ask{+x} Name.Lie{+y}:
      e => Empty.absurd({Name.Ask{x} == Name.Lie{y}: Name}, Book.head_ne(0, 3, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Ballot{+x} Name.Ask{+y}:
      e => Empty.absurd({Name.Ballot{x} == Name.Ask{y}: Name}, Book.head_ne(1, 0, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Ballot{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}} Name.Ballot{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}:
      e =>
        Equal.cong(
          List<&2, U32>,
          Name,
          l => Name.Ballot{Codes.Code.read_value(Hashes.Hash, Hashes.Hash.code.read(List.drop(&2, U32, l, 1n)), Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7})},
          Name.key(Name.Ballot{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}}),
          Name.key(Name.Ballot{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}),
          e
        )
    case Name.Ballot{+x} Name.Data{+y}:
      e => Empty.absurd({Name.Ballot{x} == Name.Data{y}: Name}, Book.head_ne(1, 2, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Ballot{+x} Name.Lie{+y}:
      e => Empty.absurd({Name.Ballot{x} == Name.Lie{y}: Name}, Book.head_ne(1, 3, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Data{+x} Name.Ask{+y}:
      e => Empty.absurd({Name.Data{x} == Name.Ask{y}: Name}, Book.head_ne(2, 0, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Data{+x} Name.Ballot{+y}:
      e => Empty.absurd({Name.Data{x} == Name.Ballot{y}: Name}, Book.head_ne(2, 1, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Data{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}} Name.Data{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}:
      e =>
        Equal.cong(
          List<&2, U32>,
          Name,
          l => Name.Data{Codes.Code.read_value(Hashes.Hash, Hashes.Hash.code.read(List.drop(&2, U32, l, 1n)), Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7})},
          Name.key(Name.Data{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}}),
          Name.key(Name.Data{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}),
          e
        )
    case Name.Data{+x} Name.Lie{+y}:
      e => Empty.absurd({Name.Data{x} == Name.Lie{y}: Name}, Book.head_ne(2, 3, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Lie{+x} Name.Ask{+y}:
      e => Empty.absurd({Name.Lie{x} == Name.Ask{y}: Name}, Book.head_ne(3, 0, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Lie{+x} Name.Ballot{+y}:
      e => Empty.absurd({Name.Lie{x} == Name.Ballot{y}: Name}, Book.head_ne(3, 1, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Lie{+x} Name.Data{+y}:
      e => Empty.absurd({Name.Lie{x} == Name.Data{y}: Name}, Book.head_ne(3, 2, Hashes.Hash.code(x, []), Hashes.Hash.code(y, []))({==})(e))
    case Name.Lie{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}} Name.Lie{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}:
      e =>
        Equal.cong(
          List<&2, U32>,
          Name,
          l => Name.Lie{Codes.Code.read_value(Hashes.Hash, Hashes.Hash.code.read(List.drop(&2, U32, l, 1n)), Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7})},
          Name.key(Name.Lie{Hashes.Hash{x0, x1, x2, x3, x4, x5, x6, x7}}),
          Name.key(Name.Lie{Hashes.Hash{y0, y1, y2, y3, y4, y5, y6, y7}}),
          e
        )

# the key of a name has nine words
def Name.key_len(n: Name) -> {List.length(&2, U32, Name.key(n)) == 9n: Nat}:
  match n:
    case Name.Ask{h}:
      match h:
        case Hashes.Hash{h0, h1, h2, h3, h4, h5, h6, h7}:
          {==}
    case Name.Ballot{h}:
      match h:
        case Hashes.Hash{h0, h1, h2, h3, h4, h5, h6, h7}:
          {==}
    case Name.Data{h}:
      match h:
        case Hashes.Hash{h0, h1, h2, h3, h4, h5, h6, h7}:
          {==}
    case Name.Lie{h}:
      match h:
        case Hashes.Hash{h0, h1, h2, h3, h4, h5, h6, h7}:
          {==}

# the words ws, each with its bits in the other order, then r, are those words
# then r
def Book.rev_append(+ws: List<&2, U32>, +r: List<&2, U32>) -> {
  Crits.Words.rev(ws, r) == List.append(&2, U32, Crits.Words.rev(ws, []), r): List<&2, U32>
}:
  match ws:
    case Nil{}:
      {==}
    case Con{w, rest}:
      %Equal.sym(
        List<&2, U32>,
        Crits.Words.rev(rest, r),
        List.append(&2, U32, Crits.Words.rev(rest, []), r),
        Book.rev_append(rest, r)
      ): {Crits.U32.rev(w) <> _ == Crits.U32.rev(w) <> List.append(&2, U32, Crits.Words.rev(rest, []), r): List<&2, U32>}
      {==}

# the length of x then r
def Book.length_append(+x: List<&2, U32>, +r: List<&2, U32>) -> {
  List.length(&2, U32, List.append(&2, U32, x, r)) == Nat.add(List.length(&2, U32, r), List.length(&2, U32, x)): Nat
}:
  match x:
    case Nil{}:
      Equal.sym(Nat, Nat.add(List.length(&2, U32, r), 0n), List.length(&2, U32, r), Shared.Nat.add_zero(List.length(&2, U32, r)))
    case Con{h, t}:
      %Equal.sym(
        Nat,
        Nat.add(List.length(&2, U32, r), 1n+List.length(&2, U32, t)),
        1n+Nat.add(List.length(&2, U32, r), List.length(&2, U32, t)),
        Shared.Nat.add_succ(List.length(&2, U32, r), List.length(&2, U32, t))
      ): {
        1n+List.length(&2, U32, List.append(&2, U32, t, r)) == _: Nat
      }
      %Equal.sym(
        Nat,
        List.length(&2, U32, List.append(&2, U32, t, r)),
        Nat.add(List.length(&2, U32, r), List.length(&2, U32, t)),
        Book.length_append(t, r)
      ): {1n+_ == 1n+Nat.add(List.length(&2, U32, r), List.length(&2, U32, t)): Nat}
      {==}

# x then r, without as many words as x has, is r
def Book.drop_append(+x: List<&2, U32>, +r: List<&2, U32>) -> {
  List.drop(&2, U32, List.append(&2, U32, x, r), List.length(&2, U32, x)) == r: List<&2, U32>
}:
  match x:
    case Nil{}:
      Shared.List.drop_zero(&2, U32, r)
    case Con{h, t}:
      Book.drop_append(t, r)

# the last nine words of x then r, when r has nine words, are r
def Book.last_nine(+x: List<&2, U32>, +r: List<&2, U32>) -> {List.length(&2, U32, r) == 9n: Nat} -> {
  List.drop(
    &2,
    U32,
    List.append(&2, U32, x, r),
    Nat.sub(List.length(&2, U32, List.append(&2, U32, x, r)), 9n)
  )
    == r: List<&2, U32>
}:
  hl =>
    %Equal.sym(
      Nat,
      List.length(&2, U32, List.append(&2, U32, x, r)),
      Nat.add(List.length(&2, U32, r), List.length(&2, U32, x)),
      Book.length_append(x, r)
    ): {List.drop(&2, U32, List.append(&2, U32, x, r), Nat.sub(_, 9n)) == r: List<&2, U32>}
    %Equal.sym(Nat, List.length(&2, U32, r), 9n, hl): {
      List.drop(&2, U32, List.append(&2, U32, x, r), Nat.sub(Nat.add(_, List.length(&2, U32, x)), 9n)) == r: List<&2, U32>
    }
    %Equal.sym(Nat, Nat.sub(List.length(&2, U32, x), 0n), List.length(&2, U32, x), Shared.Nat.sub_zero(List.length(&2, U32, x))): {
      List.drop(&2, U32, List.append(&2, U32, x, r), _) == r: List<&2, U32>
    }
    Book.drop_append(x, r)

# the key k of the ballots index of an entry of the name n ends in the key of n
def Book.key_tail.ballots(-Q: Data, e: Entry<Q>, +n: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 0n) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {
  Codes.Code.read_value(
    List<&2, U32>,
    Codes.Read.then(
      String,
      List<&2, U32>,
      Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)),
      a => r => Some{Codes.Read{r, []}}
    ),
    []
  )
    == Name.key(n): List<&2, U32>
}:
  match e:
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+pv, lk, z}}:
          hk =>
            %Shared.Maybe.some_inj(List<&2, U32>, Place.code(Place{line, h, r}, Codes.Code.text(voter, Name.key(n))), k, hk): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(_), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
            %Equal.sym(
              Maybe<&2, Codes.Read<Place>>,
              Place.code.read(Place.code(Place{line, h, r}, Codes.Code.text(voter, Name.key(n)))),
              Some{Codes.Read{Place{line, h, r}, Codes.Code.text(voter, Name.key(n))}},
              Place.code_read(Place{line, h, r}, Codes.Code.text(voter, Name.key(n)))
            ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, _, p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
            %Equal.sym(
              Maybe<&2, Codes.Read<String>>,
              Codes.Code.text.read(Codes.Code.text(voter, Name.key(n))),
              Some{Codes.Read{voter, Name.key(n)}},
              Codes.Code.text_read(voter, Name.key(n))
            ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
            {==}
    case Entry.Ask{Id{w, q}, t, a}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# the key k of the rounds index of an entry of the name n ends in the key of n
def Book.key_tail.rounds(-Q: Data, e: Entry<Q>, +n: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 1n) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {
  List.drop(
    &2,
    U32,
    Codes.Code.read_value(
      List<&2, U32>,
      Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}),
      []
    ),
    Nat.sub(
      List.length(
        &2,
        U32,
        Codes.Code.read_value(
          List<&2, U32>,
          Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}),
          []
        )
      ),
      9n
    )
  )
    == Name.key(n): List<&2, U32>
}:
  match e:
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+pv, lk, z}}:
          hk =>
            %Shared.Maybe.some_inj(List<&2, U32>, Line.code(line, h <> Crits.Key.ord(r, Name.key(n))), k, hk): {List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(_), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(_), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}
            %Equal.sym(
              Maybe<&2, Codes.Read<Line>>,
              Line.code.read(Line.code(line, h <> Crits.Key.ord(r, Name.key(n)))),
              Some{Codes.Read{line, h <> Crits.Key.ord(r, Name.key(n))}},
              Line.code_read(line, h <> Crits.Key.ord(r, Name.key(n)))
            ): {List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}
            %Equal.sym(List<&2, U32>, Crits.Words.rev(Codes.Code.count(r, []), Name.key(n)), List.append(&2, U32, Crits.Words.rev(Codes.Code.count(r, []), []), Name.key(n)), Book.rev_append(Codes.Code.count(r, []), Name.key(n))): {List.drop(&2, U32, h <> _, Nat.sub(List.length(&2, U32, h <> _), 9n)) == Name.key(n): List<&2, U32>}
            Book.last_nine(h <> Crits.Words.rev(Codes.Code.count(r, []), []), Name.key(n))(Name.key_len(n))
    case Entry.Ask{Id{w, q}, t, a}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# the key k of the heights index of an entry of the name n ends in the key of n
def Book.key_tail.heights(-Q: Data, e: Entry<Q>, +n: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 2n) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {
  List.drop(
    &2,
    U32,
    Codes.Code.read_value(
      List<&2, U32>,
      Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}),
      []
    ),
    Nat.sub(
      List.length(
        &2,
        U32,
        Codes.Code.read_value(
          List<&2, U32>,
          Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}),
          []
        )
      ),
      9n
    )
  )
    == Name.key(n): List<&2, U32>
}:
  match e:
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+pv, lk, z}}:
          hk =>
            %Shared.Maybe.some_inj(List<&2, U32>, Line.code(line, Crits.Key.ord(U32.to_nat(h), Name.key(n))), k, hk): {List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(_), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(_), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}
            %Equal.sym(
              Maybe<&2, Codes.Read<Line>>,
              Line.code.read(Line.code(line, Crits.Key.ord(U32.to_nat(h), Name.key(n)))),
              Some{Codes.Read{line, Crits.Key.ord(U32.to_nat(h), Name.key(n))}},
              Line.code_read(line, Crits.Key.ord(U32.to_nat(h), Name.key(n)))
            ): {List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}
            %Equal.sym(List<&2, U32>, Crits.Words.rev(Codes.Code.count(U32.to_nat(h), []), Name.key(n)), List.append(&2, U32, Crits.Words.rev(Codes.Code.count(U32.to_nat(h), []), []), Name.key(n)), Book.rev_append(Codes.Code.count(U32.to_nat(h), []), Name.key(n))): {List.drop(&2, U32, _, Nat.sub(List.length(&2, U32, _), 9n)) == Name.key(n): List<&2, U32>}
            Book.last_nine(Crits.Words.rev(Codes.Code.count(U32.to_nat(h), []), []), Name.key(n))(Name.key_len(n))
    case Entry.Ask{Id{w, q}, t, a}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# the key k of the liars index of an entry of the name n ends in the key of n
def Book.key_tail.liars(-Q: Data, e: Entry<Q>, +n: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 3n) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {
  Codes.Code.read_value(
    List<&2, U32>,
    Codes.Read.then(
      String,
      List<&2, U32>,
      Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)),
      a => r => Some{Codes.Read{r, []}}
    ),
    []
  )
    == Name.key(n): List<&2, U32>
}:
  match e:
    case Entry.Lie{+x}:
      h =>
        %Shared.Maybe.some_inj(List<&2, U32>, Hashes.Hash.code(Ballot.root(Lie.first(x)), Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n))), k, h): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(_), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        %Equal.sym(
          Maybe<&2, Codes.Read<Hashes.Hash>>,
          Hashes.Hash.code.read(Hashes.Hash.code(Ballot.root(Lie.first(x)), Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n)))),
          Some{Codes.Read{Ballot.root(Lie.first(x)), Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n))}},
          Hashes.Hash.code_read(Ballot.root(Lie.first(x)), Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n)))
        ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, _, p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        %Equal.sym(
          Maybe<&2, Codes.Read<String>>,
          Codes.Code.text.read(Codes.Code.text(Ballot.voter(Lie.first(x)), Name.key(n))),
          Some{Codes.Read{Ballot.voter(Lie.first(x)), Name.key(n)}},
          Codes.Code.text_read(Ballot.voter(Lie.first(x)), Name.key(n))
        ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        {==}
    case Entry.Ask{Id{w, q}, t, a}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+pv, lk, z}}:
          h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# the key k of the asks index of an entry of the name n ends in the key of n
def Book.key_tail.asks(-Q: Data, e: Entry<Q>, +n: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 4n) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {
  Codes.Code.read_value(
    List<&2, U32>,
    Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}),
    []
  )
    == Name.key(n): List<&2, U32>
}:
  match e:
    case Entry.Ask{Id{+w, q}, t, a}:
      h =>
        %Shared.Maybe.some_inj(List<&2, U32>, Codes.Code.text(w, Name.key(n)), k, h): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(_), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        %Equal.sym(
          Maybe<&2, Codes.Read<String>>,
          Codes.Code.text.read(Codes.Code.text(w, Name.key(n))),
          Some{Codes.Read{w, Name.key(n)}},
          Codes.Code.text_read(w, Name.key(n))
        ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        {==}
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+pv, lk, z}}:
          h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# a key of the index i of entries of the names n1 and n2 is of names with the
# same key
# Book.key_tail.signed once the signer s of the ballot is known
def Book.key_tail.signed.at(+n: Name, -k: List<&2, U32>, s: Maybe<&2, Hashes.Hash>) -> {
  Maybe.map(&2, Hashes.Hash, List<&2, U32>, key => Hashes.Hash.code(key, Name.key(n)), s) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}:
  match s:
    case None{}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Some{+key}:
      h =>
        %Shared.Maybe.some_inj(List<&2, U32>, Hashes.Hash.code(key, Name.key(n)), k, h): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(_), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        %Equal.sym(
          Maybe<&2, Codes.Read<Hashes.Hash>>,
          Hashes.Hash.code.read(Hashes.Hash.code(key, Name.key(n))),
          Some{Codes.Read{key, Name.key(n)}},
          Hashes.Hash.code_read(key, Name.key(n))
        ): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, _, a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}
        {==}

# the key k of the signed index (5 on) of an entry of the name n ends in the
# key of n
def Book.key_tail.signed(-Q: Data, e: Entry<Q>, +n: Name, -p: Nat, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 5n+p) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}:
  match e:
    case Entry.Ballot{b}:
      match b:
        case Ballot{Signed{Place{+line, +h, +r}, +voter, +a}, Link{+pv, +lk, +z}}:
          Book.key_tail.signed.at(n, k, Ballot.signer(Ballot{Signed{Place{line, h, r}, voter, a}, Link{pv, lk, z}}))
    case Entry.Ask{Id{w, q}, t, a}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

def Book.keys_one(-Q: Data, +i: Nat, e1: Entry<Q>, +n1: Name, e2: Entry<Q>, +n2: Name, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e1, n1), i) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {Keys.at(Entry.keys(Q, e2, n2), i) == Some{k}: Maybe<&2, List<&2, U32>>} -> {Name.key(n1) == Name.key(n2): List<&2, U32>}:
  match i:
    case 0n:
      h1 => h2 =>
        Equal.trans(
          List<&2, U32>,
          Name.key(n1),
          Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []),
          Name.key(n2),
          Equal.sym(List<&2, U32>, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Place, String, Place.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []), Name.key(n1), Book.key_tail.ballots(Q, e1, n1, k)(h1)),
          Book.key_tail.ballots(Q, e2, n2, k)(h2)
        )
    case 1n+i1:
      match i1:
        case 0n:
          h1 => h2 =>
            Equal.trans(
              List<&2, U32>,
              Name.key(n1),
              List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)),
              Name.key(n2),
              Equal.sym(List<&2, U32>, List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)), Name.key(n1), Book.key_tail.rounds(Q, e1, n1, k)(h1)),
              Book.key_tail.rounds(Q, e2, n2, k)(h2)
            )
        case 1n+i2:
          match i2:
            case 0n:
              h1 => h2 =>
                Equal.trans(
                  List<&2, U32>,
                  Name.key(n1),
                  List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)),
                  Name.key(n2),
                  Equal.sym(List<&2, U32>, List.drop(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Nat.sub(List.length(&2, U32, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Line, List<&2, U32>, Line.code.read(k), a => r => Some{Codes.Read{r, []}}), [])), 9n)), Name.key(n1), Book.key_tail.heights(Q, e1, n1, k)(h1)),
                  Book.key_tail.heights(Q, e2, n2, k)(h2)
                )
            case 1n+i3:
              match i3:
                case 0n:
                  h1 => h2 =>
                    Equal.trans(
                      List<&2, U32>,
                      Name.key(n1),
                      Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []),
                      Name.key(n2),
                      Equal.sym(List<&2, U32>, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []), Name.key(n1), Book.key_tail.liars(Q, e1, n1, k)(h1)),
                      Book.key_tail.liars(Q, e2, n2, k)(h2)
                    )
                case 1n+i4:
                  match i4:
                    case 0n:
                      h1 => h2 =>
                        Equal.trans(
                          List<&2, U32>,
                          Name.key(n1),
                          Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []),
                          Name.key(n2),
                          Equal.sym(List<&2, U32>, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []), Name.key(n1), Book.key_tail.asks(Q, e1, n1, k)(h1)),
                          Book.key_tail.asks(Q, e2, n2, k)(h2)
                        )
                    case 1n+p:
                      h1 => h2 =>
                        Equal.trans(
                          List<&2, U32>,
                          Name.key(n1),
                          Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []),
                          Name.key(n2),
                          Equal.sym(List<&2, U32>, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(Hashes.Hash, List<&2, U32>, Hashes.Hash.code.read(k), a => r => Some{Codes.Read{r, []}}), []), Name.key(n1), Book.key_tail.signed(Q, e1, n1, p, k)(h1)),
                          Book.key_tail.signed(Q, e2, n2, p, k)(h2)
                        )

# what the dict d holds under k is what its map holds there
def Book.dict_lookup(~V: Data, d: Crits.Dict(V), +k: List<&2, U32>) -> {
  Crits.Dict.get(V, d, k) == Crits.Crit.lookup(V, Crits.Dict.crit(V, d), k): Maybe<&2, V>
}:
  match d:
    case Tuple{+m, w}:
      Crits.Crit.get_lookup(~V, m, k)(w)

# each entry of the dict d is an entry of its map
def Book.dict_agrees(~V: Data, d: Crits.Dict(V)) -> Crits.Crit.agrees(V, Crits.Dict.entries(V, d), Crits.Dict.crit(V, d)):
  match d:
    case Tuple{+m, w}:
      Crits.Crit.sub_to_list(V, m, [], m)(Crits.Crit.sub_self(~V, m, 0n)(w))(Unit{})

# Book.when_end once the test of k2 and k is known (b)
def Book.when_end.at(-V: Data, -f: List<&2, U32> -> V -> Bool, +k2: List<&2, U32>, -w: V, +k: List<&2, U32>, -v: V, b: Bool) -> {
  Crits.Key.is_eq(k2, k) == b: Bool
} -> {f(k2)(w) == True{}: Bool} -> {Shared.Maybe.when(V, b, u => Some{w}) == Some{v}: Maybe<&2, V>} -> {f(k)(v) == True{}: Bool}:
  match b:
    case True{}:
      eb => hf => hw =>
        %Crits.Key.is_eq_sound(k2, k)(eb): {f(_)(v) == True{}: Bool}
        %Shared.Maybe.some_inj(V, w, v, hw): {f(k2)(_) == True{}: Bool}
        hf
    case False{}:
      eb => hf => hw => Empty.absurd({f(k)(v) == True{}: Bool}, Shared.Maybe.none_ne_some(V, v, hw))

# what holds of an entry of the key k2 and the value w holds of what it gives,
# read at k
def Book.when_end(-V: Data, -f: List<&2, U32> -> V -> Bool, +k2: List<&2, U32>, -w: V, +k: List<&2, U32>, -v: V) -> {f(k2)(w) == True{}: Bool} -> {
  Shared.Maybe.when(V, Crits.Key.is_eq(k2, k), u => Some{w}) == Some{v}: Maybe<&2, V>
} -> {f(k)(v) == True{}: Bool}:
  Book.when_end.at(V, f, k2, w, k, v, Crits.Key.is_eq(k2, k))({==})

# the entries rest of the book b are each in their place, when those of m
# then rest are
def Book.ok.entries_rest(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, m: Crits.Crit<Entry<Q>>, +rest: List<&2, Crits.Bind<Entry<Q>>>) -> {
  Book.ok.entries(~Q, ~c, b, Crits.Crit.entries.go(Entry<Q>, m, rest)) == True{}: Bool
} -> {Book.ok.entries(~Q, ~c, b, rest) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => h
    case Crits.Crit.Leaf{k, +v}:
      h => Shared.Bool.and_true_right(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))), Book.ok.entries(~Q, ~c, b, rest))(h)
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      h => Book.ok.entries_rest(~Q, ~c, b, o, rest)(Book.ok.entries_rest(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest))(h))
    case Crits.Crit.Fork{+r, p, Some{+v}, +z, +o}:
      h =>
        Book.ok.entries_rest(~Q, ~c, b, o, rest)(
          Book.ok.entries_rest(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest))(
            Shared.Bool.and_true_right(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), r), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))), Book.ok.entries(~Q, ~c, b, Crits.Crit.entries.go(Entry<Q>, z, Crits.Crit.entries.go(Entry<Q>, o, rest))))(h)
          )
        )

# an entry of m is in its place in the book b, when the entries of m then
# rest are
def Book.ok.entries_at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, m: Crits.Crit<Entry<Q>>, +rest: List<&2, Crits.Bind<Entry<Q>>>, +k: List<&2, U32>, -v: Entry<Q>) -> {
  Book.ok.entries(~Q, ~c, b, Crits.Crit.entries.go(Entry<Q>, m, rest)) == True{}: Bool
} -> {Crits.Crit.lookup(Entry<Q>, m, k) == Some{v}: Maybe<&2, Entry<Q>>} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => hl => Empty.absurd({Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Shared.Maybe.none_ne_some(Entry<Q>, v, hl))
    case Crits.Crit.Leaf{+k2, +w}:
      h => hl => Book.when_end(Entry<Q>, kk => +vv => Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, vv)), kk), Book.indexed(Q, b, Entry.keys(Q, vv, Entry.name(~Q, ~c, vv)), Entry.name(~Q, ~c, vv))), k2, w, k, v)(Shared.Bool.and_true_left(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, w)), k2), Book.indexed(Q, b, Entry.keys(Q, w, Entry.name(~Q, ~c, w)), Entry.name(~Q, ~c, w))), Book.ok.entries(~Q, ~c, b, rest))(h))(hl)
    case Crits.Crit.Fork{+r, p, None{}, +z, +o}:
      +h => hl =>
        Crits.Crit.or3_some(Entry<Q>, {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Crits.Crit.ended(Entry<Q>, r, None{}, k), Crits.Crit.lookup(Entry<Q>, z, k), Crits.Crit.lookup(Entry<Q>, o, k), v)(
          he => Empty.absurd({Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Shared.Maybe.none_ne_some(Entry<Q>, v, he))
        )(hz => Book.ok.entries_at(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest), k, v)(h)(hz))(
          ho => Book.ok.entries_at(~Q, ~c, b, o, rest, k, v)(Book.ok.entries_rest(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest))(h))(ho)
        )(hl)
    case Crits.Crit.Fork{+r, p, Some{+w}, +z, +o}:
      +h => hl =>
        +h2 = Shared.Bool.and_true_right(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, w)), r), Book.indexed(Q, b, Entry.keys(Q, w, Entry.name(~Q, ~c, w)), Entry.name(~Q, ~c, w))), Book.ok.entries(~Q, ~c, b, Crits.Crit.entries.go(Entry<Q>, z, Crits.Crit.entries.go(Entry<Q>, o, rest))))(h)
        Crits.Crit.or3_some(Entry<Q>, {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Crits.Crit.ended(Entry<Q>, r, Some{w}, k), Crits.Crit.lookup(Entry<Q>, z, k), Crits.Crit.lookup(Entry<Q>, o, k), v)(
          he => Book.when_end(Entry<Q>, kk => +vv => Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, vv)), kk), Book.indexed(Q, b, Entry.keys(Q, vv, Entry.name(~Q, ~c, vv)), Entry.name(~Q, ~c, vv))), r, w, k, v)(Shared.Bool.and_true_left(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, w)), r), Book.indexed(Q, b, Entry.keys(Q, w, Entry.name(~Q, ~c, w)), Entry.name(~Q, ~c, w))), Book.ok.entries(~Q, ~c, b, Crits.Crit.entries.go(Entry<Q>, z, Crits.Crit.entries.go(Entry<Q>, o, rest))))(h))(he)
        )(hz => Book.ok.entries_at(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest), k, v)(h2)(hz))(
          ho => Book.ok.entries_at(~Q, ~c, b, o, rest, k, v)(Book.ok.entries_rest(~Q, ~c, b, z, Crits.Crit.entries.go(Entry<Q>, o, rest))(h2))(ho)
        )(hl)

# an entry of the dict d is in its place in the book b, when the entries of d
# are
def Book.ok.entries_get(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +d: Crits.Dict(Entry<Q>), +k: List<&2, U32>, -v: Entry<Q>) -> {
  Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, d)) == True{}: Bool
} -> {Crits.Dict.get(Entry<Q>, d, k) == Some{v}: Maybe<&2, Entry<Q>>} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  h => hg =>
    Book.ok.entries_at(~Q, ~c, b, Crits.Dict.crit(Entry<Q>, d), [], k, v)(h)(
      Equal.trans(
        Maybe<&2, Entry<Q>>,
        Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, d), k),
        Crits.Dict.get(Entry<Q>, d, k),
        Some{v},
        Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, d, k), Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, d), k), Book.dict_lookup(~Entry<Q>, d, k)),
        hg
      )
    )

# the keys rest of the index i of the book b each name an entry with that key,
# when those of m then rest do
def Book.ok.index_rest(-Q: Data, +b: Book<Q>, +i: Nat, m: Crits.Crit<Name>, +rest: List<&2, Crits.Bind<Name>>) -> {
  Book.ok.index(Q, b, i, Crits.Crit.entries.go(Name, m, rest)) == True{}: Bool
} -> {Book.ok.index(Q, b, i, rest) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => h
    case Crits.Crit.Leaf{k, +v}:
      h => Shared.Bool.and_true_right(Book.ok.key(Q, Book.get(Q, b, v), i, k, v), Book.ok.index(Q, b, i, rest))(h)
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      h => Book.ok.index_rest(Q, b, i, o, rest)(Book.ok.index_rest(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest))(h))
    case Crits.Crit.Fork{+r, p, Some{+v}, +z, +o}:
      h =>
        Book.ok.index_rest(Q, b, i, o, rest)(
          Book.ok.index_rest(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest))(
            Shared.Bool.and_true_right(Book.ok.key(Q, Book.get(Q, b, v), i, r, v), Book.ok.index(Q, b, i, Crits.Crit.entries.go(Name, z, Crits.Crit.entries.go(Name, o, rest))))(h)
          )
        )

# a key of m of the index i of the book b names an entry with that key, when
# the keys of m then rest do
def Book.ok.index_at(-Q: Data, +b: Book<Q>, +i: Nat, m: Crits.Crit<Name>, +rest: List<&2, Crits.Bind<Name>>, +k: List<&2, U32>, -x: Name) -> {
  Book.ok.index(Q, b, i, Crits.Crit.entries.go(Name, m, rest)) == True{}: Bool
} -> {Crits.Crit.lookup(Name, m, k) == Some{x}: Maybe<&2, Name>} -> {Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      h => hl => Empty.absurd({Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}, Shared.Maybe.none_ne_some(Name, x, hl))
    case Crits.Crit.Leaf{+k2, +w}:
      h => hl => Book.when_end(Name, kk => +vv => Book.ok.key(Q, Book.get(Q, b, vv), i, kk, vv), k2, w, k, x)(Shared.Bool.and_true_left(Book.ok.key(Q, Book.get(Q, b, w), i, k2, w), Book.ok.index(Q, b, i, rest))(h))(hl)
    case Crits.Crit.Fork{+r, p, None{}, +z, +o}:
      +h => hl =>
        Crits.Crit.or3_some(Name, {Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}, Crits.Crit.ended(Name, r, None{}, k), Crits.Crit.lookup(Name, z, k), Crits.Crit.lookup(Name, o, k), x)(
          he => Empty.absurd({Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}, Shared.Maybe.none_ne_some(Name, x, he))
        )(hz => Book.ok.index_at(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest), k, x)(h)(hz))(
          ho => Book.ok.index_at(Q, b, i, o, rest, k, x)(Book.ok.index_rest(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest))(h))(ho)
        )(hl)
    case Crits.Crit.Fork{+r, p, Some{+w}, +z, +o}:
      +h => hl =>
        +h2 = Shared.Bool.and_true_right(Book.ok.key(Q, Book.get(Q, b, w), i, r, w), Book.ok.index(Q, b, i, Crits.Crit.entries.go(Name, z, Crits.Crit.entries.go(Name, o, rest))))(h)
        Crits.Crit.or3_some(Name, {Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}, Crits.Crit.ended(Name, r, Some{w}, k), Crits.Crit.lookup(Name, z, k), Crits.Crit.lookup(Name, o, k), x)(
          he => Book.when_end(Name, kk => +vv => Book.ok.key(Q, Book.get(Q, b, vv), i, kk, vv), r, w, k, x)(Shared.Bool.and_true_left(Book.ok.key(Q, Book.get(Q, b, w), i, r, w), Book.ok.index(Q, b, i, Crits.Crit.entries.go(Name, z, Crits.Crit.entries.go(Name, o, rest))))(h))(he)
        )(hz => Book.ok.index_at(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest), k, x)(h2)(hz))(
          ho => Book.ok.index_at(Q, b, i, o, rest, k, x)(Book.ok.index_rest(Q, b, i, z, Crits.Crit.entries.go(Name, o, rest))(h2))(ho)
        )(hl)

# a key of the dict d names an entry of the book b with that key in the index
# i, when the keys of d do
def Book.ok.index_get(-Q: Data, +b: Book<Q>, +i: Nat, +d: Crits.Dict(Name), +k: List<&2, U32>, -x: Name) -> {
  Book.ok.index(Q, b, i, Crits.Dict.entries(Name, d)) == True{}: Bool
} -> {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>} -> {Book.ok.key(Q, Book.get(Q, b, x), i, k, x) == True{}: Bool}:
  h => hg =>
    Book.ok.index_at(Q, b, i, Crits.Dict.crit(Name, d), [], k, x)(h)(
      Equal.trans(
        Maybe<&2, Name>,
        Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k),
        Crits.Dict.get(Name, d, k),
        Some{x},
        Equal.sym(Maybe<&2, Name>, Crits.Dict.get(Name, d, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Book.dict_lookup(~Name, d, k)),
        hg
      )
    )

# the entries of a put
def Book.entries_put(~Q: Data, b: Book<Q>, +e: Entry<Q>, +n: Name, -ks: Keys) -> {
  Book.entries(Q, Book.put(~Q, b, e, n, ks)) == Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(n), e): Crits.Dict(Entry<Q>)
}:
  match b:
    case Book{es, bs, rs, hs, ls, as, fs}:
      {==}

# the index i of a put
def Book.index_put(~Q: Data, b: Book<Q>, -e: Entry<Q>, +n: Name, ks: Keys, i: Nat) -> {
  Book.index(Q, Book.put(~Q, b, e, n, ks), i) == Index.put(Book.index(Q, b, i), Keys.at(ks, i), n): Crits.Dict(Name)
}:
  match b ks:
    case Book{es, bs, rs, hs, ls, as, fs} Keys{kb, kr, kh, kl, ka, kf}:
      match i:
        case 0n:
          {==}
        case 1n+i1:
          match i1:
            case 0n:
              {==}
            case 1n+i2:
              match i2:
                case 0n:
                  {==}
                case 1n+i3:
                  match i3:
                    case 0n:
                      {==}
                    case 1n+i4:
                      match i4:
                        case 0n:
                          {==}
                        case 1n+p:
                          {==}

# the entries of a take
def Book.entries_take(~Q: Data, b: Book<Q>, +n: Name, -ks: Keys) -> {
  Book.entries(Q, Book.take(~Q, b, n, ks)) == Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)): Crits.Dict(Entry<Q>)
}:
  match b:
    case Book{es, bs, rs, hs, ls, as, fs}:
      {==}

# the index i of a take
def Book.index_take(~Q: Data, b: Book<Q>, -n: Name, ks: Keys, i: Nat) -> {
  Book.index(Q, Book.take(~Q, b, n, ks), i) == Index.drop(Book.index(Q, b, i), Keys.at(ks, i)): Crits.Dict(Name)
}:
  match b ks:
    case Book{es, bs, rs, hs, ls, as, fs} Keys{kb, kr, kh, kl, ka, kf}:
      match i:
        case 0n:
          {==}
        case 1n+i1:
          match i1:
            case 0n:
              {==}
            case 1n+i2:
              match i2:
                case 0n:
                  {==}
                case 1n+i3:
                  match i3:
                    case 0n:
                      {==}
                    case 1n+i4:
                      match i4:
                        case 0n:
                          {==}
                        case 1n+p:
                          {==}

# a put of the name n under the key m holds n there
def Index.holds_put(d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>, +n: Name) -> {Index.holds(Index.put(d, m, n), m, n) == True{}: Bool}:
  match m:
    case None{}:
      {==}
    case Some{+k}:
      %Equal.sym(
        Maybe<&2, Name>,
        Crits.Dict.get(Name, Crits.Dict.set(~Name, d, k, n), k),
        Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k), Some{n}, Crits.Dict.get(Name, d, k)),
        Crits.Dict.get_set(~Name, d, k, n, k)
      ): {Shared.Maybe.is_eq(~Name, ~Name.is_eq, _, Some{n}) == True{}: Bool}
      %Equal.sym(Bool, Crits.Key.is_eq(k, k), True{}, Crits.Key.is_eq_refl(k)): {
        Shared.Maybe.is_eq(~Name, ~Name.is_eq, Bool.pick(Maybe<&2, Name>, _, Some{n}, Crits.Dict.get(Name, d, k)), Some{n}) == True{}: Bool
      }
      Name.is_eq_refl(n)

# a put under a key m that m2 is not keeps what holds under m2
def Index.holds_put_apart(+d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>, m2: Maybe<&2, List<&2, U32>>, +n: Name, +n2: Name) -> (
  @k: List<&2, U32> -> {m == Some{k}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{k}: Maybe<&2, List<&2, U32>>} -> Empty
) -> {Index.holds(Index.put(d, m, n), m2, n2) == Index.holds(d, m2, n2): Bool}:
  match m m2:
    case None{} y:
      dist => {==}
    case Some{+k} None{}:
      dist => {==}
    case Some{+k} Some{+k2}:
      dist =>
        %Equal.sym(
          Maybe<&2, Name>,
          Crits.Dict.get(Name, Crits.Dict.set(~Name, d, k, n), k2),
          Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), Some{n}, Crits.Dict.get(Name, d, k2)),
          Crits.Dict.get_set(~Name, d, k, n, k2)
        ): {
          Shared.Maybe.is_eq(~Name, ~Name.is_eq, _, Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool
        }
        Book.by({Shared.Maybe.is_eq(~Name, ~Name.is_eq, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), Some{n}, Crits.Dict.get(Name, d, k2)), Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool}, Crits.Key.is_eq(k2, k))(
          t => Empty.absurd({Shared.Maybe.is_eq(~Name, ~Name.is_eq, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), Some{n}, Crits.Dict.get(Name, d, k2)), Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool}, dist(k)({==})(Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, k2, k, Crits.Key.is_eq_sound(k2, k)(t))))
        )(
          f => Equal.cong(
            Maybe<&2, Name>,
            Bool,
            z => Shared.Maybe.is_eq(~Name, ~Name.is_eq, z, Some{n2}),
            Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), Some{n}, Crits.Dict.get(Name, d, k2)),
            Crits.Dict.get(Name, d, k2),
            Book.pick_false(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), Some{n}, Crits.Dict.get(Name, d, k2))(f)
          )
        )

# a drop of a key m that m2 is not keeps what holds under m2
def Index.holds_drop_apart(+d: Crits.Dict(Name), m: Maybe<&2, List<&2, U32>>, m2: Maybe<&2, List<&2, U32>>, +n2: Name) -> (
  @k: List<&2, U32> -> {m == Some{k}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{k}: Maybe<&2, List<&2, U32>>} -> Empty
) -> {Index.holds(Index.drop(d, m), m2, n2) == Index.holds(d, m2, n2): Bool}:
  match m m2:
    case None{} y:
      dist => {==}
    case Some{+k} None{}:
      dist => {==}
    case Some{+k} Some{+k2}:
      dist =>
        %Equal.sym(
          Maybe<&2, Name>,
          Crits.Dict.get(Name, Crits.Dict.drop(~Name, d, k), k2),
          Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), None{}, Crits.Dict.get(Name, d, k2)),
          Crits.Dict.get_drop(~Name, d, k, k2)
        ): {
          Shared.Maybe.is_eq(~Name, ~Name.is_eq, _, Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool
        }
        Book.by({Shared.Maybe.is_eq(~Name, ~Name.is_eq, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), None{}, Crits.Dict.get(Name, d, k2)), Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool}, Crits.Key.is_eq(k2, k))(
          t => Empty.absurd({Shared.Maybe.is_eq(~Name, ~Name.is_eq, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), None{}, Crits.Dict.get(Name, d, k2)), Some{n2}) == Shared.Maybe.is_eq(~Name, ~Name.is_eq, Crits.Dict.get(Name, d, k2), Some{n2}): Bool}, dist(k)({==})(Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, k2, k, Crits.Key.is_eq_sound(k2, k)(t))))
        )(
          f => Equal.cong(
            Maybe<&2, Name>,
            Bool,
            z => Shared.Maybe.is_eq(~Name, ~Name.is_eq, z, Some{n2}),
            Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), None{}, Crits.Dict.get(Name, d, k2)),
            Crits.Dict.get(Name, d, k2),
            Book.pick_false(Maybe<&2, Name>, Crits.Key.is_eq(k2, k), None{}, Crits.Dict.get(Name, d, k2))(f)
          )
        )

# keys that Crits.Key.is_eq calls apart are not equal
def Book.key_apart(+a: List<&2, U32>, +b: List<&2, U32>) -> {Crits.Key.is_eq(a, b) == False{}: Bool} -> {b == a: List<&2, U32>} -> Empty:
  hf => e =>
    Shared.Bool.true_ne_false(
      Equal.trans(
        Bool,
        True{},
        Crits.Key.is_eq(a, b),
        False{},
        Equal.trans(
          Bool,
          True{},
          Crits.Key.is_eq(a, a),
          Crits.Key.is_eq(a, b),
          Equal.sym(Bool, Crits.Key.is_eq(a, a), True{}, Crits.Key.is_eq_refl(a)),
          Equal.cong(List<&2, U32>, Bool, z => Crits.Key.is_eq(a, z), a, b, Equal.sym(List<&2, U32>, b, a, e))
        ),
        hf
      )
    )

# a book that each index of which holds what another holds under the keys ks
# indexes the name n there as the other does
def Book.indexed_same(-Q: Data, +b: Book<Q>, +b2: Book<Q>, +ks: Keys, +n: Name) -> {
  Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n) == Index.holds(Book.index(Q, b, 0n), Keys.at(ks, 0n), n): Bool
} -> {
  Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n) == Index.holds(Book.index(Q, b, 1n), Keys.at(ks, 1n), n): Bool
} -> {
  Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n) == Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n): Bool
} -> {
  Index.holds(Book.index(Q, b2, 3n), Keys.at(ks, 3n), n) == Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n): Bool
} -> {
  Index.holds(Book.index(Q, b2, 4n), Keys.at(ks, 4n), n) == Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n): Bool
} -> {
  Index.holds(Book.index(Q, b2, 5n), Keys.at(ks, 5n), n) == Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n): Bool
} -> {Book.indexed(Q, b2, ks, n) == Book.indexed(Q, b, ks, n): Bool}:
  e0 => e1 => e2 => e3 => e4 => e5 =>
    %e0: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(_, Index.holds(Book.index(Q, b, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Bool.and(Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n), Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n)))): Bool}
    %e1: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), _), Bool.and(Bool.and(Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Bool.and(Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n), Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n)))): Bool}
    %e2: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(_, Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Bool.and(Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n), Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n)))): Bool}
    %e3: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n), _), Bool.and(Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n), Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n)))): Bool}
    %e4: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b2, 3n), Keys.at(ks, 3n), n)), Bool.and(_, Index.holds(Book.index(Q, b, 5n), Keys.at(ks, 5n), n)))): Bool}
    %e5: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b2, 3n), Keys.at(ks, 3n), n)), Bool.and(Index.holds(Book.index(Q, b2, 4n), Keys.at(ks, 4n), n), _))): Bool}
    {==}

# a put of an entry e of the name n keeps what the index i holds under the key
# there of an entry v of a name m whose key is not that of n
def Book.holds_put(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +v: Entry<Q>, +m: Name, +i: Nat) -> {
  Crits.Key.is_eq(Name.key(m), Name.key(n)) == False{}: Bool
} -> {
  Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), i), Keys.at(Entry.keys(Q, v, m), i), m)
    == Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, v, m), i), m): Bool
}:
  hne =>
    %Equal.sym(
      Crits.Dict(Name),
      Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), i),
      Index.put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i), n),
      Book.index_put(~Q, b, e, n, Entry.keys(Q, e, n), i)
    ): {Index.holds(_, Keys.at(Entry.keys(Q, v, m), i), m) == Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, v, m), i), m): Bool}
    Index.holds_put_apart(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i), Keys.at(Entry.keys(Q, v, m), i), n, m)(
      kk => h1 => h2 => Book.key_apart(Name.key(m), Name.key(n))(hne)(Book.keys_one(Q, i, e, n, v, m, kk)(h1)(h2))
    )

# a take of an entry e of the name n keeps what the index i holds under the
# key there of an entry v of a name m whose key is not that of n
def Book.holds_take(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +v: Entry<Q>, +m: Name, +i: Nat) -> {
  Crits.Key.is_eq(Name.key(m), Name.key(n)) == False{}: Bool
} -> {
  Index.holds(Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), Keys.at(Entry.keys(Q, v, m), i), m)
    == Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, v, m), i), m): Bool
}:
  hne =>
    %Equal.sym(
      Crits.Dict(Name),
      Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i),
      Index.drop(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i)),
      Book.index_take(~Q, b, n, Entry.keys(Q, e, n), i)
    ): {Index.holds(_, Keys.at(Entry.keys(Q, v, m), i), m) == Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, v, m), i), m): Bool}
    Index.holds_drop_apart(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i), Keys.at(Entry.keys(Q, v, m), i), m)(
      kk => h1 => h2 => Book.key_apart(Name.key(m), Name.key(n))(hne)(Book.keys_one(Q, i, e, n, v, m, kk)(h1)(h2))
    )

# a put of the entry e of the name n indexes n under its key in the index i
def Book.holds_put_same(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +i: Nat) -> {
  Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), i), Keys.at(Entry.keys(Q, e, n), i), n) == True{}: Bool
}:
  %Equal.sym(
    Crits.Dict(Name),
    Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), i),
    Index.put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i), n),
    Book.index_put(~Q, b, e, n, Entry.keys(Q, e, n), i)
  ): {Index.holds(_, Keys.at(Entry.keys(Q, e, n), i), n) == True{}: Bool}
  Index.holds_put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i), n)

# a put of the entry e of the name n indexes n under each key of e
def Book.indexed_put(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name) -> {
  Book.indexed(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), Entry.keys(Q, e, n), n) == True{}: Bool
}:
  Shared.Bool.and_both(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 0n), Keys.at(Entry.keys(Q, e, n), 0n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 1n), Keys.at(Entry.keys(Q, e, n), 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n)), Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 4n), Keys.at(Entry.keys(Q, e, n), 4n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 5n), Keys.at(Entry.keys(Q, e, n), 5n), n))))(
    Shared.Bool.and_both(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 0n), Keys.at(Entry.keys(Q, e, n), 0n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 1n), Keys.at(Entry.keys(Q, e, n), 1n), n))(Book.holds_put_same(~Q, b, e, n, 0n))(Book.holds_put_same(~Q, b, e, n, 1n))
  )(
    Shared.Bool.and_both(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n)), Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 4n), Keys.at(Entry.keys(Q, e, n), 4n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 5n), Keys.at(Entry.keys(Q, e, n), 5n), n)))(Shared.Bool.and_both(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n))(Book.holds_put_same(~Q, b, e, n, 2n))(Book.holds_put_same(~Q, b, e, n, 3n)))(
      Shared.Bool.and_both(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 4n), Keys.at(Entry.keys(Q, e, n), 4n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 5n), Keys.at(Entry.keys(Q, e, n), 5n), n))(Book.holds_put_same(~Q, b, e, n, 4n))(Book.holds_put_same(~Q, b, e, n, 5n))
    )
  )

# an entry of the book b other than e is in its place after the add of e
def Book.add_entry.old(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, +k: List<&2, U32>, +v: Entry<Q>) -> {
  Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))) == False{}: Bool
} -> {Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k) == Some{v}: Maybe<&2, Entry<Q>>} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  +f => hv =>
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), k, v)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(hok))(hv)
    +hkm = Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, v)), k)(
      Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)))(hc)
    )
    +hne = Equal.trans(Bool, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), Name.key(Entry.name(~Q, ~c, e))), Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), False{}, Equal.cong(List<&2, U32>, Bool, z => Crits.Key.is_eq(z, Name.key(Entry.name(~Q, ~c, e))), Name.key(Entry.name(~Q, ~c, v)), k, hkm), f)
    %Equal.sym(
      Bool,
      Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed_same(Q, b, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 0n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 1n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 2n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 3n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 4n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 5n)(hne))
    ): {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), _) == True{}: Bool}
    hc

# each entry of the book b with e added is in its place
def Book.add_entry(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, +k: List<&2, U32>, +v: Entry<Q>) -> {
  Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k) == Some{v}: Maybe<&2, Entry<Q>>
} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  hg =>
    +hp = Equal.trans(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k), Crits.Dict.get(Entry<Q>, Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, k), Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Book.entries_put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.get_set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e, k))), hg)
    Book.by({Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))))(
      +t =>
        %Shared.Maybe.some_inj(
          Entry<Q>,
          e,
          v,
          Equal.trans(Maybe<&2, Entry<Q>>, Some{e}, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Some{e}, Book.pick_true(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k))(t)), hp)
        ): {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, _)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, _, Entry.name(~Q, ~c, _)), Entry.name(~Q, ~c, _))) == True{}: Bool}
        %Equal.sym(List<&2, U32>, k, Name.key(Entry.name(~Q, ~c, e)), Crits.Key.is_eq_sound(k, Name.key(Entry.name(~Q, ~c, e)))(t)): {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, e)), _), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, e, Entry.name(~Q, ~c, e)), Entry.name(~Q, ~c, e))) == True{}: Bool}
        Shared.Bool.and_both(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, e)), Name.key(Entry.name(~Q, ~c, e))), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, e, Entry.name(~Q, ~c, e)), Entry.name(~Q, ~c, e)))(
          Crits.Key.is_eq_refl(Name.key(Entry.name(~Q, ~c, e)))
        )(Book.indexed_put(~Q, b, e, Entry.name(~Q, ~c, e)))
    )(
      +f =>
        Book.add_entry.old(~Q, ~c, b, e, hok, k, v)(f)(
          Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k))(f)), hp)
        )
    )

# the entries l of the map of the book b with e added are in their place
def Book.add_entries(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, l: List<&2, Crits.Bind<Entry<Q>>>) -> Crits.Crit.agrees(
  Entry<Q>,
  l,
  Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))))
) -> {Book.ok.entries(~Q, ~c, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), l) == True{}: Bool}:
  match l:
    case Nil{}:
      a => {==}
    case Con{Crits.Bind{+k, +v}, +rest}:
      +a =>
        Shared.Bool.and_both(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))), Book.ok.entries(~Q, ~c, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), rest))(
          Book.add_entry(~Q, ~c, b, e, hok, k, v)(
            Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k), Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))))), k), Some{v}, Book.dict_lookup(~Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), k), Crits.Crit.agrees.hd(Entry<Q>, k, v, rest, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))))), a))
          )
        )(Book.add_entries(~Q, ~c, b, e, hok, rest)(Crits.Crit.agrees.tl(Entry<Q>, k, v, rest, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))))), a)))

# a key of the index i of the book b names an entry with that key after the add of e
def Book.add_key.old(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hn: {Book.get(Q, b, Entry.name(~Q, ~c, e)) == None{}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name) -> {
  Crits.Dict.get(Name, Book.index(Q, b, i), k) == Some{x}: Maybe<&2, Name>
} -> {Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), x), i, k, x) == True{}: Bool}:
  hg =>
    +hd = Book.ok.index_get(Q, b, i, Book.index(Q, b, i), k, x)(ho)(hg)
    %Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Name.key(x)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Name.key(x)), Crits.Dict.get(Entry<Q>, Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Name.key(x)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, Name.key(x)), Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Book.entries_put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.get_set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e, Name.key(x)))): {Book.ok.key(Q, _, i, k, x) == True{}: Bool}
    Book.by({Book.ok.key(Q, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), i, k, x) == True{}: Bool}, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))))(
      +t =>
        Empty.absurd(
          {Book.ok.key(Q, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), i, k, x) == True{}: Bool},
          Shared.Bool.false_ne_true(
            Equal.trans(Bool, False{}, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), False{}, Equal.cong(Maybe<&2, Entry<Q>>, Bool, z => Book.ok.key(Q, z, i, k, x), Book.get(Q, b, x), None{}, Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, b, x), Book.get(Q, b, Entry.name(~Q, ~c, e)), None{}, Equal.cong(List<&2, U32>, Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, Book.entries(Q, b), z), Name.key(x), Name.key(Entry.name(~Q, ~c, e)), Crits.Key.is_eq_sound(Name.key(x), Name.key(Entry.name(~Q, ~c, e)))(t)), hn))), hd)
          )
        )
    )(
      +f =>
        %Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x)), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x)))(f)): {
          Book.ok.key(Q, _, i, k, x) == True{}: Bool
        }
        hd
    )

# Book.add_key once the key of e in the index i is known (m)
def Book.add_key.at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hn: {Book.get(Q, b, Entry.name(~Q, ~c, e)) == None{}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name, m: Maybe<&2, List<&2, U32>>) -> {
  Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i) == m: Maybe<&2, List<&2, U32>>
} -> {Crits.Dict.get(Name, Index.put(Book.index(Q, b, i), m, Entry.name(~Q, ~c, e)), k) == Some{x}: Maybe<&2, Name>} -> {Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), x), i, k, x) == True{}: Bool}:
  match m:
    case None{}:
      em => hg => Book.add_key.old(~Q, ~c, b, e, hn, i, ho, k, x)(hg)
    case Some{+k0}:
      em => hg =>
        +hp = Equal.trans(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get(Name, Crits.Dict.set(~Name, Book.index(Q, b, i), k0, Entry.name(~Q, ~c, e)), k), Some{x}, Equal.sym(Maybe<&2, Name>, Crits.Dict.get(Name, Crits.Dict.set(~Name, Book.index(Q, b, i), k0, Entry.name(~Q, ~c, e)), k), Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get_set(~Name, Book.index(Q, b, i), k0, Entry.name(~Q, ~c, e), k)), hg)
        Book.by({Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), x), i, k, x) == True{}: Bool}, Crits.Key.is_eq(k, k0))(
          +t =>
            %Shared.Maybe.some_inj(
              Name,
              Entry.name(~Q, ~c, e),
              x,
              Equal.trans(Maybe<&2, Name>, Some{Entry.name(~Q, ~c, e)}, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Some{Entry.name(~Q, ~c, e)}, Book.pick_true(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k))(t)), hp)
            ): {Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), _), i, k, _) == True{}: Bool}
            %Equal.sym(List<&2, U32>, k, k0, Crits.Key.is_eq_sound(k, k0)(t)): {Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.name(~Q, ~c, e)), i, _, Entry.name(~Q, ~c, e)) == True{}: Bool}
            %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.name(~Q, ~c, e)), Some{e}, Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Name.key(Entry.name(~Q, ~c, e))), Crits.Dict.get(Entry<Q>, Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, Name.key(Entry.name(~Q, ~c, e))), Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Book.entries_put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Name.key(Entry.name(~Q, ~c, e))), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, e)), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)))), Some{e}, Crits.Dict.get_set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e, Name.key(Entry.name(~Q, ~c, e))), Book.pick_true(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, e)), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e))))(Crits.Key.is_eq_refl(Name.key(Entry.name(~Q, ~c, e))))))): {Book.ok.key(Q, _, i, k0, Entry.name(~Q, ~c, e)) == True{}: Bool}
            %Equal.sym(Maybe<&2, List<&2, U32>>, Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i), Some{k0}, em): {Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, _, Some{k0}) == True{}: Bool}
            Crits.Key.is_eq_refl(k0)
        )(
          +f =>
            Book.add_key.old(~Q, ~c, b, e, hn, i, ho, k, x)(
              Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Book.index(Q, b, i), k), Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get(Name, Book.index(Q, b, i), k), Book.pick_false(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), Some{Entry.name(~Q, ~c, e)}, Crits.Dict.get(Name, Book.index(Q, b, i), k))(f)), hp)
            )
        )

# each key of the index i of the book b with e added names an entry with that key
def Book.add_key(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hn: {Book.get(Q, b, Entry.name(~Q, ~c, e)) == None{}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name) -> {
  Crits.Dict.get(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), k) == Some{x}: Maybe<&2, Name>
} -> {Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), x), i, k, x) == True{}: Bool}:
  hg =>
    Book.add_key.at(~Q, ~c, b, e, hn, i, ho, k, x, Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i))({==})(
      Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Index.put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i), Entry.name(~Q, ~c, e)), k), Crits.Dict.get(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), k), Some{x}, Equal.cong(Crits.Dict(Name), Maybe<&2, Name>, z => Crits.Dict.get(Name, z, k), Index.put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i), Entry.name(~Q, ~c, e)), Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), Equal.sym(Crits.Dict(Name), Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), Index.put(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i), Entry.name(~Q, ~c, e)), Book.index_put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)), i))), hg)
    )

# the keys l of the map of the index i of the book b with e added each name an entry with that key
def Book.add_index(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hn: {Book.get(Q, b, Entry.name(~Q, ~c, e)) == None{}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, l: List<&2, Crits.Bind<Name>>) -> Crits.Crit.agrees(
  Name,
  l,
  Crits.Dict.crit(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i))
) -> {Book.ok.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i, l) == True{}: Bool}:
  match l:
    case Nil{}:
      a => {==}
    case Con{Crits.Bind{+k, +x}, +rest}:
      +a =>
        Shared.Bool.and_both(Book.ok.key(Q, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), x), i, k, x), Book.ok.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i, rest))(
          Book.add_key(~Q, ~c, b, e, hn, i, ho, k, x)(
            Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i)), k), Some{x}, Book.dict_lookup(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i), k), Crits.Crit.agrees.hd(Name, k, x, rest, Crits.Dict.crit(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i)), a))
          )
        )(Book.add_index(~Q, ~c, b, e, hn, i, ho, rest)(Crits.Crit.agrees.tl(Name, k, x, rest, Crits.Dict.crit(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), i)), a)))

# a put of an entry e that the book b lacks keeps b in its one shape
def Book.add_ok(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>) -> {Book.ok(~Q, ~c, b) == True{}: Bool} -> {Book.get(Q, b, Entry.name(~Q, ~c, e)) == None{}: Maybe<&2, Entry<Q>>} -> {Book.ok(~Q, ~c, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))) == True{}: Bool}:
  +hok => +hn =>
    +r = Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(hok)
    +l01 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(r)
    +r25 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(r)
    +l23 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(r25)
    +r45 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(r25)
    +a0 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a1 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a2 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a3 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a4 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(r45)
    +a5 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(r45)
    Shared.Bool.and_both(Book.ok.entries(~Q, ~c, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))))), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n)))))(Book.add_entries(~Q, ~c, b, e, hok, Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))))))(Book.dict_agrees(~Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))))))(
      Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n))))(
        Shared.Bool.and_both(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n))(Book.add_index(~Q, ~c, b, e, hn, 0n, a0, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n))))(Book.add_index(~Q, ~c, b, e, hn, 1n, a1, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n))))
      )(
        Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n)))(Shared.Bool.and_both(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n))(Book.add_index(~Q, ~c, b, e, hn, 2n, a2, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n))))(Book.add_index(~Q, ~c, b, e, hn, 3n, a3, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)))))(
          Shared.Bool.and_both(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n))(Book.add_index(~Q, ~c, b, e, hn, 4n, a4, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n))))(Book.add_index(~Q, ~c, b, e, hn, 5n, a5, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 5n))))
        )
      )
    )

# a maybe that is not some is none
def Book.none_of(-A: Data, m: Maybe<&2, A>) -> {Maybe.is_some(&2, A, m) == False{}: Bool} -> {m == None{}: Maybe<&2, A>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Shared.Bool.true_ne_false(h))

# an add keeps a book in its one shape
law Book.ok_add:
  for ~Q: Data
  for ~c: Codes.Codec(Q)
  for b: Book<Q>
  for e: Entry<Q>
  {Book.ok(~Q, ~c, b) == True{}: Bool} -> {Book.ok(~Q, ~c, Book.add(~Q, ~c, b, e)) == True{}: Bool}

def Book.ok_add(Q, c, b, e):
  +b = b
  +e = e
  +h =>
    Shared.Bool.when_cases(
      Book<Q>,
      x => {Book.ok(~Q, ~c, x) == True{}: Bool},
      Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e))),
      u => b,
      u => Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))),
      t => h,
      f => Book.add_ok(~Q, ~c, b, e)(h)(Book.none_of(Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)))(f))
    )

# an entry of the book b other than that of n is in its place after the take of n
def Book.drop_entry.old(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +n: Name, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, +k: List<&2, U32>, +v: Entry<Q>) -> {
  Crits.Key.is_eq(k, Name.key(n)) == False{}: Bool
} -> {Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k) == Some{v}: Maybe<&2, Entry<Q>>} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  +f => hv =>
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), k, v)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(hok))(hv)
    +hkm = Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, v)), k)(
      Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)))(hc)
    )
    +hne = Equal.trans(Bool, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), Name.key(n)), Crits.Key.is_eq(k, Name.key(n)), False{}, Equal.cong(List<&2, U32>, Bool, z => Crits.Key.is_eq(z, Name.key(n)), Name.key(Entry.name(~Q, ~c, v)), k, hkm), f)
    %Equal.sym(
      Bool,
      Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed_same(Q, b, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 0n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 1n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 2n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 3n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 4n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 5n)(hne))
    ): {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), _) == True{}: Bool}
    hc

# each entry of the book b with the take of n is in its place
def Book.drop_entry(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +n: Name, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, +k: List<&2, U32>, +v: Entry<Q>) -> {
  Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k) == Some{v}: Maybe<&2, Entry<Q>>
} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  hg =>
    +hp = Equal.trans(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k), Crits.Dict.get(Entry<Q>, Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, k), Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), Book.entries_take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.get_drop(~Entry<Q>, Book.entries(Q, b), Name.key(n), k))), hg)
    Book.by({Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}, Crits.Key.is_eq(k, Name.key(n)))(
      +t =>
        Empty.absurd(
          {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool},
          Shared.Maybe.none_ne_some(
            Entry<Q>,
            v,
            Equal.trans(Maybe<&2, Entry<Q>>, None{}, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), None{}, Book.pick_true(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k))(t)), hp)
          )
        )
    )(
      +f =>
        Book.drop_entry.old(~Q, ~c, b, e, n, hok, k, v)(f)(
          Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k)), Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(k, Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k))(f)), hp)
        )
    )

# the entries l of the map of the book b with the take of n are in their place
def Book.drop_entries(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +n: Name, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, l: List<&2, Crits.Bind<Entry<Q>>>) -> Crits.Crit.agrees(
  Entry<Q>,
  l,
  Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))))
) -> {Book.ok.entries(~Q, ~c, Book.take(~Q, b, n, Entry.keys(Q, e, n)), l) == True{}: Bool}:
  match l:
    case Nil{}:
      a => {==}
    case Con{Crits.Bind{+k, +v}, +rest}:
      +a =>
        Shared.Bool.and_both(Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))), Book.ok.entries(~Q, ~c, Book.take(~Q, b, n, Entry.keys(Q, e, n)), rest))(
          Book.drop_entry(~Q, ~c, b, e, n, hok, k, v)(
            Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k), Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)))), k), Some{v}, Book.dict_lookup(~Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), k), Crits.Crit.agrees.hd(Entry<Q>, k, v, rest, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)))), a))
          )
        )(Book.drop_entries(~Q, ~c, b, e, n, hok, rest)(Crits.Crit.agrees.tl(Entry<Q>, k, v, rest, Crits.Dict.crit(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)))), a)))

# a key of the index i of the book b names an entry with that key after the take of n, when it is not a key of the entry e of n
def Book.drop_key.old(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +hm: {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name) -> {Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, Keys.at(Entry.keys(Q, e, n), i), Some{k}) == False{}: Bool} -> {
  Crits.Dict.get(Name, Book.index(Q, b, i), k) == Some{x}: Maybe<&2, Name>
} -> {Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x) == True{}: Bool}:
  +hM => hg =>
    +hd = Book.ok.index_get(Q, b, i, Book.index(Q, b, i), k, x)(ho)(hg)
    %Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), Name.key(x)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), Name.key(x)), Crits.Dict.get(Entry<Q>, Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), Name.key(x)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, Name.key(x)), Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), Book.entries_take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.get_drop(~Entry<Q>, Book.entries(Q, b), Name.key(n), Name.key(x)))): {Book.ok.key(Q, _, i, k, x) == True{}: Bool}
    Book.by({Book.ok.key(Q, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), i, k, x) == True{}: Bool}, Crits.Key.is_eq(Name.key(x), Name.key(n)))(
      +t =>
        +ex = Name.key_inj(x, n)(Crits.Key.is_eq_sound(Name.key(x), Name.key(n))(t))
        +h1 = Equal.trans(Bool, Book.ok.key(Q, Book.get(Q, b, n), i, k, n), Book.ok.key(Q, Book.get(Q, b, x), i, k, x), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), Book.ok.key(Q, Book.get(Q, b, n), i, k, n), Equal.cong(Name, Bool, +z => Book.ok.key(Q, Book.get(Q, b, z), i, k, z), x, n, ex)), hd)
        +h2 = Equal.trans(Bool, Book.ok.key(Q, Some{e}, i, k, n), Book.ok.key(Q, Book.get(Q, b, n), i, k, n), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, n), i, k, n), Book.ok.key(Q, Some{e}, i, k, n), Equal.cong(Maybe<&2, Entry<Q>>, Bool, z => Book.ok.key(Q, z, i, k, n), Book.get(Q, b, n), Some{e}, hm)), h1)
        Empty.absurd({Book.ok.key(Q, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), i, k, x) == True{}: Bool}, Shared.Bool.true_ne_false(Equal.trans(Bool, True{}, Book.ok.key(Q, Some{e}, i, k, n), False{}, Equal.sym(Bool, Book.ok.key(Q, Some{e}, i, k, n), True{}, h2), hM)))
    )(
      +f =>
        %Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x))), Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x)), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(x), Name.key(n)), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, b), Name.key(x)))(f)): {
          Book.ok.key(Q, _, i, k, x) == True{}: Bool
        }
        hd
    )

# Book.drop_key once the key of e in the index i is known (m)
def Book.drop_key.at(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +hm: {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name, m: Maybe<&2, List<&2, U32>>) -> {
  Keys.at(Entry.keys(Q, e, n), i) == m: Maybe<&2, List<&2, U32>>
} -> {Crits.Dict.get(Name, Index.drop(Book.index(Q, b, i), m), k) == Some{x}: Maybe<&2, Name>} -> {Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x) == True{}: Bool}:
  match m:
    case None{}:
      em => hg =>
        Book.drop_key.old(~Q, b, e, n, hm, i, ho, k, x)(Equal.cong(Maybe<&2, List<&2, U32>>, Bool, z => Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, z, Some{k}), Keys.at(Entry.keys(Q, e, n), i), None{}, em))(hg)
    case Some{+k0}:
      em => hg =>
        +hp = Equal.trans(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get(Name, Crits.Dict.drop(~Name, Book.index(Q, b, i), k0), k), Some{x}, Equal.sym(Maybe<&2, Name>, Crits.Dict.get(Name, Crits.Dict.drop(~Name, Book.index(Q, b, i), k0), k), Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get_drop(~Name, Book.index(Q, b, i), k0, k)), hg)
        Book.by({Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x) == True{}: Bool}, Crits.Key.is_eq(k, k0))(
          +t =>
            Empty.absurd(
              {Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x) == True{}: Bool},
              Shared.Maybe.none_ne_some(
                Name,
                x,
                Equal.trans(Maybe<&2, Name>, None{}, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), None{}, Book.pick_true(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k))(t)), hp)
              )
            )
        )(
          +f =>
            Book.drop_key.old(~Q, b, e, n, hm, i, ho, k, x)(
              Equal.trans(Bool, Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, Keys.at(Entry.keys(Q, e, n), i), Some{k}), Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, Some{k0}, Some{k}), False{}, Equal.cong(Maybe<&2, List<&2, U32>>, Bool, z => Shared.Maybe.is_eq(~List<&2, U32>, ~Crits.Key.is_eq, z, Some{k}), Keys.at(Entry.keys(Q, e, n), i), Some{k0}, em), Crits.Key.ne_sym(k, k0)(f))
            )(
              Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Book.index(Q, b, i), k), Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k)), Crits.Dict.get(Name, Book.index(Q, b, i), k), Book.pick_false(Maybe<&2, Name>, Crits.Key.is_eq(k, k0), None{}, Crits.Dict.get(Name, Book.index(Q, b, i), k))(f)), hp)
            )
        )

# each key of the index i of the book b with the take of n names an entry with that key
def Book.drop_key(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +hm: {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name) -> {
  Crits.Dict.get(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), k) == Some{x}: Maybe<&2, Name>
} -> {Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x) == True{}: Bool}:
  hg =>
    Book.drop_key.at(~Q, b, e, n, hm, i, ho, k, x, Keys.at(Entry.keys(Q, e, n), i))({==})(
      Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Index.drop(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i)), k), Crits.Dict.get(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), k), Some{x}, Equal.cong(Crits.Dict(Name), Maybe<&2, Name>, z => Crits.Dict.get(Name, z, k), Index.drop(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i)), Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), Equal.sym(Crits.Dict(Name), Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), Index.drop(Book.index(Q, b, i), Keys.at(Entry.keys(Q, e, n), i)), Book.index_take(~Q, b, n, Entry.keys(Q, e, n), i))), hg)
    )

# the keys l of the map of the index i of the book b with the take of n each name an entry with that key
def Book.drop_index(~Q: Data, +b: Book<Q>, +e: Entry<Q>, +n: Name, +hm: {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>}, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, l: List<&2, Crits.Bind<Name>>) -> Crits.Crit.agrees(
  Name,
  l,
  Crits.Dict.crit(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i))
) -> {Book.ok.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i, l) == True{}: Bool}:
  match l:
    case Nil{}:
      a => {==}
    case Con{Crits.Bind{+k, +x}, +rest}:
      +a =>
        Shared.Bool.and_both(Book.ok.key(Q, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), x), i, k, x), Book.ok.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i, rest))(
          Book.drop_key(~Q, b, e, n, hm, i, ho, k, x)(
            Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i)), k), Some{x}, Book.dict_lookup(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i), k), Crits.Crit.agrees.hd(Name, k, x, rest, Crits.Dict.crit(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i)), a))
          )
        )(Book.drop_index(~Q, b, e, n, hm, i, ho, rest)(Crits.Crit.agrees.tl(Name, k, x, rest, Crits.Dict.crit(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), i)), a)))

# a take of the entry e of the name n that the book b holds keeps b in its one shape
def Book.drop_ok(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +n: Name) -> {Book.ok(~Q, ~c, b) == True{}: Bool} -> {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>} -> {Book.ok(~Q, ~c, Book.take(~Q, b, n, Entry.keys(Q, e, n))) == True{}: Bool}:
  +hok => +hm =>
    +r = Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(hok)
    +l01 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(r)
    +r25 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(r)
    +l23 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(r25)
    +r45 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(r25)
    +a0 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a1 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a2 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a3 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a4 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(r45)
    +a5 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(r45)
    Shared.Bool.and_both(Book.ok.entries(~Q, ~c, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))))), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n)))))(Book.drop_entries(~Q, ~c, b, e, n, hok, Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)))))(Book.dict_agrees(~Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))))))(
      Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n))))(
        Shared.Bool.and_both(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n))(Book.drop_index(~Q, b, e, n, hm, 0n, a0, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n))))(Book.drop_index(~Q, b, e, n, hm, 1n, a1, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n))))
      )(
        Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n)))(Shared.Bool.and_both(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n))(Book.drop_index(~Q, b, e, n, hm, 2n, a2, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n))))(Book.drop_index(~Q, b, e, n, hm, 3n, a3, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)))))(
          Shared.Bool.and_both(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n))(Book.drop_index(~Q, b, e, n, hm, 4n, a4, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n))))(Book.drop_index(~Q, b, e, n, hm, 5n, a5, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 5n))))
        )
      )
    )

# Book.ok_drop once what the book b holds under n is known (m)
def Book.ok_drop.at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +n: Name, m: Maybe<&2, Entry<Q>>) -> {Book.get(Q, b, n) == m: Maybe<&2, Entry<Q>>} -> {Book.ok(~Q, ~c, b) == True{}: Bool} -> {Book.ok(~Q, ~c, Book.drop.at(~Q, b, n, m)) == True{}: Bool}:
  match m:
    case None{}:
      em => hok => hok
    case Some{+e}:
      em => hok => Book.drop_ok(~Q, ~c, b, e, n)(hok)(em)

# a drop keeps a book in its one shape
law Book.ok_drop:
  for ~Q: Data
  for ~c: Codes.Codec(Q)
  for b: Book<Q>
  for n: Name
  {Book.ok(~Q, ~c, b) == True{}: Bool} -> {Book.ok(~Q, ~c, Book.drop(~Q, b, n)) == True{}: Bool}

def Book.ok_drop(Q, c, b, n):
  +b = b
  +n = n
  h => Book.ok_drop.at(~Q, ~c, b, n, Book.get(Q, b, n))({==})(h)

# The kind of books
# -----------------

# a book in its one shape, when c is the code of changes
def Book.L(~Q: Data, ~c: Codes.Codec(Q)) -> Data:
  Sigma<&2, &2, Book<Q>, b => {Book.ok(~Q, ~c, b) == True{}: Bool}>

# the book of a book in its one shape
def Book.L.book(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c)) -> Book<Q>:
  match x:
    case Tuple{b, w}:
      b

# x with the entry e
def Book.L.add(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +e: Entry<Q>) -> Book.L(~Q, ~c):
  match x:
    case Tuple{+b, w}:
      (Book.add(~Q, ~c, b, e), Book.ok_add(~Q, ~c, b, e)(w))

# x without the entry of the name n
def Book.L.drop(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +n: Name) -> Book.L(~Q, ~c):
  match x:
    case Tuple{+b, w}:
      (Book.drop(~Q, b, n), Book.ok_drop(~Q, ~c, b, n)(w))

# books as a way to keep the entries of a ledger, when c is the code of
# changes
def Book.kind(~Q: Data, ~c: Codes.Codec(Q)) -> Ledger.Kind(Q):
  (
    Book.L(~Q, ~c),
    (
      (Book.new(~Q), Book.ok_new(~Q, ~c)),
      (
        x => n => Book.get(Q, Book.L.book(~Q, ~c, x), n),
        (
          x => e => Book.L.add(~Q, ~c, x, e),
          (
            s => r => Book.missing(~Q, Book.L.book(~Q, ~c, s), Book.L.book(~Q, ~c, r)),
            (
              x => w => v => Book.ballots(Q, Book.L.book(~Q, ~c, x), w, v),
              (
                x => line => h => Book.rounds(Q, Book.L.book(~Q, ~c, x), line, h),
                (
                  x => r => Book.liars(Q, Book.L.book(~Q, ~c, x), r),
                  (
                    x => line => Book.heights(Q, Book.L.book(~Q, ~c, x), line),
                    (
                      x => a => Book.asks(Q, Book.L.book(~Q, ~c, x), a),
                      (
                        x => n => Book.L.drop(~Q, ~c, x, n),
                        x => key => Book.signed(Q, Book.L.book(~Q, ~c, x), key)
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
  )

# Name.is_eq is True only for equal names
def Name.is_eq_sound(a: Name, b: Name) -> {Name.is_eq(a, b) == True{}: Bool} -> {a == b: Name}:
  match a b:
    case Name.Ask{+x} Name.Ask{+y}:
      h => Equal.cong(Hashes.Hash, Name, z => Name.Ask{z}, x, y, Hashes.Hash.is_eq_sound(x, y)(h))
    case Name.Ask{x} Name.Ballot{y}:
      h => Empty.absurd({Name.Ask{x} == Name.Ballot{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Ask{x} Name.Data{y}:
      h => Empty.absurd({Name.Ask{x} == Name.Data{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Ask{x} Name.Lie{y}:
      h => Empty.absurd({Name.Ask{x} == Name.Lie{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Ballot{x} Name.Ask{y}:
      h => Empty.absurd({Name.Ballot{x} == Name.Ask{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Ballot{+x} Name.Ballot{+y}:
      h => Equal.cong(Hashes.Hash, Name, z => Name.Ballot{z}, x, y, Hashes.Hash.is_eq_sound(x, y)(h))
    case Name.Ballot{x} Name.Data{y}:
      h => Empty.absurd({Name.Ballot{x} == Name.Data{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Ballot{x} Name.Lie{y}:
      h => Empty.absurd({Name.Ballot{x} == Name.Lie{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Data{x} Name.Ask{y}:
      h => Empty.absurd({Name.Data{x} == Name.Ask{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Data{x} Name.Ballot{y}:
      h => Empty.absurd({Name.Data{x} == Name.Ballot{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Data{+x} Name.Data{+y}:
      h => Equal.cong(Hashes.Hash, Name, z => Name.Data{z}, x, y, Hashes.Hash.is_eq_sound(x, y)(h))
    case Name.Data{x} Name.Lie{y}:
      h => Empty.absurd({Name.Data{x} == Name.Lie{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Lie{x} Name.Ask{y}:
      h => Empty.absurd({Name.Lie{x} == Name.Ask{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Lie{x} Name.Ballot{y}:
      h => Empty.absurd({Name.Lie{x} == Name.Ballot{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Lie{x} Name.Data{y}:
      h => Empty.absurd({Name.Lie{x} == Name.Data{y}: Name}, Shared.Bool.false_ne_true(h))
    case Name.Lie{+x} Name.Lie{+y}:
      h => Equal.cong(Hashes.Hash, Name, z => Name.Lie{z}, x, y, Hashes.Hash.is_eq_sound(x, y)(h))

# an entry that a book in its one shape holds under n is of the name n
def Book.get_named(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +n: Name, +e: Entry<Q>) -> {
  Book.ok(~Q, ~c, b) == True{}: Bool
} -> {Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>} -> {Entry.name(~Q, ~c, e) == n: Name}:
  w => h =>
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), Name.key(n), e)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(w))(h)
    Name.key_inj(Entry.name(~Q, ~c, e), n)(
      Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, e)), Name.key(n))(
        Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, e)), Name.key(n)), Book.indexed(Q, b, Entry.keys(Q, e, Entry.name(~Q, ~c, e)), Entry.name(~Q, ~c, e)))(hc)
      )
    )

# what a book with e added holds under n
def Book.get_add(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +n: Name) -> {
  Book.get(Q, Book.add(~Q, ~c, b, e), n)
    == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>
}:
  Shared.Bool.when_cases(
    Book<Q>,
    x => {Book.get(Q, x, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>},
    Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e))),
    u => b,
    u => Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))),
    +t =>
      Book.by({Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}, Name.is_eq(Entry.name(~Q, ~c, e), n))(
        +tt =>
          +en = Name.is_eq_sound(Entry.name(~Q, ~c, e), n)(tt)
          %Equal.sym(Bool, Name.is_eq(Entry.name(~Q, ~c, e), n), True{}, tt): {Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, _, u => Some{e})): Maybe<&2, Entry<Q>>}
          Equal.sym(Maybe<&2, Entry<Q>>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Some{e}), Book.get(Q, b, n), Crits.Crit.or_of_some(Entry<Q>, Book.get(Q, b, n), Some{e})(
            Equal.trans(Bool, Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, n)), Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e))), True{}, Equal.cong(Name, Bool, z => Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, z)), n, Entry.name(~Q, ~c, e), Equal.sym(Name, Entry.name(~Q, ~c, e), n, en)), t)
          ))
      )(
        +ff =>
          %Equal.sym(Bool, Name.is_eq(Entry.name(~Q, ~c, e), n), False{}, ff): {Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, _, u => Some{e})): Maybe<&2, Entry<Q>>}
          Equal.sym(Maybe<&2, Entry<Q>>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), None{}), Book.get(Q, b, n), Shared.Maybe.or_none(Entry<Q>, Book.get(Q, b, n)))
      ),
    +f =>
      +hn = Book.none_of(Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)))(f)
      %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), n), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n)), Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), n), Crits.Dict.get(Entry<Q>, Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Name.key(n)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n)), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, Name.key(n)), Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e), Book.entries_put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))), Crits.Dict.get_set(~Entry<Q>, Book.entries(Q, b), Name.key(Entry.name(~Q, ~c, e)), e, Name.key(n)))): {_ == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}
      Book.by({Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n)) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))))(
        +t2 =>
          +enn = Name.key_inj(n, Entry.name(~Q, ~c, e))(Crits.Key.is_eq_sound(Name.key(n), Name.key(Entry.name(~Q, ~c, e)))(t2))
          %Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n)), Some{e}, Book.pick_true(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n))(t2)): {_ == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}
          %Equal.sym(Name, n, Entry.name(~Q, ~c, e), enn): {Some{e} == Maybe.or(&2, Entry<Q>, Book.get(Q, b, _), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), _), u => Some{e})): Maybe<&2, Entry<Q>>}
          %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, b, Entry.name(~Q, ~c, e)), None{}, hn): {Some{e} == Maybe.or(&2, Entry<Q>, _, Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), u => Some{e})): Maybe<&2, Entry<Q>>}
          %Equal.sym(Bool, Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), True{}, Name.is_eq_refl(Entry.name(~Q, ~c, e))): {Some{e} == Maybe.or(&2, Entry<Q>, None{}, Shared.Maybe.when(Entry<Q>, _, u => Some{e})): Maybe<&2, Entry<Q>>}
          {==}
      )(
        +f2 =>
          %Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n)), Book.get(Q, b, n), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Book.get(Q, b, n))(f2)): {_ == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}
          Book.by({Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>}, Name.is_eq(Entry.name(~Q, ~c, e), n))(
            +tt =>
              Empty.absurd(
                {Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>},
                Shared.Bool.true_ne_false(
                  Equal.trans(Bool, True{}, Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), False{}, Equal.trans(Bool, True{}, Crits.Key.is_eq(Name.key(n), Name.key(n)), Crits.Key.is_eq(Name.key(n), Name.key(Entry.name(~Q, ~c, e))), Equal.sym(Bool, Crits.Key.is_eq(Name.key(n), Name.key(n)), True{}, Crits.Key.is_eq_refl(Name.key(n))), Equal.cong(Name, Bool, z => Crits.Key.is_eq(Name.key(n), Name.key(z)), n, Entry.name(~Q, ~c, e), Equal.sym(Name, Entry.name(~Q, ~c, e), n, Name.is_eq_sound(Entry.name(~Q, ~c, e), n)(tt)))), f2)
                )
              )
          )(
            +ff =>
              %Equal.sym(Bool, Name.is_eq(Entry.name(~Q, ~c, e), n), False{}, ff): {Book.get(Q, b, n) == Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, _, u => Some{e})): Maybe<&2, Entry<Q>>}
              Equal.sym(Maybe<&2, Entry<Q>>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), None{}), Book.get(Q, b, n), Shared.Maybe.or_none(Entry<Q>, Book.get(Q, b, n)))
          )
      )
  )

# Book.get_drop once what the book b holds under n is known (mm)
def Book.get_drop.at(~Q: Data, +b: Book<Q>, +n: Name, +m: Name, mm: Maybe<&2, Entry<Q>>) -> {Book.get(Q, b, n) == mm: Maybe<&2, Entry<Q>>} -> {
  Book.get(Q, Book.drop.at(~Q, b, n, mm), m)
    == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>
}:
  match mm:
    case None{}:
      em =>
        Book.by({Book.get(Q, Book.drop.at(~Q, b, n, None{}), m) == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}, Name.is_eq(n, m))(
          +t =>
            %Equal.sym(Bool, Name.is_eq(n, m), True{}, t): {Book.get(Q, b, m) == Shared.Bool.when(Maybe<&2, Entry<Q>>, _, u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}
            %Name.is_eq_sound(n, m)(t): {Book.get(Q, b, _) == None{}: Maybe<&2, Entry<Q>>}
            em
        )(
          +f =>
            %Equal.sym(Bool, Name.is_eq(n, m), False{}, f): {Book.get(Q, b, m) == Shared.Bool.when(Maybe<&2, Entry<Q>>, _, u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}
            {==}
        )
    case Some{+e}:
      em =>
        %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), m), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)), Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), m), Crits.Dict.get(Entry<Q>, Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), Name.key(m)), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)), Equal.cong(Crits.Dict(Entry<Q>), Maybe<&2, Entry<Q>>, z => Crits.Dict.get(Entry<Q>, z, Name.key(m)), Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.drop(~Entry<Q>, Book.entries(Q, b), Name.key(n)), Book.entries_take(~Q, b, n, Entry.keys(Q, e, n))), Crits.Dict.get_drop(~Entry<Q>, Book.entries(Q, b), Name.key(n), Name.key(m)))): {_ == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}
        Book.by({Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)) == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}, Name.is_eq(n, m))(
          +t =>
            %Equal.sym(Bool, Name.is_eq(n, m), True{}, t): {Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)) == Shared.Bool.when(Maybe<&2, Entry<Q>>, _, u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}
            %Name.is_eq_sound(n, m)(t): {Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(_), Name.key(n)), None{}, Book.get(Q, b, _)) == None{}: Maybe<&2, Entry<Q>>}
            %Equal.sym(Bool, Crits.Key.is_eq(Name.key(n), Name.key(n)), True{}, Crits.Key.is_eq_refl(Name.key(n))): {
              Bool.pick(Maybe<&2, Entry<Q>>, _, None{}, Book.get(Q, b, n)) == None{}: Maybe<&2, Entry<Q>>
            }
            {==}
        )(
          +f =>
            %Equal.sym(Bool, Name.is_eq(n, m), False{}, f): {Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)) == Shared.Bool.when(Maybe<&2, Entry<Q>>, _, u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>}
            Book.by({Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)) == Book.get(Q, b, m): Maybe<&2, Entry<Q>>}, Crits.Key.is_eq(Name.key(m), Name.key(n)))(
              +t2 =>
                Empty.absurd(
                  {Bool.pick(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m)) == Book.get(Q, b, m): Maybe<&2, Entry<Q>>},
                  Shared.Bool.true_ne_false(
                    Equal.trans(Bool, True{}, Name.is_eq(n, m), False{}, Equal.trans(Bool, True{}, Name.is_eq(n, n), Name.is_eq(n, m), Equal.sym(Bool, Name.is_eq(n, n), True{}, Name.is_eq_refl(n)), Equal.cong(Name, Bool, z => Name.is_eq(n, z), n, m, Equal.sym(Name, m, n, Name.key_inj(m, n)(Crits.Key.is_eq_sound(Name.key(m), Name.key(n))(t2))))), f)
                  )
                )
            )(+f2 => Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Key.is_eq(Name.key(m), Name.key(n)), None{}, Book.get(Q, b, m))(f2))
        )

# what a book without the entry of n holds under m
def Book.get_drop(~Q: Data, +b: Book<Q>, +n: Name, +m: Name) -> {
  Book.get(Q, Book.drop(~Q, b, n), m)
    == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, b, m)): Maybe<&2, Entry<Q>>
}:
  Book.get_drop.at(~Q, b, n, m, Book.get(Q, b, n))({==})

# a book with e added holds e already
def Book.add_idem(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>) -> {
  Book.add(~Q, ~c, Book.add(~Q, ~c, b, e), e) == Book.add(~Q, ~c, b, e): Book<Q>
}:
  %Equal.sym(Bool, Maybe.is_some(&2, Entry<Q>, Book.get(Q, Book.add(~Q, ~c, b, e), Entry.name(~Q, ~c, e))), True{}, Equal.trans(Bool, Maybe.is_some(&2, Entry<Q>, Book.get(Q, Book.add(~Q, ~c, b, e), Entry.name(~Q, ~c, e))), Maybe.is_some(&2, Entry<Q>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), u => Some{e}))), True{}, Equal.cong(Maybe<&2, Entry<Q>>, Bool, z => Maybe.is_some(&2, Entry<Q>, z), Book.get(Q, Book.add(~Q, ~c, b, e), Entry.name(~Q, ~c, e)), Maybe.or(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), u => Some{e})), Book.get_add(~Q, ~c, b, e, Entry.name(~Q, ~c, e))), Equal.trans(Bool, Maybe.is_some(&2, Entry<Q>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), u => Some{e}))), Maybe.is_some(&2, Entry<Q>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), Some{e})), True{}, Equal.cong(Bool, Bool, z => Maybe.is_some(&2, Entry<Q>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), Shared.Maybe.when(Entry<Q>, z, u => Some{e}))), Name.is_eq(Entry.name(~Q, ~c, e), Entry.name(~Q, ~c, e)), True{}, Name.is_eq_refl(Entry.name(~Q, ~c, e))), Crits.Crit.or_some_is_some(Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, e)), e)))): {
    Shared.Bool.when(Book<Q>, _, u => Book.add(~Q, ~c, b, e), u => Book.put(~Q, Book.add(~Q, ~c, b, e), e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))) == Book.add(~Q, ~c, b, e): Book<Q>
  }
  {==}

# books in their one shape are equal when their books are: the proofs of the
# shape are
def Book.L.eq(~Q: Data, ~c: Codes.Codec(Q), +b1: Book<Q>, +b2: Book<Q>, e: {b1 == b2: Book<Q>}) -> @w1: {
  Book.ok(~Q, ~c, b1) == True{}: Bool
} -> @w2: {Book.ok(~Q, ~c, b2) == True{}: Bool} -> {Tuple{b1, w1} == Tuple{b2, w2}: Book.L(~Q, ~c)}:
  %e: @w1: {Book.ok(~Q, ~c, b1) == True{}: Bool} -> @w2: {Book.ok(~Q, ~c, _) == True{}: Bool} -> {Tuple{b1, w1} == Tuple{_, w2}: Book.L(~Q, ~c)}
  +w1 => +w2 =>
    %Crits.Bool.eq_one(Book.ok(~Q, ~c, b1), True{}, w1, w2): {Tuple{b1, w1} == Tuple{b1, _}: Book.L(~Q, ~c)}
    {==}

# an "any" whose hit is True is True
def Book.any_hit(b: Bool, -f: Unit -> Bool) -> {b == True{}: Bool} -> {List.any.if(f, b) == True{}: Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => Empty.absurd({f(Unit{}) == True{}: Bool}, Shared.Bool.false_ne_true(h))

# an "any" whose rest is True is True
def Book.any_rest(b: Bool, -r: Bool) -> {r == True{}: Bool} -> {List.any.if(u => r, b) == True{}: Bool}:
  match b:
    case True{}:
      h => {==}
    case False{}:
      h => h

# a maybe that is not some is none
def Book.none_true(-A: Data, m: Maybe<&2, A>) -> {Maybe.is_some(&2, A, m) == False{}: Bool} -> {Maybe.is_none(&2, A, m) == True{}: Bool}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({False{} == True{}: Bool}, Shared.Bool.true_ne_false(h))

# a maybe that is none is None
def Book.none_eq(-A: Data, m: Maybe<&2, A>) -> {Maybe.is_none(&2, A, m) == True{}: Bool} -> {m == None{}: Maybe<&2, A>}:
  match m:
    case None{}:
      h => {==}
    case Some{x}:
      h => Empty.absurd({Some{x} == None{}: Maybe<&2, A>}, Shared.Bool.false_ne_true(h))

# a value of the entries l of m that eq calls x is under a key of m
def Book.vals_sound(~V: Data, ~eq: V -> V -> Bool, l: List<&2, Crits.Bind<V>>, +x: V, -m: Crits.Crit<V>) -> Crits.Crit.agrees(V, l, m) -> {
  List.contains(~V, ~eq, Crits.Binds.values(V, l), x) == True{}: Bool
} -> Exists(List<&2, U32>, k => Exists(V, v => {Crits.Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>} & {eq(v, x) == True{}: Bool})):
  match l:
    case Nil{}:
      a => h => Empty.absurd(Exists(List<&2, U32>, k => Exists(V, v => {Crits.Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>} & {eq(v, x) == True{}: Bool})), Shared.Bool.false_ne_true(h))
    case Con{Crits.Bind{+k0, +v0}, +rest}:
      +a => +h =>
        Book.by(Exists(List<&2, U32>, k => Exists(V, v => {Crits.Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>} & {eq(v, x) == True{}: Bool})), eq(v0, x))(
          +t => (k0, (v0, (Crits.Crit.agrees.hd(V, k0, v0, rest, m, a), t)))
        )(
          +f =>
            Book.vals_sound(~V, ~eq, rest, x, m)(Crits.Crit.agrees.tl(V, k0, v0, rest, m, a))(
              Equal.trans(Bool, List.contains(~V, ~eq, Crits.Binds.values(V, rest), x), List.any.if(u => List.contains(~V, ~eq, Crits.Binds.values(V, rest), x), eq(v0, x)), True{}, Equal.sym(Bool, List.any.if(u => List.contains(~V, ~eq, Crits.Binds.values(V, rest), x), eq(v0, x)), List.contains(~V, ~eq, Crits.Binds.values(V, rest), x), Equal.cong(Bool, Bool, z => List.any.if(u => List.contains(~V, ~eq, Crits.Binds.values(V, rest), x), z), eq(v0, x), False{}, f)), h)
            )
        )

# the values of the entries of m then rest hold what those of rest hold
def Book.vals_mono(~V: Data, ~eq: V -> V -> Bool, m: Crits.Crit<V>, +rest: List<&2, Crits.Bind<V>>, +x: V) -> {List.contains(~V, ~eq, Crits.Binds.values(V, rest), x) == True{}: Bool} -> {
  List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool
}:
  match m:
    case Crits.Crit.Tip{}:
      h => h
    case Crits.Crit.Leaf{k, +v}:
      h => Book.any_rest(eq(v, x), List.contains(~V, ~eq, Crits.Binds.values(V, rest), x))(h)
    case Crits.Crit.Fork{r, p, None{}, +z, +o}:
      h => Book.vals_mono(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), x)(Book.vals_mono(~V, ~eq, o, rest, x)(h))
    case Crits.Crit.Fork{r, p, Some{+v}, +z, +o}:
      h =>
        Book.any_rest(eq(v, x), List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest))), x))(
          Book.vals_mono(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), x)(Book.vals_mono(~V, ~eq, o, rest, x)(h))
        )

# a value of m under a key, that eq calls x, is among the values of the entries of m then rest
def Book.vals_complete(~V: Data, ~eq: V -> V -> Bool, m: Crits.Crit<V>, +rest: List<&2, Crits.Bind<V>>, +k: List<&2, U32>, -v: V, +x: V) -> {
  Crits.Crit.lookup(V, m, k) == Some{v}: Maybe<&2, V>
} -> {eq(v, x) == True{}: Bool} -> {List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool}:
  match m:
    case Crits.Crit.Tip{}:
      hl => he => Empty.absurd({List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool}, Shared.Maybe.none_ne_some(V, v, hl))
    case Crits.Crit.Leaf{k2, +w}:
      hl => he =>
        Book.any_hit(eq(w, x), u => List.contains(~V, ~eq, Crits.Binds.values(V, rest), x))(
          %Equal.sym(V, w, v, Crits.Crit.ws_val(V, w, v, Crits.Key.is_eq(k2, k))(hl)): {eq(_, x) == True{}: Bool}
          he
        )
    case Crits.Crit.Fork{+r, p, None{}, +z, +o}:
      hl => +he =>
        Crits.Crit.or3_some(V, {List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool}, Crits.Crit.ended(V, r, None{}, k), Crits.Crit.lookup(V, z, k), Crits.Crit.lookup(V, o, k), v)(
          h1 => Empty.absurd({List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool}, Shared.Maybe.none_ne_some(V, v, h1))
        )(h2 => Book.vals_complete(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), k, v, x)(h2)(he))(
          h3 => Book.vals_mono(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), x)(Book.vals_complete(~V, ~eq, o, rest, k, v, x)(h3)(he))
        )(hl)
    case Crits.Crit.Fork{+r, p, Some{+w}, +z, +o}:
      hl => +he =>
        Crits.Crit.or3_some(V, {List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, m, rest)), x) == True{}: Bool}, Crits.Crit.ended(V, r, Some{w}, k), Crits.Crit.lookup(V, z, k), Crits.Crit.lookup(V, o, k), v)(
          h1 =>
            Book.any_hit(eq(w, x), u => List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest))), x))(
              %Equal.sym(V, w, v, Crits.Crit.ws_val(V, w, v, Crits.Key.is_eq(r, k))(h1)): {eq(_, x) == True{}: Bool}
              he
            )
        )(
          h2 =>
            Book.any_rest(eq(w, x), List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest))), x))(Book.vals_complete(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), k, v, x)(h2)(he))
        )(
          h3 =>
            Book.any_rest(eq(w, x), List.contains(~V, ~eq, Crits.Binds.values(V, Crits.Crit.entries.go(V, z, Crits.Crit.entries.go(V, o, rest))), x))(
              Book.vals_mono(~V, ~eq, z, Crits.Crit.entries.go(V, o, rest), x)(Book.vals_complete(~V, ~eq, o, rest, k, v, x)(h3)(he))
            )
        )(hl)

# Book.missing_sound once the key and the entry are found
def Book.missing_sound.of(~Q: Data, ~c: Codes.Codec(Q), +bs: Book<Q>, +ws: {Book.ok(~Q, ~c, bs) == True{}: Bool}, +br: Book<Q>, +e: Entry<Q>, ex: Exists(List<&2, U32>, k => Exists(Entry<Q>, v => {Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), k) == Some{v}: Maybe<&2, Entry<Q>>} & {Entry.same(~Q, ~c)(v, e) == True{}: Bool}))) -> {
  Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))) == True{}: Bool
}:
  match ex:
    case Tuple{+k, Tuple{+v, Tuple{hl, hs}}}:
      +hp = Equal.trans(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), k), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), Crits.Dict.get_minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br), k)), Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), k), Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), k), Some{v}, Book.dict_lookup(~Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), k), hl))
      Book.by({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))) == True{}: Bool}, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k))(
        +t => Empty.absurd({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))) == True{}: Bool}, Shared.Maybe.none_ne_some(Entry<Q>, v, Equal.trans(Maybe<&2, Entry<Q>>, None{}, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), None{}, Book.pick_true(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k))(t)), hp)))
      )(
        +f =>
          +hv = Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), Some{v}, Equal.sym(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k)), Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k), Book.pick_false(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), k), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k))(f)), hp)
          +hc = Book.ok.entries_get(~Q, ~c, bs, Book.entries(Q, bs), k, v)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, bs, Crits.Dict.entries(Entry<Q>, Book.entries(Q, bs))), Bool.and(Bool.and(Book.ok.at(Q, bs, 0n), Book.ok.at(Q, bs, 1n)), Bool.and(Bool.and(Book.ok.at(Q, bs, 2n), Book.ok.at(Q, bs, 3n)), Bool.and(Book.ok.at(Q, bs, 4n), Book.ok.at(Q, bs, 5n)))))(ws))(hv)
          +ek = Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, v)), k)(
            Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, bs, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)))(hc)
          )
          %Entry.same_sound(~Q, ~c, v, e)(hs): {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, _)), Some{_}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, _)))) == True{}: Bool}
          %Equal.sym(List<&2, U32>, Name.key(Entry.name(~Q, ~c, v)), k, ek): {
            Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), _), Some{v}), Maybe.is_none(&2, Entry<Q>, Crits.Dict.get(Entry<Q>, Book.entries(Q, br), _))) == True{}: Bool
          }
          %Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), k), Some{v}, hv): {
            Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), _, Some{v}), Maybe.is_none(&2, Entry<Q>, Crits.Dict.get(Entry<Q>, Book.entries(Q, br), k))) == True{}: Bool
          }
          Shared.Bool.and_both(Entry.same(~Q, ~c)(v, v), Maybe.is_none(&2, Entry<Q>, Crits.Dict.get(Entry<Q>, Book.entries(Q, br), k)))(Entry.same_refl(~Q, ~c, v))(
            Book.none_true(Entry<Q>, Crits.Dict.get(Entry<Q>, Book.entries(Q, br), k))(f)
          )
      )

# an entry that a book in its one shape sends to another it holds, and the other lacks
def Book.missing_sound(~Q: Data, ~c: Codes.Codec(Q), +bs: Book<Q>, +ws: {Book.ok(~Q, ~c, bs) == True{}: Bool}, +br: Book<Q>, +e: Entry<Q>) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.missing(~Q, bs, br), e) == True{}: Bool} -> {
  Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))) == True{}: Bool
}:
  h =>
    Book.missing_sound.of(~Q, ~c, bs, ws, br, e, Book.vals_sound(~Entry<Q>, ~Entry.same(~Q, ~c), Crits.Dict.entries(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), e, Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))))(Book.dict_agrees(~Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))))(h))

# a book sends each entry that it holds and another lacks
def Book.missing_complete(~Q: Data, ~c: Codes.Codec(Q), +bs: Book<Q>, +br: Book<Q>, +e: Entry<Q>) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.missing(~Q, bs, br), e) == True{}: Bool}:
  +h =>
    +hg = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), x => y => Entry.same_sound(~Q, ~c, x, y), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e})(
      Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e))))(h)
    )
    +hn = Book.none_eq(Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e))))(h))
    +hd = Equal.trans(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), Name.key(Entry.name(~Q, ~c, e))), Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), Name.key(Entry.name(~Q, ~c, e))), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), Name.key(Entry.name(~Q, ~c, e)))), Some{e}, Crits.Dict.get_minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br), Name.key(Entry.name(~Q, ~c, e))), Equal.trans(Maybe<&2, Entry<Q>>, Bool.pick(Maybe<&2, Entry<Q>>, Crits.Dict.has(Entry<Q>, Book.entries(Q, br), Name.key(Entry.name(~Q, ~c, e))), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), Name.key(Entry.name(~Q, ~c, e)))), Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Equal.cong(Maybe<&2, Entry<Q>>, Maybe<&2, Entry<Q>>, z => Bool.pick(Maybe<&2, Entry<Q>>, Maybe.is_some(&2, Entry<Q>, z), None{}, Crits.Dict.get(Entry<Q>, Book.entries(Q, bs), Name.key(Entry.name(~Q, ~c, e)))), Crits.Dict.get(Entry<Q>, Book.entries(Q, br), Name.key(Entry.name(~Q, ~c, e))), None{}, hn), hg))
    Book.vals_complete(~Entry<Q>, ~Entry.same(~Q, ~c), Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), [], Name.key(Entry.name(~Q, ~c, e)), e, e)(
      Equal.trans(Maybe<&2, Entry<Q>>, Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), Name.key(Entry.name(~Q, ~c, e))), Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), Name.key(Entry.name(~Q, ~c, e))), Some{e}, Equal.sym(Maybe<&2, Entry<Q>>, Crits.Dict.get(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), Name.key(Entry.name(~Q, ~c, e))), Crits.Crit.lookup(Entry<Q>, Crits.Dict.crit(Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br))), Name.key(Entry.name(~Q, ~c, e))), Book.dict_lookup(~Entry<Q>, Crits.Dict.minus(~Entry<Q>, Book.entries(Q, bs), Book.entries(Q, br)), Name.key(Entry.name(~Q, ~c, e)))), hd)
    )(Entry.same_refl(~Q, ~c, e))

# Book.law.missing of the books s and r
def Book.law.missing.at(~Q: Data, ~c: Codes.Codec(Q), s: Book.L(~Q, ~c), r: Book.L(~Q, ~c), +e: Entry<Q>) -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.missing(~Q, Book.L.book(~Q, ~c, s), Book.L.book(~Q, ~c, r)), e)
    == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, s), Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, Book.L.book(~Q, ~c, r), Entry.name(~Q, ~c, e)))): Bool
}:
  match s r:
    case Tuple{+bs, +ws} Tuple{+br, wr}:
      Crits.Crit.iff_eq(List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.missing(~Q, bs, br), e), Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, bs, Entry.name(~Q, ~c, e)), Some{e}), Maybe.is_none(&2, Entry<Q>, Book.get(Q, br, Entry.name(~Q, ~c, e)))))(Book.missing_sound(~Q, ~c, bs, ws, br, e))(Book.missing_complete(~Q, ~c, bs, br, e))

# dicts each of whose entries the other holds are one dict
def Book.dict_eq(~V: Data, d1: Crits.Dict(V), d2: Crits.Dict(V)) -> Crits.Crit.agrees(V, Crits.Dict.entries(V, d1), Crits.Dict.crit(V, d2)) -> Crits.Crit.agrees(
  V,
  Crits.Dict.entries(V, d2),
  Crits.Dict.crit(V, d1)
) -> {d1 == d2: Crits.Dict(V)}:
  match d1 d2:
    case Tuple{+m1, +w1} Tuple{+m2, +w2}:
      a12 => a21 =>
        Crits.Dict.of_eq(
          ~V,
          m1,
          m2,
          Crits.Crit.det(~V, m1, m2, 0n, 0n)(w1)(w2)(Crits.Crit.sub_of_list(V, m1, [], m2)(a12))(Crits.Crit.sub_of_list(V, m2, [], m1)(a21))
        )(w1)(w2)

# two picks whose tests are not both True can be taken in either order
def Book.pick_swap(-V: Data, c1: Bool, c2: Bool, -a1: Maybe<&2, V>, -a2: Maybe<&2, V>, -r: Maybe<&2, V>) -> ({c1 == True{}: Bool} -> {c2 == True{}: Bool} -> Empty) -> {
  Bool.pick(Maybe<&2, V>, c1, a1, Bool.pick(Maybe<&2, V>, c2, a2, r)) == Bool.pick(Maybe<&2, V>, c2, a2, Bool.pick(Maybe<&2, V>, c1, a1, r)): Maybe<&2, V>
}:
  match c1 c2:
    case True{} True{}:
      h => Empty.absurd({a1 == a2: Maybe<&2, V>}, h({==})({==}))
    case True{} False{}:
      h => {==}
    case False{} True{}:
      h => {==}
    case False{} False{}:
      h => {==}

# two writes of other keys give the same reads in either order
def Book.set_comm.get(~V: Data, +d: Crits.Dict(V), +k1: List<&2, U32>, +v1: V, +k2: List<&2, U32>, +v2: V, +hk: {Crits.Key.is_eq(k1, k2) == False{}: Bool}, +k: List<&2, U32>) -> {
  Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k) == Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k): Maybe<&2, V>
}:
  Equal.trans(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Crits.Dict.get(V, d, k))), Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Equal.trans(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Crits.Dict.get(V, Crits.Dict.set(~V, d, k2, v2), k)), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Crits.Dict.get(V, d, k))), Crits.Dict.get_set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1, k), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, z), Crits.Dict.get(V, Crits.Dict.set(~V, d, k2, v2), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Crits.Dict.get(V, d, k)), Crits.Dict.get_set(~V, d, k2, v2, k))), Equal.trans(Maybe<&2, V>, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Crits.Dict.get(V, d, k))), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Crits.Dict.get(V, d, k))), Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Book.pick_swap(V, Crits.Key.is_eq(k, k1), Crits.Key.is_eq(k, k2), Some{v1}, Some{v2}, Crits.Dict.get(V, d, k))(t1 => t2 => Book.key_apart(k1, k2)(hk)(Equal.trans(List<&2, U32>, k2, k, k1, Equal.sym(List<&2, U32>, k, k2, Crits.Key.is_eq_sound(k, k2)(t2)), Crits.Key.is_eq_sound(k, k1)(t1)))), Equal.sym(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Crits.Dict.get(V, d, k))), Equal.trans(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Crits.Dict.get(V, Crits.Dict.set(~V, d, k1, v1), k)), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Crits.Dict.get(V, d, k))), Crits.Dict.get_set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2, k), Equal.cong(Maybe<&2, V>, Maybe<&2, V>, z => Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k2), Some{v2}, z), Crits.Dict.get(V, Crits.Dict.set(~V, d, k1, v1), k), Bool.pick(Maybe<&2, V>, Crits.Key.is_eq(k, k1), Some{v1}, Crits.Dict.get(V, d, k)), Crits.Dict.get_set(~V, d, k1, v1, k))))))

# the entries l of one order of two writes are entries of the other
def Book.set_comm.list(~V: Data, +d: Crits.Dict(V), +k1: List<&2, U32>, +v1: V, +k2: List<&2, U32>, +v2: V, +hk: {Crits.Key.is_eq(k1, k2) == False{}: Bool}, l: List<&2, Crits.Bind<V>>) -> Crits.Crit.agrees(V, l, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2))) -> Crits.Crit.agrees(
  V,
  l,
  Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1))
):
  match l:
    case Nil{}:
      a => Unit{}
    case Con{Crits.Bind{+k, +v}, +rest}:
      +a =>
        (
          Equal.trans(Maybe<&2, V>, Crits.Crit.lookup(V, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1)), k), Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k), Some{v}, Equal.sym(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k), Crits.Crit.lookup(V, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1)), k), Book.dict_lookup(~V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k)), Equal.trans(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1), k), Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Some{v}, Book.set_comm.get(~V, d, k1, v1, k2, v2, hk, k), Equal.trans(Maybe<&2, V>, Crits.Dict.get(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Crits.Crit.lookup(V, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2)), k), Some{v}, Book.dict_lookup(~V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), k), Crits.Crit.agrees.hd(V, k, v, rest, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2)), a)))),
          Book.set_comm.list(~V, d, k1, v1, k2, v2, hk, rest)(Crits.Crit.agrees.tl(V, k, v, rest, Crits.Dict.crit(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2)), a))
        )

# writes of two other keys can be taken in either order
def Book.set_comm(~V: Data, +d: Crits.Dict(V), +k1: List<&2, U32>, +v1: V, +k2: List<&2, U32>, +v2: V) -> {Crits.Key.is_eq(k1, k2) == False{}: Bool} -> {Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2) == Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1): Crits.Dict(V)}:
  +hk =>
    Book.dict_eq(~V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2), Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1))(
      Book.set_comm.list(~V, d, k1, v1, k2, v2, hk, Crits.Dict.entries(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2)))(Book.dict_agrees(~V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k1, v1), k2, v2)))
    )(
      Book.set_comm.list(~V, d, k2, v2, k1, v1, Crits.Key.ne_sym(k1, k2)(hk), Crits.Dict.entries(V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1)))(Book.dict_agrees(~V, Crits.Dict.set(~V, Crits.Dict.set(~V, d, k2, v2), k1, v1)))
    )

# puts under keys that are not one key can be taken in either order
def Book.iput_comm(+d: Crits.Dict(Name), m1: Maybe<&2, List<&2, U32>>, +n1: Name, m2: Maybe<&2, List<&2, U32>>, +n2: Name) -> (@k: List<&2, U32> -> {m1 == Some{k}: Maybe<&2, List<&2, U32>>} -> {m2 == Some{k}: Maybe<&2, List<&2, U32>>} -> Empty) -> {
  Index.put(Index.put(d, m1, n1), m2, n2) == Index.put(Index.put(d, m2, n2), m1, n1): Crits.Dict(Name)
}:
  match m1 m2:
    case None{} y:
      dist => {==}
    case Some{+k1} None{}:
      dist => {==}
    case Some{+k1} Some{+k2}:
      dist =>
        Book.by({Crits.Dict.set(~Name, Crits.Dict.set(~Name, d, k1, n1), k2, n2) == Crits.Dict.set(~Name, Crits.Dict.set(~Name, d, k2, n2), k1, n1): Crits.Dict(Name)}, Crits.Key.is_eq(k1, k2))(
          t => Empty.absurd({Crits.Dict.set(~Name, Crits.Dict.set(~Name, d, k1, n1), k2, n2) == Crits.Dict.set(~Name, Crits.Dict.set(~Name, d, k2, n2), k1, n1): Crits.Dict(Name)}, dist(k1)({==})(Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, z => Some{z}, k2, k1, Equal.sym(List<&2, U32>, k1, k2, Crits.Key.is_eq_sound(k1, k2)(t)))))
        )(f => Book.set_comm(~Name, d, k1, n1, k2, n2)(f))

# names that differ differ the other way
def Book.name_ne_sym(+a: Name, +b: Name) -> {Name.is_eq(a, b) == False{}: Bool} -> {Name.is_eq(b, a) == False{}: Bool}:
  +h =>
    Book.by({Name.is_eq(b, a) == False{}: Bool}, Name.is_eq(b, a))(
      t =>
        Empty.absurd(
          {Name.is_eq(b, a) == False{}: Bool},
          Shared.Bool.true_ne_false(
            Equal.trans(Bool, True{}, Name.is_eq(a, a), False{}, Equal.sym(Bool, Name.is_eq(a, a), True{}, Name.is_eq_refl(a)), Equal.trans(Bool, Name.is_eq(a, a), Name.is_eq(a, b), False{}, Equal.cong(Name, Bool, z => Name.is_eq(a, z), a, b, Equal.sym(Name, b, a, Name.is_eq_sound(b, a)(t))), h))
          )
        )
    )(f => f)

# names that differ have keys that differ
def Book.key_ne(+m: Name, +n: Name) -> {Name.is_eq(m, n) == False{}: Bool} -> {Crits.Key.is_eq(Name.key(m), Name.key(n)) == False{}: Bool}:
  +h =>
    Book.by({Crits.Key.is_eq(Name.key(m), Name.key(n)) == False{}: Bool}, Crits.Key.is_eq(Name.key(m), Name.key(n)))(
      t =>
        Empty.absurd(
          {Crits.Key.is_eq(Name.key(m), Name.key(n)) == False{}: Bool},
          Shared.Bool.true_ne_false(
            Equal.trans(Bool, True{}, Name.is_eq(m, m), False{}, Equal.sym(Bool, Name.is_eq(m, m), True{}, Name.is_eq_refl(m)), Equal.trans(Bool, Name.is_eq(m, m), Name.is_eq(m, n), False{}, Equal.cong(Name, Bool, z => Name.is_eq(m, z), m, n, Name.key_inj(m, n)(Crits.Key.is_eq_sound(Name.key(m), Name.key(n))(t))), h))
          )
        )
    )(f => f)

# puts of two entries of names that differ can be taken in either order
def Book.put_comm(~Q: Data, ~c: Codes.Codec(Q), b: Book<Q>, +x: Entry<Q>, +y: Entry<Q>) -> {Name.is_eq(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y)) == False{}: Bool} -> {
  Book.put(~Q, Book.put(~Q, b, x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x))), y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y))) == Book.put(~Q, Book.put(~Q, b, y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y))), x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x))): Book<Q>
}:
  match b:
    case Book{+es, +bs, +rs, +hs, +ls, +as, +fs}:
      +hne =>
        +hk = Book.key_ne(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y))(hne)
        %Equal.sym(Crits.Dict(Entry<Q>), Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, x)), x), Name.key(Entry.name(~Q, ~c, y)), y), Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Book.set_comm(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, x)), x, Name.key(Entry.name(~Q, ~c, y)), y)(hk)): {Book{_, Index.put(Index.put(bs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Book.iput_comm(bs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 0n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), _, Index.put(Index.put(rs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Book.iput_comm(rs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 1n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), _, Index.put(Index.put(hs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Book.iput_comm(hs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 2n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), _, Index.put(Index.put(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Book.iput_comm(ls, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 3n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), _, Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Book.iput_comm(as, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 4n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), _, Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        %Equal.sym(Crits.Dict(Name), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x)), Book.iput_comm(fs, Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x), Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y))(k => h1 => h2 => Book.key_apart(Name.key(Entry.name(~Q, ~c, y)), Name.key(Entry.name(~Q, ~c, x)))(Crits.Key.ne_sym(Name.key(Entry.name(~Q, ~c, x)), Name.key(Entry.name(~Q, ~c, y)))(hk))(Book.keys_one(Q, 5n, x, Entry.name(~Q, ~c, x), y, Entry.name(~Q, ~c, y), k)(h1)(h2)))): {Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), _} == Book{Crits.Dict.set(~Entry<Q>, Crits.Dict.set(~Entry<Q>, es, Name.key(Entry.name(~Q, ~c, y)), y), Name.key(Entry.name(~Q, ~c, x)), x), Index.put(Index.put(bs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 0n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 0n), Entry.name(~Q, ~c, x)), Index.put(Index.put(rs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 1n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 1n), Entry.name(~Q, ~c, x)), Index.put(Index.put(hs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 2n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 2n), Entry.name(~Q, ~c, x)), Index.put(Index.put(ls, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 3n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 3n), Entry.name(~Q, ~c, x)), Index.put(Index.put(as, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 4n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 4n), Entry.name(~Q, ~c, x)), Index.put(Index.put(fs, Keys.at(Entry.keys(Q, y, Entry.name(~Q, ~c, y)), 5n), Entry.name(~Q, ~c, y)), Keys.at(Entry.keys(Q, x, Entry.name(~Q, ~c, x)), 5n), Entry.name(~Q, ~c, x))}: Book<Q>}
        {==}

# Book.add_comm once it is known whether the book holds each name (sa, sy)
def Book.add_comm.at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +x: Entry<Q>, +y: Entry<Q>, sa: Bool, sy: Bool) -> {Name.is_eq(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y)) == False{}: Bool} -> {
  Shared.Bool.when(Book<Q>, sy, u => Shared.Bool.when(Book<Q>, sa, u => b, u => Book.put(~Q, b, x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x)))), u => Book.put(~Q, Shared.Bool.when(Book<Q>, sa, u => b, u => Book.put(~Q, b, x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x)))), y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y)))) == Shared.Bool.when(Book<Q>, sa, u => Shared.Bool.when(Book<Q>, sy, u => b, u => Book.put(~Q, b, y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y)))), u => Book.put(~Q, Shared.Bool.when(Book<Q>, sy, u => b, u => Book.put(~Q, b, y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y)))), x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x)))): Book<Q>
}:
  match sa sy:
    case True{} True{}:
      h => {==}
    case True{} False{}:
      h => {==}
    case False{} True{}:
      h => {==}
    case False{} False{}:
      h => Book.put_comm(~Q, ~c, b, x, y)(h)

# an add keeps what a book holds under another name
def Book.get_add_other(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +x: Entry<Q>, +n: Name) -> {Name.is_eq(Entry.name(~Q, ~c, x), n) == False{}: Bool} -> {
  Book.get(Q, Book.add(~Q, ~c, b, x), n) == Book.get(Q, b, n): Maybe<&2, Entry<Q>>
}:
  h =>
    Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, Book.add(~Q, ~c, b, x), n), Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, x), n), u => Some{x})), Book.get(Q, b, n), Book.get_add(~Q, ~c, b, x, n), Equal.trans(Maybe<&2, Entry<Q>>, Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, x), n), u => Some{x})), Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), None{}), Book.get(Q, b, n), Equal.cong(Bool, Maybe<&2, Entry<Q>>, z => Maybe.or(&2, Entry<Q>, Book.get(Q, b, n), Shared.Maybe.when(Entry<Q>, z, u => Some{x})), Name.is_eq(Entry.name(~Q, ~c, x), n), False{}, h), Shared.Maybe.or_none(Entry<Q>, Book.get(Q, b, n))))

# adds of two entries that do not clash can be taken in either order
def Book.add_comm(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +x: Entry<Q>, +y: Entry<Q>) -> Entry.Agrees(~Q, ~c, x, y) -> {Book.add(~Q, ~c, Book.add(~Q, ~c, b, x), y) == Book.add(~Q, ~c, Book.add(~Q, ~c, b, y), x): Book<Q>}:
  hag =>
    Book.by({Book.add(~Q, ~c, Book.add(~Q, ~c, b, x), y) == Book.add(~Q, ~c, Book.add(~Q, ~c, b, y), x): Book<Q>}, Name.is_eq(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y)))(
      t =>
        %hag(Name.is_eq_sound(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y))(t)): {Book.add(~Q, ~c, Book.add(~Q, ~c, b, x), _) == Book.add(~Q, ~c, Book.add(~Q, ~c, b, _), x): Book<Q>}
        {==}
    )(
      +f =>
        %Equal.sym(Bool, Maybe.is_some(&2, Entry<Q>, Book.get(Q, Book.add(~Q, ~c, b, x), Entry.name(~Q, ~c, y))), Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, y))), Equal.cong(Maybe<&2, Entry<Q>>, Bool, z => Maybe.is_some(&2, Entry<Q>, z), Book.get(Q, Book.add(~Q, ~c, b, x), Entry.name(~Q, ~c, y)), Book.get(Q, b, Entry.name(~Q, ~c, y)), Book.get_add_other(~Q, ~c, b, x, Entry.name(~Q, ~c, y))(f))): {
          Shared.Bool.when(Book<Q>, _, u => Book.add(~Q, ~c, b, x), u => Book.put(~Q, Book.add(~Q, ~c, b, x), y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y)))) == Book.add(~Q, ~c, Book.add(~Q, ~c, b, y), x): Book<Q>
        }
        %Equal.sym(Bool, Maybe.is_some(&2, Entry<Q>, Book.get(Q, Book.add(~Q, ~c, b, y), Entry.name(~Q, ~c, x))), Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, x))), Equal.cong(Maybe<&2, Entry<Q>>, Bool, z => Maybe.is_some(&2, Entry<Q>, z), Book.get(Q, Book.add(~Q, ~c, b, y), Entry.name(~Q, ~c, x)), Book.get(Q, b, Entry.name(~Q, ~c, x)), Book.get_add_other(~Q, ~c, b, y, Entry.name(~Q, ~c, x))(Book.name_ne_sym(Entry.name(~Q, ~c, x), Entry.name(~Q, ~c, y))(f)))): {
          Shared.Bool.when(Book<Q>, Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, y))), u => Book.add(~Q, ~c, b, x), u => Book.put(~Q, Book.add(~Q, ~c, b, x), y, Entry.name(~Q, ~c, y), Entry.keys(Q, y, Entry.name(~Q, ~c, y)))) == Shared.Bool.when(Book<Q>, _, u => Book.add(~Q, ~c, b, y), u => Book.put(~Q, Book.add(~Q, ~c, b, y), x, Entry.name(~Q, ~c, x), Entry.keys(Q, x, Entry.name(~Q, ~c, x)))): Book<Q>
        }
        Book.add_comm.at(~Q, ~c, b, x, y, Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, x))), Maybe.is_some(&2, Entry<Q>, Book.get(Q, b, Entry.name(~Q, ~c, y))))(f)
    )

# Book.law.add_comm of the book l
def Book.law.add_comm.at(~Q: Data, ~c: Codes.Codec(Q), l: Book.L(~Q, ~c), +x: Entry<Q>, +y: Entry<Q>) -> Entry.Agrees(~Q, ~c, x, y) -> {
  Book.L.add(~Q, ~c, Book.L.add(~Q, ~c, l, x), y) == Book.L.add(~Q, ~c, Book.L.add(~Q, ~c, l, y), x): Book.L(~Q, ~c)
}:
  match l:
    case Tuple{+b, +w}:
      hag =>
        Book.L.eq(~Q, ~c, Book.add(~Q, ~c, Book.add(~Q, ~c, b, x), y), Book.add(~Q, ~c, Book.add(~Q, ~c, b, y), x), Book.add_comm(~Q, ~c, b, x, y)(hag))(
          Book.ok_add(~Q, ~c, Book.add(~Q, ~c, b, x), y)(Book.ok_add(~Q, ~c, b, x)(w))
        )(Book.ok_add(~Q, ~c, Book.add(~Q, ~c, b, y), x)(Book.ok_add(~Q, ~c, b, y)(w)))

# two codes that are the same words are of the same value
def Book.code_value(~A: Data, ~c: Codes.Codec(A), +a: A, +b: A, +r: List<&2, U32>, +s: List<&2, U32>) -> {Codes.Codec.enc(A, c)(a)(r) == Codes.Codec.enc(A, c)(b)(s): List<&2, U32>} -> {a == b: A}:
  e =>
    Equal.trans(
      A,
      a,
      Codes.Code.read_value(A, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(b)(s)), a),
      b,
      (
        %e: {a == Codes.Code.read_value(A, Codes.Codec.dec(A, c)(_), a): A}
        %Equal.sym(Maybe<&2, Codes.Read<A>>, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(a)(r)), Some{Codes.Read{a, r}}, Codes.Codec.laws(A, c)(a)(r)): {a == Codes.Code.read_value(A, _, a): A}
        {==}
      ),
      (
        %Equal.sym(Maybe<&2, Codes.Read<A>>, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(b)(s)), Some{Codes.Read{b, s}}, Codes.Codec.laws(A, c)(b)(s)): {Codes.Code.read_value(A, _, a) == b: A}
        {==}
      )
    )

# two codes that are the same words are followed by the same words
def Book.code_rest(~A: Data, ~c: Codes.Codec(A), +a: A, +b: A, +r: List<&2, U32>, +s: List<&2, U32>) -> {Codes.Codec.enc(A, c)(a)(r) == Codes.Codec.enc(A, c)(b)(s): List<&2, U32>} -> {r == s: List<&2, U32>}:
  e =>
    Equal.trans(
      List<&2, U32>,
      r,
      Codes.Code.read_value(List<&2, U32>, Codes.Read.then(A, List<&2, U32>, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(b)(s)), x => q => Some{Codes.Read{q, []}}), []),
      s,
      (
        %e: {r == Codes.Code.read_value(List<&2, U32>, Codes.Read.then(A, List<&2, U32>, Codes.Codec.dec(A, c)(_), x => q => Some{Codes.Read{q, []}}), []): List<&2, U32>}
        %Equal.sym(Maybe<&2, Codes.Read<A>>, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(a)(r)), Some{Codes.Read{a, r}}, Codes.Codec.laws(A, c)(a)(r)): {r == Codes.Code.read_value(List<&2, U32>, Codes.Read.then(A, List<&2, U32>, _, x => q => Some{Codes.Read{q, []}}), []): List<&2, U32>}
        {==}
      ),
      (
        %Equal.sym(Maybe<&2, Codes.Read<A>>, Codes.Codec.dec(A, c)(Codes.Codec.enc(A, c)(b)(s)), Some{Codes.Read{b, s}}, Codes.Codec.laws(A, c)(b)(s)): {Codes.Code.read_value(List<&2, U32>, Codes.Read.then(A, List<&2, U32>, _, x => q => Some{Codes.Read{q, []}}), []) == s: List<&2, U32>}
        {==}
      )
    )

# the characters of t before x then r
def Book.chars_append(t: String, +x: List<&2, U32>, +r: List<&2, U32>) -> {Codes.Code.chars(t, List.append(&2, U32, x, r)) == List.append(&2, U32, Codes.Code.chars(t, x), r): List<&2, U32>}:
  match t:
    case SNil{}:
      {==}
    case SCon{Chr{+w}, rest}:
      %Equal.sym(List<&2, U32>, Codes.Code.chars(rest, List.append(&2, U32, x, r)), List.append(&2, U32, Codes.Code.chars(rest, x), r), Book.chars_append(rest, x, r)): {w <> _ == w <> List.append(&2, U32, Codes.Code.chars(rest, x), r): List<&2, U32>}
      {==}

# the text t before x then r
def Book.text_append(+t: String, +x: List<&2, U32>, +r: List<&2, U32>) -> {Codes.Code.text(t, List.append(&2, U32, x, r)) == List.append(&2, U32, Codes.Code.text(t, x), r): List<&2, U32>}:
  %Equal.sym(List<&2, U32>, Codes.Code.chars(t, List.append(&2, U32, x, r)), List.append(&2, U32, Codes.Code.chars(t, x), r), Book.chars_append(t, x, r)): {
    Codes.Code.count(Codes.Code.length(t), _) == List.append(&2, U32, Codes.Code.text(t, x), r): List<&2, U32>
  }
  Equal.sym(List<&2, U32>, List.append(&2, U32, Codes.Code.count.go(Codes.Code.length(t), 0, Codes.Code.chars(t, x)), r), Codes.Code.count.go(Codes.Code.length(t), 0, List.append(&2, U32, Codes.Code.chars(t, x), r)), Codes.Code.count_append(Codes.Code.length(t), 0, Codes.Code.chars(t, x), r))

# the name of a sub line before x then r
def Book.sub_append(k: Maybe<&2, String>, +x: List<&2, U32>, +r: List<&2, U32>) -> {Codes.Code.maybe(~String, ~Codes.Code.text, k, List.append(&2, U32, x, r)) == List.append(&2, U32, Codes.Code.maybe(~String, ~Codes.Code.text, k, x), r): List<&2, U32>}:
  match k:
    case None{}:
      {==}
    case Some{+t}:
      %Equal.sym(List<&2, U32>, Codes.Code.text(t, List.append(&2, U32, x, r)), List.append(&2, U32, Codes.Code.text(t, x), r), Book.text_append(t, x, r)): {1 <> _ == 1 <> List.append(&2, U32, Codes.Code.text(t, x), r): List<&2, U32>}
      {==}

# the line c before x then r
def Book.line_append(c: Line, +x: List<&2, U32>, +r: List<&2, U32>) -> {Line.code(c, List.append(&2, U32, x, r)) == List.append(&2, U32, Line.code(c, x), r): List<&2, U32>}:
  match c:
    case Line{Hashes.Hash{+i0, +i1, +i2, +i3, +i4, +i5, +i6, +i7}, +k}:
      %Equal.sym(List<&2, U32>, Codes.Code.maybe(~String, ~Codes.Code.text, k, List.append(&2, U32, x, r)), List.append(&2, U32, Codes.Code.maybe(~String, ~Codes.Code.text, k, x), r), Book.sub_append(k, x, r)): {
        Hashes.Hash.code(Hashes.Hash{i0, i1, i2, i3, i4, i5, i6, i7}, _) == List.append(&2, U32, Hashes.Hash.code(Hashes.Hash{i0, i1, i2, i3, i4, i5, i6, i7}, Codes.Code.maybe(~String, ~Codes.Code.text, k, x)), r): List<&2, U32>
      }
      {==}

# the place w before x then r
def Book.place_append(w: Place, +x: List<&2, U32>, +r: List<&2, U32>) -> {Place.code(w, List.append(&2, U32, x, r)) == List.append(&2, U32, Place.code(w, x), r): List<&2, U32>}:
  match w:
    case Place{+l, +h, +k}:
      %Codes.Code.count_append(k, 0, x, r): {
        Line.code(l, h <> _) == List.append(&2, U32, Line.code(l, h <> Codes.Code.count(k, x)), r): List<&2, U32>
      }
      Book.line_append(l, h <> Codes.Code.count(k, x), r)

# the hash h before x then r
def Book.hash_append(h: Hashes.Hash, -x: List<&2, U32>, -r: List<&2, U32>) -> {Hashes.Hash.code(h, List.append(&2, U32, x, r)) == List.append(&2, U32, Hashes.Hash.code(h, x), r): List<&2, U32>}:
  match h:
    case Hashes.Hash{i0, i1, i2, i3, i4, i5, i6, i7}:
      {==}

# a key that starts with p is p then the rest of the key
def Book.starts_split(+p: List<&2, U32>, +k: List<&2, U32>) -> {Crits.Key.starts(p, k) == True{}: Bool} -> {k == List.append(&2, U32, p, List.drop(&2, U32, k, List.length(&2, U32, p))): List<&2, U32>}:
  match p k:
    case Nil{} y:
      h => Equal.sym(List<&2, U32>, List.drop(&2, U32, y, 0n), y, Shared.List.drop_zero(&2, U32, y))
    case Con{x, rp} Nil{}:
      h => Empty.absurd({[] == List.append(&2, U32, x <> rp, List.drop(&2, U32, [], List.length(&2, U32, x <> rp))): List<&2, U32>}, Shared.Bool.false_ne_true(h))
    case Con{+x, +rp} Con{+y, +rk}:
      +h =>
        %Shared.U32.is_eq_sound(x, y)(Shared.Bool.and_true_left(U32.is_eq(x, y), Crits.Key.starts(rp, rk))(h)): {
          _ <> rk == x <> List.append(&2, U32, rp, List.drop(&2, U32, rk, List.length(&2, U32, rp))): List<&2, U32>
        }
        %Equal.sym(List<&2, U32>, rk, List.append(&2, U32, rp, List.drop(&2, U32, rk, List.length(&2, U32, rp))), Book.starts_split(rp, rk)(Shared.Bool.and_true_right(U32.is_eq(x, y), Crits.Key.starts(rp, rk))(h))): {
          x <> _ == x <> List.append(&2, U32, rp, List.drop(&2, U32, rk, List.length(&2, U32, rp))): List<&2, U32>
        }
        {==}

# p then r starts with p
def Book.starts_append(+p: List<&2, U32>, +r: List<&2, U32>) -> {Crits.Key.starts(p, List.append(&2, U32, p, r)) == True{}: Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{+x, +rest}:
      %Equal.sym(Bool, U32.is_eq(x, x), True{}, Shared.U32.is_eq_refl(x)): {Bool.and(_, Crits.Key.starts(rest, List.append(&2, U32, rest, r))) == True{}: Bool}
      Book.starts_append(rest, r)

# the map of a dict is well formed
def Book.dict_wf(~V: Data, d: Crits.Dict(V)) -> {Crits.Crit.wf(~V, Crits.Dict.crit(V, d), 0n) == True{}: Bool}:
  match d:
    case Tuple{m, w}:
      w

# a key of the part of the index d under p starts with p, and the index holds it
def Book.under_key(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name) -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>} -> {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}:
  +hl =>
    +hp = Equal.trans(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), Some{x}, Equal.sym(Maybe<&2, Name>, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Crits.Crit.under_lookup(~Name, Crits.Dict.crit(Name, d), p, k)(Book.dict_wf(~Name, d))), hl)
    Book.by({Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}, Crits.Key.starts(p, k))(
      +t => (t, Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, d, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Some{x}, Crits.Crit.get_lookup(~Name, Crits.Dict.crit(Name, d), k)(Book.dict_wf(~Name, d)), Equal.trans(Maybe<&2, Name>, Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Book.pick_true(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{})(t)), hp)))
    )(
      +f => Empty.absurd({Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}, Shared.Maybe.none_ne_some(Name, x, Equal.trans(Maybe<&2, Name>, None{}, Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Some{x}, Equal.sym(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), None{}, Book.pick_false(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{})(f)), hp)))
    )

# a key of the index d that starts with p is a key of the part under p
def Book.under_lookup_of(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name) -> {Crits.Key.starts(p, k) == True{}: Bool} -> {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>} -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>}:
  hs => hg =>
    Equal.trans(Maybe<&2, Name>, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Some{x}, Crits.Crit.under_lookup(~Name, Crits.Dict.crit(Name, d), p, k)(Book.dict_wf(~Name, d)), Equal.trans(Maybe<&2, Name>, Bool.pick(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{}), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Some{x}, Book.pick_true(Maybe<&2, Name>, Crits.Key.starts(p, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), None{})(hs), Equal.trans(Maybe<&2, Name>, Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Crits.Dict.get(Name, d, k), Some{x}, Equal.sym(Maybe<&2, Name>, Crits.Dict.get(Name, d, k), Crits.Crit.lookup(Name, Crits.Dict.crit(Name, d), k), Crits.Crit.get_lookup(~Name, Crits.Dict.crit(Name, d), k)(Book.dict_wf(~Name, d))), hg)))

# Book.under_sound once the key is found in the index
def Book.under_sound.fin(+d: Crits.Dict(Name), +p: List<&2, U32>, +x: Name, +k: List<&2, U32>, +v: Name, +he: {Name.is_eq(v, x) == True{}: Bool}, pr: {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{v}: Maybe<&2, Name>}) -> Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}):
  match pr:
    case Tuple{+st, +gv}:
      (k, (st, Equal.trans(Maybe<&2, Name>, Crits.Dict.get(Name, d, k), Some{v}, Some{x}, gv, Equal.cong(Name, Maybe<&2, Name>, s => Some{s}, v, x, Name.is_eq_sound(v, x)(he)))))

# Book.under_sound once a key of the part under p is found
def Book.under_sound.of(+d: Crits.Dict(Name), +p: List<&2, U32>, +x: Name, ex: Exists(List<&2, U32>, k => Exists(Name, v => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{v}: Maybe<&2, Name>} & {Name.is_eq(v, x) == True{}: Bool}))) -> Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}):
  match ex:
    case Tuple{+k, Tuple{+v, Tuple{hl, he}}}:
      Book.under_sound.fin(d, p, x, k, v, he, Book.under_key(d, p, k, v)(hl))

# a name under p in the index d is under a key that starts with p
def Book.under_sound(+d: Crits.Dict(Name), +p: List<&2, U32>, +x: Name) -> {List.contains(~Name, ~Name.is_eq, Index.under(d, p), x) == True{}: Bool} -> Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>}):
  h => Book.under_sound.of(d, p, x, Book.vals_sound(~Name, ~Name.is_eq, Crits.Crit.entries(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)), x, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p))(Crits.Crit.sub_to_list(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), [], Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p))(Crits.Crit.sub_self(~Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), 0n)(Crits.Crit.under_wf(~Name, Crits.Dict.crit(Name, d), p)(Book.dict_wf(~Name, d))))(Unit{}))(h))

# a name of the index d under a key that starts with p is under p
def Book.under_complete(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name) -> {Crits.Key.starts(p, k) == True{}: Bool} -> {Crits.Dict.get(Name, d, k) == Some{x}: Maybe<&2, Name>} -> {
  List.contains(~Name, ~Name.is_eq, Index.under(d, p), x) == True{}: Bool
}:
  hs => hg => Book.vals_complete(~Name, ~Name.is_eq, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), [], k, x, x)(Book.under_lookup_of(d, p, k, x)(hs)(hg))(Name.is_eq_refl(x))

# an entry that a maybe then r holds, and the maybe is not, r holds
def Book.cons_rest(~Q: Data, ~c: Codes.Codec(Q), m: Maybe<&2, Entry<Q>>, -r: List<&2, Entry<Q>>, +y: Entry<Q>) -> {
  Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), m, Some{y}) == False{}: Bool
} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Shared.Maybe.cons(Entry<Q>, m, r), y) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y) == True{}: Bool}:
  match m:
    case None{}:
      f => h => h
    case Some{+z}:
      f => h =>
        Equal.trans(Bool, List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y), List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y), Entry.same(~Q, ~c)(z, y)), True{}, Equal.sym(Bool, List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y), Entry.same(~Q, ~c)(z, y)), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y), Equal.cong(Bool, Bool, t => List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y), t), Entry.same(~Q, ~c)(z, y), False{}, f)), h)

# a maybe then r holds what r holds
def Book.cons_mono(~Q: Data, ~c: Codes.Codec(Q), m: Maybe<&2, Entry<Q>>, -r: List<&2, Entry<Q>>, +y: Entry<Q>) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Shared.Maybe.cons(Entry<Q>, m, r), y) == True{}: Bool}:
  match m:
    case None{}:
      h => h
    case Some{+z}:
      h => Book.any_rest(Entry.same(~Q, ~c)(z, y), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), r, y))(h)

# a name of rest is a name of n0 then rest
def Book.named_sound.up(-Q: Data, +b: Book<Q>, +n0: Name, -rest: List<&2, Name>, +y: Entry<Q>, ex: Exists(Name, n => {List.contains(~Name, ~Name.is_eq, rest, n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>})) -> Exists(Name, n => {List.contains(~Name, ~Name.is_eq, n0 <> rest, n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>}):
  match ex:
    case Tuple{+n, Tuple{hc, g}}:
      (n, (Book.any_rest(Name.is_eq(n0, n), List.contains(~Name, ~Name.is_eq, rest, n))(hc), g))

# an entry of a book that the names ns name is under one of them
def Book.named_sound(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, ns: List<&2, Name>, +y: Entry<Q>) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, ns), y) == True{}: Bool} -> Exists(Name, n => {List.contains(~Name, ~Name.is_eq, ns, n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>}):
  match ns:
    case Nil{}:
      h => Empty.absurd(Exists(Name, n => {List.contains(~Name, ~Name.is_eq, [], n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>}), Shared.Bool.false_ne_true(h))
    case Con{+n0, +rest}:
      +h =>
        Book.by(Exists(Name, n => {List.contains(~Name, ~Name.is_eq, n0 <> rest, n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>}), Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, n0), Some{y}))(
          +t =>
            (
              n0,
              (
                Book.any_hit(Name.is_eq(n0, n0), u => List.contains(~Name, ~Name.is_eq, rest, n0))(Name.is_eq_refl(n0)),
                Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), x => z => Entry.same_sound(~Q, ~c, x, z), Book.get(Q, b, n0), Some{y})(t)
              )
            )
        )(
          +f =>
            Book.named_sound.up(
              Q,
              b,
              n0,
              rest,
              y,
              Book.named_sound(~Q, ~c, b, rest, y)(Book.cons_rest(~Q, ~c, Book.get(Q, b, n0), Book.named(Q, b, rest), y)(f)(h))
            )
        )

# an entry of a book under one of the names ns is among the entries that ns name
def Book.named_complete(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, ns: List<&2, Name>, +n: Name, +y: Entry<Q>) -> {List.contains(~Name, ~Name.is_eq, ns, n) == True{}: Bool} -> {
  Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>
} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, ns), y) == True{}: Bool}:
  match ns:
    case Nil{}:
      h => g => Empty.absurd({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), [], y) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{+n0, +rest}:
      +h => +g =>
        Book.by({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, n0 <> rest), y) == True{}: Bool}, Name.is_eq(n0, n))(
          +t =>
            %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, b, n0), Some{y}, Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, b, n0), Book.get(Q, b, n), Some{y}, Equal.cong(Name, Maybe<&2, Entry<Q>>, z => Book.get(Q, b, z), n0, n, Name.is_eq_sound(n0, n)(t)), g)): {
              List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Shared.Maybe.cons(Entry<Q>, _, Book.named(Q, b, rest)), y) == True{}: Bool
            }
            Book.any_hit(Entry.same(~Q, ~c)(y, y), u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, rest), y))(Entry.same_refl(~Q, ~c, y))
        )(
          +f =>
            Book.cons_mono(~Q, ~c, Book.get(Q, b, n0), Book.named(Q, b, rest), y)(
              Book.named_complete(~Q, ~c, b, rest, n, y)(
                Equal.trans(Bool, List.contains(~Name, ~Name.is_eq, rest, n), List.any.if(u => List.contains(~Name, ~Name.is_eq, rest, n), Name.is_eq(n0, n)), True{}, Equal.sym(Bool, List.any.if(u => List.contains(~Name, ~Name.is_eq, rest, n), Name.is_eq(n0, n)), List.contains(~Name, ~Name.is_eq, rest, n), Equal.cong(Bool, Bool, t => List.any.if(u => List.contains(~Name, ~Name.is_eq, rest, n), t), Name.is_eq(n0, n), False{}, f)), h)
              )(g)
            )
        )

# a ballot is among the ballots of entries exactly when it is among the entries
def Book.ballots_eq(~Q: Data, ~c: Codes.Codec(Q), es: List<&2, Entry<Q>>, +bl: Ballot) -> {List.contains(~Ballot, ~Ballot.is_eq, Entries.ballots(Q, es), bl) == List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), es, Entry.Ballot{bl}): Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{Entry.Ballot{+x}, +rest}:
      %Equal.sym(Bool, List.contains(~Ballot, ~Ballot.is_eq, Entries.ballots(Q, rest), bl), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Ballot{bl}), Book.ballots_eq(~Q, ~c, rest, bl)): {
        List.any.if(u => _, Ballot.is_eq(x, bl)) == List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Ballot{bl}), Ballot.is_eq(x, bl)): Bool
      }
      {==}
    case Con{Entry.Ask{i, t, q}, +rest}:
      Book.ballots_eq(~Q, ~c, rest, bl)
    case Con{Entry.Data{ws}, +rest}:
      Book.ballots_eq(~Q, ~c, rest, bl)
    case Con{Entry.Lie{y}, +rest}:
      Book.ballots_eq(~Q, ~c, rest, bl)

# the voter of a proof of a lie among entries is among their liars
def Book.liars_complete_list(~Q: Data, ~c: Codes.Codec(Q), es: List<&2, Entry<Q>>, +x: Lie) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), es, Entry.Lie{x}) == True{}: Bool} -> {List.contains(~String, ~String.eq, Entries.liars(Q, es), Ballot.voter(Lie.first(x))) == True{}: Bool}:
  match es:
    case Nil{}:
      h => Empty.absurd({List.contains(~String, ~String.eq, Entries.liars(Q, []), Ballot.voter(Lie.first(x))) == True{}: Bool}, Shared.Bool.false_ne_true(h))
    case Con{Entry.Lie{+y}, +rest}:
      +h =>
        Book.by({List.contains(~String, ~String.eq, Entries.liars(Q, Entry.Lie{y} <> rest), Ballot.voter(Lie.first(x))) == True{}: Bool}, Lie.is_eq(y, x))(
          +t =>
            Book.any_hit(String.eq(Ballot.voter(Lie.first(y)), Ballot.voter(Lie.first(x))), u => List.contains(~String, ~String.eq, Entries.liars(Q, rest), Ballot.voter(Lie.first(x))))(
              %Equal.sym(Lie, y, x, Shared.Eq.sound(~Lie, ~Lie.is_eq, Lie.laws(), y, x)(t)): {String.eq(Ballot.voter(Lie.first(_)), Ballot.voter(Lie.first(x))) == True{}: Bool}
              Texts.String.eq_refl(Ballot.voter(Lie.first(x)))
            )
        )(
          +f =>
            Book.any_rest(String.eq(Ballot.voter(Lie.first(y)), Ballot.voter(Lie.first(x))), List.contains(~String, ~String.eq, Entries.liars(Q, rest), Ballot.voter(Lie.first(x))))(
              Book.liars_complete_list(~Q, ~c, rest, x)(
                Equal.trans(Bool, List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}), List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}), Lie.is_eq(y, x)), True{}, Equal.sym(Bool, List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}), Lie.is_eq(y, x)), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}), Equal.cong(Bool, Bool, t => List.any.if(u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}), t), Lie.is_eq(y, x), False{}, f)), h)
              )
            )
        )
    case Con{Entry.Ask{i, t, q}, +rest}:
      h => Book.liars_complete_list(~Q, ~c, rest, x)(h)
    case Con{Entry.Data{ws}, +rest}:
      h => Book.liars_complete_list(~Q, ~c, rest, x)(h)
    case Con{Entry.Ballot{z}, +rest}:
      h => Book.liars_complete_list(~Q, ~c, rest, x)(h)

# a proof of a lie among rest is among a proof then rest
def Book.liars_sound.up(~Q: Data, ~c: Codes.Codec(Q), +y: Lie, -rest: List<&2, Entry<Q>>, +v: String, ex: Exists(Lie, x => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(x)), v) == True{}: Bool})) -> Exists(Lie, x => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Entry.Lie{y} <> rest, Entry.Lie{x}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(x)), v) == True{}: Bool}):
  match ex:
    case Tuple{+x, Tuple{hc, hs}}:
      (x, (Book.any_rest(Lie.is_eq(y, x), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{x}))(hc), hs))

# a liar of entries is the voter of a proof of a lie among them
def Book.liars_sound_list(~Q: Data, ~c: Codes.Codec(Q), es: List<&2, Entry<Q>>, +v: String) -> {List.contains(~String, ~String.eq, Entries.liars(Q, es), v) == True{}: Bool} -> Exists(Lie, x => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), es, Entry.Lie{x}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(x)), v) == True{}: Bool}):
  match es:
    case Nil{}:
      h => Empty.absurd(Exists(Lie, x => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), [], Entry.Lie{x}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(x)), v) == True{}: Bool}), Shared.Bool.false_ne_true(h))
    case Con{Entry.Lie{+y}, +rest}:
      +h =>
        Book.by(Exists(Lie, x => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Entry.Lie{y} <> rest, Entry.Lie{x}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(x)), v) == True{}: Bool}), String.eq(Ballot.voter(Lie.first(y)), v))(
          +t => (y, (Book.any_hit(Lie.is_eq(y, y), u => List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), rest, Entry.Lie{y}))(Shared.Eq.refl(~Lie, ~Lie.is_eq, Lie.laws(), y)), t))
        )(
          +f =>
            Book.liars_sound.up(
              ~Q,
              ~c,
              y,
              rest,
              v,
              Book.liars_sound_list(~Q, ~c, rest, v)(
                Equal.trans(Bool, List.contains(~String, ~String.eq, Entries.liars(Q, rest), v), List.any.if(u => List.contains(~String, ~String.eq, Entries.liars(Q, rest), v), String.eq(Ballot.voter(Lie.first(y)), v)), True{}, Equal.sym(Bool, List.any.if(u => List.contains(~String, ~String.eq, Entries.liars(Q, rest), v), String.eq(Ballot.voter(Lie.first(y)), v)), List.contains(~String, ~String.eq, Entries.liars(Q, rest), v), Equal.cong(Bool, Bool, t => List.any.if(u => List.contains(~String, ~String.eq, Entries.liars(Q, rest), v), t), String.eq(Ballot.voter(Lie.first(y)), v), False{}, f)), h)
              )
            )
        )
    case Con{Entry.Ask{i, t, q}, +rest}:
      h => Book.liars_sound_list(~Q, ~c, rest, v)(h)
    case Con{Entry.Data{ws}, +rest}:
      h => Book.liars_sound_list(~Q, ~c, rest, v)(h)
    case Con{Entry.Ballot{z}, +rest}:
      h => Book.liars_sound_list(~Q, ~c, rest, v)(h)

# a book that indexes n under the keys ks indexes it in each index
def Book.indexed_at(-Q: Data, b: Book<Q>, ks: Keys, +n: Name, i: Nat) -> {Book.indexed(Q, b, ks, n) == True{}: Bool} -> {
  Index.holds(Book.index(Q, b, i), Keys.at(ks, i), n) == True{}: Bool
}:
  match b ks:
    case Book{es, +bs, +rs, +hs, +ls, +as, +fs} Keys{+kb, +kr, +kh, +kl, +ka, +kf}:
      match i:
        case 0n:
          +h => Shared.Bool.and_true_left(Index.holds(bs, kb, n), Index.holds(rs, kr, n))(Shared.Bool.and_true_left(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h))
        case 1n+i1:
          match i1:
            case 0n:
              +h => Shared.Bool.and_true_right(Index.holds(bs, kb, n), Index.holds(rs, kr, n))(Shared.Bool.and_true_left(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h))
            case 1n+i2:
              match i2:
                case 0n:
                  +h => Shared.Bool.and_true_left(Index.holds(hs, kh, n), Index.holds(ls, kl, n))(Shared.Bool.and_true_left(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n)))(Shared.Bool.and_true_right(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h)))
                case 1n+i3:
                  match i3:
                    case 0n:
                      +h => Shared.Bool.and_true_right(Index.holds(hs, kh, n), Index.holds(ls, kl, n))(Shared.Bool.and_true_left(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n)))(Shared.Bool.and_true_right(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h)))
                    case 1n+i4:
                      match i4:
                        case 0n:
                          +h => Shared.Bool.and_true_left(Index.holds(as, ka, n), Index.holds(fs, kf, n))(Shared.Bool.and_true_right(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n)))(Shared.Bool.and_true_right(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h)))
                        case 1n+p:
                          +h => Shared.Bool.and_true_right(Index.holds(as, ka, n), Index.holds(fs, kf, n))(Shared.Bool.and_true_right(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n)))(Shared.Bool.and_true_right(Bool.and(Index.holds(bs, kb, n), Index.holds(rs, kr, n)), Bool.and(Bool.and(Index.holds(hs, kh, n), Index.holds(ls, kl, n)), Bool.and(Index.holds(as, ka, n), Index.holds(fs, kf, n))))(h)))

# Sub.is_eq is True for a sub line and itself
def Sub.is_eq_refl(k: Maybe<&2, String>) -> {Sub.is_eq(k, k) == True{}: Bool}:
  match k:
    case None{}:
      {==}
    case Some{+t}:
      Texts.String.eq_refl(t)

# Sub.is_eq is True only for equal sub lines
def Sub.is_eq_sound(a: Maybe<&2, String>, b: Maybe<&2, String>) -> {Sub.is_eq(a, b) == True{}: Bool} -> {a == b: Maybe<&2, String>}:
  Shared.Maybe.is_eq_sound(~String, ~String.eq, x => y => Texts.String.eq_sound(x, y), a, b)

# Line.is_eq is True for a line and itself
def Line.is_eq_refl(c: Line) -> {Line.is_eq(c, c) == True{}: Bool}:
  match c:
    case Line{+i, +k}:
      Shared.List.all.if_both(Hashes.Hash.is_eq(i, i), u => Sub.is_eq(k, k))(Hashes.Hash.is_eq_refl(i))(Sub.is_eq_refl(k))

# Line.is_eq is True only for equal lines
def Line.is_eq_sound(a: Line, b: Line) -> {Line.is_eq(a, b) == True{}: Bool} -> {a == b: Line}:
  match a b:
    case Line{+i1, +k1} Line{+i2, +k2}:
      +h =>
        %Hashes.Hash.is_eq_sound(i1, i2)(Shared.List.all.if_hit(Hashes.Hash.is_eq(i1, i2), u => Sub.is_eq(k1, k2))(h)): {Line{i1, k1} == Line{_, k2}: Line}
        %Sub.is_eq_sound(k1, k2)(Shared.List.all.if_rest(Hashes.Hash.is_eq(i1, i2), u => Sub.is_eq(k1, k2))(h)): {Line{i1, k1} == Line{i1, _}: Line}
        {==}

# Place.is_eq is True for a place and itself
def Place.is_eq_refl(w: Place) -> {Place.is_eq(w, w) == True{}: Bool}:
  match w:
    case Place{+c, +h, +r}:
      Shared.List.all.if_both(Line.is_eq(c, c), u => List.all.if(u2 => Nat.is_eq(r, r), U32.is_eq(h, h)))(Line.is_eq_refl(c))(
        Shared.List.all.if_both(U32.is_eq(h, h), u2 => Nat.is_eq(r, r))(Shared.U32.is_eq_refl(h))(Shared.Nat.is_eq_refl(r))
      )

# Place.is_eq is True only for equal places
def Place.is_eq_sound(a: Place, b: Place) -> {Place.is_eq(a, b) == True{}: Bool} -> {a == b: Place}:
  match a b:
    case Place{+c1, +h1, +r1} Place{+c2, +h2, +r2}:
      +h =>
        +hr = Shared.List.all.if_rest(Line.is_eq(c1, c2), u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2)))(h)
        %Line.is_eq_sound(c1, c2)(Shared.List.all.if_hit(Line.is_eq(c1, c2), u => List.all.if(u2 => Nat.is_eq(r1, r2), U32.is_eq(h1, h2)))(h)): {
          Place{c1, h1, r1} == Place{_, h2, r2}: Place
        }
        %Shared.U32.is_eq_sound(h1, h2)(Shared.List.all.if_hit(U32.is_eq(h1, h2), u2 => Nat.is_eq(r1, r2))(hr)): {Place{c1, h1, r1} == Place{c1, _, r2}: Place}
        %Shared.Nat.is_eq_sound(r1, r2)(Shared.List.all.if_rest(U32.is_eq(h1, h2), u2 => Nat.is_eq(r1, r2))(hr)): {Place{c1, h1, r1} == Place{c1, h1, _}: Place}
        {==}

# a book in its one shape holds what it gives under a name
def Book.has_of(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +n: Name, +y: Entry<Q>) -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, y)), Some{y}) == True{}: Bool}:
  +g =>
    %Equal.sym(Name, Entry.name(~Q, ~c, y), n, Book.get_named(~Q, ~c, b, n, y)(wk)(g)): {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, _), Some{y}) == True{}: Bool}
    %Equal.sym(Maybe<&2, Entry<Q>>, Book.get(Q, b, n), Some{y}, g): {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), _, Some{y}) == True{}: Bool}
    Entry.same_refl(~Q, ~c, y)

# Book.under_named_sound once the key of the name is found
def Book.under_named.of2(-Q: Data, +b: Book<Q>, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +p: List<&2, U32>, +y: Entry<Q>, +n: Name, +g: {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>}, ex: Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & {Crits.Dict.get(Name, Book.index(Q, b, i), k) == Some{n}: Maybe<&2, Name>})) -> Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, n), i) == Some{k}: Maybe<&2, List<&2, U32>>}))):
  match ex:
    case Tuple{+k, Tuple{+hs, +hk}}:
      +hd = Book.ok.index_get(Q, b, i, Book.index(Q, b, i), k, n)(ho)(hk)
      +hd2 = Equal.trans(Bool, Book.ok.key(Q, Some{y}, i, k, n), Book.ok.key(Q, Book.get(Q, b, n), i, k, n), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, n), i, k, n), Book.ok.key(Q, Some{y}, i, k, n), Equal.cong(Maybe<&2, Entry<Q>>, Bool, t => Book.ok.key(Q, t, i, k, n), Book.get(Q, b, n), Some{y}, g)), hd)
      (
        n,
        (
          k,
          (
            hs,
            (g, Shared.Maybe.is_eq_sound(~List<&2, U32>, ~Crits.Key.is_eq, s1 => s2 => Crits.Key.is_eq_sound(s1, s2), Keys.at(Entry.keys(Q, y, n), i), Some{k})(hd2))
          )
        )
      )

# Book.under_named_sound once the name is found
def Book.under_named.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +p: List<&2, U32>, +y: Entry<Q>, ex: Exists(Name, n => {List.contains(~Name, ~Name.is_eq, Index.under(Book.index(Q, b, i), p), n) == True{}: Bool} & {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>})) -> Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, n), i) == Some{k}: Maybe<&2, List<&2, U32>>}))):
  match ex:
    case Tuple{+n, Tuple{+hc, +g}}:
      Book.under_named.of2(Q, b, i, ho, p, y, n, g, Book.under_sound(Book.index(Q, b, i), p, n)(hc))

# an entry that the names under p in the index i name is under a name with a key there that starts with p
def Book.under_named_sound(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +p: List<&2, U32>, +y: Entry<Q>) -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, i), p)), y) == True{}: Bool} -> Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(p, k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, n), i) == Some{k}: Maybe<&2, List<&2, U32>>}))):
  h => Book.under_named.of1(~Q, ~c, b, i, ho, p, y, Book.named_sound(~Q, ~c, b, Index.under(Book.index(Q, b, i), p), y)(h))

# the index i of a book in its one shape holds the name of each entry under its key there
def Book.index_has(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +i: Nat, +n: Name, +y: Entry<Q>, +k: List<&2, U32>) -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {
  Keys.at(Entry.keys(Q, y, n), i) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {Crits.Dict.get(Name, Book.index(Q, b, i), k) == Some{n}: Maybe<&2, Name>}:
  +g => +hk =>
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), Name.key(n), y)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk))(g)
    +en = Name.key_inj(Entry.name(~Q, ~c, y), n)(Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, y)), Name.key(n))(Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, y)), Name.key(n)), Book.indexed(Q, b, Entry.keys(Q, y, Entry.name(~Q, ~c, y)), Entry.name(~Q, ~c, y)))(hc)))
    +hi = Equal.trans(Bool, Book.indexed(Q, b, Entry.keys(Q, y, n), n), Book.indexed(Q, b, Entry.keys(Q, y, Entry.name(~Q, ~c, y)), Entry.name(~Q, ~c, y)), True{}, Equal.sym(Bool, Book.indexed(Q, b, Entry.keys(Q, y, Entry.name(~Q, ~c, y)), Entry.name(~Q, ~c, y)), Book.indexed(Q, b, Entry.keys(Q, y, n), n), Equal.cong(Name, Bool, +t => Book.indexed(Q, b, Entry.keys(Q, y, t), t), Entry.name(~Q, ~c, y), n, en)), Shared.Bool.and_true_right(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, y)), Name.key(n)), Book.indexed(Q, b, Entry.keys(Q, y, Entry.name(~Q, ~c, y)), Entry.name(~Q, ~c, y)))(hc))
    +hh = Book.indexed_at(Q, b, Entry.keys(Q, y, n), n, i)(hi)
    Shared.Maybe.is_eq_sound(~Name, ~Name.is_eq, s1 => s2 => Name.is_eq_sound(s1, s2), Crits.Dict.get(Name, Book.index(Q, b, i), k), Some{n})(
      Equal.trans(Bool, Index.holds(Book.index(Q, b, i), Some{k}, n), Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, y, n), i), n), True{}, Equal.sym(Bool, Index.holds(Book.index(Q, b, i), Keys.at(Entry.keys(Q, y, n), i), n), Index.holds(Book.index(Q, b, i), Some{k}, n), Equal.cong(Maybe<&2, List<&2, U32>>, Bool, t => Index.holds(Book.index(Q, b, i), t, n), Keys.at(Entry.keys(Q, y, n), i), Some{k}, hk)), hh)
    )

# an entry of a book with a key in the index i that starts with p is among the entries that the names under p name
def Book.under_named_complete(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +i: Nat, +p: List<&2, U32>, +n: Name, +y: Entry<Q>, +k: List<&2, U32>) -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {
  Keys.at(Entry.keys(Q, y, n), i) == Some{k}: Maybe<&2, List<&2, U32>>
} -> {Crits.Key.starts(p, k) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, i), p)), y) == True{}: Bool}:
  +g => hk => hs =>
    Book.named_complete(~Q, ~c, b, Index.under(Book.index(Q, b, i), p), n, y)(
      Book.under_complete(Book.index(Q, b, i), p, k, n)(hs)(Book.index_has(~Q, ~c, b, wk, i, n, y, k)(g)(hk))
    )(g)

# Book.law.ballots.sound once the name and the key are found
def Book.law.ballots.sound.of(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +w: Place, +voter: String, bl: Ballot, +n: Name, +k: List<&2, U32>) -> {Crits.Key.starts(Place.code(w, Codes.Code.text(voter, [])), k) == True{}: Bool} -> {
  Book.get(Q, b, n) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>
} -> {Keys.at(Entry.keys(Q, Entry.Ballot{bl}, n), 0n) == Some{k}: Maybe<&2, List<&2, U32>>} -> {
  Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)) == True{}: Bool
}:
  match bl:
    case Ballot{Signed{Place{+line, +h, +r}, +v, +a}, Link{+pv, +lk, +z}}:
      hs => g => hk =>
        +eq = Equal.trans(List<&2, U32>, Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(n))), k, Place.code(w, Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), Shared.Maybe.some_inj(List<&2, U32>, Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(n))), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Place.code(w, Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), Book.starts_split(Place.code(w, Codes.Code.text(voter, [])), k)(hs), Equal.trans(List<&2, U32>, List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Place.code(w, List.append(&2, U32, Codes.Code.text(voter, []), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), Place.code(w, Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), Equal.sym(List<&2, U32>, Place.code(w, List.append(&2, U32, Codes.Code.text(voter, []), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Book.place_append(w, Codes.Code.text(voter, []), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))), Equal.cong(List<&2, U32>, List<&2, U32>, t => Place.code(w, t), List.append(&2, U32, Codes.Code.text(voter, []), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Equal.sym(List<&2, U32>, Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), List.append(&2, U32, Codes.Code.text(voter, []), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))), Book.text_append(voter, [], List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))))))))
        +ew = Book.code_value(~Place, ~Place.codec(), Place{line, h, r}, w, Codes.Code.text(v, Name.key(n)), Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))))(eq)
        +ev = Book.code_value(~String, ~Codes.Code.text.codec(), v, voter, Name.key(n), List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, [])))))(
          Book.code_rest(~Place, ~Place.codec(), Place{line, h, r}, w, Codes.Code.text(v, Name.key(n)), Codes.Code.text(voter, List.drop(&2, U32, k, List.length(&2, U32, Place.code(w, Codes.Code.text(voter, []))))))(eq)
        )
        %ew: {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Ballot.is_at(Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}, _, voter)) == True{}: Bool}
        %ev: {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Ballot.is_at(Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}, Place{line, h, r}, _)) == True{}: Bool}
        Shared.Bool.and_both(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Ballot.is_at(Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}, Place{line, h, r}, v))(Book.has_of(~Q, ~c, b, wk, n, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})(g))(
          Shared.List.all.if_both(Place.is_eq(Place{line, h, r}, Place{line, h, r}), u => String.eq(v, v))(Place.is_eq_refl(Place{line, h, r}))(Texts.String.eq_refl(v))
        )

# a ballot that the names under a place and a voter name is held, of that voter at that place
def Book.law.ballots.sound(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +w: Place, +voter: String, +bl: Ballot, ex: Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(Place.code(w, Codes.Code.text(voter, [])), k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, Entry.Ballot{bl}, n), 0n) == Some{k}: Maybe<&2, List<&2, U32>>})))) -> {
  Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)) == True{}: Bool
}:
  match ex:
    case Tuple{+n, Tuple{+k, Tuple{hs, Tuple{g, hk}}}}:
      Book.law.ballots.sound.of(~Q, ~c, b, wk, w, voter, bl, n, k)(hs)(g)(hk)

# a ballot that a book holds, of a voter at a place, is among the entries that the names under them name
def Book.law.ballots.complete(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +w: Place, +voter: String, bl: Ballot) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)) == True{}: Bool} -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, [])))), Entry.Ballot{bl}) == True{}: Bool
}:
  match bl:
    case Ballot{Signed{Place{+line, +h, +r}, +v, +a}, Link{+pv, +lk, +z}}:
      +hh =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), x => y => Entry.same_sound(~Q, ~c, x, y), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}})(
          Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), List.all.if(u => String.eq(v, voter), Place.is_eq(Place{line, h, r}, w)))(hh)
        )
        +hi = Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), List.all.if(u => String.eq(v, voter), Place.is_eq(Place{line, h, r}, w)))(hh)
        +ew = Place.is_eq_sound(Place{line, h, r}, w)(Shared.List.all.if_hit(Place.is_eq(Place{line, h, r}, w), u => String.eq(v, voter))(hi))
        +ev = Texts.String.eq_sound(v, voter)(Shared.List.all.if_rest(Place.is_eq(Place{line, h, r}, w), u => String.eq(v, voter))(hi))
        Book.under_named_complete(~Q, ~c, b, wk, 0n, Place.code(w, Codes.Code.text(voter, [])), Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}), Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}, Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))))(g)({==})(
          Equal.trans(Bool, Crits.Key.starts(Place.code(w, Codes.Code.text(voter, [])), Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))))), Crits.Key.starts(Place.code(w, Codes.Code.text(voter, [])), List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), True{}, Equal.cong(List<&2, U32>, Bool, t => Crits.Key.starts(Place.code(w, Codes.Code.text(voter, [])), t), Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))), Equal.trans(List<&2, U32>, Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Place.code(w, Codes.Code.text(voter, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))), Equal.trans(List<&2, U32>, Place.code(Place{line, h, r}, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Place.code(w, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Place.code(w, Codes.Code.text(voter, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Equal.cong(Place, List<&2, U32>, t => Place.code(t, Codes.Code.text(v, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Place{line, h, r}, w, ew), Equal.cong(String, List<&2, U32>, t => Place.code(w, Codes.Code.text(t, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), v, voter, ev)), Equal.trans(List<&2, U32>, Place.code(w, Codes.Code.text(voter, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Place.code(w, List.append(&2, U32, Codes.Code.text(voter, []), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), List.append(&2, U32, Place.code(w, Codes.Code.text(voter, [])), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))), Equal.cong(List<&2, U32>, List<&2, U32>, t => Place.code(w, t), Codes.Code.text(voter, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))), List.append(&2, U32, Codes.Code.text(voter, []), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))), Book.text_append(voter, [], Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))), Book.place_append(w, Codes.Code.text(voter, []), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})))))), Book.starts_append(Place.code(w, Codes.Code.text(voter, [])), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}))))
        )

# Book.law.ballots of the book x
def Book.law.ballots.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +w: Place, +voter: String, +bl: Ballot) -> {
  List.contains(~Ballot, ~Ballot.is_eq, Book.ballots(Q, Book.L.book(~Q, ~c, x), w, voter), bl) == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)): Bool
}:
  match x:
    case Tuple{+b, +wk}:
      %Equal.sym(Bool, List.contains(~Ballot, ~Ballot.is_eq, Entries.ballots(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, []))))), bl), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, [])))), Entry.Ballot{bl}), Book.ballots_eq(~Q, ~c, Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, [])))), bl)): {
        _ == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)): Bool
      }
      Crits.Crit.iff_eq(List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 0n), Place.code(w, Codes.Code.text(voter, [])))), Entry.Ballot{bl}), Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.is_at(bl, w, voter)))(
        h => Book.law.ballots.sound(~Q, ~c, b, wk, w, voter, bl, Book.under_named_sound(~Q, ~c, b, 0n, Shared.Bool.and_true_left(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk))), Place.code(w, Codes.Code.text(voter, [])), Entry.Ballot{bl})(h))
      )(Book.law.ballots.complete(~Q, ~c, b, wk, w, voter, bl))

# Book.law.asks.sound once the name and the key are found
def Book.law.asks.sound.of(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +author: String, e: Entry<Q>, +n: Name, +k: List<&2, U32>) -> {Crits.Key.starts(Codes.Code.text(author, []), k) == True{}: Bool} -> {
  Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>
} -> {Keys.at(Entry.keys(Q, e, n), 4n) == Some{k}: Maybe<&2, List<&2, U32>>} -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, e)), Some{e}), Entry.is_by(Q, e, author)) == True{}: Bool}:
  match e:
    case Entry.Ask{Id{+w, +rq}, +t, +q}:
      hs => g => hk =>
        +ew = Book.code_value(~String, ~Codes.Code.text.codec(), w, author, Name.key(n), List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, []))))(
          Equal.trans(List<&2, U32>, Codes.Code.text(w, Name.key(n)), k, Codes.Code.text(author, List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))), Shared.Maybe.some_inj(List<&2, U32>, Codes.Code.text(w, Name.key(n)), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Codes.Code.text(author, []), List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))), Codes.Code.text(author, List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))), Book.starts_split(Codes.Code.text(author, []), k)(hs), Equal.sym(List<&2, U32>, Codes.Code.text(author, List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))), List.append(&2, U32, Codes.Code.text(author, []), List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))), Book.text_append(author, [], List.drop(&2, U32, k, List.length(&2, U32, Codes.Code.text(author, [])))))))
        )
        %ew: {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})), Some{Entry.Ask{Id{w, rq}, t, q}}), String.eq(w, _)) == True{}: Bool}
        Shared.Bool.and_both(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})), Some{Entry.Ask{Id{w, rq}, t, q}}), String.eq(w, w))(Book.has_of(~Q, ~c, b, wk, n, Entry.Ask{Id{w, rq}, t, q})(g))(Texts.String.eq_refl(w))
    case Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}:
      hs => g => hk => Empty.absurd({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Entry.is_by(Q, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}, author)) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Data{ws}:
      hs => g => hk => Empty.absurd({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Data{ws})), Some{Entry.Data{ws}}), Entry.is_by(Q, Entry.Data{ws}, author)) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Lie{x}:
      hs => g => hk => Empty.absurd({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{x})), Some{Entry.Lie{x}}), Entry.is_by(Q, Entry.Lie{x}, author)) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))

# a request that the names under an author name is held, and by the author
def Book.law.asks.sound(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +author: String, +e: Entry<Q>, ex: Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(Codes.Code.text(author, []), k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{e}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, e, n), 4n) == Some{k}: Maybe<&2, List<&2, U32>>})))) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, e)), Some{e}), Entry.is_by(Q, e, author)) == True{}: Bool}:
  match ex:
    case Tuple{+n, Tuple{+k, Tuple{hs, Tuple{g, hk}}}}:
      Book.law.asks.sound.of(~Q, ~c, b, wk, author, e, n, k)(hs)(g)(hk)

# a request that a book holds, by an author, is among the entries that the names under the author name
def Book.law.asks.complete(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +author: String, e: Entry<Q>) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, e)), Some{e}), Entry.is_by(Q, e, author)) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, []))), e) == True{}: Bool}:
  match e:
    case Entry.Ask{Id{+w, +rq}, +t, +q}:
      +hh =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), x => y => Entry.same_sound(~Q, ~c, x, y), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})), Some{Entry.Ask{Id{w, rq}, t, q}})(
          Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})), Some{Entry.Ask{Id{w, rq}, t, q}}), String.eq(w, author))(hh)
        )
        +ew = Texts.String.eq_sound(w, author)(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})), Some{Entry.Ask{Id{w, rq}, t, q}}), String.eq(w, author))(hh))
        Book.under_named_complete(~Q, ~c, b, wk, 4n, Codes.Code.text(author, []), Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}), Entry.Ask{Id{w, rq}, t, q}, Codes.Code.text(w, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))))(g)({==})(
          Equal.trans(Bool, Crits.Key.starts(Codes.Code.text(author, []), Codes.Code.text(w, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})))), Crits.Key.starts(Codes.Code.text(author, []), List.append(&2, U32, Codes.Code.text(author, []), Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q})))), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Key.starts(Codes.Code.text(author, []), s), Codes.Code.text(w, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), List.append(&2, U32, Codes.Code.text(author, []), Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), Equal.trans(List<&2, U32>, Codes.Code.text(w, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), Codes.Code.text(author, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), List.append(&2, U32, Codes.Code.text(author, []), Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), Equal.cong(String, List<&2, U32>, s => Codes.Code.text(s, Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))), w, author, ew), Book.text_append(author, [], Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))))), Book.starts_append(Codes.Code.text(author, []), Name.key(Entry.name(~Q, ~c, Entry.Ask{Id{w, rq}, t, q}))))
        )
    case Entry.Ballot{+bl}:
      hh => Empty.absurd({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, []))), Entry.Ballot{bl}) == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), False{})(hh)))
    case Entry.Data{+ws}:
      hh => Empty.absurd({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, []))), Entry.Data{ws}) == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Data{ws})), Some{Entry.Data{ws}}), False{})(hh)))
    case Entry.Lie{+x}:
      hh => Empty.absurd({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, []))), Entry.Lie{x}) == True{}: Bool}, Shared.Bool.false_ne_true(Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{x})), Some{Entry.Lie{x}}), False{})(hh)))

# Book.law.asks of the book x
def Book.law.asks.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +author: String, +e: Entry<Q>) -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.asks(Q, Book.L.book(~Q, ~c, x), author), e) == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, e)), Some{e}), Entry.is_by(Q, e, author)): Bool
}:
  match x:
    case Tuple{+b, +wk}:
      Crits.Crit.iff_eq(List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 4n), Codes.Code.text(author, []))), e), Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, e)), Some{e}), Entry.is_by(Q, e, author)))(
        h => Book.law.asks.sound(~Q, ~c, b, wk, author, e, Book.under_named_sound(~Q, ~c, b, 4n, Shared.Bool.and_true_left(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk)))), Codes.Code.text(author, []), e)(h))
      )(Book.law.asks.complete(~Q, ~c, b, wk, author, e))

# Book.law.signed.sound once the signer s is known
def Book.law.signed.sound.at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +key: Hashes.Hash, +y: Entry<Q>, +n: Name, +k: List<&2, U32>, s: Maybe<&2, Hashes.Hash>) -> {
  Crits.Key.starts(Hashes.Hash.code(key, []), k) == True{}: Bool
} -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {Maybe.map(&2, Hashes.Hash, List<&2, U32>, kk => Hashes.Hash.code(kk, Name.key(n)), s) == Some{k}: Maybe<&2, List<&2, U32>>} -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, y)), Some{y}), Seals.Seal.is(key, s)) == True{}: Bool}:
  match s:
    case None{}:
      hs => g => hk => Empty.absurd({Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, y)), Some{y}), Seals.Seal.is(key, None{})) == True{}: Bool}, Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Some{+sk}:
      hs => g => hk =>
        +es = Book.code_value(~Hashes.Hash, ~Hashes.Hash.codec(), sk, key, Name.key(n), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, []))))(
          Equal.trans(List<&2, U32>, Hashes.Hash.code(sk, Name.key(n)), k, Hashes.Hash.code(key, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))), Shared.Maybe.some_inj(List<&2, U32>, Hashes.Hash.code(sk, Name.key(n)), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Hashes.Hash.code(key, []), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))), Hashes.Hash.code(key, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))), Book.starts_split(Hashes.Hash.code(key, []), k)(hs), Equal.sym(List<&2, U32>, Hashes.Hash.code(key, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))), List.append(&2, U32, Hashes.Hash.code(key, []), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))), Book.hash_append(key, [], List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(key, [])))))))
        )
        %Equal.sym(Hashes.Hash, sk, key, es): {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, y)), Some{y}), Seals.Seal.is(key, Some{_})) == True{}: Bool}
        Shared.Bool.and_both(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, y)), Some{y}), Hashes.Hash.is_eq(key, key))(Book.has_of(~Q, ~c, b, wk, n, y)(g))(Hashes.Hash.is_eq_refl(key))

# Book.law.signed.sound once the name and the key are found
def Book.law.signed.sound.of(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +key: Hashes.Hash, bl: Ballot, +n: Name, +k: List<&2, U32>) -> {Crits.Key.starts(Hashes.Hash.code(key, []), k) == True{}: Bool} -> {
  Book.get(Q, b, n) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>
} -> {Keys.at(Entry.keys(Q, Entry.Ballot{bl}, n), 5n) == Some{k}: Maybe<&2, List<&2, U32>>} -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)) == True{}: Bool}:
  match bl:
    case Ballot{Signed{Place{+line, +h, +r}, +v, +a}, Link{+pv, +lk, +z}}:
      hs => g => hk => Book.law.signed.sound.at(~Q, ~c, b, wk, key, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}, n, k, Ballot.signer(Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}))(hs)(g)(hk)

# a ballot that the names under a key name is held, and sealed by the key
def Book.law.signed.sound(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +key: Hashes.Hash, +bl: Ballot, ex: Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(Hashes.Hash.code(key, []), k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, Entry.Ballot{bl}, n), 5n) == Some{k}: Maybe<&2, List<&2, U32>>})))) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)) == True{}: Bool}:
  match ex:
    case Tuple{+n, Tuple{+k, Tuple{hs, Tuple{g, hk}}}}:
      Book.law.signed.sound.of(~Q, ~c, b, wk, key, bl, n, k)(hs)(g)(hk)

# Book.law.signed.complete once the signer s is known
def Book.law.signed.complete.at(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +key: Hashes.Hash, +y: Entry<Q>, +n: Name, s: Maybe<&2, Hashes.Hash>) -> {
  Maybe.map(&2, Hashes.Hash, List<&2, U32>, kk => Hashes.Hash.code(kk, Name.key(n)), s) == Keys.at(Entry.keys(Q, y, n), 5n): Maybe<&2, List<&2, U32>>
} -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {Seals.Seal.is(key, s) == True{}: Bool} -> {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), y) == True{}: Bool}:
  match s:
    case None{}:
      em => g => hi => Empty.absurd({List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), y) == True{}: Bool}, Shared.Bool.false_ne_true(hi))
    case Some{+sk}:
      em => g => hi =>
        +ek = Hashes.Hash.is_eq_sound(key, sk)(hi)
        Book.under_named_complete(~Q, ~c, b, wk, 5n, Hashes.Hash.code(key, []), n, y, Hashes.Hash.code(sk, Name.key(n)))(g)(
          Equal.sym(Maybe<&2, List<&2, U32>>, Some{Hashes.Hash.code(sk, Name.key(n))}, Keys.at(Entry.keys(Q, y, n), 5n), em)
        )(
          Equal.trans(Bool, Crits.Key.starts(Hashes.Hash.code(key, []), Hashes.Hash.code(sk, Name.key(n))), Crits.Key.starts(Hashes.Hash.code(key, []), Hashes.Hash.code(key, Name.key(n))), True{}, Equal.cong(Hashes.Hash, Bool, s2 => Crits.Key.starts(Hashes.Hash.code(key, []), Hashes.Hash.code(s2, Name.key(n))), sk, key, Equal.sym(Hashes.Hash, key, sk, ek)), Equal.trans(Bool, Crits.Key.starts(Hashes.Hash.code(key, []), Hashes.Hash.code(key, Name.key(n))), Crits.Key.starts(Hashes.Hash.code(key, []), List.append(&2, U32, Hashes.Hash.code(key, []), Name.key(n))), True{}, Equal.cong(List<&2, U32>, Bool, s2 => Crits.Key.starts(Hashes.Hash.code(key, []), s2), Hashes.Hash.code(key, Name.key(n)), List.append(&2, U32, Hashes.Hash.code(key, []), Name.key(n)), Book.hash_append(key, [], Name.key(n))), Book.starts_append(Hashes.Hash.code(key, []), Name.key(n))))
        )

# a ballot that a book holds, sealed by a key, is among the entries that the names under the key name
def Book.law.signed.complete(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +key: Hashes.Hash, bl: Ballot) -> {Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)) == True{}: Bool} -> {
  List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), Entry.Ballot{bl}) == True{}: Bool
}:
  match bl:
    case Ballot{Signed{Place{+line, +h, +r}, +v, +a}, Link{+pv, +lk, +z}}:
      +hh =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), x => y => Entry.same_sound(~Q, ~c, x, y), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}})(
          Shared.Bool.and_true_left(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Ballot.sealed(key, Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}))(hh)
        )
        Book.law.signed.complete.at(~Q, ~c, b, wk, key, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}), Ballot.signer(Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}))({==})(g)(
          Shared.Bool.and_true_right(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}}}), Ballot.sealed(key, Ballot{Signed{Place{line, h, r}, v, a}, Link{pv, lk, z}}))(hh)
        )

# Book.law.signed of the book x
def Book.law.signed.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +key: Hashes.Hash, +bl: Ballot) -> {
  List.contains(~Ballot, ~Ballot.is_eq, Book.signed(Q, Book.L.book(~Q, ~c, x), key), bl) == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)): Bool
}:
  match x:
    case Tuple{+b, +wk}:
      %Equal.sym(Bool, List.contains(~Ballot, ~Ballot.is_eq, Entries.ballots(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, [])))), bl), List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), Entry.Ballot{bl}), Book.ballots_eq(~Q, ~c, Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), bl)): {
        _ == Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)): Bool
      }
      Crits.Crit.iff_eq(List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Hashes.Hash.code(key, []))), Entry.Ballot{bl}), Bool.and(Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}), Ballot.sealed(key, bl)))(
        h => Book.law.signed.sound(~Q, ~c, b, wk, key, bl, Book.under_named_sound(~Q, ~c, b, 5n, Shared.Bool.and_true_right(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk)))), Hashes.Hash.code(key, []), Entry.Ballot{bl})(h))
      )(Book.law.signed.complete(~Q, ~c, b, wk, key, bl))

# Book.law.liars_complete of the book x
def Book.law.liars_complete.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +lx: Lie) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} -> {
  List.contains(~String, ~String.eq, Book.liars(Q, Book.L.book(~Q, ~c, x), Ballot.root(Lie.first(lx))), Ballot.voter(Lie.first(lx))) == True{}: Bool
}:
  match x:
    case Tuple{+b, +wk}:
      +hh =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), s1 => s2 => Entry.same_sound(~Q, ~c, s1, s2), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}})(hh)
        Book.liars_complete_list(~Q, ~c, Book.named(Q, b, Index.under(Book.index(Q, b, 3n), Hashes.Hash.code(Ballot.root(Lie.first(lx)), []))), lx)(
          Book.under_named_complete(~Q, ~c, b, wk, 3n, Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), Entry.name(~Q, ~c, Entry.Lie{lx}), Entry.Lie{lx}, Hashes.Hash.code(Ballot.root(Lie.first(lx)), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx})))))(g)({==})(
            Equal.trans(Bool, Crits.Key.starts(Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), Hashes.Hash.code(Ballot.root(Lie.first(lx)), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx}))))), Crits.Key.starts(Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), List.append(&2, U32, Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx}))))), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Key.starts(Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), s), Hashes.Hash.code(Ballot.root(Lie.first(lx)), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx})))), List.append(&2, U32, Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx})))), Book.hash_append(Ballot.root(Lie.first(lx)), [], Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx}))))), Book.starts_append(Hashes.Hash.code(Ballot.root(Lie.first(lx)), []), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(Entry.name(~Q, ~c, Entry.Lie{lx})))))
          )
        )

# Book.law.liars_sound once the name and the key are found
def Book.law.liars_sound.of3(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +r: Hashes.Hash, +voter: String, +lx: Lie, +hv: {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool}, +y: Entry<Q>, +n: Name, +k: List<&2, U32>) -> {
  y == Entry.Lie{lx}: Entry<Q>
} -> {Crits.Key.starts(Hashes.Hash.code(r, []), k) == True{}: Bool} -> {Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} -> {Keys.at(Entry.keys(Q, y, n), 3n) == Some{k}: Maybe<&2, List<&2, U32>>} -> Exists(Lie, lx => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} & ({Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool})):
  ey =>
    %Equal.sym(Entry<Q>, y, Entry.Lie{lx}, ey): {Crits.Key.starts(Hashes.Hash.code(r, []), k) == True{}: Bool} -> {Book.get(Q, b, n) == Some{_}: Maybe<&2, Entry<Q>>} -> {Keys.at(Entry.keys(Q, _, n), 3n) == Some{k}: Maybe<&2, List<&2, U32>>} -> Exists(Lie, lx => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} & ({Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool}))
    hs => g => hk =>
      +er = Book.code_value(~Hashes.Hash, ~Hashes.Hash.codec(), Ballot.root(Lie.first(lx)), r, Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(n)), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, []))))(
        Equal.trans(List<&2, U32>, Hashes.Hash.code(Ballot.root(Lie.first(lx)), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(n))), k, Hashes.Hash.code(r, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))), Shared.Maybe.some_inj(List<&2, U32>, Hashes.Hash.code(Ballot.root(Lie.first(lx)), Codes.Code.text(Ballot.voter(Lie.first(lx)), Name.key(n))), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Hashes.Hash.code(r, []), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))), Hashes.Hash.code(r, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))), Book.starts_split(Hashes.Hash.code(r, []), k)(hs), Equal.sym(List<&2, U32>, Hashes.Hash.code(r, List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))), List.append(&2, U32, Hashes.Hash.code(r, []), List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))), Book.hash_append(r, [], List.drop(&2, U32, k, List.length(&2, U32, Hashes.Hash.code(r, [])))))))
      )
      (
        lx,
        (
          Book.has_of(~Q, ~c, b, wk, n, Entry.Lie{lx})(g),
          (Equal.trans(Bool, Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r), Hashes.Hash.is_eq(r, r), True{}, Equal.cong(Hashes.Hash, Bool, s => Hashes.Hash.is_eq(s, r), Ballot.root(Lie.first(lx)), r, er), Hashes.Hash.is_eq_refl(r)), hv)
        )
      )

# Book.law.liars_sound once the proof of the lie is found
def Book.law.liars_sound.of2(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +r: Hashes.Hash, +voter: String, +lx: Lie, +hv: {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool}, +y: Entry<Q>, ex: Exists(Name, n => Exists(List<&2, U32>, k => {Crits.Key.starts(Hashes.Hash.code(r, []), k) == True{}: Bool} & ({Book.get(Q, b, n) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, n), 3n) == Some{k}: Maybe<&2, List<&2, U32>>})))) -> {
  y == Entry.Lie{lx}: Entry<Q>
} -> Exists(Lie, lx => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} & ({Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool})):
  match ex:
    case Tuple{+n, Tuple{+k, Tuple{hs, Tuple{g, hk}}}}:
      ey => Book.law.liars_sound.of3(~Q, ~c, b, wk, r, voter, lx, hv, y, n, k)(ey)(hs)(g)(hk)

# Book.law.liars_sound once a proof of a lie among the named entries is found
def Book.law.liars_sound.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +r: Hashes.Hash, +voter: String, ex: Exists(Lie, lx => {List.contains(~Entry<Q>, ~Entry.same(~Q, ~c), Book.named(Q, b, Index.under(Book.index(Q, b, 3n), Hashes.Hash.code(r, []))), Entry.Lie{lx}) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool})) -> Exists(Lie, lx => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} & ({Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool})):
  match ex:
    case Tuple{+lx, Tuple{hc, +hv}}:
      Book.law.liars_sound.of2(~Q, ~c, b, wk, r, voter, lx, hv, Entry.Lie{lx}, Book.under_named_sound(~Q, ~c, b, 3n, Shared.Bool.and_true_right(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk)))), Hashes.Hash.code(r, []), Entry.Lie{lx})(hc))({==})

# Book.law.liars_sound of the book x
def Book.law.liars_sound.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +r: Hashes.Hash, +voter: String) -> {List.contains(~String, ~String.eq, Book.liars(Q, Book.L.book(~Q, ~c, x), r), voter) == True{}: Bool} -> Exists(Lie, lx => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Lie{lx})), Some{Entry.Lie{lx}}) == True{}: Bool} & ({Hashes.Hash.is_eq(Ballot.root(Lie.first(lx)), r) == True{}: Bool} & {String.eq(Ballot.voter(Lie.first(lx)), voter) == True{}: Bool})):
  match x:
    case Tuple{+b, +wk}:
      h => Book.law.liars_sound.of1(~Q, ~c, b, wk, r, voter, Book.liars_sound_list(~Q, ~c, Book.named(Q, b, Index.under(Book.index(Q, b, 3n), Hashes.Hash.code(r, []))), voter)(h))

# Book.last_bound once the last key is known to be p then the number n2
def Book.last_bound.fin(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name, +nn: Nat, +kk: List<&2, U32>, +kl: List<&2, U32>, +hl: {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>}, +ek: {k == List.append(&2, U32, p, Crits.Key.ord(nn, kk)): List<&2, U32>}, hq: @q: List<&2, U32> -> {
  Maybe.is_some(&2, Name, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), q)) == True{}: Bool
} -> {Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(q)) == False{}: Bool}, +n2: Nat, +k2: List<&2, U32>, +ekl: {kl == List.append(&2, U32, p, Crits.Key.ord(n2, k2)): List<&2, U32>}) -> {Nat.is_le(nn, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, p))), 0n)) == True{}: Bool}:
      %Equal.sym(List<&2, U32>, kl, List.append(&2, U32, p, Crits.Key.ord(n2, k2)), ekl): {Nat.is_le(nn, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, _, List.length(&2, U32, p))), 0n)) == True{}: Bool}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, List.append(&2, U32, p, Crits.Key.ord(n2, k2)), List.length(&2, U32, p)), Crits.Key.ord(n2, k2), Book.drop_append(p, Crits.Key.ord(n2, k2))): {Nat.is_le(nn, Maybe.default(&2, Nat, Crits.Key.ord.value(_), 0n)) == True{}: Bool}
  %Equal.sym(Maybe<&2, Nat>, Crits.Key.ord.value(Crits.Key.ord(n2, k2)), Some{n2}, Crits.Key.ord_value(n2, k2)): {Nat.is_le(nn, Maybe.default(&2, Nat, _, 0n)) == True{}: Bool}
  Book.by({Nat.is_le(nn, n2) == True{}: Bool}, Nat.is_lt(n2, nn))(
    +t =>
      Empty.absurd(
        {Nat.is_le(nn, n2) == True{}: Bool},
        Shared.Bool.true_ne_false(
          Equal.trans(Bool, True{}, Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(k)), False{}, Equal.sym(Bool, Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(k)), True{}, Equal.trans(Bool, Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(k)), Crits.Bits.lt(Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(n2, k2))), Crits.Key.bits(k)), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Bits.lt(Crits.Key.bits(s), Crits.Key.bits(k)), kl, List.append(&2, U32, p, Crits.Key.ord(n2, k2)), ekl), Equal.trans(Bool, Crits.Bits.lt(Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(n2, k2))), Crits.Key.bits(k)), Crits.Bits.lt(Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(n2, k2))), Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(nn, kk)))), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Bits.lt(Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(n2, k2))), Crits.Key.bits(s)), k, List.append(&2, U32, p, Crits.Key.ord(nn, kk)), ek), Equal.trans(Bool, Crits.Bits.lt(Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(n2, k2))), Crits.Key.bits(List.append(&2, U32, p, Crits.Key.ord(nn, kk)))), Crits.Bits.lt(Crits.Key.bits(Crits.Key.ord(n2, k2)), Crits.Key.bits(Crits.Key.ord(nn, kk))), True{}, Crits.Key.lt_after(p, Crits.Key.ord(n2, k2), Crits.Key.ord(nn, kk)), Crits.Key.ord_lt(n2, nn, k2, kk)(t))))), hq(k)(Equal.cong(Maybe<&2, Name>, Bool, s => Maybe.is_some(&2, Name, s), Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), Some{x}, hl)))
        )
      )
  )(+f => Shared.Nat.nlt_le(n2, nn)(f))

# Book.last_bound once the last key is known to be of the number n2
def Book.last_bound.dec(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name, +nn: Nat, +kk: List<&2, U32>, +kl: List<&2, U32>, +hl: {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>}, +ek: {k == List.append(&2, U32, p, Crits.Key.ord(nn, kk)): List<&2, U32>}, hq: @q: List<&2, U32> -> {
  Maybe.is_some(&2, Name, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), q)) == True{}: Bool
} -> {Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(q)) == False{}: Bool}, ex: Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, p, Crits.Key.ord(n2, k2)): List<&2, U32>}))) -> {Nat.is_le(nn, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, p))), 0n)) == True{}: Bool}:
  match ex:
    case Tuple{+n2, Tuple{+k2, ekl}}:
      Book.last_bound.fin(d, p, k, x, nn, kk, kl, hl, ek, hq, n2, k2, ekl)

# Book.last_bound once the last entry is known to come after every key
def Book.last_bound.max(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name, +nn: Nat, +kk: List<&2, U32>, +kl: List<&2, U32>, +xl: Name, +hl: {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>}, +ek: {k == List.append(&2, U32, p, Crits.Key.ord(nn, kk)): List<&2, U32>}, lm: {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl) == Some{xl}: Maybe<&2, Name>} & (@q: List<&2, U32> -> {Maybe.is_some(&2, Name, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), q)) == True{}: Bool} -> {Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(q)) == False{}: Bool}), dec: @kl: List<&2, U32> -> @xl: Name -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl) == Some{xl}: Maybe<&2, Name>} -> Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, p, Crits.Key.ord(n2, k2)): List<&2, U32>}))) -> {Nat.is_le(nn, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, p))), 0n)) == True{}: Bool}:
  match lm:
    case Tuple{+hll, hq}:
      Book.last_bound.dec(d, p, k, x, nn, kk, kl, hl, ek, hq, dec(kl)(xl)(hll))

# Book.last_bound once the last entry under p is known (mm)
def Book.last_bound.at(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name, +nn: Nat, +kk: List<&2, U32>, mm: Maybe<&2, Crits.Bind<Name>>) -> {Crits.Crit.last(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)) == mm: Maybe<&2, Crits.Bind<Name>>} -> {
  Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>
} -> {k == List.append(&2, U32, p, Crits.Key.ord(nn, kk)): List<&2, U32>} -> (@kl: List<&2, U32> -> @xl: Name -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl) == Some{xl}: Maybe<&2, Name>} -> Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, p, Crits.Key.ord(n2, k2)): List<&2, U32>}))) -> {Nat.is_le(nn, Index.number(mm, List.length(&2, U32, p))) == True{}: Bool}:
  match mm:
    case None{}:
      em => hl => ek => dec =>
        Empty.absurd(
          {Nat.is_le(nn, Index.number(None{}, List.length(&2, U32, p))) == True{}: Bool},
          Shared.Maybe.none_ne_some(Name, x, Equal.trans(Maybe<&2, Name>, None{}, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), Some{x}, Equal.sym(Maybe<&2, Name>, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k), None{}, Crits.Crit.last_none(~Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k)(Crits.Crit.under_wf(~Name, Crits.Dict.crit(Name, d), p)(Book.dict_wf(~Name, d)))(em)), hl))
        )
    case Some{Crits.Bind{+kl, +xl}}:
      em => hl => ek => dec => Book.last_bound.max(d, p, k, x, nn, kk, kl, xl, hl, ek, Crits.Crit.last_max(~Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl, xl)(Crits.Crit.under_wf(~Name, Crits.Dict.crit(Name, d), p)(Book.dict_wf(~Name, d)))(em), dec)

# the number of a key of the index d under p, when each such key is p then a number, is at most the number of the last one
def Book.last_bound(+d: Crits.Dict(Name), +p: List<&2, U32>, +k: List<&2, U32>, +x: Name, +nn: Nat, +kk: List<&2, U32>) -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), k) == Some{x}: Maybe<&2, Name>} -> {
  k == List.append(&2, U32, p, Crits.Key.ord(nn, kk)): List<&2, U32>
} -> (@kl: List<&2, U32> -> @xl: Name -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl) == Some{xl}: Maybe<&2, Name>} -> Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, p, Crits.Key.ord(n2, k2)): List<&2, U32>}))) -> {Nat.is_le(nn, Index.last(d, p)) == True{}: Bool}:
  Book.last_bound.at(d, p, k, x, nn, kk, Crits.Crit.last(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)))({==})

# Book.last_found once the last entry is known
def Book.last_found.max(+d: Crits.Dict(Name), +p: List<&2, U32>, +kl: List<&2, U32>, +xl: Name, lm: {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl) == Some{xl}: Maybe<&2, Name>} & (@q: List<&2, U32> -> {Maybe.is_some(&2, Name, Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), q)) == True{}: Bool} -> {Crits.Bits.lt(Crits.Key.bits(kl), Crits.Key.bits(q)) == False{}: Bool})) -> Exists(List<&2, U32>, ka => Exists(Name, xa => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), ka) == Some{xa}: Maybe<&2, Name>} & {Index.number(Some{Crits.Bind{kl, xl}}, List.length(&2, U32, p)) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, ka, List.length(&2, U32, p))), 0n): Nat})):
  match lm:
    case Tuple{hll, hq}:
      (kl, (xl, (hll, {==})))

# Book.last_found once the last entry under p is known (mm)
def Book.last_found.at(+d: Crits.Dict(Name), +p: List<&2, U32>, mm: Maybe<&2, Crits.Bind<Name>>) -> {Crits.Crit.last(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)) == mm: Maybe<&2, Crits.Bind<Name>>} -> {
  Nat.is_eq(Index.number(mm, List.length(&2, U32, p)), 0n) == False{}: Bool
} -> Exists(List<&2, U32>, ka => Exists(Name, xa => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), ka) == Some{xa}: Maybe<&2, Name>} & {Index.number(mm, List.length(&2, U32, p)) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, ka, List.length(&2, U32, p))), 0n): Nat})):
  match mm:
    case None{}:
      em => hz => Empty.absurd(Exists(List<&2, U32>, ka => Exists(Name, xa => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), ka) == Some{xa}: Maybe<&2, Name>} & {Index.number(None{}, List.length(&2, U32, p)) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, ka, List.length(&2, U32, p))), 0n): Nat})), Shared.Bool.true_ne_false(hz))
    case Some{Crits.Bind{+kl, +xl}}:
      em => hz => Book.last_found.max(d, p, kl, xl, Crits.Crit.last_max(~Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), kl, xl)(Crits.Crit.under_wf(~Name, Crits.Dict.crit(Name, d), p)(Book.dict_wf(~Name, d)))(em))

# a number of the last key under p that is not 0 is that of a key of the index d
def Book.last_found(+d: Crits.Dict(Name), +p: List<&2, U32>) -> {Nat.is_eq(Index.last(d, p), 0n) == False{}: Bool} -> Exists(List<&2, U32>, ka => Exists(Name, xa => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p), ka) == Some{xa}: Maybe<&2, Name>} & {Index.last(d, p) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, ka, List.length(&2, U32, p))), 0n): Nat})):
  Book.last_found.at(d, p, Crits.Crit.last(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, d), p)))({==})

# a name under a key of the index i of a book in its one shape names an entry with that key
def Book.key_entry(-Q: Data, +b: Book<Q>, +i: Nat, +ho: {Book.ok.at(Q, b, i) == True{}: Bool}, +k: List<&2, U32>, +x: Name, mm: Maybe<&2, Entry<Q>>) -> {Book.get(Q, b, x) == mm: Maybe<&2, Entry<Q>>} -> {
  Crits.Dict.get(Name, Book.index(Q, b, i), k) == Some{x}: Maybe<&2, Name>
} -> Exists(Entry<Q>, y => {Book.get(Q, b, x) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, x), i) == Some{k}: Maybe<&2, List<&2, U32>>}):
  match mm:
    case None{}:
      em => gi =>
        Empty.absurd(
          Exists(Entry<Q>, y => {Book.get(Q, b, x) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, x), i) == Some{k}: Maybe<&2, List<&2, U32>>}),
          Shared.Bool.false_ne_true(Equal.trans(Bool, False{}, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), False{}, Equal.cong(Maybe<&2, Entry<Q>>, Bool, t => Book.ok.key(Q, t, i, k, x), Book.get(Q, b, x), None{}, em)), Book.ok.index_get(Q, b, i, Book.index(Q, b, i), k, x)(ho)(gi)))
        )
    case Some{+y}:
      +em => gi =>
        (
          y,
          (
            em,
            Shared.Maybe.is_eq_sound(~List<&2, U32>, ~Crits.Key.is_eq, s1 => s2 => Crits.Key.is_eq_sound(s1, s2), Keys.at(Entry.keys(Q, y, x), i), Some{k})(
              Equal.trans(Bool, Book.ok.key(Q, Some{y}, i, k, x), Book.ok.key(Q, Book.get(Q, b, x), i, k, x), True{}, Equal.sym(Bool, Book.ok.key(Q, Book.get(Q, b, x), i, k, x), Book.ok.key(Q, Some{y}, i, k, x), Equal.cong(Maybe<&2, Entry<Q>>, Bool, t => Book.ok.key(Q, t, i, k, x), Book.get(Q, b, x), Some{y}, em)), Book.ok.index_get(Q, b, i, Book.index(Q, b, i), k, x)(ho)(gi))
            )
          )
        )

# a key of the rounds index under a line and a height is of a ballot at that height of the line, and its round follows the prefix
def Book.round_key(-Q: Data, +line: Line, +h: U32, y: Entry<Q>, +x: Name, +k: List<&2, U32>) -> {Keys.at(Entry.keys(Q, y, x), 1n) == Some{k}: Maybe<&2, List<&2, U32>>} -> {
  Crits.Key.starts(Line.code(line, [h]), k) == True{}: Bool
} -> Exists(Ballot, bl => Exists(Nat, r3 => {y == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(x)): List<&2, U32>}))):
  match y:
    case Entry.Ballot{Ballot{Signed{Place{+l3, +h3, +r3}, +v, +a}, Link{+pv, +lk, +z}}}:
      hk => hs =>
        +eq = Equal.trans(List<&2, U32>, Line.code(l3, h3 <> Crits.Key.ord(r3, Name.key(x))), k, Line.code(line, h <> List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))), Shared.Maybe.some_inj(List<&2, U32>, Line.code(l3, h3 <> Crits.Key.ord(r3, Name.key(x))), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Line.code(line, [h]), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))), Line.code(line, h <> List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))), Book.starts_split(Line.code(line, [h]), k)(hs), Equal.sym(List<&2, U32>, Line.code(line, h <> List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))), List.append(&2, U32, Line.code(line, [h]), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))), Book.line_append(line, [h], List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h])))))))
        +er = Book.code_rest(~Line, ~Line.codec(), l3, line, h3 <> Crits.Key.ord(r3, Name.key(x)), h <> List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))))(eq)
        +el = Book.code_value(~Line, ~Line.codec(), l3, line, h3 <> Crits.Key.ord(r3, Name.key(x)), h <> List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))))(eq)
        +eh = Shared.List.head_eq(U32, h3, h, Crits.Key.ord(r3, Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))), er)
        (
          Ballot{Signed{Place{l3, h3, r3}, v, a}, Link{pv, lk, z}},
          (
            r3,
            (
              {==},
              (
                (
                  %el: {Ballot.is_at(Ballot{Signed{Place{l3, h3, r3}, v, a}, Link{pv, lk, z}}, Place{_, h, r3}, v) == True{}: Bool}
                  %eh: {Ballot.is_at(Ballot{Signed{Place{l3, h3, r3}, v, a}, Link{pv, lk, z}}, Place{l3, _, r3}, v) == True{}: Bool}
                  Shared.List.all.if_both(Place.is_eq(Place{l3, h3, r3}, Place{l3, h3, r3}), u => String.eq(v, v))(Place.is_eq_refl(Place{l3, h3, r3}))(Texts.String.eq_refl(v))
                ),
                Equal.sym(List<&2, U32>, Crits.Key.ord(r3, Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))), Shared.List.tail_eq(U32, h3, h, Crits.Key.ord(r3, Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))), er))
              )
            )
          )
        )
    case Entry.Ask{Id{w, q}, t, aa}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(Nat, r3 => {Entry.Ask{Id{w, q}, t, aa} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(x)): List<&2, U32>}))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Data{ws}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(Nat, r3 => {Entry.Data{ws} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(x)): List<&2, U32>}))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Lie{lx}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(Nat, r3 => {Entry.Lie{lx} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(x)): List<&2, U32>}))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))

# a key of the heights index under a line is of a ballot on the line, and its height follows the prefix
def Book.height_key(-Q: Data, +line: Line, y: Entry<Q>, +x: Name, +k: List<&2, U32>) -> {Keys.at(Entry.keys(Q, y, x), 2n) == Some{k}: Maybe<&2, List<&2, U32>>} -> {
  Crits.Key.starts(Line.code(line, []), k) == True{}: Bool
} -> Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {y == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(x)): List<&2, U32>})))):
  match y:
    case Entry.Ballot{Ballot{Signed{Place{+l3, +h3, +r3}, +v, +a}, Link{+pv, +lk, +z}}}:
      hk => hs =>
        +eq = Equal.trans(List<&2, U32>, Line.code(l3, Crits.Key.ord(U32.to_nat(h3), Name.key(x))), k, Line.code(line, List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))), Shared.Maybe.some_inj(List<&2, U32>, Line.code(l3, Crits.Key.ord(U32.to_nat(h3), Name.key(x))), k, hk), Equal.trans(List<&2, U32>, k, List.append(&2, U32, Line.code(line, []), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))), Line.code(line, List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))), Book.starts_split(Line.code(line, []), k)(hs), Equal.sym(List<&2, U32>, Line.code(line, List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))), List.append(&2, U32, Line.code(line, []), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))), Book.line_append(line, [], List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, [])))))))
        +el = Book.code_value(~Line, ~Line.codec(), l3, line, Crits.Key.ord(U32.to_nat(h3), Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))))(eq)
        (
          Ballot{Signed{Place{l3, h3, r3}, v, a}, Link{pv, lk, z}},
          (
            h3,
            (
              r3,
              (
                {==},
                (
                  (
                    %el: {Ballot.is_at(Ballot{Signed{Place{l3, h3, r3}, v, a}, Link{pv, lk, z}}, Place{_, h3, r3}, v) == True{}: Bool}
                    Shared.List.all.if_both(Place.is_eq(Place{l3, h3, r3}, Place{l3, h3, r3}), u => String.eq(v, v))(Place.is_eq_refl(Place{l3, h3, r3}))(Texts.String.eq_refl(v))
                  ),
                  Equal.sym(List<&2, U32>, Crits.Key.ord(U32.to_nat(h3), Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))), Book.code_rest(~Line, ~Line.codec(), l3, line, Crits.Key.ord(U32.to_nat(h3), Name.key(x)), List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))))(eq))
                )
              )
            )
          )
        )
    case Entry.Ask{Id{w, q}, t, aa}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Entry.Ask{Id{w, q}, t, aa} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(x)): List<&2, U32>})))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Data{ws}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Entry.Data{ws} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(x)): List<&2, U32>})))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))
    case Entry.Lie{lx}:
      hk => hs => Empty.absurd(Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Entry.Lie{lx} == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, k, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(x)): List<&2, U32>})))), Shared.Maybe.none_ne_some(List<&2, U32>, k, hk))

# Book.rounds.key once the ballot is decoded
def Book.rounds.of3(-Q: Data, +b: Book<Q>, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name, +st: {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool}, +y: Entry<Q>, +g: {Book.get(Q, b, xl) == Some{y}: Maybe<&2, Entry<Q>>}, ex: Exists(Ballot, bl => Exists(Nat, r3 => {y == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>})))) -> Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>})))):
  match ex:
    case Tuple{+bl, Tuple{+r3, Tuple{ey, Tuple{isat, ed}}}}:
      (bl, (r3, (st, (Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, b, xl), Some{y}, Some{Entry.Ballot{bl}}, g, Equal.cong(Entry<Q>, Maybe<&2, Entry<Q>>, s => Some{s}, y, Entry.Ballot{bl}, ey)), (isat, ed)))))

# Book.rounds.key once the entry of the name is found
def Book.rounds.of2(-Q: Data, +b: Book<Q>, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name, +st: {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool}, ex: Exists(Entry<Q>, y => {Book.get(Q, b, xl) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, xl), 1n) == Some{kl}: Maybe<&2, List<&2, U32>>})) -> Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>})))):
  match ex:
    case Tuple{+y, Tuple{+g, +hk}}:
      Book.rounds.of3(Q, b, line, h, kl, xl, st, y, g, Book.round_key(Q, line, h, y, xl, kl)(hk)(st))

# Book.rounds.key once the key is found in the index
def Book.rounds.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name, pr: {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & {Crits.Dict.get(Name, Book.index(Q, b, 1n), kl) == Some{xl}: Maybe<&2, Name>}) -> Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>})))):
  match pr:
    case Tuple{+st, +gi}:
      Book.rounds.of2(Q, b, line, h, kl, xl, st, Book.key_entry(Q, b, 1n, Shared.Bool.and_true_right(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk))), kl, xl, Book.get(Q, b, xl))({==})(gi))

# a key of the rounds index under the prefix is of a ballot that the book holds
def Book.rounds.key(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name) -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, Book.index(Q, b, 1n)), Line.code(line, [h])), kl) == Some{xl}: Maybe<&2, Name>} -> Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>})))):
  hl => Book.rounds.of1(~Q, ~c, b, wk, line, h, kl, xl, Book.under_key(Book.index(Q, b, 1n), Line.code(line, [h]), kl, xl)(hl))

# a key of the rounds index under the prefix is the prefix then a number
def Book.rounds.ord(-Q: Data, +b: Book<Q>, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name, ex: Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>}))))) -> Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, Line.code(line, [h]), Crits.Key.ord(n2, k2)): List<&2, U32>})):
  match ex:
    case Tuple{+bl, Tuple{+r3, Tuple{+st, Tuple{g, Tuple{isat, ed}}}}}:
      (r3, (Name.key(xl), Equal.trans(List<&2, U32>, kl, List.append(&2, U32, Line.code(line, [h]), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h])))), List.append(&2, U32, Line.code(line, [h]), Crits.Key.ord(r3, Name.key(xl))), Book.starts_split(Line.code(line, [h]), kl)(st), Equal.cong(List<&2, U32>, List<&2, U32>, s => List.append(&2, U32, Line.code(line, [h]), s), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))), Crits.Key.ord(r3, Name.key(xl)), ed))))

# Book.heights.key once the ballot is decoded
def Book.heights.of3(-Q: Data, +b: Book<Q>, +line: Line, +kl: List<&2, U32>, +xl: Name, +st: {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool}, +y: Entry<Q>, +g: {Book.get(Q, b, xl) == Some{y}: Maybe<&2, Entry<Q>>}, ex: Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {y == Entry.Ballot{bl}: Entry<Q>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>}))))) -> Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>}))))):
  match ex:
    case Tuple{+bl, Tuple{+h3, Tuple{+r3, Tuple{ey, Tuple{isat, ed}}}}}:
      (bl, (h3, (r3, (st, (Equal.trans(Maybe<&2, Entry<Q>>, Book.get(Q, b, xl), Some{y}, Some{Entry.Ballot{bl}}, g, Equal.cong(Entry<Q>, Maybe<&2, Entry<Q>>, s => Some{s}, y, Entry.Ballot{bl}, ey)), (isat, ed))))))

# Book.heights.key once the entry of the name is found
def Book.heights.of2(-Q: Data, +b: Book<Q>, +line: Line, +kl: List<&2, U32>, +xl: Name, +st: {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool}, ex: Exists(Entry<Q>, y => {Book.get(Q, b, xl) == Some{y}: Maybe<&2, Entry<Q>>} & {Keys.at(Entry.keys(Q, y, xl), 2n) == Some{kl}: Maybe<&2, List<&2, U32>>})) -> Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>}))))):
  match ex:
    case Tuple{+y, Tuple{+g, +hk}}:
      Book.heights.of3(Q, b, line, kl, xl, st, y, g, Book.height_key(Q, line, y, xl, kl)(hk)(st))

# Book.heights.key once the key is found in the index
def Book.heights.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +kl: List<&2, U32>, +xl: Name, pr: {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & {Crits.Dict.get(Name, Book.index(Q, b, 2n), kl) == Some{xl}: Maybe<&2, Name>}) -> Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>}))))):
  match pr:
    case Tuple{+st, +gi}:
      Book.heights.of2(Q, b, line, kl, xl, st, Book.key_entry(Q, b, 2n, Shared.Bool.and_true_left(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))(Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n))))(Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Bool.and(Book.ok.at(Q, b, 4n), Book.ok.at(Q, b, 5n)))))(wk)))), kl, xl, Book.get(Q, b, xl))({==})(gi))

# a key of the heights index under the prefix is of a ballot that the book holds
def Book.heights.key(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +kl: List<&2, U32>, +xl: Name) -> {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, Book.index(Q, b, 2n)), Line.code(line, [])), kl) == Some{xl}: Maybe<&2, Name>} -> Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>}))))):
  hl => Book.heights.of1(~Q, ~c, b, wk, line, kl, xl, Book.under_key(Book.index(Q, b, 2n), Line.code(line, []), kl, xl)(hl))

# a key of the heights index under the prefix is the prefix then a number
def Book.heights.ord(-Q: Data, +b: Book<Q>, +line: Line, +kl: List<&2, U32>, +xl: Name, ex: Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>})))))) -> Exists(Nat, n2 => Exists(List<&2, U32>, k2 => {kl == List.append(&2, U32, Line.code(line, []), Crits.Key.ord(n2, k2)): List<&2, U32>})):
  match ex:
    case Tuple{+bl, Tuple{+h3, Tuple{+r3, Tuple{+st, Tuple{g, Tuple{isat, ed}}}}}}:
      (U32.to_nat(h3), (Name.key(xl), Equal.trans(List<&2, U32>, kl, List.append(&2, U32, Line.code(line, []), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [])))), List.append(&2, U32, Line.code(line, []), Crits.Key.ord(U32.to_nat(h3), Name.key(xl))), Book.starts_split(Line.code(line, []), kl)(st), Equal.cong(List<&2, U32>, List<&2, U32>, s => List.append(&2, U32, Line.code(line, []), s), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))), Crits.Key.ord(U32.to_nat(h3), Name.key(xl)), ed))))

# no ballot that a book holds is at a round above its bound
def Book.rounds.le(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, bl: Ballot, +line: Line, +h: U32, +r: Nat, +voter: String) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} -> {
  Ballot.is_at(bl, Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(r, Book.rounds(Q, b, line, h)) == True{}: Bool}:
  match bl:
    case Ballot{Signed{Place{+l2, +h2, +r2}, +v, +a}, Link{+pv, +lk, +z}}:
      +hh => +hi =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), s1 => s2 => Entry.same_sound(~Q, ~c, s1, s2), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}})(hh)
        +hp = Shared.List.all.if_hit(Place.is_eq(Place{l2, h2, r2}, Place{line, h, r}), u => String.eq(v, voter))(hi)
        +hr = Shared.List.all.if_rest(Line.is_eq(l2, line), u => List.all.if(u2 => Nat.is_eq(r2, r), U32.is_eq(h2, h)))(hp)
        +el = Line.is_eq_sound(l2, line)(Shared.List.all.if_hit(Line.is_eq(l2, line), u => List.all.if(u2 => Nat.is_eq(r2, r), U32.is_eq(h2, h)))(hp))
        +eh = Shared.U32.is_eq_sound(h2, h)(Shared.List.all.if_hit(U32.is_eq(h2, h), u2 => Nat.is_eq(r2, r))(hr))
        +ek = Book.line_append(l2, [h2], Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))
        +gi = Book.index_has(~Q, ~c, b, wk, 1n, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}), Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}, Line.code(l2, h2 <> Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))))(g)({==})
        +hs = Equal.trans(Bool, Crits.Key.starts(Line.code(l2, [h2]), Line.code(l2, h2 <> Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))), Crits.Key.starts(Line.code(l2, [h2]), List.append(&2, U32, Line.code(l2, [h2]), Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Key.starts(Line.code(l2, [h2]), s), Line.code(l2, h2 <> Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), List.append(&2, U32, Line.code(l2, [h2]), Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), ek), Book.starts_append(Line.code(l2, [h2]), Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))))
        %el: {Nat.is_le(r, Book.rounds(Q, b, _, h)) == True{}: Bool}
        %eh: {Nat.is_le(r, Book.rounds(Q, b, l2, _)) == True{}: Bool}
        %Shared.Nat.is_eq_sound(r2, r)(Shared.List.all.if_rest(U32.is_eq(h2, h), u2 => Nat.is_eq(r2, r))(hr)): {Nat.is_le(_, Book.rounds(Q, b, l2, h2)) == True{}: Bool}
        Book.last_bound(Book.index(Q, b, 1n), Line.code(l2, [h2]), Line.code(l2, h2 <> Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}), r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))(Book.under_lookup_of(Book.index(Q, b, 1n), Line.code(l2, [h2]), Line.code(l2, h2 <> Crits.Key.ord(r2, Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))(hs)(gi))(ek)(
          +kl => +xl => hl => Book.rounds.ord(Q, b, l2, h2, kl, xl, Book.rounds.key(~Q, ~c, b, wk, l2, h2, kl, xl)(hl))
        )

# no ballot that a book holds on a line is at a height above its bound
def Book.heights.le(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, bl: Ballot, +line: Line, +h: U32, +r: Nat, +voter: String) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} -> {
  Ballot.is_at(bl, Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(U32.to_nat(h), Book.heights(Q, b, line)) == True{}: Bool}:
  match bl:
    case Ballot{Signed{Place{+l2, +h2, +r2}, +v, +a}, Link{+pv, +lk, +z}}:
      +hh => +hi =>
        +g = Shared.Maybe.is_eq_sound(~Entry<Q>, ~Entry.same(~Q, ~c), s1 => s2 => Entry.same_sound(~Q, ~c, s1, s2), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})), Some{Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}})(hh)
        +hp = Shared.List.all.if_hit(Place.is_eq(Place{l2, h2, r2}, Place{line, h, r}), u => String.eq(v, voter))(hi)
        +hr = Shared.List.all.if_rest(Line.is_eq(l2, line), u => List.all.if(u2 => Nat.is_eq(r2, r), U32.is_eq(h2, h)))(hp)
        +el = Line.is_eq_sound(l2, line)(Shared.List.all.if_hit(Line.is_eq(l2, line), u => List.all.if(u2 => Nat.is_eq(r2, r), U32.is_eq(h2, h)))(hp))
        +eh = Shared.U32.is_eq_sound(h2, h)(Shared.List.all.if_hit(U32.is_eq(h2, h), u2 => Nat.is_eq(r2, r))(hr))
        +ek = Book.line_append(l2, [], Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))
        +gi = Book.index_has(~Q, ~c, b, wk, 2n, Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}), Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}, Line.code(l2, Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))))(g)({==})
        +hs = Equal.trans(Bool, Crits.Key.starts(Line.code(l2, []), Line.code(l2, Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))), Crits.Key.starts(Line.code(l2, []), List.append(&2, U32, Line.code(l2, []), Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))))), True{}, Equal.cong(List<&2, U32>, Bool, s => Crits.Key.starts(Line.code(l2, []), s), Line.code(l2, Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), List.append(&2, U32, Line.code(l2, []), Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), ek), Book.starts_append(Line.code(l2, []), Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))))
        %el: {Nat.is_le(U32.to_nat(h), Book.heights(Q, b, _)) == True{}: Bool}
        %eh: {Nat.is_le(U32.to_nat(_), Book.heights(Q, b, l2)) == True{}: Bool}
        Book.last_bound(Book.index(Q, b, 2n), Line.code(l2, []), Line.code(l2, Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}), U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))(Book.under_lookup_of(Book.index(Q, b, 2n), Line.code(l2, []), Line.code(l2, Crits.Key.ord(U32.to_nat(h2), Name.key(Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}})))), Entry.name(~Q, ~c, Entry.Ballot{Ballot{Signed{Place{l2, h2, r2}, v, a}, Link{pv, lk, z}}}))(hs)(gi))(ek)(
          +kl => +xl => hl => Book.heights.ord(Q, b, l2, kl, xl, Book.heights.key(~Q, ~c, b, wk, l2, kl, xl)(hl))
        )

# Book.rounds.some once the last key is decoded
def Book.rounds.some.of2(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +h: U32, +kl: List<&2, U32>, +xl: Name, +en: {Book.rounds(Q, b, line, h) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h])))), 0n): Nat}, ex: Exists(Ballot, bl => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, [h]), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))) == Crits.Key.ord(r3, Name.key(xl)): List<&2, U32>}))))) -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & {Ballot.is_at(bl, Place{line, h, Book.rounds(Q, b, line, h)}, Ballot.voter(bl)) == True{}: Bool}):
  match ex:
    case Tuple{+bl, Tuple{+r3, Tuple{st, Tuple{+g, Tuple{isat, ed}}}}}:
      +eR = Equal.trans(Nat, Book.rounds(Q, b, line, h), Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h])))), 0n), r3, en, Equal.trans(Nat, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h])))), 0n), Maybe.default(&2, Nat, Crits.Key.ord.value(Crits.Key.ord(r3, Name.key(xl))), 0n), r3, Equal.cong(List<&2, U32>, Nat, s => Maybe.default(&2, Nat, Crits.Key.ord.value(s), 0n), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h]))), Crits.Key.ord(r3, Name.key(xl)), ed), Equal.cong(Maybe<&2, Nat>, Nat, s => Maybe.default(&2, Nat, s, 0n), Crits.Key.ord.value(Crits.Key.ord(r3, Name.key(xl))), Some{r3}, Crits.Key.ord_value(r3, Name.key(xl)))))
      (
        bl,
        (
          Book.has_of(~Q, ~c, b, wk, xl, Entry.Ballot{bl})(g),
          Equal.trans(Bool, Ballot.is_at(bl, Place{line, h, Book.rounds(Q, b, line, h)}, Ballot.voter(bl)), Ballot.is_at(bl, Place{line, h, r3}, Ballot.voter(bl)), True{}, Equal.cong(Nat, Bool, s => Ballot.is_at(bl, Place{line, h, s}, Ballot.voter(bl)), Book.rounds(Q, b, line, h), r3, eR), isat)
        )
      )

# Book.rounds.some once the last key is found
def Book.rounds.some.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +h: U32, ex: Exists(List<&2, U32>, kl => Exists(Name, xl => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, Book.index(Q, b, 1n)), Line.code(line, [h])), kl) == Some{xl}: Maybe<&2, Name>} & {Book.rounds(Q, b, line, h) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [h])))), 0n): Nat}))) -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & {Ballot.is_at(bl, Place{line, h, Book.rounds(Q, b, line, h)}, Ballot.voter(bl)) == True{}: Bool}):
  match ex:
    case Tuple{+kl, Tuple{+xl, Tuple{hl, en}}}:
      Book.rounds.some.of2(~Q, ~c, b, wk, line, h, kl, xl, en, Book.rounds.key(~Q, ~c, b, wk, line, h, kl, xl)(hl))

# a round bound of a book that is not 0 is the round of a ballot it holds
def Book.rounds.some(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +h: U32) -> {Nat.is_eq(Book.rounds(Q, b, line, h), 0n) == False{}: Bool} -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & {Ballot.is_at(bl, Place{line, h, Book.rounds(Q, b, line, h)}, Ballot.voter(bl)) == True{}: Bool}):
  hz => Book.rounds.some.of1(~Q, ~c, b, wk, line, h, Book.last_found(Book.index(Q, b, 1n), Line.code(line, [h]))(hz))

# Book.heights.some once the last key is decoded
def Book.heights.some.of2(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, +kl: List<&2, U32>, +xl: Name, +en: {Book.heights(Q, b, line) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [])))), 0n): Nat}, ex: Exists(Ballot, bl => Exists(U32, h3 => Exists(Nat, r3 => {Crits.Key.starts(Line.code(line, []), kl) == True{}: Bool} & ({Book.get(Q, b, xl) == Some{Entry.Ballot{bl}}: Maybe<&2, Entry<Q>>} & ({Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))) == Crits.Key.ord(U32.to_nat(h3), Name.key(xl)): List<&2, U32>})))))) -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & Exists(U32, h3 => Exists(Nat, r3 => {Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {U32.to_nat(h3) == Book.heights(Q, b, line): Nat}))):
  match ex:
    case Tuple{+bl, Tuple{+h3, Tuple{+r3, Tuple{st, Tuple{+g, Tuple{isat, ed}}}}}}:
      (
        bl,
        (
          Book.has_of(~Q, ~c, b, wk, xl, Entry.Ballot{bl})(g),
          (
            h3,
            (
              r3,
              (
                isat,
                Equal.sym(Nat, Book.heights(Q, b, line), U32.to_nat(h3), Equal.trans(Nat, Book.heights(Q, b, line), Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [])))), 0n), U32.to_nat(h3), en, Equal.trans(Nat, Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [])))), 0n), Maybe.default(&2, Nat, Crits.Key.ord.value(Crits.Key.ord(U32.to_nat(h3), Name.key(xl))), 0n), U32.to_nat(h3), Equal.cong(List<&2, U32>, Nat, s => Maybe.default(&2, Nat, Crits.Key.ord.value(s), 0n), List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, []))), Crits.Key.ord(U32.to_nat(h3), Name.key(xl)), ed), Equal.cong(Maybe<&2, Nat>, Nat, s => Maybe.default(&2, Nat, s, 0n), Crits.Key.ord.value(Crits.Key.ord(U32.to_nat(h3), Name.key(xl))), Some{U32.to_nat(h3)}, Crits.Key.ord_value(U32.to_nat(h3), Name.key(xl))))))
              )
            )
          )
        )
      )

# Book.heights.some once the last key is found
def Book.heights.some.of1(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line, ex: Exists(List<&2, U32>, kl => Exists(Name, xl => {Crits.Crit.lookup(Name, Crits.Crit.under(Name, Crits.Dict.crit(Name, Book.index(Q, b, 2n)), Line.code(line, [])), kl) == Some{xl}: Maybe<&2, Name>} & {Book.heights(Q, b, line) == Maybe.default(&2, Nat, Crits.Key.ord.value(List.drop(&2, U32, kl, List.length(&2, U32, Line.code(line, [])))), 0n): Nat}))) -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & Exists(U32, h3 => Exists(Nat, r3 => {Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {U32.to_nat(h3) == Book.heights(Q, b, line): Nat}))):
  match ex:
    case Tuple{+kl, Tuple{+xl, Tuple{hl, en}}}:
      Book.heights.some.of2(~Q, ~c, b, wk, line, kl, xl, en, Book.heights.key(~Q, ~c, b, wk, line, kl, xl)(hl))

# a height bound of a book that is not 0 is the height of a ballot it holds on the line
def Book.heights.some(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +wk: {Book.ok(~Q, ~c, b) == True{}: Bool}, +line: Line) -> {Nat.is_eq(Book.heights(Q, b, line), 0n) == False{}: Bool} -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, b, Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & Exists(U32, h3 => Exists(Nat, r3 => {Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {U32.to_nat(h3) == Book.heights(Q, b, line): Nat}))):
  hz => Book.heights.some.of1(~Q, ~c, b, wk, line, Book.last_found(Book.index(Q, b, 2n), Line.code(line, []))(hz))

# the first half of Book.law.rounds, of the book x
def Book.law.rounds.le.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +bl: Ballot, +line: Line, +h: U32, +r: Nat, +voter: String) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} -> {
  Ballot.is_at(bl, Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(r, Book.rounds(Q, Book.L.book(~Q, ~c, x), line, h)) == True{}: Bool}:
  match x:
    case Tuple{+b, +wk}:
      Book.rounds.le(~Q, ~c, b, wk, bl, line, h, r, voter)

# the second half of Book.law.rounds, of the book x
def Book.law.rounds.some.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +line: Line, +h: U32) -> {Nat.is_eq(Book.rounds(Q, Book.L.book(~Q, ~c, x), line, h), 0n) == False{}: Bool} -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & {Ballot.is_at(bl, Place{line, h, Book.rounds(Q, Book.L.book(~Q, ~c, x), line, h)}, Ballot.voter(bl)) == True{}: Bool}):
  match x:
    case Tuple{+b, +wk}:
      Book.rounds.some(~Q, ~c, b, wk, line, h)

# the first half of Book.law.heights, of the book x
def Book.law.heights.le.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +bl: Ballot, +line: Line, +h: U32, +r: Nat, +voter: String) -> {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} -> {
  Ballot.is_at(bl, Place{line, h, r}, voter) == True{}: Bool
} -> {Nat.is_le(U32.to_nat(h), Book.heights(Q, Book.L.book(~Q, ~c, x), line)) == True{}: Bool}:
  match x:
    case Tuple{+b, +wk}:
      Book.heights.le(~Q, ~c, b, wk, bl, line, h, r, voter)

# the second half of Book.law.heights, of the book x
def Book.law.heights.some.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +line: Line) -> {Nat.is_eq(Book.heights(Q, Book.L.book(~Q, ~c, x), line), 0n) == False{}: Bool} -> Exists(Ballot, bl => {Shared.Maybe.is_eq(~Entry<Q>, ~Entry.same(~Q, ~c), Book.get(Q, Book.L.book(~Q, ~c, x), Entry.name(~Q, ~c, Entry.Ballot{bl})), Some{Entry.Ballot{bl}}) == True{}: Bool} & Exists(U32, h3 => Exists(Nat, r3 => {Ballot.is_at(bl, Place{line, h3, r3}, Ballot.voter(bl)) == True{}: Bool} & {U32.to_nat(h3) == Book.heights(Q, Book.L.book(~Q, ~c, x), line): Nat}))):
  match x:
    case Tuple{+b, +wk}:
      Book.heights.some(~Q, ~c, b, wk, line)

# a new book holds nothing
def Book.law.get_empty(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.GetEmpty(Q, Book.kind(~Q, ~c)):
  n => {==}

# Book.law.get_add of the book x
def Book.law.get_add.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +e: Entry<Q>, +n: Name) -> {
  Book.get(Q, Book.L.book(~Q, ~c, Book.L.add(~Q, ~c, x, e)), n)
    == Maybe.or(&2, Entry<Q>, Book.get(Q, Book.L.book(~Q, ~c, x), n), Shared.Maybe.when(Entry<Q>, Name.is_eq(Entry.name(~Q, ~c, e), n), u => Some{e})): Maybe<&2, Entry<Q>>
}:
  match x:
    case Tuple{+b, w}:
      Book.get_add(~Q, ~c, b, e, n)

# an add keeps what a book holds, and puts the entry under its name when nothing is there
def Book.law.get_add(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.GetAdd(Q, c, Book.kind(~Q, ~c)):
  l => e => n => Book.law.get_add.at(~Q, ~c, l, e, n)

# Book.law.get_named of the book x
def Book.law.get_named.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +n: Name, +e: Entry<Q>) -> {Book.get(Q, Book.L.book(~Q, ~c, x), n) == Some{e}: Maybe<&2, Entry<Q>>} -> {
  Entry.name(~Q, ~c, e) == n: Name
}:
  match x:
    case Tuple{+b, w}:
      Book.get_named(~Q, ~c, b, n, e)(w)

# a book holds each entry under its own name
def Book.law.get_named(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.GetNamed(Q, c, Book.kind(~Q, ~c)):
  l => n => e => Book.law.get_named.at(~Q, ~c, l, n, e)

# two entries that do not clash give one book in either order
def Book.law.add_comm(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.AddComm(Q, c, Book.kind(~Q, ~c)):
  l => x => y => h => Book.law.add_comm.at(~Q, ~c, l, x, y)(h)

# Book.law.add_twice of the book x
def Book.law.add_twice.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +e: Entry<Q>) -> {
  Book.L.add(~Q, ~c, Book.L.add(~Q, ~c, x, e), e) == Book.L.add(~Q, ~c, x, e): Book.L(~Q, ~c)
}:
  match x:
    case Tuple{+b, +w}:
      Book.L.eq(~Q, ~c, Book.add(~Q, ~c, Book.add(~Q, ~c, b, e), e), Book.add(~Q, ~c, b, e), Book.add_idem(~Q, ~c, b, e))(
        Book.ok_add(~Q, ~c, Book.add(~Q, ~c, b, e), e)(Book.ok_add(~Q, ~c, b, e)(w))
      )(Book.ok_add(~Q, ~c, b, e)(w))

# an entry added twice to a book is added once
def Book.law.add_twice(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.AddTwice(Q, Book.kind(~Q, ~c)):
  l => e => Book.law.add_twice.at(~Q, ~c, l, e)

# the entries of a book that another lacks are those it holds that the other lacks
def Book.law.missing(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Missing(Q, c, Book.kind(~Q, ~c)):
  s => r => e => Book.law.missing.at(~Q, ~c, s, r, e)

# the ballots of a voter at a place in a book are those it holds there
def Book.law.ballots(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Ballots(Q, c, Book.kind(~Q, ~c)):
  l => w => voter => bl => Book.law.ballots.at(~Q, ~c, l, w, voter, bl)

# the round bound of a book is the round of a ballot it holds, above all others
def Book.law.rounds(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Rounds(Q, c, Book.kind(~Q, ~c)):
  (
    l => bl => line => h => r => voter => hh => hi => Book.law.rounds.le.at(~Q, ~c, l, bl, line, h, r, voter)(hh)(hi),
    l => line => h => hz => Book.law.rounds.some.at(~Q, ~c, l, line, h)(hz)
  )

# the height bound of a book is the height of a ballot it holds, above all others
def Book.law.heights(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Heights(Q, c, Book.kind(~Q, ~c)):
  (
    l => bl => line => h => r => voter => hh => hi => Book.law.heights.le.at(~Q, ~c, l, bl, line, h, r, voter)(hh)(hi),
    l => line => hz => Book.law.heights.some.at(~Q, ~c, l, line)(hz)
  )

# the requests of an author in a book are those it holds by the author
def Book.law.asks(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Asks(Q, c, Book.kind(~Q, ~c)):
  l => author => e => Book.law.asks.at(~Q, ~c, l, author, e)

# Book.law.drop of the book x
def Book.law.drop.at(~Q: Data, ~c: Codes.Codec(Q), x: Book.L(~Q, ~c), +n: Name, +m: Name) -> {
  Book.get(Q, Book.L.book(~Q, ~c, Book.L.drop(~Q, ~c, x, n)), m)
    == Shared.Bool.when(Maybe<&2, Entry<Q>>, Name.is_eq(n, m), u => None{}, u => Book.get(Q, Book.L.book(~Q, ~c, x), m)): Maybe<&2, Entry<Q>>
}:
  match x:
    case Tuple{+b, w}:
      Book.get_drop(~Q, b, n, m)

# a book without the entry of a name holds nothing there, and all else it held
def Book.law.drop(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Drop(Q, Book.kind(~Q, ~c)):
  l => n => m => Book.law.drop.at(~Q, ~c, l, n, m)

# a liar of a book under a root is the voter of a proof of a lie it holds
def Book.law.liars_sound(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.LiarsSound(Q, c, Book.kind(~Q, ~c)):
  l => r => voter => h => Book.law.liars_sound.at(~Q, ~c, l, r, voter)(h)

# each proof of a lie that a book holds names its voter a liar
def Book.law.liars_complete(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.LiarsComplete(Q, c, Book.kind(~Q, ~c)):
  l => lx => h => Book.law.liars_complete.at(~Q, ~c, l, lx)(h)

# the ballots that a key signs in a book are those it holds that the key seals
def Book.law.signed(~Q: Data, ~c: Codes.Codec(Q)) -> Laws.Signed(Q, c, Book.kind(~Q, ~c)):
  l => key => bl => Book.law.signed.at(~Q, ~c, l, key, bl)

# books obey the laws of a ledger
law Book.laws:
  for ~Q: Data
  for ~c: Codes.Codec(Q)
  Ledger.Laws(Q, c, Book.kind(~Q, ~c))

def Book.laws(Q, c):
  (Book.law.get_empty(~Q, ~c), (Book.law.get_add(~Q, ~c), (Book.law.get_named(~Q, ~c), (Book.law.add_comm(~Q, ~c), (Book.law.add_twice(~Q, ~c), (Book.law.missing(~Q, ~c), (Book.law.ballots(~Q, ~c), (Book.law.rounds(~Q, ~c), (Book.law.heights(~Q, ~c), (Book.law.asks(~Q, ~c), (Book.law.drop(~Q, ~c), (Book.law.liars_sound(~Q, ~c), (Book.law.liars_complete(~Q, ~c), Book.law.signed(~Q, ~c))))))))))))))
