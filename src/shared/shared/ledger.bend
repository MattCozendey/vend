import Base
import ./shared/quorum.bend as Quorums
import ./shared/shared/cell.bend as Cells
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

# b is a ballot of the voter under the root r whose chain names p as the
# place of the ballot before it (none: b is the first). A key signs one
# ballot only, so two such ballots are a lie
def Ballot.follows(+b: Ballot, r: Hashes.Hash, voter: String, p: Maybe<&2, Place>) -> Bool:
  Bool.and(
    Bool.and(Hashes.Hash.is_eq(Ballot.root(b), r), String.eq(Ballot.voter(b), voter)),
    Shared.Maybe.is_eq(~Place, ~Place.is_eq, Ballot.prev(b), p)
  )

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
# no ballot of a line is above; the requests of an author; the ledger
# without the entry of a name; and the ballots of a voter under a root that
# follow a place in its chain
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
                                    & ((L -> Name -> L) & (L -> Hashes.Hash -> String -> Maybe<&2, Place> -> List<&2, Ballot>))
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

# the ballots of a voter under a root that follow a place in its chain (none:
# the first), in a ledger of the kind k
def Kind.after(
  -Q: Data,
  k: Ledger.Kind(Q)
) -> Kind.L(Q, k) -> Hashes.Hash -> String -> Maybe<&2, Place> -> List<&2, Ballot>:
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

# the ballots of a voter under a root that follow a place are the ballots of
# the ledger that follow it so, and no other: a lie is found in one read
def Laws.After(-Q: Data, -c: Codes.Codec(Q), -k: Ledger.Kind(Q)) -> Type:
  @l: Kind.L(Q, k) -> @r: Hashes.Hash -> @voter: String -> @p: Maybe<&2, Place> -> @b: Ballot -> {
    List.contains(~Ballot, ~Ballot.is_eq, Kind.after(Q, k)(l)(r)(voter)(p), b)
      == Bool.and(Kind.has(~Q, ~c, ~k, l, Entry.Ballot{b}), Ballot.follows(b, r, voter, p)): Bool
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
                                            & (Laws.LiarsSound(Q, c, k) & (Laws.LiarsComplete(Q, c, k) & Laws.After(Q, c, k)))
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
# requests of an author, and the ballots of a voter under a root by the
# place before them
type Book<-Q: Data> is Data:
  Book{
    entries: Crits.Dict(Entry<Q>),
    ballots: Crits.Dict(Name),
    rounds: Crits.Dict(Name),
    heights: Crits.Dict(Name),
    liars: Crits.Dict(Name),
    asks: Crits.Dict(Name),
    after: Crits.Dict(Name)
  }

# the keys of an entry in each index of a book (none: it is not in that one)
type Keys is Data:
  Keys{
    ballot: Maybe<&2, List<&2, U32>>,
    round: Maybe<&2, List<&2, U32>>,
    height: Maybe<&2, List<&2, U32>>,
    liar: Maybe<&2, List<&2, U32>>,
    ask: Maybe<&2, List<&2, U32>>,
    after: Maybe<&2, List<&2, U32>>
  }

# the key, then r, of the ballots of a voter under the root rt whose chain
# names p as the place before them
def Index.after.key(rt: Hashes.Hash, voter: String, p: Maybe<&2, Place>, r: List<&2, U32>) -> List<&2, U32>:
  Hashes.Hash.code(rt, Codes.Code.text(voter, Codes.Code.maybe(~Place, ~Place.code, p, r)))

# the root of the line c
def Line.root(c: Line) -> Hashes.Hash:
  match c:
    case Line{r, s}:
      r

# the keys of the ballot b, of the name n
def Ballot.keys(b: Ballot, +n: Name) -> Keys:
  match b:
    case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, Link{+p, k, z}}:
      Keys{
        Some{Place.code(Place{line, h, r}, Codes.Code.text(voter, Name.key(n)))},
        Some{Line.code(line, h <> Crits.Key.ord(r, Name.key(n)))},
        Some{Line.code(line, Crits.Key.ord(U32.to_nat(h), Name.key(n)))},
        None{},
        None{},
        Some{Index.after.key(Line.root(line), voter, p, Name.key(n))}
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
# liars, 4 asks, 5 after
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

# the ballots of the voter under the root rt that follow the place p
def Book.after(-Q: Data, +b: Book<Q>, rt: Hashes.Hash, voter: String, p: Maybe<&2, Place>) -> List<&2, Ballot>:
  Entries.ballots(Q, Book.named(Q, b, Index.under(Book.index(Q, b, 5n), Index.after.key(rt, voter, p, []))))

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
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, l}:
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
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, l}:
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
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, l}:
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
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, l}:
          h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Read.then(Hashes.Hash, String, Hashes.Hash.code.read(k), p => r => Codes.Code.text.read(r)), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# the key k of the asks index (4 on) of an entry of the name n ends in the
# key of n
def Book.key_tail.asks(-Q: Data, e: Entry<Q>, +n: Name, -p: Nat, -k: List<&2, U32>) -> {
  Keys.at(Entry.keys(Q, e, n), 4n+p) == Some{k}: Maybe<&2, List<&2, U32>>
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
        case Ballot{Signed{Place{+line, +h, +r}, +voter, a}, l}:
          h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Data{ws}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))
    case Entry.Lie{x}:
      h => Empty.absurd({Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []) == Name.key(n): List<&2, U32>}, Shared.Maybe.none_ne_some(List<&2, U32>, k, h))

# a key of the index i of entries of the names n1 and n2 is of names with the
# same key
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
                case 1n+p:
                  h1 => h2 =>
                    Equal.trans(
                      List<&2, U32>,
                      Name.key(n1),
                      Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []),
                      Name.key(n2),
                      Equal.sym(List<&2, U32>, Codes.Code.read_value(List<&2, U32>, Codes.Read.then(String, List<&2, U32>, Codes.Code.text.read(k), a => r => Some{Codes.Read{r, []}}), []), Name.key(n1), Book.key_tail.asks(Q, e1, n1, p, k)(h1)),
                      Book.key_tail.asks(Q, e2, n2, p, k)(h2)
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
    case Book{es, bs, rs, hs, ls, as, fs} Keys{kb, kr, kh, kl, ka}:
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
    case Book{es, bs, rs, hs, ls, as, fs} Keys{kb, kr, kh, kl, ka}:
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
} -> {Book.indexed(Q, b2, ks, n) == Book.indexed(Q, b, ks, n): Bool}:
  e0 => e1 => e2 => e3 => e4 =>
    %e0: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(_, Index.holds(Book.index(Q, b, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n))): Bool}
    %e1: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), _), Bool.and(Bool.and(Index.holds(Book.index(Q, b, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n))): Bool}
    %e2: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(_, Index.holds(Book.index(Q, b, 3n), Keys.at(ks, 3n), n)), Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n))): Bool}
    %e3: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n), _), Index.holds(Book.index(Q, b, 4n), Keys.at(ks, 4n), n))): Bool}
    %e4: {Book.indexed(Q, b2, ks, n) == Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 0n), Keys.at(ks, 0n), n), Index.holds(Book.index(Q, b2, 1n), Keys.at(ks, 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, b2, 2n), Keys.at(ks, 2n), n), Index.holds(Book.index(Q, b2, 3n), Keys.at(ks, 3n), n)), _)): Bool}
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
  Shared.Bool.and_both(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 0n), Keys.at(Entry.keys(Q, e, n), 0n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 1n), Keys.at(Entry.keys(Q, e, n), 1n), n)), Bool.and(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n)), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 4n), Keys.at(Entry.keys(Q, e, n), 4n), n)))(
    Shared.Bool.and_both(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 0n), Keys.at(Entry.keys(Q, e, n), 0n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 1n), Keys.at(Entry.keys(Q, e, n), 1n), n))(Book.holds_put_same(~Q, b, e, n, 0n))(Book.holds_put_same(~Q, b, e, n, 1n))
  )(
    Shared.Bool.and_both(Bool.and(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n)), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 4n), Keys.at(Entry.keys(Q, e, n), 4n), n))(Shared.Bool.and_both(Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 2n), Keys.at(Entry.keys(Q, e, n), 2n), n), Index.holds(Book.index(Q, Book.put(~Q, b, e, n, Entry.keys(Q, e, n)), 3n), Keys.at(Entry.keys(Q, e, n), 3n), n))(Book.holds_put_same(~Q, b, e, n, 2n))(Book.holds_put_same(~Q, b, e, n, 3n)))(Book.holds_put_same(~Q, b, e, n, 4n))
  )

# an entry of the book b other than e is in its place after the add of e
def Book.add_entry.old(~Q: Data, ~c: Codes.Codec(Q), +b: Book<Q>, +e: Entry<Q>, +hok: {Book.ok(~Q, ~c, b) == True{}: Bool}, +k: List<&2, U32>, +v: Entry<Q>) -> {
  Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))) == False{}: Bool
} -> {Crits.Dict.get(Entry<Q>, Book.entries(Q, b), k) == Some{v}: Maybe<&2, Entry<Q>>} -> {Bool.and(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))) == True{}: Bool}:
  +f => hv =>
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), k, v)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))))(hok))(hv)
    +hkm = Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, v)), k)(
      Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)))(hc)
    )
    +hne = Equal.trans(Bool, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), Name.key(Entry.name(~Q, ~c, e))), Crits.Key.is_eq(k, Name.key(Entry.name(~Q, ~c, e))), False{}, Equal.cong(List<&2, U32>, Bool, z => Crits.Key.is_eq(z, Name.key(Entry.name(~Q, ~c, e))), Name.key(Entry.name(~Q, ~c, v)), k, hkm), f)
    %Equal.sym(
      Bool,
      Book.indexed(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed_same(Q, b, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 0n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 1n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 2n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 3n)(hne))(Book.holds_put(~Q, b, e, Entry.name(~Q, ~c, e), v, Entry.name(~Q, ~c, v), 4n)(hne))
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
    +r = Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))))(hok)
    +l01 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n)))(r)
    +r24 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n)))(r)
    +l23 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))(r24)
    +a0 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a1 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a2 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a3 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a4 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))(r24)
    Shared.Bool.and_both(Book.ok.entries(~Q, ~c, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))))), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n))))(Book.add_entries(~Q, ~c, b, e, hok, Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))))))(Book.dict_agrees(~Entry<Q>, Book.entries(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e)))))))(
      Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n)))(
        Shared.Bool.and_both(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n))(Book.add_index(~Q, ~c, b, e, hn, 0n, a0, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 0n))))(Book.add_index(~Q, ~c, b, e, hn, 1n, a1, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 1n))))
      )(
        Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n))(Shared.Bool.and_both(Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n), Book.ok.at(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n))(Book.add_index(~Q, ~c, b, e, hn, 2n, a2, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 2n))))(Book.add_index(~Q, ~c, b, e, hn, 3n, a3, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 3n)))))(Book.add_index(~Q, ~c, b, e, hn, 4n, a4, Crits.Dict.entries(Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n)))(Book.dict_agrees(~Name, Book.index(Q, Book.put(~Q, b, e, Entry.name(~Q, ~c, e), Entry.keys(Q, e, Entry.name(~Q, ~c, e))), 4n))))
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
    +hc = Book.ok.entries_get(~Q, ~c, b, Book.entries(Q, b), k, v)(Shared.Bool.and_true_left(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))))(hok))(hv)
    +hkm = Crits.Key.is_eq_sound(Name.key(Entry.name(~Q, ~c, v)), k)(
      Shared.Bool.and_true_left(Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), k), Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)))(hc)
    )
    +hne = Equal.trans(Bool, Crits.Key.is_eq(Name.key(Entry.name(~Q, ~c, v)), Name.key(n)), Crits.Key.is_eq(k, Name.key(n)), False{}, Equal.cong(List<&2, U32>, Bool, z => Crits.Key.is_eq(z, Name.key(n)), Name.key(Entry.name(~Q, ~c, v)), k, hkm), f)
    %Equal.sym(
      Bool,
      Book.indexed(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed(Q, b, Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v)),
      Book.indexed_same(Q, b, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Entry.keys(Q, v, Entry.name(~Q, ~c, v)), Entry.name(~Q, ~c, v))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 0n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 1n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 2n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 3n)(hne))(Book.holds_take(~Q, b, e, n, v, Entry.name(~Q, ~c, v), 4n)(hne))
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
    +r = Shared.Bool.and_true_right(Book.ok.entries(~Q, ~c, b, Crits.Dict.entries(Entry<Q>, Book.entries(Q, b))), Bool.and(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))))(hok)
    +l01 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n)))(r)
    +r24 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n)), Bool.and(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n)))(r)
    +l23 = Shared.Bool.and_true_left(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))(r24)
    +a0 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a1 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 0n), Book.ok.at(Q, b, 1n))(l01)
    +a2 = Shared.Bool.and_true_left(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a3 = Shared.Bool.and_true_right(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n))(l23)
    +a4 = Shared.Bool.and_true_right(Bool.and(Book.ok.at(Q, b, 2n), Book.ok.at(Q, b, 3n)), Book.ok.at(Q, b, 4n))(r24)
    Shared.Bool.and_both(Book.ok.entries(~Q, ~c, Book.take(~Q, b, n, Entry.keys(Q, e, n)), Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))))), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n))))(Book.drop_entries(~Q, ~c, b, e, n, hok, Crits.Dict.entries(Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)))))(Book.dict_agrees(~Entry<Q>, Book.entries(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n))))))(
      Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)), Bool.and(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n)))(
        Shared.Bool.and_both(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n))(Book.drop_index(~Q, b, e, n, hm, 0n, a0, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 0n))))(Book.drop_index(~Q, b, e, n, hm, 1n, a1, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 1n))))
      )(
        Shared.Bool.and_both(Bool.and(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n))(Shared.Bool.and_both(Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n), Book.ok.at(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n))(Book.drop_index(~Q, b, e, n, hm, 2n, a2, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 2n))))(Book.drop_index(~Q, b, e, n, hm, 3n, a3, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 3n)))))(Book.drop_index(~Q, b, e, n, hm, 4n, a4, Crits.Dict.entries(Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n)))(Book.dict_agrees(~Name, Book.index(Q, Book.take(~Q, b, n, Entry.keys(Q, e, n)), 4n))))
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
