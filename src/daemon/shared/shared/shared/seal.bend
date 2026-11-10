import Base
import ./code.bend as Codes
import ./hash.bend as Hashes

# Seals
# -----
# A seal is a one-time signature of a hash (Winternitz, 16 ways), made with
# SHA-256 only. A secret seed gives 67 chains: a chain starts at the hash of
# the seed and its index, and each step is the hash of the value before it.
# The public key is the hash of the 67 values at step 15. A seal gives, for
# each of the 64 nibbles d of the message and the 3 nibbles of their checksum,
# the value of its chain at step d. A check moves each value 15 - d steps more
# and compares the hash of the ends with the public key (Seal.check_sign).
# A seed must sign one message only: two seals of one seed show values that
# make other seals. That only the owner of the seed can make a seal that
# checks is a cryptographic assumption on SHA-256, not a law.

# a seal: the value of each chain, in order
type Seal is Data:
  Seal{values: List<&2, Hashes.Hash>}

# a nibble: its 4 bits, the highest first
type Nibble is Data:
  Nibble{b8: Bool, b4: Bool, b2: Bool, b1: Bool}

# Codes
# -----

# the seal s, then r
def Seal.code(s: Seal, r: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Seal{vs}:
      Codes.Code.list(~Hashes.Hash, ~Hashes.Hash.code, vs, r)

# a seal
def Seal.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Seal>>:
  Codes.Code.one.read(
    ~List<&2, Hashes.Hash>,
    ~Seal,
    ~(q => Codes.Code.list.read(~Hashes.Hash, ~Hashes.Hash.code.read, q)),
    vs => Seal{vs},
    ts
  )

# Nibbles
# -------

# r, plus w when b holds
def Nibble.bit(b: Bool, w: Nat, r: Nat) -> Nat:
  match b:
    case True{}:
      Nat.add(w, r)
    case False{}:
      r

# the number of n: 0 to 15
def Nibble.count(n: Nibble) -> Nat:
  match n:
    case Nibble{a, b, c, d}:
      Nibble.bit(a, 8n, Nibble.bit(b, 4n, Nibble.bit(c, 2n, Nibble.bit(d, 1n, 0n))))

# 15 minus the number of n
def Nibble.rest(n: Nibble) -> Nat:
  match n:
    case Nibble{a, b, c, d}:
      Nibble.count(Nibble{Bool.not(a), Bool.not(b), Bool.not(c), Bool.not(d)})

# the bits of x that m has are not all zero
def Nibble.has(x: U32, m: U32) -> Bool:
  Bool.not(U32.is_eq(U32.and(x, m), 0))

# the lowest 4 bits of x
def Nibble.of(+x: U32) -> Nibble:
  Nibble{Nibble.has(x, 8), Nibble.has(x, 4), Nibble.has(x, 2), Nibble.has(x, 1)}

# the 8 nibbles of x, highest first, then r
def Nibbles.word(+x: U32, r: List<&2, Nibble>) -> List<&2, Nibble>:
  Nibble.of(
    U32.shrn(x, 28n)
  )
    <> Nibble.of(U32.shrn(x, 24n))
    <> Nibble.of(U32.shrn(x, 20n))
    <> Nibble.of(U32.shrn(x, 16n))
    <> Nibble.of(U32.shrn(x, 12n))
    <> Nibble.of(U32.shrn(x, 8n))
    <> Nibble.of(U32.shrn(x, 4n))
    <> Nibble.of(x)
    <> r

# the 64 nibbles of the hash h, highest first
def Nibbles.of(h: Hashes.Hash) -> List<&2, Nibble>:
  match h:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      Nibbles.word(
        a,
        Nibbles.word(
          b,
          Nibbles.word(
            c,
            Nibbles.word(d, Nibbles.word(e, Nibbles.word(f, Nibbles.word(g, Nibbles.word(i, [])))))
          )
        )
      )

# the checksum of ns: the sum of 15 minus each number
def Nibbles.sum(ns: List<&2, Nibble>) -> Nat:
  match ns:
    case Nil{}:
      0n
    case Con{n, r}:
      Nat.add(Nibble.rest(n), Nibbles.sum(r))

# the lowest 3 nibbles of x, highest first
def Nibbles.low(+x: U32) -> List<&2, Nibble>:
  [Nibble.of(U32.shrn(x, 8n)), Nibble.of(U32.shrn(x, 4n)), Nibble.of(x)]

# ns, then the 3 nibbles of their checksum
def Nibbles.summed(+ns: List<&2, Nibble>) -> List<&2, Nibble>:
  List.append(&2, Nibble, ns, Nibbles.low(U32.from_nat(Nibbles.sum(ns))))

# Chains
# ------

# the 67 nibbles that a seal of the message m shows: the 64 of m, then the 3
# of their checksum
def Seal.digits(m: Hashes.Hash) -> List<&2, Nibble>:
  Nibbles.summed(Nibbles.of(m))

# the value after h in a chain
def Seal.step(h: Hashes.Hash) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(h, []))

# the value n steps after h in a chain
def Seal.steps(n: Nat, h: Hashes.Hash) -> Hashes.Hash:
  match n:
    case 0n:
      h
    case 1n+p:
      Seal.step(Seal.steps(p, h))

# the start of the chain j of the seed: secret
def Seal.start(seed: Hashes.Hash, j: U32) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, [j]))

# the ends of the n chains of the seed from the chain j
def Seal.tops(n: Nat, +seed: Hashes.Hash, +j: U32) -> List<&2, Hashes.Hash>:
  match n:
    case 0n:
      []
    case 1n+p:
      Seal.steps(15n, Seal.start(seed, j)) <> Seal.tops(p, seed, U32.inc(j))

# the values that the seed shows for the nibbles ds, from the chain j
def Seal.shows(ds: List<&2, Nibble>, +seed: Hashes.Hash, +j: U32) -> List<&2, Hashes.Hash>:
  match ds:
    case Nil{}:
      []
    case Con{d, r}:
      Seal.steps(Nibble.count(d), Seal.start(seed, j)) <> Seal.shows(r, seed, U32.inc(j))

# the end e, then the ends m, if any
def Seal.ends.con(
  e: Hashes.Hash,
  m: Maybe<&2, List<&2, Hashes.Hash>>
) -> Maybe<&2, List<&2, Hashes.Hash>>:
  match m:
    case None{}:
      None{}
    case Some{es}:
      Some{e <> es}

# the ends of the chains of the values vs, shown for the nibbles ds; none when
# the values are not one for each nibble
def Seal.ends(ds: List<&2, Nibble>, vs: List<&2, Hashes.Hash>) -> Maybe<&2, List<&2, Hashes.Hash>>:
  match ds vs:
    case Nil{} Nil{}:
      Some{[]}
    case Con{d, r} Con{v, w}:
      Seal.ends.con(Seal.steps(Nibble.rest(d), v), Seal.ends(r, w))
    case _ _:
      None{}

# the key of the chain ends es: the hash of all of them
def Seal.key(es: List<&2, Hashes.Hash>) -> Hashes.Hash:
  Hashes.Sha.hash(Codes.Code.items(~Hashes.Hash, ~Hashes.Hash.code, es, []))

# Seals
# -----

# the public key of the secret seed
def Seal.public(seed: Hashes.Hash) -> Hashes.Hash:
  Seal.key(Seal.tops(67n, seed, 0))

# the seal of the message m by the seed
def Seal.sign(seed: Hashes.Hash, m: Hashes.Hash) -> Seal:
  Seal{Seal.shows(Seal.digits(m), seed, 0)}

# the ends m, if any, give the key pub
def Seal.check.ends(pub: Hashes.Hash, m: Maybe<&2, List<&2, Hashes.Hash>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{es}:
      Hashes.Hash.is_eq(pub, Seal.key(es))

# s is a seal of the message m by the seed of the public key pub
def Seal.check(pub: Hashes.Hash, m: Hashes.Hash, s: Seal) -> Bool:
  match s:
    case Seal{vs}:
      Seal.check.ends(pub, Seal.ends(Seal.digits(m), vs))

# Laws
# ----

# a seal reads back
def Seal.code_read(
  s: Seal,
  r: List<&2, U32>
) -> {Seal.code.read(Seal.code(s, r)) == Some{Codes.Read{s, r}}: Maybe<&2, Codes.Read<Seal>>}:
  match s:
    case Seal{vs}:
      Codes.Code.one_read(
        ~List<&2, Hashes.Hash>,
        ~Seal,
        ~Codes.Code.list.codec(~Hashes.Hash, ~Hashes.Hash.codec()),
        ws => Seal{ws},
        vs,
        r
      )

# the code of seals
def Seal.codec() -> Codes.Codec(Seal):
  (Seal.code, (Seal.code.read, s => r => Seal.code_read(s, r)))

# the number of a nibble and its rest make 15
def Nibble.rest_count(n: Nibble) -> {Nat.add(Nibble.rest(n), Nibble.count(n)) == 15n: Nat}:
  match n:
    case Nibble{True{}, True{}, True{}, True{}}:
      {==}
    case Nibble{True{}, True{}, True{}, False{}}:
      {==}
    case Nibble{True{}, True{}, False{}, True{}}:
      {==}
    case Nibble{True{}, True{}, False{}, False{}}:
      {==}
    case Nibble{True{}, False{}, True{}, True{}}:
      {==}
    case Nibble{True{}, False{}, True{}, False{}}:
      {==}
    case Nibble{True{}, False{}, False{}, True{}}:
      {==}
    case Nibble{True{}, False{}, False{}, False{}}:
      {==}
    case Nibble{False{}, True{}, True{}, True{}}:
      {==}
    case Nibble{False{}, True{}, True{}, False{}}:
      {==}
    case Nibble{False{}, True{}, False{}, True{}}:
      {==}
    case Nibble{False{}, True{}, False{}, False{}}:
      {==}
    case Nibble{False{}, False{}, True{}, True{}}:
      {==}
    case Nibble{False{}, False{}, True{}, False{}}:
      {==}
    case Nibble{False{}, False{}, False{}, True{}}:
      {==}
    case Nibble{False{}, False{}, False{}, False{}}:
      {==}

# a seal shows 67 nibbles
def Seal.digits_length(m: Hashes.Hash) -> {List.length(&2, Nibble, Seal.digits(m)) == 67n: Nat}:
  match m:
    case Hashes.Hash{a, b, c, d, e, f, g, i}:
      {==}

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in an erased argument; the checker accepts it
# b steps, then a steps, are a plus b steps
def Seal.steps_add(
  a: Nat,
  b: Nat,
  h: Hashes.Hash
) -> {Seal.steps(a, Seal.steps(b, h)) == Seal.steps(Nat.add(a, b), h): Hashes.Hash}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(
        Hashes.Hash,
        Hashes.Hash,
        Seal.step,
        Seal.steps(p, Seal.steps(b, h)),
        Seal.steps(Nat.add(p, b), h),
        Seal.steps_add(p, b, h)
      )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the steps of a nibble, then the steps of its rest, are 15 steps
def Seal.steps_full(
  +d: Nibble,
  h: Hashes.Hash
) -> {
  Seal.steps(Nibble.rest(d), Seal.steps(Nibble.count(d), h)) == Seal.steps(15n, h): Hashes.Hash
}:
  %Nibble.rest_count(
    d
  ): {Seal.steps(Nibble.rest(d), Seal.steps(Nibble.count(d), h)) == Seal.steps(_, h): Hashes.Hash}
  Seal.steps_add(Nibble.rest(d), Nibble.count(d), h)

# the values that a seed shows for nibbles end at the ends of its chains
def Seal.ends_shows(
  ds: List<&2, Nibble>,
  +seed: Hashes.Hash,
  +j: U32
) -> {
  Seal.ends(
    ds,
    Seal.shows(ds, seed, j)
  )
    == Some{Seal.tops(List.length(&2, Nibble, ds), seed, j)}: Maybe<&2, List<&2, Hashes.Hash>>
}:
  match ds:
    case Nil{}:
      {==}
    case Con{d, r}:
      %Equal.sym(
        Maybe<&2, List<&2, Hashes.Hash>>,
        Seal.ends(r, Seal.shows(r, seed, U32.inc(j))),
        Some{Seal.tops(List.length(&2, Nibble, r), seed, U32.inc(j))},
        Seal.ends_shows(r, seed, U32.inc(j))
      ): {
        Seal.ends.con(
          Seal.steps(Nibble.rest(d), Seal.steps(Nibble.count(d), Seal.start(seed, j))),
          _
        )
          == Some{
            Seal.steps(
              15n,
              Seal.start(seed, j)
            )
              <> Seal.tops(List.length(&2, Nibble, r), seed, U32.inc(j))
          }: Maybe<&2, List<&2, Hashes.Hash>>
      }
      %Equal.sym(
        Hashes.Hash,
        Seal.steps(Nibble.rest(d), Seal.steps(Nibble.count(d), Seal.start(seed, j))),
        Seal.steps(15n, Seal.start(seed, j)),
        Seal.steps_full(d, Seal.start(seed, j))
      ): {
        Some{
          _ <> Seal.tops(List.length(&2, Nibble, r), seed, U32.inc(j))
        }
          == Some{
            Seal.steps(
              15n,
              Seal.start(seed, j)
            )
              <> Seal.tops(List.length(&2, Nibble, r), seed, U32.inc(j))
          }: Maybe<&2, List<&2, Hashes.Hash>>
      }
      {==}

# the seal of a message by a seed checks with the public key of the seed
law Seal.check_sign:
  for +seed: Hashes.Hash
  for +m: Hashes.Hash
  {Seal.check(Seal.public(seed), m, Seal.sign(seed, m)) == True{}: Bool}

def Seal.check_sign(seed, m):
  %Equal.sym(
    Maybe<&2, List<&2, Hashes.Hash>>,
    Seal.ends(Seal.digits(m), Seal.shows(Seal.digits(m), seed, 0)),
    Some{Seal.tops(List.length(&2, Nibble, Seal.digits(m)), seed, 0)},
    Seal.ends_shows(Seal.digits(m), seed, 0)
  ): {Seal.check.ends(Seal.public(seed), _) == True{}: Bool}
  %Equal.sym(
    Nat,
    List.length(&2, Nibble, Seal.digits(m)),
    67n,
    Seal.digits_length(m)
  ): {Hashes.Hash.is_eq(Seal.public(seed), Seal.key(Seal.tops(_, seed, 0))) == True{}: Bool}
  Hashes.Hash.is_eq_refl(Seal.public(seed))
