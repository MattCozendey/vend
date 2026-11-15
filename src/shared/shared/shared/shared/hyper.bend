import Base
import ./code.bend as Codes
import ./hash.bend as Hashes
import ./seal.bend as Seals
import ./shared.bend as Shared

# Hyper keys
# ----------
# A many-time signature made of one-time seals (seal.bend): a hypertree, as in
# XMSS^MT and SPHINCS, with SHA-256 only. A secret seed gives each leaf of
# each layer a seal seed: the hash of the seed, the layer and the bits of the
# leaf. A tree of a layer has Hyper.height levels: the key of a leaf is the
# public key of its seal seed, and a node is the hash of its two children.
# The trees of layer 0 sign messages; the tree above signs the root of each
# tree below, at the leaf whose bits are the bits of that tree; the top layer
# has one tree, and its root is the public key. A signature with the leaf
# number i gives, for each layer, the seal of the leaf on the way and the path
# from that leaf to the root of its tree: Hyper.layers seals and paths. The
# bits of each path are the bits of i, so a check needs no number: it takes
# each seal to its key, each path to its root, and the last root must be the
# public key (Hyper.check_sign). A leaf must seal one message only: a signer
# uses each number once, below Hyper.count. The trees are built when a
# signature needs them, from the seed: a key costs one tree, a signature one
# tree per layer.

# Parameters
# ----------

# the levels of a tree
def Hyper.height() -> Nat:
  5n

# the layers of trees
def Hyper.layers() -> Nat:
  4n

# the bits of a leaf number: the height times the layers
def Hyper.bits() -> Nat:
  20n

# how many leaf numbers there are: two to the bits
def Hyper.count() -> U32:
  1048576

# Bits
# ----
# The bits of a leaf, the lowest first: those of its place in its tree, then
# those that pick its tree.

# the n lowest bits of x, the lowest first
def Bits.of(n: Nat, +x: U32) -> List<&2, Bool>:
  match n:
    case 0n:
      []
    case 1n+p:
      Bool.not(U32.is_eq(U32.and(x, 1), 0)) <> Bits.of(p, U32.shrn(x, 1n))

# the bits bs as words, then r
def Bits.code(bs: List<&2, Bool>, r: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      r
    case Con{b, rest}:
      Bool.to_u32(b) <> Bits.code(rest, r)

# the first of the bits bs; false when there is none
def Bits.head(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case Con{b, rest}:
      b

# the bits bs after the first
def Bits.tail(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      []
    case Con{b, rest}:
      rest

# Trees
# -----

# one step of a path, from the top: the side of the node on the way (true:
# the right one) and the root of the other side
type Turn is Data:
  Turn{right: Bool, other: Hashes.Hash}

# the node whose children are a and b
def Node.of(a: Hashes.Hash, b: Hashes.Hash) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(a, Hashes.Hash.code(b, [])))

# the seal seed of the leaf of the bits bs of the layer k of the seed
def Leaf.seed(seed: Hashes.Hash, k: U32, bs: List<&2, Bool>) -> Hashes.Hash:
  Hashes.Sha.hash(Hashes.Hash.code(seed, 1 <> k <> Bits.code(bs, [])))

# the key of the leaf of the bits bs of the layer k of the seed
def Leaf.key(seed: Hashes.Hash, k: U32, bs: List<&2, Bool>) -> Hashes.Hash:
  Seals.Seal.public(Leaf.seed(seed, k, bs))

# the root of the tree of height l of the layer k of the seed whose leaves
# end in the bits hi; its halves are built in parallel
def Tree.root(+l: Nat, +seed: Hashes.Hash, +k: U32, +hi: List<&2, Bool>) -> Hashes.Hash:
  match l:
    case 0n:
      Leaf.key(seed, k, hi)
    case 1n+p:
      a b = Tree.root(p, seed, k, False{} <> hi) Tree.root(p, seed, k, True{} <> hi)
      Node.of(a, b)

# the node above x, which is on the side right, beside y
def Turn.up(right: Bool, x: Hashes.Hash, y: Hashes.Hash) -> Hashes.Hash:
  match right:
    case True{}:
      Node.of(y, x)
    case False{}:
      Node.of(x, y)

# the root that the path ts, the top first, leads to from the leaf key x
def Path.root(ts: List<&2, Turn>, x: Hashes.Hash) -> Hashes.Hash:
  match ts:
    case Nil{}:
      x
    case Con{Turn{b, y}, rest}:
      Turn.up(b, Path.root(rest, x), y)

# the path, the top first, to the leaf that the bits bs pick, the highest
# first, in the tree of height l of the layer k of the seed whose leaves end
# in the bits hi
def Walk.path(
  +l: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +hi: List<&2, Bool>,
  +bs: List<&2, Bool>
) -> List<&2, Turn>:
  match l:
    case 0n:
      []
    case 1n+p:
      +b = Bits.head(bs)
      y ts = Tree.root(p, seed, k, Bool.not(b) <> hi) Walk.path(p, seed, k, b <> hi, Bits.tail(bs))
      Turn{b, y} <> ts

# the bits of the leaf that the bits bs pick, the highest first, in a tree of
# height l whose leaves end in the bits hi
def Walk.leaf(l: Nat, hi: List<&2, Bool>, +bs: List<&2, Bool>) -> List<&2, Bool>:
  match l:
    case 0n:
      hi
    case 1n+p:
      Walk.leaf(p, Bits.head(bs) <> hi, Bits.tail(bs))

# Signatures
# ----------

# the part of a signature for one layer: the seal of the leaf on the way, and
# the path from it to the root of its tree
type Layer is Data:
  Layer{seal: Seals.Seal, path: List<&2, Turn>}

# a signature: a part for each layer, the lowest first
type Sig is Data:
  Sig{layers: List<&2, Layer>}

# the layer n layers above the layer k
def Layer.above(n: Nat, k: U32) -> U32:
  match n:
    case 0n:
      k
    case 1n+p:
      Layer.above(p, U32.inc(k))

# the top layer of n layers
def Layer.top(n: Nat) -> U32:
  match n:
    case 0n:
      0
    case 1n+p:
      Layer.above(p, 0)

# the public key of the secret seed, for n layers of trees of height h: the
# root of the top tree
def Hyper.public(h: Nat, n: Nat, seed: Hashes.Hash) -> Hashes.Hash:
  Tree.root(h, seed, Layer.top(n), [])

# the bits that pick the tree of height h of the leaf of the bits bs, the
# lowest first, below p more layers: none for the top layer
def Sign.hi(p: Nat, h: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match p:
    case 0n:
      []
    case 1n+q:
      List.drop(&2, Bool, bs, h)

# the bits that pick the leaf of the bits bs in its tree of height h, the
# highest first
def Sign.turns(h: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  List.reverse(&2, Bool, List.take(&2, Bool, bs, h))

# the path from the leaf of the bits bs of the layer k of the seed to the
# root of its tree of height h, whose leaves end in the bits hi
def Sign.path(
  +h: Nat,
  seed: Hashes.Hash,
  k: U32,
  hi: List<&2, Bool>,
  bs: List<&2, Bool>
) -> List<&2, Turn>:
  Walk.path(h, seed, k, hi, Sign.turns(h, bs))

# the seal seed of that leaf
def Sign.leaf(
  +h: Nat,
  seed: Hashes.Hash,
  k: U32,
  hi: List<&2, Bool>,
  bs: List<&2, Bool>
) -> Hashes.Hash:
  Leaf.seed(seed, k, Walk.leaf(h, hi, Sign.turns(h, bs)))

# the root of the tree of that leaf, from its path
def Sign.root(
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +hi: List<&2, Bool>,
  +bs: List<&2, Bool>
) -> Hashes.Hash:
  Path.root(Sign.path(h, seed, k, hi, bs), Seals.Seal.public(Sign.leaf(h, seed, k, hi, bs)))

# the parts of the signature of the message m by the seed, for n layers of
# trees of height h from the layer k, at the leaf of the bits bs of the layer
# k; the trees of the top layer pick no bits
def Sign.go(
  +n: Nat,
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +bs: List<&2, Bool>,
  m: Hashes.Hash
) -> List<&2, Layer>:
  match n:
    case 0n:
      []
    case 1n+p:
      +hi = Sign.hi(p, h, bs)
      Layer{
        Seals.Seal.sign(Sign.leaf(h, seed, k, hi, bs), m),
        Sign.path(h, seed, k, hi, bs)
      }
        <> Sign.go(p, h, seed, U32.inc(k), hi, Sign.root(h, seed, k, hi, bs))

# the root that the signer reaches above n layers of trees of height h from
# the layer k, at the leaf of the bits bs, for the message m
def Sign.top(
  +n: Nat,
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +bs: List<&2, Bool>,
  m: Hashes.Hash
) -> Hashes.Hash:
  match n:
    case 0n:
      m
    case 1n+p:
      +hi = Sign.hi(p, h, bs)
      Sign.top(p, h, seed, U32.inc(k), hi, Sign.root(h, seed, k, hi, bs))

# the signature of the message m by the seed, for n layers of trees of height
# h, at the leaf of the bits bs, the lowest first
def Hyper.sign(h: Nat, n: Nat, seed: Hashes.Hash, bs: List<&2, Bool>, m: Hashes.Hash) -> Sig:
  Sig{Sign.go(n, h, seed, 0, bs, m)}

# the root that the path ts leads to from the key m, if any
def Path.up(m: Maybe<&2, Hashes.Hash>, ts: List<&2, Turn>) -> Maybe<&2, Hashes.Hash>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Path.root(ts, x)}

# the root that the part p shows for the message m, if any: none when its
# seal is not a seal of m
def Layer.up(m: Maybe<&2, Hashes.Hash>, p: Layer) -> Maybe<&2, Hashes.Hash>:
  match m p:
    case None{} _:
      None{}
    case Some{x} Layer{s, ts}:
      Path.up(Seals.Seal.signer(x, s), ts)

# the root that the parts ps show for the message m, if any
def Hyper.root(ps: List<&2, Layer>, m: Maybe<&2, Hashes.Hash>) -> Maybe<&2, Hashes.Hash>:
  match ps:
    case Nil{}:
      m
    case Con{p, rest}:
      Hyper.root(rest, Layer.up(m, p))

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- a signature has Hyper.layers parts (4): the right side is at most 4 steps of this loop
# the parts ps have the shape of a signature: n parts, each with a path of h
# turns
def Hyper.fits(n: Nat, ps: List<&2, Layer>, +h: Nat) -> Bool:
  match n ps:
    case 0n Nil{}:
      True{}
    case 1n+q Con{Layer{s, ts}, rest}:
      Bool.and(Nat.is_eq(List.length(&2, Turn, ts), h), Hyper.fits(q, rest, h))
    case _ _:
      False{}
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the parts ps of a signature show the public key pub for the message m,
# when they have the shape of one (ok)
def Hyper.check.if(ok: Bool, pub: Hashes.Hash, m: Hashes.Hash, ps: List<&2, Layer>) -> Bool:
  match ok:
    case True{}:
      Seals.Seal.is(pub, Hyper.root(ps, Some{m}))
    case False{}:
      False{}

# s is a signature of the message m by the seed of the public key pub, for n
# layers of trees of height h
def Hyper.check(h: Nat, n: Nat, pub: Hashes.Hash, m: Hashes.Hash, s: Sig) -> Bool:
  match s:
    case Sig{+ps}:
      Hyper.check.if(Hyper.fits(n, ps, h), pub, m, ps)

# The keys of a node
# ------------------
# Hyper.layers layers of trees of Hyper.height levels: Hyper.count leaves.

# the public key of the secret seed
def Key.public(seed: Hashes.Hash) -> Hashes.Hash:
  Hyper.public(Hyper.height(), Hyper.layers(), seed)

# the signature of the message m by the seed at the leaf number i (its bits
# below Hyper.count)
def Key.sign(seed: Hashes.Hash, i: U32, m: Hashes.Hash) -> Sig:
  Hyper.sign(Hyper.height(), Hyper.layers(), seed, Bits.of(Hyper.bits(), i), m)

# s is a signature of the message m by the seed of the public key pub
def Key.check(pub: Hashes.Hash, m: Hashes.Hash, s: Sig) -> Bool:
  Hyper.check(Hyper.height(), Hyper.layers(), pub, m, s)

# Codes
# -----

# the turn t, then r
def Turn.code(t: Turn, r: List<&2, U32>) -> List<&2, U32>:
  match t:
    case Turn{b, h}:
      Bool.to_u32(b) <> Hashes.Hash.code(h, r)

# the side of the word w: 0 is the left, 1 the right
def Turn.side(w: U32) -> Maybe<&2, Bool>:
  match w:
    case 0:
      Some{False{}}
    case 1:
      Some{True{}}
    case _:
      None{}

# the turn to the side b, from the hash that r read
def Turn.code.at(b: Bool, r: Codes.Read<Hashes.Hash>) -> Codes.Read<Turn>:
  match r:
    case Codes.Read{h, rest}:
      Codes.Read{Turn{b, h}, rest}

# a turn, once its side is read (m)
def Turn.code.of(m: Maybe<&2, Bool>, ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Turn>>:
  match m:
    case None{}:
      None{}
    case Some{b}:
      Maybe.map(
        &2,
        Codes.Read<Hashes.Hash>,
        Codes.Read<Turn>,
        x => Turn.code.at(b, x),
        Hashes.Hash.code.read(ts)
      )

# a turn
def Turn.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Turn>>:
  match ts:
    case Nil{}:
      None{}
    case Con{w, rest}:
      Turn.code.of(Turn.side(w), rest)

# the part p, then r
def Layer.code(p: Layer, r: List<&2, U32>) -> List<&2, U32>:
  match p:
    case Layer{s, ts}:
      Seals.Seal.code(s, Codes.Code.list(~Turn, ~Turn.code, ts, r))

# a part
def Layer.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Layer>>:
  Codes.Code.two.read(
    ~Seals.Seal,
    ~List<&2, Turn>,
    ~Layer,
    ~Seals.Seal.code.read,
    ~(q => Codes.Code.list.read(~Turn, ~Turn.code.read, q)),
    a => b => Layer{a, b},
    ts
  )

# the signature s, then r
def Sig.code(s: Sig, r: List<&2, U32>) -> List<&2, U32>:
  match s:
    case Sig{ps}:
      Codes.Code.list(~Layer, ~Layer.code, ps, r)

# a signature
def Sig.code.read(ts: List<&2, U32>) -> Maybe<&2, Codes.Read<Sig>>:
  Codes.Code.one.read(
    ~List<&2, Layer>,
    ~Sig,
    ~(q => Codes.Code.list.read(~Layer, ~Layer.code.read, q)),
    ps => Sig{ps},
    ts
  )

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in an erased argument (Equal.sym's sides); the checker accepts it
# the seal of a message by a seed shows the public key of the seed
def Seal.signer_sign(
  seed: Hashes.Hash,
  +m: Hashes.Hash
) -> {
  Seals.Seal.signer(
    m,
    Seals.Seal.sign(seed, m)
  )
    == Some{Seals.Seal.public(seed)}: Maybe<&2, Hashes.Hash>
}:
  %Equal.sym(
    Maybe<&2, List<&2, Hashes.Hash>>,
    Seals.Seal.ends(Seals.Seal.digits(m), Seals.Seal.shows(Seals.Seal.digits(m), seed, 0)),
    Some{Seals.Seal.tops(List.length(&2, Seals.Nibble, Seals.Seal.digits(m)), seed, 0)},
    Seals.Seal.ends_shows(Seals.Seal.digits(m), seed, 0)
  ): {
    Maybe.map(
      &2,
      List<&2, Hashes.Hash>,
      Hashes.Hash,
      Seals.Seal.key,
      _
    )
      == Some{Seals.Seal.public(seed)}: Maybe<&2, Hashes.Hash>
  }
  %Equal.sym(
    Nat,
    List.length(&2, Seals.Nibble, Seals.Seal.digits(m)),
    67n,
    Seals.Seal.digits_length(m)
  ): {
    Some{
      Seals.Seal.key(Seals.Seal.tops(_, seed, 0))
    }
      == Some{Seals.Seal.public(seed)}: Maybe<&2, Hashes.Hash>
  }
  {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a turn to the side b, from the root of that side, to the root of the other
# side, is the node above both
def Turn.up_root(
  b: Bool,
  p: Nat,
  seed: Hashes.Hash,
  k: U32,
  hi: List<&2, Bool>
) -> {
  Turn.up(
    b,
    Tree.root(p, seed, k, b <> hi),
    Tree.root(p, seed, k, Bool.not(b) <> hi)
  )
    == Tree.root(1n+p, seed, k, hi): Hashes.Hash
}:
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

# the path to a leaf leads from its key to the root of its tree
def Walk.root(
  +l: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +hi: List<&2, Bool>,
  +bs: List<&2, Bool>
) -> {
  Path.root(
    Walk.path(l, seed, k, hi, bs),
    Leaf.key(seed, k, Walk.leaf(l, hi, bs))
  )
    == Tree.root(l, seed, k, hi): Hashes.Hash
}:
  match l:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(
        Hashes.Hash,
        Path.root(
          Walk.path(p, seed, k, Bits.head(bs) <> hi, Bits.tail(bs)),
          Leaf.key(seed, k, Walk.leaf(p, Bits.head(bs) <> hi, Bits.tail(bs)))
        ),
        Tree.root(p, seed, k, Bits.head(bs) <> hi),
        Walk.root(p, seed, k, Bits.head(bs) <> hi, Bits.tail(bs))
      ): {
        Turn.up(
          Bits.head(bs),
          _,
          Tree.root(p, seed, k, Bool.not(Bits.head(bs)) <> hi)
        )
          == Tree.root(1n+p, seed, k, hi): Hashes.Hash
      }
      Turn.up_root(Bits.head(bs), p, seed, k, hi)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in an erased argument (Equal.sym's sides); the checker accepts it
# a path has one turn for each level of its tree
def Walk.path_length(
  +l: Nat,
  seed: Hashes.Hash,
  k: U32,
  hi: List<&2, Bool>,
  +bs: List<&2, Bool>
) -> {List.length(&2, Turn, Walk.path(l, seed, k, hi, bs)) == l: Nat}:
  match l:
    case 0n:
      {==}
    case 1n+lp:
      %Equal.sym(
        Nat,
        List.length(&2, Turn, Walk.path(lp, seed, k, Bits.head(bs) <> hi, Bits.tail(bs))),
        lp,
        Walk.path_length(lp, seed, k, Bits.head(bs) <> hi, Bits.tail(bs))
      ): {1n+_ == 1n+lp: Nat}
      {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the parts of a signature have the shape of one
def Sign.fits(
  +n: Nat,
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +bs: List<&2, Bool>,
  m: Hashes.Hash
) -> {Hyper.fits(n, Sign.go(n, h, seed, k, bs, m), h) == True{}: Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hi = Sign.hi(p, h, bs)
      %Equal.sym(
        Nat,
        List.length(&2, Turn, Walk.path(h, seed, k, hi, Sign.turns(h, bs))),
        h,
        Walk.path_length(h, seed, k, hi, Sign.turns(h, bs))
      ): {
        Bool.and(
          Nat.is_eq(_, h),
          Hyper.fits(p, Sign.go(p, h, seed, U32.inc(k), hi, Sign.root(h, seed, k, hi, bs)), h)
        )
          == True{}: Bool
      }
      %Equal.sym(
        Bool,
        Nat.is_eq(h, h),
        True{},
        Shared.Nat.is_eq_refl(h)
      ): {
        Bool.and(
          _,
          Hyper.fits(p, Sign.go(p, h, seed, U32.inc(k), hi, Sign.root(h, seed, k, hi, bs)), h)
        )
          == True{}: Bool
      }
      Sign.fits(p, h, seed, U32.inc(k), hi, Sign.root(h, seed, k, hi, bs))

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in this proof a second use sits in an erased argument (Equal.sym's sides); the checker accepts it
# the parts of a signature show the root that the signer reached
def Sign.root_go(
  +n: Nat,
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +bs: List<&2, Bool>,
  m: Hashes.Hash
) -> {
  Hyper.root(
    Sign.go(n, h, seed, k, bs, m),
    Some{m}
  )
    == Some{Sign.top(n, h, seed, k, bs, m)}: Maybe<&2, Hashes.Hash>
}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      +hi = Sign.hi(p, h, bs)
      r = Sign.root(h, seed, k, hi, bs)
      %Equal.sym(
        Maybe<&2, Hashes.Hash>,
        Seals.Seal.signer(m, Seals.Seal.sign(Sign.leaf(h, seed, k, hi, bs), m)),
        Some{Seals.Seal.public(Sign.leaf(h, seed, k, hi, bs))},
        Seal.signer_sign(Sign.leaf(h, seed, k, hi, bs), m)
      ): {
        Hyper.root(
          Sign.go(p, h, seed, U32.inc(k), hi, r),
          Path.up(_, Sign.path(h, seed, k, hi, bs))
        )
          == Some{Sign.top(p, h, seed, U32.inc(k), hi, r)}: Maybe<&2, Hashes.Hash>
      }
      Sign.root_go(p, h, seed, U32.inc(k), hi, r)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# the root that the signer reaches is the root of the top tree
def Sign.top_root(
  +q: Nat,
  +h: Nat,
  +seed: Hashes.Hash,
  +k: U32,
  +bs: List<&2, Bool>,
  m: Hashes.Hash
) -> {Sign.top(1n+q, h, seed, k, bs, m) == Tree.root(h, seed, Layer.above(q, k), []): Hashes.Hash}:
  match q:
    case 0n:
      Walk.root(h, seed, k, [], Sign.turns(h, bs))
    case 1n+r:
      Sign.top_root(
        r,
        h,
        seed,
        U32.inc(k),
        Sign.hi(1n+r, h, bs),
        Sign.root(h, seed, k, Sign.hi(1n+r, h, bs), bs)
      )

# a signature of a message by a seed checks with the public key of the seed,
# for any height of the trees, any number of layers but none, and any bits of
# a leaf (a signer uses the bits of each leaf number once)
law Hyper.check_sign:
  for +h: Nat
  for +q: Nat
  for +seed: Hashes.Hash
  for +bs: List<&2, Bool>
  for +m: Hashes.Hash
  {
    Hyper.check(
      h,
      1n+q,
      Hyper.public(h, 1n+q, seed),
      m,
      Hyper.sign(h, 1n+q, seed, bs, m)
    )
      == True{}: Bool
  }

def Hyper.check_sign(h, q, seed, bs, m):
  pub = Hyper.public(h, 1n+q, seed)
  %Equal.sym(
    Bool,
    Hyper.fits(1n+q, Sign.go(1n+q, h, seed, 0, bs, m), h),
    True{},
    Sign.fits(1n+q, h, seed, 0, bs, m)
  ): {Hyper.check.if(_, pub, m, Sign.go(1n+q, h, seed, 0, bs, m)) == True{}: Bool}
  %Equal.sym(
    Maybe<&2, Hashes.Hash>,
    Hyper.root(Sign.go(1n+q, h, seed, 0, bs, m), Some{m}),
    Some{Sign.top(1n+q, h, seed, 0, bs, m)},
    Sign.root_go(1n+q, h, seed, 0, bs, m)
  ): {Seals.Seal.is(pub, _) == True{}: Bool}
  %Equal.sym(
    Hashes.Hash,
    Sign.top(1n+q, h, seed, 0, bs, m),
    Tree.root(h, seed, Layer.above(q, 0), []),
    Sign.top_root(q, h, seed, 0, bs, m)
  ): {Seals.Seal.is(pub, Some{_}) == True{}: Bool}
  Hashes.Hash.is_eq_refl(pub)
